/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Design
import GeoDa.ReducedForm
import Lean

/-!
# A minimal Lean-native DSL for spatial model specifications

`GeoDa.GNSDes` and its siblings are ordinary Lean definitions: to add a model you
write the model equation out again, with its parameter list, and then re-derive
whatever you want to say about it. This file adds a `spatial_model` command that
writes the definition for you from the equation alone.

```
spatial_model MySAR (n k : ℕ) (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) (ρ : ℝ) :
  y = ρ • (W *ᵥ y) + X *ᵥ β + ε
```

generates

```
def MySAR (n k : ℕ) (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + X *ᵥ β + ε
```

which is an ordinary `def`: `#print MySAR` shows it, `rfl` proves it equal to a
hand-written specification with the same binder list, and every later proof goes
through unchanged.

## The trust boundary: there isn't one

The command **elaborates the equation with Lean's own elaborator**. It does not
interpret it, does not rewrite it, and does not decide whether it is true. The
generated `def` is a normal declaration, so:

* it is type-checked by the kernel like any other definition;
* it is inspectable (`#print`);
* anything proved about it is proved by the ordinary kernel, and is audited by
  `GeoDaTest/Axioms.lean` like everything else.

There is no separate compiler, no serialized intermediate representation and no
trusted oracle, because there is nothing here that could be one. That is the whole
argument for this design over an external DSL — see `docs/DSL-RFC.md`.

## What the command checks

Two things, both of which Lean would otherwise let through silently.

* **Undeclared identifiers.** The generated definition is elaborated under
  `set_option autoImplicit false`, so a coefficient that appears in the equation but
  not in the binder list is a hard error rather than a silently introduced implicit
  parameter. Writing `y = ρ • (W *ᵥ y) + …` without declaring `(ρ : ℝ)` would
  otherwise produce a *different* model than intended, with `ρ` as an invisible
  argument — exactly the "silently strengthening the hypotheses" failure this
  project is meant to avoid.
* **Inconsistent dimensions.** The declared slot types are inspected and their row
  dimensions compared. Lean itself catches a mismatch wherever the slots *meet* in
  the equation, but not a slot whose dimension is never pinned down by the equation;
  the command reports both, naming the slots and the dimensions involved.

## Limits

Stated here and argued in the RFC. The command generates a *definition* and nothing
else: no theorems, no assumptions, no proof search. It cannot know whether the
equation you wrote is the model you meant. It does not check that the weights matrix
is row-standardized, nonnegative or connected — those are the predicates of
`GeoDa.SpatialWeights`, to be required by the theorems that need them, not by the
syntax that names the model.
-/

open Lean Elab Command Term Meta

namespace GeoDa

/-- Declare a spatial model by its structural equation.

`spatial_model Name (binders) : equation` generates `def Name (binders) : Prop :=
equation`. The binder list may declare the dimensions as well as the slots; see the
module docstring for what is checked. -/
syntax (name := spatialModelCmd) "spatial_model " ident bracketedBinder* " : " term : command

namespace SpatialModel

/-- A slot shape, as far as this command cares about it: the row dimension, and the
column dimension when the slot is a matrix. Both are `Expr`s rather than `Nat`s
because a dimension is usually a variable such as `n`. -/
structure Shape where
  /-- The first index of a `Matrix`, or the index of a vector. -/
  row : Expr
  /-- The second index of a `Matrix`; `none` for a vector. -/
  col : Option Expr
  deriving Inhabited

/-- Recover a slot's shape from its type, or `none` when the type is not a vector or
matrix of the expected form.

Recognised are `Matrix (Fin a) (Fin b) α` (and its `WMat`/`DMat` abbreviations) and
`Fin a → α` (and its `Vec` abbreviation), directly or after unfolding. Anything else
— a scalar, a list, a user-defined type — yields `none` and is simply not
dimension-checked, so the command stays usable for slots this design did not foresee.
-/
def shapeOf (ty : Expr) : MetaM (Option Shape) := do
  let ty ← whnf ty
  let (fn, args) := ty.getAppFnArgs
  if fn == ``Matrix && args.size == 3 then
    let .app (.const ``Fin _) a := args[0]! | return none
    let .app (.const ``Fin _) b := args[1]! | return none
    return some { row := a, col := some b }
  if fn == ``Vec && args.size == 1 then
    let .app (.const ``Fin _) a := args[0]! | return none
    return some { row := a, col := none }
  -- `Vec n` and `WMat n` may already have unfolded into a `Pi` type.
  if ty.isForall then
    let .forallE _ dom _ _ := ty | return none
    let .app (.const ``Fin _) a := dom | return none
    match ty.bindingBody! with
    | .forallE _ dom2 _ _ =>
      if let .app (.const ``Fin _) b := dom2 then
        return some { row := a, col := some b }
      return none
    | _ => return some { row := a, col := none }
  return none

/-- Pretty-print a dimension for an error message. Uses the local context, so a
dimension declared as `{n k : ℕ}` is reported as `n`, not as `_uniq.6`. -/
def dimStr (e : Expr) : MetaM MessageData := do
  if let some id := e.fvarId? then
    if let some d := (← getLCtx).find? id then
      return m!"{d.userName}"
  return m!"{e}"

/-- The three groups a spatial model's slots fall into, by shape. -/
structure Slots where
  /-- Matrix slots whose row and column dimensions are the same expression: `W`. -/
  squares : Array (Name × Shape) := #[]
  /-- Matrix slots whose dimensions differ: `X`, and the lagged design `W * X`. -/
  rects : Array (Name × Shape) := #[]
  /-- Vector slots: `y`, `u`, `ε`, and the coefficient vectors `β`, `θ`. -/
  vecs : Array (Name × Shape) := #[]

/-- Sort the declared slots by shape. A slot whose type this design does not
recognise was never added, so it is neither checked nor complained about. -/
def classify (found : Array (Name × Shape)) : Slots := Id.run do
  let mut out : Slots := {}
  for (nm, sh) in found do
    match sh.col with
    | none => out := { out with vecs := out.vecs.push (nm, sh) }
    | some c =>
      if c.equal sh.row then
        out := { out with squares := out.squares.push (nm, sh) }
      else
        out := { out with rects := out.rects.push (nm, sh) }
  return out

end SpatialModel

open SpatialModel

/-- Elaborate the declared slots and check that their dimensions agree.

The rule is the one the GNS slot shapes impose. Some slot fixes the row dimension `n`
— the square weights matrix `W` if there is one, otherwise the first matrix, otherwise
the first vector. Every other slot's row dimension must then be either `n` or the
column dimension `k` of the design matrix. Nothing here is re-derived from the
equation: this only catches a slot whose dimension the equation never pins down,
which is precisely the case Lean's own type checker cannot see.
-/
private def checkShapes (binders : Array Syntax) : CommandElabM Unit := do
  liftTermElabM do
    elabBinders binders fun fvars => do
      let mut found : Array (Name × Shape) := #[]
      for fv in fvars do
        let some id := fv.fvarId? | continue
        let some decl := (← getLCtx).find? id | continue
        let ty ← instantiateMVars decl.type
        if let some sh ← shapeOf ty then
          found := found.push (decl.userName, sh)
      let sl := classify found
      let nOpt :=
        (sl.squares.map (·.2.row)).toList.head?
          <|> (sl.rects.map (·.2.row)).toList.head?
          <|> (sl.vecs.map (·.2.row)).toList.head?
      let some nE := nOpt | return
      let nName :=
        (sl.squares.toList.head?.map (·.1))
          <|> (sl.rects.toList.head?.map (·.1))
          <|> (sl.vecs.toList.head?.map (·.1))
      let nWho := nName.getD `n
      for (nm, sh) in sl.squares ++ sl.rects do
        unless sh.row.equal nE do
          let got ← dimStr sh.row
          let want ← dimStr nE
          throwError "spatial_model: the slot {nm} has row dimension {got}, but \
            {nWho} fixes the row dimension to {want}; every vector and matrix slot of \
            a spatial model must have the same row dimension"
      -- `k`: the common column dimension of the rectangular (design) matrices.
      let mut kE : Option (Name × Expr) := none
      for (nm, sh) in sl.rects do
        let c := sh.col.get!
        match kE with
        | none => kE := some (nm, c)
        | some (km, kc) =>
          unless c.equal kc do
            let got ← dimStr c
            let want ← dimStr kc
            throwError "spatial_model: the design matrices {km} and {nm} have \
              different column dimensions ({want} and {got})"
      for (nm, sh) in sl.vecs do
        let okN := sh.row.equal nE
        let okK := match kE with
          | some (_, kc) => sh.row.equal kc
          | none => false
        unless okN || okK do
          let got ← dimStr sh.row
          let nStr ← dimStr nE
          let kStr ← match kE with
            | some (_, kc) => dimStr kc
            | none => pure m!"(no design matrix, so no k)"
          throwError "spatial_model: the vector slot {nm} has dimension {got}, which \
            is neither the row dimension {nStr} nor the coefficient dimension {kStr}"

/-- The `spatial_model` command. -/
elab_rules : command
  | `(spatial_model $name:ident $binders:bracketedBinder* : $eq:term) => do
    checkShapes binders
    let defCmd ← `(command|
      set_option autoImplicit false in
      /-- Declared by `spatial_model` from the structural equation
      `$eq`. Generated, not interpreted: it is an ordinary Lean definition. -/
      def $name $binders* : Prop := $eq)
    elabCommand defCmd

end GeoDa
