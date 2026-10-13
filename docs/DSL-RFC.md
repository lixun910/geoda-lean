# RFC: a minimal Lean-native DSL for spatial model specifications

Status: **accepted and implemented** in `GeoDa/DSL.lean`, tested in `GeoDaTest/DSL.lean`.

## 1. Summary

Add one command, `spatial_model`, that turns a model's structural equation into an
ordinary Lean `def`. The design is the *Lean-native* option: no new language, no
serialized intermediate representation, no separate compiler. The generated `def` is
elaborated and type-checked by Lean's own elaborator and kernel, so there is no trust
boundary to argue about — there is nothing in the design that could be one.

The command additionally rejects two failures that Lean would otherwise let through
silently: a coefficient used in the equation but not declared, and a slot whose
dimension is inconsistent with the rest.

## 2. Motivation

To add a model today you write the equation out again, with its binder list, and then
re-derive anything you want to say about it. The equation is one line; the surrounding
declaration and the parameter order are boilerplate. That is tolerable at four models
and becomes a liability at twenty.

The failure mode that matters is not verbosity, though. It is that a *near-miss* in the
boilerplate is silent. Two of them are real, and both were hit while building this
repository:

* **An undeclared coefficient.** Writing `y = ρ • (W *ᵥ y) + …` without `(ρ : ℝ)` in the
  binder list does not fail. With Lean's default `autoImplicit`, `ρ` becomes an
  *implicit* parameter of the definition. The result is a different model than the one
  written, with an invisible argument, and every downstream proof still goes through.
  This is the same failure as "silently strengthening the hypotheses" that
  `CLAUDE.md` warns about, arriving through the syntax instead of through a theorem.
* **A dimension the equation never pins down.** Lean catches a dimension mismatch
  wherever the slots *meet* in the equation. A slot that is declared and used only in a
  position that determines its dimension by unification will not be caught, and a
  `WMat m` where `WMat n` was meant goes unnoticed.

A DSL that does not close these two is not worth having: it produces plausible
definitions that are not the ones you meant.

## 3. Requirements

1. **R1 — Small.** The specification must fit in a page, and the implementation should
   be readable by someone who knows Lean's elaborator API only a little.
2. **R2 — Generated claims are checked, not trusted.** Whatever comes out must be
   verified by the kernel. No appeal to the generator's correctness.
3. **R3 — Inspectable.** `#print` on a generated definition must show something a
   reader can check against the RFC.
4. **R4 — Reuse, not restate.** Declaring SAR must produce the same thing as
   `GeoDa.SARDes`, mechanically — not "the same up to the reader's attention".
5. **R5 — Reject the two silent failures of §2**, with a message that names the slot.
6. **R6 — No new trusted component.** The audit in `GeoDaTest/Axioms.lean` must remain
   the whole story about what a proof depends on.

## 4. The options

### (A) Lean 4 macros and elaborators — **chosen**

The syntax and the definition live in Lean. The command parses the equation, runs two
checks over the elaborated declarations, and generates a `def` which Lean then
elaborates normally.

* R1: the implementation is about 150 lines, most of it error messages.
* R2, R3, R6: satisfied by construction. There is no generated artifact that Lean does
  not elaborate, and the audit is unaffected.
* R4: satisfied *maximally* — the generated definition can be proved equal to the
  hand-written one by `rfl` (§7).
* R5: satisfied by the two checks of §6.2, both of which run before the `def` is
  elaborated, so a rejected model leaves nothing behind.
* Cost: the user must enable nothing, install nothing, and learn one command. The
  price is that the DSL is *Lean syntax*, so its surface form is constrained by Lean's
  parser (§8).

### (B) An external typed DSL with a deterministic compiler

A separate language (JSON, YAML, TOML, a bespoke grammar) plus a generator emitting
Lean source.

* R2 is the problem. Either the emitted source is trusted — which forfeits R2 outright,
  since the generator becomes a trusted component — or it is checked, in which case the
  external layer has bought nothing over (A) and cost a second language, a second
  parser, a second error-reporting surface, and a serialization format to version.
* R3 degrades: the reader now has to trust that the checked source corresponds to the
  external specification, which is a second correspondence to verify.
* R1 fails on its face: the smallest rigorous version of (B) is strictly larger than
  (A), and the additional rigour is all in *not* being trusted.
* Where (B) would win is authoring by non-Lean tools — a web form, a notebook, a
  different language's runtime. That is a real use case, and it is not this issue.

### (C) Ordinary Lean structures, no new syntax

Define a structure recording the slots and an interpretation function, so that a model
is data.

* Smallest specification of the three, and it needs no metaprogramming at all.
* But a model then has **two** representations — the structure and the `Prop` — and R4
  becomes "prove the interpretation of this data is the intended equation", which is
  exactly the thing a DSL was supposed to save you from writing.
* The equations are also no longer readable as equations: the model becomes values of
  a record type, and a reader cannot check it against the mathematics at a glance.
  Failing R3 and R4 to buy R1 is a bad trade for this project, whose central discipline
  is that statements are legible and load-bearing.

## 5. Decision

**(A)**, with the scope deliberately cut to the smallest thing that closes §2's two
silent failures and nothing more. Concretely, the command generates a *definition* and
no theorems, performs no proof search, and does not attempt to check the mathematics.

## 6. Specification

### 6.1 Syntax

```
spatial_model <Name> <binders> : <equation>
```

`<binders>` is Lean's ordinary bracketed binder list, so `(x : α)`, `{x : α}` and
`{n k : ℕ}` all work. `<equation>` is an ordinary Lean term of type `Prop`. The command
generates

```
def <Name> <binders> : Prop := <equation>
```

as a normal declaration. Illustrative:

```
spatial_model MySAR {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) (ρ : ℝ) : y = ρ • (W *ᵥ y) + X *ᵥ β + ε
```

```
spatial_model MySLX {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (ε : Vec n) : y = X *ᵥ β + (W * X) *ᵥ θ + ε
```

A multi-equation model is written with `∧`, matching how `SEMDes` and `GNSDes` are
already written:

```
spatial_model MySEM {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (u : Vec n) (ε : Vec n) (lam : ℝ) : y = X *ᵥ β + u ∧ u = lam • (W *ᵥ u) + ε
```

### 6.2 Semantics of the two checks

Both run over the *elaborated* binders, in order, so each slot's type is inspected in
the context of the dimensions declared before it.

**Undeclared identifiers.** The generated `def` is elaborated under
`set_option autoImplicit false`, scoped to that declaration. A coefficient missing from
the binder list is therefore an `Unknown identifier` error rather than a silently
introduced implicit parameter. This is the whole of the fix for §2's first failure.

**Dimension consistency.** Slot types of the recognised forms are classified by shape:

| form | meaning |
| --- | --- |
| `Matrix (Fin a) (Fin a) α` | square matrix, row dimension `a` |
| `Matrix (Fin a) (Fin b) α` | rectangular matrix, rows `a`, columns `b` |
| `Fin a → α` | vector, dimension `a` |

(`WMat`, `DMat` and `Vec` are abbreviations of these, and are recognised after
unfolding.) The rule is the one the GNS slot shapes impose:

1. Some slot fixes the row dimension `n`: the square matrix if there is one, otherwise
   the first matrix, otherwise the first vector.
2. Every other matrix's row dimension must be `n`.
3. The rectangular matrices' column dimensions must all agree; that common value is `k`.
4. Every vector slot's dimension must be `n` or `k`.

Anything that violates this is an error naming the offending slot and the two
dimensions involved. A slot of a type this design does not recognise is neither checked
nor complained about, so the command stays usable for slot types it did not foresee.

**Nothing here re-derives mathematics from the equation.** The check only catches a
slot whose dimension the equation never pins down, which is exactly the case Lean's own
type checker cannot see. Everything else — that the equation type-checks, that the
slots are used consistently, that the whole `Prop` is well formed — is Lean's job, and
the command does not duplicate it.

### 6.3 What it deliberately does not do

* It does **not** generate theorems, and it does not prove anything. It cannot: whether
  the equation you wrote is the model you meant is not a formal property.
* It does **not** check that the weights matrix is row-standardized, nonnegative,
  connected, or has a zero diagonal. Those are the predicates of
  `GeoDa.SpatialWeights`, and they belong to the theorems that need them, not to the
  syntax that names a model. Requiring them here would silently strengthen every model
  declared through the DSL.
* It does **not** check that the dimensions are what the *literature* would call `n`
  and `k`; only that they are consistent with each other.
* It does **not** interpret the equation. There is no normal form, no rewriting, no
  simplification. The equation you write is the body you get.

## 7. Equivalence to the hand-written specifications

This is the criterion that decides whether the DSL is a convenience or a liability, and
it is checked mechanically rather than argued. Because the generated `def` has the same
binder list and the same body as the hand-written one, the equality is `rfl`:

```
theorem myGNS_eq_GNSDes : @MyGNS = @GNSDes := rfl
```

Not "provably equivalent" — *the same function*, up to definitional equality. `rfl` is
the strongest form the criterion can take, and it fails the build the moment the DSL
starts adding, dropping or reordering anything.

For `SAR`, `SDM`, `SEM` and `GNS` all four are established in `GeoDaTest/DSL.lean`, and
they are audited in `GeoDaTest/Axioms.lean` like every other main theorem.

## 8. Trust boundary

The security and trust question for a DSL is: *what does a user have to trust in order
for a generated claim to be believed?* For this design the answer is **nothing beyond
Lean itself**, and that is the point of choosing (A).

* The command emits Lean syntax, which Lean elaborates. There is no unverified
  translation step, because there is no translation step.
* The generated declaration lands in the ordinary environment. `#print` shows it,
  `#check` pins it, and `GeoDaTest/Axioms.lean` audits its axiom footprint exactly as
  for a hand-written definition.
* The two checks of §6.2 can only ever *reject*; they cannot change what is generated.
  A bug in `checkShapes` could therefore make the command refuse a good model, but
  could not make it accept a wrong one — the generated `def` is checked either way.
* There is no proof search and no tactic invocation, so there is no place for an
  unverified step to hide.

For contrast, the trust story under (B) would require: the external specification means
what we say it means; the compiler is deterministic and correct; the emitted source is
what the user's specification describes; and only *then* Lean verifies the emitted
source. Three of those four are informal, and none of them are needed here.

What a user *does* still have to trust is the same thing they trust when writing the
`def` by hand: that the equation is the model they had in mind. The DSL does not and
cannot help with that, and §6.2's second check is deliberately the only place where it
goes beyond syntax.

## 9. Limits

* **The surface syntax is Lean's.** A docstring cannot precede a `spatial_model`
  invocation (Lean's parser attaches docstrings to declarations, and this is not one).
  Use a `--` comment, or let the generated `def` carry the docstring, which it does.
* **The body must be a single `Prop`.** Multi-equation models use `∧`. This is not a
  limitation in practice, since the existing definitions are written that way.
* **The dimension rule assumes the GNS slot shapes.** A model whose matrices are not
  `n × n` and `n × k` will be rejected or misclassified. This is stated in §6.2 rather
  than papered over; the alternative is a general dependent type checker, which is not
  in scope and would duplicate Lean's.
* **Only the definition is generated.** Nesting theorems, reduced forms and the
  equivalence-to-reference lemma are still written by hand. Generating *statements* is
  a plausible next step; generating *proofs* is not something this design should
  attempt.
* **`λ` cannot be used as an identifier**, so the spatial-error parameter is `lam`
  throughout. The existing sources already do this; the DSL inherits it.

## 10. Evidence

* `GeoDa/DSL.lean` — the command. `GeoDaTest/DSL.lean` — the tests.
* Four models are proved equal to their hand-written counterparts by `rfl`, and a fifth
  model (`MySLX`) with no counterpart in the repository is declared and used, in both
  cases without touching an existing file.
* Three rejections are pinned with `#guard_msgs`: an inconsistent row dimension, a
  vector slot whose dimension is neither `n` nor `k`, and an undeclared coefficient —
  plus a plain type error, to show Lean's own error still applies.
* `./scripts/verify.sh` builds everything, finds no `sorry`/`admit`, and audits all 87
  main theorems, the DSL's included, against the standard three axioms.

## 11. Open questions

1. Should the command generate the *equivalence* lemma to a named reference
   automatically, e.g. `spatial_model MySAR … referencing SARDes := …`? It would save
   one `rfl` line; it would also couple the DSL to a naming convention.
2. Should generated statements (nesting, reduced form) be templated? The obstacle is
   that "reduced form of this model" is not a syntactic operation on the equation — it
   needs the model to be *recognised*, which reintroduces the interpretation this design
   avoids.
3. Is the dimension rule of §6.2 the right one, or should it be relaxed to "all matrix
   rows agree, and each vector is either a row or a column dimension"? The current rule
   is the stricter of the two and has not yet been in the way.
