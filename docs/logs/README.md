# Compiler logs from the session that produced this repository

Primary-source record of the compile/fix iterations. Kept because the README's
"Provenance" section makes claims about what the compiler caught in the original
draft, and this is the evidence for them.

| file | what it is |
| --- | --- |
| `verify-final.log` | a clean, complete run of `./scripts/verify.sh` (exit 0) |
| `compile-lake-update.log` | first `lake update` — materialising Lean v4.35.0 + Mathlib |
| `compile-build.log` | **first** build of the pre-existing draft: the `λ` parse errors |
| `compile-build2.log` … `compile-build11.log` | successive build attempts while the proofs were repaired |

The numbering is chronological, not the number of successful builds: `build.log`
is the first attempt, `build11.log` is the last failing one. Most iterations were
run against a single file, so the same log appears to repeat itself.

Two things worth reading directly:

* `compile-build.log` — `unexpected token 'λ'` at three places. The draft bound
  the disturbance coefficient as `λ`, which is Lean's lambda token and cannot be
  an identifier, so the file could not be parsed at all. This is why "it was
  never compiled" is a claim and not an inference: the compiler says so.
* `compile-build2.log` onwards — the `simp`-based nesting proofs leaving goals of
  the form `(P ∧ Q) ↔ (R ∧ Q)`, which `simp` does not close. The eventual proofs
  are deliberately independent of `simp`'s normal form.

Caveat on the logs: the file paths in them are sandbox-internal
(`/sessions/…`), and they were produced on a Linux VM, not on the machine that
now holds this repository. They are evidence of *what the compiler reported*, not
a reproducible build transcript — for that, run `./scripts/verify.sh`.
