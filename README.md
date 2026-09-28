# RMF_lean

Lean 4 formalization of
*Moments of random multiplicative functions with polynomial phases on the circle*

The repository contains the paper (`paper/`) and a Lake project (`lean/`).
The main theorem proved in Lean is stated below. The corollary is proved as well.
The development takes three inputs as given, as explained under Build and check.
Two of these are Lean axioms; Lemma 2 is represented definitionally.
To compare the statements with the PDF, click through [REVIEW.md](REVIEW.md).
Label-by-label names are in [CORRESPONDENCE.md](CORRESPONDENCE.md).

## Formalized results

- `RMFLean.MomentDichotomy` formalizes Theorem 1 of the paper.
- `RMFLean.CentralLimit` formalizes the central limit theorem corollary; `RMFLean.CentralLimitMoments` records the corresponding moment convergence.

The exact mathematical statements are in [`paper/main.pdf`](paper/main.pdf).
For the correspondence between the paper and Lean declarations, see [REVIEW.md](REVIEW.md) and [CORRESPONDENCE.md](CORRESPONDENCE.md).

## Build and check

The toolchain is Lean 4 `v4.31.0` with Mathlib `v4.31.0` (`lean/lean-toolchain`, `lean/lakefile.toml`). Install [elan](https://github.com/leanprover/elan) if you do not already have it. Elan will download this toolchain on the first `lake` run.

```text
git clone https://github.com/cutedonkeyhhh/RMF_repo.git
cd RMF_repo/lean
lake exe cache get
lake build
```

`lake exe cache get` fetches the Mathlib oleans. `lake build` compiles the library, including the proofs of Theorem 1 and the corollary. A successful check is that the command finishes with no error.

To build only the two assembled theorems:

```text
lake build RMFLean.Proof.Assemble.Main
lake build RMFLean.Proof.Assemble.Corollary
```

Three inputs are taken as given.

- Lemma 2, the identification of the moment with the exponential sum over the product equation. The formalization defines `U` to be this finite sum, and `moment_formula` is then a theorem. The underlying probability space and Steinhaus orthogonality are not formalized.
- Lemma 6, the exponential dichotomy: `exponential_dichotomy` in `lean/RMFLean/Trusted/Axioms.lean`. The paper proves this lemma; the formalization takes the statement as an axiom.
- Gut, Chapter 5, Theorem 8.6 (method of moments), used only for the corollary: `billingsley_method_of_moments` in `lean/RMFLean/Trusted/Corollary.lean`.

The latter two inputs are Lean axioms. The rest of `Proof/` compiles from these inputs and Mathlib.

Compile the paper from `paper/` (`main.tex`, XeLaTeX).

## Layout

| Path | Content |
|------|---------|
| `paper/` | TeX sources, bibliography, and the compiled PDF |
| `lean/` | Lake project; run `lake` here |
| `lean/RMFLean/Trusted/` | Statements and axioms |
| `lean/RMFLean/Proof/Setup/` | $V$, $\mathscr{F}_i$, sparse complement, error shapes |
| `lean/RMFLean/Proof/F1/` | Proposition 1, $J_1$, $J_2$ |
| `lean/RMFLean/Proof/Intersection/` | Proposition 2, $I_1$, $I_2$ |
| `lean/RMFLean/Proof/Assemble/` | Assembling to prove the main theorem and the corollary |
| `CORRESPONDENCE.md` | PDF label and Lean name |
| `REVIEW.md` | Click-through for the statements |
