# RMF_lean

Lean 4 formalization of
*Moments of random multiplicative functions with polynomial phases on the circle*

The repository contains the paper (`paper/`) and a Lake project (`lean/`).
The main theorem proved in Lean is stated below. The corollary is proved as well.
The development takes three inputs as given, as explained under Build and check.
Two of these are Lean axioms; Lemma 2 is represented definitionally.
To compare the statements with the PDF, click through [REVIEW.md](REVIEW.md).
Label-by-label names are in [CORRESPONDENCE.md](CORRESPONDENCE.md).

## Main theorem

The following is the main theorem proved in Lean.

Let $d\ge 0$ be an integer. There exists a real number $C_d>0$ such that for every integer $s\ge 2$ there exist real numbers $C_{\ell\ell}>0$ and $C>0$, and an integer $N_0$, for which the following holds. Let $N\ge\max(N_0,3)$ be an integer and let $\delta$ be a real number with $N^{-C}<\delta<1/8$. Let $g(n)=\sum_{j=0}^d\beta_j n^j$ be a polynomial with real coefficients, and write $e(x)=\exp(2\pi i x)$. Define

$$
\mathcal{M}_s(N)=N^{-s}\sum_{1\le n_i,m_i\le N \atop n_1\cdots n_s=m_1\cdots m_s}\prod_{i=1}^s e(g(n_i))\,\overline{e(g(m_i))},
$$

where the sum runs over integers $n_1,\ldots,n_s,m_1,\ldots,m_s$, and $\log$ denotes the natural logarithm. Then at least one of the following holds.

1. $\bigl|\mathcal{M}_s(N)-s!\bigr|\le C_{\ell\ell}\,\delta\,(2s\log N)^{3s^2}$.
2. There exists a nonzero integer $k$ such that $|k|\le\delta^{-C_d}$ and $\|kg\|_{C^\infty\lbrack N\rbrack}\le\delta^{-C_d}$, where

$$
\|g\|_{C^\infty\lbrack N\rbrack}=\max_{1\le j\le d} N^j\,\|\beta_j\|_{\mathbb{R}/\mathbb{Z}}.
$$

and $\|x\|_{\mathbb{R}/\mathbb{Z}}$ is the distance from $x$ to the nearest integer. The polynomial $kg$ has coefficients $k\beta_j$.

The constants $C_{\ell\ell}$, $C$, and $N_0$ depend only on $d$ and $s$, and $C_d$ depends only on $d$.

Let $f$ be a Steinhaus random multiplicative function and let $S_N=N^{-1/2}\sum_{n\le N}f(n)\,e(g(n))$. Steinhaus orthogonality gives $\mathbb{E}\bigl[f(n)\overline{f(m)}\bigr]=\mathbf{1}_{n=m}$, and therefore $\mathcal{M}_s(N)=\mathbb{E}|S_N|^{2s}$. The dichotomy above is Theorem 1 of the paper.

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

- Lemma 2 (`lem:moment-formula`), the identification of the moment with the exponential sum over the product equation. The formalization defines `U` to be this finite sum, and `moment_formula` is then a theorem. The underlying probability space and Steinhaus orthogonality are not formalized.
- Lemma 6 (`lem:diophantine-nil`), the exponential dichotomy: `exponential_dichotomy` in `lean/RMFLean/Trusted/Axioms.lean`. The paper proves this lemma; the formalization takes the statement as an axiom.
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
