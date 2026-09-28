# Review trail

If you want to check if the lean code matches the statements in PDF, you can complete the check by clicking through the links in this file one by one.

You don't need to read `lean/RMFLean/Proof/` unless you want the implementation.

Repo: [cutedonkeyhhh/RMF_repo](https://github.com/cutedonkeyhhh/RMF_repo)

---

## 1. Symbols

[lean/RMFLean/Trusted/Defs.lean](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean)

| PDF | Lean |
|-----|------|
| polynomial \(g\), \(e(g(n))\) | [`CirclePoly`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L43), [`ePhase`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L55) |
| \(\|g\|_{C^\infty[N]}\) | [`cInfinityNorm`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L76) |
| solution set \(V\) | [`Sol`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L90) |
| \(U_s(N)\), \(\mathcal{M}_s(N)=\mathbb{E}\|S_N\|^{2s}\) | [`U`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L274), [`M`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L278) |
| mixed moment \(\mathbb{E}[S_N^{s_1}\overline{S_N}^{s_2}]\) | [`mixedM`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L285) |

Next: [Lemma 1 and Lemma 6](#2-lemma-1-theorem-and-lemma-6-axiom)

---

## 2. Lemma 1 (theorem) and Lemma 6 (axiom)

Lemma 1 is proved in [`DivisorSums.lean`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/DivisorSums.lean). Lemma 6 remains an axiom in [`Axioms.lean`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Axioms.lean).

| PDF | Lean |
|-----|------|
| Lemma 1 (`lem:divisor`) | [`divisor_sum_bound`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/DivisorSums.lean#L350), `divisor_sum_sq_bound`, `divisor_tail_bound`, `divisor_sum_div_bound` |
| Lemma 2 (`lem:moment-formula`) | not an axiom: [`U`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Defs.lean#L274) *is* \(\operatorname{Re} S_g(V)\); [`moment_formula`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Axioms.lean#L65) is a short proof that the sum is real |
| Lemma 6 (`lem:diophantine-nil`) | [`exponential_dichotomy`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Axioms.lean#L189) |

The remaining number-theoretic fact taken as given is Lemma 6. The paper already sketches it. The corollary additionally admits the moment method (`billingsley_method_of_moments` in `Corollary.lean`).

Next: [Theorem 1](#3-theorem-1)

---

## 3. Theorem 1

[lean/RMFLean/Trusted/MainTheorem.lean](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/MainTheorem.lean#L91)

PDF `thm:main` ↔ [`MomentDichotomy`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/MainTheorem.lean#L91)

Check: alternatives (1) Gaussian moment / (2) Diophantine; quantifiers \(C_d\), then \(s\), then \(C_{\ell\ell}\), \(C\), \(N_0\); \(\delta\) window \(N^{-C}<\delta<1/8\); constants independent of \(g\).

Next: [Corollary](#4-corollary)

---

## 4. Corollary

[lean/RMFLean/Trusted/Corollary.lean](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Corollary.lean)

| PDF | Lean |
|-----|------|
| [Diophantine hypothesis](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Corollary.lean#L67) \(\forall\varepsilon>0\,\exists C>0:\;\max_i\lVert q\beta_i\rVert\ge C\exp(-|q|^\varepsilon)\) | [`coeffDiophantine`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Corollary.lean#L67) |
| \(S_N\) converges in law to \(\mathcal{CN}(0,1)\) | [`CentralLimit`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Corollary.lean#L132) |
| Gut, Chapter 5, Theorem 8.6 | [`billingsley_method_of_moments`](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/lean/RMFLean/Trusted/Corollary.lean#L120) |

The number theory proves even/mixed moments; Gut Theorem 8.6 is cited, not proved.

Done. If the four files match the PDF, the statement obligation is finished.

---

## Optional

Label-by-label table: [CORRESPONDENCE.md](https://github.com/cutedonkeyhhh/RMF_repo/blob/main/CORRESPONDENCE.md).

From `lean/`, `lake build RMFLean.Proof.Assemble.Main` and `lake build RMFLean.Proof.Assemble.Corollary` check that the proofs compile from Lemma 1 (theorem) and the axioms above.
