# PDF ↔ Lean correspondence

Click-through for referees: [REVIEW.md](REVIEW.md).

Source PDF: `paper/main.pdf`.

## Reviewer surface (only these need statement checking)

| PDF | Lean |
|-----|------|
| Theorem 1 (`thm:main`) | `RMFLean.MomentDichotomy` in `lean/RMFLean/Trusted/MainTheorem.lean` |
| Corollary (`thm:cor-clt`) | `RMFLean.CentralLimit` in `lean/RMFLean/Trusted/Corollary.lean` (moments: `CentralLimitMoments`) |
| Definitions of `S_N`, `U_s`, `ℳ_s`, mixed moments, `V`, `ℱ_i`, `S_g`, `C^∞[N]`, `𝒬` | `lean/RMFLean/Trusted/Defs.lean` |
| Lemma 1 (`lem:divisor`) | `lean/RMFLean/Trusted/DivisorSums.lean` (`divisor_sum_bound`, `divisor_sum_sq_bound`, `divisor_tail_bound`, `divisor_sum_div_bound`) |
| Lemma 2 (`lem:moment-formula`) | definition of `U` in `lean/RMFLean/Trusted/Defs.lean`; theorem `moment_formula` in `lean/RMFLean/Trusted/Axioms.lean` |
| Lemma 6 (`lem:diophantine-nil`) | `lean/RMFLean/Trusted/Axioms.lean` (`exponential_dichotomy`) |

PDF Lemma 5 is the Waring count (Green–Tao, Möbius paper, Lemma 3.3). It is used only inside the paper’s proof of Lemma 6 and is not an axiom.

## Proof skeleton (implementation; not required for statement audit)

| PDF | Lean module |
|-----|-------------|
| §2.1 `V`, `ℱ_i` | `lean/RMFLean/Proof/Setup/SolutionSet.lean` |
| Lemma 3 sparse complement | `lean/RMFLean/Proof/Setup/SparseComplement.lean` |
| Lemma 4 effective recurrence, Lemma 5 Waring | not formalised; used in the paper’s proof of Lemma 6 |
| Lemma 6 exponential dichotomy | axiom `exponential_dichotomy` (`Lem5Cd` is the historical Lean name for this \(C_d\)) |
| Lemma 7 matrix param | `lean/RMFLean/Proof/Param/MatrixParam.lean` |
| Lemma 8 `J_1` | `lean/RMFLean/Proof/F1/J1.lean` / `J1LongShort.lean` |
| Lemma 9 `J_2` | `lean/RMFLean/Proof/F1/J2.lean` |
| Proposition 1 + Remark 2 | `lean/RMFLean/Proof/F1/PropF1.lean` |
| Lemma 10 intersection param | `lean/RMFLean/Proof/Param/IntersectionParam.lean` |
| Lemma 11 `I_1` | `lean/RMFLean/Proof/Intersection/I1*.lean`, `I1Bound.lean` |
| Lemma 12 `I_2` | `lean/RMFLean/Proof/Intersection/I2.lean` / `I2Fibre.lean` |
| Proposition 2 | `lean/RMFLean/Proof/Intersection/PropIntersection.lean` |
| §2.6 assembly → Theorem 1 | `lean/RMFLean/Proof/Assemble/Main.lean` (`momentDichotomy`) |
| Corollary proof (`thm:cor-clt`) | `lean/RMFLean/Proof/Assemble/Corollary.lean` (`centralLimit` / `centralLimitMoments`), mixed half in `CorollaryMixed.lean` |

## Trusted axioms

Lemma **6** is an axiom on the reviewer surface (`lean/RMFLean/Trusted/Axioms.lean`).
Lemma 1 is a theorem in `lean/RMFLean/Trusted/DivisorSums.lean`.
Lemma 2 is the definition of `U` as `Re S_g(V)` (plus a short proof that the sum is real).
Gut, *Probability: a graduate course*, Chapter 5, Theorem 8.6 (moment method) is the axiom
`billingsley_method_of_moments` in `lean/RMFLean/Trusted/Corollary.lean`: even and mixed moments matching
the circularly symmetric complex normal imply convergence in law.
Theorem 1 is proved from the paper’s Propositions 1–2 and assembly, admitting Lemma 6.
