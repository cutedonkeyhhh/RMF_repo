/-
# Trusted main theorem statement (PDF Theorem 1)

**Reviewer checklist:** compare this file together with `Defs.lean` and `Axioms.lean`
to `D:/RMF_file/main.pdf`, Theorem 1 (`thm:main`).

The proof is in `RMFLean/Proof/Assemble/Main.lean` and is not part of the
statement-correspondence obligation.
-/
import RMFLean.Trusted.Axioms
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real Nat

namespace RMFLean

/-- Gaussian target `s!` in PDF Theorem 1, alternative (1). -/
def gaussianMoment (s : ℕ) : ℝ := (s.factorial : ℝ)

/--
Error factor in PDF Theorem 1, alternative (1):
`(2s log N)^{3s²}`.
-/
noncomputable def momentErrorFactor (N s : ℕ) : ℝ :=
  tailQ N s

/--
Basic range for PDF Theorem 1 at a given `N` and `s`: `2 ≤ s` and `N ≥ 3`
(so logarithms in error factors are defined).  Any further growth restriction
on `s` relative to `N` is absorbed into "`N` sufficiently large" depending on `s`.
-/
def inMomentRange (N s : ℕ) : Prop :=
  2 ≤ s ∧ 3 ≤ N

/--
Internal Cauchy--Schwarz packaging, not the PDF statement:
`|𝔼|S_N|^{2s} - s!| ≤ Cll · δ^{1/2} (2s log N)^{3s²}`.
The exported form `altGaussian` follows on replacing `δ` by `δ²`.
-/
def altGaussianSqrt (d N s : ℕ) (g : CirclePoly d) (δ Cll : ℝ) : Prop :=
  |M d s N g - gaussianMoment s| ≤ Cll * (Real.sqrt δ * momentErrorFactor N s)

/--
PDF Theorem 1, alternative (1):
`|𝔼|S_N|^{2s} - s!| ≤ Cll · δ (2s log N)^{3s²}`.

The Vinogradov constant `Cll` is quantified *outside* `∀ N, δ, g`
(see `MomentDichotomy`), so it may depend on `d,s` but not on `N,δ,g`.

Encoded via `M d s N g = ℳ_s(N)`, with `U` defined as `Re S_g(V)`
(the combinatorial expansion of the Steinhaus moment).
-/
def altGaussian (d N s : ℕ) (g : CirclePoly d) (δ Cll : ℝ) : Prop :=
  |M d s N g - gaussianMoment s| ≤ Cll * (δ * momentErrorFactor N s)

/--
PDF Theorem 1, alternative (2), with fixed exponent `Cd`
(standing for the PDF's `O_d(1)`, depending only on `d`):
exists nonzero `k` with `|k| ≤ δ^{-Cd}` and `‖k g‖_{C^∞[N]} ≤ δ^{-Cd}`.
-/
def altDiophantine (d N : ℕ) (g : CirclePoly d) (δ Cd : ℝ) : Prop :=
  ∃ k : ℤ, k ≠ 0 ∧
    (|k| : ℝ) ≤ Real.rpow δ (-Cd) ∧
    (k • g).cInfinityNorm N ≤ Real.rpow δ (-Cd)

/--
Larger Diophantine exponent is a weaker alternative: if `0 < δ < 1` and
`Cd ≤ Cd'`, then `δ^{-Cd} ≤ δ^{-Cd'}`.
-/
theorem altDiophantine_mono {d N : ℕ} {g : CirclePoly d} {δ Cd Cd' : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hCd : Cd ≤ Cd')
    (h : altDiophantine d N g δ Cd) :
    altDiophantine d N g δ Cd' := by
  obtain ⟨k, hk0, hk, hg⟩ := h
  have hpow : Real.rpow δ (-Cd) ≤ Real.rpow δ (-Cd') :=
    Real.rpow_le_rpow_of_exponent_ge hδ (le_of_lt hδ1) (neg_le_neg hCd)
  exact ⟨k, hk0, hk.trans hpow, hg.trans hpow⟩

/--
PDF Theorem 1 (`thm:main`) — Moment dichotomy (statement only).

Quantifier order matches the PDF:
there exists `C_d > 0` (the PDF's `O_d(1)`), and for every `s ≥ 2` there
exist `Cll = Cll(d,s) > 0` (the Vinogradov `≪_s` constant) and
`C = C(d,s) > 0`, such that for all sufficiently large `N`
and every `δ` with `N^{-C} < δ < 1/8`, **for every** polynomial `g` of
degree `d`, at least one of the following holds:
1. `|𝔼|S_N|^{2s} - s!| ≤ Cll · δ (2s log N)^{3s²}`;
2. exists nonzero `k` with `|k| ≤ δ^{-C_d}` and
   `‖k g‖_{C^∞[N]} ≤ δ^{-C_d}`.

The upper cut `δ < 1/8` matches Lemma 6 / Propositions 1–2 (the paper's
proof regime). In particular `Cll`, `C` and `C_d` do **not** depend on `g`
(nor on `N,δ`).
-/
def MomentDichotomy (d : ℕ) : Prop :=
  ∃ Cd : ℝ, 0 < Cd ∧
    ∀ s : ℕ, 2 ≤ s →
      ∃ Cll : ℝ, 0 < Cll ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N0 : ℕ,
            ∀ N : ℕ, N0 ≤ N →
              inMomentRange N s →
                ∀ δ : ℝ, Real.rpow (N : ℝ) (-C) < δ →
                  δ < 1 / 8 →
                    ∀ g : CirclePoly d,
                      altGaussian d N s g δ Cll ∨ altDiophantine d N g δ Cd

end RMFLean
