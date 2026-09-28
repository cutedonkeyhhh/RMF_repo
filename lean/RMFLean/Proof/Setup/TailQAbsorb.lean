/-
Analytic packaging: polylog factors are absorbed into `𝒬 = (2s log N)^{3s²}`.
-/
import RMFLean.Trusted.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section

open Real

namespace RMFLean

theorem log_N_gt_one {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) < Real.log N := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
  exact lt_of_lt_of_le hlog3
    (Real.log_le_log (by norm_num) (by exact_mod_cast hN))

theorem two_s_log_pos {N s : ℕ} (hs : 1 ≤ s) (hN : 3 ≤ N) :
    0 < 2 * (s : ℝ) * Real.log N := by
  have hlog := log_N_gt_one hN
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (Nat.succ_le_iff.mp hs)
  positivity

theorem tailQ_pos_of_three_le (N s : ℕ) (hN : 3 ≤ N) :
    0 < tailQ N s := by
  simp only [tailQ, tailQExp]
  have hs : 1 ≤ max s 1 := Nat.le_max_right _ _
  have hbase : 0 < 2 * (s : ℝ) * Real.log N ∨ s = 0 := by
    by_cases h : s = 0
    · exact Or.inr h
    · exact Or.inl (two_s_log_pos (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h)) hN)
  rcases hbase with hpos | rfl
  · exact pow_pos hpos _
  · simp

theorem tailQ_ge_one_of (N s : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N) :
    (1 : ℝ) ≤ tailQ N s := by
  simp only [tailQ, tailQExp]
  have hbase : (1 : ℝ) ≤ 2 * (s : ℝ) * Real.log N := by
    have hlog := log_N_gt_one hN
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  exact one_le_pow₀ hbase

/-- `(2s log N)^k ≤ 𝒬` when `k ≤ 3s²`. -/
theorem two_s_log_pow_le_tailQ (s N k : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hk : k ≤ tailQExp s) :
    (2 * (s : ℝ) * Real.log N) ^ k ≤ tailQ N s := by
  simp only [tailQ]
  have hbase : 1 ≤ 2 * (s : ℝ) * Real.log N := by
    have hlog := log_N_gt_one hN
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  exact pow_le_pow_right₀ hbase hk

/-- `(log N)^a ≤ 𝒬` when `a ≤ 3s²`. -/
theorem log_pow_le_tailQ_of_le (s N a : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (ha : a ≤ tailQExp s) :
    (Real.log N) ^ a ≤ tailQ N s := by
  have hlog0 : 0 ≤ Real.log N := le_of_lt (lt_trans (by norm_num) (log_N_gt_one hN))
  have hle : Real.log N ≤ 2 * (s : ℝ) * Real.log N := by
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith [log_N_gt_one hN, hs2]
  have hpow : (Real.log N) ^ a ≤ (2 * (s : ℝ) * Real.log N) ^ a :=
    pow_le_pow_left₀ hlog0 hle a
  exact hpow.trans (two_s_log_pow_le_tailQ s N a hs hN ha)

/-- Uniform multiplicative absorption of `(log N)^a` into `𝒬`. -/
theorem log_pow_le_mul_tailQ (s : ℕ) (hs : 2 ≤ s) (a : ℕ)
    (ha : a ≤ tailQExp s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        (Real.log N) ^ a ≤ K * tailQ N s :=
  ⟨1, by norm_num, fun N hN => by
    simpa using log_pow_le_tailQ_of_le s N a hs hN ha⟩

/-- `(A log N)^k ≤ 𝒬` when `k ≤ 3s²` and `A ≤ 2s`. -/
theorem const_log_pow_le_tailQ (s N : ℕ) (A : ℝ) (k : ℕ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 0 < A) (hAle : A ≤ 2 * (s : ℝ))
    (hk : k ≤ tailQExp s) :
    (A * Real.log N) ^ k ≤ tailQ N s := by
  have hlog0 : 0 ≤ Real.log N := le_of_lt (lt_trans (by norm_num) (log_N_gt_one hN))
  have hle : A * Real.log N ≤ 2 * (s : ℝ) * Real.log N :=
    mul_le_mul_of_nonneg_right hAle hlog0
  have hpow : (A * Real.log N) ^ k ≤ (2 * (s : ℝ) * Real.log N) ^ k :=
    pow_le_pow_left₀ (mul_nonneg (le_of_lt hA) hlog0) hle k
  exact hpow.trans (two_s_log_pow_le_tailQ s N k hs hN hk)

/-- Uniform multiplicative absorption of `(A log N)^k` into `𝒬`. -/
theorem const_log_pow_le_mul_tailQ (s : ℕ) (hs : 2 ≤ s)
    (A : ℝ) (hA : 0 < A) (k : ℕ) (hAle : A ≤ 2 * (s : ℝ))
    (hk : k ≤ tailQExp s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        (A * Real.log N) ^ k ≤ K * tailQ N s :=
  ⟨1, by norm_num, fun N hN => by
    simpa using const_log_pow_le_tailQ s N A k hs hN hA hAle hk⟩

/-- `δ · P ≤ δ^{1/2} · 𝒬` when `P ≤ 𝒬` and `0 ≤ δ ≤ 1`. -/
theorem delta_polylog_le_sqrt (δ P Q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    δ * P ≤ Real.sqrt δ * Q := by
  have hsq : Real.sqrt δ ≤ 1 :=
    (Real.sqrt_le_iff.2 ⟨by norm_num, by simpa using hδ1⟩)
  have hδ : δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ0).symm
  calc
    δ * P = Real.sqrt δ * Real.sqrt δ * P := by
      conv_lhs => rw [hδ]
    _ ≤ Real.sqrt δ * 1 * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) hP
    _ = Real.sqrt δ * P := by ring
    _ ≤ Real.sqrt δ * Q := mul_le_mul_of_nonneg_left hPQ (Real.sqrt_nonneg _)

theorem delta_le_sqrt_delta {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ≤ Real.sqrt δ := by
  have h := delta_polylog_le_sqrt δ 1 1 hδ0 hδ1 (by norm_num) le_rfl
  simpa using h

/-- `δ N^s 𝒬 ≤ δ^{1/2} N^s 𝒬` when `0 ≤ δ ≤ 1`. -/
theorem delta_mul_Ns_tailQ_le_errorSize (N s : ℕ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hN : 3 ≤ N) :
    δ * (N : ℝ) ^ s * tailQ N s ≤ errorSize N s δ := by
  have ht := tailQ_pos_of_three_le N s hN
  have hle :=
    delta_polylog_le_sqrt δ (tailQ N s) (tailQ N s) hδ0 hδ1 ht.le le_rfl
  have hNpow : 0 ≤ (N : ℝ) ^ s := pow_nonneg (Nat.cast_nonneg _) _
  simp only [errorSize]
  calc
    δ * (N : ℝ) ^ s * tailQ N s
        = (δ * tailQ N s) * (N : ℝ) ^ s := by ring
    _ ≤ (Real.sqrt δ * tailQ N s) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hle hNpow
    _ = Real.sqrt δ * (N : ℝ) ^ s * tailQ N s := by ring

theorem s_mul_pred_le_tailQExp (s : ℕ) : s * (s - 1) ≤ tailQExp s := by
  simp only [tailQExp, pow_two]
  have h : s * (s - 1) ≤ s * s := Nat.mul_le_mul_left s (Nat.sub_le _ _)
  have h3 : s * s ≤ 3 * (s * s) := Nat.le_mul_of_pos_left _ (by decide)
  exact h.trans h3

theorem two_pred_sq_sub_one_le_tailQExp (s : ℕ) :
    2 * (s - 1) ^ 2 - 1 ≤ tailQExp s := by
  have h1 : 2 * (s - 1) ^ 2 ≤ 2 * s ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
  have h2 : 2 * s ^ 2 ≤ 3 * s ^ 2 :=
    Nat.mul_le_mul_right _ (by decide : 2 ≤ 3)
  exact (Nat.sub_le _ _).trans (h1.trans (h2.trans_eq (by simp [tailQExp])))

/-- `2(s-1)² + s ≤ 3s²`, used to absorb harmonic × CS × `(2 log N)^s`. -/
theorem two_pred_sq_add_s_le_tailQExp (s : ℕ) :
    2 * (s - 1) ^ 2 + s ≤ tailQExp s := by
  have h1 : 2 * (s - 1) ^ 2 ≤ 2 * s ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
  have h2 : s ≤ s ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) s
  have hsum : 2 * (s - 1) ^ 2 + s ≤ 2 * s ^ 2 + s ^ 2 :=
    Nat.add_le_add h1 h2
  have h3 : 2 * s ^ 2 + s ^ 2 = 3 * s ^ 2 := by ring
  exact hsum.trans_eq (h3.trans (by simp [tailQExp]))

/-- `(2(s-1) log N)^{3(s-1)²} ≤ (2s log N)^{3s²}`. -/
theorem tailQ_mono_s {N s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) (hN : 3 ≤ N) :
    tailQ N s ≤ tailQ N t := by
  have hbase : 2 * (s : ℝ) * Real.log N ≤ 2 * (t : ℝ) * Real.log N := by
    have hlog := log_N_gt_one hN
    have hst : (s : ℝ) ≤ t := Nat.cast_le.mpr ht
    nlinarith
  have hpos : 1 ≤ 2 * (s : ℝ) * Real.log N := by
    have hlog := log_N_gt_one hN
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hpow :
      (2 * (s : ℝ) * Real.log N) ^ tailQExp s ≤
        (2 * (t : ℝ) * Real.log N) ^ tailQExp s :=
    pow_le_pow_left₀ (le_trans (by norm_num) hpos) hbase _
  have hexp : tailQExp s ≤ tailQExp t := by
    simp only [tailQExp]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht 2)
  have hbase_t : 1 ≤ 2 * (t : ℝ) * Real.log N :=
    le_trans hpos hbase
  simp only [tailQ]
  exact hpow.trans (pow_le_pow_right₀ hbase_t hexp)

end RMFLean
