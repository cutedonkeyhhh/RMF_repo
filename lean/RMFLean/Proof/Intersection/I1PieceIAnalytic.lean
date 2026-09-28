/-
Analytic finish for Piece I / II: divisor full sum × δ-tail × log absorption into `𝒬`.
-/
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.Intersection.I1
import RMFLean.Proof.Setup.TailQAbsorb
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Real Filter Topology

namespace RMFLean

set_option maxHeartbeats 800000

/-! ### Cross-term weighted sums via AM-GM + Lemma 1 -/

theorem tau_cross_le_half_sq (s n : ℕ) :
    (tau s n : ℝ) * (tau (s - 1) n : ℝ) ≤
      ((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2 := by
  have h := two_mul_le_add_sq (tau s n : ℝ) (tau (s - 1) n : ℝ)
  linarith

theorem log_ge_one_of_three_le (X : ℕ) (hX : 3 ≤ X) :
    (1 : ℝ) ≤ Real.log X := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
  exact le_trans (le_of_lt hlog3)
    (Real.log_le_log (by norm_num) (by exact_mod_cast hX))

theorem two_log_ge_one_of_three_le (X : ℕ) (hX : 3 ≤ X) :
    (1 : ℝ) ≤ 2 * Real.log X := by
  nlinarith [log_ge_one_of_three_le X hX]

theorem two_log_ge_two_of_three_le (X : ℕ) (hX : 3 ≤ X) :
    (2 : ℝ) ≤ 2 * Real.log X := by
  nlinarith [log_ge_one_of_three_le X hX]

theorem pow_sq_level_mono (X s : ℕ) (hX : 3 ≤ X) (hs : 2 ≤ s) {a b : ℕ}
    (hab : a ≤ b) :
    (2 * Real.log X) ^ a ≤ (2 * Real.log X) ^ b :=
  pow_le_pow_right₀ (two_log_ge_one_of_three_le X hX) hab

theorem tau_cross_weighted_sum_bound (X s : ℕ) (hX : 3 ≤ X) (hs : 2 ≤ s) :
    (∑ n ∈ Finset.Icc 1 X,
        (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2) ≤
      5 * (2 * Real.log X) ^ (s ^ 2) := by
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hs1' : 1 ≤ s - 1 := by omega
  have hfull_s := tau_sq_weighted_sum_bound X s hX hs1
  have hfull_s1 := tau_sq_weighted_sum_bound X (s - 1) hX hs1'
  have hpow_le :
      (2 * Real.log X) ^ ((s - 1) ^ 2) ≤ (2 * Real.log X) ^ (s ^ 2) := by
    refine pow_sq_level_mono X s hX hs ?_
    have h : s - 1 ≤ s := Nat.sub_le _ _
    calc
      (s - 1) ^ 2 = (s - 1) * (s - 1) := pow_two _
      _ ≤ s * s := Nat.mul_le_mul h h
      _ = s ^ 2 := (pow_two s).symm
  have hpoint : ∀ n ∈ Finset.Icc 1 X,
      (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 ≤
        (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) / (n : ℝ) ^ 2 := by
    intro n _
    exact div_le_div_of_nonneg_right (tau_cross_le_half_sq s n) (sq_nonneg _)
  have hsum :
      ∑ n ∈ Finset.Icc 1 X,
          (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) / (n : ℝ) ^ 2 =
        (1 / 2) * ∑ n ∈ Finset.Icc 1 X, (tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2 +
          (1 / 2) * ∑ n ∈ Finset.Icc 1 X,
            (tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    trans ∑ n ∈ Finset.Icc 1 X,
        ((1 / 2) * ((tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2) +
          (1 / 2) * ((tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2))
    · refine Finset.sum_congr rfl ?_
      intro n _
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    (∑ n ∈ Finset.Icc 1 X,
          (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 X,
            (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) /
              (n : ℝ) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (1 / 2) * ∑ n ∈ Finset.Icc 1 X, (tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2 +
          (1 / 2) * ∑ n ∈ Finset.Icc 1 X,
            (tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2 := hsum
    _ ≤ (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2)) +
          (1 / 2) * (5 * (2 * Real.log X) ^ ((s - 1) ^ 2)) := by
      gcongr <;> assumption
    _ ≤ (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2)) +
          (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2)) := by gcongr
    _ = 5 * (2 * Real.log X) ^ (s ^ 2) := by ring

theorem tau_cross_weighted_Icc_tail (X s A : ℕ)
    (hX : 3 ≤ X) (hs : 2 ≤ s) (hA : 0 < A) (hAX : A < X) :
    (∑ n ∈ Finset.Icc A X,
        (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2) ≤
      (5 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) / (A : ℝ) := by
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hs1' : 1 ≤ s - 1 := by omega
  have htail_s := divisor_tail_bound X s A hX hs1 hA hAX
  have htail_s1 := divisor_tail_bound X (s - 1) A hX hs1' hA hAX
  have hpow_le :
      (2 * Real.log X) ^ ((s - 1) ^ 2 - 1) ≤
        (2 * Real.log X) ^ (s ^ 2 - 1) := by
    refine pow_sq_level_mono X s hX hs ?_
    have h : s - 1 ≤ s := Nat.sub_le _ _
    have hsq : (s - 1) ^ 2 ≤ s ^ 2 := by
      calc
        (s - 1) ^ 2 = (s - 1) * (s - 1) := pow_two _
        _ ≤ s * s := Nat.mul_le_mul h h
        _ = s ^ 2 := (pow_two s).symm
    omega
  have hpoint : ∀ n ∈ Finset.Icc A X,
      (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 ≤
        (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) / (n : ℝ) ^ 2 := by
    intro n _
    exact div_le_div_of_nonneg_right (tau_cross_le_half_sq s n) (sq_nonneg _)
  have hsum :
      ∑ n ∈ Finset.Icc A X,
          (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) / (n : ℝ) ^ 2 =
        (1 / 2) * ∑ n ∈ Finset.Icc A X, (tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2 +
          (1 / 2) * ∑ n ∈ Finset.Icc A X,
            (tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    trans ∑ n ∈ Finset.Icc A X,
        ((1 / 2) * ((tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2) +
          (1 / 2) * ((tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2))
    · refine Finset.sum_congr rfl ?_
      intro n _
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    (∑ n ∈ Finset.Icc A X,
          (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Icc A X,
            (((tau s n : ℝ) ^ 2 + (tau (s - 1) n : ℝ) ^ 2) / 2) /
              (n : ℝ) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (1 / 2) * ∑ n ∈ Finset.Icc A X, (tau s n : ℝ) ^ 2 / (n : ℝ) ^ 2 +
          (1 / 2) * ∑ n ∈ Finset.Icc A X,
            (tau (s - 1) n : ℝ) ^ 2 / (n : ℝ) ^ 2 := hsum
    _ ≤ (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2 - 1) / (A : ℝ)) +
          (1 / 2) * (5 * (2 * Real.log X) ^ ((s - 1) ^ 2 - 1) / (A : ℝ)) := by
      gcongr <;> assumption
    _ ≤ (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2 - 1) / (A : ℝ)) +
          (1 / 2) * (5 * (2 * Real.log X) ^ (s ^ 2 - 1) / (A : ℝ)) := by
      gcongr
    _ = (5 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) / (A : ℝ) := by ring

theorem tau_cross_weighted_tail_bound (X s : ℕ) (δ : ℝ)
    (hX : 3 ≤ X) (hs : 2 ≤ s) (hδ : 0 < δ) :
    (∑ n ∈ Finset.Icc 1 X,
        if (1 : ℝ) ≤ δ * (n : ℝ) then
          (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2
        else 0) ≤
      (5 : ℝ) * δ * (2 * Real.log X) ^ (s ^ 2) := by
  classical
  set A : ℕ := Nat.ceil (1 / δ)
  have hfilter_iff (n : ℕ) : (1 : ℝ) ≤ δ * (n : ℝ) ↔ A ≤ n := by
    constructor
    · intro h
      exact Nat.ceil_le.2 (by rwa [div_le_iff₀ hδ, mul_comm])
    · intro h
      have : (1 : ℝ) / δ ≤ n := Nat.ceil_le.1 h
      rwa [div_le_iff₀ hδ, mul_comm] at this
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 X,
          if (1 : ℝ) ≤ δ * (n : ℝ) then
            (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2
          else 0) =
        ∑ n ∈ (Finset.Icc 1 X).filter (fun n => A ≤ n),
          (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 := by
    simp [Finset.sum_filter, hfilter_iff]
  rw [hsum_eq]
  have hterm0 (n : ℕ) :
      0 ≤ (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  by_cases hhit : (1 : ℝ) ≤ δ * (X : ℝ)
  · have hAleX : A ≤ X := (hfilter_iff X).1 hhit
    have hApos : 0 < A := by
      have hpos : (0 : ℝ) < 1 / δ := one_div_pos.2 hδ
      exact Nat.ceil_pos.2 hpos
    have hX2 : 2 ≤ X := le_trans (by decide : 2 ≤ 3) hX
    set A0 : ℕ := min A (X - 1)
    have hA0pos : 0 < A0 := lt_min hApos (by omega)
    have hA0X : A0 < X :=
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt
        (lt_of_lt_of_le (by decide : 0 < 3) hX) (by decide))
    have hsub :
        (Finset.Icc 1 X).filter (fun n => A ≤ n) ⊆ Finset.Icc A0 X := by
      intro n hn
      obtain ⟨hnI, hnA⟩ := Finset.mem_filter.1 hn
      exact Finset.mem_Icc.2 ⟨le_trans (min_le_left _ _) hnA, (Finset.mem_Icc.1 hnI).2⟩
    have h1Xδ : (1 : ℝ) / X ≤ δ := by
      have hXpos : (0 : ℝ) < X := by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hX
      rw [div_le_iff₀ hXpos]
      simpa [mul_comm] using hhit
    have hA0inv : (1 : ℝ) / A0 ≤ (2 : ℝ) * δ := by
      by_cases hmin : A ≤ X - 1
      · have hA0A : A0 = A := min_eq_left hmin
        have hge : (1 : ℝ) / δ ≤ (A : ℝ) := Nat.le_ceil _
        have hApos' : (0 : ℝ) < A := by exact_mod_cast hApos
        have hle : (1 : ℝ) / A ≤ δ := by
          rwa [div_le_iff₀ hApos', mul_comm, ← div_le_iff₀ hδ]
        calc
          (1 : ℝ) / A0 = 1 / A := by rw [hA0A]
          _ ≤ δ := hle
          _ ≤ 2 * δ := by nlinarith [hδ.le]
      · have hA0X1 : A0 = X - 1 := min_eq_right (le_of_not_ge hmin)
        have hXpos : (0 : ℝ) < X := by
          exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hX)
        have hcast : ((X - 1 : ℕ) : ℝ) = (X : ℝ) - 1 := by
          exact_mod_cast Nat.cast_sub (le_trans (by decide : 1 ≤ 2) hX2)
        have hle : (1 : ℝ) / ((X : ℝ) - 1) ≤ (2 : ℝ) / X := by
          rw [div_le_div_iff₀
            (sub_pos.2 (by exact_mod_cast
              (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hX))) hXpos]
          nlinarith [show (2 : ℝ) ≤ X by exact_mod_cast hX2]
        calc
          (1 : ℝ) / A0 = 1 / ((X : ℝ) - 1) := by rw [hA0X1, hcast]
          _ ≤ 2 / X := hle
          _ = 2 * (1 / X) := by ring
          _ ≤ 2 * δ := mul_le_mul_of_nonneg_left h1Xδ (by norm_num)
    have hmono :
        ∑ n ∈ (Finset.Icc 1 X).filter (fun n => A ≤ n),
            (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 ≤
          ∑ n ∈ Finset.Icc A0 X,
            (tau s n : ℝ) * (tau (s - 1) n : ℝ) / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hterm0 n
    have hle_tail := tau_cross_weighted_Icc_tail X s A0 hX hs hA0pos hA0X
    have hsq : s ^ 2 - 1 + 1 = s ^ 2 := by
      have : 1 ≤ s ^ 2 := Nat.one_le_pow 2 s (by omega : 0 < s)
      omega
    have habsorb :
        (5 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) / (A0 : ℝ) ≤
          (5 : ℝ) * δ * (2 * Real.log X) ^ (s ^ 2) := by
      have h2log := two_log_ge_two_of_three_le X hX
      have hstep :
          (2 * Real.log X) ^ (s ^ 2 - 1) / (A0 : ℝ) ≤
            δ * (2 * Real.log X) ^ (s ^ 2) := by
        have hmul :
            (2 * Real.log X) ^ (s ^ 2 - 1) * (1 / A0) ≤
              (2 * Real.log X) ^ (s ^ 2 - 1) * (2 * δ) :=
          mul_le_mul_of_nonneg_left hA0inv (by positivity)
        have hpow :
            (2 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) ≤
              (2 * Real.log X) ^ (s ^ 2) := by
          calc
            (2 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1)
                ≤ (2 * Real.log X) * (2 * Real.log X) ^ (s ^ 2 - 1) :=
              mul_le_mul_of_nonneg_right h2log (by positivity)
            _ = (2 * Real.log X) ^ (s ^ 2 - 1 + 1) := (pow_succ' _ _).symm
            _ = (2 * Real.log X) ^ (s ^ 2) := by rw [hsq]
        calc
          (2 * Real.log X) ^ (s ^ 2 - 1) / (A0 : ℝ)
              = (2 * Real.log X) ^ (s ^ 2 - 1) * (1 / A0) := by ring
          _ ≤ (2 * Real.log X) ^ (s ^ 2 - 1) * (2 * δ) := hmul
          _ = δ * (2 * (2 * Real.log X) ^ (s ^ 2 - 1)) := by ring
          _ ≤ δ * (2 * Real.log X) ^ (s ^ 2) :=
            mul_le_mul_of_nonneg_left hpow hδ.le
      calc
        (5 : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) / (A0 : ℝ)
            = 5 * ((2 * Real.log X) ^ (s ^ 2 - 1) / (A0 : ℝ)) := by ring
        _ ≤ (5 : ℝ) * δ * (2 * Real.log X) ^ (s ^ 2) := by
          simpa [mul_assoc, mul_div_assoc] using
            mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 5)
    exact (hmono.trans hle_tail).trans habsorb
  · have hempty :
        (Finset.Icc 1 X).filter (fun n => A ≤ n) = ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hnI hnA
      exact hhit ((hfilter_iff X).2 (le_trans hnA (Finset.mem_Icc.1 hnI).2))
    rw [hempty, Finset.sum_empty]
    positivity

theorem two_log_rpow_le_slog (N s : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N) :
    2 * Real.log (N ^ (s - 1)) ≤ 2 * (s : ℝ) * Real.log N := by
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hlogN : 0 ≤ Real.log N :=
    le_of_lt (Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 3) hN))
  have hcast :
      Real.log (N ^ (s - 1)) = Nat.cast (s - 1) * Real.log N :=
    Real.log_pow (N : ℝ) (s - 1)
  calc
    2 * Real.log (N ^ (s - 1)) = 2 * (Nat.cast (s - 1) * Real.log N) := by rw [hcast]
    _ ≤ 2 * ((s : ℝ) * Real.log N) := by
      nlinarith [show (Nat.cast (s - 1) : ℝ) ≤ s by exact_mod_cast Nat.sub_le s 1, hlogN]
    _ = 2 * (s : ℝ) * Real.log N := by ring

theorem Npow_succ_le_three (N s : ℕ) (hN : 3 ≤ N) (hs : 2 ≤ s) :
    3 ≤ N ^ (s - 1) := by
  calc
    3 ≤ N := hN
    _ ≤ N ^ (s - 1) := Nat.le_self_pow (by omega : s - 1 ≠ 0) N

/-! ### `(2s log N)^k ≤ C(s,k) · 𝒬(N,s)` -/

theorem tailQ_pos (N s : ℕ) (hN : 3 ≤ N) :
    0 < tailQ N s :=
  tailQ_pos_of_three_le N s hN

theorem twos_log_pow_le_mul_tailQ (s : ℕ) (hs : 2 ≤ s) (k : ℕ)
    (hk : k ≤ tailQExp s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 3 ≤ N →
        (2 * (s : ℝ) * Real.log N) ^ k ≤ C * tailQ N s :=
  ⟨1, by norm_num, fun N hN => by
    simpa using two_s_log_pow_le_tailQ s N k hs hN hk⟩

theorem I1_piece_weighted_product_bound (s N : ℕ) (δ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) :
    (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
        (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
      (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
        if (1 : ℝ) ≤ δ * (T : ℝ) then
          (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
        else 0) ≤
      (25 : ℝ) * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) := by
  set X := N ^ (s - 1)
  have hX : 3 ≤ X := Npow_succ_le_three N s hN hs
  have hfull := tau_cross_weighted_sum_bound X s hX hs
  have htail := tau_cross_weighted_tail_bound X s δ hX hs hδ
  have hle_base : 2 * Real.log X ≤ 2 * (s : ℝ) * Real.log N := by
    simpa [X] using two_log_rpow_le_slog N s hs hN
  have hlogX :
      (2 * Real.log X) ^ (2 * s ^ 2) ≤ (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) :=
    pow_le_pow_left₀ (by positivity) hle_base (2 * s ^ 2)
  calc
    (∑ e ∈ Finset.Icc 1 X, (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
        (∑ T ∈ Finset.Icc 1 X,
          if (1 : ℝ) ≤ δ * (T : ℝ) then
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
          else 0)
        ≤ (5 * (2 * Real.log X) ^ (s ^ 2)) *
            (5 * δ * (2 * Real.log X) ^ (s ^ 2)) := by
          gcongr <;> assumption
    _ = (25 : ℝ) * δ * (2 * Real.log X) ^ (2 * s ^ 2) := by ring
    _ ≤ (25 : ℝ) * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hlogX (by positivity)

theorem I1_piece_weighted_product_bound_II (s N : ℕ) (δ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) :
    (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
        (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
      (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
        if (1 : ℝ) ≤ δ * (e : ℝ) then
          (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
        else 0) ≤
      (25 : ℝ) * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) := by
  set X := N ^ (s - 1)
  have hX : 3 ≤ X := Npow_succ_le_three N s hN hs
  have hfull := tau_cross_weighted_sum_bound X s hX hs
  have htail := tau_cross_weighted_tail_bound X s δ hX hs hδ
  have hle_base : 2 * Real.log X ≤ 2 * (s : ℝ) * Real.log N := by
    simpa [X] using two_log_rpow_le_slog N s hs hN
  have hlogX :
      (2 * Real.log X) ^ (2 * s ^ 2) ≤ (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) :=
    pow_le_pow_left₀ (by positivity) hle_base (2 * s ^ 2)
  calc
    (∑ T ∈ Finset.Icc 1 X, (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
        (∑ e ∈ Finset.Icc 1 X,
          if (1 : ℝ) ≤ δ * (e : ℝ) then
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
          else 0)
        ≤ (5 * (2 * Real.log X) ^ (s ^ 2)) *
            (5 * δ * (2 * Real.log X) ^ (s ^ 2)) := by
          gcongr <;> assumption
    _ = (25 : ℝ) * δ * (2 * Real.log X) ^ (2 * s ^ 2) := by ring
    _ ≤ (25 : ℝ) * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hlogX (by positivity)

theorem I1_piece_I_weighted_le_error (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 3 ≤ N → 0 < δ → δ < 1 / 8 →
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
            (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
              (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
            (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              if (1 : ℝ) ≤ δ * (T : ℝ) then
                (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
              else 0) ≤
          C * errorSize N s δ := by
  obtain ⟨C0, hC0, habs⟩ := twos_log_pow_le_mul_tailQ s hs (3 * s ^ 2) (by simp [tailQExp])
  refine ⟨25 * C0, mul_pos (by norm_num) hC0, fun N δ hN hδ _hδ' => ?_⟩
  have hprod := I1_piece_weighted_product_bound s N δ hs hN hδ
  have hpow0 : 0 ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by positivity
  have hinner :=
    mul_le_mul_of_nonneg_left hprod hpow0
  have hform :
      (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
            if (1 : ℝ) ≤ δ * (T : ℝ) then
              (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
            else 0) =
        (N : ℝ) ^ s * ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
              (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
            (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              if (1 : ℝ) ≤ δ * (T : ℝ) then
                (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
              else 0))) := by ring_nf
  calc
    (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
        (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
        (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
          if (1 : ℝ) ≤ δ * (T : ℝ) then
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
          else 0)
        ≤ (N : ℝ) ^ s *
            ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
              (25 * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2))) := by
      rw [hform]
      exact mul_le_mul_of_nonneg_left hinner (pow_nonneg (Nat.cast_nonneg _) _)
    _ = 25 * δ * (N : ℝ) ^ s *
          (2 * (s : ℝ) * Real.log N) ^ (3 * s ^ 2) := by ring
    _ ≤ 25 * C0 * δ * (N : ℝ) ^ s * tailQ N s := by
      have hlog := habs N hN
      have hpos : 0 ≤ 25 * δ * (N : ℝ) ^ s := by positivity
      calc
        25 * δ * (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (3 * s ^ 2)
            ≤ 25 * δ * (N : ℝ) ^ s * (C0 * tailQ N s) := by
              gcongr
        _ = 25 * C0 * δ * (N : ℝ) ^ s * tailQ N s := by ring
    _ ≤ (25 * C0) * errorSize N s δ := by
      have hδ1 : δ ≤ 1 := le_of_lt (lt_trans _hδ' (by norm_num))
      have herr := delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN
      have hC0' : 0 ≤ 25 * C0 := mul_nonneg (by norm_num) hC0.le
      calc
        25 * C0 * δ * (N : ℝ) ^ s * tailQ N s
            = (25 * C0) * (δ * (N : ℝ) ^ s * tailQ N s) := by ring
        _ ≤ (25 * C0) * errorSize N s δ :=
          mul_le_mul_of_nonneg_left herr hC0'

theorem I1_piece_II_weighted_le_error (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 3 ≤ N → 0 < δ → δ < 1 / 8 →
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
            (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
            (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
              if (1 : ℝ) ≤ δ * (e : ℝ) then
                (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
              else 0) ≤
          C * errorSize N s δ := by
  obtain ⟨C0, hC0, habs⟩ := twos_log_pow_le_mul_tailQ s hs (3 * s ^ 2) (by simp [tailQExp])
  refine ⟨25 * C0, mul_pos (by norm_num) hC0, fun N δ hN hδ _hδ' => ?_⟩
  have hprod := I1_piece_weighted_product_bound_II s N δ hs hN hδ
  have hpow0 : 0 ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by positivity
  have hinner :=
    mul_le_mul_of_nonneg_left hprod hpow0
  have hform :
      (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
          (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
            if (1 : ℝ) ≤ δ * (e : ℝ) then
              (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
            else 0) =
        (N : ℝ) ^ s * ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
            (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
              if (1 : ℝ) ≤ δ * (e : ℝ) then
                (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
              else 0))) := by ring_nf
  calc
    (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
        (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
          (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
        (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          if (1 : ℝ) ≤ δ * (e : ℝ) then
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
          else 0)
        ≤ (N : ℝ) ^ s *
            ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
              (25 * δ * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2))) := by
      rw [hform]
      exact mul_le_mul_of_nonneg_left hinner (pow_nonneg (Nat.cast_nonneg _) _)
    _ = 25 * δ * (N : ℝ) ^ s *
          (2 * (s : ℝ) * Real.log N) ^ (3 * s ^ 2) := by ring
    _ ≤ 25 * C0 * δ * (N : ℝ) ^ s * tailQ N s := by
      have hlog := habs N hN
      calc
        25 * δ * (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (3 * s ^ 2)
            ≤ 25 * δ * (N : ℝ) ^ s * (C0 * tailQ N s) := by
              gcongr
        _ = 25 * C0 * δ * (N : ℝ) ^ s * tailQ N s := by ring
    _ ≤ (25 * C0) * errorSize N s δ := by
      have hδ1 : δ ≤ 1 := le_of_lt (lt_trans _hδ' (by norm_num))
      have herr := delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN
      have hC0' : 0 ≤ 25 * C0 := mul_nonneg (by norm_num) hC0.le
      calc
        25 * C0 * δ * (N : ℝ) ^ s * tailQ N s
            = (25 * C0) * (δ * (N : ℝ) ^ s * tailQ N s) := by ring
        _ ≤ (25 * C0) * errorSize N s δ :=
          mul_le_mul_of_nonneg_left herr hC0'

end RMFLean
