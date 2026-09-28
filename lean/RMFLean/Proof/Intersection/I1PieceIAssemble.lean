/-
Assemble Piece I / II card majorants from fixed-`(T,e,k)` package bounds.
-/
import RMFLean.Proof.Intersection.I1PieceICardMajorant
import RMFLean.Proof.Intersection.I1PieceIAnalytic

noncomputable section

open Classical BigOperators Real

namespace RMFLean

set_option maxHeartbeats 800000

theorem I1PieceIFixedCardSum_eq_sum_k (s N A : ℕ) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ) :
    I1PieceIFixedCardSum s N A δ I h0 T e =
      if (1 : ℝ) ≤ δ * (T : ℝ) then
        ∑ k ∈ Finset.Icc 1 N,
          ((I1PieceIFixedK s N A I h0 T e k).card : ℝ)
      else 0 := by
  classical
  by_cases hδT : (1 : ℝ) ≤ δ * (T : ℝ)
  · simp only [hδT, ↓reduceIte]
    set OuterT :=
      (I1Outer (s := s) (N := N) A I h0).filter fun ν => ν.T h0 = T
    have hF :
        (I1Outer (s := s) (N := N) A I h0).filter
            fun ν => ν.T h0 = T ∧ (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) =
          OuterT := by
      ext ν
      simp only [OuterT, Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.1, h.2.1⟩
      · intro h; exact ⟨h.1, h.2, by simpa [h.2] using hδT⟩
    simp only [I1PieceIFixedCardSum, hF]
    have hν : ∀ ν ∈ OuterT,
        (if e ∈ (ν.Q h0).divisors then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0) =
          ∑ k ∈ Finset.Icc 1 N,
            if e ∈ (ν.Q h0).divisors ∧ e * k ∈ fibreB s N A ν h0 then
              (1 : ℝ) else 0 := by
      intro ν _
      by_cases he : e ∈ (ν.Q h0).divisors
      · simp [he, Finset.sum_boole]
      · simp [he]
    rw [Finset.sum_congr rfl hν, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hK :
        I1PieceIFixedK s N A I h0 T e k =
          OuterT.filter fun ν =>
            e ∈ (ν.Q h0).divisors ∧ e * k ∈ fibreB s N A ν h0 := by
      ext ν; simp [I1PieceIFixedK, OuterT, Finset.mem_filter]; tauto
    simp [hK, Finset.sum_boole]
  · have hempty :
        (I1Outer (s := s) (N := N) A I h0).filter
            fun ν => ν.T h0 = T ∧ (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) = ∅ := by
      ext ν
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro h
      exact hδT (by simpa [h.2.1] using h.2.2)
    simp [hδT, I1PieceIFixedCardSum, hempty]

theorem I1PieceIIFixedCardSum_eq_sum_k (s N A : ℕ) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ) :
    I1PieceIIFixedCardSum s N A δ I h0 T e =
      if (1 : ℝ) ≤ δ * (e : ℝ) then
        ∑ k ∈ Finset.Icc 1 N,
          ((I1PieceIFixedK s N A I h0 T e k).card : ℝ)
      else 0 := by
  classical
  by_cases hδe : (1 : ℝ) ≤ δ * (e : ℝ)
  · simp only [hδe, ↓reduceIte]
    set OuterT :=
      (I1Outer (s := s) (N := N) A I h0).filter fun ν => ν.T h0 = T
    simp only [I1PieceIIFixedCardSum]
    change ∑ ν ∈ OuterT,
        (if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0) =
      ∑ k ∈ Finset.Icc 1 N, ((I1PieceIFixedK s N A I h0 T e k).card : ℝ)
    have hν : ∀ ν ∈ OuterT,
        (if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0) =
          ∑ k ∈ Finset.Icc 1 N,
            if e ∈ (ν.Q h0).divisors ∧ e * k ∈ fibreB s N A ν h0 then
              (1 : ℝ) else 0 := by
      intro ν _
      by_cases he : e ∈ (ν.Q h0).divisors
      · simp [he, hδe, Finset.sum_boole]
      · simp [he]
    rw [Finset.sum_congr rfl hν, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hK :
        I1PieceIFixedK s N A I h0 T e k =
          OuterT.filter fun ν =>
            e ∈ (ν.Q h0).divisors ∧ e * k ∈ fibreB s N A ν h0 := by
      ext ν; simp [I1PieceIFixedK, OuterT, Finset.mem_filter]; tauto
    simp [hK, Finset.sum_boole]
  · simp only [hδe, ↓reduceIte, I1PieceIIFixedCardSum]
    refine Finset.sum_eq_zero fun ν _ => by simp [hδe]

theorem one_add_log_mul_pow_le (N s : ℕ) (hN : 3 ≤ N) (hs : 2 ≤ s) :
    (1 + Real.log N) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) ≤
      (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3)
      (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hbase : (0 : ℝ) < 2 * (s : ℝ) * Real.log N := by positivity
  have hle : 1 + Real.log N ≤ 2 * (s : ℝ) * Real.log N := by
    have : (1 : ℝ) + Real.log N ≤ 2 * Real.log N := by nlinarith [hlog1]
    exact le_trans this (by nlinarith [hsR, hlog1])
  have hpow :
      s ^ 2 - 1 + 1 = s ^ 2 := by
    have : 1 ≤ s ^ 2 := Nat.one_le_pow 2 s (by omega : 0 < s)
    omega
  calc
    (1 + Real.log N) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)
        ≤ (2 * (s : ℝ) * Real.log N) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg (le_of_lt hbase) _)
    _ = (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1 + 1) := (pow_succ' _ _).symm
    _ = (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by rw [hpow]

theorem fixedK_sum_k_le (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s)
    (T e : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N) (hT : 1 ≤ T) (he : 1 ≤ e) :
    (∑ k ∈ Finset.Icc 1 N,
        ((I1PieceIFixedK s N A I h0 T e k).card : ℝ)) ≤
      (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
        ((tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
        ((tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) := by
  classical
  have hepos : (0 : ℝ) < e := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one he
  have hTpos : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hT
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      ((I1PieceIFixedK s N A I h0 T e k).card : ℝ) ≤
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) * ((1 : ℝ) / (k : ℝ)) := by
    intro k hk
    have hk0 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk0
    have hcard :=
      I1PieceIFixedK_card_le (s := s) (N := N) (A := A) (I := I)
        (h0 := h0) T e k hs hN hT he hk0
    set X := N ^ s / (e ^ 2 * k * T ^ 2)
    have hconv :=
      tau_ss_conv_sum_bound_weak s (e * T) X N hs hN (Nat.div_le_self _ _)
    have hτmul : (tau s (e * T) : ℝ) ≤ (tau s e : ℝ) * (tau s T : ℝ) := by
      exact_mod_cast tau_mul_le s e T (le_trans (by decide : 1 ≤ 2) hs)
    have hτT : (0 : ℝ) ≤ (tau (s - 1) T : ℝ) := by exact_mod_cast Nat.zero_le _
    have hτe : (0 : ℝ) ≤ (tau (s - 1) e : ℝ) := by exact_mod_cast Nat.zero_le _
    have hτse : (0 : ℝ) ≤ (tau s e : ℝ) := by exact_mod_cast Nat.zero_le _
    have hτsT : (0 : ℝ) ≤ (tau s T : ℝ) := by exact_mod_cast Nat.zero_le _
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le _
    have hpow0 : (0 : ℝ) ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
      positivity
    have hXle : (X : ℝ) ≤
        (N : ℝ) ^ s / ((e : ℝ) ^ 2 * (k : ℝ) * (T : ℝ) ^ 2) := by
      have h : (X : ℝ) ≤ ((N ^ s : ℕ) : ℝ) / ((e ^ 2 * k * T ^ 2 : ℕ) : ℝ) :=
        Nat.cast_div_le (m := N ^ s) (n := e ^ 2 * k * T ^ 2)
      refine h.trans_eq ?_
      simp [Nat.cast_pow, Nat.cast_mul]
    have hstep1 :
        ((I1PieceIFixedK s N A I h0 T e k).card : ℝ) ≤
          (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s (e * T) : ℝ) * (X : ℝ) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) :=
      le_trans hcard (mul_le_mul_of_nonneg_left hconv (mul_nonneg hτT hτe))
    have hstep2 :
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s (e * T) : ℝ) * (X : ℝ) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) ≤
          (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s e : ℝ) * (tau s T : ℝ) * (X : ℝ) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hτT hτe)
      refine mul_le_mul_of_nonneg_right ?_ hpow0
      exact mul_le_mul_of_nonneg_right hτmul hX0
    have hstep3 :
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s e : ℝ) * (tau s T : ℝ) * (X : ℝ) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) ≤
          (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s e : ℝ) * (tau s T : ℝ) *
              ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (k : ℝ) * (T : ℝ) ^ 2)) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hτT hτe)
      refine mul_le_mul_of_nonneg_right ?_ hpow0
      exact mul_le_mul_of_nonneg_left hXle (mul_nonneg hτse hτsT)
    have hstep4 :
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
            ((tau s e : ℝ) * (tau s T : ℝ) *
              ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (k : ℝ) * (T : ℝ) ^ 2)) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) =
          (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
            (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) * ((1 : ℝ) / (k : ℝ)) := by
      field_simp [hkpos.ne', hepos.ne', hTpos.ne']
      try ring
    exact (hstep1.trans hstep2).trans (hstep3.trans_eq hstep4)
  have hsum := Finset.sum_le_sum hterm
  have hfac :
      ∑ k ∈ Finset.Icc 1 N,
          (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
            (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) * ((1 : ℝ) / (k : ℝ)) =
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
    simp [← Finset.mul_sum, mul_assoc]
  have hharm :=
    sum_Icc_inv_le_one_add_log N (le_trans (by decide : 1 ≤ 3) hN)
  have habsorb := one_add_log_mul_pow_le N s hN hs
  calc
    ∑ k ∈ Finset.Icc 1 N, ((I1PieceIFixedK s N A I h0 T e k).card : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 N,
            (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
              (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) * ((1 : ℝ) / (k : ℝ)) :=
          hsum
    _ = (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := hfac
    _ ≤ (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) * (1 + Real.log N) := by
            refine mul_le_mul_of_nonneg_left hharm ?_; positivity
    _ = (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          ((1 + Real.log N) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) := by
            ring
    _ ≤ (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) * (tau s e : ℝ) *
          (tau s T : ℝ) * ((N : ℝ) ^ s / ((e : ℝ) ^ 2 * (T : ℝ) ^ 2)) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
            refine mul_le_mul_of_nonneg_left habsorb ?_; positivity
    _ = (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          ((tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) := by
            field_simp [hepos.ne', hTpos.ne']; try ring_nf

theorem I1PieceIFixedCardSum_le (s N A : ℕ) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hT : 1 ≤ T) (he : 1 ≤ e) :
    I1PieceIFixedCardSum s N A δ I h0 T e ≤
      if (1 : ℝ) ≤ δ * (T : ℝ) then
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          ((tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2)
      else 0 := by
  rw [I1PieceIFixedCardSum_eq_sum_k]
  split_ifs with hδT
  · exact fixedK_sum_k_le s N A I h0 T e hs hN hT he
  · rfl

theorem I1PieceIIFixedCardSum_le (s N A : ℕ) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hT : 1 ≤ T) (he : 1 ≤ e) :
    I1PieceIIFixedCardSum s N A δ I h0 T e ≤
      if (1 : ℝ) ≤ δ * (e : ℝ) then
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          ((tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2)
      else 0 := by
  rw [I1PieceIIFixedCardSum_eq_sum_k]
  split_ifs with hδe
  · exact fixedK_sum_k_le s N A I h0 T e hs hN hT he
  · rfl

theorem I1_piece_I_card_majorant (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s))
    (h0 : 0 < s) (hs : 2 ≤ s) (hN : 3 ≤ N) (_hδ : 0 < δ) (_hA : 1 ≤ A) :
    I1PieceICardSum s N A δ I h0 ≤
      (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
        (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
        (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
          if (1 : ℝ) ≤ δ * (T : ℝ) then
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
          else 0) := by
  classical
  rw [I1PieceICardSum_eq_sum_fixed (s := s) (N := N) (A := A) (δ := δ)
    (I := I) (h0 := h0) (_hN := hN)]
  set S := Finset.Icc 1 (N ^ (s - 1))
  have hterm : ∀ T ∈ S, ∀ e ∈ S,
      I1PieceIFixedCardSum s N A δ I h0 T e ≤
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          (if (1 : ℝ) ≤ δ * (T : ℝ) then
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2 else 0) := by
    intro T hT e he
    have hle := I1PieceIFixedCardSum_le s N A δ I h0 T e hs hN
      (Finset.mem_Icc.1 hT).1 (Finset.mem_Icc.1 he).1
    split_ifs with hδT
    · simpa [hδT, mul_assoc, mul_left_comm, mul_comm] using hle
    · simpa [hδT] using hle
  have hsum :=
    Finset.sum_le_sum fun T hT =>
      Finset.sum_le_sum fun e he => hterm T hT e he
  set C : ℝ := (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2)
  set fe : ℕ → ℝ := fun e => (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
  set gT : ℕ → ℝ := fun T =>
    if (1 : ℝ) ≤ δ * (T : ℝ) then
      (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2 else 0
  have hpull :
      ∑ T ∈ S, ∑ e ∈ S, C * fe e * gT T = C * (∑ e ∈ S, fe e) * (∑ T ∈ S, gT T) := by
    calc
      ∑ T ∈ S, ∑ e ∈ S, C * fe e * gT T
          = ∑ T ∈ S, ∑ e ∈ S, gT T * (C * fe e) := by
            refine Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
      _ = (∑ T ∈ S, gT T) * ∑ e ∈ S, C * fe e :=
            (Finset.sum_mul_sum (s := S) (t := S) gT (fun e => C * fe e)).symm
      _ = (∑ e ∈ S, C * fe e) * ∑ T ∈ S, gT T := mul_comm _ _
      _ = C * (∑ e ∈ S, fe e) * (∑ T ∈ S, gT T) := by
            simp [Finset.mul_sum, mul_assoc]
  exact hsum.trans (le_of_eq (by simpa [C, fe, gT, S, mul_assoc] using hpull))

theorem I1PieceIICardSum_eq_sum_fixed (s N A : ℕ) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (_hN : 3 ≤ N) :
    I1PieceIICardSum s N A δ I h0 =
      ∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
        ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          I1PieceIIFixedCardSum s N A δ I h0 T e := by
  classical
  -- Mirror `I1PieceICardSum_eq_sum_fixed`, with δ-cutoff on `e`.
  set Outer := I1Outer (s := s) (N := N) A I h0
  set Srange := Finset.Icc 1 (N ^ (s - 1))
  have hTmem : ∀ ν ∈ Outer, ν.T h0 ∈ Srange := fun ν hν => I1Outer_T_mem_Icc hν
  have hνsum : ∀ ν ∈ Outer,
      (∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
        (((Finset.Icc 1 N).filter fun k =>
          e * k ∈ fibreB s N A ν h0).card : ℝ)) =
        ∑ e ∈ Srange,
          if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else (0 : ℝ) := by
    intro ν hν
    have hsubset : (ν.Q h0).divisors ⊆ Srange := fun e he =>
      I1Outer_divisor_mem_Icc hν he
    have hset :
        (ν.Q h0).divisors.filter fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ) =
          Srange.filter fun e =>
            e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro h; exact ⟨hsubset h.1, h.1, h.2⟩
      · intro h; exact ⟨h.2.1, h.2.2⟩
    rw [← Finset.sum_filter
        (f := fun e =>
          (((Finset.Icc 1 N).filter fun k =>
            e * k ∈ fibreB s N A ν h0).card : ℝ))
        (p := fun e => e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ))]
    rw [← hset]
  calc
    I1PieceIICardSum s N A δ I h0 =
        ∑ ν ∈ Outer, ∑ e ∈ (ν.Q h0).divisors.filter
          fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
          (((Finset.Icc 1 N).filter fun k =>
            e * k ∈ fibreB s N A ν h0).card : ℝ) := by
      simp [I1PieceIICardSum, Outer]
    _ = ∑ ν ∈ Outer, ∑ e ∈ Srange,
          if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else (0 : ℝ) := Finset.sum_congr rfl hνsum
    _ = ∑ e ∈ Srange, ∑ ν ∈ Outer,
          if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else (0 : ℝ) := Finset.sum_comm
    _ = ∑ e ∈ Srange, ∑ T ∈ Srange,
          ∑ ν ∈ Outer.filter fun ν => ν.T h0 = T,
            if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
              (((Finset.Icc 1 N).filter fun k =>
                e * k ∈ fibreB s N A ν h0).card : ℝ)
            else (0 : ℝ) := by
          refine Finset.sum_congr rfl fun e _ =>
            (Finset.sum_fiberwise_of_maps_to hTmem _).symm
    _ = ∑ T ∈ Srange, ∑ e ∈ Srange,
          I1PieceIIFixedCardSum s N A δ I h0 T e := by
          rw [Finset.sum_comm]
          simp [I1PieceIIFixedCardSum, Outer]

theorem I1_piece_II_card_majorant (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s))
    (h0 : 0 < s) (hs : 2 ≤ s) (hN : 3 ≤ N) (_hδ : 0 < δ) (_hA : 1 ≤ A) :
    I1PieceIICardSum s N A δ I h0 ≤
      (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
        (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
          (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
        (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          if (1 : ℝ) ≤ δ * (e : ℝ) then
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
          else 0) := by
  classical
  rw [I1PieceIICardSum_eq_sum_fixed (s := s) (N := N) (A := A) (δ := δ)
    (I := I) (h0 := h0) (_hN := hN)]
  set S := Finset.Icc 1 (N ^ (s - 1))
  have hterm : ∀ T ∈ S, ∀ e ∈ S,
      I1PieceIIFixedCardSum s N A δ I h0 T e ≤
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          ((tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
          (if (1 : ℝ) ≤ δ * (e : ℝ) then
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2 else 0) := by
    intro T hT e he
    have hle := I1PieceIIFixedCardSum_le s N A δ I h0 T e hs hN
      (Finset.mem_Icc.1 hT).1 (Finset.mem_Icc.1 he).1
    split_ifs with hδe
    · simpa [hδe, mul_assoc, mul_left_comm, mul_comm] using hle
    · simpa [hδe] using hle
  have hsum :=
    Finset.sum_le_sum fun T hT =>
      Finset.sum_le_sum fun e he => hterm T hT e he
  set C : ℝ := (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2)
  set fT : ℕ → ℝ := fun T => (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
  set ge : ℕ → ℝ := fun e =>
    if (1 : ℝ) ≤ δ * (e : ℝ) then
      (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2 else 0
  have hpull :
      ∑ T ∈ S, ∑ e ∈ S, C * fT T * ge e = C * (∑ T ∈ S, fT T) * (∑ e ∈ S, ge e) := by
    calc
      ∑ T ∈ S, ∑ e ∈ S, C * fT T * ge e
          = ∑ T ∈ S, ∑ e ∈ S, (C * fT T) * ge e := by
            refine Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
      _ = (∑ T ∈ S, C * fT T) * ∑ e ∈ S, ge e :=
            (Finset.sum_mul_sum (s := S) (t := S) (fun T => C * fT T) ge).symm
      _ = C * (∑ T ∈ S, fT T) * (∑ e ∈ S, ge e) := by
            simp [Finset.mul_sum, mul_assoc]
  exact hsum.trans (le_of_eq (by simpa [C, fT, ge, S, mul_assoc] using hpull))

theorem I1_piece_I (d : ℕ) :
    ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (I : Finset (Fin s)) (hN : 3 ≤ N)
        (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
        (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A),
        I1PieceISum d s N A g δ I (by omega) ≤ C * errorSize N s δ := by
  intro s hs
  obtain ⟨C, hC, hfin⟩ := I1_piece_I_weighted_le_error s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ I hN _hI0 _hIcard hδ hδ' hA
  set h0 : 0 < s := by omega
  have hcard := I1PieceISum_le_cardSum (N := N) (A := A) g δ I h0
  have hmaj := I1_piece_I_card_majorant s N A δ I h0 hs hN hδ hA
  calc
    I1PieceISum d s N A g δ I h0 ≤ I1PieceICardSum s N A δ I h0 := hcard
    _ ≤ (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
            (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2) *
          (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
            if (1 : ℝ) ≤ δ * (T : ℝ) then
              (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2
            else 0) := hmaj
    _ ≤ C * errorSize N s δ := hfin N δ hN hδ hδ'

theorem I1_piece_II (d : ℕ) :
    ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (I : Finset (Fin s)) (hN : 3 ≤ N)
        (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
        (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A),
        I1PieceIISum d s N A g δ I (by omega) ≤ C * errorSize N s δ := by
  intro s hs
  obtain ⟨C, hC, hfin⟩ := I1_piece_II_weighted_le_error s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ I hN _hI0 _hIcard hδ hδ' hA
  set h0 : 0 < s := by omega
  have hcard := I1PieceIISum_le_cardSum (N := N) (A := A) g δ I h0
  have hmaj := I1_piece_II_card_majorant s N A δ I h0 hs hN hδ hA
  calc
    I1PieceIISum d s N A g δ I h0 ≤ I1PieceIICardSum s N A δ I h0 := hcard
    _ ≤ (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) *
          (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
            (tau s T : ℝ) * (tau (s - 1) T : ℝ) / (T : ℝ) ^ 2) *
          (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
            if (1 : ℝ) ≤ δ * (e : ℝ) then
              (tau s e : ℝ) * (tau (s - 1) e : ℝ) / (e : ℝ) ^ 2
            else 0) := hmaj
    _ ≤ C * errorSize N s δ := hfin N δ hN hδ hδ'

end RMFLean
