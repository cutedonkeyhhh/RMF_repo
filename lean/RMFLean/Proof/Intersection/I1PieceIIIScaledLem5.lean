/-
Scaled Lemma 5 packaging for Piece III: apply Trusted `exponential_dichotomy`
to `g_h = g.compMul h` at scale `N/h` with lower endpoint `ceil(A/h)`.
-/
import RMFLean.Proof.F1.J1LongShort
import RMFLean.Proof.F1.J1Lem5
import RMFLean.Trusted.Axioms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex Real

namespace RMFLean

/-! ### Scaled head ↔ `expSum` on `g_h` -/

theorem Nat_div_h_mul_eq {N h M : ℕ} (_hh : 1 ≤ h) (_hM : 1 ≤ M) :
    N / (h * M) = (N / h) / M := by
  rw [Nat.div_div_eq_div_mul]

theorem J1InnerSumScaled_eq_expSum {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) :
    J1InnerSumScaled g k N A h h0 =
      expSum d (g.compMul h) (k.rowOffDiag ⟨0, h0⟩) (k.colOffDiag ⟨0, h0⟩)
        (keyHeadFibreScaled k N A h h0) := by
  simp only [J1InnerSumScaled, expSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simpa using
    ePhase_mul_star_eq_expSum_term (g.compMul h) n
      (k.rowOffDiag ⟨0, h0⟩) (k.colOffDiag ⟨0, h0⟩)

theorem norm_J1InnerSumScaled_eq_expSum_swap {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) :
    ‖J1InnerSumScaled g k N A h h0‖ =
      ‖expSum d (g.compMul h) (k.colOffDiag ⟨0, h0⟩) (k.rowOffDiag ⟨0, h0⟩)
        (keyHeadFibreScaled k N A h h0)‖ := by
  rw [J1InnerSumScaled_eq_expSum, expSum_star_swap, norm_star]

theorem J1InnerSumScaled_eq_zero_of_empty {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s)
    (hempty : keyHeadFibreScaled k N A h h0 = ∅) :
    J1InnerSumScaled g k N A h h0 = 0 := by
  simp [J1InnerSumScaled, hempty]

theorem keyHeadFibreScaled_eq_empty_iff {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hA1 : 1 ≤ A) (hh : 1 ≤ h) :
    keyHeadFibreScaled k N A h h0 = ∅ ↔
      N / (h * keyScale k ⟨0, h0⟩) < scaledHeadLo A h := by
  rw [keyHeadFibreScaled_eq_Icc k N A h h0 hA1 hh, Finset.Icc_eq_empty_iff, not_le]

theorem Nh_div_le_N_div_h_div (N h B : ℕ) (_hh : 0 < h) (_hB : 0 < B) :
    ((N / h : ℕ) : ℝ) / (B : ℝ) ≤ ((N : ℝ) / (h : ℝ)) / (B : ℝ) := by
  exact div_le_div_of_nonneg_right Nat.cast_div_le (Nat.cast_nonneg _)

/-! ### Pointwise scaled Lem5 -/

theorem lem5_pointwise_scaled_A_lt_B (d : ℕ) (g : CirclePoly d) (δ Cd : ℝ)
    (s N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd5 : 5 < Cd)
    (hA1 : 1 ≤ A)
    (hA'lo : Real.rpow δ (-Cd) < (scaledHeadLo A h : ℝ))
    (_hA'hi : (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd)))
    (R : ℕ → Finset ℕ)
    (hR : ∀ D : ℕ,
      R D = lem5ExceptionalSet d (g.compMul h) δ Cd (N / h) (scaledHeadLo A h) D)
    (k : MatrixParam s) (hk : k ∈ PieceIIIFibres_A_lt_B s N h0) :
    ‖J1InnerSumScaled g k N A h h0‖ ≤
      (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, h0⟩) +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, h0⟩) else 0) := by
  set A' := scaledHeadLo A h
  set gh := g.compMul h
  set Nh := N / h
  have hkIII : k ∈ PieceIIIFibres s N := (Finset.mem_filter.1 hk).1
  have hAB : k.rowOffDiag ⟨0, h0⟩ < k.colOffDiag ⟨0, h0⟩ :=
    (Finset.mem_filter.1 hk).2
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = B1 := max_eq_right (Nat.le_of_lt hAB)
  have hA'3 : 3 ≤ A' := A_ge_three δ Cd A' hδ hδ' hCd5 hA'lo
  have hApos : 0 < A1 := k.rowOffDiag_pos ⟨0, h0⟩
  have hBpos : 0 < B1 := Finset.prod_pos fun _ _ => k.entries_pos _ _
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hB1ge : 1 ≤ B1 := Nat.succ_le_of_lt hBpos
  by_cases hempty : keyHeadFibreScaled k N A h h0 = ∅
  · have hz := J1InnerSumScaled_eq_zero_of_empty g k N A h h0 hempty
    rw [hz, norm_zero]
    refine add_nonneg (by positivity) ?_
    split_ifs <;> positivity
  · have hhead : A' ≤ N / (h * B1) := by
      have :=
        (not_iff_not.2 (keyHeadFibreScaled_eq_empty_iff k N A h h0 hA1 hh)).1 hempty
      simpa [hM, not_lt] using this
    have hheadNh : A' ≤ Nh / B1 := by
      simpa [Nh, Nat_div_h_mul_eq hh hB1ge, hM] using hhead
    have hBNh : B1 < Nh := by
      by_contra hge
      have hle : Nh / B1 ≤ 1 := by
        have hNhle : Nh ≤ B1 := le_of_not_gt hge
        rcases eq_or_lt_of_le hNhle with heq | hlt
        · have hpos : 0 < Nh := heq ▸ hBpos
          simpa [heq.symm, Nat.div_self hpos]
        · simpa [Nat.div_eq_of_lt hlt]
      exact (not_le_of_gt (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hA'3))
        (le_trans hheadNh hle)
    have hND : (Nh : ℝ) / (B1 : ℝ) > Real.rpow δ (-Cd) :=
      N_div_D_gt_rpow_neg_Cd δ Cd A' Nh B1 hδ hA'lo hheadNh hBpos
    have hguard : 0 < B1 ∧ B1 < Nh ∧ (Nh : ℝ) / (B1 : ℝ) > Real.rpow δ (-Cd) :=
      ⟨hBpos, hBNh, hND⟩
    set Llong := intInterval A' (Nh / B1)
    set Lshort1 := intInterval 1 (Nh / B1)
    set Lshort2 := intInterval 1 (A' - 1)
    set badLong :=
      if 2 * A' < Nh / B1 then badDilates d gh δ Nh B1 Llong else (∅ : Finset ℕ)
    set badShort1 :=
      if A' ≤ Nh / B1 ∧ Nh / B1 ≤ 2 * A' then badDilates d gh δ Nh B1 Lshort1
      else (∅ : Finset ℕ)
    set badShort2 :=
      if A' ≤ Nh / B1 ∧ Nh / B1 ≤ 2 * A' ∧ 3 ≤ A' then
        badDilates d gh δ Nh B1 Lshort2
      else (∅ : Finset ℕ)
    have hRval : R B1 = badLong ∪ badShort1 ∪ badShort2 := by
      rw [hR]
      simp only [lem5ExceptionalSet, dif_pos hguard, badLong, badShort1, badShort2,
        Llong, Lshort1, Lshort2, gh, Nh, A']
    have hIcc : A1 ∈ Finset.Icc 1 (B1 - 1) := by
      refine Finset.mem_Icc.2 ⟨Nat.one_le_of_lt hApos, Nat.le_sub_one_of_lt hAB⟩
    have hIcc_eq :
        keyHeadFibreScaled k N A h h0 = Finset.Icc A' (N / (h * B1)) := by
      simpa [hM, A'] using keyHeadFibreScaled_eq_Icc k N A h h0 hA1 hh
    have hnorm :
        ‖J1InnerSumScaled g k N A h h0‖ =
          ‖expSum d gh A1 B1 (Finset.Icc A' (N / (h * B1)))‖ := by
      rw [J1InnerSumScaled_eq_expSum, hIcc_eq]
    have hNh_le : (Nh : ℝ) ≤ (N : ℝ) / (h : ℝ) := Nat.cast_div_le
    have hlen :
        (↑(N / (h * B1)) : ℝ) ≤ ((N : ℝ) / (h : ℝ)) / B1 := by
      have hrew : (↑(N / (h * B1)) : ℝ) = ↑(Nh / B1) := by
        rw [Nat_div_h_mul_eq hh hB1ge]
      have h1 : (↑(Nh / B1) : ℝ) ≤ (Nh : ℝ) / B1 := Nat.cast_div_le
      have h2 : (Nh : ℝ) / B1 ≤ ((N : ℝ) / (h : ℝ)) / B1 :=
        div_le_div_of_nonneg_right hNh_le (Nat.cast_nonneg _)
      exact hrew ▸ (h1.trans h2)
    have htriv :
        ‖J1InnerSumScaled g k N A h h0‖ ≤ ((N : ℝ) / (h : ℝ)) / B1 := by
      rw [hnorm]
      refine le_trans (norm_expSum_le_card gh A1 B1 _) ?_
      have hc : ((Finset.Icc A' (N / (h * B1))).card : ℝ) ≤ ↑(N / (h * B1)) := by
        exact_mod_cast (by rw [Nat.card_Icc]; omega)
      exact le_trans hc hlen
    have hδ_lift :
        δ * (Nh : ℝ) / B1 ≤ δ * ((N : ℝ) / (h : ℝ)) / B1 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNh_le hδ.le)
        (Nat.cast_nonneg _)
    by_cases hmem : A1 ∈ R B1
    · simp only [hmem, ↓reduceIte]
      linarith [htriv, show (0 : ℝ) ≤ (2 * δ) * ((N : ℝ) / (h : ℝ)) / B1 by positivity]
    · simp only [hmem, ↓reduceIte, add_zero]
      have hnotin_union : A1 ∉ badLong ∪ badShort1 ∪ badShort2 := by
        simpa [hRval] using hmem
      have hheadKey : A' ≤ Nh / keyScale k ⟨0, h0⟩ := by simpa [hM] using hheadNh
      have hLS := key_long_or_short (N := Nh) (A := A') k h0 hheadKey
      rcases hLS with hLong | hShort
      · have hLong' : 2 * A' < Nh / B1 := by simpa [KeyIsLong, hM, Nh] using hLong
        have hbadEq : badLong = badDilates d gh δ Nh B1 Llong := by
          simp [badLong, hLong']
        have hnotin : A1 ∉ badDilates d gh δ Nh B1 Llong := by
          intro hin; exact hnotin_union (by simp [hbadEq, hin])
        have hle := not_mem_badDilates_norm_le gh δ Nh B1 Llong A1
          (by simpa [Llong, intInterval] using hIcc) hnotin
        have hle' :
            ‖expSum d gh A1 B1 (Finset.Icc A' (N / (h * B1)))‖ ≤
              δ * (Nh : ℝ) / B1 := by
          simpa [Llong, intInterval, Nat_div_h_mul_eq hh hB1ge, Nh] using hle
        have hδle : δ * (Nh : ℝ) / B1 ≤ (2 * δ) * ((N : ℝ) / (h : ℝ)) / B1 := by
          have h2 : δ * ((N : ℝ) / (h : ℝ)) / B1 ≤
              (2 * δ) * ((N : ℝ) / (h : ℝ)) / B1 := by
            have : (δ : ℝ) ≤ 2 * δ := by linarith [le_of_lt hδ]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right this (by positivity)) (Nat.cast_nonneg _)
          exact le_trans hδ_lift h2
        exact le_trans (by simpa [hnorm] using hle') hδle
      · have hShort' : A' ≤ Nh / B1 ∧ Nh / B1 ≤ 2 * A' := by
          simpa [KeyIsShort, hM, Nh] using hShort
        have hA'2 : 2 ≤ A' := le_trans (by norm_num : 2 ≤ 3) hA'3
        have hdiff :
            expSum d gh A1 B1 (Finset.Icc A' (N / (h * B1))) =
              expSum d gh A1 B1 (Finset.Icc 1 (Nh / B1)) -
                expSum d gh A1 B1 (Finset.Icc 1 (A' - 1)) := by
          simpa [Nh, Nat_div_h_mul_eq hh hB1ge] using
            expSum_Icc_A_eq_sub gh A1 B1 Nh A' hA'2 hShort'.1
        have hbad1 : badShort1 = badDilates d gh δ Nh B1 Lshort1 := by
          simp [badShort1, hShort']
        have hbad2 : badShort2 = badDilates d gh δ Nh B1 Lshort2 := by
          simp [badShort2, hShort', hA'3]
        have hnotin1 : A1 ∉ badDilates d gh δ Nh B1 Lshort1 := by
          intro hin; apply hnotin_union; simp [hbad1, hin]
        have hnotin2 : A1 ∉ badDilates d gh δ Nh B1 Lshort2 := by
          intro hin
          apply hnotin_union
          refine Finset.mem_union.2 (Or.inr ?_)
          simpa [hbad2] using hin
        have hle1 := not_mem_badDilates_norm_le gh δ Nh B1 Lshort1 A1
          (by simpa [Lshort1, intInterval] using hIcc) hnotin1
        have hle2 := not_mem_badDilates_norm_le gh δ Nh B1 Lshort2 A1
          (by simpa [Lshort2, intInterval] using hIcc) hnotin2
        have hle1' :
            ‖expSum d gh A1 B1 (Finset.Icc 1 (Nh / B1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / B1 := by
          have h0' :
              ‖expSum d gh A1 B1 (Finset.Icc 1 (Nh / B1))‖ ≤
                δ * (Nh : ℝ) / B1 := by
            simpa [Lshort1, intInterval] using hle1
          exact le_trans h0' hδ_lift
        have hle2' :
            ‖expSum d gh A1 B1 (Finset.Icc 1 (A' - 1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / B1 := by
          have h0' :
              ‖expSum d gh A1 B1 (Finset.Icc 1 (A' - 1))‖ ≤
                δ * (Nh : ℝ) / B1 := by
            simpa [Lshort2, intInterval] using hle2
          exact le_trans h0' hδ_lift
        have hsum :
            ‖expSum d gh A1 B1 (Finset.Icc A' (N / (h * B1)))‖ ≤
              (2 * δ) * ((N : ℝ) / (h : ℝ)) / B1 := by
          rw [hdiff]
          refine le_trans (norm_sub_le _ _) ?_
          calc
            ‖expSum d gh A1 B1 (Finset.Icc 1 (Nh / B1))‖ +
                ‖expSum d gh A1 B1 (Finset.Icc 1 (A' - 1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / B1 +
                δ * ((N : ℝ) / (h : ℝ)) / B1 := add_le_add hle1' hle2'
            _ = (2 * δ) * ((N : ℝ) / (h : ℝ)) / B1 := by ring
        simpa [hnorm] using hsum

theorem lem5_pointwise_scaled_B_lt_A (d : ℕ) (g : CirclePoly d) (δ Cd : ℝ)
    (s N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd5 : 5 < Cd)
    (hA1 : 1 ≤ A)
    (hA'lo : Real.rpow δ (-Cd) < (scaledHeadLo A h : ℝ))
    (_hA'hi : (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd)))
    (R : ℕ → Finset ℕ)
    (hR : ∀ D : ℕ,
      R D = lem5ExceptionalSet d (g.compMul h) δ Cd (N / h) (scaledHeadLo A h) D)
    (k : MatrixParam s) (hk : k ∈ PieceIIIFibres_B_lt_A s N h0) :
    ‖J1InnerSumScaled g k N A h h0‖ ≤
      (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, h0⟩) +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, h0⟩) else 0) := by
  set A' := scaledHeadLo A h
  set gh := g.compMul h
  set Nh := N / h
  have hkIII : k ∈ PieceIIIFibres s N := (Finset.mem_filter.1 hk).1
  have hBA : k.colOffDiag ⟨0, h0⟩ < k.rowOffDiag ⟨0, h0⟩ :=
    (Finset.mem_filter.1 hk).2
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = A1 := max_eq_left (Nat.le_of_lt hBA)
  have hA'3 : 3 ≤ A' := A_ge_three δ Cd A' hδ hδ' hCd5 hA'lo
  have hBpos : 0 < B1 := Finset.prod_pos fun _ _ => k.entries_pos _ _
  have hApos : 0 < A1 := k.rowOffDiag_pos ⟨0, h0⟩
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hA1ge : 1 ≤ A1 := Nat.succ_le_of_lt hApos
  by_cases hempty : keyHeadFibreScaled k N A h h0 = ∅
  · have hz := J1InnerSumScaled_eq_zero_of_empty g k N A h h0 hempty
    rw [hz, norm_zero]
    refine add_nonneg (by positivity) ?_
    split_ifs <;> positivity
  · have hhead : A' ≤ N / (h * A1) := by
      have :=
        (not_iff_not.2 (keyHeadFibreScaled_eq_empty_iff k N A h h0 hA1 hh)).1 hempty
      simpa [hM, not_lt] using this
    have hheadNh : A' ≤ Nh / A1 := by
      simpa [Nh, Nat_div_h_mul_eq hh hA1ge, hM] using hhead
    have hANh : A1 < Nh := by
      by_contra hge
      have hle : Nh / A1 ≤ 1 := by
        have hNhle : Nh ≤ A1 := le_of_not_gt hge
        rcases eq_or_lt_of_le hNhle with heq | hlt
        · have hpos : 0 < Nh := heq ▸ hApos
          simpa [heq.symm, Nat.div_self hpos]
        · simpa [Nat.div_eq_of_lt hlt]
      exact (not_le_of_gt (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hA'3))
        (le_trans hheadNh hle)
    have hND : (Nh : ℝ) / (A1 : ℝ) > Real.rpow δ (-Cd) :=
      N_div_D_gt_rpow_neg_Cd δ Cd A' Nh A1 hδ hA'lo hheadNh hApos
    have hguard : 0 < A1 ∧ A1 < Nh ∧ (Nh : ℝ) / (A1 : ℝ) > Real.rpow δ (-Cd) :=
      ⟨hApos, hANh, hND⟩
    set Llong := intInterval A' (Nh / A1)
    set Lshort1 := intInterval 1 (Nh / A1)
    set Lshort2 := intInterval 1 (A' - 1)
    set badLong :=
      if 2 * A' < Nh / A1 then badDilates d gh δ Nh A1 Llong else (∅ : Finset ℕ)
    set badShort1 :=
      if A' ≤ Nh / A1 ∧ Nh / A1 ≤ 2 * A' then badDilates d gh δ Nh A1 Lshort1
      else (∅ : Finset ℕ)
    set badShort2 :=
      if A' ≤ Nh / A1 ∧ Nh / A1 ≤ 2 * A' ∧ 3 ≤ A' then
        badDilates d gh δ Nh A1 Lshort2
      else (∅ : Finset ℕ)
    have hRval : R A1 = badLong ∪ badShort1 ∪ badShort2 := by
      rw [hR]
      simp only [lem5ExceptionalSet, dif_pos hguard, badLong, badShort1, badShort2,
        Llong, Lshort1, Lshort2, gh, Nh, A']
    have hIcc : B1 ∈ Finset.Icc 1 (A1 - 1) := by
      refine Finset.mem_Icc.2 ⟨Nat.one_le_of_lt hBpos, Nat.le_sub_one_of_lt hBA⟩
    have hIcc_eq :
        keyHeadFibreScaled k N A h h0 = Finset.Icc A' (N / (h * A1)) := by
      simpa [hM, A'] using keyHeadFibreScaled_eq_Icc k N A h h0 hA1 hh
    have hnorm :
        ‖J1InnerSumScaled g k N A h h0‖ =
          ‖expSum d gh B1 A1 (Finset.Icc A' (N / (h * A1)))‖ := by
      rw [norm_J1InnerSumScaled_eq_expSum_swap, hIcc_eq]
    have hNh_le : (Nh : ℝ) ≤ (N : ℝ) / (h : ℝ) := Nat.cast_div_le
    have hlen :
        (↑(N / (h * A1)) : ℝ) ≤ ((N : ℝ) / (h : ℝ)) / A1 := by
      have hrew : (↑(N / (h * A1)) : ℝ) = ↑(Nh / A1) := by
        rw [Nat_div_h_mul_eq hh hA1ge]
      have h1 : (↑(Nh / A1) : ℝ) ≤ (Nh : ℝ) / A1 := Nat.cast_div_le
      have h2 : (Nh : ℝ) / A1 ≤ ((N : ℝ) / (h : ℝ)) / A1 :=
        div_le_div_of_nonneg_right hNh_le (Nat.cast_nonneg _)
      exact hrew ▸ (h1.trans h2)
    have htriv :
        ‖J1InnerSumScaled g k N A h h0‖ ≤ ((N : ℝ) / (h : ℝ)) / A1 := by
      rw [hnorm]
      refine le_trans (norm_expSum_le_card gh B1 A1 _) ?_
      have hc : ((Finset.Icc A' (N / (h * A1))).card : ℝ) ≤ ↑(N / (h * A1)) := by
        exact_mod_cast (by rw [Nat.card_Icc]; omega)
      exact le_trans hc hlen
    have hδ_lift :
        δ * (Nh : ℝ) / A1 ≤ δ * ((N : ℝ) / (h : ℝ)) / A1 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNh_le hδ.le)
        (Nat.cast_nonneg _)
    by_cases hmem : B1 ∈ R A1
    · simp only [hmem, ↓reduceIte]
      linarith [htriv, show (0 : ℝ) ≤ (2 * δ) * ((N : ℝ) / (h : ℝ)) / A1 by positivity]
    · simp only [hmem, ↓reduceIte, add_zero]
      have hnotin_union : B1 ∉ badLong ∪ badShort1 ∪ badShort2 := by
        simpa [hRval] using hmem
      have hheadKey : A' ≤ Nh / keyScale k ⟨0, h0⟩ := by simpa [hM] using hheadNh
      have hLS := key_long_or_short (N := Nh) (A := A') k h0 hheadKey
      rcases hLS with hLong | hShort
      · have hLong' : 2 * A' < Nh / A1 := by simpa [KeyIsLong, hM, Nh] using hLong
        have hbadEq : badLong = badDilates d gh δ Nh A1 Llong := by
          simp [badLong, hLong']
        have hnotin : B1 ∉ badDilates d gh δ Nh A1 Llong := by
          intro hin; exact hnotin_union (by simp [hbadEq, hin])
        have hle := not_mem_badDilates_norm_le gh δ Nh A1 Llong B1
          (by simpa [Llong, intInterval] using hIcc) hnotin
        have hle' :
            ‖expSum d gh B1 A1 (Finset.Icc A' (N / (h * A1)))‖ ≤
              δ * (Nh : ℝ) / A1 := by
          simpa [Llong, intInterval, Nat_div_h_mul_eq hh hA1ge, Nh] using hle
        have hδle : δ * (Nh : ℝ) / A1 ≤ (2 * δ) * ((N : ℝ) / (h : ℝ)) / A1 := by
          have h2 : δ * ((N : ℝ) / (h : ℝ)) / A1 ≤
              (2 * δ) * ((N : ℝ) / (h : ℝ)) / A1 := by
            have : (δ : ℝ) ≤ 2 * δ := by linarith [le_of_lt hδ]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right this (by positivity)) (Nat.cast_nonneg _)
          exact le_trans hδ_lift h2
        exact le_trans (by simpa [hnorm] using hle') hδle
      · have hShort' : A' ≤ Nh / A1 ∧ Nh / A1 ≤ 2 * A' := by
          simpa [KeyIsShort, hM, Nh] using hShort
        have hA'2 : 2 ≤ A' := le_trans (by norm_num : 2 ≤ 3) hA'3
        have hdiff :
            expSum d gh B1 A1 (Finset.Icc A' (N / (h * A1))) =
              expSum d gh B1 A1 (Finset.Icc 1 (Nh / A1)) -
                expSum d gh B1 A1 (Finset.Icc 1 (A' - 1)) := by
          simpa [Nh, Nat_div_h_mul_eq hh hA1ge] using
            expSum_Icc_A_eq_sub gh B1 A1 Nh A' hA'2 hShort'.1
        have hbad1 : badShort1 = badDilates d gh δ Nh A1 Lshort1 := by
          simp [badShort1, hShort']
        have hbad2 : badShort2 = badDilates d gh δ Nh A1 Lshort2 := by
          simp [badShort2, hShort', hA'3]
        have hnotin1 : B1 ∉ badDilates d gh δ Nh A1 Lshort1 := by
          intro hin; apply hnotin_union; simp [hbad1, hin]
        have hnotin2 : B1 ∉ badDilates d gh δ Nh A1 Lshort2 := by
          intro hin
          apply hnotin_union
          refine Finset.mem_union.2 (Or.inr ?_)
          simpa [hbad2] using hin
        have hle1 := not_mem_badDilates_norm_le gh δ Nh A1 Lshort1 B1
          (by simpa [Lshort1, intInterval] using hIcc) hnotin1
        have hle2 := not_mem_badDilates_norm_le gh δ Nh A1 Lshort2 B1
          (by simpa [Lshort2, intInterval] using hIcc) hnotin2
        have hle1' :
            ‖expSum d gh B1 A1 (Finset.Icc 1 (Nh / A1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / A1 := by
          have h0' :
              ‖expSum d gh B1 A1 (Finset.Icc 1 (Nh / A1))‖ ≤
                δ * (Nh : ℝ) / A1 := by
            simpa [Lshort1, intInterval] using hle1
          exact le_trans h0' hδ_lift
        have hle2' :
            ‖expSum d gh B1 A1 (Finset.Icc 1 (A' - 1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / A1 := by
          have h0' :
              ‖expSum d gh B1 A1 (Finset.Icc 1 (A' - 1))‖ ≤
                δ * (Nh : ℝ) / A1 := by
            simpa [Lshort2, intInterval] using hle2
          exact le_trans h0' hδ_lift
        have hsum :
            ‖expSum d gh B1 A1 (Finset.Icc A' (N / (h * A1)))‖ ≤
              (2 * δ) * ((N : ℝ) / (h : ℝ)) / A1 := by
          rw [hdiff]
          refine le_trans (norm_sub_le _ _) ?_
          calc
            ‖expSum d gh B1 A1 (Finset.Icc 1 (Nh / A1))‖ +
                ‖expSum d gh B1 A1 (Finset.Icc 1 (A' - 1))‖ ≤
              δ * ((N : ℝ) / (h : ℝ)) / A1 +
                δ * ((N : ℝ) / (h : ℝ)) / A1 := add_le_add hle1' hle2'
            _ = (2 * δ) * ((N : ℝ) / (h : ℝ)) / A1 := by ring
        simpa [hnorm] using hsum

/-! ### Main scaled exceptional-set theorem -/

/--
Scaled long/short applications of Trusted Lemma 5 on both off-diagonal sides
over `PieceIIIFibres`, for `g_h` at scale `N/h` and `A' = ⌈A/h⌉`.
Requires the A-window on `A'`. Pointwise coefficient is `2δ` (short fibres).
-/
theorem J1_lem5_exceptional_sets_scaled (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ) (h : ℕ)
        (_hs : 2 ≤ s) (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
        (_hA : 1 ≤ A) (_hh1 : 1 ≤ h) (_hhδ : (h : ℝ) * δ ^ 2 < 1)
        (_hhN : h ≤ N),
        Real.rpow δ (-Cd) < (scaledHeadLo A h : ℝ) →
        (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd)) →
        altDiophantine d (N / h) (CirclePoly.compMul g h) δ Cd ∨
          (∃ R R' : ℕ → Finset ℕ,
            (∀ D : ℕ, 0 < D →
              ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
            (∀ D : ℕ, R D ⊆ Finset.Icc 1 (D - 1)) ∧
            (∀ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
              ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
                (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩) +
                  (if (k.rowOffDiag ⟨0, by omega⟩) ∈
                      R (k.colOffDiag ⟨0, by omega⟩) then
                    ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩)
                  else 0)) ∧
            (∀ D : ℕ, 0 < D →
              ((R' D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
            (∀ D : ℕ, R' D ⊆ Finset.Icc 1 (D - 1)) ∧
            (∀ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
              ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
                (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩) +
                  (if (k.colOffDiag ⟨0, by omega⟩) ∈
                      R' (k.rowOffDiag ⟨0, by omega⟩) then
                    ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩)
                  else 0))) := by
  set Cd := Lem5Cd d
  have hCd5 : 5 < Cd := Lem5Cd_gt5 d
  obtain ⟨Cbad, hCbad, h3Cbad, hlem⟩ := Lem5Cd_spec d
  refine ⟨Cd, rfl, hCd5, ?_⟩
  intro s N A g δ h _hs _hN hδ hδ' hA hh1 _hhδ _hhN hA'lo hA'hi
  classical
  set A' := scaledHeadLo A h
  set gh := g.compMul h
  set Nh := N / h
  rcases Classical.em (altDiophantine d Nh gh δ Cd) with hDio | hNotDio
  · exact Or.inl hDio
  · refine Or.inr ?_
    let R : ℕ → Finset ℕ := fun D => lem5ExceptionalSet d gh δ Cd Nh A' D
    refine ⟨R, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro D hD
      exact lem5ExceptionalSet_card_le d gh δ Cd Cbad Nh A' hCbad hCd5 h3Cbad hlem
        hNotDio hδ hδ' hA'lo hA'hi D hD
    · intro D
      exact lem5ExceptionalSet_subset d gh δ Cd Nh A' D
    · intro k hk
      exact lem5_pointwise_scaled_A_lt_B d g δ Cd s N A h (by omega) hh1
        hδ hδ' hCd5 hA hA'lo hA'hi R (fun _ => rfl) k hk
    · intro D hD
      exact lem5ExceptionalSet_card_le d gh δ Cd Cbad Nh A' hCbad hCd5 h3Cbad hlem
        hNotDio hδ hδ' hA'lo hA'hi D hD
    · intro D
      exact lem5ExceptionalSet_subset d gh δ Cd Nh A' D
    · intro k hk
      exact lem5_pointwise_scaled_B_lt_A d g δ Cd s N A h (by omega) hh1
        hδ hδ' hCd5 hA hA'lo hA'hi R (fun _ => rfl) k hk

end RMFLean
