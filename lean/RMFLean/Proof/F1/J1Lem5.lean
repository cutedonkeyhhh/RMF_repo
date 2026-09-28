/-
Helpers for deriving `J1_lem5_exceptional_sets` from Trusted `exponential_dichotomy`.
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field

noncomputable section

open Classical

namespace RMFLean

/-! ### Real vs nat division -/

theorem div_lt_floor_add_one (N D : ℕ) (hD : 0 < D) :
    (N : ℝ) / (D : ℝ) < ↑(N / D) + 1 := by
  have hmod : N % D < D := Nat.mod_lt _ hD
  have hdecomp : (N : ℝ) = (D : ℝ) * ↑(N / D) + ↑(N % D) := by
    exact_mod_cast (Nat.div_add_mod N D).symm
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hfrac : ↑(N % D) / (D : ℝ) < 1 := by
    rw [div_lt_one hD0]
    exact_mod_cast hmod
  calc
    (N : ℝ) / (D : ℝ) = ((D : ℝ) * ↑(N / D) + ↑(N % D)) / (D : ℝ) := by rw [hdecomp]
    _ = ↑(N / D) + ↑(N % D) / (D : ℝ) := by field_simp
    _ < ↑(N / D) + 1 := by linarith

/-! ### `cardAsymp` for Lem5 intervals -/

theorem card_Icc_one_ge (m : ℕ) (_hm : 1 ≤ m) :
    (Finset.Icc 1 m).card = m := by
  rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- `[1, ⌊N/D⌋]` has cardinality ≍ `N/D` (lower constant `1/4`). -/
theorem cardAsymp_Icc_one (N D : ℕ) (hD : 0 < D) (hND : 1 ≤ N / D) :
    cardAsymp (Finset.Icc 1 (N / D)) N D := by
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hcard : ((Finset.Icc 1 (N / D)).card : ℝ) = ↑(N / D) := by
    rw [card_Icc_one_ge _ hND]
  have h1 : (1 : ℝ) ≤ ↑(N / D) := by exact_mod_cast hND
  have hNDge : (1 : ℝ) ≤ (N : ℝ) / (D : ℝ) := by
    have hDN : D ≤ N :=
      (Nat.le_mul_of_pos_right D (lt_of_lt_of_le Nat.zero_lt_one hND)).trans
        (Nat.mul_div_le N D)
    exact (one_le_div hD0).2 (Nat.cast_le.mpr hDN)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    by_cases hsmall : (N : ℝ) / (4 * (D : ℝ)) < 1
    · exact lt_of_lt_of_le hsmall h1
    · have hge : (1 : ℝ) ≤ (N : ℝ) / (4 * (D : ℝ)) := le_of_not_gt hsmall
      have hND4 : (4 : ℝ) ≤ (N : ℝ) / (D : ℝ) := by
        have : (1 : ℝ) ≤ ((N : ℝ) / (D : ℝ)) * (1 / 4) := by
          convert hge using 1; ring
        linarith
      have hfloor : (N : ℝ) / (D : ℝ) - 1 < ↑(N / D) := by
        linarith [div_lt_floor_add_one N D hD]
      have hcmp : (N : ℝ) / (4 * (D : ℝ)) ≤ (N : ℝ) / (D : ℝ) - 1 := by
        have : ((N : ℝ) / (D : ℝ)) / 4 ≤ (N : ℝ) / (D : ℝ) - 1 := by linarith
        convert this using 1; ring
      exact lt_of_le_of_lt hcmp hfloor
  · rw [hcard]
    have hle : ↑(N / D) ≤ (N : ℝ) / (D : ℝ) := Nat.cast_div_le
    have : ↑(N / D) < 2 * (N : ℝ) / (D : ℝ) := by
      have hx : (0 : ℝ) < (N : ℝ) / (D : ℝ) := lt_of_lt_of_le (by norm_num) hNDge
      have h2 : (N : ℝ) / (D : ℝ) < 2 * (N : ℝ) / (D : ℝ) := by
        have : (N : ℝ) / (D : ℝ) < (2 : ℝ) * ((N : ℝ) / (D : ℝ)) := by linarith
        convert this using 1; ring
      exact lt_of_le_of_lt hle h2
    exact this

/-- Long fibre interval `[A, ⌊N/D⌋]` when `2A < ⌊N/D⌋`. -/
theorem cardAsymp_Icc_A_long (N D A : ℕ) (hD : 0 < D)
    (hA : 1 ≤ A) (hlong : 2 * A < N / D) :
    cardAsymp (Finset.Icc A (N / D)) N D := by
  have hle : A ≤ N / D := by omega
  have hcard_nat : (Finset.Icc A (N / D)).card = N / D - A + 1 := by
    rw [Nat.card_Icc]; omega
  have hcard : ((Finset.Icc A (N / D)).card : ℝ) = ↑(N / D - A + 1) := by
    rw [hcard_nat]
  have hNDnat : (2 : ℝ) * ↑A < ↑(N / D) := by exact_mod_cast hlong
  have hNDreal : ↑(N / D) ≤ (N : ℝ) / (D : ℝ) := Nat.cast_div_le
  have h2A : (2 : ℝ) * ↑A < (N : ℝ) / (D : ℝ) := lt_of_lt_of_le hNDnat hNDreal
  refine ⟨?_, ?_⟩
  · rw [hcard]
    have hcast : (↑(N / D - A + 1) : ℝ) = ↑(N / D) - ↑A + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
    have hgap : (↑(N / D) : ℝ) / 2 + 1 ≤ ↑(N / D) - ↑A + 1 := by
      linarith [hNDnat]
    have hlo : (N : ℝ) / (4 * (D : ℝ)) < (↑(N / D) : ℝ) / 2 + 1 := by
      have hfloor := div_lt_floor_add_one N D hD
      have hstep : (N : ℝ) / (4 * (D : ℝ)) < (↑(N / D) + 1) / 4 := by
        have : (N : ℝ) / (4 * (D : ℝ)) = ((N : ℝ) / (D : ℝ)) / 4 := by ring
        rw [this]
        exact div_lt_div_of_pos_right hfloor (by norm_num)
      have : (↑(N / D) + 1) / 4 ≤ (↑(N / D) : ℝ) / 2 + 1 := by linarith
      exact lt_of_lt_of_le hstep this
    have : (N : ℝ) / (4 * (D : ℝ)) < ↑(N / D) - ↑A + 1 :=
      lt_of_lt_of_le hlo hgap
    simpa [hcast] using this
  · rw [hcard]
    have hup1 : (↑(N / D - A + 1) : ℝ) ≤ (↑(N / D) : ℝ) + 1 := by
      exact_mod_cast (by omega : N / D - A + 1 ≤ N / D + 1)
    have hup2 : (↑(N / D) : ℝ) + 1 < 2 * (N : ℝ) / (D : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) / (D : ℝ) := by
        have : (2 : ℝ) * 1 ≤ (2 : ℝ) * ↑A :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hA) (by norm_num)
        linarith [h2A]
      have hmul : 2 * (N : ℝ) / (D : ℝ) = 2 * ((N : ℝ) / (D : ℝ)) := by ring
      rw [hmul]
      linarith [hNDreal]
    exact lt_of_le_of_lt hup1 hup2

/-- Short fibre initial segment `[1, A-1]` when `A ≤ ⌊N/D⌋ ≤ 2A` and `A ≥ 3`. -/
theorem cardAsymp_Icc_one_pred (N D A : ℕ) (hD : 0 < D)
    (hA : 3 ≤ A) (hshort : N / D ≤ 2 * A) (hND : A ≤ N / D) :
    cardAsymp (Finset.Icc 1 (A - 1)) N D := by
  have hAm : 1 ≤ A - 1 := by omega
  have hcard : ((Finset.Icc 1 (A - 1)).card : ℝ) = ↑(A - 1) := by
    rw [card_Icc_one_ge _ hAm]
  refine ⟨?_, ?_⟩
  · rw [hcard]
    have hlt : (N : ℝ) / (4 * (D : ℝ)) < ((2 : ℝ) * ↑A + 1) / 4 := by
      have hfloor := div_lt_floor_add_one N D hD
      have hle : ↑(N / D) ≤ (2 : ℝ) * ↑A := by exact_mod_cast hshort
      have hNDlt : (N : ℝ) / (D : ℝ) < (2 : ℝ) * ↑A + 1 := by linarith
      have hrw : (N : ℝ) / (4 * (D : ℝ)) = ((N : ℝ) / (D : ℝ)) / 4 := by ring
      rw [hrw]
      exact div_lt_div_of_pos_right hNDlt (by norm_num)
    have hmid : ((2 : ℝ) * ↑A + 1) / 4 ≤ ↑(A - 1) := by
      have hcast : ↑(A - 1) = (↑A : ℝ) - 1 := by
        rw [Nat.cast_sub (le_trans (by norm_num : 1 ≤ 3) hA)]; simp
      have : (3 : ℝ) ≤ ↑A := by exact_mod_cast hA
      linarith
    exact lt_of_lt_of_le hlt hmid
  · rw [hcard]
    have hA_le : (↑A : ℝ) ≤ ↑(N / D) := by exact_mod_cast hND
    have hfloor : ↑(N / D) ≤ (N : ℝ) / (D : ℝ) := Nat.cast_div_le
    have hcast : ↑(A - 1) = (↑A : ℝ) - 1 := by
      rw [Nat.cast_sub (le_trans (by norm_num : 1 ≤ 3) hA)]; simp
    have hx : (0 : ℝ) < (N : ℝ) / (D : ℝ) := by
      have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
      have hDN : D ≤ N := by
        have hpos : 0 < N / D :=
          lt_of_lt_of_le Nat.zero_lt_one (le_trans (by omega : 1 ≤ A) hND)
        exact (Nat.le_mul_of_pos_right D hpos).trans (Nat.mul_div_le N D)
      have : (1 : ℝ) ≤ (N : ℝ) / (D : ℝ) :=
        (one_le_div hD0).2 (Nat.cast_le.mpr hDN)
      linarith
    have : ↑(A - 1) < 2 * (N : ℝ) / (D : ℝ) := by
      have hmul : 2 * (N : ℝ) / (D : ℝ) = 2 * ((N : ℝ) / (D : ℝ)) := by ring
      rw [hmul]
      linarith
    exact this

/-! ### A-range consequences -/

theorem rpow_neg_Cd_gt_three (δ Cd : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (hCd : 5 < Cd) : (3 : ℝ) < Real.rpow δ (-Cd) := by
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ' (by norm_num)
  have hrpow : Real.rpow δ (-5) < Real.rpow δ (-Cd) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith : (-Cd : ℝ) < -5)
  have hinv : (2 : ℝ) ≤ δ⁻¹ :=
    (inv_anti₀ hδ (le_of_lt hδ')).trans' (by norm_num)
  have hpow : Real.rpow (2 : ℝ) 5 ≤ Real.rpow (δ⁻¹) 5 :=
    Real.rpow_le_rpow (by norm_num) hinv (by norm_num)
  have heq : Real.rpow δ (-5) = Real.rpow (δ⁻¹) 5 :=
    (Real.rpow_neg (le_of_lt hδ) (5 : ℝ)).trans
      (Real.inv_rpow (le_of_lt hδ) (5 : ℝ)).symm
  have h32 : (32 : ℝ) ≤ Real.rpow δ (-5) := by
    rw [heq]
    exact le_trans (by norm_num : (32 : ℝ) ≤ Real.rpow (2 : ℝ) 5) hpow
  linarith

theorem A_ge_three (δ Cd : ℝ) (A : ℕ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd : 5 < Cd)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ)) : 3 ≤ A := by
  have hlt : (3 : ℝ) < (A : ℝ) :=
    lt_trans (rpow_neg_Cd_gt_three δ Cd hδ hδ' hCd) hAlo
  by_contra h
  push Not at h
  have : (A : ℝ) ≤ 2 := by exact_mod_cast (Nat.le_of_lt_succ h)
  linarith

@[deprecated A_ge_three (since := "2026-08-04")]
abbrev A_ge_three_of_A_range := A_ge_three

theorem badDilates_subset_Icc (d : ℕ) (g : CirclePoly d) (δ : ℝ)
    (N D : ℕ) (L : Finset ℕ) :
    badDilates d g δ N D L ⊆ Finset.Icc 1 (D - 1) :=
  Finset.filter_subset _ _

theorem N_div_D_gt_rpow_neg_Cd (δ Cd : ℝ) (A N D : ℕ)
    (hδ : 0 < δ) (hAlo : Real.rpow δ (-Cd) < (A : ℝ))
    (hhead : A ≤ N / D) (hD : 0 < D) :
    (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd) := by
  have hND : (A : ℝ) ≤ (N : ℝ) / (D : ℝ) :=
    (Nat.cast_le.mpr hhead).trans Nat.cast_div_le
  linarith

/-- Upper A-window `A < δ^{-(3+Cd)}` is defeq to Lem5 left-endpoint shape. -/
theorem lo_lt_rpow_neg_Cd_add_three (δ Cd : ℝ) (lo : ℕ)
    (hlo : (lo : ℝ) < Real.rpow δ (-(3 + Cd))) :
    (lo : ℝ) < Real.rpow δ (-(Cd + 3)) := by
  simpa [add_comm 3 Cd] using hlo

@[deprecated lo_lt_rpow_neg_Cd_add_three (since := "2026-08-05")]
theorem lo_lt_rpow_neg_Cd_add_two (δ Cd : ℝ) (lo : ℕ)
    (hlo : (lo : ℝ) < Real.rpow δ (-(3 + Cd))) :
    (lo : ℝ) < Real.rpow δ (-(Cd + 3)) :=
  lo_lt_rpow_neg_Cd_add_three δ Cd lo hlo

theorem one_lt_rpow_neg_Cd_add_three (δ Cd : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd : 0 < Cd)
    (hA : (1 : ℝ) < Real.rpow δ (-(3 + Cd))) :
    (1 : ℝ) < Real.rpow δ (-(Cd + 3)) := by
  simpa [add_comm 3 Cd] using hA

@[deprecated one_lt_rpow_neg_Cd_add_three (since := "2026-08-05")]
theorem one_lt_rpow_neg_Cd_add_two (δ Cd : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd : 0 < Cd)
    (hA : (1 : ℝ) < Real.rpow δ (-(3 + Cd))) :
    (1 : ℝ) < Real.rpow δ (-(Cd + 3)) :=
  one_lt_rpow_neg_Cd_add_three δ Cd hδ hδ' hCd hA

theorem not_mem_badDilates_norm_le {d : ℕ} (g : CirclePoly d) (δ : ℝ)
    (N D : ℕ) (L : Finset ℕ) (c : ℕ)
    (hc : c ∈ Finset.Icc 1 (D - 1))
    (hc' : c ∉ badDilates d g δ N D L) :
    ‖expSum d g c D L‖ ≤ δ * (N : ℝ) / D := by
  by_contra hgt
  push Not at hgt
  exact hc' (by
    simp only [badDilates, Finset.mem_filter, hc, true_and]
    exact hgt)

/-- Trusted Lemma 5 bad branch when Diophantine alternative is excluded. -/
theorem lem5_badDilates_card (d : ℕ) (g : CirclePoly d) (δ Cd Cbad : ℝ)
    (N : ℕ) (hCbad : 0 < Cbad)
    (hlem :
      ∀ (g' : CirclePoly d) (δ' : ℝ) (N' D' lo hi : ℕ),
        0 < δ' → δ' < 1 / 8 → 0 < D' → D' < N' →
          (N' : ℝ) / (D' : ℝ) > Real.rpow δ' (-Cd) →
          let L := intInterval lo hi
          1 ≤ lo → hi ≤ 2 * (N' / D') → cardAsymp L N' D' →
          (lo : ℝ) < Real.rpow δ' (-(Cd + 3)) →
          ((badDilates d g' δ' N' D' L).card : ℝ) ≤ Cbad * δ' * (D' : ℝ) ∨
            ∃ K : ℤ, K ≠ 0 ∧
              (|K| : ℝ) ≤ Real.rpow δ' (-Cd) ∧
              (K • g').cInfinityNorm N' ≤ Real.rpow δ' (-Cd))
    (hNotDio : ¬ altDiophantine d N g δ Cd)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (D lo hi : ℕ) (hD : 0 < D) (hDN : D < N)
    (hND : (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd))
    (hlo : 1 ≤ lo) (hhi : hi ≤ 2 * (N / D))
    (hcard : cardAsymp (intInterval lo hi) N D)
    (hloδ : (lo : ℝ) < Real.rpow δ (-(Cd + 3))) :
    ((badDilates d g δ N D (intInterval lo hi)).card : ℝ) ≤
      Cbad * δ * (D : ℝ) := by
  rcases hlem g δ N D lo hi hδ hδ' hD hDN hND hlo hhi hcard hloδ with hb | hdio
  · exact hb
  · exact absurd hdio hNotDio

end RMFLean
