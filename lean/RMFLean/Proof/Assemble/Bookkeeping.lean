/-
PDF §2.6 analytic / combinatorial bookkeeping used by the assembly of Theorem 1.

These are the same grade of packaging lemmas as `log_pow_le_tailQ` /
`J2_error_absorbed`: no new number-theoretic content beyond Propositions 1–2.
-/
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.SparseComplement
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.F1.PropF1
import RMFLean.Proof.Intersection.PropIntersection
import RMFLean.Proof.Assemble.IntersectionSym
import RMFLean.Proof.Assemble.InclusionExclusion
import RMFLean.Proof.Setup.TailQAbsorb
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

open Classical Real Complex Filter Topology Asymptotics

namespace RMFLean

/--
Unified Diophantine exponent for Theorem 1: Prop 2's Piece III lift
`Lem5Cd + 3d + 2` (dominates Prop 1's `Lem5Cd`).
-/
noncomputable def CdStar (d : ℕ) : ℝ :=
  Lem5Cd d + (3 : ℝ) * (d : ℝ) + 2

theorem CdStar_ge_Lem5Cd (d : ℕ) : Lem5Cd d ≤ CdStar d := by
  simp only [CdStar]; linarith [Lem5Cd_gt5 d]

theorem CdStar_eq_Int_exp (d : ℕ) :
    CdStar d = Lem5Cd d + (3 : ℝ) * (d : ℝ) + 2 :=
  rfl

theorem CdStar_pos (d : ℕ) : 0 < CdStar d :=
  lt_of_lt_of_le (lt_trans (by norm_num : (0 : ℝ) < 5) (Lem5Cd_gt5 d))
    (CdStar_ge_Lem5Cd d)
noncomputable def windowLo (Cd : ℝ) : ℝ := Cd + 2
noncomputable def windowHi (Cd : ℝ) : ℝ := Cd + 3
noncomputable def assembleC (s : ℕ) (Cd : ℝ) : ℝ :=
  1 / (2 * (1 + 2 * (s : ℝ) * (Cd + 3)))

theorem assembleC_pos (s : ℕ) {Cd : ℝ} (hCd : 0 < Cd) : 0 < assembleC s Cd := by
  have hden : 0 < 2 * (1 + 2 * (s : ℝ) * (Cd + 3)) := by positivity
  simpa [assembleC] using (inv_pos.2 hden)

theorem assembleC_mul_den (s : ℕ) (Cd : ℝ) (_hCd : 0 < Cd) :
    assembleC s Cd * (1 + 2 * (s : ℝ) * (Cd + 3)) = 1 / 2 := by
  have hden : (2 * (1 + 2 * (s : ℝ) * (Cd + 3)) : ℝ) ≠ 0 := by positivity
  simp only [assembleC]
  field_simp [hden]

theorem polylog_le_sqrt (s : ℕ) :
    ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) ≤ Real.sqrt (N : ℝ) := by
  set k : ℕ := (s + 1) ^ 2
  have hlo :
      (fun x : ℝ => Real.log x ^ (k : ℝ)) =o[atTop]
        fun x => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num)
  have htend :
      Tendsto (fun x : ℝ =>
        (2 * (s : ℝ)) ^ k * Real.log x ^ (k : ℝ) /
          x ^ (1 / 2 : ℝ)) atTop (nhds 0) :=
    (hlo.const_mul_left ((2 * (s : ℝ)) ^ k)).tendsto_div_nhds_zero
  have hev :
      ∀ᶠ x : ℝ in atTop,
        (2 * (s : ℝ) * Real.log x) ^ k ≤ Real.sqrt x := by
    filter_upwards [(tendsto_order.1 htend).2 (1 : ℝ) (by norm_num),
      eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := lt_trans (by norm_num) hx1
    have hden : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hmul :
        (2 * (s : ℝ) * Real.log x) ^ k =
          (2 * (s : ℝ)) ^ k * Real.log x ^ k := mul_pow _ _ _
    have hrpow : Real.log x ^ k = Real.log x ^ (k : ℝ) :=
      (Real.rpow_natCast (Real.log x) k).symm
    have hle :
        (2 * (s : ℝ)) ^ k * Real.log x ^ (k : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← div_le_one₀ hden]
      exact le_of_lt hx
    calc
      (2 * (s : ℝ) * Real.log x) ^ k
          = (2 * (s : ℝ)) ^ k * Real.log x ^ k := hmul
      _ = (2 * (s : ℝ)) ^ k * Real.log x ^ (k : ℝ) := by rw [hrpow]
      _ ≤ x ^ (1 / 2 : ℝ) := hle
      _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 hev
  refine ⟨Nat.ceil x0, ?_⟩
  intro N hN
  exact hx0 (N : ℝ) (le_trans (Nat.le_ceil x0) (Nat.cast_le.2 hN))

theorem sqrt_add_one_lt (N : ℕ) (hN : 3 ≤ N) :
    Real.sqrt (N : ℝ) + 1 < (N : ℝ) := by
  have hsq : Real.sqrt (N : ℝ) < (N : ℝ) - 1 := by
    rw [Real.sqrt_lt (by positivity) (by linarith [show (3 : ℝ) ≤ N from by exact_mod_cast hN])]
    nlinarith [sq_nonneg ((N : ℝ) - 2), show (3 : ℝ) ≤ N from by exact_mod_cast hN]
  linarith

/-- Core absorption: polylog bound + δ > N^{-C} ⇒ sparse majorant ≤ errorSize. -/
theorem sparse_window_absorb (s N : ℕ) (δ Cd C : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hCd : 0 < Cd) (hδ : 0 < δ)
    (hC : C = assembleC s Cd)
    (hδlo : Real.rpow (N : ℝ) (-C) < δ) (hδ1 : δ ≤ 1)
    (hpoly : (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) ≤ Real.sqrt (N : ℝ)) :
    (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
        (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) ≤
      errorSize N s δ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hN
  have hC_half : C * (1 + 2 * (s : ℝ) * (Cd + 3)) = 1 / 2 := by
    rw [hC]; exact assembleC_mul_den s Cd hCd
  have hδpow :
      Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) <
        Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) := by
    have hexp : 0 < 1 + 2 * (s : ℝ) * (Cd + 3) := by positivity
    have h :
        Real.rpow (Real.rpow (N : ℝ) (-C)) (1 + 2 * (s : ℝ) * (Cd + 3)) <
          Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) :=
      Real.rpow_lt_rpow (Real.rpow_pos_of_pos hNpos _).le hδlo hexp
    have hrw :
        Real.rpow (Real.rpow (N : ℝ) (-C)) (1 + 2 * (s : ℝ) * (Cd + 3)) =
          Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) := by
      have hmul :=
        (Real.rpow_mul hNpos.le (-C) (1 + 2 * (s : ℝ) * (Cd + 3))).symm
      refine hmul.trans ?_
      congr 1
      linarith [hC_half]
    rwa [hrw] at h
  have htail_ge1 : (1 : ℝ) ≤ tailQ N s := tailQ_ge_one_of N s hs hN
  have hs_ge1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  -- Reduce polylog to √N.
  have hstep1 :
      (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
          (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) ≤
        (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
          Real.sqrt (N : ℝ) := by
    refine mul_le_mul_of_nonneg_left hpoly ?_
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hδ.le _)
  refine hstep1.trans ?_
  -- N^{s-1} √N = N^{s-1/2}
  have hNcomb :
      (N : ℝ) ^ (s - 1) * Real.sqrt (N : ℝ) =
        Real.rpow (N : ℝ) ((s : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs_ge1, Nat.cast_one]
    rw [hsub]; ring
  -- N^{s-1/2} = N^{-1/2} N^s
  have hNsplit :
      Real.rpow (N : ℝ) ((s : ℝ) - 1 / 2) =
        Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) * (N : ℝ) ^ s := by
    calc
      Real.rpow (N : ℝ) ((s : ℝ) - 1 / 2)
          = Real.rpow (N : ℝ) (-(1 / 2 : ℝ) + (s : ℝ)) := by congr 1; ring
      _ = Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) * Real.rpow (N : ℝ) (s : ℝ) :=
          Real.rpow_add hNpos _ _
      _ = Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) * (N : ℝ) ^ s := by
          congr 1
          exact Real.rpow_natCast (N : ℝ) s
  -- Main comparison
  have hmain :
      Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
          Real.rpow (N : ℝ) ((s : ℝ) - 1 / 2) ≤
        δ * (N : ℝ) ^ s * tailQ N s := by
    rw [hNsplit]
    have h1 :
        Real.rpow (N : ℝ) (-(1 / 2 : ℝ)) * (N : ℝ) ^ s ≤
          Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right (le_of_lt hδpow) (pow_nonneg (Nat.cast_nonneg _) _)
    have h2 :
        Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s ≤
          Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s * tailQ N s := by
      have hnn :
          0 ≤ Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s :=
        mul_nonneg (Real.rpow_nonneg hδ.le _) (pow_nonneg (Nat.cast_nonneg _) _)
      simpa [mul_assoc] using (le_mul_of_one_le_right hnn htail_ge1)
    have h3 := h1.trans h2
    have hz :=
      mul_le_mul_of_nonneg_left h3
        (Real.rpow_nonneg hδ.le (-(2 * (s : ℝ) * (Cd + 3))))
    have hsum :
        Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
            Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) =
          δ := by
      have hadd :=
        (Real.rpow_add hδ (-(2 * (s : ℝ) * (Cd + 3)))
          (1 + 2 * (s : ℝ) * (Cd + 3))).symm
      refine hadd.trans ?_
      have h1 : -(2 * (s : ℝ) * (Cd + 3)) + (1 + 2 * (s : ℝ) * (Cd + 3)) = (1 : ℝ) := by
        ring
      rw [h1, Real.rpow_one]
    have hrw :
        Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
            (Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s *
              tailQ N s) =
          δ * (N : ℝ) ^ s * tailQ N s := by
      calc
        Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
            (Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3)) * (N : ℝ) ^ s *
              tailQ N s)
            = (Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
                Real.rpow δ (1 + 2 * (s : ℝ) * (Cd + 3))) *
              ((N : ℝ) ^ s * tailQ N s) := by ring
        _ = δ * ((N : ℝ) ^ s * tailQ N s) := by rw [hsum]
        _ = δ * (N : ℝ) ^ s * tailQ N s := by ring
    exact hz.trans_eq hrw
  -- Finish
  have : (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
      Real.sqrt (N : ℝ) ≤ errorSize N s δ := by
    calc
      (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
          Real.sqrt (N : ℝ)
          = Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
              ((N : ℝ) ^ (s - 1) * Real.sqrt (N : ℝ)) := by ring
      _ = Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
            Real.rpow (N : ℝ) ((s : ℝ) - 1 / 2) := by rw [hNcomb]
      _ ≤ δ * (N : ℝ) ^ s * tailQ N s := hmain
      _ ≤ errorSize N s δ :=
          delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN
  exact this

theorem assemble_choose_A (_d s : ℕ) (hs : 2 ≤ s) (Cd : ℝ)
    (hCd : 0 < Cd) :
    ∃ C : ℝ, 0 < C ∧
      ∃ N0 : ℕ,
        ∀ N : ℕ, N0 ≤ N →
          3 ≤ N →
            ∀ δ : ℝ, Real.rpow (N : ℝ) (-C) < δ →
              δ < 1 / 8 →
                ∃ A : ℕ, 2 ≤ A ∧ A < N ∧
                  Real.rpow δ (-windowLo Cd) < (A : ℝ) ∧
                  (A : ℝ) < Real.rpow δ (-windowHi Cd) ∧
                  ((sparseComplementFinset (s := s) (N := N) A
                      (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs)).card : ℝ) ≤
                    errorSize N s δ := by
  set C : ℝ := assembleC s Cd
  have hCpos : 0 < C := assembleC_pos s hCd
  have hC_half : C * (1 + 2 * (s : ℝ) * (Cd + 3)) = 1 / 2 :=
    assembleC_mul_den s Cd hCd
  obtain ⟨N0poly, hpoly⟩ := polylog_le_sqrt s
  refine ⟨C, hCpos, max 3 N0poly, ?_⟩
  intro N hN0 hN δ hδlo hδhalf
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 3) hN)
  have hNposR : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN1
  have hδpos : 0 < δ :=
    lt_trans (Real.rpow_pos_of_pos hNposR _) hδlo
  have hδ1 : δ < 1 := lt_trans hδhalf (by norm_num)
  set x : ℝ := Real.rpow δ (-windowLo Cd)
  have hxpos : 0 < x := Real.rpow_pos_of_pos hδpos _
  set A : ℕ := Nat.floor x + 1
  have hAlo : x < (A : ℝ) := by simpa [A] using Nat.lt_floor_add_one x
  have hA_le : (A : ℝ) ≤ x + 1 := by
    have : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hxpos.le
    simp only [A, Nat.cast_add, Nat.cast_one]
    linarith
  have hWinLo : Real.rpow δ (-windowLo Cd) < (A : ℝ) := by simpa [x] using hAlo
  have hx_gt1 : (1 : ℝ) < x := by
    have : (1 : ℝ) = Real.rpow δ 0 := (Real.rpow_zero δ).symm
    rw [this]
    exact Real.rpow_lt_rpow_of_exponent_gt hδpos hδ1 (by
      simp only [windowLo]; linarith [hCd])
  have hinv : (2 : ℝ) < δ⁻¹ := by
    -- `(1/8)⁻¹ < δ⁻¹ ↔ δ < 1/8`, hence `2 < δ⁻¹`
    have h :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 8) hδpos).mpr hδhalf
    have : (1 / 8 : ℝ)⁻¹ = (8 : ℝ) := by norm_num
    have h8 : (8 : ℝ) < δ⁻¹ := by rwa [this] at h
    linarith
  have hup0 : Real.rpow δ (-windowHi Cd) = δ⁻¹ * x := by
    simp only [windowHi, windowLo, x]
    calc
      Real.rpow δ (-(Cd + 3))
          = Real.rpow δ (-1 + -(Cd + 2)) := by congr 1; ring
      _ = Real.rpow δ (-1) * Real.rpow δ (-(Cd + 2)) := Real.rpow_add hδpos _ _
      _ = δ⁻¹ * Real.rpow δ (-(Cd + 2)) := by
          rw [show Real.rpow δ (-1) = δ⁻¹ from Real.rpow_neg_one δ]
  have hx1_lt : x + 1 < Real.rpow δ (-windowHi Cd) := by
    rw [hup0]
    have h2x : 2 * x < δ⁻¹ * x := mul_lt_mul_of_pos_right hinv hxpos
    have hx1_le : x + 1 ≤ 2 * x := by nlinarith [hx_gt1]
    exact lt_of_le_of_lt hx1_le h2x
  have hWinHi : (A : ℝ) < Real.rpow δ (-windowHi Cd) :=
    lt_of_le_of_lt hA_le hx1_lt
  have hA2 : 2 ≤ A := by
    have hfloor : 1 ≤ Nat.floor x := by
      apply Nat.le_floor
      exact_mod_cast (le_of_lt hx_gt1)
    exact Nat.succ_le_succ hfloor
  have hx_lt_Npow : x < Real.rpow (N : ℝ) (C * windowLo Cd) := by
    have hneg : -(windowLo Cd) < 0 := by
      simp only [windowLo]; linarith [hCd]
    have h :
        Real.rpow δ (-windowLo Cd) <
          Real.rpow (Real.rpow (N : ℝ) (-C)) (-windowLo Cd) :=
      Real.rpow_lt_rpow_of_neg (Real.rpow_pos_of_pos hNposR _) hδlo hneg
    have hrw :
        Real.rpow (Real.rpow (N : ℝ) (-C)) (-windowLo Cd) =
          Real.rpow (N : ℝ) (C * windowLo Cd) := by
      have hmul := (Real.rpow_mul hNposR.le (-C) (-windowLo Cd)).symm
      refine hmul.trans ?_
      congr 1
      ring
    exact lt_of_lt_of_eq h hrw
  have hC_lo : C * windowLo Cd ≤ 1 / 2 := by
    simp only [windowLo]
    have hle : Cd + 2 ≤ 1 + 2 * (s : ℝ) * (Cd + 3) := by
      have hs2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      nlinarith [hCd]
    exact (mul_le_mul_of_nonneg_left hle hCpos.le).trans_eq hC_half
  have hNpow_le_sqrt :
      Real.rpow (N : ℝ) (C * windowLo Cd) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hC_lo
  have hA_lt_N : A < N := by
    have hAreal : (A : ℝ) < (N : ℝ) :=
      calc
        (A : ℝ) ≤ x + 1 := hA_le
        _ < Real.rpow (N : ℝ) (C * windowLo Cd) + 1 := by linarith [hx_lt_Npow]
        _ ≤ Real.sqrt (N : ℝ) + 1 := by linarith [hNpow_le_sqrt]
        _ < (N : ℝ) := sqrt_add_one_lt N hN
    exact_mod_cast hAreal
  have hN0poly : N0poly ≤ N := le_trans (le_max_right _ _) hN0
  have hcard := sparse_complement_bound s N A hs hN hA2
  have hA_lt_hi : (A : ℝ) < Real.rpow δ (-(Cd + 3)) := by
    simpa [windowHi, add_comm Cd 3] using hWinHi
  have hApow :
      (A : ℝ) ^ (2 * s) ≤ Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) := by
    have hle : (A : ℝ) ≤ Real.rpow δ (-(Cd + 3)) := le_of_lt hA_lt_hi
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg A) hle (2 * s)
    refine hpow.trans_eq ?_
    have h1 :
        (Real.rpow δ (-(Cd + 3))) ^ (2 * s) =
          Real.rpow (Real.rpow δ (-(Cd + 3))) ((2 * s : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    have h2 :
        Real.rpow (Real.rpow δ (-(Cd + 3))) ((2 * s : ℕ) : ℝ) =
          Real.rpow δ (-(Cd + 3) * ((2 * s : ℕ) : ℝ)) :=
      (Real.rpow_mul hδpos.le _ _).symm
    refine h1.trans (h2.trans ?_)
    congr 1
    push_cast
    ring
  have hRHS :
      sparseRHS s N A ≤
        (N : ℝ) ^ (s - 1) * Real.rpow δ (-(2 * (s : ℝ) * (Cd + 3))) *
          (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) := by
    simp only [sparseRHS]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hApow (by positivity)
  have habsorb :=
    sparse_window_absorb s N δ Cd C hs hN hCd hδpos rfl hδlo hδ1.le (hpoly N hN0poly)
  refine ⟨A, hA2, hA_lt_N, hWinLo, hWinHi, ?_⟩
  exact hcard.trans (hRHS.trans habsorb)



theorem two_pow_log_pow_le_exp_gap (s : ℕ) (hs : 2 ≤ s) :
    ∃ x0 : ℝ,
      ∀ x : ℝ, x0 ≤ x →
        (2 : ℝ) ^ s * (Real.log x) ^ (s ^ 2) ≤
          Real.exp (((s : ℝ) - 1) * Real.log x / Real.log (Real.log x)) := by
  have hs1pos : (0 : ℝ) < (s : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  set a : ℝ := (s : ℝ) * Real.log 2 / ((s : ℝ) - 1)
  set b : ℝ := (s : ℝ) ^ 2 / ((s : ℝ) - 1)
  have ha0 : 0 ≤ a :=
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
      hs1pos.le
  have hevL :
      ∀ᶠ L : ℝ in atTop,
        1 ≤ L →
          (s : ℝ) * Real.log 2 * L + (s : ℝ) ^ 2 * L ^ 2 ≤
            ((s : ℝ) - 1) * Real.exp L := by
    filter_upwards [(tendsto_exp_div_pow_atTop 2).eventually_ge_atTop (a + b)] with
      L hLab
    intro hL1
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
    have haL : a * L ≤ a * L ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hL1]) ha0
    have hsum : a * L + b * L ^ 2 ≤ (a + b) * L ^ 2 := by linarith [haL]
    have hmul : (a + b) * L ^ 2 ≤ Real.exp L := by
      have : a + b ≤ Real.exp L / L ^ 2 := hLab
      rwa [le_div_iff₀ (pow_pos hLpos 2)] at this
    have hstep : a * L + b * L ^ 2 ≤ Real.exp L := le_trans hsum hmul
    have ha_def : a * ((s : ℝ) - 1) = (s : ℝ) * Real.log 2 := by
      simp only [a]; field_simp [hs1pos.ne']
    have hb_def : b * ((s : ℝ) - 1) = (s : ℝ) ^ 2 := by
      simp only [b]; field_simp [hs1pos.ne']
    calc
      (s : ℝ) * Real.log 2 * L + (s : ℝ) ^ 2 * L ^ 2
          = (a * ((s : ℝ) - 1)) * L + (b * ((s : ℝ) - 1)) * L ^ 2 := by
            rw [ha_def, hb_def]
      _ = ((s : ℝ) - 1) * (a * L + b * L ^ 2) := by ring
      _ ≤ ((s : ℝ) - 1) * Real.exp L :=
        mul_le_mul_of_nonneg_left hstep hs1pos.le
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hevL
  set M : ℝ := max L0 1
  refine ⟨Real.exp (Real.exp M), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlog_ge : Real.exp M ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 hx
  have hloglog_ge : M ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hlog_ge)).2 hlog_ge
  have hL1 : 1 ≤ Real.log (Real.log x) := le_trans (le_max_right L0 1) hloglog_ge
  have hineq := hL0 (Real.log (Real.log x)) (le_trans (le_max_left L0 1) hloglog_ge) hL1
  set L : ℝ := Real.log (Real.log x)
  have hlog1 : (1 : ℝ) < Real.log x :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 1))
      (le_trans ((Real.exp_le_exp).2 (le_max_right L0 1)) hlog_ge)
  have hexpL : Real.exp L = Real.log x := Real.exp_log (lt_trans (by norm_num) hlog1)
  have hcleared :
      (s : ℝ) * Real.log 2 * L + (s : ℝ) ^ 2 * L ^ 2 ≤
        ((s : ℝ) - 1) * Real.log x := by
    simpa [hexpL] using hineq
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hpos2 : 0 < (2 : ℝ) ^ s := by positivity
  have hposl : 0 < (Real.log x) ^ (s ^ 2) :=
    pow_pos (lt_trans (by norm_num) hlog1) _
  have hs2 : ((s ^ 2 : ℕ) : ℝ) = (s : ℝ) ^ 2 := by simp [pow_two]
  have hlogLHS :
      Real.log ((2 : ℝ) ^ s * (Real.log x) ^ (s ^ 2)) =
        (s : ℝ) * Real.log 2 + (s : ℝ) ^ 2 * L := by
    rw [Real.log_mul hpos2.ne' hposl.ne', Real.log_pow, Real.log_pow, hs2]
  have hlogle :
      Real.log ((2 : ℝ) ^ s * (Real.log x) ^ (s ^ 2)) ≤
        ((s : ℝ) - 1) * Real.log x / L := by
    rw [hlogLHS, le_div_iff₀ hLpos]
    linarith [hcleared]
  have hLHS_pos : 0 < (2 : ℝ) ^ s * (Real.log x) ^ (s ^ 2) := by positivity
  exact (Real.log_le_iff_le_exp hLHS_pos).1 (by simpa [L] using hlogle)

theorem two_pow_tailQ_le_momentError (s : ℕ) (_hs : 2 ≤ s) :
    ∃ K : ℝ, 0 < K ∧
      ∃ N0 : ℕ,
        ∀ N : ℕ, N0 ≤ N →
          3 ≤ N →
            (2 : ℝ) ^ s * tailQ N s ≤ K * momentErrorFactor N s :=
  ⟨(2 : ℝ) ^ s, by positivity, 0, fun _ _ _ => by
    simp only [momentErrorFactor]
    exact le_rfl⟩


theorem altGaussian_of_U_bound (d s N : ℕ) (g : CirclePoly d) (δ Cerr K : ℝ)
    (_hs : 2 ≤ s) (hN : 3 ≤ N) (_hδ : 0 < δ) (hCerr : 0 < Cerr) (hK : 0 < K)
    (hU :
      ‖(U d s N g : ℂ) - ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ)‖ ≤
        (2 : ℝ) ^ s * Cerr * errorSize N s δ)
    (habs : (2 : ℝ) ^ s * tailQ N s ≤ K * momentErrorFactor N s) :
    altGaussianSqrt d N s g δ (Cerr * K) := by
  have hNpos : (0 : ℝ) < (N : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 (lt_of_lt_of_le (by decide : 0 < 3) hN)) _
  have hUreal :
      |U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s| ≤
        (2 : ℝ) ^ s * Cerr * errorSize N s δ := by
    have hcast :
        (U d s N g : ℂ) - ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) =
          ((U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℝ) : ℂ) := by
      simp
    rw [hcast, Complex.norm_real] at hU
    exact hU
  have hM :
      |M d s N g - gaussianMoment s| =
        |U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s| / (N : ℝ) ^ s := by
    unfold M gaussianMoment
    have hden : (N : ℝ) ^ s ≠ 0 := ne_of_gt hNpos
    calc
      |U d s N g / (N : ℝ) ^ s - (Nat.factorial s : ℝ)|
          = |U d s N g / (N : ℝ) ^ s -
              ((Nat.factorial s : ℝ) * (N : ℝ) ^ s) / (N : ℝ) ^ s| := by
            rw [mul_div_cancel_right₀ _ hden]
      _ = |(U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s) / (N : ℝ) ^ s| := by
            rw [← sub_div]
      _ = |U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s| / |(N : ℝ) ^ s| :=
            abs_div _ _
      _ = |U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s| / (N : ℝ) ^ s := by
            rw [abs_of_pos hNpos]
  have hcalc :
      (2 : ℝ) ^ s * Cerr * errorSize N s δ / (N : ℝ) ^ s =
        Cerr * Real.sqrt δ * ((2 : ℝ) ^ s * tailQ N s) := by
    simp only [errorSize]
    field_simp [hNpos.ne']
  have hle : Cerr * Real.sqrt δ * ((2 : ℝ) ^ s * tailQ N s) ≤
      Cerr * Real.sqrt δ * (K * momentErrorFactor N s) := by
    gcongr
  calc
    |M d s N g - gaussianMoment s|
        = |U d s N g - (Nat.factorial s : ℝ) * (N : ℝ) ^ s| / (N : ℝ) ^ s := hM
    _ ≤ (2 : ℝ) ^ s * Cerr * errorSize N s δ / (N : ℝ) ^ s :=
      div_le_div_of_nonneg_right hUreal (le_of_lt hNpos)
    _ = Cerr * Real.sqrt δ * ((2 : ℝ) ^ s * tailQ N s) := hcalc
    _ ≤ Cerr * Real.sqrt δ * (K * momentErrorFactor N s) := hle
    _ = (Cerr * K) * (Real.sqrt δ * momentErrorFactor N s) := by ring

/-- Replacing the free parameter `δ` by `δ²` turns the `√δ` bound into `δ`. -/
theorem altGaussian_of_sqrt_sq {d N s : ℕ} {g : CirclePoly d} {δ Cll : ℝ}
    (hδ : 0 ≤ δ)
    (h : altGaussianSqrt d N s g (δ ^ 2) Cll) :
    altGaussian d N s g δ Cll := by
  have hsq : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq hδ
  simpa [altGaussian, altGaussianSqrt, hsq] using h

/-- Diophantine alternative at `δ²` with exponent `Cd` is the same
alternative at `δ` with exponent `2 * Cd`. -/
theorem altDiophantine_of_sq {d N : ℕ} {g : CirclePoly d} {δ Cd : ℝ}
    (hδ : 0 < δ)
    (h : altDiophantine d N g (δ ^ 2) Cd) :
    altDiophantine d N g δ (2 * Cd) := by
  obtain ⟨k, hk0, hk, hg⟩ := h
  have hpow : Real.rpow (δ ^ 2) (-Cd) = Real.rpow δ (-(2 * Cd)) := by
    have h1 : (δ : ℝ) ^ 2 = Real.rpow δ (2 : ℝ) :=
      (Real.rpow_natCast δ 2).symm
    have h2 : Real.rpow (Real.rpow δ (2 : ℝ)) (-Cd) =
        Real.rpow δ ((2 : ℝ) * (-Cd)) :=
      (Real.rpow_mul hδ.le (2 : ℝ) (-Cd)).symm
    have h3 : (2 : ℝ) * (-Cd) = -(2 * Cd) := by ring
    calc
      Real.rpow (δ ^ 2) (-Cd)
          = Real.rpow (Real.rpow δ (2 : ℝ)) (-Cd) := by rw [h1]
      _ = Real.rpow δ ((2 : ℝ) * (-Cd)) := h2
      _ = Real.rpow δ (-(2 * Cd)) := by rw [h3]
  rw [hpow] at hk hg
  exact ⟨k, hk0, hk, hg⟩

end RMFLean
