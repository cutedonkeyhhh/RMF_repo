/-
PDF Proposition 2 (`prop:intersection`).
-/
import RMFLean.Proof.Intersection.I1Bound
import RMFLean.Proof.Intersection.I2
import RMFLean.Proof.Setup.TailQAbsorb
import RMFLean.Trusted.MainTheorem
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Positivity

noncomputable section

open Classical Real

namespace RMFLean

/-- Full k-fold intersection `⋂_{i∈I} ℱ_i`. -/
def IntersectionSupport (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    Finset (Sol s N) :=
  Finset.univ.filter fun x => ∀ i ∈ I, x.memF A i h0

/-- Diagonal part of a full intersection. -/
def DiagIntersectionSupport (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    (∀ i ∈ I, x.memF A i h0) ∧ x.onDiag h0

/--
If `0 ∈ I` and `#I ≥ 2`, one may choose any second index
`ℓ ∈ I`, `ℓ ≠ 0` (PDF writes `ℓ = 2` after relabelling).
-/
theorem exists_mem_ne_zero {s : ℕ} (I : Finset (Fin s)) (h0 : 0 < s)
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) :
    ∃ ℓ ∈ I, ℓ ≠ ⟨0, h0⟩ := by
  let i0 : {i // i ∈ I} := ⟨⟨0, h0⟩, hI0⟩
  have hcard : 1 < Fintype.card {i // i ∈ I} := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i0
  exact ⟨j.1, j.2, fun h => hj (Subtype.ext h)⟩

theorem intersection_eq_offDiag_union_diag
    (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    IntersectionSupport (s := s) (N := N) A I h0 =
      I1Support (s := s) (N := N) A I h0 ∪
        DiagIntersectionSupport (s := s) (N := N) A I h0 := by
  ext x
  simp only [IntersectionSupport, I1Support, DiagIntersectionSupport,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

theorem offDiag_disjoint_diag
    (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    Disjoint
      (I1Support (s := s) (N := N) A I h0)
      (DiagIntersectionSupport (s := s) (N := N) A I h0) := by
  refine Finset.disjoint_left.2 ?_
  intro x hx1 hx2
  exact (Finset.mem_filter.1 hx1).2.2 (Finset.mem_filter.1 hx2).2.2

/--
For any chosen `ℓ ∈ I`, the diagonal intersection is contained in the
single-index diagonal support estimated by Lemma 10.
-/
theorem diagIntersection_subset_I2Support
    (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s)
    (ℓ : Fin s) (hℓI : ℓ ∈ I) :
    DiagIntersectionSupport (s := s) (N := N) A I h0 ⊆
      I2Support (s := s) (N := N) A ℓ h0 := by
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ x, hx'.2, ?_⟩
  exact hx'.1 ℓ hℓI

/--
Log powers in Lemma 10 are absorbed by `𝒬(N,s)` up to an `s`-dependent constant.
-/
theorem log_pow_le_tailQ (s : ℕ) (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2) ≤ K * tailQ N s := by
  have hsR : (0 : ℝ) < 2 * (s : ℝ) := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    positivity
  have hk : 2 * s ^ 2 - 2 ≤ tailQExp s := by
    simp only [tailQExp]
    omega
  simpa using
    const_log_pow_le_mul_tailQ s hs (2 * (s : ℝ)) hsR (2 * s ^ 2 - 2) le_rfl hk

/--
If `A ≥ δ⁻¹`, Lemma 10 upgrades to the Proposition 2 error size.
-/
theorem I2_le_errorSize (s N A : ℕ) (ℓ : Fin s)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 1 ≤ A) (hA_lt : A < N)
    (hℓ : ℓ ≠ ⟨0, by omega⟩)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAδ : (1 : ℝ) / δ ≤ (A : ℝ))
    (K : ℝ) (_hK : 0 < K)
    (habs :
      (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2) ≤ K * tailQ N s) :
    ((I2Support (s := s) (N := N) A ℓ (by omega)).card : ℝ) ≤
      (5 * K) * errorSize N s δ := by
  have hcard := I2_card_bound (s := s) (N := N) A ℓ hs hN hA hA_lt hℓ
  have hApos : 0 < (A : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hAinv : (1 : ℝ) / A ≤ δ := by
    rw [div_le_iff₀ hApos, mul_comm]
    rwa [div_le_iff₀ hδ] at hAδ
  have hRHS :
      I2RHS s N A ≤
        δ * (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2) := by
    simp only [I2RHS]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAinv (by positivity)) (by positivity)
  calc
    ((I2Support (s := s) (N := N) A ℓ (by omega)).card : ℝ)
        ≤ (5 : ℝ) * I2RHS s N A := hcard
    _ ≤ (5 : ℝ) * (δ * (N : ℝ) ^ s *
          (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2)) :=
      mul_le_mul_of_nonneg_left hRHS (by norm_num)
    _ ≤ (5 : ℝ) * (δ * (N : ℝ) ^ s * (K * tailQ N s)) := by gcongr
    _ ≤ (5 * K) * errorSize N s δ := by
      have herr := delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN
      nlinarith [herr]

/--
PDF Proposition 2: k-fold intersections are error (or Diophantine).

Exists `C_d > 0` and `C > 0`, both depending only on `d`, such that either
`|Sg(⋂ ℱ_i)| ≤ C δ N^s 𝒬`, or Diophantine with exponent `C_d`.
-/
theorem prop_intersection (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (_hN : 3 ≤ N)
          (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A) (hA_lt : A < N),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            ‖Sg g (IntersectionSupport (s := s) (N := N) A I (by omega))‖ ≤
                C * errorSize N s δ ∨
              altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  obtain ⟨Cd, hEq, hCd, hI1⟩ := I1_bound d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C₁, hC₁, hI1s⟩ := hI1 s hs
  obtain ⟨K, hK, habsAll⟩ := log_pow_le_tailQ s hs
  refine ⟨C₁ + 5 * K, by positivity, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hA_lt hAlo hAhi
  set h0 : 0 < s := by omega
  obtain ⟨ℓ, hℓI, hℓ0⟩ := exists_mem_ne_zero I h0 hI0 hIcard
  have hdiagSub :
      DiagIntersectionSupport (s := s) (N := N) A I h0 ⊆
        I2Support (s := s) (N := N) A ℓ h0 :=
    diagIntersection_subset_I2Support s N A I h0 ℓ hℓI
  -- `δ^(-(Cd+2)) < A` with `Cd > 0` implies `1/δ ≤ A`.
  have hAδ : (1 : ℝ) / δ ≤ (A : ℝ) := by
    have hδ1 : δ < 1 := lt_of_lt_of_le hδ' (by norm_num)
    have hexp : -(Cd + 2) < (-1 : ℝ) := by linarith [hCd]
    have hpow : Real.rpow δ (-1 : ℝ) < Real.rpow δ (-(Cd + 2)) :=
      Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 hexp
    have hinv : (1 : ℝ) / δ = Real.rpow δ (-1 : ℝ) := by
      calc
        (1 : ℝ) / δ = δ⁻¹ := by rw [one_div]
        _ = (Real.rpow δ (1 : ℝ))⁻¹ :=
          congrArg Inv.inv (Real.rpow_one δ).symm
        _ = Real.rpow δ (-(1 : ℝ)) :=
          (Real.rpow_neg (le_of_lt hδ) (1 : ℝ)).symm
    rw [hinv]
    exact le_of_lt (lt_trans hpow hAlo)
  have hI2card :=
    I2_le_errorSize s N A ℓ hs hN hA hA_lt hℓ0 δ hδ
      (le_of_lt (lt_trans hδ' (by norm_num))) hAδ K hK (habsAll N hN)
  have hdiagNorm :
      ‖Sg g (DiagIntersectionSupport (s := s) (N := N) A I h0)‖ ≤
        (5 * K) * errorSize N s δ := by
    calc
      ‖Sg g (DiagIntersectionSupport (s := s) (N := N) A I h0)‖
          ≤ ((DiagIntersectionSupport (s := s) (N := N) A I h0).card : ℝ) :=
        norm_Sg_le_card g _
      _ ≤ ((I2Support (s := s) (N := N) A ℓ h0).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hdiagSub
      _ ≤ (5 * K) * errorSize N s δ := hI2card
  rcases hI1s N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi with hI1n | hdio
  · refine Or.inl ?_
    have hsplit :
        Sg g (IntersectionSupport (s := s) (N := N) A I h0) =
          Sg g (I1Support (s := s) (N := N) A I h0) +
            Sg g (DiagIntersectionSupport (s := s) (N := N) A I h0) := by
      rw [intersection_eq_offDiag_union_diag s N A I h0]
      exact Finset.sum_union (offDiag_disjoint_diag s N A I h0)
    rw [hsplit]
    calc
      ‖Sg g (I1Support (s := s) (N := N) A I h0) +
          Sg g (DiagIntersectionSupport (s := s) (N := N) A I h0)‖
          ≤ ‖Sg g (I1Support (s := s) (N := N) A I h0)‖ +
              ‖Sg g (DiagIntersectionSupport (s := s) (N := N) A I h0)‖ :=
        norm_add_le _ _
      _ ≤ C₁ * errorSize N s δ + (5 * K) * errorSize N s δ :=
        add_le_add hI1n hdiagNorm
      _ = (C₁ + 5 * K) * errorSize N s δ := by ring
  · exact Or.inr hdio

end RMFLean
