/-
PDF Lemma 10 (`lem:I2`) — diagonal part of a k-fold intersection (`k ≥ 2`).

Reformalised from the user's exact-gcd outline:
  support ⊆ ⋃_{h≥A} {n₁=m₁, gcd(m₁,m_ℓ)=h} ∩ V
  (a disjoint union), each fibre ≤ ∑_{n≤N^s} τ_s(n/h²) τ_s(n),
  then convolution + Lemma 1 tail.
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.Setup.SolFinite
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Intersection.I2Fibre
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Real Classical

namespace RMFLean

/--
Diagonal support:
`{x ∈ V : n₁ = m₁ ∧ gcd(n₁, m_ℓ) ≥ A}` with `ℓ ≠ 0` (PDF: `ℓ = i₂ ≥ 2`).
Equivalent to `{n₁ = m₁ ∧ gcd(m₁, m_ℓ) ≥ A}` by the diagonal condition.
-/
def I2Support (s N A : ℕ) (ℓ : Fin s) (h0 : 0 < s) :
    Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    x.onDiag h0 ∧ A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m ℓ)

/-- PDF Lemma 10 RHS (up to the absolute `≪` constant).
Uses log-base `2 s log N` after the fibre convolution packing. -/
noncomputable def I2RHS (s N A : ℕ) : ℝ :=
  (1 / (A : ℝ)) * (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2)

/--
Exact-gcd partition: every support point lies in the unique fibre
`h = gcd(m₁, m_ℓ)`.
-/
theorem I2Support_subset_biUnion_fibres
    (s N A : ℕ) (ℓ : Fin s) (h0 : 0 < s) :
    I2Support (s := s) (N := N) A ℓ h0 ⊆
      (Finset.Icc A N).biUnion fun h => I2Fibre (s := s) (N := N) h ℓ h0 := by
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  -- On the diagonal, `gcd(n₁, m_ℓ) = gcd(m₁, m_ℓ)`.
  have hgcd_eq :
      Nat.gcd (x.n ⟨0, h0⟩) (x.m ℓ) = Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) := by
    rw [hx'.1]
  set g := Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ)
  have hgA : A ≤ g := by
    rw [← hgcd_eq]; exact hx'.2
  have hg_le_m1 : g ≤ x.m ⟨0, h0⟩ := by
    have hm1pos : 0 < x.m ⟨0, h0⟩ :=
      lt_of_lt_of_le Nat.zero_lt_one (x.hm ⟨0, h0⟩).1
    exact Nat.gcd_le_left (x.m ℓ) hm1pos
  have hgN : g ≤ N := le_trans hg_le_m1 (x.hm ⟨0, h0⟩).2
  refine Finset.mem_biUnion.2 ⟨g, Finset.mem_Icc.2 ⟨hgA, hgN⟩, ?_⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_univ x, ?_⟩
  exact ⟨hx'.1, rfl⟩

/-- Distinct exact-gcd fibres are disjoint. -/
theorem I2Fibre_disjoint {s N : ℕ} {ℓ : Fin s} {h0 : 0 < s} {h₁ h₂ : ℕ}
    (hne : h₁ ≠ h₂) :
    Disjoint
      (I2Fibre (s := s) (N := N) h₁ ℓ h0)
      (I2Fibre (s := s) (N := N) h₂ ℓ h0) := by
  refine Finset.disjoint_left.2 ?_
  intro x hx1 hx2
  have h1 : Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) = h₁ := (Finset.mem_filter.1 hx1).2.2
  have h2 : Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) = h₂ := (Finset.mem_filter.1 hx2).2.2
  exact hne (h1.symm.trans h2)

/--
PDF Lemma 10 (`lem:I2`), combinatorial form.
Requires `ℓ ≠ 0` (PDF / user's note: `ℓ = i₂ ≥ 2`).
-/
theorem I2_card_bound (s N A : ℕ) (ℓ : Fin s) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hA : 1 ≤ A) (hA_lt : A < N) (hℓ : ℓ ≠ ⟨0, by omega⟩) :
    ((I2Support (s := s) (N := N) A ℓ (by omega)).card : ℝ) ≤
      (5 : ℝ) * I2RHS s N A := by
  set h0 : 0 < s := by omega
  -- Card ≤ sum of exact-gcd fibre cards (disjoint, so this is sharp up to empty fibres).
  have hcard_le :
      (I2Support (s := s) (N := N) A ℓ h0).card ≤
        ∑ h ∈ Finset.Icc A N, (I2Fibre (s := s) (N := N) h ℓ h0).card := by
    refine (Finset.card_le_card
      (I2Support_subset_biUnion_fibres s N A ℓ h0)).trans ?_
    exact Finset.card_biUnion_le
  have hfib' :
      ∀ h ∈ Finset.Icc A N,
        ((I2Fibre (s := s) (N := N) h ℓ h0).card : ℝ) ≤
          ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
            (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
    intro h hh
    have hh1 : 1 ≤ h := le_trans hA (Finset.mem_Icc.1 hh).1
    exact I2_fibre_card_le s N h ℓ hs hN hh1 hℓ
  have hsum0 :
      (∑ h ∈ Finset.Icc A N,
          ((I2Fibre (s := s) (N := N) h ℓ h0).card : ℝ)) ≤
        ∑ h ∈ Finset.Icc A N,
          ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
            (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
    Finset.sum_le_sum hfib'
  have hsum :
      (∑ h ∈ Finset.Icc A N,
          ((I2Fibre (s := s) (N := N) h ℓ h0).card : ℝ)) ≤
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          (∑ h ∈ Finset.Icc A N, (tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) := by
    refine hsum0.trans_eq ?_
    have hfactor (h : ℕ) :
        ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
            (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) =
          ((N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) *
            ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) := by
      ring
    simp_rw [hfactor, ← Finset.mul_sum]
  have htail :=
    divisor_tail_bound N s A hN (by omega : 1 ≤ s) (by omega : 0 < A) hA_lt
  have hpow_exp :
      (s ^ 2 - 1) + (s ^ 2 - 1) = 2 * s ^ 2 - 2 := by
    have : 1 ≤ s ^ 2 :=
      calc
        1 ≤ s := by omega
        _ ≤ s ^ 2 := Nat.le_self_pow (by omega : (2 : ℕ) ≠ 0) s
    omega
  have hpow :
      (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) =
        (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2) := by
    rw [← pow_add, hpow_exp]
  -- Trusted tail uses `(2 log N)^{s²-1}`; compare to `(2 s log N)^{s²-1}`.
  have htail' :
      (∑ h ∈ Finset.Icc A N, (tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) ≤
        5 * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) / (A : ℝ) := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs)
    have hlog : (0 : ℝ) ≤ Real.log N :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 3) hN))
    have hle :
        2 * Real.log N ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
    have hpow_le :
        (2 * Real.log N) ^ (s ^ 2 - 1) ≤
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
      pow_le_pow_left₀ (by positivity) hle _
    have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    calc
      ∑ h ∈ Finset.Icc A N, (tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2
          ≤ 5 * (2 * Real.log N) ^ (s ^ 2 - 1) / (A : ℝ) := htail
      _ ≤ 5 * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) / (A : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le (by norm_num)) (le_of_lt hApos)
  calc
    ((I2Support (s := s) (N := N) A ℓ h0).card : ℝ)
        ≤ (∑ h ∈ Finset.Icc A N,
            ((I2Fibre (s := s) (N := N) h ℓ h0).card : ℝ)) := by
          exact_mod_cast hcard_le
    _ ≤ (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          (∑ h ∈ Finset.Icc A N, (tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) := hsum
    _ ≤ (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
          (5 * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) / (A : ℝ)) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
    _ = 5 * (1 / (A : ℝ)) * (N : ℝ) ^ s *
          ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) := by
        ring
    _ = 5 * (1 / (A : ℝ)) * (N : ℝ) ^ s *
          (2 * (s : ℝ) * Real.log N) ^ (2 * s ^ 2 - 2) := by
        rw [hpow]
    _ = 5 * I2RHS s N A := by
        simp only [I2RHS]; ring

/--
PDF Lemma 10 for the exponential sum: `|I₂| ≪ A^{-1} N^s (2 s log N)^{2s²-2}`.
-/
theorem I2_bound {d : ℕ} (g : CirclePoly d) (s N A : ℕ) (ℓ : Fin s)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 1 ≤ A) (hA_lt : A < N)
    (hℓ : ℓ ≠ ⟨0, by omega⟩) :
    ‖Sg g (I2Support (s := s) (N := N) A ℓ (by omega))‖ ≤
      (5 : ℝ) * I2RHS s N A := by
  exact le_trans (norm_Sg_le_card g _)
    (I2_card_bound (s := s) (N := N) A ℓ hs hN hA hA_lt hℓ)

end RMFLean
