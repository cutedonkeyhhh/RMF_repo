/-
PDF Proposition 1 (`prop:F1`) and Remark 3 (symmetry among `ℱ_i`).
-/
import RMFLean.Proof.F1.J1
import RMFLean.Proof.F1.J1LongShort
import RMFLean.Proof.F1.J2
import RMFLean.Proof.Setup.PhaseNorm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Classical

namespace RMFLean

/-- `ℱ_1` as a finset. -/
def F1Support (s N A : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Ffinset (N := N) A ⟨0, h0⟩ h0

/-- Off-diagonal / diagonal split of `ℱ_1`. -/
theorem F1Support_eq_union (s N A : ℕ) (h0 : 0 < s) :
    F1Support (s := s) (N := N) A h0 =
      J1Support (s := s) (N := N) A h0 ∪ J2Support (s := s) (N := N) A h0 := by
  ext x
  simp only [F1Support, Ffinset, J1Support, J2Support, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hmem
    by_cases hdiag : x.onDiag h0
    · exact Or.inr ⟨hmem, hdiag⟩
    · exact Or.inl ⟨hmem, hdiag⟩
  · intro h
    rcases h with h | h
    · exact h.1
    · exact h.1

theorem disjoint_J1Support_J2Support (s N A : ℕ) (h0 : 0 < s) :
    Disjoint (J1Support (s := s) (N := N) A h0) (J2Support (s := s) (N := N) A h0) := by
  refine Finset.disjoint_left.2 ?_
  intro x hx1 hx2
  have hnodiag : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx1).2.2
  have hdiag : x.onDiag h0 := (Finset.mem_filter.1 hx2).2.2
  exact hnodiag hdiag

theorem Sg_F1Support_eq_add (d s N A : ℕ) (g : CirclePoly d) (h0 : 0 < s) :
    Sg g (F1Support (s := s) (N := N) A h0) =
      Sg g (J1Support (s := s) (N := N) A h0) +
        Sg g (J2Support (s := s) (N := N) A h0) := by
  simp only [Sg, F1Support_eq_union s N A h0]
  exact Finset.sum_union (disjoint_J1Support_J2Support s N A h0)

/-! ### Coordinate swap on the `m`-side (Remark 3) -/

def solSwapM {s N : ℕ} (x : Sol s N) (i j : Fin s) : Sol s N where
  n := x.n
  m := fun k => x.m (Equiv.swap i j k)
  hn := x.hn
  hm := fun k => x.hm (Equiv.swap i j k)
  hprod := by
    calc
      (∏ k, x.n k) = ∏ k, x.m k := x.hprod
      _ = ∏ k, x.m (Equiv.swap i j k) :=
        (Equiv.prod_comp (Equiv.swap i j) x.m).symm

theorem solSwapM_involutive {s N : ℕ} (x : Sol s N) (i j : Fin s) :
    solSwapM (solSwapM x i j) i j = x := by
  refine Sol.ext rfl ?_
  funext k
  simp [solSwapM]

theorem phaseWeight_solSwapM {d s N : ℕ} (g : CirclePoly d) (x : Sol s N)
    (i j : Fin s) :
    phaseWeight g (solSwapM x i j) = phaseWeight g x := by
  simp only [phaseWeight, solSwapM]
  have hm :
      (∏ k : Fin s, starRingEnd ℂ (g.ePhase (x.m (Equiv.swap i j k)))) =
        ∏ k : Fin s, starRingEnd ℂ (g.ePhase (x.m k)) :=
    Equiv.prod_comp (Equiv.swap i j)
      (fun k => starRingEnd ℂ (g.ePhase (x.m k)))
  calc
    (∏ k, g.ePhase (x.n k) * starRingEnd ℂ (g.ePhase (x.m (Equiv.swap i j k))))
        = (∏ k, g.ePhase (x.n k)) *
            (∏ k, starRingEnd ℂ (g.ePhase (x.m (Equiv.swap i j k)))) := by
          simp [Finset.prod_mul_distrib]
    _ = (∏ k, g.ePhase (x.n k)) *
            (∏ k, starRingEnd ℂ (g.ePhase (x.m k))) := by rw [hm]
    _ = ∏ k, g.ePhase (x.n k) * starRingEnd ℂ (g.ePhase (x.m k)) := by
          simp [Finset.prod_mul_distrib]

theorem memF_solSwapM_zero {s N A : ℕ} {h0 : 0 < s} (x : Sol s N) (i : Fin s) :
    (solSwapM x ⟨0, h0⟩ i).memF A ⟨0, h0⟩ h0 ↔ x.memF A i h0 := by
  simp only [Sol.memF, solSwapM, Equiv.swap_apply_left]

theorem Sg_Ffinset_swapM {d s N A : ℕ} (g : CirclePoly d) (i : Fin s)
    (h0 : 0 < s) :
    Sg g (Ffinset (N := N) A i h0) =
      Sg g (Ffinset (N := N) A ⟨0, h0⟩ h0) := by
  let f : Sol s N → Sol s N := fun x => solSwapM x ⟨0, h0⟩ i
  have hinj : Function.Injective f := by
    intro x y hxy
    simpa [f, solSwapM_involutive] using
      congrArg (fun z => solSwapM z ⟨0, h0⟩ i) hxy
  have hmaps :
      ∀ x ∈ Ffinset (N := N) A i h0,
        f x ∈ Ffinset (N := N) A ⟨0, h0⟩ h0 := by
    intro x hx
    have hmem : x.memF A i h0 := (Finset.mem_filter.1 hx).2
    simp only [Ffinset, Finset.mem_filter, Finset.mem_univ, true_and, f]
    exact (memF_solSwapM_zero x i).2 hmem
  have hsurj :
      ∀ y ∈ Ffinset (N := N) A ⟨0, h0⟩ h0,
        ∃ x ∈ Ffinset (N := N) A i h0, f x = y := by
    intro y hy
    refine ⟨solSwapM y ⟨0, h0⟩ i, ?_, ?_⟩
    · have hmem : y.memF A ⟨0, h0⟩ h0 := (Finset.mem_filter.1 hy).2
      simp only [Ffinset, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [Sol.memF, solSwapM, Equiv.swap_apply_left, Equiv.swap_apply_right] using
        hmem
    · exact solSwapM_involutive y ⟨0, h0⟩ i
  have hsum :
      (∑ x ∈ Ffinset (N := N) A i h0, phaseWeight g x) =
        ∑ y ∈ Ffinset (N := N) A ⟨0, h0⟩ h0, phaseWeight g y := by
    refine Finset.sum_nbij f hmaps (fun _ _ _ _ h => hinj h) hsurj ?_
    intro x hx
    exact (phaseWeight_solSwapM g x ⟨0, h0⟩ i).symm
  simpa [Sg] using hsum

/-- `δ^{-C} < A` implies `δ^{-1} ≤ A` when `C > 5` and `0 < δ < 1`. -/
theorem A_ge_delta_inv_of_window {A : ℕ} {δ Cd : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hCd : 5 < Cd)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ)) :
    Real.rpow δ (-(1 : ℝ)) ≤ (A : ℝ) := by
  have hmono : (-Cd) ≤ (-(1 : ℝ)) := by linarith
  have hpow : Real.rpow δ (-(1 : ℝ)) ≤ Real.rpow δ (-Cd) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (le_of_lt hδ1) hmono
  exact le_trans hpow (le_of_lt hAlo)

/--
PDF Proposition 1: exists `C_d > 5` depending only on `d`, and for each `s`,
each Diophantine exponent `Cd' ≥ C_d`, and each inductive Vinogradov constant
`Cll_ind > 0`, there is `C = C(d,s,Cll_ind) > 0` such that whenever
`δ^{-C_d} < A < δ^{-(3+C_d)}` and `δ > N^{-J2DeltaExp C_d}`, either
`|S_g(ℱ_1) - (s-1)! N^s| ≤ C · δ N^s 𝒬`, or Diophantine with exponent `Cd'`.

The flexible `Cd'` lets the inductive hypothesis use the outer unified exponent
of Theorem 1 (larger than the Lemma 5 exponent).  The J₂ absorption constant
from `Hyp` is folded into `C`.
-/
theorem prop_F1 (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s),
        ∀ (Cd' : ℝ), Cd ≤ Cd' →
          ∀ (Cll_ind : ℝ), 0 < Cll_ind →
            ∃ C : ℝ, 0 < C ∧
              ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
                (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
                (_hAN : A < N),
                Real.rpow δ (-Cd) < (A : ℝ) →
                (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
                Real.rpow (N : ℝ) (-J2DeltaExp Cd) < δ →
                (s = 2 ∨ Hyp d (s - 1) N g δ Cd' Cll_ind) →
                (s = 2 ∨ inMomentRange N (s - 1)) →
                ‖(Sg g (F1Support (s := s) (N := N) A
                    (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs)) : ℂ) -
                    (mainTermF s N : ℂ)‖ ≤
                  C * errorSize N s δ ∨
                  altDiophantine d N g δ Cd' := by
  obtain ⟨Cd, hEq, hCd, hJ1⟩ := J1_bound d
  have hCd0 : 0 < Cd := lt_trans (by norm_num : (0 : ℝ) < 5) hCd
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs Cd' hCd' Cll_ind hCll
  obtain ⟨C₁, hC₁, hJ1s⟩ := hJ1 s hs
  set C₂ : ℝ := Cll_ind + (Nat.factorial (s - 1) : ℝ)
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N A g δ hN hδ hδ' hAN hAlo hAhi hδN hind hrange
  have h0 : 0 < s := Nat.lt_of_lt_of_le (by decide : 0 < 2) hs
  have hAN' : A ≤ N := le_of_lt hAN
  have hA : 1 ≤ A := by
    have hpos : (0 : ℝ) < Real.rpow δ (-Cd) :=
      Real.rpow_pos_of_pos hδ _
    have : (0 : ℝ) < (A : ℝ) := lt_trans hpos hAlo
    exact Nat.succ_le_of_lt (Nat.cast_pos.1 this)
  have hδ1 : δ < 1 := lt_trans hδ' (by norm_num)
  rcases hJ1s N A g δ hN hδ hδ' hAN hAlo hAhi with hJ1n | hdio
  · rcases J2_bound d Cd hCd0 s N A g δ Cd' Cll_ind hCd' hCll hs hN hA hAN'
        hδ hδ' hAlo hAhi hδN hind hrange with hJ2n | hdio
    · refine Or.inl ?_
      have hsplit := Sg_F1Support_eq_add d s N A g h0
      calc
        ‖Sg g (F1Support (s := s) (N := N) A h0) - (mainTermF s N : ℂ)‖
            = ‖Sg g (J1Support (s := s) (N := N) A h0) +
                Sg g (J2Support (s := s) (N := N) A h0) -
                  (mainTermF s N : ℂ)‖ := by rw [hsplit]
        _ = ‖Sg g (J1Support (s := s) (N := N) A h0) +
                (Sg g (J2Support (s := s) (N := N) A h0) -
                  (mainTermF s N : ℂ))‖ := by
              congr 1; abel
        _ ≤ ‖Sg g (J1Support (s := s) (N := N) A h0)‖ +
              ‖Sg g (J2Support (s := s) (N := N) A h0) -
                (mainTermF s N : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ C₁ * errorSize N s δ + C₂ * errorSize N s δ :=
          add_le_add hJ1n (by simpa [C₂] using hJ2n)
        _ = (C₁ + C₂) * errorSize N s δ := by ring
    · exact Or.inr hdio
  · exact Or.inr (altDiophantine_mono hδ hδ1 hCd' hdio)

/-- PDF Remark 3: same main term/error for every `ℱ_i`. -/
theorem Fi_symmetry (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s),
        ∀ (Cd' : ℝ), Cd ≤ Cd' →
          ∀ (Cll_ind : ℝ), 0 < Cll_ind →
            ∃ C : ℝ, 0 < C ∧
              ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ) (i : Fin s)
                (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
                (_hAN : A < N),
                Real.rpow δ (-Cd) < (A : ℝ) →
                (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
                Real.rpow (N : ℝ) (-J2DeltaExp Cd) < δ →
                (s = 2 ∨ Hyp d (s - 1) N g δ Cd' Cll_ind) →
                (s = 2 ∨ inMomentRange N (s - 1)) →
                ‖(Sg g (Ffinset (N := N) A i
                    (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs)) : ℂ) -
                    (mainTermF s N : ℂ)‖ ≤
                  C * errorSize N s δ ∨
                  altDiophantine d N g δ Cd' := by
  obtain ⟨Cd, hEq, hCd, hF1⟩ := prop_F1 d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs Cd' hCd' Cll_ind hCll
  obtain ⟨C, hC, hF1s⟩ := hF1 s hs Cd' hCd' Cll_ind hCll
  refine ⟨C, hC, ?_⟩
  intro N A g δ i hN hδ hδ' hAN hAlo hAhi hδN hind hrange
  have h0 : 0 < s := Nat.lt_of_lt_of_le (by decide : 0 < 2) hs
  have hSg :
      Sg g (Ffinset (N := N) A i h0) =
        Sg g (F1Support (s := s) (N := N) A h0) := by
    simpa [F1Support] using Sg_Ffinset_swapM g i h0
  rcases hF1s N A g δ hN hδ hδ' hAN hAlo hAhi hδN hind hrange with hb | hdio
  · exact Or.inl (by simpa [hSg] using hb)
  · exact Or.inr hdio

end RMFLean
