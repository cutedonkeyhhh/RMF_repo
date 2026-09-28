/-
m-coordinate swap symmetry for k-fold intersections (Remark 3 style).

Lifts Prop 2 from the special case `0 ∈ I` to arbitrary `I` with `#I ≥ 2`.
-/
import RMFLean.Proof.F1.PropF1
import RMFLean.Proof.Intersection.PropIntersection
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic

noncomputable section

open Classical Real

set_option maxHeartbeats 800000

namespace RMFLean

/-- Swapping `m`-coordinates of `a` and `b` conjugates `memF` by `Equiv.swap a b`. -/
theorem memF_solSwapM {s N A : ℕ} {h0 : 0 < s} (x : Sol s N) (a b j : Fin s) :
    (solSwapM x a b).memF A j h0 ↔ x.memF A (Equiv.swap a b j) h0 := by
  simp only [Sol.memF, solSwapM]

/-- Image of an index set under coordinate swap. -/
def swapIndexSet {s : ℕ} (a b : Fin s) (I : Finset (Fin s)) : Finset (Fin s) :=
  I.map (Equiv.swap a b).toEmbedding

theorem mem_swapIndexSet {s : ℕ} (a b : Fin s) (I : Finset (Fin s)) (j : Fin s) :
    j ∈ swapIndexSet a b I ↔ Equiv.swap a b j ∈ I := by
  simp only [swapIndexSet, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [Equiv.swap_apply_self] using hk
  · intro hj
    exact ⟨Equiv.swap a b j, hj, by simp [Equiv.swap_apply_self]⟩

theorem card_swapIndexSet {s : ℕ} (a b : Fin s) (I : Finset (Fin s)) :
    (swapIndexSet a b I).card = I.card := by
  simp only [swapIndexSet, Finset.card_map]

theorem zero_mem_swapIndexSet_of_mem {s : ℕ} {h0 : 0 < s} {I : Finset (Fin s)}
    (i : Fin s) (hi : i ∈ I) :
    (⟨0, h0⟩ : Fin s) ∈ swapIndexSet ⟨0, h0⟩ i I := by
  rw [mem_swapIndexSet, Equiv.swap_apply_left]
  exact hi

theorem swapIndexSet_involutive {s : ℕ} (a b : Fin s) (I : Finset (Fin s)) :
    swapIndexSet a b (swapIndexSet a b I) = I := by
  ext j
  simp only [mem_swapIndexSet, Equiv.swap_apply_self]

/--
`solSwapM · 0 i` is a bijection
`IntersectionSupport I ≃ IntersectionSupport (swapIndexSet 0 i I)`.
-/
theorem mem_IntersectionSupport_solSwapM {s N A : ℕ} {h0 : 0 < s}
    (x : Sol s N) (i : Fin s) (I : Finset (Fin s)) :
    solSwapM x ⟨0, h0⟩ i ∈
        IntersectionSupport (s := s) (N := N) A (swapIndexSet ⟨0, h0⟩ i I) h0 ↔
      x ∈ IntersectionSupport (s := s) (N := N) A I h0 := by
  simp only [IntersectionSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    memF_solSwapM, mem_swapIndexSet]
  constructor
  · intro h j hj
    simpa [Equiv.swap_apply_self] using h (Equiv.swap ⟨0, h0⟩ i j)
      (by simpa [Equiv.swap_apply_self] using hj)
  · intro h k hk
    exact h _ hk

theorem Sg_IntersectionSupport_swapM {d s N A : ℕ} (g : CirclePoly d)
    (i : Fin s) (I : Finset (Fin s)) (h0 : 0 < s) :
    Sg g (IntersectionSupport (s := s) (N := N) A I h0) =
      Sg g (IntersectionSupport (s := s) (N := N) A
        (swapIndexSet ⟨0, h0⟩ i I) h0) := by
  -- Same pattern as `Sg_Ffinset_swapM`: bijection by `solSwapM · 0 i`.
  let f : Sol s N → Sol s N := fun x => solSwapM x ⟨0, h0⟩ i
  let I' := swapIndexSet ⟨0, h0⟩ i I
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => solSwapM z ⟨0, h0⟩ i) hxy
    simpa [f, solSwapM_involutive] using this
  have hmaps :
      ∀ x ∈ IntersectionSupport (s := s) (N := N) A I h0,
        f x ∈ IntersectionSupport (s := s) (N := N) A I' h0 := by
    intro x hx
    exact (mem_IntersectionSupport_solSwapM x i I).2 hx
  have hsurj :
      ∀ y ∈ IntersectionSupport (s := s) (N := N) A I' h0,
        ∃ x ∈ IntersectionSupport (s := s) (N := N) A I h0, f x = y := by
    intro y hy
    refine ⟨f y, ?_, ?_⟩
    · -- `mem_IntersectionSupport_solSwapM` at `x = f y` says
      -- `f (f y) ∈ I' ↔ f y ∈ I`; left side is `y ∈ I'`.
      have hy' : f (f y) ∈ IntersectionSupport (s := s) (N := N) A I' h0 := by
        change solSwapM (solSwapM y ⟨0, h0⟩ i) ⟨0, h0⟩ i ∈
          IntersectionSupport (s := s) (N := N) A I' h0
        rwa [solSwapM_involutive]
      exact (mem_IntersectionSupport_solSwapM (f y) i I).1 hy'
    · exact solSwapM_involutive y ⟨0, h0⟩ i
  have hsum :
      (∑ x ∈ IntersectionSupport (s := s) (N := N) A I h0, phaseWeight g x) =
        ∑ y ∈ IntersectionSupport (s := s) (N := N) A I' h0, phaseWeight g y := by
    refine Finset.sum_nbij f hmaps (fun _ _ _ _ h => hinj h) hsurj ?_
    intro x _
    exact (phaseWeight_solSwapM g x ⟨0, h0⟩ i).symm
  simpa [Sg, I'] using hsum

/--
Prop 2 after m-coordinate swap: the hypothesis `0 ∈ I` may be dropped.
(Same symmetry mechanism as Remark 3 / `Fi_symmetry`.)
-/
theorem prop_intersection_any (d : ℕ) (CdI : ℝ) (_hCdI : 0 < CdI)
    (hInt :
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (_hN : 3 ≤ N)
          (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A) (hA_lt : A < N),
          Real.rpow δ (-(CdI + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + CdI)) →
            ‖Sg g (IntersectionSupport (s := s) (N := N) A I (by omega))‖ ≤
                C * errorSize N s δ ∨
              altDiophantine d N g δ (CdI + (3 : ℝ) * (d : ℝ) + 2)) :
    ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (I : Finset (Fin s)) (_hN : 3 ≤ N) (_hIcard : 2 ≤ I.card)
        (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A) (hA_lt : A < N),
        Real.rpow δ (-(CdI + 2)) < (A : ℝ) →
          (A : ℝ) < Real.rpow δ (-(3 + CdI)) →
          ‖Sg g (IntersectionSupport (s := s) (N := N) A I (by omega))‖ ≤
              C * errorSize N s δ ∨
            altDiophantine d N g δ (CdI + (3 : ℝ) * (d : ℝ) + 2) := by
  intro s hs
  obtain ⟨C, hC, hInts⟩ := hInt s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ I hN hIcard hδ hδ' hA hA_lt hAlo hAhi
  have h0 : 0 < s := Nat.lt_of_lt_of_le (by decide : 0 < 2) hs
  obtain ⟨i, hi⟩ : ∃ i : Fin s, i ∈ I := by
    have : I.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le (by decide : 0 < 2) hIcard)
    exact this
  set I' := swapIndexSet ⟨0, h0⟩ i I
  have hI'0 : (⟨0, h0⟩ : Fin s) ∈ I' := zero_mem_swapIndexSet_of_mem i hi
  have hI'card : 2 ≤ I'.card := by
    simpa [I', card_swapIndexSet] using hIcard
  have hSg :
      Sg g (IntersectionSupport (s := s) (N := N) A I h0) =
        Sg g (IntersectionSupport (s := s) (N := N) A I' h0) :=
    Sg_IntersectionSupport_swapM g i I h0
  rcases hInts N A g δ I' hN hI'0 hI'card hδ hδ' hA hA_lt hAlo hAhi with hb | hdio
  · refine Or.inl ?_
    simpa [hSg] using hb
  · exact Or.inr hdio

end RMFLean
