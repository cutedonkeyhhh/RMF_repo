/-
PDF section 7 inclusion-exclusion for S_g over the union of F_i.
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Intersection.PropIntersection
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex

namespace RMFLean

/-- The union of the F_i as a finset. -/
def FUnion (s N A : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  (Finset.univ : Finset (Fin s)).biUnion fun i => Ffinset (N := N) A i h0

theorem mem_FUnion {s N A : ℕ} {h0 : 0 < s} {x : Sol s N} :
    x ∈ FUnion s N A h0 ↔ ∃ i : Fin s, x.memF A i h0 := by
  simp [FUnion, Ffinset]

theorem sparse_union_eq_univ (s N A : ℕ) (h0 : 0 < s) :
    sparseComplementFinset (N := N) A h0 ∪ FUnion s N A h0 = Finset.univ := by
  ext x
  simp only [Finset.mem_union, mem_sparseComplementFinset, mem_FUnion, Finset.mem_univ,
    iff_true]
  by_cases h : ∃ i : Fin s, x.memF A i h0
  . exact Or.inr h
  . exact Or.inl fun i hi => h ⟨i, hi⟩

theorem sparse_disjoint_union (s N A : ℕ) (h0 : 0 < s) :
    Disjoint (sparseComplementFinset (N := N) A h0) (FUnion s N A h0) := by
  refine Finset.disjoint_left.2 ?_
  intro x hx hxU
  obtain ⟨i, hi⟩ := mem_FUnion.1 hxU
  exact (mem_sparseComplementFinset.1 hx) i hi

theorem IntersectionSupport_eq_inf' {s N A : ℕ} {I : Finset (Fin s)} (h0 : 0 < s)
    (hI : I.Nonempty) :
    IntersectionSupport (s := s) (N := N) A I h0 =
      I.inf' hI fun i => Ffinset (N := N) A i h0 := by
  ext x
  simp only [IntersectionSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inf']
  simp [Ffinset]

theorem IntersectionSupport_singleton {s N A : ℕ} (i : Fin s) (h0 : 0 < s) :
    IntersectionSupport (s := s) (N := N) A ({i} : Finset (Fin s)) h0 =
      Ffinset (N := N) A i h0 := by
  ext x
  simp [IntersectionSupport, Ffinset]

/-- Nonempty subsets of Fin s, as used by Mathlib IE. -/
abbrev NonemptySubsets (s : ℕ) : Finset (Finset (Fin s)) :=
  (Finset.univ : Finset (Fin s)).powerset.filter (fun t => t.Nonempty)

theorem card_NonemptySubsets (s : ℕ) :
    (NonemptySubsets s).card = 2 ^ s - 1 := by
  have hpow : ((Finset.univ : Finset (Fin s)).powerset).card = 2 ^ s := by
    simp
  have hunion :
      (Finset.univ : Finset (Fin s)).powerset =
        NonemptySubsets s ∪ {∅} := by
    ext t
    simp only [NonemptySubsets, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_singleton]
    constructor
    . intro ht
      by_cases h : t.Nonempty
      . exact Or.inl ⟨ht, h⟩
      . exact Or.inr (Finset.not_nonempty_iff_eq_empty.1 h)
    . intro h
      rcases h with h | rfl
      . exact h.1
      . exact Finset.empty_subset _
  have hdisj : Disjoint (NonemptySubsets s) ({∅} : Finset (Finset (Fin s))) := by
    refine Finset.disjoint_left.2 ?_
    intro t ht ht0
    have hne := (Finset.mem_filter.1 ht).2
    have hempty : t = ∅ := Finset.mem_singleton.1 ht0
    exact Finset.not_nonempty_iff_eq_empty.2 hempty hne
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hunion, hpow, Finset.card_singleton] at hcard
  omega

theorem singleton_mem_NonemptySubsets {s : ℕ} (i : Fin s) :
    ({i} : Finset (Fin s)) ∈ NonemptySubsets s := by
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (by simp), Finset.singleton_nonempty i⟩

/-- Inclusion-exclusion for S_g on the union. -/
theorem Sg_FUnion_ie {d s N A : ℕ} (g : CirclePoly d) (h0 : 0 < s) :
    Sg g (FUnion s N A h0) =
      ∑ t ∈ NonemptySubsets s,
        ((-1 : ℂ) ^ (t.card + 1)) *
          Sg g (IntersectionSupport (s := s) (N := N) A t h0) := by
  let hIE :=
    Finset.inclusion_exclusion_sum_biUnion
      (s := (Finset.univ : Finset (Fin s)))
      (S := fun i => Ffinset (N := N) A i h0)
      (f := fun a => (phaseWeight g a : ℂ))
  simp only [Sg, FUnion]
  refine Eq.trans hIE ?_
  rw [← Finset.sum_coe_sort (s := NonemptySubsets s)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hne : t.1.Nonempty := (Finset.mem_filter.1 t.2).2
  simp only [zsmul_eq_mul]
  rw [IntersectionSupport_eq_inf' h0 hne]
  congr 1
  simp [Int.cast_neg, Int.cast_one]
private theorem sum_mainTerm_eq_factorial (s N : ℕ) (hs : 2 ≤ s) :
    (∑ _i : Fin s, (mainTermF s N : ℂ)) =
      ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) := by
  have hfac : s * (s - 1).factorial = s.factorial :=
    Nat.mul_factorial_pred (by omega)
  simp only [mainTermF, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  -- goal: (s:C) * (( (s-1)! : R) * (N:R)^s : C) = ...
  convert_to ((s * (s - 1).factorial : ℕ) : ℂ) * ((N : ℝ) ^ s : ℂ) = _
  . push_cast; ring
  rw [hfac]
  push_cast
  ring

/-- Sum of main terms over singleton subsets equals s! N^s. -/
theorem sum_singleton_mainTerm (s N : ℕ) (hs : 2 ≤ s) :
    (∑ t ∈ NonemptySubsets s,
        if t.card = 1 then (mainTermF s N : ℂ) else 0) =
      ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) := by
  have himg :
      (NonemptySubsets s).filter (fun t => t.card = 1) =
        (Finset.univ : Finset (Fin s)).image fun i => ({i} : Finset (Fin s)) := by
    ext t
    constructor
    . intro ht
      have ht' := Finset.mem_filter.1 ht
      have hc : t.card = 1 := ht'.2
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hc
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    . intro ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ht
      exact Finset.mem_filter.2 ⟨singleton_mem_NonemptySubsets i, by simp⟩
  have hinj :
      Set.InjOn (fun i : Fin s => ({i} : Finset (Fin s)))
        (Finset.univ : Finset (Fin s)) := by
    intro i _ j _ hij
    exact Finset.singleton_inj.1 hij
  calc
    (∑ t ∈ NonemptySubsets s, if t.card = 1 then (mainTermF s N : ℂ) else 0)
        = ∑ t ∈ (NonemptySubsets s).filter (fun t => t.card = 1),
            (mainTermF s N : ℂ) := by
          rw [← Finset.sum_filter]
    _ = ∑ t ∈ ((Finset.univ : Finset (Fin s)).image fun i => ({i} : Finset (Fin s))),
            (mainTermF s N : ℂ) := by rw [himg]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin s)), (mainTermF s N : ℂ) := by
          rw [Finset.sum_image hinj]
    _ = (∑ _i : Fin s, (mainTermF s N : ℂ)) := by simp
    _ = ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) := sum_mainTerm_eq_factorial s N hs

private theorem signed_singleton_mainTerm (s N : ℕ) (hs : 2 ≤ s) :
    (∑ t ∈ NonemptySubsets s,
        if t.card = 1 then
          ((-1 : ℂ) ^ (t.card + 1)) * (mainTermF s N : ℂ)
        else 0) =
      ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) := by
  have hsign :
      (∑ t ∈ NonemptySubsets s,
          if t.card = 1 then
            ((-1 : ℂ) ^ (t.card + 1)) * (mainTermF s N : ℂ)
          else 0) =
        ∑ t ∈ NonemptySubsets s,
          if t.card = 1 then (mainTermF s N : ℂ) else 0 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with h
    . have : (-1 : ℂ) ^ (t.card + 1) = 1 := by rw [h]; norm_num
      simp [this]
    . rfl
  rw [hsign, sum_singleton_mainTerm s N hs]

private theorem ie_telescope_sum {d s N A : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (hs : 2 ≤ s) :
    (∑ t ∈ NonemptySubsets s,
        ((-1 : ℂ) ^ (t.card + 1)) *
          Sg g (IntersectionSupport (s := s) (N := N) A t h0)) -
        ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) =
      ∑ t ∈ NonemptySubsets s,
        ((-1 : ℂ) ^ (t.card + 1)) *
          (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
            if t.card = 1 then (mainTermF s N : ℂ) else 0) := by
  rw [← signed_singleton_mainTerm s N hs]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

/-- PDF section 7 IE telescope. -/
theorem U_ie_bound (d s N A : ℕ) (g : CirclePoly d) (δ Cerr : ℝ)
    (hs : 2 ≤ s) (_hN : 3 ≤ N) (_hA : 2 ≤ A) (_hAN : A < N)
    (_hδ : 0 < δ) (_hCerr : 0 < Cerr)
    (hFi :
      ∀ i : Fin s,
        ‖(Sg g (Ffinset (N := N) A i
            (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs)) : ℂ) -
            (mainTermF s N : ℂ)‖ ≤
          Cerr * errorSize N s δ)
    (hInt :
      ∀ I : Finset (Fin s), 2 ≤ I.card →
        ‖Sg g (IntersectionSupport (s := s) (N := N) A I
            (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs))‖ ≤
          Cerr * errorSize N s δ)
    (hSp :
      ‖Sg g (sparseComplementFinset (s := s) (N := N) A
          (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs))‖ ≤
        Cerr * errorSize N s δ) :
    ‖(U d s N g : ℂ) - ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ)‖ ≤
      (2 : ℝ) ^ s * Cerr * errorSize N s δ := by
  set h0 : 0 < s := Nat.lt_of_lt_of_le (by decide : 0 < 2) hs
  have hU : (U d s N g : ℂ) = Sg g (Finset.univ : Finset (Sol s N)) :=
    moment_formula g Finset.univ fun _ => Finset.mem_univ _
  have hsplit :
      Sg g (Finset.univ : Finset (Sol s N)) =
        Sg g (sparseComplementFinset (N := N) A h0) + Sg g (FUnion s N A h0) := by
    have hdisj := sparse_disjoint_union s N A h0
    have hunion := sparse_union_eq_univ s N A h0
    have h := Finset.sum_union (f := phaseWeight g) hdisj
    simp only [Sg]
    rw [← h, hunion]
  have hcalc :
      (U d s N g : ℂ) - ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ) =
        Sg g (sparseComplementFinset (N := N) A h0) +
          ∑ t ∈ NonemptySubsets s,
            ((-1 : ℂ) ^ (t.card + 1)) *
              (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
                if t.card = 1 then (mainTermF s N : ℂ) else 0) := by
    rw [hU, hsplit, Sg_FUnion_ie g h0, add_sub_assoc, ie_telescope_sum g h0 hs]
  have hterm_le :
      ∀ t ∈ NonemptySubsets s,
        ‖((-1 : ℂ) ^ (t.card + 1)) *
            (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
              if t.card = 1 then (mainTermF s N : ℂ) else 0)‖ ≤
          Cerr * errorSize N s δ := by
    intro t ht
    have hnorm1 : ‖((-1 : ℂ) ^ (t.card + 1))‖ = 1 := by
      rw [norm_pow, norm_neg, norm_one, one_pow]
    rw [norm_mul, hnorm1, one_mul]
    by_cases hc : t.card = 1
    . obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hc
      simpa [hc, hi, IntersectionSupport_singleton] using hFi i
    . simp only [if_neg hc, sub_zero]
      have hcard2 : 2 ≤ t.card := by
        have hpos : 1 ≤ t.card := Finset.one_le_card.2 (Finset.mem_filter.1 ht).2
        omega
      exact hInt t hcard2
  have hsum_le :
      ‖∑ t ∈ NonemptySubsets s,
          ((-1 : ℂ) ^ (t.card + 1)) *
            (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
              if t.card = 1 then (mainTermF s N : ℂ) else 0)‖ ≤
        ((NonemptySubsets s).card : ℝ) * (Cerr * errorSize N s δ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm_le).trans_eq ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  have herr :
      ‖Sg g (sparseComplementFinset (N := N) A h0) +
          ∑ t ∈ NonemptySubsets s,
            ((-1 : ℂ) ^ (t.card + 1)) *
              (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
                if t.card = 1 then (mainTermF s N : ℂ) else 0)‖ ≤
        Cerr * errorSize N s δ +
          ((NonemptySubsets s).card : ℝ) * (Cerr * errorSize N s δ) :=
    (norm_add_le _ _).trans (add_le_add hSp hsum_le)
  have hcard' : ((NonemptySubsets s).card : ℝ) = (2 : ℝ) ^ s - 1 := by
    have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
    have := card_NonemptySubsets s
    calc
      ((NonemptySubsets s).card : ℝ) = ((2 ^ s - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 : ℝ) ^ s - 1 := by rw [Nat.cast_sub h1]; norm_cast
  calc
    ‖(U d s N g : ℂ) - ((Nat.factorial s : ℝ) * (N : ℝ) ^ s : ℂ)‖
        = ‖Sg g (sparseComplementFinset (N := N) A h0) +
            ∑ t ∈ NonemptySubsets s,
              ((-1 : ℂ) ^ (t.card + 1)) *
                (Sg g (IntersectionSupport (s := s) (N := N) A t h0) -
                  if t.card = 1 then (mainTermF s N : ℂ) else 0)‖ := by
          rw [hcalc]
    _ ≤ Cerr * errorSize N s δ +
          ((NonemptySubsets s).card : ℝ) * (Cerr * errorSize N s δ) := herr
    _ = Cerr * errorSize N s δ + ((2 : ℝ) ^ s - 1) * (Cerr * errorSize N s δ) := by
        rw [hcard']
    _ = (2 : ℝ) ^ s * Cerr * errorSize N s δ := by ring

end RMFLean

