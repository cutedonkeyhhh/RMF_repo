/-
PDF Lemma 3 (`lem:sparse-complement`).
-/
import RMFLean.Trusted.Axioms
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section

open Real Classical

namespace RMFLean

/-- First coordinate `n₁`. -/
def Sol.n1 {s N : ℕ} (x : Sol s N) (h0 : 0 < s) : ℕ :=
  x.n ⟨0, h0⟩

/--
Classic peeling lemma used in PDF Lemma 3:
if `n ∣ a * b` and `d = Nat.gcd n a`, then `n / d ∣ b`.
Requires `0 < n` (always true for coordinates in `V`).
-/
theorem dvd_of_dvd_mul_gcd {n a b : ℕ} (hn : 0 < n) (h : n ∣ a * b) :
    n / Nat.gcd n a ∣ b := by
  set d := Nat.gcd n a
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left a hn
  have hn' : n = d * (n / d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n a)).symm
  have ha' : a = d * (a / d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n a)).symm
  have h' : d * (n / d) ∣ d * ((a / d) * b) := by
    rw [← hn', ← mul_assoc, ← ha']
    exact h
  have hnd : n / d ∣ (a / d) * b := Nat.dvd_of_mul_dvd_mul_left hd_pos h'
  have hcop : Nat.Coprime (n / d) (a / d) := by
    have hmul :
        Nat.gcd n a = d * Nat.gcd (n / d) (a / d) := by
      calc
        Nat.gcd n a = Nat.gcd (d * (n / d)) (d * (a / d)) := by rw [← hn', ← ha']
        _ = d * Nat.gcd (n / d) (a / d) := Nat.gcd_mul_left _ _ _
    have : d = d * Nat.gcd (n / d) (a / d) := by
      simpa [d] using hmul
    exact Nat.coprime_iff_gcd_eq_one.2
      (Nat.eq_of_mul_eq_mul_left hd_pos (by rw [← this, mul_one]))
  exact hcop.dvd_of_dvd_mul_left hnd

/--
If `n ∣ ∏ mᵢ` and `gcd(n, mᵢ) < A` for every `i`, then `n ≤ A^s`.
First arithmetic step of PDF Lemma 3.
-/
theorem n_le_A_pow_of_gcd_lt
    {s A n : ℕ} (m : Fin s → ℕ) (_hA : 2 ≤ A) (hn : 0 < n)
    (hdvd : n ∣ ∏ i, m i)
    (hgcd : ∀ i : Fin s, Nat.gcd n (m i) < A) :
    n ≤ A ^ s := by
  induction s generalizing n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty] at hdvd
    have : n = 1 := Nat.eq_one_of_dvd_one hdvd
    simp [this]
  | succ s ih =>
    let d := Nat.gcd n (m ⟨0, Nat.succ_pos _⟩)
    have hd_lt : d < A := hgcd ⟨0, Nat.succ_pos _⟩
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ hn
    have hn_div : 0 < n / d :=
      Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n _)) hd_pos
    have hmul :
        n ∣ m ⟨0, Nat.succ_pos _⟩ *
          (∏ i : Fin s, m i.succ) := by
      simpa [Fin.prod_univ_succ] using hdvd
    have htail : n / d ∣ ∏ i : Fin s, m i.succ :=
      dvd_of_dvd_mul_gcd hn hmul
    have hgcd_tail : ∀ i : Fin s, Nat.gcd (n / d) (m i.succ) < A := by
      intro i
      refine lt_of_le_of_lt ?_ (hgcd i.succ)
      have hdiv : Nat.gcd (n / d) (m i.succ) ∣ Nat.gcd n (m i.succ) := by
        refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
        exact (Nat.gcd_dvd_left _ _).trans
          (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n _))
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn) hdiv
    have ih' := ih (fun i => m i.succ) hn_div htail hgcd_tail
    have hn_eq : n = d * (n / d) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left n _)).symm
    have hd_le : d ≤ A - 1 := Nat.le_pred_of_lt hd_lt
    calc
      n = d * (n / d) := hn_eq
      _ ≤ (A - 1) * A ^ s := Nat.mul_le_mul hd_le ih'
      _ ≤ A * A ^ s := Nat.mul_le_mul_right _ (Nat.sub_le A 1)
      _ = A ^ (s + 1) := by ring

/-- On the sparse complement, `n₁ ≤ A^s`. -/
theorem sparse_n1_le
    {s N A : ℕ} (x : Sol s N) (h0 : 0 < s) (hA : 2 ≤ A)
    (hgcd : ∀ i : Fin s, Nat.gcd (x.n1 h0) (x.m i) < A) :
    x.n1 h0 ≤ A ^ s := by
  have hn1 : 0 < x.n1 h0 :=
    lt_of_lt_of_le Nat.zero_lt_one (by simpa [Sol.n1] using (x.hn ⟨0, h0⟩).1)
  have hdivn : x.n1 h0 ∣ ∏ i, x.n i := by
    simpa [Sol.n1] using
      Finset.dvd_prod_of_mem (fun i => x.n i) (Finset.mem_univ ⟨0, h0⟩)
  have hdvd : x.n1 h0 ∣ ∏ i, x.m i := by
    simpa [x.hprod] using hdivn
  exact n_le_A_pow_of_gcd_lt (m := x.m) hA hn1 hdvd hgcd

/-- Sparse complement solutions satisfy `n₁ ≤ A^s`. -/
theorem mem_sparse_n1_le {s N A : ℕ} (hs : 2 ≤ s) (hA : 2 ≤ A)
    {x : Sol s N} (hx : x ∈ sparseComplementFinset (N := N) A (by omega)) :
    x.n1 (by omega) ≤ A ^ s := by
  have hgcd : ∀ i : Fin s, Nat.gcd (x.n1 (by omega)) (x.m i) < A := by
    intro i
    have := (mem_sparseComplementFinset (N := N)).1 hx i
    exact Nat.lt_of_not_ge this
  exact sparse_n1_le x (by omega) hA hgcd

/-- PDF Lemma 3 RHS. -/
noncomputable def sparseRHS (s N A : ℕ) : ℝ :=
  (N : ℝ) ^ (s - 1) * (A : ℝ) ^ (2 * s) *
    (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2)

/-- Solutions in `V` with fixed `n₁ = g`. -/
def fibreN1 (s N g : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x => x.n1 h0 = g

/-- Each `g ≤ M`, so `∑_{g=1}^M g ≤ M^2`. -/
theorem sum_Icc_id_le_sq (M : ℕ) :
    (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) ≤ (M : ℝ) ^ 2 := by
  have hnat : ∑ g ∈ Finset.Icc 1 M, g ≤ M * M := by
    have h : ∑ g ∈ Finset.Icc 1 M, g ≤ ∑ _g ∈ Finset.Icc 1 M, M := by
      refine Finset.sum_le_sum ?_
      intro g hg
      exact (Finset.mem_Icc.1 hg).2
    have hcard : (Finset.Icc 1 M).card ≤ M := by
      simp [Nat.card_Icc]
    calc
      ∑ g ∈ Finset.Icc 1 M, g ≤ ∑ _g ∈ Finset.Icc 1 M, M := h
      _ = (Finset.Icc 1 M).card * M := by simp [Finset.sum_const]
      _ ≤ M * M := Nat.mul_le_mul_right M hcard
  have hcast : (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) ≤ (↑(M * M) : ℝ) := by
    simpa [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).2 hnat
  refine hcast.trans_eq ?_
  simp [sq, Nat.cast_mul]

/--
PDF Lemma 3 (`lem:sparse-complement`):
`#(V \ ⋃_i ℱ_i) ≤ N^{s-1} A^{2s} (2s log N)^{(s+1)²}`.
-/
theorem sparse_complement_bound (s N A : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hA : 2 ≤ A) :
    ((sparseComplementFinset (s := s) (N := N) A (by omega)).card : ℝ) ≤
      sparseRHS s N A := by
  set h0 : 0 < s := by omega
  set M := min (A ^ s) N
  -- Every sparse point lies in some fibre `n₁ = g` with `1 ≤ g ≤ M`.
  have hcover :
      sparseComplementFinset (s := s) (N := N) A h0 ⊆
        (Finset.Icc 1 M).biUnion fun g => fibreN1 s N g h0 := by
    intro x hx
    have hxN : x.n1 h0 ≤ N := (x.hn ⟨0, h0⟩).2
    have hxA : x.n1 h0 ≤ A ^ s := mem_sparse_n1_le hs hA hx
    have hxM : x.n1 h0 ≤ M := by
      simp [M, hxN, hxA]
    have hx1 : 1 ≤ x.n1 h0 := by simpa [Sol.n1] using (x.hn ⟨0, h0⟩).1
    refine Finset.mem_biUnion.2 ⟨x.n1 h0, Finset.mem_Icc.2 ⟨hx1, hxM⟩, ?_⟩
    simp [fibreN1]
  -- Cardinality ≤ sum of fibre cardinalities.
  have hcard_le :
      (sparseComplementFinset (s := s) (N := N) A h0).card ≤
        ∑ g ∈ Finset.Icc 1 M, (fibreN1 s N g h0).card := by
    refine (Finset.card_le_card hcover).trans ?_
    exact Finset.card_biUnion_le
  -- Bound each fibre by the divisor-sum estimate.
  have hfib :
      ∀ g ∈ Finset.Icc 1 M,
        ((fibreN1 s N g h0).card : ℝ) ≤
          (g : ℝ) * (N : ℝ) ^ (s - 1) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
    intro g hg
    have hg1 : 1 ≤ g := (Finset.mem_Icc.1 hg).1
    have hgN : g ≤ N :=
      le_trans (Finset.mem_Icc.1 hg).2 (Nat.min_le_right _ _)
    simpa [fibreN1, Sol.n1] using fibre_n1_bound s N g hs hN hg1 hgN
  -- Sum the fibre bounds.
  have hsum :
      ((∑ g ∈ Finset.Icc 1 M, (fibreN1 s N g h0).card) : ℝ) ≤
        (∑ g ∈ Finset.Icc 1 M, g : ℝ) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
    calc
      ((∑ g ∈ Finset.Icc 1 M, (fibreN1 s N g h0).card) : ℝ)
          = ∑ g ∈ Finset.Icc 1 M, ((fibreN1 s N g h0).card : ℝ) := by
            simp
      _ ≤ ∑ g ∈ Finset.Icc 1 M,
            (g : ℝ) * (N : ℝ) ^ (s - 1) *
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
            refine Finset.sum_le_sum hfib
      _ = (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) * (N : ℝ) ^ (s - 1) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
            simp [Finset.sum_mul, mul_assoc]
  -- `∑ g ≤ M^2 ≤ A^{2s}`.
  have hM : (M : ℝ) ≤ (A : ℝ) ^ s := by
    have : M ≤ A ^ s := Nat.min_le_left _ _
    exact_mod_cast this
  have hsumg : (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) ≤ (A : ℝ) ^ (2 * s) := by
    calc
      ∑ g ∈ Finset.Icc 1 M, (g : ℝ) ≤ (M : ℝ) ^ 2 := sum_Icc_id_le_sq M
      _ ≤ ((A : ℝ) ^ s) ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
      _ = (A : ℝ) ^ (2 * s) := by ring
  -- Log factor: `(2s log N)^{s²} ≤ (2s log N)^{(s+1)²}`.
  have hbase : 1 ≤ 2 * (s : ℝ) * Real.log N := by
    have hs2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hlog3 : (2 / 3 : ℝ) ≤ Real.log 3 := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
      convert this using 1
      norm_num
    have hlogN : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hlog : (2 / 3 : ℝ) ≤ Real.log N := le_trans hlog3 hlogN
    nlinarith
  have hpow :
      (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) ≤
        (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) :=
    pow_le_pow_right₀ hbase (by
      -- `s² ≤ (s+1)²`
      exact Nat.pow_le_pow_left (Nat.le_succ s) 2)
  have hNnonneg : 0 ≤ (N : ℝ) ^ (s - 1) := by positivity
  have hApow : 0 ≤ (A : ℝ) ^ (2 * s) := by positivity
  have hlog1 : 0 ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by positivity
  -- Assemble.
  have h1 :
      ((sparseComplementFinset (s := s) (N := N) A h0).card : ℝ) ≤
        (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) := by
    refine le_trans ?_ hsum
    exact_mod_cast hcard_le
  have h2 :
      (∑ g ∈ Finset.Icc 1 M, (g : ℝ)) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) ≤
        (A : ℝ) ^ (2 * s) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsumg hNnonneg) hlog1
  have h3 :
      (A : ℝ) ^ (2 * s) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2) ≤
        (A : ℝ) ^ (2 * s) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg hApow hNnonneg)
  have h4 :
      (A : ℝ) ^ (2 * s) * (N : ℝ) ^ (s - 1) *
          (2 * (s : ℝ) * Real.log N) ^ ((s + 1) ^ 2) =
        sparseRHS s N A := by
    simp only [sparseRHS]
    ring
  exact h1.trans (h2.trans (h3.trans_eq h4))

end RMFLean
