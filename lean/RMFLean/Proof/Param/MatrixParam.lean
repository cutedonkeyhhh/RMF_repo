/-
PDF Lemma 4 (`lem:param-general`) — matrix parametrisation.

Construction (PDF proof):
  1. Diagonals first: a_ii = gcd(n_i, m_i), then set
     ñ_i = n_i / a_ii, m̃_i = m_i / a_ii (pairwise coprime residuals).
  2. Off-diagonal factorisation of the residual solution by successive
     border gcds (firstRow / firstCol) and induction on s
     (`solToMatrixCore`); diagonals of the core matrix are 1.
  3. Reassemble: scale core diagonals by a_ii.
  Fibre exactness: with gcd(A_i,B_i)=1, diagonals in the fibre are
  exactly the positive integers d ≤ N/M_i.
-/
import RMFLean.Trusted.Defs
import RMFLean.Proof.Setup.SolutionSet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith

noncomputable section

open Classical BigOperators

namespace RMFLean

/-- Matrix of positive entries. -/
structure MatrixParam (s : ℕ) where
  a : Fin s → Fin s → ℕ
  entries_pos : ∀ i j, 0 < a i j

theorem MatrixParam.ext {s : ℕ} {p q : MatrixParam s}
    (h : ∀ i j, p.a i j = q.a i j) : p = q := by
  cases p
  cases q
  simp only [MatrixParam.mk.injEq]
  exact funext fun i => funext fun j => h i j

namespace MatrixParam

/-- PDF `A_i = ∏_{j≠i} a_{ij}`. -/
def rowOffDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p.a i j

/-- PDF `B_i = ∏_{k≠i} a_{ki}`. -/
def colOffDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p.a j i

/-- PDF `M_i = max(A_i,B_i)`. -/
def scale {s : ℕ} (p : MatrixParam s) (i : Fin s) : ℕ :=
  max (p.rowOffDiag i) (p.colOffDiag i)

/-- Reconstruct `n_i = ∏_j a_{ij}`. -/
def rowProd {s : ℕ} (p : MatrixParam s) (i : Fin s) : ℕ :=
  ∏ j, p.a i j

/-- Reconstruct `m_i = ∏_k a_{ki}`. -/
def colProd {s : ℕ} (p : MatrixParam s) (i : Fin s) : ℕ :=
  ∏ k, p.a k i

/-- Allowed diagonal variable `a11 ∈ [H, N/M1]` (PDF fibre). -/
def headFibre {s : ℕ} (p : MatrixParam s)
    (N H : ℕ) (h0 : 0 < s) : Finset ℕ :=
  Finset.Icc H (N / p.scale ⟨0, h0⟩)

/-- PDF long-fibre condition `N/M1 > 2H`. -/
def IsLong {s : ℕ} (p : MatrixParam s)
    (N H : ℕ) (h0 : 0 < s) : Prop :=
  2 * H < N / p.scale ⟨0, h0⟩

/-- PDF short-fibre condition `H ≤ N/M1 ≤ 2H`. -/
def IsShort {s : ℕ} (p : MatrixParam s)
    (N H : ℕ) (h0 : 0 < s) : Prop :=
  H ≤ N / p.scale ⟨0, h0⟩ ∧ N / p.scale ⟨0, h0⟩ ≤ 2 * H

theorem long_or_short {s N H : ℕ} (p : MatrixParam s)
    (h0 : 0 < s) (hne : H ≤ N / p.scale ⟨0, h0⟩) :
    p.IsLong N H h0 ∨ p.IsShort N H h0 := by
  simp only [IsLong, IsShort]
  omega

/-- Coprimality condition (1): `gcd(A_i,B_i)=1`. -/
def CoprimeOffDiag {s : ℕ} (p : MatrixParam s) : Prop :=
  ∀ i, Nat.gcd (p.rowOffDiag i) (p.colOffDiag i) = 1

theorem rowProd_eq_diag_mul_offDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    p.rowProd i = p.a i i * p.rowOffDiag i := by
  simpa [rowProd, rowOffDiag] using
    (Finset.mul_prod_erase Finset.univ (fun j => p.a i j) (Finset.mem_univ i)).symm

theorem colProd_eq_diag_mul_offDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    p.colProd i = p.a i i * p.colOffDiag i := by
  simpa [colProd, colOffDiag] using
    (Finset.mul_prod_erase Finset.univ (fun k => p.a k i) (Finset.mem_univ i)).symm

theorem scale_pos {s : ℕ} (p : MatrixParam s) (i : Fin s) : 0 < p.scale i := by
  have hA : 0 < p.rowOffDiag i :=
    Finset.prod_pos fun _ _ => p.entries_pos _ _
  exact lt_max_of_lt_left hA

end MatrixParam

/-! ### Domain `V_H` -/

/--
PDF `V_H = {(n,m)∈V : gcd(n1,m1) > H}`.
(For `F_1` with threshold `A`, use `H = A-1`, since `gcd ≥ A ↔ gcd > A-1`.)
-/
def VH (s N H : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    H < Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩)

theorem mem_VH {s N H : ℕ} {h0 : 0 < s} {x : Sol s N} :
    x ∈ VH s N H h0 ↔
      H < Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) := by
  simp [VH]

/-- `F_1` with threshold `A` sits in `V_{A-1}` when `A ≥ 1`. -/
theorem F1_subset_VH {s N A : ℕ} (h0 : 0 < s) (hA : 1 ≤ A) :
    Ffinset (N := N) A ⟨0, h0⟩ h0 ⊆ VH s N (A - 1) h0 := by
  intro x hx
  have hx' : A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) :=
    (Finset.mem_filter.1 hx).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ x, ?_⟩
  omega

/-! ### Successive gcd extraction of the first row / column -/

/--
First-row extraction by successive gcds (PDF):
`a0 = gcd(n1, m0)`, then recurse on `(n1/a0, m.tail)`.
-/
def firstRow : (s : ℕ) → ℕ → (Fin s → ℕ) → Fin s → ℕ
  | 0, _, _ => fun j => nomatch j
  | s + 1, n1, m =>
      let a0 := Nat.gcd n1 (m 0)
      Fin.cons a0 (firstRow s (n1 / a0) (fun i => m i.succ))

/--
Tail of the first column after fixing `a11`:
`a = gcd(n0, rem)`, then recurse on `(rem/a, n.tail)`.
-/
def firstColTail : (s : ℕ) → ℕ → (Fin s → ℕ) → Fin s → ℕ
  | 0, _, _ => fun i => nomatch i
  | s + 1, rem, n =>
      let a := Nat.gcd (n 0) rem
      Fin.cons a (firstColTail s (rem / a) (fun j => n j.succ))

/--
First-column extraction (PDF), with corner `a11` already chosen:
`a01 := a11`, and the remaining entries via `firstColTail`.
-/
def firstCol {s : ℕ} (a11 : ℕ) (n : Fin s → ℕ) (m1 : ℕ) : Fin s → ℕ :=
  match s with
  | 0 => fun i => nomatch i
  | s + 1 =>
      Fin.cons a11 (firstColTail s (m1 / a11) (fun i => n i.succ))

theorem firstRow_zero {s : ℕ} (n1 : ℕ) (m : Fin (s + 1) → ℕ) :
    firstRow (s + 1) n1 m 0 = Nat.gcd n1 (m 0) := by
  simp [firstRow]

theorem firstCol_zero {s : ℕ} (a11 : ℕ) (n : Fin (s + 1) → ℕ) (m1 : ℕ) :
    firstCol a11 n m1 0 = a11 := by
  simp [firstCol]

theorem firstRow_pos (s : ℕ) (n1 : ℕ) (m : Fin s → ℕ)
    (hn1 : 0 < n1) (hm : ∀ j, 0 < m j) (j : Fin s) :
    0 < firstRow s n1 m j := by
  induction s generalizing n1 with
  | zero => exact Fin.elim0 j
  | succ s ih =>
      cases j using Fin.cases with
      | zero =>
          rw [firstRow, Fin.cons_zero]
          exact Nat.gcd_pos_of_pos_left (m 0) hn1
      | succ i =>
          rw [firstRow, Fin.cons_succ]
          have ha0 : 0 < Nat.gcd n1 (m 0) := Nat.gcd_pos_of_pos_left (m 0) hn1
          have hdiv : 0 < n1 / Nat.gcd n1 (m 0) :=
            Nat.div_pos (Nat.le_of_dvd hn1 (Nat.gcd_dvd_left _ _)) ha0
          exact ih (n1 / Nat.gcd n1 (m 0)) (fun k => m k.succ) hdiv
            (fun k => hm k.succ) i

theorem firstColTail_pos (s : ℕ) (rem : ℕ) (n : Fin s → ℕ)
    (hrem : 0 < rem) (hn : ∀ i, 0 < n i) (i : Fin s) :
    0 < firstColTail s rem n i := by
  induction s generalizing rem with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      cases i using Fin.cases with
      | zero =>
          rw [firstColTail, Fin.cons_zero]
          exact Nat.gcd_pos_of_pos_left rem (hn 0)
      | succ j =>
          rw [firstColTail, Fin.cons_succ]
          have ha : 0 < Nat.gcd (n 0) rem := Nat.gcd_pos_of_pos_left rem (hn 0)
          have hdiv : 0 < rem / Nat.gcd (n 0) rem :=
            Nat.div_pos (Nat.le_of_dvd hrem (Nat.gcd_dvd_right _ _)) ha
          exact ih (rem / Nat.gcd (n 0) rem) (fun k => n k.succ) hdiv
            (fun k => hn k.succ) j

theorem firstCol_pos {s : ℕ} (a11 : ℕ) (n : Fin s → ℕ) (m1 : ℕ)
    (ha : 0 < a11) (hn : ∀ i, 0 < n i) (hm1 : 0 < m1)
    (hdvd : a11 ∣ m1) (i : Fin s) :
    0 < firstCol a11 n m1 i := by
  match s with
  | 0 => exact Fin.elim0 i
  | s + 1 =>
      cases i using Fin.cases with
      | zero =>
          rw [firstCol, Fin.cons_zero]; exact ha
      | succ j =>
          rw [firstCol, Fin.cons_succ]
          have hdiv : 0 < m1 / a11 := Nat.div_pos (Nat.le_of_dvd hm1 hdvd) ha
          exact firstColTail_pos s (m1 / a11) (fun k => n k.succ) hdiv
            (fun k => hn k.succ) j

theorem firstRow_dvd_m (s : ℕ) (n1 : ℕ) (m : Fin s → ℕ) (j : Fin s) :
    firstRow s n1 m j ∣ m j := by
  induction s generalizing n1 with
  | zero => exact Fin.elim0 j
  | succ s ih =>
      cases j using Fin.cases with
      | zero =>
          rw [firstRow, Fin.cons_zero]; exact Nat.gcd_dvd_right _ _
      | succ i =>
          rw [firstRow, Fin.cons_succ]
          exact ih (n1 / Nat.gcd n1 (m 0)) (fun k => m k.succ) i

theorem firstColTail_dvd_n (s : ℕ) (rem : ℕ) (n : Fin s → ℕ) (i : Fin s) :
    firstColTail s rem n i ∣ n i := by
  induction s generalizing rem with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      cases i using Fin.cases with
      | zero =>
          rw [firstColTail, Fin.cons_zero]; exact Nat.gcd_dvd_left _ _
      | succ j =>
          rw [firstColTail, Fin.cons_succ]
          exact ih (rem / Nat.gcd (n 0) rem) (fun k => n k.succ) j

theorem firstCol_dvd_n {s : ℕ} (a11 : ℕ) (n : Fin (s + 1) → ℕ) (m1 : ℕ)
    (ha_dvd_n0 : a11 ∣ n 0) (i : Fin (s + 1)) :
    firstCol a11 n m1 i ∣ n i := by
  cases i using Fin.cases with
  | zero =>
      rw [firstCol, Fin.cons_zero]; exact ha_dvd_n0
  | succ j =>
      rw [firstCol, Fin.cons_succ]
      exact firstColTail_dvd_n s (m1 / a11) (fun k => n k.succ) j

/-! ### Border product recovery (handwritten refinement lemma) -/

/--
Successive gcds recover `n1 = ∏_j a1j` whenever `n1 ∣ ∏ m_j`.
Handwritten: after `a0 = gcd(n1,m0)`, the coprime residual divides the tail product.
-/
theorem firstRow_prod (s : ℕ) (n1 : ℕ) (m : Fin s → ℕ)
    (hn1 : 0 < n1) (hm : ∀ j, 0 < m j)
    (hdvd : n1 ∣ ∏ j, m j) :
    (∏ j, firstRow s n1 m j) = n1 := by
  induction s generalizing n1 with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.prod_empty] at hdvd ⊢
      exact (Nat.dvd_one.mp hdvd).symm
  | succ s ih =>
      set a0 := Nat.gcd n1 (m 0) with ha0
      have ha0n : a0 ∣ n1 := Nat.gcd_dvd_left _ _
      have ha0m : a0 ∣ m 0 := Nat.gcd_dvd_right _ _
      have ha0pos : 0 < a0 := Nat.gcd_pos_of_pos_left (m 0) hn1
      have hn1' : 0 < n1 / a0 :=
        Nat.div_pos (Nat.le_of_dvd hn1 ha0n) ha0pos
      have hcop : Nat.Coprime (n1 / a0) (m 0 / a0) := by
        simpa [ha0] using Nat.coprime_div_gcd_div_gcd (m := n1) (n := m 0) ha0pos
      have hdvd' : n1 / a0 ∣ ∏ i : Fin s, m i.succ := by
        have hmul : a0 * (n1 / a0) ∣ m 0 * ∏ i : Fin s, m i.succ := by
          rw [Nat.mul_div_cancel' ha0n]
          simpa [Fin.prod_univ_succ] using hdvd
        have hrew : m 0 * ∏ i : Fin s, m i.succ =
            a0 * ((m 0 / a0) * ∏ i : Fin s, m i.succ) := by
          rw [← mul_assoc, Nat.mul_div_cancel' ha0m]
        have hmul' : a0 * (n1 / a0) ∣
            a0 * ((m 0 / a0) * ∏ i : Fin s, m i.succ) := by
          rwa [← hrew]
        have hdiv : n1 / a0 ∣ (m 0 / a0) * ∏ i : Fin s, m i.succ :=
          Nat.dvd_of_mul_dvd_mul_left ha0pos hmul'
        exact hcop.dvd_of_dvd_mul_left hdiv
      have hshape :
          firstRow (s + 1) n1 m =
            Fin.cons a0 (firstRow s (n1 / a0) (fun i => m i.succ)) := by
        simp [firstRow, ha0]
      rw [hshape, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih (n1 / a0) (fun i => m i.succ) hn1' (fun k => hm k.succ) hdvd']
      exact Nat.mul_div_cancel' ha0n

/--
Successive gcds recover `rem = ∏ firstColTail` whenever `rem ∣ ∏ n`.
-/
theorem firstColTail_prod (s : ℕ) (rem : ℕ) (n : Fin s → ℕ)
    (hrem : 0 < rem) (hn : ∀ i, 0 < n i)
    (hdvd : rem ∣ ∏ i, n i) :
    (∏ i, firstColTail s rem n i) = rem := by
  induction s generalizing rem with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.prod_empty] at hdvd ⊢
      exact (Nat.dvd_one.mp hdvd).symm
  | succ s ih =>
      set a := Nat.gcd (n 0) rem with ha
      have han : a ∣ n 0 := Nat.gcd_dvd_left _ _
      have har : a ∣ rem := Nat.gcd_dvd_right _ _
      have hapos : 0 < a := Nat.gcd_pos_of_pos_left rem (hn 0)
      have hrem' : 0 < rem / a :=
        Nat.div_pos (Nat.le_of_dvd hrem har) hapos
      have hcop : Nat.Coprime (n 0 / a) (rem / a) := by
        simpa [ha] using Nat.coprime_div_gcd_div_gcd (m := n 0) (n := rem) hapos
      have hdvd' : rem / a ∣ ∏ i : Fin s, n i.succ := by
        have hmul : a * (rem / a) ∣ n 0 * ∏ i : Fin s, n i.succ := by
          rw [Nat.mul_div_cancel' har]
          simpa [Fin.prod_univ_succ] using hdvd
        have hrew : n 0 * ∏ i : Fin s, n i.succ =
            a * ((n 0 / a) * ∏ i : Fin s, n i.succ) := by
          rw [← mul_assoc, Nat.mul_div_cancel' han]
        have hmul' : a * (rem / a) ∣
            a * ((n 0 / a) * ∏ i : Fin s, n i.succ) := by
          rwa [← hrew]
        have hdiv : rem / a ∣ (n 0 / a) * ∏ i : Fin s, n i.succ :=
          Nat.dvd_of_mul_dvd_mul_left hapos hmul'
        exact hcop.symm.dvd_of_dvd_mul_left hdiv
      have hshape :
          firstColTail (s + 1) rem n =
            Fin.cons a (firstColTail s (rem / a) (fun i => n i.succ)) := by
        simp [firstColTail, ha]
      rw [hshape, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih (rem / a) (fun i => n i.succ) hrem' (fun k => hn k.succ) hdvd']
      exact Nat.mul_div_cancel' har

/--
First-column product: `a11 ∣ m1` and `(m1/a11) ∣ ∏_{i≥1} n_i`.
(The tail-divisibility is what the product equation gives after cancelling `gcd`.)
-/
theorem firstCol_prod {s : ℕ} (a11 : ℕ) (n : Fin (s + 1) → ℕ) (m1 : ℕ)
    (ha : 0 < a11) (hn : ∀ i, 0 < n i) (hm1 : 0 < m1)
    (hdvd_a : a11 ∣ m1)
    (hdvd_rem : m1 / a11 ∣ ∏ i : Fin s, n i.succ) :
    (∏ i, firstCol a11 n m1 i) = m1 := by
  have hdiv : 0 < m1 / a11 := Nat.div_pos (Nat.le_of_dvd hm1 hdvd_a) ha
  have hshape :
      firstCol a11 n m1 =
        Fin.cons a11 (firstColTail s (m1 / a11) (fun i => n i.succ)) := by
    simp [firstCol]
  rw [hshape, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [firstColTail_prod s (m1 / a11) (fun i => n i.succ) hdiv
      (fun k => hn k.succ) hdvd_rem]
  exact Nat.mul_div_cancel' hdvd_a

/-! ### Residuals after border extraction -/

/-- Residual row coordinates after removing the first column. -/
def residualN {s : ℕ} (n : Fin (s + 1) → ℕ) (aCol : Fin (s + 1) → ℕ) :
    Fin s → ℕ :=
  fun i => n i.succ / aCol i.succ

/-- Residual column coordinates after removing the first row. -/
def residualM {s : ℕ} (m : Fin (s + 1) → ℕ) (aRow : Fin (s + 1) → ℕ) :
    Fin s → ℕ :=
  fun i => m i.succ / aRow i.succ

/-- From `∏ n = ∏ m`, the corner residual of `m0` divides the `n`-tail. -/
theorem rem_m_dvd_n_tail {s : ℕ} (n m : Fin (s + 1) → ℕ)
    (hn : ∀ i, 0 < n i) (_hm : ∀ i, 0 < m i)
    (hprod : (∏ i, n i) = (∏ i, m i)) :
    let a11 := Nat.gcd (n 0) (m 0)
    m 0 / a11 ∣ ∏ i : Fin s, n i.succ := by
  intro a11
  have ha11n : a11 ∣ n 0 := Nat.gcd_dvd_left _ _
  have ha11m : a11 ∣ m 0 := Nat.gcd_dvd_right _ _
  have ha11pos : 0 < a11 := Nat.gcd_pos_of_pos_left (m 0) (hn 0)
  have hcop : Nat.Coprime (n 0 / a11) (m 0 / a11) :=
    Nat.coprime_div_gcd_div_gcd (m := n 0) (n := m 0) ha11pos
  have hmul :
      a11 * (n 0 / a11) * ∏ i : Fin s, n i.succ =
        a11 * (m 0 / a11) * ∏ i : Fin s, m i.succ := by
    rw [Nat.mul_div_cancel' ha11n, Nat.mul_div_cancel' ha11m]
    simpa [Fin.prod_univ_succ] using hprod
  have hmul' :
      (n 0 / a11) * ∏ i : Fin s, n i.succ =
        (m 0 / a11) * ∏ i : Fin s, m i.succ :=
    Nat.mul_left_cancel ha11pos (by simpa [mul_assoc] using hmul)
  have : m 0 / a11 ∣ (n 0 / a11) * ∏ i : Fin s, n i.succ := by
    rw [hmul']
    exact dvd_mul_right _ _
  exact hcop.symm.dvd_of_dvd_mul_left this

/--
Handwritten inductive cancellation: after extracting the first row/column,
the residuals satisfy a product equation of order `s`.
-/
theorem residual_product {s : ℕ}
    (n m : Fin (s + 1) → ℕ)
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i)
    (hprod : (∏ i, n i) = (∏ i, m i)) :
    let aRow := firstRow (s + 1) (n 0) m
    let aCol := firstCol (aRow 0) n (m 0)
    (∏ i, residualN n aCol i) = (∏ i, residualM m aRow i) := by
  intro aRow aCol
  have hn0_dvd : n 0 ∣ ∏ j, m j := by
    have : n 0 ∣ ∏ i, n i := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    exact this.trans (hprod ▸ dvd_rfl)
  have hrow : (∏ j, aRow j) = n 0 :=
    firstRow_prod (s + 1) (n 0) m (hn 0) hm hn0_dvd
  have ha11 : aRow 0 = Nat.gcd (n 0) (m 0) := firstRow_zero (n 0) m
  have ha11pos : 0 < aRow 0 :=
    firstRow_pos (s + 1) (n 0) m (hn 0) hm 0
  have ha11m : aRow 0 ∣ m 0 := firstRow_dvd_m (s + 1) (n 0) m 0
  have ha11n : aRow 0 ∣ n 0 := by
    rw [ha11]; exact Nat.gcd_dvd_left _ _
  have hdvd_rem : m 0 / aRow 0 ∣ ∏ i : Fin s, n i.succ := by
    simpa [ha11] using rem_m_dvd_n_tail n m hn hm hprod
  have hcol : (∏ i, aCol i) = m 0 :=
    firstCol_prod (s := s) (aRow 0) n (m 0) ha11pos hn (hm 0) ha11m hdvd_rem
  have hdivN : ∀ i : Fin s, aCol i.succ ∣ n i.succ := fun i =>
    firstCol_dvd_n (s := s) (aRow 0) n (m 0) ha11n i.succ
  have hdivM : ∀ i : Fin s, aRow i.succ ∣ m i.succ := fun i =>
    firstRow_dvd_m (s + 1) (n 0) m i.succ
  have hn_eq : ∀ i : Fin s, n i.succ = aCol i.succ * residualN n aCol i :=
    fun i => (Nat.mul_div_cancel' (hdivN i)).symm
  have hm_eq : ∀ i : Fin s, m i.succ = aRow i.succ * residualM m aRow i :=
    fun i => (Nat.mul_div_cancel' (hdivM i)).symm
  have hprod' :
      n 0 * ∏ i : Fin s, n i.succ = m 0 * ∏ i : Fin s, m i.succ := by
    simpa [Fin.prod_univ_succ] using hprod
  have hN :
      ∏ i : Fin s, n i.succ =
        (∏ i : Fin s, aCol i.succ) * ∏ i, residualN n aCol i := by
    simp_rw [hn_eq, Finset.prod_mul_distrib]
  have hM :
      ∏ i : Fin s, m i.succ =
        (∏ i : Fin s, aRow i.succ) * ∏ i, residualM m aRow i := by
    simp_rw [hm_eq, Finset.prod_mul_distrib]
  have hrow' : n 0 = aRow 0 * ∏ i : Fin s, aRow i.succ := by
    simpa [Fin.prod_univ_succ] using hrow.symm
  have hcol' : m 0 = aCol 0 * ∏ i : Fin s, aCol i.succ := by
    simpa [Fin.prod_univ_succ] using hcol.symm
  have ha00 : aRow 0 = aCol 0 := by
    simp [aCol, firstCol, ha11]
  have hcancel :
      aRow 0 * (∏ i : Fin s, aRow i.succ) * (∏ i : Fin s, aCol i.succ) *
          ∏ i, residualN n aCol i =
        aRow 0 * (∏ i : Fin s, aCol i.succ) * (∏ i : Fin s, aRow i.succ) *
          ∏ i, residualM m aRow i := by
    calc
      aRow 0 * (∏ i : Fin s, aRow i.succ) * (∏ i : Fin s, aCol i.succ) *
          ∏ i, residualN n aCol i =
        n 0 * ∏ i : Fin s, n i.succ := by
          rw [← hrow', hN]; ring
      _ = m 0 * ∏ i : Fin s, m i.succ := hprod'
      _ = aCol 0 * (∏ i : Fin s, aCol i.succ) * (∏ i : Fin s, aRow i.succ) *
            ∏ i, residualM m aRow i := by
          rw [hcol', hM]; ring
      _ = aRow 0 * (∏ i : Fin s, aCol i.succ) * (∏ i : Fin s, aRow i.succ) *
            ∏ i, residualM m aRow i := by
          rw [ha00]
  have hpos :
      0 < aRow 0 * (∏ i : Fin s, aRow i.succ) * (∏ i : Fin s, aCol i.succ) := by
    refine Nat.mul_pos (Nat.mul_pos ha11pos ?_) ?_
    · exact Finset.prod_pos fun i _ =>
        firstRow_pos (s + 1) (n 0) m (hn 0) hm i.succ
    · exact Finset.prod_pos fun i _ =>
        firstCol_pos (aRow 0) n (m 0) ha11pos hn (hm 0) ha11m i.succ
  have hcancel' :
      aRow 0 * (∏ i : Fin s, aRow i.succ) * (∏ i : Fin s, aCol i.succ) *
          ∏ i, residualN n aCol i =
        aRow 0 * (∏ i : Fin s, aRow i.succ) * (∏ i : Fin s, aCol i.succ) *
          ∏ i, residualM m aRow i := by
    convert hcancel using 1
    ac_rfl
  exact Nat.mul_left_cancel hpos hcancel'

/-- Residuals stay in `[1,N]`. -/
theorem residual_bounds {s N : ℕ}
    (n m : Fin (s + 1) → ℕ)
    (hn : ∀ i, 1 ≤ n i ∧ n i ≤ N) (hm : ∀ i, 1 ≤ m i ∧ m i ≤ N) :
    let aRow := firstRow (s + 1) (n 0) m
    let aCol := firstCol (aRow 0) n (m 0)
    (∀ i, 1 ≤ residualN n aCol i ∧ residualN n aCol i ≤ N) ∧
      (∀ i, 1 ≤ residualM m aRow i ∧ residualM m aRow i ≤ N) := by
  intro aRow aCol
  have hnpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hn i).1
  have hmpos : ∀ i, 0 < m i := fun i => lt_of_lt_of_le Nat.zero_lt_one (hm i).1
  have ha11pos : 0 < aRow 0 :=
    firstRow_pos (s + 1) (n 0) m (hnpos 0) hmpos 0
  have ha11m : aRow 0 ∣ m 0 := firstRow_dvd_m (s + 1) (n 0) m 0
  have ha11n : aRow 0 ∣ n 0 := by
    have : aRow 0 = Nat.gcd (n 0) (m 0) := firstRow_zero (n 0) m
    rw [this]; exact Nat.gcd_dvd_left _ _
  refine ⟨?_, ?_⟩
  · intro i
    have hdiv : aCol i.succ ∣ n i.succ :=
      firstCol_dvd_n (aRow 0) n (m 0) ha11n i.succ
    have hapos : 0 < aCol i.succ :=
      firstCol_pos (aRow 0) n (m 0) ha11pos hnpos (hmpos 0) ha11m i.succ
    have hge : 1 ≤ residualN n aCol i := by
      exact Nat.div_pos (Nat.le_of_dvd (hnpos i.succ) hdiv) hapos
    have hle : residualN n aCol i ≤ N :=
      le_trans (Nat.div_le_self _ _) (hn i.succ).2
    exact ⟨hge, hle⟩
  · intro i
    have hdiv : aRow i.succ ∣ m i.succ :=
      firstRow_dvd_m (s + 1) (n 0) m i.succ
    have hapos : 0 < aRow i.succ :=
      firstRow_pos (s + 1) (n 0) m (hnpos 0) hmpos i.succ
    have hge : 1 ≤ residualM m aRow i := by
      exact Nat.div_pos (Nat.le_of_dvd (hmpos i.succ) hdiv) hapos
    have hle : residualM m aRow i ≤ N :=
      le_trans (Nat.div_le_self _ _) (hm i.succ).2
    exact ⟨hge, hle⟩

/-! ### Recursive matrix construction -/

/-! ### Residual solution for the recursive branch -/

/-- Pairwise coprimality: `gcd(n_i,m_i)=1` for every index. -/
def PairwiseCoprime {s N : ℕ} (x : Sol s N) : Prop :=
  ∀ i, Nat.gcd (x.n i) (x.m i) = 1

/-- Diagonal gcd vector `a_ii := gcd(n_i,m_i)`. -/
def diagGcd {s N : ℕ} (x : Sol s N) (i : Fin s) : ℕ :=
  Nat.gcd (x.n i) (x.m i)

theorem diagGcd_pos {s N : ℕ} (x : Sol s N) (i : Fin s) : 0 < diagGcd x i :=
  Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn i).1)

theorem diagGcd_dvd_n {s N : ℕ} (x : Sol s N) (i : Fin s) : diagGcd x i ∣ x.n i :=
  Nat.gcd_dvd_left _ _

theorem diagGcd_dvd_m {s N : ℕ} (x : Sol s N) (i : Fin s) : diagGcd x i ∣ x.m i :=
  Nat.gcd_dvd_right _ _

/-- Peel diagonals: `ñ_i = n_i/a_ii`, `m̃_i = m_i/a_ii` (PDF: define `a_ii` first). -/
noncomputable def afterDiag {s N : ℕ} (x : Sol s N) : Sol s N := by
  refine
    { n := fun i => x.n i / diagGcd x i
      m := fun i => x.m i / diagGcd x i
      hn := ?_
      hm := ?_
      hprod := ?_ }
  · intro i
    have hpos := diagGcd_pos x i
    have hdvd := diagGcd_dvd_n x i
    refine ⟨Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hn i).1) hdvd) hpos, ?_⟩
    exact le_trans (Nat.div_le_self _ _) (x.hn i).2
  · intro i
    have hpos := diagGcd_pos x i
    have hdvd := diagGcd_dvd_m x i
    refine ⟨Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hm i).1) hdvd) hpos, ?_⟩
    exact le_trans (Nat.div_le_self _ _) (x.hm i).2
  · have hmul :
        (∏ i, diagGcd x i) * ∏ i, x.n i / diagGcd x i =
          (∏ i, diagGcd x i) * ∏ i, x.m i / diagGcd x i := by
      have hn : (∏ i, diagGcd x i) * ∏ i, x.n i / diagGcd x i = ∏ i, x.n i := by
        simp_rw [← Finset.prod_mul_distrib, Nat.mul_div_cancel' (diagGcd_dvd_n x _)]
      have hm : (∏ i, diagGcd x i) * ∏ i, x.m i / diagGcd x i = ∏ i, x.m i := by
        simp_rw [← Finset.prod_mul_distrib, Nat.mul_div_cancel' (diagGcd_dvd_m x _)]
      rw [hn, hm, x.hprod]
    have hpos : 0 < ∏ i, diagGcd x i := Finset.prod_pos fun i _ => diagGcd_pos x i
    exact Nat.mul_left_cancel hpos hmul

theorem afterDiag_n {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (afterDiag x).n i = x.n i / diagGcd x i := rfl

theorem afterDiag_m {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (afterDiag x).m i = x.m i / diagGcd x i := rfl

theorem afterDiag_pairwiseCoprime {s N : ℕ} (x : Sol s N) :
    PairwiseCoprime (afterDiag x) := by
  intro i
  simpa [PairwiseCoprime, afterDiag_n, afterDiag_m, diagGcd] using
    Nat.coprime_div_gcd_div_gcd (diagGcd_pos x i)

/-- Residual solution used in the recursive branch of `solToMatrixCore`. -/
noncomputable def solToMatrixCore.residualSol {s N : ℕ} (x : Sol (s + 2) N) :
    Sol (s + 1) N := by
  let aRow := firstRow (s + 2) (x.n 0) x.m
  let aCol := firstCol (aRow 0) x.n (x.m 0)
  have hb := residual_bounds (s := s + 1) (N := N) x.n x.m x.hn x.hm
  have hp := residual_product (s := s + 1) x.n x.m
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (x.hn i).1)
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (x.hm i).1) x.hprod
  exact
    { n := residualN x.n aCol
      m := residualM x.m aRow
      hn := fun i => hb.1 i
      hm := fun i => hb.2 i
      hprod := hp }

/--
Border extraction + induction on `s` (off-diagonal factorisation of a
pairwise-coprime solution). Diagonals of the result are `1` when
`PairwiseCoprime x`.
-/
def solToMatrixCore {s N : ℕ} (x : Sol s N) : MatrixParam s :=
  match s with
  | 0 =>
      { a := fun i _ => nomatch i
        entries_pos := fun i _ => nomatch i }
  | 1 =>
      { a := fun _ _ => x.n 0
        entries_pos := fun _ _ => lt_of_lt_of_le Nat.zero_lt_one (x.hn 0).1 }
  | s + 2 =>
      let aRow := firstRow (s + 2) (x.n 0) x.m
      let aCol := firstCol (aRow 0) x.n (x.m 0)
      let pRec := solToMatrixCore (solToMatrixCore.residualSol x)
      { a := fun i j =>
          if i.1 = 0 then aRow j
          else if j.1 = 0 then aCol i
          else pRec.a ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩
        entries_pos := by
          intro i j
          by_cases hi : i.1 = 0
          · simp [hi]
            exact firstRow_pos (s + 2) (x.n 0) x.m
              (lt_of_lt_of_le Nat.zero_lt_one (x.hn 0).1)
              (fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hm k).1) j
          · by_cases hj : j.1 = 0
            · simp [hi, hj]
              have ha11 : 0 < aRow 0 :=
                firstRow_pos (s + 2) (x.n 0) x.m
                  (lt_of_lt_of_le Nat.zero_lt_one (x.hn 0).1)
                  (fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hm k).1) 0
              have hdvd : aRow 0 ∣ x.m 0 := firstRow_dvd_m (s + 2) (x.n 0) x.m 0
              exact firstCol_pos (aRow 0) x.n (x.m 0) ha11
                (fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hn k).1)
                (lt_of_lt_of_le Nat.zero_lt_one (x.hm 0).1) hdvd i
            · simp [hi, hj]
              exact pRec.entries_pos _ _ }

/--
PDF Lemma 4 map: peel `a_ii = gcd(n_i,m_i)`, then factor off-diagonals of the
coprime residuals by `solToMatrixCore`.
-/
def solToMatrix {s N : ℕ} (x : Sol s N) : MatrixParam s :=
  let p := solToMatrixCore (afterDiag x)
  { a := fun i j =>
      if i = j then diagGcd x i * p.a i j else p.a i j
    entries_pos := by
      intro i j
      by_cases hij : i = j
      · subst hij
        simpa using Nat.mul_pos (diagGcd_pos x i) (p.entries_pos i i)
      · simpa [hij] using p.entries_pos i j }

/-! ### Unfolding lemmas for the `s ≥ 2` branch of `solToMatrixCore` -/

theorem solToMatrixCore_a_row0 {s N : ℕ} (x : Sol (s + 2) N) (j : Fin (s + 2)) :
    (solToMatrixCore x).a 0 j = firstRow (s + 2) (x.n 0) x.m j := by
  simp [solToMatrixCore]

theorem solToMatrixCore_a_col0 {s N : ℕ} (x : Sol (s + 2) N)
    (i : Fin (s + 2)) (hi : i.1 ≠ 0) :
    (solToMatrixCore x).a i 0 =
      firstCol (firstRow (s + 2) (x.n 0) x.m 0) x.n (x.m 0) i := by
  have hi' : i ≠ 0 := Fin.ne_of_val_ne hi
  simp [solToMatrixCore, hi']

theorem solToMatrixCore_a_inner {s N : ℕ} (x : Sol (s + 2) N)
    (i j : Fin (s + 2)) (hi : i.1 ≠ 0) (hj : j.1 ≠ 0) :
    (solToMatrixCore x).a i j =
      (solToMatrixCore (solToMatrixCore.residualSol x)).a
        ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩ := by
  have hi' : i ≠ 0 := Fin.ne_of_val_ne hi
  have hj' : j ≠ 0 := Fin.ne_of_val_ne hj
  simp [solToMatrixCore, hi', hj']

/-- Core reconstruction: `n_i = ∏_j a_{ij}`. -/
theorem solToMatrixCore_rowProd {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrixCore x).rowProd i = x.n i := by
  induction s generalizing N with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      match s with
      | 0 =>
          fin_cases i
          simp [solToMatrixCore, MatrixParam.rowProd]
      | s + 1 =>
          let aRow := firstRow (s + 2) (x.n 0) x.m
          let aCol := firstCol (aRow 0) x.n (x.m 0)
          have hnpos : ∀ k, 0 < x.n k :=
            fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hn k).1
          have hmpos : ∀ k, 0 < x.m k :=
            fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hm k).1
          have hn0_dvd : x.n 0 ∣ ∏ j, x.m j := by
            have : x.n 0 ∣ ∏ k, x.n k :=
              Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
            exact this.trans (x.hprod ▸ dvd_rfl)
          have hrowBorder : (∏ j, aRow j) = x.n 0 :=
            firstRow_prod (s + 2) (x.n 0) x.m (hnpos 0) hmpos hn0_dvd
          by_cases hi : i.1 = 0
          · have hi0 : i = 0 := Fin.ext hi
            rw [hi0, MatrixParam.rowProd]
            simp_rw [solToMatrixCore_a_row0]
            exact hrowBorder
          · set iRes : Fin (s + 1) := ⟨i.1 - 1, by omega⟩
            have hi_succ : iRes.succ = i := Fin.ext (by simp [iRes]; omega)
            have hdiv : aCol i ∣ x.n i := by
              have ha11n : aRow 0 ∣ x.n 0 := by
                have : aRow 0 = Nat.gcd (x.n 0) (x.m 0) :=
                  firstRow_zero (x.n 0) x.m
                rw [this]; exact Nat.gcd_dvd_left _ _
              simpa [aCol] using firstCol_dvd_n (aRow 0) x.n (x.m 0) ha11n i
            have hy :
                (solToMatrixCore.residualSol x).n iRes = x.n i / aCol i := by
              simp only [solToMatrixCore.residualSol, residualN, aCol]
              rw [hi_succ]
            calc
              (solToMatrixCore x).rowProd i
                = (solToMatrixCore x).a i 0 *
                    ∏ k : Fin (s + 1), (solToMatrixCore x).a i k.succ := by
                      simp [MatrixParam.rowProd, Fin.prod_univ_succ]
              _ = aCol i *
                    ∏ k : Fin (s + 1),
                      (solToMatrixCore (solToMatrixCore.residualSol x)).a iRes k := by
                    rw [solToMatrixCore_a_col0 x i hi]
                    refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
                    have hk : (k.succ : Fin (s + 2)).1 ≠ 0 := by simp
                    simpa [iRes] using solToMatrixCore_a_inner x i k.succ hi hk
              _ = aCol i *
                    (solToMatrixCore (solToMatrixCore.residualSol x)).rowProd iRes := rfl
              _ = aCol i * (solToMatrixCore.residualSol x).n iRes := by
                    rw [ih (solToMatrixCore.residualSol x) iRes]
              _ = aCol i * (x.n i / aCol i) := by rw [hy]
              _ = x.n i := Nat.mul_div_cancel' hdiv

/-- Core reconstruction: `m_i = ∏_k a_{ki}`. -/
theorem solToMatrixCore_colProd {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrixCore x).colProd i = x.m i := by
  induction s generalizing N with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      match s with
      | 0 =>
          fin_cases i
          simp [solToMatrixCore, MatrixParam.colProd]
          have hnm : x.n 0 = x.m 0 := by
            simpa [Fin.prod_univ_one] using x.hprod
          exact hnm
      | s + 1 =>
          let aRow := firstRow (s + 2) (x.n 0) x.m
          let aCol := firstCol (aRow 0) x.n (x.m 0)
          have hnpos : ∀ k, 0 < x.n k :=
            fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hn k).1
          have hmpos : ∀ k, 0 < x.m k :=
            fun k => lt_of_lt_of_le Nat.zero_lt_one (x.hm k).1
          have ha11 : aRow 0 = Nat.gcd (x.n 0) (x.m 0) := firstRow_zero (x.n 0) x.m
          have ha11pos : 0 < aRow 0 :=
            firstRow_pos (s + 2) (x.n 0) x.m (hnpos 0) hmpos 0
          have ha11m : aRow 0 ∣ x.m 0 := firstRow_dvd_m (s + 2) (x.n 0) x.m 0
          have hdvd_rem : x.m 0 / aRow 0 ∣ ∏ k : Fin (s + 1), x.n k.succ := by
            simpa [ha11] using
              rem_m_dvd_n_tail (s := s + 1) x.n x.m hnpos hmpos x.hprod
          have hcolBorder : (∏ k, aCol k) = x.m 0 :=
            firstCol_prod (s := s + 1) (aRow 0) x.n (x.m 0)
              ha11pos hnpos (hmpos 0) ha11m hdvd_rem
          by_cases hi : i.1 = 0
          · have hi0 : i = 0 := Fin.ext hi
            rw [hi0, MatrixParam.colProd]
            have hcmp :
                (fun k : Fin (s + 2) => (solToMatrixCore x).a k 0) = aCol := by
              funext k
              by_cases hk : k.1 = 0
              · have hk0 : k = 0 := Fin.ext hk
                rw [hk0]
                simp [solToMatrixCore_a_row0, aCol, firstCol, aRow]
              · exact solToMatrixCore_a_col0 x k hk
            simp_rw [hcmp]
            exact hcolBorder
          · set iRes : Fin (s + 1) := ⟨i.1 - 1, by omega⟩
            have hi_succ : iRes.succ = i := Fin.ext (by simp [iRes]; omega)
            have hdiv : aRow i ∣ x.m i := firstRow_dvd_m (s + 2) (x.n 0) x.m i
            have hy :
                (solToMatrixCore.residualSol x).m iRes = x.m i / aRow i := by
              simp only [solToMatrixCore.residualSol, residualM, aRow]
              rw [hi_succ]
            calc
              (solToMatrixCore x).colProd i
                = (solToMatrixCore x).a 0 i *
                    ∏ k : Fin (s + 1), (solToMatrixCore x).a k.succ i := by
                      simp [MatrixParam.colProd, Fin.prod_univ_succ]
              _ = aRow i *
                    ∏ k : Fin (s + 1),
                      (solToMatrixCore (solToMatrixCore.residualSol x)).a k iRes := by
                    rw [solToMatrixCore_a_row0 x i]
                    refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
                    have hk : (k.succ : Fin (s + 2)).1 ≠ 0 := by simp
                    simpa [iRes] using solToMatrixCore_a_inner x k.succ i hk hi
              _ = aRow i *
                    (solToMatrixCore (solToMatrixCore.residualSol x)).colProd iRes := rfl
              _ = aRow i * (solToMatrixCore.residualSol x).m iRes := by
                    rw [ih (solToMatrixCore.residualSol x) iRes]
              _ = aRow i * (x.m i / aRow i) := by rw [hy]
              _ = x.m i := Nat.mul_div_cancel' hdiv

/-! ### Pairwise-coprime core: diagonals are 1 and condition (1) -/

theorem residualSol_pairwiseCoprime {s N : ℕ} (x : Sol (s + 2) N)
    (hx : PairwiseCoprime x) :
    PairwiseCoprime (solToMatrixCore.residualSol x) := by
  intro i
  set aRow := firstRow (s + 2) (x.n 0) x.m
  set aCol := firstCol (aRow 0) x.n (x.m 0)
  have hn' : (solToMatrixCore.residualSol x).n i = x.n i.succ / aCol i.succ := by
    simp only [solToMatrixCore.residualSol, residualN, aRow, aCol]
  have hm' : (solToMatrixCore.residualSol x).m i = x.m i.succ / aRow i.succ := by
    simp only [solToMatrixCore.residualSol, residualM, aRow]
  have ha11n : aRow 0 ∣ x.n 0 := by
    have : aRow 0 = Nat.gcd (x.n 0) (x.m 0) := firstRow_zero (x.n 0) x.m
    rw [this]; exact Nat.gcd_dvd_left _ _
  have hdivN : aCol i.succ ∣ x.n i.succ :=
    firstCol_dvd_n (aRow 0) x.n (x.m 0) ha11n i.succ
  have hdivM : aRow i.succ ∣ x.m i.succ := firstRow_dvd_m (s + 2) (x.n 0) x.m i.succ
  set d := Nat.gcd ((solToMatrixCore.residualSol x).n i)
      ((solToMatrixCore.residualSol x).m i)
  have hd_n' : d ∣ (solToMatrixCore.residualSol x).n i := Nat.gcd_dvd_left _ _
  have hd_m' : d ∣ (solToMatrixCore.residualSol x).m i := Nat.gcd_dvd_right _ _
  have hd_n : d ∣ x.n i.succ := by
    rw [hn'] at hd_n'
    exact hd_n'.trans (Nat.div_dvd_of_dvd hdivN)
  have hd_m : d ∣ x.m i.succ := by
    rw [hm'] at hd_m'
    exact hd_m'.trans (Nat.div_dvd_of_dvd hdivM)
  have hd_gcd : d ∣ Nat.gcd (x.n i.succ) (x.m i.succ) := Nat.dvd_gcd hd_n hd_m
  have h1 : Nat.gcd (x.n i.succ) (x.m i.succ) = 1 := hx i.succ
  have hd1 : d = 1 := by rwa [h1, Nat.dvd_one] at hd_gcd
  simp [d, hd1]

theorem solToMatrixCore_diag_eq_gcd_of_pairwise {s N : ℕ} (x : Sol s N)
    (hx : PairwiseCoprime x) (i : Fin s) :
    (solToMatrixCore x).a i i = Nat.gcd (x.n i) (x.m i) := by
  induction s generalizing N with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      match s with
      | 0 =>
          fin_cases i
          simp [solToMatrixCore]
          have hnm : x.n 0 = x.m 0 := by
            simpa [Fin.prod_univ_one] using x.hprod
          simp [hnm, Nat.gcd_self]
      | s + 1 =>
          by_cases hi : i.1 = 0
          · have hi0 : i = 0 := Fin.ext hi
            subst hi0
            simp [solToMatrixCore, firstRow_zero]
          · set iRes : Fin (s + 1) := ⟨i.1 - 1, by omega⟩
            have hres := residualSol_pairwiseCoprime x hx
            have hinner := solToMatrixCore_a_inner x i i hi hi
            have hih := ih (solToMatrixCore.residualSol x) hres iRes
            have hx1 : Nat.gcd (x.n i) (x.m i) = 1 := hx i
            have hr1 :
                Nat.gcd ((solToMatrixCore.residualSol x).n iRes)
                  ((solToMatrixCore.residualSol x).m iRes) = 1 := hres iRes
            calc
              (solToMatrixCore x).a i i
                = (solToMatrixCore (solToMatrixCore.residualSol x)).a iRes iRes := by
                    simpa [iRes] using hinner
              _ = Nat.gcd ((solToMatrixCore.residualSol x).n iRes)
                    ((solToMatrixCore.residualSol x).m iRes) := hih
              _ = 1 := hr1
              _ = Nat.gcd (x.n i) (x.m i) := hx1.symm

theorem solToMatrixCore_diag_eq_one_of_pairwise {s N : ℕ} (x : Sol s N)
    (hx : PairwiseCoprime x) (i : Fin s) :
    (solToMatrixCore x).a i i = 1 := by
  rw [solToMatrixCore_diag_eq_gcd_of_pairwise x hx i, hx i]

theorem solToMatrixCore_coprime_of_pairwise {s N : ℕ} (x : Sol s N)
    (hx : PairwiseCoprime x) :
    (solToMatrixCore x).CoprimeOffDiag := by
  intro i
  set p := solToMatrixCore x
  set aii := p.a i i
  set A := p.rowOffDiag i
  set B := p.colOffDiag i
  have ha : aii = 1 := solToMatrixCore_diag_eq_one_of_pairwise x hx i
  have hn : aii * A = x.n i := by
    rw [← p.rowProd_eq_diag_mul_offDiag i, solToMatrixCore_rowProd]
  have hm : aii * B = x.m i := by
    rw [← p.colProd_eq_diag_mul_offDiag i, solToMatrixCore_colProd]
  have hA : A = x.n i := by simpa [ha] using hn
  have hB : B = x.m i := by simpa [ha] using hm
  simpa [hA, hB] using hx i

/-! ### Wrapper `solToMatrix` properties -/

theorem solToMatrix_a_off {s N : ℕ} (x : Sol s N) (i j : Fin s) (hij : i ≠ j) :
    (solToMatrix x).a i j = (solToMatrixCore (afterDiag x)).a i j := by
  simp only [solToMatrix]
  exact if_neg hij

theorem solToMatrix_a_diag {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).a i i =
      diagGcd x i * (solToMatrixCore (afterDiag x)).a i i := by
  simp [solToMatrix]

theorem solToMatrix_rowOffDiag_eq {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).rowOffDiag i =
      (solToMatrixCore (afterDiag x)).rowOffDiag i := by
  simp only [MatrixParam.rowOffDiag]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : j ≠ i := by
    have : j ∈ Finset.univ.erase i := hj
    exact Finset.ne_of_mem_erase this
  exact solToMatrix_a_off x i j hij.symm

theorem solToMatrix_colOffDiag_eq {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).colOffDiag i =
      (solToMatrixCore (afterDiag x)).colOffDiag i := by
  simp only [MatrixParam.colOffDiag]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by
    have : j ∈ Finset.univ.erase i := hj
    exact Finset.ne_of_mem_erase this
  exact solToMatrix_a_off x j i hji

theorem solToMatrix_diag_eq_gcd {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).a i i = diagGcd x i := by
  rw [solToMatrix_a_diag, solToMatrixCore_diag_eq_one_of_pairwise
      (afterDiag x) (afterDiag_pairwiseCoprime x) i, mul_one]

/-- PDF reconstruction: `n_i = ∏_j a_{ij}`. -/
theorem solToMatrix_rowProd {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).rowProd i = x.n i := by
  set p := solToMatrix x
  set c := solToMatrixCore (afterDiag x)
  have hcore : c.rowProd i = (afterDiag x).n i := solToMatrixCore_rowProd _ i
  calc
    p.rowProd i = p.a i i * p.rowOffDiag i := p.rowProd_eq_diag_mul_offDiag i
    _ = diagGcd x i * c.a i i * c.rowOffDiag i := by
          rw [solToMatrix_a_diag, solToMatrix_rowOffDiag_eq]
    _ = diagGcd x i * c.rowProd i := by
          rw [mul_assoc, ← c.rowProd_eq_diag_mul_offDiag i]
    _ = diagGcd x i * (x.n i / diagGcd x i) := by
          rw [hcore, afterDiag_n]
    _ = x.n i := Nat.mul_div_cancel' (diagGcd_dvd_n x i)

/-- PDF reconstruction: `m_i = ∏_k a_{ki}`. -/
theorem solToMatrix_colProd {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).colProd i = x.m i := by
  set p := solToMatrix x
  set c := solToMatrixCore (afterDiag x)
  have hcore : c.colProd i = (afterDiag x).m i := solToMatrixCore_colProd _ i
  calc
    p.colProd i = p.a i i * p.colOffDiag i := p.colProd_eq_diag_mul_offDiag i
    _ = diagGcd x i * c.a i i * c.colOffDiag i := by
          rw [solToMatrix_a_diag, solToMatrix_colOffDiag_eq]
    _ = diagGcd x i * c.colProd i := by
          rw [mul_assoc, ← c.colProd_eq_diag_mul_offDiag i]
    _ = diagGcd x i * (x.m i / diagGcd x i) := by
          rw [hcore, afterDiag_m]
    _ = x.m i := Nat.mul_div_cancel' (diagGcd_dvd_m x i)

theorem solToMatrix_a00 {s N : ℕ} (x : Sol s N) (hs : 1 ≤ s) :
    (solToMatrix x).a ⟨0, by omega⟩ ⟨0, by omega⟩ =
      Nat.gcd (x.n ⟨0, by omega⟩) (x.m ⟨0, by omega⟩) := by
  simpa [diagGcd] using solToMatrix_diag_eq_gcd x ⟨0, by omega⟩

/-- PDF condition (1) for every index. -/
theorem solToMatrix_coprime {s N : ℕ} (x : Sol s N) :
    (solToMatrix x).CoprimeOffDiag := by
  intro i
  simpa [MatrixParam.CoprimeOffDiag, solToMatrix_rowOffDiag_eq,
    solToMatrix_colOffDiag_eq] using
    solToMatrixCore_coprime_of_pairwise (afterDiag x) (afterDiag_pairwiseCoprime x) i

/-- Diagonal entry bound: `a_ii ≤ N/M_i` from `n_i,m_i ≤ N`. -/
theorem solToMatrix_diag_le_scale {s N : ℕ} (x : Sol s N) (i : Fin s) :
    (solToMatrix x).a i i ≤ N / (solToMatrix x).scale i := by
  set p := solToMatrix x
  set aii := p.a i i
  set A := p.rowOffDiag i
  set B := p.colOffDiag i
  set M := p.scale i
  have hn : aii * A = x.n i := by
    rw [← p.rowProd_eq_diag_mul_offDiag i, solToMatrix_rowProd]
  have hm : aii * B = x.m i := by
    rw [← p.colProd_eq_diag_mul_offDiag i, solToMatrix_colProd]
  have hMpos : 0 < M := p.scale_pos i
  have hle : aii * M ≤ N := by
    dsimp [M, MatrixParam.scale]
    cases le_total A B with
    | inl hAB =>
        rw [max_eq_right hAB, hm]; exact (x.hm i).2
    | inr hBA =>
        rw [max_eq_left hBA, hn]; exact (x.hn i).2
  exact (Nat.le_div_iff_mul_le hMpos).2 (mul_comm aii M ▸ hle)

theorem solToMatrix_head_fibre {s N H : ℕ} (x : Sol s N)
    (h0 : 0 < s) (hx : x ∈ VH s N H h0) :
    H < (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ ∧
      (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ ≤
        N / (solToMatrix x).scale ⟨0, h0⟩ := by
  refine ⟨?_, solToMatrix_diag_le_scale x ⟨0, h0⟩⟩
  have ha00 := solToMatrix_a00 x (by omega)
  have hgcd : H < Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) :=
    (mem_VH).1 hx
  rwa [ha00]

theorem solToMatrix_diag_fibre {s N : ℕ} (x : Sol s N)
    (i : Fin s) (h0 : 0 < s) (_hi : i ≠ ⟨0, h0⟩) :
    1 ≤ (solToMatrix x).a i i ∧
      (solToMatrix x).a i i ≤ N / (solToMatrix x).scale i := by
  refine ⟨?_, solToMatrix_diag_le_scale x i⟩
  exact Nat.succ_le_of_lt ((solToMatrix x).entries_pos i i)

theorem solToMatrix_injective {s N : ℕ} :
    Function.Injective (solToMatrix : Sol s N → MatrixParam s) := by
  intro x y hxy
  have hn : x.n = y.n := by
    funext i
    rw [← solToMatrix_rowProd x i, ← solToMatrix_rowProd y i, hxy]
  have hm : x.m = y.m := by
    funext i
    rw [← solToMatrix_colProd x i, ← solToMatrix_colProd y i, hxy]
  cases x; cases y
  simp_all

theorem solToMatrix_inj_on_VH {s N H : ℕ} (_h0 : 0 < s) :
    Set.InjOn (fun x : Sol s N => solToMatrix x)
      {x | x ∈ VH s N H _h0} := by
  intro x _ y _ hxy
  exact solToMatrix_injective hxy

/-! ### Fibre exactness (PDF: off-diagonals fixed + (1) ⇒ box) -/

theorem gcd_mul_of_coprime (d A B : ℕ) (hcop : Nat.gcd A B = 1) :
    Nat.gcd (d * A) (d * B) = d := by
  rw [Nat.gcd_mul_left, hcop, mul_one]

theorem MatrixParam.diag_le_scale_iff {s : ℕ} (p : MatrixParam s)
    (N : ℕ) (i : Fin s) (d : ℕ) :
    d * p.rowOffDiag i ≤ N ∧ d * p.colOffDiag i ≤ N ↔
      d ≤ N / p.scale i := by
  set A := p.rowOffDiag i
  set B := p.colOffDiag i
  set M := p.scale i
  have hMpos : 0 < M := p.scale_pos i
  constructor
  · intro ⟨hA, hB⟩
    have hle : d * M ≤ N := by
      dsimp [M, MatrixParam.scale]
      cases le_total A B with
      | inl hAB => rw [max_eq_right hAB]; exact hB
      | inr hBA => rw [max_eq_left hBA]; exact hA
    exact (Nat.le_div_iff_mul_le hMpos).2 (mul_comm d M ▸ hle)
  · intro h
    have hle : d * M ≤ N := (Nat.le_div_iff_mul_le hMpos).1 h
    dsimp [M, MatrixParam.scale] at hle
    constructor
    · exact le_trans (Nat.mul_le_mul_left d (le_max_left A B)) hle
    · exact le_trans (Nat.mul_le_mul_left d (le_max_right A B)) hle

/--
With off-diagonals fixed and condition (1), a positive diagonal value `d` at
index `i` recovers `gcd(d A_i, d B_i) = d`, and the bound `n_i,m_i ≤ N` is
exactly `d ≤ N/M_i`.
-/
theorem MatrixParam.offDiag_fibre_diag {s : ℕ} (p : MatrixParam s)
    (N : ℕ) (i : Fin s) (d : ℕ) (_hd : 0 < d)
    (hcop : Nat.gcd (p.rowOffDiag i) (p.colOffDiag i) = 1) :
    Nat.gcd (d * p.rowOffDiag i) (d * p.colOffDiag i) = d ∧
      (d * p.rowOffDiag i ≤ N ∧ d * p.colOffDiag i ≤ N ↔
        d ≤ N / p.scale i) :=
  ⟨gcd_mul_of_coprime d _ _ hcop, p.diag_le_scale_iff N i d⟩

/-! ### Package statement matching PDF Lemma 4 -/

/--
PDF Lemma 4 (`lem:param-general`).

Injection `φ : V_H →` positive matrices with row/col products, full
off-diagonal coprimality (1), and head fibre range (2). Diagonals are
`a_ii = gcd(n_i,m_i)`; off-diagonals come from the core factorisation of the
pairwise-coprime residuals. With off-diagonals fixed, (1) makes the diagonal
fibre exactly the integer box in (2) (`offDiag_fibre_diag`).
-/
theorem matrix_parametrisation (s N H : ℕ) (hs : 2 ≤ s) :
    ∃ φ : Sol s N → MatrixParam s,
      (∀ x ∈ VH s N H (by omega),
        (∀ i, (φ x).rowProd i = x.n i) ∧
          (∀ i, (φ x).colProd i = x.m i) ∧
          (φ x).CoprimeOffDiag ∧
          H < (φ x).a ⟨0, by omega⟩ ⟨0, by omega⟩ ∧
          (φ x).a ⟨0, by omega⟩ ⟨0, by omega⟩ ≤
            N / (φ x).scale ⟨0, by omega⟩) ∧
        Set.InjOn φ {x | x ∈ VH s N H (by omega)} := by
  refine ⟨solToMatrix, ?_, solToMatrix_inj_on_VH (by omega)⟩
  intro x hx
  refine ⟨?_, ?_, solToMatrix_coprime x, ?_⟩
  · intro i; exact solToMatrix_rowProd x i
  · intro i; exact solToMatrix_colProd x i
  · exact solToMatrix_head_fibre x (by omega) hx

end RMFLean
