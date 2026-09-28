/-
PDF Lemma 8 (`lem:intersection-param`) — intersection parametrisation.

Canonical successive-gcd representation of points in `⋂_{i∈I} ℱ_i`
(after reindexing so that `1 ∈ I`), and identification of the `b_s`-fibre.

Indexing: Lean `Fin s` uses `0` for PDF index `1`.
-/
import RMFLean.Trusted.Defs
import RMFLean.Proof.Setup.SolFinite
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

noncomputable section

open Classical

namespace RMFLean

/--
Outer parameters `ν` in PDF Lemma 8:
`(t₂,…,tₛ, n₁', m₁', n₂,…,nₛ, m₂',…,mₛ')`.
- `t ⟨0,_⟩` and `m' ⟨0,_⟩` are unused dummies
- `nTail` stores `n₂,…,nₛ` (`nTail ⟨0,_⟩` is an unused dummy, always `1`)
-/
@[ext]
structure IntersectionOuter (s : ℕ) where
  t : Fin s → ℕ
  n1' : ℕ
  m1' : ℕ
  nTail : Fin s → ℕ
  m' : Fin s → ℕ

/-- Product `T = t₂⋯tₛ`. -/
def IntersectionOuter.T {s : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s) : ℕ :=
  ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.t i

structure IntersectionCanon (s : ℕ) where
  b : ℕ
  outer : IntersectionOuter s

/--
Ordered recursion over Lean indices `1,…,s-1` (PDF `j=2,…,s`).
`intersectionRunFrom j b t` continues from index `j` with current gcd residue `b`.
-/
def intersectionRunFrom {s N : ℕ} (x : Sol s N) (h0 : 0 < s)
    (j : ℕ) (b : ℕ) (t : Fin s → ℕ) : ℕ × (Fin s → ℕ) :=
  if hj : j < s then
    if j = 0 then
      intersectionRunFrom (x := x) h0 (j + 1) b t
    else
      let jf : Fin s := ⟨j, hj⟩
      let tj := Nat.gcd b (x.m jf)
      intersectionRunFrom (x := x) h0 (j + 1) (b / tj) (Function.update t jf tj)
  else
    (b, t)
  termination_by s - j

def Sol.b1 {s N : ℕ} (x : Sol s N) (h0 : 0 < s) : ℕ :=
  Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩)

def Sol.toIntersectionCanon {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    IntersectionCanon s :=
  let b1 := x.b1 h0
  let final := intersectionRunFrom (x := x) h0 1 b1 (fun _ => 1)
  { b := final.1
    outer :=
      { t := final.2
        n1' := x.n ⟨0, h0⟩ / b1
        m1' := x.m ⟨0, h0⟩ / b1
        nTail := fun j => if j = ⟨0, h0⟩ then 1 else x.n j
        m' := fun j =>
          if j = ⟨0, h0⟩ then x.m ⟨0, h0⟩ / b1 else x.m j / final.2 j } }

def IntersectionCanon.reconN1 {s : ℕ} (c : IntersectionCanon s) (h0 : 0 < s) : ℕ :=
  c.b * c.outer.T h0 * c.outer.n1'

def IntersectionCanon.reconM1 {s : ℕ} (c : IntersectionCanon s) (h0 : 0 < s) : ℕ :=
  c.b * c.outer.T h0 * c.outer.m1'

def IntersectionCanon.reconM {s : ℕ} (c : IntersectionCanon s) (h0 : 0 < s)
    (j : Fin s) : ℕ :=
  if j = ⟨0, h0⟩ then c.reconM1 h0 else c.outer.t j * c.outer.m' j

def fibreG (s N A : ℕ) (ν : IntersectionOuter s) (h0 : 0 < s) : Finset ℕ :=
  let T := ν.T h0
  let M := max ν.n1' ν.m1'
  (Finset.Icc 1 N).filter fun b =>
    A ≤ b * T ∧ b * T * M ≤ N ∧
      ∀ j : Fin s, j ≠ ⟨0, h0⟩ → Nat.gcd b (ν.m' j) = 1

theorem toIntersectionCanon_n1'_m1'_coprime {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    Nat.gcd (x.toIntersectionCanon h0).outer.n1'
      (x.toIntersectionCanon h0).outer.m1' = 1 := by
  simp only [Sol.toIntersectionCanon, Sol.b1]
  have hpos : 0 < Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) :=
    Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
  exact (Nat.coprime_div_gcd_div_gcd hpos).gcd_eq_one

/-! ### Run invariants (PDF: `b₁ = b_s T`, and `t_j ∣ m_j`) -/

/-- Indices `i` with `j ≤ i.val`. -/
private def runTail (s j : ℕ) : Finset (Fin s) :=
  Finset.univ.filter fun i : Fin s => j ≤ i.val

/--
Inductive content of the PDF recursion `b_{j-1} = t_j b_j`:
starting at index `j ≥ 1` with residue `b` and map `t`, the completed run
satisfies
`b = b_final * ∏_{i : j ≤ ↑i} t_final(i)`, freezes `t` on `{i : ↑i < j}`,
and each newly written `t_i` divides `m_i`.
-/
theorem intersectionRunFrom_invariant {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    ∀ (n j : ℕ) (b : ℕ) (t : Fin s → ℕ),
      s - j = n → 0 < j →
        let final := intersectionRunFrom (x := x) h0 j b t
        let F := runTail s j
        b = final.1 * (∏ i ∈ F, final.2 i) ∧
          (∀ i : Fin s, i.val < j → final.2 i = t i) ∧
          (∀ i ∈ F, final.2 i ∣ x.m i) ∧
          (∀ i ∈ F, Nat.gcd final.1 (x.m i / final.2 i) = 1) ∧
          (∀ i ∈ F,
            Nat.gcd (final.1 * ∏ k ∈ F.filter fun k => i.val < k.val, final.2 k)
              (x.m i / final.2 i) = 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j b t hn hj
    unfold intersectionRunFrom
    split_ifs with hjlt hj0
    · exact (lt_irrefl 0 (hj0 ▸ hj)).elim
    · -- Recursive step at index `j` with `0 < j < s`.
      set jf : Fin s := ⟨j, hjlt⟩
      set tj := Nat.gcd b (x.m jf)
      set t' := Function.update t jf tj
      set b' := b / tj
      have hn' : s - (j + 1) < n := by
        have : s - (j + 1) < s - j := Nat.sub_succ_lt_self s j hjlt
        simpa [hn] using this
      have hrec := ih (s - (j + 1)) hn' (j + 1) b' t' rfl (Nat.succ_pos _)
      set final := intersectionRunFrom (x := x) h0 (j + 1) b' t'
      set F' : Finset (Fin s) := runTail s (j + 1)
      set F : Finset (Fin s) := runTail s j
      obtain ⟨hprod', hfreeze', hdvd', hcop', hstep'⟩ := hrec
      have htj_dvd_b : tj ∣ b := Nat.gcd_dvd_left _ _
      have hmul : b' * tj = b := Nat.div_mul_cancel htj_dvd_b
      have hF_split : F = insert jf F' := by
        ext i
        simp only [F, F', runTail, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
          true_and, jf]
        constructor
        · intro hij
          rcases Nat.eq_or_lt_of_le hij with hEq | hlt
          · left; exact Fin.ext hEq.symm
          · right; exact Nat.succ_le_of_lt hlt
        · rintro (rfl | hi')
          · exact Nat.le_refl _
          · exact Nat.le_of_succ_le hi'
      have hnotin : jf ∉ F' := by
        simp [F', runTail, jf]
      have hfreeze_jf : final.2 jf = tj := by
        have := hfreeze' jf (Nat.lt_succ_self j)
        simpa [t', Function.update_self] using this
      have hprodF :
          (∏ i ∈ F, final.2 i) = tj * (∏ i ∈ F', final.2 i) := by
        rw [hF_split, Finset.prod_insert hnotin, hfreeze_jf]
      have htjpos : 0 < tj :=
        Nat.gcd_pos_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one (x.hm jf).1)
      have hcop_step : Nat.Coprime b' (x.m jf / tj) :=
        Nat.coprime_div_gcd_div_gcd htjpos
      have hfinal_dvd_b' : final.1 ∣ b' := Dvd.intro _ hprod'.symm
      have hfilter_jf :
          F.filter (fun k : Fin s => jf.val < k.val) = F' := by
        ext k
        simp only [F, F', runTail, Finset.mem_filter, Finset.mem_univ, true_and, jf]
        constructor
        · intro ⟨_hk, hgt⟩
          exact Nat.succ_le_of_lt hgt
        · intro hk
          exact ⟨Nat.le_of_succ_le hk, Nat.lt_of_succ_le hk⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · calc
          b = b' * tj := hmul.symm
          _ = (final.1 * (∏ i ∈ F', final.2 i)) * tj := by rw [hprod']
          _ = final.1 * (∏ i ∈ F, final.2 i) := by
                rw [hprodF]; ring
      · intro i hi
        have hi' : i.val < j + 1 := Nat.lt_succ_of_lt hi
        have hne : i ≠ jf := by
          intro h; exact absurd (h ▸ hi) (lt_irrefl _)
        exact (hfreeze' i hi').trans (Function.update_of_ne hne tj t)
      · intro i hi
        rcases Finset.mem_insert.1 (by simpa [hF_split] using hi) with hEq | hi'
        · subst hEq
          simpa [hfreeze_jf] using Nat.gcd_dvd_right b (x.m jf)
        · exact hdvd' i hi'
      · intro i hi
        rcases Finset.mem_insert.1 (by simpa [hF_split] using hi) with hEq | hi'
        · subst hEq
          rw [hfreeze_jf]
          exact (hcop_step.coprime_dvd_left hfinal_dvd_b').gcd_eq_one
        · exact hcop' i hi'
      · intro i hi
        rcases Finset.mem_insert.1 (by simpa [hF_split] using hi) with hEq | hi'
        · subst hEq
          rw [hfreeze_jf, hfilter_jf]
          have : final.1 * (∏ k ∈ F', final.2 k) = b' := hprod'.symm
          simpa [this] using hcop_step.gcd_eq_one
        · have hfilter_i :
              F.filter (fun k : Fin s => i.val < k.val) =
                F'.filter (fun k : Fin s => i.val < k.val) := by
            ext k
            simp only [hF_split, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hmem, hgt⟩
              rcases hmem with hEqk | hk'
              · subst hEqk
                have hiF' : j + 1 ≤ i.val := by simpa [F', runTail] using hi'
                exact absurd hgt (not_lt.mpr (Nat.le_trans (Nat.le_succ j) hiF'))
              · exact ⟨hk', hgt⟩
            · rintro ⟨hk', hgt⟩
              exact ⟨Or.inr hk', hgt⟩
          rw [hfilter_i]; exact hstep' i hi'
    · -- Base: `¬ j < s`, so the remaining index set is empty.
      have hFempty : runTail s j = (∅ : Finset (Fin s)) := by
        simp only [runTail, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
        intro i hij
        exact hjlt (lt_of_le_of_lt hij i.isLt)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hFempty]; simp
      · intro i _hi; rfl
      · intro i hi
        simp [hFempty] at hi
      · intro i hi
        simp [hFempty] at hi
      · intro i hi
        simp [hFempty] at hi

/-- Starting the run at `j=1` with `b₁` yields `b₁ = b_s * T`. -/
theorem intersectionRunFrom_b1_eq_b_mul_T {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    let b1 := x.b1 h0
    let final := intersectionRunFrom (x := x) h0 1 b1 (fun _ => 1)
    b1 = final.1 * (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), final.2 i) := by
  have h :=
    intersectionRunFrom_invariant (x := x) h0 (s - 1) 1 (x.b1 h0) (fun _ => 1) rfl
      Nat.one_pos
  obtain ⟨hprod, _, _, _, _⟩ := h
  have hF : runTail s 1 = Finset.univ.erase (⟨0, h0⟩ : Fin s) := by
    ext i
    simp only [runTail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro h
      have : i.val = 0 := congrArg Fin.val h
      omega
    · intro ⟨hne, _⟩
      have : i.val ≠ 0 := by
        intro h0i
        exact hne (Fin.ext h0i)
      omega
  rw [← hF]
  exact hprod

/-- Each produced `t_j` (`j≠0`) divides `m_j`. -/
theorem intersectionRunFrom_t_dvd_m {s N : ℕ} (x : Sol s N) (h0 : 0 < s)
    (j : Fin s) (hj : j ≠ ⟨0, h0⟩) :
    let b1 := x.b1 h0
    let final := intersectionRunFrom (x := x) h0 1 b1 (fun _ => 1)
    final.2 j ∣ x.m j := by
  have h :=
    intersectionRunFrom_invariant (x := x) h0 (s - 1) 1 (x.b1 h0) (fun _ => 1) rfl
      Nat.one_pos
  obtain ⟨_, _, hdvd, _, _⟩ := h
  have hjpos : 1 ≤ j.val := by
    have : j.val ≠ 0 := by
      intro h0j
      exact hj (Fin.ext h0j)
    omega
  exact hdvd j (by simp [runTail, hjpos])

/-- Unfolded accessors. -/
theorem toIntersectionCanon_b {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).b =
      (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).1 := by
  simp [Sol.toIntersectionCanon]

theorem toIntersectionCanon_t {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).outer.t =
      (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 := by
  simp [Sol.toIntersectionCanon]

theorem toIntersectionCanon_T {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).outer.T h0 =
      ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
        (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 i := by
  simp [Sol.toIntersectionCanon, IntersectionOuter.T]

/-- PDF: `n₁ = b₁ n₁' = b_s T n₁'`. -/
theorem toIntersectionCanon_reconN1 (s N : ℕ) (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).reconN1 h0 = x.n ⟨0, h0⟩ := by
  have hbT := intersectionRunFrom_b1_eq_b_mul_T (x := x) h0
  have hdvd : x.b1 h0 ∣ x.n ⟨0, h0⟩ := Nat.gcd_dvd_left _ _
  have hmul := Nat.mul_div_cancel' hdvd
  simp only [IntersectionCanon.reconN1, Sol.toIntersectionCanon, IntersectionOuter.T,
    Sol.b1] at hbT ⊢
  change
      (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).1 *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 i) *
          (x.n ⟨0, h0⟩ / x.b1 h0) =
        x.n ⟨0, h0⟩
  have hbT' :
      x.b1 h0 =
        (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).1 *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 i) := by
    simpa [Sol.b1] using hbT
  rw [← hbT']
  exact hmul

/-- PDF: `m₁ = b₁ m₁' = b_s T m₁'`. -/
theorem toIntersectionCanon_reconM1 (s N : ℕ) (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).reconM1 h0 = x.m ⟨0, h0⟩ := by
  have hbT := intersectionRunFrom_b1_eq_b_mul_T (x := x) h0
  have hdvd : x.b1 h0 ∣ x.m ⟨0, h0⟩ := Nat.gcd_dvd_right _ _
  have hmul := Nat.mul_div_cancel' hdvd
  simp only [IntersectionCanon.reconM1, Sol.toIntersectionCanon, IntersectionOuter.T,
    Sol.b1] at hbT ⊢
  change
      (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).1 *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 i) *
          (x.m ⟨0, h0⟩ / x.b1 h0) =
        x.m ⟨0, h0⟩
  have hbT' :
      x.b1 h0 =
        (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).1 *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)).2 i) := by
    simpa [Sol.b1] using hbT
  rw [← hbT']
  exact hmul

/-- PDF: `m_j = t_j m_j'` for `j ≥ 2`. -/
theorem toIntersectionCanon_reconM_tail (s N : ℕ) (x : Sol s N) (h0 : 0 < s)
    (j : Fin s) (hj : j ≠ ⟨0, h0⟩) :
    (x.toIntersectionCanon h0).reconM h0 j = x.m j := by
  have ht_dvd := intersectionRunFrom_t_dvd_m (x := x) h0 j hj
  simp only [IntersectionCanon.reconM, hj, ↓reduceIte, Sol.toIntersectionCanon, Sol.b1]
  simp only [Sol.b1] at ht_dvd
  exact Nat.mul_div_cancel' ht_dvd

/-- PDF Lemma 8 reconstruction package. -/
theorem toIntersectionCanon_recon (s N : ℕ) (x : Sol s N) (h0 : 0 < s) :
    let c := x.toIntersectionCanon h0
    c.reconN1 h0 = x.n ⟨0, h0⟩ ∧
      c.reconM1 h0 = x.m ⟨0, h0⟩ ∧
      (∀ j : Fin s, j ≠ ⟨0, h0⟩ → c.reconM h0 j = x.m j) :=
  ⟨toIntersectionCanon_reconN1 s N x h0,
    toIntersectionCanon_reconM1 s N x h0,
    toIntersectionCanon_reconM_tail s N x h0⟩

/-- `b1 = b_s * T > 0`. -/
theorem toIntersectionCanon_b_mul_T_pos (s N : ℕ) (x : Sol s N) (h0 : 0 < s) :
    0 < (x.toIntersectionCanon h0).b * (x.toIntersectionCanon h0).outer.T h0 := by
  have hbT := intersectionRunFrom_b1_eq_b_mul_T (x := x) h0
  have hb1pos : 0 < x.b1 h0 :=
    Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
  have hbT' :
      x.b1 h0 =
        (x.toIntersectionCanon h0).b * (x.toIntersectionCanon h0).outer.T h0 := by
    simpa [Sol.toIntersectionCanon, IntersectionOuter.T, Sol.b1] using hbT
  rwa [← hbT']

/-- PDF: `gcd(b_s, m_j') = 1` for tail indices. -/
theorem toIntersectionCanon_bs_coprime_m' {s N : ℕ} (x : Sol s N) (h0 : 0 < s)
    (j : Fin s) (hj : j ≠ ⟨0, h0⟩) :
    Nat.gcd (x.toIntersectionCanon h0).b
      ((x.toIntersectionCanon h0).outer.m' j) = 1 := by
  have h :=
    intersectionRunFrom_invariant (x := x) h0 (s - 1) 1 (x.b1 h0) (fun _ => 1) rfl
      Nat.one_pos
  obtain ⟨_, _, _hdvd, hcop, _⟩ := h
  have hjpos : 1 ≤ j.val := by
    have : j.val ≠ 0 := fun h0j => hj (Fin.ext h0j)
    omega
  have hjF : j ∈ runTail s 1 := by simp [runTail, hjpos]
  have hcopj := hcop j hjF
  simp only [Sol.toIntersectionCanon, Sol.b1] at hcopj ⊢
  simp only [hj, ↓reduceIte]
  exact hcopj

/--
PDF outer product identity:
`n1' * prod_{j>=2} n_j = T * m1' * prod_{j>=2} m_j'`.
-/
theorem toIntersectionCanon_outer_product (s N : ℕ) (x : Sol s N) (h0 : 0 < s) :
    let c := x.toIntersectionCanon h0
    let E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
    c.outer.n1' * (∏ i ∈ E, c.outer.nTail i) =
      c.outer.T h0 * c.outer.m1' * (∏ i ∈ E, c.outer.m' i) := by
  set c := x.toIntersectionCanon h0
  set E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  set i0 : Fin s := ⟨0, h0⟩
  have hi0 : i0 ∈ Finset.univ := Finset.mem_univ _
  have hE : E = Finset.univ.erase i0 := by simp [E, i0]
  have hn0 : c.reconN1 h0 = x.n i0 := by
    simpa [c, i0] using toIntersectionCanon_reconN1 s N x h0
  have hm0 : c.reconM1 h0 = x.m i0 := by
    simpa [c, i0] using toIntersectionCanon_reconM1 s N x h0
  have hnTail : ∀ i ∈ E, c.outer.nTail i = x.n i := by
    intro i hi
    have hi0' : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
    simp [c, Sol.toIntersectionCanon, hi0']
  have hmFactor : ∀ i ∈ E, x.m i = c.outer.t i * c.outer.m' i := by
    intro i hi
    have hi0' : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
    have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0'
    have hform :
        (x.toIntersectionCanon h0).reconM h0 i =
          (x.toIntersectionCanon h0).outer.t i *
            (x.toIntersectionCanon h0).outer.m' i := by
      rw [IntersectionCanon.reconM, if_neg hi0']
    simpa [c] using hrecon.symm.trans hform
  have hprod_n :
      (∏ i, x.n i) =
        (∏ i ∈ Finset.univ.erase i0, x.n i) * x.n i0 :=
    (Finset.prod_erase_mul (s := Finset.univ) (a := i0) (f := x.n) hi0).symm
  have hprod_m :
      (∏ i, x.m i) =
        (∏ i ∈ Finset.univ.erase i0, x.m i) * x.m i0 :=
    (Finset.prod_erase_mul (s := Finset.univ) (a := i0) (f := x.m) hi0).symm
  have hN :
      (∏ i, x.n i) =
        (∏ i ∈ E, c.outer.nTail i) * (c.b * c.outer.T h0 * c.outer.n1') := by
    have hprodE :
        (∏ i ∈ E, c.outer.nTail i) = (∏ i ∈ Finset.univ.erase i0, x.n i) := by
      rw [hE]
      exact Finset.prod_congr rfl fun i hi => hnTail i (by simpa [hE] using hi)
    calc
      (∏ i, x.n i)
          = (∏ i ∈ Finset.univ.erase i0, x.n i) * x.n i0 := hprod_n
      _ = (∏ i ∈ E, c.outer.nTail i) * c.reconN1 h0 := by
            rw [← hprodE, hn0]
      _ = (∏ i ∈ E, c.outer.nTail i) * (c.b * c.outer.T h0 * c.outer.n1') := by
            simp [IntersectionCanon.reconN1]
  have hM :
      (∏ i, x.m i) =
        ((∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i)) *
          (c.b * c.outer.T h0 * c.outer.m1') := by
    have hmE :
        (∏ i ∈ E, x.m i) =
          (∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i) := by
      have := Finset.prod_congr rfl hmFactor
      simpa [Finset.prod_mul_distrib] using this
    calc
      (∏ i, x.m i)
          = (∏ i ∈ Finset.univ.erase i0, x.m i) * x.m i0 := hprod_m
      _ = (∏ i ∈ E, x.m i) * c.reconM1 h0 := by
            rw [← hE, hm0]
      _ = ((∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i)) *
            (c.b * c.outer.T h0 * c.outer.m1') := by
            simp [hmE, IntersectionCanon.reconM1]
  have hpos : 0 < c.b * c.outer.T h0 := toIntersectionCanon_b_mul_T_pos s N x h0
  have hEq1 :
      (∏ i ∈ E, c.outer.nTail i) * (c.b * c.outer.T h0 * c.outer.n1') =
        ((∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i)) *
          (c.b * c.outer.T h0 * c.outer.m1') := by
    rw [← hN, ← hM, x.hprod]
  have hEq2 :
      c.b * c.outer.T h0 *
          (c.outer.n1' * (∏ i ∈ E, c.outer.nTail i)) =
        c.b * c.outer.T h0 *
          (c.outer.T h0 * c.outer.m1' * (∏ i ∈ E, c.outer.m' i)) := by
    have hT : c.outer.T h0 = ∏ i ∈ E, c.outer.t i := rfl
    calc
      c.b * c.outer.T h0 * (c.outer.n1' * (∏ i ∈ E, c.outer.nTail i))
          = (∏ i ∈ E, c.outer.nTail i) * (c.b * c.outer.T h0 * c.outer.n1') := by
            ring
      _ = ((∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i)) *
            (c.b * c.outer.T h0 * c.outer.m1') := hEq1
      _ = c.b * c.outer.T h0 *
            (c.outer.T h0 * c.outer.m1' * (∏ i ∈ E, c.outer.m' i)) := by
            simp [hT]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hEq2

/-- Necessity: constructed `b_s` lies in `fibreG`. -/
theorem toIntersectionCanon_mem_fibreG (s N A : ℕ) (x : Sol s N) (h0 : 0 < s)
    (_hA : 1 ≤ A) (hmem0 : x.memF A ⟨0, h0⟩ h0) :
    (x.toIntersectionCanon h0).b ∈
      fibreG s N A (x.toIntersectionCanon h0).outer h0 := by
  set c := x.toIntersectionCanon h0
  set T := c.outer.T h0
  set M := max c.outer.n1' c.outer.m1'
  have hn0 := toIntersectionCanon_reconN1 s N x h0
  have hm0 := toIntersectionCanon_reconM1 s N x h0
  have hbT : x.b1 h0 = c.b * T := by
    simpa [c, T, Sol.toIntersectionCanon, IntersectionOuter.T, Sol.b1] using
      intersectionRunFrom_b1_eq_b_mul_T (x := x) h0
  have hAT : A ≤ c.b * T := by
    have : A ≤ x.b1 h0 := by simpa [Sol.memF, Sol.b1] using hmem0
    rwa [← hbT]
  have hn1_le : c.b * T * c.outer.n1' ≤ N := by
    have : c.b * T * c.outer.n1' = x.n ⟨0, h0⟩ := by
      simpa [IntersectionCanon.reconN1, T] using hn0
    exact this ▸ (x.hn ⟨0, h0⟩).2
  have hm1_le : c.b * T * c.outer.m1' ≤ N := by
    have : c.b * T * c.outer.m1' = x.m ⟨0, h0⟩ := by
      simpa [IntersectionCanon.reconM1, T] using hm0
    exact this ▸ (x.hm ⟨0, h0⟩).2
  have hM_le : c.b * T * M ≤ N := by
    cases le_total c.outer.n1' c.outer.m1' with
    | inl h =>
        have hM : M = c.outer.m1' := max_eq_right h
        simpa [hM] using hm1_le
    | inr h =>
        have hM : M = c.outer.n1' := max_eq_left h
        simpa [hM] using hn1_le
  have hposBT : 0 < c.b * T := by
    simpa [T] using toIntersectionCanon_b_mul_T_pos s N x h0
  have hbpos : 0 < c.b := by
    by_contra h
    simp [Nat.eq_zero_of_not_pos h] at hposBT
  have hTpos : 0 < T := by
    by_contra h
    simp [Nat.eq_zero_of_not_pos h] at hposBT
  have hb_le_N : c.b ≤ N := by
    have hb_le_b1 : c.b ≤ x.b1 h0 := by
      have : c.b ≤ c.b * T := Nat.le_mul_of_pos_right c.b hTpos
      rwa [← hbT] at this
    exact le_trans hb_le_b1 <|
      le_trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
        (Nat.gcd_dvd_left _ _)) (x.hn ⟨0, h0⟩).2
  refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hbpos, hb_le_N⟩, ?_⟩
  refine ⟨hAT, hM_le, ?_⟩
  intro j hj
  exact toIntersectionCanon_bs_coprime_m' (x := x) h0 j hj

/-- Canonical residue `b_{j-1} = b_s * ∏_{i : j ≤ ↑i} t_i`. -/
def IntersectionCanon.residue {s : ℕ} (c : IntersectionCanon s) (j : ℕ) : ℕ :=
  c.b * (∏ i ∈ runTail s j, c.outer.t i)

/--
If `gcd(bNext, m') = 1`, then `t = gcd(t * bNext, t * m')`.
Used for uniqueness of the successive-gcd factorisation.
-/
theorem nat_gcd_of_coprime_factor (t bNext m' : ℕ)
    (hcop : Nat.gcd bNext m' = 1) :
    t = Nat.gcd (t * bNext) (t * m') := by
  rw [Nat.gcd_mul_left, hcop, mul_one]

/--
First-column uniqueness: reconstruction of `(n₁, m₁)` with
`gcd(n₁', m₁') = 1` forces `b_s T = b₁` and recovers `(n₁', m₁')`.
-/
theorem intersection_param_unique_first_column (s N : ℕ) (h0 : 0 < s)
    (x : Sol s N) (c : IntersectionCanon s)
    (h1 : c.reconN1 h0 = x.n ⟨0, h0⟩)
    (hm1 : c.reconM1 h0 = x.m ⟨0, h0⟩)
    (hcop : Nat.gcd c.outer.n1' c.outer.m1' = 1) :
    c.b * c.outer.T h0 = x.b1 h0 ∧
      c.outer.n1' = x.n ⟨0, h0⟩ / x.b1 h0 ∧
      c.outer.m1' = x.m ⟨0, h0⟩ / x.b1 h0 := by
  have hn : x.n ⟨0, h0⟩ = c.b * c.outer.T h0 * c.outer.n1' := by
    simpa [IntersectionCanon.reconN1] using h1.symm
  have hm : x.m ⟨0, h0⟩ = c.b * c.outer.T h0 * c.outer.m1' := by
    simpa [IntersectionCanon.reconM1] using hm1.symm
  have hbT : c.b * c.outer.T h0 = x.b1 h0 := by
    have hgcd :
        x.b1 h0 =
          Nat.gcd (c.b * c.outer.T h0 * c.outer.n1')
            (c.b * c.outer.T h0 * c.outer.m1') := by
      simp [Sol.b1, hn, hm]
    have hmul :
        Nat.gcd (c.b * c.outer.T h0 * c.outer.n1')
            (c.b * c.outer.T h0 * c.outer.m1') =
          c.b * c.outer.T h0 * Nat.gcd c.outer.n1' c.outer.m1' := by
      simpa [mul_assoc] using
        (Nat.gcd_mul_left (c.b * c.outer.T h0) c.outer.n1' c.outer.m1')
    simp [hgcd, hmul, hcop, mul_one]
  have hpos : 0 < x.b1 h0 :=
    Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
  refine ⟨hbT, ?_, ?_⟩
  · have hn' : x.n ⟨0, h0⟩ = x.b1 h0 * c.outer.n1' := by
      rw [← hbT, hn, mul_assoc]
    have := Nat.mul_div_cancel_left c.outer.n1' hpos
    rw [← hn'] at this
    exact this.symm
  · have hm' : x.m ⟨0, h0⟩ = x.b1 h0 * c.outer.m1' := by
      rw [← hbT, hm, mul_assoc]
    have := Nat.mul_div_cancel_left c.outer.m1' hpos
    rw [← hm'] at this
    exact this.symm

theorem IntersectionCanon.residue_split {s : ℕ} (c : IntersectionCanon s)
    {j : ℕ} (hjlt : j < s) (_hjpos : 0 < j) :
    c.residue j = c.outer.t ⟨j, hjlt⟩ * c.residue (j + 1) := by
  set jf : Fin s := ⟨j, hjlt⟩
  simp only [IntersectionCanon.residue]
  have hsplit : runTail s j = insert jf (runTail s (j + 1)) := by
    ext i
    simp only [runTail, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, jf]
    constructor
    · intro hij
      rcases Nat.eq_or_lt_of_le hij with hEq | hlt
      · left; exact Fin.ext hEq.symm
      · right; exact Nat.succ_le_of_lt hlt
    · rintro (rfl | hi')
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le hi'
  have hnotin : jf ∉ runTail s (j + 1) := by simp [runTail, jf]
  rw [hsplit, Finset.prod_insert hnotin]
  ac_rfl

theorem nat_mul_pos_left_of_mul_eq {t m' m : ℕ} (heq : t * m' = m) (hm : 0 < m) :
    0 < t := by
  by_contra h
  have ht0 : t = 0 := Nat.eq_zero_of_not_pos h
  exact absurd (by simpa [ht0] using heq.symm) (ne_of_gt hm)

/--
Under step-coprimality, the successive-gcd run starting at residue `c.residue j`
recovers `(c.b, c.outer.t)`.
-/
theorem intersectionRunFrom_matches_canon {s N : ℕ} (x : Sol s N) (h0 : 0 < s)
    (c : IntersectionCanon s)
    (hm : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → c.outer.t j * c.outer.m' j = x.m j)
    (hstep : ∀ j : Fin s, j ≠ ⟨0, h0⟩ →
      Nat.gcd (c.residue (j.val + 1)) (c.outer.m' j) = 1)
    (_ht0 : c.outer.t ⟨0, h0⟩ = 1) :
    ∀ (n j : ℕ) (tMap : Fin s → ℕ),
      s - j = n → 0 < j →
        (∀ i : Fin s, i.val < j → tMap i = c.outer.t i) →
          let final := intersectionRunFrom (x := x) h0 j (c.residue j) tMap
          final.1 = c.b ∧
            (∀ i : Fin s, j ≤ i.val → final.2 i = c.outer.t i) ∧
            (∀ i : Fin s, i.val < j → final.2 i = tMap i) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j tMap hn hj ht_agree
    by_cases hjlt : j < s
    · by_cases hj0 : j = 0
      · exact (lt_irrefl 0 (hj0 ▸ hj)).elim
      · set jf : Fin s := ⟨j, hjlt⟩
        have hjne : jf ≠ ⟨0, h0⟩ := by
          intro h; exact hj0 (congrArg Fin.val h)
        have hbPrev := c.residue_split hjlt hj
        have hmJ : c.outer.t jf * c.outer.m' jf = x.m jf := hm jf hjne
        have hcopJ : Nat.gcd (c.residue (j + 1)) (c.outer.m' jf) = 1 :=
          hstep jf hjne
        have hgcd : Nat.gcd (c.residue j) (x.m jf) = c.outer.t jf := by
          have hfactor :=
            nat_gcd_of_coprime_factor (c.outer.t jf) (c.residue (j + 1))
              (c.outer.m' jf) hcopJ
          calc
            Nat.gcd (c.residue j) (x.m jf)
                = Nat.gcd (c.outer.t jf * c.residue (j + 1))
                    (c.outer.t jf * c.outer.m' jf) := by
                  rw [hbPrev, ← hmJ]
            _ = c.outer.t jf := hfactor.symm
        set tj := Nat.gcd (c.residue j) (x.m jf)
        set t' := Function.update tMap jf tj
        set b' := c.residue j / tj
        have htj_eq : tj = c.outer.t jf := hgcd
        have htpos : 0 < c.outer.t jf :=
          nat_mul_pos_left_of_mul_eq hmJ
            (lt_of_lt_of_le Nat.zero_lt_one (x.hm jf).1)
        have hb' : b' = c.residue (j + 1) := by
          simp only [b', htj_eq]
          rw [hbPrev, Nat.mul_div_cancel_left _ htpos]
        have ht'_agree : ∀ i : Fin s, i.val < j + 1 → t' i = c.outer.t i := by
          intro i hi
          by_cases hEq : i = jf
          · subst hEq; simp [t', Function.update_self, htj_eq]
          · have hi0 : i.val < j := by
              have : i.val ≠ j := fun hv => hEq (Fin.ext hv)
              omega
            simpa [t', Function.update_of_ne hEq] using ht_agree i hi0
        have hn' : s - (j + 1) < n := by
          have : s - (j + 1) < s - j := Nat.sub_succ_lt_self s j hjlt
          simpa [hn] using this
        have hrun :
            intersectionRunFrom (x := x) h0 j (c.residue j) tMap =
              intersectionRunFrom (x := x) h0 (j + 1) b' t' := by
          rw [intersectionRunFrom, dif_pos hjlt, if_neg hj0]
        have hrec :=
          ih (s - (j + 1)) hn' (j + 1) t' rfl (Nat.succ_pos _) ht'_agree
        have hrec' :
            let final := intersectionRunFrom (x := x) h0 (j + 1) b' t'
            final.1 = c.b ∧
              (∀ i : Fin s, j + 1 ≤ i.val → final.2 i = c.outer.t i) ∧
              (∀ i : Fin s, i.val < j + 1 → final.2 i = t' i) := by
          simpa [hb'] using hrec
        obtain ⟨hbF, ht_ge, ht_lt⟩ := hrec'
        rw [hrun]
        refine ⟨hbF, ?_, ?_⟩
        · intro i hi
          rcases Nat.eq_or_lt_of_le hi with hEq | hlt
          · have : i = jf := Fin.ext hEq.symm
            subst this
            have := ht_lt jf (Nat.lt_succ_self j)
            simpa [t', Function.update_self, htj_eq] using this
          · exact ht_ge i (Nat.succ_le_of_lt hlt)
        · intro i hi
          have hi' : i.val < j + 1 := Nat.lt_succ_of_lt hi
          have hne : i ≠ jf := fun h => absurd (h ▸ hi) (lt_irrefl _)
          exact (ht_lt i hi').trans (Function.update_of_ne hne tj tMap)
    · have hrun :
          intersectionRunFrom (x := x) h0 j (c.residue j) tMap =
            (c.residue j, tMap) := by
        rw [intersectionRunFrom, dif_neg hjlt]
      have hFempty : runTail s j = (∅ : Finset (Fin s)) := by
        simp only [runTail, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
        intro i hij
        exact hjlt (lt_of_le_of_lt hij i.isLt)
      have hres : c.residue j = c.b := by
        simp [IntersectionCanon.residue, hFempty]
      rw [hrun, hres]
      refine ⟨rfl, ?_, fun _ _ => rfl⟩
      · intro i hi
        exact False.elim (hjlt (lt_of_le_of_lt hi i.isLt))

/-- PDF Lemma 8 uniqueness (successive gcd extraction). -/
theorem intersection_param_unique (s N : ℕ) (h0 : 0 < s) (x : Sol s N)
    (c : IntersectionCanon s)
    (h1 : c.reconN1 h0 = x.n ⟨0, h0⟩)
    (hm : ∀ j, c.reconM h0 j = x.m j)
    (hcop : Nat.gcd c.outer.n1' c.outer.m1' = 1)
    (htail : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → c.outer.nTail j = x.n j)
    (hstep : ∀ j : Fin s, j ≠ ⟨0, h0⟩ →
      Nat.gcd (c.residue (j.val + 1)) (c.outer.m' j) = 1)
    (ht0 : c.outer.t ⟨0, h0⟩ = 1)
    (hn0' : c.outer.nTail ⟨0, h0⟩ = 1)
    (hm0' : c.outer.m' ⟨0, h0⟩ = c.outer.m1') :
    c = x.toIntersectionCanon h0 := by
  have hm1col : c.reconM1 h0 = x.m ⟨0, h0⟩ := by
    simpa [IntersectionCanon.reconM] using hm ⟨0, h0⟩
  obtain ⟨hbT, hn1', hm1'⟩ :=
    intersection_param_unique_first_column s N h0 x c h1 hm1col hcop
  have hm_tail : ∀ j : Fin s, j ≠ ⟨0, h0⟩ →
      c.outer.t j * c.outer.m' j = x.m j := by
    intro j hj
    simpa [IntersectionCanon.reconM, hj] using hm j
  have hF : runTail s 1 = Finset.univ.erase (⟨0, h0⟩ : Fin s) := by
    ext i
    simp only [runTail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro h; have : i.val = 0 := congrArg Fin.val h; omega
    · intro ⟨hne, _⟩
      have : i.val ≠ 0 := fun h0i => hne (Fin.ext h0i)
      omega
  have hres1 : c.residue 1 = x.b1 h0 := by
    simpa [IntersectionCanon.residue, IntersectionOuter.T, hF] using hbT
  have ht_agree0 :
      ∀ i : Fin s, i.val < 1 → (fun _ : Fin s => (1 : ℕ)) i = c.outer.t i := by
    intro i hi
    have hival : i.val = 0 := Nat.lt_one_iff.mp hi
    have : i = ⟨0, h0⟩ := Fin.ext hival
    simpa [this] using ht0.symm
  have hmatch :=
    intersectionRunFrom_matches_canon (x := x) h0 c hm_tail hstep ht0
      (s - 1) 1 (fun _ => 1) rfl Nat.one_pos ht_agree0
  have hmatch' :
      let final := intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)
      final.1 = c.b ∧
        (∀ i : Fin s, 1 ≤ i.val → final.2 i = c.outer.t i) ∧
        (∀ i : Fin s, i.val < 1 → final.2 i = (1 : ℕ)) := by
    simpa [hres1] using hmatch
  obtain ⟨hb, ht_ge, ht_lt⟩ := hmatch'
  set final := intersectionRunFrom (x := x) h0 1 (x.b1 h0) (fun _ => 1)
  have hb_eq : c.b = final.1 := hb.symm
  have ht_eq : c.outer.t = final.2 := by
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have h := ht_lt ⟨0, h0⟩ Nat.zero_lt_one
      simp [ht0, h, final]
    · have hi : 1 ≤ i.val := by
        have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        omega
      exact (ht_ge i hi).symm
  have hnTail_eq : c.outer.nTail = fun j =>
      if j = ⟨0, h0⟩ then 1 else x.n j := by
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0; simp [hn0']
    · simp [hi0, htail i hi0]
  have hm'_eq : c.outer.m' = fun j =>
      if j = ⟨0, h0⟩ then x.m ⟨0, h0⟩ / x.b1 h0 else x.m j / final.2 j := by
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      simp [hm0', hm1']
    · have hi : 1 ≤ i.val := by
        have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        omega
      have hmt := hm_tail i hi0
      have htpos :=
        nat_mul_pos_left_of_mul_eq hmt
          (lt_of_lt_of_le Nat.zero_lt_one (x.hm i).1)
      have hdiv : x.m i / c.outer.t i = c.outer.m' i := by
        rw [← hmt, Nat.mul_div_cancel_left _ htpos]
      simp only [hi0, ↓reduceIte]
      rw [ht_ge i hi]
      exact hdiv.symm
  -- Compare with the unfolded canonical construction.
  have hc :
      c =
        { b := final.1
          outer :=
            { t := final.2
              n1' := x.n ⟨0, h0⟩ / x.b1 h0
              m1' := x.m ⟨0, h0⟩ / x.b1 h0
              nTail := fun j => if j = ⟨0, h0⟩ then 1 else x.n j
              m' := fun j =>
                if j = ⟨0, h0⟩ then x.m ⟨0, h0⟩ / x.b1 h0
                else x.m j / final.2 j } } := by
    cases c with
    | mk _ outer =>
      cases outer with
      | mk _ _ _ _ _ =>
        simp only [IntersectionCanon.mk.injEq, IntersectionOuter.mk.injEq]
        exact ⟨hb_eq, ht_eq, hn1', hm1', hnTail_eq, hm'_eq⟩
  rw [hc]
  simp only [Sol.toIntersectionCanon]
  rfl

/-- Reconstruct `(n, m)` from outer parameters and a fibre value `b`. -/
def reconstructFromOuter (s : ℕ) (h0 : 0 < s) (ν : IntersectionOuter s) (b : ℕ) :
    (Fin s → ℕ) × (Fin s → ℕ) :=
  let T := ν.T h0
  (fun i => if i = ⟨0, h0⟩ then b * T * ν.n1' else ν.nTail i,
    fun i => if i = ⟨0, h0⟩ then b * T * ν.m1' else ν.t i * ν.m' i)

/-- Outer-product identity lifts to `∏ n = ∏ m` after reconstruction. -/
theorem reconstructFromOuter_prod (s : ℕ) (h0 : 0 < s)
    (ν : IntersectionOuter s) (b : ℕ)
    (hprod : ν.n1' * (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.nTail i) =
      ν.T h0 * ν.m1' * (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.m' i)) :
    let nm := reconstructFromOuter (s := s) h0 ν b
    (∏ i, nm.1 i) = (∏ i, nm.2 i) := by
  set E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  set i0 : Fin s := ⟨0, h0⟩
  set T := ν.T h0
  set n := (reconstructFromOuter (s := s) h0 ν b).1
  set m := (reconstructFromOuter (s := s) h0 ν b).2
  have hi0 : i0 ∈ Finset.univ := Finset.mem_univ _
  have hn0 : n i0 = b * T * ν.n1' := by
    simp [n, reconstructFromOuter, i0, T]
  have hm0 : m i0 = b * T * ν.m1' := by
    simp [m, reconstructFromOuter, i0, T]
  have hnE : ∀ i ∈ E, n i = ν.nTail i := by
    intro i hi
    have : i ≠ i0 := (Finset.mem_erase.1 hi).1
    simp [n, reconstructFromOuter, i0, this]
  have hmE : ∀ i ∈ E, m i = ν.t i * ν.m' i := by
    intro i hi
    have : i ≠ i0 := (Finset.mem_erase.1 hi).1
    simp [m, reconstructFromOuter, i0, this]
  have hTn :
      (∏ i, n i) = (∏ i ∈ E, ν.nTail i) * (b * T * ν.n1') := by
    have h := (Finset.prod_erase_mul (s := Finset.univ) (a := i0) (f := n) hi0).symm
    have hEprod : (∏ i ∈ E, n i) = (∏ i ∈ E, ν.nTail i) :=
      Finset.prod_congr rfl hnE
    calc
      (∏ i, n i) = (∏ i ∈ Finset.univ.erase i0, n i) * n i0 := h
      _ = (∏ i ∈ E, n i) * (b * T * ν.n1') := by
            rw [show Finset.univ.erase i0 = E from rfl, hn0]
      _ = (∏ i ∈ E, ν.nTail i) * (b * T * ν.n1') := by rw [hEprod]
  have hTm :
      (∏ i, m i) =
        (∏ i ∈ E, ν.t i) * (∏ i ∈ E, ν.m' i) * (b * T * ν.m1') := by
    have h := (Finset.prod_erase_mul (s := Finset.univ) (a := i0) (f := m) hi0).symm
    have hEprod : (∏ i ∈ E, m i) = (∏ i ∈ E, ν.t i * ν.m' i) :=
      Finset.prod_congr rfl hmE
    have hmul := Finset.prod_mul_distrib (s := E) (f := ν.t) (g := ν.m')
    calc
      (∏ i, m i) = (∏ i ∈ Finset.univ.erase i0, m i) * m i0 := h
      _ = (∏ i ∈ E, m i) * (b * T * ν.m1') := by
            rw [show Finset.univ.erase i0 = E from rfl, hm0]
      _ = (∏ i ∈ E, ν.t i * ν.m' i) * (b * T * ν.m1') := by rw [hEprod]
      _ = (∏ i ∈ E, ν.t i) * (∏ i ∈ E, ν.m' i) * (b * T * ν.m1') := by
            rw [hmul]
  have hTdef : T = ∏ i ∈ E, ν.t i := by simp [T, E, IntersectionOuter.T]
  calc
    (∏ i, n i) = (∏ i ∈ E, ν.nTail i) * (b * T * ν.n1') := hTn
    _ = b * T * (ν.n1' * (∏ i ∈ E, ν.nTail i)) := by ring
    _ = b * T * (T * ν.m1' * (∏ i ∈ E, ν.m' i)) := by rw [hprod]
    _ = (∏ i ∈ E, ν.t i) * (∏ i ∈ E, ν.m' i) * (b * T * ν.m1') := by
          simp [hTdef]; ring
    _ = (∏ i, m i) := hTm.symm

/-! ### Fibre converse helpers -/

theorem toIntersectionCanon_t0 {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).outer.t ⟨0, h0⟩ = 1 := by
  have h :=
    intersectionRunFrom_invariant (x := x) h0 (s - 1) 1 (x.b1 h0) (fun _ => 1) rfl
      Nat.one_pos
  obtain ⟨_, hfreeze, _, _, _⟩ := h
  simpa [Sol.toIntersectionCanon] using hfreeze ⟨0, h0⟩ Nat.zero_lt_one

theorem toIntersectionCanon_nTail0 {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).outer.nTail ⟨0, h0⟩ = 1 := by
  simp [Sol.toIntersectionCanon]

theorem toIntersectionCanon_m0' {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).outer.m' ⟨0, h0⟩ =
      (x.toIntersectionCanon h0).outer.m1' := by
  simp [Sol.toIntersectionCanon]

theorem toIntersectionCanon_residue1 {s N : ℕ} (x : Sol s N) (h0 : 0 < s) :
    (x.toIntersectionCanon h0).residue 1 = x.b1 h0 := by
  have hF : runTail s 1 = Finset.univ.erase (⟨0, h0⟩ : Fin s) := by
    ext i
    simp only [runTail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro h; have : i.val = 0 := congrArg Fin.val h; omega
    · intro ⟨hne, _⟩
      have : i.val ≠ 0 := fun h0i => hne (Fin.ext h0i)
      omega
  have hbT := intersectionRunFrom_b1_eq_b_mul_T (x := x) h0
  simpa [IntersectionCanon.residue, IntersectionOuter.T, Sol.toIntersectionCanon, hF, Sol.b1]
    using hbT.symm

/-- PDF: `gcd(b_j, m_j') = 1` with `b_j = residue (j+1)`. -/
theorem toIntersectionCanon_step_coprime {s N : ℕ} (x : Sol s N) (h0 : 0 < s)
    (j : Fin s) (hj : j ≠ ⟨0, h0⟩) :
    Nat.gcd ((x.toIntersectionCanon h0).residue (j.val + 1))
      ((x.toIntersectionCanon h0).outer.m' j) = 1 := by
  have h :=
    intersectionRunFrom_invariant (x := x) h0 (s - 1) 1 (x.b1 h0) (fun _ => 1) rfl
      Nat.one_pos
  obtain ⟨_, _, _, _, hstep⟩ := h
  have hjpos : 1 ≤ j.val := by
    have : j.val ≠ 0 := fun h0j => hj (Fin.ext h0j)
    omega
  have hjF : j ∈ runTail s 1 := by simp [runTail, hjpos]
  have hfilter :
      (runTail s 1).filter (fun k : Fin s => j.val < k.val) = runTail s (j.val + 1) := by
    ext k
    simp only [runTail, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨_hk, hgt⟩
      exact Nat.succ_le_of_lt hgt
    · intro hk
      exact ⟨Nat.le_trans (by omega : 1 ≤ j.val + 1) hk, Nat.lt_of_succ_le hk⟩
  have hstepj := hstep j hjF
  rw [hfilter] at hstepj
  simpa [IntersectionCanon.residue, Sol.toIntersectionCanon, hj] using hstepj

/--
PDF fibre gcd identity: if `gcd(b, m') = 1` and `t ∣ T`, then
`gcd(b · T · n1', t · m') = gcd(T · n1', t · m')`.
-/
theorem gcd_fibre_independent (b T n1' t m' : ℕ)
    (hcop : Nat.gcd b m' = 1) (ht : t ∣ T) :
    Nat.gcd (b * T * n1') (t * m') = Nat.gcd (T * n1') (t * m') := by
  have htU : t ∣ T * n1' := dvd_mul_of_dvd_left ht n1'
  obtain ⟨U', hU'⟩ := htU
  have hcop' : Nat.Coprime b m' := hcop
  calc
    Nat.gcd (b * T * n1') (t * m')
        = Nat.gcd (b * (t * U')) (t * m') := by rw [mul_assoc, ← hU']
    _ = Nat.gcd (t * (b * U')) (t * m') := by
          simp [mul_left_comm b]
    _ = t * Nat.gcd (b * U') m' := by rw [Nat.gcd_mul_left]
    _ = t * Nat.gcd U' m' := by rw [hcop'.gcd_mul_left_cancel U']
    _ = Nat.gcd (t * U') (t * m') := by rw [← Nat.gcd_mul_left]
    _ = Nat.gcd (T * n1') (t * m') := by rw [hU']

/--
PDF fibre converse: varying `b` in `fibreG` preserves membership in every `F_i`.
-/
theorem intersection_param_fibre_converse (s N A : ℕ) (I : Finset (Fin s))
    (h0 : 0 < s) (_ : (⟨0, h0⟩ : Fin s) ∈ I) (_ : 2 ≤ I.card)
    (x : Sol s N) (hx : ∀ i ∈ I, x.memF A i h0)
    (b : ℕ) (hb : b ∈ fibreG s N A (x.toIntersectionCanon h0).outer h0) :
    ∃ y : Sol s N,
      y.toIntersectionCanon h0 =
        { b := b, outer := (x.toIntersectionCanon h0).outer } ∧
      (∀ i ∈ I, y.memF A i h0) := by
  set cₓ := x.toIntersectionCanon h0
  set ν := cₓ.outer
  set T := ν.T h0
  set M := max ν.n1' ν.m1'
  have hbF : b ∈ Finset.Icc 1 N ∧
      A ≤ b * T ∧ b * T * M ≤ N ∧
        ∀ j : Fin s, j ≠ ⟨0, h0⟩ → Nat.gcd b (ν.m' j) = 1 := by
    simpa [fibreG, T, M, ν, cₓ] using Finset.mem_filter.1 hb
  obtain ⟨hbIcc, hAT, hNM, hbcop⟩ := hbF
  have hbpos : 1 ≤ b := (Finset.mem_Icc.1 hbIcc).1
  have hprodν := toIntersectionCanon_outer_product s N x h0
  set nm := reconstructFromOuter (s := s) h0 ν b
  set n := nm.1
  set m := nm.2
  have hn0 : n ⟨0, h0⟩ = b * T * ν.n1' := by simp [n, nm, reconstructFromOuter, T]
  have hm0 : m ⟨0, h0⟩ = b * T * ν.m1' := by simp [m, nm, reconstructFromOuter, T]
  have hn_tail : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → n j = ν.nTail j := by
    intro j hj; simp [n, nm, reconstructFromOuter, hj]
  have hm_tail : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → m j = ν.t j * ν.m' j := by
    intro j hj; simp [m, nm, reconstructFromOuter, hj]
  have hn_tail_x : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → n j = x.n j := by
    intro j hj
    have : ν.nTail j = x.n j := by simp [ν, cₓ, Sol.toIntersectionCanon, hj]
    exact (hn_tail j hj).trans this
  have hm_tail_x : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → m j = x.m j := by
    intro j hj
    have hrecon := toIntersectionCanon_reconM_tail s N x h0 j hj
    have : ν.t j * ν.m' j = x.m j := by
      simpa [IntersectionCanon.reconM, hj, ν, cₓ] using hrecon
    exact (hm_tail j hj).trans this
  -- positivity / bounds for reconstructed coordinates
  have hn1'pos : 0 < ν.n1' := by
    have hdiv : ν.n1' = x.n ⟨0, h0⟩ / x.b1 h0 := by simp [ν, cₓ, Sol.toIntersectionCanon]
    have hb1pos : 0 < x.b1 h0 :=
      Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
    have hle : x.b1 h0 ≤ x.n ⟨0, h0⟩ :=
      Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
        (Nat.gcd_dvd_left _ _)
    have : 0 < x.n ⟨0, h0⟩ / x.b1 h0 := Nat.div_pos hle hb1pos
    simpa [hdiv] using this
  have hm1'pos : 0 < ν.m1' := by
    have hdiv : ν.m1' = x.m ⟨0, h0⟩ / x.b1 h0 := by simp [ν, cₓ, Sol.toIntersectionCanon]
    have hb1pos : 0 < x.b1 h0 :=
      Nat.gcd_pos_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1)
    have hle : x.b1 h0 ≤ x.m ⟨0, h0⟩ :=
      Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hm ⟨0, h0⟩).1)
        (Nat.gcd_dvd_right _ _)
    have : 0 < x.m ⟨0, h0⟩ / x.b1 h0 := Nat.div_pos hle hb1pos
    simpa [hdiv] using this
  have hTpos : 0 < T := by
    have hpos : 0 < cₓ.b * T := by simpa [cₓ, T, ν] using
      toIntersectionCanon_b_mul_T_pos s N x h0
    by_contra h
    simp [Nat.eq_zero_of_not_pos h] at hpos
  have hn_bounds : ∀ i, 1 ≤ n i ∧ n i ≤ N := by
    intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have hle : b * T * ν.n1' ≤ N :=
        calc
          b * T * ν.n1' ≤ b * T * M :=
            Nat.mul_le_mul_left _ (le_max_left _ _)
          _ ≤ N := hNM
      have hge : 1 ≤ b * T * ν.n1' := by
        have : 0 < b * T * ν.n1' :=
          Nat.mul_pos (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hbpos) hTpos) hn1'pos
        exact Nat.succ_le_of_lt this
      simpa [hn0] using And.intro hge hle
    · have := x.hn i
      simpa [hn_tail_x i hi0] using this
  have hm_bounds : ∀ i, 1 ≤ m i ∧ m i ≤ N := by
    intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have hle : b * T * ν.m1' ≤ N :=
        calc
          b * T * ν.m1' ≤ b * T * M :=
            Nat.mul_le_mul_left _ (le_max_right _ _)
          _ ≤ N := hNM
      have hge : 1 ≤ b * T * ν.m1' := by
        have : 0 < b * T * ν.m1' :=
          Nat.mul_pos (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hbpos) hTpos) hm1'pos
        exact Nat.succ_le_of_lt this
      simpa [hm0] using And.intro hge hle
    · have := x.hm i
      simpa [hm_tail_x i hi0] using this
  have hprod_nm : (∏ i, n i) = (∏ i, m i) := by
    simpa [n, m, nm] using
      reconstructFromOuter_prod (s := s) h0 ν b (by simpa [ν, cₓ] using hprodν)
  let y : Sol s N := ⟨n, m, hn_bounds, hm_bounds, hprod_nm⟩
  refine ⟨y, ?_, ?_⟩
  · -- canonical recovery via uniqueness
    set c : IntersectionCanon s := { b := b, outer := ν }
    have h1 : c.reconN1 h0 = y.n ⟨0, h0⟩ := by
      simp [c, IntersectionCanon.reconN1, y, hn0, T, ν]
    have hm : ∀ j, c.reconM h0 j = y.m j := by
      intro j
      by_cases hj0 : j = ⟨0, h0⟩
      · subst hj0
        simp [c, IntersectionCanon.reconM, IntersectionCanon.reconM1, y, hm0, T, ν]
      · simp [c, IntersectionCanon.reconM, hj0, y, hm_tail j hj0]
    have hcop : Nat.gcd c.outer.n1' c.outer.m1' = 1 :=
      toIntersectionCanon_n1'_m1'_coprime x h0
    have htail : ∀ j : Fin s, j ≠ ⟨0, h0⟩ → c.outer.nTail j = y.n j := by
      intro j hj
      simp [c, y, hn_tail j hj]
    have ht0 : c.outer.t ⟨0, h0⟩ = 1 := toIntersectionCanon_t0 x h0
    have hn0' : c.outer.nTail ⟨0, h0⟩ = 1 := toIntersectionCanon_nTail0 x h0
    have hm0' : c.outer.m' ⟨0, h0⟩ = c.outer.m1' := toIntersectionCanon_m0' x h0
    have hstep : ∀ j : Fin s, j ≠ ⟨0, h0⟩ →
        Nat.gcd (c.residue (j.val + 1)) (c.outer.m' j) = 1 := by
      intro j hj
      have horig := toIntersectionCanon_step_coprime (x := x) h0 j hj
      have hcopb : Nat.gcd b (ν.m' j) = 1 := hbcop j hj
      -- residue = b * ∏_{i ≥ j+1} t_i, and original gives gcd(bₓ * ∏, m') = 1
      -- hence gcd(∏, m') = 1; combine with gcd(b, m') = 1
      have hprod_tail :
          c.residue (j.val + 1) =
            b * (∏ i ∈ runTail s (j.val + 1), ν.t i) := by
        simp [c, IntersectionCanon.residue, ν]
      have horig' :
          Nat.gcd (cₓ.residue (j.val + 1)) (ν.m' j) = 1 := by
        simpa [cₓ, ν] using horig
      have hresₓ :
          cₓ.residue (j.val + 1) =
            cₓ.b * (∏ i ∈ runTail s (j.val + 1), ν.t i) := by
        simp [IntersectionCanon.residue, ν, cₓ]
      have hcop_prod :
          Nat.gcd (∏ i ∈ runTail s (j.val + 1), ν.t i) (ν.m' j) = 1 := by
        -- gcd(bₓ * P, m') = 1 ⇒ gcd(P, m') = 1
        have : Nat.Coprime (cₓ.b * (∏ i ∈ runTail s (j.val + 1), ν.t i))
            (ν.m' j) := by
          simpa [hresₓ] using horig'
        exact (Nat.coprime_mul_iff_left.mp this).2.gcd_eq_one
      have : Nat.Coprime
          (b * (∏ i ∈ runTail s (j.val + 1), ν.t i)) (ν.m' j) :=
        Nat.coprime_mul_iff_left.mpr ⟨hcopb, hcop_prod⟩
      simpa [hprod_tail, c, ν] using this.gcd_eq_one
    have huniq :=
      intersection_param_unique s N h0 y c h1 hm hcop htail hstep ht0 hn0' hm0'
    -- `huniq : c = y.toIntersectionCanon`, and `c = {b, ν} = {b, cₓ.outer}`
    simpa [c, ν, cₓ] using huniq.symm
  · -- membership in every `F_i`
    intro i hi
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      -- `memF` at 0: `A ≤ gcd(n₀, m₀) = b T`
      have hcop : Nat.gcd ν.n1' ν.m1' = 1 :=
        toIntersectionCanon_n1'_m1'_coprime x h0
      have hgcd :
          Nat.gcd (y.n ⟨0, h0⟩) (y.m ⟨0, h0⟩) = b * T := by
        simp only [y, hn0, hm0]
        have := Nat.gcd_mul_left (b * T) ν.n1' ν.m1'
        simpa [mul_assoc, hcop, mul_one] using this
      have : A ≤ Nat.gcd (y.n ⟨0, h0⟩) (y.m ⟨0, h0⟩) := by
        simpa [hgcd] using hAT
      simpa [Sol.memF] using this
    · -- `i ≠ 0`: gcd independent of fibre variable `b`
      have hmemx : A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m i) := by
        simpa [Sol.memF] using hx i hi
      have ht_dvd : ν.t i ∣ T := by
        have hiE : i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s) := by
          exact Finset.mem_erase.2 ⟨hi0, Finset.mem_univ _⟩
        exact Finset.dvd_prod_of_mem ν.t hiE
      have hcopb : Nat.gcd b (ν.m' i) = 1 := hbcop i hi0
      have hgx :
          Nat.gcd (x.n ⟨0, h0⟩) (x.m i) = Nat.gcd (T * ν.n1') (ν.t i * ν.m' i) := by
        have hnₓ : x.n ⟨0, h0⟩ = cₓ.b * T * ν.n1' := by
          simpa [IntersectionCanon.reconN1, T, ν, cₓ] using
            (toIntersectionCanon_reconN1 s N x h0).symm
        have hmₓ : x.m i = ν.t i * ν.m' i :=
          (hm_tail_x i hi0).symm.trans (hm_tail i hi0)
        have hcopₓ : Nat.gcd cₓ.b (ν.m' i) = 1 :=
          toIntersectionCanon_bs_coprime_m' (x := x) h0 i hi0
        rw [hnₓ, hmₓ]
        exact gcd_fibre_independent cₓ.b T ν.n1' (ν.t i) (ν.m' i) hcopₓ ht_dvd
      have hgy :
          Nat.gcd (y.n ⟨0, h0⟩) (y.m i) = Nat.gcd (T * ν.n1') (ν.t i * ν.m' i) := by
        have hmᵢ : y.m i = ν.t i * ν.m' i := by simpa [y] using hm_tail i hi0
        rw [show y.n ⟨0, h0⟩ = b * T * ν.n1' from by simpa [y] using hn0, hmᵢ]
        exact gcd_fibre_independent b T ν.n1' (ν.t i) (ν.m' i) hcopb ht_dvd
      have : A ≤ Nat.gcd (y.n ⟨0, h0⟩) (y.m i) := by
        rwa [hgy, ← hgx]
      simpa [Sol.memF] using this

/--
PDF Lemma 8 packaged: reconstruction, uniqueness, fibre necessity and converse.
-/
theorem intersection_parametrisation (s N A : ℕ) (I : Finset (Fin s))
    (hs : 2 ≤ s) (hA : 1 ≤ A)
    (hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) :
    ∀ x : Sol s N,
      (∀ i ∈ I, x.memF A i (by omega)) →
        let c := x.toIntersectionCanon (by omega)
        let E := Finset.univ.erase (⟨0, by omega⟩ : Fin s)
        -- reconstruction / outer identities
        Nat.gcd c.outer.n1' c.outer.m1' = 1 ∧
          c.reconN1 (by omega) = x.n ⟨0, by omega⟩ ∧
          c.reconM1 (by omega) = x.m ⟨0, by omega⟩ ∧
          (∀ j : Fin s, j ≠ ⟨0, by omega⟩ → c.reconM (by omega) j = x.m j) ∧
          c.outer.n1' * (∏ i ∈ E, c.outer.nTail i) =
            c.outer.T (by omega) * c.outer.m1' * (∏ i ∈ E, c.outer.m' i) ∧
          -- fibre necessity
          c.b ∈ fibreG s N A c.outer (by omega) ∧
          -- uniqueness of successive-gcd representation
          (∀ c' : IntersectionCanon s,
            c'.reconN1 (by omega) = x.n ⟨0, by omega⟩ →
              (∀ j, c'.reconM (by omega) j = x.m j) →
                Nat.gcd c'.outer.n1' c'.outer.m1' = 1 →
                  (∀ j : Fin s, j ≠ ⟨0, by omega⟩ → c'.outer.nTail j = x.n j) →
                    (∀ j : Fin s, j ≠ ⟨0, by omega⟩ →
                      Nat.gcd (c'.residue (j.val + 1)) (c'.outer.m' j) = 1) →
                      c'.outer.t ⟨0, by omega⟩ = 1 →
                        c'.outer.nTail ⟨0, by omega⟩ = 1 →
                          c'.outer.m' ⟨0, by omega⟩ = c'.outer.m1' →
                            c' = c) ∧
          -- fibre converse
          (∀ b ∈ fibreG s N A c.outer (by omega),
            ∃ y : Sol s N,
              y.toIntersectionCanon (by omega) = { b := b, outer := c.outer } ∧
                ∀ i ∈ I, y.memF A i (by omega)) := by
  intro x hx
  have h0 : 0 < s := by omega
  have hmem0 : x.memF A ⟨0, h0⟩ h0 := hx ⟨0, h0⟩ hI0
  refine ⟨toIntersectionCanon_n1'_m1'_coprime x h0, ?_⟩
  refine ⟨toIntersectionCanon_reconN1 s N x h0, ?_⟩
  refine ⟨toIntersectionCanon_reconM1 s N x h0, ?_⟩
  refine ⟨toIntersectionCanon_reconM_tail s N x h0, ?_⟩
  refine ⟨toIntersectionCanon_outer_product s N x h0, ?_⟩
  refine ⟨toIntersectionCanon_mem_fibreG s N A x h0 hA hmem0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro c' h1 hm hcop htail hstep ht0 hn0' hm0'
    exact intersection_param_unique s N h0 x c' h1 hm hcop htail hstep ht0 hn0' hm0'
  · intro b hb
    exact intersection_param_fibre_converse s N A I h0 hI0 hIcard x hx b hb

/-- Box of fibre values without the coprimality constraints (PDF `ℬ(ν)`). -/
def fibreB (s N A : ℕ) (ν : IntersectionOuter s) (h0 : 0 < s) : Finset ℕ :=
  let T := ν.T h0
  let M := max ν.n1' ν.m1'
  (Finset.Icc 1 N).filter fun b => A ≤ b * T ∧ b * T * M ≤ N

theorem fibreG_subset_fibreB (s N A : ℕ) (ν : IntersectionOuter s) (h0 : 0 < s) :
    fibreG s N A ν h0 ⊆ fibreB s N A ν h0 := by
  intro b hb
  simp only [fibreG, fibreB, Finset.mem_filter] at hb ⊢
  exact ⟨hb.1, hb.2.1, hb.2.2.1⟩

end RMFLean
