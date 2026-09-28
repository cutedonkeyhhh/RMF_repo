/-
Piece III scaled `J1` bridge (PDF `eq:piece-III-matrix` / `eq:piece-III-fixed`).

Architecture:
1. matrix embedding `ScaledBlock → J1ScaledSumAtHeight` (proved);
2. scaled Lemma 6 on that sum:
   - `J1_lem5_exceptional_sets_scaled` (lem:diophantine-nil on `g_h`);
   - theorems `PieceIII_sigma_I/II_scaled_bound` (row-factor / matrixFun)
     + side sums → `J1_scaled_sum_from_exceptional`;
   - assembled as theorem `J1_bound_scaled_height` (`∃ Cd, ∀ s, ∃ C`).
-/
import RMFLean.Proof.Intersection.I1PieceIIIComb
import RMFLean.Proof.Intersection.I1PieceIIIDio
import RMFLean.Proof.Intersection.I1PieceIIIScaledLem5
import RMFLean.Proof.F1.J1
import RMFLean.Proof.F1.J1LongShort
import RMFLean.Proof.F1.J1SigmaII
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex Real

namespace RMFLean

/-! ### Phase / range bridge (`I1BoxSum` ↔ scaled `g_h` head sum) -/

theorem I1FibrePhase_eq_compMul {d s : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) (D k : ℕ) :
    I1FibrePhase g h0 ν (D * k) =
      (g.compMul (D * ν.T h0)).ePhase (k * ν.n1') *
        starRingEnd ℂ ((g.compMul (D * ν.T h0)).ePhase (k * ν.m1')) := by
  simp only [I1FibrePhase, CirclePoly.ePhase_compMul]
  have h1 : D * k * ν.T h0 * ν.n1' = D * ν.T h0 * (k * ν.n1') := by ring
  have h2 : D * k * ν.T h0 * ν.m1' = D * ν.T h0 * (k * ν.m1') := by ring
  simp [h1, h2]

/--
`e * k ∈ fibreB` is the PDF scaled head condition at height `h = e T`,
up to the ambient `k ∈ [1,N]` cut.
-/
theorem mem_fibreB_mul_iff {s N A : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s)
    (e k : ℕ) :
    e * k ∈ fibreB s N A ν h0 ↔
      e * k ∈ Finset.Icc 1 N ∧
        A ≤ e * k * ν.T h0 ∧
          e * k * ν.T h0 * max ν.n1' ν.m1' ≤ N := by
  simp only [fibreB, Finset.mem_filter]

theorem I1BoxSum_eq_sum_compMul {d s N A : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) (e : ℕ) :
    I1BoxSum g N A h0 ν e =
      ∑ k ∈ (Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0,
        (g.compMul (e * ν.T h0)).ePhase (k * ν.n1') *
          starRingEnd ℂ
            ((g.compMul (e * ν.T h0)).ePhase (k * ν.m1')) := by
  simp only [I1BoxSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa using I1FibrePhase_eq_compMul g h0 ν e k

/-- PDF image coordinates `(n₁',n₂,…; m₁',t₂m₂',…)`. -/
def IntersectionOuter.imageN {s : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s)
    (i : Fin s) : ℕ :=
  if i = ⟨0, h0⟩ then ν.n1' else ν.nTail i

def IntersectionOuter.imageM {s : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s)
    (i : Fin s) : ℕ :=
  if i = ⟨0, h0⟩ then ν.m1' else ν.t i * ν.m' i

/--
Image solution attached to an outer coming from `I1Outer`
(PDF map before matrix parametrisation).
-/
noncomputable def I1Outer.imageSol {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : Sol s N := by
  classical
  -- recover a witness `x` with `ν = outer(x)`
  have hx : ∃ x ∈ I1Support (s := s) (N := N) A I h0,
      (x.toIntersectionCanon h0).outer = ν := by
    simpa [I1Outer] using Finset.mem_image.1 hν
  exact Classical.choose hx

theorem I1Outer.imageSol_memSupport {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    I1Outer.imageSol hν ∈ I1Support (s := s) (N := N) A I h0 := by
  classical
  have hx : ∃ x ∈ I1Support (s := s) (N := N) A I h0,
      (x.toIntersectionCanon h0).outer = ν := by
    simpa [I1Outer] using Finset.mem_image.1 hν
  exact (Classical.choose_spec hx).1

theorem I1Outer.imageSol_outer {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ((I1Outer.imageSol hν).toIntersectionCanon h0).outer = ν := by
  classical
  have hx : ∃ x ∈ I1Support (s := s) (N := N) A I h0,
      (x.toIntersectionCanon h0).outer = ν := by
    simpa [I1Outer] using Finset.mem_image.1 hν
  exact (Classical.choose_spec hx).2

/--
PDF image as a `Sol`: `(n₁', n₂,…; m₁', t₂m₂',…)`, via the witness outer.
-/
noncomputable def I1Outer.toImageSol {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : Sol s N := by
  classical
  set x := I1Outer.imageSol hν
  set c := x.toIntersectionCanon h0
  have houter : c.outer = ν := by
    simpa [x, c] using I1Outer.imageSol_outer hν
  refine
    { n := fun i => if i = ⟨0, h0⟩ then c.outer.n1' else x.n i
      m := fun i => if i = ⟨0, h0⟩ then c.outer.m1' else x.m i
      hn := ?_
      hm := ?_
      hprod := ?_ }
  · intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have hn0 := toIntersectionCanon_reconN1 s N x h0
      have hbT := toIntersectionCanon_b_mul_T_pos s N x h0
      have hrep : x.n ⟨0, h0⟩ = c.b * c.outer.T h0 * c.outer.n1' := by
        simpa [IntersectionCanon.reconN1, c] using hn0.symm
      have hle : c.outer.n1' ≤ x.n ⟨0, h0⟩ := by
        have : c.outer.n1' ≤ c.b * c.outer.T h0 * c.outer.n1' :=
          Nat.le_mul_of_pos_left _ hbT
        simpa [hrep] using this
      have hpos : 0 < c.outer.n1' := by
        have hxpos := lt_of_lt_of_le Nat.zero_lt_one (x.hn ⟨0, h0⟩).1
        have : 0 < c.b * c.outer.T h0 * c.outer.n1' := by simpa [hrep] using hxpos
        exact Nat.pos_of_mul_pos_left this
      exact ⟨Nat.succ_le_of_lt hpos, hle.trans (x.hn ⟨0, h0⟩).2⟩
    · simpa [hi0] using x.hn i
  · intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have hm0 := toIntersectionCanon_reconM1 s N x h0
      have hbT := toIntersectionCanon_b_mul_T_pos s N x h0
      have hrep : x.m ⟨0, h0⟩ = c.b * c.outer.T h0 * c.outer.m1' := by
        simpa [IntersectionCanon.reconM1, c] using hm0.symm
      have hle : c.outer.m1' ≤ x.m ⟨0, h0⟩ := by
        have : c.outer.m1' ≤ c.b * c.outer.T h0 * c.outer.m1' :=
          Nat.le_mul_of_pos_left _ hbT
        simpa [hrep] using this
      have hpos : 0 < c.outer.m1' := by
        have hxpos := lt_of_lt_of_le Nat.zero_lt_one (x.hm ⟨0, h0⟩).1
        have : 0 < c.b * c.outer.T h0 * c.outer.m1' := by simpa [hrep] using hxpos
        exact Nat.pos_of_mul_pos_left this
      exact ⟨Nat.succ_le_of_lt hpos, hle.trans (x.hm ⟨0, h0⟩).2⟩
    · simpa [hi0] using x.hm i
  · -- product identity from outer_product + m_i = t_i m_i'
    have hEq := toIntersectionCanon_outer_product s N x h0
    set E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
    have h0mem : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
    have hn :
        (∏ i, (if i = ⟨0, h0⟩ then c.outer.n1' else x.n i)) =
          c.outer.n1' * (∏ i ∈ E, x.n i) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = ⟨0, h0⟩ then c.outer.n1' else x.n i) h0mem]
      change c.outer.n1' *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (if i = ⟨0, h0⟩ then c.outer.n1' else x.n i)) =
        c.outer.n1' * (∏ i ∈ E, x.n i)
      congr 1
      refine Finset.prod_congr (by simp [E]) fun i hi => ?_
      have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      simp [hi0]
    have hm :
        (∏ i, (if i = ⟨0, h0⟩ then c.outer.m1' else x.m i)) =
          c.outer.m1' * (∏ i ∈ E, x.m i) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = ⟨0, h0⟩ then c.outer.m1' else x.m i) h0mem]
      change c.outer.m1' *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (if i = ⟨0, h0⟩ then c.outer.m1' else x.m i)) =
        c.outer.m1' * (∏ i ∈ E, x.m i)
      congr 1
      refine Finset.prod_congr (by simp [E]) fun i hi => ?_
      have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      simp [hi0]
    have hnE : (∏ i ∈ E, x.n i) = ∏ i ∈ E, c.outer.nTail i := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      simp [c, Sol.toIntersectionCanon, hi0]
    have hmE : (∏ i ∈ E, x.m i) = ∏ i ∈ E, (c.outer.t i * c.outer.m' i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      have := toIntersectionCanon_reconM_tail s N x h0 i hi0
      simpa [IntersectionCanon.reconM, hi0, c] using this.symm
    calc
      (∏ i, (if i = ⟨0, h0⟩ then c.outer.n1' else x.n i))
          = c.outer.n1' * (∏ i ∈ E, c.outer.nTail i) := by rw [hn, hnE]
      _ = c.outer.T h0 * c.outer.m1' * (∏ i ∈ E, c.outer.m' i) := hEq
      _ = c.outer.m1' * ((∏ i ∈ E, c.outer.t i) * (∏ i ∈ E, c.outer.m' i)) := by
            simp [IntersectionOuter.T, E]; ring
      _ = c.outer.m1' * (∏ i ∈ E, c.outer.t i * c.outer.m' i) := by
            rw [← Finset.prod_mul_distrib]
      _ = c.outer.m1' * (∏ i ∈ E, x.m i) := by rw [hmE]
      _ = (∏ i, (if i = ⟨0, h0⟩ then c.outer.m1' else x.m i)) := by rw [← hm]

/-- Off-diagonal matrix label of the PDF image. -/
noncomputable def I1Outer.fibreKey {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : MatrixParam s :=
  offDiagNormalize (solToMatrix (I1Outer.toImageSol hν))

theorem I1Outer.toImageSol_n0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (I1Outer.toImageSol hν).n ⟨0, h0⟩ = ν.n1' := by
  have houter := I1Outer.imageSol_outer hν
  simp only [I1Outer.toImageSol]
  simp [houter]

theorem I1Outer.toImageSol_m0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (I1Outer.toImageSol hν).m ⟨0, h0⟩ = ν.m1' := by
  have houter := I1Outer.imageSol_outer hν
  simp only [I1Outer.toImageSol]
  simp [houter]

theorem I1Outer.toImageSol_not_onDiag {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ¬ (I1Outer.toImageSol hν).onDiag h0 := by
  have hx := I1Outer.imageSol_memSupport hν
  have hne := I1Support_n1'_ne_m1' hx
  have houter := I1Outer.imageSol_outer hν
  intro hdiag
  have hn := I1Outer.toImageSol_n0 hν
  have hm := I1Outer.toImageSol_m0 hν
  simp only [Sol.onDiag, hn, hm] at hdiag
  exact hne (by simpa [houter] using hdiag)

theorem I1Outer.fibreKey_mem_PieceIIIFibres {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    I1Outer.fibreKey hν ∈ PieceIIIFibres s N := by
  simp only [PieceIIIFibres, h0, ↓reduceDIte, I1Outer.fibreKey]
  exact Finset.mem_image.2
    ⟨I1Outer.toImageSol hν,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, I1Outer.toImageSol_not_onDiag hν⟩,
      rfl⟩

theorem I1Outer.toImageSol_gcd0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    Nat.gcd ((I1Outer.toImageSol hν).n ⟨0, h0⟩)
      ((I1Outer.toImageSol hν).m ⟨0, h0⟩) = 1 := by
  rw [I1Outer.toImageSol_n0 hν, I1Outer.toImageSol_m0 hν]
  have hx := I1Outer.imageSol_memSupport hν
  have houter := I1Outer.imageSol_outer hν
  have hcop := toIntersectionCanon_n1'_m1'_coprime (I1Outer.imageSol hν) h0
  simpa [houter] using hcop

theorem I1Outer.toImageSol_n_tail {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) :
    (I1Outer.toImageSol hν).n i = ν.nTail i := by
  have houter := I1Outer.imageSol_outer hν
  have : (I1Outer.imageSol hν).n i = ν.nTail i := by
    have h := congrArg (fun ω : IntersectionOuter s => ω.nTail i) houter
    -- h: outer.nTail i = ν.nTail i, and outer.nTail i = x.n i
    simpa [Sol.toIntersectionCanon, hi0] using h
  simp only [I1Outer.toImageSol]
  simpa [hi0] using this

theorem I1Outer.toImageSol_m_tail {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) :
    (I1Outer.toImageSol hν).m i = ν.t i * ν.m' i := by
  have houter := I1Outer.imageSol_outer hν
  have hrecon :=
    toIntersectionCanon_reconM_tail s N (I1Outer.imageSol hν) h0 i hi0
  have : (I1Outer.imageSol hν).m i = ν.t i * ν.m' i := by
    -- recon: outer.t * outer.m' = x.m; rewrite outer → ν
    simpa [IntersectionCanon.reconM, hi0, houter] using hrecon.symm
  simp only [I1Outer.toImageSol]
  simpa [hi0] using this

/-- PDF: image map is injective on outers with a fixed `t`-vector. -/
theorem I1Outer.toImageSol_injective_of_eq_t {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν₁ ν₂ : IntersectionOuter s}
    (hν₁ : ν₁ ∈ I1Outer (s := s) (N := N) A I h0)
    (hν₂ : ν₂ ∈ I1Outer (s := s) (N := N) A I h0)
    (ht : ν₁.t = ν₂.t)
    (heq : I1Outer.toImageSol hν₁ = I1Outer.toImageSol hν₂) : ν₁ = ν₂ := by
  have hn0 :
      ν₁.n1' = ν₂.n1' :=
    (I1Outer.toImageSol_n0 hν₁).symm.trans <|
      (congrArg (fun y : Sol s N => y.n ⟨0, h0⟩) heq).trans
        (I1Outer.toImageSol_n0 hν₂)
  have hm0 :
      ν₁.m1' = ν₂.m1' :=
    (I1Outer.toImageSol_m0 hν₁).symm.trans <|
      (congrArg (fun y : Sol s N => y.m ⟨0, h0⟩) heq).trans
        (I1Outer.toImageSol_m0 hν₂)
  have hnTail : ν₁.nTail = ν₂.nTail := by
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have ht1 : ν₁.nTail ⟨0, h0⟩ = 1 := by
        rcases Finset.mem_image.1 hν₁ with ⟨x, _, rfl⟩
        exact toIntersectionCanon_nTail0 x h0
      have ht2 : ν₂.nTail ⟨0, h0⟩ = 1 := by
        rcases Finset.mem_image.1 hν₂ with ⟨x, _, rfl⟩
        exact toIntersectionCanon_nTail0 x h0
      simp [ht1, ht2]
    · have h := congrArg (fun y : Sol s N => y.n i) heq
      rw [I1Outer.toImageSol_n_tail hν₁ hi0, I1Outer.toImageSol_n_tail hν₂ hi0] at h
      exact h
  have hm' : ν₁.m' = ν₂.m' := by
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      have hm1 : ν₁.m' ⟨0, h0⟩ = ν₁.m1' := by
        rcases Finset.mem_image.1 hν₁ with ⟨x, _, rfl⟩
        exact toIntersectionCanon_m0' x h0
      have hm2 : ν₂.m' ⟨0, h0⟩ = ν₂.m1' := by
        rcases Finset.mem_image.1 hν₂ with ⟨x, _, rfl⟩
        exact toIntersectionCanon_m0' x h0
      simp [hm1, hm2, hm0]
    · have h := congrArg (fun y : Sol s N => y.m i) heq
      rw [I1Outer.toImageSol_m_tail hν₁ hi0, I1Outer.toImageSol_m_tail hν₂ hi0] at h
      have ht_i : ν₁.t i = ν₂.t i := congrFun ht i
      have hpos : 0 < ν₁.t i := I1Outer_t_pos hν₁ hi0
      exact Nat.mul_left_cancel hpos (by simpa [ht_i] using h)
  cases ν₁; cases ν₂
  simp_all [IntersectionOuter.mk.injEq]

/-- Head off-diagonals of the image fibre equal `(n₁', m₁')`. -/
theorem I1Outer.fibreKey_rowOff {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (I1Outer.fibreKey hν).rowOffDiag ⟨0, h0⟩ = ν.n1' := by
  set y := I1Outer.toImageSol hν
  have hgcd : diagGcd y ⟨0, h0⟩ = 1 := by
    simp only [diagGcd, y]
    exact I1Outer.toImageSol_gcd0 hν
  have ha : (solToMatrix y).a ⟨0, h0⟩ ⟨0, h0⟩ = 1 := by
    rw [solToMatrix_diag_eq_gcd, hgcd]
  have hrowOff : (solToMatrix y).rowOffDiag ⟨0, h0⟩ = y.n ⟨0, h0⟩ := by
    have hform :
        (solToMatrix y).a ⟨0, h0⟩ ⟨0, h0⟩ * (solToMatrix y).rowOffDiag ⟨0, h0⟩ =
          y.n ⟨0, h0⟩ := by
      simpa [MatrixParam.rowProd_eq_diag_mul_offDiag] using
        solToMatrix_rowProd y ⟨0, h0⟩
    rw [ha, one_mul] at hform
    exact hform
  calc
    (I1Outer.fibreKey hν).rowOffDiag ⟨0, h0⟩
        = (solToMatrix y).rowOffDiag ⟨0, h0⟩ := by
            simp [I1Outer.fibreKey, y, offDiagNormalize_rowOffDiag]
    _ = y.n ⟨0, h0⟩ := hrowOff
    _ = ν.n1' := I1Outer.toImageSol_n0 hν

theorem I1Outer.fibreKey_colOff {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (I1Outer.fibreKey hν).colOffDiag ⟨0, h0⟩ = ν.m1' := by
  set y := I1Outer.toImageSol hν
  have hgcd : diagGcd y ⟨0, h0⟩ = 1 := by
    simp only [diagGcd, y]
    exact I1Outer.toImageSol_gcd0 hν
  have ha : (solToMatrix y).a ⟨0, h0⟩ ⟨0, h0⟩ = 1 := by
    rw [solToMatrix_diag_eq_gcd, hgcd]
  have hcolOff : (solToMatrix y).colOffDiag ⟨0, h0⟩ = y.m ⟨0, h0⟩ := by
    have hform :
        (solToMatrix y).a ⟨0, h0⟩ ⟨0, h0⟩ * (solToMatrix y).colOffDiag ⟨0, h0⟩ =
          y.m ⟨0, h0⟩ := by
      simpa [MatrixParam.colProd_eq_diag_mul_offDiag] using
        solToMatrix_colProd y ⟨0, h0⟩
    rw [ha, one_mul] at hform
    exact hform
  calc
    (I1Outer.fibreKey hν).colOffDiag ⟨0, h0⟩
        = (solToMatrix y).colOffDiag ⟨0, h0⟩ := by
            simp [I1Outer.fibreKey, y, offDiagNormalize_colOffDiag]
    _ = y.m ⟨0, h0⟩ := hcolOff
    _ = ν.m1' := I1Outer.toImageSol_m0 hν

theorem I1Outer.fibreKey_scale0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    keyScale (I1Outer.fibreKey hν) ⟨0, h0⟩ = max ν.n1' ν.m1' := by
  simp only [keyScale, MatrixParam.scale, I1Outer.fibreKey_rowOff hν,
    I1Outer.fibreKey_colOff hν]

/--
`I1BoxSum` rewritten on the image fibre key: phases are the scaled `J1`
head summands for `(n₁',m₁')`.
-/
theorem I1BoxSum_eq_sum_on_fibreKey {d s N A : ℕ} (g : CirclePoly d)
    {I : Finset (Fin s)} {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ) :
    I1BoxSum g N A h0 ν e =
      ∑ k ∈ (Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0,
        (g.compMul (e * ν.T h0)).ePhase
            (k * (I1Outer.fibreKey hν).rowOffDiag ⟨0, h0⟩) *
          starRingEnd ℂ
            ((g.compMul (e * ν.T h0)).ePhase
              (k * (I1Outer.fibreKey hν).colOffDiag ⟨0, h0⟩)) := by
  rw [I1BoxSum_eq_sum_compMul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [I1Outer.fibreKey_rowOff hν, I1Outer.fibreKey_colOff hν]

/-- Box index set equals the scaled head fibre of the image label. -/
theorem I1Box_support_eq_keyHeadFibreScaled {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ) (he : 1 ≤ e)
    (hT : 0 < ν.T h0) (hM : 0 < max ν.n1' ν.m1') :
    (Finset.Icc 1 N).filter (fun k => e * k ∈ fibreB s N A ν h0) =
      keyHeadFibreScaled (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 := by
  set h := e * ν.T h0
  set M := max ν.n1' ν.m1'
  set F := I1Outer.fibreKey hν
  have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he
  have hh1 : 1 ≤ h := Nat.succ_le_of_lt (Nat.mul_pos hepos hT)
  have hscale : keyScale F ⟨0, h0⟩ = M := by
    simpa [F, M] using I1Outer.fibreKey_scale0 hν
  ext k
  constructor
  · intro hk
    have hkHead :
        k ∈ (Finset.Icc 1 N).filter fun b =>
          A ≤ h * b ∧ h * b * keyScale F ⟨0, h0⟩ ≤ N := by
      rcases Finset.mem_filter.1 hk with ⟨hkIcc, hb⟩
      rcases (mem_fibreB_mul_iff ν h0 e k).1 hb with ⟨_, hA, hNM⟩
      refine Finset.mem_filter.2 ⟨hkIcc, ?_, ?_⟩
      · simpa [h, mul_assoc, mul_left_comm, mul_comm] using hA
      · simpa [h, hscale, M, mul_assoc, mul_left_comm, mul_comm] using hNM
    simpa [keyHeadFibreScaled, hh1, F, h] using hkHead
  · intro hk
    have hkHead :
        k ∈ (Finset.Icc 1 N).filter fun b =>
          A ≤ h * b ∧ h * b * keyScale F ⟨0, h0⟩ ≤ N := by
      simpa [keyHeadFibreScaled, hh1, F, h] using hk
    rcases Finset.mem_filter.1 hkHead with ⟨hkIcc, hA, hNM⟩
    have hk1 := (Finset.mem_Icc.1 hkIcc).1
    have hA' : A ≤ e * k * ν.T h0 := by
      simpa [h, mul_assoc, mul_left_comm, mul_comm] using hA
    have hNM' : e * k * ν.T h0 * M ≤ N := by
      simpa [h, hscale, M, mul_assoc, mul_left_comm, mul_comm] using hNM
    have hposTM : 0 < ν.T h0 * M := Nat.mul_pos hT hM
    have hek_le : e * k ≤ N :=
      le_trans (Nat.le_mul_of_pos_right (e * k) hposTM)
        (by simpa [mul_assoc] using hNM')
    have hek1 : 1 ≤ e * k := Nat.mul_le_mul he hk1
    have hb : e * k ∈ fibreB s N A ν h0 :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hek1, hek_le⟩, hA', hNM'⟩
    exact Finset.mem_filter.2 ⟨hkIcc, hb⟩

/--
Box support lands in the usual `Icc` majorant of the scaled head fibre.
-/
theorem mem_keyHead_of_mem_I1Box {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e k : ℕ) (he : 1 ≤ e)
    (hT : 0 < ν.T h0) (hM : 0 < max ν.n1' ν.m1')
    (hk : k ∈ (Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0) :
    k ∈ Finset.Icc (max 1 (A / (e * ν.T h0)))
      (N / (e * ν.T h0 * max ν.n1' ν.m1')) := by
  have hscale : keyScale (I1Outer.fibreKey hν) ⟨0, h0⟩ = max ν.n1' ν.m1' :=
    I1Outer.fibreKey_scale0 hν
  have hh1 : 1 ≤ e * ν.T h0 :=
    Nat.succ_le_of_lt (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one he) hT)
  have hk' : k ∈ keyHeadFibreScaled (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 := by
    simpa [I1Box_support_eq_keyHeadFibreScaled hν e he hT hM] using hk
  have hsub :=
    keyHeadFibreScaled_subset_Icc (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 hh1
      (by simpa [hscale] using hM)
  simpa [hscale] using hsub hk'

/-- PDF identification: box sum = scaled head sum on the image fibre. -/
theorem I1BoxSum_eq_J1InnerSumScaled {d s N A : ℕ} (g : CirclePoly d)
    {I : Finset (Fin s)} {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ) (he : 1 ≤ e)
    (hT : 0 < ν.T h0) (hM : 0 < max ν.n1' ν.m1') :
    I1BoxSum g N A h0 ν e =
      J1InnerSumScaled g (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 := by
  rw [I1BoxSum_eq_sum_on_fibreKey g hν e, J1InnerSumScaled,
    I1Box_support_eq_keyHeadFibreScaled hν e he hT hM]

theorem I1Outer.n1'_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : 0 < ν.n1' := by
  have hn := (I1Outer.toImageSol hν).hn ⟨0, h0⟩
  have : (I1Outer.toImageSol hν).n ⟨0, h0⟩ = ν.n1' := I1Outer.toImageSol_n0 hν
  have : 1 ≤ ν.n1' := by simpa [this] using hn.1
  exact lt_of_lt_of_le Nat.zero_lt_one this

theorem I1Outer.m1'_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : 0 < ν.m1' := by
  have hm := (I1Outer.toImageSol hν).hm ⟨0, h0⟩
  have : (I1Outer.toImageSol hν).m ⟨0, h0⟩ = ν.m1' := I1Outer.toImageSol_m0 hν
  have : 1 ≤ ν.m1' := by simpa [this] using hm.1
  exact lt_of_lt_of_le Nat.zero_lt_one this

theorem I1Outer.max_n1'_m1'_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : 0 < max ν.n1' ν.m1' :=
  lt_max_of_lt_left (I1Outer.n1'_pos hν)

/-- Pointwise: ‖box‖ = ‖scaled inner‖ ≤ scaled fibre contribution. -/
theorem norm_I1BoxSum_le_fibreContrib {d : ℕ} (g : CirclePoly d)
    {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ) (he : 1 ≤ e)
    (hTpos : 0 < ν.T h0) :
    ‖I1BoxSum g N A h0 ν e‖ ≤
      J1FibreContributionScaled g (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 := by
  have hM := I1Outer.max_n1'_m1'_pos hν
  rw [I1BoxSum_eq_J1InnerSumScaled g hν e he hTpos hM]
  simp only [J1FibreContributionScaled]
  exact le_mul_of_one_le_right (norm_nonneg _)
    (J1TailWeight_one_le_of_mem_PieceIIIFibres h0
      (I1Outer.fibreKey_mem_PieceIIIFibres hν))

theorem fold_max_le_of_forall_le (s : Finset ℝ) {C : ℝ} (h0C : 0 ≤ C)
    (hC : ∀ x ∈ s, x ≤ C) : s.fold max 0 id ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    exact max_le (hC a (Finset.mem_insert_self _ _))
      (ih fun x hx => hC x (Finset.mem_insert_of_mem hx))

theorem J1ScaledSumAtHeight_nonneg (d s N A : ℕ) (g : CirclePoly d) (h : ℕ) :
    0 ≤ J1ScaledSumAtHeight d s N A g h := by
  simp only [J1ScaledSumAtHeight]
  split_ifs with hs
  · refine Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (J1TailWeight_nonneg _ _ _)
  · exact le_rfl

/-- Vacuous height: scaled head fibres empty, so the majorant sum is 0. -/
theorem J1ScaledSumAtHeight_eq_zero_of_h_gt_N (d s N A : ℕ) (g : CirclePoly d)
    (h : ℕ) (hh1 : 1 ≤ h) (hNlt : N < h) :
    J1ScaledSumAtHeight d s N A g h = 0 := by
  simp only [J1ScaledSumAtHeight]
  split_ifs with hs
  · refine Finset.sum_eq_zero fun k _ => ?_
    have h0 : 0 < s := by omega
    have hempty := keyHeadFibreScaled_eq_empty_of_h_gt_N k N A h h0 hh1 hNlt
    simp only [J1FibreContributionScaled, J1InnerSumScaled, hempty,
      Finset.sum_empty, norm_zero, zero_mul]
  · rfl

/-- If `⌈A/h⌉ > N/h`, every scaled head fibre is empty. -/
theorem J1ScaledSumAtHeight_eq_zero_of_head_gt_Nh (d s N A : ℕ)
    (g : CirclePoly d) (h : ℕ) (hs : 2 ≤ s) (hA : 1 ≤ A) (hh1 : 1 ≤ h)
    (hgt : N / h < scaledHeadLo A h) :
    J1ScaledSumAtHeight d s N A g h = 0 := by
  simp only [J1ScaledSumAtHeight, hs, ↓reduceIte]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h0 : 0 < s := by omega
  have hM : 1 ≤ keyScale k ⟨0, h0⟩ := Nat.succ_le_of_lt (k.scale_pos ⟨0, h0⟩)
  have hNM : N / (h * keyScale k ⟨0, h0⟩) ≤ N / h := by
    have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh1
    have hmul : h ≤ h * keyScale k ⟨0, h0⟩ := Nat.le_mul_of_pos_right h hM
    exact Nat.div_le_div_left hmul hh0
  have hempty :
      keyHeadFibreScaled k N A h h0 = ∅ :=
    (keyHeadFibreScaled_eq_empty_iff k N A h h0 hA hh1).2
      (lt_of_le_of_lt hNM hgt)
  simp only [J1FibreContributionScaled, J1InnerSumScaled, hempty,
    Finset.sum_empty, norm_zero, zero_mul]

/-! ### Fixed-`t` grouping: multiplicity ≤ ambient tail weight -/

/-- Diagonal box with head fixed to `1` (Piece III image has `a₁₁ = 1`). -/
def pieceIIITailDiagBox {s : ℕ} (k : MatrixParam s) (N : ℕ) (h0 : 0 < s) :
    Finset (Fin s → ℕ) :=
  Fintype.piFinset fun i =>
    if i = ⟨0, h0⟩ then ({1} : Finset ℕ)
    else Finset.Icc 1 (N / keyScale k i)

theorem card_pieceIIITailDiagBox {s : ℕ} (k : MatrixParam s) (N : ℕ)
    (h0 : 0 < s) :
    (pieceIIITailDiagBox k N h0).card =
      ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), N / keyScale k i := by
  classical
  simp only [pieceIIITailDiagBox]
  have h0mem : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
  rw [Fintype.card_piFinset,
    ← Finset.mul_prod_erase (Finset.univ : Finset (Fin s))
      (fun i => (if i = ⟨0, h0⟩ then ({1} : Finset ℕ)
        else Finset.Icc 1 (N / keyScale k i)).card) h0mem]
  have h1 : (({1} : Finset ℕ)).card = 1 := by simp
  simp only [↓reduceIte, h1, one_mul]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
  simp [hi0, Nat.card_Icc]

theorem card_pieceIIITailDiagBox_eq_tailWeight {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) :
    ((pieceIIITailDiagBox k N h0).card : ℝ) = J1TailWeight k N h0 := by
  simp only [J1TailWeight, card_pieceIIITailDiagBox]
  push_cast
  rfl

/-- Diagonals of the image solution. -/
noncomputable def I1Outer.imageDiag {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : Fin s → ℕ :=
  fun i => (solToMatrix (I1Outer.toImageSol hν)).a i i

theorem I1Outer.imageDiag_zero {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    I1Outer.imageDiag hν ⟨0, h0⟩ = 1 := by
  simp only [I1Outer.imageDiag]
  have hgcd : diagGcd (I1Outer.toImageSol hν) ⟨0, h0⟩ = 1 := by
    simp only [diagGcd]
    exact I1Outer.toImageSol_gcd0 hν
  simpa [solToMatrix_diag_eq_gcd, hgcd]

theorem I1Outer.imageDiag_mem_tailBox {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    I1Outer.imageDiag hν ∈
      pieceIIITailDiagBox (I1Outer.fibreKey hν) N h0 := by
  set y := I1Outer.toImageSol hν
  set F := I1Outer.fibreKey hν
  have hkey : offDiagNormalize (solToMatrix y) = F := rfl
  refine (Fintype.mem_piFinset).2 fun i => ?_
  by_cases hi0 : i = ⟨0, h0⟩
  · subst hi0
    simpa [pieceIIITailDiagBox, I1Outer.imageDiag, y, F] using
      I1Outer.imageDiag_zero hν
  · simp only [pieceIIITailDiagBox, hi0, ↓reduceIte]
    have h1 : 1 ≤ (solToMatrix y).a i i :=
      Nat.succ_le_of_lt ((solToMatrix y).entries_pos i i)
    have hle := solToMatrix_diag_le_scale y i
    have hscale : (solToMatrix y).scale i = keyScale F i := by
      rw [← hkey, keyScale_eq_scale]
    refine Finset.mem_Icc.2 ⟨h1, ?_⟩
    simpa [I1Outer.imageDiag, y, hscale] using hle

/-- Dummy matrix label used only off `I1Outer`. -/
def defaultMatrixParam (s : ℕ) : MatrixParam s where
  a := fun _ _ => 1
  entries_pos := fun _ _ => Nat.one_pos

/-- Fibre key as a total function on outers (agrees with `fibreKey` on `I1Outer`). -/
noncomputable def I1Outer.keyOn {s N A : ℕ} (I : Finset (Fin s)) (h0 : 0 < s)
    (ν : IntersectionOuter s) : MatrixParam s :=
  if h : ν ∈ I1Outer (s := s) (N := N) A I h0 then I1Outer.fibreKey h
  else defaultMatrixParam s

theorem I1Outer.keyOn_eq_fibreKey {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    I1Outer.keyOn (N := N) (A := A) I h0 ν = I1Outer.fibreKey hν := by
  simp [I1Outer.keyOn, hν]

/--
Fixed-`t` multiplicity of an image fibre label is at most the ambient tail
weight (PDF: bound diagonal choices `i ≥ 2` trivially; head diagonal is `1`).
-/
theorem card_fixed_t_fibreKey_le_tail {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} (tVec : Fin s → ℕ) (F : MatrixParam s) :
    let Outer := I1Outer (s := s) (N := N) A I h0
    let S := Outer.filter fun ν => ν.t = tVec
    let SF := S.filter fun ν => I1Outer.keyOn (N := N) (A := A) I h0 ν = F
    (SF.card : ℝ) ≤ J1TailWeight F N h0 := by
  intro Outer S SF
  classical
  set diagOf : IntersectionOuter s → Fin s → ℕ := fun ν =>
    if hν : ν ∈ Outer then I1Outer.imageDiag hν else fun _ => 0
  have hmem :
      ∀ ν ∈ SF, diagOf ν ∈ pieceIIITailDiagBox F N h0 := by
    intro ν hνSF
    have hνS : ν ∈ S := (Finset.mem_filter.1 hνSF).1
    have hνO : ν ∈ Outer := (Finset.mem_filter.1 hνS).1
    have hF : I1Outer.fibreKey hνO = F := by
      simpa [I1Outer.keyOn_eq_fibreKey hνO] using (Finset.mem_filter.1 hνSF).2
    have : diagOf ν = I1Outer.imageDiag hνO := by simp [diagOf, hνO]
    rw [this, ← hF]
    exact I1Outer.imageDiag_mem_tailBox hνO
  have hinj : Set.InjOn diagOf SF := by
    intro ν₁ h1 ν₂ h2 heq
    have h1S : ν₁ ∈ S := (Finset.mem_filter.1 h1).1
    have h2S : ν₂ ∈ S := (Finset.mem_filter.1 h2).1
    have h1O : ν₁ ∈ Outer := (Finset.mem_filter.1 h1S).1
    have h2O : ν₂ ∈ Outer := (Finset.mem_filter.1 h2S).1
    have ht : ν₁.t = ν₂.t := by
      have ht1 : ν₁.t = tVec := (Finset.mem_filter.1 h1S).2
      have ht2 : ν₂.t = tVec := (Finset.mem_filter.1 h2S).2
      exact ht1.trans ht2.symm
    have hF1 : I1Outer.fibreKey h1O = F := by
      simpa [I1Outer.keyOn_eq_fibreKey h1O] using (Finset.mem_filter.1 h1).2
    have hF2 : I1Outer.fibreKey h2O = F := by
      simpa [I1Outer.keyOn_eq_fibreKey h2O] using (Finset.mem_filter.1 h2).2
    have hdiag : I1Outer.imageDiag h1O = I1Outer.imageDiag h2O := by
      simpa [diagOf, h1O, h2O] using heq
    have hmat : solToMatrix (I1Outer.toImageSol h1O) =
        solToMatrix (I1Outer.toImageSol h2O) := by
      refine MatrixParam.ext fun i j => ?_
      by_cases hij : i = j
      · subst hij
        simpa [I1Outer.imageDiag] using congrFun hdiag i
      · have hx : (solToMatrix (I1Outer.toImageSol h1O)).a i j = F.a i j := by
          have := congrArg (fun p : MatrixParam s => p.a i j) hF1
          simpa [I1Outer.fibreKey, offDiagNormalize, hij] using this
        have hy : (solToMatrix (I1Outer.toImageSol h2O)).a i j = F.a i j := by
          have := congrArg (fun p : MatrixParam s => p.a i j) hF2
          simpa [I1Outer.fibreKey, offDiagNormalize, hij] using this
        simp [hx, hy]
    exact I1Outer.toImageSol_injective_of_eq_t h1O h2O ht
      (solToMatrix_injective hmat)
  have hcard : SF.card ≤ (pieceIIITailDiagBox F N h0).card :=
    Finset.card_le_card_of_injOn diagOf hmem hinj
  exact (Nat.cast_le.2 hcard).trans
    (le_of_eq (card_pieceIIITailDiagBox_eq_tailWeight F N h0))

theorem T_eq_of_embedTailTvec {s : ℕ} (h0 : 0 < s) {T : ℕ}
    (f : OrderedFactors (s - 1) T) {ν : IntersectionOuter s}
    (ht : ν.t = embedTailTvec h0 f.val) :
    ν.T h0 = T := by
  simp only [IntersectionOuter.T, ht]
  exact embedTailTvec_T h0 T f

/-- Group a fixed-`t` outer sum by image fibre labels. -/
theorem sum_norm_inner_fiberwise {d s N A : ℕ} (g : CirclePoly d)
    {I : Finset (Fin s)} {h0 : 0 < s} (e T : ℕ)
    (tVec : Fin s → ℕ) :
    let Outer := I1Outer (s := s) (N := N) A I h0
    let S := Outer.filter fun ν => ν.t = tVec
    let φ := I1Outer.keyOn (N := N) (A := A) I h0
    (∑ ν ∈ S, ‖J1InnerSumScaled g (φ ν) N A (e * T) h0‖) =
      ∑ k ∈ PieceIIIFibres s N,
        ((S.filter fun ν => φ ν = k).card : ℝ) *
          ‖J1InnerSumScaled g k N A (e * T) h0‖ := by
  intro Outer S φ
  classical
  have hexpand :
      (∑ ν ∈ S, ‖J1InnerSumScaled g (φ ν) N A (e * T) h0‖) =
        ∑ ν ∈ S,
          ∑ k ∈ PieceIIIFibres s N,
            if φ ν = k then ‖J1InnerSumScaled g k N A (e * T) h0‖ else 0 := by
    refine Finset.sum_congr rfl fun ν hνS => ?_
    have hνO : ν ∈ Outer := (Finset.mem_filter.1 hνS).1
    have hφ : φ ν = I1Outer.fibreKey hνO := I1Outer.keyOn_eq_fibreKey hνO
    have hFmem : φ ν ∈ PieceIIIFibres s N := by
      simpa [hφ] using I1Outer.fibreKey_mem_PieceIIIFibres hνO
    rw [Finset.sum_eq_single (φ ν)]
    · simp
    · intro k _ hkne
      simp [if_neg (Ne.symm hkne)]
    · exact fun hk => (hk hFmem).elim
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/--
Per-`(t,e)` embedding into the scaled fibre sum (PDF: group fixed-`t`
outers by image fibre labels; multiplicity ≤ ambient tail weight).
-/
theorem I1PieceIIITvecSum_le_J1ScaledSum (d : ℕ) :
    ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
      (I : Finset (Fin s)) (hs : 2 ≤ s) (_hN : 3 ≤ N) (_hA : 1 ≤ A)
      (e : ℕ) (hh1 : 1 ≤ e) (T : ℕ) (hT : 1 ≤ T)
      (f : OrderedFactors (s - 1) T),
      I1PieceIIITvecSum d s N A g δ I (by omega)
          (embedTailTvec (by omega) f.val) e ≤
        J1ScaledSumAtHeight d s N A g (e * T) := by
  intro s N A g δ I hs _hN _hA e hh1 T hT f
  classical
  set h0 : 0 < s := by omega
  set tVec := embedTailTvec h0 f.val
  set Outer := I1Outer (s := s) (N := N) A I h0
  set S := Outer.filter fun ν => ν.t = tVec
  set φ := I1Outer.keyOn (N := N) (A := A) I h0
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hstep1 :
      I1PieceIIITvecSum d s N A g δ I h0 tVec e ≤
        ∑ ν ∈ S, ‖I1BoxSum g N A h0 ν e‖ := by
    set S0 := Outer.filter fun ν => ν.t = tVec ∧ δ * (ν.T h0 : ℝ) < 1
    have hsub : S0 ⊆ S := by
      intro ν hν
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hν).1,
        (Finset.mem_filter.1 hν).2.1⟩
    simp only [I1PieceIIITvecSum]
    change (∑ ν ∈ S0,
        if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
          ‖I1BoxSum g N A h0 ν e‖ else 0) ≤
      ∑ ν ∈ S, ‖I1BoxSum g N A h0 ν e‖
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun _ _ _ => norm_nonneg _)
    refine Finset.sum_le_sum fun ν _ => ?_
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hinner :
      ∀ ν ∈ S,
        ‖I1BoxSum g N A h0 ν e‖ =
          ‖J1InnerSumScaled g (φ ν) N A (e * T) h0‖ := by
    intro ν hνS
    have hνO : ν ∈ Outer := (Finset.mem_filter.1 hνS).1
    have ht : ν.t = tVec := (Finset.mem_filter.1 hνS).2
    have hTν : ν.T h0 = T := T_eq_of_embedTailTvec h0 f ht
    have hTνpos : 0 < ν.T h0 := by simpa [hTν] using hTpos
    rw [I1BoxSum_eq_J1InnerSumScaled g hνO e hh1 hTνpos
      (I1Outer.max_n1'_m1'_pos hνO), hTν]
    simp [φ, I1Outer.keyOn_eq_fibreKey hνO]
  have hsum :
      (∑ ν ∈ S, ‖I1BoxSum g N A h0 ν e‖) ≤
        ∑ k ∈ PieceIIIFibres s N,
          J1FibreContributionScaled g k N A (e * T) h0 := by
    calc
      (∑ ν ∈ S, ‖I1BoxSum g N A h0 ν e‖)
          = ∑ ν ∈ S, ‖J1InnerSumScaled g (φ ν) N A (e * T) h0‖ :=
            Finset.sum_congr rfl hinner
      _ = ∑ k ∈ PieceIIIFibres s N,
            ((S.filter fun ν => φ ν = k).card : ℝ) *
              ‖J1InnerSumScaled g k N A (e * T) h0‖ := by
            simpa [Outer, S, φ] using
              sum_norm_inner_fiberwise (d := d) (s := s) (N := N) (A := A) g
                (I := I) (h0 := h0) e T tVec
      _ ≤ ∑ k ∈ PieceIIIFibres s N,
            J1FibreContributionScaled g k N A (e * T) h0 := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hcard :
              (((S.filter fun ν => φ ν = k).card) : ℝ) ≤
                J1TailWeight k N h0 := by
            simpa [Outer, S, φ] using
              card_fixed_t_fibreKey_le_tail (s := s) (N := N) (A := A) (I := I)
                (h0 := h0) tVec k
          simp only [J1FibreContributionScaled]
          calc
            (((S.filter fun ν => φ ν = k).card) : ℝ) *
                ‖J1InnerSumScaled g k N A (e * T) h0‖ ≤
              J1TailWeight k N h0 * ‖J1InnerSumScaled g k N A (e * T) h0‖ :=
              mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
            _ = ‖J1InnerSumScaled g k N A (e * T) h0‖ * J1TailWeight k N h0 :=
              mul_comm _ _
  simpa [J1ScaledSumAtHeight, hs, h0] using le_trans hstep1 hsum

/--
PDF embedding: `ScaledBlock(h)` ≤ scaled fibre sum over `PieceIIIFibres`.
-/
theorem I1PieceIIIScaledBlock_le_J1ScaledSum (d : ℕ) :
    ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N)
      (hA : 1 ≤ A) (h : ℕ) (hh1 : 1 ≤ h),
      I1PieceIIIScaledBlock d s N A g δ h ≤ J1ScaledSumAtHeight d s N A g h := by
  intro s N A g δ hs hN hA h hh1
  classical
  have hpt := I1PieceIIITvecSum_le_J1ScaledSum d
  have hsum0 := J1ScaledSumAtHeight_nonneg d s N A g h
  have hcand :
      ∀ x ∈ I1PieceIIIScaledBlockCandidates d s N A g δ h,
        x ≤ J1ScaledSumAtHeight d s N A g h := by
    intro x hx
    simp only [I1PieceIIIScaledBlockCandidates, hs, ↓reduceDIte] at hx
    rcases Finset.mem_biUnion.1 hx with ⟨I, _, hxI⟩
    rcases Finset.mem_biUnion.1 hxI with ⟨e, heIcc, hxE⟩
    by_cases he : e ∣ h
    · simp only [he, ↓reduceDIte] at hxE
      rcases Finset.mem_image.1 hxE with ⟨f, _, rfl⟩
      have he1 : 1 ≤ e := (Finset.mem_Icc.1 heIcc).1
      obtain ⟨T, hTe⟩ := he
      subst hTe
      have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he1
      have hT : 1 ≤ T := by
        have : 0 < e * T := lt_of_lt_of_le Nat.zero_lt_one hh1
        exact Nat.succ_le_of_lt (Nat.pos_of_mul_pos_left this)
      have hTeq : e * T / e = T := Nat.mul_div_cancel_left T hepos
      let fT : OrderedFactors (s - 1) T :=
        ⟨f.val, by simpa [hTeq] using f.property⟩
      simpa [hTeq] using hpt s N A g δ I hs hN hA e he1 T hT fT
    · simp only [he, ↓reduceDIte] at hxE
      exact (Finset.notMem_empty x hxE).elim
  simpa [I1PieceIIIScaledBlock] using fold_max_le_of_forall_le _ hsum0 hcand

/-! ### Scaled Σ bookkeeping (head length `N/(h M₁)` ⇒ factor `1/h`) -/

/-- Scaled fibre weight: ambient `J1FullWeight` divided by height `h`. -/
noncomputable def J1FullWeightScaled {s : ℕ} (k : MatrixParam s)
    (N h : ℕ) (h0 : 0 < s) : ℝ :=
  ((N : ℝ) / (h : ℝ)) / (keyScale k ⟨0, h0⟩ : ℝ) * J1TailWeight k N h0

theorem J1FullWeightScaled_eq_div {s : ℕ} (k : MatrixParam s)
    (N h : ℕ) (h0 : 0 < s) (_hh : 0 < (h : ℝ)) :
    J1FullWeightScaled k N h h0 =
      J1FullWeight k N h0 / (h : ℝ) := by
  simp only [J1FullWeightScaled, J1FullWeight, div_div]
  field_simp

theorem J1FullWeightScaled_nonneg {s : ℕ} (k : MatrixParam s)
    (N h : ℕ) (h0 : 0 < s) : 0 ≤ J1FullWeightScaled k N h h0 := by
  simp only [J1FullWeightScaled]
  exact mul_nonneg (div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (J1TailWeight_nonneg k N h0)

theorem J1_scaled_contrib_le_weight_A_lt_B {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) (δ : ℝ)
    (R : ℕ → Finset ℕ)
    (hAB : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩))
    (_hδ0 : 0 ≤ δ)
    (hbound : ‖J1InnerSumScaled g k N A h h0‖ ≤
      δ * ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, h0⟩) +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, h0⟩) else 0)) :
    J1FibreContributionScaled g k N A h h0 ≤
      δ * J1FullWeightScaled k N h h0 +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          J1FullWeightScaled k N h h0 else 0) := by
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = B1 := max_eq_right (Nat.le_of_lt hAB)
  have htail : 0 ≤ J1TailWeight k N h0 := J1TailWeight_nonneg k N h0
  have hstep :
      J1FibreContributionScaled g k N A h h0 ≤
        (δ * ((N : ℝ) / (h : ℝ)) / B1 +
          (if A1 ∈ R B1 then ((N : ℝ) / (h : ℝ)) / B1 else 0)) *
          J1TailWeight k N h0 := by
    simp only [J1FibreContributionScaled, A1, B1] at hbound ⊢
    exact mul_le_mul_of_nonneg_right hbound htail
  have hW :
      J1FullWeightScaled k N h h0 =
        ((N : ℝ) / (h : ℝ)) / B1 * J1TailWeight k N h0 := by
    simp only [J1FullWeightScaled, hM, B1]
  have hdistrib :
      (δ * ((N : ℝ) / (h : ℝ)) / B1 +
          (if A1 ∈ R B1 then ((N : ℝ) / (h : ℝ)) / B1 else 0)) *
          J1TailWeight k N h0 =
        δ * J1FullWeightScaled k N h h0 +
          (if A1 ∈ R B1 then J1FullWeightScaled k N h h0 else 0) := by
    rw [hW]
    split_ifs <;> ring
  exact hdistrib ▸ hstep

theorem J1_scaled_contrib_le_weight_B_lt_A {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) (δ : ℝ)
    (R : ℕ → Finset ℕ)
    (hBA : (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩))
    (_hδ0 : 0 ≤ δ)
    (hbound : ‖J1InnerSumScaled g k N A h h0‖ ≤
      δ * ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, h0⟩) +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, h0⟩) else 0)) :
    J1FibreContributionScaled g k N A h h0 ≤
      δ * J1FullWeightScaled k N h h0 +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          J1FullWeightScaled k N h h0 else 0) := by
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = A1 := max_eq_left (Nat.le_of_lt hBA)
  have htail : 0 ≤ J1TailWeight k N h0 := J1TailWeight_nonneg k N h0
  have hstep :
      J1FibreContributionScaled g k N A h h0 ≤
        (δ * ((N : ℝ) / (h : ℝ)) / A1 +
          (if B1 ∈ R A1 then ((N : ℝ) / (h : ℝ)) / A1 else 0)) *
          J1TailWeight k N h0 := by
    simp only [J1FibreContributionScaled, A1, B1] at hbound ⊢
    exact mul_le_mul_of_nonneg_right hbound htail
  have hW :
      J1FullWeightScaled k N h h0 =
        ((N : ℝ) / (h : ℝ)) / A1 * J1TailWeight k N h0 := by
    simp only [J1FullWeightScaled, hM, A1]
  have hdistrib :
      (δ * ((N : ℝ) / (h : ℝ)) / A1 +
          (if B1 ∈ R A1 then ((N : ℝ) / (h : ℝ)) / A1 else 0)) *
          J1TailWeight k N h0 =
        δ * J1FullWeightScaled k N h h0 +
          (if B1 ∈ R A1 then J1FullWeightScaled k N h h0 else 0) := by
    rw [hW]
    split_ifs <;> ring
  exact hdistrib ▸ hstep

theorem PieceIIIFibres_disjoint_union (s N : ℕ) (h0 : 0 < s) :
    PieceIIIFibres_A_lt_B s N h0 ∪ PieceIIIFibres_B_lt_A s N h0 ∪
        PieceIIIFibres_A_eq_B s N h0 =
      PieceIIIFibres s N := by
  ext k
  simp only [PieceIIIFibres_A_lt_B, PieceIIIFibres_B_lt_A,
    PieceIIIFibres_A_eq_B, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h
    rcases h with (h | h) | h <;> exact h.1
  · intro hk
    have : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩) ∨
        (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩) ∨
        (k.rowOffDiag ⟨0, h0⟩) = (k.colOffDiag ⟨0, h0⟩) := by omega
    rcases this with h | h | h
    · exact Or.inl (Or.inl ⟨hk, h⟩)
    · exact Or.inl (Or.inr ⟨hk, h⟩)
    · exact Or.inr ⟨hk, h⟩

theorem PieceIIIFibres_pairwise_disjoint (s N : ℕ) (h0 : 0 < s) :
    Disjoint (PieceIIIFibres_A_lt_B s N h0) (PieceIIIFibres_B_lt_A s N h0) ∧
      Disjoint
        (PieceIIIFibres_A_lt_B s N h0 ∪ PieceIIIFibres_B_lt_A s N h0)
        (PieceIIIFibres_A_eq_B s N h0) := by
  constructor
  · refine Finset.disjoint_left.2 fun k hk1 hk2 => ?_
    have h1 := (Finset.mem_filter.1 hk1).2
    have h2 := (Finset.mem_filter.1 hk2).2
    omega
  · refine Finset.disjoint_left.2 fun k hk1 hk2 => ?_
    have heq := (Finset.mem_filter.1 hk2).2
    simp only [Finset.mem_union, PieceIIIFibres_A_lt_B, PieceIIIFibres_B_lt_A,
      Finset.mem_filter] at hk1
    rcases hk1 with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega

theorem sum_scaled_contrib_split {d s N A : ℕ} (g : CirclePoly d)
    (h : ℕ) (h0 : 0 < s) (hs : 2 ≤ s) :
    J1ScaledSumAtHeight d s N A g h =
      (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
          J1FibreContributionScaled g k N A h h0) +
      (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
          J1FibreContributionScaled g k N A h h0) +
      (∑ k ∈ PieceIIIFibres_A_eq_B s N h0,
          J1FibreContributionScaled g k N A h h0) := by
  have hU := PieceIIIFibres_disjoint_union s N h0
  have hD := PieceIIIFibres_pairwise_disjoint s N h0
  simp only [J1ScaledSumAtHeight, hs, ↓reduceDIte]
  rw [← hU, Finset.sum_union hD.2, Finset.sum_union hD.1]

/-- Side sum on `A₁ < B₁` from scaled exceptional bounds. -/
theorem J1_scaled_side_sum_A_lt_B {d s N A : ℕ} (g : CirclePoly d)
    (δ : ℝ) (h : ℕ) (hs : 2 ≤ s) (hδ : 0 < δ)
    (R : ℕ → Finset ℕ)
    (hpt : ∀ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
      ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
        δ * ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩) +
          (if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
            ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩) else 0)) :
    (∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
        J1FibreContributionScaled g k N A h (by omega)) ≤
      δ * (∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
            J1FullWeightScaled k N h (by omega)) +
        ∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
          if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
            J1FullWeightScaled k N h (by omega) else 0 := by
  have h0 : 0 < s := by omega
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  calc
    (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
        J1FibreContributionScaled g k N A h h0) ≤
      ∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
        (δ * J1FullWeightScaled k N h h0 +
          (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
            J1FullWeightScaled k N h h0 else 0)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hAB := (Finset.mem_filter.1 hk).2
      exact J1_scaled_contrib_le_weight_A_lt_B g k N A h h0 δ R hAB hδ0 (hpt k hk)
    _ = δ * (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            J1FullWeightScaled k N h h0) +
          ∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0 := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem J1_scaled_side_sum_B_lt_A {d s N A : ℕ} (g : CirclePoly d)
    (δ : ℝ) (h : ℕ) (hs : 2 ≤ s) (hδ : 0 < δ)
    (R : ℕ → Finset ℕ)
    (hpt : ∀ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
      ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
        δ * ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩) +
          (if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
            ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩) else 0)) :
    (∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
        J1FibreContributionScaled g k N A h (by omega)) ≤
      δ * (∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
            J1FullWeightScaled k N h (by omega)) +
        ∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
          if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
            J1FullWeightScaled k N h (by omega) else 0 := by
  have h0 : 0 < s := by omega
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  calc
    (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
        J1FibreContributionScaled g k N A h h0) ≤
      ∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
        (δ * J1FullWeightScaled k N h h0 +
          (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
            J1FullWeightScaled k N h h0 else 0)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hBA := (Finset.mem_filter.1 hk).2
      exact J1_scaled_contrib_le_weight_B_lt_A g k N A h h0 δ R hBA hδ0 (hpt k hk)
    _ = δ * (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            J1FullWeightScaled k N h h0) +
          ∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0 := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Scaled Lemma 6 (PDF: apply the J1 argument to `g_h`) -/

-- `J1_lem5_exceptional_sets_scaled` is proved in `I1PieceIIIScaledLem5.lean`
-- (window on `scaledHeadLo A h`, pointwise coefficient `2δ`).

/-- `(log N)^{s(s-1)} ≤ I1PieceIIIPolylog`. -/
theorem log_pow_le_I1PieceIIIPolylog (N s : ℕ) (hN : 3 ≤ N) (_hs : 2 ≤ s) :
    (Real.log N) ^ (s * (s - 1)) ≤ I1PieceIIIPolylog N s := by
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hN)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hN1
  dsimp [I1PieceIIIPolylog]
  exact le_add_of_nonneg_right
    (mul_nonneg (pow_nonneg hlogN.le _)
      (pow_nonneg (mul_nonneg (by norm_num) hlogN.le) _))

/-- `σ_{II} ≤ (2 log N)^{(s-1)²}` when `N ≥ 3`. -/
theorem sigmaIILogFactor_le_twolog (N s : ℕ) (hN : 3 ≤ N) :
    sigmaIILogFactor N s ≤ (2 * Real.log N) ^ ((s - 1) * (s - 1)) := by
  have hlog := log_N_gt_one hN
  have hbase : (1 : ℝ) ≤ 2 * Real.log N := by nlinarith
  simp only [sigmaIILogFactor]
  refine (Real.sqrt_le_iff.2 ⟨pow_nonneg (mul_nonneg (by norm_num)
      (le_of_lt (lt_trans (by norm_num) hlog))) _, ?_⟩)
  have hpow :
      (2 * Real.log N) ^ ((s - 1) ^ 2 - 1) ≤
        (2 * Real.log N) ^ (2 * ((s - 1) * (s - 1))) := by
    have hk : (s - 1) ^ 2 - 1 ≤ 2 * ((s - 1) * (s - 1)) := by
      have : (s - 1) ^ 2 - 1 ≤ (s - 1) ^ 2 := Nat.sub_le _ _
      refine this.trans ?_
      have h2 : (s - 1) ^ 2 ≤ 2 * (s - 1) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by decide)
      simpa [pow_two] using h2
    exact pow_le_pow_right₀ hbase hk
  have hy2 :
      ((2 * Real.log N) ^ ((s - 1) * (s - 1))) ^ 2 =
        (2 * Real.log N) ^ (2 * ((s - 1) * (s - 1))) := by
    rw [pow_two, ← pow_add]
    congr 1
    ring
  exact hpow.trans_eq hy2.symm

/-- Harmonic × CS factor sits under the second summand of `I1PieceIIIPolylog`. -/
theorem cs_factor_le_I1PieceIIIPolylog (N s : ℕ) (hN : 3 ≤ N) :
    (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
      I1PieceIIIPolylog N s := by
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hN)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have hE := sigmaIILogFactor_le_twolog N s hN
  have hsec :
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        (Real.log N) ^ ((s - 1) * (s - 1)) *
          (2 * Real.log N) ^ ((s - 1) * (s - 1)) :=
    mul_le_mul_of_nonneg_left hE (pow_nonneg hlogN.le _)
  dsimp [I1PieceIIIPolylog]
  exact le_trans hsec (le_add_of_nonneg_left (pow_nonneg hlogN.le _))

/-- Empty `A₁ = B₁` side for the scaled majorant. -/
theorem PieceIII_A_eq_B_scaled_bound (d s N A : ℕ) (g : CirclePoly d)
    (h : ℕ) (h0 : 0 < s) :
    (∑ k ∈ PieceIIIFibres_A_eq_B s N h0,
        J1FibreContributionScaled g k N A h h0) = 0 := by
  simp [PieceIIIFibres_A_eq_B_empty s N h0]

theorem sum_J1FullWeightScaled_eq_div {s N h : ℕ}
    (S : Finset (MatrixParam s)) (h0 : 0 < s) (hh : 0 < (h : ℝ)) :
    (∑ k ∈ S, J1FullWeightScaled k N h h0) =
      (∑ k ∈ S, J1FullWeight k N h0) / (h : ℝ) := by
  simp_rw [J1FullWeightScaled_eq_div (k := _) (N := N) (h := h) (h0 := h0) hh,
    div_eq_mul_inv]
  rw [← Finset.sum_mul]

theorem sum_ite_J1FullWeightScaled_eq_div {s N h : ℕ}
    (S : Finset (MatrixParam s)) (p : MatrixParam s → Prop)
    [DecidablePred p] (h0 : 0 < s) (hh : 0 < (h : ℝ)) :
    (∑ k ∈ S, if p k then J1FullWeightScaled k N h h0 else 0) =
      (∑ k ∈ S, if p k then J1FullWeight k N h0 else 0) / (h : ℝ) := by
  have hterm : ∀ k,
      (if p k then J1FullWeightScaled k N h h0 else 0) =
        (if p k then J1FullWeight k N h0 else 0) * (h : ℝ)⁻¹ := by
    intro k
    by_cases hk : p k
    · simp only [hk, ↓reduceIte]
      rw [J1FullWeightScaled_eq_div k N h h0 hh, div_eq_mul_inv]
    · simp [hk]
  simp_rw [hterm, ← Finset.sum_mul, ← div_eq_mul_inv]

/--
Scaled Σ_I on `PieceIIIFibres` (both off-diagonal sides), constant may depend on `s`:
`∑ FullWeightScaled ≪ N^s/h · (log N)^{s(s-1)}`.
-/
theorem PieceIII_sigma_I_scaled_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A h : ℕ) (_hN : 3 ≤ N) (_hA : 1 ≤ A)
        (_hh1 : 1 ≤ h) (_hhN : h ≤ N),
        (∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
            J1FullWeightScaled k N h (by omega)) ≤
          C * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) ∧
        (∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
            J1FullWeightScaled k N h (by omega)) ≤
          C * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) := by
  obtain ⟨Ch, hCh, hhall⟩ := tau_harmonic_partial_sum s hs
  refine ⟨Ch ^ s, by positivity, ?_⟩
  intro N A h hN _hA hh1 _hhN
  have h0 : 0 < s := by omega
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hh1)
  have hrow : J1RowFactorSum s N ≤
      Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
    have hH := hhall N hN
    have hone :
        0 ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ) := by
      refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => ?_)
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hfactor :
        (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ) ≤
          Ch * (N : ℝ) * (Real.log N) ^ (s - 1) := by
      have := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg N)
      linarith
    have hpow :
        ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ^ s ≤
          (Ch * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ s :=
      pow_le_pow_left₀ hone hfactor s
    calc
      J1RowFactorSum s N =
          ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ^ s :=
        J1RowFactorSum_eq s N
      _ ≤ (Ch * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ s := hpow
      _ = Ch ^ s * (N : ℝ) ^ s * ((Real.log N) ^ (s - 1)) ^ s := by ring
      _ = Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
        rw [← pow_mul, mul_comm (s - 1) s]
  obtain ⟨hArow, hBrow⟩ := PieceIII_sigma_I_side_le_row_factor_sum s N h0
  have hdivA :=
    sum_J1FullWeightScaled_eq_div (N := N) (PieceIIIFibres_A_lt_B s N h0) h0 hhpos
  have hdivB :=
    sum_J1FullWeightScaled_eq_div (N := N) (PieceIIIFibres_B_lt_A s N h0) h0 hhpos
  have hA : (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
        J1FullWeightScaled k N h h0) ≤
      Ch ^ s * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) := by
    calc
      _ = (∑ k ∈ PieceIIIFibres_A_lt_B s N h0, J1FullWeight k N h0) / (h : ℝ) :=
        hdivA
      _ ≤ J1RowFactorSum s N / (h : ℝ) :=
        div_le_div_of_nonneg_right hArow hhpos.le
      _ ≤ (Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) / (h : ℝ) :=
        div_le_div_of_nonneg_right hrow hhpos.le
      _ = Ch ^ s * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) := by
        ring
  have hB : (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
        J1FullWeightScaled k N h h0) ≤
      Ch ^ s * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) := by
    calc
      _ = (∑ k ∈ PieceIIIFibres_B_lt_A s N h0, J1FullWeight k N h0) / (h : ℝ) :=
        hdivB
      _ ≤ J1RowFactorSum s N / (h : ℝ) :=
        div_le_div_of_nonneg_right hBrow hhpos.le
      _ ≤ (Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) / (h : ℝ) :=
        div_le_div_of_nonneg_right hrow hhpos.le
      _ = Ch ^ s * ((N : ℝ) ^ s / (h : ℝ) * (Real.log N) ^ (s * (s - 1))) := by
        ring
  exact ⟨hA, hB⟩

/--
Finish Piece III Σ_II CS core → harmonic × `sigmaIILogFactor`.
-/
theorem PieceIII_sigma_II_le_polylog (s N : ℕ) (δ X : ℝ) (Cpre Ch : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (_hδ : 0 < δ)
    (hCpre : 0 < Cpre) (hCh : 0 < Ch)
    (hH :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        Ch * (Real.log N) ^ (s - 1))
    (hcore :
      X ≤
        Cpre * Real.sqrt δ * (N : ℝ) * sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1)) :
    X ≤ Cpre * Ch ^ (s - 1) * Real.sqrt δ * (N : ℝ) ^ s *
          ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s) := by
  set E := sigmaIILogFactor N s
  set H := ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)
  have hHnonneg : 0 ≤ H :=
    Finset.sum_nonneg fun _ _ =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hharm : ((N : ℝ) * H) ^ (s - 1) ≤
      (Ch * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ (s - 1) := by
    refine pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hHnonneg) ?_ (s - 1)
    have := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg N)
    linarith
  have hpow :
      (Ch * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ (s - 1) =
        Ch ^ (s - 1) * (N : ℝ) ^ (s - 1) *
          (Real.log N) ^ ((s - 1) * (s - 1)) := by
    simp only [mul_pow]
    rw [← pow_mul]
  have hNpow : (N : ℝ) * (N : ℝ) ^ (s - 1) = (N : ℝ) ^ s := by
    have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
    calc
      (N : ℝ) * (N : ℝ) ^ (s - 1) = (N : ℝ) ^ ((s - 1) + 1) :=
        (pow_succ' _ _).symm
      _ = (N : ℝ) ^ s := by rw [Nat.sub_add_cancel hs1]
  calc
    X ≤ Cpre * Real.sqrt δ * (N : ℝ) * E * ((N : ℝ) * H) ^ (s - 1) := by
      simpa [E, H, mul_assoc] using hcore
    _ ≤ Cpre * Real.sqrt δ * (N : ℝ) * E *
          (Ch * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ (s - 1) := by
      have : 0 ≤ Cpre * Real.sqrt δ * (N : ℝ) * E :=
        mul_nonneg (mul_nonneg (mul_nonneg hCpre.le (Real.sqrt_nonneg _))
          (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
      gcongr
    _ = Cpre * Real.sqrt δ * (N : ℝ) * E *
          (Ch ^ (s - 1) * (N : ℝ) ^ (s - 1) *
            (Real.log N) ^ ((s - 1) * (s - 1))) := by
      rw [hpow]
    _ = Cpre * Ch ^ (s - 1) * Real.sqrt δ * ((N : ℝ) * (N : ℝ) ^ (s - 1)) *
          ((Real.log N) ^ ((s - 1) * (s - 1)) * E) := by
      ring
    _ = Cpre * Ch ^ (s - 1) * Real.sqrt δ * (N : ℝ) ^ s *
          ((Real.log N) ^ ((s - 1) * (s - 1)) * E) := by
      rw [hNpow]

/--
Scaled Σ_II on `PieceIIIFibres` exceptional fibres, constant may depend on `s`.
RHS keeps a `√Cd` from Cauchy--Schwarz on `|ℛ| ≤ Cd δ D`.
-/
theorem PieceIII_sigma_II_scaled_bound (d : ℕ) (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (δ : ℝ) (h : ℕ) (Cd : ℝ) (R R' : ℕ → Finset ℕ)
        (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hA : 1 ≤ A)
        (_hh1 : 1 ≤ h) (_hhN : h ≤ N) (_hCd : 0 < Cd),
        (∀ D : ℕ, 0 < D → ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) →
        (∀ D : ℕ, 0 < D → ((R' D).card : ℝ) ≤ Cd * δ * (D : ℝ)) →
        (∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
            if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
              J1FullWeightScaled k N h (by omega) else 0) ≤
          C * Real.sqrt Cd * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) ∧
        (∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
            if (k.colOffDiag ⟨0, by omega⟩) ∈ R' (k.rowOffDiag ⟨0, by omega⟩) then
              J1FullWeightScaled k N h (by omega) else 0) ≤
          C * Real.sqrt Cd * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) := by
  obtain ⟨Ch, hCh, hhall⟩ := tau_harmonic_partial_sum s hs
  obtain ⟨Cexp, hCexp, _hCexp4, hτall⟩ := tau_uniform_exp_bound
  refine ⟨Ch ^ (s - 1) * Real.sqrt 3, by positivity, ?_⟩
  intro N A δ h Cd R R' hN hδ _hA hh1 _hhN hCd hR hR'
  have h0 : 0 < s := by omega
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hh1)
  have hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cexp * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)) :=
    fun n hn hnN => hτall (s - 1) N n hN (by omega) hn hnN
  have hH := hhall N hN
  have hcore := PieceIII_sigma_II_le_delta_row_factor d s N δ R Cd Cexp
    hs hN hδ hCd hCexp hτ hR
  have hcore' := PieceIII_sigma_II_le_delta_row_factor_sym d s N δ R' Cd Cexp
    hs hN hδ hCd hCexp hτ hR'
  have hCpre : 0 < Real.sqrt (3 * Cd) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hCd)
  have hunscA :=
    PieceIII_sigma_II_le_polylog s N δ _ (Real.sqrt (3 * Cd)) Ch
      hs hN hδ hCpre hCh hH hcore
  have hunscB :=
    PieceIII_sigma_II_le_polylog s N δ _ (Real.sqrt (3 * Cd)) Ch
      hs hN hδ hCpre hCh hH hcore'
  have hsplit : Real.sqrt (3 * Cd) = Real.sqrt 3 * Real.sqrt Cd :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) Cd
  have hpack :
      Real.sqrt (3 * Cd) * Ch ^ (s - 1) =
        (Ch ^ (s - 1) * Real.sqrt 3) * Real.sqrt Cd := by
    rw [hsplit]; ring
  have hA :
      (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
          if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
            J1FullWeightScaled k N h h0 else 0) ≤
        (Ch ^ (s - 1) * Real.sqrt 3) * Real.sqrt Cd *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) := by
    have hdiv :=
      sum_ite_J1FullWeightScaled_eq_div (N := N)
        (PieceIIIFibres_A_lt_B s N h0)
        (fun k => k.rowOffDiag ⟨0, h0⟩ ∈ R (k.colOffDiag ⟨0, h0⟩)) h0 hhpos
    calc
      _ = (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) / (h : ℝ) := hdiv
      _ ≤ (Real.sqrt (3 * Cd) * Ch ^ (s - 1) * Real.sqrt δ * (N : ℝ) ^ s *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) /
              (h : ℝ) :=
        div_le_div_of_nonneg_right hunscA hhpos.le
      _ = (Ch ^ (s - 1) * Real.sqrt 3) * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) := by
        rw [hpack]; ring
  have hB :
      (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
          if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
            J1FullWeightScaled k N h h0 else 0) ≤
        (Ch ^ (s - 1) * Real.sqrt 3) * Real.sqrt Cd *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) := by
    have hdiv :=
      sum_ite_J1FullWeightScaled_eq_div (N := N)
        (PieceIIIFibres_B_lt_A s N h0)
        (fun k => k.colOffDiag ⟨0, h0⟩ ∈ R' (k.rowOffDiag ⟨0, h0⟩)) h0 hhpos
    calc
      _ = (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) / (h : ℝ) := hdiv
      _ ≤ (Real.sqrt (3 * Cd) * Ch ^ (s - 1) * Real.sqrt δ * (N : ℝ) ^ s *
            ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) /
              (h : ℝ) :=
        div_le_div_of_nonneg_right hunscB hhpos.le
      _ = (Ch ^ (s - 1) * Real.sqrt 3) * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) := by
        rw [hpack]; ring
  exact ⟨hA, hB⟩

/--
PDF: with exceptional sets from `g_h`, Σ_I / Σ_II give the scaled majorant.
Constants may depend on `s` and on the Lem5 factor `Cd`.
-/
theorem J1_scaled_sum_from_exceptional (d : ℕ) (s : ℕ) (hs : 2 ≤ s)
    (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ) (h : ℕ)
        (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hA : 1 ≤ A)
        (_hh1 : 1 ≤ h) (_hhN : h ≤ N)
        (R R' : ℕ → Finset ℕ),
        (∀ D : ℕ, 0 < D → ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) →
        (∀ D : ℕ, R D ⊆ Finset.Icc 1 (D - 1)) →
        (∀ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
          ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
            (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩) +
              (if (k.rowOffDiag ⟨0, by omega⟩) ∈
                  R (k.colOffDiag ⟨0, by omega⟩) then
                ((N : ℝ) / (h : ℝ)) / (k.colOffDiag ⟨0, by omega⟩)
              else 0)) →
        (∀ D : ℕ, 0 < D → ((R' D).card : ℝ) ≤ Cd * δ * (D : ℝ)) →
        (∀ D : ℕ, R' D ⊆ Finset.Icc 1 (D - 1)) →
        (∀ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
          ‖J1InnerSumScaled g k N A h (by omega)‖ ≤
            (2 * δ) * ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩) +
              (if (k.colOffDiag ⟨0, by omega⟩) ∈
                  R' (k.rowOffDiag ⟨0, by omega⟩) then
                ((N : ℝ) / (h : ℝ)) / (k.rowOffDiag ⟨0, by omega⟩)
              else 0)) →
        (_hδ1 : δ ≤ 1) →
        J1ScaledSumAtHeight d s N A g h ≤
          C * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
  obtain ⟨C_I, hC_I, hIall⟩ := PieceIII_sigma_I_scaled_bound s hs
  obtain ⟨C_II, hC_II, hIIall⟩ := PieceIII_sigma_II_scaled_bound d s hs
  refine ⟨4 * C_I + 2 * C_II * Real.sqrt Cd, by positivity, ?_⟩
  intro N A g δ h hN hδ hA hh1 hhN R R'
    hRcard _hRsub hpt hRcard' _hRsub' hpt' hδ1
  have h0 : 0 < s := by omega
  have h2δ : 0 < 2 * δ := by positivity
  have hside := J1_scaled_side_sum_A_lt_B g (2 * δ) h hs h2δ R hpt
  have hside' := J1_scaled_side_sum_B_lt_A g (2 * δ) h hs h2δ R' hpt'
  obtain ⟨hIA, hIB⟩ := hIall N A h hN hA hh1 hhN
  obtain ⟨hIIA, hIIB⟩ :=
    hIIall N A δ h Cd R R' hN hδ hA hh1 hhN hCd hRcard hRcard'
  have hpoly1 := log_pow_le_I1PieceIIIPolylog N s hN hs
  have hpoly2 := cs_factor_le_I1PieceIIIPolylog N s hN
  have hδsqrt := delta_le_sqrt_delta hδ.le hδ1
  have hAerr :
      (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
          J1FibreContributionScaled g k N A h h0) ≤
        (2 * C_I + C_II * Real.sqrt Cd) *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
    refine le_trans hside ?_
    have hδI :
        (2 * δ) * (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
              J1FullWeightScaled k N h h0) ≤
          (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            I1PieceIIIPolylog N s) := by
      calc
        (2 * δ) * (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
              J1FullWeightScaled k N h h0) ≤
            (2 * δ) * (C_I * ((N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1)))) :=
          mul_le_mul_of_nonneg_left hIA (by positivity)
        _ = (2 * C_I) * (δ * (N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by ring
        _ ≤ (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by
          have : 0 ≤ (2 * C_I) * ((N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by positivity
          gcongr
        _ ≤ (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              I1PieceIIIPolylog N s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpoly1 (by positivity)) (by positivity)
    have hIIerr :
        (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0) ≤
          C_II * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
      calc
        _ ≤ C_II * Real.sqrt Cd *
              (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
                ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) :=
          hIIA
        _ ≤ C_II * Real.sqrt Cd *
              (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpoly2 (by positivity))
            (mul_nonneg hC_II.le (Real.sqrt_nonneg _))
    calc
      (2 * δ) * (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            J1FullWeightScaled k N h h0) +
          (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0) ≤
        (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            I1PieceIIIPolylog N s) +
          C_II * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) :=
        add_le_add hδI hIIerr
      _ = (2 * C_I + C_II * Real.sqrt Cd) *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
        ring
  have hBerr :
      (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
          J1FibreContributionScaled g k N A h h0) ≤
        (2 * C_I + C_II * Real.sqrt Cd) *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
    refine le_trans hside' ?_
    have hδI :
        (2 * δ) * (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
              J1FullWeightScaled k N h h0) ≤
          (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            I1PieceIIIPolylog N s) := by
      calc
        (2 * δ) * (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
              J1FullWeightScaled k N h h0) ≤
            (2 * δ) * (C_I * ((N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1)))) :=
          mul_le_mul_of_nonneg_left hIB (by positivity)
        _ = (2 * C_I) * (δ * (N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by ring
        _ ≤ (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by
          have : 0 ≤ (2 * C_I) * ((N : ℝ) ^ s / (h : ℝ) *
              (Real.log N) ^ (s * (s - 1))) := by positivity
          gcongr
        _ ≤ (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
              I1PieceIIIPolylog N s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpoly1 (by positivity)) (by positivity)
    have hIIerr :
        (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0) ≤
          C_II * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
      calc
        _ ≤ C_II * Real.sqrt Cd *
              (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
                ((Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s)) :=
          hIIB
        _ ≤ C_II * Real.sqrt Cd *
              (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpoly2 (by positivity))
            (mul_nonneg hC_II.le (Real.sqrt_nonneg _))
    calc
      (2 * δ) * (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            J1FullWeightScaled k N h h0) +
          (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeightScaled k N h h0 else 0) ≤
        (2 * C_I) * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) *
            I1PieceIIIPolylog N s) +
          C_II * Real.sqrt Cd *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) :=
        add_le_add hδI hIIerr
      _ = (2 * C_I + C_II * Real.sqrt Cd) *
            (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
        ring
  have heq := PieceIII_A_eq_B_scaled_bound d s N A g h h0
  have hsplit := sum_scaled_contrib_split (g := g) (s := s) (N := N) (A := A)
    (h := h) h0 hs
  rw [hsplit, heq, add_zero]
  calc
    (∑ k ∈ PieceIIIFibres_A_lt_B s N h0,
          J1FibreContributionScaled g k N A h h0) +
        (∑ k ∈ PieceIIIFibres_B_lt_A s N h0,
          J1FibreContributionScaled g k N A h h0) ≤
      (2 * C_I + C_II * Real.sqrt Cd) *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) +
        (2 * C_I + C_II * Real.sqrt Cd) *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) :=
      add_le_add hAerr hBerr
    _ = (4 * C_I + 2 * C_II * Real.sqrt Cd) *
          (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
      ring

/--
Scaled Lemma 6 at height `h`. Constants may depend on `s`
(harmonic / divisor bounds).
-/
theorem J1_bound_scaled_height (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (_hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
          (_hA : 1 ≤ A) (h : ℕ) (_hh1 : 1 ≤ h) (_hhδ : (h : ℝ) * δ ^ 2 < 1),
          Real.rpow δ (-Cd) < (scaledHeadLo A h : ℝ) →
          (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd)) →
          (h ≤ N ∧
              altDiophantine d (N / h) (CirclePoly.compMul g h) δ Cd) ∨
            J1ScaledSumAtHeight d s N A g h ≤
              C * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
  obtain ⟨Cd, hEq, hCd5, hlem5⟩ := J1_lem5_exceptional_sets_scaled d
  refine ⟨Cd, hEq, by linarith, ?_⟩
  intro s hs
  have hCd : 0 < Cd := by linarith
  obtain ⟨C, hC, hsum⟩ := J1_scaled_sum_from_exceptional d s hs Cd hCd
  refine ⟨C, hC, ?_⟩
  intro N A g δ hN hδ hδ' hA h hh1 hhδ hA'lo hA'hi
  by_cases hhN : h ≤ N
  · rcases hlem5 s N A g δ h hs hN hδ hδ' hA hh1 hhδ hhN
        hA'lo hA'hi with hdio | hR
    · exact Or.inl ⟨hhN, hdio⟩
    · rcases hR with ⟨R, R', hRcard, hRsub, hpt, hRcard', hRsub', hpt'⟩
      exact Or.inr
        (hsum N A g δ h hN hδ hA hh1 hhN R R'
          hRcard hRsub hpt hRcard' hRsub' hpt'
          (le_of_lt (lt_trans hδ' (by norm_num))))
  · refine Or.inr ?_
    have hNlt : N < h := Nat.lt_of_not_ge hhN
    have hzero := J1ScaledSumAtHeight_eq_zero_of_h_gt_N d s N A g h hh1 hNlt
    rw [hzero]
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hh1)
    have hpoly : 0 ≤ I1PieceIIIPolylog N s := by
      dsimp [I1PieceIIIPolylog]
      positivity
    positivity

/--
Pointwise scaled `J1` at height `h`. Assembled from the matrix embedding +
scaled Lemma 6. Requires the A-window on `⌈A/h⌉`.
-/
theorem I1_piece_III_scaled_J1_at_h (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (_hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (_I : Finset (Fin s)) (_hN : 3 ≤ N)
          (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ _I) (_hIcard : 2 ≤ _I.card)
          (_hδ : 0 < δ) (_hδ' : δ < 1 / 8) (_hA : 1 ≤ A)
          (h : ℕ) (_hh1 : 1 ≤ h) (_hhδ : (h : ℝ) * δ ^ 2 < 1),
          Real.rpow δ (-Cd) < (scaledHeadLo A h : ℝ) →
          (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd)) →
          (h ≤ N ∧
              altDiophantine d (N / h) (CirclePoly.compMul g h) δ Cd) ∨
            I1PieceIIIScaledBlock d s N A g δ h ≤
              C * (Real.sqrt δ * (N : ℝ) ^ s / (h : ℝ) * I1PieceIIIPolylog N s) := by
  obtain ⟨Cd, hEq, hCd, hJ1⟩ := J1_bound_scaled_height d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C, hC, hJ1s⟩ := hJ1 s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ _I hN _hI0 _hIcard hδ hδ' hA h hh1 hhδ hA'lo hA'hi
  have hembed := I1PieceIIIScaledBlock_le_J1ScaledSum d s N A g δ hs hN hA h hh1
  rcases hJ1s N A g δ hN hδ hδ' hA h hh1 hhδ hA'lo hA'hi with hdio | hbound
  · exact Or.inl hdio
  · refine Or.inr (le_trans hembed hbound)

/--
Assembled fixed-`(T,e)` bound: combinatorial `τ` factor + scaled `J1`.
`Cd` is the Lem5 exponent. Ambient lower window is strengthened to `Cd+2`
so every height `h = eT` with `h δ² < 1` inherits `δ^(-Cd) < ⌈A/h⌉`;
upper window is `A < δ^(-(3+Cd))` (PDF `C_d' = C_d+1` slack; nonempty vs lower).
Diophantine alternative is at `Cd + 3d + 2`.
Used by `I1_piece_III_embed_J1` in `I1Bound.lean`.
-/
theorem I1_piece_III_fixed_Te_assembled (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (hN : 3 ≤ N)
          (hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) ∨
              (∀ T ∈ Finset.Icc 1 (N ^ (s - 1)),
                ∀ e ∈ Finset.Icc 1 (N ^ (s - 1)),
                  δ * (T : ℝ) < 1 →
                    δ * (e : ℝ) < 1 →
                      I1PieceIIIFixedSum d s N A g δ I (by omega) T e ≤
                        C * (tau (s - 1) T : ℝ) *
                          (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                            I1PieceIIIPolylog N s)) := by
  obtain ⟨Ccomb, hCcomb, hcomb⟩ := I1_piece_III_fixed_Te_comb d
  obtain ⟨Cd0, hEq, hCd0, hsc⟩ := I1_piece_III_scaled_J1_at_h d
  refine ⟨Cd0, hEq, hCd0, ?_⟩
  intro s hs
  obtain ⟨Csc, hCsc, hsc_s⟩ := hsc s hs
  refine ⟨Ccomb * Csc, mul_pos hCcomb hCsc, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi
  classical
  by_cases H :
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ N ∧ (h : ℝ) * δ ^ 2 < 1 ∧
        altDiophantine d (N / h) (CirclePoly.compMul g h) δ Cd0
  · obtain ⟨h, hh1, hhle, hhδ, hdio⟩ := H
    refine Or.inl ?_
    have hN1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 3) hN
    exact altDiophantine_of_compMul d N h g δ Cd0 hN1 hh1 hhle hδ hδ'
      hhδ hCd0 hdio
  · refine Or.inr ?_
    intro T hT e he hTδ heδ
    have h1T : 1 ≤ T := (Finset.mem_Icc.1 hT).1
    have h1e : 1 ≤ e := (Finset.mem_Icc.1 he).1
    have h1h : 1 ≤ e * T := by
      have : (1 : ℕ) * 1 ≤ e * T := Nat.mul_le_mul h1e h1T
      simpa using this
    have hhδ : ((e * T : ℕ) : ℝ) * δ ^ 2 < 1 := by
      have he0 : 0 ≤ δ * (e : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
      have ht0 : 0 ≤ δ * (T : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
      have hmul : (δ * (e : ℝ)) * (δ * (T : ℝ)) < (1 : ℝ) := by
        simpa using mul_lt_mul'' heδ hTδ he0 ht0
      convert hmul using 1
      simp [Nat.cast_mul, pow_two]
      ring
    set h := e * T
    have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one h1h
    have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 hh0
    have hδ1 : δ < 1 := lt_of_lt_of_le hδ' (by norm_num)
    have hh_lt : (h : ℝ) < Real.rpow δ (-(2 : ℝ)) :=
      h_lt_delta_inv_sq h δ hhpos hδ hδ1 hhδ
    have hAh : (A : ℝ) / (h : ℝ) ≤ (scaledHeadLo A h : ℝ) :=
      scaledHeadLo_cast_ge A h hh0
    -- Lower A'-window: `δ^(-(Cd0+2)) < A` and `h < δ^(-2)` ⇒ `δ^(-Cd0) < A/h ≤ A'`.
    have hA'lo : Real.rpow δ (-Cd0) < (scaledHeadLo A h : ℝ) := by
      have hpos2 : (0 : ℝ) < Real.rpow δ (-(2 : ℝ)) := Real.rpow_pos_of_pos hδ _
      have hposA : (0 : ℝ) < Real.rpow δ (-(Cd0 + 2)) := Real.rpow_pos_of_pos hδ _
      have hquot :
          Real.rpow δ (-(Cd0 + 2)) / Real.rpow δ (-(2 : ℝ)) <
            Real.rpow δ (-(Cd0 + 2)) / (h : ℝ) :=
        div_lt_div_of_pos_left hposA hhpos hh_lt
      have hrw :
          Real.rpow δ (-(Cd0 + 2)) / Real.rpow δ (-(2 : ℝ)) =
            Real.rpow δ (-Cd0) := by
        rw [div_eq_iff (ne_of_gt hpos2)]
        have hsum : -(Cd0 + 2) = (-Cd0) + (-(2 : ℝ)) := by ring
        calc
          Real.rpow δ (-(Cd0 + 2))
              = Real.rpow δ ((-Cd0) + (-(2 : ℝ))) := by rw [hsum]
          _ = Real.rpow δ (-Cd0) * Real.rpow δ (-(2 : ℝ)) :=
            Real.rpow_add hδ _ _
      have hdivA :
          Real.rpow δ (-(Cd0 + 2)) / (h : ℝ) < (A : ℝ) / (h : ℝ) :=
        div_lt_div_of_pos_right hAlo hhpos
      calc
        Real.rpow δ (-Cd0)
            = Real.rpow δ (-(Cd0 + 2)) / Real.rpow δ (-(2 : ℝ)) := hrw.symm
        _ < Real.rpow δ (-(Cd0 + 2)) / (h : ℝ) := hquot
        _ < (A : ℝ) / (h : ℝ) := hdivA
        _ ≤ (scaledHeadLo A h : ℝ) := hAh
    -- Upper A'-window: `A' ≤ A < δ^(-(3+Cd0))`.
    have hA'hi :
        (scaledHeadLo A h : ℝ) < Real.rpow δ (-(3 + Cd0)) := by
      have hA'le : (scaledHeadLo A h : ℝ) ≤ (A : ℝ) := by
        exact_mod_cast scaledHeadLo_le_A hA h1h
      exact lt_of_le_of_lt hA'le hAhi
    have hcomb' :=
      hcomb s N A g δ I hs hN hI0 hIcard hδ hδ' hA T e hT he hTδ heδ
    have hblock0 :=
      hsc_s N A g δ I hN hI0 hIcard hδ hδ' hA h h1h hhδ hA'lo hA'hi
    have hblock' :
        I1PieceIIIScaledBlock d s N A g δ h ≤
          Csc * (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
            I1PieceIIIPolylog N s) := by
      rcases hblock0 with hdio | hbound
      · exact False.elim (H ⟨h, h1h, hdio.1, hhδ, hdio.2⟩)
      · simpa [h, Nat.cast_mul] using hbound
    have hstep :
        Ccomb * (tau (s - 1) T : ℝ) * I1PieceIIIScaledBlock d s N A g δ h ≤
          Ccomb * (tau (s - 1) T : ℝ) *
            (Csc * (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
              I1PieceIIIPolylog N s)) :=
      mul_le_mul_of_nonneg_left hblock'
        (mul_nonneg hCcomb.le (Nat.cast_nonneg _))
    calc
      I1PieceIIIFixedSum d s N A g δ I (by omega) T e
          ≤ Ccomb * (tau (s - 1) T : ℝ) *
              I1PieceIIIScaledBlock d s N A g δ h := by
                simpa [h] using hcomb'
      _ ≤ Ccomb * (tau (s - 1) T : ℝ) *
            (Csc * (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
              I1PieceIIIPolylog N s)) := hstep
      _ = (Ccomb * Csc) * (tau (s - 1) T : ℝ) *
            (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
              I1PieceIIIPolylog N s) := by ring

end RMFLean
