/-
Piece I / II card majorants: fixed-`(T,e,k)` package overcount.
-/
import RMFLean.Proof.Intersection.I1PieceIComb

noncomputable section

open Classical BigOperators Real

namespace RMFLean

set_option maxHeartbeats 800000

/-! ### Cofactor `m = m₁'(Q/e)` -/

def IntersectionOuter.mCofactor {s : ℕ} (ν : IntersectionOuter s)
    (h0 : 0 < s) (e : ℕ) : ℕ :=
  ν.m1' * (ν.Q h0 / e)

theorem I1Outer_nProd_eq_eT_mCofactor {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ)
    (he : e ∈ (ν.Q h0).divisors) :
    ν.nProd h0 = e * ν.T h0 * ν.mCofactor h0 e := by
  have hQdvd := Nat.dvd_of_mem_divisors he
  rw [I1Outer_nProd_eq hν, IntersectionOuter.mCofactor]
  calc
    ν.T h0 * ν.m1' * ν.Q h0
        = ν.T h0 * ν.m1' * (e * (ν.Q h0 / e)) := by
          rw [Nat.mul_div_cancel' hQdvd]
    _ = e * ν.T h0 * (ν.m1' * (ν.Q h0 / e)) := by ring

theorem I1Outer_nTail0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.nTail ⟨0, h0⟩ = 1 := by
  rcases Finset.mem_image.1 hν with ⟨x, _, rfl⟩
  exact toIntersectionCanon_nTail0 x h0

theorem I1Outer_m0' {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.m' ⟨0, h0⟩ = ν.m1' := by
  rcases Finset.mem_image.1 hν with ⟨x, _, rfl⟩
  exact toIntersectionCanon_m0' x h0

/-- Explicit cofactor ordered-factor coordinates. -/
noncomputable def cofactorFactor {s : ℕ} (h0 : 0 < s)
    (m1' : ℕ) (m' : Fin s → ℕ) (e : ℕ) (i : Fin s) : ℕ :=
  if hi0 : i = ⟨0, h0⟩ then m1'
  else
    let j : Fin (s - 1) := ⟨i.val - 1, by
      have : i.val ≠ 0 := fun hval => hi0 (Fin.ext hval)
      omega⟩
    restrictTailM' h0 m' j / extractFactors (s - 1) e (restrictTailM' h0 m') j

/-- Ordered `s`-factorisation of the cofactor `m₁'(Q/e)`. -/
def I1Outer.toOrderedFactorsR {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ)
    (he : e ∈ (ν.Q h0).divisors) :
    OrderedFactors s (ν.mCofactor h0 e) := by
  set ftail := restrictTailM' h0 ν.m'
  set fa := extractFactors (s - 1) e ftail
  have hQpos := I1Outer_Q_pos hν
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have hbpos : 0 < ν.Q h0 / e :=
    Nat.div_pos (Nat.le_of_dvd hQpos (Nat.dvd_of_mem_divisors he)) hepos
  have hfpos : ∀ j, 0 < ftail j := fun j =>
    I1Outer_m'_pos hν (by
      intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _))
  have hprod_tail : (∏ j, ftail j) = e * (ν.Q h0 / e) := by
    have hQ : (∏ j, ftail j) = ν.Q h0 := by
      simp [ftail, restrictTailM'_prod, IntersectionOuter.Q]
    rw [hQ, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  have hspec :=
    extractFactors_spec (s - 1) e (ν.Q h0 / e) ftail hbpos hfpos hprod_tail
  let f : Fin s → ℕ := cofactorFactor h0 ν.m1' ν.m' e
  have hfpos' : ∀ i, 0 < f i := by
    intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · simpa [f, cofactorFactor, hi0] using I1Outer.m1'_pos hν
    · simpa [f, cofactorFactor, hi0, fa, ftail] using hspec.2.2.2.2
        ⟨i.val - 1, by
          have : i.val ≠ 0 := fun hval => hi0 (Fin.ext hval)
          omega⟩
  have hprod' : (∏ i, f i) = ν.mCofactor h0 e := by
    have hmem : (⟨0, h0⟩ : Fin s) ∈ (Finset.univ : Finset (Fin s)) :=
      Finset.mem_univ _
    rw [← Finset.prod_erase_mul _ _ hmem]
    have h0f : f ⟨0, h0⟩ = ν.m1' := by simp [f, cofactorFactor]
    have htail :
        (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), f i) = ν.Q h0 / e := by
      let ι : Fin (s - 1) ↪ Fin s :=
        ⟨fun j => ⟨j.val + 1, by omega⟩, by
          intro a b h; exact Fin.ext (Nat.succ.inj (congrArg Fin.val h))⟩
      have hmap :
          Finset.univ.erase (⟨0, h0⟩ : Fin s) =
            (Finset.univ : Finset (Fin (s - 1))).map ι := by
        ext i; constructor
        · intro hi
          have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
          have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h =>
            hi0 (Fin.ext h))
          refine Finset.mem_map.2 ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
          apply Fin.ext
          simp [ι]
          omega
        · intro hi
          rcases Finset.mem_map.1 hi with ⟨j, _, rfl⟩
          exact Finset.mem_erase.2 ⟨by
            intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _),
            Finset.mem_univ _⟩
      rw [hmap, Finset.prod_map]
      have hfa : (∏ j : Fin (s - 1), f (ι j)) =
          ∏ j : Fin (s - 1), (ftail j / fa j) := by
        refine Fintype.prod_congr _ _ fun j => ?_
        have hj0 : ι j ≠ ⟨0, h0⟩ := by
          intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _)
        simp [f, cofactorFactor, ι, fa, ftail]
      rw [hfa]
      simpa [fa, ftail] using hspec.2.2.1
    simp [IntersectionOuter.mCofactor, h0f, htail, Nat.mul_comm]
  exact ⟨f, ⟨hfpos', hprod'⟩⟩

theorem I1Outer.toOrderedFactorsR_val {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ)
    (he : e ∈ (ν.Q h0).divisors) :
    (I1Outer.toOrderedFactorsR hν e he).val =
      cofactorFactor h0 ν.m1' ν.m' e :=
  rfl

theorem I1Outer.toOrderedFactorsE_val {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ)
    (he : e ∈ (ν.Q h0).divisors) :
    (I1Outer.toOrderedFactorsE hν e he).val =
      extractFactors (s - 1) e (restrictTailM' h0 ν.m') :=
  rfl

theorem I1Outer.toOrderedFactorsN_val {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (I1Outer.toOrderedFactorsN hν).val =
      fun i => if i = ⟨0, h0⟩ then ν.n1' else ν.nTail i :=
  rfl

theorem I1Outer_mCofactor_le_X {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {e k : ℕ}
    (he : 1 ≤ e) (hk : 1 ≤ k)
    (hb : e * k ∈ fibreB s N A ν h0)
    (hediv : e ∈ (ν.Q h0).divisors) :
    ν.mCofactor h0 e ≤ N ^ s / (e ^ 2 * k * ν.T h0 ^ 2) := by
  have hTpos : 0 < ν.T h0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 (I1Outer_T_mem_Icc hν)).1
  have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he
  have hn := I1Outer_nProd_le_of_mem_box hν he hk hb
  have hEq := I1Outer_nProd_eq_eT_mCofactor hν e hediv
  have hdenpos : 0 < e * ν.T h0 := Nat.mul_pos hepos hTpos
  have hm : ν.mCofactor h0 e = ν.nProd h0 / (e * ν.T h0) := by
    have hmul : ν.nProd h0 = ν.mCofactor h0 e * (e * ν.T h0) := by
      rw [hEq]; ring
    exact (Nat.div_eq_of_eq_mul_left hdenpos hmul).symm
  have hbound : ν.nProd h0 / (e * ν.T h0) ≤
      (N ^ s / (e * k * ν.T h0)) / (e * ν.T h0) :=
    Nat.div_le_div_right hn
  have hsimp : (N ^ s / (e * k * ν.T h0)) / (e * ν.T h0) =
      N ^ s / (e * k * ν.T h0 * (e * ν.T h0)) :=
    Nat.div_div_eq_div_mul _ _ _
  have hden : e * k * ν.T h0 * (e * ν.T h0) = e ^ 2 * k * ν.T h0 ^ 2 := by
    ring
  rw [hm]
  exact hbound.trans_eq (hsimp.trans (by rw [hden]))

/-! ### Fixed-`(T,e,k)` package overcount -/

def I1PieceIFixedK (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s)
    (T e k : ℕ) : Finset (IntersectionOuter s) :=
  (I1Outer (s := s) (N := N) A I h0).filter fun ν =>
    ν.T h0 = T ∧ e ∈ (ν.Q h0).divisors ∧ e * k ∈ fibreB s N A ν h0

abbrev I1PieceIPackage (s T e m : ℕ) : Type :=
  OrderedFactors (s - 1) T ×
    OrderedFactors (s - 1) e ×
      OrderedFactors s (e * T * m) ×
        OrderedFactors s m

theorem card_I1PieceIPackage (s T e m : ℕ) :
    Fintype.card (I1PieceIPackage s T e m) =
      tau (s - 1) T * tau (s - 1) e * tau s (e * T * m) * tau s m := by
  unfold I1PieceIPackage
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp [tau, mul_assoc]

theorem OrderedFactors.cast_val {k n n' : Nat} (h : n = n')
    (f : OrderedFactors k n) : ((Eq.recOn h f) : OrderedFactors k n').val = f.val := by
  subst h; rfl

/-- Rebuild an outer parameter from its ordered-factor package. -/
def recoverOuterFromPackage {s : ℕ} (h0 : 0 < s) {T e m : ℕ}
    (p : I1PieceIPackage s T e m) : IntersectionOuter s where
  t := embedTailTvec h0 p.1.val
  n1' := p.2.2.1.val ⟨0, h0⟩
  m1' := p.2.2.2.val ⟨0, h0⟩
  nTail := fun i => if i = ⟨0, h0⟩ then 1 else p.2.2.1.val i
  m' := fun i =>
    if hi0 : i = ⟨0, h0⟩ then p.2.2.2.val ⟨0, h0⟩
    else
      let j : Fin (s - 1) := ⟨i.val - 1, by
        have : i.val ≠ 0 := fun hval => hi0 (Fin.ext hval)
        omega⟩
      p.2.1.val j * p.2.2.2.val i

noncomputable def I1PieceIFixedK.packageOf {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {T e k : ℕ} {ν : IntersectionOuter s}
    (hνmem : ν ∈ I1PieceIFixedK s N A I h0 T e k) :
    Σ m : ℕ, I1PieceIPackage s T e m := by
  have hν : ν ∈ I1Outer (s := s) (N := N) A I h0 :=
    (Finset.mem_filter.1 hνmem).1
  have hT : ν.T h0 = T := (Finset.mem_filter.1 hνmem).2.1
  have hediv : e ∈ (ν.Q h0).divisors := (Finset.mem_filter.1 hνmem).2.2.1
  refine ⟨ν.mCofactor h0 e, ?_⟩
  refine ⟨I1Outer.toOrderedFactors hν T hT,
    I1Outer.toOrderedFactorsE hν e hediv, ?_,
    I1Outer.toOrderedFactorsR hν e hediv⟩
  have hEq : ν.nProd h0 = e * T * ν.mCofactor h0 e := by
    simpa [hT] using I1Outer_nProd_eq_eT_mCofactor hν e hediv
  exact hEq ▸ I1Outer.toOrderedFactorsN hν

theorem I1PieceIFixedK.packageOf_m_mem {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {T e k : ℕ} {ν : IntersectionOuter s}
    (hνmem : ν ∈ I1PieceIFixedK s N A I h0 T e k)
    (he : 1 ≤ e) (hk : 1 ≤ k) :
    (I1PieceIFixedK.packageOf hνmem).1 ∈
      Finset.Icc 1 (N ^ s / (e ^ 2 * k * T ^ 2)) := by
  have hν : ν ∈ I1Outer (s := s) (N := N) A I h0 :=
    (Finset.mem_filter.1 hνmem).1
  have hT : ν.T h0 = T := (Finset.mem_filter.1 hνmem).2.1
  have hediv : e ∈ (ν.Q h0).divisors := (Finset.mem_filter.1 hνmem).2.2.1
  have hb : e * k ∈ fibreB s N A ν h0 := (Finset.mem_filter.1 hνmem).2.2.2
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · exact Nat.succ_le_of_lt <|
      Nat.mul_pos (I1Outer.m1'_pos hν)
        (Nat.div_pos (Nat.le_of_dvd (I1Outer_Q_pos hν)
          (Nat.dvd_of_mem_divisors hediv)) (lt_of_lt_of_le Nat.zero_lt_one he))
  · simpa [I1PieceIFixedK.packageOf, hT] using
      I1Outer_mCofactor_le_X hν he hk hb hediv

theorem recover_packageOf {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {T e k : ℕ} {ν : IntersectionOuter s}
    (hνmem : ν ∈ I1PieceIFixedK s N A I h0 T e k) :
    recoverOuterFromPackage h0 (I1PieceIFixedK.packageOf hνmem).2 = ν := by
  have hν : ν ∈ I1Outer (s := s) (N := N) A I h0 :=
    (Finset.mem_filter.1 hνmem).1
  have hT : ν.T h0 = T := (Finset.mem_filter.1 hνmem).2.1
  have hediv : e ∈ (ν.Q h0).divisors := (Finset.mem_filter.1 hνmem).2.2.1
  have ht0 := I1Outer_t0 hν
  have hn0 := I1Outer_nTail0 hν
  have hm0 := I1Outer_m0' hν
  set fT := I1Outer.toOrderedFactors hν T hT
  set fE := I1Outer.toOrderedFactorsE hν e hediv
  set fR := I1Outer.toOrderedFactorsR hν e hediv
  have hEq : ν.nProd h0 = e * T * ν.mCofactor h0 e := by
    simpa [hT] using I1Outer_nProd_eq_eT_mCofactor hν e hediv
  set fN : OrderedFactors s (e * T * ν.mCofactor h0 e) :=
    hEq ▸ I1Outer.toOrderedFactorsN hν
  have hpkg : (I1PieceIFixedK.packageOf hνmem).2 = (fT, fE, fN, fR) := by
    simp [I1PieceIFixedK.packageOf, fT, fE, fN, fR]
  rw [hpkg]
  apply IntersectionOuter.ext
  · exact embed_restrictTailTvec h0 ν.t ht0
  · have hfNval : fN.val =
        (fun i => if i = ⟨0, h0⟩ then ν.n1' else ν.nTail i) := by
      have : fN.val = (I1Outer.toOrderedFactorsN hν).val :=
        OrderedFactors.cast_val hEq (I1Outer.toOrderedFactorsN hν)
      simpa [I1Outer.toOrderedFactorsN_val] using this
    simpa [recoverOuterFromPackage, hfNval]
  · have : fR.val ⟨0, h0⟩ = ν.m1' := by
      simp [fR, I1Outer.toOrderedFactorsR_val, cofactorFactor]
    simpa [recoverOuterFromPackage] using this
  · have hfNval : fN.val =
        (fun i => if i = ⟨0, h0⟩ then ν.n1' else ν.nTail i) := by
      have : fN.val = (I1Outer.toOrderedFactorsN hν).val :=
        OrderedFactors.cast_val hEq (I1Outer.toOrderedFactorsN hν)
      simpa [I1Outer.toOrderedFactorsN_val] using this
    funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0; simpa [recoverOuterFromPackage] using hn0.symm
    · simp [recoverOuterFromPackage, hfNval, hi0]
  · funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      simp [recoverOuterFromPackage, fR, I1Outer.toOrderedFactorsR_val,
        cofactorFactor, hm0]
    · set j : Fin (s - 1) := ⟨i.val - 1, by
        have : i.val ≠ 0 := fun hval => hi0 (Fin.ext hval)
        omega⟩
      have hfpos : ∀ u, 0 < restrictTailM' h0 ν.m' u := fun u =>
        I1Outer_m'_pos hν (by
          intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _))
      have hbpos : 0 < ν.Q h0 / e :=
        Nat.div_pos (Nat.le_of_dvd (I1Outer_Q_pos hν)
          (Nat.dvd_of_mem_divisors hediv)) (Nat.pos_of_mem_divisors hediv)
      have hprod : (∏ u, restrictTailM' h0 ν.m' u) = e * (ν.Q h0 / e) := by
        have : (∏ u, restrictTailM' h0 ν.m' u) = ν.Q h0 := by
          simp [restrictTailM'_prod, IntersectionOuter.Q]
        rw [this, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hediv)]
      have hspec :=
        extractFactors_spec (s - 1) e (ν.Q h0 / e)
          (restrictTailM' h0 ν.m') hbpos hfpos hprod
      have hfa : fE.val j =
          extractFactors (s - 1) e (restrictTailM' h0 ν.m') j := by
        simp [fE, I1Outer.toOrderedFactorsE_val]
      have hr : fR.val i =
          restrictTailM' h0 ν.m' j /
            extractFactors (s - 1) e (restrictTailM' h0 ν.m') j := by
        simp [fR, I1Outer.toOrderedFactorsR_val, cofactorFactor, hi0, j]
      have hmi : restrictTailM' h0 ν.m' j = ν.m' i := by
        simp [restrictTailM', j]
        congr 1; apply Fin.ext; simp
        have : i.val ≠ 0 := fun hval => hi0 (Fin.ext hval)
        omega
      have hrec : ν.m' i =
          extractFactors (s - 1) e (restrictTailM' h0 ν.m') j *
            (restrictTailM' h0 ν.m' j /
              extractFactors (s - 1) e (restrictTailM' h0 ν.m') j) := by
        rw [← hmi]
        exact (Nat.mul_div_cancel' (hspec.1 j)).symm
      simp only [recoverOuterFromPackage, hi0, ↓reduceDIte]
      rw [hfa, hr, hrec]

theorem I1PieceIFixedK.packageOf_inj {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {T e k : ℕ} (_he : 1 ≤ e) :
    ∀ {ν₁ ν₂ : IntersectionOuter s}
      (h₁ : ν₁ ∈ I1PieceIFixedK s N A I h0 T e k)
      (h₂ : ν₂ ∈ I1PieceIFixedK s N A I h0 T e k),
      I1PieceIFixedK.packageOf h₁ = I1PieceIFixedK.packageOf h₂ → ν₁ = ν₂ := by
  intro ν₁ ν₂ h₁ h₂ hpkg
  rw [← recover_packageOf h₁, ← recover_packageOf h₂]
  revert hpkg
  generalize hσ₁ : I1PieceIFixedK.packageOf h₁ = σ₁
  generalize hσ₂ : I1PieceIFixedK.packageOf h₂ = σ₂
  intro hpkg
  rcases σ₁ with ⟨m₁, p₁⟩
  rcases σ₂ with ⟨m₂, p₂⟩
  dsimp only at hpkg ⊢
  injection hpkg with hm hp
  subst hm
  exact congrArg (recoverOuterFromPackage h0) (eq_of_heq hp)

theorem I1PieceIFixedK_card_le {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} (T e k : ℕ) (_hs : 2 ≤ s) (_hN : 3 ≤ N)
    (_hT : 1 ≤ T) (he : 1 ≤ e) (hk : 1 ≤ k) :
    ((I1PieceIFixedK s N A I h0 T e k).card : ℝ) ≤
      (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
        ∑ m ∈ Finset.Icc 1 (N ^ s / (e ^ 2 * k * T ^ 2)),
          (tau s (e * T * m) : ℝ) * (tau s m : ℝ) := by
  classical
  set X := N ^ s / (e ^ 2 * k * T ^ 2)
  set S := I1PieceIFixedK s N A I h0 T e k
  let pkgType := Σ m : ↥(Finset.Icc 1 X), I1PieceIPackage s T e m.1
  let φ : S → pkgType := fun νmem =>
    ⟨⟨(I1PieceIFixedK.packageOf νmem.property).1,
        I1PieceIFixedK.packageOf_m_mem νmem.property he hk⟩,
      (I1PieceIFixedK.packageOf νmem.property).2⟩
  have hinj : Function.Injective φ := by
    intro a b hφ
    refine Subtype.ext ?_
    refine I1PieceIFixedK.packageOf_inj he a.property b.property ?_
    have ⟨hsub, hp⟩ := Sigma.ext_iff.mp hφ
    have hm : (I1PieceIFixedK.packageOf a.property).1 =
        (I1PieceIFixedK.packageOf b.property).1 :=
      congrArg Subtype.val hsub
    exact Sigma.ext hm (by simpa [φ] using hp)
  have hle : (S.card : ℝ) ≤ (Fintype.card pkgType : ℝ) := by
    have := Fintype.card_le_of_injective φ hinj
    simpa [Fintype.card_coe S] using this
  have hcard_pkg :
      (Fintype.card pkgType : ℝ) =
        (tau (s - 1) T : ℝ) * (tau (s - 1) e : ℝ) *
          ∑ m ∈ Finset.Icc 1 X, (tau s (e * T * m) : ℝ) * (tau s m : ℝ) := by
    simp only [pkgType, Fintype.card_sigma, card_I1PieceIPackage]
    have hsum :
        (∑ m : ↥(Finset.Icc 1 X),
            (tau (s - 1) T * tau (s - 1) e * tau s (e * T * (m : ℕ)) *
              tau s (m : ℕ) : ℕ)) =
          tau (s - 1) T * tau (s - 1) e *
            ∑ m ∈ Finset.Icc 1 X, tau s (e * T * m) * tau s m := by
      rw [Finset.sum_coe_sort (s := Finset.Icc 1 X)
        (f := fun m =>
          tau (s - 1) T * tau (s - 1) e * tau s (e * T * (m : ℕ)) *
            tau s (m : ℕ))]
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsum
    simpa [Nat.cast_sum, Nat.cast_mul] using hcast
  exact hle.trans_eq hcard_pkg

end RMFLean
