/-
Piece III combinatorial packaging: group outer `t`-factorisations of a fixed
product `T` (at most `τ_{s-1}(T)` many) and pass to a height-`h = e T` block.
-/
import RMFLean.Proof.Intersection.I1
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

open Classical BigOperators Complex

namespace RMFLean

/-! ### Tail `t`-vector ↔ ordered factorisation -/

/-- Embed an `(s-1)`-factorisation as a `Fin s → ℕ` `t`-vector (dummy at `0`). -/
def embedTailTvec {s : ℕ} (h0 : 0 < s) (f : Fin (s - 1) → ℕ) : Fin s → ℕ :=
  fun i =>
    if hi0 : i = ⟨0, h0⟩ then 1
    else
      f ⟨i.val - 1, by
        have hi : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        have : i.val < s := i.isLt
        omega⟩

/-- Restrict a `t`-vector to its `(s-1)` tail factors. -/
def restrictTailTvec {s : ℕ} (h0 : 0 < s) (tVec : Fin s → ℕ) : Fin (s - 1) → ℕ :=
  fun j => tVec ⟨j.val + 1, by omega⟩

theorem restrict_embedTailTvec {s : ℕ} (h0 : 0 < s) (f : Fin (s - 1) → ℕ) :
    restrictTailTvec h0 (embedTailTvec h0 f) = f := by
  funext j
  simp only [restrictTailTvec, embedTailTvec]
  have hj0 : (⟨j.val + 1, by omega⟩ : Fin s) ≠ ⟨0, h0⟩ := by
    intro h
    have : j.val + 1 = 0 := congrArg Fin.val h
    omega
  simp [hj0]

theorem embed_restrictTailTvec {s : ℕ} (h0 : 0 < s) (tVec : Fin s → ℕ)
    (ht0 : tVec ⟨0, h0⟩ = 1) :
    embedTailTvec h0 (restrictTailTvec h0 tVec) = tVec := by
  funext i
  by_cases hi0 : i = ⟨0, h0⟩
  · subst hi0; simpa [embedTailTvec] using ht0.symm
  · simp only [embedTailTvec, hi0, ↓reduceDIte, restrictTailTvec]
    congr 1
    refine Fin.ext ?_
    have hi : 0 < i.val :=
      Nat.pos_of_ne_zero fun h => hi0 (Fin.ext h)
    exact Nat.sub_add_cancel hi

private theorem erase_zero_eq_map_succ (n : ℕ) :
    Finset.univ.erase (0 : Fin (n + 1)) =
      (Finset.univ : Finset (Fin n)).map ⟨Fin.succ, Fin.succ_injective n⟩ := by
  ext i
  constructor
  · intro hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
    refine Finset.mem_map.2 ⟨i.pred hi0, Finset.mem_univ _, Fin.succ_pred i hi0⟩
  · intro hi
    rcases Finset.mem_map.1 hi with ⟨j, _, rfl⟩
    exact Finset.mem_erase.2 ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩

theorem restrictTailTvec_prod {s : ℕ} (h0 : 0 < s) (tVec : Fin s → ℕ) :
    (∏ j : Fin (s - 1), restrictTailTvec h0 tVec j) =
      ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), tVec i := by
  classical
  cases s with
  | zero => exact (Nat.not_lt_zero _ h0).elim
  | succ n =>
    change (∏ j : Fin n, tVec j.succ) =
      ∏ i ∈ Finset.univ.erase (0 : Fin (n + 1)), tVec i
    rw [erase_zero_eq_map_succ n, Finset.prod_map]
    exact Fintype.prod_congr _ _ fun _ => rfl

theorem embedTailTvec_T {s : ℕ} (h0 : 0 < s) (T : ℕ) (f : OrderedFactors (s - 1) T) :
    (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), embedTailTvec h0 f.val i) = T := by
  have h := restrictTailTvec_prod h0 (embedTailTvec h0 f.val)
  rw [← h, restrict_embedTailTvec]
  exact f.property.2

theorem I1Outer_t_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) : 0 < ν.t i := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
  have heq : (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i = x.m i := by
    simpa [IntersectionCanon.reconM, hi0] using hrecon
  have hm1 : 1 ≤ x.m i := (x.hm i).1
  have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i :=
    lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm1)
  exact Nat.pos_of_mul_pos_right hmul_pos

theorem I1Outer_t0 {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.t ⟨0, h0⟩ = 1 := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  exact toIntersectionCanon_t0 x h0

/-- Ordered factorisation recovered from an outer `t`-vector with product `T`. -/
def I1Outer.toOrderedFactors {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (T : ℕ)
    (hT : ν.T h0 = T) : OrderedFactors (s - 1) T :=
  ⟨restrictTailTvec h0 ν.t, by
    refine ⟨fun j => I1Outer_t_pos hν (by
      intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _)), ?_⟩
    have hprod := restrictTailTvec_prod h0 ν.t
    simpa [hprod, IntersectionOuter.T, hT]⟩

/-! ### Single-`t` blocks and height-`h` majorant -/

/-- Contribution of outer parameters with a fixed `t`-vector. -/
def I1PieceIIITvecSum (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (tVec : Fin s → ℕ) (e : ℕ) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => ν.t = tVec ∧ δ * (ν.T h0 : ℝ) < 1,
    if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
      ‖I1BoxSum g N A h0 ν e‖ else 0

/-- Candidate values for the height-`h` majorant. -/
noncomputable def I1PieceIIIScaledBlockCandidates
    (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ) (h : ℕ) : Finset ℝ :=
  if hs : 2 ≤ s then
    (Finset.univ : Finset (Finset (Fin s))).biUnion fun I =>
      (Finset.Icc 1 (max h 1)).biUnion fun e =>
        if he : e ∣ h then
          let T := h / e
          (Finset.univ : Finset (OrderedFactors (s - 1) T)).image fun f =>
            I1PieceIIITvecSum d s N A g δ I (by omega)
              (embedTailTvec (by omega) f.val) e
        else
          (∅ : Finset ℝ)
  else
    (∅ : Finset ℝ)

/--
Majorant for the PDF matrix contribution at fixed height `h = e T`
(`eq:piece-III-matrix`), before the scaled `J1` estimate.
-/
noncomputable def I1PieceIIIScaledBlock (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (h : ℕ) : ℝ :=
  (I1PieceIIIScaledBlockCandidates d s N A g δ h).fold max 0 id

theorem I1PieceIIIScaledBlock_nonneg (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (h : ℕ) : 0 ≤ I1PieceIIIScaledBlock d s N A g δ h := by
  classical
  simp only [I1PieceIIIScaledBlock]
  refine Finset.induction_on (I1PieceIIIScaledBlockCandidates d s N A g δ h)
    (by simp) ?_
  intro a s ha ih
  simp only [Finset.fold_insert ha, id]
  exact le_max_of_le_right ih

theorem fold_max_mem_le (s : Finset ℝ) {t : ℝ} (ht : t ∈ s) :
    t ≤ s.fold max 0 id := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => exact (Finset.notMem_empty t ht).elim
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    change t ≤ max (id a) (Finset.fold max 0 id s)
    rcases Finset.mem_insert.1 ht with rfl | ht'
    · exact le_max_left _ _
    · exact le_trans (ih ht') (le_max_right _ _)

theorem I1PieceIIITvecSum_mem_candidates
    (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (hs : 2 ≤ s) (T e : ℕ) (heT : 1 ≤ e * T)
    (f : OrderedFactors (s - 1) T) :
    I1PieceIIITvecSum d s N A g δ I (by omega)
        (embedTailTvec (by omega) f.val) e ∈
      I1PieceIIIScaledBlockCandidates d s N A g δ (e * T) := by
  classical
  set h := e * T
  have hepos : 0 < e := Nat.pos_of_mul_pos_right (lt_of_lt_of_le Nat.zero_lt_one heT)
  have hTeq : h / e = T := Nat.mul_div_cancel_left T hepos
  have hedvd : e ∣ h := ⟨T, rfl⟩
  have heIcc : e ∈ Finset.Icc 1 (max h 1) := by
    refine Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hepos, ?_⟩
    exact (Nat.le_mul_of_pos_right e
      (Nat.pos_of_mul_pos_left (lt_of_lt_of_le Nat.zero_lt_one heT))).trans
      (le_max_left _ _)
  simp only [I1PieceIIIScaledBlockCandidates, hs, ↓reduceDIte]
  refine Finset.mem_biUnion.2 ⟨I, Finset.mem_univ _, ?_⟩
  refine Finset.mem_biUnion.2 ⟨e, heIcc, ?_⟩
  simp only [hedvd, ↓reduceDIte]
  let f' : OrderedFactors (s - 1) (h / e) :=
    ⟨f.val, by simpa [hTeq] using f.property⟩
  refine Finset.mem_image.2 ⟨f', Finset.mem_univ _, rfl⟩

theorem I1PieceIIITvecSum_le_scaledBlock
    (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (hs : 2 ≤ s) (T e : ℕ) (heT : 1 ≤ e * T)
    (f : OrderedFactors (s - 1) T) :
    I1PieceIIITvecSum d s N A g δ I (by omega)
        (embedTailTvec (by omega) f.val) e ≤
      I1PieceIIIScaledBlock d s N A g δ (e * T) := by
  have hmem := I1PieceIIITvecSum_mem_candidates d s N A g δ I hs T e heT f
  simpa [I1PieceIIIScaledBlock] using
    fold_max_mem_le (I1PieceIIIScaledBlockCandidates d s N A g δ (e * T)) hmem

/-- Fixed-`(T,e)` sum equals the sum over ordered `t`-factorisations of `T`. -/
theorem I1PieceIIIFixedSum_eq_sum_tvec
    (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ) :
    I1PieceIIIFixedSum d s N A g δ I h0 T e =
      ∑ f : OrderedFactors (s - 1) T,
        I1PieceIIITvecSum d s N A g δ I h0 (embedTailTvec h0 f.val) e := by
  classical
  set Outer := I1Outer (s := s) (N := N) A I h0
  set F := Outer.filter fun ν => ν.T h0 = T ∧ δ * (ν.T h0 : ℝ) < 1
  set w : IntersectionOuter s → ℝ := fun ν =>
    ite (e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1)
      ‖I1BoxSum g N A h0 ν e‖ 0
  have hLHS : I1PieceIIIFixedSum d s N A g δ I h0 T e = ∑ ν ∈ F, w ν := by
    simp only [I1PieceIIIFixedSum, F, Outer, w]
  -- Bound via fiber cardinality: each term of FixedSum is ≤ ScaledBlock after
  -- regrouping by `t`, but here we prove exact equality of sums.
  -- Strategy: both sides equal ∑_{ν ∈ F} w ν after expanding TvecSum.
  have hexpand :
      ∑ f : OrderedFactors (s - 1) T,
          I1PieceIIITvecSum d s N A g δ I h0 (embedTailTvec h0 f.val) e =
        ∑ f : OrderedFactors (s - 1) T,
          ∑ ν ∈ Outer.filter fun ν =>
              ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1, w ν := by
    refine Fintype.sum_congr _ _ fun f => ?_
    simp only [I1PieceIIITvecSum, w, Outer]
  -- Pair (f, ν) with ν.t = embed f contributes iff ν ∈ F and f = restrict(ν.t)
  have hbij :
      ∑ f : OrderedFactors (s - 1) T,
          ∑ ν ∈ Outer.filter fun ν =>
              ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1, w ν =
        ∑ ν ∈ F, w ν := by
    -- Rewrite inner filter sums as ite sums, then commute
    have hite :
        ∀ f : OrderedFactors (s - 1) T,
          (∑ ν ∈ Outer.filter fun ν =>
              ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1, w ν) =
            ∑ ν ∈ Outer,
              ite (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1)
                (w ν) 0 := by
      intro f
      simp only [Finset.sum_filter]
    simp_rw [hite]
    rw [Finset.sum_comm]
    have hpoint :
        ∀ ν ∈ Outer,
          (∑ f : OrderedFactors (s - 1) T,
              ite (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1)
                (w ν) 0) =
            ite (ν ∈ F) (w ν) 0 := by
      intro ν hν
      by_cases hδT : δ * (ν.T h0 : ℝ) < 1
      · by_cases hT : ν.T h0 = T
        · let f := I1Outer.toOrderedFactors hν T hT
          have hembed : embedTailTvec h0 f.val = ν.t :=
            embed_restrictTailTvec h0 ν.t (I1Outer_t0 hν)
          have hterm : ∀ f' : OrderedFactors (s - 1) T,
              ite (ν.t = embedTailTvec h0 f'.val ∧ δ * (ν.T h0 : ℝ) < 1)
                (w ν) 0 =
              ite (f' = f) (w ν) 0 := by
            intro f'
            by_cases hf' : f' = f
            · subst hf'
              simp [hembed, hδT]
            · have hne : ν.t ≠ embedTailTvec h0 f'.val := by
                intro heq
                apply hf'
                apply Subtype.ext
                calc
                  f'.val = restrictTailTvec h0 (embedTailTvec h0 f'.val) :=
                    (restrict_embedTailTvec h0 f'.val).symm
                  _ = restrictTailTvec h0 ν.t := by rw [← heq]
                  _ = f.val := rfl
              simp [hne, hf']
          have huniq :
              (∑ f' : OrderedFactors (s - 1) T,
                  ite (ν.t = embedTailTvec h0 f'.val ∧ δ * (ν.T h0 : ℝ) < 1)
                    (w ν) 0) = w ν := by
            calc
              ∑ f' : OrderedFactors (s - 1) T,
                    ite (ν.t = embedTailTvec h0 f'.val ∧ δ * (ν.T h0 : ℝ) < 1)
                      (w ν) 0
                  = ∑ f' : OrderedFactors (s - 1) T, ite (f' = f) (w ν) 0 :=
                    Fintype.sum_congr _ _ hterm
              _ = w ν := by simp [Fintype.sum_ite_eq']
          have hFmem : ν ∈ F := Finset.mem_filter.2 ⟨hν, hT, hδT⟩
          simpa [hFmem] using huniq
        · have hnone :
              (∑ f : OrderedFactors (s - 1) T,
                  ite (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1)
                    (w ν) 0) = 0 := by
            refine Fintype.sum_eq_zero _ fun f => ?_
            by_cases hcond :
                ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1
            · have : ν.T h0 = T := by
                have ht : ν.T h0 =
                    ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.t i := rfl
                rw [ht, hcond.1, embedTailTvec_T h0 T f]
              exact False.elim (hT this)
            · simp [hcond]
          have hFmem : ν ∉ F := fun hF => hT (Finset.mem_filter.1 hF).2.1
          rw [hnone, if_neg hFmem]
      · have hnone :
            (∑ f : OrderedFactors (s - 1) T,
                ite (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1)
                  (w ν) 0) = 0 := by
          refine Fintype.sum_eq_zero _ fun f => by
            have : ¬ (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1) := by
              intro h; exact hδT h.2
            simp [this]
        have hFmem : ν ∉ F := fun hF =>
          (lt_irrefl _) <|
            lt_of_lt_of_le (Finset.mem_filter.1 hF).2.2 (le_of_not_gt hδT)
        rw [hnone, if_neg hFmem]
    have hsum_ite :
        (∑ ν ∈ Outer, ite (ν ∈ F) (w ν) 0) = ∑ ν ∈ F, w ν := by
      have hEq : Outer.filter (fun ν => ν ∈ F) = F := by
        ext ν
        constructor
        · intro h
          exact (Finset.mem_filter.1 h).2
        · intro h
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, h⟩
      calc
        ∑ ν ∈ Outer, ite (ν ∈ F) (w ν) 0
            = ∑ ν ∈ Outer.filter (fun ν => ν ∈ F), w ν := by
              exact (Finset.sum_filter
                (p := fun ν : IntersectionOuter s => ν ∈ F) (f := w)).symm
        _ = ∑ ν ∈ F, w ν := by rw [hEq]
    calc
      ∑ ν ∈ Outer,
            ∑ f : OrderedFactors (s - 1) T,
              ite (ν.t = embedTailTvec h0 f.val ∧ δ * (ν.T h0 : ℝ) < 1)
                (w ν) 0
          = ∑ ν ∈ Outer, ite (ν ∈ F) (w ν) 0 := by
            refine Finset.sum_congr rfl fun ν hν => hpoint ν hν
      _ = ∑ ν ∈ F, w ν := hsum_ite
  calc
    I1PieceIIIFixedSum d s N A g δ I h0 T e = ∑ ν ∈ F, w ν := hLHS
    _ = ∑ f : OrderedFactors (s - 1) T,
          I1PieceIIITvecSum d s N A g δ I h0 (embedTailTvec h0 f.val) e := by
            rw [← hbij, hexpand]

/--
Combinatorial step (PDF): group outer `t`-factorisations of a fixed product
`T` (at most `τ_{s-1}(T)` many) and pass to the height-`h = e T` block.
-/
theorem I1_piece_III_fixed_Te_comb (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (I : Finset (Fin s)) (hs : 2 ≤ s) (_hN : 3 ≤ N)
        (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
        (_hδ : 0 < δ) (_hδ' : δ < 1 / 8) (_hA : 1 ≤ A)
        (T e : ℕ) (hT : T ∈ Finset.Icc 1 (N ^ (s - 1)))
        (he : e ∈ Finset.Icc 1 (N ^ (s - 1)))
        (_hTδ : δ * (T : ℝ) < 1) (_heδ : δ * (e : ℝ) < 1),
        I1PieceIIIFixedSum d s N A g δ I (by omega) T e ≤
          C * (tau (s - 1) T : ℝ) *
            I1PieceIIIScaledBlock d s N A g δ (e * T) := by
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro s N A g δ I hs _hN _hI0 _hIcard _hδ _hδ' _hA T e hT he _hTδ _heδ
  set h0 : 0 < s := by omega
  have h1T : 1 ≤ T := (Finset.mem_Icc.1 hT).1
  have h1e : 1 ≤ e := (Finset.mem_Icc.1 he).1
  have h1h : 1 ≤ e * T := by
    have : (1 : ℕ) * 1 ≤ e * T := Nat.mul_le_mul h1e h1T
    simpa using this
  have hblock :
      ∀ f : OrderedFactors (s - 1) T,
        I1PieceIIITvecSum d s N A g δ I h0 (embedTailTvec h0 f.val) e ≤
          I1PieceIIIScaledBlock d s N A g δ (e * T) :=
    fun f => I1PieceIIITvecSum_le_scaledBlock d s N A g δ I hs T e h1h f
  have hsum := I1PieceIIIFixedSum_eq_sum_tvec d s N A g δ I h0 T e
  calc
    I1PieceIIIFixedSum d s N A g δ I h0 T e
        = ∑ f : OrderedFactors (s - 1) T,
            I1PieceIIITvecSum d s N A g δ I h0 (embedTailTvec h0 f.val) e :=
          hsum
    _ ≤ ∑ _f : OrderedFactors (s - 1) T,
          I1PieceIIIScaledBlock d s N A g δ (e * T) :=
          Finset.sum_le_sum fun f _ => hblock f
    _ = (Fintype.card (OrderedFactors (s - 1) T) : ℝ) *
          I1PieceIIIScaledBlock d s N A g δ (e * T) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (tau (s - 1) T : ℝ) *
          I1PieceIIIScaledBlock d s N A g δ (e * T) := by
          rw [tau_eq_card_ordered_cast]
    _ = (1 : ℝ) * (tau (s - 1) T : ℝ) *
          I1PieceIIIScaledBlock d s N A g δ (e * T) := by ring

-- Analytic scaled `J1` and `I1_piece_III_fixed_Te_assembled` live in
-- `I1PieceIIIScaledJ1.lean` (proved from scaled Lem5 + matrix embedding).

end RMFLean
