/-
PDF Lemma 6 Σ_I row-factor bookkeeping (PDF (347)–(350)).

Combinatorial core: fibre weights vs `∏_i (N ∑ τ_{s-1}/n)`.
-/
import RMFLean.Proof.F1.J1
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Fintype.Pi

noncomputable section

open Classical BigOperators Fintype

namespace RMFLean

/-! ### Scale vs row off-diagonal -/

theorem MatrixParam.scale_ge_rowOffDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    p.rowOffDiag i ≤ p.scale i :=
  Nat.le_max_left _ _

theorem keyScale_ge_rowOffDiag {s : ℕ} (k : MatrixParam s) (i : Fin s) :
    k.rowOffDiag i ≤ keyScale k i :=
  MatrixParam.scale_ge_rowOffDiag k i

theorem MatrixParam.rowOffDiag_pos {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    0 < p.rowOffDiag i :=
  Finset.prod_pos fun _ _ => p.entries_pos _ _

theorem MatrixParam.rowOffDiag_one_le {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    1 ≤ p.rowOffDiag i :=
  Nat.one_le_of_lt (p.rowOffDiag_pos i)

/-! ### Real division bounds -/

theorem J1_nat_div_cast_le_real_div {N M : ℕ} (_hM : 0 < M) :
    ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) :=
  Nat.cast_div_le

theorem J1_real_div_le_of_scale_ge_row {s : ℕ} (k : MatrixParam s) (N : ℕ) (i : Fin s) :
    (N : ℝ) / (keyScale k i : ℝ) ≤ (N : ℝ) / (k.rowOffDiag i : ℝ) := by
  have hApos : 0 < k.rowOffDiag i := k.rowOffDiag_pos i
  have hle : (k.rowOffDiag i : ℝ) ≤ (keyScale k i : ℝ) :=
    Nat.cast_le.mpr (keyScale_ge_rowOffDiag k i)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (Nat.cast_pos.mpr hApos) hle

/-! ### Weight as a row-product bound -/

noncomputable def J1RowProdVec {s : ℕ} (k : MatrixParam s) : Fin s → ℕ :=
  fun i => k.rowOffDiag i

noncomputable def J1WeightProdRowOffDiag {s : ℕ} (k : MatrixParam s) (N : ℕ) : ℝ :=
  ∏ i : Fin s, (N : ℝ) / (k.rowOffDiag i : ℝ)

noncomputable def J1WeightProdRowOffDiagVec {s : ℕ} (As : Fin s → ℕ) (N : ℕ) : ℝ :=
  ∏ i : Fin s, (N : ℝ) / (As i : ℝ)

theorem J1WeightProdRowOffDiag_eq_vec {s : ℕ} (k : MatrixParam s) (N : ℕ) :
    J1WeightProdRowOffDiag k N = J1WeightProdRowOffDiagVec (J1RowProdVec k) N := by
  simp [J1WeightProdRowOffDiag, J1WeightProdRowOffDiagVec, J1RowProdVec]

theorem J1FullWeight_eq_head_mul_tail {s N : ℕ} (k : MatrixParam s) (h0 : 0 < s) :
    J1FullWeight k N h0 =
      (N : ℝ) / (keyScale k ⟨0, h0⟩ : ℝ) * J1TailWeight k N h0 := by
  simp [J1FullWeight]

theorem J1FullWeight_le_prod_real_scale_div {s N : ℕ} (k : MatrixParam s) (h0 : 0 < s) :
    J1FullWeight k N h0 ≤
      ∏ i : Fin s, (N : ℝ) / (keyScale k i : ℝ) := by
  have hi0 : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
  rw [J1FullWeight_eq_head_mul_tail]
  have hdecomp :
      ∏ i : Fin s, (N : ℝ) / (keyScale k i : ℝ) =
        (N : ℝ) / (keyScale k ⟨0, h0⟩ : ℝ) *
          ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            (N : ℝ) / (keyScale k i : ℝ) :=
    (Finset.mul_prod_erase Finset.univ
      (fun i => (N : ℝ) / (keyScale k i : ℝ)) hi0).symm
  rw [hdecomp]
  have htail :
      J1TailWeight k N h0 ≤
        ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
          (N : ℝ) / (keyScale k i : ℝ) := by
    simp only [J1TailWeight]
    refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => ?_
    simpa using J1_nat_div_cast_le_real_div (MatrixParam.scale_pos k i)
  exact mul_le_mul_of_nonneg_left htail
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem J1FullWeight_le_prod_rowOffDiag {s N : ℕ} (k : MatrixParam s) (h0 : 0 < s) :
    J1FullWeight k N h0 ≤ J1WeightProdRowOffDiag k N := by
  refine le_trans (J1FullWeight_le_prod_real_scale_div k h0) ?_
  refine Finset.prod_le_prod
    (fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg (keyScale k i)))
    fun i _ => J1_real_div_le_of_scale_ge_row k N i

/-! ### Row products of fibres lie in `[1, N]^s` -/

theorem J1Fibre_rowOffDiag_le_N {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (i : Fin s) : k.rowOffDiag i ≤ N := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
  have hrow :
      (offDiagNormalize (solToMatrix x)).rowOffDiag i =
        (solToMatrix x).rowOffDiag i :=
    offDiagNormalize_rowOffDiag _ i
  rw [hrow]
  have hprod := solToMatrix_rowProd x i
  have hdiag : 1 ≤ (solToMatrix x).a i i := by
    have := (solToMatrix x).entries_pos i i
    omega
  have hmul :
      (solToMatrix x).rowOffDiag i ≤
        (solToMatrix x).a i i * (solToMatrix x).rowOffDiag i :=
    Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one hdiag)
  have heq :
      (solToMatrix x).a i i * (solToMatrix x).rowOffDiag i = x.n i := by
    simpa [MatrixParam.rowProd_eq_diag_mul_offDiag] using hprod
  exact le_trans (heq ▸ hmul) (x.hn i).2

theorem J1Fibre_rowOffDiag_one_le {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (i : Fin s) : 1 ≤ k.rowOffDiag i := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
  simpa [offDiagNormalize_rowOffDiag] using
    MatrixParam.rowOffDiag_one_le (offDiagNormalize (solToMatrix x)) i

theorem J1Fibre_rowOffDiag_mem_Icc {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (i : Fin s) :
    k.rowOffDiag i ∈ Finset.Icc 1 N :=
  Finset.mem_Icc.mpr ⟨J1Fibre_rowOffDiag_one_le h0 hk i, J1Fibre_rowOffDiag_le_N h0 hk i⟩

/-! ### Fibre grouping by row off-diagonal products -/

noncomputable def J1RowProdFinset (s N : ℕ) : Finset (Fin s → ℕ) :=
  piFinset fun _ : Fin s => Finset.Icc 1 N

theorem mem_J1RowProdFinset_iff {s N : ℕ} {As : Fin s → ℕ} :
    As ∈ J1RowProdFinset s N ↔ ∀ i, As i ∈ Finset.Icc 1 N := by
  simp [J1RowProdFinset, mem_piFinset]

noncomputable def J1FibresWithRowProds (s N A : ℕ) (As : Fin s → ℕ) :
    Finset (MatrixParam s) :=
  (J1Fibres s N A).filter fun k => ∀ i, k.rowOffDiag i = As i

theorem J1RowProdVec_maps_to {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) :
    J1RowProdVec k ∈ J1RowProdFinset s N := by
  simp only [J1RowProdFinset, mem_piFinset, J1RowProdVec]
  intro i
  exact J1Fibre_rowOffDiag_mem_Icc h0 hk i

/-! ### Row-factor sum identity -/

theorem J1RowFactorSum_eq (s N : ℕ) :
    J1RowFactorSum s N =
      ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ^ s := by
  simp only [J1RowFactorSum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

noncomputable def J1RowFactorTerm (s N : ℕ) (n : ℕ) : ℝ :=
  (N : ℝ) / (n : ℝ) * (tau (s - 1) n : ℝ)

theorem J1RowFactorSum_eq_sum_prod (s N : ℕ) :
    J1RowFactorSum s N =
      ∏ i : Fin s,
        ∑ n ∈ Finset.Icc 1 N, J1RowFactorTerm s N n := by
  have hterm :
      ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N, J1RowFactorTerm s N n := by
    simp only [J1RowFactorTerm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnpos : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1))
    field_simp [hnpos]
  simp only [J1RowFactorSum]
  refine Finset.prod_congr rfl fun _ _ => hterm

theorem J1RowProdFinset_sum_weight_le_row_factor_sum (s N A : ℕ)
    (hrow :
      ∀ As ∈ J1RowProdFinset s N,
        ((J1FibresWithRowProds s N A As).card : ℝ) ≤
          ∏ i : Fin s, (tau (s - 1) (As i) : ℝ)) :
    ∑ As ∈ J1RowProdFinset s N,
        ((J1FibresWithRowProds s N A As).card : ℝ) *
          J1WeightProdRowOffDiagVec As N ≤
      J1RowFactorSum s N := by
  have hsum :
      ∑ As ∈ J1RowProdFinset s N,
          ((J1FibresWithRowProds s N A As).card : ℝ) *
            J1WeightProdRowOffDiagVec As N ≤
        ∑ As ∈ J1RowProdFinset s N,
          (∏ i : Fin s, (tau (s - 1) (As i) : ℝ)) *
            J1WeightProdRowOffDiagVec As N := by
    refine Finset.sum_le_sum fun As hAs => ?_
    have hτ := hrow As hAs
    have hweight : 0 ≤ J1WeightProdRowOffDiagVec As N := by
      refine Finset.prod_nonneg fun i _ =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg (As i))
    exact mul_le_mul_of_nonneg_right hτ hweight
  have hsplit :
      ∑ As ∈ J1RowProdFinset s N,
          (∏ i : Fin s, (tau (s - 1) (As i) : ℝ)) *
            J1WeightProdRowOffDiagVec As N =
        ∑ f ∈ J1RowProdFinset s N,
          ∏ i : Fin s, J1RowFactorTerm s N (f i) := by
    refine Finset.sum_congr rfl fun As _ => ?_
    simp only [J1RowFactorTerm, J1WeightProdRowOffDiagVec]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hprod :
      ∑ f ∈ J1RowProdFinset s N, ∏ i : Fin s, J1RowFactorTerm s N (f i) =
        ∏ i : Fin s, ∑ n ∈ Finset.Icc 1 N, J1RowFactorTerm s N n := by
    simpa [J1RowProdFinset] using
      (Finset.sum_prod_piFinset (ι := Fin s) (s := Finset.Icc 1 N)
        (g := fun (_ : Fin s) n => J1RowFactorTerm s N n))
  calc
    _ ≤ _ := hsum
    _ = _ := hsplit
    _ = _ := hprod
    _ = J1RowFactorSum s N := (J1RowFactorSum_eq_sum_prod s N).symm

/-! ### Σ_I combinatorial fibre bound -/

theorem mem_J1Fibres_diag_eq_one {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (i : Fin s) : k.a i i = 1 := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
  exact offDiagNormalize_diag _ i

/--
PDF fibre multiplicity bound: for fixed row products `A_i`, at most
`∏_i τ_{s-1}(A_i)` normalised off-diagonal matrices arise from `J1Support`.
Each row's off-diagonal `(s-1)`-tuple is an ordered factorisation of `A_i`.
-/
theorem J1_card_fibres_rowProds_le (s N A : ℕ) (As : Fin s → ℕ)
    (hs : 2 ≤ s) (_hN : 3 ≤ N) (_hA : 1 ≤ A)
    (_hAs : ∀ i, As i ∈ Finset.Icc 1 N) :
    (J1FibresWithRowProds s N A As).card ≤
      ∏ i : Fin s, tau (s - 1) (As i) := by
  have h0 : 0 < s := by omega
  have herase : ∀ i : Fin s, (Finset.univ.erase i).card = s - 1 := by
    intro i
    simp [Finset.card_erase_of_mem]
  let e (i : Fin s) : Fin (s - 1) ≃ ↥(Finset.univ.erase i) :=
    (Finset.univ.erase i).equivFinOfCardEq (herase i) |>.symm
  let toFactors :
      {k // k ∈ J1FibresWithRowProds s N A As} →
        (i : Fin s) → OrderedFactors (s - 1) (As i) := fun k i =>
    ⟨fun t => k.1.a i (e i t).1, by
      constructor
      · intro t
        exact k.1.entries_pos i (e i t).1
      · have hrow : k.1.rowOffDiag i = As i :=
          (Finset.mem_filter.1 k.2).2 i
        calc
          (∏ t : Fin (s - 1), k.1.a i (e i t).1) =
              ∏ y : ↥(Finset.univ.erase i), k.1.a i y.1 :=
            Fintype.prod_equiv (e i) (fun t => k.1.a i (e i t).1)
              (fun y => k.1.a i y.1) (fun _ => rfl)
          _ = ∏ y ∈ Finset.univ.erase i, k.1.a i y := by
            rw [Finset.univ_eq_attach, Finset.prod_attach]
          _ = k.1.rowOffDiag i := rfl
          _ = As i := hrow⟩
  have hinj : Function.Injective toFactors := by
    intro k₁ k₂ h
    refine Subtype.ext ?_
    refine MatrixParam.ext ?_
    intro i j
    by_cases hij : i = j
    · subst j
      have hk1 : k₁.1 ∈ J1Fibres s N A := (Finset.mem_filter.1 k₁.2).1
      have hk2 : k₂.1 ∈ J1Fibres s N A := (Finset.mem_filter.1 k₂.2).1
      rw [mem_J1Fibres_diag_eq_one h0 hk1, mem_J1Fibres_diag_eq_one h0 hk2]
    · have hjmem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ _⟩
      have hv :=
        congrArg
          (fun f : (i : Fin s) → OrderedFactors (s - 1) (As i) =>
            (f i).1 ((e i).symm ⟨j, hjmem⟩)) h
      simpa [toFactors] using hv
  have hcard := Fintype.card_le_of_injective toFactors hinj
  simpa [Fintype.card_coe, Fintype.card_pi, tau_eq_card_ordered] using hcard

set_option maxHeartbeats 800000

theorem J1_sigma_I_le_row_factor_sum (s N A : ℕ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 1 ≤ A) :
    J1SigmaWeight s N A (by omega) (J1Fibres s N A) ≤ J1RowFactorSum s N := by
  have h0 : 0 < s := by omega
  have hterm :
      ∀ k ∈ J1Fibres s N A,
        J1FullWeight k N h0 ≤ J1WeightProdRowOffDiag k N :=
    fun k hk => J1FullWeight_le_prod_rowOffDiag k h0
  have hrow :
      ∀ As ∈ J1RowProdFinset s N,
        ((J1FibresWithRowProds s N A As).card : ℝ) ≤
          ∏ i : Fin s, (tau (s - 1) (As i) : ℝ) := by
    intro As hAs
    have hAs' : ∀ i, As i ∈ Finset.Icc 1 N := by
      simpa [J1RowProdFinset, mem_piFinset] using hAs
    exact_mod_cast J1_card_fibres_rowProds_le s N A As hs hN hA hAs'
  have hfiber :
      ∑ k ∈ J1Fibres s N A, J1WeightProdRowOffDiag k N =
        ∑ As ∈ J1RowProdFinset s N,
          ∑ k ∈ J1Fibres s N A with J1RowProdVec k = As,
            J1WeightProdRowOffDiagVec As N := by
    have hmaps :
        ∀ k ∈ J1Fibres s N A, J1RowProdVec k ∈ J1RowProdFinset s N :=
      fun k hk => J1RowProdVec_maps_to h0 hk
    have hsum :
        ∑ k ∈ J1Fibres s N A, J1WeightProdRowOffDiagVec (J1RowProdVec k) N =
          ∑ As ∈ J1RowProdFinset s N,
            ∑ k ∈ J1Fibres s N A with J1RowProdVec k = As,
              J1WeightProdRowOffDiagVec As N := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to' (s := J1Fibres s N A)
          (t := J1RowProdFinset s N) (g := J1RowProdVec) hmaps
          (f := fun As => J1WeightProdRowOffDiagVec As N)).symm
    simpa [J1WeightProdRowOffDiag_eq_vec] using hsum
  have hfiber' :
      ∑ As ∈ J1RowProdFinset s N,
          ∑ k ∈ J1Fibres s N A with J1RowProdVec k = As,
            J1WeightProdRowOffDiagVec As N =
        ∑ As ∈ J1RowProdFinset s N,
          ((J1FibresWithRowProds s N A As).card : ℝ) *
            J1WeightProdRowOffDiagVec As N := by
    refine Finset.sum_congr rfl fun As _ => ?_
    have hinner :
        ∑ k ∈ J1Fibres s N A with J1RowProdVec k = As,
            J1WeightProdRowOffDiagVec As N =
          ((J1Fibres s N A).filter fun k => J1RowProdVec k = As).card *
            J1WeightProdRowOffDiagVec As N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hfilter :
        (J1Fibres s N A).filter (fun k => J1RowProdVec k = As) =
          J1FibresWithRowProds s N A As := by
      ext k
      simp [J1FibresWithRowProds, J1RowProdVec, funext_iff]
    rw [hinner, hfilter]
  calc
    J1SigmaWeight s N A h0 (J1Fibres s N A) =
        ∑ k ∈ J1Fibres s N A, J1FullWeight k N h0 := rfl
    _ ≤ ∑ k ∈ J1Fibres s N A, J1WeightProdRowOffDiag k N :=
      Finset.sum_le_sum hterm
    _ = ∑ As ∈ J1RowProdFinset s N,
          ((J1FibresWithRowProds s N A As).card : ℝ) *
            J1WeightProdRowOffDiagVec As N := by
      rw [hfiber, hfiber']
    _ ≤ J1RowFactorSum s N :=
      J1RowProdFinset_sum_weight_le_row_factor_sum s N A hrow

end RMFLean
