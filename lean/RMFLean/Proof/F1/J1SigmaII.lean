/-
PDF Lemma 6 Σ_II core (357)–(368).
-/
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.F1.J1
import RMFLean.Proof.F1.J1RowFactor
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Fintype

namespace RMFLean

/-! ### Uniform divisor bound (Trusted Lemma 1) -/

/-- Alias of `divisor_pointwise_exp_bound` (PDF Lemma 1 / Norton). -/
def tau_uniform_exp_bound := divisor_pointwise_exp_bound

/-! ### Row / matrix configurations -/

noncomputable def rowFunFinset (s N : ℕ) (i : Fin s) : Finset (Fin s → ℕ) :=
  (piFinset fun j : Fin s =>
      if j = i then ({1} : Finset ℕ) else Finset.Icc 1 N).filter
    fun r => (∏ j ∈ Finset.univ.erase i, r j) ≤ N

noncomputable def matrixFunFinset (s N : ℕ) : Finset (Fin s → Fin s → ℕ) :=
  piFinset fun i : Fin s => rowFunFinset s N i

def funRowOff {s : ℕ} (f : Fin s → Fin s → ℕ) (i : Fin s) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, f i j

def funColOff {s : ℕ} (f : Fin s → Fin s → ℕ) (i : Fin s) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, f j i

def transposeFun {s : ℕ} (f : Fin s → Fin s → ℕ) : Fin s → Fin s → ℕ :=
  fun i j => f j i

theorem funRowOff_transpose {s : ℕ} (f : Fin s → Fin s → ℕ) (i : Fin s) :
    funRowOff (transposeFun f) i = funColOff f i := by
  simp [funRowOff, funColOff, transposeFun]

theorem funColOff_transpose {s : ℕ} (f : Fin s → Fin s → ℕ) (i : Fin s) :
    funColOff (transposeFun f) i = funRowOff f i := by
  simp [funRowOff, funColOff, transposeFun]

theorem funRowOff_eq_rowOffDiag {s : ℕ} (k : MatrixParam s) (i : Fin s) :
    funRowOff k.a i = k.rowOffDiag i :=
  rfl

theorem funColOff_eq_colOffDiag {s : ℕ} (k : MatrixParam s) (i : Fin s) :
    funColOff k.a i = k.colOffDiag i :=
  rfl

theorem mem_rowFunFinset_diag {s N : ℕ} {i : Fin s} {r : Fin s → ℕ}
    (hr : r ∈ rowFunFinset s N i) : r i = 1 := by
  have := mem_piFinset.1 (Finset.mem_filter.1 hr).1 i
  simpa using this

theorem mem_rowFunFinset_off {s N : ℕ} {i j : Fin s} {r : Fin s → ℕ}
    (hr : r ∈ rowFunFinset s N i) (hij : j ≠ i) :
    r j ∈ Finset.Icc 1 N := by
  have := mem_piFinset.1 (Finset.mem_filter.1 hr).1 j
  simpa [hij] using this

theorem mem_rowFunFinset_prod_le {s N : ℕ} {i : Fin s} {r : Fin s → ℕ}
    (hr : r ∈ rowFunFinset s N i) :
    (∏ j ∈ Finset.univ.erase i, r j) ≤ N :=
  (Finset.mem_filter.1 hr).2

theorem mem_rowFunFinset_prod_pos {s N : ℕ} {i : Fin s} {r : Fin s → ℕ}
    (hr : r ∈ rowFunFinset s N i) :
    0 < ∏ j ∈ Finset.univ.erase i, r j := by
  refine Finset.prod_pos fun j hj => ?_
  exact (Finset.mem_Icc.1
    (mem_rowFunFinset_off hr (Finset.mem_erase.1 hj).1)).1

/-- Off-diag row tuples with product `n` are counted by `τ_{s-1}`. -/
theorem card_rowFun_eq_prod_le_tau {s N n : ℕ} (i : Fin s)
    (_hn : 1 ≤ n) (_hnN : n ≤ N) :
    (((rowFunFinset s N i).filter
        fun r => (∏ j ∈ Finset.univ.erase i, r j) = n).card) ≤
      tau (s - 1) n := by
  have herase : (Finset.univ.erase i).card = s - 1 := by
    simp [Finset.card_erase_of_mem]
  let e : Fin (s - 1) ≃ ↥(Finset.univ.erase i) :=
    (Finset.univ.erase i).equivFinOfCardEq herase |>.symm
  rw [tau_eq_card_ordered]
  let toFactors :
      {r // r ∈ (rowFunFinset s N i).filter
        (fun r => (∏ j ∈ Finset.univ.erase i, r j) = n)} →
        OrderedFactors (s - 1) n := fun r =>
    ⟨fun t => r.1 (e t).1, by
      constructor
      · intro t
        have ht : (e t).1 ≠ i := (Finset.mem_erase.1 (e t).2).1
        exact (Finset.mem_Icc.1
          (mem_rowFunFinset_off (Finset.mem_filter.1 r.2).1 ht)).1
      · calc
          (∏ t : Fin (s - 1), r.1 (e t).1) =
              ∏ y : ↥(Finset.univ.erase i), r.1 y.1 := by
            exact Fintype.prod_equiv e (fun t => r.1 (e t).1)
              (fun y => r.1 y.1) (fun _ => rfl)
          _ = ∏ y ∈ Finset.univ.erase i, r.1 y := by
            rw [Finset.univ_eq_attach, Finset.prod_attach]
          _ = n := (Finset.mem_filter.1 r.2).2⟩
  have hcard := Fintype.card_le_of_injective toFactors (by
    intro r₁ r₂ h
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      rw [mem_rowFunFinset_diag (Finset.mem_filter.1 r₁.2).1,
        mem_rowFunFinset_diag (Finset.mem_filter.1 r₂.2).1]
    · have hjmem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩
      have hv := congrArg
        (fun f : OrderedFactors (s - 1) n => f.1 (e.symm ⟨j, hjmem⟩)) h
      simpa [toFactors] using hv)
  simpa using hcard

theorem sum_rowFun_N_div_prod (s N : ℕ) (i : Fin s) :
    (∑ r ∈ rowFunFinset s N i,
        (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ)) ≤
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ) := by
  have hmaps :
      ∀ r ∈ rowFunFinset s N i,
        (∏ j ∈ Finset.univ.erase i, r j) ∈ Finset.Icc 1 N := by
    intro r hr
    exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt (mem_rowFunFinset_prod_pos hr),
      mem_rowFunFinset_prod_le hr⟩
  have hgroup :
      ∑ r ∈ rowFunFinset s N i,
          (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) =
        ∑ n ∈ Finset.Icc 1 N,
          (((rowFunFinset s N i).filter
              fun r => (∏ j ∈ Finset.univ.erase i, r j) = n).card : ℝ) *
            ((N : ℝ) / (n : ℝ)) := by
    have h :=
      (Finset.sum_fiberwise_of_maps_to' (s := rowFunFinset s N i)
        (t := Finset.Icc 1 N)
        (g := fun r => (∏ j ∈ Finset.univ.erase i, r j)) hmaps
        (f := fun n => (N : ℝ) / (n : ℝ))).symm
    have h' :
        ∑ r ∈ rowFunFinset s N i,
            (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) =
          ∑ n ∈ Finset.Icc 1 N,
            ∑ r ∈ (rowFunFinset s N i).filter
                (fun r => (∏ j ∈ Finset.univ.erase i, r j) = n),
              (N : ℝ) / (n : ℝ) := by
      simpa only [Nat.cast_prod] using h
    calc
      _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ r ∈ (rowFunFinset s N i).filter
              (fun r => (∏ j ∈ Finset.univ.erase i, r j) = n),
            (N : ℝ) / (n : ℝ) := h'
      _ = _ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp [Finset.sum_const, nsmul_eq_mul]
  rw [hgroup]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
  have hcard := card_rowFun_eq_prod_le_tau (i := i) (N := N) hn1 hnN
  have hden : 0 ≤ (N : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (tau (s - 1) n : ℝ) * ((N : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hden
    _ = (N : ℝ) * ((tau (s - 1) n : ℝ) / (n : ℝ)) := by ring

theorem MatrixParam_a_mem_matrixFunFinset {s N A : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ J1Fibres s N A) :
    k.a ∈ matrixFunFinset s N := by
  refine mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨?_, ?_⟩
  · refine mem_piFinset.2 fun j => ?_
    by_cases hij : j = i
    · subst hij
      rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
      simp [offDiagNormalize]
    · rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
      set p := offDiagNormalize (solToMatrix x)
      have h1 : 1 ≤ p.a i j := Nat.one_le_of_lt (p.entries_pos i j)
      have hrow := J1Fibre_rowOffDiag_le_N h0 hk i
      have hdiv : p.a i j ∣ p.rowOffDiag i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)
      have hle : p.a i j ≤ N :=
        le_trans (Nat.le_of_dvd (MatrixParam.rowOffDiag_pos p i) hdiv) hrow
      simpa [hij, p] using Finset.mem_Icc.2 ⟨h1, hle⟩
  · simpa [MatrixParam.rowOffDiag] using J1Fibre_rowOffDiag_le_N h0 hk i

theorem J1Fibre_colOffDiag_le_N {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (i : Fin s) : k.colOffDiag i ≤ N := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
  have hcol :
      (offDiagNormalize (solToMatrix x)).colOffDiag i =
        (solToMatrix x).colOffDiag i :=
    offDiagNormalize_colOffDiag _ i
  rw [hcol]
  have hprod := solToMatrix_colProd x i
  have hdiag : 1 ≤ (solToMatrix x).a i i := by
    have := (solToMatrix x).entries_pos i i
    omega
  have hmul :
      (solToMatrix x).colOffDiag i ≤
        (solToMatrix x).a i i * (solToMatrix x).colOffDiag i :=
    Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one hdiag)
  have heq :
      (solToMatrix x).a i i * (solToMatrix x).colOffDiag i = x.m i := by
    simpa [MatrixParam.colProd_eq_diag_mul_offDiag] using hprod
  exact le_trans (heq ▸ hmul) (x.hm i).2

theorem MatrixParam_transpose_a_mem_matrixFunFinset {s N A : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ J1Fibres s N A) :
    transposeFun k.a ∈ matrixFunFinset s N := by
  refine mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨?_, ?_⟩
  · refine mem_piFinset.2 fun j => ?_
    by_cases hij : j = i
    · subst hij
      rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
      simp [transposeFun, offDiagNormalize]
    · rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
      set p := offDiagNormalize (solToMatrix x)
      have h1 : 1 ≤ p.a j i := Nat.one_le_of_lt (p.entries_pos j i)
      have hcol := J1Fibre_colOffDiag_le_N h0 hk i
      have hdiv : p.a j i ∣ p.colOffDiag i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)
      have hle : p.a j i ≤ N :=
        le_trans (Nat.le_of_dvd
          (Finset.prod_pos fun _ _ => p.entries_pos _ _) hdiv) hcol
      simpa [transposeFun, hij, p] using Finset.mem_Icc.2 ⟨h1, hle⟩
  · simpa [transposeFun, MatrixParam.colOffDiag, funColOff] using
      J1Fibre_colOffDiag_le_N h0 hk i

theorem J1FullWeight_le_funWeight_A_lt_B {s : ℕ}
    (k : MatrixParam s) (N : ℕ) (h0 : 0 < s)
    (hAB : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩)) :
    J1FullWeight k N h0 ≤
      (N : ℝ) / (k.colOffDiag ⟨0, h0⟩ : ℝ) *
        ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
          (N : ℝ) / (k.rowOffDiag i : ℝ) := by
  have hM : keyScale k ⟨0, h0⟩ = k.colOffDiag ⟨0, h0⟩ :=
    max_eq_right (Nat.le_of_lt hAB)
  simp only [J1FullWeight, hM]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simp only [J1TailWeight]
  refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => ?_
  refine le_trans (J1_nat_div_cast_le_real_div (MatrixParam.scale_pos k i)) ?_
  exact J1_real_div_le_of_scale_ge_row k N i

theorem J1FullWeight_le_funWeight_B_lt_A {s : ℕ}
    (k : MatrixParam s) (N : ℕ) (h0 : 0 < s)
    (hBA : (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩)) :
    J1FullWeight k N h0 ≤
      (N : ℝ) / (k.rowOffDiag ⟨0, h0⟩ : ℝ) *
        ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
          (N : ℝ) / (k.colOffDiag i : ℝ) := by
  have hM : keyScale k ⟨0, h0⟩ = k.rowOffDiag ⟨0, h0⟩ :=
    max_eq_left (Nat.le_of_lt hBA)
  simp only [J1FullWeight, hM]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simp only [J1TailWeight]
  refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i hi => ?_
  refine le_trans (J1_nat_div_cast_le_real_div (MatrixParam.scale_pos k i)) ?_
  have hBpos : 0 < k.colOffDiag i :=
    Finset.prod_pos fun _ _ => k.entries_pos _ _
  have hle : (k.colOffDiag i : ℝ) ≤ (keyScale k i : ℝ) :=
    Nat.cast_le.mpr (Nat.le_max_right _ _)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (Nat.cast_pos.mpr hBpos) hle

/-- Cauchy--Schwarz factor `(2 log N)^{((s-1)²-1)/2}` on an exceptional row. -/
noncomputable def sigmaIILogFactor (N s : ℕ) : ℝ :=
  Real.sqrt ((2 * Real.log N) ^ ((s - 1) ^ 2 - 1))

/--
Cauchy--Schwarz on `ℛ_D ∩ [1, min(N,D)]` at scale `max(3,min(N,D))`,
using Lemma 1 (`∑ τ²`) and `|ℛ| ≤ C δ D`.
-/
theorem sum_tau_on_R_le (s N D : ℕ) (δ : ℝ) (Rd : Finset ℕ) (C : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hD : 0 < D) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hR : (Rd.card : ℝ) ≤ C * δ * (D : ℝ)) :
    (∑ n ∈ Rd ∩ Finset.Icc 1 (min N D), (tau (s - 1) n : ℝ)) ≤
      Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) *
        sigmaIILogFactor N s := by
  set S := Rd ∩ Finset.Icc 1 (min N D)
  set X : ℕ := max 3 (min N D)
  set L : ℝ := (2 * Real.log N) ^ ((s - 1) ^ 2 - 1)
  have hX3 : 3 ≤ X := le_max_left _ _
  have hXN : X ≤ N := max_le hN (min_le_left _ _)
  have hXle : X ≤ 3 * D := by
    have h1 : max 3 (min N D) ≤ max 3 D :=
      max_le_max le_rfl (min_le_right _ _)
    have hD1 : 1 ≤ D := Nat.succ_le_of_lt hD
    have h3 : 3 ≤ 3 * D := Nat.mul_le_mul_left 3 hD1
    have hD3 : D ≤ 3 * D := Nat.le_mul_of_pos_left D (by decide)
    exact h1.trans (max_le h3 hD3)
  have hSsub : S ⊆ Finset.Icc 1 X := by
    intro n hn
    have hnI : n ∈ Finset.Icc 1 (min N D) := (Finset.mem_inter.1 hn).2
    have hn1 := (Finset.mem_Icc.1 hnI).1
    have hnmin := (Finset.mem_Icc.1 hnI).2
    exact Finset.mem_Icc.2 ⟨hn1, hnmin.trans (le_max_right _ _)⟩
  have hℓ : 1 ≤ s - 1 := by omega
  have hsq := divisor_sum_sq_bound X (s - 1) hX3 hℓ
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hX3)
  have hlogX : Real.log X ≤ Real.log N :=
    Real.log_le_log hXpos (Nat.cast_le.mpr hXN)
  have hlogN : (1 : ℝ) < Real.log N := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    exact lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hN))
  have hL0 : 0 ≤ L := by positivity
  have hlogX0 : 0 ≤ Real.log X := by
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    exact (lt_trans (by norm_num : (0 : ℝ) < 1) h3).le.trans
      (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hX3))
  have hpow :
      (2 * Real.log X) ^ ((s - 1) ^ 2 - 1) ≤ L :=
    pow_le_pow_left₀ (by positivity) (by gcongr) _
  have hsumsq :
      ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2 ≤ (X : ℝ) * L := by
    calc
      ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2
          ≤ ∑ n ∈ Finset.Icc 1 X, (tau (s - 1) n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub
          (fun _ _ _ => sq_nonneg _)
      _ ≤ (X : ℝ) * (2 * Real.log X) ^ ((s - 1) ^ 2 - 1) := hsq
      _ ≤ (X : ℝ) * L := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  have hcs :
      (∑ n ∈ S, (tau (s - 1) n : ℝ)) ^ 2 ≤
        (S.card : ℝ) * ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2 := by
    simpa using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
        (fun n => (tau (s - 1) n : ℝ))
  have hsum0 : 0 ≤ ∑ n ∈ S, (tau (s - 1) n : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsqrt :
      ∑ n ∈ S, (tau (s - 1) n : ℝ) ≤
        Real.sqrt ((S.card : ℝ) * ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2) :=
    Real.le_sqrt_of_sq_le hcs
  have hcard : (S.card : ℝ) ≤ C * δ * (D : ℝ) :=
    le_trans (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)) hR
  have hprod :
      Real.sqrt ((S.card : ℝ) * ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2) ≤
        Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt ((X : ℝ) * L) := by
    have hmul :
        (S.card : ℝ) * ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2 ≤
          (C * δ * (D : ℝ)) * ((X : ℝ) * L) :=
      mul_le_mul hcard hsumsq
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (mul_nonneg (mul_nonneg hC hδ) (Nat.cast_nonneg _))
    have hsq := Real.sqrt_le_sqrt hmul
    have hsplit :
        Real.sqrt ((C * δ * (D : ℝ)) * ((X : ℝ) * L)) =
          Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt ((X : ℝ) * L) := by
      rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hC hδ) (Nat.cast_nonneg _))]
    exact hsq.trans_eq hsplit
  have hsqrtXL :
      Real.sqrt ((X : ℝ) * L) = Real.sqrt (X : ℝ) * Real.sqrt L := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  have hX3D : (X : ℝ) ≤ (3 : ℝ) * (D : ℝ) := by exact_mod_cast hXle
  have hsqrtX : Real.sqrt (X : ℝ) ≤ Real.sqrt ((3 : ℝ) * (D : ℝ)) :=
    Real.sqrt_le_sqrt hX3D
  have h3D : Real.sqrt ((3 : ℝ) * (D : ℝ)) =
      Real.sqrt 3 * Real.sqrt (D : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
  have hCD :
      Real.sqrt (C * δ * (D : ℝ)) =
        Real.sqrt C * Real.sqrt δ * Real.sqrt (D : ℝ) := by
    have h1 : Real.sqrt (C * δ * (D : ℝ)) =
        Real.sqrt (C * δ) * Real.sqrt (D : ℝ) := by
      rw [Real.sqrt_mul (mul_nonneg hC hδ)]
    have h2 : Real.sqrt (C * δ) = Real.sqrt C * Real.sqrt δ := by
      rw [Real.sqrt_mul hC]
    rw [h1, h2]
  have hpack :
      Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt (X : ℝ) ≤
        Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) := by
    have hsqrtD : Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ) = (D : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    calc
      Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt (X : ℝ)
          ≤ Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt ((3 : ℝ) * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtX (Real.sqrt_nonneg _)
      _ = (Real.sqrt C * Real.sqrt δ * Real.sqrt (D : ℝ)) *
            (Real.sqrt 3 * Real.sqrt (D : ℝ)) := by
          rw [hCD, h3D]
      _ = Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) := by
          have h3C : Real.sqrt (3 * C) = Real.sqrt 3 * Real.sqrt C := by
            rw [Real.sqrt_mul (by norm_num)]
          calc
            (Real.sqrt C * Real.sqrt δ * Real.sqrt (D : ℝ)) *
                (Real.sqrt 3 * Real.sqrt (D : ℝ))
                = (Real.sqrt 3 * Real.sqrt C) * Real.sqrt δ *
                    (Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ)) := by ring
            _ = Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) := by
                  rw [h3C, hsqrtD]
  calc
    ∑ n ∈ S, (tau (s - 1) n : ℝ)
        ≤ Real.sqrt ((S.card : ℝ) * ∑ n ∈ S, (tau (s - 1) n : ℝ) ^ 2) := hsqrt
    _ ≤ Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt ((X : ℝ) * L) := hprod
    _ = Real.sqrt (C * δ * (D : ℝ)) * Real.sqrt (X : ℝ) * Real.sqrt L := by
          rw [hsqrtXL]; ring
    _ ≤ Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) * Real.sqrt L := by
          refine mul_le_mul_of_nonneg_right hpack (Real.sqrt_nonneg _)
    _ = Real.sqrt (3 * C) * Real.sqrt δ * (D : ℝ) * sigmaIILogFactor N s := by
          simp [sigmaIILogFactor, L]

/-- PDF exceptional matrix weight (`A₁ < B₁` branch). -/
noncomputable def sigmaIIFunWeight (s N : ℕ) (h0 : 0 < s)
    (R : ℕ → Finset ℕ) (f : Fin s → Fin s → ℕ) : ℝ :=
  if funRowOff f ⟨0, h0⟩ ∈ R (funColOff f ⟨0, h0⟩) ∧
      funRowOff f ⟨0, h0⟩ ≤ funColOff f ⟨0, h0⟩ then
    (N : ℝ) / (funColOff f ⟨0, h0⟩ : ℝ) *
      ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
        (N : ℝ) / (funRowOff f i : ℝ)
  else 0

theorem sigmaIIFunWeight_nonneg (s N : ℕ) (h0 : 0 < s)
    (R : ℕ → Finset ℕ) (f : Fin s → Fin s → ℕ) :
    0 ≤ sigmaIIFunWeight s N h0 R f := by
  simp only [sigmaIIFunWeight]
  split_ifs
  · refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
    exact Finset.prod_nonneg fun _ _ =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

/-! ### Peel row 0 from `matrixFunFinset` -/

private noncomputable def dummyRow (s : ℕ) : Fin s → ℕ := fun _ => 1

private noncomputable def tailsFinset (s N : ℕ) (i0 : Fin s) :
    Finset (Fin s → Fin s → ℕ) :=
  piFinset fun i : Fin s =>
    if i = i0 then ({dummyRow s} : Finset (Fin s → ℕ))
    else rowFunFinset s N i

private def combineRow {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) : Fin s → Fin s → ℕ :=
  fun i => if i = i0 then r0 else t i

private theorem combineRow_row0 {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) :
    combineRow i0 r0 t i0 = r0 := by
  simp [combineRow]

private theorem combineRow_row_ne {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) {i : Fin s} (hi : i ≠ i0) :
    combineRow i0 r0 t i = t i := by
  simp [combineRow, hi]

private theorem funRowOff_combine_i0 {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) :
    funRowOff (combineRow i0 r0 t) i0 =
      ∏ j ∈ Finset.univ.erase i0, r0 j := by
  simp [funRowOff, combineRow_row0]

private theorem funRowOff_combine_ne {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) {i : Fin s} (hi : i ≠ i0) :
    funRowOff (combineRow i0 r0 t) i = funRowOff t i := by
  simp only [funRowOff]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [combineRow_row_ne i0 r0 t hi]

private theorem funColOff_combine_i0 {s : ℕ} (i0 : Fin s) (r0 : Fin s → ℕ)
    (t : Fin s → Fin s → ℕ) :
    funColOff (combineRow i0 r0 t) i0 =
      ∏ i ∈ Finset.univ.erase i0, t i i0 := by
  simp only [funColOff]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hine : i ≠ i0 := (Finset.mem_erase.1 hi).1
  rw [combineRow_row_ne i0 r0 t hine]

private theorem sum_matrixFun_eq_sum_combine (s N : ℕ) (i0 : Fin s)
    (F : (Fin s → Fin s → ℕ) → ℝ) :
    ∑ f ∈ matrixFunFinset s N, F f =
      ∑ t ∈ tailsFinset s N i0,
        ∑ r0 ∈ rowFunFinset s N i0, F (combineRow i0 r0 t) := by
  let e : (Fin s → Fin s → ℕ) →
      (Fin s → ℕ) × (Fin s → Fin s → ℕ) := fun f =>
    (f i0, fun i => if i = i0 then dummyRow s else f i)
  let j : (Fin s → ℕ) × (Fin s → Fin s → ℕ) →
      (Fin s → Fin s → ℕ) := fun p => combineRow i0 p.1 p.2
  have hi :
      ∀ f ∈ matrixFunFinset s N,
        e f ∈ (rowFunFinset s N i0).product (tailsFinset s N i0) := by
    intro f hf
    refine Finset.mem_product.2 ⟨mem_piFinset.1 hf i0, ?_⟩
    refine mem_piFinset.2 fun i => ?_
    by_cases hii : i = i0
    · subst i
      simp [e]
    · simp [e, hii, mem_piFinset.1 hf i]
  have hj :
      ∀ p ∈ (rowFunFinset s N i0).product (tailsFinset s N i0),
        j p ∈ matrixFunFinset s N := by
    intro p hp
    rcases Finset.mem_product.1 hp with ⟨hp0, hpt⟩
    refine mem_piFinset.2 fun i => ?_
    by_cases hii : i = i0
    · subst i
      simpa [j, combineRow] using hp0
    · simpa [j, combineRow, hii] using mem_piFinset.1 hpt i
  have hleft :
      ∀ f ∈ matrixFunFinset s N, j (e f) = f := by
    intro f _
    funext i
    by_cases hii : i = i0
    · subst i
      simp [j, e, combineRow]
    · simp [j, e, combineRow, hii]
  have hright :
      ∀ p ∈ (rowFunFinset s N i0).product (tailsFinset s N i0),
        e (j p) = p := by
    intro p hp
    rcases Finset.mem_product.1 hp with ⟨_, hpt⟩
    apply Prod.ext
    · simp [e, j, combineRow]
    · funext i
      by_cases hii : i = i0
      · subst i
        have ht0 := mem_piFinset.1 hpt i0
        have ht0eq : p.2 i0 = dummyRow s := by
          simpa [tailsFinset] using ht0
        simp [e, j, ht0eq]
      · simp [e, j, combineRow, hii]
  have hpair :
      ∑ f ∈ matrixFunFinset s N, F f =
        ∑ p ∈ (rowFunFinset s N i0).product (tailsFinset s N i0),
          F (j p) := by
    exact Finset.sum_nbij' e j hi hj hleft hright
      (fun f hf => congrArg F (hleft f hf).symm)
  calc
    ∑ f ∈ matrixFunFinset s N, F f =
        ∑ p ∈ (rowFunFinset s N i0).product (tailsFinset s N i0),
          F (j p) := hpair
    _ = ∑ r0 ∈ rowFunFinset s N i0,
          ∑ t ∈ tailsFinset s N i0, F (combineRow i0 r0 t) := by
      simpa [j] using
        (Finset.sum_product (s := rowFunFinset s N i0)
          (t := tailsFinset s N i0) (f := fun p => F (j p)))
    _ = ∑ t ∈ tailsFinset s N i0,
          ∑ r0 ∈ rowFunFinset s N i0, F (combineRow i0 r0 t) := by
      rw [Finset.sum_comm]

/-
Core combinatorial/analytic bound on unrestricted matrices.
Proved by fixing rows `2..s` and Cauchy--Schwarz on `#R_D ≪ δ D`.
-/
theorem matrixFun_sigma_II_bound (d s N : ℕ) (δ : ℝ) (R : ℕ → Finset ℕ)
    (Cd Cτ : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ)
    (hCd : 0 < Cd) (_hCτ : 0 < Cτ)
    (_hτbound : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ f ∈ matrixFunFinset s N,
        sigmaIIFunWeight s N (by omega) R f) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  have h0 : 0 < s := by omega
  set i0 : Fin s := ⟨0, h0⟩
  set T : ℝ := sigmaIILogFactor N s
  have hTnonneg : 0 ≤ T := Real.sqrt_nonneg _
  let Cuni : ℝ := Cd
  have hCuni_pos : 0 < Cuni := by simpa [Cuni] using hCd
  set H : ℝ :=
    (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)
  have hHnonneg : 0 ≤ H :=
    mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun _ _ =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  -- Tail factorisation bound.
  have htail :
      ∑ t ∈ tailsFinset s N i0,
          ∏ i ∈ Finset.univ.erase i0,
            (N : ℝ) / (funRowOff t i : ℝ) ≤ H ^ (s - 1) := by
    let S : Fin s → Finset (Fin s → ℕ) := fun i =>
      if i = i0 then ({dummyRow s} : Finset (Fin s → ℕ))
      else rowFunFinset s N i
    let g : Fin s → (Fin s → ℕ) → ℝ := fun i r =>
      if i = i0 then (1 : ℝ)
      else (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ)
    have hsum_eq :
        ∑ t ∈ tailsFinset s N i0,
            ∏ i ∈ Finset.univ.erase i0,
              (N : ℝ) / (funRowOff t i : ℝ) =
          ∑ t ∈ piFinset S, ∏ i, g i (t i) := by
      simp only [tailsFinset, S]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hprod :
          ∏ i, g i (t i) =
            ∏ i ∈ Finset.univ.erase i0, (N : ℝ) / (funRowOff t i : ℝ) := by
        have hi0 : i0 ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase _ _ hi0]
        have hg0 : g i0 (t i0) = 1 := by simp [g]
        simp only [hg0, one_mul, funRowOff, g]
        refine Finset.prod_congr rfl fun i hi => ?_
        have hine : i ≠ i0 := (Finset.mem_erase.1 hi).1
        simp [hine]
      exact hprod.symm
    have hfactor :
        ∑ t ∈ piFinset S, ∏ i, g i (t i) = ∏ i, ∑ r ∈ S i, g i r :=
      (Finset.prod_univ_sum S g).symm
    have hbound_factor :
        ∏ i, ∑ r ∈ S i, g i r ≤ H ^ (s - 1) := by
      have hall :
          ∏ i, ∑ r ∈ S i, g i r =
            ∏ i ∈ Finset.univ.erase i0,
              ∑ r ∈ rowFunFinset s N i,
                (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) := by
        have hi0 : i0 ∈ (Finset.univ : Finset (Fin s)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin s))
          (fun i => ∑ r ∈ S i, g i r) hi0]
        simp only [S, g]
        simp
        refine Finset.prod_congr rfl fun i hi => ?_
        have hine : i ≠ i0 := (Finset.mem_erase.1 hi).1
        simp [hine]
      have hrows :
          ∏ i ∈ Finset.univ.erase i0, ∑ r ∈ rowFunFinset s N i,
              (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) ≤
            ∏ i ∈ Finset.univ.erase i0, H := by
        refine Finset.prod_le_prod
          (fun _ _ => Finset.sum_nonneg fun _ _ =>
            div_nonneg (Nat.cast_nonneg _) (by positivity))
          fun i _ => ?_
        simpa [H] using sum_rowFun_N_div_prod s N i
      have hcard : (Finset.univ.erase i0).card = s - 1 := by
        simp [Finset.card_erase_of_mem, Fintype.card_fin]
      calc
        ∏ i, ∑ r ∈ S i, g i r =
            ∏ i ∈ Finset.univ.erase i0, ∑ r ∈ rowFunFinset s N i,
              (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) := hall
        _ ≤ ∏ i ∈ Finset.univ.erase i0, H := hrows
        _ = H ^ (s - 1) := by rw [Finset.prod_const, hcard]
    calc
      _ = ∑ t ∈ piFinset S, ∏ i, g i (t i) := hsum_eq
      _ = ∏ i, ∑ r ∈ S i, g i r := hfactor
      _ ≤ H ^ (s - 1) := hbound_factor
  -- Main estimate via peeling row 0.
  have hmain :
      ∑ f ∈ matrixFunFinset s N, sigmaIIFunWeight s N h0 R f ≤
        Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T * H ^ (s - 1) := by
    rw [sum_matrixFun_eq_sum_combine s N i0 (sigmaIIFunWeight s N h0 R)]
    have hpoint :
        ∀ t ∈ tailsFinset s N i0,
          ∑ r0 ∈ rowFunFinset s N i0,
              sigmaIIFunWeight s N h0 R (combineRow i0 r0 t) ≤
            Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T *
              ∏ i ∈ Finset.univ.erase i0, (N : ℝ) / (funRowOff t i : ℝ) := by
      intro t ht
      set B : ℕ := ∏ i ∈ Finset.univ.erase i0, t i i0
      set Tail : ℝ :=
        ∏ i ∈ Finset.univ.erase i0, (N : ℝ) / (funRowOff t i : ℝ)
      have hBpos : 0 < B := by
        refine Finset.prod_pos fun i hi => ?_
        have hine : i ≠ i0 := (Finset.mem_erase.1 hi).1
        have hrow : t i ∈ rowFunFinset s N i := by
          simpa [tailsFinset, hine] using mem_piFinset.1 ht i
        exact (Finset.mem_Icc.1 (mem_rowFunFinset_off hrow (Ne.symm hine))).1
      have hrewrite :
          ∑ r0 ∈ rowFunFinset s N i0,
              sigmaIIFunWeight s N h0 R (combineRow i0 r0 t) =
            ∑ r0 ∈ rowFunFinset s N i0,
              if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                  (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                (N : ℝ) / (B : ℝ) * Tail else 0 := by
        refine Finset.sum_congr rfl fun r0 hr0 => ?_
        have hA : funRowOff (combineRow i0 r0 t) i0 =
            ∏ j ∈ Finset.univ.erase i0, r0 j := funRowOff_combine_i0 i0 r0 t
        have hB' : funColOff (combineRow i0 r0 t) i0 = B := by
          simpa [B] using funColOff_combine_i0 i0 r0 t
        have hTail :
            ∏ i ∈ Finset.univ.erase i0,
                (N : ℝ) / (funRowOff (combineRow i0 r0 t) i : ℝ) = Tail := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hine : i ≠ i0 := (Finset.mem_erase.1 hi).1
          rw [funRowOff_combine_ne i0 r0 t hine]
        simp [sigmaIIFunWeight, i0, hA, hB', hTail, Tail]
      rw [hrewrite]
      have hcount :
          ∑ r0 ∈ rowFunFinset s N i0,
              (if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                  (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                (1 : ℝ) else 0) ≤
            ∑ n ∈ R B ∩ Finset.Icc 1 (min N B), (tau (s - 1) n : ℝ) := by
        have hmaps :
            ∀ r0 ∈ rowFunFinset s N i0,
              (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ Finset.Icc 1 N := by
          intro r0 hr0
          exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt (mem_rowFunFinset_prod_pos hr0),
            mem_rowFunFinset_prod_le hr0⟩
        have hfib :
            ∑ r0 ∈ rowFunFinset s N i0,
                (if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                    (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                  (1 : ℝ) else 0) =
              ∑ n ∈ Finset.Icc 1 N,
                if n ∈ R B ∧ n ≤ B then
                  (((rowFunFinset s N i0).filter
                      fun r => (∏ j ∈ Finset.univ.erase i0, r j) = n).card : ℝ)
                else 0 := by
          have h :=
            (Finset.sum_fiberwise_of_maps_to' (s := rowFunFinset s N i0)
              (t := Finset.Icc 1 N)
              (g := fun r0 => ∏ j ∈ Finset.univ.erase i0, r0 j) hmaps
              (f := fun n => if n ∈ R B ∧ n ≤ B then (1 : ℝ) else 0)).symm
          calc
            _ = ∑ n ∈ Finset.Icc 1 N,
                ∑ r0 ∈ (rowFunFinset s N i0).filter
                    (fun r => (∏ j ∈ Finset.univ.erase i0, r j) = n),
                  (if n ∈ R B ∧ n ≤ B then (1 : ℝ) else 0) := h
            _ = _ := by
              refine Finset.sum_congr rfl fun n _ => ?_
              by_cases hmem : n ∈ R B ∧ n ≤ B
              · simp [hmem, Finset.sum_const, nsmul_eq_mul]
              · simp [hmem]
        rw [hfib]
        have hfilter :
            ∑ n ∈ Finset.Icc 1 N,
                (if n ∈ R B ∧ n ≤ B then
                  (((rowFunFinset s N i0).filter
                    fun r => (∏ j ∈ Finset.univ.erase i0, r j) = n).card : ℝ)
                else 0) =
              ∑ n ∈ R B ∩ Finset.Icc 1 (min N B),
                (((rowFunFinset s N i0).filter
                  fun r => (∏ j ∈ Finset.univ.erase i0, r j) = n).card : ℝ) := by
          rw [← Finset.sum_filter]
          congr 1
          ext n
          constructor
          · intro h
            rcases Finset.mem_filter.1 h with ⟨hnI, hnR, hnB⟩
            rcases Finset.mem_Icc.1 hnI with ⟨hn1, hnN⟩
            exact Finset.mem_inter.2
              ⟨hnR, Finset.mem_Icc.2 ⟨hn1, le_min hnN hnB⟩⟩
          · intro h
            rcases Finset.mem_inter.1 h with ⟨hnR, hnI⟩
            rcases Finset.mem_Icc.1 hnI with ⟨hn1, hnmin⟩
            exact Finset.mem_filter.2
              ⟨Finset.mem_Icc.2 ⟨hn1, hnmin.trans (min_le_left _ _)⟩, hnR,
                hnmin.trans (min_le_right _ _)⟩
        rw [hfilter]
        refine Finset.sum_le_sum fun n hn => ?_
        have hnIcc : n ∈ Finset.Icc 1 (min N B) := (Finset.mem_inter.1 hn).2
        have hn1 := (Finset.mem_Icc.1 hnIcc).1
        have hnN : n ≤ N := (Finset.mem_Icc.1 hnIcc).2.trans (min_le_left _ _)
        exact_mod_cast card_rowFun_eq_prod_le_tau (i := i0) hn1 hnN
      have hsumTau :
          (∑ n ∈ R B ∩ Finset.Icc 1 (min N B), (tau (s - 1) n : ℝ)) ≤
            Real.sqrt (3 * Cuni) * Real.sqrt δ * (B : ℝ) * T :=
        sum_tau_on_R_le s N B δ (R B) Cuni hs hN hBpos hδ.le
          (le_of_lt (by simpa [Cuni] using hCd))
          (by simpa [Cuni] using hR B hBpos)
      have hTailNonneg : 0 ≤ Tail :=
        Finset.prod_nonneg fun _ _ =>
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hweighted :
          ∑ r0 ∈ rowFunFinset s N i0,
              (if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                  (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                (N : ℝ) / (B : ℝ) * Tail else 0) =
            ((N : ℝ) / (B : ℝ) * Tail) *
              ∑ r0 ∈ rowFunFinset s N i0,
                (if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                    (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                  (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r0 _ => ?_
        split_ifs <;> ring
      rw [hweighted]
      have hfactorNonneg : 0 ≤ (N : ℝ) / (B : ℝ) * Tail :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hTailNonneg
      calc
        ((N : ℝ) / (B : ℝ) * Tail) *
            ∑ r0 ∈ rowFunFinset s N i0,
              (if (∏ j ∈ Finset.univ.erase i0, r0 j) ∈ R B ∧
                  (∏ j ∈ Finset.univ.erase i0, r0 j) ≤ B then
                (1 : ℝ) else 0) ≤
          ((N : ℝ) / (B : ℝ) * Tail) *
            ∑ n ∈ R B ∩ Finset.Icc 1 (min N B), (tau (s - 1) n : ℝ) :=
          mul_le_mul_of_nonneg_left hcount hfactorNonneg
        _ ≤ ((N : ℝ) / (B : ℝ) * Tail) *
            (Real.sqrt (3 * Cuni) * Real.sqrt δ * (B : ℝ) * T) :=
          mul_le_mul_of_nonneg_left hsumTau hfactorNonneg
        _ = Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T * Tail := by
          field_simp [ne_of_gt (Nat.cast_pos.mpr hBpos)]
    calc
      ∑ t ∈ tailsFinset s N i0,
          ∑ r0 ∈ rowFunFinset s N i0,
            sigmaIIFunWeight s N h0 R (combineRow i0 r0 t) ≤
        ∑ t ∈ tailsFinset s N i0,
          Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T *
            ∏ i ∈ Finset.univ.erase i0,
              (N : ℝ) / (funRowOff t i : ℝ) :=
        Finset.sum_le_sum hpoint
      _ = (Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T) *
          ∑ t ∈ tailsFinset s N i0,
            ∏ i ∈ Finset.univ.erase i0,
              (N : ℝ) / (funRowOff t i : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T) * H ^ (s - 1) := by
        exact mul_le_mul_of_nonneg_left htail (by positivity)
      _ = Real.sqrt (3 * Cuni) * Real.sqrt δ * (N : ℝ) * T * H ^ (s - 1) := by
          ring
  simpa [Cuni, T, H] using hmain

/-! ### Return from unrestricted matrices to J1 fibres -/

theorem J1_sigma_II_le_delta_row_factor_filter (d s N A : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (_hA : 1 ≤ A)
    (_hAN : A < N) (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτbound : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ (J1Fibres s N A).filter
          (fun k => k.rowOffDiag ⟨0, by omega⟩ <
            k.colOffDiag ⟨0, by omega⟩),
        if k.rowOffDiag ⟨0, by omega⟩ ∈ R (k.colOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  have h0 : 0 < s := by omega
  let S := (J1Fibres s N A).filter
    (fun k => k.rowOffDiag ⟨0, h0⟩ < k.colOffDiag ⟨0, h0⟩)
  have hmatrix := matrixFun_sigma_II_bound d s N δ R Cd Cτ
    hs hN hδ hCd hCτ hτbound hR
  exact le_trans (by
    calc
    (∑ k ∈ S,
        if k.rowOffDiag ⟨0, h0⟩ ∈ R (k.colOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) ≤
      ∑ k ∈ S, sigmaIIFunWeight s N h0 R k.a := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_filter.1 hk
        by_cases hex :
            k.rowOffDiag ⟨0, h0⟩ ∈ R (k.colOffDiag ⟨0, h0⟩)
        · have hle :
              k.rowOffDiag ⟨0, h0⟩ ≤ k.colOffDiag ⟨0, h0⟩ :=
            Nat.le_of_lt hk'.2
          simp only [hex, if_true]
          simpa [sigmaIIFunWeight, funRowOff_eq_rowOffDiag,
            funColOff_eq_colOffDiag, hex, hle] using
            J1FullWeight_le_funWeight_A_lt_B k N h0 hk'.2
        · simp [sigmaIIFunWeight, funRowOff_eq_rowOffDiag,
            funColOff_eq_colOffDiag, hex]
    _ = ∑ f ∈ S.image (fun k => k.a), sigmaIIFunWeight s N h0 R f := by
      symm
      apply Finset.sum_image
      intro k₁ _ k₂ _ ha
      cases k₁
      cases k₂
      simp_all
    _ ≤ ∑ f ∈ matrixFunFinset s N, sigmaIIFunWeight s N h0 R f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro f hf
        rcases Finset.mem_image.1 hf with ⟨k, hk, rfl⟩
        exact MatrixParam_a_mem_matrixFunFinset h0 (Finset.mem_filter.1 hk).1
      · intro f _ _
        exact sigmaIIFunWeight_nonneg s N h0 R f) hmatrix

theorem J1_sigma_II_le_delta_row_factor_sym_filter (d s N A : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (_hA : 1 ≤ A)
    (_hAN : A < N) (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτbound : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ (J1Fibres s N A).filter
          (fun k => k.colOffDiag ⟨0, by omega⟩ <
            k.rowOffDiag ⟨0, by omega⟩),
        if k.colOffDiag ⟨0, by omega⟩ ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  have h0 : 0 < s := by omega
  let S := (J1Fibres s N A).filter
    (fun k => k.colOffDiag ⟨0, h0⟩ < k.rowOffDiag ⟨0, h0⟩)
  have hmatrix := matrixFun_sigma_II_bound d s N δ R Cd Cτ
    hs hN hδ hCd hCτ hτbound hR
  exact le_trans (by
    calc
    (∑ k ∈ S,
        if k.colOffDiag ⟨0, h0⟩ ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) ≤
      ∑ k ∈ S, sigmaIIFunWeight s N h0 R (transposeFun k.a) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_filter.1 hk
        by_cases hex :
            k.colOffDiag ⟨0, h0⟩ ∈ R (k.rowOffDiag ⟨0, h0⟩)
        · have hle :
              k.colOffDiag ⟨0, h0⟩ ≤ k.rowOffDiag ⟨0, h0⟩ :=
            Nat.le_of_lt hk'.2
          simp only [hex, if_true]
          simpa [sigmaIIFunWeight, funRowOff_transpose, funColOff_transpose,
            funRowOff_eq_rowOffDiag, funColOff_eq_colOffDiag, hex, hle] using
            J1FullWeight_le_funWeight_B_lt_A k N h0 hk'.2
        · simp [sigmaIIFunWeight, funRowOff_transpose, funColOff_transpose,
            funRowOff_eq_rowOffDiag, funColOff_eq_colOffDiag, hex]
    _ = ∑ f ∈ S.image (fun k => transposeFun k.a),
          sigmaIIFunWeight s N h0 R f := by
      symm
      apply Finset.sum_image
      intro k₁ _ k₂ _ ha
      cases k₁
      cases k₂
      congr
      funext i j
      have hij := congrFun (congrFun ha j) i
      simpa [transposeFun] using hij
    _ ≤ ∑ f ∈ matrixFunFinset s N, sigmaIIFunWeight s N h0 R f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro f hf
        rcases Finset.mem_image.1 hf with ⟨k, hk, rfl⟩
        exact MatrixParam_transpose_a_mem_matrixFunFinset h0
          (Finset.mem_filter.1 hk).1
      · intro f _ _
        exact sigmaIIFunWeight_nonneg s N h0 R f) hmatrix

/-! ### Piece III fibres → unrestricted matrices -/

theorem PieceIII_rowOffDiag_le_N {s N : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ PieceIIIFibres s N) (i : Fin s) : k.rowOffDiag i ≤ N :=
  (keyScale_ge_rowOffDiag k i).trans (keyScale_le_N_of_mem_PieceIIIFibres h0 hk i)

theorem PieceIII_colOffDiag_le_N {s N : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ PieceIIIFibres s N) (i : Fin s) : k.colOffDiag i ≤ N :=
  (Nat.le_max_right _ _).trans (keyScale_le_N_of_mem_PieceIIIFibres h0 hk i)

theorem PieceIII_a_mem_matrixFunFinset {s N : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ PieceIIIFibres s N) :
    k.a ∈ matrixFunFinset s N := by
  refine mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨?_, ?_⟩
  · refine mem_piFinset.2 fun j => ?_
    by_cases hij : j = i
    · subst hij
      simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
      rcases Finset.mem_image.1 hk with ⟨x, _, rfl⟩
      simp [offDiagNormalize]
    · simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
      rcases Finset.mem_image.1 hk with ⟨x, hx, rfl⟩
      set p := offDiagNormalize (solToMatrix x)
      have hk' : p ∈ PieceIIIFibres s N := by
        simpa [PieceIIIFibres, h0, p] using Finset.mem_image.2 ⟨x, hx, rfl⟩
      have h1 : 1 ≤ p.a i j := Nat.one_le_of_lt (p.entries_pos i j)
      have hrow := PieceIII_rowOffDiag_le_N h0 hk' i
      have hdiv : p.a i j ∣ p.rowOffDiag i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)
      have hle : p.a i j ≤ N :=
        le_trans (Nat.le_of_dvd (MatrixParam.rowOffDiag_pos p i) hdiv) hrow
      simpa [hij, p] using Finset.mem_Icc.2 ⟨h1, hle⟩
  · simpa [MatrixParam.rowOffDiag] using PieceIII_rowOffDiag_le_N h0 hk i

theorem PieceIII_transpose_a_mem_matrixFunFinset {s N : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ PieceIIIFibres s N) :
    transposeFun k.a ∈ matrixFunFinset s N := by
  refine mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨?_, ?_⟩
  · refine mem_piFinset.2 fun j => ?_
    by_cases hij : j = i
    · subst hij
      simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
      rcases Finset.mem_image.1 hk with ⟨x, _, rfl⟩
      simp [transposeFun, offDiagNormalize]
    · simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
      rcases Finset.mem_image.1 hk with ⟨x, hx, rfl⟩
      set p := offDiagNormalize (solToMatrix x)
      have hk' : p ∈ PieceIIIFibres s N := by
        simpa [PieceIIIFibres, h0, p] using Finset.mem_image.2 ⟨x, hx, rfl⟩
      have h1 : 1 ≤ p.a j i := Nat.one_le_of_lt (p.entries_pos j i)
      have hcol := PieceIII_colOffDiag_le_N h0 hk' i
      have hdiv : p.a j i ∣ p.colOffDiag i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)
      have hle : p.a j i ≤ N :=
        le_trans (Nat.le_of_dvd
          (Finset.prod_pos fun _ _ => p.entries_pos _ _) hdiv) hcol
      simpa [transposeFun, hij, p] using Finset.mem_Icc.2 ⟨h1, hle⟩
  · simpa [transposeFun, MatrixParam.colOffDiag, funColOff] using
      PieceIII_colOffDiag_le_N h0 hk i

theorem PieceIII_sigma_II_le_delta_row_factor (d s N : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ)
    (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτbound : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ PieceIIIFibres_A_lt_B s N (by omega),
        if k.rowOffDiag ⟨0, by omega⟩ ∈ R (k.colOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  have h0 : 0 < s := by omega
  let S := PieceIIIFibres_A_lt_B s N h0
  have hmatrix := matrixFun_sigma_II_bound d s N δ R Cd Cτ
    hs hN hδ hCd hCτ hτbound hR
  exact le_trans (by
    calc
    (∑ k ∈ S,
        if k.rowOffDiag ⟨0, h0⟩ ∈ R (k.colOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) ≤
      ∑ k ∈ S, sigmaIIFunWeight s N h0 R k.a := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_filter.1 hk
        by_cases hex :
            k.rowOffDiag ⟨0, h0⟩ ∈ R (k.colOffDiag ⟨0, h0⟩)
        · have hle :
              k.rowOffDiag ⟨0, h0⟩ ≤ k.colOffDiag ⟨0, h0⟩ :=
            Nat.le_of_lt hk'.2
          simp only [hex, if_true]
          simpa [sigmaIIFunWeight, funRowOff_eq_rowOffDiag,
            funColOff_eq_colOffDiag, hex, hle] using
            J1FullWeight_le_funWeight_A_lt_B k N h0 hk'.2
        · simp [sigmaIIFunWeight, funRowOff_eq_rowOffDiag,
            funColOff_eq_colOffDiag, hex]
    _ = ∑ f ∈ S.image (fun k => k.a), sigmaIIFunWeight s N h0 R f := by
      symm
      apply Finset.sum_image
      intro k₁ _ k₂ _ ha
      cases k₁
      cases k₂
      simp_all
    _ ≤ ∑ f ∈ matrixFunFinset s N, sigmaIIFunWeight s N h0 R f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro f hf
        rcases Finset.mem_image.1 hf with ⟨k, hk, rfl⟩
        exact PieceIII_a_mem_matrixFunFinset h0 (Finset.mem_filter.1 hk).1
      · intro f _ _
        exact sigmaIIFunWeight_nonneg s N h0 R f) hmatrix

theorem PieceIII_sigma_II_le_delta_row_factor_sym (d s N : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ)
    (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτbound : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ PieceIIIFibres_B_lt_A s N (by omega),
        if k.colOffDiag ⟨0, by omega⟩ ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  have h0 : 0 < s := by omega
  let S := PieceIIIFibres_B_lt_A s N h0
  have hmatrix := matrixFun_sigma_II_bound d s N δ R Cd Cτ
    hs hN hδ hCd hCτ hτbound hR
  exact le_trans (by
    calc
    (∑ k ∈ S,
        if k.colOffDiag ⟨0, h0⟩ ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) ≤
      ∑ k ∈ S, sigmaIIFunWeight s N h0 R (transposeFun k.a) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_filter.1 hk
        by_cases hex :
            k.colOffDiag ⟨0, h0⟩ ∈ R (k.rowOffDiag ⟨0, h0⟩)
        · have hle :
              k.colOffDiag ⟨0, h0⟩ ≤ k.rowOffDiag ⟨0, h0⟩ :=
            Nat.le_of_lt hk'.2
          simp only [hex, if_true]
          simpa [sigmaIIFunWeight, funRowOff_transpose, funColOff_transpose,
            funRowOff_eq_rowOffDiag, funColOff_eq_colOffDiag, hex, hle] using
            J1FullWeight_le_funWeight_B_lt_A k N h0 hk'.2
        · simp [sigmaIIFunWeight, funRowOff_transpose, funColOff_transpose,
            funRowOff_eq_rowOffDiag, funColOff_eq_colOffDiag, hex]
    _ = ∑ f ∈ S.image (fun k => transposeFun k.a),
          sigmaIIFunWeight s N h0 R f := by
      symm
      apply Finset.sum_image
      intro k₁ _ k₂ _ ha
      cases k₁
      cases k₂
      congr
      funext i j
      have hij := congrFun (congrFun ha j) i
      simpa [transposeFun] using hij
    _ ≤ ∑ f ∈ matrixFunFinset s N, sigmaIIFunWeight s N h0 R f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro f hf
        rcases Finset.mem_image.1 hf with ⟨k, hk, rfl⟩
        exact PieceIII_transpose_a_mem_matrixFunFinset h0
          (Finset.mem_filter.1 hk).1
      · intro f _ _
        exact sigmaIIFunWeight_nonneg s N h0 R f) hmatrix

/-- Unrestricted matrix row-product sum ≤ `J1RowFactorSum`. -/
theorem sum_matrixFun_prod_rowOff_le_row_factor (s N : ℕ) :
    (∑ f ∈ matrixFunFinset s N,
        ∏ i : Fin s, (N : ℝ) / (funRowOff f i : ℝ)) ≤
      J1RowFactorSum s N := by
  have hprod :
      (∑ f ∈ matrixFunFinset s N,
          ∏ i : Fin s, (N : ℝ) / (funRowOff f i : ℝ)) =
        ∏ i : Fin s,
          ∑ r ∈ rowFunFinset s N i,
            (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ) := by
    simpa [matrixFunFinset, funRowOff] using
      (Finset.prod_univ_sum (t := fun i => rowFunFinset s N i)
        (f := fun i r =>
          (N : ℝ) / ((∏ j ∈ Finset.univ.erase i, r j) : ℝ))).symm
  rw [hprod, J1RowFactorSum]
  refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    fun i _ => sum_rowFun_N_div_prod s N i

theorem PieceIII_sigma_I_le_row_factor_sum (s N : ℕ) (h0 : 0 < s) :
    (∑ k ∈ PieceIIIFibres s N, J1FullWeight k N h0) ≤
      J1RowFactorSum s N := by
  let g : (Fin s → Fin s → ℕ) → ℝ :=
    fun f => ∏ i : Fin s, (N : ℝ) / (funRowOff f i : ℝ)
  have hstep1 :
      (∑ k ∈ PieceIIIFibres s N, J1FullWeight k N h0) ≤
        ∑ k ∈ PieceIIIFibres s N, g k.a := by
    refine Finset.sum_le_sum fun k _ => ?_
    simpa [g, J1WeightProdRowOffDiag, funRowOff_eq_rowOffDiag] using
      J1FullWeight_le_prod_rowOffDiag k h0
  have hstep2 :
      (∑ k ∈ PieceIIIFibres s N, g k.a) =
        ∑ f ∈ (PieceIIIFibres s N).image (fun k => k.a), g f := by
    refine (Finset.sum_image ?_).symm
    intro k₁ _ k₂ _ ha
    exact MatrixParam.ext fun i j => congrFun (congrFun ha i) j
  have hstep3 :
      (∑ f ∈ (PieceIIIFibres s N).image (fun k => k.a), g f) ≤
        ∑ f ∈ matrixFunFinset s N, g f := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro f hf
      rcases Finset.mem_image.1 hf with ⟨k, hk, rfl⟩
      exact PieceIII_a_mem_matrixFunFinset h0 hk
    · intro f _ _
      exact Finset.prod_nonneg fun _ _ => by positivity
  exact le_trans hstep1
    (le_trans (le_of_eq hstep2)
      (le_trans hstep3 (sum_matrixFun_prod_rowOff_le_row_factor s N)))

theorem PieceIII_sigma_I_side_le_row_factor_sum (s N : ℕ) (h0 : 0 < s) :
    (∑ k ∈ PieceIIIFibres_A_lt_B s N h0, J1FullWeight k N h0) ≤
      J1RowFactorSum s N ∧
    (∑ k ∈ PieceIIIFibres_B_lt_A s N h0, J1FullWeight k N h0) ≤
      J1RowFactorSum s N := by
  have htotal := PieceIII_sigma_I_le_row_factor_sum s N h0
  refine ⟨le_trans ?_ htotal, le_trans ?_ htotal⟩
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k _ _ => J1FullWeight_nonneg k N h0
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k _ _ => J1FullWeight_nonneg k N h0

end RMFLean
