/-
PDF Lemma 6 long/short fibres + Σ_I / Σ_II, using Trusted Lemma 5.

Proves `J1_long_short_sum_bound` / `J1_bound` by assembling:
- phase shape = Trusted `expSum` (proved)
- Lem5 long/short → exceptional sets (Proof axiom)
- Σ_I / Σ_II bookkeeping (Proof axioms; Σ_I uses `tau_harmonic_partial_sum`)
-/
import RMFLean.Proof.F1.J1
import RMFLean.Proof.F1.J1Lem5
import RMFLean.Proof.F1.J1RowFactor
import RMFLean.Proof.F1.J1SigmaII
import RMFLean.Proof.Setup.TailQAbsorb
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex

namespace RMFLean

/-! ### Phase shape matches Trusted `expSum` -/

theorem star_ePhase {d : ℕ} (g : CirclePoly d) (n : ℕ) :
    starRingEnd ℂ (g.ePhase n) =
      Complex.exp (2 * (Real.pi : ℂ) * I * (-(g.eval (n : ℤ) : ℂ))) := by
  simp only [CirclePoly.ePhase]
  set z : ℂ := 2 * (Real.pi : ℂ) * I * (g.eval (n : ℤ) : ℂ)
  have hstar :
      starRingEnd ℂ z = 2 * (Real.pi : ℂ) * I * (-(g.eval (n : ℤ) : ℂ)) := by
    dsimp [z]
    rw [map_mul, map_mul, map_mul]
    simp [map_ofNat, Complex.conj_I]
  calc
    starRingEnd ℂ (cexp z) = cexp (starRingEnd ℂ z) := (Complex.exp_conj z).symm
    _ = cexp (2 * (Real.pi : ℂ) * I * (-(g.eval (n : ℤ) : ℂ))) := by rw [hstar]

theorem ePhase_mul_star_eq_expSum_term {d : ℕ} (g : CirclePoly d)
    (n c D : ℕ) :
    g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D)) =
      Complex.exp (2 * (Real.pi : ℂ) * I *
        (g.eval ((n : ℤ) * c) - g.eval ((n : ℤ) * D))) := by
  rw [star_ePhase, CirclePoly.ePhase]
  have hn : ((n * c : ℕ) : ℤ) = (n : ℤ) * c := by simp
  have hm : ((n * D : ℕ) : ℤ) = (n : ℤ) * D := by simp
  rw [← Complex.exp_add]
  congr 1
  push_cast [hn, hm]
  ring

theorem J1InnerSum_eq_expSum {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) :
    J1InnerSum g k N A h0 =
      expSum d g (k.rowOffDiag ⟨0, h0⟩) (k.colOffDiag ⟨0, h0⟩) (keyHeadFibre k N A h0) := by
  simp only [J1InnerSum, expSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simpa using ePhase_mul_star_eq_expSum_term g n (k.rowOffDiag ⟨0, h0⟩) (k.colOffDiag ⟨0, h0⟩)

/-- `expSum g c D L` is the conjugate of `expSum g D c L`. -/
theorem expSum_star_swap {d : ℕ} (g : CirclePoly d) (c D : ℕ) (L : Finset ℕ) :
    expSum d g c D L = star (expSum d g D c L) := by
  calc
    expSum d g c D L =
        ∑ n ∈ L, g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D)) := by
      simp only [expSum]
      exact Finset.sum_congr rfl fun n _ =>
        (ePhase_mul_star_eq_expSum_term g n c D).symm
    _ = ∑ n ∈ L,
          star (g.ePhase (n * D) * starRingEnd ℂ (g.ePhase (n * c))) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp [star_mul, mul_comm]
    _ = star
          (∑ n ∈ L, g.ePhase (n * D) * starRingEnd ℂ (g.ePhase (n * c))) := by
      exact (star_sum (s := L)
        (fun n => g.ePhase (n * D) * starRingEnd ℂ (g.ePhase (n * c)))).symm
    _ = star (expSum d g D c L) := by
      congr 1
      simp only [expSum]
      exact Finset.sum_congr rfl fun n _ =>
        ePhase_mul_star_eq_expSum_term g n D c

/-- When `A₁ > B₁`, Lem5 wants dilate `c=B₁ < D=A₁`; the sum is the conjugate. -/
theorem norm_J1InnerSum_eq_expSum_swap {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) :
    ‖J1InnerSum g k N A h0‖ =
      ‖expSum d g (k.colOffDiag ⟨0, h0⟩) (k.rowOffDiag ⟨0, h0⟩) (keyHeadFibre k N A h0)‖ := by
  rw [J1InnerSum_eq_expSum, expSum_star_swap, norm_star]

/-! ### Weights (PDF ∏ N/M_i) — `J1FullWeight` / `J1SigmaWeight` live in `J1.lean` -/

/-- Fibres with `A₁ < B₁`. -/
noncomputable def J1Fibres_A_lt_B (s N A : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (J1Fibres s N A).filter fun k => (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩)

/-- Fibres with `B₁ < A₁`. -/
noncomputable def J1Fibres_B_lt_A (s N A : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (J1Fibres s N A).filter fun k => (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩)

/-- Fibres with `A₁ = B₁` (empty for off-diagonal `J1Support`). -/
noncomputable def J1Fibres_A_eq_B (s N A : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (J1Fibres s N A).filter fun k => (k.rowOffDiag ⟨0, h0⟩) = (k.colOffDiag ⟨0, h0⟩)

/-! ### Off-diagonal ⇒ `A₁ ≠ B₁` -/

/--
On `J1Support`, `n₁ ≠ m₁` and `n₁ = a₁₁ A₁`, `m₁ = a₁₁ B₁` with `a₁₁ > 0`,
so fibre labels satisfy `A₁ ≠ B₁`.
-/
theorem J1Fibres_A_ne_B {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) :
    (k.rowOffDiag ⟨0, h0⟩) ≠ (k.colOffDiag ⟨0, h0⟩) := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
  have hnodiag : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx).2.2
  have hn :
      x.n ⟨0, h0⟩ =
        (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ *
          (solToMatrix x).rowOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.rowProd_eq_diag_mul_offDiag, solToMatrix_rowProd]
  have hm :
      x.m ⟨0, h0⟩ =
        (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ *
          (solToMatrix x).colOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.colProd_eq_diag_mul_offDiag, solToMatrix_colProd]
  intro heq
  have heq' :
      (solToMatrix x).rowOffDiag ⟨0, h0⟩ =
        (solToMatrix x).colOffDiag ⟨0, h0⟩ := by
    rw [← offDiagNormalize_rowOffDiag, ← offDiagNormalize_colOffDiag]
    simpa using heq
  have hdiag : x.onDiag h0 := by
    simp only [Sol.onDiag, hn, hm, heq']
  exact hnodiag hdiag

theorem J1Fibres_A_eq_B_empty (s N A : ℕ) (h0 : 0 < s) :
    J1Fibres_A_eq_B s N A h0 = ∅ := by
  exact Finset.filter_eq_empty_iff.2 fun k hk heq =>
    J1Fibres_A_ne_B h0 hk heq


/-! ### `expSum` / head-fibre tools for Lemma 5 -/

theorem norm_expSum_le_card {d : ℕ} (g : CirclePoly d) (c D : ℕ) (L : Finset ℕ) :
    ‖expSum d g c D L‖ ≤ (L.card : ℝ) := by
  have hterm :
      ∀ n ∈ L,
        ‖g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D))‖ ≤ 1 := by
    intro n _
    have hnorm1 (m : ℕ) : ‖g.ePhase m‖ = 1 := by
      simp only [CirclePoly.ePhase, Complex.norm_exp]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have h1 := hnorm1 (n * c)
    have h2 : ‖starRingEnd ℂ (g.ePhase (n * D))‖ = 1 := by
      rw [Complex.norm_conj]; exact hnorm1 _
    calc
      ‖g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D))‖ =
          ‖g.ePhase (n * c)‖ * ‖starRingEnd ℂ (g.ePhase (n * D))‖ :=
        norm_mul _ _
      _ = (1 : ℝ) * 1 := by rw [h1, h2]
      _ ≤ 1 := by norm_num
  calc
    ‖expSum d g c D L‖ =
        ‖∑ n ∈ L, g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D))‖ := by
      simp only [expSum]
      exact congrArg norm (Finset.sum_congr rfl fun n _ =>
        (ePhase_mul_star_eq_expSum_term g n c D).symm)
    _ ≤ ∑ n ∈ L, ‖g.ePhase (n * c) * starRingEnd ℂ (g.ePhase (n * D))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ L, (1 : ℝ) := Finset.sum_le_sum fun n hn => hterm n hn
    _ = (L.card : ℝ) := by simp

theorem norm_J1InnerSum_le_card {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) :
    ‖J1InnerSum g k N A h0‖ ≤
      ((keyHeadFibre k N A h0).card : ℝ) := by
  rw [J1InnerSum_eq_expSum]
  exact norm_expSum_le_card g (k.rowOffDiag ⟨0, h0⟩) (k.colOffDiag ⟨0, h0⟩)
    (keyHeadFibre k N A h0)

theorem keyHeadFibre_card_le {s : ℕ} (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s)
    (hA : 1 ≤ A) (hhead : A ≤ N / keyScale k ⟨0, h0⟩) :
    (keyHeadFibre k N A h0).card ≤ N / keyScale k ⟨0, h0⟩ := by
  simp only [keyHeadFibre, Nat.card_Icc]
  omega

theorem expSum_disjUnion {d : ℕ} (g : CirclePoly d) (c D : ℕ)
    {L1 L2 : Finset ℕ} (hdisj : Disjoint L1 L2) :
    expSum d g c D (L1 ∪ L2) =
      expSum d g c D L1 + expSum d g c D L2 := by
  simp only [expSum]
  rw [Finset.sum_union hdisj]

theorem Icc_one_pred_union_Icc_A (A m : ℕ) (hA : 2 ≤ A) (hle : A ≤ m) :
    Finset.Icc 1 (A - 1) ∪ Finset.Icc A m = Finset.Icc 1 m := by
  ext n
  simp only [Finset.mem_union, Finset.mem_Icc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.trans (le_trans (Nat.sub_le _ _) hle)⟩
    · exact ⟨le_trans (by omega : 1 ≤ A) h1, h2⟩
  · intro ⟨h1, h2⟩
    by_cases hn : n < A
    · left; exact ⟨h1, by omega⟩
    · right; exact ⟨by omega, h2⟩

theorem Icc_one_pred_disjoint_Icc_A (A m : ℕ) (hA : 2 ≤ A) (hle : A ≤ m) :
    Disjoint (Finset.Icc 1 (A - 1)) (Finset.Icc A m) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext n
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, Finset.mem_Icc]
  intro ⟨h1, h2⟩; omega

theorem expSum_Icc_A_eq_sub {d : ℕ} (g : CirclePoly d) (c D N A : ℕ)
    (hA : 2 ≤ A) (hle : A ≤ N / D) :
    expSum d g c D (Finset.Icc A (N / D)) =
      expSum d g c D (Finset.Icc 1 (N / D)) -
        expSum d g c D (Finset.Icc 1 (A - 1)) := by
  have hdisj := Icc_one_pred_disjoint_Icc_A A (N / D) hA hle
  have hunion := Icc_one_pred_union_Icc_A A (N / D) hA hle
  have hsum := expSum_disjUnion g c D hdisj
  rw [hunion] at hsum
  exact eq_sub_of_add_eq' hsum.symm

theorem finset_card_union3_le (S1 S2 S3 : Finset ℕ) :
    (S1 ∪ S2 ∪ S3).card ≤ S1.card + S2.card + S3.card := by
  have := Finset.card_union_le (S1 ∪ S2) S3
  have := Finset.card_union_le S1 S2
  omega

/-- Exceptional dilate set for denominator `D` (union of up to three Lem5 bad sets). -/
noncomputable def lem5ExceptionalSet (d : ℕ) (g : CirclePoly d) (δ Cd0 : ℝ)
    (N A : ℕ) (D : ℕ) : Finset ℕ :=
  if h : 0 < D ∧ D < N ∧ (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd0) then
    let Llong := intInterval A (N / D)
    let Lshort1 := intInterval 1 (N / D)
    let Lshort2 := intInterval 1 (A - 1)
    let badLong :=
      if 2 * A < N / D then badDilates d g δ N D Llong else (∅ : Finset ℕ)
    let badShort1 :=
      if A ≤ N / D ∧ N / D ≤ 2 * A then badDilates d g δ N D Lshort1 else (∅ : Finset ℕ)
    let badShort2 :=
      if A ≤ N / D ∧ N / D ≤ 2 * A ∧ 3 ≤ A then badDilates d g δ N D Lshort2 else (∅ : Finset ℕ)
    badLong ∪ badShort1 ∪ badShort2
  else
    (∅ : Finset ℕ)

theorem lem5ExceptionalSet_subset (d : ℕ) (g : CirclePoly d) (δ Cd0 : ℝ)
    (N A D : ℕ) :
    lem5ExceptionalSet d g δ Cd0 N A D ⊆ Finset.Icc 1 (D - 1) := by
  intro c hc
  simp only [lem5ExceptionalSet] at hc
  by_cases h : 0 < D ∧ D < N ∧ (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd0)
  · simp only [dif_pos h, Finset.mem_union] at hc
    have hbad := badDilates_subset_Icc d g δ N D
    rcases hc with (hc | hc) | hc
    · by_cases hlong : 2 * A < N / D
      · simp only [hlong, ↓reduceIte] at hc
        exact hbad _ hc
      · simp only [hlong, ↓reduceIte] at hc; cases hc
    · by_cases hshort1 : A ≤ N / D ∧ N / D ≤ 2 * A
      · simp only [hshort1, ↓reduceIte] at hc
        exact hbad _ hc
      · simp only [hshort1, ↓reduceIte] at hc; cases hc
    · by_cases hshort2 : A ≤ N / D ∧ N / D ≤ 2 * A ∧ 3 ≤ A
      · simp only [hshort2, ↓reduceIte] at hc
        exact hbad _ hc
      · simp only [hshort2, ↓reduceIte] at hc; cases hc
  · simp only [dif_neg h] at hc
    cases hc

theorem lem5ExceptionalSet_card_le (d : ℕ) (g : CirclePoly d) (δ : ℝ)
    (Cd Cbad : ℝ) (N A : ℕ) (hCbad : 0 < Cbad) (hCd5 : 5 < Cd)
    (h3Cbad : 3 * Cbad ≤ Cd)
    (hlem :
      ∀ (g' : CirclePoly d) (δ' : ℝ) (N' D' lo hi : ℕ),
        0 < δ' → δ' < 1 / 8 → 0 < D' → D' < N' →
          (N' : ℝ) / (D' : ℝ) > Real.rpow δ' (-Cd) →
          let L := intInterval lo hi
          1 ≤ lo → hi ≤ 2 * (N' / D') → cardAsymp L N' D' →
          (lo : ℝ) < Real.rpow δ' (-(Cd + 3)) →
          ((badDilates d g' δ' N' D' L).card : ℝ) ≤ Cbad * δ' * (D' : ℝ) ∨
            ∃ K : ℤ, K ≠ 0 ∧
              (|K| : ℝ) ≤ Real.rpow δ' (-Cd) ∧
              (K • g').cInfinityNorm N' ≤ Real.rpow δ' (-Cd))
    (hNotDio : ¬ altDiophantine d N g δ Cd)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ)) (hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (D : ℕ) (_hD : 0 < D) :
    ((lem5ExceptionalSet d g δ Cd N A D).card : ℝ) ≤ Cd * δ * (D : ℝ) := by
  by_cases h : 0 < D ∧ D < N ∧ (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd)
  · rcases h with ⟨hDpos, hDN, hND⟩
    have hA3 : 3 ≤ A := A_ge_three δ Cd A hδ hδ' hCd5 hAlo
    have hAloδ : (A : ℝ) < Real.rpow δ (-(Cd + 3)) :=
      lo_lt_rpow_neg_Cd_add_three δ Cd A hAhi
    have h1lo : (1 : ℝ) < Real.rpow δ (-(Cd + 3)) := by
      have h1A : (1 : ℝ) < (A : ℝ) := by
        have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA3
        linarith
      exact lt_trans h1A hAloδ
    have hbad :=
      lem5_badDilates_card d g δ Cd Cbad N hCbad hlem hNotDio hδ hδ'
    set badLong :=
      if 2 * A < N / D then badDilates d g δ N D (intInterval A (N / D))
      else (∅ : Finset ℕ)
    set badShort1 :=
      if A ≤ N / D ∧ N / D ≤ 2 * A then
        badDilates d g δ N D (intInterval 1 (N / D))
      else (∅ : Finset ℕ)
    set badShort2 :=
      if A ≤ N / D ∧ N / D ≤ 2 * A ∧ 3 ≤ A then
        badDilates d g δ N D (intInterval 1 (A - 1))
      else (∅ : Finset ℕ)
    have hguard : 0 < D ∧ D < N ∧ (N : ℝ) / (D : ℝ) > Real.rpow δ (-Cd) :=
      ⟨hDpos, hDN, hND⟩
    have hR :
        lem5ExceptionalSet d g δ Cd N A D = badLong ∪ badShort1 ∪ badShort2 := by
      simp only [lem5ExceptionalSet, dif_pos hguard, badLong, badShort1, badShort2]
    have hlong_card : (badLong.card : ℝ) ≤ Cbad * δ * D := by
      dsimp [badLong]
      split_ifs with hlong
      · exact hbad D A (N / D) hDpos hDN hND (by omega)
          (by omega : N / D ≤ 2 * (N / D))
          (by simpa [intInterval] using cardAsymp_Icc_A_long N D A hDpos (by omega) hlong)
          hAloδ
      · simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    have hshort1_card : (badShort1.card : ℝ) ≤ Cbad * δ * D := by
      dsimp [badShort1]
      split_ifs with hshort
      · rcases hshort with ⟨hNDle, _⟩
        have hND1 : 1 ≤ N / D := le_trans (by omega : 1 ≤ A) hNDle
        exact hbad D 1 (N / D) hDpos hDN hND (by decide)
          (by omega : N / D ≤ 2 * (N / D))
          (by simpa [intInterval] using cardAsymp_Icc_one N D hDpos hND1)
          (by simpa using h1lo)
      · simp only [Finset.card_empty, Nat.cast_zero]; positivity
    have hshort2_card : (badShort2.card : ℝ) ≤ Cbad * δ * D := by
      dsimp [badShort2]
      split_ifs with hshort
      · rcases hshort with ⟨hNDle, hshort2, _⟩
        exact hbad D 1 (A - 1) hDpos hDN hND (by decide)
          (by omega : A - 1 ≤ 2 * (N / D))
          (by simpa [intInterval] using
            cardAsymp_Icc_one_pred N D A hDpos hA3 hshort2 hNDle)
          (by simpa using h1lo)
      · simp only [Finset.card_empty, Nat.cast_zero]; positivity
    have hunion :
        ((lem5ExceptionalSet d g δ Cd N A D).card : ℝ) ≤ 3 * Cbad * δ * D := by
      rw [hR]
      have hle := finset_card_union3_le badLong badShort1 badShort2
      have hcast :
          ((badLong ∪ badShort1 ∪ badShort2).card : ℝ) ≤
            (badLong.card + badShort1.card + badShort2.card : ℝ) := by
        exact_mod_cast hle
      linarith [hlong_card, hshort1_card, hshort2_card]
    have hscale : 3 * Cbad * δ * (D : ℝ) ≤ Cd * δ * (D : ℝ) := by
      nlinarith [h3Cbad, le_of_lt hδ]
    exact le_trans hunion hscale
  · simp only [lem5ExceptionalSet, dif_neg h, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Pointwise Lem5 bound on `{A₁ < B₁}` fibres. -/
theorem lem5_pointwise_A_lt_B (d : ℕ) (g : CirclePoly d) (δ Cd : ℝ)
    (s N A : ℕ) (h0 : 0 < s) (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd5 : 5 < Cd)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ)) (_hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (R : ℕ → Finset ℕ)
    (hR : ∀ D : ℕ, R D = lem5ExceptionalSet d g δ Cd N A D)
    (k : MatrixParam s) (hk : k ∈ J1Fibres_A_lt_B s N A h0) :
    ‖J1InnerSum g k N A h0‖ ≤
      (2 * δ) * (N : ℝ) / (k.colOffDiag ⟨0, h0⟩) +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          (N : ℝ) / (k.colOffDiag ⟨0, h0⟩) else 0) := by
  have hkJ1 : k ∈ J1Fibres s N A := (Finset.mem_filter.1 hk).1
  have hAB : k.rowOffDiag ⟨0, h0⟩ < k.colOffDiag ⟨0, h0⟩ :=
    (Finset.mem_filter.1 hk).2
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = B1 := max_eq_right (Nat.le_of_lt hAB)
  have hA3 : 3 ≤ A := A_ge_three δ Cd A hδ hδ' hCd5 hAlo
  have hA1 : 1 ≤ A := le_trans (by norm_num : 1 ≤ 3) hA3
  have hhead := J1Fibre_head_nonempty s N A k h0 hkJ1 hA1
  have hheadB : A ≤ N / B1 := by simpa [hM] using hhead
  have hApos : 0 < A1 := k.rowOffDiag_pos ⟨0, h0⟩
  have hBpos : 0 < B1 := Finset.prod_pos fun _ _ => k.entries_pos _ _
  have hkIII : k ∈ PieceIIIFibres s N :=
    J1Fibres_subset_PieceIIIFibres s N A hkJ1
  have hB_le_N : B1 ≤ N := by
    simpa [hM] using keyScale_le_N_of_mem_PieceIIIFibres h0 hkIII ⟨0, h0⟩
  have hBN : B1 < N := by
    by_contra hge
    have hEq : B1 = N := le_antisymm hB_le_N (le_of_not_gt hge)
    have hNpos : 0 < N := lt_of_lt_of_le hBpos hB_le_N
    have hdiv : N / B1 = 1 := by rw [hEq, Nat.div_self hNpos]
    have hAle : A ≤ 1 := by simpa [hdiv] using hheadB
    have hlt : A < 3 := lt_of_le_of_lt hAle (by decide : (1 : ℕ) < 3)
    exact (not_le_of_gt hlt) hA3
  have hND : (N : ℝ) / (B1 : ℝ) > Real.rpow δ (-Cd) :=
    N_div_D_gt_rpow_neg_Cd δ Cd A N B1 hδ hAlo hheadB hBpos
  have hguard : 0 < B1 ∧ B1 < N ∧ (N : ℝ) / (B1 : ℝ) > Real.rpow δ (-Cd) :=
    ⟨hBpos, hBN, hND⟩
  set Llong := intInterval A (N / B1)
  set Lshort1 := intInterval 1 (N / B1)
  set Lshort2 := intInterval 1 (A - 1)
  set badLong :=
    if 2 * A < N / B1 then badDilates d g δ N B1 Llong else (∅ : Finset ℕ)
  set badShort1 :=
    if A ≤ N / B1 ∧ N / B1 ≤ 2 * A then badDilates d g δ N B1 Lshort1
    else (∅ : Finset ℕ)
  set badShort2 :=
    if A ≤ N / B1 ∧ N / B1 ≤ 2 * A ∧ 3 ≤ A then badDilates d g δ N B1 Lshort2
    else (∅ : Finset ℕ)
  have hRval : R B1 = badLong ∪ badShort1 ∪ badShort2 := by
    rw [hR]
    simp only [lem5ExceptionalSet, dif_pos hguard, badLong, badShort1, badShort2,
      Llong, Lshort1, Lshort2]
  have hIcc : A1 ∈ Finset.Icc 1 (B1 - 1) := by
    refine Finset.mem_Icc.2 ⟨Nat.one_le_of_lt hApos, ?_⟩
    exact Nat.le_sub_one_of_lt hAB
  have hnorm :
      ‖J1InnerSum g k N A h0‖ =
        ‖expSum d g A1 B1 (Finset.Icc A (N / B1))‖ := by
    rw [J1InnerSum_eq_expSum]
    simp only [keyHeadFibre, hM, A1, B1]
  have htriv : ‖J1InnerSum g k N A h0‖ ≤ (N : ℝ) / B1 := by
    rw [hnorm]
    refine le_trans (norm_expSum_le_card g A1 B1 _) ?_
    have hc : ((Finset.Icc A (N / B1)).card : ℝ) ≤ ↑(N / B1) := by
      exact_mod_cast (by
        rw [Nat.card_Icc]
        omega)
    exact le_trans hc Nat.cast_div_le
  by_cases hmem : A1 ∈ R B1
  · simp only [hmem, ↓reduceIte]
    have h2 : 0 ≤ (2 * δ) * (N : ℝ) / B1 := by positivity
    linarith [htriv]
  · simp only [hmem, ↓reduceIte, add_zero]
    have hnotin_union : A1 ∉ badLong ∪ badShort1 ∪ badShort2 := by
      simpa [hRval] using hmem
    have hLS := key_long_or_short k h0 (by simpa [hM] using hhead)
    rcases hLS with hLong | hShort
    · have hLong' : 2 * A < N / B1 := by simpa [KeyIsLong, hM] using hLong
      have hbadEq : badLong = badDilates d g δ N B1 Llong := by
        simp [badLong, hLong']
      have hnotin : A1 ∉ badDilates d g δ N B1 Llong := by
        intro hin
        exact hnotin_union (by simp [hbadEq, hin])
      have hle := not_mem_badDilates_norm_le g δ N B1 Llong A1
        (by simpa [Llong, intInterval] using hIcc) hnotin
      have hle' : ‖expSum d g A1 B1 (Finset.Icc A (N / B1))‖ ≤ δ * (N : ℝ) / B1 := by
        simpa [Llong, intInterval] using hle
      have h2 : δ * (N : ℝ) / B1 ≤ (2 * δ) * (N : ℝ) / B1 := by
        have hδle : (δ : ℝ) ≤ 2 * δ := by linarith [le_of_lt hδ]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
      exact le_trans (by simpa [hnorm] using hle') h2
    · have hShort' : A ≤ N / B1 ∧ N / B1 ≤ 2 * A := by
        simpa [KeyIsShort, hM] using hShort
      have hA2 : 2 ≤ A := le_trans (by norm_num : 2 ≤ 3) hA3
      have hdiff :
          expSum d g A1 B1 (Finset.Icc A (N / B1)) =
            expSum d g A1 B1 (Finset.Icc 1 (N / B1)) -
              expSum d g A1 B1 (Finset.Icc 1 (A - 1)) :=
        expSum_Icc_A_eq_sub g A1 B1 N A hA2 hShort'.1
      have hbad1 : badShort1 = badDilates d g δ N B1 Lshort1 := by
        simp [badShort1, hShort']
      have hbad2 : badShort2 = badDilates d g δ N B1 Lshort2 := by
        simp [badShort2, hShort', hA3]
      have hnotin1 : A1 ∉ badDilates d g δ N B1 Lshort1 := by
        intro hin
        apply hnotin_union
        simp [hbad1, hin]
      have hnotin2 : A1 ∉ badDilates d g δ N B1 Lshort2 := by
        intro hin
        apply hnotin_union
        refine Finset.mem_union.2 (Or.inr ?_)
        simpa [hbad2] using hin
      have hle1 := not_mem_badDilates_norm_le g δ N B1 Lshort1 A1
        (by simpa [Lshort1, intInterval] using hIcc) hnotin1
      have hle2 := not_mem_badDilates_norm_le g δ N B1 Lshort2 A1
        (by simpa [Lshort2, intInterval] using hIcc) hnotin2
      have hle1' :
          ‖expSum d g A1 B1 (Finset.Icc 1 (N / B1))‖ ≤ δ * (N : ℝ) / B1 := by
        simpa [Lshort1, intInterval] using hle1
      have hle2' :
          ‖expSum d g A1 B1 (Finset.Icc 1 (A - 1))‖ ≤ δ * (N : ℝ) / B1 := by
        simpa [Lshort2, intInterval] using hle2
      have hsum :
          ‖expSum d g A1 B1 (Finset.Icc A (N / B1))‖ ≤
            (2 * δ) * (N : ℝ) / B1 := by
        rw [hdiff]
        refine le_trans (norm_sub_le _ _) ?_
        calc
          ‖expSum d g A1 B1 (Finset.Icc 1 (N / B1))‖ +
              ‖expSum d g A1 B1 (Finset.Icc 1 (A - 1))‖ ≤
            δ * (N : ℝ) / B1 + δ * (N : ℝ) / B1 := add_le_add hle1' hle2'
          _ = (2 * δ) * (N : ℝ) / B1 := by ring
      simpa [hnorm] using hsum

/-- Pointwise Lem5 bound on `{B₁ < A₁}` fibres (conjugate swap). -/
theorem lem5_pointwise_B_lt_A (d : ℕ) (g : CirclePoly d) (δ Cd : ℝ)
    (s N A : ℕ) (h0 : 0 < s) (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hCd5 : 5 < Cd)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ)) (_hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (R : ℕ → Finset ℕ)
    (hR : ∀ D : ℕ, R D = lem5ExceptionalSet d g δ Cd N A D)
    (k : MatrixParam s) (hk : k ∈ J1Fibres_B_lt_A s N A h0) :
    ‖J1InnerSum g k N A h0‖ ≤
      (2 * δ) * (N : ℝ) / (k.rowOffDiag ⟨0, h0⟩) +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          (N : ℝ) / (k.rowOffDiag ⟨0, h0⟩) else 0) := by
  have hkJ1 : k ∈ J1Fibres s N A := (Finset.mem_filter.1 hk).1
  have hBA : k.colOffDiag ⟨0, h0⟩ < k.rowOffDiag ⟨0, h0⟩ :=
    (Finset.mem_filter.1 hk).2
  set A1 := k.rowOffDiag ⟨0, h0⟩
  set B1 := k.colOffDiag ⟨0, h0⟩
  have hM : keyScale k ⟨0, h0⟩ = A1 := max_eq_left (Nat.le_of_lt hBA)
  have hA3 : 3 ≤ A := A_ge_three δ Cd A hδ hδ' hCd5 hAlo
  have hA1 : 1 ≤ A := le_trans (by norm_num : 1 ≤ 3) hA3
  have hhead := J1Fibre_head_nonempty s N A k h0 hkJ1 hA1
  have hheadA : A ≤ N / A1 := by simpa [hM] using hhead
  have hBpos : 0 < B1 := Finset.prod_pos fun _ _ => k.entries_pos _ _
  have hApos : 0 < A1 := k.rowOffDiag_pos ⟨0, h0⟩
  have hkIII : k ∈ PieceIIIFibres s N :=
    J1Fibres_subset_PieceIIIFibres s N A hkJ1
  have hA_le_N : A1 ≤ N := by
    simpa [hM] using keyScale_le_N_of_mem_PieceIIIFibres h0 hkIII ⟨0, h0⟩
  have hAN : A1 < N := by
    by_contra hge
    have hEq : A1 = N := le_antisymm hA_le_N (le_of_not_gt hge)
    have hNpos : 0 < N := lt_of_lt_of_le hApos hA_le_N
    have hdiv : N / A1 = 1 := by rw [hEq, Nat.div_self hNpos]
    have hAle : A ≤ 1 := by simpa [hdiv] using hheadA
    have hlt : A < 3 := lt_of_le_of_lt hAle (by decide : (1 : ℕ) < 3)
    exact (not_le_of_gt hlt) hA3
  have hND : (N : ℝ) / (A1 : ℝ) > Real.rpow δ (-Cd) :=
    N_div_D_gt_rpow_neg_Cd δ Cd A N A1 hδ hAlo hheadA hApos
  have hguard : 0 < A1 ∧ A1 < N ∧ (N : ℝ) / (A1 : ℝ) > Real.rpow δ (-Cd) :=
    ⟨hApos, hAN, hND⟩
  set Llong := intInterval A (N / A1)
  set Lshort1 := intInterval 1 (N / A1)
  set Lshort2 := intInterval 1 (A - 1)
  set badLong :=
    if 2 * A < N / A1 then badDilates d g δ N A1 Llong else (∅ : Finset ℕ)
  set badShort1 :=
    if A ≤ N / A1 ∧ N / A1 ≤ 2 * A then badDilates d g δ N A1 Lshort1
    else (∅ : Finset ℕ)
  set badShort2 :=
    if A ≤ N / A1 ∧ N / A1 ≤ 2 * A ∧ 3 ≤ A then badDilates d g δ N A1 Lshort2
    else (∅ : Finset ℕ)
  have hRval : R A1 = badLong ∪ badShort1 ∪ badShort2 := by
    rw [hR]
    simp only [lem5ExceptionalSet, dif_pos hguard, badLong, badShort1, badShort2,
      Llong, Lshort1, Lshort2]
  have hIcc : B1 ∈ Finset.Icc 1 (A1 - 1) := by
    refine Finset.mem_Icc.2 ⟨Nat.one_le_of_lt hBpos, Nat.le_sub_one_of_lt hBA⟩
  have hnorm :
      ‖J1InnerSum g k N A h0‖ =
        ‖expSum d g B1 A1 (Finset.Icc A (N / A1))‖ := by
    rw [norm_J1InnerSum_eq_expSum_swap]
    simp only [keyHeadFibre, hM, A1, B1]
  have htriv : ‖J1InnerSum g k N A h0‖ ≤ (N : ℝ) / A1 := by
    rw [hnorm]
    refine le_trans (norm_expSum_le_card g B1 A1 _) ?_
    have hc : ((Finset.Icc A (N / A1)).card : ℝ) ≤ ↑(N / A1) := by
      exact_mod_cast (by
        rw [Nat.card_Icc]
        omega)
    exact le_trans hc Nat.cast_div_le
  by_cases hmem : B1 ∈ R A1
  · simp only [hmem, ↓reduceIte]
    have h2 : 0 ≤ (2 * δ) * (N : ℝ) / A1 := by positivity
    linarith [htriv]
  · simp only [hmem, ↓reduceIte, add_zero]
    have hnotin_union : B1 ∉ badLong ∪ badShort1 ∪ badShort2 := by
      simpa [hRval] using hmem
    have hLS := key_long_or_short k h0 (by simpa [hM] using hhead)
    rcases hLS with hLong | hShort
    · have hLong' : 2 * A < N / A1 := by simpa [KeyIsLong, hM] using hLong
      have hbadEq : badLong = badDilates d g δ N A1 Llong := by
        simp [badLong, hLong']
      have hnotin : B1 ∉ badDilates d g δ N A1 Llong := by
        intro hin
        apply hnotin_union
        simp [hbadEq, hin]
      have hle := not_mem_badDilates_norm_le g δ N A1 Llong B1
        (by simpa [Llong, intInterval] using hIcc) hnotin
      have hle' : ‖expSum d g B1 A1 (Finset.Icc A (N / A1))‖ ≤ δ * (N : ℝ) / A1 := by
        simpa [Llong, intInterval] using hle
      have h2 : δ * (N : ℝ) / A1 ≤ (2 * δ) * (N : ℝ) / A1 := by
        have hδle : (δ : ℝ) ≤ 2 * δ := by linarith [le_of_lt hδ]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
      exact le_trans (by simpa [hnorm] using hle') h2
    · have hShort' : A ≤ N / A1 ∧ N / A1 ≤ 2 * A := by
        simpa [KeyIsShort, hM] using hShort
      have hA2 : 2 ≤ A := le_trans (by norm_num : 2 ≤ 3) hA3
      have hdiff :
          expSum d g B1 A1 (Finset.Icc A (N / A1)) =
            expSum d g B1 A1 (Finset.Icc 1 (N / A1)) -
              expSum d g B1 A1 (Finset.Icc 1 (A - 1)) :=
        expSum_Icc_A_eq_sub g B1 A1 N A hA2 hShort'.1
      have hbad1 : badShort1 = badDilates d g δ N A1 Lshort1 := by
        simp [badShort1, hShort']
      have hbad2 : badShort2 = badDilates d g δ N A1 Lshort2 := by
        simp [badShort2, hShort', hA3]
      have hnotin1 : B1 ∉ badDilates d g δ N A1 Lshort1 := by
        intro hin
        apply hnotin_union
        simp [hbad1, hin]
      have hnotin2 : B1 ∉ badDilates d g δ N A1 Lshort2 := by
        intro hin
        apply hnotin_union
        refine Finset.mem_union.2 (Or.inr ?_)
        simpa [hbad2] using hin
      have hle1 := not_mem_badDilates_norm_le g δ N A1 Lshort1 B1
        (by simpa [Lshort1, intInterval] using hIcc) hnotin1
      have hle2 := not_mem_badDilates_norm_le g δ N A1 Lshort2 B1
        (by simpa [Lshort2, intInterval] using hIcc) hnotin2
      have hle1' :
          ‖expSum d g B1 A1 (Finset.Icc 1 (N / A1))‖ ≤ δ * (N : ℝ) / A1 := by
        simpa [Lshort1, intInterval] using hle1
      have hle2' :
          ‖expSum d g B1 A1 (Finset.Icc 1 (A - 1))‖ ≤ δ * (N : ℝ) / A1 := by
        simpa [Lshort2, intInterval] using hle2
      have hsum :
          ‖expSum d g B1 A1 (Finset.Icc A (N / A1))‖ ≤
            (2 * δ) * (N : ℝ) / A1 := by
        rw [hdiff]
        refine le_trans (norm_sub_le _ _) ?_
        calc
          ‖expSum d g B1 A1 (Finset.Icc 1 (N / A1))‖ +
              ‖expSum d g B1 A1 (Finset.Icc 1 (A - 1))‖ ≤
            δ * (N : ℝ) / A1 + δ * (N : ℝ) / A1 := add_le_add hle1' hle2'
          _ = (2 * δ) * (N : ℝ) / A1 := by ring
      simpa [hnorm] using hsum

/-! ### Lemma 5 → exceptional sets (PDF (319)–(336)) -/

/--
Long/short applications of Trusted Lemma 5 on both off-diagonal sides.
`C_d > 5` depends only on `d`. The range
`δ^{-C_d} < A < δ^{-(3+C_d)}` forces every fibre scale
`D ≤ N/A` to satisfy `N/D > δ^{-C_d}`, and the left endpoint of each
Lem~5 interval is `< δ^{-(C_d+2)}` (long: `A`; short: `1`).
Short fibres contribute a factor `2δ` (difference of two Lem5 sums).
-/
theorem J1_lem5_exceptional_sets (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (_hs : 2 ≤ s) (_hN : 3 ≤ N) (_hδ : 0 < δ)
        (_hδ' : δ < 1 / 8) (_hAN : A < N),
        Real.rpow δ (-Cd) < (A : ℝ) →
        (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
      altDiophantine d N g δ Cd ∨
      (∃ R R' : ℕ → Finset ℕ,
        (∀ D : ℕ, 0 < D →
          ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
        (∀ D : ℕ, R D ⊆ Finset.Icc 1 (D - 1)) ∧
        (∀ k ∈ J1Fibres_A_lt_B s N A (by omega),
          ‖J1InnerSum g k N A (by omega)‖ ≤
            (2 * δ) * (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) +
              (if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
                (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) else 0)) ∧
        (∀ D : ℕ, 0 < D →
          ((R' D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
        (∀ D : ℕ, R' D ⊆ Finset.Icc 1 (D - 1)) ∧
        (∀ k ∈ J1Fibres_B_lt_A s N A (by omega),
          ‖J1InnerSum g k N A (by omega)‖ ≤
            (2 * δ) * (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) +
              (if (k.colOffDiag ⟨0, by omega⟩) ∈ R' (k.rowOffDiag ⟨0, by omega⟩) then
                (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) else 0))) := by
  set Cd := Lem5Cd d
  have hCd5 : 5 < Cd := Lem5Cd_gt5 d
  obtain ⟨Cbad, hCbad, h3Cbad, hlem⟩ := Lem5Cd_spec d
  refine ⟨Cd, rfl, hCd5, ?_⟩
  intro s N A g δ hs hN hδ hδ' hAN hAlo hAhi
  classical
  rcases Classical.em (altDiophantine d N g δ Cd) with hDio | hNotDio
  · exact Or.inl hDio
  · refine Or.inr ?_
    let R : ℕ → Finset ℕ := fun D => lem5ExceptionalSet d g δ Cd N A D
    refine ⟨R, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro D hD
      exact lem5ExceptionalSet_card_le d g δ Cd Cbad N A hCbad hCd5 h3Cbad hlem
        hNotDio hδ hδ' hAlo hAhi D hD
    · intro D
      exact lem5ExceptionalSet_subset d g δ Cd N A D
    · intro k hk
      exact lem5_pointwise_A_lt_B d g δ Cd s N A (by omega) hδ hδ' hCd5 hAlo hAhi R
        (fun _ => rfl) k hk
    · intro D hD
      exact lem5ExceptionalSet_card_le d g δ Cd Cbad N A hCbad hCd5 h3Cbad hlem
        hNotDio hδ hδ' hAlo hAhi D hD
    · intro D
      exact lem5ExceptionalSet_subset d g δ Cd N A D
    · intro k hk
      exact lem5_pointwise_B_lt_A d g δ Cd s N A (by omega) hδ hδ' hCd5 hAlo hAhi R
        (fun _ => rfl) k hk


/-! ### Σ_I / Σ_II / log absorption -/

theorem J1RowFactorSum_le_log_pow (s N : ℕ) (C0 : ℝ) (_hs : 2 ≤ s) (_hN : 3 ≤ N)
    (hC0 : 0 < C0)
    (hsum :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        C0 * (Real.log N) ^ (s - 1)) :
    J1RowFactorSum s N ≤ C0 ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
  have hone :
      0 ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ) := by
    refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => ?_)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfactor :
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ) ≤
        C0 * (N : ℝ) * (Real.log N) ^ (s - 1) := by
    have := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    linarith
  have hpow :
      ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ^ s ≤
        (C0 * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ s :=
    pow_le_pow_left₀ hone hfactor s
  calc
    J1RowFactorSum s N =
        ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ^ s :=
      J1RowFactorSum_eq s N
    _ ≤ (C0 * (N : ℝ) * (Real.log N) ^ (s - 1)) ^ s := hpow
    _ = C0 ^ s * (N : ℝ) ^ s * ((Real.log N) ^ (s - 1)) ^ s := by ring
    _ = C0 ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
      rw [← pow_mul, mul_comm (s - 1) s]

/--
PDF Σ_I over all off-diagonal fibres (both `A₁<B₁` and `B₁<A₁`),
via row factorisation + `tau_harmonic_partial_sum`.
-/
theorem J1_sigma_I_bound_total (s N A : ℕ) (C0 : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hA : 1 ≤ A) (hC0 : 0 < C0)
    (hsum :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        C0 * (Real.log N) ^ (s - 1)) :
    J1SigmaWeight s N A (by omega) (J1Fibres s N A) ≤
      C0 ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
  have hrow := J1RowFactorSum_le_log_pow s N C0 hs hN hC0 hsum
  exact le_trans (J1_sigma_I_le_row_factor_sum s N A hs hN hA) hrow

theorem J1_sigma_I_bound (s N A : ℕ) (C0 : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hA : 1 ≤ A) (hC0 : 0 < C0)
    (hsum :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        C0 * (Real.log N) ^ (s - 1)) :
    J1SigmaWeight s N A (by omega) (J1Fibres_A_lt_B s N A (by omega)) ≤
      C0 ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
  have h := J1_sigma_I_bound_total s N A C0 hs hN hA hC0 hsum
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k _ _ => J1FullWeight_nonneg k N (by omega)) h

theorem J1_sigma_I_bound_sym (s N A : ℕ) (C0 : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hA : 1 ≤ A) (hC0 : 0 < C0)
    (hsum :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        C0 * (Real.log N) ^ (s - 1)) :
    J1SigmaWeight s N A (by omega) (J1Fibres_B_lt_A s N A (by omega)) ≤
      C0 ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1)) := by
  have h := J1_sigma_I_bound_total s N A C0 hs hN hA hC0 hsum
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k _ _ => J1FullWeight_nonneg k N (by omega)) h

/-- On `{A₁ < B₁}`, `M₁ = B₁`, so full weight is `(N/B₁) * tail`. -/
theorem J1FullWeight_A_lt_B {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) (hAB : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩)) :
    J1FullWeight k N h0 =
      (N : ℝ) / ((k.colOffDiag ⟨0, h0⟩) : ℝ) * J1TailWeight k N h0 := by
  have hM : keyScale k ⟨0, h0⟩ = (k.colOffDiag ⟨0, h0⟩) :=
    max_eq_right (Nat.le_of_lt hAB)
  simp [J1FullWeight, hM]

/-- On `{B₁ < A₁}`, `M₁ = A₁`. -/
theorem J1FullWeight_B_lt_A {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) (hBA : (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩)) :
    J1FullWeight k N h0 =
      (N : ℝ) / ((k.rowOffDiag ⟨0, h0⟩) : ℝ) * J1TailWeight k N h0 := by
  have hM : keyScale k ⟨0, h0⟩ = (k.rowOffDiag ⟨0, h0⟩) :=
    max_eq_left (Nat.le_of_lt hBA)
  simp [J1FullWeight, hM]

/--
PDF (357)–(368) core for `{A₁ < B₁}`:
exceptional fibre sum
  `≤ C δ N · exp(C s log N / log log N) · (N ∑_{n≤N} τ_{s-1}(n)/n)^{s-1}`.

This is proved by embedding J1 fibres into unrestricted positive
off-diagonal matrices, fixing rows `2..s`, and counting row 1.
-/
theorem J1_sigma_II_le_delta_row_factor (d s N A : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (hA : 1 ≤ A)
    (hAN : A < N) (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ J1Fibres_A_lt_B s N A (by omega),
        if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  simpa [J1Fibres_A_lt_B] using
    J1_sigma_II_le_delta_row_factor_filter d s N A δ R Cd Cτ
      hs hN hδ hA hAN hCd hCτ hτ hR

/-- Symmetric core on `{B₁ < A₁}`. -/
theorem J1_sigma_II_le_delta_row_factor_sym (d s N A : ℕ) (δ : ℝ)
    (R : ℕ → Finset ℕ) (Cd Cτ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (hA : 1 ≤ A)
    (hAN : A < N) (hCd : 0 < Cd) (hCτ : 0 < Cτ)
    (hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) :
    (∑ k ∈ J1Fibres_B_lt_A s N A (by omega),
        if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
        Real.sqrt (3 * Cd) * Real.sqrt δ * (N : ℝ) *
          sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1) := by
  simpa [J1Fibres_B_lt_A] using
    J1_sigma_II_le_delta_row_factor_sym_filter d s N A δ R Cd Cτ
      hs hN hδ hA hAN hCd hCτ hτ hR

/--
Absorb the Σ_II Cauchy--Schwarz × harmonic logs into
`𝒬 = (2s log N)^{3s²}`.
-/
theorem J1_sigma_II_absorb_tailQ (s : ℕ) (hs : 2 ≤ s) :
    ∀ N : ℕ, 3 ≤ N →
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        tailQ N s := by
  intro N hN
  have hlog := log_N_gt_one hN
  have hbase1 : (1 : ℝ) ≤ 2 * Real.log N := by nlinarith
  have hbaseQ : (1 : ℝ) ≤ 2 * (s : ℝ) * Real.log N := by
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hk : 2 * (s - 1) ^ 2 - 1 ≤ tailQExp s := two_pred_sq_sub_one_le_tailQExp s
  have hsqrt :
      sigmaIILogFactor N s ≤
        (2 * Real.log N) ^ ((s - 1) ^ 2 - 1) := by
    simp only [sigmaIILogFactor]
    have hx : (1 : ℝ) ≤ (2 * Real.log N) ^ ((s - 1) ^ 2 - 1) :=
      one_le_pow₀ hbase1
    exact (Real.sqrt_le_iff.2 ⟨by positivity, by
      have : (2 * Real.log N) ^ ((s - 1) ^ 2 - 1) ≤
          ((2 * Real.log N) ^ ((s - 1) ^ 2 - 1)) ^ 2 := by
        have h := le_mul_of_one_le_left (le_of_lt (lt_of_lt_of_le (by norm_num) hx)) hx
        simpa [pow_two] using h
      exact this⟩)
  calc
    (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s
        ≤ (2 * (s : ℝ) * Real.log N) ^ ((s - 1) * (s - 1)) *
            (2 * Real.log N) ^ ((s - 1) ^ 2 - 1) := by
          refine mul_le_mul ?_ hsqrt (Real.sqrt_nonneg _) (by positivity)
          exact pow_le_pow_left₀ (le_of_lt (lt_trans (by norm_num) hlog))
            (by
              have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
              nlinarith [hlog, hs2]) _
    _ ≤ (2 * (s : ℝ) * Real.log N) ^ ((s - 1) * (s - 1)) *
          (2 * (s : ℝ) * Real.log N) ^ ((s - 1) ^ 2 - 1) := by
          gcongr
          have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
          nlinarith [hlog, hs2]
    _ = (2 * (s : ℝ) * Real.log N) ^
          ((s - 1) * (s - 1) + ((s - 1) ^ 2 - 1)) := by
          rw [← pow_add]
    _ = (2 * (s : ℝ) * Real.log N) ^ (2 * (s - 1) ^ 2 - 1) := by
          congr 1
          simp [pow_two]
          omega
    _ ≤ tailQ N s := two_s_log_pow_le_tailQ s N (2 * (s - 1) ^ 2 - 1) hs hN hk

/-- Ratio used to absorb the finite range before the eventual threshold. -/
noncomputable def J1SigmaIIAbsorbRatio (s : ℕ) (N : ℕ) : ℝ :=
  (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s / tailQ N s

/--
Uniform-in-`N` form: the Cauchy--Schwarz × harmonic logs sit under `𝒬`.
-/
theorem J1_sigma_II_absorb_tailQ_mul (s : ℕ)
    (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
          K * tailQ N s :=
  ⟨1, by norm_num, fun N hN => by
    simpa using J1_sigma_II_absorb_tailQ s hs N hN⟩

/-- `exp(Cexp ·) ≤ exp(4 ·)` when `Cexp ≤ 4` (kept for Lemma 1 pointwise bound). -/
theorem J1_exp_le_tailQ_exp (Cexp : ℝ) (hCexp4 : Cexp ≤ 4)
    (N s : ℕ) (hN : 3 ≤ N) (hs : 2 ≤ s) :
    Real.exp (Cexp * ((s - 1 : ℕ) : ℝ) *
        Real.log N / Real.log (Real.log N)) ≤
      Real.exp (4 * ((s : ℝ) - 1) *
        Real.log N / Real.log (Real.log N)) := by
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hN)
  have hlogN : (1 : ℝ) < Real.log N := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    exact lt_of_lt_of_le hlog3
      (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hloglog : 0 < Real.log (Real.log N) := Real.log_pos hlogN
  have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 2) hs)]; norm_num
  have hs1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs)
    linarith
  have hLpos : 0 ≤ Real.log N / Real.log (Real.log N) :=
    div_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hlogN))
      (le_of_lt hloglog)
  refine Real.exp_le_exp.mpr ?_
  have hcoef : Cexp * ((s - 1 : ℕ) : ℝ) ≤ 4 * ((s : ℝ) - 1) := by
    rw [hcast]
    exact mul_le_mul_of_nonneg_right hCexp4 hs1
  calc
    Cexp * ((s - 1 : ℕ) : ℝ) * Real.log N / Real.log (Real.log N) =
        (Cexp * ((s - 1 : ℕ) : ℝ)) * (Real.log N / Real.log (Real.log N)) := by
      ring
    _ ≤ (4 * ((s : ℝ) - 1)) * (Real.log N / Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_right hcoef hLpos
    _ = 4 * ((s : ℝ) - 1) * Real.log N / Real.log (Real.log N) := by ring

/-- Finish Σ_II from the CS core bound + harmonic + `tailQ` absorption. -/
theorem J1_sigma_II_from_core (s N : ℕ) (δ X : ℝ) (Cpre Ch K : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (_hδ : 0 < δ)
    (hCpre : 0 < Cpre) (hCh : 0 < Ch) (hK : 0 < K)
    (hH :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        Ch * (Real.log N) ^ (s - 1))
    (habs :
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        K * tailQ N s)
    (hcore :
      X ≤
        Cpre * Real.sqrt δ * (N : ℝ) * sigmaIILogFactor N s *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
              (tau (s - 1) n : ℝ) / (n : ℝ)) ^ (s - 1)) :
    X ≤ Cpre * Ch ^ (s - 1) * K * Real.sqrt δ * (N : ℝ) ^ s * tailQ N s := by
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
      (N : ℝ) * (N : ℝ) ^ (s - 1) = (N : ℝ) ^ ((s - 1) + 1) := (pow_succ' _ _).symm
      _ = (N : ℝ) ^ s := by rw [Nat.sub_add_cancel hs1]
  have habsE : (Real.log N) ^ ((s - 1) * (s - 1)) * E ≤ K * tailQ N s := by
    simpa [E] using habs
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
    _ ≤ Cpre * Ch ^ (s - 1) * Real.sqrt δ * (N : ℝ) ^ s * (K * tailQ N s) := by
      gcongr
    _ = Cpre * Ch ^ (s - 1) * K * Real.sqrt δ * (N : ℝ) ^ s * tailQ N s := by
        ring

theorem J1_sigma_II_bound (d s N A : ℕ) (δ : ℝ) (R : ℕ → Finset ℕ)
    (Cd Cτ Ch K : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ)
    (hA : 1 ≤ A) (hAN : A < N) (hCd : 0 < Cd)
    (hCτ : 0 < Cτ) (hCτ4 : Cτ ≤ 4) (hCh : 0 < Ch) (hK : 0 < K)
    (hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hH :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        Ch * (Real.log N) ^ (s - 1))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ))
    (habs :
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        K * tailQ N s) :
    (∑ k ∈ J1Fibres_A_lt_B s N A (by omega),
        if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
      Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * Real.sqrt δ *
        (N : ℝ) ^ s * tailQ N s := by
  have hcore := J1_sigma_II_le_delta_row_factor d s N A δ R Cd Cτ
    hs hN hδ hA hAN hCd hCτ hτ hR
  exact J1_sigma_II_from_core s N δ _ (Real.sqrt (3 * Cd)) Ch K
    hs hN hδ (Real.sqrt_pos.2 (mul_pos (by norm_num) hCd)) hCh hK hH habs hcore

theorem J1_sigma_II_bound_sym (d s N A : ℕ) (δ : ℝ) (R : ℕ → Finset ℕ)
    (Cd Cτ Ch K : ℝ) (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ)
    (hA : 1 ≤ A) (hAN : A < N) (hCd : 0 < Cd)
    (hCτ : 0 < Cτ) (hCτ4 : Cτ ≤ 4) (hCh : 0 < Ch) (hK : 0 < K)
    (hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (hH :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        Ch * (Real.log N) ^ (s - 1))
    (hR : ∀ D : ℕ, 0 < D →
      ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ))
    (habs :
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        K * tailQ N s) :
    (∑ k ∈ J1Fibres_B_lt_A s N A (by omega),
        if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
          J1FullWeight k N (by omega) else 0) ≤
      Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * Real.sqrt δ *
        (N : ℝ) ^ s * tailQ N s := by
  have hcore := J1_sigma_II_le_delta_row_factor_sym d s N A δ R Cd Cτ
    hs hN hδ hA hAN hCd hCτ hτ hR
  exact J1_sigma_II_from_core s N δ _ (Real.sqrt (3 * Cd)) Ch K
    hs hN hδ (Real.sqrt_pos.2 (mul_pos (by norm_num) hCd)) hCh hK hH habs hcore

/-- Off-diagonal: `A₁ = B₁` fibre set is empty, so the contribution is 0. -/
theorem J1_A_eq_B_bound (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      (∑ k ∈ J1Fibres_A_eq_B s N A (by omega),
        J1FibreContribution g k N A (by omega)) ≤
          C * errorSize N s δ := by
  refine ⟨1, one_pos, ?_⟩
  have h0 : 0 < s := by omega
  simp only [J1Fibres_A_eq_B_empty s N A h0, Finset.sum_empty, errorSize,
    one_mul]
  refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) ?_
  exact (tailQ_pos_of_three_le N s hN).le

/-- `(log N)^{s(s-1)} ≤ K · 𝒬(N,s)` with an `s`-dependent constant. -/
theorem J1_log_pow_le_tailQ (s : ℕ) (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        (Real.log N) ^ (s * (s - 1)) ≤ K * tailQ N s :=
  log_pow_le_mul_tailQ s hs (s * (s - 1)) (s_mul_pred_le_tailQExp s)

/-! ### Pointwise → contribution -/

theorem J1_contrib_le_weight_A_lt_B {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) (δ : ℝ)
    (R : ℕ → Finset ℕ)
    (hAB : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩))
    (hδ0 : 0 ≤ δ)
    (hbound : ‖J1InnerSum g k N A h0‖ ≤
      δ * (N : ℝ) / (k.colOffDiag ⟨0, h0⟩) +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          (N : ℝ) / (k.colOffDiag ⟨0, h0⟩) else 0)) :
    J1FibreContribution g k N A h0 ≤
      δ * J1FullWeight k N h0 +
        (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) := by
  set A1 := (k.rowOffDiag ⟨0, h0⟩)
  set B1 := (k.colOffDiag ⟨0, h0⟩)
  have hM : keyScale k ⟨0, h0⟩ = B1 :=
    max_eq_right (Nat.le_of_lt hAB)
  have htail : 0 ≤ J1TailWeight k N h0 := J1TailWeight_nonneg k N h0
  have hstep :
      J1FibreContribution g k N A h0 ≤
        (δ * (N : ℝ) / B1 +
          (if A1 ∈ R B1 then (N : ℝ) / B1 else 0)) *
          J1TailWeight k N h0 := by
    simp only [J1FibreContribution, A1, B1] at hbound ⊢
    exact mul_le_mul_of_nonneg_right hbound htail
  have hW : J1FullWeight k N h0 = (N : ℝ) / B1 * J1TailWeight k N h0 := by
    simp only [J1FullWeight, hM, B1]
  have hdistrib :
      (δ * (N : ℝ) / B1 + (if A1 ∈ R B1 then (N : ℝ) / B1 else 0)) *
          J1TailWeight k N h0 =
        δ * J1FullWeight k N h0 +
          (if A1 ∈ R B1 then J1FullWeight k N h0 else 0) := by
    rw [hW]
    split_ifs with h
    · ring
    · ring
  exact hdistrib ▸ hstep

theorem J1_contrib_le_weight_B_lt_A {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) (δ : ℝ)
    (R : ℕ → Finset ℕ)
    (hBA : (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩))
    (hδ0 : 0 ≤ δ)
    (hbound : ‖J1InnerSum g k N A h0‖ ≤
      δ * (N : ℝ) / (k.rowOffDiag ⟨0, h0⟩) +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          (N : ℝ) / (k.rowOffDiag ⟨0, h0⟩) else 0)) :
    J1FibreContribution g k N A h0 ≤
      δ * J1FullWeight k N h0 +
        (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
          J1FullWeight k N h0 else 0) := by
  set A1 := (k.rowOffDiag ⟨0, h0⟩)
  set B1 := (k.colOffDiag ⟨0, h0⟩)
  have hM : keyScale k ⟨0, h0⟩ = A1 :=
    max_eq_left (Nat.le_of_lt hBA)
  have htail : 0 ≤ J1TailWeight k N h0 := J1TailWeight_nonneg k N h0
  have hstep :
      J1FibreContribution g k N A h0 ≤
        (δ * (N : ℝ) / A1 +
          (if B1 ∈ R A1 then (N : ℝ) / A1 else 0)) *
          J1TailWeight k N h0 := by
    simp only [J1FibreContribution, A1, B1] at hbound ⊢
    exact mul_le_mul_of_nonneg_right hbound htail
  have hW : J1FullWeight k N h0 = (N : ℝ) / A1 * J1TailWeight k N h0 := by
    simp only [J1FullWeight, hM, A1]
  have hdistrib :
      (δ * (N : ℝ) / A1 + (if B1 ∈ R A1 then (N : ℝ) / A1 else 0)) *
          J1TailWeight k N h0 =
        δ * J1FullWeight k N h0 +
          (if B1 ∈ R A1 then J1FullWeight k N h0 else 0) := by
    rw [hW]
    split_ifs <;> ring
  exact hdistrib ▸ hstep

/-! ### Side sum from exceptional sets -/

theorem J1_side_sum_A_lt_B {d s N A : ℕ} (g : CirclePoly d) (δ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (hA : 1 ≤ A)
    (R : ℕ → Finset ℕ)
    (hpt : ∀ k ∈ J1Fibres_A_lt_B s N A (by omega),
      ‖J1InnerSum g k N A (by omega)‖ ≤
        δ * (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) +
          (if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
            (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) else 0)) :
    (∑ k ∈ J1Fibres_A_lt_B s N A (by omega),
        J1FibreContribution g k N A (by omega)) ≤
      δ * J1SigmaWeight s N A (by omega) (J1Fibres_A_lt_B s N A (by omega)) +
        ∑ k ∈ J1Fibres_A_lt_B s N A (by omega),
          if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
            J1FullWeight k N (by omega) else 0 := by
  have h0 : 0 < s := by omega
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  calc
    (∑ k ∈ J1Fibres_A_lt_B s N A h0,
        J1FibreContribution g k N A h0) ≤
      ∑ k ∈ J1Fibres_A_lt_B s N A h0,
        (δ * J1FullWeight k N h0 +
          (if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
            J1FullWeight k N h0 else 0)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hAB : (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩) :=
        (Finset.mem_filter.1 hk).2
      exact J1_contrib_le_weight_A_lt_B g k N A h0 δ R hAB hδ0 (hpt k hk)
    _ = δ * J1SigmaWeight s N A h0 (J1Fibres_A_lt_B s N A h0) +
        ∑ k ∈ J1Fibres_A_lt_B s N A h0,
          if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
            J1FullWeight k N h0 else 0 := by
      simp only [J1SigmaWeight, Finset.mul_sum, Finset.sum_add_distrib]

theorem J1_side_sum_B_lt_A {d s N A : ℕ} (g : CirclePoly d) (δ : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (hA : 1 ≤ A)
    (R : ℕ → Finset ℕ)
    (hpt : ∀ k ∈ J1Fibres_B_lt_A s N A (by omega),
      ‖J1InnerSum g k N A (by omega)‖ ≤
        δ * (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) +
          (if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
            (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) else 0)) :
    (∑ k ∈ J1Fibres_B_lt_A s N A (by omega),
        J1FibreContribution g k N A (by omega)) ≤
      δ * J1SigmaWeight s N A (by omega) (J1Fibres_B_lt_A s N A (by omega)) +
        ∑ k ∈ J1Fibres_B_lt_A s N A (by omega),
          if (k.colOffDiag ⟨0, by omega⟩) ∈ R (k.rowOffDiag ⟨0, by omega⟩) then
            J1FullWeight k N (by omega) else 0 := by
  have h0 : 0 < s := by omega
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  calc
    (∑ k ∈ J1Fibres_B_lt_A s N A h0,
        J1FibreContribution g k N A h0) ≤
      ∑ k ∈ J1Fibres_B_lt_A s N A h0,
        (δ * J1FullWeight k N h0 +
          (if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
            J1FullWeight k N h0 else 0)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hBA : (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩) :=
        (Finset.mem_filter.1 hk).2
      exact J1_contrib_le_weight_B_lt_A g k N A h0 δ R hBA hδ0 (hpt k hk)
    _ = δ * J1SigmaWeight s N A h0 (J1Fibres_B_lt_A s N A h0) +
        ∑ k ∈ J1Fibres_B_lt_A s N A h0,
          if (k.colOffDiag ⟨0, h0⟩) ∈ R (k.rowOffDiag ⟨0, h0⟩) then
            J1FullWeight k N h0 else 0 := by
      simp only [J1SigmaWeight, Finset.mul_sum, Finset.sum_add_distrib]

/-! ### Partition of fibres -/

theorem J1Fibres_disjoint_union (s N A : ℕ) (h0 : 0 < s) :
    (J1Fibres_A_lt_B s N A h0 ∪ J1Fibres_B_lt_A s N A h0 ∪
      J1Fibres_A_eq_B s N A h0) = J1Fibres s N A := by
  ext k
  simp only [J1Fibres_A_lt_B, J1Fibres_B_lt_A, J1Fibres_A_eq_B,
    Finset.mem_union, Finset.mem_filter]
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

theorem J1Fibres_pairwise_disjoint (s N A : ℕ) (h0 : 0 < s) :
    Disjoint (J1Fibres_A_lt_B s N A h0) (J1Fibres_B_lt_A s N A h0) ∧
      Disjoint (J1Fibres_A_lt_B s N A h0 ∪ J1Fibres_B_lt_A s N A h0)
        (J1Fibres_A_eq_B s N A h0) := by
  refine ⟨?_, ?_⟩
  · refine Finset.disjoint_left.2 fun k hk1 hk2 => ?_
    have h1 := (Finset.mem_filter.1 hk1).2
    have h2 := (Finset.mem_filter.1 hk2).2
    omega
  · refine Finset.disjoint_left.2 fun k hk1 hk2 => ?_
    have heq := (Finset.mem_filter.1 hk2).2
    simp only [Finset.mem_union, J1Fibres_A_lt_B, J1Fibres_B_lt_A,
      Finset.mem_filter] at hk1
    rcases hk1 with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega

theorem sum_contrib_split {d s N A : ℕ} (g : CirclePoly d) (h0 : 0 < s) :
    (∑ k ∈ J1Fibres s N A, J1FibreContribution g k N A h0) =
      (∑ k ∈ J1Fibres_A_lt_B s N A h0, J1FibreContribution g k N A h0) +
      (∑ k ∈ J1Fibres_B_lt_A s N A h0, J1FibreContribution g k N A h0) +
      (∑ k ∈ J1Fibres_A_eq_B s N A h0, J1FibreContribution g k N A h0) := by
  have hU := J1Fibres_disjoint_union s N A h0
  have hD := J1Fibres_pairwise_disjoint s N A h0
  have hdisj1 := hD.1
  have hdisj2 := hD.2
  rw [← hU, Finset.sum_union hdisj2, Finset.sum_union hdisj1]

/-! ### Assemble `J1_long_short_sum_bound` -/

theorem J1_long_short_sum_bound (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (Cd : ℝ)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (hAN : A < N) (hCd : 0 < Cd)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ))
    (hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (hlem5 : altDiophantine d N g δ Cd ∨
      (∃ R R' : ℕ → Finset ℕ,
        (∀ D : ℕ, 0 < D →
          ((R D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
        (∀ D : ℕ, R D ⊆ Finset.Icc 1 (D - 1)) ∧
        (∀ k ∈ J1Fibres_A_lt_B s N A (by omega),
          ‖J1InnerSum g k N A (by omega)‖ ≤
            (2 * δ) * (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) +
              (if (k.rowOffDiag ⟨0, by omega⟩) ∈ R (k.colOffDiag ⟨0, by omega⟩) then
                (N : ℝ) / (k.colOffDiag ⟨0, by omega⟩) else 0)) ∧
        (∀ D : ℕ, 0 < D →
          ((R' D).card : ℝ) ≤ Cd * δ * (D : ℝ)) ∧
        (∀ D : ℕ, R' D ⊆ Finset.Icc 1 (D - 1)) ∧
        (∀ k ∈ J1Fibres_B_lt_A s N A (by omega),
          ‖J1InnerSum g k N A (by omega)‖ ≤
            (2 * δ) * (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) +
              (if (k.colOffDiag ⟨0, by omega⟩) ∈ R' (k.rowOffDiag ⟨0, by omega⟩) then
                (N : ℝ) / (k.rowOffDiag ⟨0, by omega⟩) else 0))))
    (Ch : ℝ) (hCh : 0 < Ch)
    (hharm :
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
        Ch * (Real.log N) ^ (s - 1))
    (Cτ K Klog : ℝ) (hCτ : 0 < Cτ) (hCτ4 : Cτ ≤ 4) (hK : 0 < K) (hKlog : 0 < Klog)
    (hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)))
    (habs :
      (Real.log N) ^ ((s - 1) * (s - 1)) * sigmaIILogFactor N s ≤
        K * tailQ N s)
    (hlog :
      (Real.log N) ^ (s * (s - 1)) ≤ Klog * tailQ N s) :
    (∑ k ∈ J1Fibres s N A,
        J1FibreContribution g k N A (by omega)) ≤
      (4 * Ch ^ s * Klog + 2 * Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K + 1) *
        errorSize N s δ ∨
      altDiophantine d N g δ Cd := by
  have h0 : 0 < s := by omega
  have h2δ : 0 < 2 * δ := by positivity
  have hA : 1 ≤ A := by
    have hpos : (0 : ℝ) < Real.rpow δ (-Cd) :=
      Real.rpow_pos_of_pos hδ _
    have : (0 : ℝ) < (A : ℝ) := lt_trans hpos hAlo
    exact Nat.succ_le_of_lt (Nat.cast_pos.1 this)
  rcases hlem5 with hdio | hR
  · exact Or.inr hdio
  rcases hR with ⟨R, R', hRcard, _, hpt, hRcard', _, hpt'⟩
  have hside := J1_side_sum_A_lt_B g (2 * δ) hs hN h2δ hA R hpt
  have hside' := J1_side_sum_B_lt_A g (2 * δ) hs hN h2δ hA R' hpt'
  have hI := J1_sigma_I_bound s N A Ch hs hN hA hCh hharm
  have hI' := J1_sigma_I_bound_sym s N A Ch hs hN hA hCh hharm
  have hII := J1_sigma_II_bound d s N A δ R Cd Cτ Ch K
    hs hN hδ hA hAN hCd hCτ hCτ4 hCh hK hτ hharm hRcard habs
  have hII' :=
    J1_sigma_II_bound_sym d s N A δ R' Cd Cτ Ch K
      hs hN hδ hA hAN hCd hCτ hCτ4 hCh hK hτ hharm hRcard' habs
  have hsplit := sum_contrib_split (g := g) (s := s) (N := N) (A := A) h0
  refine Or.inl ?_
  have hAerr :
      (∑ k ∈ J1Fibres_A_lt_B s N A h0,
          J1FibreContribution g k N A h0) ≤
        (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
          errorSize N s δ := by
    refine le_trans hside ?_
    have hδ1 : δ ≤ 1 := le_of_lt (lt_trans hδ' (by norm_num))
    have hδI :
        (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_A_lt_B s N A h0) ≤
          (2 * Ch ^ s * Klog) * errorSize N s δ := by
      calc
        (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_A_lt_B s N A h0) ≤
            (2 * δ) * (Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) :=
          mul_le_mul_of_nonneg_left hI (le_of_lt h2δ)
        _ = (2 * Ch ^ s) * (δ * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) := by ring
        _ ≤ (2 * Ch ^ s) * (δ * (N : ℝ) ^ s * (Klog * tailQ N s)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog (by positivity))
            (by positivity)
        _ = (2 * Ch ^ s * Klog) * (δ * (N : ℝ) ^ s * tailQ N s) := by ring
        _ ≤ (2 * Ch ^ s * Klog) * errorSize N s δ :=
          mul_le_mul_of_nonneg_left
            (delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN) (by positivity)
    have hIIerr :
        (∑ k ∈ J1Fibres_A_lt_B s N A h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) ≤
          Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ := by
      calc
        _ ≤ Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * Real.sqrt δ *
              (N : ℝ) ^ s * tailQ N s := hII
        _ = Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ := by
          simp [errorSize]; ring
    calc
      (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_A_lt_B s N A h0) +
          (∑ k ∈ J1Fibres_A_lt_B s N A h0,
            if (k.rowOffDiag ⟨0, h0⟩) ∈ R (k.colOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) ≤
          (2 * Ch ^ s * Klog) * errorSize N s δ +
            Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ :=
        add_le_add hδI hIIerr
      _ = (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
            errorSize N s δ := by ring
  have hBerr :
      (∑ k ∈ J1Fibres_B_lt_A s N A h0,
          J1FibreContribution g k N A h0) ≤
        (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
          errorSize N s δ := by
    refine le_trans hside' ?_
    have hδ1 : δ ≤ 1 := le_of_lt (lt_trans hδ' (by norm_num))
    have hδI :
        (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_B_lt_A s N A h0) ≤
          (2 * Ch ^ s * Klog) * errorSize N s δ := by
      calc
        (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_B_lt_A s N A h0) ≤
            (2 * δ) * (Ch ^ s * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) :=
          mul_le_mul_of_nonneg_left hI' (le_of_lt h2δ)
        _ = (2 * Ch ^ s) * (δ * (N : ℝ) ^ s * (Real.log N) ^ (s * (s - 1))) := by ring
        _ ≤ (2 * Ch ^ s) * (δ * (N : ℝ) ^ s * (Klog * tailQ N s)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog (by positivity))
            (by positivity)
        _ = (2 * Ch ^ s * Klog) * (δ * (N : ℝ) ^ s * tailQ N s) := by ring
        _ ≤ (2 * Ch ^ s * Klog) * errorSize N s δ :=
          mul_le_mul_of_nonneg_left
            (delta_mul_Ns_tailQ_le_errorSize N s hδ.le hδ1 hN) (by positivity)
    have hIIerr :
        (∑ k ∈ J1Fibres_B_lt_A s N A h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) ≤
          Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ := by
      calc
        _ ≤ Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * Real.sqrt δ *
              (N : ℝ) ^ s * tailQ N s := hII'
        _ = Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ := by
          simp [errorSize]; ring
    calc
      (2 * δ) * J1SigmaWeight s N A h0 (J1Fibres_B_lt_A s N A h0) +
          (∑ k ∈ J1Fibres_B_lt_A s N A h0,
            if (k.colOffDiag ⟨0, h0⟩) ∈ R' (k.rowOffDiag ⟨0, h0⟩) then
              J1FullWeight k N h0 else 0) ≤
          (2 * Ch ^ s * Klog) * errorSize N s δ +
            Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K * errorSize N s δ :=
        add_le_add hδI hIIerr
      _ = (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
            errorSize N s δ := by ring
  have heq1 :
      (∑ k ∈ J1Fibres_A_eq_B s N A h0,
          J1FibreContribution g k N A h0) ≤
        1 * errorSize N s δ := by
    simp only [J1Fibres_A_eq_B_empty s N A h0, Finset.sum_empty, one_mul, errorSize]
    refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) ?_
    exact (tailQ_pos_of_three_le N s hN).le
  rw [hsplit]
  calc
    _ ≤ (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
            errorSize N s δ +
          (2 * Ch ^ s * Klog + Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K) *
            errorSize N s δ +
          1 * errorSize N s δ :=
      add_le_add (add_le_add hAerr hBerr) heq1
    _ = (4 * Ch ^ s * Klog + 2 * Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K + 1) *
          errorSize N s δ := by
      ring

/--
Pointwise form of Lemma 6: for each `(s,N,A,g,δ)` some `C` works.
Public `J1_bound` strengthens to a constant independent of `N,A,g,δ` (per `s`).
-/
theorem J1_bound_pointwise (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
        (hs : 2 ≤ s) (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
        (hAN : A < N),
        Real.rpow δ (-Cd) < (A : ℝ) →
        (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
        (∃ C : ℝ, 0 < C ∧
          ‖Sg g (J1Support (s := s) (N := N) A
              (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs))‖ ≤
            C * errorSize N s δ) ∨
          altDiophantine d N g δ Cd := by
  obtain ⟨Cd, hEq, hCd, hlem5⟩ := J1_lem5_exceptional_sets d
  have hCd0 : 0 < Cd := lt_trans (by norm_num : (0 : ℝ) < 5) hCd
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s N A g δ hs hN hδ hδ' hAN hAlo hAhi
  have hA : 1 ≤ A := by
    have hpos : (0 : ℝ) < Real.rpow δ (-Cd) :=
      Real.rpow_pos_of_pos hδ _
    have : (0 : ℝ) < (A : ℝ) := lt_trans hpos hAlo
    exact Nat.succ_le_of_lt (Nat.cast_pos.1 this)
  have hpartition :
      ∀ k ∈ J1Fibres s N A,
        KeyIsLong k N A (by omega) ∨ KeyIsShort k N A (by omega) := by
    intro k hk
    exact key_long_or_short k (by omega)
      (J1Fibre_head_nonempty s N A k (by omega) hk hA)
  obtain ⟨Ch, hCh, hhall⟩ := tau_harmonic_partial_sum s hs
  obtain ⟨Cτ, hCτ, hCτ4, hτall⟩ := tau_uniform_exp_bound
  obtain ⟨K, hK, habsAll⟩ := J1_sigma_II_absorb_tailQ_mul s hs
  obtain ⟨Klog, hKlog, hlogAll⟩ := J1_log_pow_le_tailQ s hs
  have hharm := hhall N hN
  have hpkg := hlem5 s N A g δ hs hN hδ hδ' hAN hAlo hAhi
  have hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)) :=
    fun n hn hnN => hτall (s - 1) N n hN (by omega) hn hnN
  rcases J1_long_short_sum_bound d s N A g δ Cd hs hN hδ hδ' hAN hCd0
      hAlo hAhi hpkg Ch hCh hharm Cτ K Klog hCτ hCτ4 hK hKlog hτ
      (habsAll N hN) (hlogAll N hN) with hsum | hdio
  · exact Or.inl
      ⟨4 * Ch ^ s * Klog + 2 * Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K + 1,
        by positivity,
        (J1_parameter_reduction d s N A g hs hN hA).trans hsum⟩
  · exact Or.inr hdio

/--
PDF Lemma 6 / `lem:J1`.

Exists `C_d > 5` depending only on `d`, and for each `s ≥ 2` an error constant
`C` independent of `N,A,g,δ` (coming from the `s`-dependent harmonic constant and
`C_d`), such that whenever `δ^{-C_d} < A < δ^{-(3+C_d)}`, either
`|J₁| ≤ C δ N^s 𝒬` or Diophantine with exponent `C_d`.
-/
theorem J1_bound (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 5 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (_hN : 3 ≤ N) (_hδ : 0 < δ) (_hδ' : δ < 1 / 8)
          (_hAN : A < N),
          Real.rpow δ (-Cd) < (A : ℝ) →
          (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
          ‖Sg g (J1Support (s := s) (N := N) A
              (Nat.lt_of_lt_of_le (by decide : 0 < 2) hs))‖ ≤
            C * errorSize N s δ ∨
          altDiophantine d N g δ Cd := by
  obtain ⟨Cd, hEq, hCd, hlem5⟩ := J1_lem5_exceptional_sets d
  have hCd0 : 0 < Cd := lt_trans (by norm_num : (0 : ℝ) < 5) hCd
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨Ch, hCh, hhall⟩ := tau_harmonic_partial_sum s hs
  obtain ⟨Cτ, hCτ, hCτ4, hτall⟩ := tau_uniform_exp_bound
  obtain ⟨K, hK, habsAll⟩ := J1_sigma_II_absorb_tailQ_mul s hs
  obtain ⟨Klog, hKlog, hlogAll⟩ := J1_log_pow_le_tailQ s hs
  refine ⟨4 * Ch ^ s * Klog + 2 * Real.sqrt (3 * Cd) * Ch ^ (s - 1) * K + 1,
    by positivity, ?_⟩
  intro N A g δ hN hδ hδ' hAN hAlo hAhi
  have hA : 1 ≤ A := by
    have hpos : (0 : ℝ) < Real.rpow δ (-Cd) :=
      Real.rpow_pos_of_pos hδ _
    have : (0 : ℝ) < (A : ℝ) := lt_trans hpos hAlo
    exact Nat.succ_le_of_lt (Nat.cast_pos.1 this)
  have hharm := hhall N hN
  have hpkg := hlem5 s N A g δ hs hN hδ hδ' hAN hAlo hAhi
  have hτ : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      (tau (s - 1) n : ℝ) ≤
        Real.exp (Cτ * ((s - 1 : ℕ) : ℝ) *
          Real.log N / Real.log (Real.log N)) :=
    fun n hn hnN => hτall (s - 1) N n hN (by omega) hn hnN
  rcases J1_long_short_sum_bound d s N A g δ Cd hs hN hδ hδ' hAN hCd0
      hAlo hAhi hpkg Ch hCh hharm Cτ K Klog hCτ hCτ4 hK hKlog hτ
      (habsAll N hN) (hlogAll N hN) with hsum | hdio
  · exact Or.inl
      ((J1_parameter_reduction d s N A g hs hN hA).trans hsum)
  · exact Or.inr hdio

end RMFLean
