/-
PDF section 7 -- Proof of Theorem 1 by inclusion-exclusion + Propositions 1-2.
-/
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Assemble.Bookkeeping
import RMFLean.Proof.Setup.SparseComplement
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.F1.PropF1
import RMFLean.Proof.Intersection.PropIntersection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

noncomputable section

open Classical Real

namespace RMFLean

/-- Shared A-window `(Cd+2, Cd+3)` sits inside Prop 1's `(Cd, Cd+3)`. -/
theorem window_imp_F1_lo {Cd delta : ℝ} {A : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hCd : 0 < Cd)
    (h : Real.rpow delta (-windowLo Cd) < (A : ℝ)) :
    Real.rpow delta (-Cd) < (A : ℝ) := by
  have hle : -(windowLo Cd) ≤ (-Cd) := by
    simp only [windowLo]
    linarith
  have hpow : Real.rpow delta (-Cd) ≤ Real.rpow delta (-windowLo Cd) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta (le_of_lt hdelta1) hle
  exact lt_of_le_of_lt hpow h

theorem window_imp_F1_hi {Cd delta : ℝ} {A : ℕ}
    (h : (A : ℝ) < Real.rpow delta (-windowHi Cd)) :
    (A : ℝ) < Real.rpow delta (-(3 + Cd)) := by
  simpa [windowHi, add_comm Cd 3] using h

theorem sq_lt_eighth {δ : ℝ} (hδ : 0 < δ) (h : δ < 1 / 8) : δ ^ 2 < 1 / 8 := by
  have hsq : δ ^ 2 < (1 / 8 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h (le_of_lt hδ) (by norm_num)
  have h64 : (1 / 8 : ℝ) ^ 2 = 1 / 64 := by norm_num
  exact lt_trans (hsq.trans_eq h64) (by norm_num)

theorem rpow_neg_half_sq {N : ℕ} {C : ℝ} (_hN : (1 : ℝ) ≤ N) :
    Real.rpow (N : ℝ) (-C) = (Real.rpow (N : ℝ) (-(C / 2))) ^ 2 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hexp : (-(C / 2)) * (2 : ℝ) = -C := by ring
  calc
    Real.rpow (N : ℝ) (-C)
        = Real.rpow (N : ℝ) ((-(C / 2)) * 2) := by rw [hexp]
    _ = Real.rpow (Real.rpow (N : ℝ) (-(C / 2))) 2 :=
        Real.rpow_mul hN0 _ _
    _ = (Real.rpow (N : ℝ) (-(C / 2))) ^ 2 := Real.rpow_two _

theorem rpow_neg_half_lt_imp_sq {N : ℕ} {C δ : ℝ}
    (hN : (1 : ℝ) ≤ N) (hδ : 0 < δ)
    (h : Real.rpow (N : ℝ) (-(C / 2)) < δ) :
    Real.rpow (N : ℝ) (-C) < δ ^ 2 := by
  have hbase := rpow_neg_half_sq (N := N) (C := C) hN
  have hnon : 0 ≤ Real.rpow (N : ℝ) (-(C / 2)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsq : (Real.rpow (N : ℝ) (-(C / 2))) ^ 2 < δ ^ 2 := by
    refine (sq_lt_sq).mpr ?_
    rwa [abs_of_nonneg hnon, abs_of_pos hδ]
  rwa [← hbase] at hsq

/--
PDF Theorem 1 (`thm:main`), proved from the paper's lemmas
(Lemma 1 is a theorem in `DivisorSums`; Lemma 6 is an axiom).

Regime: `N^{-C} < delta < 1/8` (as in Lemma 5 / Props 1-2).
Shared Lem5 exponent `Lem5Cd d`; A-window is Piece III's
`delta^{-(Cd+2)} < A < delta^{-(Cd+3)}`.
Vinogradov constant `Cll` depends only on `d,s` (via the inductive
`Cll_ind` and the Prop 1-2 constants).
-/
theorem momentDichotomy (d : ℕ) : MomentDichotomy d := by
  obtain ⟨Cd, hEqF, hCd5, hFi⟩ := Fi_symmetry d
  obtain ⟨CdI, hEqI, hCdI, hInt0⟩ := prop_intersection d
  have hCd : 0 < Cd := lt_trans (by norm_num : (0 : ℝ) < 5) hCd5
  have hSame : CdI = Cd := hEqI.trans hEqF.symm
  rw [hSame] at hInt0
  have hInt := prop_intersection_any d Cd hCd hInt0
  set CdS := CdStar d
  have hCdS : 0 < CdS := CdStar_pos d
  have hCd_le : Cd ≤ CdS := by
    simpa [hEqF] using CdStar_ge_Lem5Cd d
  refine ⟨2 * CdS, mul_pos (by norm_num) hCdS, ?_⟩
  intro s0 hs0
  have key :
      ∀ t : ℕ, 2 ≤ t →
        ∃ Cll : ℝ, 0 < Cll ∧
          ∃ C : ℝ, 0 < C ∧
            ∃ N0 : ℕ,
              ∀ N : ℕ, N0 ≤ N →
                inMomentRange N t →
                  ∀ delta : ℝ, Real.rpow (N : ℝ) (-C) < delta →
                    delta < 1 / 8 →
                      ∀ g : CirclePoly d,
                        altGaussianSqrt d N t g delta Cll ∨
                          altDiophantine d N g delta CdS := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      obtain ⟨CI, hCI, hIntt⟩ := hInt t ht
      obtain ⟨Csel, hCsel, N0sel, hsel⟩ :=
        assemble_choose_A d t ht Cd hCd
      obtain ⟨K, hK, N0abs, habs⟩ := two_pow_tailQ_le_momentError t ht
      obtain ⟨Cll_ind, hCll_ind, Cind, hCind, N0ind, hind⟩ :
          ∃ Cll : ℝ, 0 < Cll ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
            ∀ N : ℕ, N0 ≤ N →
              inMomentRange N (t - 1) →
                ∀ delta : ℝ, Real.rpow (N : ℝ) (-C) < delta →
                  delta < 1 / 8 →
                    ∀ g : CirclePoly d,
                      altGaussianSqrt d N (t - 1) g delta Cll ∨
                        altDiophantine d N g delta CdS := by
        by_cases h2 : t = 2
        · refine ⟨1, by norm_num, 1, by norm_num, 0, ?_⟩
          intro N _ hrange delta _ _ g
          exact absurd hrange.1 (by omega)
        · have ht1 : 2 ≤ t - 1 := by omega
          have hlt : t - 1 < t :=
            Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) ht) (by decide)
          exact ih (t - 1) hlt ht1
      obtain ⟨CF, hCF, hFits⟩ := hFi t ht CdS hCd_le Cll_ind hCll_ind
      set CJ2 : ℝ := J2DeltaExp Cd
      have hCJ2 : 0 < CJ2 := J2DeltaExp_pos hCd
      set C : ℝ := min Csel (min Cind CJ2)
      have hCpos : 0 < C := lt_min hCsel (lt_min hCind hCJ2)
      set N0 : ℕ := max N0sel (max N0ind N0abs)
      set Cerr : ℝ := CF + CI + 1
      have hCerr : 0 < Cerr := by positivity
      set Cll : ℝ := Cerr * K
      have hCll : 0 < Cll := mul_pos hCerr hK
      refine ⟨Cll, hCll, C, hCpos, N0, ?_⟩
      intro N hN0 hrange delta hdeltalo hdeltahalf g
      have hN : 3 ≤ N := hrange.2
      have hN0sel : N0sel ≤ N := le_trans (le_max_left _ _) hN0
      have hN0ind : N0ind ≤ N :=
        le_trans (le_trans (le_max_left N0ind _) (le_max_right N0sel _)) hN0
      have hN0abs' : N0abs ≤ N :=
        le_trans (le_trans (le_max_right N0ind N0abs)
          (le_max_right N0sel _)) hN0
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 3) hN)
      have hdeltapos : 0 < delta :=
        lt_trans (Real.rpow_pos_of_pos
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN1) _) hdeltalo
      have hC_le_sel : C ≤ Csel := min_le_left _ _
      have hC_le_ind : C ≤ Cind :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hC_le_J2 : C ≤ CJ2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hdeltalo_sel : Real.rpow (N : ℝ) (-Csel) < delta := by
        have : Real.rpow (N : ℝ) (-Csel) ≤ Real.rpow (N : ℝ) (-C) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hC_le_sel)
        exact lt_of_le_of_lt this hdeltalo
      have hδN : Real.rpow (N : ℝ) (-J2DeltaExp Cd) < delta := by
        have : Real.rpow (N : ℝ) (-CJ2) ≤ Real.rpow (N : ℝ) (-C) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hC_le_J2)
        exact lt_of_le_of_lt this hdeltalo
      obtain ⟨A, hA2, hAN, hAlo, hAhi, hSpCard⟩ :=
        hsel N hN0sel hN delta hdeltalo_sel hdeltahalf
      have hdelta1 : delta < 1 := lt_trans hdeltahalf (by norm_num)
      have hFlo := window_imp_F1_lo hdeltapos hdelta1 hCd hAlo
      have hFhi := window_imp_F1_hi hAhi
      have hIlo : Real.rpow delta (-(Cd + 2)) < (A : ℝ) := by
        simpa [windowLo] using hAlo
      have hIhi : (A : ℝ) < Real.rpow delta (-(3 + Cd)) :=
        window_imp_F1_hi hAhi
      have hA1 : 1 ≤ A := le_trans (by decide : 1 ≤ 2) hA2
      have hindHyp : t = 2 ∨ Hyp d (t - 1) N g delta CdS Cll_ind := by
        by_cases h2 : t = 2
        · exact Or.inl h2
        · refine Or.inr ?_
          have hrange1 : inMomentRange N (t - 1) := ⟨by omega, hN⟩
          have hdeltalo_ind : Real.rpow (N : ℝ) (-Cind) < delta := by
            have : Real.rpow (N : ℝ) (-Cind) ≤ Real.rpow (N : ℝ) (-C) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hC_le_ind)
            exact lt_of_le_of_lt this hdeltalo
          exact hind N hN0ind hrange1 delta hdeltalo_ind hdeltahalf g
      have hrangeInd : t = 2 ∨ inMomentRange N (t - 1) := by
        by_cases h2 : t = 2
        · exact Or.inl h2
        · exact Or.inr ⟨by omega, hN⟩
      by_cases hDio : altDiophantine d N g delta CdS
      · exact Or.inr hDio
      · have herr0 : 0 ≤ errorSize N t delta := by
          simp only [errorSize, tailQ]; positivity
        have hFiAll :
            ∀ i : Fin t,
              ‖(Sg g (Ffinset (N := N) A i
                  (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht)) : ℂ) -
                  (mainTermF t N : ℂ)‖ ≤
                CF * errorSize N t delta := by
          intro i
          rcases hFits N A g delta i hN hdeltapos hdeltahalf hAN hFlo hFhi
              hδN hindHyp hrangeInd with h | h
          · exact h
          · exact (hDio h).elim
        have hIntAll :
            ∀ I : Finset (Fin t), 2 ≤ I.card →
              ‖Sg g (IntersectionSupport (s := t) (N := N) A I
                  (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht))‖ ≤
                CI * errorSize N t delta := by
          intro I hIcard
          rcases hIntt N A g delta I hN hIcard hdeltapos hdeltahalf hA1 hAN hIlo hIhi
            with h | h
          · exact h
          · exact (hDio (altDiophantine_mono hdeltapos hdelta1
              (by
                simp only [CdS, CdStar]
                linarith [hEqF]) h)).elim
        have hSp :
            ‖Sg g (sparseComplementFinset (s := t) (N := N) A
                (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht))‖ ≤
              (1 : ℝ) * errorSize N t delta := by
          calc
            ‖Sg g _‖ ≤ (_ : ℝ) := norm_Sg_le_card g _
            _ ≤ errorSize N t delta := hSpCard
            _ = 1 * errorSize N t delta := by ring
        have hFi' :
            ∀ i : Fin t,
              ‖(Sg g (Ffinset (N := N) A i
                  (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht)) : ℂ) -
                  (mainTermF t N : ℂ)‖ ≤
                Cerr * errorSize N t delta := by
          intro i
          exact (hFiAll i).trans <|
            mul_le_mul_of_nonneg_right (by simp only [Cerr]; linarith)
              herr0
        have hInt' :
            ∀ I : Finset (Fin t), 2 ≤ I.card →
              ‖Sg g (IntersectionSupport (s := t) (N := N) A I
                  (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht))‖ ≤
                Cerr * errorSize N t delta := by
          intro I hI
          exact (hIntAll I hI).trans <|
            mul_le_mul_of_nonneg_right (by simp only [Cerr]; linarith)
              herr0
        have hSp' :
            ‖Sg g (sparseComplementFinset (s := t) (N := N) A
                (Nat.lt_of_lt_of_le (by decide : 0 < 2) ht))‖ ≤
              Cerr * errorSize N t delta :=
          hSp.trans <|
            mul_le_mul_of_nonneg_right (by simp only [Cerr]; linarith)
              herr0
        have hU :=
          U_ie_bound d t N A g delta Cerr ht hN hA2 hAN hdeltapos hCerr hFi' hInt' hSp'
        have hGauss :=
          altGaussian_of_U_bound d t N g delta Cerr K ht hN hdeltapos hCerr hK hU
            (habs N hN0abs' hN)
        exact Or.inl (by simpa [Cll] using hGauss)
  obtain ⟨Cll, hCll, C, hCpos, N0, hkey⟩ := key s0 hs0
  refine ⟨Cll, hCll, C / 2, half_pos hCpos, N0, ?_⟩
  intro N hN0 hrange δ hlo hhi g
  have hN : 3 ≤ N := hrange.2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 3) hN)
  have hδpos : 0 < δ :=
    lt_trans (Real.rpow_pos_of_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN1) _) hlo
  have hsq_hi : δ ^ 2 < 1 / 8 := sq_lt_eighth hδpos hhi
  have hsq_lo : Real.rpow (N : ℝ) (-C) < δ ^ 2 :=
    rpow_neg_half_lt_imp_sq hN1 hδpos hlo
  rcases hkey N hN0 hrange (δ ^ 2) hsq_lo hsq_hi g with hG | hD
  · exact Or.inl (altGaussian_of_sqrt_sq hδpos.le hG)
  · exact Or.inr (altDiophantine_of_sq hδpos hD)

end RMFLean
