/-
PDF Lemma 1 (`lem:divisor`): four divisor-sum bounds, proved from Mathlib.
Helpers are `private` so they do not collide with `Proof/F1/J1.lean`.
-/
import RMFLean.Trusted.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

noncomputable section

open Classical BigOperators Nat Real Fintype
open Finset hiding card
open scoped Nat

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace RMFLean

/-! ### Recurrence `τ_{k+1}(n) = ∑_{d∣n} τ_k(n/d)` -/

private theorem factor_dvd {k n : ℕ} (_hn : n ≠ 0) (f : OrderedFactors k n) (i : Fin k) :
    f.val i ∣ n := by
  have hprod : (∏ j, f.val j) = n := f.property.2
  have hdvd : f.val i ∣ ∏ j, f.val j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rwa [hprod] at hdvd

private def tauSuccEquiv (k n : ℕ) (hn : 0 < n) :
    OrderedFactors (k + 1) n ≃
      (d : { x // x ∈ n.divisors }) × OrderedFactors k (n / d) where
  toFun f :=
    let d := f.val 0
    have hdvd : d ∣ n := factor_dvd hn.ne' f 0
    have hd : d ∈ n.divisors := Nat.mem_divisors.2 ⟨hdvd, hn.ne'⟩
    have hrest :
        (∏ i : Fin k, f.val i.succ) = n / d := by
      have hprod := f.property.2
      rw [Fin.prod_univ_succ] at hprod
      exact Nat.eq_div_of_mul_eq_right (f.property.1 0).ne' hprod
    ⟨⟨d, hd⟩, ⟨fun i => f.val i.succ, ⟨fun i => f.property.1 i.succ, hrest⟩⟩⟩
  invFun p :=
    let d := (p.1 : ℕ)
    have hdvd : d ∣ n := (Nat.mem_divisors.1 p.1.property).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors p.1.property
    ⟨Fin.cons d p.2.val, ⟨by
        intro i
        induction i using Fin.cases with
        | zero => exact hdpos
        | succ i => exact p.2.property.1 i,
      by
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [p.2.property.2, Nat.mul_div_cancel' hdvd]⟩⟩
  left_inv f := by
    refine Subtype.ext ?_
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  right_inv p := by
    obtain ⟨d, f⟩ := p
    refine Sigma.ext ?_ ?_
    · ext
      simp [Fin.cons_zero]
    · exact HEq.rfl

private theorem tau_succ_eq_sum (k n : ℕ) (hn : 0 < n) :
    tau (k + 1) n = ∑ d ∈ n.divisors, tau k (n / d) := by
  rw [tau, Fintype.card_congr (tauSuccEquiv k n hn), Fintype.card_sigma]
  simp_rw [tau]
  exact Finset.sum_coe_sort n.divisors fun d => tau k (n / d)

/-! ### Harmonic majorant of `∑ τ_k(n)/n` -/

private def posProdFinset (k N : ℕ) : Finset (Fin k → ℕ) :=
  piFinset fun _ : Fin k => Finset.Icc 1 N

private def posProdLEFinset (k N : ℕ) : Finset (Fin k → ℕ) :=
  (posProdFinset k N).filter fun f => (∏ i, f i) ≤ N

private def invProd (k : ℕ) (f : Fin k → ℕ) : ℝ :=
  (∏ i : Fin k, (f i : ℝ))⁻¹

private theorem mem_posProdFinset_iff {k N : ℕ} {f : Fin k → ℕ} :
    f ∈ posProdFinset k N ↔ ∀ i, f i ∈ Finset.Icc 1 N := by
  simp [posProdFinset, Fintype.mem_piFinset]

private theorem mem_posProdLEFinset_iff {k N : ℕ} {f : Fin k → ℕ} :
    f ∈ posProdLEFinset k N ↔
      (∀ i, f i ∈ Finset.Icc 1 N) ∧ (∏ i, f i) ≤ N := by
  simp [posProdLEFinset, posProdFinset, Fintype.mem_piFinset, and_assoc]

private abbrev IccSubtype (N : ℕ) := { n // n ∈ Finset.Icc 1 N }

private abbrev OrderedSigma (k N : ℕ) :=
  Σ n : IccSubtype N, OrderedFactors k n.val

private theorem ordered_mem_posProdLE {k N : ℕ} (p : OrderedSigma k N) :
    p.2.1 ∈ posProdLEFinset k N := by
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [posProdFinset, Fintype.mem_piFinset]
    intro i
    have hn : (p.1 : ℕ) ≠ 0 :=
      Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp p.1.property).1)
    have hle :=
      (OrderedFactors.factor_le hn p.2 i).trans (Finset.mem_Icc.mp p.1.property).2
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (p.2.property.1 i), hle⟩
  · simpa [p.2.property.2] using (Finset.mem_Icc.mp p.1.property).2

private def orderedProdEquiv (k N : ℕ) :
    OrderedSigma k N ≃ { f // f ∈ posProdLEFinset k N } where
  toFun p := ⟨p.2.1, ordered_mem_posProdLE p⟩
  invFun f :=
    let n := ∏ i : Fin k, f.1 i
    let hIcc : ∀ i, f.1 i ∈ Finset.Icc 1 N := (mem_posProdLEFinset_iff.mp f.property).1
    let hprod : (∏ i, f.1 i) ≤ N := (mem_posProdLEFinset_iff.mp f.property).2
    ⟨⟨n,
        Finset.mem_Icc.mpr
          ⟨Finset.one_le_prod' fun i _ => (Finset.mem_Icc.mp (hIcc i)).1, hprod⟩⟩,
      ⟨f.1, fun i => Nat.succ_le_iff.mp (Finset.mem_Icc.mp (hIcc i)).1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨n, hn⟩, ⟨f, hpos, hprod⟩⟩
    apply Sigma.ext
    · exact Subtype.ext hprod
    · cases hprod
      rfl
  right_inv := by
    rintro ⟨f, _hf⟩
    rfl

private theorem tau_div_eq_sum_invProd (k n : ℕ) (hn : 1 ≤ n) :
    (tau k n : ℝ) / (n : ℝ) = ∑ f : OrderedFactors k n, invProd k f.1 := by
  have hcard : (Fintype.card (OrderedFactors k n) : ℝ) =
      ∑ _f : OrderedFactors k n, (1 : ℝ) := by
    simpa using Fintype.card_eq_sum_ones (OrderedFactors k n)
  rw [tau, hcard, Finset.sum_div]
  refine Fintype.sum_congr _ _ fun f => ?_
  have hprod : (∏ i, (f.val i : ℝ)) = (n : ℝ) := by exact_mod_cast f.property.2
  simp [invProd, hprod]

private theorem tau_harmonic_sum_eq_posProdLE (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)) =
      ∑ f ∈ posProdLEFinset k N, invProd k f := by
  have hinner :
      (∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)) =
        ∑ n : IccSubtype N, (tau k (n : ℕ) : ℝ) / (n : ℝ) := by
    rw [← Finset.sum_coe_sort]
  have hsplit :
      ∑ n : IccSubtype N, (tau k (n : ℕ) : ℝ) / (n : ℝ) =
        ∑ n : IccSubtype N, ∑ f : OrderedFactors k n.val, invProd k f.1 := by
    refine Fintype.sum_congr _ _ fun n =>
      tau_div_eq_sum_invProd k n (Finset.mem_Icc.mp n.property).1
  have hfold :
      ∑ n : IccSubtype N, ∑ f : OrderedFactors k n.val, invProd k f.1 =
        ∑ p : OrderedSigma k N, invProd k p.2.1 :=
    (Fintype.sum_sigma (fun p : OrderedSigma k N => invProd k p.2.1)).symm
  have hequiv :
      ∑ p : OrderedSigma k N, invProd k p.2.1 =
        ∑ f ∈ posProdLEFinset k N, invProd k f := by
    calc
      ∑ p : OrderedSigma k N, invProd k p.2.1
          = ∑ t : { f // f ∈ posProdLEFinset k N }, invProd k t.1 :=
            Fintype.sum_equiv (orderedProdEquiv k N)
              (fun p => invProd k p.2.1) (fun t => invProd k t.1) fun _ => rfl
      _ = ∑ f ∈ posProdLEFinset k N, invProd k f :=
            Finset.sum_coe_sort (posProdLEFinset k N) (invProd k)
  rw [hinner, hsplit, hfold, hequiv]

private theorem posProdLE_sum_le_posProd (k N : ℕ) :
    (∑ f ∈ posProdLEFinset k N, invProd k f) ≤
      ∑ f ∈ posProdFinset k N, invProd k f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun f hf _ => by
    have hpos : 0 < ∏ i : Fin k, (f i : ℝ) :=
      Finset.prod_pos fun i _ =>
        Nat.cast_pos.mpr
          (Nat.succ_le_iff.mp (Finset.mem_Icc.mp (mem_posProdFinset_iff.mp hf i)).1)
    exact inv_nonneg.mpr (le_of_lt hpos)

private theorem posProdFinset_sum_eq_harmonic_pow (k N : ℕ) :
    (∑ f ∈ posProdFinset k N, invProd k f) =
      (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k := by
  have hinv :
      ∀ f ∈ posProdFinset k N, invProd k f = ∏ i : Fin k, (f i : ℝ)⁻¹ := by
    intro f hf
    have hpos : ∀ i, 0 < f i := fun i =>
      Nat.succ_le_iff.mp (Finset.mem_Icc.mp (mem_posProdFinset_iff.mp hf i)).1
    simp only [invProd]
    rw [← Finset.prod_inv_distrib]
  calc
    ∑ f ∈ posProdFinset k N, invProd k f
        = ∑ f ∈ posProdFinset k N, ∏ i : Fin k, (f i : ℝ)⁻¹ :=
          Finset.sum_congr rfl fun f hf => hinv f hf
    _ = ∏ _i : Fin k, ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
        simpa [posProdFinset] using
          (Finset.sum_prod_piFinset (ι := Fin k) (s := Finset.Icc 1 N)
            (g := fun _ m => (m : ℝ)⁻¹))
    _ = (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k := by
      simp [Finset.prod_const, Fintype.card_fin]

private theorem harmonic_Icc_le_one_add_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at this
  simpa using this

private theorem tau_harmonic_le_harmonic_pow (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)) ≤
      (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k := by
  calc
    ∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)
        = ∑ f ∈ posProdLEFinset k N, invProd k f :=
          tau_harmonic_sum_eq_posProdLE k N
    _ ≤ ∑ f ∈ posProdFinset k N, invProd k f :=
          posProdLE_sum_le_posProd k N
    _ = (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k :=
          posProdFinset_sum_eq_harmonic_pow k N

private theorem logN_gt_one {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) < Real.log N :=
  (Real.lt_log_iff_exp_lt (by positivity)).2 <|
    Real.exp_one_lt_three.trans_le (Nat.cast_le.mpr hN)

private theorem one_add_log_le_two_log {N : ℕ} (hN : 3 ≤ N) :
    1 + Real.log N ≤ 2 * Real.log N := by
  linarith [logN_gt_one hN]

private theorem one_le_two_mul_log {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ 2 * Real.log N := by
  linarith [logN_gt_one hN]

/-! ### Double-sum swap `∑_n ∑_{d∣n} τ(n/d) = ∑_m τ(m) ⌊N/m⌋` -/

private theorem mem_Icc_div_of_dvd {N n d : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hd : d ∈ n.divisors) :
    n / d ∈ Finset.Icc 1 N := by
  have hnpos : 0 < n := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1
  have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  exact Finset.mem_Icc.mpr
    ⟨(Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd hnpos hdvd),
      (Nat.div_le_self n d).trans (Finset.mem_Icc.mp hn).2⟩

private theorem mem_Icc_floor_of_dvd {N n d : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hd : d ∈ n.divisors) :
    d ∈ Finset.Icc 1 (N / (n / d)) := by
  have hnpos : 0 < n := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1
  have hdvd : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hmpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hdpos
  have hmul : d * (n / d) = n := by rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hdpos,
    (Nat.le_div_iff_mul_le hmpos).2 (hmul.trans_le (Finset.mem_Icc.mp hn).2)⟩

private theorem sum_tau_over_divisors_eq (k N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (tau k (n / d) : ℝ) =
      ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) * ((N / m : ℕ) : ℝ) := by
  rw [Finset.sum_sigma']
  have hmap :
      ∑ p ∈ (Finset.Icc 1 N).sigma fun n => n.divisors, (tau k (p.1 / p.2) : ℝ) =
        ∑ q ∈ (Finset.Icc 1 N).sigma fun m => Finset.Icc 1 (N / m), (tau k q.1 : ℝ) := by
    refine Finset.sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      have hn : p.1 ∈ Finset.Icc 1 N := (Finset.mem_sigma.1 hp).1
      have hd : p.2 ∈ p.1.divisors := (Finset.mem_sigma.1 hp).2
      exact Finset.mem_sigma.2 ⟨mem_Icc_div_of_dvd hn hd, mem_Icc_floor_of_dvd hn hd⟩
    · intro p hp q hq h
      have hd : p.2 ∈ p.1.divisors := (Finset.mem_sigma.1 hp).2
      have hqd : q.2 ∈ q.1.divisors := (Finset.mem_sigma.1 hq).2
      obtain ⟨hfst, hsnd'⟩ := Sigma.mk.inj h
      have hsnd : p.2 = q.2 := eq_of_heq hsnd'
      apply Sigma.ext
      · have hp1 : p.1 = p.2 * (p.1 / p.2) :=
          (Nat.mul_div_cancel' (Nat.mem_divisors.1 hd).1).symm
        have hq1 : q.1 = q.2 * (q.1 / q.2) :=
          (Nat.mul_div_cancel' (Nat.mem_divisors.1 hqd).1).symm
        rw [hp1, hq1, hfst, hsnd]
      · exact hsnd'
    · intro q hq
      have hm : q.1 ∈ Finset.Icc 1 N := (Finset.mem_sigma.1 hq).1
      have hdI : q.2 ∈ Finset.Icc 1 (N / q.1) := (Finset.mem_sigma.1 hq).2
      have hmpos : 0 < q.1 := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hm).1
      have hdpos : 0 < q.2 := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hdI).1
      have hle : q.2 * q.1 ≤ N := by
        have := (Nat.le_div_iff_mul_le hmpos).1 (Finset.mem_Icc.mp hdI).2
        omega
      refine ⟨⟨q.2 * q.1, q.2⟩, Finset.mem_sigma.2 ?_, ?_⟩
      · exact ⟨Finset.mem_Icc.mpr
          ⟨Nat.mul_le_mul (Nat.succ_le_iff.mpr hdpos) (Nat.succ_le_iff.mpr hmpos), hle⟩,
          Nat.mem_divisors.2 ⟨dvd_mul_right _ _, (Nat.mul_pos hdpos hmpos).ne'⟩⟩
      · apply Sigma.ext
        · exact Nat.mul_div_cancel_left q.1 hdpos
        · rfl
    · intro p hp
      rfl
  rw [hmap, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hcard : (Finset.Icc 1 (N / m)).card = N / m := by
    simp [Nat.card_Icc]
  simp [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

private theorem sum_tau_succ_le (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (tau (k + 1) n : ℝ)) ≤
      (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) / (m : ℝ) := by
  have hrec :
      ∑ n ∈ Finset.Icc 1 N, (tau (k + 1) n : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (tau k (n / d) : ℝ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnpos : 0 < n := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1
    exact_mod_cast tau_succ_eq_sum k n hnpos
  calc
    ∑ n ∈ Finset.Icc 1 N, (tau (k + 1) n : ℝ)
        = ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) * ((N / m : ℕ) : ℝ) := by
          rw [hrec, sum_tau_over_divisors_eq]
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) * ((N : ℝ) / (m : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by exact_mod_cast (Nat.zero_le _))
    _ = (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) / (m : ℝ) := by
          simp [div_eq_mul_inv, mul_left_comm, Finset.mul_sum]

/-- PDF Lemma 1, first inequality. -/
theorem divisor_sum_bound (N ℓ : ℕ) (hN : 3 ≤ N) (hℓ : 1 ≤ ℓ) :
    (∑ n ∈ Finset.Icc 1 N, (tau ℓ n : Real)) ≤
      (N : Real) * (2 * Real.log N) ^ (ℓ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hH := tau_harmonic_le_harmonic_pow k N
  have hpow : (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k ≤ (2 * Real.log N) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    exact (harmonic_Icc_le_one_add_log N).trans (one_add_log_le_two_log hN)
  calc
    ∑ n ∈ Finset.Icc 1 N, (tau (k + 1) n : ℝ)
        ≤ (N : ℝ) * ∑ m ∈ Finset.Icc 1 N, (tau k m : ℝ) / (m : ℝ) :=
          sum_tau_succ_le k N
    _ ≤ (N : ℝ) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k :=
          mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ (N : ℝ) * (2 * Real.log N) ^ k := by gcongr

/-- PDF Lemma 1, fourth inequality. -/
theorem divisor_sum_div_bound (N ℓ : ℕ) (hN : 3 ≤ N) (_hℓ : 1 ≤ ℓ) :
    (∑ n ∈ Finset.Icc 1 N, (tau ℓ n : Real) / (n : Real)) ≤
      (2 * Real.log N) ^ ℓ := by
  calc
    ∑ n ∈ Finset.Icc 1 N, (tau ℓ n : ℝ) / (n : ℝ)
        ≤ (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ ℓ :=
          tau_harmonic_le_harmonic_pow ℓ N
    _ ≤ (1 + Real.log N) ^ ℓ :=
          pow_le_pow_left₀ (by positivity) (harmonic_Icc_le_one_add_log N) _
    _ ≤ (2 * Real.log N) ^ ℓ :=
          pow_le_pow_left₀ (by positivity) (one_add_log_le_two_log hN) _

/-! ### Multiplicativity and `τ_k(n)² ≤ τ_{k²}(n)` -/

private def aPart (a m : ℕ) : ℕ := Nat.gcd m (a ^ m)

private def bPart (a m : ℕ) : ℕ := m / aPart a m

private theorem aPart_pos {a m : ℕ} (hm : 0 < m) : 0 < aPart a m :=
  Nat.gcd_pos_of_pos_left _ hm

private theorem aPart_dvd (a m : ℕ) : aPart a m ∣ m :=
  Nat.gcd_dvd_left _ _

private theorem aPart_mul_bPart {a m : ℕ} :
    aPart a m * bPart a m = m :=
  Nat.mul_div_cancel' (aPart_dvd a m)

private theorem aPart_factorization {a m p : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (aPart a m).factorization p =
      if a.factorization p = 0 then 0 else m.factorization p := by
  have hpow : a ^ m ≠ 0 := pow_ne_zero m ha
  rw [aPart, Nat.factorization_gcd hm hpow, Nat.factorization_pow]
  change min (m.factorization p) (m * a.factorization p) =
    if a.factorization p = 0 then 0 else m.factorization p
  split_ifs with hp
  · simp [hp]
  · have hapos : 0 < a.factorization p := Nat.pos_of_ne_zero hp
    have hlt : m.factorization p < m := Nat.factorization_lt p hm
    exact min_eq_left (le_trans (Nat.le_of_lt hlt) (Nat.le_mul_of_pos_right m hapos))

private theorem factorization_eq_zero_of_coprime_right {a b p : ℕ}
    (hcop : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : a.factorization p ≠ 0) : b.factorization p = 0 := by
  have hmin : min (a.factorization p) (b.factorization p) = 0 := by
    have hfg := Nat.factorization_gcd ha hb
    rw [hcop.gcd_eq_one, Nat.factorization_one] at hfg
    have := congrArg (fun f : ℕ →₀ ℕ => f p) hfg
    simpa [Finsupp.zero_apply, Finsupp.inf_apply] using this.symm
  omega

private theorem aPart_prod {k a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) (f : OrderedFactors k (a * b)) :
    (∏ i, aPart a (f.val i)) = a := by
  have hpos : ∀ i, 0 < aPart a (f.val i) := fun i => aPart_pos (f.property.1 i)
  have hP : (∏ i, aPart a (f.val i)) ≠ 0 := (Finset.prod_pos fun i _ => hpos i).ne'
  refine Nat.eq_of_factorization_eq hP ha fun p => ?_
  have hfi : ∀ i ∈ Finset.univ, aPart a (f.val i) ≠ 0 := fun i _ => (hpos i).ne'
  rw [show (∏ i, aPart a (f.val i)) = ∏ i ∈ Finset.univ, aPart a (f.val i) by rfl,
    Nat.factorization_prod hfi, Finsupp.finsetSum_apply]
  simp_rw [aPart_factorization ha (f.property.1 _).ne']
  by_cases hp : a.factorization p = 0
  · simp [hp]
  · simp only [hp, if_false]
    have hf0 : ∀ i ∈ Finset.univ, f.val i ≠ 0 := fun i _ => (f.property.1 i).ne'
    have hsf := congrArg (fun g : ℕ →₀ ℕ => g p) (Nat.factorization_prod hf0)
    rw [Finsupp.finsetSum_apply] at hsf
    have hb0 : b.factorization p = 0 :=
      factorization_eq_zero_of_coprime_right hcop ha hb hp
    have hab : (a * b).factorization p = a.factorization p := by
      rw [Nat.factorization_mul ha hb, Finsupp.add_apply, hb0, add_zero]
    have hprod : (∏ i ∈ Finset.univ, f.val i) = a * b := f.property.2
    rw [hprod, hab] at hsf
    exact hsf.symm

private theorem aPart_eq_left {a b fa fb : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a b) (hfa : fa ∣ a) (hfb : fb ∣ b)
    (hfa_pos : 0 < fa) (hfb_pos : 0 < fb) :
    aPart a (fa * fb) = fa := by
  have hmul_ne : fa * fb ≠ 0 := mul_ne_zero hfa_pos.ne' hfb_pos.ne'
  refine Nat.eq_of_factorization_eq (aPart_pos (mul_pos hfa_pos hfb_pos)).ne' hfa_pos.ne' fun p => ?_
  rw [aPart_factorization ha hmul_ne]
  by_cases hp : a.factorization p = 0
  · have hfa0 : fa.factorization p = 0 := by
      have := (Nat.factorization_le_iff_dvd hfa_pos.ne' ha).2 hfa p
      omega
    simp [hp, hfa0]
  · have hb0 : b.factorization p = 0 :=
      factorization_eq_zero_of_coprime_right hcop ha hb hp
    have hfb0 : fb.factorization p = 0 := by
      have := (Nat.factorization_le_iff_dvd hfb_pos.ne' hb).2 hfb p
      omega
    rw [if_neg hp, Nat.factorization_mul hfa_pos.ne' hfb_pos.ne', Finsupp.add_apply, hfb0, add_zero]

private def tauMulEquiv {k a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    OrderedFactors k (a * b) ≃ OrderedFactors k a × OrderedFactors k b where
  toFun f :=
    have hprodA : (∏ i, aPart a (f.val i)) = a := aPart_prod ha.ne' hb.ne' hcop f
    have hmul :
        (∏ i, aPart a (f.val i)) * (∏ i, bPart a (f.val i)) = a * b := by
      rw [← Finset.prod_mul_distrib]
      exact (Finset.prod_congr rfl fun i _ => aPart_mul_bPart).trans f.property.2
    have hprodB : (∏ i, bPart a (f.val i)) = b := by
      apply Nat.mul_left_cancel ha
      rwa [hprodA] at hmul
    ⟨⟨fun i => aPart a (f.val i), ⟨fun i => aPart_pos (f.property.1 i), hprodA⟩⟩,
      ⟨fun i => bPart a (f.val i),
        ⟨fun i => Nat.div_pos (Nat.le_of_dvd (f.property.1 i) (aPart_dvd a _))
            (aPart_pos (f.property.1 i)), hprodB⟩⟩⟩
  invFun p :=
    ⟨fun i => p.1.val i * p.2.val i,
      ⟨fun i => mul_pos (p.1.property.1 i) (p.2.property.1 i), by
        rw [Finset.prod_mul_distrib, p.1.property.2, p.2.property.2]⟩⟩
  left_inv f := by
    refine Subtype.ext ?_
    funext i
    simp [aPart_mul_bPart]
  right_inv p := by
    have hfa : ∀ i, p.1.val i ∣ a := fun i => by
      have := Finset.dvd_prod_of_mem (fun j => p.1.val j) (Finset.mem_univ i)
      rwa [p.1.property.2] at this
    have hfb : ∀ i, p.2.val i ∣ b := fun i => by
      have := Finset.dvd_prod_of_mem (fun j => p.2.val j) (Finset.mem_univ i)
      rwa [p.2.property.2] at this
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      funext i
      exact aPart_eq_left ha.ne' hb.ne' hcop (hfa i) (hfb i) (p.1.property.1 i) (p.2.property.1 i)
    · refine Subtype.ext ?_
      funext i
      have hA := aPart_eq_left ha.ne' hb.ne' hcop (hfa i) (hfb i)
        (p.1.property.1 i) (p.2.property.1 i)
      simp [bPart, hA, Nat.mul_div_cancel_left _ (p.1.property.1 i)]

private theorem tau_mul_coprime {k a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    tau k (a * b) = tau k a * tau k b := by
  rw [tau, tau, tau, Fintype.card_congr (tauMulEquiv (k := k) ha hb hcop), Fintype.card_prod]

private theorem tau_k_one (k : ℕ) : tau k 1 = 1 := by
  refine Fintype.card_eq_one_iff.2 ⟨⟨fun _ => 1, ⟨fun _ => Nat.zero_lt_one, by simp⟩⟩, ?_⟩
  intro f
  refine Subtype.ext ?_
  funext i
  have hdvd : f.val i ∣ 1 := by
    have := Finset.dvd_prod_of_mem (fun j => f.val j) (Finset.mem_univ i)
    rwa [f.property.2] at this
  exact Nat.eq_one_of_dvd_one hdvd

private theorem tau_one_of_pos (n : ℕ) (hn : 0 < n) : tau 1 n = 1 := by
  refine Fintype.card_eq_one_iff.2 ⟨⟨fun _ => n, ⟨fun _ => hn, by simp [Fin.prod_univ_one]⟩⟩, ?_⟩
  intro f
  refine Subtype.ext ?_
  funext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  simpa [Fin.prod_univ_one] using f.property.2

private theorem tau_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ {k : ℕ}, 1 ≤ k → ∀ e, tau k (p ^ e) = (e + k - 1).choose (k - 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro e
    simpa [tau_one_of_pos (p ^ e) (pow_pos hp.pos e)] using
      (show (e + 1 - 1).choose 0 = 1 by simp)
  | succ k hk ih =>
    intro e
    have hpos : 0 < p ^ e := pow_pos hp.pos e
    rw [tau_succ_eq_sum k (p ^ e) hpos, Nat.divisors_prime_pow hp e, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have hsum :
        ∑ j ∈ Finset.range (e + 1), tau k (p ^ e / p ^ j) =
          ∑ t ∈ Finset.range (e + 1), (t + k - 1).choose (k - 1) := by
      have h1 :
          ∑ j ∈ Finset.range (e + 1), tau k (p ^ e / p ^ j) =
            ∑ j ∈ Finset.range (e + 1), tau k (p ^ (e - j)) :=
        Finset.sum_congr rfl fun j hj => by
          have hle : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [Nat.pow_div hle hp.pos]
      have h2 :
          ∑ j ∈ Finset.range (e + 1), tau k (p ^ (e - j)) =
            ∑ t ∈ Finset.range (e + 1), tau k (p ^ t) :=
        Finset.sum_range_reflect (fun t => tau k (p ^ t)) (e + 1)
      exact h1.trans (h2.trans (Finset.sum_congr rfl fun t ht => ih t))
    have hsum' :
        ∑ t ∈ Finset.range (e + 1), (t + k - 1).choose (k - 1) =
          ∑ t ∈ Finset.range (e + 1), (t + (k - 1)).choose (k - 1) :=
      Finset.sum_congr rfl fun t ht => by
        have : t + k - 1 = t + (k - 1) := by omega
        simp [this]
    rw [hsum, hsum', Nat.sum_range_add_choose e (k - 1)]
    congr 1 <;> omega

private theorem choose_sq_le (a k : ℕ) (hk : 1 ≤ k) :
    ((a + k - 1).choose (k - 1)) ^ 2 ≤ (a + k ^ 2 - 1).choose (k ^ 2 - 1) := by
  have hk2 : 1 ≤ k * k :=
    hk.trans (Nat.le_mul_of_pos_left k (Nat.succ_le_iff.mp hk))
  induction a with
  | zero =>
    have h1 : 0 + k - 1 = k - 1 := by omega
    have h2 : 0 + k ^ 2 - 1 = k ^ 2 - 1 := by omega
    simp [h1, h2]
  | succ a ih =>
    have hnk : 1 ≤ a + k := le_trans hk (Nat.le_add_left k a)
    have hnk2 : 1 ≤ a + k ^ 2 := by
      have : 1 ≤ k ^ 2 := by simpa [pow_two] using hk2
      exact le_trans this (Nat.le_add_left _ a)
    have hrec_left :
        (a + k).choose (k - 1) * (a + 1) =
          (a + k - 1).choose (k - 1) * (a + k) := by
      have h := Nat.choose_mul_succ_eq (a + k - 1) (k - 1)
      simp [Nat.sub_add_cancel hnk] at h
      have hr' : a + k - (k - 1) = a + 1 := by
        rw [Nat.add_sub_assoc (Nat.sub_le k 1), Nat.sub_sub_self hk]
      rw [hr'] at h
      exact h.symm
    have hrec_right :
        (a + k ^ 2).choose (k ^ 2 - 1) * (a + 1) =
          (a + k ^ 2 - 1).choose (k ^ 2 - 1) * (a + k ^ 2) := by
      have h := Nat.choose_mul_succ_eq (a + k ^ 2 - 1) (k ^ 2 - 1)
      simp [Nat.sub_add_cancel hnk2] at h
      have hk2' : 1 ≤ k ^ 2 := by simpa [pow_two] using hk2
      have hr' : a + k ^ 2 - (k ^ 2 - 1) = a + 1 := by
        rw [Nat.add_sub_assoc (Nat.sub_le (k ^ 2) 1), Nat.sub_sub_self hk2']
      rw [hr'] at h
      exact h.symm
    have hquad : (a + k) ^ 2 ≤ (a + 1) * (a + k ^ 2) := by
      have hk1sq : (0 : ℤ) ≤ ((k : ℤ) - 1) ^ 2 := sq_nonneg _
      have hZ : ((a : ℤ) + k) ^ 2 ≤ (a + 1 : ℤ) * (a + (k : ℤ) ^ 2) := by
        nlinarith [hk1sq]
      exact_mod_cast hZ
    have hsq :
        ((a + k).choose (k - 1)) ^ 2 * (a + 1) ^ 2 ≤
          (a + k ^ 2).choose (k ^ 2 - 1) * (a + 1) ^ 2 := by
      have h1 :
          ((a + k).choose (k - 1)) ^ 2 * (a + 1) ^ 2 =
            ((a + k - 1).choose (k - 1)) ^ 2 * (a + k) ^ 2 := by
        calc
          ((a + k).choose (k - 1)) ^ 2 * (a + 1) ^ 2
              = ((a + k).choose (k - 1) * (a + 1)) ^ 2 := by ring
          _ = ((a + k - 1).choose (k - 1) * (a + k)) ^ 2 := by rw [hrec_left]
          _ = ((a + k - 1).choose (k - 1)) ^ 2 * (a + k) ^ 2 := by ring
      have h2 :
          ((a + k - 1).choose (k - 1)) ^ 2 * (a + k) ^ 2 ≤
            (a + k ^ 2 - 1).choose (k ^ 2 - 1) * (a + k) ^ 2 :=
        Nat.mul_le_mul_right _ ih
      have h3 :
          (a + k ^ 2 - 1).choose (k ^ 2 - 1) * (a + k) ^ 2 ≤
            (a + k ^ 2 - 1).choose (k ^ 2 - 1) * ((a + 1) * (a + k ^ 2)) :=
        Nat.mul_le_mul_left _ hquad
      have h4 :
          (a + k ^ 2 - 1).choose (k ^ 2 - 1) * ((a + 1) * (a + k ^ 2)) =
            (a + k ^ 2).choose (k ^ 2 - 1) * (a + 1) ^ 2 := by
        calc
          _ = (a + k ^ 2 - 1).choose (k ^ 2 - 1) * (a + k ^ 2) * (a + 1) := by ring
          _ = (a + k ^ 2).choose (k ^ 2 - 1) * (a + 1) ^ 2 := by
                rw [← hrec_right]; ring
      exact h1.symm ▸ h2.trans (h3.trans (le_of_eq h4))
    have hpos : 0 < (a + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos a)
    have h1eq : a + 1 + k - 1 = a + k := by omega
    have h2eq : a + 1 + k ^ 2 - 1 = a + k ^ 2 := by omega
    simpa [h1eq, h2eq] using Nat.le_of_mul_le_mul_right hsq hpos

private theorem tau_sq_le_tau_sq (k n : ℕ) (hk : 1 ≤ k) :
    tau k n ^ 2 ≤ tau (k * k) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · have h0 : tau k 0 = 0 := Fintype.card_eq_zero
      have h0' : tau (k * k) 0 = 0 := Fintype.card_eq_zero
      rw [h0, h0']
      exact Nat.zero_le _
    · by_cases h1 : n.succ = 1
      · have h1' : n + 1 = 1 := by simpa [Nat.succ_eq_add_one] using h1
        simp [h1', tau_k_one]
      · obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h1
        set e := n.succ.factorization p
        set m := ordCompl[p] n.succ
        have hn : 0 < n.succ := Nat.succ_pos _
        have he_pos : 0 < e :=
          (Nat.Prime.dvd_iff_one_le_factorization hp hn.ne').1 hdvd
        have hdecomp : p ^ e * m = n.succ :=
          Nat.ordProj_mul_ordCompl_eq_self n.succ p
        have hpepos : 0 < p ^ e := pow_pos hp.pos e
        have hmpos : 0 < m := by
          have : m = n.succ / p ^ e := rfl
          exact Nat.div_pos (Nat.le_of_dvd hn (by simpa [e] using Nat.ordProj_dvd n.succ p)) hpepos
        have hm_lt : m < n.succ := by
          have hp2 : 2 ≤ p ^ e :=
            hp.two_le.trans (Nat.le_self_pow (Nat.ne_zero_of_lt he_pos) p)
          have h2m : m < 2 * m := by
            have : m < m + m := Nat.lt_add_of_pos_right hmpos
            simpa [two_mul] using this
          calc
            m < 2 * m := h2m
            _ ≤ p ^ e * m := Nat.mul_le_mul_right m hp2
            _ = n.succ := hdecomp
        have hcop : Nat.Coprime (p ^ e) m := (Nat.coprime_ordCompl hp hn.ne').pow_left e
        have hn1 : n + 1 = p ^ e * m := by
          simpa [Nat.succ_eq_add_one] using hdecomp.symm
        rw [hn1, tau_mul_coprime hpepos hmpos hcop,
          tau_mul_coprime (k := k * k) hpepos hmpos hcop, mul_pow]
        have hpow : tau k (p ^ e) ^ 2 ≤ tau (k * k) (p ^ e) := by
          rw [tau_prime_pow hp hk e, tau_prime_pow hp
            (hk.trans (Nat.le_mul_of_pos_left k (Nat.succ_le_iff.mp hk))) e]
          simpa [pow_two] using choose_sq_le e k hk
        exact Nat.mul_le_mul hpow (ih m (Nat.succ_eq_add_one n ▸ hm_lt))

/-- PDF Lemma 1, second inequality. -/
theorem divisor_sum_sq_bound (N ℓ : ℕ) (hN : 3 ≤ N) (hℓ : 1 ≤ ℓ) :
    (∑ n ∈ Finset.Icc 1 N, (tau ℓ n : Real) ^ 2) ≤
      (N : Real) * (2 * Real.log N) ^ (ℓ ^ 2 - 1) := by
  have hpt : ∀ n ∈ Finset.Icc 1 N, (tau ℓ n : ℝ) ^ 2 ≤ (tau (ℓ * ℓ) n : ℝ) := fun n hn => by
    exact_mod_cast tau_sq_le_tau_sq ℓ n hℓ
  have hsum := divisor_sum_bound N (ℓ * ℓ) hN
    (hℓ.trans (Nat.le_mul_of_pos_left ℓ (Nat.succ_le_iff.mp hℓ)))
  calc
    ∑ n ∈ Finset.Icc 1 N, (tau ℓ n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 N, (tau (ℓ * ℓ) n : ℝ) := Finset.sum_le_sum hpt
    _ ≤ (N : ℝ) * (2 * Real.log N) ^ (ℓ * ℓ - 1) := hsum
    _ = (N : ℝ) * (2 * Real.log N) ^ (ℓ ^ 2 - 1) := by simp [pow_two]

/-! ### Abel tail -/

private def Ssq (ℓ X : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 X, (tau ℓ n : ℝ) ^ 2

private theorem Ssq_succ (ℓ n : ℕ) (hn : 1 ≤ n) :
    Ssq ℓ n = Ssq ℓ (n - 1) + (tau ℓ n : ℝ) ^ 2 := by
  have hins : insert n (Finset.Icc 1 (n - 1)) = Finset.Icc 1 n :=
    Finset.insert_Icc_pred_right_eq_Icc hn
  have hnmem : n ∉ Finset.Icc 1 (n - 1) := by
    simp [Finset.mem_Icc]; omega
  rw [Ssq, ← hins, Finset.sum_insert hnmem, Ssq, add_comm]

private theorem tau_le_divisors_pow (k n : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    tau k n ≤ n.divisors.card ^ (k - 1) := by
  cases k with
  | zero => cases hk
  | succ t =>
  let toDivs : OrderedFactors (t + 1) n → (Fin t → { d // d ∈ n.divisors }) :=
    fun f i => ⟨f.val i.castSucc, Nat.mem_divisors.2 ⟨factor_dvd hn.ne' f i.castSucc, hn.ne'⟩⟩
  have hinj : Function.Injective toDivs := by
    intro f g hfg
    refine Subtype.ext ?_
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrArg Subtype.val (congrFun hfg j)
    · have hf := f.property.2
      have hg := g.property.2
      rw [Fin.prod_univ_castSucc] at hf hg
      have hprod :
          (∏ j : Fin t, f.val j.castSucc) = ∏ j : Fin t, g.val j.castSucc :=
        Finset.prod_congr rfl fun j _ => congrArg Subtype.val (congrFun hfg j)
      have hpos : 0 < ∏ j : Fin t, f.val j.castSucc :=
        Finset.prod_pos fun j _ => f.property.1 _
      have hfeq :
          (∏ j : Fin t, f.val j.castSucc) * f.val (Fin.last t) =
            (∏ j : Fin t, f.val j.castSucc) * g.val (Fin.last t) := by
        calc
          (∏ j : Fin t, f.val j.castSucc) * f.val (Fin.last t) = n := hf
          _ = (∏ j : Fin t, g.val j.castSucc) * g.val (Fin.last t) := hg.symm
          _ = (∏ j : Fin t, f.val j.castSucc) * g.val (Fin.last t) := by rw [hprod]
      exact Nat.mul_left_cancel hpos hfeq
  simpa [tau, Fintype.card_pi, Fintype.card_coe] using Fintype.card_le_of_injective toDivs hinj

private theorem Ssq_le (N ℓ k : ℕ) (hN : 3 ≤ N) (hℓ : 1 ≤ ℓ) (hk : k ≤ N) :
    Ssq ℓ k ≤ (k : ℝ) * (2 * Real.log N) ^ (ℓ ^ 2 - 1) := by
  let L : ℝ := (2 * Real.log N) ^ (ℓ ^ 2 - 1)
  have hL : 1 ≤ L := one_le_pow₀ (one_le_two_mul_log hN)
  rcases k with _ | k
  · simp [Ssq]
  · by_cases h3 : 3 ≤ k.succ
    · have hbound := divisor_sum_sq_bound k.succ ℓ h3 hℓ
      have hlog : Real.log k.succ ≤ Real.log N :=
        Real.log_le_log (by positivity) (Nat.cast_le.mpr hk)
      have hpow : (2 * Real.log k.succ) ^ (ℓ ^ 2 - 1) ≤ L :=
        pow_le_pow_left₀ (by positivity) (by gcongr) _
      exact hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    · have hk12 : k.succ = 1 ∨ k.succ = 2 := by omega
      rcases hk12 with hk1 | hk2
      · have hk1' : k + 1 = 1 := by simpa [Nat.succ_eq_add_one] using hk1
        rw [hk1']
        simpa [Ssq, tau_k_one] using hL
      · have hk2' : k + 1 = 2 := by simpa [Nat.succ_eq_add_one] using hk2
        rw [hk2']
        have hτ : tau ℓ 2 ≤ 2 ^ (ℓ - 1) := by
          have hdiv : (2 : ℕ).divisors.card = 2 := by
            simp [Nat.Prime.divisors Nat.prime_two]
          have := tau_le_divisors_pow ℓ 2 (by decide) hℓ
          simpa [hdiv] using this
        have hS : Ssq ℓ 2 = 1 + (tau ℓ 2 : ℝ) ^ 2 := by
          rw [Ssq_succ ℓ 2 (by decide)]
          simp [Ssq, tau_k_one]
        rw [hS]
        have h2 : (tau ℓ 2 : ℝ) ^ 2 ≤ L := by
          rcases eq_or_lt_of_le hℓ with rfl | hℓ2
          · have : tau 1 2 = 1 := tau_one_of_pos 2 (by decide)
            simp [this]
            exact hL
          · have hbase : (2 : ℝ) ≤ 2 * Real.log N := by linarith [logN_gt_one hN]
            have hexp : 2 * (ℓ - 1) ≤ ℓ ^ 2 - 1 := by
              have h2le : 2 ≤ ℓ := Nat.succ_le_of_lt hℓ2
              have h1 : 1 ≤ ℓ ^ 2 :=
                le_trans (by decide : 1 ≤ 2 ^ 2) (Nat.pow_le_pow_left h2le 2)
              rw [Nat.le_sub_iff_add_le h1]
              have hZ : (2 * (ℓ - 1) + 1 : ℤ) ≤ (ℓ : ℤ) ^ 2 := by
                have : (2 : ℤ) ≤ ℓ := by exact_mod_cast h2le
                nlinarith
              exact_mod_cast hZ
            have hτR : (tau ℓ 2 : ℝ) ≤ (2 : ℝ) ^ (ℓ - 1) := by exact_mod_cast hτ
            have hsq : (tau ℓ 2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (ℓ - 1)) := by
              have := pow_le_pow_left₀ (by positivity) hτR 2
              rwa [← pow_mul, mul_comm (ℓ - 1)] at this
            have : (2 : ℝ) ^ (2 * (ℓ - 1)) ≤ L := by
              calc
                (2 : ℝ) ^ (2 * (ℓ - 1)) ≤ (2 * Real.log N) ^ (2 * (ℓ - 1)) :=
                  pow_le_pow_left₀ (by positivity) hbase _
                _ ≤ (2 * Real.log N) ^ (ℓ ^ 2 - 1) :=
                  pow_le_pow_right₀ (by linarith [logN_gt_one hN]) hexp
            exact hsq.trans this
        have h2L : (1 : ℝ) + (tau ℓ 2 : ℝ) ^ 2 ≤ (2 : ℝ) * L := by
          nlinarith [hL, h2]
        exact h2L

private theorem inv_sq_diff_le (k : ℕ) (hk : 0 < k) :
    ((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2 ≤ 2 / (k : ℝ) ^ 3 := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hdiff :
      ((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2 =
        (2 * (k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  have hnum : 2 * (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by linarith
  have hden : 0 ≤ (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 := by positivity
  have h1 :
      (2 * (k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) ≤
        2 * ((k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) :=
    div_le_div_of_nonneg_right hnum hden
  have h2 :
      2 * ((k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) =
        2 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) := by
    field_simp
  have h3 : 2 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) ≤ 2 / (k : ℝ) ^ 3 := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    simpa [pow_succ] using
      mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith) (sq_nonneg (k : ℝ))
  calc
    ((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2
        = (2 * (k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := hdiff
    _ ≤ 2 * ((k : ℝ) + 1) / ((k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := h1
    _ = 2 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) := h2
    _ ≤ 2 / (k : ℝ) ^ 3 := h3

private theorem telescope_inv {A M : ℕ} (_hA : 0 < A) (hAM : A ≤ M) :
    ∑ k ∈ Finset.Icc A M, ((1 : ℝ) / k - 1 / (k + 1)) = 1 / A - 1 / (M + 1 : ℝ) := by
  induction M, hAM using Nat.le_induction with
  | base =>
    simp
    try ring
  | succ M hM ih =>
    have hle : A ≤ M + 1 := Nat.le_succ_of_le hM
    rw [← Finset.insert_Icc_right_eq_Icc_add_one hle,
      Finset.sum_insert (by simp [Finset.mem_Icc]), ih]
    simp [Nat.cast_succ] <;> ring

private theorem sum_inv_sq_le {A M : ℕ} (hA : 0 < A) (hAM : A ≤ M) :
    ∑ k ∈ Finset.Icc A M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / (A : ℝ) := by
  have hterm : ∀ k ∈ Finset.Icc A M,
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / k - 1 / (k + 1)) := by
    intro k hk
    have hkpos : 0 < k := lt_of_lt_of_le hA (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hkpos
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hkpos)
    have hle : (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * (k + 1)) := by
      have hmul : (k : ℝ) * (k + 1) ≤ 2 * (k : ℝ) ^ 2 := by nlinarith [hk1]
      exact (div_le_div_iff₀ (pow_pos hk0 2) (mul_pos hk0 (by linarith))).mpr
        (by simpa using hmul)
    have heq : (2 : ℝ) / ((k : ℝ) * (k + 1)) = 2 * (1 / k - 1 / (k + 1)) := by
      field_simp
      try ring
    exact hle.trans (le_of_eq heq)
  have htel := telescope_inv hA hAM
  have hsum := Finset.sum_le_sum hterm
  have hmul :
      ∑ k ∈ Finset.Icc A M, 2 * ((1 : ℝ) / k - 1 / (k + 1)) =
        2 * (1 / A - 1 / (M + 1 : ℝ)) := by
    rw [← Finset.mul_sum, htel]
  have hlast : 2 * ((1 : ℝ) / A - 1 / (M + 1 : ℝ)) ≤ 2 / (A : ℝ) := by
    have : 2 * ((1 : ℝ) / A - 1 / (M + 1 : ℝ)) = 2 / A - 2 / (M + 1 : ℝ) := by ring
    rw [this]
    have : 0 ≤ (2 : ℝ) / (M + 1 : ℝ) := by positivity
    linarith
  linarith

/-- Partial sums of `τ²` from `1`, matching Abel's `G` after zeroing the `n = 0` term. -/
private theorem Gsq_range (ℓ n : ℕ) :
    ∑ i ∈ Finset.range n, (if i = 0 then (0 : ℝ) else (tau ℓ i : ℝ) ^ 2) =
      Ssq ℓ (n - 1) := by
  cases n with
  | zero => simp [Ssq]
  | succ n =>
    have hr : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
    rw [hr, Finset.sum_insert hmem, if_pos rfl, zero_add]
    simp only [Nat.add_sub_cancel, Ssq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 :=
      (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)
    simp [hk0]

private theorem abel_tau_sq (ℓ A N : ℕ) (hA : 0 < A) (hAN : A < N) :
    ∑ n ∈ Finset.Icc A N, (tau ℓ n : ℝ) ^ 2 / (n : ℝ) ^ 2 =
      Ssq ℓ N / (N : ℝ) ^ 2 - Ssq ℓ (A - 1) / (A : ℝ) ^ 2 +
        ∑ k ∈ Finset.Icc A (N - 1),
          Ssq ℓ k * (((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2) := by
  let f : ℕ → ℝ := fun i => ((i : ℝ)⁻¹) ^ 2
  let g : ℕ → ℝ := fun i => if i = 0 then 0 else (tau ℓ i : ℝ) ^ 2
  have hIcc : Finset.Icc A N = Finset.Ioc (A - 1) N := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hmid : Finset.Icc A (N - 1) = Finset.Ioc (A - 1) (N - 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hm : A - 1 < N := by omega
  have hG : ∀ t, ∑ i ∈ Finset.range t, g i = Ssq ℓ (t - 1) := fun t => by
    simpa [g] using Gsq_range ℓ t
  have hterm : ∀ i ∈ Finset.Ioc (A - 1) N,
      f i * g i = (tau ℓ i : ℝ) ^ 2 / (i : ℝ) ^ 2 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      have : A - 1 < i := (Finset.mem_Ioc.mp hi).1
      omega
    simp [f, g, hi0, div_eq_mul_inv, pow_two, mul_comm]
  have hparts := Finset.sum_Ioc_by_parts (R := ℝ) (M := ℝ) f g hm
  simp only [smul_eq_mul] at hparts
  have hsum_fg :
      ∑ n ∈ Finset.Icc A N, (tau ℓ n : ℝ) ^ 2 / (n : ℝ) ^ 2 =
        ∑ n ∈ Finset.Ioc (A - 1) N, f n * g n := by
    rw [hIcc]
    refine Finset.sum_congr rfl fun n hn => (hterm n hn).symm
  rw [hsum_fg, hparts]
  have hGN : ∑ i ∈ Finset.range (N + 1), g i = Ssq ℓ N := by simpa using hG (N + 1)
  have hGA : ∑ i ∈ Finset.range A, g i = Ssq ℓ (A - 1) := hG A
  have hGi : ∀ i, ∑ j ∈ Finset.range (i + 1), g j = Ssq ℓ i := fun i => by
    simpa using hG (i + 1)
  have hApred : A - 1 + 1 = A := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hA)
  simp only [hGN, hGA, hApred]
  simp_rw [hGi]
  have hfront_eq :
      f N * Ssq ℓ N - f A * Ssq ℓ (A - 1) =
        Ssq ℓ N / (N : ℝ) ^ 2 - Ssq ℓ (A - 1) / (A : ℝ) ^ 2 := by
    simp [f, div_eq_mul_inv, pow_two, mul_comm]
  have hlast :
      -∑ i ∈ Finset.Ioc (A - 1) (N - 1), (f (i + 1) - f i) * Ssq ℓ i =
        ∑ i ∈ Finset.Icc A (N - 1), Ssq ℓ i * (f i - f (i + 1)) := by
    rw [hmid, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hfront_eq, sub_eq_add_neg, hlast]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  simp [f]

/-- PDF Lemma 1, third inequality (`A < N`; Abel gives the factor `5`). -/
theorem divisor_tail_bound (N ℓ A : ℕ) (hN : 3 ≤ N) (hℓ : 1 ≤ ℓ)
    (hA : 0 < A) (hAN : A < N) :
    (∑ n ∈ Finset.Icc A N, (tau ℓ n : Real) ^ 2 / (n : Real) ^ 2) ≤
      5 * (2 * Real.log N) ^ (ℓ ^ 2 - 1) / (A : Real) := by
  let L : ℝ := (2 * Real.log N) ^ (ℓ ^ 2 - 1)
  have hL : 0 ≤ L := by positivity
  have hSsq_nonneg : ∀ t, 0 ≤ Ssq ℓ t := fun t =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAbel := abel_tau_sq ℓ A N hA hAN
  have hmid : 0 ≤ Ssq ℓ (A - 1) / (A : ℝ) ^ 2 :=
    div_nonneg (hSsq_nonneg _) (sq_nonneg _)
  have hS : ∀ k, k ≤ N → Ssq ℓ k ≤ (k : ℝ) * L := fun k hk => Ssq_le N ℓ k hN hℓ hk
  have hfront : Ssq ℓ N / (N : ℝ) ^ 2 ≤ L / A := by
    have hSN : Ssq ℓ N ≤ (N : ℝ) * L := hS N le_rfl
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hA (le_of_lt hAN))
    have hle : Ssq ℓ N / (N : ℝ) ^ 2 ≤ L / N := by
      have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hN2 (by positivity : (0 : ℝ) < N)]
      nlinarith [hSN, hNpos, hL]
    exact hle.trans (div_le_div_of_nonneg_left hL (by positivity)
      (Nat.cast_le.mpr (le_of_lt hAN)))
  have hA' : A ≤ N - 1 := Nat.le_pred_of_lt hAN
  have hpt : ∀ k ∈ Finset.Icc A (N - 1),
      Ssq ℓ k * (((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2) ≤ 2 * L / (k : ℝ) ^ 2 := by
    intro k hk
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2.trans (Nat.sub_le N 1)
    have hkpos : 0 < k := lt_of_lt_of_le hA (Finset.mem_Icc.mp hk).1
    have hSk : Ssq ℓ k ≤ (k : ℝ) * L := hS k hkN
    have hdiff := inv_sq_diff_le k hkpos
    have hnn : 0 ≤ ((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2 :=
      sub_nonneg.2 <| pow_le_pow_left₀ (by positivity)
        (inv_anti₀ (by positivity) (by linarith)) 2
    have hmul : Ssq ℓ k * (((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2) ≤
        (k : ℝ) * L * (2 / (k : ℝ) ^ 3) :=
      mul_le_mul hSk hdiff hnn (by positivity)
    have heq : (k : ℝ) * L * (2 / (k : ℝ) ^ 3) = 2 * L / (k : ℝ) ^ 2 := by
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hkpos.ne'
      field_simp [hk0]
      try ring
    exact hmul.trans (le_of_eq heq)
  have hsum := Finset.sum_le_sum hpt
  have hsq := sum_inv_sq_le (A := A) (M := N - 1) hA hA'
  have hsum' :
      ∑ k ∈ Finset.Icc A (N - 1), 2 * L / (k : ℝ) ^ 2 =
        2 * L * ∑ k ∈ Finset.Icc A (N - 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
    simp [div_eq_mul_inv, mul_assoc, Finset.mul_sum]
  have h4 : 2 * L * ∑ k ∈ Finset.Icc A (N - 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * L * (2 / A) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  calc
    ∑ n ∈ Finset.Icc A N, (tau ℓ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        = Ssq ℓ N / (N : ℝ) ^ 2 - Ssq ℓ (A - 1) / (A : ℝ) ^ 2 +
            ∑ k ∈ Finset.Icc A (N - 1),
              Ssq ℓ k * (((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2) := hAbel
    _ ≤ Ssq ℓ N / (N : ℝ) ^ 2 +
          ∑ k ∈ Finset.Icc A (N - 1),
            Ssq ℓ k * (((k : ℝ)⁻¹) ^ 2 - ((k + 1 : ℝ)⁻¹) ^ 2) := by
          linarith [hmid]
    _ ≤ L / A + ∑ k ∈ Finset.Icc A (N - 1), 2 * L / (k : ℝ) ^ 2 :=
          add_le_add hfront hsum
    _ = L / A + 2 * L * ∑ k ∈ Finset.Icc A (N - 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
          rw [hsum']
    _ ≤ L / A + 2 * L * (2 / A) := by linarith [h4]
    _ = 5 * L / A := by ring

/-! ### Pointwise maximal order -/

private theorem succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc
      e + 1 + 1 ≤ 2 ^ e + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ e + 2 ^ e := Nat.add_le_add_left (Nat.one_le_two_pow (n := e)) _
      _ = 2 ^ (e + 1) := by ring

private theorem log_div_self_le_log4_div_four {Λ : ℝ} (hΛ : 4 < Λ) :
    Real.log Λ / Λ ≤ Real.log 4 / 4 := by
  have hexp1_le4 : Real.exp 1 ≤ 4 :=
    le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
  have hΛe : Real.exp 1 ≤ Λ := le_trans hexp1_le4 (le_of_lt hΛ)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hexp1_le4) (Set.mem_Ici.2 hΛe) (le_of_lt hΛ)

private theorem two_log_div_self_le_log_two {Λ : ℝ} (hΛ : 4 < Λ) :
    2 * (Real.log Λ / Λ) ≤ Real.log 2 := by
  have hanti := log_div_self_le_log4_div_four hΛ
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow 2 2]
    simp
  have : 2 * (Real.log 4 / 4) = Real.log 2 := by rw [hlog4]; ring
  have := mul_le_mul_of_nonneg_left hanti (by positivity : (0 : ℝ) ≤ 2)
  linarith

private theorem two_mul_log_lt {Λ : ℝ} (hΛ : 4 < Λ) : 2 * Real.log Λ < Λ := by
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛ
  have hlog2lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have h2 : 2 * (Real.log Λ / Λ) ≤ Real.log 2 := two_log_div_self_le_log_two hΛ
  have hdiv : 2 * Real.log Λ / Λ < 1 := by
    rw [mul_div_assoc]
    exact lt_of_le_of_lt h2 hlog2lt
  exact (div_lt_one hΛpos).1 hdiv

private theorem wigert_z_gt_one {L Λ : ℝ} (hLpos : 0 < L) (hΛ : 4 < Λ)
    (hdef : Λ = Real.log L) : 1 < L / Λ ^ 2 := by
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛ
  have h2lt := two_mul_log_lt hΛ
  have hpow : Λ ^ 2 < L := by
    have hΛ2pos : 0 < Λ ^ 2 := pow_pos hΛpos 2
    have hlogeq : Real.log (Λ ^ 2) = 2 * Real.log Λ := Real.log_pow Λ 2
    exact (Real.log_lt_log_iff hΛ2pos hLpos).1 (by
      rw [hlogeq]
      simpa [hdef] using h2lt)
  exact (one_lt_div (pow_pos hΛpos 2)).2 hpow

private theorem wigert_log_coeff {L Λ : ℝ} (hL : 1 < L) (hΛ : 4 < Λ) (hdef : Λ = Real.log L) :
    let z := L / Λ ^ 2
    z * Real.log (1 + L / Real.log 2) + Real.log 2 / Real.log z * L ≤ 4 * L / Λ := by
  intro z
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛ
  have hLpos : 0 < L := lt_trans (by norm_num) hL
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hz : z = L / Λ ^ 2 := rfl
  have hzpos : 0 < z := by rw [hz]; positivity
  have hlogz_eq : Real.log z = Λ - 2 * Real.log Λ := by
    have hΛ2 : (Λ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [hz, Real.log_div hLpos.ne' hΛ2, Real.log_pow Λ 2, hdef]
    ring
  have h2log := two_log_div_self_le_log_two hΛ
  have hlogz_ge : Λ * (1 - Real.log 2) ≤ Real.log z := by
    have hrewrite : Real.log z = Λ * (1 - 2 * (Real.log Λ / Λ)) := by
      calc
        Real.log z = Λ - 2 * Real.log Λ := hlogz_eq
        _ = Λ * (1 - 2 * (Real.log Λ / Λ)) := by
          field_simp [hΛpos.ne']
          try ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left (by linarith [h2log]) (le_of_lt hΛpos)
  have hden0 : 0 < 1 - Real.log 2 := sub_pos.2 hlog2lt
  have hlogzpos : 0 < Real.log z := by nlinarith [hΛpos, hlogz_ge, hden0]
  have hx : 1 ≤ L / Real.log 2 :=
    (one_le_div hlog2pos).2 (le_trans (le_of_lt hlog2lt) (le_of_lt hL))
  have hdouble : 1 + L / Real.log 2 ≤ 2 * L / Real.log 2 := by
    calc
      1 + L / Real.log 2 ≤ 2 * (L / Real.log 2) := by linarith [hx]
      _ = 2 * L / Real.log 2 := by ring
  have hlog_eq : Real.log (2 * L / Real.log 2) = Real.log 2 + Λ - Real.log (Real.log 2) := by
    rw [Real.log_div (by positivity) hlog2pos.ne', Real.log_mul (by positivity) hLpos.ne', hdef] <;>
      ring
  have hloglog2 : -Real.log (Real.log 2) ≤ Real.log 2 := by
    have hhalf : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlog_half : Real.log (1 / 2) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by positivity) (le_of_lt hhalf)
    have hlog_half_eq : Real.log (1 / 2) = -Real.log 2 := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_one, zero_sub]
    linarith [hlog_half, hlog_half_eq]
  have hlog_small : Real.log (1 + L / Real.log 2) ≤ Λ + 2 := by
    have hpos : 0 < 1 + L / Real.log 2 := by positivity
    have hle := Real.log_le_log hpos hdouble
    have hbound : Real.log (1 + L / Real.log 2) ≤
        Real.log 2 + Λ - Real.log (Real.log 2) :=
      hle.trans (le_of_eq hlog_eq)
    have hpair : Real.log 2 - Real.log (Real.log 2) ≤ 2 := by
      linarith [hloglog2, Real.log_two_lt_d9]
    linarith [hbound, hpair]
  have hfirst : z * Real.log (1 + L / Real.log 2) ≤ (3 / 2) * L / Λ := by
    have hfrac : (Λ + 2) / Λ ^ 2 ≤ (3 / 2) / Λ := by
      rw [div_le_div_iff₀ (pow_pos hΛpos 2) hΛpos]
      nlinarith [hΛ]
    have hmul : z * Real.log (1 + L / Real.log 2) ≤ (L / Λ ^ 2) * (Λ + 2) := by
      rw [hz]
      exact mul_le_mul_of_nonneg_left hlog_small
        (div_nonneg (le_of_lt hLpos) (sq_nonneg _))
    have heq : (L / Λ ^ 2) * (Λ + 2) = L * (Λ + 2) / Λ ^ 2 := by ring
    calc
      z * Real.log (1 + L / Real.log 2) ≤ (L / Λ ^ 2) * (Λ + 2) := hmul
      _ = L * (Λ + 2) / Λ ^ 2 := heq
      _ = L * ((Λ + 2) / Λ ^ 2) := by ring
      _ ≤ L * ((3 / 2) / Λ) := mul_le_mul_of_nonneg_left hfrac (le_of_lt hLpos)
      _ = (3 / 2) * L / Λ := by ring
  have hsecond :
      Real.log 2 / Real.log z * L ≤ (Real.log 2 / (1 - Real.log 2)) * L / Λ := by
    have hle_div : Real.log 2 / Real.log z ≤ Real.log 2 / (Λ * (1 - Real.log 2)) :=
      div_le_div_of_nonneg_left (le_of_lt hlog2pos)
        (mul_pos hΛpos hden0) hlogz_ge
    have hrewrite :
        Real.log 2 / (Λ * (1 - Real.log 2)) =
          (Real.log 2 / (1 - Real.log 2)) / Λ := by
      field_simp [hΛpos.ne', hden0.ne']
    have hmul' :
        Real.log 2 / Real.log z * L ≤
          (Real.log 2 / (1 - Real.log 2)) / Λ * L :=
      mul_le_mul_of_nonneg_right (hle_div.trans (le_of_eq hrewrite)) (le_of_lt hLpos)
    have heq : (Real.log 2 / (1 - Real.log 2)) / Λ * L =
        (Real.log 2 / (1 - Real.log 2)) * L / Λ := by ring
    rwa [heq] at hmul'
  have hcoeff : (3 : ℝ) / 2 + Real.log 2 / (1 - Real.log 2) ≤ 4 := by
    have hnum : Real.log 2 ≤ (7 : ℝ) / 10 := le_of_lt <|
      lt_trans Real.log_two_lt_d9 (by norm_num)
    have hden_gt : (3 : ℝ) / 10 ≤ 1 - Real.log 2 := by linarith [Real.log_two_lt_d9]
    have h1 : Real.log 2 / (1 - Real.log 2) ≤ (7 / 10) / (1 - Real.log 2) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden0)
    have h2 : (7 / 10 : ℝ) / (1 - Real.log 2) ≤ (7 / 10) / (3 / 10) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden_gt
    have hval : (7 / 10 : ℝ) / (3 / 10) = 7 / 3 := by norm_num
    have hsum : (3 : ℝ) / 2 + 7 / 3 ≤ 4 := by norm_num
    linarith
  have hcomb := add_le_add hfirst hsecond
  have hrewrite :
      (3 / 2 : ℝ) * L / Λ + (Real.log 2 / (1 - Real.log 2)) * L / Λ =
        ((3 : ℝ) / 2 + Real.log 2 / (1 - Real.log 2)) * L / Λ := by ring
  have hfinal :
      ((3 : ℝ) / 2 + Real.log 2 / (1 - Real.log 2)) * L / Λ ≤ 4 * L / Λ := by
    have : 0 ≤ L / Λ := div_nonneg (le_of_lt hLpos) (le_of_lt hΛpos)
    have hmul' := mul_le_mul_of_nonneg_right hcoeff this
    have heq1 :
        ((3 : ℝ) / 2 + Real.log 2 / (1 - Real.log 2)) * L / Λ =
          ((3 : ℝ) / 2 + Real.log 2 / (1 - Real.log 2)) * (L / Λ) := by ring
    have heq2 : (4 : ℝ) * L / Λ = 4 * (L / Λ) := by ring
    rwa [heq1, heq2]
  linarith [hcomb, hrewrite, hfinal]

private theorem card_divisors_le_exp_of_loglog_le {N n : ℕ}
    (hN : 3 ≤ N) (hle : n ≤ N) (hΛ : Real.log (Real.log N) ≤ 4) :
    (n.divisors.card : ℝ) ≤ Real.exp (4 * Real.log N / Real.log (Real.log N)) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN : (1 : ℝ) < Real.log N := logN_gt_one hN
  have hloglog : 0 < Real.log (Real.log N) := Real.log_pos hlogN
  have hd : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hnN : (n : ℝ) ≤ N := Nat.cast_le.mpr hle
  have hNexp : (N : ℝ) ≤ Real.exp (4 * Real.log N / Real.log (Real.log N)) := by
    rw [← Real.log_le_iff_le_exp hNpos, le_div_iff₀ hloglog]
    nlinarith [hlogN, hΛ]
  exact hd.trans (hnN.trans hNexp)

private theorem card_divisors_wigert {N n : ℕ} (hN : 3 ≤ N) (hn : 1 ≤ n) (hle : n ≤ N)
    (hΛ : 4 < Real.log (Real.log N)) :
    (n.divisors.card : ℝ) ≤ Real.exp (4 * Real.log N / Real.log (Real.log N)) := by
  have hn0 : n ≠ 0 := (Nat.succ_le_iff.mp hn).ne'
  have hlogN : (1 : ℝ) < Real.log N := logN_gt_one hN
  let L : ℝ := Real.log N
  let Λ : ℝ := Real.log L
  let z : ℝ := L / Λ ^ 2
  have hΛ' : 4 < Λ := hΛ
  have hΛpos : 0 < Λ := lt_trans (by norm_num) hΛ'
  have hLpos : 0 < L := lt_trans (by norm_num) hlogN
  have hzpos : 0 < z := by positivity
  have hz1 : 1 < z := wigert_z_gt_one hLpos hΛ' rfl
  have hcard : (n.divisors.card : ℝ) =
      ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors hn0
  let P : ℕ → Prop := fun p => (p : ℝ) ≤ z
  let small : Finset ℕ := n.primeFactors.filter P
  let large : Finset ℕ := n.primeFactors.filter fun p : ℕ => ¬ P p
  have hsplit :
      ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) =
        (∏ p ∈ small, ((n.factorization p + 1 : ℕ) : ℝ)) *
          ∏ p ∈ large, ((n.factorization p + 1 : ℕ) : ℝ) := by
    simpa [small, large, P] using
      (Finset.prod_filter_mul_prod_filter_not n.primeFactors
        P (fun p => ((n.factorization p + 1 : ℕ) : ℝ))).symm
  have hsmall_card : (small.card : ℝ) ≤ z := by
    have hz0 : 0 ≤ z := le_of_lt hzpos
    have hsub : small ⊆ Finset.Icc 1 (Nat.floor z) := by
      intro p hp
      have hpz : (p : ℝ) ≤ z := (Finset.mem_filter.1 hp).2
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_le
      exact Finset.mem_Icc.mpr ⟨hp1, (Nat.le_floor_iff hz0).2 hpz⟩
    have hcard_le := Finset.card_le_card hsub
    have hIcc : (Finset.Icc 1 (Nat.floor z)).card = Nat.floor z := by
      simp [Nat.card_Icc]
    have : ((Finset.Icc 1 (Nat.floor z)).card : ℝ) ≤ z := by
      simpa [hIcc] using Nat.floor_le hz0
    exact le_trans (Nat.cast_le.mpr hcard_le) this
  have hsmall :
      ∏ p ∈ small, ((n.factorization p + 1 : ℕ) : ℝ) ≤
        (1 + L / Real.log 2) ^ small.card := by
    have hpt : ∀ p ∈ small, ((n.factorization p + 1 : ℕ) : ℝ) ≤ 1 + L / Real.log 2 := by
      intro p hp
      have hpPr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
      have hpe : (p : ℝ) ^ n.factorization p ≤ n := by
        exact_mod_cast Nat.ordProj_le p hn0
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast hpPr.one_lt
      have hlogp : 0 < Real.log p := Real.log_pos hp1
      have hlog_pow : (n.factorization p : ℝ) * Real.log p ≤ Real.log n := by
        have := Real.log_le_log (pow_pos (lt_trans zero_lt_one hp1) _) hpe
        simpa [Real.log_pow (p : ℝ) (n.factorization p)] using this
      have he_le : (n.factorization p : ℝ) ≤ Real.log n / Real.log p :=
        (le_div_iff₀ hlogp).2 hlog_pow
      have hlogp2 : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by positivity : (0 : ℝ) < 2) (by exact_mod_cast hpPr.two_le)
      have hden : Real.log n / Real.log p ≤ Real.log n / Real.log 2 :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hn))
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlogp2
      have hnL : Real.log n ≤ L :=
        Real.log_le_log (by exact_mod_cast (Nat.succ_le_iff.mp hn)) (Nat.cast_le.mpr hle)
      have : (n.factorization p : ℝ) + 1 ≤ 1 + L / Real.log 2 := by
        have hL2 : Real.log n / Real.log 2 ≤ L / Real.log 2 :=
          div_le_div_of_nonneg_right hnL (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        linarith [he_le, hden, hL2]
      simpa [Nat.cast_add_one] using this
    have hprod := Finset.prod_le_prod (fun _ _ => by positivity) hpt
    simpa [Finset.prod_const] using hprod
  have hsmall' :
      ∏ p ∈ small, ((n.factorization p + 1 : ℕ) : ℝ) ≤
        Real.exp (z * Real.log (1 + L / Real.log 2)) := by
    have hbase : (1 : ℝ) ≤ 1 + L / Real.log 2 :=
      le_add_of_nonneg_right (div_nonneg (le_of_lt hLpos)
        (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
    have hpow : (1 + L / Real.log 2) ^ small.card ≤ (1 + L / Real.log 2) ^ z := by
      simpa [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hsmall_card
    have hrpow : (1 + L / Real.log 2) ^ z =
        Real.exp (z * Real.log (1 + L / Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      rw [mul_comm]
    exact hsmall.trans (hpow.trans (le_of_eq hrpow))
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlarge :
      ∏ p ∈ large, ((n.factorization p + 1 : ℕ) : ℝ) ≤
        Real.exp (Real.log 2 * L / Real.log z) := by
    have hpt : ∀ p ∈ large, ((n.factorization p + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ n.factorization p := fun p hp => by
      exact_mod_cast succ_le_two_pow (n.factorization p)
    have hprod := Finset.prod_le_prod (fun _ _ => by positivity) hpt
    have hpowsum :
        ∏ p ∈ large, (2 : ℝ) ^ n.factorization p =
          (2 : ℝ) ^ ∑ p ∈ large, n.factorization p :=
      Finset.prod_pow_eq_pow_sum _ _ _
    have hsum_e : (∑ p ∈ large, n.factorization p : ℝ) ≤ L / Real.log z := by
      by_cases hempty : large = ∅
      · simp [hempty]
        exact div_nonneg (le_of_lt hLpos) (le_of_lt hlogz)
      · have hsum_log :
            Real.log z * ∑ p ∈ large, (n.factorization p : ℝ) ≤
              ∑ p ∈ large, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun p hp => ?_
          have hpz : ¬ ((p : ℝ) ≤ z) := (Finset.mem_filter.1 hp).2
          have hlogp : Real.log z ≤ Real.log (p : ℝ) :=
            Real.log_le_log hzpos (le_of_lt (lt_of_not_ge hpz))
          rw [mul_comm (Real.log z)]
          exact mul_le_mul_of_nonneg_left hlogp (Nat.cast_nonneg _)
        have hdvd : (∏ p ∈ large, p ^ n.factorization p) ∣ n := by
          have hfull : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
            simpa [Finsupp.prod, Nat.support_factorization] using
              Nat.prod_factorization_pow_eq_self hn0
          have hsub : large ⊆ n.primeFactors := Finset.filter_subset _ _
          exact (Finset.prod_dvd_prod_of_subset large n.primeFactors
            (fun p => p ^ n.factorization p) hsub).trans (dvd_of_eq hfull)
        have hprod_le : (∏ p ∈ large, (p : ℝ) ^ n.factorization p) ≤ n := by
          exact_mod_cast Nat.le_of_dvd (Nat.succ_le_iff.mp hn) hdvd
        have hlog_prod :
            ∑ p ∈ large, (n.factorization p : ℝ) * Real.log p =
              Real.log (∏ p ∈ large, (p : ℝ) ^ n.factorization p) := by
          trans ∑ p ∈ large, Real.log ((p : ℝ) ^ n.factorization p)
          · refine Finset.sum_congr rfl fun p hp => ?_
            have hp0 : (0 : ℝ) < p :=
              Nat.cast_pos.2 (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos
            exact (Real.log_pow (p : ℝ) (n.factorization p)).symm
          · exact (Real.log_prod (s := large)
              (f := fun p => (p : ℝ) ^ n.factorization p)
              (fun p hp =>
                (pow_pos (Nat.cast_pos.2
                  (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos) _).ne')).symm
        have hlogn : Real.log (∏ p ∈ large, (p : ℝ) ^ n.factorization p) ≤ Real.log n :=
          Real.log_le_log (Finset.prod_pos fun p hp =>
            pow_pos (by exact_mod_cast
              (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos) _) hprod_le
        have : Real.log z * ∑ p ∈ large, (n.factorization p : ℝ) ≤ L := by
          have : Real.log n ≤ L :=
            Real.log_le_log (by exact_mod_cast (Nat.succ_le_iff.mp hn)) (Nat.cast_le.mpr hle)
          linarith [hsum_log, hlog_prod, hlogn]
        exact (le_div_iff₀ hlogz).2 (by rw [mul_comm]; exact this)
    have hexp : (2 : ℝ) ^ ∑ p ∈ large, n.factorization p ≤
        Real.exp (Real.log 2 * (L / Real.log z)) := by
      have heq : (2 : ℝ) ^ ∑ p ∈ large, n.factorization p =
          Real.exp (Real.log 2 * ((∑ p ∈ large, n.factorization p : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      have hcast :
          ((∑ p ∈ large, n.factorization p : ℕ) : ℝ) =
            ∑ p ∈ large, (n.factorization p : ℝ) :=
        Nat.cast_sum (R := ℝ) large fun p => n.factorization p
      have hle' :
          Real.log 2 * ((∑ p ∈ large, n.factorization p : ℕ) : ℝ) ≤
            Real.log 2 * (L / Real.log z) := by
        rw [hcast]
        exact mul_le_mul_of_nonneg_left hsum_e
          (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
      exact (le_of_eq heq).trans (Real.exp_le_exp.2 hle')
    have hassoc : Real.exp (Real.log 2 * (L / Real.log z)) =
        Real.exp (Real.log 2 * L / Real.log z) := by ring_nf
    exact hprod.trans ((le_of_eq hpowsum).trans (hexp.trans (le_of_eq hassoc)))
  have hbound := mul_le_mul hsmall' hlarge (by positivity) (by positivity)
  have hcoeff := wigert_log_coeff (L := L) (Λ := Λ) hlogN hΛ' rfl
  have hexp_mul :
      Real.exp (z * Real.log (1 + L / Real.log 2)) *
          Real.exp (Real.log 2 * L / Real.log z) =
        Real.exp (z * Real.log (1 + L / Real.log 2) + Real.log 2 / Real.log z * L) := by
    rw [← Real.exp_add]
    ring_nf
  have : (n.divisors.card : ℝ) ≤
      Real.exp (z * Real.log (1 + L / Real.log 2) + Real.log 2 / Real.log z * L) := by
    rw [hcard, hsplit, ← hexp_mul]
    exact hbound
  exact this.trans (Real.exp_le_exp.2 hcoeff)

/-- PDF Lemma 1, pointwise maximal-order bound (Norton / Wigert form). -/
theorem divisor_pointwise_exp_bound :
    ∃ Cτ : ℝ, 0 < Cτ ∧ Cτ ≤ 4 ∧
      ∀ (ℓ N n : ℕ), 3 ≤ N → 1 ≤ ℓ → 1 ≤ n → n ≤ N →
        (tau ℓ n : ℝ) ≤
          Real.exp (Cτ * (ℓ : ℝ) * Real.log N / Real.log (Real.log N)) := by
  refine ⟨4, by norm_num, le_rfl, ?_⟩
  intro ℓ N n hN hℓ hn hle
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  have hτ : (tau ℓ n : ℝ) ≤ (n.divisors.card : ℝ) ^ (ℓ - 1) := by
    exact_mod_cast tau_le_divisors_pow ℓ n hnpos hℓ
  have hlogN : (1 : ℝ) < Real.log N := logN_gt_one hN
  have hloglog : 0 < Real.log (Real.log N) := Real.log_pos hlogN
  have hgoal_of_d :
      (n.divisors.card : ℝ) ≤ Real.exp (4 * Real.log N / Real.log (Real.log N)) →
      (tau ℓ n : ℝ) ≤
        Real.exp (4 * (ℓ : ℝ) * Real.log N / Real.log (Real.log N)) := by
    intro hd
    have hpow := pow_le_pow_left₀ (by positivity) hd (ℓ - 1)
    have hexp :
        Real.exp (4 * Real.log N / Real.log (Real.log N)) ^ (ℓ - 1) =
          Real.exp (4 * Real.log N / Real.log (Real.log N) * (ℓ - 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_comm, Nat.cast_sub hℓ, Nat.cast_one]
    have hcoeff :
        4 * Real.log N / Real.log (Real.log N) * (ℓ - 1 : ℝ) ≤
          4 * (ℓ : ℝ) * Real.log N / Real.log (Real.log N) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hloglog)
      have hle' : (ℓ - 1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast Nat.sub_le ℓ 1
      nlinarith [hle', le_of_lt hlogN]
    exact hτ.trans (hpow.trans ((le_of_eq hexp).trans (Real.exp_le_exp.2 hcoeff)))
  by_cases hΛ : Real.log (Real.log N) ≤ 4
  · exact hgoal_of_d (card_divisors_le_exp_of_loglog_le hN hle hΛ)
  · exact hgoal_of_d (card_divisors_wigert hN hn hle (lt_of_not_ge hΛ))

end RMFLean
