/-
PDF Corollary mixed-moment half:
`|𝔼[S_N^{s₁} conj(S_N)^{s₂}]| → 0` for `s₁ ≠ s₂`, by counting unbalanced
product equations and Lemma 1 (Cauchy–Schwarz / AM–GM + divisor squares).
-/
import RMFLean.Trusted.DivisorSums
import RMFLean.Trusted.Corollary
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex Filter Topology Real Asymptotics

namespace RMFLean

set_option maxHeartbeats 400000

/-! ### Cardinality of unbalanced solutions -/

def UnbalSol.swap {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) : UnbalSol s2 s1 N where
  n := x.m
  m := x.n
  hn := x.hm
  hm := x.hn
  hprod := x.hprod.symm

@[simp] theorem UnbalSol.swap_swap {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) :
    x.swap.swap = x := rfl

def unbalSwapEquiv (s1 s2 N : ℕ) : UnbalSol s1 s2 N ≃ UnbalSol s2 s1 N where
  toFun := UnbalSol.swap
  invFun := UnbalSol.swap
  left_inv := UnbalSol.swap_swap
  right_inv := UnbalSol.swap_swap

theorem card_unbalSol_swap (s1 s2 N : ℕ) :
    Fintype.card (UnbalSol s1 s2 N) = Fintype.card (UnbalSol s2 s1 N) :=
  Fintype.card_congr (unbalSwapEquiv s1 s2 N)

theorem unbal_prod_m_le_pow {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) :
    ∏ j, x.m j ≤ N ^ s2 := by
  have hle : ∀ j, x.m j ≤ N := fun j => (x.hm j).2
  calc
    ∏ j, x.m j ≤ ∏ _j : Fin s2, N :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun j _ => hle j
    _ = N ^ s2 := by simp [Finset.prod_const, Fintype.card_fin]

theorem unbal_prod_m_pos {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) :
    1 ≤ ∏ j, x.m j := by
  refine Finset.one_le_prod' fun j _ => (x.hm j).1

/-- Pack an unbalanced solution by the `m`-product (used when `s₂ ≤ s₁`). -/
def UnbalSol.toPackedM {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) :
    Σ p : Finset.Icc (1 : ℕ) (N ^ s2),
      OrderedFactors s1 (p : ℕ) × OrderedFactors s2 (p : ℕ) :=
  ⟨⟨∏ j, x.m j, Finset.mem_Icc.2 ⟨unbal_prod_m_pos x, unbal_prod_m_le_pow x⟩⟩,
    ⟨⟨x.n, ⟨fun i => lt_of_lt_of_le Nat.zero_lt_one (x.hn i).1, x.hprod⟩⟩,
      ⟨x.m, ⟨fun j => lt_of_lt_of_le Nat.zero_lt_one (x.hm j).1, rfl⟩⟩⟩⟩

theorem UnbalSol.toPackedM_injective (s1 s2 N : ℕ) :
    Function.Injective (@UnbalSol.toPackedM s1 s2 N) := by
  intro x y h
  have hp : (∏ j, x.m j) = ∏ j, y.m j := by
    simpa [UnbalSol.toPackedM] using congrArg (fun z => (z.1 : ℕ)) h
  have hn : x.n = y.n := by
    have h2 := congrArg (fun z => z.2.1.val) h
    simpa [UnbalSol.toPackedM] using h2
  have hm : x.m = y.m := by
    have h2 := congrArg (fun z => z.2.2.val) h
    simpa [UnbalSol.toPackedM] using h2
  cases x; cases y
  simp only at hn hm
  subst hn; subst hm
  rfl

theorem card_unbalSol_le_tau_sum_s2 (s1 s2 N : ℕ) :
    Fintype.card (UnbalSol s1 s2 N) ≤
      ∑ n ∈ Finset.Icc 1 (N ^ s2), tau s1 n * tau s2 n := by
  have hinj := UnbalSol.toPackedM_injective s1 s2 N
  have hcard := Fintype.card_le_of_injective _ hinj
  have hσ :
      Fintype.card
          (Σ p : Finset.Icc (1 : ℕ) (N ^ s2),
            OrderedFactors s1 (p : ℕ) × OrderedFactors s2 (p : ℕ)) =
        ∑ n ∈ Finset.Icc 1 (N ^ s2), tau s1 n * tau s2 n := by
    rw [Fintype.card_sigma]
    have hpt : ∀ i : Finset.Icc (1 : ℕ) (N ^ s2),
        Fintype.card (OrderedFactors s1 (i : ℕ) × OrderedFactors s2 (i : ℕ)) =
          tau s1 (i : ℕ) * tau s2 (i : ℕ) := by
      intro i
      rw [Fintype.card_prod]
      rfl
    simp_rw [hpt]
    exact (Finset.sum_subtype (Finset.Icc 1 (N ^ s2)) (fun _ => Iff.rfl)
        (fun n => tau s1 n * tau s2 n)).symm
  exact hcard.trans (le_of_eq hσ)

theorem card_unbalSol_le_tau_sum (s1 s2 N : ℕ) :
    Fintype.card (UnbalSol s1 s2 N) ≤
      ∑ n ∈ Finset.Icc 1 (N ^ min s1 s2), tau s1 n * tau s2 n := by
  rcases le_total s2 s1 with h | h
  · have hmin : min s1 s2 = s2 := min_eq_right h
    simpa [hmin] using card_unbalSol_le_tau_sum_s2 s1 s2 N
  · have hmin : min s1 s2 = s1 := min_eq_left h
    have hswap := card_unbalSol_swap s1 s2 N
    have hbound := card_unbalSol_le_tau_sum_s2 s2 s1 N
    have hsum :
        ∑ n ∈ Finset.Icc 1 (N ^ s1), tau s2 n * tau s1 n =
          ∑ n ∈ Finset.Icc 1 (N ^ s1), tau s1 n * tau s2 n :=
      Finset.sum_congr rfl fun n _ => mul_comm _ _
    rw [hmin, hswap]
    exact hbound.trans (le_of_eq hsum)

/-! ### Phase modulus -/

theorem norm_mixedWeight {d s1 s2 N : ℕ} (g : CirclePoly d)
    (x : UnbalSol s1 s2 N) : ‖mixedWeight g x‖ = 1 := by
  simp only [mixedWeight]
  rw [norm_mul, norm_prod, norm_prod]
  have h1 : (∏ i, ‖g.ePhase (x.n i)‖) = 1 :=
    Finset.prod_eq_one fun i _ => norm_ePhase g _
  have h2 : (∏ j, ‖starRingEnd ℂ (g.ePhase (x.m j))‖) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    change ‖star (g.ePhase (x.m j))‖ = 1
    rw [norm_star, norm_ePhase]
  rw [h1, h2, mul_one]

theorem norm_mixedU_le_card {d s1 s2 N : ℕ} (g : CirclePoly d) :
    ‖mixedU d s1 s2 N g‖ ≤ Fintype.card (UnbalSol s1 s2 N) := by
  simp only [mixedU]
  calc
    ‖∑ x : UnbalSol s1 s2 N, mixedWeight g x‖
        ≤ ∑ x : UnbalSol s1 s2 N, ‖mixedWeight g x‖ := by
          simpa using
            (norm_sum_le (Finset.univ : Finset (UnbalSol s1 s2 N))
              (mixedWeight g) : _)
    _ = ∑ x : UnbalSol s1 s2 N, (1 : ℝ) :=
          Fintype.sum_congr _ _ fun x => norm_mixedWeight g x
    _ = Fintype.card (UnbalSol s1 s2 N) := by simp

theorem norm_mixedM_le {d s1 s2 N : ℕ} (g : CirclePoly d) (hN : 1 ≤ N) :
    ‖mixedM d s1 s2 N g‖ ≤
      Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) *
        Fintype.card (UnbalSol s1 s2 N) := by
  simp only [mixedM]
  have hr : 0 ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) := Real.rpow_nonneg (by positivity) _
  calc
    ‖(Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2))) • mixedU d s1 s2 N g‖
        = ‖Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2))‖ *
            ‖mixedU d s1 s2 N g‖ := by
          rw [norm_smul]
    _ = Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) * ‖mixedU d s1 s2 N g‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) *
          Fintype.card (UnbalSol s1 s2 N) := by
          exact mul_le_mul_of_nonneg_left (norm_mixedU_le_card g) hr

/-! ### Lemma 1 bound on `∑ τ_{s₁} τ_{s₂}` -/

theorem two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem tau_prod_sum_le_sq {s1 s2 M : ℕ} (hs1 : 1 ≤ s1) (hs2 : 1 ≤ s2)
    (hM : 3 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, (tau s1 n : ℝ) * (tau s2 n : ℝ)) ≤
      (M : ℝ) * (2 * Real.log M) ^ (s1 ^ 2 - 1) +
        (M : ℝ) * (2 * Real.log M) ^ (s2 ^ 2 - 1) := by
  have hpoint : ∀ n ∈ Finset.Icc 1 M,
      (tau s1 n : ℝ) * (tau s2 n : ℝ) ≤
        (tau s1 n : ℝ) ^ 2 + (tau s2 n : ℝ) ^ 2 := by
    intro n _
    have h := two_mul_le_add_sq (tau s1 n : ℝ) (tau s2 n : ℝ)
    nlinarith [sq_nonneg (tau s1 n : ℝ), sq_nonneg (tau s2 n : ℝ)]
  have hsq1 := divisor_sum_sq_bound M s1 hM hs1
  have hsq2 := divisor_sum_sq_bound M s2 hM hs2
  calc
    ∑ n ∈ Finset.Icc 1 M, (tau s1 n : ℝ) * (tau s2 n : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 M,
            ((tau s1 n : ℝ) ^ 2 + (tau s2 n : ℝ) ^ 2) :=
          Finset.sum_le_sum hpoint
    _ = ∑ n ∈ Finset.Icc 1 M, (tau s1 n : ℝ) ^ 2 +
          ∑ n ∈ Finset.Icc 1 M, (tau s2 n : ℝ) ^ 2 :=
          Finset.sum_add_distrib
    _ ≤ (M : ℝ) * (2 * Real.log M) ^ (s1 ^ 2 - 1) +
          (M : ℝ) * (2 * Real.log M) ^ (s2 ^ 2 - 1) :=
          add_le_add hsq1 hsq2

theorem tau_one (k : ℕ) : tau k 1 = 1 := by
  refine Fintype.card_eq_one_iff.2 ?_
  refine ⟨⟨fun _ => 1, ⟨fun _ => Nat.zero_lt_one, by simp⟩⟩, ?_⟩
  intro f
  refine Subtype.ext ?_
  funext i
  have hdvd : f.val i ∣ 1 := by
    have hprod := f.property.2
    have := Finset.dvd_prod_of_mem (fun j => f.val j) (Finset.mem_univ i)
    rwa [hprod] at this
  exact Nat.eq_one_of_dvd_one hdvd

theorem min_lt_max_of_ne {a b : ℕ} (h : a ≠ b) : min a b < max a b := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact hlt
  · rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact hlt

theorem mixed_exponent_pos {s1 s2 : ℕ} (hne : s1 ≠ s2) :
    0 < (s1 + s2 : ℝ) / 2 - (min s1 s2 : ℝ) := by
  have hlt := min_lt_max_of_ne hne
  have hnat : min s1 s2 + min s1 s2 < s1 + s2 := by
    have : min s1 s2 + min s1 s2 < min s1 s2 + max s1 s2 :=
      Nat.add_lt_add_left hlt _
    rwa [min_add_max] at this
  have hR : (min s1 s2 : ℝ) + (min s1 s2 : ℝ) < (s1 : ℝ) + s2 := by
    exact_mod_cast hnat
  linarith

theorem N_le_pow_min {s1 s2 N : ℕ} (hN : 3 ≤ N) (hmin : 1 ≤ min s1 s2) :
    N ≤ N ^ min s1 s2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN
  have : N ^ 1 ≤ N ^ min s1 s2 := Nat.pow_le_pow_right hNpos hmin
  simpa using this

theorem card_unbal_le_one_of_min_zero (s1 s2 N : ℕ) (hmin : min s1 s2 = 0) :
    Fintype.card (UnbalSol s1 s2 N) ≤ 1 := by
  have h := card_unbalSol_le_tau_sum s1 s2 N
  have hpow : N ^ min s1 s2 = 1 := by rw [hmin, pow_zero]
  have hIcc : Finset.Icc 1 (N ^ min s1 s2) = {1} := by
    rw [hpow]; simp
  have hsum :
      ∑ n ∈ Finset.Icc 1 (N ^ min s1 s2), tau s1 n * tau s2 n = 1 := by
    simp [hIcc, tau_one]
  exact h.trans (le_of_eq hsum)

theorem card_unbal_real_le_of_min_pos (s1 s2 N : ℕ) (hN : 3 ≤ N)
    (hmin : 1 ≤ min s1 s2) :
    (Fintype.card (UnbalSol s1 s2 N) : ℝ) ≤
      (↑(N ^ min s1 s2) : ℝ) * (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s1 ^ 2 - 1) +
        (↑(N ^ min s1 s2) : ℝ) * (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s2 ^ 2 - 1) := by
  have hs1 : 1 ≤ s1 := le_trans hmin (min_le_left _ _)
  have hs2 : 1 ≤ s2 := le_trans hmin (min_le_right _ _)
  have hM : 3 ≤ N ^ min s1 s2 := le_trans hN (N_le_pow_min hN hmin)
  have hcard := card_unbalSol_le_tau_sum s1 s2 N
  have hcardR : (Fintype.card (UnbalSol s1 s2 N) : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 (N ^ min s1 s2), (tau s1 n : ℝ) * (tau s2 n : ℝ) :=
    by exact_mod_cast hcard
  exact hcardR.trans (tau_prod_sum_le_sq hs1 hs2 hM)

theorem mixedM_le_of_min_zero {d s1 s2 N : ℕ} (g : CirclePoly d)
    (hN : 3 ≤ N) (hmin : min s1 s2 = 0) :
    ‖mixedM d s1 s2 N g‖ ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) := by
  have hN1 : 1 ≤ N := le_trans (by decide : 1 ≤ 3) hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hcard1 : (Fintype.card (UnbalSol s1 s2 N) : ℝ) ≤ 1 := by
    exact_mod_cast card_unbal_le_one_of_min_zero s1 s2 N hmin
  have hr0 : 0 ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) :=
    Real.rpow_nonneg (le_of_lt hNpos) (-((s1 + s2 : ℝ) / 2))
  calc
    ‖mixedM d s1 s2 N g‖
        ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) *
            Fintype.card (UnbalSol s1 s2 N) :=
          norm_mixedM_le g hN1
    _ ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) * 1 :=
          mul_le_mul_of_nonneg_left hcard1 hr0
    _ = Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) := mul_one _

theorem tendsto_log_pow_mul_rpow_neg (C : ℝ) (p : ℕ) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun N : ℕ =>
        C * (Real.log (N : ℝ)) ^ p * Real.rpow (N : ℝ) (-β)) atTop (nhds 0) := by
  have hlo :
      (fun x : ℝ => Real.log x ^ (p : ℝ)) =o[atTop] fun x => x ^ β :=
    isLittleO_log_rpow_rpow_atTop (p : ℝ) hβ
  have htend :
      Tendsto (fun x : ℝ => C * Real.log x ^ (p : ℝ) / x ^ β) atTop (nhds 0) :=
    (hlo.const_mul_left C).tendsto_div_nhds_zero
  have hcomp : Tendsto (fun N : ℕ =>
      C * Real.log (N : ℝ) ^ (p : ℝ) / (N : ℝ) ^ β) atTop (nhds 0) :=
    htend.comp tendsto_natCast_atTop_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hN)
  have hpow : (Real.log (N : ℝ)) ^ p = Real.log (N : ℝ) ^ (p : ℝ) :=
    (Real.rpow_natCast (Real.log (N : ℝ)) p).symm
  have hneg : Real.rpow (N : ℝ) (-β) = ((N : ℝ) ^ β)⁻¹ :=
    Real.rpow_neg (le_of_lt hNpos) β
  calc
    C * Real.log (N : ℝ) ^ (p : ℝ) / (N : ℝ) ^ β
        = C * Real.log (N : ℝ) ^ (p : ℝ) * ((N : ℝ) ^ β)⁻¹ := by
          rw [div_eq_mul_inv]
    _ = C * (Real.log (N : ℝ)) ^ p * Real.rpow (N : ℝ) (-β) := by
          rw [← hpow, ← hneg]

theorem tendsto_rpow_neg_nat (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun N : ℕ => Real.rpow (N : ℝ) (-β)) atTop (nhds 0) := by
  have h := tendsto_log_pow_mul_rpow_neg (1 : ℝ) 0 β hβ
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N _hN
  simp [pow_zero]

theorem rpow_mul_npow {N : ℕ} (hN : (0 : ℝ) < N) (a : ℝ) (k : ℕ) :
    Real.rpow (N : ℝ) a * (N : ℝ) ^ k = Real.rpow (N : ℝ) (a + k) := by
  have h1 : (N : ℝ) ^ k = (N : ℝ) ^ (k : ℝ) := (Real.rpow_natCast (N : ℝ) k).symm
  rw [h1]
  change (N : ℝ) ^ a * (N : ℝ) ^ (k : ℝ) = (N : ℝ) ^ (a + (k : ℝ))
  exact (Real.rpow_add hN a (k : ℝ)).symm

theorem one_le_s1_add_s2_of_min_zero {s1 s2 : ℕ} (hne : s1 ≠ s2)
    (hmin : min s1 s2 = 0) : 1 ≤ s1 + s2 := by
  have hlt := min_lt_max_of_ne hne
  have hpos : 0 < s1 + s2 := by
    have : min s1 s2 + min s1 s2 < s1 + s2 := by
      have h := Nat.add_lt_add_left hlt (min s1 s2)
      rwa [min_add_max] at h
    simpa [hmin] using this
  exact Nat.succ_le_of_lt hpos

theorem mixedMomentsVanish_any (d : ℕ) (g : CirclePoly d) :
    MixedMomentsVanish d g := by
  intro s1 s2 hne
  by_cases hmin : min s1 s2 = 0
  · have hsum := one_le_s1_add_s2_of_min_zero hne hmin
    have hβ : 0 < (s1 + s2 : ℝ) / 2 := by
      have : (0 : ℝ) < (s1 + s2 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hsum)
      exact div_pos this (by norm_num)
    have htend := tendsto_rpow_neg_nat ((s1 + s2 : ℝ) / 2) hβ
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ htend
    filter_upwards [eventually_ge_atTop 3] with N hN
    exact mixedM_le_of_min_zero g hN hmin
  · have hminpos : 1 ≤ min s1 s2 := Nat.one_le_iff_ne_zero.2 hmin
    have hβ : 0 < (s1 + s2 : ℝ) / 2 - (min s1 s2 : ℝ) := mixed_exponent_pos hne
    set β := (s1 + s2 : ℝ) / 2 - (min s1 s2 : ℝ)
    set p := s1 ^ 2 + s2 ^ 2 + 1
    set K := (2 : ℝ) * ((s1 : ℝ) + (s2 : ℝ) + 1)
    have hβ' : 0 < β := hβ
    have htend :
        Tendsto (fun N : ℕ =>
            (2 : ℝ) * Real.rpow (N : ℝ) (-β) * (K * Real.log (N : ℝ)) ^ p) atTop
          (nhds 0) := by
      have hfun :
          (fun N : ℕ =>
              (2 : ℝ) * Real.rpow (N : ℝ) (-β) * (K * Real.log (N : ℝ)) ^ p) =
            fun N : ℕ =>
              (2 * K ^ p) * (Real.log (N : ℝ)) ^ p * Real.rpow (N : ℝ) (-β) := by
        funext N
        rw [mul_pow]
        ring
      rw [hfun]
      exact tendsto_log_pow_mul_rpow_neg (2 * K ^ p) p β hβ'
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ htend
    filter_upwards [eventually_ge_atTop 3] with N hN
    -- Bound via Lemma 1 + `N^{min} N^{-(s1+s2)/2} = N^{-β}`.
    have hN1 : 1 ≤ N := le_trans (by decide : 1 ≤ 3) hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hN1)
    have hr0 : 0 ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) :=
      Real.rpow_nonneg (le_of_lt hNpos) (-((s1 + s2 : ℝ) / 2))
    have hcard := card_unbal_real_le_of_min_pos s1 s2 N hN hminpos
    have hlog1 : (1 : ℝ) < Real.log N := by
      have h3 : (1 : ℝ) < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
      exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) (Nat.cast_le.2 hN))
    have hcast : (↑(N ^ min s1 s2) : ℝ) = (N : ℝ) ^ min s1 s2 := Nat.cast_pow N _
    have hlogM :
        Real.log (↑(N ^ min s1 s2) : ℝ) = (min s1 s2 : ℝ) * Real.log N := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_min]
    have hmin_le : (min s1 s2 : ℝ) ≤ (s1 : ℝ) + (s2 : ℝ) + 1 := by
      have hleft : (min s1 s2 : ℝ) ≤ (s1 : ℝ) := by exact_mod_cast min_le_left s1 s2
      have hs2 : (0 : ℝ) ≤ (s2 : ℝ) := Nat.cast_nonneg _
      linarith [hleft, hs2]
    have h2log :
        2 * Real.log (↑(N ^ min s1 s2) : ℝ) ≤ K * Real.log N := by
      rw [hlogM]
      simp only [K]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmin_le (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hlog1)))
        (by norm_num : (0 : ℝ) ≤ 2)
    have hlogM0 : 0 ≤ 2 * Real.log (↑(N ^ min s1 s2) : ℝ) := by
      have hM : 3 ≤ N ^ min s1 s2 := le_trans hN (N_le_pow_min hN hminpos)
      exact mul_nonneg (by norm_num)
        (le_trans (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 3)))
          (Real.log_le_log (by norm_num) (Nat.cast_le.2 hM)))
    have hbase : (1 : ℝ) ≤ K * Real.log N := by
      have hs1 : (0 : ℝ) ≤ (s1 : ℝ) := Nat.cast_nonneg _
      have hs2 : (0 : ℝ) ≤ (s2 : ℝ) := Nat.cast_nonneg _
      have hcoef : (1 : ℝ) ≤ (s1 : ℝ) + (s2 : ℝ) + 1 :=
        le_add_of_nonneg_left (add_nonneg hs1 hs2)
      have hK : (2 : ℝ) ≤ K := by
        simp only [K]
        have : (2 : ℝ) * (1 : ℝ) ≤ (2 : ℝ) * ((s1 : ℝ) + (s2 : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hcoef (by norm_num)
        simpa using this
      have hlog : (1 : ℝ) ≤ Real.log N := le_of_lt hlog1
      calc
        (1 : ℝ) ≤ (2 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ K * Real.log N :=
          mul_le_mul hK hlog (by norm_num)
            (le_trans (by norm_num : (0 : ℝ) ≤ 2) hK)
    have hp : s1 ^ 2 - 1 ≤ s1 ^ 2 + s2 ^ 2 + 1 :=
      (Nat.sub_le (s1 ^ 2) 1).trans (Nat.le_add_right (s1 ^ 2) (s2 ^ 2 + 1))
    have hq : s2 ^ 2 - 1 ≤ s1 ^ 2 + s2 ^ 2 + 1 :=
      (Nat.sub_le (s2 ^ 2) 1).trans
        ((Nat.le_add_left (s2 ^ 2) (s1 ^ 2)).trans (Nat.le_add_right (s1 ^ 2 + s2 ^ 2) 1))
    have hpow1 :
        (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s1 ^ 2 - 1) ≤ (K * Real.log N) ^ p :=
      (pow_le_pow_left₀ hlogM0 h2log _).trans (pow_le_pow_right₀ hbase hp)
    have hpow2 :
        (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s2 ^ 2 - 1) ≤ (K * Real.log N) ^ p :=
      (pow_le_pow_left₀ hlogM0 h2log _).trans (pow_le_pow_right₀ hbase hq)
    have hM0 : 0 ≤ (↑(N ^ min s1 s2) : ℝ) := Nat.cast_nonneg _
    have hcard' :
        (Fintype.card (UnbalSol s1 s2 N) : ℝ) ≤
          2 * (N : ℝ) ^ min s1 s2 * (K * Real.log N) ^ p := by
      calc
        (Fintype.card (UnbalSol s1 s2 N) : ℝ)
            ≤ (↑(N ^ min s1 s2) : ℝ) *
                  (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s1 ^ 2 - 1) +
                (↑(N ^ min s1 s2) : ℝ) *
                  (2 * Real.log (↑(N ^ min s1 s2) : ℝ)) ^ (s2 ^ 2 - 1) := hcard
        _ ≤ (↑(N ^ min s1 s2) : ℝ) * (K * Real.log N) ^ p +
              (↑(N ^ min s1 s2) : ℝ) * (K * Real.log N) ^ p :=
              add_le_add (mul_le_mul_of_nonneg_left hpow1 hM0)
                (mul_le_mul_of_nonneg_left hpow2 hM0)
        _ = 2 * (↑(N ^ min s1 s2) : ℝ) * (K * Real.log N) ^ p := by ring
        _ = 2 * (N : ℝ) ^ min s1 s2 * (K * Real.log N) ^ p := by rw [hcast]
    have hrpow_mul :
        Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) * (N : ℝ) ^ min s1 s2 =
          Real.rpow (N : ℝ) (-β) := by
      have hexp : -((s1 + s2 : ℝ) / 2) + ↑(min s1 s2) = -β := by
        simp only [β]
        rw [Nat.cast_min]
        ring
      rw [rpow_mul_npow hNpos, hexp]
    calc
      ‖mixedM d s1 s2 N g‖
          ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) *
              Fintype.card (UnbalSol s1 s2 N) :=
            norm_mixedM_le g hN1
      _ ≤ Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) *
            (2 * (N : ℝ) ^ min s1 s2 * (K * Real.log N) ^ p) :=
            mul_le_mul_of_nonneg_left hcard' hr0
      _ = 2 * (Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2)) * (N : ℝ) ^ min s1 s2) *
            (K * Real.log N) ^ p := by ring
      _ = 2 * Real.rpow (N : ℝ) (-β) * (K * Real.log N) ^ p := by
            rw [hrpow_mul]

end RMFLean
