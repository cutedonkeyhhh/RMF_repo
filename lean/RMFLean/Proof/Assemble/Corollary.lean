/-
PDF Corollary (`thm:cor-clt`):
even moments `ℳ_s(N) → s!` from Theorem 1 + coefficient Diophantine
(with `δ = deltaCLT`), mixed moments from `CorollaryMixed`, then
Gut, Chapter 5, Theorem 8.6 (`billingsley_method_of_moments`) for convergence in law.
-/
import RMFLean.Proof.Assemble.Main
import RMFLean.Proof.Assemble.CorollaryMixed
import RMFLean.Proof.Intersection.I1PieceIIIDio
import RMFLean.Proof.Setup.TailQAbsorb
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Basic

noncomputable section

open Classical Complex Filter Topology Real Asymptotics

namespace RMFLean

set_option maxHeartbeats 400000

/-! ### `s = 1` -/

theorem M_one {d N : ℕ} (g : CirclePoly d) (hN : 0 < N) :
    M d 1 N g = 1 := by
  simp only [M, pow_one]
  rw [U_one]
  exact div_self (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 hN))

theorem evenMoments_s_one {d : ℕ} (g : CirclePoly d) :
    Tendsto (fun N : ℕ => M d 1 N g) atTop (nhds (1 : ℝ)) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  simpa [gaussianMoment] using M_one g hpos

/-! ### Lists for the coefficient hypothesis -/

theorem ofFn_maximum_getD_le {n : ℕ} (f : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i, f i ≤ M) :
    ((List.ofFn f).maximum).getD 0 ≤ M := by
  set l := List.ofFn f
  have hall : ∀ a ∈ l, a ≤ M := by
    intro a ha
    rcases List.mem_ofFn.1 ha with ⟨i, rfl⟩
    exact h i
  have hle : l.maximum ≤ (↑M : WithBot ℝ) :=
    List.maximum_le_of_forall_le fun a ha => WithBot.coe_le_coe.2 (hall a ha)
  have hget : l.maximum.getD 0 = l.maximum.unbotD 0 := by
    cases l.maximum <;> rfl
  rw [hget]
  exact (WithBot.unbotD_le_iff (fun _ => hM)).2 hle

theorem exists_of_ofFn_maximum_getD_ge {n : ℕ} (f : Fin n → ℝ) {t : ℝ}
    (hn : 0 < n) (h : t ≤ ((List.ofFn f).maximum).getD 0) :
    ∃ i : Fin n, t ≤ f i := by
  set l := List.ofFn f
  have hlen : l.length = n := List.length_ofFn
  have hpos : 0 < l.length := by rw [hlen]; exact hn
  have hle : t ≤ l.maximum_of_length_pos hpos := by
    cases hm : l.maximum with
    | bot =>
      exact absurd hm (List.maximum_ne_bot_of_length_pos hpos)
    | coe a =>
      have hget : l.maximum.getD 0 = a := by rw [hm]; rfl
      have hmp : l.maximum_of_length_pos hpos = a := by
        have hcoe := List.coe_maximum_of_length_pos (l := l) hpos
        rw [hm] at hcoe
        exact WithBot.coe_inj.mp hcoe
      rw [hget] at h
      rwa [hmp]
  have hmem : l.maximum_of_length_pos hpos ∈ l :=
    List.maximum_of_length_pos_mem hpos
  rcases List.mem_ofFn.1 hmem with ⟨i, hi⟩
  exact ⟨i, hi ▸ hle⟩

/-! ### Asymptotics for `δ = N^{-o(1)}` -/

theorem tendsto_id_div_log_atTop :
    Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero
  refine Filter.tendsto_atTop.2 fun b => ?_
  have hε : (0 : ℝ) < 1 / max b 1 :=
    one_div_pos.2 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right b 1))
  filter_upwards [(tendsto_order.1 h0).2 (1 / max b 1) hε,
    eventually_gt_atTop (Real.exp 1)] with x hx hx1
  have hxpos : (0 : ℝ) < x := lt_trans (Real.exp_pos _) hx1
  have hlog : (1 : ℝ) < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx1
  have hlog0 : (0 : ℝ) < Real.log x := lt_trans (by norm_num) hlog
  have hpos : (0 : ℝ) < Real.log x / x := div_pos hlog0 hxpos
  have hinv : max b 1 < x / Real.log x := by
    have := (inv_lt_inv₀ hε hpos).mpr hx
    have hrw1 : (1 / max b 1)⁻¹ = max b 1 := by rw [one_div, inv_inv]
    have hrw2 : (Real.log x / x)⁻¹ = x / Real.log x := inv_div _ _
    rwa [hrw1, hrw2] at this
  exact le_of_lt (lt_of_le_of_lt (le_max_left b 1) hinv)

theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_nat_atTop

theorem tendsto_log_div_loglog_atTop :
    Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) atTop atTop :=
  tendsto_id_div_log_atTop.comp tendsto_log_nat_atTop

theorem s_sub_one_pos {s : ℕ} (hs : 2 ≤ s) : (0 : ℝ) < (s : ℝ) - 1 := by
  have hsR : (2 : ℝ) ≤ (s : ℝ) := Nat.cast_le.2 hs
  exact sub_pos.2 (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hsR)

theorem deltaCLT_pos (N s : ℕ) (hN : 3 ≤ N) : 0 < deltaCLT N s := by
  simp only [deltaCLT]
  exact Real.rpow_pos_of_pos (lt_trans (by norm_num) (log_N_gt_one hN)) _

/-- `δ · 𝒬 = (2s)^{3s²} (log N)^{-4s²}`. -/
theorem deltaCLT_mul_momentError (N s : ℕ) (hN : 3 ≤ N) :
    deltaCLT N s * momentErrorFactor N s =
      (2 * (s : ℝ)) ^ tailQExp s *
        (Real.log N) ^ (-((4 : ℝ) * (s : ℝ) ^ 2)) := by
  have hlog := log_N_gt_one hN
  have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog
  have hδ :
      deltaCLT N s =
        (Real.log N) ^ (-((7 : ℝ) * (s : ℝ) ^ 2)) := by
    simp only [deltaCLT]
  have hQ :
      momentErrorFactor N s =
        (2 * (s : ℝ)) ^ tailQExp s *
          (Real.log N) ^ (tailQExp s : ℝ) := by
    simp only [momentErrorFactor, tailQ]
    have hassoc : (2 * (s : ℝ) * Real.log N) = (2 * (s : ℝ)) * Real.log N := by
      ring
    rw [hassoc, mul_pow]
    congr 1
    exact (Real.rpow_natCast (Real.log N) (tailQExp s)).symm
  rw [hδ, hQ]
  have hexp : (tailQExp s : ℝ) = (3 : ℝ) * (s : ℝ) ^ 2 := by
    simp only [tailQExp, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hsum :
      (Real.log N) ^ (tailQExp s : ℝ) *
          (Real.log N) ^ (-((7 : ℝ) * (s : ℝ) ^ 2)) =
        (Real.log N) ^ (-((4 : ℝ) * (s : ℝ) ^ 2)) := by
    have hexp' :
        (tailQExp s : ℝ) + (-((7 : ℝ) * (s : ℝ) ^ 2)) =
          -((4 : ℝ) * (s : ℝ) ^ 2) := by
      rw [hexp]; ring
    exact (Real.rpow_add hlog0 _ _).symm.trans (by rw [hexp'])
  calc
    (Real.log N) ^ (-((7 : ℝ) * (s : ℝ) ^ 2)) *
        ((2 * (s : ℝ)) ^ tailQExp s *
          (Real.log N) ^ (tailQExp s : ℝ))
        = (2 * (s : ℝ)) ^ tailQExp s *
            ((Real.log N) ^ (tailQExp s : ℝ) *
              (Real.log N) ^ (-((7 : ℝ) * (s : ℝ) ^ 2))) := by
          ring
    _ = (2 * (s : ℝ)) ^ tailQExp s *
          (Real.log N) ^ (-((4 : ℝ) * (s : ℝ) ^ 2)) := by
          rw [hsum]

theorem tendsto_deltaCLT_mul_error (s : ℕ) (hs : 2 ≤ s) (Cll : ℝ) :
    Tendsto (fun N : ℕ =>
        Cll * deltaCLT N s * momentErrorFactor N s)
      atTop (nhds 0) := by
  have ha : (0 : ℝ) < (4 : ℝ) * (s : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    positivity
  have htail :
      Tendsto (fun N : ℕ =>
          Cll * (2 * (s : ℝ)) ^ tailQExp s *
            (Real.log (N : ℝ)) ^ (-((4 : ℝ) * (s : ℝ) ^ 2)))
        atTop (nhds 0) := by
    set K : ℝ := Cll * (2 * (s : ℝ)) ^ tailQExp s
    simpa [K] using
      ((tendsto_rpow_neg_atTop ha).comp tendsto_log_nat_atTop).const_mul K
  refine Tendsto.congr' ?_ htail
  filter_upwards [eventually_ge_atTop 3] with N hN
  simp [mul_assoc, deltaCLT_mul_momentError N s hN]

/-! ### `δ` sits in the Theorem 1 window for large `N` -/

theorem eventually_deltaCLT_lt_eighth (s : ℕ) (hs : 2 ≤ s) :
    ∀ᶠ N : ℕ in atTop, deltaCLT N s < 1 / 8 := by
  have hexp : (0 : ℝ) < (7 : ℝ) * (s : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    positivity
  filter_upwards [eventually_ge_atTop 3,
    (tendsto_atTop.1 tendsto_log_nat_atTop)
      (Real.rpow 8 (1 / ((7 : ℝ) * (s : ℝ) ^ 2)) + 1)] with N hN3 hlog'
  have hlog1 := log_N_gt_one hN3
  have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog1
  have hbase : Real.rpow 8 (1 / ((7 : ℝ) * (s : ℝ) ^ 2)) < Real.log N :=
    lt_of_lt_of_le (lt_add_one _) hlog'
  have h8 : (0 : ℝ) < 8 := by norm_num
  have hpow : (8 : ℝ) < Real.rpow (Real.log N) ((7 : ℝ) * (s : ℝ) ^ 2) := by
    have hrw : (8 : ℝ) =
        Real.rpow (Real.rpow 8 (1 / ((7 : ℝ) * (s : ℝ) ^ 2)))
          ((7 : ℝ) * (s : ℝ) ^ 2) := by
      have hmul :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)
          (1 / ((7 : ℝ) * (s : ℝ) ^ 2)) ((7 : ℝ) * (s : ℝ) ^ 2)
      have hone :
          Real.rpow 8 ((1 / ((7 : ℝ) * (s : ℝ) ^ 2)) *
            ((7 : ℝ) * (s : ℝ) ^ 2)) = 8 := by
        rw [one_div_mul_cancel (ne_of_gt hexp)]
        exact Real.rpow_one 8
      exact hone.symm.trans hmul
    rw [hrw]
    exact Real.rpow_lt_rpow (Real.rpow_nonneg (by norm_num) _) hbase hexp
  have hrw : deltaCLT N s =
      (Real.rpow (Real.log N) ((7 : ℝ) * (s : ℝ) ^ 2))⁻¹ := by
    simp only [deltaCLT]
    exact Real.rpow_neg hlog0.le _
  rw [hrw, one_div]
  exact (inv_lt_inv₀ (Real.rpow_pos_of_pos hlog0 _) h8).mpr hpow

theorem eventually_rpow_lt_deltaCLT (s : ℕ) (_hs : 2 ≤ s) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, Real.rpow (N : ℝ) (-C) < deltaCLT N s := by
  filter_upwards [eventually_ge_atTop 3,
    (tendsto_atTop.1 tendsto_log_div_loglog_atTop)
      ((7 : ℝ) * (s : ℝ) ^ 2 / C + 1)] with N hN3 hrat
  have hNpos : (0 : ℝ) < N :=
    Nat.cast_pos.2 (lt_of_lt_of_le (by decide : 0 < 3) hN3)
  have hlog1 := log_N_gt_one hN3
  have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog1
  have hllpos : 0 < Real.log (Real.log N) := Real.log_pos hlog1
  have hgt : (7 : ℝ) * (s : ℝ) ^ 2 / C <
      Real.log N / Real.log (Real.log N) :=
    lt_of_lt_of_le (lt_add_one _) hrat
  have hmid : (7 : ℝ) * (s : ℝ) ^ 2 <
      C * (Real.log N / Real.log (Real.log N)) := by
    have := (div_lt_iff₀ hC).1 hgt
    simpa [mul_comm] using this
  have hmul : (7 : ℝ) * (s : ℝ) ^ 2 * Real.log (Real.log N) < C * Real.log N := by
    have := mul_lt_mul_of_pos_right hmid hllpos
    have hrw :
        C * (Real.log N / Real.log (Real.log N)) * Real.log (Real.log N) =
          C * Real.log N := by
      calc
        C * (Real.log N / Real.log (Real.log N)) * Real.log (Real.log N)
            = C * Real.log N * Real.log (Real.log N) /
                Real.log (Real.log N) := by ring
        _ = C * Real.log N :=
            mul_div_cancel_right₀ _ (ne_of_gt hllpos)
    rwa [hrw] at this
  have hNexp : Real.rpow (N : ℝ) (-C) = Real.exp (Real.log N * (-C)) :=
    Real.rpow_def_of_pos hNpos _
  have hδexp : deltaCLT N s =
      Real.exp (Real.log (Real.log N) * (-((7 : ℝ) * (s : ℝ) ^ 2))) := by
    simp only [deltaCLT]
    exact Real.rpow_def_of_pos hlog0 _
  rw [hNexp, hδexp]
  exact Real.exp_lt_exp.2 (by linarith)

theorem eventually_deltaCLT_kills_scale (s : ℕ) (_hs : 2 ≤ s)
    {Cd γ : ℝ} (hCd : 0 < Cd) (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) < (N : ℝ) * Real.rpow (deltaCLT N s) (Cd * γ) := by
  have hα : (0 : ℝ) < (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ := by positivity
  filter_upwards [eventually_ge_atTop 3,
    (tendsto_atTop.1 tendsto_log_div_loglog_atTop)
      ((7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ + 1)] with N hN3 hrat
  have hNpos : (0 : ℝ) < N :=
    Nat.cast_pos.2 (lt_of_lt_of_le (by decide : 0 < 3) hN3)
  have hlog1 := log_N_gt_one hN3
  have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog1
  have hllpos : 0 < Real.log (Real.log N) := Real.log_pos hlog1
  have hδpos : 0 < deltaCLT N s := deltaCLT_pos N s hN3
  have hgt : (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ <
      Real.log N / Real.log (Real.log N) :=
    lt_of_lt_of_le (lt_add_one _) hrat
  have hmul : (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ * Real.log (Real.log N) <
      Real.log N := by
    have := mul_lt_mul_of_pos_right hgt hllpos
    have hrw :
        Real.log N / Real.log (Real.log N) * Real.log (Real.log N) =
          Real.log N :=
      div_mul_cancel₀ _ (ne_of_gt hllpos)
    rwa [hrw] at this
  have hdiff : 0 < Real.log N -
      (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ * Real.log (Real.log N) :=
    sub_pos.2 hmul
  have hδpow :
      Real.rpow (deltaCLT N s) (Cd * γ) =
        Real.rpow (Real.log N) (-((7 : ℝ) * (s : ℝ) ^ 2) * (Cd * γ)) := by
    simp only [deltaCLT]
    exact (Real.rpow_mul hlog0.le _ _).symm
  have hprodpos : (0 : ℝ) < (N : ℝ) * Real.rpow (deltaCLT N s) (Cd * γ) :=
    mul_pos hNpos (Real.rpow_pos_of_pos hδpos _)
  have hlogprod :
      Real.log ((N : ℝ) * Real.rpow (deltaCLT N s) (Cd * γ)) =
        Real.log N - (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ * Real.log (Real.log N) := by
    set α := -((7 : ℝ) * (s : ℝ) ^ 2) * (Cd * γ)
    have hposy : 0 < Real.rpow (Real.log N) α :=
      Real.rpow_pos_of_pos hlog0 _
    have hlr : Real.log (Real.rpow (Real.log N) α) =
        α * Real.log (Real.log N) := Real.log_rpow hlog0 _
    calc
      Real.log ((N : ℝ) * Real.rpow (deltaCLT N s) (Cd * γ))
          = Real.log ((N : ℝ) * Real.rpow (Real.log N) α) := by
            rw [hδpow]
      _ = Real.log N + Real.log (Real.rpow (Real.log N) α) :=
          Real.log_mul (ne_of_gt hNpos) (ne_of_gt hposy)
      _ = Real.log N + α * Real.log (Real.log N) := by rw [hlr]
      _ = Real.log N - (7 : ℝ) * (s : ℝ) ^ 2 * Cd * γ *
            Real.log (Real.log N) := by
          simp only [α]; ring
  have : (1 : ℝ) < (N : ℝ) * Real.rpow (deltaCLT N s) (Cd * γ) := by
    have hexp := Real.exp_lt_exp.2 (hlogprod ▸ hdiff)
    rwa [Real.exp_zero, Real.exp_log hprodpos] at hexp
  exact this

/--
With \(\delta=(\log N)^{-7s^2}\) and \(\varepsilon\) small enough that
\(7s^2 C_d\varepsilon<1\), one has
\(B\exp(B^\varepsilon)<C N\) for \(B=\delta^{-C_d}\) and large \(N\).
-/
theorem eventually_deltaCLT_kills_exp (s : ℕ) (_hs : 2 ≤ s)
    {Cd ε C : ℝ} (_hCd : 0 < Cd) (_hε : 0 < ε) (hC : 0 < C)
    (hsmall : (7 : ℝ) * (s : ℝ) ^ 2 * Cd * ε < 1) :
    ∀ᶠ N : ℕ in atTop,
      (deltaCLT N s) ^ (-Cd) *
        Real.exp (((deltaCLT N s) ^ (-Cd)) ^ ε)
        < C * (N : ℝ) := by
  set α : ℝ := (7 : ℝ) * (s : ℝ) ^ 2 * Cd * ε
  have hα1 : α < 1 := hsmall
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  have hpow0 :
      Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (α - 1))
        atTop (nhds 0) := by
    have hneg :
        Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (-(1 - α)))
          atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop h1α).comp tendsto_log_nat_atTop
    convert hneg using 1
    ext N
    congr 1
    ring
  have hloglog :
      Tendsto (fun N : ℕ =>
        ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log (N : ℝ)) /
          Real.log (N : ℝ)) atTop (nhds 0) := by
    have h0 : Tendsto (fun N : ℕ =>
        Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (nhds 0) :=
      isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_nat_atTop
    simpa [mul_div_assoc] using
      h0.const_mul ((7 : ℝ) * (s : ℝ) ^ 2 * Cd)
  have hdiff :
      Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) - (Real.log (N : ℝ)) ^ α -
          ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log (N : ℝ)))
        atTop atTop := by
    refine Filter.tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop 3,
      (tendsto_atTop.1 tendsto_log_nat_atTop) (2 * max b 1 + 1),
      (tendsto_order.1 hpow0).2 (1 / 4) (by norm_num),
      (tendsto_order.1 hloglog).2 (1 / 4) (by norm_num)] with N hN3 hlogbig hpow hll
    have hlog1 := log_N_gt_one hN3
    have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog1
    have hLα : (Real.log N) ^ α < Real.log N / 4 := by
      have hrw : (Real.log N : ℝ) ^ α =
          (Real.log N : ℝ) ^ (α - 1) * Real.log N := by
        have hadd := Real.rpow_add hlog0 (α - 1) (1 : ℝ)
        rw [sub_add_cancel, Real.rpow_one] at hadd
        exact hadd
      rw [hrw]
      have : (Real.log N : ℝ) ^ (α - 1) * Real.log N <
          (1 / 4) * Real.log N :=
        mul_lt_mul_of_pos_right hpow hlog0
      rwa [one_div, inv_mul_eq_div] at this
    have hKll :
        ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log N) <
          Real.log N / 4 := by
      have : ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log N) <
          (1 / 4) * Real.log N := (div_lt_iff₀ hlog0).1 hll
      rwa [one_div, inv_mul_eq_div] at this
    have hhalf :
        Real.log N / 2 <
          Real.log N - (Real.log N) ^ α -
            ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log N) := by
      linarith
    have hb : b < Real.log N / 2 := by
      have : 2 * max b 1 < Real.log N := by linarith
      have : max b 1 < Real.log N / 2 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)
      exact lt_of_le_of_lt (le_max_left b 1) this
    exact le_of_lt (hb.trans hhalf)
  filter_upwards [eventually_ge_atTop 3,
    (tendsto_atTop.1 hdiff) (-Real.log C + 1)] with N hN3 hdiffN
  have hNpos : (0 : ℝ) < N :=
    Nat.cast_pos.2 (lt_of_lt_of_le (by decide : 0 < 3) hN3)
  have hlog1 := log_N_gt_one hN3
  have hlog0 : 0 < Real.log N := lt_trans (by norm_num) hlog1
  have hδpos : 0 < deltaCLT N s := deltaCLT_pos N s hN3
  have hB :
      (deltaCLT N s) ^ (-Cd) =
        (Real.log N : ℝ) ^ ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) := by
    simp only [deltaCLT]
    rw [← Real.rpow_mul hlog0.le]
    congr 1
    ring
  have hBε :
      ((deltaCLT N s) ^ (-Cd)) ^ ε = (Real.log N : ℝ) ^ α := by
    rw [hB, ← Real.rpow_mul hlog0.le]
  have hBpos : 0 < (deltaCLT N s) ^ (-Cd) :=
    Real.rpow_pos_of_pos hδpos _
  have hexppos : 0 < Real.exp (((deltaCLT N s) ^ (-Cd)) ^ ε) :=
    Real.exp_pos _
  have hleftpos : 0 <
      (deltaCLT N s) ^ (-Cd) * Real.exp (((deltaCLT N s) ^ (-Cd)) ^ ε) :=
    mul_pos hBpos hexppos
  have hCNpos : 0 < C * (N : ℝ) := mul_pos hC hNpos
  have hlogL :
      Real.log ((deltaCLT N s) ^ (-Cd) *
        Real.exp (((deltaCLT N s) ^ (-Cd)) ^ ε)) =
        ((7 : ℝ) * (s : ℝ) ^ 2 * Cd) * Real.log (Real.log N) +
          (Real.log N) ^ α := by
    rw [Real.log_mul (ne_of_gt hBpos) (ne_of_gt hexppos), Real.log_exp, hB,
      Real.log_rpow hlog0, ← hB, hBε]
  have hlogR : Real.log (C * (N : ℝ)) = Real.log C + Real.log N :=
    Real.log_mul (ne_of_gt hC) (ne_of_gt hNpos)
  have hltlog :
      Real.log ((deltaCLT N s) ^ (-Cd) *
        Real.exp (((deltaCLT N s) ^ (-Cd)) ^ ε)) <
        Real.log (C * (N : ℝ)) := by
    rw [hlogL, hlogR]
    linarith [hdiffN]
  exact (Real.log_lt_log_iff hleftpos hCNpos).1 hltlog

/-! ### Coefficient hypothesis kills alternative (2) -/

theorem coeffDiophantine.pos_degree {d : ℕ} {g : CirclePoly d}
    (h : coeffDiophantine g) : 0 < d := by
  obtain ⟨_C, _hC, hbound⟩ := h (1 : ℝ) (by norm_num)
  by_contra hd
  simpa [dif_neg hd] using hbound 1 Int.one_ne_zero

/--
PDF Corollary proof: some degree \(i\) has
\(\|k\beta_i\|\ge C\exp(-|k|^\varepsilon)\).  Combined with
\(\|kg\|_{C^\infty[N]}\le\delta^{-C_d}\) this is
\(C\exp(-|k|^\varepsilon)\le\delta^{-C_d}N^{-i}\).  With
\(|k|\le\delta^{-C_d}=:B\) the left side is \(\ge C\exp(-B^\varepsilon)\),
hence \(C N^i\le B\exp(B^\varepsilon)\).  The coarsest comparison
\(C N\le B\exp(B^\varepsilon)\) still fails for large \(N\) once
\(\varepsilon\) is small enough that \(B^\varepsilon=o(\log N)\), so
alternative (2) is impossible.
-/
theorem not_altDiophantine_of_coeff {d : ℕ} {g : CirclePoly d} {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε)
    (hbound : ∀ q : ℤ, q ≠ 0 →
      if _h : 0 < d then
        ((List.ofFn fun i : Fin d => coeffDist g q i).maximum).getD 0
          ≥ coeffExpLower C ε q
      else False)
    {N : ℕ} (hN : 3 ≤ N)
    {δ Cd : ℝ} (_hδ : 0 < δ) (_hδ1 : δ < 1) (_hCd : 0 < Cd)
    (hscale :
      Real.rpow δ (-Cd) *
        Real.exp (Real.rpow (Real.rpow δ (-Cd)) ε) < C * (N : ℝ)) :
    ¬ altDiophantine d N g δ Cd := by
  intro hDio
  have hd : 0 < d := by
    by_contra hd
    simpa [dif_neg hd] using hbound 1 Int.one_ne_zero
  rcases hDio with ⟨k, hk0, hk, hnorm⟩
  have hhyp := hbound k hk0
  rw [dif_pos hd] at hhyp
  obtain ⟨i, hi⟩ := exists_of_ofFn_maximum_getD_ge
    (fun j : Fin d => coeffDist g k j) hd hhyp
  set i' : ℕ := (i : ℕ) + 1
  have hi'pos : 1 ≤ i' := Nat.succ_le_succ (Nat.zero_le _)
  have hNpos : (0 : ℝ) < N :=
    Nat.cast_pos.2 (lt_of_lt_of_le (by decide : 0 < 3) hN)
  set B : ℝ := Real.rpow δ (-Cd)
  set x : ℝ := Real.rpow B ε
  have hj : (coeffIndex i : ℕ) ≠ 0 := by
    simp only [coeffIndex, Fin.val_succ]
    exact Nat.succ_ne_zero _
  have hge := CirclePoly.cInfinityNorm_ge_term (k • g) N (coeffIndex i) hj
  have hbeta : (k • g).beta (coeffIndex i) =
      (k : ℝ) * g.beta (coeffIndex i) := CirclePoly.beta_smul k g _
  rw [hbeta] at hge
  have hi'val : (coeffIndex i : ℕ) = i' := by
    simp only [coeffIndex, i', Fin.val_succ]
  have hle :
      (N : ℝ) ^ i' *
        CirclePoly.distToInt ((k : ℝ) * g.beta (coeffIndex i)) ≤ B := by
    simpa [hi'val, B] using hge.trans hnorm
  have hNjpos : (0 : ℝ) < (N : ℝ) ^ i' := pow_pos hNpos _
  have hdist :
      CirclePoly.distToInt ((k : ℝ) * g.beta (coeffIndex i)) ≤
        B / (N : ℝ) ^ i' := by
    rw [le_div_iff₀ hNjpos, mul_comm]
    exact hle
  have hkabs1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hk0)
  have hkabs0 : (0 : ℝ) < |(k : ℝ)| := lt_of_lt_of_le (by norm_num) hkabs1
  have hkleB : |(k : ℝ)| ≤ B := hk
  have hdist_ge :
      coeffExpLower C ε k ≤
        CirclePoly.distToInt ((k : ℝ) * g.beta (coeffIndex i)) := by
    simpa [coeffDist] using hi
  have hCexp :
      C * Real.exp (-Real.rpow |(k : ℝ)| ε) ≤ B / (N : ℝ) ^ i' := by
    simpa [coeffExpLower] using hdist_ge.trans hdist
  have hpowle : Real.rpow |(k : ℝ)| ε ≤ x :=
    Real.rpow_le_rpow (le_of_lt hkabs0) hkleB (le_of_lt hε)
  have hexpge : Real.exp (-x) ≤ Real.exp (-Real.rpow |(k : ℝ)| ε) :=
    Real.exp_le_exp.2 (neg_le_neg hpowle)
  have hlow : C * Real.exp (-x) ≤ B / (N : ℝ) ^ i' :=
    (mul_le_mul_of_nonneg_left hexpge (le_of_lt hC)).trans hCexp
  have hxpos : 0 < Real.exp x := Real.exp_pos _
  have h1 :
      C * Real.exp (-x) * ((N : ℝ) ^ i' * Real.exp x) ≤
        (B / (N : ℝ) ^ i') * ((N : ℝ) ^ i' * Real.exp x) :=
    mul_le_mul_of_nonneg_right hlow
      (mul_nonneg (le_of_lt hNjpos) (le_of_lt hxpos))
  have hleft :
      C * Real.exp (-x) * ((N : ℝ) ^ i' * Real.exp x) = C * (N : ℝ) ^ i' := by
    calc
      C * Real.exp (-x) * ((N : ℝ) ^ i' * Real.exp x)
          = C * (N : ℝ) ^ i' * (Real.exp (-x) * Real.exp x) := by ring
      _ = C * (N : ℝ) ^ i' * Real.exp (-x + x) := by rw [Real.exp_add]
      _ = C * (N : ℝ) ^ i' * Real.exp 0 := by simp
      _ = C * (N : ℝ) ^ i' := by rw [Real.exp_zero, mul_one]
  have hright :
      (B / (N : ℝ) ^ i') * ((N : ℝ) ^ i' * Real.exp x) = B * Real.exp x := by
    field_simp [ne_of_gt hNjpos]
  have hmul : C * (N : ℝ) ^ i' ≤ B * Real.exp x := by
    rwa [hleft, hright] at h1
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ i' := by
    have : N ≤ N ^ i' :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hi'pos)) N
    exact_mod_cast this
  have hCN : C * (N : ℝ) ≤ C * (N : ℝ) ^ i' :=
    mul_le_mul_of_nonneg_left hNpow (le_of_lt hC)
  exact ((hCN.trans hmul).trans_eq (by simp [B, x])).not_gt hscale

/-! ### Even moments and the corollary -/

theorem evenMoments_of_coeffDiophantine (d : ℕ) (g : CirclePoly d)
    (hcoeff : coeffDiophantine g) : EvenMomentsToGaussian d g := by
  intro s hs
  rcases Nat.eq_or_lt_of_le hs with h1 | hlt
  · subst h1
    simpa [gaussianMoment] using evenMoments_s_one g
  · have hs2 : 2 ≤ s := Nat.succ_le_of_lt hlt
    obtain ⟨Cd, hCd, hrest⟩ := momentDichotomy d
    obtain ⟨Cll, _hCll, C, hC, N0, hmain⟩ := hrest s hs2
    set ε : ℝ := (1 : ℝ) / ((14 : ℝ) * (s : ℝ) ^ 2 * Cd + 1)
    have hεpos : 0 < ε := by
      have : 0 < (14 : ℝ) * (s : ℝ) ^ 2 * Cd + 1 := by positivity
      exact one_div_pos.2 this
    have hsmall : (7 : ℝ) * (s : ℝ) ^ 2 * Cd * ε < 1 := by
      have hnum : 0 < (7 : ℝ) * (s : ℝ) ^ 2 * Cd := by positivity
      have hden0 : 0 < (14 : ℝ) * (s : ℝ) ^ 2 * Cd := by positivity
      have hrw : (7 : ℝ) * (s : ℝ) ^ 2 * Cd * ε =
          (7 : ℝ) * (s : ℝ) ^ 2 * Cd / ((14 : ℝ) * (s : ℝ) ^ 2 * Cd + 1) := by
        simp only [ε, div_eq_inv_mul]
        ring
      rw [hrw]
      have hhalf :
          (7 : ℝ) * (s : ℝ) ^ 2 * Cd / ((14 : ℝ) * (s : ℝ) ^ 2 * Cd) = 1 / 2 := by
        field_simp
        ring
      have hlt :
          (7 : ℝ) * (s : ℝ) ^ 2 * Cd / ((14 : ℝ) * (s : ℝ) ^ 2 * Cd + 1) <
            (7 : ℝ) * (s : ℝ) ^ 2 * Cd / ((14 : ℝ) * (s : ℝ) ^ 2 * Cd) :=
        div_lt_div_of_pos_left hnum hden0 (lt_add_one _)
      exact lt_trans (hlt.trans_eq hhalf) (by norm_num : (1 : ℝ) / 2 < 1)
    obtain ⟨Ccoeff, hCcoeff, hcoeffBound⟩ := hcoeff ε hεpos
    have hbound :
        ∀ᶠ N : ℕ in atTop,
          |M d s N g - gaussianMoment s| ≤
            Cll * deltaCLT N s * momentErrorFactor N s := by
      filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop 3,
        eventually_deltaCLT_lt_eighth s hs2,
        eventually_rpow_lt_deltaCLT s hs2 hC,
        eventually_deltaCLT_kills_exp s hs2 hCd hεpos hCcoeff hsmall]
        with N hN0 hN3 hhalf hlo hscale
      have hrange : inMomentRange N s := ⟨hs2, hN3⟩
      have hδ : 0 < deltaCLT N s := deltaCLT_pos N s hN3
      have hδ1 : deltaCLT N s < 1 := lt_trans hhalf (by norm_num)
      rcases hmain N hN0 hrange (deltaCLT N s) hlo hhalf g with hG | hD
      · simpa [altGaussian, mul_assoc] using hG
      · exact (not_altDiophantine_of_coeff hCcoeff hεpos hcoeffBound
            hN3 hδ hδ1 hCd hscale hD).elim
    have hv := tendsto_deltaCLT_mul_error s hs2 Cll
    have hvneg :
        Tendsto (fun N : ℕ =>
            -(Cll * deltaCLT N s * momentErrorFactor N s))
          atTop (nhds 0) := by
      simpa using hv.neg
    have hlo' :
        ∀ᶠ N : ℕ in atTop,
          -(Cll * deltaCLT N s * momentErrorFactor N s) ≤
            M d s N g - gaussianMoment s := by
      filter_upwards [hbound] with N h
      exact neg_le_of_abs_le h
    have hhi' :
        ∀ᶠ N : ℕ in atTop,
          M d s N g - gaussianMoment s ≤
            Cll * deltaCLT N s * momentErrorFactor N s := by
      filter_upwards [hbound] with N h
      exact le_of_abs_le h
    have hdiff :
        Tendsto (fun N : ℕ => M d s N g - gaussianMoment s) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hvneg hv hlo' hhi'
    have hconst :
        Tendsto (fun _ : ℕ => gaussianMoment s) atTop (nhds (gaussianMoment s)) :=
      tendsto_const_nhds
    have hsum := hdiff.add hconst
    simpa [sub_add_cancel, zero_add, gaussianMoment] using hsum

theorem centralLimitMoments (d : ℕ) : CentralLimitMoments d :=
  fun g hg => ⟨evenMoments_of_coeffDiophantine d g hg, mixedMomentsVanish_any d g⟩

theorem centralLimit (d : ℕ) : CentralLimit d :=
  fun g hg =>
    billingsley_method_of_moments g
      (evenMoments_of_coeffDiophantine d g hg)
      (mixedMomentsVanish_any d g)

end RMFLean
