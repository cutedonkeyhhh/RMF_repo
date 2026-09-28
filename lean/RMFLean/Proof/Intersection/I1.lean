/-
PDF Lemma 9 (lem:I1) -- off-diagonal part of a k-fold intersection.

Uses Lemma 8 (IntersectionParam) for the outer/fibre splitting, then
Moebius inversion on fibre coprimality (PDF eq:mobius-step), then the
three-piece split (Pieces I--III).
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.DivisorSums
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Param.IntersectionParam
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Fintype.Card

noncomputable section

open Classical BigOperators Complex
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RMFLean

/--
Off-diagonal k-fold intersection support (after reindexing i1 = 1):
intersection of F_i with n1 != m1.
-/
def I1Support (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    (∀ i ∈ I, x.memF A i h0) ∧ ¬ x.onDiag h0

/-- Outer parameters of an off-diagonal intersection point. -/
def I1Outer (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s) :
    Finset (IntersectionOuter s) :=
  (I1Support (s := s) (N := N) A I h0).image fun x =>
    (x.toIntersectionCanon h0).outer

/-- PDF `Q(ν) = m₂'⋯mₛ'`, combining all fibre coprimality constraints. -/
def IntersectionOuter.Q {s : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s) : ℕ :=
  ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.m' i

theorem gcd_I1Outer_Q_eq_one_iff {s : ℕ} (ν : IntersectionOuter s)
    (h0 : 0 < s) (b : ℕ) :
    Nat.gcd b (ν.Q h0) = 1 ↔
      ∀ j : Fin s, j ≠ ⟨0, h0⟩ → Nat.gcd b (ν.m' j) = 1 := by
  change Nat.Coprime b (ν.Q h0) ↔
    ∀ j : Fin s, j ≠ ⟨0, h0⟩ → Nat.Coprime b (ν.m' j)
  rw [IntersectionOuter.Q, Nat.coprime_prod_right_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

/-- The PDF fibre is the box `B(ν)` filtered by one condition `gcd(b,Q(ν))=1`. -/
theorem fibreG_eq_filter_fibreB (s N A : ℕ) (ν : IntersectionOuter s)
    (h0 : 0 < s) :
    fibreG s N A ν h0 =
      (fibreB s N A ν h0).filter fun b => Nat.gcd b (ν.Q h0) = 1 := by
  ext b
  simp only [fibreG, fibreB, Finset.mem_filter]
  rw [gcd_I1Outer_Q_eq_one_iff]
  tauto

/-- Off-diagonal forces n1' != m1'. -/
theorem I1Support_n1'_ne_m1' {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {x : Sol s N} (hx : x ∈ I1Support (s := s) (N := N) A I h0) :
    (x.toIntersectionCanon h0).outer.n1' ≠
      (x.toIntersectionCanon h0).outer.m1' := by
  have hond : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx).2.2
  intro heq
  apply hond
  have hn := toIntersectionCanon_reconN1 s N x h0
  have hm := toIntersectionCanon_reconM1 s N x h0
  simp only [Sol.onDiag]
  have : x.n ⟨0, h0⟩ = x.m ⟨0, h0⟩ := by
    rw [← hn, ← hm]
    simp only [IntersectionCanon.reconN1, IntersectionCanon.reconM1, heq]
  exact this

/-- Sum of mu over divisors is 1 at n=1 and 0 otherwise (n > 0). -/
theorem sum_moebius_divisors_eq (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (μ d : ℂ) = if n = 1 then 1 else 0 := by
  have hμζ : ((μ : ArithmeticFunction ℂ) * (zeta : ArithmeticFunction ℂ)) = 1 :=
    coe_moebius_mul_coe_zeta
  have hprod : ((μ : ArithmeticFunction ℂ) * zeta) n = (1 : ArithmeticFunction ℂ) n := by
    rw [hμζ]
  rw [ArithmeticFunction.mul_apply] at hprod
  have hconv :
      ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℂ) * (zeta x.2 : ℂ) =
        ∑ d ∈ n.divisors, (μ d : ℂ) := by
    rw [Nat.sum_divisorsAntidiagonal (fun i j => (μ i : ℂ) * (zeta j : ℂ))]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdd : d ∣ n := (Nat.mem_divisors.1 hd).1
    have hpos : 0 < n / d :=
      Nat.div_pos (Nat.le_of_dvd hn hdd) (Nat.pos_of_dvd_of_pos hdd hn)
    have hne : n / d ≠ 0 := ne_of_gt hpos
    simp [ArithmeticFunction.zeta_apply, hne]
  have hone : (1 : ArithmeticFunction ℂ) n = if n = 1 then (1 : ℂ) else 0 := by
    simp [ArithmeticFunction.one_apply]
  calc
    ∑ d ∈ n.divisors, (μ d : ℂ)
        = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℂ) * (zeta x.2 : ℂ) := hconv.symm
    _ = (1 : ArithmeticFunction ℂ) n := hprod
    _ = if n = 1 then 1 else 0 := hone

/-- Indicator of coprimality via Moebius. -/
theorem moebius_indicator_coprime (b m : ℕ) (hb : 0 < b) :
    (if Nat.gcd b m = 1 then (1 : ℂ) else 0) =
      ∑ d ∈ (Nat.gcd b m).divisors, (μ d : ℂ) := by
  have hg := Nat.gcd_pos_of_pos_left m hb
  rw [sum_moebius_divisors_eq _ hg]

/-- Divisors of gcd(b,m) equal divisors of m that also divide b. -/
theorem divisors_gcd_eq_filter (b m : ℕ) (_hb : 0 < b) (hm : m ≠ 0) :
    (Nat.gcd b m).divisors = m.divisors.filter fun d => d ∣ b := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · intro ⟨hd, _⟩
    exact ⟨⟨hd.trans (Nat.gcd_dvd_right b m), hm⟩,
      hd.trans (Nat.gcd_dvd_left b m)⟩
  · intro ⟨⟨hdm, _⟩, hdb⟩
    exact ⟨Nat.dvd_gcd hdb hdm, fun h => absurd (Nat.gcd_eq_zero_iff.1 h).2 hm⟩

/-- One-step Moebius inversion on a finite box (PDF eq:mobius-step). -/
theorem mobius_step_sum_complex (B : Finset ℕ) (m : ℕ) (H : ℕ → ℂ)
    (hB : ∀ b ∈ B, 0 < b) (hm : m ≠ 0) :
    (∑ b ∈ B.filter fun b => Nat.gcd b m = 1, H b) =
      ∑ d ∈ m.divisors, (μ d : ℂ) * ∑ b ∈ B.filter fun b => d ∣ b, H b := by
  have hterm : ∀ b ∈ B,
      (if Nat.gcd b m = 1 then H b else 0) =
        (∑ d ∈ (Nat.gcd b m).divisors, (μ d : ℂ)) * H b := by
    intro b hb
    rw [← moebius_indicator_coprime b m (hB b hb)]
    by_cases hcop : Nat.gcd b m = 1 <;> simp [hcop]
  calc
    (∑ b ∈ B.filter fun b => Nat.gcd b m = 1, H b)
        = ∑ b ∈ B, if Nat.gcd b m = 1 then H b else 0 := by
          simp [Finset.sum_filter]
    _ = ∑ b ∈ B, (∑ d ∈ (Nat.gcd b m).divisors, (μ d : ℂ)) * H b :=
          Finset.sum_congr rfl hterm
    _ = ∑ b ∈ B, ∑ d ∈ (Nat.gcd b m).divisors, (μ d : ℂ) * H b := by
          refine Finset.sum_congr rfl ?_
          intro b _hb
          rw [Finset.sum_mul]
    _ = ∑ b ∈ B, ∑ d ∈ m.divisors,
          if d ∣ b then (μ d : ℂ) * H b else 0 := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [divisors_gcd_eq_filter b m (hB b hb) hm, Finset.sum_filter]
    _ = ∑ d ∈ m.divisors, ∑ b ∈ B,
          if d ∣ b then (μ d : ℂ) * H b else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ m.divisors, (μ d : ℂ) * ∑ b ∈ B.filter fun b => d ∣ b, H b := by
          refine Finset.sum_congr rfl ?_
          intro d _hd
          calc
            (∑ b ∈ B, if d ∣ b then (μ d : ℂ) * H b else 0)
                = ∑ b ∈ B.filter fun b => d ∣ b, (μ d : ℂ) * H b := by
                  simp [Finset.sum_filter]
            _ = (μ d : ℂ) * ∑ b ∈ B.filter fun b => d ∣ b, H b := by
                  simp [Finset.mul_sum]

/-! ### Phases, fibre sums, and Möbius bookkeeping -/

/-- Outer phase `Ω(ν)` (PDF): product over coordinates `i ≥ 2`. -/
def I1OuterPhase {d s : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) : ℂ :=
  ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
    g.ePhase (ν.nTail i) * starRingEnd ℂ (g.ePhase (ν.t i * ν.m' i))

/-- Fibre phase attached to a reconstructed point `(b, ν)`. -/
def I1FibrePhase {d s : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) (b : ℕ) : ℂ :=
  g.ePhase (b * ν.T h0 * ν.n1') *
    starRingEnd ℂ (g.ePhase (b * ν.T h0 * ν.m1'))

/-- Circle sum `S(ν)` on the coprime fibre. -/
def I1FibreSum {d s : ℕ} (g : CirclePoly d) (N A : ℕ) (h0 : 0 < s)
    (ν : IntersectionOuter s) : ℂ :=
  ∑ b ∈ fibreG s N A ν h0, I1FibrePhase g h0 ν b

/--
Inner circle sum on a scaled box (PDF `S(ν,d)`).
Support is `{k | D·k ∈ ℬ(ν)}`, equivalent to the PDF range
`A/(DT) ≤ k ≤ N/(DTM)`.
-/
def I1BoxSum {d s : ℕ} (g : CirclePoly d) (N A : ℕ) (h0 : 0 < s)
    (ν : IntersectionOuter s) (D : ℕ) : ℂ :=
  ∑ k ∈ (Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0,
    I1FibrePhase g h0 ν (D * k)

theorem norm_I1OuterPhase {d s : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) : ‖I1OuterPhase g h0 ν‖ = 1 := by
  simp only [I1OuterPhase]
  rw [norm_prod]
  refine Finset.prod_eq_one ?_
  intro i _
  have h1 : ‖g.ePhase (ν.nTail i)‖ = 1 := norm_ePhase g _
  have h2 : ‖starRingEnd ℂ (g.ePhase (ν.t i * ν.m' i))‖ = 1 := by
    change ‖star (g.ePhase (ν.t i * ν.m' i))‖ = 1
    rw [norm_star, norm_ePhase]
  rw [norm_mul, h1, h2, one_mul]

theorem fibreB_pos (s N A : ℕ) (ν : IntersectionOuter s) (h0 : 0 < s)
    {b : ℕ} (hb : b ∈ fibreB s N A ν h0) : 0 < b := by
  have : b ∈ Finset.Icc 1 N := (Finset.mem_filter.1 hb).1
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 this).1

/-- Outer parameters coming from solutions have positive `Q`. -/
theorem I1Outer_Q_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) : 0 < ν.Q h0 := by
  rcases Finset.mem_image.1 hν with ⟨x, hx, rfl⟩
  simp only [IntersectionOuter.Q]
  refine Finset.prod_pos ?_
  intro i hi
  have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
  have hm := (x.hm i).1
  have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
  have heq : (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i = x.m i := by
    simpa [IntersectionCanon.reconM, hi0] using hrecon
  have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i :=
    lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm)
  exact Nat.pos_of_mul_pos_left hmul_pos

theorem norm_moebius_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  have h : |(μ n : ℤ)| ≤ (1 : ℤ) := abs_moebius_le_one
  have h' : |((μ n : ℤ) : ℝ)| ≤ (1 : ℝ) := by exact_mod_cast h
  simpa [Complex.norm_intCast, Int.cast_abs] using h'

/--
Change of variables `b = d k` (PDF after Möbius):
`∑_{b ∈ B, d|b} fibrePhase(b) = I1BoxSum(..., d)`.
-/
theorem sum_fibreB_dvd_eq_I1BoxSum {d_poly s N A : ℕ} (g : CirclePoly d_poly)
    (ν : IntersectionOuter s) (h0 : 0 < s) (d : ℕ) (hd : 0 < d) :
    (∑ b ∈ (fibreB s N A ν h0).filter fun b => d ∣ b,
        I1FibrePhase g h0 ν b) =
      I1BoxSum g N A h0 ν d := by
  classical
  set LHS := (fibreB s N A ν h0).filter fun b => d ∣ b
  set RHS := (Finset.Icc 1 N).filter fun k => d * k ∈ fibreB s N A ν h0
  refine Finset.sum_bij (fun b _ => b / d) ?_ ?_ ?_ ?_
  · intro b hb
    have hbF := Finset.mem_filter.1 hb
    have hdvd : d ∣ b := hbF.2
    have hbB := hbF.1
    have hbIcc : b ∈ Finset.Icc 1 N := (Finset.mem_filter.1 hbB).1
    have hdiv : d * (b / d) = b := Nat.mul_div_cancel' hdvd
    refine Finset.mem_filter.2 ⟨?_, by simpa [hdiv] using hbB⟩
    have hpos : 0 < b / d :=
      Nat.div_pos (Nat.le_of_dvd (fibreB_pos s N A ν h0 hbB) hdvd) hd
    have hle : b / d ≤ N :=
      Nat.le_trans (Nat.div_le_self b d) (Finset.mem_Icc.1 hbIcc).2
    exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hpos, hle⟩
  · intro b hb b' hb' h
    have hdvd : d ∣ b := (Finset.mem_filter.1 hb).2
    have hdvd' : d ∣ b' := (Finset.mem_filter.1 hb').2
    calc
      b = d * (b / d) := (Nat.mul_div_cancel' hdvd).symm
      _ = d * (b' / d) := by rw [h]
      _ = b' := Nat.mul_div_cancel' hdvd'
  · intro k hk
    refine ⟨d * k, ?_, Nat.mul_div_cancel_left k hd⟩
    have hkF := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨hkF.2, Nat.dvd_mul_right d k⟩
  · intro b hb
    have hdvd : d ∣ b := (Finset.mem_filter.1 hb).2
    simp [Nat.mul_div_cancel' hdvd]

/-- Möbius step ⇒ PDF bound `|S(ν)| ≤ ∑_{d|Q} |S(ν,d)|`. -/
theorem I1FibreSum_norm_le_sum_box {d_poly s N A : ℕ} (g : CirclePoly d_poly)
    (ν : IntersectionOuter s) (h0 : 0 < s) (hQ : 0 < ν.Q h0) :
    ‖I1FibreSum g N A h0 ν‖ ≤
      ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖ := by
  have hBpos : ∀ b ∈ fibreB s N A ν h0, 0 < b := fun b hb =>
    fibreB_pos s N A ν h0 hb
  have hQne : ν.Q h0 ≠ 0 := ne_of_gt hQ
  have hstep :=
    mobius_step_sum_complex (fibreB s N A ν h0) (ν.Q h0)
      (I1FibrePhase g h0 ν) hBpos hQne
  have hG :
      I1FibreSum g N A h0 ν =
        ∑ b ∈ (fibreB s N A ν h0).filter fun b => Nat.gcd b (ν.Q h0) = 1,
          I1FibrePhase g h0 ν b := by
    simp only [I1FibreSum, fibreG_eq_filter_fibreB]
  rw [hG, hstep]
  calc
    ‖∑ e ∈ (ν.Q h0).divisors,
          (μ e : ℂ) *
            ∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
              I1FibrePhase g h0 ν b‖ ≤
        ∑ e ∈ (ν.Q h0).divisors,
          ‖(μ e : ℂ) *
            ∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
              I1FibrePhase g h0 ν b‖ :=
      norm_sum_le _ _
    _ = ∑ e ∈ (ν.Q h0).divisors,
          ‖(μ e : ℂ)‖ *
            ‖∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
              I1FibrePhase g h0 ν b‖ := by
          refine Finset.sum_congr rfl ?_
          intro e _; rw [norm_mul]
    _ ≤ ∑ e ∈ (ν.Q h0).divisors,
          ‖∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
            I1FibrePhase g h0 ν b‖ := by
          refine Finset.sum_le_sum ?_
          intro e _he
          have hμ := norm_moebius_le_one e
          have hsum :=
            norm_nonneg
              (∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
                I1FibrePhase g h0 ν b)
          calc
            ‖(μ e : ℂ)‖ *
                ‖∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
                  I1FibrePhase g h0 ν b‖ ≤
              (1 : ℝ) *
                ‖∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
                  I1FibrePhase g h0 ν b‖ :=
              mul_le_mul_of_nonneg_right hμ hsum
            _ = ‖∑ b ∈ (fibreB s N A ν h0).filter fun b => e ∣ b,
                  I1FibrePhase g h0 ν b‖ := by simp
    _ = ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖ := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have hepos : 0 < e := Nat.pos_of_mem_divisors he
          rw [sum_fibreB_dvd_eq_I1BoxSum g ν h0 e hepos]

/-- Phase weight factors through Lemma 8 reconstruction. -/
theorem phaseWeight_eq_I1_phases {d s N : ℕ} (g : CirclePoly d) (x : Sol s N)
    (h0 : 0 < s) :
    phaseWeight g x =
      I1OuterPhase g h0 (x.toIntersectionCanon h0).outer *
        I1FibrePhase g h0 (x.toIntersectionCanon h0).outer
          (x.toIntersectionCanon h0).b := by
  set c := x.toIntersectionCanon h0
  set ν := c.outer
  set E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  set i0 : Fin s := ⟨0, h0⟩
  have hi0 : i0 ∈ Finset.univ := Finset.mem_univ _
  have hn0 : x.n i0 = c.b * ν.T h0 * ν.n1' := by
    simpa [c, ν, i0, IntersectionCanon.reconN1] using
      (toIntersectionCanon_reconN1 s N x h0).symm
  have hm0 : x.m i0 = c.b * ν.T h0 * ν.m1' := by
    simpa [c, ν, i0, IntersectionCanon.reconM1] using
      (toIntersectionCanon_reconM1 s N x h0).symm
  have hnE : ∀ i ∈ E, x.n i = ν.nTail i := by
    intro i hi
    have hi0' : i ≠ i0 := (Finset.mem_erase.1 hi).1
    simp [ν, c, Sol.toIntersectionCanon, i0, hi0']
  have hmE : ∀ i ∈ E, x.m i = ν.t i * ν.m' i := by
    intro i hi
    have hi0' : i ≠ i0 := (Finset.mem_erase.1 hi).1
    have h := toIntersectionCanon_reconM_tail s N x h0 i hi0'
    simpa [IntersectionCanon.reconM, hi0', ν, c, i0] using h.symm
  have hprod :=
    (Finset.prod_erase_mul (s := Finset.univ) (a := i0)
      (f := fun i => g.ePhase (x.n i) * starRingEnd ℂ (g.ePhase (x.m i)))
      hi0).symm
  simp only [phaseWeight, I1OuterPhase, I1FibrePhase]
  calc
    (∏ i, g.ePhase (x.n i) * starRingEnd ℂ (g.ePhase (x.m i)))
        = (∏ i ∈ Finset.univ.erase i0,
              g.ePhase (x.n i) * starRingEnd ℂ (g.ePhase (x.m i))) *
            (g.ePhase (x.n i0) * starRingEnd ℂ (g.ePhase (x.m i0))) := hprod
    _ = (∏ i ∈ E, g.ePhase (ν.nTail i) *
              starRingEnd ℂ (g.ePhase (ν.t i * ν.m' i))) *
            (g.ePhase (c.b * ν.T h0 * ν.n1') *
              starRingEnd ℂ (g.ePhase (c.b * ν.T h0 * ν.m1'))) := by
          congr 1
          · refine Finset.prod_congr rfl ?_
            intro i hi
            rw [hnE i hi, hmE i hi]
          · rw [hn0, hm0]

/-- Fibre of `I1Support` over a fixed outer parameter. -/
def I1OuterFibre (s N A : ℕ) (I : Finset (Fin s)) (h0 : 0 < s)
    (ν : IntersectionOuter s) : Finset (Sol s N) :=
  (I1Support (s := s) (N := N) A I h0).filter fun x =>
    (x.toIntersectionCanon h0).outer = ν

/-- Group `Sg` by outer parameters (exact finite-sum identity). -/
theorem Sg_I1Support_eq_sum_outer {d s N A : ℕ} (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s) :
    Sg g (I1Support (s := s) (N := N) A I h0) =
      ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
        ∑ x ∈ I1OuterFibre s N A I h0 ν, phaseWeight g x := by
  classical
  set F := I1Support (s := s) (N := N) A I h0
  set key : Sol s N → IntersectionOuter s :=
    fun x => (x.toIntersectionCanon h0).outer
  have hmaps : ∀ x ∈ F, key x ∈ F.image key := fun x hx =>
    Finset.mem_image_of_mem key hx
  have hfib :=
    (Finset.sum_fiberwise_of_maps_to hmaps (phaseWeight g)).symm
  simpa [Sg, F, I1Outer, I1OuterFibre, key] using hfib

/-- Triangle inequality after grouping by outer parameters. -/
theorem I1_norm_le_sum_outer_fibres {d s N A : ℕ} (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s) :
    ‖Sg g (I1Support (s := s) (N := N) A I h0)‖ ≤
      ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
        ‖∑ x ∈ I1OuterFibre s N A I h0 ν, phaseWeight g x‖ := by
  rw [Sg_I1Support_eq_sum_outer g I h0]
  exact norm_sum_le _ _

/-- Canon of a point in an outer fibre is `{b, ν}`. -/
theorem I1OuterFibre_canon {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s} {x : Sol s N}
    (hx : x ∈ I1OuterFibre s N A I h0 ν) :
    x.toIntersectionCanon h0 = { b := (x.toIntersectionCanon h0).b, outer := ν } := by
  have houter : (x.toIntersectionCanon h0).outer = ν :=
    (Finset.mem_filter.1 hx).2
  revert houter
  cases x.toIntersectionCanon h0 with
  | mk b outer =>
    intro houter
    cases houter
    rfl

/-- Points in an outer fibre have fibre variable in `fibreG`. -/
theorem I1OuterFibre_b_mem_fibreG {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hA : 1 ≤ A)
    {ν : IntersectionOuter s} {x : Sol s N}
    (hx : x ∈ I1OuterFibre s N A I h0 ν) :
    (x.toIntersectionCanon h0).b ∈ fibreG s N A ν h0 := by
  have hxF := (Finset.mem_filter.1 hx).1
  have hmem : ∀ i ∈ I, x.memF A i h0 := (Finset.mem_filter.1 hxF).2.1
  have houter : (x.toIntersectionCanon h0).outer = ν :=
    (Finset.mem_filter.1 hx).2
  have hb :=
    toIntersectionCanon_mem_fibreG s N A x h0 hA (hmem _ hI0)
  simpa [houter] using hb

/--
Reconstruct a unique off-diagonal intersection point from `(b, ν)`.
-/
theorem I1_exists_of_mem_fibreG {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) (_hA : 1 ≤ A)
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0)
    {b : ℕ} (hb : b ∈ fibreG s N A ν h0) :
    ∃ y : Sol s N,
      y ∈ I1OuterFibre s N A I h0 ν ∧
        (y.toIntersectionCanon h0).b = b := by
  rcases Finset.mem_image.1 hν with ⟨x0, hx0, rfl⟩
  have hmem0 : ∀ i ∈ I, x0.memF A i h0 := (Finset.mem_filter.1 hx0).2.1
  obtain ⟨y, hcan, hmem⟩ :=
    intersection_param_fibre_converse s N A I h0 hI0 hIcard x0 hmem0 b hb
  have houter : (y.toIntersectionCanon h0).outer =
      (x0.toIntersectionCanon h0).outer := by simp [hcan]
  have hb_y : (y.toIntersectionCanon h0).b = b := by simp [hcan]
  have hn1'ne := I1Support_n1'_ne_m1' hx0
  have hbIcc : b ∈ Finset.Icc 1 N := (Finset.mem_filter.1 hb).1
  have hbpos : 0 < b :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 hbIcc).1
  have hTpos : 0 < (x0.toIntersectionCanon h0).outer.T h0 := by
    have hpos := toIntersectionCanon_b_mul_T_pos s N x0 h0
    exact Nat.pos_of_mul_pos_left hpos
  have hond : ¬ y.onDiag h0 := by
    intro hdiag
    have hn := (toIntersectionCanon_reconN1 s N y h0).symm
    have hm := (toIntersectionCanon_reconM1 s N y h0).symm
    -- `y.n₀ = b T n₁'` and `y.m₀ = b T m₁'`
    have heq :
        b * (x0.toIntersectionCanon h0).outer.T h0 *
            (x0.toIntersectionCanon h0).outer.n1' =
          b * (x0.toIntersectionCanon h0).outer.T h0 *
            (x0.toIntersectionCanon h0).outer.m1' := by
      simp only [Sol.onDiag] at hdiag
      have hn' :
          y.n ⟨0, h0⟩ =
            b * (x0.toIntersectionCanon h0).outer.T h0 *
              (x0.toIntersectionCanon h0).outer.n1' := by
        simpa [hcan, IntersectionCanon.reconN1] using hn
      have hm' :
          y.m ⟨0, h0⟩ =
            b * (x0.toIntersectionCanon h0).outer.T h0 *
              (x0.toIntersectionCanon h0).outer.m1' := by
        simpa [hcan, IntersectionCanon.reconM1] using hm
      calc
        b * (x0.toIntersectionCanon h0).outer.T h0 *
            (x0.toIntersectionCanon h0).outer.n1'
            = y.n ⟨0, h0⟩ := hn'.symm
        _ = y.m ⟨0, h0⟩ := hdiag
        _ = b * (x0.toIntersectionCanon h0).outer.T h0 *
              (x0.toIntersectionCanon h0).outer.m1' := hm'
    have : (x0.toIntersectionCanon h0).outer.n1' =
        (x0.toIntersectionCanon h0).outer.m1' :=
      Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hbpos hTpos) heq
    exact hn1'ne this
  refine ⟨y, ?_, hb_y⟩
  refine Finset.mem_filter.2 ⟨?_, houter⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hmem, hond⟩⟩

/-- Local `Sol` extensionality (same statement as elsewhere in the project). -/
theorem sol_ext {s N : ℕ} {x y : Sol s N}
    (hn : x.n = y.n) (hm : x.m = y.m) : x = y := by
  cases x; cases y; cases hn; cases hm; rfl

/-- Two solutions with the same canonical data are equal. -/
theorem sol_eq_of_toIntersectionCanon_eq {s N : ℕ} {h0 : 0 < s}
    {x y : Sol s N}
    (h : x.toIntersectionCanon h0 = y.toIntersectionCanon h0) : x = y := by
  refine sol_ext ?_ ?_
  · funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      calc
        x.n ⟨0, h0⟩ = (x.toIntersectionCanon h0).reconN1 h0 :=
          (toIntersectionCanon_reconN1 s N x h0).symm
        _ = (y.toIntersectionCanon h0).reconN1 h0 := by rw [h]
        _ = y.n ⟨0, h0⟩ := toIntersectionCanon_reconN1 s N y h0
    · have hn_x : x.n i = (x.toIntersectionCanon h0).outer.nTail i := by
        simp [Sol.toIntersectionCanon, hi0]
      have hn_y : y.n i = (y.toIntersectionCanon h0).outer.nTail i := by
        simp [Sol.toIntersectionCanon, hi0]
      simp [hn_x, hn_y, h]
  · funext i
    by_cases hi0 : i = ⟨0, h0⟩
    · subst hi0
      calc
        x.m ⟨0, h0⟩ = (x.toIntersectionCanon h0).reconM1 h0 :=
          (toIntersectionCanon_reconM1 s N x h0).symm
        _ = (y.toIntersectionCanon h0).reconM1 h0 := by rw [h]
        _ = y.m ⟨0, h0⟩ := toIntersectionCanon_reconM1 s N y h0
    · have hx := toIntersectionCanon_reconM_tail s N x h0 i hi0
      have hy := toIntersectionCanon_reconM_tail s N y h0 i hi0
      simp [← hx, ← hy, h]

/--
Identify each outer fibre sum with `Ω(ν) · S(ν)` (PDF eq:I1-outer-decomposition).
-/
theorem I1_outer_fibre_sum_eq {d s N A : ℕ} (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s)
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) (hA : 1 ≤ A)
    (ν : IntersectionOuter s)
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    (∑ x ∈ I1OuterFibre s N A I h0 ν, phaseWeight g x) =
      I1OuterPhase g h0 ν * I1FibreSum g N A h0 ν := by
  classical
  set Fibre := I1OuterFibre s N A I h0 ν
  set G := fibreG s N A ν h0
  -- Phase factorisation on the fibre.
  have hphase :
      ∀ x ∈ Fibre,
        phaseWeight g x =
          I1OuterPhase g h0 ν * I1FibrePhase g h0 ν (x.toIntersectionCanon h0).b := by
    intro x hx
    have houter : (x.toIntersectionCanon h0).outer = ν :=
      (Finset.mem_filter.1 hx).2
    simpa [houter] using phaseWeight_eq_I1_phases g x h0
  -- Bijection `Fibre → G` by the fibre variable `b`.
  have hsum :
      (∑ x ∈ Fibre, I1FibrePhase g h0 ν (x.toIntersectionCanon h0).b) =
        ∑ b ∈ G, I1FibrePhase g h0 ν b := by
    refine Finset.sum_bij (fun x _ => (x.toIntersectionCanon h0).b) ?_ ?_ ?_ ?_
    · intro x hx
      exact I1OuterFibre_b_mem_fibreG hI0 hA hx
    · intro x hx y hy hxy
      have hxcan := I1OuterFibre_canon hx
      have hycan := I1OuterFibre_canon hy
      have hcan : x.toIntersectionCanon h0 = y.toIntersectionCanon h0 := by
        rw [hxcan, hycan, hxy]
      exact sol_eq_of_toIntersectionCanon_eq hcan
    · intro b hb
      obtain ⟨y, hy, hb_y⟩ := I1_exists_of_mem_fibreG hI0 hIcard hA hν hb
      exact ⟨y, hy, hb_y⟩
    · intro x _hx; rfl
  calc
    (∑ x ∈ Fibre, phaseWeight g x)
        = ∑ x ∈ Fibre,
            I1OuterPhase g h0 ν *
              I1FibrePhase g h0 ν (x.toIntersectionCanon h0).b := by
          refine Finset.sum_congr rfl hphase
    _ = I1OuterPhase g h0 ν *
          ∑ x ∈ Fibre, I1FibrePhase g h0 ν (x.toIntersectionCanon h0).b := by
          simp [Finset.mul_sum]
    _ = I1OuterPhase g h0 ν * ∑ b ∈ G, I1FibrePhase g h0 ν b := by rw [hsum]
    _ = I1OuterPhase g h0 ν * I1FibreSum g N A h0 ν := by
          simp [I1FibreSum, G]

/--
Group by outer parameters (PDF eq:I1-outer-decomposition + triangle).
-/
theorem I1_norm_le_sum_fibre {d s N A : ℕ} (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s)
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) (hA : 1 ≤ A) :
    ‖Sg g (I1Support (s := s) (N := N) A I h0)‖ ≤
      ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
        ‖I1FibreSum g N A h0 ν‖ := by
  refine le_trans (I1_norm_le_sum_outer_fibres g I h0) ?_
  refine Finset.sum_le_sum ?_
  intro ν hν
  have heq := I1_outer_fibre_sum_eq g I h0 hI0 hIcard hA ν hν
  rw [heq, norm_mul, norm_I1OuterPhase, one_mul]

/-- Absolute double sum over outer parameters and Möbius divisors. -/
def I1AbsDoubleSum (d s N A : ℕ) (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
    ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖

theorem I1_norm_le_absDoubleSum {d s N A : ℕ} (g : CirclePoly d)
    (I : Finset (Fin s)) (h0 : 0 < s)
    (hI0 : (⟨0, h0⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card) (hA : 1 ≤ A) :
    ‖Sg g (I1Support (s := s) (N := N) A I h0)‖ ≤
      I1AbsDoubleSum d s N A g I h0 := by
  refine le_trans (I1_norm_le_sum_fibre g I h0 hI0 hIcard hA) ?_
  simp only [I1AbsDoubleSum]
  gcongr with ν hν
  exact I1FibreSum_norm_le_sum_box g ν h0 (I1Outer_Q_pos hν)

/-- Piece I region: `T ≥ δ⁻¹` (equivalently `1 ≤ δ T`). -/
def I1PieceISum (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => (1 : ℝ) ≤ δ * (ν.T h0 : ℝ),
    ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖

/-- Piece II region: `d ≥ δ⁻¹`. -/
def I1PieceIISum (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
    ∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
      ‖I1BoxSum g N A h0 ν e‖

/-- Piece III region: `T,d < δ⁻¹`. -/
def I1PieceIIISum (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => δ * (ν.T h0 : ℝ) < 1,
    ∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => δ * (e : ℝ) < 1,
      ‖I1BoxSum g N A h0 ν e‖

/--
Cover inequality for the three-piece partition (nonnegative summands;
harmless double counting when both `T` and `d` are large).
-/
theorem I1AbsDoubleSum_le_three_pieces (d s N A : ℕ) (g : CirclePoly d)
    (δ : ℝ) (I : Finset (Fin s)) (h0 : 0 < s) (_hδ : 0 < δ) :
    I1AbsDoubleSum d s N A g I h0 ≤
      I1PieceISum d s N A g δ I h0 +
        I1PieceIISum d s N A g δ I h0 +
        I1PieceIIISum d s N A g δ I h0 := by
  classical
  -- For each fixed outer ν, compare the divisor sum with the three pieces.
  have hν :
      ∀ ν ∈ I1Outer (s := s) (N := N) A I h0,
        (∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖) ≤
          (if (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) then
              ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖
            else 0) +
            (∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
              ‖I1BoxSum g N A h0 ν e‖) +
            (if δ * (ν.T h0 : ℝ) < 1 then
              ∑ e ∈ (ν.Q h0).divisors.filter
                  fun e : ℕ => δ * (e : ℝ) < 1,
                ‖I1BoxSum g N A h0 ν e‖
            else 0) := by
    intro ν _hνmem
    set a : ℕ → ℝ := fun e => ‖I1BoxSum g N A h0 ν e‖
    have ha0 : ∀ e, 0 ≤ a e := fun _ => norm_nonneg _
    by_cases hT : (1 : ℝ) ≤ δ * (ν.T h0 : ℝ)
    · -- Large T: LHS is the Piece I contribution; other pieces ≥ 0.
      have hTnot : ¬ δ * (ν.T h0 : ℝ) < 1 := not_lt.2 hT
      have hII :
          0 ≤ ∑ e ∈ (ν.Q h0).divisors.filter
              fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ), a e :=
        Finset.sum_nonneg fun e _ => ha0 e
      -- Unfold the ite using `hT` / `hTnot`.
      have hform :
          (if (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) then
              ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖
            else 0) +
            (∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
              ‖I1BoxSum g N A h0 ν e‖) +
            (if δ * (ν.T h0 : ℝ) < 1 then
              ∑ e ∈ (ν.Q h0).divisors.filter
                  fun e : ℕ => δ * (e : ℝ) < 1,
                ‖I1BoxSum g N A h0 ν e‖
            else 0) =
          (∑ e ∈ (ν.Q h0).divisors, a e) +
            (∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ), a e) +
            0 := by
        simp [hT, hTnot, a]
      rw [hform, add_zero]
      exact le_add_of_nonneg_right hII
    · -- Small T: partition divisors into large-d and small-d.
      have hTlt : δ * (ν.T h0 : ℝ) < 1 := lt_of_not_ge hT
      set SII :=
        (ν.Q h0).divisors.filter fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ)
      set SIII :=
        (ν.Q h0).divisors.filter fun e : ℕ => δ * (e : ℝ) < 1
      have hunion : (ν.Q h0).divisors = SII ∪ SIII := by
        ext e
        simp only [SII, SIII, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro he
          by_cases hde : (1 : ℝ) ≤ δ * (e : ℝ)
          · exact Or.inl ⟨he, hde⟩
          · exact Or.inr ⟨he, lt_of_not_ge hde⟩
        · intro h
          rcases h with ⟨he, _⟩ | ⟨he, _⟩ <;> exact he
      have hdj : Disjoint SII SIII := by
        refine Finset.disjoint_left.2 ?_
        intro e heII heIII
        exact (not_lt.2 (Finset.mem_filter.1 heII).2)
          (Finset.mem_filter.1 heIII).2
      have hsum :
          (∑ e ∈ (ν.Q h0).divisors, a e) =
            (∑ e ∈ SII, a e) + (∑ e ∈ SIII, a e) := by
        rw [hunion, Finset.sum_union hdj]
      have hform :
          (if (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) then
              ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖
            else 0) +
            (∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
              ‖I1BoxSum g N A h0 ν e‖) +
            (if δ * (ν.T h0 : ℝ) < 1 then
              ∑ e ∈ (ν.Q h0).divisors.filter
                  fun e : ℕ => δ * (e : ℝ) < 1,
                ‖I1BoxSum g N A h0 ν e‖
            else 0) =
          0 + (∑ e ∈ SII, a e) + (∑ e ∈ SIII, a e) := by
        simp [hT, hTlt, a, SII, SIII]
      rw [hform, hsum, zero_add]
  -- Sum over ν.
  calc
    I1AbsDoubleSum d s N A g I h0 =
        ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
          ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖ := rfl
    _ ≤ ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
          ((if (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) then
              ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖
            else 0) +
            (∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
              ‖I1BoxSum g N A h0 ν e‖) +
            (if δ * (ν.T h0 : ℝ) < 1 then
              ∑ e ∈ (ν.Q h0).divisors.filter
                  fun e : ℕ => δ * (e : ℝ) < 1,
                ‖I1BoxSum g N A h0 ν e‖
            else 0)) :=
      Finset.sum_le_sum fun ν hνmem => hν ν hνmem
    _ = (∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
            if (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) then
              ∑ e ∈ (ν.Q h0).divisors, ‖I1BoxSum g N A h0 ν e‖
            else 0) +
          (∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
            ∑ e ∈ (ν.Q h0).divisors.filter
                fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
              ‖I1BoxSum g N A h0 ν e‖) +
          (∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
            if δ * (ν.T h0 : ℝ) < 1 then
              ∑ e ∈ (ν.Q h0).divisors.filter
                  fun e : ℕ => δ * (e : ℝ) < 1,
                ‖I1BoxSum g N A h0 ν e‖
            else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = I1PieceISum d s N A g δ I h0 +
          I1PieceIISum d s N A g δ I h0 +
          I1PieceIIISum d s N A g δ I h0 := by
      simp only [I1PieceISum, I1PieceIISum, I1PieceIIISum, Finset.sum_filter]

/-! ### Piece I / II: trivial bound + divisor counting -/

theorem norm_I1FibrePhase {d s : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) (b : ℕ) : ‖I1FibrePhase g h0 ν b‖ = 1 := by
  simp only [I1FibrePhase]
  have h1 : ‖g.ePhase (b * ν.T h0 * ν.n1')‖ = 1 := norm_ePhase g _
  have h2 : ‖starRingEnd ℂ (g.ePhase (b * ν.T h0 * ν.m1'))‖ = 1 := by
    change ‖star (g.ePhase (b * ν.T h0 * ν.m1'))‖ = 1
    rw [norm_star, norm_ePhase]
  rw [norm_mul, h1, h2, one_mul]

/-- Trivial bound `|S(ν,d)| ≤ # scaled box`. -/
theorem norm_I1BoxSum_le_card {d s N A : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (ν : IntersectionOuter s) (D : ℕ) :
    ‖I1BoxSum g N A h0 ν D‖ ≤
      (((Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0).card : ℝ) := by
  simp only [I1BoxSum]
  calc
    ‖∑ k ∈ (Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0,
          I1FibrePhase g h0 ν (D * k)‖ ≤
        ∑ k ∈ (Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0,
          ‖I1FibrePhase g h0 ν (D * k)‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ (Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0,
          (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro k _; exact norm_I1FibrePhase g h0 ν _
    _ = (((Finset.Icc 1 N).filter fun k => D * k ∈ fibreB s N A ν h0).card : ℝ) := by
          simp

/-- Absolute card sum underlying Piece I. -/
def I1PieceICardSum (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => (1 : ℝ) ≤ δ * (ν.T h0 : ℝ),
    ∑ e ∈ (ν.Q h0).divisors,
      (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ)

/-- Absolute card sum underlying Piece II. -/
def I1PieceIICardSum (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ I1Outer (s := s) (N := N) A I h0,
    ∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => (1 : ℝ) ≤ δ * (e : ℝ),
      (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ)

theorem I1PieceISum_le_cardSum {d s N A : ℕ} (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) :
    I1PieceISum d s N A g δ I h0 ≤ I1PieceICardSum s N A δ I h0 := by
  simp only [I1PieceISum, I1PieceICardSum]
  gcongr with ν _hν e _he
  exact norm_I1BoxSum_le_card g h0 ν e

theorem I1PieceIISum_le_cardSum {d s N A : ℕ} (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) :
    I1PieceIISum d s N A g δ I h0 ≤ I1PieceIICardSum s N A δ I h0 := by
  simp only [I1PieceIISum, I1PieceIICardSum]
  gcongr with ν _hν e _he
  exact norm_I1BoxSum_le_card g h0 ν e

-- Piece I / II card majorants are proved in `I1PieceIAssemble.lean`.

/--
Full weighted sum from PDF Lemma 1 / Abel (Proof-layer packaging).
-/
theorem tau_sq_weighted_sum_bound (N ℓ : ℕ) (hN : 3 ≤ N) (hℓ : 1 ≤ ℓ) :
    (∑ n ∈ Finset.Icc 1 N, (tau ℓ n : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      5 * (2 * Real.log N) ^ (ℓ ^ 2) := by
  have hA : 0 < (1 : ℕ) := zero_lt_one
  have hAN : 1 < N := lt_of_lt_of_le (by decide : 1 < 3) hN
  have htail :=
    divisor_tail_bound N ℓ 1 hN hℓ hA hAN
  simp only [Nat.cast_one, div_one] at htail
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3)
      (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hN))
  have h1log : (1 : ℝ) ≤ 2 * Real.log N := by
    nlinarith
  have hlogpos : 0 < 2 * Real.log N :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hlogN)
  have hsq : ℓ ^ 2 - 1 + 1 = ℓ ^ 2 := by
    have hle : 1 ≤ ℓ ^ 2 :=
      calc
        1 ≤ ℓ := hℓ
        _ ≤ ℓ ^ 2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) ℓ
    omega
  calc
    (∑ n ∈ Finset.Icc 1 N, (tau ℓ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
        ≤ 5 * (2 * Real.log N) ^ (ℓ ^ 2 - 1) := htail
    _ ≤ 5 * (2 * Real.log N) ^ (ℓ ^ 2) := by
      have hx : 0 ≤ (2 * Real.log N) ^ (ℓ ^ 2 - 1) :=
        pow_nonneg (le_of_lt hlogpos) _
      have hpow : (2 * Real.log N) ^ (ℓ ^ 2 - 1) ≤
          (2 * Real.log N) ^ (ℓ ^ 2) := by
        calc (2 * Real.log N) ^ (ℓ ^ 2 - 1)
            ≤ (2 * Real.log N) * (2 * Real.log N) ^ (ℓ ^ 2 - 1) :=
              le_mul_of_one_le_left hx h1log
          _ = (2 * Real.log N) ^ (ℓ ^ 2 - 1 + 1) :=
              (pow_succ' (2 * Real.log N) (ℓ ^ 2 - 1)).symm
          _ = (2 * Real.log N) ^ (ℓ ^ 2) := by rw [hsq]
      exact mul_le_mul_of_nonneg_left hpow (by norm_num)

/-! ### Piece III — scaled `J1` + small `(T,d)` sum -/

/--
PDF polylog from the scaled `J1` bound `eq:piece-III-fixed`.
The second summand covers the harmonic × Cauchy--Schwarz factor
`(log N)^{(s-1)²} (2 log N)^{(s-1)²}` on the exceptional row.
-/
noncomputable def I1PieceIIIPolylog (N s : ℕ) : ℝ :=
  (Real.log N) ^ (s * (s - 1)) +
    (Real.log N) ^ ((s - 1) * (s - 1)) *
      (2 * Real.log N) ^ ((s - 1) * (s - 1))

/--
Weight arising after summing the scaled `J1` bound over
`T,d < δ⁻¹` (PDF after `eq:piece-III-fixed`):
`(∑_{T: δT<1} τ_{s-1}(T)/T) (∑_{d: δd<1} 1/d)`.
-/
noncomputable def I1PieceIIITdWeight (N s : ℕ) (δ : ℝ) : ℝ :=
  (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
      if δ * (T : ℝ) < 1 then (tau (s - 1) T : ℝ) / (T : ℝ) else 0) *
    (∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
      if δ * (e : ℝ) < 1 then (1 : ℝ) / (e : ℝ) else 0)

/-- Absolute card sum underlying Piece III. -/
def I1PieceIIICardSum (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s)) (h0 : 0 < s) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => δ * (ν.T h0 : ℝ) < 1,
    ∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => δ * (e : ℝ) < 1,
      (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ)

theorem I1PieceIIISum_le_cardSum {d s N A : ℕ} (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) :
    I1PieceIIISum d s N A g δ I h0 ≤ I1PieceIIICardSum s N A δ I h0 := by
  simp only [I1PieceIIISum, I1PieceIIICardSum]
  gcongr with ν _hν e _he
  exact norm_I1BoxSum_le_card g h0 ν e

-- Diophantine transfer lives in `I1PieceIIIDio` (imported by ScaledJ1).
/--
PDF weighted double sum after summing fixed-`(T,d)` scaled `J1` bounds:
`∑∑ τ_{s-1}(T) · δ^{1/2} N^s/(Td) · polylog = δ^{1/2} N^s · polylog · TdWeight`.
-/
theorem I1_piece_III_factor_double_sum (N s : ℕ) (δ : ℝ) :
    (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
      ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
        if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
          (tau (s - 1) T : ℝ) *
            (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) * I1PieceIIIPolylog N s)
        else 0) =
      Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ := by
  classical
  set S := Finset.Icc 1 (N ^ (s - 1))
  set poly := I1PieceIIIPolylog N s
  set f : ℕ → ℝ := fun T =>
    if δ * (T : ℝ) < 1 then (tau (s - 1) T : ℝ) / (T : ℝ) else 0
  set gfun : ℕ → ℝ := fun e =>
    if δ * (e : ℝ) < 1 then (1 : ℝ) / (e : ℝ) else 0
  set c := Real.sqrt δ * (N : ℝ) ^ s * poly
  have hpoint :
      ∀ T ∈ S, ∀ e ∈ S,
        (if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
            (tau (s - 1) T : ℝ) *
              (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) * poly)
          else 0) =
          c * f T * gfun e := by
    intro T hT e he
    have hTpos : (0 : ℝ) < T := by
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 hT).1)
    have hepos : (0 : ℝ) < e := by
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 he).1)
    dsimp only [f, gfun, c]
    by_cases h1 : δ * (T : ℝ) < 1
    · by_cases h2 : δ * (e : ℝ) < 1
      · simp only [h1, h2, and_self, ↓reduceIte]
        field_simp [ne_of_gt hTpos, ne_of_gt hepos]
      · simp [h1, h2]
    · simp [h1]
  have hrewrite :
      (∑ T ∈ S, ∑ e ∈ S,
          if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
            (tau (s - 1) T : ℝ) *
              (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) * poly)
          else 0) =
        ∑ T ∈ S, ∑ e ∈ S, c * f T * gfun e := by
    refine Finset.sum_congr rfl fun T hT =>
      Finset.sum_congr rfl fun e he => hpoint T hT e he
  have hfactor :
      ∑ T ∈ S, ∑ e ∈ S, c * f T * gfun e =
        c * (∑ T ∈ S, f T) * (∑ e ∈ S, gfun e) := by
    have hinner :
        ∀ T, ∑ e ∈ S, (c * f T) * gfun e = (c * f T) * ∑ e ∈ S, gfun e := by
      intro T
      exact (Finset.mul_sum (s := S) (f := gfun) (a := c * f T)).symm
    calc
      ∑ T ∈ S, ∑ e ∈ S, c * f T * gfun e
          = ∑ T ∈ S, ∑ e ∈ S, (c * f T) * gfun e := by
            refine Finset.sum_congr rfl fun T _ =>
              Finset.sum_congr rfl fun e _ => by ring
      _ = ∑ T ∈ S, (c * f T) * ∑ e ∈ S, gfun e := by
            refine Finset.sum_congr rfl fun T _ => hinner T
      _ = (∑ T ∈ S, c * f T) * ∑ e ∈ S, gfun e := by
            rw [← Finset.sum_mul]
      _ = (c * ∑ T ∈ S, f T) * ∑ e ∈ S, gfun e := by
            congr 1
            exact (Finset.mul_sum (s := S) (f := f) (a := c)).symm
      _ = c * (∑ T ∈ S, f T) * (∑ e ∈ S, gfun e) := by ring
  calc
    (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
      ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
        if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
          (tau (s - 1) T : ℝ) *
            (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) * I1PieceIIIPolylog N s)
        else 0)
        = ∑ T ∈ S, ∑ e ∈ S, c * f T * gfun e := by
          simpa [S, poly] using hrewrite
    _ = c * (∑ T ∈ S, f T) * (∑ e ∈ S, gfun e) := hfactor
    _ = Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ := by
          simp only [c, f, gfun, S, I1PieceIIITdWeight, poly, mul_assoc]

/-! ### Piece III: fixed `(T,e)` blocks (combinatorial shell; analytic core axiomatised) -/

/--
Piece III contribution at fixed product `T = T(ν)` and Möbius index `e`.
-/
def I1PieceIIIFixedSum (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => ν.T h0 = T ∧ δ * (ν.T h0 : ℝ) < 1,
    if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
      ‖I1BoxSum g N A h0 ν e‖ else 0

theorem I1PieceIIIFixedSum_nonneg (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (T e : ℕ) :
    0 ≤ I1PieceIIIFixedSum d s N A g δ I h0 T e := by
  classical
  simp only [I1PieceIIIFixedSum]
  refine Finset.sum_nonneg fun ν _ => ?_
  by_cases h : e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1
  · simp only [h, ↓reduceIte]; exact norm_nonneg _
  · simp only [h, ↓reduceIte, le_rfl]

/-- Outer parameters from solutions satisfy `1 ≤ T(ν) ≤ N^{s-1}`. -/
theorem I1Outer_T_mem_Icc {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.T h0 ∈ Finset.Icc 1 (N ^ (s - 1)) := by
  classical
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  set E : Finset (Fin s) := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  have hcard : E.card = s - 1 := by
    simp [E, Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin]
  have ht_le : ∀ i ∈ E, (x.toIntersectionCanon h0).outer.t i ≤ N := by
    intro i hi
    have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
    have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
    have heq : (x.toIntersectionCanon h0).outer.t i *
        (x.toIntersectionCanon h0).outer.m' i = x.m i := by
      simpa [IntersectionCanon.reconM, hi0] using hrecon
    have hm1 : 1 ≤ x.m i := (x.hm i).1
    have hmN : x.m i ≤ N := (x.hm i).2
    have hm'pos : 0 < (x.toIntersectionCanon h0).outer.m' i := by
      have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
          (x.toIntersectionCanon h0).outer.m' i :=
        lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm1)
      exact Nat.pos_of_mul_pos_left hmul_pos
    have htle : (x.toIntersectionCanon h0).outer.t i ≤
        (x.toIntersectionCanon h0).outer.t i *
          (x.toIntersectionCanon h0).outer.m' i :=
      Nat.le_mul_of_pos_right _ hm'pos
    exact htle.trans (by simpa [heq] using hmN)
  have hTpos : 0 < (x.toIntersectionCanon h0).outer.T h0 := by
    simp only [IntersectionOuter.T]
    refine Finset.prod_pos fun i hi => ?_
    have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
    have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
    have heq : (x.toIntersectionCanon h0).outer.t i *
        (x.toIntersectionCanon h0).outer.m' i = x.m i := by
      simpa [IntersectionCanon.reconM, hi0] using hrecon
    have hm1 : 1 ≤ x.m i := (x.hm i).1
    have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
        (x.toIntersectionCanon h0).outer.m' i :=
      lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm1)
    exact Nat.pos_of_mul_pos_right hmul_pos
  have hTle : (x.toIntersectionCanon h0).outer.T h0 ≤ N ^ (s - 1) := by
    simp only [IntersectionOuter.T]
    have hle :
        ∏ i ∈ E, (x.toIntersectionCanon h0).outer.t i ≤ ∏ i ∈ E, N :=
      Finset.prod_le_prod' fun i hi => ht_le i hi
    simpa [Finset.prod_const, hcard] using hle
  exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hTpos, hTle⟩

/-- Outer `Q(ν)` satisfies `1 ≤ Q(ν) ≤ N^{s-1}`. -/
theorem I1Outer_Q_mem_Icc {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.Q h0 ∈ Finset.Icc 1 (N ^ (s - 1)) := by
  classical
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  set E : Finset (Fin s) := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  have hcard : E.card = s - 1 := by
    simp [E, Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin]
  have hm'_le : ∀ i ∈ E, (x.toIntersectionCanon h0).outer.m' i ≤ N := by
    intro i hi
    have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
    have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
    have heq : (x.toIntersectionCanon h0).outer.t i *
        (x.toIntersectionCanon h0).outer.m' i = x.m i := by
      simpa [IntersectionCanon.reconM, hi0] using hrecon
    have hm1 : 1 ≤ x.m i := (x.hm i).1
    have hmN : x.m i ≤ N := (x.hm i).2
    have htpos : 0 < (x.toIntersectionCanon h0).outer.t i := by
      have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
          (x.toIntersectionCanon h0).outer.m' i :=
        lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm1)
      exact Nat.pos_of_mul_pos_right hmul_pos
    have hm'le : (x.toIntersectionCanon h0).outer.m' i ≤
        (x.toIntersectionCanon h0).outer.t i *
          (x.toIntersectionCanon h0).outer.m' i :=
      Nat.le_mul_of_pos_left _ htpos
    exact hm'le.trans (by simpa [heq] using hmN)
  have hQpos := I1Outer_Q_pos hν
  have hQle : (x.toIntersectionCanon h0).outer.Q h0 ≤ N ^ (s - 1) := by
    simp only [IntersectionOuter.Q]
    have hle :
        ∏ i ∈ E, (x.toIntersectionCanon h0).outer.m' i ≤ ∏ i ∈ E, N :=
      Finset.prod_le_prod' fun i hi => hm'_le i hi
    simpa [Finset.prod_const, hcard] using hle
  exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hQpos, hQle⟩

theorem I1Outer_divisor_mem_Icc {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {e : ℕ}
    (he : e ∈ (ν.Q h0).divisors) :
    e ∈ Finset.Icc 1 (N ^ (s - 1)) := by
  have hQ := I1Outer_Q_mem_Icc hν
  have hqpos : 0 < ν.Q h0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 hQ).1
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have hele : e ≤ ν.Q h0 := Nat.le_of_dvd hqpos (Nat.dvd_of_mem_divisors he)
  exact Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hepos,
    hele.trans (Finset.mem_Icc.1 hQ).2⟩

/--
Regroup Piece III by the values `(T(ν), e)` over the PDF range
`1 ≤ T,e ≤ N^{s-1}`.
-/
theorem I1PieceIIISum_eq_sum_fixed (d s N A : ℕ) (g : CirclePoly d) (δ : ℝ)
    (I : Finset (Fin s)) (h0 : 0 < s) (_hN : 3 ≤ N) :
    I1PieceIIISum d s N A g δ I h0 =
      ∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
        ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          I1PieceIIIFixedSum d s N A g δ I h0 T e := by
  classical
  set Outer := I1Outer (s := s) (N := N) A I h0
  set Srange := Finset.Icc 1 (N ^ (s - 1))
  set F := Outer.filter fun ν => δ * (ν.T h0 : ℝ) < 1
  have hTmem : ∀ ν ∈ F, ν.T h0 ∈ Srange := by
    intro ν hν
    exact I1Outer_T_mem_Icc (Finset.mem_filter.1 hν).1
  have hνsum :
      ∀ ν ∈ F,
        (∑ e ∈ (ν.Q h0).divisors.filter fun e : ℕ => δ * (e : ℝ) < 1,
            ‖I1BoxSum g N A h0 ν e‖) =
          ∑ e ∈ Srange,
            if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
              ‖I1BoxSum g N A h0 ν e‖ else 0 := by
    intro ν hν
    have hνOuter : ν ∈ Outer := (Finset.mem_filter.1 hν).1
    have hsubset : (ν.Q h0).divisors ⊆ Srange := fun e he =>
      I1Outer_divisor_mem_Icc hνOuter he
    have hset :
        (ν.Q h0).divisors.filter (fun e : ℕ => δ * (e : ℝ) < 1) =
          Srange.filter fun e : ℕ =>
            e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 := by
      ext e
      constructor
      · intro he
        refine Finset.mem_filter.2 ?_
        have hediv : e ∈ (ν.Q h0).divisors := (Finset.mem_filter.1 he).1
        exact ⟨hsubset hediv, hediv, (Finset.mem_filter.1 he).2⟩
      · intro he
        exact Finset.mem_filter.2
          ⟨(Finset.mem_filter.1 he).2.1, (Finset.mem_filter.1 he).2.2⟩
    rw [hset, Finset.sum_filter]
  have hF_filter :
      ∀ T : ℕ,
        F.filter (fun ν => ν.T h0 = T) =
          Outer.filter fun ν => ν.T h0 = T ∧ δ * (ν.T h0 : ℝ) < 1 := by
    intro T
    ext ν
    simp only [F, Outer, Finset.mem_filter]
    tauto
  calc
    I1PieceIIISum d s N A g δ I h0
        = ∑ ν ∈ F, ∑ e ∈ (ν.Q h0).divisors.filter
            fun e : ℕ => δ * (e : ℝ) < 1, ‖I1BoxSum g N A h0 ν e‖ := by
          simp only [I1PieceIIISum, F, Outer]
    _ = ∑ ν ∈ F, ∑ e ∈ Srange,
          if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
            ‖I1BoxSum g N A h0 ν e‖ else 0 := by
          refine Finset.sum_congr rfl fun ν hν => hνsum ν hν
    _ = ∑ e ∈ Srange, ∑ ν ∈ F,
          if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
            ‖I1BoxSum g N A h0 ν e‖ else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ Srange, ∑ T ∈ Srange, ∑ ν ∈ F.filter fun ν => ν.T h0 = T,
          if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
            ‖I1BoxSum g N A h0 ν e‖ else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          exact
            (Finset.sum_fiberwise_of_maps_to (g := fun ν => ν.T h0) hTmem
                (fun ν =>
                  if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
                    ‖I1BoxSum g N A h0 ν e‖ else 0)).symm
    _ = ∑ T ∈ Srange, ∑ e ∈ Srange, ∑ ν ∈ F.filter fun ν => ν.T h0 = T,
          if e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1 then
            ‖I1BoxSum g N A h0 ν e‖ else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ Srange, ∑ e ∈ Srange,
          I1PieceIIIFixedSum d s N A g δ I h0 T e := by
          refine Finset.sum_congr rfl fun T _ =>
            Finset.sum_congr rfl fun e _ => ?_
          simp only [I1PieceIIIFixedSum, hF_filter T, Outer]

end RMFLean
