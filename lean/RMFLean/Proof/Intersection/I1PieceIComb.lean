/-
Piece I / II combinatorial counting majorants (PDF lem:I1, Pieces I--II).

Combinatorial helpers for `I1_piece_I/II_card_majorant`
(assembled in `I1PieceIAssemble.lean`).
-/
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.Intersection.I1
import RMFLean.Proof.Intersection.I1PieceIIIComb
import RMFLean.Proof.Intersection.I1PieceIIIScaledJ1
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Real

namespace RMFLean

set_option maxHeartbeats 400000

/-! ### Analytic helpers -/

/-- `∑_{m≤X} τ_s(g m) τ_s(m) ≤ τ_s(g) · X · (2 log X)^{s²-1}` for `X≥3`. -/
theorem tau_ss_conv_sum_bound (s g X : ℕ) (hs : 2 ≤ s) (hX : 3 ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ)) ≤
      (tau s g : ℝ) * (X : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) := by
  have hg1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hterm : ∀ m ∈ Finset.Icc 1 X,
      (tau s (g * m) : ℝ) * (tau s m : ℝ) ≤
        (tau s g : ℝ) * (tau s m : ℝ) ^ 2 := by
    intro m _
    have h1 : (tau s (g * m) : ℝ) ≤ (tau s g : ℝ) * (tau s m : ℝ) := by
      exact_mod_cast tau_mul_le s g m hg1
    nlinarith [sq_nonneg (tau s m : ℝ)]
  have hsq := divisor_sum_sq_bound X s hX hg1
  have hτg : (0 : ℝ) ≤ tau s g := by exact_mod_cast Nat.zero_le _
  calc
    (∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 X, (tau s g : ℝ) * (tau s m : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = (tau s g : ℝ) * ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2 :=
      (Finset.mul_sum (Finset.Icc 1 X) (fun m => (tau s m : ℝ) ^ 2) (tau s g : ℝ)).symm
    _ ≤ (tau s g : ℝ) * ((X : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1)) :=
      mul_le_mul_of_nonneg_left hsq hτg
    _ = (tau s g : ℝ) * (X : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) := by ring

/-- Same with log-base `N` when `X ≤ N^s`. -/
theorem tau_ss_conv_sum_bound_weak (s g X N : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hXle : X ≤ N ^ s) :
    (∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ)) ≤
      (tau s g : ℝ) * (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
  by_cases hX3 : 3 ≤ X
  · have h := tau_ss_conv_sum_bound s g X hs hX3
    have hXpos : (0 : ℝ) < X := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hX3
    have hXleR : (X : ℝ) ≤ (N : ℝ) ^ s := by exact_mod_cast hXle
    have hlog : Real.log X ≤ (s : ℝ) * Real.log N := by
      have := Real.log_le_log hXpos hXleR
      rwa [Real.log_pow (N : ℝ) s] at this
    have h2 : 2 * Real.log X ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
    have hpow :
        (2 * Real.log X) ^ (s ^ 2 - 1) ≤
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have hτg : (0 : ℝ) ≤ tau s g := by exact_mod_cast Nat.zero_le _
    have hX0 : (0 : ℝ) ≤ X := by exact_mod_cast Nat.zero_le _
    calc
      ∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ)
          ≤ (tau s g : ℝ) * (X : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) := h
      _ ≤ (tau s g : ℝ) * (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hτg hX0)
  · -- `X ≤ 2`: empty if `X = 0`; else dominate by the `X = 3` bound.
    by_cases hX0 : X = 0
    · subst hX0; simp
    · have hX1 : 1 ≤ X := Nat.pos_of_ne_zero hX0
      have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 3 := by
        intro m hm
        exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hm).1,
          le_trans (Finset.mem_Icc.1 hm).2 (by omega)⟩
      have hmono :
          (∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ)) ≤
            ∑ m ∈ Finset.Icc 1 3, (tau s (g * m) : ℝ) * (tau s m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          mul_nonneg (by exact_mod_cast Nat.zero_le (tau s (g * m)))
            (by exact_mod_cast Nat.zero_le (tau s m))
      have h3 := tau_ss_conv_sum_bound s g 3 hs (by decide)
      have hτg : (0 : ℝ) ≤ tau s g := by exact_mod_cast Nat.zero_le _
      have hlogN : (1 : ℝ) ≤ Real.log N := by
        have hlog3 : (1 : ℝ) < Real.log 3 :=
          (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
        exact le_trans (le_of_lt hlog3)
          (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
      have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
      have hge2 : 2 ≤ s ^ 2 - 1 := by
        have hs2 : 4 ≤ s ^ 2 := by
          have := Nat.mul_le_mul hs hs
          simpa [pow_two] using this
        omega
      -- `3 · (2 log 3)^k ≤ 1 · (2 s log N)^k` since `(2 log 3)/(2 s log N) ≤ 1/2`
      -- and `3 / 2^k ≤ 1` for `k ≥ 2`.
      have h3le :
          (3 : ℝ) * (2 * Real.log 3) ^ (s ^ 2 - 1) ≤
            (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
        have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX1
        have hlog3le : Real.log 3 ≤ Real.log N :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hN)
        have hfrac : 2 * Real.log 3 ≤ (2 * (s : ℝ) * Real.log N) / 2 := by
          nlinarith [hsR, hlogN, hlog3le]
        have hp :
            (2 * Real.log 3) ^ (s ^ 2 - 1) ≤
              ((2 * (s : ℝ) * Real.log N) / 2) ^ (s ^ 2 - 1) :=
          pow_le_pow_left₀ (by positivity) hfrac _
        have hdiv :
            ((2 * (s : ℝ) * Real.log N) / 2) ^ (s ^ 2 - 1) =
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) / (2 : ℝ) ^ (s ^ 2 - 1) :=
          div_pow _ _ _
        have h2pow : (4 : ℝ) ≤ (2 : ℝ) ^ (s ^ 2 - 1) := by
          calc
            (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ (2 : ℝ) ^ (s ^ 2 - 1) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hge2
        have hmain :
            (3 : ℝ) * (2 * Real.log 3) ^ (s ^ 2 - 1) ≤
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
          calc
            (3 : ℝ) * (2 * Real.log 3) ^ (s ^ 2 - 1)
                ≤ 3 * (((2 * (s : ℝ) * Real.log N) / 2) ^ (s ^ 2 - 1)) :=
              mul_le_mul_of_nonneg_left hp (by norm_num)
            _ = 3 * ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) /
                  (2 : ℝ) ^ (s ^ 2 - 1)) := by rw [hdiv]
            _ ≤ 3 * ((2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) / 4) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h2pow
            _ = (3 / 4) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by ring
            _ ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
              nlinarith [pow_nonneg (by positivity :
                (0 : ℝ) ≤ 2 * (s : ℝ) * Real.log N) (s ^ 2 - 1)]
        nlinarith [hx, hmain,
          pow_nonneg (by positivity :
            (0 : ℝ) ≤ 2 * (s : ℝ) * Real.log N) (s ^ 2 - 1)]
      calc
        ∑ m ∈ Finset.Icc 1 X, (tau s (g * m) : ℝ) * (tau s m : ℝ)
            ≤ ∑ m ∈ Finset.Icc 1 3, (tau s (g * m) : ℝ) * (tau s m : ℝ) := hmono
        _ ≤ (tau s g : ℝ) * (3 : ℝ) * (2 * Real.log 3) ^ (s ^ 2 - 1) := h3
        _ ≤ (tau s g : ℝ) * (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left h3le hτg

theorem sum_Icc_inv_le_one_add_log (M : ℕ) (_hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log M := by
  have := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at this
  simpa [div_eq_mul_inv] using this

/-- Scaled fibre box cardinality `≤ N/(e T)` (as ℝ via Nat inequality). -/
theorem I1Box_card_le_div {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ) (he : 1 ≤ e) :
    (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ) ≤
      (N : ℝ) / ((e : ℝ) * (ν.T h0 : ℝ)) := by
  have hTpos : 0 < ν.T h0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 (I1Outer_T_mem_Icc hν)).1
  have hM := I1Outer.max_n1'_m1'_pos hν
  have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he
  have hh1 : 1 ≤ e * ν.T h0 := Nat.succ_le_of_lt (Nat.mul_pos hepos hTpos)
  have hEq := I1Box_support_eq_keyHeadFibreScaled hν e he hTpos hM
  have hscale : keyScale (I1Outer.fibreKey hν) ⟨0, h0⟩ = max ν.n1' ν.m1' :=
    I1Outer.fibreKey_scale0 hν
  rw [hEq]
  have hle :
      (keyHeadFibreScaled (I1Outer.fibreKey hν) N A (e * ν.T h0) h0).card ≤
        N / (e * ν.T h0 * max ν.n1' ν.m1') := by
    simpa [hscale, Nat.mul_assoc] using
      card_keyHeadFibreScaled_le (I1Outer.fibreKey hν) N A (e * ν.T h0) h0 hh1
        (by simpa [hscale] using hM)
  have hden :
      N / (e * ν.T h0 * max ν.n1' ν.m1') ≤ N / (e * ν.T h0) :=
    Nat.div_le_div_left (Nat.le_mul_of_pos_right _ hM) (Nat.mul_pos hepos hTpos)
  have hcard : (keyHeadFibreScaled (I1Outer.fibreKey hν) N A (e * ν.T h0) h0).card ≤
      N / (e * ν.T h0) := hle.trans hden
  have hcast : ((N / (e * ν.T h0) : ℕ) : ℝ) ≤ (N : ℝ) / (↑(e * ν.T h0) : ℝ) :=
    Nat.cast_div_le
  have hdenR : (↑(e * ν.T h0) : ℝ) = (e : ℝ) * (ν.T h0 : ℝ) := by push_cast; rfl
  exact (Nat.cast_le.2 hcard).trans (hcast.trans_eq (by rw [hdenR]))

/-! ### Outer `m'` / `nProd` packages -/

def restrictTailM' {s : ℕ} (h0 : 0 < s) (m' : Fin s → ℕ) : Fin (s - 1) → ℕ :=
  fun j => m' ⟨j.val + 1, by omega⟩

theorem restrictTailM'_prod {s : ℕ} (h0 : 0 < s) (m' : Fin s → ℕ) :
    (∏ j : Fin (s - 1), restrictTailM' h0 m' j) =
      ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), m' i :=
  restrictTailTvec_prod h0 m'

theorem I1Outer_m'_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) : 0 < ν.m' i := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  have hrecon := toIntersectionCanon_reconM_tail s N x h0 i hi0
  have heq : (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i = x.m i := by
    simpa [IntersectionCanon.reconM, hi0] using hrecon
  have hm1 : 1 ≤ x.m i := (x.hm i).1
  have hmul_pos : 0 < (x.toIntersectionCanon h0).outer.t i *
      (x.toIntersectionCanon h0).outer.m' i :=
    lt_of_lt_of_le Nat.zero_lt_one (by simpa [heq] using hm1)
  have hm' := Nat.eq_zero_or_pos ((x.toIntersectionCanon h0).outer.m' i)
  rcases hm' with hm'0 | hm'pos
  · simp [hm'0] at hmul_pos
  · exact hm'pos

theorem I1Outer_nTail_pos {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) : 0 < ν.nTail i := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  have hrecon : (x.toIntersectionCanon h0).outer.nTail i = x.n i := by
    simp [Sol.toIntersectionCanon, hi0]
  have hn1 : 1 ≤ x.n i := (x.hn i).1
  exact lt_of_lt_of_le Nat.zero_lt_one (by simpa [hrecon] using hn1)

def IntersectionOuter.nProd {s : ℕ} (ν : IntersectionOuter s) (h0 : 0 < s) : ℕ :=
  ν.n1' * ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.nTail i

theorem I1Outer_nProd_eq {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    ν.nProd h0 = ν.T h0 * ν.m1' * ν.Q h0 := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  simpa [IntersectionOuter.nProd, IntersectionOuter.Q, IntersectionOuter.T]
    using toIntersectionCanon_outer_product s N x h0

theorem I1Outer_nTail_le {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {i : Fin s}
    (hi0 : i ≠ ⟨0, h0⟩) : ν.nTail i ≤ N := by
  rcases Finset.mem_image.1 hν with ⟨x, _hx, rfl⟩
  have : (x.toIntersectionCanon h0).outer.nTail i = x.n i := by
    simp [Sol.toIntersectionCanon, hi0]
  simpa [this] using (x.hn i).2

theorem I1Outer_nProd_le_of_mem_box {s N A : ℕ} {I : Finset (Fin s)}
    {h0 : 0 < s} {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) {e k : ℕ}
    (he : 1 ≤ e) (hk : 1 ≤ k)
    (hb : e * k ∈ fibreB s N A ν h0) :
    ν.nProd h0 ≤ N ^ s / (e * k * ν.T h0) := by
  have hTpos : 0 < ν.T h0 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.1 (I1Outer_T_mem_Icc hν)).1
  have hepos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  rcases (mem_fibreB_mul_iff ν h0 e k).1 hb with ⟨_, _, hNM⟩
  have hM := I1Outer.max_n1'_m1'_pos hν
  have hn1le : ν.n1' ≤ N / (e * k * ν.T h0) := by
    have hle : ν.n1' ≤ max ν.n1' ν.m1' := le_max_left _ _
    have hmul : e * k * ν.T h0 * ν.n1' ≤ N :=
      le_trans (Nat.mul_le_mul_left _ hle) (by simpa [mul_assoc] using hNM)
    have hdenpos : 0 < e * k * ν.T h0 :=
      Nat.mul_pos (Nat.mul_pos hepos hkpos) hTpos
    exact (Nat.le_div_iff_mul_le hdenpos).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  set E := Finset.univ.erase (⟨0, h0⟩ : Fin s)
  have hcardE : E.card = s - 1 := by
    simp [E, Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin]
  have htail : ∏ i ∈ E, ν.nTail i ≤ N ^ (s - 1) := by
    have hle : ∀ i ∈ E, ν.nTail i ≤ N := fun i hi =>
      I1Outer_nTail_le hν (Finset.mem_erase.1 hi).1
    calc
      ∏ i ∈ E, ν.nTail i ≤ ∏ i ∈ E, N := Finset.prod_le_prod' hle
      _ = N ^ E.card := Finset.prod_const _
      _ = N ^ (s - 1) := by rw [hcardE]
  have hdenpos : 0 < e * k * ν.T h0 :=
    Nat.mul_pos (Nat.mul_pos hepos hkpos) hTpos
  have hpow : N * N ^ (s - 1) = N ^ s := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
    congr 1
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt h0)
  have hstd : (N / (e * k * ν.T h0)) * N ^ (s - 1) ≤
      N ^ s / (e * k * ν.T h0) := by
    have h2 : N / (e * k * ν.T h0) * (e * k * ν.T h0) ≤ N :=
      Nat.div_mul_le_self _ _
    refine (Nat.le_div_iff_mul_le hdenpos).2 ?_
    calc
      (N / (e * k * ν.T h0) * N ^ (s - 1)) * (e * k * ν.T h0)
          = (N / (e * k * ν.T h0) * (e * k * ν.T h0)) * N ^ (s - 1) := by
            ring
      _ ≤ N * N ^ (s - 1) := Nat.mul_le_mul_right _ h2
      _ = N ^ s := hpow
  calc
    ν.nProd h0 = ν.n1' * ∏ i ∈ E, ν.nTail i := rfl
    _ ≤ (N / (e * k * ν.T h0)) * N ^ (s - 1) := Nat.mul_le_mul hn1le htail
    _ ≤ N ^ s / (e * k * ν.T h0) := hstd

/-- `e`-allocation `OF(s-1, e)` from `e ∣ Q(ν)`. -/
def I1Outer.toOrderedFactorsE {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) (e : ℕ)
    (he : e ∈ (ν.Q h0).divisors) : OrderedFactors (s - 1) e := by
  set f := restrictTailM' h0 ν.m'
  set b := ν.Q h0 / e
  have hQpos := I1Outer_Q_pos hν
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have hbpos : 0 < b :=
    Nat.div_pos (Nat.le_of_dvd hQpos (Nat.dvd_of_mem_divisors he)) hepos
  have hfpos : ∀ j, 0 < f j := fun j =>
    I1Outer_m'_pos hν (by
      intro h; exact absurd (congrArg Fin.val h) (Nat.succ_ne_zero _))
  have hprod : (∏ j, f j) = e * b := by
    have hQ : (∏ j, f j) = ν.Q h0 := by
      simp [f, restrictTailM'_prod, IntersectionOuter.Q]
    have heb : e * b = ν.Q h0 :=
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    rw [hQ, ← heb]
  have hspec := extractFactors_spec (s - 1) e b f hbpos hfpos hprod
  exact ⟨extractFactors (s - 1) e f, ⟨hspec.2.2.2.1, hspec.2.1⟩⟩

/-- Ordered `s`-factorisation of `nProd`. -/
def I1Outer.toOrderedFactorsN {s N A : ℕ} {I : Finset (Fin s)} {h0 : 0 < s}
    {ν : IntersectionOuter s}
    (hν : ν ∈ I1Outer (s := s) (N := N) A I h0) :
    OrderedFactors s (ν.nProd h0) := by
  let f : Fin s → ℕ := fun i =>
    if hi0 : i = ⟨0, h0⟩ then ν.n1' else ν.nTail i
  have hfpos : ∀ i, 0 < f i := by
    intro i
    by_cases hi0 : i = ⟨0, h0⟩
    · simpa [f, hi0] using I1Outer.n1'_pos hν
    · simpa [f, hi0] using I1Outer_nTail_pos hν hi0
  have hprod : (∏ i, f i) = ν.nProd h0 := by
    have hmem : (⟨0, h0⟩ : Fin s) ∈ (Finset.univ : Finset (Fin s)) :=
      Finset.mem_univ _
    rw [← Finset.prod_erase_mul _ _ hmem]
    have h0f : f ⟨0, h0⟩ = ν.n1' := by simp [f]
    have htail :
        (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), f i) =
          ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), ν.nTail i := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hi0 : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      simp [f, hi0]
    simp [IntersectionOuter.nProd, h0f, htail, Nat.mul_comm]
  exact ⟨f, ⟨hfpos, hprod⟩⟩

/-! ### Fixed-`(T,e)` card sums -/

def I1PieceIFixedCardSum (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s))
    (h0 : 0 < s) (T e : ℕ) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter
      fun ν => ν.T h0 = T ∧ (1 : ℝ) ≤ δ * (ν.T h0 : ℝ),
    if e ∈ (ν.Q h0).divisors then
      (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ)
    else 0

def I1PieceIIFixedCardSum (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s))
    (h0 : 0 < s) (T e : ℕ) : ℝ :=
  ∑ ν ∈ (I1Outer (s := s) (N := N) A I h0).filter fun ν => ν.T h0 = T,
    if e ∈ (ν.Q h0).divisors ∧ (1 : ℝ) ≤ δ * (e : ℝ) then
      (((Finset.Icc 1 N).filter fun k => e * k ∈ fibreB s N A ν h0).card : ℝ)
    else 0

/-- Regroup Piece I card sum by `(T,e)`. -/
theorem I1PieceICardSum_eq_sum_fixed (s N A : ℕ) (δ : ℝ) (I : Finset (Fin s))
    (h0 : 0 < s) (_hN : 3 ≤ N) :
    I1PieceICardSum s N A δ I h0 =
      ∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
        ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
          I1PieceIFixedCardSum s N A δ I h0 T e := by
  classical
  set Outer := I1Outer (s := s) (N := N) A I h0
  set Srange := Finset.Icc 1 (N ^ (s - 1))
  set F := Outer.filter fun ν => (1 : ℝ) ≤ δ * (ν.T h0 : ℝ)
  have hTmem : ∀ ν ∈ F, ν.T h0 ∈ Srange := fun ν hν =>
    I1Outer_T_mem_Icc (Finset.mem_filter.1 hν).1
  have hνsum : ∀ ν ∈ F,
      (∑ e ∈ (ν.Q h0).divisors,
          (((Finset.Icc 1 N).filter fun k =>
            e * k ∈ fibreB s N A ν h0).card : ℝ)) =
        ∑ e ∈ Srange,
          if e ∈ (ν.Q h0).divisors then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0 := by
    intro ν hν
    have hsubset : (ν.Q h0).divisors ⊆ Srange := fun e he =>
      I1Outer_divisor_mem_Icc (Finset.mem_filter.1 hν).1 he
    have hset :
        (ν.Q h0).divisors =
          Srange.filter fun e => e ∈ (ν.Q h0).divisors := by
      ext e
      exact ⟨fun he => Finset.mem_filter.2 ⟨hsubset he, he⟩,
        fun he => (Finset.mem_filter.1 he).2⟩
    symm
    rw [← Finset.sum_filter (fun e => e ∈ (ν.Q h0).divisors)]
    rw [← hset]
  have hFfilter : ∀ T : ℕ,
      F.filter (fun ν => ν.T h0 = T) =
        Outer.filter fun ν => ν.T h0 = T ∧ (1 : ℝ) ≤ δ * (ν.T h0 : ℝ) := by
    intro T; ext ν
    simp only [F, Outer, Finset.mem_filter]
    tauto
  calc
    I1PieceICardSum s N A δ I h0
        = ∑ ν ∈ F, ∑ e ∈ (ν.Q h0).divisors,
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ) := by
          simp [I1PieceICardSum, F, Outer]
    _ = ∑ ν ∈ F, ∑ e ∈ Srange,
          if e ∈ (ν.Q h0).divisors then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0 := Finset.sum_congr rfl fun ν hν => hνsum ν hν
    _ = ∑ e ∈ Srange, ∑ ν ∈ F,
          if e ∈ (ν.Q h0).divisors then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0 := Finset.sum_comm
    _ = ∑ e ∈ Srange, ∑ T ∈ Srange, ∑ ν ∈ F.filter fun ν => ν.T h0 = T,
          if e ∈ (ν.Q h0).divisors then
            (((Finset.Icc 1 N).filter fun k =>
              e * k ∈ fibreB s N A ν h0).card : ℝ)
          else 0 := by
          refine Finset.sum_congr rfl fun e _ =>
            (Finset.sum_fiberwise_of_maps_to (g := fun ν => ν.T h0) hTmem
              (fun ν =>
                if e ∈ (ν.Q h0).divisors then
                  (((Finset.Icc 1 N).filter fun k =>
                    e * k ∈ fibreB s N A ν h0).card : ℝ)
                else 0)).symm
    _ = ∑ T ∈ Srange, ∑ e ∈ Srange,
          I1PieceIFixedCardSum s N A δ I h0 T e := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ =>
            Finset.sum_congr rfl fun e _ => ?_
          simp only [I1PieceIFixedCardSum, hFfilter T, Outer]

end RMFLean
