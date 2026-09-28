/-
PDF Lemma 7 (`lem:J2`) — diagonal contribution on `ℱ_1`.

PDF proof (general `s`):
  on `ℱ_1 ∩ {n₁=m₁}`, the gcd constraint is `n₁≥A`, the head phase is `1`,
  and `J₂ = (N-A+1) U_{s-1}(N)`.
  Then expand and apply `U_one` (`s=2`) or `ℋ(s-1)` (`s≥3`).
  Paper's sharper exp factor is absorbed into `errorSize` (user: B4).
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.SolFinite
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Setup.TailQAbsorb
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section

open Classical Complex Real Set

namespace RMFLean

set_option maxHeartbeats 800000

/-- δ-exponent for J₂ absorption: `N^{-J2DeltaExp Cd} < δ`. -/
noncomputable def J2DeltaExp (Cd : ℝ) : ℝ := 1 / (2 * (Cd + 4))

theorem J2DeltaExp_pos {Cd : ℝ} (hCd : 0 < Cd) : 0 < J2DeltaExp Cd := by
  simp only [J2DeltaExp]
  positivity

/--
Inductive dichotomy at a fixed ambient scale `(N,δ)` (PDF `ℋ(s)` applied at the
same `N,δ` as the ambient argument).  Diophantine exponent `Cd` depends only on
`d` when chosen outside.  Vinogradov constant `Cll` is fixed for this `s`
(quantified outside `∀ N, δ, g` at the call site).
-/
def Hyp (d s N : ℕ) (g : CirclePoly d) (δ Cd Cll : ℝ) : Prop :=
  altGaussianSqrt d N s g δ Cll ∨ altDiophantine d N g δ Cd

/-- Diagonal part of `ℱ_1`: `n₁ = m₁` and `gcd(n₁,m₁) ≥ A`. -/
def J2Support (s N A : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    x.memF A ⟨0, h0⟩ h0 ∧ x.onDiag h0

/-- On the diagonal, `memF A 0` is just `A ≤ n₁`. -/
theorem memF_onDiag_iff {s N A : ℕ} {h0 : 0 < s} {x : Sol s N}
    (hdiag : x.onDiag h0) :
    x.memF A ⟨0, h0⟩ h0 ↔ A ≤ x.n ⟨0, h0⟩ := by
  simp only [Sol.memF, Sol.onDiag] at hdiag ⊢
  rw [hdiag, Nat.gcd_self]

/-- Head phase factor is `1` when `n₁ = m₁`. -/
theorem ePhase_mul_conj_eq_one {d : ℕ} (g : CirclePoly d) (n : ℕ) :
    g.ePhase n * starRingEnd ℂ (g.ePhase n) = 1 := by
  have hnorm : ‖g.ePhase n‖ = 1 := norm_ePhase g n
  have hsq : Complex.normSq (g.ePhase n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
  rw [Complex.mul_conj, hsq]
  norm_num

theorem Sol.ext_n_m {s N : ℕ} {x y : Sol s N}
    (hn : x.n = y.n) (hm : x.m = y.m) : x = y := by
  cases x; cases y; cases hn; cases hm; rfl

/-- Drop the head of a diagonal solution. Requires `onDiag` to cancel the head factor. -/
def Sol.tailDiag {s N : ℕ} (hs : 0 < s) (x : Sol s N)
    (hdiag : x.onDiag hs) : Sol (s - 1) N :=
  match s, x with
  | 0, x => False.elim (Nat.lt_irrefl _ hs)
  | _s' + 1, x =>
    { n := fun i => x.n i.succ
      m := fun i => x.m i.succ
      hn := fun i => x.hn i.succ
      hm := fun i => x.hm i.succ
      hprod := by
        have h := x.hprod
        rw [Fin.prod_univ_succ (fun i => x.n i), Fin.prod_univ_succ (fun i => x.m i)]
          at h
        have hn0 : x.n 0 = x.m 0 := hdiag
        rw [hn0] at h
        exact Nat.mul_left_cancel (x.hm 0).1 h }

/-- Prepend the same head `k` on both sides (diagonal extension). -/
def Sol.consDiag {s N : ℕ} (hs : 0 < s) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) : Sol s N :=
  match s, hs, y with
  | 0, hs, _y => False.elim (Nat.lt_irrefl _ hs)
  | _s' + 1, _, y =>
    { n := Fin.cons k y.n
      m := Fin.cons k y.m
      hn := fun i => Fin.cases hk (fun j => y.hn j) i
      hm := fun i => Fin.cases hk (fun j => y.hm j) i
      hprod := by
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        exact congrArg (HMul.hMul k) y.hprod }

theorem Sol.consDiag_n0 {s N : ℕ} (hs : 0 < s) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) :
    (Sol.consDiag hs k hk y).n ⟨0, hs⟩ = k := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp [Sol.consDiag]

theorem Sol.consDiag_m0 {s N : ℕ} (hs : 0 < s) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) :
    (Sol.consDiag hs k hk y).m ⟨0, hs⟩ = k := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp [Sol.consDiag]

theorem Sol.consDiag_onDiag {s N : ℕ} (hs : 0 < s) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) :
    (Sol.consDiag hs k hk y).onDiag hs := by
  simp [Sol.onDiag, Sol.consDiag_n0, Sol.consDiag_m0]

theorem Sol.tailDiag_consDiag {s N : ℕ} (hs : 0 < s) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) :
    Sol.tailDiag hs (Sol.consDiag hs k hk y)
      (Sol.consDiag_onDiag hs k hk y) = y := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  refine Sol.ext_n_m ?_ ?_
  · funext i; simp [Sol.tailDiag, Sol.consDiag]
  · funext i; simp [Sol.tailDiag, Sol.consDiag]

theorem Sol.consDiag_tailDiag {s N : ℕ} (hs : 0 < s) (x : Sol s N)
    (hdiag : x.onDiag hs) :
    Sol.consDiag hs (x.n ⟨0, hs⟩)
        ⟨(x.hn ⟨0, hs⟩).1, (x.hn ⟨0, hs⟩).2⟩ (Sol.tailDiag hs x hdiag) = x := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  refine Sol.ext_n_m ?_ ?_
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Sol.consDiag]
    · simp [Sol.consDiag, Sol.tailDiag]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [Sol.consDiag, Sol.onDiag] using hdiag
    · simp [Sol.consDiag, Sol.tailDiag]

theorem phaseWeight_consDiag {d s N : ℕ} (g : CirclePoly d) (hs : 0 < s)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ N) (y : Sol (s - 1) N) :
    phaseWeight g (Sol.consDiag hs k hk y) = phaseWeight g y := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [phaseWeight, Sol.consDiag, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ePhase_mul_conj_eq_one, one_mul]
  rfl

theorem mem_J2Support_iff {s N A : ℕ} (hs : 0 < s) {x : Sol s N} :
    x ∈ J2Support s N A hs ↔
      A ≤ x.n ⟨0, hs⟩ ∧ x.n ⟨0, hs⟩ ≤ N ∧ x.onDiag hs := by
  constructor
  · intro hx
    have hx' := (Finset.mem_filter.1 hx).2
    have hdiag := hx'.2
    have hA := (memF_onDiag_iff hdiag).1 hx'.1
    exact ⟨hA, (x.hn ⟨0, hs⟩).2, hdiag⟩
  · intro ⟨hA, _, hdiag⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (memF_onDiag_iff hdiag).2 hA, hdiag⟩

theorem mem_J2Support_consDiag {s N A : ℕ} (hs : 0 < s) (k : ℕ)
    (hk1 : 1 ≤ k) (hAk : A ≤ k) (hkN : k ≤ N) (y : Sol (s - 1) N) :
    Sol.consDiag hs k ⟨hk1, hkN⟩ y ∈ J2Support s N A hs := by
  refine (mem_J2Support_iff hs).2 ⟨?_, ?_, Sol.consDiag_onDiag hs k ⟨hk1, hkN⟩ y⟩
  · simpa [Sol.consDiag_n0] using hAk
  · simpa [Sol.consDiag_n0] using hkN

theorem card_Icc_A_N (A N : ℕ) (hAN : A ≤ N) :
    (Finset.Icc A N).card = N - A + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Fixed-head slice of the diagonal support. -/
def J2SupportAt (s N A k : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  (J2Support s N A h0).filter fun x => x.n ⟨0, h0⟩ = k

theorem J2Support_eq_biUnion (s N A : ℕ) (h0 : 0 < s) :
    J2Support s N A h0 =
      (Finset.Icc A N).biUnion fun k => J2SupportAt s N A k h0 := by
  ext x
  constructor
  · intro hx
    have hx' := (mem_J2Support_iff h0).1 hx
    refine Finset.mem_biUnion.2 ⟨x.n ⟨0, h0⟩, Finset.mem_Icc.2 ⟨hx'.1, hx'.2.1⟩, ?_⟩
    exact Finset.mem_filter.2 ⟨hx, rfl⟩
  · intro hx
    rcases Finset.mem_biUnion.1 hx with ⟨k, _, hk⟩
    exact (Finset.mem_filter.1 hk).1

theorem pairwiseDisjoint_J2SupportAt (s N A : ℕ) (h0 : 0 < s) :
    (Finset.Icc A N : Set ℕ).PairwiseDisjoint fun k =>
      J2SupportAt s N A k h0 := by
  intro k _ k' _ hne
  refine Finset.disjoint_left.2 ?_
  intro x hx hx'
  exact hne
    ((Finset.mem_filter.1 hx).2.symm.trans (Finset.mem_filter.1 hx').2)

theorem consDiag_eq_of_head_eq {s N : ℕ} (hs : 0 < s) {k k' : ℕ}
    (hk : 1 ≤ k ∧ k ≤ N) (hk' : 1 ≤ k' ∧ k' ≤ N) (y : Sol (s - 1) N)
    (h : k = k') :
    Sol.consDiag hs k hk y = Sol.consDiag hs k' hk' y := by
  cases h
  rfl

theorem sum_J2SupportAt_eq {d s N A k : ℕ} (g : CirclePoly d) (h0 : 0 < s)
    (hk1 : 1 ≤ k) (hAk : A ≤ k) (hkN : k ≤ N) :
    (∑ x ∈ J2SupportAt s N A k h0, phaseWeight g x) =
      ∑ y : Sol (s - 1) N, phaseWeight g y := by
  refine Finset.sum_bij'
      (fun x hx =>
        Sol.tailDiag h0 x ((mem_J2Support_iff h0).1 (Finset.mem_filter.1 hx).1).2.2)
      (fun y _ => Sol.consDiag h0 k ⟨hk1, hkN⟩ y)
      ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_univ _
  · intro y _
    refine Finset.mem_filter.2 ⟨mem_J2Support_consDiag h0 k hk1 hAk hkN y, ?_⟩
    exact Sol.consDiag_n0 h0 k ⟨hk1, hkN⟩ y
  · intro x hx
    have hxJ := (Finset.mem_filter.1 hx).1
    have hdiag := ((mem_J2Support_iff h0).1 hxJ).2.2
    have hn0 : x.n ⟨0, h0⟩ = k := (Finset.mem_filter.1 hx).2
    have hrec := Sol.consDiag_tailDiag h0 x hdiag
    -- Goal: consDiag k (tailDiag x) = x
    have hx_eq :
        Sol.consDiag h0 k ⟨hk1, hkN⟩ (Sol.tailDiag h0 x hdiag) =
          Sol.consDiag h0 (x.n ⟨0, h0⟩)
            ⟨(x.hn ⟨0, h0⟩).1, (x.hn ⟨0, h0⟩).2⟩ (Sol.tailDiag h0 x hdiag) :=
      consDiag_eq_of_head_eq h0 ⟨hk1, hkN⟩
        ⟨(x.hn ⟨0, h0⟩).1, (x.hn ⟨0, h0⟩).2⟩ _ hn0.symm
    exact hx_eq.trans hrec
  · intro y _
    exact Sol.tailDiag_consDiag h0 k ⟨hk1, hkN⟩ y
  · intro x hx
    have hxJ := (Finset.mem_filter.1 hx).1
    have hdiag := ((mem_J2Support_iff h0).1 hxJ).2.2
    have hn0 : x.n ⟨0, h0⟩ = k := (Finset.mem_filter.1 hx).2
    have hrec := Sol.consDiag_tailDiag h0 x hdiag
    have hx_eq :
        x = Sol.consDiag h0 k ⟨hk1, hkN⟩ (Sol.tailDiag h0 x hdiag) := by
      have :
          Sol.consDiag h0 (x.n ⟨0, h0⟩)
              ⟨(x.hn ⟨0, h0⟩).1, (x.hn ⟨0, h0⟩).2⟩ (Sol.tailDiag h0 x hdiag) =
            Sol.consDiag h0 k ⟨hk1, hkN⟩ (Sol.tailDiag h0 x hdiag) :=
        consDiag_eq_of_head_eq h0
          ⟨(x.hn ⟨0, h0⟩).1, (x.hn ⟨0, h0⟩).2⟩ ⟨hk1, hkN⟩ _ hn0
      exact hrec.symm.trans this
    calc
      phaseWeight g x
          = phaseWeight g
              (Sol.consDiag h0 k ⟨hk1, hkN⟩ (Sol.tailDiag h0 x hdiag)) :=
            congrArg _ hx_eq
      _ = phaseWeight g (Sol.tailDiag h0 x hdiag) :=
          phaseWeight_consDiag g h0 k ⟨hk1, hkN⟩ _

/--
PDF identity: `J₂ = (N-A+1) U_{s-1}(N)` as complex numbers.
Combinatorial content: diagonal solutions are head `k∈[A,N]` times a tail in `V_{s-1}`,
and the head phase is `1` (`ePhase_mul_conj_eq_one`).
-/
theorem J2_eq_shift_U (d s N A : ℕ) (g : CirclePoly d)
    (hs : 2 ≤ s) (_hN : 3 ≤ N) (hA : 1 ≤ A) (hAN : A ≤ N) :
    (Sg g (J2Support (s := s) (N := N) A (by omega)) : ℂ) =
      ((N - A + 1 : ℕ) : ℂ) * (U d (s - 1) N g : ℂ) := by
  have h0 : 0 < s := by omega
  have hsplit :
      (∑ x ∈ J2Support s N A h0, phaseWeight g x) =
        ∑ k ∈ Finset.Icc A N,
          ∑ x ∈ J2SupportAt s N A k h0, phaseWeight g x := by
    rw [J2Support_eq_biUnion s N A h0]
    exact Finset.sum_biUnion (pairwiseDisjoint_J2SupportAt s N A h0)
  have hslice :
      ∀ k ∈ Finset.Icc A N,
        (∑ x ∈ J2SupportAt s N A k h0, phaseWeight g x) =
          ∑ y : Sol (s - 1) N, phaseWeight g y := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    exact sum_J2SupportAt_eq g h0 (hA.trans hk'.1) hk'.1 hk'.2
  have hU :
      (∑ y : Sol (s - 1) N, phaseWeight g y) = (U d (s - 1) N g : ℂ) := by
    simpa [Sg] using
      (moment_formula (d := d) (s := s - 1) (N := N) g Finset.univ
        (fun _ => Finset.mem_univ _)).symm
  simp only [Sg]
  rw [hsplit, Finset.sum_congr rfl hslice, Finset.sum_const, nsmul_eq_mul,
    card_Icc_A_N A N hAN, hU]

/--
From A-window upper bound and `δ > N^{-J2DeltaExp Cd}`, deduce `A ≤ δ N`.
-/
theorem A_le_delta_N (Cd : ℝ) (hCd : 0 < Cd) (N A : ℕ) (δ : ℝ)
    (hN : 3 ≤ N) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (hδN : Real.rpow (N : ℝ) (-J2DeltaExp Cd) < δ) :
    (A : ℝ) ≤ δ * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (by decide : 1 ≤ 3) hN
  have hexp : (0 : ℝ) < 4 + Cd := by linarith
  have hα : J2DeltaExp Cd * (4 + Cd) = (1 : ℝ) / 2 := by
    simp only [J2DeltaExp]; field_simp; ring
  -- Work uniformly with `^` (= `Real.rpow`) to avoid `.rpow`/`^` mismatch.
  have hpow : (N : ℝ) ^ (-(1 / 2 : ℝ)) < δ ^ (4 + Cd) := by
    have h1 : ((N : ℝ) ^ (-J2DeltaExp Cd)) ^ (4 + Cd) < δ ^ (4 + Cd) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hNpos.le _) hδN hexp
    have hrew :
        ((N : ℝ) ^ (-J2DeltaExp Cd)) ^ (4 + Cd) =
          (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        ((N : ℝ) ^ (-J2DeltaExp Cd)) ^ (4 + Cd)
            = (N : ℝ) ^ ((-J2DeltaExp Cd) * (4 + Cd)) :=
              (Real.rpow_mul hNpos.le _ _).symm
        _ = (N : ℝ) ^ (-(J2DeltaExp Cd * (4 + Cd))) := by ring_nf
        _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hα]
    rwa [hrew] at h1
  have hinv : δ ^ (-(4 + Cd)) < (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hδpow : 0 < δ ^ (4 + Cd) := Real.rpow_pos_of_pos hδ _
    have hNhalf : 0 < (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have h := (inv_lt_inv₀ hδpow hNhalf).mpr hpow
    have hδinv : (δ ^ (4 + Cd))⁻¹ = δ ^ (-(4 + Cd)) :=
      (Real.rpow_neg hδ.le (4 + Cd)).symm
    have hNinv :
        ((N : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ = (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        ((N : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
            = (N : ℝ) ^ (-(-(1 / 2 : ℝ))) := (Real.rpow_neg hNpos.le _).symm
        _ = (N : ℝ) ^ (1 / 2 : ℝ) := by ring_nf
    rwa [hδinv, hNinv] at h
  have h4 : δ ^ (-(4 + Cd)) / (N : ℝ) < 1 := by
    have hsqrt :
        (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ)
            = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ)⁻¹ := by ring
        _ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) := by
              congr 1; exact (Real.rpow_neg_one (N : ℝ)).symm
        _ = (N : ℝ) ^ (1 / 2 + -1) := (Real.rpow_add hNpos _ _).symm
        _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring_nf
    have hlt :
        δ ^ (-(4 + Cd)) / (N : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) :=
      div_lt_div_of_pos_right hinv hNpos
    calc
      δ ^ (-(4 + Cd)) / (N : ℝ)
          < (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) := hlt
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := hsqrt
      _ ≤ (1 : ℝ) :=
          Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hden : 0 < δ * (N : ℝ) := mul_pos hδ hNpos
  refine le_of_lt ?_
  rw [← div_lt_one hden]
  calc
    (A : ℝ) / (δ * (N : ℝ))
        < δ ^ (-(3 + Cd)) / (δ * (N : ℝ)) :=
          div_lt_div_of_pos_right hAhi hden
    _ = δ ^ (-(4 + Cd)) / (N : ℝ) := by
          have hrew : δ ^ (-(3 + Cd)) / δ = δ ^ (-(4 + Cd)) := by
            calc
              δ ^ (-(3 + Cd)) / δ
                  = δ ^ (-(3 + Cd)) * δ⁻¹ := by ring
              _ = δ ^ (-(3 + Cd)) * δ ^ (-(1 : ℝ)) := by
                    congr 1; exact (Real.rpow_neg_one δ).symm
              _ = δ ^ (-(3 + Cd) + -1) := (Real.rpow_add hδ _ _).symm
              _ = δ ^ (-(4 + Cd)) := by ring_nf
          calc
            δ ^ (-(3 + Cd)) / (δ * (N : ℝ))
                = (δ ^ (-(3 + Cd)) / δ) / (N : ℝ) := by ring
            _ = δ ^ (-(4 + Cd)) / (N : ℝ) := by rw [hrew]
    _ < 1 := h4

theorem momentError_le_tailQ (s N : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N) :
    momentErrorFactor N (s - 1) ≤ tailQ N s := by
  simp only [momentErrorFactor]
  have hs1 : 1 ≤ s - 1 := by omega
  exact tailQ_mono_s hs1 (Nat.sub_le s 1) hN

theorem tailQ_ge_one (N s : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N) :
    (1 : ℝ) ≤ tailQ N s :=
  tailQ_ge_one_of N s hs hN

theorem J2_real_abs_eq (d s N A : ℕ) (g : CirclePoly d) :
    ‖((N - A + 1 : ℕ) : ℂ) * (U d (s - 1) N g : ℂ) - (mainTermF s N : ℂ)‖ =
      |((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - mainTermF s N| := by
  let z : ℝ :=
    ((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - mainTermF s N
  have hz :
      ((N - A + 1 : ℕ) : ℂ) * (U d (s - 1) N g : ℂ) - (mainTermF s N : ℂ) =
        (z : ℂ) := by
    simp only [z]
    norm_cast
  rw [hz, Complex.norm_real]
  rfl

/--
Truncation / induction-error absorption into `errorSize`.
Requires `δ > N^{-J2DeltaExp Cd}` so that `A ≤ δ N` under the A-window.
The inductive Vinogradov constant `Cll_ind` from `Hyp` is folded into the
returned explicit constant `Cll_ind + (s-1)!`.
-/
theorem J2_error_absorbed (d : ℕ) (Cd : ℝ) (hCd : 0 < Cd)
    (s N A : ℕ) (g : CirclePoly d) (δ Cd' Cll_ind : ℝ)
    (hCd' : Cd ≤ Cd') (hCll : 0 < Cll_ind)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 1 ≤ A) (hAN : A ≤ N)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (_hAlo : Real.rpow δ (-Cd) < (A : ℝ))
    (hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (hδN : Real.rpow (N : ℝ) (-J2DeltaExp Cd) < δ)
    (hind : s = 2 ∨ Hyp d (s - 1) N g δ Cd' Cll_ind)
    (_hrange : s = 2 ∨ inMomentRange N (s - 1)) :
    ‖((N - A + 1 : ℕ) : ℂ) * (U d (s - 1) N g : ℂ) -
        (mainTermF s N : ℂ)‖ ≤
      (Cll_ind + (Nat.factorial (s - 1) : ℝ)) * errorSize N s δ ∨
      altDiophantine d N g δ Cd' := by
  have hδ1 : δ < 1 := lt_trans hδ' (by norm_num)
  have hAN_delta := A_le_delta_N Cd hCd N A δ hN hδ hδ1 hAhi hδN
  have hQ := tailQ_ge_one N s hs hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hN
  have hnorm := J2_real_abs_eq d s N A g
  set fact : ℝ := (Nat.factorial (s - 1) : ℝ)
  have herr0 : 0 ≤ errorSize N s δ := by
    simp only [errorSize, tailQ]; positivity
  by_cases h2 : s = 2
  · subst h2
    refine Or.inl ?_
    have hU : U d 1 N g = (N : ℝ) := U_one d N g
    have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have habs :
        |((N - A + 1 : ℕ) : ℝ) * (N : ℝ) - (N : ℝ) ^ 2| =
          (N : ℝ) * ((A : ℝ) - 1) := by
      have hcalc :
          ((N - A + 1 : ℕ) : ℝ) * (N : ℝ) - (N : ℝ) ^ 2 =
            (N : ℝ) * (1 - (A : ℝ)) := by
        rw [Nat.cast_add, Nat.cast_sub hAN, Nat.cast_one]; ring
      rw [hcalc, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonpos (sub_nonpos.2 hA1)]; ring
    have hle1 :
        ‖((N - A + 1 : ℕ) : ℂ) * (U d 1 N g : ℂ) - (mainTermF 2 N : ℂ)‖ ≤
          errorSize N 2 δ := by
      have hle' :
          |((N - A + 1 : ℕ) : ℝ) * U d 1 N g - mainTermF 2 N| ≤
            errorSize N 2 δ := by
        calc
          |((N - A + 1 : ℕ) : ℝ) * U d 1 N g - mainTermF 2 N|
              = |((N - A + 1 : ℕ) : ℝ) * (N : ℝ) - (N : ℝ) ^ 2| := by
                simp [hU, mainTermF, Nat.factorial_one]
          _ = (N : ℝ) * ((A : ℝ) - 1) := habs
          _ ≤ (N : ℝ) * (A : ℝ) :=
              mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
          _ ≤ (N : ℝ) * (δ * (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hAN_delta (Nat.cast_nonneg _)
          _ = δ * (N : ℝ) ^ 2 := by ring
          _ ≤ δ * (N : ℝ) ^ 2 * tailQ N 2 :=
              le_mul_of_one_le_right
                (mul_nonneg hδ.le (pow_nonneg (Nat.cast_nonneg _) _)) hQ
          _ ≤ errorSize N 2 δ :=
              delta_mul_Ns_tailQ_le_errorSize N 2 hδ.le
                (le_of_lt (lt_trans hδ' (by norm_num))) hN
      rwa [hnorm]
    have hC : (1 : ℝ) ≤ Cll_ind + fact := by
      have hf : fact = 1 := by
        simp only [fact]
        norm_num
      rw [hf]; linarith [hCll]
    calc
      ‖((N - A + 1 : ℕ) : ℂ) * (U d 1 N g : ℂ) - (mainTermF 2 N : ℂ)‖
          ≤ errorSize N 2 δ := hle1
      _ = 1 * errorSize N 2 δ := by ring
      _ ≤ (Cll_ind + fact) * errorSize N 2 δ :=
          mul_le_mul_of_nonneg_right hC herr0
  · have hind' : Hyp d (s - 1) N g δ Cd' Cll_ind := Or.resolve_left hind h2
    rcases hind' with hgauss | hdio
    · have hM :
          |M d (s - 1) N g - gaussianMoment (s - 1)| ≤
            Cll_ind * (Real.sqrt δ * momentErrorFactor N (s - 1)) := hgauss
      refine Or.inl ?_
      have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
      have hUeq :
          U d (s - 1) N g = M d (s - 1) N g * (N : ℝ) ^ (s - 1) := by
        simp only [M]; field_simp [ne_of_gt (pow_pos hNpos _)]
      have hcardR : ((N - A + 1 : ℕ) : ℝ) = (N : ℝ) - (A : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hAN, Nat.cast_one]
      have hpowNs : (N : ℝ) ^ s = (N : ℝ) * (N : ℝ) ^ (s - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hs1]
      have hsplit :
          ((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - fact * (N : ℝ) ^ s =
            ((N - A + 1 : ℕ) : ℝ) *
                (M d (s - 1) N g - gaussianMoment (s - 1)) *
                  (N : ℝ) ^ (s - 1) -
              fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1) := by
        simp only [hUeq, gaussianMoment, fact, hpowNs, hcardR]; ring
      have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      have htri :
          |((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - mainTermF s N| ≤
            ((N - A + 1 : ℕ) : ℝ) *
                |M d (s - 1) N g - gaussianMoment (s - 1)| *
                  (N : ℝ) ^ (s - 1) +
              fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1) := by
        simp only [mainTermF, fact]
        set a : ℝ :=
          ((N - A + 1 : ℕ) : ℝ) *
            (M d (s - 1) N g - gaussianMoment (s - 1)) * (N : ℝ) ^ (s - 1)
        set b : ℝ := fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1)
        have h1 :
            |((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - fact * (N : ℝ) ^ s| =
              |a - b| := by
          simp only [a, b]; rw [hsplit]
        have h2 : |a - b| ≤ |a| + |b| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
        have hcpos : 0 ≤ ((N - A + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hNpow : 0 ≤ (N : ℝ) ^ (s - 1) := pow_nonneg (Nat.cast_nonneg _) _
        have hfpos : 0 ≤ fact := Nat.cast_nonneg _
        have ha :
            |a| =
              ((N - A + 1 : ℕ) : ℝ) *
                |M d (s - 1) N g - gaussianMoment (s - 1)| *
                  (N : ℝ) ^ (s - 1) := by
          simp only [a, abs_mul, abs_of_nonneg hcpos, abs_of_nonneg hNpow]
        have hb : |b| = fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1) := by
          simp only [b, abs_mul, abs_of_nonneg hfpos, abs_of_nonneg hNpow,
            abs_of_nonneg (sub_nonneg.2 hA1)]
        calc
          |((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - fact * (N : ℝ) ^ s|
              = |a - b| := h1
          _ ≤ |a| + |b| := h2
          _ = ((N - A + 1 : ℕ) : ℝ) *
                  |M d (s - 1) N g - gaussianMoment (s - 1)| *
                    (N : ℝ) ^ (s - 1) +
                fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1) := by
              rw [ha, hb]
      have hcard_le : ((N - A + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
        rw [hcardR]; linarith
      have hterm1 :
          ((N - A + 1 : ℕ) : ℝ) *
              |M d (s - 1) N g - gaussianMoment (s - 1)| *
                (N : ℝ) ^ (s - 1) ≤
            Cll_ind * errorSize N s δ := by
        calc
          ((N - A + 1 : ℕ) : ℝ) *
              |M d (s - 1) N g - gaussianMoment (s - 1)| *
                (N : ℝ) ^ (s - 1)
              ≤ (N : ℝ) * (Cll_ind * (Real.sqrt δ * momentErrorFactor N (s - 1))) *
                  (N : ℝ) ^ (s - 1) := by
                refine mul_le_mul_of_nonneg_right ?_
                  (pow_nonneg (Nat.cast_nonneg _) _)
                exact mul_le_mul hcard_le hM (abs_nonneg _) (Nat.cast_nonneg _)
          _ = Cll_ind * Real.sqrt δ * momentErrorFactor N (s - 1) *
                ((N : ℝ) * (N : ℝ) ^ (s - 1)) := by ring
          _ = Cll_ind * Real.sqrt δ * momentErrorFactor N (s - 1) *
                (N : ℝ) ^ s := by
                rw [hpowNs]
          _ ≤ Cll_ind * Real.sqrt δ * tailQ N s * (N : ℝ) ^ s := by
                gcongr; exact momentError_le_tailQ s N hs hN
          _ = Cll_ind * errorSize N s δ := by simp [errorSize]; ring
      have hterm2 :
          fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1) ≤
            fact * errorSize N s δ := by
        calc
          fact * ((A : ℝ) - 1) * (N : ℝ) ^ (s - 1)
              ≤ fact * (A : ℝ) * (N : ℝ) ^ (s - 1) := by
                refine mul_le_mul_of_nonneg_right ?_
                  (pow_nonneg (Nat.cast_nonneg _) _)
                exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
          _ ≤ fact * (δ * (N : ℝ)) * (N : ℝ) ^ (s - 1) := by gcongr
          _ = fact * δ * ((N : ℝ) * (N : ℝ) ^ (s - 1)) := by ring
          _ = fact * δ * (N : ℝ) ^ s := by rw [hpowNs]
          _ ≤ fact * δ * (N : ℝ) ^ s * tailQ N s :=
              le_mul_of_one_le_right
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ.le)
                  (pow_nonneg (Nat.cast_nonneg _) _)) hQ
          _ = fact * (δ * (N : ℝ) ^ s * tailQ N s) := by ring
          _ ≤ fact * errorSize N s δ :=
              mul_le_mul_of_nonneg_left
                (delta_mul_Ns_tailQ_le_errorSize N s hδ.le
                  (le_of_lt (lt_trans hδ' (by norm_num))) hN)
                (show 0 ≤ fact from Nat.cast_nonneg _)
      rw [hnorm]
      calc
        |((N - A + 1 : ℕ) : ℝ) * U d (s - 1) N g - mainTermF s N|
            ≤ _ := htri
        _ ≤ Cll_ind * errorSize N s δ + fact * errorSize N s δ :=
          add_le_add hterm1 hterm2
        _ = (Cll_ind + fact) * errorSize N s δ := by ring
    · exact Or.inr hdio

/--
PDF Lemma 7 / `lem:J2`: `|J₂ - (s-1)! N^s| ≤ C · δ N^s 𝒬` or Diophantine,
with explicit `C = Cll_ind + (s-1)!` depending only on the inductive constant.
Requires `δ > N^{-J2DeltaExp Cd}`.
-/
theorem J2_bound (d : ℕ) (Cd : ℝ) (hCd : 0 < Cd)
    (s N A : ℕ) (g : CirclePoly d) (δ Cd' Cll_ind : ℝ)
    (hCd' : Cd ≤ Cd') (hCll : 0 < Cll_ind)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hA : 1 ≤ A) (hAN : A ≤ N)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (hAlo : Real.rpow δ (-Cd) < (A : ℝ))
    (hAhi : (A : ℝ) < Real.rpow δ (-(3 + Cd)))
    (hδN : Real.rpow (N : ℝ) (-J2DeltaExp Cd) < δ)
    (hind : s = 2 ∨ Hyp d (s - 1) N g δ Cd' Cll_ind)
    (hrange : s = 2 ∨ inMomentRange N (s - 1)) :
    ‖(Sg g (J2Support (s := s) (N := N) A (by omega)) : ℂ) -
        (mainTermF s N : ℂ)‖ ≤
      (Cll_ind + (Nat.factorial (s - 1) : ℝ)) * errorSize N s δ ∨
      altDiophantine d N g δ Cd' := by
  rw [J2_eq_shift_U d s N A g hs hN hA hAN]
  exact J2_error_absorbed d Cd hCd s N A g δ Cd' Cll_ind hCd' hCll hs hN hA hAN
    hδ hδ' hAlo hAhi hδN hind hrange

end RMFLean
