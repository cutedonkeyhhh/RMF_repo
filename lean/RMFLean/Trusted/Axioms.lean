/-
# Trusted axioms

Admitted facts matching PDF Lemma 6 (`lem:diophantine-nil`).
PDF Lemma 1 is a theorem in `Trusted/DivisorSums.lean`.
PDF Lemma 5 is the Waring count, used only in the paper's proof of Lemma 6
and not formalised. The method of moments (Gut, Chapter 5, Theorem 8.6) is
`billingsley_method_of_moments` in `Trusted/Corollary.lean`.
Lemma 2 is a theorem (`moment_formula`) from the definition of `U`.
Reviewers check these against `D:/RMF_file/main.pdf`, then need not read `Proof/`.
-/
import RMFLean.Trusted.Defs
import RMFLean.Trusted.DivisorSums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat

noncomputable section

open Classical Real Complex BigOperators

namespace RMFLean

/-! ### Lemma 1 — Divisor sums (`lem:divisor`)

Proved in `DivisorSums.lean`: `divisor_sum_bound`, `divisor_sum_sq_bound`,
`divisor_tail_bound`, `divisor_pointwise_exp_bound`.
-/

/-! ### Lemma 2 — Moment formula (`lem:moment-formula`)

`U` is *defined* as `Re S_g(V)` in `Defs.lean`.  The identification
`(U : ℂ) = S_g(V)` is the statement that this sum is real, which follows
from the `(n,m) ↔ (m,n)` involution conjugating the phase weight.
-/

theorem sum_phaseWeight_eq_star {d s N : ℕ} (g : CirclePoly d) :
    starRingEnd ℂ (∑ x : Sol s N, phaseWeight g x) =
      ∑ x : Sol s N, phaseWeight g x := by
  rw [map_sum]
  simp_rw [(phaseWeight_swap g _).symm]
  exact Fintype.sum_equiv (solSwapEquiv s N)
    (fun x => phaseWeight g x.swap) (phaseWeight g) fun _ => rfl

/-- `S_g(V)` is real, hence equals the coercion of `U`. -/
theorem U_eq_Sg {d s N : ℕ} (g : CirclePoly d) :
    (U d s N g : ℂ) = Sg g (Finset.univ : Finset (Sol s N)) := by
  have hstar := sum_phaseWeight_eq_star (d := d) (s := s) (N := N) g
  have hre : ((∑ x : Sol s N, phaseWeight g x).re : ℂ) =
      ∑ x : Sol s N, phaseWeight g x :=
    (Complex.conj_eq_iff_re (z := ∑ x : Sol s N, phaseWeight g x)).1 hstar
  simpa [U, Sg] using hre

/--
PDF Lemma 2: `U_s(N) = S_g(V)`.
`univV` enumerates every solution in `Sol s N`.
-/
theorem moment_formula {d s N : ℕ} (g : CirclePoly d)
    (univV : Finset (Sol s N)) (huniv : ∀ x : Sol s N, x ∈ univV) :
    (U d s N g : ℂ) = Sg g univV := by
  have h : univV = Finset.univ := Finset.eq_univ_iff_forall.2 huniv
  rw [h, U_eq_Sg]

/-- `|e(g(n))| = 1`. -/
private theorem norm_ePhase_one {d : ℕ} (g : CirclePoly d) (n : ℕ) :
    ‖g.ePhase n‖ = 1 := by
  simp only [CirclePoly.ePhase]
  have h :
      (2 * (Real.pi : ℂ) * Complex.I * (g.eval (n : ℤ)) : ℂ) =
        Complex.I * (↑(2 * Real.pi * g.eval (n : ℤ)) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

private theorem ePhase_mul_star_eq_one {d : ℕ} (g : CirclePoly d) (n : ℕ) :
    g.ePhase n * starRingEnd ℂ (g.ePhase n) = 1 := by
  have hsq : Complex.normSq (g.ePhase n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_ePhase_one g n, one_pow]
  rw [Complex.mul_conj, hsq]
  norm_num

/-- `n₁ = m₁` for a length-1 solution. -/
private theorem sol_one_n_eq_m {N : ℕ} (x : Sol 1 N) :
    x.n 0 = x.m 0 := by
  simpa [Fin.prod_univ_one] using x.hprod

/-- Length-1 solutions are diagonal tuples `n = m = k` for `k ∈ [1,N]`. -/
def equivSolOne (N : ℕ) : Sol 1 N ≃ Finset.Icc (1 : ℕ) N where
  toFun x := ⟨x.n 0, Finset.mem_Icc.2 (x.hn 0)⟩
  invFun k :=
    { n := fun _ => (k : ℕ)
      m := fun _ => (k : ℕ)
      hn := fun _ => Finset.mem_Icc.1 k.property
      hm := fun _ => Finset.mem_Icc.1 k.property
      hprod := by simp }
  left_inv x := by
    have hnm := sol_one_n_eq_m x
    refine Sol.ext ?_ ?_
    · funext i
      have : i = 0 := Subsingleton.elim i 0
      subst this
      rfl
    · funext i
      have : i = 0 := Subsingleton.elim i 0
      subst this
      exact hnm
  right_inv k := rfl

/-- Base case: `U_1(N) = N`, hence `ℳ_1(N) = 1` (PDF §2 opening). -/
theorem U_one (d N : ℕ) (g : CirclePoly d) : U d 1 N g = (N : ℝ) := by
  have h1 : ∀ k : Finset.Icc (1 : ℕ) N,
      phaseWeight g ((equivSolOne N).symm k) = 1 := by
    intro k
    simp only [phaseWeight, equivSolOne, Equiv.symm_mk]
    rw [Fin.prod_univ_one]
    exact ePhase_mul_star_eq_one g (k : ℕ)
  have hcard : Fintype.card (Finset.Icc (1 : ℕ) N) = N := by
    simp [Fintype.card_coe, Nat.card_Icc]
  have hsum : (∑ x : Sol 1 N, phaseWeight g x) = (N : ℂ) := by
    calc
      (∑ x : Sol 1 N, phaseWeight g x)
          = ∑ k : Finset.Icc (1 : ℕ) N,
              phaseWeight g ((equivSolOne N).symm k) :=
            Fintype.sum_equiv (equivSolOne N) (phaseWeight g)
              (fun k => phaseWeight g ((equivSolOne N).symm k))
              (fun x => by simp)
      _ = ∑ _k : Finset.Icc (1 : ℕ) N, (1 : ℂ) :=
            Fintype.sum_congr _ _ h1
      _ = (Fintype.card (Finset.Icc (1 : ℕ) N) : ℂ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (N : ℂ) := by rw [hcard]
  simp [U, hsum]

/-! ### Lemma 6 — Exponential dichotomy (`lem:diophantine-nil`) -/

/-- Integer interval finset `{n | lo ≤ n ≤ hi}`. -/
def intInterval (lo hi : ℕ) : Finset ℕ := Finset.Icc lo hi

/-- Inner exponential sum from PDF Lemma 6. -/
noncomputable def expSum (d : ℕ) (g : CirclePoly d) (c D : ℕ) (L : Finset ℕ) : ℂ :=
  ∑ n ∈ L, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (g.eval ((n : ℤ) * c) - g.eval ((n : ℤ) * D)))

/--
Bad dilates for PDF Lemma 6, alternative (1):
`{c : 1 ≤ c < D : |∑_{n∈L} e(g(nc)-g(nD))| > δ N/D }`.
-/
noncomputable def badDilates (d : ℕ) (g : CirclePoly d) (δ : Real) (N D : ℕ)
    (L : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (D - 1)).filter fun c =>
    δ * (N : Real) / D < ‖expSum d g c D L‖

/--
`|L| ≍ N/D` in the form used by Lemma 6.
Lower constant is `1/4` (not `1/2`) so short-fibre intervals
`[1,A-1]` with `A ≤ N/D ≤ 2A` still qualify; BT supplies `|L| ≍ N/D`.
-/
def cardAsymp (L : Finset ℕ) (N D : ℕ) : Prop :=
  (N : Real) / (4 * (D : Real)) < (L.card : Real) ∧
    (L.card : Real) < 2 * (N : Real) / (D : Real)

/--
PDF Lemma 6 (`lem:diophantine-nil`).

Exists constants depending only on `d`:
- `C_d > 5` (Diophantine exponent; enlarged to absorb ≪_d factors and
  to dominate `3 C_bad` for long/short union bookkeeping),
- `C_bad > 0` with `3 C_bad ≤ C_d` (bad-dilate cardinality),
such that for all `0 < δ < 1/8`, `0 < D < N` with `N/D > δ^{-C_d}`,
and an interval `L = [lo,hi] ⊆ [1, 2⌊N/D⌋]` with
`|L| ≍ N/D` (see `cardAsymp`) and left endpoint `lo < δ^{-(C_d+3)}`
(PDF: `a < δ^{-C_d-3}`; the extra unit of slack makes the Piece III
ambient window `δ^{-(C_d+2)} < A < δ^{-(C_d+3)}` nonempty), either
1. `#badDilates ≤ C_bad · δ D`, or
2. exists nonzero `K` with `|K| ≤ δ^{-C_d}` and
   `‖K g‖_{C^∞[N]} ≤ δ^{-C_d}`.

The Dio size factor from ≪_d is absorbed into `C_d` (PDF notation).
Quantifier order: constants sit outside the `∀`, hence are uniform in
`g, δ, N, D, L` (depending only on `d`).
-/
axiom exponential_dichotomy (d : ℕ) :
    ∃ Cd : Real, 5 < Cd ∧
      ∃ Cbad : Real, 0 < Cbad ∧ 3 * Cbad ≤ Cd ∧
          ∀ (g : CirclePoly d) (δ : Real) (N D lo hi : ℕ),
            0 < δ → δ < 1 / 8 → 0 < D → D < N →
            (N : Real) / (D : Real) > Real.rpow δ (-Cd) →
            let N_D := N / D
            let L := intInterval lo hi
            1 ≤ lo → hi ≤ 2 * N_D → cardAsymp L N D →
            (lo : Real) < Real.rpow δ (-(Cd + 3)) →
            ((badDilates d g δ N D L).card : Real) ≤ Cbad * δ * (D : Real) ∨
              ∃ K : Int, K ≠ 0 ∧
                (|K| : Real) ≤ Real.rpow δ (-Cd) ∧
                (K • g).cInfinityNorm N ≤ Real.rpow δ (-Cd)

/--
Canonical PDF Lemma 6 exponent `C_d` (shared by Prop 1 and Prop 2 / Piece III).
The Lean name `Lem5Cd` is historical.
-/
noncomputable def Lem5Cd (d : ℕ) : Real :=
  Classical.choose (exponential_dichotomy d)

theorem Lem5Cd_gt5 (d : ℕ) : 5 < Lem5Cd d :=
  (Classical.choose_spec (exponential_dichotomy d)).1

theorem Lem5Cd_spec (d : ℕ) :
    ∃ Cbad : Real, 0 < Cbad ∧ 3 * Cbad ≤ Lem5Cd d ∧
      ∀ (g : CirclePoly d) (δ : Real) (N D lo hi : ℕ),
        0 < δ → δ < 1 / 8 → 0 < D → D < N →
        (N : Real) / (D : Real) > Real.rpow δ (-Lem5Cd d) →
        let N_D := N / D
        let L := intInterval lo hi
        1 ≤ lo → hi ≤ 2 * N_D → cardAsymp L N D →
        (lo : Real) < Real.rpow δ (-(Lem5Cd d + 3)) →
        ((badDilates d g δ N D L).card : Real) ≤ Cbad * δ * (D : Real) ∨
          ∃ K : Int, K ≠ 0 ∧
            (|K| : Real) ≤ Real.rpow δ (-Lem5Cd d) ∧
            (K • g).cInfinityNorm N ≤ Real.rpow δ (-Lem5Cd d) :=
  (Classical.choose_spec (exponential_dichotomy d)).2

end RMFLean
