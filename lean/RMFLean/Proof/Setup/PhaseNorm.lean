/-
Basic modulus facts for circle phases (used by `I₂`, `J₁`, etc.).
-/
import RMFLean.Trusted.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax

noncomputable section

open Complex

namespace RMFLean

/-! ### `distToInt` / `cInfinityNorm` helpers (Piece III Dio transfer) -/

theorem CirclePoly.distToInt_nonneg (x : ℝ) : 0 ≤ CirclePoly.distToInt x :=
  abs_nonneg _

theorem CirclePoly.distToInt_le_abs_sub (x : ℝ) (m : ℤ) :
    CirclePoly.distToInt x ≤ |x - (m : ℝ)| := by
  simpa [CirclePoly.distToInt] using (round_le (α := ℝ) x m)

theorem CirclePoly.distToInt_mul_int (n : ℤ) (x : ℝ) :
    CirclePoly.distToInt ((n : ℝ) * x) ≤
      |(n : ℝ)| * CirclePoly.distToInt x := by
  refine le_trans (CirclePoly.distToInt_le_abs_sub ((n : ℝ) * x) (n * round x)) ?_
  refine le_of_eq ?_
  calc
    |((n : ℝ) * x) - ((n * round x : ℤ) : ℝ)|
        = |((n : ℝ) * x) - ((n : ℝ) * (round x : ℝ))| := by
          rw [Int.cast_mul]
    _ = |(n : ℝ) * (x - (round x : ℝ))| := by rw [← mul_sub]
    _ = |(n : ℝ)| * |x - (round x : ℝ)| := abs_mul _ _
    _ = |(n : ℝ)| * CirclePoly.distToInt x := by rfl

theorem CirclePoly.beta_smul {d : ℕ} (k : ℤ) (g : CirclePoly d) (j : Fin (d + 1)) :
    (k • g).beta j = (k : ℝ) * g.beta j := rfl

theorem CirclePoly.beta_compMul {d : ℕ} (g : CirclePoly d) (h : ℕ) (j : Fin (d + 1)) :
    (g.compMul h).beta j = g.beta j * (h : ℝ) ^ (j : ℕ) := rfl

theorem CirclePoly.cInfinityNorm_le_of_forall {d : ℕ} (g : CirclePoly d) (N : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j : Fin (d + 1), (j : ℕ) ≠ 0 →
      (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt (g.beta j) ≤ M) :
    g.cInfinityNorm N ≤ M := by
  simp only [CirclePoly.cInfinityNorm]
  set l : List ℝ := List.ofFn fun j : Fin (d + 1) =>
    if (j : ℕ) = 0 then (0 : ℝ)
    else (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt (g.beta j)
  have hall : ∀ a ∈ l, a ≤ M := by
    intro a ha
    rcases List.mem_ofFn.1 ha with ⟨j, rfl⟩
    split_ifs with hj
    · exact hM
    · exact h j hj
  have hle : l.maximum ≤ (↑M : WithBot ℝ) :=
    List.maximum_le_of_forall_le fun a ha =>
      WithBot.coe_le_coe.2 (hall a ha)
  -- `cInfinityNorm` uses `maximum.getD`; equal to `unbotD` on `WithBot`.
  have hget : l.maximum.getD 0 = l.maximum.unbotD 0 := by
    cases l.maximum <;> rfl
  rw [hget]
  exact (WithBot.unbotD_le_iff (fun _ => hM)).2 hle

/-- `|e(g(n))| = 1`. -/
theorem norm_ePhase {d : ℕ} (g : CirclePoly d) (n : ℕ) : ‖g.ePhase n‖ = 1 := by
  simp only [CirclePoly.ePhase]
  have h :
      (2 * (Real.pi : ℂ) * I * (g.eval (n : ℤ)) : ℂ) =
        I * (↑(2 * Real.pi * g.eval (n : ℤ)) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

/-- `g_h(n) = g(h n)` on evaluations. -/
theorem CirclePoly.eval_compMul {d : ℕ} (g : CirclePoly d) (h : ℕ) (n : ℤ) :
    (g.compMul h).eval n = g.eval ((h : ℤ) * n) := by
  simp only [CirclePoly.eval, CirclePoly.compMul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Int.cast_mul, mul_pow]
  ring

/-- Phase form of `g_h(n) = g(h n)`. -/
theorem CirclePoly.ePhase_compMul {d : ℕ} (g : CirclePoly d) (h n : ℕ) :
    (g.compMul h).ePhase n = g.ePhase (h * n) := by
  simp only [CirclePoly.ePhase, CirclePoly.eval_compMul]
  congr 3

/-- Each summand in `S_g` has modulus 1. -/
theorem norm_phaseWeight {d s N : ℕ} (g : CirclePoly d) (x : Sol s N) :
    ‖phaseWeight g x‖ = 1 := by
  simp only [phaseWeight]
  rw [norm_prod]
  refine Finset.prod_eq_one ?_
  intro i _
  have h1 : ‖g.ePhase (x.n i)‖ = 1 := norm_ePhase g _
  have h2 : ‖starRingEnd ℂ (g.ePhase (x.m i))‖ = 1 := by
    change ‖star (g.ePhase (x.m i))‖ = 1
    rw [norm_star, norm_ePhase]
  rw [norm_mul, h1, h2, one_mul]

/-- `|S_g(F)| ≤ #F`. -/
theorem norm_Sg_le_card {d s N : ℕ} (g : CirclePoly d) (F : Finset (Sol s N)) :
    ‖Sg g F‖ ≤ (F.card : ℝ) := by
  calc
    ‖Sg g F‖ ≤ ∑ x ∈ F, ‖phaseWeight g x‖ := by
      simpa [Sg] using norm_sum_le F (phaseWeight g)
    _ = ∑ x ∈ F, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro x _; exact norm_phaseWeight g x
    _ = (F.card : ℝ) := by simp

end RMFLean
