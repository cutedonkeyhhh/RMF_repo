/-
# Trusted definitions

Must match `D:/RMF_file/main.pdf`. PDF labels appear in docstrings.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fintype.BigOperators

noncomputable section

open Classical Complex Real BigOperators

namespace RMFLean

/-! ## PDF correspondence (review checklist)

| Lean | PDF label / symbol |
|------|--------------------|
| `CirclePoly` | polynomial `g : ℤ → ℝ/ℤ` of degree `d` |
| `CirclePoly.ePhase` | `e(g(n))` |
| `CirclePoly.cInfinityNorm` | `‖g‖_{C^∞[N]}` |
| `Sol` / `V` | solution set `V` |
| `Sol.memF` | `ℱ_i` |
| `phaseWeight` / `Sg` | `\gprod` / `S_g(ℱ)` |
| `U` / `M` | `U_s(N)` / `ℳ_s(N)` |
| `UnbalSol` / `mixedU` / `mixedM` | unbalanced product equation / `𝔼[S_N^{s₁}\overline{S_N}^{s₂}]` |
| `tailQ` | `𝒬(N,s)` |
| `tau` | `τ_ℓ` |
-/

/-- Polynomial phase on the circle: `g(n) = ∑_{j=0}^d β_j n^j` (PDF Theorem 1). -/
structure CirclePoly (d : ℕ) where
  beta : Fin (d + 1) → ℝ

namespace CirclePoly

variable {d : ℕ} (g : CirclePoly d)

/-- Real-valued lift before reducing mod `ℤ`. -/
def eval (n : ℤ) : ℝ :=
  ∑ j : Fin (d + 1), g.beta j * (n : ℝ) ^ (j : ℕ)

/-- Circle phase `e(g(n)) = exp(2πi g(n))`. -/
def ePhase (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (g.eval (n : ℤ)))

/-- Integer multiple `kg` (PDF Theorem 1, alternative 2). -/
def smul (k : ℤ) : CirclePoly d where
  beta := fun j => (k : ℝ) * g.beta j

/--
Scaled phase polynomial `g_h(n) = g(h n)` (PDF Piece III / `eq:piece-III-fixed`).
Coefficient-wise: `(g_h)_j = β_j h^j`.
-/
def compMul (h : ℕ) : CirclePoly d where
  beta := fun j => g.beta j * (h : ℝ) ^ (j : ℕ)

/-- Distance to the nearest integer `‖x‖_{ℝ/ℤ}`. -/
def distToInt (x : ℝ) : ℝ := |x - round x|

/--
`‖g‖_{C^∞[N]}`, unpacked as in PDF Definition 1:
for each `j = 1,…,d`, the quantity `N^j ‖β_j‖_{ℝ/ℤ}`; we take the max.
-/
def cInfinityNorm (N : ℕ) : ℝ :=
  ((List.ofFn fun j : Fin (d + 1) =>
      if (j : ℕ) = 0 then (0 : ℝ)
      else (N : ℝ) ^ (j : ℕ) * distToInt (g.beta j)).maximum).getD 0

end CirclePoly

instance {d : ℕ} : HSMul ℤ (CirclePoly d) (CirclePoly d) where
  hSMul := fun k g => g.smul k

/--
Positive integral solution of `n₁⋯nₛ = m₁⋯mₛ` with entries in `[1,N]`
(PDF §2.1, set `V`).
-/
structure Sol (s N : ℕ) where
  n : Fin s → ℕ
  m : Fin s → ℕ
  hn : ∀ i, 1 ≤ n i ∧ n i ≤ N
  hm : ∀ i, 1 ≤ m i ∧ m i ≤ N
  hprod : (∏ i, n i) = (∏ i, m i)

/-- The ambient set `V` is the type of all solutions. -/
abbrev V (s N : ℕ) := Sol s N

namespace Sol

variable {s N : ℕ} (x : Sol s N)

/--
Membership in `ℱ_i` (PDF §2.1): `gcd(n₁, m_i) ≥ A`.
Requires `0 < s` (paper always has `s ≥ 2`).
-/
def memF (A : ℕ) (i : Fin s) (h0 : 0 < s := by omega) : Prop :=
  A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m i)

/-- Diagonal condition `n₁ = m₁`. -/
def onDiag (h0 : 0 < s := by omega) : Prop :=
  x.n ⟨0, h0⟩ = x.m ⟨0, h0⟩

/-- Swap the two sides of the product equation. -/
def swap : Sol s N where
  n := x.m
  m := x.n
  hn := x.hm
  hm := x.hn
  hprod := x.hprod.symm

@[simp] theorem swap_swap : x.swap.swap = x := rfl

end Sol

@[ext] theorem Sol.ext {s N : ℕ} {x y : Sol s N} (hn : x.n = y.n) (hm : x.m = y.m) :
    x = y := by
  cases x; cases y; cases hn; cases hm; rfl

/-- Involution swapping the two sides of a solution. -/
def solSwapEquiv (s N : ℕ) : Sol s N ≃ Sol s N where
  toFun := Sol.swap
  invFun := Sol.swap
  left_inv := Sol.swap_swap
  right_inv := Sol.swap_swap

/-- Phase weight `∏_i e(g(n_i)) conj(e(g(m_i)))` (PDF `\gprod`). -/
noncomputable def phaseWeight {d s N : ℕ} (g : CirclePoly d) (x : Sol s N) : ℂ :=
  ∏ i : Fin s, g.ePhase (x.n i) * starRingEnd ℂ (g.ePhase (x.m i))

theorem phaseWeight_swap {d s N : ℕ} (g : CirclePoly d) (x : Sol s N) :
    phaseWeight g x.swap = starRingEnd ℂ (phaseWeight g x) := by
  simp only [phaseWeight, Sol.swap, map_prod, map_mul, starRingEnd_self_apply]
  refine Finset.prod_congr rfl fun _ _ => mul_comm _ _

/-- `S_g(ℱ)` (PDF `(1)`). -/
noncomputable def Sg {d s N : ℕ} (g : CirclePoly d) (F : Finset (Sol s N)) : ℂ :=
  ∑ x ∈ F, phaseWeight g x

/--
Unbalanced solutions of `n₁⋯n_{s₁} = m₁⋯m_{s₂}` in `[1,N]`
(PDF Corollary mixed-moment expansion).
-/
structure UnbalSol (s1 s2 N : ℕ) where
  n : Fin s1 → ℕ
  m : Fin s2 → ℕ
  hn : ∀ i, 1 ≤ n i ∧ n i ≤ N
  hm : ∀ j, 1 ≤ m j ∧ m j ≤ N
  hprod : (∏ i, n i) = (∏ j, m j)

/-- Bounded tuples used to present `UnbalSol` as a subtype of a finite type. -/
abbrev UnbalTuple (k N : ℕ) := Fin k → Finset.Icc (1 : ℕ) N

def UnbalRaw (s1 s2 N : ℕ) :=
  { p : UnbalTuple s1 N × UnbalTuple s2 N //
    (∏ i, (p.1 i : ℕ)) = (∏ j, (p.2 j : ℕ)) }

instance (k N : ℕ) : Fintype (UnbalTuple k N) :=
  inferInstanceAs (Fintype (Fin k → Finset.Icc (1 : ℕ) N))

instance (s1 s2 N : ℕ) : Fintype (UnbalRaw s1 s2 N) :=
  Subtype.fintype _

private lemma mem_Icc_iff_bounds_unbal {N n : ℕ} :
    n ∈ Finset.Icc 1 N ↔ 1 ≤ n ∧ n ≤ N := by
  simp [Finset.mem_Icc]

def UnbalRaw.toUnbalSol {s1 s2 N : ℕ} (p : UnbalRaw s1 s2 N) : UnbalSol s1 s2 N where
  n := fun i => (p.val.1 i : ℕ)
  m := fun j => (p.val.2 j : ℕ)
  hn := fun i => (mem_Icc_iff_bounds_unbal).1 (p.val.1 i).property
  hm := fun j => (mem_Icc_iff_bounds_unbal).1 (p.val.2 j).property
  hprod := p.property

def UnbalSol.toRaw {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) : UnbalRaw s1 s2 N :=
  ⟨(fun i => ⟨x.n i, (mem_Icc_iff_bounds_unbal).2 (x.hn i)⟩,
    fun j => ⟨x.m j, (mem_Icc_iff_bounds_unbal).2 (x.hm j)⟩), by
    simpa using x.hprod⟩

@[simp] theorem UnbalRaw.toUnbalSol_toRaw {s1 s2 N : ℕ} (x : UnbalSol s1 s2 N) :
    (x.toRaw).toUnbalSol = x := by
  cases x
  rfl

@[simp] theorem UnbalSol.toRaw_toUnbalSol {s1 s2 N : ℕ} (p : UnbalRaw s1 s2 N) :
    (p.toUnbalSol).toRaw = p := by
  refine Subtype.ext ?_
  ext <;> rfl

def unbalEquivRaw (s1 s2 N : ℕ) : UnbalSol s1 s2 N ≃ UnbalRaw s1 s2 N where
  toFun := UnbalSol.toRaw
  invFun := UnbalRaw.toUnbalSol
  left_inv := UnbalRaw.toUnbalSol_toRaw
  right_inv := UnbalSol.toRaw_toUnbalSol

instance (s1 s2 N : ℕ) : Fintype (UnbalSol s1 s2 N) :=
  Fintype.ofEquiv (UnbalRaw s1 s2 N) (unbalEquivRaw s1 s2 N).symm

/-- `Sol` is the balanced case of `UnbalSol`. -/
def Sol.toUnbal {s N : ℕ} (x : Sol s N) : UnbalSol s s N where
  n := x.n
  m := x.m
  hn := x.hn
  hm := x.hm
  hprod := x.hprod

def UnbalSol.toSol {s N : ℕ} (x : UnbalSol s s N) : Sol s N where
  n := x.n
  m := x.m
  hn := x.hn
  hm := x.hm
  hprod := x.hprod

@[simp] theorem Sol.toUnbal_toSol {s N : ℕ} (x : Sol s N) :
    x.toUnbal.toSol = x := by
  cases x
  rfl

@[simp] theorem UnbalSol.toSol_toUnbal {s N : ℕ} (x : UnbalSol s s N) :
    x.toSol.toUnbal = x := by
  cases x
  rfl

def solEquivUnbal (s N : ℕ) : Sol s N ≃ UnbalSol s s N where
  toFun := Sol.toUnbal
  invFun := UnbalSol.toSol
  left_inv := Sol.toUnbal_toSol
  right_inv := UnbalSol.toSol_toUnbal

instance (s N : ℕ) : Fintype (Sol s N) :=
  Fintype.ofEquiv (UnbalSol s s N) (solEquivUnbal s N).symm

/-- Phase weight on an unbalanced tuple (PDF mixed-moment expansion). -/
noncomputable def mixedWeight {d s1 s2 N : ℕ} (g : CirclePoly d)
    (x : UnbalSol s1 s2 N) : ℂ :=
  (∏ i, g.ePhase (x.n i)) * (∏ j, starRingEnd ℂ (g.ePhase (x.m j)))

/--
Unnormalised mixed moment after Steinhaus orthogonality:
sum of `mixedWeight` over `n₁⋯n_{s₁}=m₁⋯m_{s₂}` in `[1,N]`.
This *is* the expansion in the PDF Corollary proof; no extra axiom.
-/
noncomputable def mixedU (d s1 s2 N : ℕ) (g : CirclePoly d) : ℂ :=
  ∑ x : UnbalSol s1 s2 N, mixedWeight g x

/-- Exponent in `𝒬(N,s) = (2s log N)^{3s²}`. -/
def tailQExp (s : ℕ) : ℕ := 3 * s ^ 2

/--
`𝒬(N,s) = (2s log N)^{3s²}`
(PDF, before Proposition 1).

The exponent `3s²` is large enough for every divisor polylog in the proof
(the largest explicit power is `(2s log N)^{3s²-2}` on `I₁` Pieces I/II).
-/
noncomputable def tailQ (N s : ℕ) : ℝ :=
  (2 * (s : ℝ) * Real.log (N : ℝ)) ^ tailQExp s

/--
Unnormalised moment `U_s(N)`.  Defined as the real part of `S_g(V)`,
the combinatorial expansion in PDF Lemma 2.  (The paper's Steinhaus
expectation is this quantity; we do not axiomatise a probability space.)
The sum is real because swapping `(n,m)` conjugates the phase weight.
-/
noncomputable def U (d s N : ℕ) (g : CirclePoly d) : ℝ :=
  (∑ x : Sol s N, phaseWeight g x).re

/-- Normalised moment `ℳ_s(N) = N^{-s} U_s(N) = 𝔼|S_N|^{2s}` (PDF §2). -/
noncomputable def M (d s N : ℕ) (g : CirclePoly d) : ℝ :=
  U d s N g / (N : ℝ) ^ s

/--
Normalised mixed moment `𝔼[S_N^{s₁} \overline{S_N}^{s₂}]`
`= N^{-(s₁+s₂)/2} · mixedU` (PDF Corollary proof).
-/
noncomputable def mixedM (d s1 s2 N : ℕ) (g : CirclePoly d) : ℂ :=
  (Real.rpow (N : ℝ) (-((s1 + s2 : ℝ) / 2))) • mixedU d s1 s2 N g

/-- Ordered positive factorizations of `n` into exactly `k` factors. -/
def OrderedFactors (k n : ℕ) :=
  { f : Fin k → ℕ // (∀ i, 0 < f i) ∧ (∏ i, f i) = n }

/-- Each factor divides `n`, hence is `≤ n` when `n ≠ 0`. -/
theorem OrderedFactors.factor_le {k n : ℕ} (hn : n ≠ 0)
    (f : OrderedFactors k n) (i : Fin k) : f.val i ≤ n := by
  have hprod : (∏ j, f.val j) = n := f.property.2
  have hdvd : f.val i ∣ ∏ j, f.val j :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [hprod] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd

/-- No positive factorization of `0`. -/
theorem OrderedFactors.isEmpty_zero (k : ℕ) : IsEmpty (OrderedFactors k 0) :=
  ⟨fun f => by
    have hprod : (∏ i, f.val i) = 0 := f.property.2
    by_cases hk : k = 0
    · subst hk
      simp at hprod
    · have hpos : 0 < ∏ i, f.val i :=
        Finset.prod_pos fun i _ => f.property.1 i
      omega⟩

instance (k : ℕ) : IsEmpty (OrderedFactors k 0) :=
  OrderedFactors.isEmpty_zero k

/-- `OrderedFactors` is finite (as a `Fintype`). -/
instance (k n : ℕ) : Fintype (OrderedFactors k n) := by
  by_cases hn : n = 0
  · subst hn
    exact Fintype.ofIsEmpty (α := OrderedFactors k 0)
  · refine Fintype.ofInjective
      (fun f : OrderedFactors k n =>
        fun i => (⟨f.val i, Nat.lt_succ_of_le (OrderedFactors.factor_le hn f i)⟩ :
          Fin (n + 1)))
      ?_
    intro f g hfg
    refine Subtype.ext ?_
    funext i
    have := congrArg (fun φ => (φ i).val) hfg
    simpa using this

/--
`ℓ`-fold divisor function `τ_ℓ` (PDF Notation / Lemma 1):
number of ordered positive `ℓ`-factorizations.
-/
def tau (k n : ℕ) : ℕ := Fintype.card (OrderedFactors k n)

/-- Absolute `≪`: `|X| ≤ C Y` for some absolute `C > 0`. -/
def IsAbsLL (X Y : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ |X| ≤ C * Y

/--
Pointwise packaging of `|X| ≤ C Y` for some `C > 0`.
**Caution:** as a standalone predicate on fixed `X,Y` this is weak
(take `C = |X|/Y` when `Y > 0`). A true Vinogradov `≪_d` needs the
constant quantified *outside* any `∀` over the family (see
`exponential_dichotomy`). The unused `_d` only documents intended dependence.
-/
def IsLLDep (_d : ℕ) (X Y : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ |X| ≤ C * Y

/-- Bound of shape `δ^{-O_d(1)}` for `0 < δ < 1`. -/
def IsDeltaPowOd (_d : ℕ) (X δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ |X| ≤ Real.rpow δ (-C)

/-- PDF error size `δ^{1/2} N^s 𝒬(N,s)`. -/
noncomputable def errorSize (N s : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt δ * (N : ℝ) ^ s * tailQ N s

/-- Main term `(s-1)! N^s` on a single `ℱ_i`. -/
noncomputable def mainTermF (s N : ℕ) : ℝ :=
  (Nat.factorial (s - 1) : ℝ) * (N : ℝ) ^ s

end RMFLean
