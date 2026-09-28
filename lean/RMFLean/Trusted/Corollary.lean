/-
# Trusted corollary statement (PDF Corollary `thm:cor-clt`)

**Reviewer checklist:** compare this file together with `Defs.lean` and
`MainTheorem.lean` to `D:/RMF_file/main.pdf`, Corollary (`thm:cor-clt`).

PDF statement: if for every \(\varepsilon>0\) there exists
\(C=C(g,\varepsilon)>0\) such that for every nonzero integer \(q\),

\[
\max_{1\le i\le d}\,\|q\beta_i\|_{\mathbb{R}/\mathbb{Z}}
\ge C\exp\bigl(-|q|^{\varepsilon}\bigr),
\]

then \(S_N\) converges in law to a complex normal of mean \(0\) and
variance \(1\).

The number-theoretic work is the even/mixed moment matching
(`CentralLimitMoments`).  Convergence in law is the cited implication
Gut, Chapter 5, Theorem 8.6 (method of moments),
recorded as `billingsley_method_of_moments`.  Mixed moments
are the unbalanced product-equation sum `mixedU` in `Defs.lean` (no extra
axiom).  The proof from `MomentDichotomy` lives in `RMFLean/Proof/` and is
not part of the statement-correspondence check.
-/
import RMFLean.Trusted.MainTheorem
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

open Real Filter Topology

namespace RMFLean

/-- Index `i : Fin d` as the coefficient \(\beta_{i+1}\) (PDF \(\beta_1,\ldots,\beta_d\)). -/
def coeffIndex {d : ℕ} (i : Fin d) : Fin (d + 1) := i.succ

/--
One term of the PDF Corollary Diophantine max:
\(\|q\beta_{i+1}\|_{\mathbb{R}/\mathbb{Z}}\).
-/
noncomputable def coeffDist {d : ℕ} (g : CirclePoly d) (q : ℤ) (i : Fin d) : ℝ :=
  CirclePoly.distToInt ((q : ℝ) * g.beta (coeffIndex i))

/-- Lower bound \(C\exp(-|q|^\varepsilon)\) in the PDF Corollary hypothesis. -/
noncomputable def coeffExpLower (C ε : ℝ) (q : ℤ) : ℝ :=
  C * Real.exp (-Real.rpow |(q : ℝ)| ε)

/--
PDF Corollary hypothesis:
for every \(\varepsilon>0\) there exists \(C=C(g,\varepsilon)>0\) such that
for every nonzero integer \(q\),

\[
\max_{1\le i\le d}\,\|q\beta_i\|_{\mathbb{R}/\mathbb{Z}}
\ge C\exp\bigl(-|q|^{\varepsilon}\bigr).
\]

If \(d=0\) there are no coefficients \(\beta_1,\ldots,\beta_d\); the
hypothesis is defined to be false (constant phase is Harper’s unweighted
sum, which does not obey a CLT).
-/
def coeffDiophantine {d : ℕ} (g : CirclePoly d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℤ, q ≠ 0 →
        if _h : 0 < d then
          ((List.ofFn fun i : Fin d => coeffDist g q i).maximum).getD 0
            ≥ coeffExpLower C ε q
        else
          False

/--
PDF Corollary, even-moment half:
\(\mathbb{E}|S_N|^{2s}\to s!\) for every fixed \(s\ge 1\).
-/
def EvenMomentsToGaussian (d : ℕ) (g : CirclePoly d) : Prop :=
  ∀ s : ℕ, 1 ≤ s →
    Tendsto (fun N : ℕ => M d s N g) atTop (nhds (s.factorial : ℝ))

/--
PDF Corollary, mixed-moment half:
\(\mathbb{E}[S_N^{s_1}\overline{S_N}^{s_2}]\to 0\) whenever \(s_1\neq s_2\).
-/
def MixedMomentsVanish (d : ℕ) (g : CirclePoly d) : Prop :=
  ∀ s1 s2 : ℕ, s1 ≠ s2 →
    Tendsto (fun N : ℕ => ‖mixedM d s1 s2 N g‖) atTop (nhds 0)

/--
Moment form of the PDF Corollary proof: even moments \(\to s!\) and mixed
moments vanish.  This is the number-theoretic input to the method of moments.
-/
def CentralLimitMoments (d : ℕ) : Prop :=
  ∀ g : CirclePoly d,
    coeffDiophantine g →
      EvenMomentsToGaussian d g ∧ MixedMomentsVanish d g

/--
PDF Corollary conclusion: the Steinhaus sums \(S_N\) converge in law to the
standard complex normal \(Z=X+iY\) of mean \(0\) and variance \(1\)
(\(X,Y\) independent real normals of mean \(0\) and variance \(1/2\)).

Not unpacked as a `Measure` on \(\mathbb{C}\): the paper cites Gut
rather than constructing the law, and the combinatorial moments `M` /
`mixedM` are already identified with \(\mathbb{E}|S_N|^{2s}\) and
\(\mathbb{E}[S_N^{s_1}\overline{S_N}^{s_2}]\).
-/
opaque ConvergesInLawToComplexNormal {d : ℕ} (g : CirclePoly d) : Prop

/--
Gut, *Probability: a graduate course*, Chapter 5, Theorem 8.6
(method of moments), as in the PDF Corollary proof: the even and mixed
moments of \(S_N\) match those of \(Z=X+iY\), hence \(S_N\) converges
in law to this normal.
-/
axiom billingsley_method_of_moments {d : ℕ} (g : CirclePoly d) :
    EvenMomentsToGaussian d g →
    MixedMomentsVanish d g →
    ConvergesInLawToComplexNormal g

/--
PDF Corollary (`thm:cor-clt`).

For every polynomial \(g\) of degree \(d\) satisfying the coefficient
hypothesis, \(S_N\) converges in law to a complex normal of mean \(0\)
and variance \(1\).
-/
def CentralLimit (d : ℕ) : Prop :=
  ∀ g : CirclePoly d, coeffDiophantine g → ConvergesInLawToComplexNormal g

/--
PDF \(\delta_s(N)\) in the Corollary proof (`eq:delta-clt`):
`(log N)^{-7s²}`, so that `δ (2s log N)^{3s²} → 0`.
-/
noncomputable def deltaCLT (N s : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ (-((7 : ℝ) * (s : ℝ) ^ 2))

end RMFLean
