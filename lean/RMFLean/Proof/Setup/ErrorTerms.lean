/-
Shared error shapes from the paper (`δ^{1/2} N^s 𝒬(N,s)`, Diophantine fork).
-/
import RMFLean.Trusted.MainTheorem

noncomputable section

namespace RMFLean

/-- PDF error size `δ^{1/2} N^s 𝒬(N,s)`. -/
noncomputable def deltaError (s N : ℕ) (δ : ℝ) : ℝ :=
  errorSize N s δ

/--
Standard dichotomy used by Propositions 1–2 / Lemmas 6,7,9:
either `|X| ≤ Cll · δ^{1/2} N^s 𝒬`, or the Diophantine alternative with fixed `Cd`
(to be chosen depending only on `d`).  The constant `Cll` is quantified
outside `∀ N, δ, g` at call sites.
-/
def AbsDichotomy (d N s : ℕ) (g : CirclePoly d) (δ Cd Cll : ℝ) (X : ℝ) : Prop :=
  |X| ≤ Cll * deltaError s N δ ∨ altDiophantine d N g δ Cd

/-- Same with a complex exponential sum. -/
def SgDichotomy (d N s : ℕ) (g : CirclePoly d) (δ Cd Cll : ℝ)
    {α : Type*} (F : Finset α) (w : α → ℂ) : Prop :=
  AbsDichotomy d N s g δ Cd Cll ‖∑ x ∈ F, w x‖

end RMFLean
