/-
PDF §2.1: `V`, `ℱ_i`, and the sparse complement set.
-/
import RMFLean.Trusted.Defs
import RMFLean.Proof.Setup.SolFinite

noncomputable section

open Classical

namespace RMFLean

variable {s N : ℕ}

/-- Decidability of `memF` (needed for `Finset.filter`). -/
instance decidable_memF (A : ℕ) (i : Fin s) (h0 : 0 < s) (x : Sol s N) :
    Decidable (x.memF A i h0) :=
  inferInstanceAs (Decidable (A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m i)))

/-- The set `ℱ_i` as a finset (PDF §2.1). -/
def Ffinset (A : ℕ) (i : Fin s) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x => x.memF A i h0

/-- Sparse complement `V \ ⋃_i ℱ_i` as a finset (PDF Lemma 3). -/
def sparseComplementFinset (A : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x => ∀ i : Fin s, ¬ x.memF A i h0

/-- Membership form of the sparse complement. -/
theorem mem_sparseComplementFinset {A : ℕ} {h0 : 0 < s} {x : Sol s N} :
    x ∈ sparseComplementFinset (N := N) A h0 ↔
      ∀ i : Fin s, ¬ x.memF A i h0 := by
  simp [sparseComplementFinset]

end RMFLean
