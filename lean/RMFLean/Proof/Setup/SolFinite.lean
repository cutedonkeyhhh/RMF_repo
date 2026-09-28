/-
Cardinality helper for `Sol` (PDF set `V`).
Finiteness of `Sol` is in `Trusted/Defs.lean` (via `UnbalSol`).
-/
import RMFLean.Trusted.Defs

noncomputable section

namespace RMFLean

/-- Cardinality of the full solution set `V`. -/
def cardV (s N : ℕ) : ℕ := Fintype.card (Sol s N)

end RMFLean
