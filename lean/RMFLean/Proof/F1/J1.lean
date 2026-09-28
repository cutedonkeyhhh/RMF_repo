/-
PDF Lemma 6 (`lem:J1`) — off-diagonal contribution on `ℱ_1`.
Uses trusted Lemma 5. Matrix fibres come from Lemma 4 (`solToMatrix`).

Fibre labels are the full off-diagonal matrix entries (`π₂ ∘ φ`):
a `MatrixParam` with diagonals normalised to `1`. This is *not* the
product pair `(A_i,B_i)` (that lost factorisation multiplicity).
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.SolFinite
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.PhaseNorm
import RMFLean.Proof.Setup.TauFactors
import RMFLean.Proof.Param.MatrixParam
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.GroupWithZero.Basic

noncomputable section

open Classical BigOperators Fintype

namespace RMFLean

/-- Off-diagonal part of `ℱ_1`: `n₁ ≠ m₁` and `gcd(n₁,m₁) ≥ A`. -/
def J1Support (s N A : ℕ) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    x.memF A ⟨0, h0⟩ h0 ∧ ¬ x.onDiag h0

/-! ### Off-diagonal fibre labels from Lemma 4 (`π₂ ∘ φ`) -/

/--
PDF `π₂`: keep off-diagonal entries, set diagonals to `1`.
Two matrices with the same off-diagonals give the same label.
-/
def offDiagNormalize {s : ℕ} (p : MatrixParam s) : MatrixParam s where
  a := fun i j => if i = j then 1 else p.a i j
  entries_pos := by
    intro i j
    split_ifs with hij
    · exact Nat.zero_lt_one
    · exact p.entries_pos i j

theorem offDiagNormalize_diag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    (offDiagNormalize p).a i i = 1 := by
  simp [offDiagNormalize]

theorem offDiagNormalize_off {s : ℕ} (p : MatrixParam s) {i j : Fin s}
    (hij : i ≠ j) : (offDiagNormalize p).a i j = p.a i j := by
  simp [offDiagNormalize, hij]

theorem offDiagNormalize_rowOffDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    (offDiagNormalize p).rowOffDiag i = p.rowOffDiag i := by
  simp only [MatrixParam.rowOffDiag]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h; simp [h] at hj
  exact offDiagNormalize_off p hij

theorem offDiagNormalize_colOffDiag {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    (offDiagNormalize p).colOffDiag i = p.colOffDiag i := by
  simp only [MatrixParam.colOffDiag]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by
    intro h; simp [h] at hj
  exact offDiagNormalize_off p hji

theorem offDiagNormalize_scale {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    (offDiagNormalize p).scale i = p.scale i := by
  simp [MatrixParam.scale, offDiagNormalize_rowOffDiag, offDiagNormalize_colOffDiag]

/-- PDF fibre labels: normalised off-diagonal matrices from `J1Support`. -/
noncomputable def J1Fibres (s N A : ℕ) : Finset (MatrixParam s) :=
  if h : 0 < s then
    (J1Support (s := s) (N := N) A h).image fun x =>
      offDiagNormalize (solToMatrix x)
  else
    ∅

theorem mem_J1Fibres_iff {s N A : ℕ} (h0 : 0 < s) (k : MatrixParam s) :
    k ∈ J1Fibres s N A ↔
      ∃ x ∈ J1Support (s := s) (N := N) A h0,
        offDiagNormalize (solToMatrix x) = k := by
  simp only [J1Fibres, h0, ↓reduceDIte, Finset.mem_image]

/-- `M_i = max(A_i,B_i)` from a fibre label (already a matrix). -/
abbrev keyScale {s : ℕ} (k : MatrixParam s) (i : Fin s) : ℕ :=
  k.scale i

theorem keyScale_eq_scale {s : ℕ} (p : MatrixParam s) (i : Fin s) :
    keyScale (offDiagNormalize p) i = p.scale i :=
  offDiagNormalize_scale p i

/--
Parameterized head fibre: lower endpoint `H`, upper `N/M₁`
(PDF `a₁₁∈[A,N/M₁]` for Lemma 6; Piece III uses `H=A/h`, `N↦N/h`).
-/
def keyHeadFibre {s : ℕ} (k : MatrixParam s)
    (N H : ℕ) (h0 : 0 < s) : Finset ℕ :=
  Finset.Icc H (N / keyScale k ⟨0, h0⟩)

/-- Inner `a₁₁` exponential sum on an off-diagonal fibre. -/
noncomputable def J1InnerSum {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) : ℂ :=
  ∑ a11 ∈ keyHeadFibre k N A h0,
    g.ePhase (a11 * k.rowOffDiag ⟨0, h0⟩) *
      starRingEnd ℂ (g.ePhase (a11 * k.colOffDiag ⟨0, h0⟩))

/-- Trivial number of choices for `a₂₂,…,aₛₛ`. -/
noncomputable def J1TailWeight {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) : ℝ :=
  ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
    ((N / keyScale k i : ℕ) : ℝ)

/-- Nonnegative contribution of one off-diagonal fibre. -/
noncomputable def J1FibreContribution {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) : ℝ :=
  ‖J1InnerSum g k N A h0‖ * J1TailWeight k N h0

/--
Scaled head fibre at height `h` (PDF `eq:piece-III-matrix`):
exact integer cut `A ≤ h b` and `h b M₁ ≤ N` with `b ≥ 1`
(equivalent to the rescaled `fibreB` condition; avoids `Nat`/`A/h` mismatch).
-/
def keyHeadFibreScaled {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) : Finset ℕ :=
  if 1 ≤ h then
    (Finset.Icc 1 N).filter fun b =>
      A ≤ h * b ∧ h * b * keyScale k ⟨0, h0⟩ ≤ N
  else
    (∅ : Finset ℕ)

/-- Integer lower endpoint `⌈A/h⌉` for the scaled head range. -/
def scaledHeadLo (A h : ℕ) : ℕ := (A + h - 1) / h

theorem scaledHeadLo_le_iff {A h b : ℕ} (hh : 0 < h) :
    scaledHeadLo A h ≤ b ↔ A ≤ h * b := by
  simp only [scaledHeadLo]
  rw [Nat.div_le_iff_le_mul_add_pred hh]
  -- `A + h - 1 ≤ h * b + (h - 1)` ↔ `A ≤ h * b`
  cases h with
  | zero => cases hh
  | succ h' => simp

theorem scaledHeadLo_ge_one {A h : ℕ} (hA : 1 ≤ A) (hh : 1 ≤ h) :
    1 ≤ scaledHeadLo A h := by
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hle0 : scaledHeadLo A h ≤ 0 := Nat.le_of_eq h0
  have : A ≤ h * 0 := (scaledHeadLo_le_iff hh0).1 hle0
  simp only [Nat.mul_zero, Nat.le_zero_eq] at this
  exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hA)) this

/-- `⌈A/h⌉` is at least the real quotient `A/h`. -/
theorem scaledHeadLo_cast_ge (A h : ℕ) (hh : 0 < h) :
    (A : ℝ) / (h : ℝ) ≤ (scaledHeadLo A h : ℝ) := by
  have hAh : A ≤ h * scaledHeadLo A h :=
    (scaledHeadLo_le_iff hh).1 le_rfl
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 hh
  have hcast : (A : ℝ) ≤ (scaledHeadLo A h : ℝ) * (h : ℝ) := by
    have : (A : ℝ) ≤ (h : ℝ) * (scaledHeadLo A h : ℝ) := by exact_mod_cast hAh
    simpa [mul_comm] using this
  exact (div_le_iff₀ hhpos).2 hcast

/-- For `1 ≤ A` and `1 ≤ h`, `⌈A/h⌉ ≤ A`. -/
theorem scaledHeadLo_le_A {A h : ℕ} (_hA : 1 ≤ A) (hh : 1 ≤ h) :
    scaledHeadLo A h ≤ A := by
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  rw [scaledHeadLo_le_iff hh0]
  exact Nat.le_mul_of_pos_left A hh0

/-- Exact cut equals `Icc ⌈A/h⌉ (N/(h M₁))`. -/
theorem keyHeadFibreScaled_eq_Icc {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hA1 : 1 ≤ A) (hh : 1 ≤ h) :
    keyHeadFibreScaled k N A h h0 =
      Finset.Icc (scaledHeadLo A h) (N / (h * keyScale k ⟨0, h0⟩)) := by
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hlo1 := scaledHeadLo_ge_one hA1 hh
  ext b
  simp only [keyHeadFibreScaled, hh, ↓reduceIte, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro ⟨hbIcc, hA, hNM⟩
    refine ⟨(scaledHeadLo_le_iff hh0).2 hA, ?_⟩
    have hM : 0 < keyScale k ⟨0, h0⟩ := by simpa [keyScale] using k.scale_pos ⟨0, h0⟩
    have hhm : 0 < h * keyScale k ⟨0, h0⟩ := Nat.mul_pos hh0 hM
    exact (Nat.le_div_iff_mul_le hhm).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hNM)
  · intro ⟨hlo, hhi⟩
    have hM : 0 < keyScale k ⟨0, h0⟩ := by simpa [keyScale] using k.scale_pos ⟨0, h0⟩
    have hhm : 0 < h * keyScale k ⟨0, h0⟩ := Nat.mul_pos hh0 hM
    have hb1 : 1 ≤ b := le_trans hlo1 hlo
    have hA : A ≤ h * b := (scaledHeadLo_le_iff hh0).1 hlo
    have hNM : h * b * keyScale k ⟨0, h0⟩ ≤ N := by
      have := (Nat.le_div_iff_mul_le hhm).1 hhi
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hbN : b ≤ N :=
      le_trans hhi (Nat.div_le_self _ _)
    exact ⟨⟨hb1, hbN⟩, hA, hNM⟩

/-- The exact cut sits inside the usual `Icc (A/h) (N/(h M₁))` range. -/
theorem keyHeadFibreScaled_subset_Icc {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h)
    (hM : 0 < keyScale k ⟨0, h0⟩) :
    keyHeadFibreScaled k N A h h0 ⊆
      Finset.Icc (max 1 (A / h)) (N / (h * keyScale k ⟨0, h0⟩)) := by
  intro b hb
  simp only [keyHeadFibreScaled, hh, ↓reduceIte, Finset.mem_filter] at hb
  rcases hb with ⟨hbIcc, hA, hNM⟩
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hb1 := (Finset.mem_Icc.1 hbIcc).1
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · exact max_le_iff.2 ⟨hb1, Nat.div_le_of_le_mul hA⟩
  · have hhm : 0 < h * keyScale k ⟨0, h0⟩ := Nat.mul_pos hhpos hM
    exact (Nat.le_div_iff_mul_le hhm).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hNM)

theorem keyHeadFibreScaled_subset_Icc_one {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h)
    (hM : 0 < keyScale k ⟨0, h0⟩) :
    keyHeadFibreScaled k N A h h0 ⊆
      Finset.Icc 1 (N / (h * keyScale k ⟨0, h0⟩)) :=
  (keyHeadFibreScaled_subset_Icc k N A h h0 hh hM).trans
    (Finset.Icc_subset_Icc (le_max_left 1 (A / h)) le_rfl)

/-- If `h > N`, the cut `h·b·M₁ ≤ N` with `b,M₁ ≥ 1` is impossible. -/
theorem keyHeadFibreScaled_eq_empty_of_h_gt_N {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h) (hNlt : N < h) :
    keyHeadFibreScaled k N A h h0 = ∅ := by
  ext b
  simp only [keyHeadFibreScaled, hh, ↓reduceIte, Finset.notMem_empty,
    Finset.mem_filter, iff_false]
  intro hb
  rcases hb with ⟨hbIcc, _hA, hNM⟩
  have hb1 := (Finset.mem_Icc.1 hbIcc).1
  have hM : 1 ≤ keyScale k ⟨0, h0⟩ :=
    Nat.succ_le_of_lt (by simpa [keyScale] using k.scale_pos ⟨0, h0⟩)
  have hle : h ≤ N :=
    calc
      h = h * 1 * 1 := by ring
      _ ≤ h * b * keyScale k ⟨0, h0⟩ :=
        Nat.mul_le_mul (Nat.mul_le_mul_left h hb1) hM
      _ ≤ N := hNM
  exact (not_le_of_gt hNlt) hle

/--
Scaled inner sum for `g_h` on `keyHeadFibreScaled` (PDF head range at height `h`).
-/
noncomputable def J1InnerSumScaled {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) : ℂ :=
  ∑ a11 ∈ keyHeadFibreScaled k N A h h0,
    (g.compMul h).ePhase (a11 * k.rowOffDiag ⟨0, h0⟩) *
      starRingEnd ℂ
        ((g.compMul h).ePhase (a11 * k.colOffDiag ⟨0, h0⟩))

theorem J1InnerSumScaled_eq {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) (_hh : 1 ≤ h) :
    J1InnerSumScaled g k N A h h0 =
      ∑ a11 ∈ keyHeadFibreScaled k N A h h0,
        (g.compMul h).ePhase (a11 * k.rowOffDiag ⟨0, h0⟩) *
          starRingEnd ℂ
            ((g.compMul h).ePhase (a11 * k.colOffDiag ⟨0, h0⟩)) := rfl

/-- Trivial majorant: each scaled head summand has modulus 1. -/
theorem norm_J1InnerSumScaled_le_card {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) :
    ‖J1InnerSumScaled g k N A h h0‖ ≤
      ((keyHeadFibreScaled k N A h h0).card : ℝ) := by
  have hsum :
      (∑ a11 ∈ keyHeadFibreScaled k N A h h0,
          ‖(g.compMul h).ePhase (a11 * k.rowOffDiag ⟨0, h0⟩) *
            starRingEnd ℂ
              ((g.compMul h).ePhase (a11 * k.colOffDiag ⟨0, h0⟩))‖) =
        ((keyHeadFibreScaled k N A h h0).card : ℝ) := by
    calc
      (∑ a11 ∈ keyHeadFibreScaled k N A h h0,
          ‖(g.compMul h).ePhase (a11 * k.rowOffDiag ⟨0, h0⟩) *
            starRingEnd ℂ
              ((g.compMul h).ePhase (a11 * k.colOffDiag ⟨0, h0⟩))‖)
          = ∑ _a11 ∈ keyHeadFibreScaled k N A h h0, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun a11 _ => ?_
            rw [norm_mul,
              norm_ePhase (g.compMul h) (a11 * k.rowOffDiag ⟨0, h0⟩)]
            change 1 *
                ‖star ((g.compMul h).ePhase (a11 * k.colOffDiag ⟨0, h0⟩))‖ = 1
            rw [norm_star,
              norm_ePhase (g.compMul h) (a11 * k.colOffDiag ⟨0, h0⟩), one_mul]
      _ = ((keyHeadFibreScaled k N A h h0).card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  exact (norm_sum_le _ _).trans (le_of_eq hsum)

/-- Scaled fibre contribution: ‖scaled inner‖ × **ambient** tail weight at `N`. -/
noncomputable def J1FibreContributionScaled {d s : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (N A h : ℕ) (h0 : 0 < s) : ℝ :=
  ‖J1InnerSumScaled g k N A h h0‖ * J1TailWeight k N h0

/--
Off-diagonal matrix labels from ambient **off-diagonal** solutions
(majorant for Piece III image fibres in PDF `eq:piece-III-matrix`).
Wider than `J1Fibres` (no `gcd ≥ A`), but restricted to `¬ onDiag` so that
`A₁ ≠ B₁` as in the PDF embedding.
-/
noncomputable def PieceIIIFibres (s N : ℕ) : Finset (MatrixParam s) :=
  if h : 0 < s then
    ((Finset.univ : Finset (Sol s N)).filter fun x => ¬ x.onDiag h).image
      fun x => offDiagNormalize (solToMatrix x)
  else
    (∅ : Finset (MatrixParam s))

/--
PDF `eq:piece-III-matrix` majorant over `PieceIIIFibres`
(head scaled by `h`, tails at ambient `N`).
-/
noncomputable def J1ScaledSumAtHeight (d s N A : ℕ) (g : CirclePoly d)
    (h : ℕ) : ℝ :=
  if hs : 2 ≤ s then
    ∑ k ∈ PieceIIIFibres s N, J1FibreContributionScaled g k N A h (by omega)
  else
    (0 : ℝ)

theorem J1Fibres_subset_PieceIIIFibres (s N A : ℕ) :
    J1Fibres s N A ⊆ PieceIIIFibres s N := by
  intro k hk
  simp only [PieceIIIFibres]
  split_ifs with h0
  · rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
    have hond : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx).2.2
    exact Finset.mem_image.2
      ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hond⟩, rfl⟩
  · simp only [J1Fibres, h0, ↓reduceDIte] at hk
    exact (Finset.notMem_empty k hk).elim

/-- Piece III fibres with `A₁ < B₁`. -/
noncomputable def PieceIIIFibres_A_lt_B (s N : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (PieceIIIFibres s N).filter fun k =>
    (k.rowOffDiag ⟨0, h0⟩) < (k.colOffDiag ⟨0, h0⟩)

/-- Piece III fibres with `B₁ < A₁`. -/
noncomputable def PieceIIIFibres_B_lt_A (s N : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (PieceIIIFibres s N).filter fun k =>
    (k.colOffDiag ⟨0, h0⟩) < (k.rowOffDiag ⟨0, h0⟩)

/-- Piece III fibres with `A₁ = B₁`. -/
noncomputable def PieceIIIFibres_A_eq_B (s N : ℕ) (h0 : 0 < s) :
    Finset (MatrixParam s) :=
  (PieceIIIFibres s N).filter fun k =>
    (k.rowOffDiag ⟨0, h0⟩) = (k.colOffDiag ⟨0, h0⟩)

/-- On off-diagonal sols, normalised labels satisfy `A₁ ≠ B₁`. -/
theorem PieceIIIFibres_A_ne_B {s N : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ PieceIIIFibres s N) :
    (k.rowOffDiag ⟨0, h0⟩) ≠ (k.colOffDiag ⟨0, h0⟩) := by
  simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
  rcases Finset.mem_image.1 hk with ⟨x, hx, rfl⟩
  have hnodiag : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx).2
  have hn :
      x.n ⟨0, h0⟩ =
        (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ *
          (solToMatrix x).rowOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.rowProd_eq_diag_mul_offDiag, solToMatrix_rowProd]
  have hm :
      x.m ⟨0, h0⟩ =
        (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ *
          (solToMatrix x).colOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.colProd_eq_diag_mul_offDiag, solToMatrix_colProd]
  intro heq
  have heq' :
      (solToMatrix x).rowOffDiag ⟨0, h0⟩ =
        (solToMatrix x).colOffDiag ⟨0, h0⟩ := by
    rw [← offDiagNormalize_rowOffDiag, ← offDiagNormalize_colOffDiag]
    simpa using heq
  have hdiag : x.onDiag h0 := by
    simp only [Sol.onDiag, hn, hm, heq']
  exact hnodiag hdiag

theorem PieceIIIFibres_A_eq_B_empty (s N : ℕ) (h0 : 0 < s) :
    PieceIIIFibres_A_eq_B s N h0 = ∅ := by
  exact Finset.filter_eq_empty_iff.2 fun k hk heq =>
    PieceIIIFibres_A_ne_B h0 hk heq

/--
Fibre weight with real head factor `N/M₁` (matches Lemma 5's `δ N/D`)
times the integer tail weight.
-/
noncomputable def J1FullWeight {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) : ℝ :=
  (N : ℝ) / (keyScale k ⟨0, h0⟩ : ℝ) * J1TailWeight k N h0

theorem J1TailWeight_nonneg {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) : 0 ≤ J1TailWeight k N h0 :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

theorem keyScale_le_N_of_mem_PieceIIIFibres {s N : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ PieceIIIFibres s N) (i : Fin s) :
    keyScale k i ≤ N := by
  simp only [PieceIIIFibres, h0, ↓reduceDIte] at hk
  rcases Finset.mem_image.1 hk with ⟨x, _, rfl⟩
  have hrow :
      (offDiagNormalize (solToMatrix x)).rowOffDiag i ≤ x.n i := by
    have hprod := solToMatrix_rowProd x i
    have hform :
        (solToMatrix x).a i i * (solToMatrix x).rowOffDiag i = x.n i := by
      simpa [MatrixParam.rowProd_eq_diag_mul_offDiag] using hprod
    have hdiag : 1 ≤ (solToMatrix x).a i i :=
      Nat.succ_le_of_lt ((solToMatrix x).entries_pos i i)
    have : (solToMatrix x).rowOffDiag i ≤
        (solToMatrix x).a i i * (solToMatrix x).rowOffDiag i :=
      Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one hdiag)
    simpa [offDiagNormalize_rowOffDiag, hform] using this
  have hcol :
      (offDiagNormalize (solToMatrix x)).colOffDiag i ≤ x.m i := by
    have hprod := solToMatrix_colProd x i
    have hform :
        (solToMatrix x).a i i * (solToMatrix x).colOffDiag i = x.m i := by
      simpa [MatrixParam.colProd_eq_diag_mul_offDiag] using hprod
    have hdiag : 1 ≤ (solToMatrix x).a i i :=
      Nat.succ_le_of_lt ((solToMatrix x).entries_pos i i)
    have : (solToMatrix x).colOffDiag i ≤
        (solToMatrix x).a i i * (solToMatrix x).colOffDiag i :=
      Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one hdiag)
    simpa [offDiagNormalize_colOffDiag, hform] using this
  have hscale :
      keyScale (offDiagNormalize (solToMatrix x)) i ≤ max (x.n i) (x.m i) := by
    simp only [keyScale, MatrixParam.scale]
    exact max_le_max hrow hcol
  exact hscale.trans (max_le (x.hn i).2 (x.hm i).2)

theorem J1TailWeight_one_le_of_mem_PieceIIIFibres {s N : ℕ} (h0 : 0 < s)
    {k : MatrixParam s} (hk : k ∈ PieceIIIFibres s N) :
    1 ≤ J1TailWeight k N h0 := by
  simp only [J1TailWeight]
  have hterm :
      ∀ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
        (1 : ℝ) ≤ ((N / keyScale k i : ℕ) : ℝ) := by
    intro i _
    have hpos : 0 < keyScale k i := by
      simpa [keyScale] using k.scale_pos i
    have hle : keyScale k i ≤ N := keyScale_le_N_of_mem_PieceIIIFibres h0 hk i
    exact_mod_cast (Nat.le_div_iff_mul_le hpos).2 (by simpa using hle)
  calc
    (1 : ℝ) = ∏ _i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s), (1 : ℝ) := by
      simp
    _ ≤ ∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
        ((N / keyScale k i : ℕ) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) hterm

theorem J1FullWeight_nonneg {s : ℕ} (k : MatrixParam s)
    (N : ℕ) (h0 : 0 < s) : 0 ≤ J1FullWeight k N h0 :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (J1TailWeight_nonneg k N h0)

/-- PDF unrestricted row-factor sum: `∏_i (N ∑_{n≤N} τ_{s-1}(n)/n)`. -/
noncomputable def J1RowFactorSum (s N : ℕ) : ℝ :=
  ∏ _i : Fin s,
    ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ))

noncomputable def J1SigmaWeight (s N A : ℕ) (h0 : 0 < s)
    (S : Finset (MatrixParam s)) : ℝ :=
  ∑ k ∈ S, J1FullWeight k N h0

/-- Long-fibre condition on an off-diagonal label. -/
def KeyIsLong {s : ℕ} (k : MatrixParam s)
    (N A : ℕ) (h0 : 0 < s) : Prop :=
  2 * A < N / keyScale k ⟨0, h0⟩

/-- Short-fibre condition on an off-diagonal label. -/
def KeyIsShort {s : ℕ} (k : MatrixParam s)
    (N A : ℕ) (h0 : 0 < s) : Prop :=
  A ≤ N / keyScale k ⟨0, h0⟩ ∧ N / keyScale k ⟨0, h0⟩ ≤ 2 * A

theorem key_long_or_short {s N A : ℕ} (k : MatrixParam s)
    (h0 : 0 < s) (hne : A ≤ N / keyScale k ⟨0, h0⟩) :
    KeyIsLong k N A h0 ∨ KeyIsShort k N A h0 := by
  simp only [KeyIsLong, KeyIsShort]
  omega

/-! ### Head nonempty -/

theorem J1Fibre_head_nonempty (s N A : ℕ) (k : MatrixParam s)
    (h0 : 0 < s) (hk : k ∈ J1Fibres s N A) (hA : 1 ≤ A) :
    A ≤ N / keyScale k ⟨0, h0⟩ := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
  have hxF : x.memF A ⟨0, h0⟩ h0 := (Finset.mem_filter.1 hx).2.1
  have hxVH : x ∈ VH s N (A - 1) h0 := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ x, ?_⟩
    have : A ≤ Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) := hxF
    omega
  have hfibre := solToMatrix_head_fibre x h0 hxVH
  have ha_ge : A ≤ (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ := by
    have : A - 1 < (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ := hfibre.1
    omega
  have hle := le_trans ha_ge hfibre.2
  simpa [keyScale_eq_scale] using hle

/-! ### Rebuild Sol from off-diagonal matrix + diagonals -/

theorem MatrixParam.prod_rowOffDiag_eq_prod_colOffDiag {s : ℕ}
    (p : MatrixParam s) :
    (∏ i, p.rowOffDiag i) = (∏ i, p.colOffDiag i) := by
  have hrc : (∏ i, p.rowProd i) = (∏ i, p.colProd i) := by
    simp only [MatrixParam.rowProd, MatrixParam.colProd]
    rw [Finset.prod_comm]
  have hrc' :
      (∏ i, p.a i i * p.rowOffDiag i) =
        (∏ i, p.a i i * p.colOffDiag i) := by
    simpa [MatrixParam.rowProd_eq_diag_mul_offDiag,
      MatrixParam.colProd_eq_diag_mul_offDiag] using hrc
  have hpos : 0 < ∏ i, p.a i i :=
    Finset.prod_pos fun i _ => p.entries_pos i i
  simp_rw [Finset.prod_mul_distrib] at hrc'
  exact Nat.mul_left_cancel hpos hrc'

/-- Rebuild `(n,m)` from off-diagonal data of `p` and diagonal tuple `d`. -/
noncomputable def solFromOffDiag {s N : ℕ} (p : MatrixParam s) (d : Fin s → ℕ)
    (hd : ∀ i, 1 ≤ d i)
    (hle : ∀ i, d i * p.scale i ≤ N) : Sol s N where
  n := fun i => d i * p.rowOffDiag i
  m := fun i => d i * p.colOffDiag i
  hn := by
    intro i
    have hApos : 0 < p.rowOffDiag i :=
      Finset.prod_pos fun _ _ => p.entries_pos _ _
    exact ⟨one_le_mul_of_one_le_of_one_le (hd i) (Nat.succ_le_of_lt hApos),
      le_trans (Nat.mul_le_mul_left _ (le_max_left _ _)) (hle i)⟩
  hm := by
    intro i
    have hBpos : 0 < p.colOffDiag i :=
      Finset.prod_pos fun _ _ => p.entries_pos _ _
    exact ⟨one_le_mul_of_one_le_of_one_le (hd i) (Nat.succ_le_of_lt hBpos),
      le_trans (Nat.mul_le_mul_left _ (le_max_right _ _)) (hle i)⟩
  hprod := by
    have hr :
        (∏ i, d i * p.rowOffDiag i) =
          (∏ i, d i) * ∏ i, p.rowOffDiag i := by
      simp_rw [Finset.prod_mul_distrib]
    have hc :
        (∏ i, d i * p.colOffDiag i) =
          (∏ i, d i) * ∏ i, p.colOffDiag i := by
      simp_rw [Finset.prod_mul_distrib]
    rw [hr, hc, p.prod_rowOffDiag_eq_prod_colOffDiag]

theorem solFromOffDiag_n {s N : ℕ} (p : MatrixParam s) (d : Fin s → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hle : ∀ i, d i * p.scale i ≤ N) (i : Fin s) :
    (solFromOffDiag p d hd hle).n i = d i * p.rowOffDiag i := rfl

theorem solFromOffDiag_m {s N : ℕ} (p : MatrixParam s) (d : Fin s → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hle : ∀ i, d i * p.scale i ≤ N) (i : Fin s) :
    (solFromOffDiag p d hd hle).m i = d i * p.colOffDiag i := rfl

/-- After peeling diagonals, residuals are exactly the off-diagonal products. -/
theorem afterDiag_solFromOffDiag {s N : ℕ} (p : MatrixParam s)
    (d : Fin s → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hle : ∀ i, d i * p.scale i ≤ N)
    (hcop : p.CoprimeOffDiag) :
    (afterDiag (solFromOffDiag p d hd hle)).n = p.rowOffDiag ∧
      (afterDiag (solFromOffDiag p d hd hle)).m = p.colOffDiag := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have hgcd : diagGcd (solFromOffDiag p d hd hle) i = d i := by
      simp only [diagGcd, solFromOffDiag_n, solFromOffDiag_m]
      have hc : Nat.gcd (p.rowOffDiag i) (p.colOffDiag i) = 1 := hcop i
      simp [Nat.gcd_mul_left, hc]
    simp [afterDiag_n, solFromOffDiag_n, hgcd,
      Nat.mul_div_cancel_left _ (lt_of_lt_of_le Nat.zero_lt_one (hd i))]
  · have hgcd : diagGcd (solFromOffDiag p d hd hle) i = d i := by
      simp only [diagGcd, solFromOffDiag_n, solFromOffDiag_m]
      have hc : Nat.gcd (p.rowOffDiag i) (p.colOffDiag i) = 1 := hcop i
      simp [Nat.gcd_mul_left, hc]
    simp [afterDiag_m, solFromOffDiag_m, hgcd,
      Nat.mul_div_cancel_left _ (lt_of_lt_of_le Nat.zero_lt_one (hd i))]

/-! ### Parameter reduction -/

/-! ### Partial summation of `τ_{s-1}(n)/n` -/

noncomputable def posProdFinset (k N : ℕ) : Finset (Fin k → ℕ) :=
  piFinset fun _ : Fin k => Finset.Icc 1 N

noncomputable def posProdLEFinset (k N : ℕ) : Finset (Fin k → ℕ) :=
  (posProdFinset k N).filter fun f => (∏ i, f i) ≤ N

noncomputable def invProd (k : ℕ) (f : Fin k → ℕ) : ℝ :=
  (∏ i : Fin k, (f i : ℝ))⁻¹

theorem mem_posProdFinset_iff {k N : ℕ} {f : Fin k → ℕ} :
    f ∈ posProdFinset k N ↔ ∀ i, f i ∈ Finset.Icc 1 N := by
  simp [posProdFinset, Fintype.mem_piFinset]

theorem mem_posProdLEFinset_iff {k N : ℕ} {f : Fin k → ℕ} :
    f ∈ posProdLEFinset k N ↔
      (∀ i, f i ∈ Finset.Icc 1 N) ∧ (∏ i, f i) ≤ N := by
  simp [posProdLEFinset, posProdFinset, Fintype.mem_piFinset, and_assoc]

theorem invProd_eq_prod_inv {k : ℕ} {f : Fin k → ℕ}
    (hf : ∀ i, 0 < f i) : invProd k f = ∏ i : Fin k, (f i : ℝ)⁻¹ := by
  simp only [invProd]
  rw [← Finset.prod_inv_distrib]

theorem tau_div_eq_sum_invProd (k n : ℕ) (hn : 1 ≤ n) :
    (tau k n : ℝ) / (n : ℝ) =
      ∑ f : OrderedFactors k n, invProd k f.1 := by
  rw [tau_eq_card_ordered_cast]
  have hcard : (Fintype.card (OrderedFactors k n) : ℝ) =
      ∑ _f : OrderedFactors k n, (1 : ℝ) := by
    simpa using Fintype.card_eq_sum_ones (OrderedFactors k n)
  have hsplit :
      (∑ _f : OrderedFactors k n, (1 : ℝ)) / (n : ℝ) =
        ∑ f : OrderedFactors k n, (1 : ℝ) / (n : ℝ) := by
    rw [Finset.sum_div]
  rw [hcard, hsplit]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hpos : ∀ i, 0 < f.1 i := f.property.1
  have hprod : ∏ i : Fin k, (f.1 i : ℝ) = (n : ℝ) := by
    exact_mod_cast f.property.2
  simpa [invProd_eq_prod_inv hpos, hprod]

abbrev IccSubtype (N : ℕ) := {n // n ∈ Finset.Icc 1 N}

abbrev OrderedSigma (k N : ℕ) :=
  Σ n : IccSubtype N, OrderedFactors k n.val

theorem ordered_mem_posProdLE {k N : ℕ} (p : OrderedSigma k N) :
    p.2.1 ∈ posProdLEFinset k N := by
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [posProdFinset, Fintype.mem_piFinset]
    intro i
    have hn : (p.1 : ℕ) ≠ 0 :=
      ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp p.1.property).1)
    have hi := p.2.property.1 i
    have hle :=
      (OrderedFactors.factor_le hn p.2 i).trans (Finset.mem_Icc.mp p.1.property).2
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hi, hle⟩
  · simpa [p.2.property.2] using (Finset.mem_Icc.mp p.1.property).2

noncomputable def orderedProdEquiv (k N : ℕ) :
    OrderedSigma k N ≃ {f // f ∈ posProdLEFinset k N} where
  toFun p := ⟨p.2.1, ordered_mem_posProdLE p⟩
  invFun f :=
    let n := ∏ i : Fin k, f.1 i
    let hIcc : ∀ i, f.1 i ∈ Finset.Icc 1 N := (mem_posProdLEFinset_iff.mp f.property).1
    let hprod : (∏ i, f.1 i) ≤ N := (mem_posProdLEFinset_iff.mp f.property).2
    ⟨⟨n,
        Finset.mem_Icc.mpr
          ⟨Finset.one_le_prod' fun i _ => (Finset.mem_Icc.mp (hIcc i)).1, hprod⟩⟩,
      ⟨f.1, fun i => Nat.succ_le_iff.mp (Finset.mem_Icc.mp (hIcc i)).1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨n, hn⟩, ⟨f, hpos, hprod⟩⟩
    apply Sigma.ext
    · exact Subtype.ext hprod
    · -- Dependent second component: values agree, so `HEq` follows by subst.
      cases hprod
      rfl
  right_inv := by
    rintro ⟨f, _hf⟩
    rfl

theorem tau_harmonic_sum_eq_posProdLE (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)) =
      ∑ f ∈ posProdLEFinset k N, invProd k f := by
  have hinner :
      (∑ n ∈ Finset.Icc 1 N, (tau k n : ℝ) / (n : ℝ)) =
        ∑ n : IccSubtype N, (tau k (n : ℕ) : ℝ) / (n : ℝ) := by
    rw [← Finset.sum_coe_sort]
  have hsplit :
      ∑ n : IccSubtype N, (tau k (n : ℕ) : ℝ) / (n : ℝ) =
        ∑ n : IccSubtype N, ∑ f : OrderedFactors k n.val, invProd k f.1 := by
    refine Fintype.sum_congr _ _ fun n =>
      tau_div_eq_sum_invProd k n (Finset.mem_Icc.mp n.property).1
  have hfold :
      ∑ n : IccSubtype N, ∑ f : OrderedFactors k n.val, invProd k f.1 =
        ∑ p : OrderedSigma k N, invProd k p.2.1 :=
    (Fintype.sum_sigma (fun p : OrderedSigma k N => invProd k p.2.1)).symm
  have hequiv :
      ∑ p : OrderedSigma k N, invProd k p.2.1 =
        ∑ f ∈ posProdLEFinset k N, invProd k f := by
    calc
      ∑ p : OrderedSigma k N, invProd k p.2.1
          = ∑ t : {f // f ∈ posProdLEFinset k N}, invProd k t.1 :=
        Fintype.sum_equiv (orderedProdEquiv k N)
          (fun p => invProd k p.2.1) (fun t => invProd k t.1) fun _ => rfl
      _ = ∑ f ∈ posProdLEFinset k N, invProd k f :=
        Finset.sum_coe_sort (posProdLEFinset k N) (invProd k)
  rw [hinner, hsplit, hfold, hequiv]

theorem posProdLE_sum_le_posProd (k N : ℕ) :
    (∑ f ∈ posProdLEFinset k N, invProd k f) ≤
      ∑ f ∈ posProdFinset k N, invProd k f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun f hf _ => by
    have hpos : 0 < ∏ i : Fin k, (f i : ℝ) :=
      Finset.prod_pos fun i _ =>
        Nat.cast_pos.mpr
          (Nat.succ_le_iff.mp (Finset.mem_Icc.mp (mem_posProdFinset_iff.mp hf i)).1)
    unfold invProd
    exact inv_nonneg.mpr (le_of_lt hpos)

theorem posProdFinset_sum_eq_harmonic_pow (k N : ℕ) :
    (∑ f ∈ posProdFinset k N, invProd k f) =
      (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k := by
  have hinv :
      ∀ f ∈ posProdFinset k N, invProd k f = ∏ i : Fin k, (f i : ℝ)⁻¹ := by
    intro f hf
    have hpos : ∀ i, 0 < f i := fun i =>
      Nat.succ_le_iff.mp (Finset.mem_Icc.mp (mem_posProdFinset_iff.mp hf i)).1
    simpa using invProd_eq_prod_inv hpos
  calc
    ∑ f ∈ posProdFinset k N, invProd k f
        = ∑ f ∈ posProdFinset k N, ∏ i : Fin k, (f i : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun f hf => (hinv f hf)
    _ = ∏ i : Fin k, ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
        simpa [posProdFinset] using
          (Finset.sum_prod_piFinset (ι := Fin k) (s := Finset.Icc 1 N)
            (g := fun _ m => (m : ℝ)⁻¹))
    _ = (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k := by
      simp [Finset.prod_const, Fintype.card_fin]

theorem harmonic_Icc_le_one_add_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at this
  simpa using this

/--
Partial summation consequence of PDF Lemma 1:
`∑_{n≤N} τ_{s-1}(n)/n ≪_s (log N)^{s-1}`.
-/
theorem tau_harmonic_partial_sum (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 3 ≤ N →
        (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ)) ≤
          C * (Real.log N) ^ (s - 1) := by
  let k := s - 1
  have hk : 1 ≤ k := by omega
  refine ⟨(1 + 1 / Real.log 3) ^ k, ?_, fun N hN => ?_⟩
  · have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    exact pow_pos (by positivity) k
  · have hlogN : 0 < Real.log N :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hN))
    have hlog3le : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (Nat.cast_le.mpr hN)
    have hratio : 1 / Real.log N ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 3)) hlog3le
    have hcoef : 1 + 1 / Real.log N ≤ 1 + 1 / Real.log 3 := by
      linarith
    have hharm :
        (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k ≤ (1 + Real.log N) ^ k := by
      refine pow_le_pow_left₀ (by positivity) ?_ k
      exact harmonic_Icc_le_one_add_log N
    have hrewrite :
        (1 + Real.log N) ^ k = (Real.log N) ^ k * (1 + 1 / Real.log N) ^ k := by
      have hne : Real.log N ≠ 0 := hlogN.ne'
      have hmul : 1 + Real.log N = Real.log N * (1 + 1 / Real.log N) := by field_simp; ring
      rw [hmul, mul_pow]
    have hpowcoef : (1 + 1 / Real.log N) ^ k ≤ (1 + 1 / Real.log 3) ^ k :=
      pow_le_pow_left₀ (by positivity) hcoef k
    calc
      (∑ n ∈ Finset.Icc 1 N, (tau (s - 1) n : ℝ) / (n : ℝ))
          = ∑ f ∈ posProdLEFinset k N, invProd k f :=
        tau_harmonic_sum_eq_posProdLE k N
      _ ≤ ∑ f ∈ posProdFinset k N, invProd k f :=
        posProdLE_sum_le_posProd k N
      _ = (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ^ k :=
        posProdFinset_sum_eq_harmonic_pow k N
      _ ≤ (1 + Real.log N) ^ k := hharm
      _ = (Real.log N) ^ k * (1 + 1 / Real.log N) ^ k := hrewrite
      _ ≤ (1 + 1 / Real.log 3) ^ k * (Real.log N) ^ k := by
        have hmul :
            (Real.log N) ^ k * (1 + 1 / Real.log N) ^ k ≤
              (Real.log N) ^ k * (1 + 1 / Real.log 3) ^ k :=
          mul_le_mul_of_nonneg_left hpowcoef (pow_nonneg (le_of_lt hlogN) k)
        simpa [mul_comm] using hmul
      _ = (1 + 1 / Real.log 3) ^ k * (Real.log N) ^ (s - 1) := by
        simp [k, pow_mul, mul_comm]

/-- Unit-modulus diagonal phase factor from off-diagonal products. -/
noncomputable def diagPhase {d s : ℕ} (g : CirclePoly d) (p : MatrixParam s)
    (i : Fin s) (t : ℕ) : ℂ :=
  g.ePhase (t * p.rowOffDiag i) *
    starRingEnd ℂ (g.ePhase (t * p.colOffDiag i))

theorem norm_diagPhase {d s : ℕ} (g : CirclePoly d) (p : MatrixParam s)
    (i : Fin s) (t : ℕ) : ‖diagPhase g p i t‖ = 1 := by
  simp [diagPhase, norm_ePhase]

theorem phaseWeight_eq_diagPhase_prod {d s N : ℕ} (g : CirclePoly d)
    (x : Sol s N) :
    phaseWeight g x =
      ∏ i : Fin s, diagPhase g (solToMatrix x) i ((solToMatrix x).a i i) := by
  simp only [phaseWeight, diagPhase]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hn : x.n i = (solToMatrix x).a i i * (solToMatrix x).rowOffDiag i := by
    rw [← MatrixParam.rowProd_eq_diag_mul_offDiag, solToMatrix_rowProd]
  have hm : x.m i = (solToMatrix x).a i i * (solToMatrix x).colOffDiag i := by
    rw [← MatrixParam.colProd_eq_diag_mul_offDiag, solToMatrix_colProd]
  simp [hn, hm]

/-- Fibre label inherits off-diagonal coprimality from Lemma 4. -/
theorem J1Fibre_coprime {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) : k.CoprimeOffDiag := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, _, rfl⟩
  intro i
  simpa [MatrixParam.CoprimeOffDiag, offDiagNormalize_rowOffDiag,
    offDiagNormalize_colOffDiag] using solToMatrix_coprime x i

/-- On `J1Support`, the head off-diagonal products are unequal. -/
theorem J1Fibre_rowOff_ne_colOff {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) :
    k.rowOffDiag ⟨0, h0⟩ ≠ k.colOffDiag ⟨0, h0⟩ := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
  have hon : ¬ x.onDiag h0 := (Finset.mem_filter.1 hx).2.2
  intro heq
  apply hon
  have hr : x.n ⟨0, h0⟩ =
      (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ * (solToMatrix x).rowOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.rowProd_eq_diag_mul_offDiag, solToMatrix_rowProd]
  have hc : x.m ⟨0, h0⟩ =
      (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ * (solToMatrix x).colOffDiag ⟨0, h0⟩ := by
    rw [← MatrixParam.colProd_eq_diag_mul_offDiag, solToMatrix_colProd]
  simp only [Sol.onDiag]
  rw [hr, hc, ← offDiagNormalize_rowOffDiag, ← offDiagNormalize_colOffDiag, heq]

/-- Diagonal range for fibre `k`: head `[A,N/M₁]`, tails `[1,N/M_i]`. -/
def keyDiagBox {s : ℕ} (k : MatrixParam s) (N A : ℕ) (h0 : 0 < s) :
    Finset (Fin s → ℕ) :=
  Fintype.piFinset fun i =>
    if i = ⟨0, h0⟩ then keyHeadFibre k N A h0
    else Finset.Icc 1 (N / keyScale k i)

theorem mem_keyDiagBox_iff {s : ℕ} (k : MatrixParam s) (N A : ℕ)
    (h0 : 0 < s) (d : Fin s → ℕ) :
    d ∈ keyDiagBox k N A h0 ↔
      d ⟨0, h0⟩ ∈ keyHeadFibre k N A h0 ∧
        ∀ i : Fin s, i ≠ ⟨0, h0⟩ → d i ∈ Finset.Icc 1 (N / keyScale k i) := by
  simp only [keyDiagBox, Fintype.mem_piFinset]
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · simpa using hd ⟨0, h0⟩
    · intro i hi
      simpa [hi] using hd i
  · intro ⟨h0mem, htail⟩ i
    by_cases hi : i = ⟨0, h0⟩
    · simpa [hi] using h0mem
    · simpa [hi] using htail i hi

/-- Diagonals of a class representative land in the Lemma 4 box. -/
theorem J1_class_diag_mem_box {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (x : Sol s N)
    (hx : x ∈ (J1Support (s := s) (N := N) A h0).filter
      (fun y => offDiagNormalize (solToMatrix y) = k)) :
    (fun i => (solToMatrix x).a i i) ∈ keyDiagBox k N A h0 := by
  have hxF := Finset.mem_filter.1 hx
  have hkey : offDiagNormalize (solToMatrix x) = k := hxF.2
  have hsup := hxF.1
  have hmemF : x.memF A ⟨0, h0⟩ h0 := (Finset.mem_filter.1 hsup).2.1
  refine (mem_keyDiagBox_iff k N A h0 _).2 ⟨?_, ?_⟩
  · have ha : A ≤ (solToMatrix x).a ⟨0, h0⟩ ⟨0, h0⟩ := by
      have hs1 : 1 ≤ s := Nat.succ_le_of_lt h0
      simpa [Sol.memF, solToMatrix_a00 x hs1] using hmemF
    have hle := solToMatrix_diag_le_scale x ⟨0, h0⟩
    have hscale : (solToMatrix x).scale ⟨0, h0⟩ = keyScale k ⟨0, h0⟩ := by
      rw [← hkey, keyScale_eq_scale]
    refine Finset.mem_Icc.2 ⟨ha, ?_⟩
    simpa [keyHeadFibre, hscale] using hle
  · intro i hi
    have h1 : 1 ≤ (solToMatrix x).a i i :=
      Nat.succ_le_of_lt ((solToMatrix x).entries_pos i i)
    have hle := solToMatrix_diag_le_scale x i
    have hscale : (solToMatrix x).scale i = keyScale k i := by
      rw [← hkey, keyScale_eq_scale]
    refine Finset.mem_Icc.2 ⟨h1, ?_⟩
    simpa [hscale] using hle

theorem diagPhase_eq_of_key {d s : ℕ} (g : CirclePoly d)
    (p : MatrixParam s) (k : MatrixParam s) (i : Fin s) (t : ℕ)
    (hrow : p.rowOffDiag i = k.rowOffDiag i)
    (hcol : p.colOffDiag i = k.colOffDiag i) :
    diagPhase g p i t = diagPhase g k i t := by
  simp [diagPhase, hrow, hcol]

/-- Rebuild from a fibre label recovers the same off-diagonal normalisation. -/
theorem offDiagNormalize_solFromOffDiag_of_mem_fibres
    {s N A : ℕ} (h0 : 0 < s) {k : MatrixParam s}
    (hk : k ∈ J1Fibres s N A) (d : Fin s → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hle : ∀ i, d i * k.scale i ≤ N) :
    offDiagNormalize (solToMatrix (solFromOffDiag k d hd hle)) = k := by
  rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x0, _, rfl⟩
  set k : MatrixParam s := offDiagNormalize (solToMatrix x0)
  set x := solFromOffDiag k d hd hle
  have hcop : k.CoprimeOffDiag := by
    intro i
    have h := solToMatrix_coprime x0 i
    simpa [MatrixParam.CoprimeOffDiag, offDiagNormalize_rowOffDiag,
      offDiagNormalize_colOffDiag, k] using h
  have hres := afterDiag_solFromOffDiag k d hd hle hcop
  have hres0_n : (afterDiag x0).n = k.rowOffDiag := by
    funext i
    have ha : (solToMatrix x0).a i i = diagGcd x0 i := solToMatrix_diag_eq_gcd x0 i
    have hn :
        x0.n i = (solToMatrix x0).a i i * (solToMatrix x0).rowOffDiag i := by
      rw [← MatrixParam.rowProd_eq_diag_mul_offDiag, solToMatrix_rowProd]
    have hpos : 0 < (solToMatrix x0).a i i := (solToMatrix x0).entries_pos i i
    calc
      (afterDiag x0).n i = x0.n i / diagGcd x0 i := afterDiag_n x0 i
      _ = ((solToMatrix x0).a i i * (solToMatrix x0).rowOffDiag i) /
            (solToMatrix x0).a i i := by rw [hn, ha]
      _ = (solToMatrix x0).rowOffDiag i := Nat.mul_div_cancel_left _ hpos
      _ = k.rowOffDiag i := (offDiagNormalize_rowOffDiag _ _).symm
  have hres0_m : (afterDiag x0).m = k.colOffDiag := by
    funext i
    have ha : (solToMatrix x0).a i i = diagGcd x0 i := solToMatrix_diag_eq_gcd x0 i
    have hm :
        x0.m i = (solToMatrix x0).a i i * (solToMatrix x0).colOffDiag i := by
      rw [← MatrixParam.colProd_eq_diag_mul_offDiag, solToMatrix_colProd]
    have hpos : 0 < (solToMatrix x0).a i i := (solToMatrix x0).entries_pos i i
    calc
      (afterDiag x0).m i = x0.m i / diagGcd x0 i := afterDiag_m x0 i
      _ = ((solToMatrix x0).a i i * (solToMatrix x0).colOffDiag i) /
            (solToMatrix x0).a i i := by rw [hm, ha]
      _ = (solToMatrix x0).colOffDiag i := Nat.mul_div_cancel_left _ hpos
      _ = k.colOffDiag i := (offDiagNormalize_colOffDiag _ _).symm
  have hafter : afterDiag x = afterDiag x0 :=
    Sol.ext (by rw [hres.1, hres0_n]) (by rw [hres.2, hres0_m])
  refine MatrixParam.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp [offDiagNormalize_diag]
  · have hx :
        (solToMatrix x).a i j = (solToMatrixCore (afterDiag x)).a i j :=
      solToMatrix_a_off x i j hij
    have hx0 :
        (solToMatrix x0).a i j = (solToMatrixCore (afterDiag x0)).a i j :=
      solToMatrix_a_off x0 i j hij
    simp only [offDiagNormalize, hij, ↓reduceIte, hx, hx0, hafter]

theorem keyDiagBox_one_le {s : ℕ} (k : MatrixParam s) (N A : ℕ)
    (h0 : 0 < s) (hA : 1 ≤ A) {d : Fin s → ℕ}
    (hd : d ∈ keyDiagBox k N A h0) (i : Fin s) : 1 ≤ d i := by
  have h := (mem_keyDiagBox_iff k N A h0 d).1 hd
  by_cases hi : i = ⟨0, h0⟩
  · subst hi
    exact le_trans hA (Finset.mem_Icc.1 h.1).1
  · exact (Finset.mem_Icc.1 (h.2 i hi)).1

theorem keyDiagBox_mul_scale_le {s : ℕ} (k : MatrixParam s) (N A : ℕ)
    (h0 : 0 < s) {d : Fin s → ℕ}
    (hd : d ∈ keyDiagBox k N A h0) (i : Fin s) :
    d i * k.scale i ≤ N := by
  have h := (mem_keyDiagBox_iff k N A h0 d).1 hd
  have hMpos : 0 < k.scale i := k.scale_pos i
  have hdi : d i ≤ N / k.scale i := by
    by_cases hi : i = ⟨0, h0⟩
    · subst hi
      simpa [keyHeadFibre, keyScale] using (Finset.mem_Icc.1 h.1).2
    · simpa [keyScale] using (Finset.mem_Icc.1 (h.2 i hi)).2
  have : d i * k.scale i ≤ N :=
    (Nat.le_div_iff_mul_le hMpos).1 (by simpa [mul_comm] using hdi)
  exact this

noncomputable def solOfDiagBox {s N A : ℕ} (k : MatrixParam s)
    (h0 : 0 < s) (hA : 1 ≤ A) (d : Fin s → ℕ)
    (hd : d ∈ keyDiagBox k N A h0) : Sol s N :=
  solFromOffDiag k d
    (fun i => keyDiagBox_one_le k N A h0 hA hd i)
    (fun i => keyDiagBox_mul_scale_le k N A h0 hd i)

theorem solOfDiagBox_mem_class {s N A : ℕ} (k : MatrixParam s)
    (h0 : 0 < s) (hA : 1 ≤ A) (hk : k ∈ J1Fibres s N A)
    (d : Fin s → ℕ) (hd : d ∈ keyDiagBox k N A h0) :
    solOfDiagBox k h0 hA d hd ∈
      (J1Support (s := s) (N := N) A h0).filter
        (fun x => offDiagNormalize (solToMatrix x) = k) := by
  set x := solOfDiagBox k h0 hA d hd
  have hkey : offDiagNormalize (solToMatrix x) = k := by
    dsimp [x, solOfDiagBox]
    exact offDiagNormalize_solFromOffDiag_of_mem_fibres h0 hk d _ _
  have hcop := J1Fibre_coprime h0 hk
  have hne := J1Fibre_rowOff_ne_colOff h0 hk
  have hd0 := (mem_keyDiagBox_iff k N A h0 d).1 hd
  have hbox0 := Finset.mem_Icc.1 hd0.1
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩, hkey⟩
  · have hgcd :
        Nat.gcd (x.n ⟨0, h0⟩) (x.m ⟨0, h0⟩) = d ⟨0, h0⟩ := by
      dsimp [x, solOfDiagBox]
      simp only [solFromOffDiag_n, solFromOffDiag_m]
      exact gcd_mul_of_coprime _ _ _ (hcop ⟨0, h0⟩)
    simpa [Sol.memF, hgcd] using hbox0.1
  · intro hon
    have : x.n ⟨0, h0⟩ = x.m ⟨0, h0⟩ := hon
    dsimp [x, solOfDiagBox] at this
    simp only [solFromOffDiag_n, solFromOffDiag_m] at this
    have hpos : 0 < d ⟨0, h0⟩ :=
      lt_of_lt_of_le Nat.zero_lt_one (keyDiagBox_one_le k N A h0 hA hd _)
    exact hne (Nat.mul_left_cancel hpos this)

theorem solOfDiagBox_diag {s N A : ℕ} (k : MatrixParam s)
    (h0 : 0 < s) (hA : 1 ≤ A) (hk : k ∈ J1Fibres s N A)
    (d : Fin s → ℕ) (hd : d ∈ keyDiagBox k N A h0) (i : Fin s) :
    (solToMatrix (solOfDiagBox k h0 hA d hd)).a i i = d i := by
  have hcop := J1Fibre_coprime h0 hk
  set x := solOfDiagBox k h0 hA d hd
  have hgcd : diagGcd x i = d i := by
    dsimp [x, solOfDiagBox, diagGcd]
    simp only [solFromOffDiag_n, solFromOffDiag_m]
    exact gcd_mul_of_coprime _ _ _ (hcop i)
  rw [solToMatrix_diag_eq_gcd, hgcd]

theorem card_Icc_one (m : ℕ) : (Finset.Icc 1 m).card = m := by
  by_cases hm : 1 ≤ m
  · rw [Nat.card_Icc]
    omega
  · have : m = 0 := by omega
    subst this
    simp

/-- PDF first-diagonal length: `# {b} ≤ N/(h M₁)`. -/
theorem card_keyHeadFibreScaled_le {s : ℕ} (k : MatrixParam s)
    (N A h : ℕ) (h0 : 0 < s) (hh : 1 ≤ h)
    (hM : 0 < keyScale k ⟨0, h0⟩) :
    (keyHeadFibreScaled k N A h h0).card ≤
      N / (h * keyScale k ⟨0, h0⟩) := by
  have hsub := keyHeadFibreScaled_subset_Icc_one k N A h h0 hh hM
  exact (Finset.card_le_card hsub).trans (le_of_eq (card_Icc_one _))

/--
Class estimate (PDF fibre factorisation): phase sum over the fibre of `k`
is bounded by `J1FibreContribution`, via Lemma 4 exactness + `|e|=1`.
-/
theorem J1_class_phase_le_contribution {d s N A : ℕ} (g : CirclePoly d)
    (k : MatrixParam s) (h0 : 0 < s) (hA : 1 ≤ A)
    (hk : k ∈ J1Fibres s N A) :
    ‖∑ x ∈ (J1Support (s := s) (N := N) A h0).filter
        (fun x => offDiagNormalize (solToMatrix x) = k),
      phaseWeight g x‖ ≤
      J1FibreContribution g k N A h0 := by
  set F := (J1Support (s := s) (N := N) A h0).filter
    (fun x => offDiagNormalize (solToMatrix x) = k)
  set Box := keyDiagBox k N A h0
  set diagOf : Sol s N → (Fin s → ℕ) :=
    fun x => fun i => (solToMatrix x).a i i
  set D : Fin s → Finset ℕ := fun i =>
    if i = ⟨0, h0⟩ then keyHeadFibre k N A h0
    else Finset.Icc 1 (N / keyScale k i)
  have hBox : Box = Fintype.piFinset D := by
    simp only [Box, keyDiagBox, D]
  have himg : F.image diagOf = Box := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨x, hx, rfl⟩
      exact J1_class_diag_mem_box h0 x hx
    · intro hd
      refine Finset.mem_image.2 ⟨solOfDiagBox k h0 hA d hd, ?_, ?_⟩
      · exact solOfDiagBox_mem_class k h0 hA hk d hd
      · funext i
        exact solOfDiagBox_diag k h0 hA hk d hd i
  have hinj : Set.InjOn diagOf F := by
    intro x hx y hy heq
    have hkeyx : offDiagNormalize (solToMatrix x) = k :=
      (Finset.mem_filter.1 hx).2
    have hkeyy : offDiagNormalize (solToMatrix y) = k :=
      (Finset.mem_filter.1 hy).2
    have hmat : solToMatrix x = solToMatrix y := by
      refine MatrixParam.ext fun i j => ?_
      by_cases hij : i = j
      · subst hij
        exact congrFun heq i
      · have hxij : (solToMatrix x).a i j = k.a i j := by
          have := congrArg (fun p : MatrixParam s => p.a i j) hkeyx
          simpa [offDiagNormalize, hij] using this
        have hyij : (solToMatrix y).a i j = k.a i j := by
          have := congrArg (fun p : MatrixParam s => p.a i j) hkeyy
          simpa [offDiagNormalize, hij] using this
        simp [hxij, hyij]
    exact solToMatrix_injective hmat
  have hphase :
      ∀ x ∈ F,
        phaseWeight g x = ∏ i : Fin s, diagPhase g k i (diagOf x i) := by
    intro x hx
    have hkey : offDiagNormalize (solToMatrix x) = k :=
      (Finset.mem_filter.1 hx).2
    rw [phaseWeight_eq_diagPhase_prod g x]
    refine Finset.prod_congr rfl fun i _ => ?_
    simpa [diagOf] using
      diagPhase_eq_of_key g (solToMatrix x) k i _
        (by rw [← offDiagNormalize_rowOffDiag, hkey])
        (by rw [← offDiagNormalize_colOffDiag, hkey])
  have hsum :
      (∑ x ∈ F, phaseWeight g x) =
        ∑ d ∈ Box, ∏ i : Fin s, diagPhase g k i (d i) := by
    refine Finset.sum_bij (fun x _ => diagOf x) ?_ ?_ ?_ ?_
    · intro x hx
      exact J1_class_diag_mem_box h0 x hx
    · intro x hx y hy hxy
      exact hinj hx hy hxy
    · intro d hd
      refine ⟨solOfDiagBox k h0 hA d hd,
        solOfDiagBox_mem_class k h0 hA hk d hd, ?_⟩
      funext i
      simpa [diagOf] using solOfDiagBox_diag k h0 hA hk d hd i
    · intro x hx
      exact hphase x hx
  have hfactor :
      (∑ d ∈ Box, ∏ i : Fin s, diagPhase g k i (d i)) =
        ∏ i : Fin s, ∑ t ∈ D i, diagPhase g k i t := by
    rw [hBox]
    exact (Finset.prod_univ_sum D (fun i t => diagPhase g k i t)).symm
  rw [hsum, hfactor, norm_prod]
  have hi0 : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin s))
    (fun i => ‖∑ t ∈ D i, diagPhase g k i t‖) hi0]
  have hhead :
      ‖∑ t ∈ D ⟨0, h0⟩, diagPhase g k ⟨0, h0⟩ t‖ =
        ‖J1InnerSum g k N A h0‖ := by
    simp only [D, if_pos rfl, J1InnerSum, diagPhase]
  have htail :
      (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
          ‖∑ t ∈ D i, diagPhase g k i t‖) ≤
        J1TailWeight k N h0 := by
    have hpt :
        ∀ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
          ‖∑ t ∈ D i, diagPhase g k i t‖ ≤
            ((N / keyScale k i : ℕ) : ℝ) := by
      intro i hi
      have hine : i ≠ ⟨0, h0⟩ := (Finset.mem_erase.1 hi).1
      have hDi : D i = Finset.Icc 1 (N / keyScale k i) := by
        simp [D, hine]
      have hbound :
          ‖∑ t ∈ D i, diagPhase g k i t‖ ≤ ((D i).card : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        simp only [norm_diagPhase, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast le_rfl
      refine le_trans hbound ?_
      simp only [hDi, keyScale]
      exact_mod_cast (le_of_eq (card_Icc_one _))
    refine le_trans
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) hpt) ?_
    simp only [J1TailWeight, keyScale]
    exact le_of_eq rfl
  have hfin :
      ‖∑ t ∈ D ⟨0, h0⟩, diagPhase g k ⟨0, h0⟩ t‖ *
          (∏ i ∈ Finset.univ.erase (⟨0, h0⟩ : Fin s),
            ‖∑ t ∈ D i, diagPhase g k i t‖) ≤
        ‖J1InnerSum g k N A h0‖ * J1TailWeight k N h0 := by
    rw [hhead]
    exact mul_le_mul_of_nonneg_left htail (norm_nonneg _)
  simpa [J1FibreContribution] using hfin

/--
PDF Lemma 4 reduces `J₁` to the sum of off-diagonal fibre contributions.
One term per normalised off-diagonal matrix — no diagonal overcounting.
-/
theorem J1_parameter_reduction (d s N A : ℕ) (g : CirclePoly d)
    (hs : 2 ≤ s) (_hN : 3 ≤ N) (hA : 1 ≤ A) :
    ‖Sg g (J1Support (s := s) (N := N) A (by omega))‖ ≤
      ∑ k ∈ J1Fibres s N A,
        J1FibreContribution g k N A (by omega) := by
  set h0 : 0 < s := by omega
  set F := J1Support (s := s) (N := N) A h0
  set key : Sol s N → MatrixParam s := fun x => offDiagNormalize (solToMatrix x)
  have hFib : J1Fibres s N A = F.image key := by
    ext k
    constructor
    · intro hk
      rcases (mem_J1Fibres_iff h0 k).1 hk with ⟨x, hx, rfl⟩
      exact Finset.mem_image.2 ⟨x, hx, rfl⟩
    · intro hk
      rcases Finset.mem_image.1 hk with ⟨x, hx, rfl⟩
      exact (mem_J1Fibres_iff h0 _).2 ⟨x, hx, rfl⟩
  have hrep :
      Sg g F =
        ∑ k ∈ J1Fibres s N A,
          ∑ x ∈ F.filter (fun x => key x = k), phaseWeight g x := by
    rw [hFib]
    simpa [Sg, key] using
      (Finset.sum_fiberwise_of_maps_to (g := key) (s := F) (t := F.image key)
        (fun _ hx => Finset.mem_image_of_mem key hx) (phaseWeight g)).symm
  have htri :
      ‖Sg g F‖ ≤
        ∑ k ∈ J1Fibres s N A,
          ‖∑ x ∈ F.filter (fun x => key x = k), phaseWeight g x‖ := by
    simpa [hrep] using
      norm_sum_le (J1Fibres s N A) fun k =>
        ∑ x ∈ F.filter (fun x => key x = k), phaseWeight g x
  refine le_trans htri ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hclass := J1_class_phase_le_contribution (g := g) k h0 hA hk
  have hfilter :
      F.filter (fun x => key x = k) =
        F.filter (fun x => offDiagNormalize (solToMatrix x) = k) := by
    simp [key]
  simpa [hfilter] using hclass

-- `J1_long_short_sum_bound` / `J1_bound` are proved in `J1LongShort.lean`.

end RMFLean
