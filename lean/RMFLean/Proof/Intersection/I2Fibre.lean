/-
I₂ fibre estimate (user's exact-gcd form).

For fixed `h = gcd(m₁, m_ℓ)` with `ℓ ≠ 0` and `n₁ = m₁`:
  #{solutions} ≤ ∑_{n ≤ N^s} τ_s(n/h²) τ_s(n).
Then apply Lemma 1 + multiplicativity to the inner sum.
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.Setup.SolFinite
import RMFLean.Proof.Setup.SolutionSet
import RMFLean.Proof.Setup.TauFactors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open Classical Real

namespace RMFLean

/--
Exact-gcd fibre (user's form):
`n₁ = m₁` and `gcd(m₁, m_ℓ) = h` (hence also `gcd(n₁, m_ℓ) = h`).
-/
def I2Fibre (s N h : ℕ) (ℓ : Fin s) (h0 : 0 < s) : Finset (Sol s N) :=
  Finset.univ.filter fun x =>
    x.onDiag h0 ∧ Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) = h

/-- Common product `∏ mᵢ`. -/
def Sol.prodM {s N : ℕ} (x : Sol s N) : ℕ :=
  ∏ i, x.m i

/--
If `ℓ ≠ 0` and `gcd(m₁, m_ℓ) = h`, then `h² ∣ ∏ mᵢ`.
-/
theorem I2Fibre_hpow_dvd_prodM
    {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (hℓ : ℓ ≠ ⟨0, h0⟩) :
    h ^ 2 ∣ x.prodM := by
  have hx' := (Finset.mem_filter.1 hx).2
  have hgcd : Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) = h := hx'.2
  have h_m0 : h ∣ x.m ⟨0, h0⟩ := by
    rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have h_ml : h ∣ x.m ℓ := by
    rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  have hmul : h * h ∣ x.m ⟨0, h0⟩ * x.m ℓ := Nat.mul_dvd_mul h_m0 h_ml
  have hdiv : x.m ⟨0, h0⟩ * x.m ℓ ∣ x.prodM := by
    simp only [Sol.prodM]
    have h0in : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
    have hprod0 :
        (∏ i, x.m i) =
          x.m ⟨0, h0⟩ * ∏ i ∈ Finset.univ.erase ⟨0, h0⟩, x.m i :=
      (Finset.mul_prod_erase Finset.univ x.m h0in).symm
    have hlin : ℓ ∈ Finset.univ.erase ⟨0, h0⟩ := by
      simp [hℓ]
    have hprodℓ :
        (∏ i, x.m i) =
          x.m ⟨0, h0⟩ * x.m ℓ *
            ∏ i ∈ (Finset.univ.erase ⟨0, h0⟩).erase ℓ, x.m i := by
      rw [hprod0, (Finset.mul_prod_erase _ x.m hlin).symm, mul_assoc]
    rw [hprodℓ]
    exact dvd_mul_right _ _
  have : h * h ∣ x.prodM := dvd_trans hmul hdiv
  simpa [pow_two] using this

/-- Product of coordinates on `[1,N]` is in `[1, N^s]`. -/
theorem Sol.prodM_mem_Icc {s N : ℕ} (x : Sol s N) :
    x.prodM ∈ Finset.Icc 1 (N ^ s) := by
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · exact Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_one (x.hm i).1
  · calc
      x.prodM ≤ ∏ _i : Fin s, N := by
        refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) ?_
        intro i _; exact (x.hm i).2
      _ = N ^ s := by simp [Finset.prod_const]

/--
Scaled `m`-tuple after factoring out exact gcd `h` at indices `0` and `ℓ`.
-/
def I2Fibre.scaledM {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (_hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (_hℓ : ℓ ≠ ⟨0, h0⟩) : Fin s → ℕ :=
  fun i =>
    if i = ⟨0, h0⟩ then x.m ⟨0, h0⟩ / h
    else if i = ℓ then x.m ℓ / h
    else x.m i

theorem I2Fibre.gcd_eq {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    {x : Sol s N} (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0) :
    Nat.gcd (x.m ⟨0, h0⟩) (x.m ℓ) = h :=
  (Finset.mem_filter.1 hx).2.2

theorem I2Fibre.scaledM_pos {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (hℓ : ℓ ≠ ⟨0, h0⟩) (hh : 1 ≤ h) (i : Fin s) :
    0 < I2Fibre.scaledM (h := h) x hx hℓ i := by
  have hgcd := I2Fibre.gcd_eq (h := h) hx
  have h_m0 : h ∣ x.m ⟨0, h0⟩ := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have h_ml : h ∣ x.m ℓ := by rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  simp only [I2Fibre.scaledM]
  split_ifs with _h0i _hℓi
  · exact Nat.div_pos
      (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hm _).1) h_m0) hhpos
  · exact Nat.div_pos
      (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (x.hm _).1) h_ml) hhpos
  · exact lt_of_lt_of_le Nat.zero_lt_one (x.hm i).1

/-- Recover `m` from the scaled tuple by multiplying back by `h` at indices `0,ℓ`. -/
theorem I2Fibre.m_eq_mul_scaledM {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (hℓ : ℓ ≠ ⟨0, h0⟩) (i : Fin s) :
    x.m i =
      if i = ⟨0, h0⟩ then h * I2Fibre.scaledM (h := h) x hx hℓ i
      else if i = ℓ then h * I2Fibre.scaledM (h := h) x hx hℓ i
      else I2Fibre.scaledM (h := h) x hx hℓ i := by
  have hgcd := I2Fibre.gcd_eq (h := h) hx
  have h_m0 : h ∣ x.m ⟨0, h0⟩ := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have h_ml : h ∣ x.m ℓ := by rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  simp only [I2Fibre.scaledM]
  split_ifs with h0i hℓi
  · rw [h0i]; exact (Nat.mul_div_cancel' h_m0).symm
  · rw [hℓi]; exact (Nat.mul_div_cancel' h_ml).symm
  · rfl

theorem I2Fibre.scaledM_prod {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (hℓ : ℓ ≠ ⟨0, h0⟩) :
    (∏ i, I2Fibre.scaledM (h := h) x hx hℓ i) = x.prodM / h ^ 2 := by
  have hgcd := I2Fibre.gcd_eq (h := h) hx
  have h_m0 : h ∣ x.m ⟨0, h0⟩ := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  have h_ml : h ∣ x.m ℓ := by rw [← hgcd]; exact Nat.gcd_dvd_right _ _
  have h0in : (⟨0, h0⟩ : Fin s) ∈ Finset.univ := Finset.mem_univ _
  have hlin : ℓ ∈ Finset.univ.erase ⟨0, h0⟩ := by simp [hℓ]
  set rest := (Finset.univ.erase ⟨0, h0⟩).erase ℓ
  have hscaled0 : I2Fibre.scaledM (h := h) x hx hℓ ⟨0, h0⟩ = x.m ⟨0, h0⟩ / h := by
    simp [I2Fibre.scaledM]
  have hscaledℓ : I2Fibre.scaledM (h := h) x hx hℓ ℓ = x.m ℓ / h := by
    simp [I2Fibre.scaledM, hℓ]
  have hscaled_rest :
      ∀ i ∈ rest, I2Fibre.scaledM (h := h) x hx hℓ i = x.m i := by
    intro i hi
    have hi0 : i ≠ ⟨0, h0⟩ := by
      exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hiℓ : i ≠ ℓ := Finset.ne_of_mem_erase hi
    simp [I2Fibre.scaledM, hi0, hiℓ]
  have hprod_scaled :
      (∏ i, I2Fibre.scaledM (h := h) x hx hℓ i) =
        (x.m ⟨0, h0⟩ / h) * (x.m ℓ / h) * ∏ i ∈ rest, x.m i := by
    have h1 :
        (∏ i, I2Fibre.scaledM (h := h) x hx hℓ i) =
          I2Fibre.scaledM (h := h) x hx hℓ ⟨0, h0⟩ *
            ∏ i ∈ Finset.univ.erase ⟨0, h0⟩, I2Fibre.scaledM (h := h) x hx hℓ i :=
      (Finset.mul_prod_erase Finset.univ _ h0in).symm
    have h2 :
        (∏ i ∈ Finset.univ.erase ⟨0, h0⟩, I2Fibre.scaledM (h := h) x hx hℓ i) =
          I2Fibre.scaledM (h := h) x hx hℓ ℓ *
            ∏ i ∈ rest, I2Fibre.scaledM (h := h) x hx hℓ i :=
      (Finset.mul_prod_erase _ _ hlin).symm
    simp_rw [h1, h2, hscaled0, hscaledℓ, Finset.prod_congr rfl hscaled_rest, mul_assoc]
  have hprod_m :
      x.prodM = x.m ⟨0, h0⟩ * x.m ℓ * ∏ i ∈ rest, x.m i := by
    simp only [Sol.prodM]
    have h1 :
        (∏ i, x.m i) =
          x.m ⟨0, h0⟩ * ∏ i ∈ Finset.univ.erase ⟨0, h0⟩, x.m i :=
      (Finset.mul_prod_erase Finset.univ x.m h0in).symm
    have h2 :
        (∏ i ∈ Finset.univ.erase ⟨0, h0⟩, x.m i) =
          x.m ℓ * ∏ i ∈ rest, x.m i :=
      (Finset.mul_prod_erase _ x.m hlin).symm
    rw [h1, h2, mul_assoc]
  have hmul :
      (∏ i, I2Fibre.scaledM (h := h) x hx hℓ i) * h ^ 2 = x.prodM := by
    rw [hprod_scaled, hprod_m, pow_two]
    have hm0 : (x.m ⟨0, h0⟩ / h) * h = x.m ⟨0, h0⟩ := Nat.div_mul_cancel h_m0
    have hmℓ : (x.m ℓ / h) * h = x.m ℓ := Nat.div_mul_cancel h_ml
    calc
      (x.m ⟨0, h0⟩ / h) * (x.m ℓ / h) * (∏ i ∈ rest, x.m i) * (h * h)
          = ((x.m ⟨0, h0⟩ / h) * h) * ((x.m ℓ / h) * h) * (∏ i ∈ rest, x.m i) := by
            ring
      _ = x.m ⟨0, h0⟩ * x.m ℓ * (∏ i ∈ rest, x.m i) := by
            rw [hm0, hmℓ]
  have hh2 : h ^ 2 ≠ 0 := by
    have : 0 < h :=
      Nat.pos_of_dvd_of_pos h_m0 (lt_of_lt_of_le Nat.zero_lt_one (x.hm _).1)
    positivity
  exact Nat.eq_div_of_mul_eq_left hh2 hmul

/-- Pair of ordered factorizations attached to a fibre point. -/
def I2Fibre.toFactors {s N h : ℕ} {ℓ : Fin s} {h0 : 0 < s}
    (x : Sol s N) (hx : x ∈ I2Fibre (s := s) (N := N) h ℓ h0)
    (hℓ : ℓ ≠ ⟨0, h0⟩) (hh : 1 ≤ h) :
    OrderedFactors s (x.prodM / h ^ 2) × OrderedFactors s x.prodM :=
  (⟨I2Fibre.scaledM (h := h) x hx hℓ,
      ⟨I2Fibre.scaledM_pos (h := h) x hx hℓ hh,
        I2Fibre.scaledM_prod (h := h) x hx hℓ⟩⟩,
    ⟨x.n, ⟨fun i => lt_of_lt_of_le Nat.zero_lt_one (x.hn i).1,
      by simpa [Sol.prodM] using x.hprod⟩⟩)

/--
Rebuild an `OrderedFactors` after rewriting the product value.
-/
def OrderedFactors.congr {k n₁ n₂ : ℕ} (h : n₁ = n₂)
    (f : OrderedFactors k n₁) : OrderedFactors k n₂ :=
  ⟨f.val, ⟨f.property.1, by rw [← h]; exact f.property.2⟩⟩

/--
For fixed product `n`, fibre points inject into
`OrderedFactors s (n/h²) × OrderedFactors s n`.
-/
theorem I2_fibre_fixed_prod_card_le (s N h n : ℕ) (ℓ : Fin s)
    (h0 : 0 < s) (hh : 1 ≤ h) (hℓ : ℓ ≠ ⟨0, h0⟩) :
    ((I2Fibre (s := s) (N := N) h ℓ h0).filter
        fun x => x.prodM = n).card ≤
      Fintype.card (OrderedFactors s (n / h ^ 2)) *
        Fintype.card (OrderedFactors s n) := by
  set F := I2Fibre (s := s) (N := N) h ℓ h0
  set Fn := F.filter fun x => x.prodM = n
  let ψ : { x // x ∈ Fn } →
      OrderedFactors s (n / h ^ 2) × OrderedFactors s n := fun x =>
    let hxF : x.1 ∈ F := (Finset.mem_filter.1 x.2).1
    let hprod : x.1.prodM = n := (Finset.mem_filter.1 x.2).2
    let pr := I2Fibre.toFactors (h := h) x.1 hxF hℓ hh
    (OrderedFactors.congr (by rw [hprod]) pr.1,
      OrderedFactors.congr hprod pr.2)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have hxF : x.1 ∈ F := (Finset.mem_filter.1 x.2).1
    have hyF : y.1 ∈ F := (Finset.mem_filter.1 y.2).1
    have hm_scaled :
        I2Fibre.scaledM (h := h) x.1 hxF hℓ =
          I2Fibre.scaledM (h := h) y.1 hyF hℓ := by
      have := congrArg (fun p : OrderedFactors s (n / h ^ 2) × OrderedFactors s n =>
        p.1.val) hxy
      simpa [ψ, I2Fibre.toFactors, OrderedFactors.congr] using this
    have hn_tuple : x.1.n = y.1.n := by
      have := congrArg (fun p : OrderedFactors s (n / h ^ 2) × OrderedFactors s n =>
        p.2.val) hxy
      simpa [ψ, I2Fibre.toFactors, OrderedFactors.congr] using this
    have hm : x.1.m = y.1.m := by
      funext i
      rw [I2Fibre.m_eq_mul_scaledM (h := h) x.1 hxF hℓ i,
        I2Fibre.m_eq_mul_scaledM (h := h) y.1 hyF hℓ i, hm_scaled]
    exact Subtype.ext (Sol.ext hn_tuple hm)
  have hcard := Fintype.card_le_of_injective ψ hinj
  have hFn : Fn.card = Fintype.card { x // x ∈ Fn } := (Fintype.card_coe Fn).symm
  have hprod_card :
      Fintype.card (OrderedFactors s (n / h ^ 2) × OrderedFactors s n) =
        Fintype.card (OrderedFactors s (n / h ^ 2)) *
          Fintype.card (OrderedFactors s n) :=
    Fintype.card_prod _ _
  omega

/--
Combinatorial step (user B1 form): for `ℓ ≠ 0` and `h = gcd(m₁, m_ℓ)`,
`#(I2Fibre h) ≤ ∑_{m ≤ N^s/h²} τ_s(m) τ_s(h² m)`.
Only multiples `n = h² m` appear (exact-gcd fibres have `h² ∣ ∏ mᵢ`).
-/
theorem I2_fibre_le_tau_sum (s N h : ℕ) (ℓ : Fin s)
    (_hs : 2 ≤ s) (_hN : 3 ≤ N) (hh : 1 ≤ h)
    (hℓ : ℓ ≠ ⟨0, by omega⟩) :
    ((I2Fibre (s := s) (N := N) h ℓ (by omega)).card : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
        (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ) := by
  set h0 : 0 < s := by omega
  set F := I2Fibre (s := s) (N := N) h ℓ h0
  -- Every fibre point has `h² ∣ prodM` and `m := prodM/h² ≤ N^s/h²`.
  have hmem :
      ∀ x ∈ F, x.prodM / h ^ 2 ∈ Finset.Icc 1 (N ^ s / h ^ 2) := by
    intro x hx
    have hpow := I2Fibre_hpow_dvd_prodM (h := h) x hx hℓ
    have hprod_mem := Sol.prodM_mem_Icc (s := s) (N := N) x
    have hpos : 1 ≤ x.prodM / h ^ 2 := by
      have hxpos : 1 ≤ x.prodM := (Finset.mem_Icc.1 hprod_mem).1
      have hh2pos : 0 < h ^ 2 := Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_one hh)
      exact Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hxpos) hpow) hh2pos
    have hle : x.prodM / h ^ 2 ≤ N ^ s / h ^ 2 :=
      Nat.div_le_div_right (Finset.mem_Icc.1 hprod_mem).2
    exact Finset.mem_Icc.2 ⟨hpos, hle⟩
  have hsplit :
      F.card =
        ∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
          (F.filter fun x => x.prodM / h ^ 2 = m).card :=
    Finset.card_eq_sum_card_fiberwise hmem
  have hpoint :
      ∀ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
        (F.filter fun x => x.prodM / h ^ 2 = m).card ≤
          Fintype.card (OrderedFactors s m) *
            Fintype.card (OrderedFactors s (h ^ 2 * m)) := by
    intro m hm
    -- Restrict to points with `prodM = h² m` (equivalent on the fibre).
    have hsub :
        (F.filter fun x => x.prodM / h ^ 2 = m) ⊆
          (F.filter fun x => x.prodM = h ^ 2 * m) := by
      intro x hx
      have hxF := (Finset.mem_filter.1 hx).1
      have hdiv := (Finset.mem_filter.1 hx).2
      have hpow := I2Fibre_hpow_dvd_prodM (h := h) x hxF hℓ
      refine Finset.mem_filter.2 ⟨hxF, ?_⟩
      -- `prodM/h² = m` and `h²∣prodM` ⇒ `prodM = h² m`
      have := Nat.div_mul_cancel hpow
      rw [hdiv] at this
      rw [← this, Nat.mul_comm]
    refine (Finset.card_le_card hsub).trans ?_
    -- Reuse fixed-product bound at `n = h² m`.
    have hle :=
      I2_fibre_fixed_prod_card_le (s := s) (N := N) h (h ^ 2 * m) ℓ h0 hh hℓ
    -- ` (h²m)/h² = m `
    have hdiv : (h ^ 2 * m) / h ^ 2 = m := by
      rw [Nat.mul_comm, Nat.mul_div_cancel]
      exact Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_one hh)
    simpa [hdiv] using hle
  have hcard_le :
      F.card ≤
        ∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
          Fintype.card (OrderedFactors s m) *
            Fintype.card (OrderedFactors s (h ^ 2 * m)) := by
    rw [hsplit]
    exact Finset.sum_le_sum hpoint
  calc
    (F.card : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
            ((Fintype.card (OrderedFactors s m) *
                Fintype.card (OrderedFactors s (h ^ 2 * m)) : ℕ) : ℝ) := by
          exact_mod_cast hcard_le
    _ = ∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
          (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [tau_eq_card_ordered_cast, tau_eq_card_ordered_cast, Nat.cast_mul]

/--
Analytic step (`tau_mul_le` / `tau_sq_le` + Trusted `divisor_sum_sq_bound`):
`∑_{m≤N^s/h²} τ(m) τ(h² m) ≤ (τ(h)²/h²) N^s (2 s log N)^{s²-1}`.

Log base: `X = N^s/h² ≤ N^s` ⇒ `log X ≤ s log N` (same packaging as
`tau_ss_conv_sum_bound_weak`).
-/
theorem tau_I2_convolution_bound (s N h : ℕ) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hh : 1 ≤ h) :
    (∑ m ∈ Finset.Icc 1 (N ^ s / h ^ 2),
        (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)) ≤
      ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
  set X := N ^ s / h ^ 2
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hτh2 : (0 : ℝ) ≤ (tau s h : ℝ) ^ 2 := sq_nonneg _
  have hterm : ∀ m ∈ Finset.Icc 1 X,
      (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ) ≤
        (tau s h : ℝ) ^ 2 * (tau s m : ℝ) ^ 2 := by
    intro m _
    have hτm : (0 : ℝ) ≤ tau s m := by exact_mod_cast Nat.zero_le _
    have hmul : (tau s (h ^ 2 * m) : ℝ) ≤
        (tau s (h ^ 2) : ℝ) * (tau s m : ℝ) := by
      exact_mod_cast tau_mul_le s (h ^ 2) m hs1
    have hsq : (tau s (h ^ 2) : ℝ) ≤ (tau s h : ℝ) ^ 2 := by
      have := tau_sq_le s h hs1
      simpa [pow_two] using (by exact_mod_cast this : (tau s (h ^ 2) : ℝ) ≤
        (tau s h : ℝ) * (tau s h : ℝ))
    calc
      (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)
          ≤ (tau s m : ℝ) * ((tau s (h ^ 2) : ℝ) * (tau s m : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul hτm
      _ = (tau s (h ^ 2) : ℝ) * (tau s m : ℝ) ^ 2 := by ring
      _ ≤ (tau s h : ℝ) ^ 2 * (tau s m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hsum_sq :
      (∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)) ≤
        (tau s h : ℝ) ^ 2 *
          ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2 := by
    calc
      ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)
          ≤ ∑ m ∈ Finset.Icc 1 X, (tau s h : ℝ) ^ 2 * (tau s m : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
      _ = (tau s h : ℝ) ^ 2 * ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2 :=
        (Finset.mul_sum (Finset.Icc 1 X) (fun m => (tau s m : ℝ) ^ 2)
          ((tau s h : ℝ) ^ 2)).symm
  have hXle_N : (X : ℝ) ≤ (N : ℝ) ^ s / (h : ℝ) ^ 2 := by
    have hmul : (X : ℝ) * (h : ℝ) ^ 2 ≤ (N : ℝ) ^ s := by
      calc
        (X : ℝ) * (h : ℝ) ^ 2
            = ((X * h ^ 2 : ℕ) : ℝ) := by
              rw [← Nat.cast_pow, ← Nat.cast_mul]
        _ ≤ ((N ^ s : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self (N ^ s) (h ^ 2)
        _ = (N : ℝ) ^ s := by rw [Nat.cast_pow]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (h : ℝ) ^ 2)).2 hmul
  have hpack (hXbound :
      ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2 ≤
        (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) :
      (∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)) ≤
        ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
          (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
    have hpow0 : (0 : ℝ) ≤ (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
      positivity
    have hX0 : (0 : ℝ) ≤ X := by exact_mod_cast Nat.zero_le _
    calc
      ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) * (tau s (h ^ 2 * m) : ℝ)
          ≤ (tau s h : ℝ) ^ 2 *
              ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2 := hsum_sq
      _ ≤ (tau s h : ℝ) ^ 2 *
            ((X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hXbound hτh2
      _ = (tau s h : ℝ) ^ 2 * (X : ℝ) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by ring
      _ ≤ (tau s h : ℝ) ^ 2 * ((N : ℝ) ^ s / (h : ℝ) ^ 2) *
            (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hXle_N hτh2) hpow0
      _ = ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
            (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
        field_simp
  by_cases hX3 : 3 ≤ X
  · have hsq := divisor_sum_sq_bound X s hX3 hs1
    have hXpos : (0 : ℝ) < X := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hX3
    have hXleR : (X : ℝ) ≤ (N : ℝ) ^ s := by
      exact_mod_cast (Nat.div_le_self (N ^ s) (h ^ 2) : X ≤ N ^ s)
    have hlog : Real.log X ≤ (s : ℝ) * Real.log N := by
      have := Real.log_le_log hXpos hXleR
      rwa [Real.log_pow (N : ℝ) s] at this
    have h2 : 2 * Real.log X ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
    have hpow :
        (2 * Real.log X) ^ (s ^ 2 - 1) ≤
          (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have hX0' : (0 : ℝ) ≤ X := le_of_lt hXpos
    exact hpack (calc
      ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2
          ≤ (X : ℝ) * (2 * Real.log X) ^ (s ^ 2 - 1) := hsq
      _ ≤ (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left hpow hX0')
  · by_cases hXeq0 : X = 0
    · simp [hXeq0]; positivity
    · have hX1 : 1 ≤ X := Nat.pos_of_ne_zero hXeq0
      have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 3 := by
        intro m hm
        exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hm).1,
          le_trans (Finset.mem_Icc.1 hm).2 (by omega)⟩
      have hmono :
          (∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2) ≤
            ∑ m ∈ Finset.Icc 1 3, (tau s m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => sq_nonneg _
      have h3 := divisor_sum_sq_bound 3 s (by decide) hs1
      have hlogN : (1 : ℝ) ≤ Real.log N := by
        have hlog3 : (1 : ℝ) < Real.log 3 :=
          (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
            Real.exp_one_lt_three
        exact le_trans (le_of_lt hlog3)
          (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
      have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
      have hge2 : 2 ≤ s ^ 2 - 1 := by
        have hs2 : 4 ≤ s ^ 2 := by
          have := Nat.mul_le_mul hs hs
          simpa [pow_two] using this
        omega
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
              (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) /
                (2 : ℝ) ^ (s ^ 2 - 1) :=
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
      exact hpack (calc
        ∑ m ∈ Finset.Icc 1 X, (tau s m : ℝ) ^ 2
            ≤ ∑ m ∈ Finset.Icc 1 3, (tau s m : ℝ) ^ 2 := hmono
        _ ≤ (3 : ℝ) * (2 * Real.log 3) ^ (s ^ 2 - 1) := h3
        _ ≤ (X : ℝ) * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := h3le)

/--
Per-fibre bound: `#(I2Fibre h) ≤ (τ_s(h)²/h²) N^s (2 s log N)^{s²-1}`.
-/
theorem I2_fibre_card_le (s N h : ℕ) (ℓ : Fin s)
    (hs : 2 ≤ s) (hN : 3 ≤ N) (hh : 1 ≤ h)
    (hℓ : ℓ ≠ ⟨0, by omega⟩) :
    ((I2Fibre (s := s) (N := N) h ℓ (by omega)).card : ℝ) ≤
      ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
        (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) :=
  (I2_fibre_le_tau_sum s N h ℓ hs hN hh hℓ).trans
    (tau_I2_convolution_bound s N h hs hN hh)

/-- Uniform packaging used by `I2_card_bound` (constant `C = 1`). -/
theorem I2_fibre_bound_uniform (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N h : ℕ) (ℓ : Fin s),
        3 ≤ N → 1 ≤ h → ℓ ≠ ⟨0, by omega⟩ →
          ((I2Fibre (s := s) (N := N) h ℓ (by omega)).card : ℝ) ≤
            C * ((tau s h : ℝ) ^ 2 / (h : ℝ) ^ 2) *
              (N : ℝ) ^ s * (2 * (s : ℝ) * Real.log N) ^ (s ^ 2 - 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro N h ℓ hN hh hℓ
  simpa using I2_fibre_card_le s N h ℓ hs hN hh hℓ

end RMFLean
