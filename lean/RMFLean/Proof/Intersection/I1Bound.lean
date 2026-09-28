/-
PDF Lemma 9 conclusion: assemble Piece III embedding through `I1_bound`.

Imports `I1PieceIIIScaledJ1` for `I1_piece_III_fixed_Te_assembled`
(scaled `J1` bridge + combinatorial `τ` packaging).
-/
import RMFLean.Proof.Intersection.I1PieceIIIScaledJ1
import RMFLean.Proof.Intersection.I1PieceIAssemble
import RMFLean.Proof.Setup.TailQAbsorb
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity

noncomputable section

open Classical BigOperators Complex Real

namespace RMFLean

/--
PDF Piece III embedding + scaled `J1`: either
`Σ_III ≤ C · ∑∑_{δT,δe<1} τ_{s-1}(T) · δ^{1/2} N^s/(Te) · polylog`,
or `altDiophantine` for `g`.
-/
theorem I1_piece_III_embed_J1 (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (hN : 3 ≤ N)
          (hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            I1PieceIIISum d s N A g δ I (by omega) ≤
                C *
                  (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
                    ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
                      if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
                        (tau (s - 1) T : ℝ) *
                          (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                            I1PieceIIIPolylog N s)
                      else 0) ∨
              altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  obtain ⟨Cd, hEq, hCd, hfixed⟩ := I1_piece_III_fixed_Te_assembled d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C, hC, hfixed_s⟩ := hfixed s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi
  set h0 : 0 < s := by omega
  rcases hfixed_s N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi with hdio | hpt
  · exact Or.inr hdio
  · refine Or.inl ?_
    have hregroup := I1PieceIIISum_eq_sum_fixed d s N A g δ I h0 hN
    have hmaj :
        ∀ T ∈ Finset.Icc 1 (N ^ (s - 1)),
          ∀ e ∈ Finset.Icc 1 (N ^ (s - 1)),
            I1PieceIIIFixedSum d s N A g δ I h0 T e ≤
              C *
                (if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
                  (tau (s - 1) T : ℝ) *
                    (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                      I1PieceIIIPolylog N s)
                else 0) := by
      intro T hT e he
      by_cases hTe : δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1
      · have hbound := hpt T hT e he hTe.1 hTe.2
        simp only [hTe, ↓reduceIte]
        calc
          I1PieceIIIFixedSum d s N A g δ I h0 T e
              ≤ C * (tau (s - 1) T : ℝ) *
                  (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                    I1PieceIIIPolylog N s) := hbound
          _ = C *
                ((tau (s - 1) T : ℝ) *
                  (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                    I1PieceIIIPolylog N s)) := by ring
      · have hzero : I1PieceIIIFixedSum d s N A g δ I h0 T e = 0 := by
          simp only [I1PieceIIIFixedSum]
          refine Finset.sum_eq_zero fun ν hν => ?_
          have hνT : ν.T h0 = T ∧ δ * (ν.T h0 : ℝ) < 1 :=
            (Finset.mem_filter.1 hν).2
          by_cases he' : e ∈ (ν.Q h0).divisors ∧ δ * (e : ℝ) < 1
          · exact False.elim (hTe ⟨by simpa [hνT.1] using hνT.2, he'.2⟩)
          · simp only [he', ↓reduceIte]
        simp only [hTe, ↓reduceIte, hzero, mul_zero, le_rfl]
    calc
      I1PieceIIISum d s N A g δ I h0
          = ∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
                I1PieceIIIFixedSum d s N A g δ I h0 T e := hregroup
      _ ≤ ∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
            ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
              C *
                (if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
                  (tau (s - 1) T : ℝ) *
                    (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                      I1PieceIIIPolylog N s)
                else 0) := by
            refine Finset.sum_le_sum fun T hT =>
              Finset.sum_le_sum fun e he => hmaj T hT e he
      _ = C *
            (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
              ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
                if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
                  (tau (s - 1) T : ℝ) *
                    (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                      I1PieceIIIPolylog N s)
                else 0) := by
            simp_rw [← Finset.mul_sum]

/--
PDF Piece III reduction: either
`Σ_III ≤ C · δ^{1/2} N^s · I1PieceIIIPolylog · I1PieceIIITdWeight`,
or the Diophantine alternative for `g`.
-/
theorem I1_piece_III_reduce (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (hN : 3 ≤ N)
          (hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (hA : 1 ≤ A),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            I1PieceIIISum d s N A g δ I (by omega) ≤
                C * Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s *
                  I1PieceIIITdWeight N s δ ∨
              altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  obtain ⟨Cd, hEq, hCd, hembed⟩ := I1_piece_III_embed_J1 d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C, hC, hembed_s⟩ := hembed s hs
  refine ⟨C, hC, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi
  rcases hembed_s N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi with hbound | hdio
  · refine Or.inl ?_
    have hfactor := I1_piece_III_factor_double_sum N s δ
    calc
      I1PieceIIISum d s N A g δ I (by omega)
          ≤ C *
              (∑ T ∈ Finset.Icc 1 (N ^ (s - 1)),
                ∑ e ∈ Finset.Icc 1 (N ^ (s - 1)),
                  if δ * (T : ℝ) < 1 ∧ δ * (e : ℝ) < 1 then
                    (tau (s - 1) T : ℝ) *
                      (Real.sqrt δ * (N : ℝ) ^ s / ((e : ℝ) * (T : ℝ)) *
                        I1PieceIIIPolylog N s)
                  else 0) := hbound
      _ = C *
            (Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s *
              I1PieceIIITdWeight N s δ) := by rw [hfactor]
      _ = C * Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s *
            I1PieceIIITdWeight N s δ := by ring
  · exact Or.inr hdio

/--
PDF after `eq:piece-III-fixed`: the double truncated harmonic weight satisfies
`(∑_{δT<1} τ_{s-1}(T)/T)(∑_{δd<1} 1/d) ≪_s (2 log N)^s`
(Lemma 1 + partial summation).  The implied constant may depend on `s`
(matching the paper's `≪`; a bare factor `1` fails for large `s`).
-/
theorem I1_piece_III_Td_sum_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 3 ≤ N → 0 < δ → δ < 1 / 8 →
        I1PieceIIITdWeight N s δ ≤ C * (2 * Real.log N) ^ s := by
  let k := s - 1
  have hk : 1 ≤ k := by omega
  -- `(1+(s-1)log N)^s ≤ ((s-1)+1/log 3)^s (log N)^s`
  -- and `(log N)^s ≤ (2 log N)^s / 2^s`.
  set C0 : ℝ := ((k : ℝ) + 1 / Real.log 3) ^ s / (2 : ℝ) ^ s
  refine ⟨C0, ?_, fun N δ hN hδ _hδ' => ?_⟩
  · have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    exact div_pos (pow_pos (by positivity) s) (pow_pos (by norm_num) s)
  · set M := N ^ (s - 1)
    have hM3 : 3 ≤ M := by
      have : 3 ≤ N := hN
      exact le_trans this (Nat.le_self_pow (by omega : s - 1 ≠ 0) N)
    have hlogN : 0 < Real.log N :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hN))
    have hlog3le : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (Nat.cast_le.mpr hN)
    have hlogM : Real.log M = (k : ℝ) * Real.log N := by
      dsimp [M, k]
      rw [Nat.cast_pow, Real.log_pow (N : ℝ) (s - 1),
        Nat.cast_sub (le_trans (by decide : 1 ≤ 2) hs)]
    -- Truncation ≤ full sum on `Icc 1 M`.
    have hτtrunc :
        (∑ T ∈ Finset.Icc 1 M,
            if δ * (T : ℝ) < 1 then (tau k T : ℝ) / (T : ℝ) else 0) ≤
          ∑ T ∈ Finset.Icc 1 M, (tau k T : ℝ) / (T : ℝ) := by
      refine Finset.sum_le_sum fun T _ => ?_
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h1trunc :
        (∑ e ∈ Finset.Icc 1 M,
            if δ * (e : ℝ) < 1 then (1 : ℝ) / (e : ℝ) else 0) ≤
          ∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / (e : ℝ) := by
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    have hτ :
        (∑ T ∈ Finset.Icc 1 M, (tau k T : ℝ) / (T : ℝ)) ≤
          (1 + Real.log M) ^ k := by
      calc
        (∑ T ∈ Finset.Icc 1 M, (tau k T : ℝ) / (T : ℝ))
            = ∑ f ∈ posProdLEFinset k M, invProd k f :=
          tau_harmonic_sum_eq_posProdLE k M
        _ ≤ ∑ f ∈ posProdFinset k M, invProd k f :=
          posProdLE_sum_le_posProd k M
        _ = (∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹) ^ k :=
          posProdFinset_sum_eq_harmonic_pow k M
        _ ≤ (1 + Real.log M) ^ k :=
          pow_le_pow_left₀ (by positivity) (harmonic_Icc_le_one_add_log M) k
    have h1 :
        (∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / (e : ℝ)) ≤ 1 + Real.log M := by
      simpa [div_eq_mul_inv, one_mul] using harmonic_Icc_le_one_add_log M
    have hprod :
        I1PieceIIITdWeight N s δ ≤ (1 + Real.log M) ^ s := by
      have h0τ :
          0 ≤ ∑ T ∈ Finset.Icc 1 M,
            if δ * (T : ℝ) < 1 then (tau k T : ℝ) / (T : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by
          split_ifs
          · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          · exact le_rfl
      have h01 :
          0 ≤ ∑ e ∈ Finset.Icc 1 M,
            if δ * (e : ℝ) < 1 then (1 : ℝ) / (e : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by
          split_ifs
          · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
          · exact le_rfl
      have hτ' := le_trans hτtrunc hτ
      have h1' := le_trans h1trunc h1
      dsimp [I1PieceIIITdWeight]
      -- `k = s-1`, `M = N^(s-1)`
      change
          (∑ T ∈ Finset.Icc 1 M,
              if δ * (T : ℝ) < 1 then (tau k T : ℝ) / (T : ℝ) else 0) *
            (∑ e ∈ Finset.Icc 1 M,
              if δ * (e : ℝ) < 1 then (1 : ℝ) / (e : ℝ) else 0) ≤
            (1 + Real.log M) ^ s
      calc
        _ ≤ (1 + Real.log M) ^ k * (1 + Real.log M) :=
          mul_le_mul hτ' h1' h01 (pow_nonneg (by positivity) k)
        _ = (1 + Real.log M) ^ (k + 1) := by rw [pow_succ]
        _ = (1 + Real.log M) ^ s := by
          have : k + 1 = s := by omega
          rw [this]
    have hrewrite :
        (1 + Real.log M) ^ s =
          ((k : ℝ) + 1 / Real.log N) ^ s * (Real.log N) ^ s := by
      have hmul : 1 + Real.log M = (Real.log N) * ((k : ℝ) + 1 / Real.log N) := by
        rw [hlogM]
        field_simp
        ring
      rw [hmul, mul_pow, mul_comm]
    have hcoef :
        (k : ℝ) + 1 / Real.log N ≤ (k : ℝ) + 1 / Real.log 3 := by
      have := one_div_le_one_div_of_le
        (Real.log_pos (by norm_num : (1 : ℝ) < 3)) hlog3le
      linarith
    have hpowcoef :
        ((k : ℝ) + 1 / Real.log N) ^ s ≤ ((k : ℝ) + 1 / Real.log 3) ^ s :=
      pow_le_pow_left₀ (by positivity) hcoef s
    have htwo :
        (Real.log N) ^ s = (2 * Real.log N) ^ s / (2 : ℝ) ^ s := by
      have hne : (2 : ℝ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
      rw [mul_pow, mul_comm (2 ^ s), eq_div_iff hne]
    calc
      I1PieceIIITdWeight N s δ ≤ (1 + Real.log M) ^ s := hprod
      _ = ((k : ℝ) + 1 / Real.log N) ^ s * (Real.log N) ^ s := hrewrite
      _ ≤ ((k : ℝ) + 1 / Real.log 3) ^ s * (Real.log N) ^ s :=
        mul_le_mul_of_nonneg_right hpowcoef (pow_nonneg (le_of_lt hlogN) s)
      _ = ((k : ℝ) + 1 / Real.log 3) ^ s *
            ((2 * Real.log N) ^ s / (2 : ℝ) ^ s) := by rw [htwo]
      _ = C0 * (2 * Real.log N) ^ s := by
        dsimp [C0]
        ring

/--
Absorb `I1PieceIIIPolylog · (2 log N)^s` into `𝒬 = (2s log N)^{3s²}`.
The two summands have exponents `s²` and `2(s-1)²+s`, both `≤ 3s²`.
-/
theorem I1_piece_III_polylog_twolog_le_tailQ (s : ℕ) (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 3 ≤ N →
        I1PieceIIIPolylog N s * (2 * Real.log N) ^ s ≤
          K * (2 : ℝ) ^ (s + 1) * tailQ N s := by
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
  have hpow : s * (s - 1) + s = s * s := by
    calc
      s * (s - 1) + s = s * (s - 1) + s * 1 := by rw [Nat.mul_one]
      _ = s * ((s - 1) + 1) := (Nat.mul_add s (s - 1) 1).symm
      _ = s * s := by rw [Nat.sub_add_cancel hs1]
  have ha : s * s ≤ tailQExp s := by
    simp only [tailQExp, pow_two]
    exact Nat.le_mul_of_pos_left _ (by decide)
  have hb : 2 * ((s - 1) * (s - 1)) + s ≤ tailQExp s := by
    simpa [pow_two] using two_pred_sq_add_s_le_tailQExp s
  obtain ⟨K1, hK1, h1⟩ := log_pow_le_mul_tailQ s hs (s * s) ha
  refine ⟨K1 / 2 + 1 / 2, by positivity, fun N hN => ?_⟩
  have h2pow : (2 * Real.log N) ^ s = (2 : ℝ) ^ s * (Real.log N) ^ s := by
    rw [mul_pow]
  have hlog := log_N_gt_one hN
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hbase : (1 : ℝ) ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
  have htermA :
      (Real.log N) ^ (s * (s - 1)) * (2 * Real.log N) ^ s ≤
        (K1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by
    calc
      (Real.log N) ^ (s * (s - 1)) * (2 * Real.log N) ^ s
          = (Real.log N) ^ (s * (s - 1)) * ((2 : ℝ) ^ s * (Real.log N) ^ s) := by
            rw [h2pow]
      _ = (2 : ℝ) ^ s *
            ((Real.log N) ^ (s * (s - 1)) * (Real.log N) ^ s) := by ring
      _ = (2 : ℝ) ^ s * (Real.log N) ^ (s * (s - 1) + s) := by rw [← pow_add]
      _ = (2 : ℝ) ^ s * (Real.log N) ^ (s * s) := by rw [hpow]
      _ ≤ (2 : ℝ) ^ s * (K1 * tailQ N s) :=
        mul_le_mul_of_nonneg_left (h1 N hN) (pow_nonneg (by norm_num) _)
      _ = (K1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by ring
  have htermB :
      (Real.log N) ^ ((s - 1) * (s - 1)) *
          (2 * Real.log N) ^ ((s - 1) * (s - 1)) * (2 * Real.log N) ^ s ≤
        (1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by
    have hlogle : Real.log N ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
    have h2le : 2 * Real.log N ≤ 2 * (s : ℝ) * Real.log N := by nlinarith
    have hlog0 : 0 ≤ Real.log N := le_of_lt (lt_trans (by norm_num) hlog)
    calc
      (Real.log N) ^ ((s - 1) * (s - 1)) *
          (2 * Real.log N) ^ ((s - 1) * (s - 1)) * (2 * Real.log N) ^ s
          = (Real.log N) ^ ((s - 1) * (s - 1)) *
              (2 * Real.log N) ^ ((s - 1) * (s - 1) + s) := by
            rw [mul_assoc, ← pow_add]
      _ ≤ (2 * (s : ℝ) * Real.log N) ^ ((s - 1) * (s - 1)) *
            (2 * (s : ℝ) * Real.log N) ^ ((s - 1) * (s - 1) + s) :=
          mul_le_mul
            (pow_le_pow_left₀ hlog0 hlogle _)
            (pow_le_pow_left₀ (mul_nonneg (by norm_num) hlog0) h2le _)
            (pow_nonneg (mul_nonneg (by norm_num) hlog0) _)
            (pow_nonneg (le_trans (by norm_num) hbase) _)
      _ = (2 * (s : ℝ) * Real.log N) ^
            (2 * ((s - 1) * (s - 1)) + s) := by
          rw [← pow_add]; ring
      _ ≤ tailQ N s :=
        two_s_log_pow_le_tailQ s N (2 * ((s - 1) * (s - 1)) + s) hs hN hb
      _ ≤ (1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by
            have hQ : 0 ≤ tailQ N s := (tailQ_pos_of_three_le N s hN).le
            have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
            have hfac : (2 : ℝ) ^ s = (1 / 2) * (2 : ℝ) ^ (s + 1) := by
              rw [pow_succ]; ring
            calc
              tailQ N s ≤ (2 : ℝ) ^ s * tailQ N s :=
                le_mul_of_one_le_left hQ h2s
              _ = (1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by rw [hfac]
  dsimp [I1PieceIIIPolylog]
  calc
    ((Real.log N) ^ (s * (s - 1)) +
          (Real.log N) ^ ((s - 1) * (s - 1)) *
            (2 * Real.log N) ^ ((s - 1) * (s - 1))) *
        (2 * Real.log N) ^ s
        = (Real.log N) ^ (s * (s - 1)) * (2 * Real.log N) ^ s +
            (Real.log N) ^ ((s - 1) * (s - 1)) *
              (2 * Real.log N) ^ ((s - 1) * (s - 1)) *
                (2 * Real.log N) ^ s := by ring
    _ ≤ (K1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s +
          (1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s :=
      add_le_add htermA htermB
    _ = (K1 / 2 + 1 / 2) * (2 : ℝ) ^ (s + 1) * tailQ N s := by ring

/--
PDF finish for Piece III: `polylog · TdWeight ≤ C · 2^{s+1} · 𝒬`,
with `C` folding the Td harmonic constant and the polylog absorption constant.
-/
theorem I1_piece_III_polylog_Td_le_tailQ (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 3 ≤ N → 0 < δ → δ < 1 / 8 →
        I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ ≤
          C * (2 : ℝ) ^ (s + 1) * tailQ N s := by
  obtain ⟨CTd, hCTd, hTdall⟩ := I1_piece_III_Td_sum_bound s hs
  obtain ⟨K, hK, habsAll⟩ := I1_piece_III_polylog_twolog_le_tailQ s hs
  refine ⟨CTd * K, by positivity, fun N δ hN hδ hδ' => ?_⟩
  have hTd := hTdall N δ hN hδ hδ'
  have habsorb := habsAll N hN
  have hpoly0 : 0 ≤ I1PieceIIIPolylog N s := by
    dsimp [I1PieceIIIPolylog]
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
    have hlogN : (1 : ℝ) < Real.log N :=
      lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
    positivity
  have h2log0 : 0 ≤ (2 * Real.log N) ^ s := by
    have hlogN : 0 ≤ Real.log N :=
      le_of_lt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hN)))
    exact pow_nonneg (mul_nonneg (by norm_num) hlogN) s
  calc
    I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ
        ≤ I1PieceIIIPolylog N s * (CTd * (2 * Real.log N) ^ s) :=
      mul_le_mul_of_nonneg_left hTd hpoly0
    _ = CTd * (I1PieceIIIPolylog N s * (2 * Real.log N) ^ s) := by ring
    _ ≤ CTd * (K * (2 : ℝ) ^ (s + 1) * tailQ N s) :=
      mul_le_mul_of_nonneg_left habsorb hCTd.le
    _ = (CTd * K) * (2 : ℝ) ^ (s + 1) * tailQ N s := by ring

/-- Piece III (PDF): small `T,d` reduce to a scaled `J1` / Lemma 5 argument. -/
theorem I1_piece_III (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (hN : 3 ≤ N)
          (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
          (hδ : 0 < δ) (hδ' : δ < 1 / 8) (_hA : 1 ≤ A),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            I1PieceIIISum d s N A g δ I (by omega) ≤ C * errorSize N s δ ∨
              altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  obtain ⟨Cd, hEq, hCd, hred⟩ := I1_piece_III_reduce d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C0, hC0, hred_s⟩ := hred s hs
  obtain ⟨CTd, hCTd, hTdFin⟩ := I1_piece_III_polylog_Td_le_tailQ s hs
  refine ⟨C0 * CTd * (2 : ℝ) ^ (s + 1), by positivity, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi
  rcases hred_s N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi with hbound | hdio
  · refine Or.inl ?_
    have hfin := hTdFin N δ hN hδ hδ'
    have hδNs_nonneg : 0 ≤ Real.sqrt δ * (N : ℝ) ^ s :=
      mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    have hmul :
        Real.sqrt δ * (N : ℝ) ^ s *
            (I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ) ≤
          Real.sqrt δ * (N : ℝ) ^ s * (CTd * (2 : ℝ) ^ (s + 1) * tailQ N s) :=
      mul_le_mul_of_nonneg_left hfin hδNs_nonneg
    calc
      I1PieceIIISum d s N A g δ I (by omega)
          ≤ C0 * Real.sqrt δ * (N : ℝ) ^ s * I1PieceIIIPolylog N s *
              I1PieceIIITdWeight N s δ := hbound
      _ = C0 * (Real.sqrt δ * (N : ℝ) ^ s *
            (I1PieceIIIPolylog N s * I1PieceIIITdWeight N s δ)) := by ring
      _ ≤ C0 * (Real.sqrt δ * (N : ℝ) ^ s * (CTd * (2 : ℝ) ^ (s + 1) * tailQ N s)) :=
          mul_le_mul_of_nonneg_left hmul hC0.le
      _ = (C0 * CTd * (2 : ℝ) ^ (s + 1)) *
            (Real.sqrt δ * (N : ℝ) ^ s * tailQ N s) := by ring
      _ = (C0 * CTd * (2 : ℝ) ^ (s + 1)) * errorSize N s δ := by
          simp [errorSize]
  · exact Or.inr hdio
/--
PDF Lemma 9: `|I₁| ≪ δ N^s 𝒬` or Diophantine alternative.
`Cd` is the Lem5 / A-window exponent; the alternative is at `Cd + 3d + 2`.
Constants may depend on `s` (via Piece III harmonic estimates).
-/
theorem I1_bound (d : ℕ) :
    ∃ Cd : ℝ, Cd = Lem5Cd d ∧ 0 < Cd ∧
      ∀ (s : ℕ) (hs : 2 ≤ s), ∃ C : ℝ, 0 < C ∧
        ∀ (N A : ℕ) (g : CirclePoly d) (δ : ℝ)
          (I : Finset (Fin s)) (_hN : 3 ≤ N)
          (_hI0 : (⟨0, by omega⟩ : Fin s) ∈ I) (_hIcard : 2 ≤ I.card)
          (_hδ : 0 < δ) (_hδ' : δ < 1 / 8) (_hA : 1 ≤ A),
          Real.rpow δ (-(Cd + 2)) < (A : ℝ) →
            (A : ℝ) < Real.rpow δ (-(3 + Cd)) →
            ‖Sg g (I1Support (s := s) (N := N) A I (by omega))‖ ≤
                C * errorSize N s δ ∨
              altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  obtain ⟨Cd, hEq, hCd, hIII⟩ := I1_piece_III d
  refine ⟨Cd, hEq, hCd, ?_⟩
  intro s hs
  obtain ⟨C_I, hC_I, hI⟩ := I1_piece_I d s hs
  obtain ⟨C_II, hC_II, hII⟩ := I1_piece_II d s hs
  obtain ⟨C_III, hC_III, hIIIs⟩ := hIII s hs
  refine ⟨C_I + C_II + C_III,
    add_pos (add_pos hC_I hC_II) hC_III, ?_⟩
  intro N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi
  set h0 : 0 < s := by omega
  have habs :=
    I1_norm_le_absDoubleSum (d := d) (s := s) (N := N) (A := A) g I h0 hI0 hIcard hA
  have hsplit := I1AbsDoubleSum_le_three_pieces d s N A g δ I h0 hδ
  have hIbound := hI N A g δ I hN hI0 hIcard hδ hδ' hA
  have hIIbound := hII N A g δ I hN hI0 hIcard hδ hδ' hA
  rcases hIIIs N A g δ I hN hI0 hIcard hδ hδ' hA hAlo hAhi with hIIIbound | hdio
  · refine Or.inl ?_
    calc
      ‖Sg g (I1Support (s := s) (N := N) A I h0)‖
          ≤ I1AbsDoubleSum d s N A g I h0 := habs
      _ ≤ I1PieceISum d s N A g δ I h0 +
            I1PieceIISum d s N A g δ I h0 +
            I1PieceIIISum d s N A g δ I h0 := hsplit
      _ ≤ C_I * errorSize N s δ + C_II * errorSize N s δ +
            C_III * errorSize N s δ :=
        add_le_add (add_le_add hIbound hIIbound) hIIIbound
      _ = (C_I + C_II + C_III) * errorSize N s δ := by ring
  · exact Or.inr hdio

end RMFLean
