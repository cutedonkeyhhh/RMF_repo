/-
Diophantine transfer for Piece III:
an alternative for `g_h` on scale `N/h` upgrades to an alternative for `g`
on scale `N`, via `K' = K * h^d` and `h * delta^2 < 1`.
-/
import RMFLean.Trusted.MainTheorem
import RMFLean.Proof.Setup.PhaseNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax

noncomputable section

namespace RMFLean

/-- `h * delta^2 < 1` implies `h < delta^{-2}`. -/
theorem h_lt_delta_inv_sq (h : ℕ) (δ : ℝ) (_hhpos : (0 : ℝ) < h)
    (hδ : 0 < δ) (_hδ1 : δ < 1) (hhδ : (h : ℝ) * δ ^ 2 < 1) :
    (h : ℝ) < δ ^ (-(2 : ℝ)) := by
  have hδsq_pos : (0 : ℝ) < δ ^ 2 := sq_pos_of_pos hδ
  have hlt : (h : ℝ) < (δ ^ 2)⁻¹ := by
    have : (h : ℝ) < 1 / δ ^ 2 :=
      (lt_div_iff₀ hδsq_pos).2 (by simpa [mul_comm] using hhδ)
    simpa [one_div] using this
  have hrw : δ ^ (-(2 : ℝ)) = (δ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδ)]
    congr 1
    exact Real.rpow_natCast δ 2
  simpa [hrw] using hlt

/-- `0 < delta ≤ 1/8` implies `2 ≤ delta^{-1}`. -/
theorem two_le_delta_inv (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 8) :
    (2 : ℝ) ≤ δ ^ (-(1 : ℝ)) := by
  have : (2 : ℝ) ≤ δ⁻¹ :=
    (inv_anti₀ hδ hδ').trans' (by norm_num : (2 : ℝ) ≤ (1 / 8 : ℝ)⁻¹)
  have hrw : δ ^ (-(1 : ℝ)) = δ⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδ), Real.rpow_one]
  simpa [hrw] using this

/-- Real-vs-nat division: `N/h ≤ 2*(N/h)` when `1 ≤ N/h`. -/
theorem div_real_le_two_div_nat (N h : ℕ) (hh : 1 ≤ h) (hle : h ≤ N) :
    (N : ℝ) / (h : ℝ) ≤ (2 : ℝ) * ↑(N / h) := by
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hNh1 : 1 ≤ N / h := Nat.div_pos hle (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hle' : (N : ℝ) / (h : ℝ) ≤ ↑(N / h) + 1 := by
    have hmod : N % h < h := Nat.mod_lt _ (lt_of_lt_of_le Nat.zero_lt_one hh)
    have hdecomp : N = h * (N / h) + N % h := (Nat.div_add_mod N h).symm
    have hNle : N ≤ h * (N / h) + h := by
      have : N % h ≤ h := Nat.le_of_lt hmod
      calc
        N = h * (N / h) + N % h := hdecomp
        _ ≤ h * (N / h) + h := Nat.add_le_add_left this _
    have hcast : (N : ℝ) ≤ (h : ℝ) * ↑(N / h) + (h : ℝ) := by exact_mod_cast hNle
    exact (div_le_iff₀ hhpos).2 (by linarith [hcast])
  have : ↑(N / h) + (1 : ℝ) ≤ (2 : ℝ) * ↑(N / h) := by
    have : (1 : ℝ) ≤ ↑(N / h) := by exact_mod_cast hNh1
    linarith
  exact le_trans hle' this

/-- A nonzero term of `cInfinityNorm` is `≤` the norm. -/
theorem CirclePoly.cInfinityNorm_ge_term {d : ℕ} (g : CirclePoly d) (N : ℕ)
    (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0) :
    (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt (g.beta j) ≤ g.cInfinityNorm N := by
  simp only [CirclePoly.cInfinityNorm]
  set term : ℝ := (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt (g.beta j)
  set l : List ℝ := List.ofFn fun i : Fin (d + 1) =>
    if (i : ℕ) = 0 then (0 : ℝ)
    else (N : ℝ) ^ (i : ℕ) * CirclePoly.distToInt (g.beta i)
  have hmem : term ∈ l := by
    refine List.mem_ofFn.2 ⟨j, ?_⟩
    simp [term, hj]
  have hle_max : (↑term : WithBot ℝ) ≤ l.maximum := List.le_maximum_of_mem' hmem
  have hget : l.maximum.getD 0 = l.maximum.unbotD 0 := by
    cases l.maximum <;> rfl
  rw [hget]
  have hne : l.maximum ≠ ⊥ := by
    intro hbot
    have hempty : l = [] := by simpa [List.maximum_eq_bot] using hbot
    have hlen : List.length l = d + 1 := by simp [l, List.length_ofFn]
    rw [hempty, List.length_nil] at hlen
    exact Nat.succ_ne_zero d hlen.symm
  exact (WithBot.le_unbotD_iff hne).2 hle_max

/--
PDF after `eq:piece-III-fixed`: transfer Diophantine alternative along
`compMul`. Exponent `Cd + 3d + 2` accounts for `h^d < delta^{-2d}`, the
scale comparison `(N/h)_R ≤ 2(N/h)`, and slack.
-/
theorem altDiophantine_of_compMul (d N h : ℕ) (g : CirclePoly d) (δ Cd : ℝ)
    (_hN : 1 ≤ N) (hh : 1 ≤ h) (hle : h ≤ N)
    (hδ : 0 < δ) (hδ' : δ < 1 / 8)
    (hhδ : (h : ℝ) * δ ^ 2 < 1)
    (_hCd : 0 < Cd)
    (hdio : altDiophantine d (N / h) (CirclePoly.compMul g h) δ Cd) :
    altDiophantine d N g δ (Cd + (3 : ℝ) * (d : ℝ) + 2) := by
  classical
  rcases hdio with ⟨K, hKne, hKsize, hKnorm⟩
  set Nh : ℕ := N / h
  set K' : ℤ := K * ((h : ℤ) ^ d)
  set Cd' : ℝ := Cd + (3 : ℝ) * (d : ℝ) + 2
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hδ1 : δ ≤ 1 := le_of_lt (lt_trans hδ' (by norm_num : (1 / 8 : ℝ) < 1))
  have hδlt1 : δ < 1 := lt_of_lt_of_le hδ' (by norm_num)
  have hh_lt : (h : ℝ) < δ ^ (-(2 : ℝ)) :=
    h_lt_delta_inv_sq h δ hhpos hδ hδlt1 hhδ
  have hh_pow : (h : ℝ) ^ d ≤ δ ^ (-((2 : ℝ) * (d : ℝ))) := by
    by_cases hd0 : d = 0
    · simp [hd0, Real.rpow_zero]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hlt := pow_lt_pow_left₀ hh_lt (le_of_lt hhpos) (ne_of_gt hdpos)
      have hrw : (δ ^ (-(2 : ℝ))) ^ d = δ ^ (-((2 : ℝ) * (d : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hδ)]
        ring_nf
      exact le_of_lt (hrw ▸ hlt)
  have h2le : (2 : ℝ) ≤ δ ^ (-(1 : ℝ)) :=
    two_le_delta_inv δ hδ (le_of_lt hδ')
  have h2pow : (2 : ℝ) ^ d ≤ δ ^ (-(d : ℝ)) := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2le d
    have hrw : (δ ^ (-(1 : ℝ))) ^ d = δ ^ (-(d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hδ)]
      ring_nf
    simpa [hrw] using this
  have htarget_pos : (0 : ℝ) < δ ^ (-Cd') :=
    Real.rpow_pos_of_pos hδ _
  have hK'ne : K' ≠ 0 := by
    dsimp [K']
    exact mul_ne_zero hKne (pow_ne_zero _ (by exact_mod_cast ne_of_gt hhpos))
  have hK'size : (|K'| : ℝ) ≤ δ ^ (-Cd') := by
    have habs : (|K'| : ℝ) = (|K| : ℝ) * (h : ℝ) ^ d := by
      simp [K', abs_mul, abs_pow, Nat.abs_cast, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast]
    rw [habs]
    have h1 : (|K| : ℝ) * (h : ℝ) ^ d ≤ δ ^ (-Cd) * (h : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right hKsize (pow_nonneg (le_of_lt hhpos) _)
    have h2 : δ ^ (-Cd) * (h : ℝ) ^ d ≤
        δ ^ (-Cd) * δ ^ (-((2 : ℝ) * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hh_pow (Real.rpow_nonneg (le_of_lt hδ) _)
    have h3 : δ ^ (-Cd) * δ ^ (-((2 : ℝ) * (d : ℝ))) =
        δ ^ (-(Cd + (2 : ℝ) * (d : ℝ))) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have h4 : δ ^ (-(Cd + (2 : ℝ) * (d : ℝ))) ≤ δ ^ (-Cd') := by
      dsimp [Cd']
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    exact le_trans (le_trans h1 h2) (le_trans (le_of_eq h3) h4)
  have hscale : (N : ℝ) / (h : ℝ) ≤ (2 : ℝ) * (Nh : ℝ) := by
    simpa [Nh] using div_real_le_two_div_nat N h hh hle
  have hpoint :
      ∀ j : Fin (d + 1), (j : ℕ) ≠ 0 →
        (N : ℝ) ^ (j : ℕ) *
            CirclePoly.distToInt ((K' : ℝ) * g.beta j) ≤
          δ ^ (-Cd') := by
    intro j hj
    have hj' : (j : ℕ) ≤ d := Nat.lt_succ_iff.1 j.is_lt
    have hterm_gh :
        (Nh : ℝ) ^ (j : ℕ) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) ≤
          δ ^ (-Cd) := by
      have := CirclePoly.cInfinityNorm_ge_term (K • g.compMul h) Nh j hj
      -- hKnorm : cInfinityNorm ≤ Real.rpow δ (-Cd), defeq to δ^(-Cd)
      simpa [CirclePoly.beta_smul] using le_trans this hKnorm
    have hbeta : (g.compMul h).beta j = g.beta j * (h : ℝ) ^ (j : ℕ) :=
      CirclePoly.beta_compMul g h j
    have hK'beta :
        (K' : ℝ) * g.beta j =
          (((h : ℤ) ^ (d - (j : ℕ)) : ℤ) : ℝ) *
            ((K : ℝ) * (g.compMul h).beta j) := by
      dsimp [K']
      rw [hbeta, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_pow,
        Int.cast_natCast]
      have hpow : (h : ℝ) ^ d = (h : ℝ) ^ (j : ℕ) * (h : ℝ) ^ (d - (j : ℕ)) := by
        rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hj']
      rw [hpow]; ring
    have hdist :
        CirclePoly.distToInt ((K' : ℝ) * g.beta j) ≤
          (h : ℝ) ^ (d - (j : ℕ)) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := by
      have := CirclePoly.distToInt_mul_int ((h : ℤ) ^ (d - (j : ℕ)))
        ((K : ℝ) * (g.compMul h).beta j)
      have habs :
          |(((h : ℤ) ^ (d - (j : ℕ)) : ℤ) : ℝ)| = (h : ℝ) ^ (d - (j : ℕ)) := by
        rw [Int.cast_pow, Int.cast_natCast, abs_pow, Nat.abs_cast]
      simpa [hK'beta, habs] using this
    have hdist0 :
        0 ≤ CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) :=
      CirclePoly.distToInt_nonneg _
    have hcalc :
        (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt ((K' : ℝ) * g.beta j) ≤
          (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := by
      have hmul :
          (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt ((K' : ℝ) * g.beta j) ≤
            (N : ℝ) ^ (j : ℕ) *
              ((h : ℝ) ^ (d - (j : ℕ)) *
                CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j)) :=
        mul_le_mul_of_nonneg_left hdist
          (pow_nonneg (Nat.cast_nonneg N) (j : ℕ))
      refine le_trans hmul (le_of_eq ?_)
      have hrw :
          (N : ℝ) ^ (j : ℕ) * (h : ℝ) ^ (d - (j : ℕ)) =
            (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) := by
        have hne : (h : ℝ) ≠ 0 := ne_of_gt hhpos
        have hpow :
            (h : ℝ) ^ (d - (j : ℕ)) * (h : ℝ) ^ (j : ℕ) = (h : ℝ) ^ d := by
          rw [← pow_add, Nat.sub_add_cancel hj']
        calc
          (N : ℝ) ^ (j : ℕ) * (h : ℝ) ^ (d - (j : ℕ))
              = (N : ℝ) ^ (j : ℕ) / (h : ℝ) ^ (j : ℕ) *
                  ((h : ℝ) ^ (d - (j : ℕ)) * (h : ℝ) ^ (j : ℕ)) := by
                field_simp [hne]
          _ = ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) * (h : ℝ) ^ d := by
                rw [hpow, div_pow]
          _ = (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) := by ring
      calc
        (N : ℝ) ^ (j : ℕ) *
              ((h : ℝ) ^ (d - (j : ℕ)) *
                CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j)) =
            ((N : ℝ) ^ (j : ℕ) * (h : ℝ) ^ (d - (j : ℕ))) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := by
          ring
        _ = (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := by
          rw [hrw]
    have hscalej :
        ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) ≤ ((2 : ℝ) * (Nh : ℝ)) ^ (j : ℕ) :=
      pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (le_of_lt hhpos)) hscale _
    have h2j : (2 : ℝ) ^ (j : ℕ) ≤ (2 : ℝ) ^ d :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj'
    have hbound1 :
        (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) ≤
          (h : ℝ) ^ d * ((2 : ℝ) * (Nh : ℝ)) ^ (j : ℕ) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscalej (pow_nonneg (le_of_lt hhpos) _)) hdist0
    have hbound2 :
        (h : ℝ) ^ d * ((2 : ℝ) * (Nh : ℝ)) ^ (j : ℕ) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) ≤
          (h : ℝ) ^ d * ((2 : ℝ) ^ d * (Nh : ℝ) ^ (j : ℕ)) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := by
      have : ((2 : ℝ) * (Nh : ℝ)) ^ (j : ℕ) ≤
          (2 : ℝ) ^ d * (Nh : ℝ) ^ (j : ℕ) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h2j (pow_nonneg (Nat.cast_nonneg _) _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left this (pow_nonneg (le_of_lt hhpos) _)) hdist0
    have hbound3 :
        (h : ℝ) ^ d * ((2 : ℝ) ^ d * (Nh : ℝ) ^ (j : ℕ)) *
            CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) =
          ((h : ℝ) ^ d * (2 : ℝ) ^ d) *
            ((Nh : ℝ) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j)) := by
      ring
    have hprod :
        ((h : ℝ) ^ d * (2 : ℝ) ^ d) *
            ((Nh : ℝ) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j)) ≤
          (δ ^ (-((2 : ℝ) * (d : ℝ))) * δ ^ (-(d : ℝ))) * δ ^ (-Cd) := by
      have hfac :
          (h : ℝ) ^ d * (2 : ℝ) ^ d ≤
            δ ^ (-((2 : ℝ) * (d : ℝ))) * δ ^ (-(d : ℝ)) :=
        mul_le_mul hh_pow h2pow
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
          (Real.rpow_nonneg (le_of_lt hδ) _)
      have hterm0 :
          0 ≤
            (Nh : ℝ) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) :=
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hdist0
      exact mul_le_mul hfac hterm_gh hterm0
        (mul_nonneg (Real.rpow_nonneg (le_of_lt hδ) _)
          (Real.rpow_nonneg (le_of_lt hδ) _))
    have hrw :
        δ ^ (-((2 : ℝ) * (d : ℝ))) * δ ^ (-(d : ℝ)) * δ ^ (-Cd) =
          δ ^ (-(Cd + (3 : ℝ) * (d : ℝ))) := by
      rw [mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      ring_nf
    have hslack : δ ^ (-(Cd + (3 : ℝ) * (d : ℝ))) ≤ δ ^ (-Cd') := by
      dsimp [Cd']
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      (N : ℝ) ^ (j : ℕ) * CirclePoly.distToInt ((K' : ℝ) * g.beta j)
          ≤ (h : ℝ) ^ d * ((N : ℝ) / (h : ℝ)) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := hcalc
      _ ≤ (h : ℝ) ^ d * ((2 : ℝ) * (Nh : ℝ)) ^ (j : ℕ) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := hbound1
      _ ≤ (h : ℝ) ^ d * ((2 : ℝ) ^ d * (Nh : ℝ) ^ (j : ℕ)) *
              CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j) := hbound2
      _ = ((h : ℝ) ^ d * (2 : ℝ) ^ d) *
              ((Nh : ℝ) ^ (j : ℕ) *
                CirclePoly.distToInt ((K : ℝ) * (g.compMul h).beta j)) :=
            hbound3
      _ ≤ (δ ^ (-((2 : ℝ) * (d : ℝ))) * δ ^ (-(d : ℝ))) * δ ^ (-Cd) := hprod
      _ = δ ^ (-(Cd + (3 : ℝ) * (d : ℝ))) := hrw
      _ ≤ δ ^ (-Cd') := hslack
  have hnorm : (K' • g).cInfinityNorm N ≤ δ ^ (-Cd') := by
    refine CirclePoly.cInfinityNorm_le_of_forall (K' • g) N
      (le_of_lt htarget_pos) ?_
    intro j hj
    simpa [CirclePoly.beta_smul] using hpoint j hj
  -- `altDiophantine` is stated with `Real.rpow`; convert.
  refine ⟨K', hK'ne, ?_, ?_⟩
  · simpa using hK'size
  · simpa using hnorm

end RMFLean
