/-
Definitional content of the opaque `tau` used in PDF Lemma 1 / Lemma 3 / Lemma 10.
-/
import RMFLean.Trusted.Axioms
import RMFLean.Trusted.DivisorSums
import RMFLean.Proof.Setup.SolutionSet
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

open Classical

namespace RMFLean

/--
Greedy extraction of an ordered factorization of `a` from a tuple whose product is a
multiple of `a`: at each coordinate take `gcd` with the remaining cofactor of `a`.
-/
def extractFactors : (k : Nat) → Nat → (Fin k → Nat) → (Fin k → Nat)
  | 0, _, _ => Fin.elim0
  | k + 1, a, f =>
    let d := Nat.gcd (f 0) a
    Fin.cons d (extractFactors k (a / d) fun i => f i.succ)

/--
If `∏ f = a * b` with positive coordinates, then `extractFactors k a f` is an ordered
factorization of `a`, and the cofactor tuple is an ordered factorization of `b`.
-/
theorem extractFactors_spec :
    ∀ (k a b : Nat) (f : Fin k → Nat),
      0 < b → (∀ i, 0 < f i) → (∏ i, f i) = a * b →
        let fa := extractFactors k a f
        (∀ i, fa i ∣ f i) ∧
          (∏ i, fa i) = a ∧
            (∏ i, (f i / fa i)) = b ∧
              (∀ i, 0 < fa i) ∧ ∀ i, 0 < f i / fa i := by
  intro k
  induction k with
  | zero =>
    intro a b f _hb _hf hprod
    have hab : a * b = 1 := by
      simpa [Finset.univ_eq_empty, Finset.prod_empty] using hprod.symm
    have ha : a = 1 := Nat.eq_one_of_dvd_one ⟨b, hab.symm⟩
    have hb1 : b = 1 := by
      have : (1 : Nat) * b = 1 := by simpa [ha] using hab
      simpa using this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · simpa [extractFactors] using ha.symm
    · simpa [extractFactors] using hb1.symm
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ k ih =>
    intro a b f hb hf hprod
    let d := Nat.gcd (f 0) a
    let a' := a / d
    let u := f 0 / d
    let f' : Fin k → Nat := fun i => f i.succ
    have hf0 : 0 < f 0 := hf 0
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left a hf0
    have hd_f : d ∣ f 0 := Nat.gcd_dvd_left _ _
    have hd_a : d ∣ a := Nat.gcd_dvd_right _ _
    have hf0_eq : f 0 = d * u := (Nat.mul_div_cancel' hd_f).symm
    have ha_eq : a = d * a' := (Nat.mul_div_cancel' hd_a).symm
    have hf' : ∀ i, 0 < f' i := fun i => hf i.succ
    have hprod' : f 0 * ∏ i, f' i = a * b := by
      rw [← hprod, Fin.prod_univ_succ]
    have hcancel : u * ∏ i, f' i = a' * b := by
      have h := hprod'
      rw [hf0_eq, ha_eq] at h
      have h' : d * (u * ∏ i, f' i) = d * (a' * b) := by
        calc
          d * (u * ∏ i, f' i) = (d * u) * ∏ i, f' i := (mul_assoc _ _ _).symm
          _ = (d * a') * b := h
          _ = d * (a' * b) := mul_assoc _ _ _
      exact Nat.eq_of_mul_eq_mul_left hdpos h'
    have hcoprime : Nat.Coprime u a' :=
      Nat.coprime_div_gcd_div_gcd hdpos
    have hu_b : u ∣ b := by
      have : u ∣ a' * b := ⟨∏ i, f' i, by rw [← hcancel, mul_comm]⟩
      exact hcoprime.dvd_of_dvd_mul_left this
    have hu_pos : 0 < u := Nat.div_pos (Nat.le_of_dvd hf0 hd_f) hdpos
    let b' := b / u
    have hb' : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb hu_b) hu_pos
    have hb_eq : b = u * b' := (Nat.mul_div_cancel' hu_b).symm
    have hprod_f' : (∏ i, f' i) = a' * b' := by
      have : u * ∏ i, f' i = u * (a' * b') := by
        rw [hcancel, hb_eq, mul_left_comm]
      exact Nat.eq_of_mul_eq_mul_left hu_pos this
    have hspec := ih a' b' f' hb' hf' hprod_f'
    let fa' := extractFactors k a' f'
    have hfa_def : extractFactors (k + 1) a f = Fin.cons d fa' := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.induction with
      | zero =>
        simpa [hfa_def, d] using hd_f
      | succ i _ =>
        simpa [hfa_def] using hspec.1 i
    · rw [hfa_def, Fin.prod_cons, hspec.2.1, ← ha_eq]
    · have hdiv_succ :
          (∏ i : Fin k, (f i.succ / fa' i)) = b' := by
        simpa [fa', f'] using hspec.2.2.1
      have h0 : f 0 / extractFactors (k + 1) a f 0 = u := by
        rw [hfa_def, Fin.cons_zero]
      have hs : ∀ i : Fin k,
          f i.succ / extractFactors (k + 1) a f i.succ = f i.succ / fa' i := by
        intro i
        rw [hfa_def, Fin.cons_succ]
      calc
        (∏ i, (f i / extractFactors (k + 1) a f i))
            = (f 0 / extractFactors (k + 1) a f 0) *
                ∏ i : Fin k, (f i.succ / extractFactors (k + 1) a f i.succ) :=
              Fin.prod_univ_succ _
        _ = u * ∏ i : Fin k, (f i.succ / fa' i) := by
            rw [h0]
            exact congrArg (u * ·) (Finset.prod_congr rfl fun i _ => hs i)
        _ = u * b' := by rw [hdiv_succ]
        _ = b := hb_eq.symm
    · intro i
      induction i using Fin.induction with
      | zero =>
        simpa [hfa_def, d] using hdpos
      | succ i _ =>
        simpa [hfa_def] using hspec.2.2.2.1 i
    · intro i
      induction i using Fin.induction with
      | zero =>
        change 0 < f 0 / extractFactors (k + 1) a f 0
        rw [hfa_def, Fin.cons_zero]
        exact hu_pos
      | succ i _ =>
        simpa [hfa_def] using hspec.2.2.2.2 i

/-- Split an ordered factorization of `a*b` into a pair via greedy `gcd` extraction. -/
def OrderedFactors.split {k a b : Nat} (hb : 0 < b)
    (f : OrderedFactors k (a * b)) :
    OrderedFactors k a × OrderedFactors k b :=
  let hspec := extractFactors_spec k a b f.val hb f.property.1 f.property.2
  (⟨extractFactors k a f.val, ⟨hspec.2.2.2.1, hspec.2.1⟩⟩,
    ⟨fun i => f.val i / extractFactors k a f.val i,
      ⟨hspec.2.2.2.2, hspec.2.2.1⟩⟩)

theorem OrderedFactors.split_mul_cancel {k a b : Nat} (hb : 0 < b)
    (f : OrderedFactors k (a * b)) (i : Fin k) :
    (OrderedFactors.split hb f).1.val i * (OrderedFactors.split hb f).2.val i =
      f.val i := by
  have hspec := extractFactors_spec k a b f.val hb f.property.1 f.property.2
  exact Nat.mul_div_cancel' (hspec.1 i)

/--
`#OrderedFactors k (a*b) ≤ #OrderedFactors k a * #OrderedFactors k b`.
-/
theorem card_orderedFactors_mul_le (k a b : Nat) :
    Fintype.card (OrderedFactors k (a * b)) ≤
      Fintype.card (OrderedFactors k a) * Fintype.card (OrderedFactors k b) := by
  by_cases hb : b = 0
  · subst hb
    simp
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    by_cases ha : a = 0
    · subst ha
      simp
    · let φ : OrderedFactors k (a * b) →
          OrderedFactors k a × OrderedFactors k b :=
        OrderedFactors.split hbpos
      have hinj : Function.Injective φ := by
        intro f g hfg
        refine Subtype.ext ?_
        funext i
        have hf := OrderedFactors.split_mul_cancel hbpos f i
        have hg := OrderedFactors.split_mul_cancel hbpos g i
        have h1 :=
          congrArg (fun p : OrderedFactors k a × OrderedFactors k b => p.1.val i) hfg
        have h2 :=
          congrArg (fun p : OrderedFactors k a × OrderedFactors k b => p.2.val i) hfg
        calc
          f.val i
              = (OrderedFactors.split hbpos f).1.val i *
                  (OrderedFactors.split hbpos f).2.val i := hf.symm
          _ = (OrderedFactors.split hbpos g).1.val i *
                (OrderedFactors.split hbpos g).2.val i := by rw [h1, h2]
          _ = g.val i := hg
      have hcard := Fintype.card_le_of_injective φ hinj
      simpa [Fintype.card_prod] using hcard

/--
`τ_k(n)` counts ordered positive `k`-factorizations of `n` (by definition).
-/
theorem tau_eq_card_ordered (k n : Nat) :
    tau k n = Fintype.card (OrderedFactors k n) :=
  rfl

theorem tau_eq_card_ordered_cast (k n : Nat) :
    (tau k n : Real) = (Fintype.card (OrderedFactors k n) : Real) := by
  exact_mod_cast tau_eq_card_ordered k n

/-- Multiplicativity upper bound: `τ_k(ab) ≤ τ_k(a) τ_k(b)`. -/
theorem tau_mul_le (k a b : Nat) (_hk : 1 ≤ k) :
    tau k (a * b) ≤ tau k a * tau k b := by
  simp_rw [tau_eq_card_ordered]
  exact card_orderedFactors_mul_le k a b

/-- `τ_k(h²) ≤ τ_k(h)²`. -/
theorem tau_sq_le (k h : Nat) (hk : 1 ≤ k) :
    tau k (h ^ 2) ≤ tau k h * tau k h := by
  simpa [pow_two] using tau_mul_le k h h hk

/-- `τ_k(n) ≥ 1` for `k, n ≥ 1` via the factorization `(n,1,…,1)`. -/
theorem tau_ge_one (k n : Nat) (hk : 1 ≤ k) (hn : 1 ≤ n) : 1 ≤ tau k n := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  let f : Fin (k' + 1) → Nat := Fin.cons n fun _ => 1
  have hpos : ∀ i, 0 < f i := by
    intro i
    induction i using Fin.induction with
    | zero => exact hn
    | succ _ _ => exact Nat.succ_pos 0
  have hprod : (∏ i, f i) = n := by
    simp [f, Fin.prod_cons, Finset.prod_const_one]
  have : Nonempty (OrderedFactors (k' + 1) n) := ⟨⟨f, hpos, hprod⟩⟩
  simpa [tau] using Nat.succ_le_of_lt (Fintype.card_pos_iff.2 this)

/-- Rebuild `Sol` equality from coordinate tuples. -/
theorem Sol.ext_n_m {s N : Nat} {x y : Sol s N}
    (hn : x.n = y.n) (hm : x.m = y.m) : x = y := by
  cases x; cases y; cases hn; cases hm; rfl

/--
PDF: fibre over `n₁ = g` is at most
`∑_{m ≤ N^{s-1}} τ_s(g m) τ_{s-1}(m)`
(equivalently `∑_{n ≤ g N^{s-1}, g∣n} τ_s(n) τ_{s-1}(n/g)`).
-/
theorem card_fibre_n1_le (s N g : Nat) (hs : 2 ≤ s) (_hN : 3 ≤ N)
    (_hg : 1 ≤ g) (_hgN : g ≤ N) :
    (((Finset.univ.filter fun x : Sol s N =>
        x.n ⟨0, by omega⟩ = g).card) : Real) ≤
      ∑ m ∈ Finset.Icc 1 (N ^ (s - 1)),
        (tau s (g * m) : Real) * (tau (s - 1) m : Real) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  -- Now `s = t + 1`, so `Fin.prod_univ_succ` applies definitionally.
  set F := Finset.univ.filter fun x : Sol (t + 1) N => x.n 0 = g
  let nTail (x : Sol (t + 1) N) : Nat := ∏ i : Fin t, x.n i.succ
  have hmem : ∀ x ∈ F, nTail x ∈ Finset.Icc 1 (N ^ t) := by
    intro x hx
    have hMpos : 1 ≤ nTail x :=
      Nat.succ_le_of_lt
        (Finset.prod_pos fun i _ =>
          lt_of_lt_of_le Nat.zero_lt_one (x.hn i.succ).1)
    have hMle : nTail x ≤ N ^ t := by
      calc
        nTail x ≤ ∏ _i : Fin t, N :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) fun i _ =>
            (x.hn i.succ).2
        _ = N ^ t := by simp [Finset.card_univ, Fintype.card_fin]
    exact Finset.mem_Icc.2 ⟨hMpos, hMle⟩
  have hsplit :
      F.card =
        ∑ m ∈ Finset.Icc 1 (N ^ t), (F.filter fun x => nTail x = m).card :=
    Finset.card_eq_sum_card_fiberwise hmem
  have hpoint :
      ∀ m ∈ Finset.Icc 1 (N ^ t),
        (F.filter fun x => nTail x = m).card ≤
          tau t m * tau (t + 1) (g * m) := by
    intro m hm
    set Fm := F.filter fun x => nTail x = m
    let φ : { x // x ∈ Fm } →
        OrderedFactors t m × OrderedFactors (t + 1) (g * m) := fun x =>
      have hxF : x.1 ∈ F := (Finset.mem_filter.1 x.2).1
      have hnt : nTail x.1 = m := (Finset.mem_filter.1 x.2).2
      have hn1 : x.1.n 0 = g := (Finset.mem_filter.1 hxF).2
      have hprod_m : ∏ i, x.1.m i = g * m := by
        have hprod_n : x.1.n 0 * nTail x.1 = ∏ i, x.1.n i :=
          (Fin.prod_univ_succ _).symm
        calc
          ∏ i, x.1.m i = ∏ i, x.1.n i := x.1.hprod.symm
          _ = x.1.n 0 * nTail x.1 := hprod_n.symm
          _ = g * m := by rw [hn1, hnt]
      (⟨fun i => x.1.n i.succ,
          ⟨fun i => lt_of_lt_of_le Nat.zero_lt_one (x.1.hn i.succ).1,
            by simpa [nTail, hnt] using rfl⟩⟩,
        ⟨x.1.m,
          ⟨fun i => lt_of_lt_of_le Nat.zero_lt_one (x.1.hm i).1, hprod_m⟩⟩)
    have hinj : Function.Injective φ := by
      intro x y hxy
      have hntail :
          (fun i : Fin t => x.1.n i.succ) = fun i => y.1.n i.succ :=
        congrArg (fun p : OrderedFactors t m × OrderedFactors (t + 1) (g * m) =>
          p.1.val) hxy
      have hm' : x.1.m = y.1.m :=
        congrArg (fun p : OrderedFactors t m × OrderedFactors (t + 1) (g * m) =>
          p.2.val) hxy
      have hn0 : x.1.n 0 = y.1.n 0 := by
        have hx := (Finset.mem_filter.1 (Finset.mem_filter.1 x.2).1).2
        have hy := (Finset.mem_filter.1 (Finset.mem_filter.1 y.2).1).2
        rw [hx, hy]
      have hn : x.1.n = y.1.n := by
        funext i
        induction i using Fin.induction with
        | zero => exact hn0
        | succ i _ => exact congrFun hntail i
      exact Subtype.ext (Sol.ext_n_m hn hm')
    have hcard := Fintype.card_le_of_injective φ hinj
    have hFm : Fm.card = Fintype.card { x // x ∈ Fm } :=
      (Fintype.card_coe Fm).symm
    have hprod_card :
        Fintype.card (OrderedFactors t m × OrderedFactors (t + 1) (g * m)) =
          tau t m * tau (t + 1) (g * m) := by
      simp [Fintype.card_prod, tau]
    omega
  have hnat :
      F.card ≤
        ∑ m ∈ Finset.Icc 1 (N ^ t),
          tau (t + 1) (g * m) * tau t m := by
    rw [hsplit]
    refine (Finset.sum_le_sum hpoint).trans_eq ?_
    refine Finset.sum_congr rfl ?_
    intro m _; ac_rfl
  have hreal :
      (F.card : Real) ≤
        ∑ m ∈ Finset.Icc 1 (N ^ t),
          (tau (t + 1) (g * m) : Real) * (tau t m : Real) := by
    exact_mod_cast hnat
  simpa [F] using hreal

/--
PDF sparse-complement divisor sum, with `g∣n` built in via `m ↦ g m`.

From Trusted `divisor_sum_sq_bound` + AM-GM one gets exponent `s^2`
(the paper's `s+1` is too optimistic for an absolute factor; `s^2` is
absorbed by `sparseRHS`'s `(s+1)^2`).  Requires `g ≤ N`.
-/
theorem tau_mul_sum_bound (s g N : Nat) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hg : 1 ≤ g) (hgN : g ≤ N) :
    (∑ m ∈ Finset.Icc 1 (N ^ (s - 1)),
        (tau s (g * m) : Real) * (tau (s - 1) m : Real)) ≤
      (g : Real) * (N : Real) ^ (s - 1) *
        (2 * (s : Real) * Real.log N) ^ (s ^ 2) := by
  set M := N ^ (s - 1)
  set X := g * M
  have hgpos : 0 < g := hg
  have hM3 : 3 ≤ M :=
    le_trans hN (Nat.le_self_pow (by omega : s - 1 ≠ 0) N)
  have hX3 : 3 ≤ X :=
    le_trans hM3 (Nat.le_mul_of_pos_left _ hgpos)
  have hXle : X ≤ N ^ s := by
    have hs1' : 1 ≤ s := le_trans (by decide : 1 ≤ 2) hs
    calc
      X = g * N ^ (s - 1) := rfl
      _ ≤ N * N ^ (s - 1) := Nat.mul_le_mul_right _ hgN
      _ = N ^ (s - 1) * N := Nat.mul_comm _ _
      _ = N ^ s := by
          rw [← Nat.pow_succ]
          congr 1
          omega
  have hbase : 1 ≤ 2 * (s : Real) * Real.log N := by
    have hs2 : (2 : Real) ≤ (s : Real) := by exact_mod_cast hs
    have h1log3 : (1 : Real) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : Real) < 3)).2 Real.exp_one_lt_three
    have hlog3 : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    nlinarith
  have hlogXle : Real.log X ≤ (s : Real) * Real.log N := by
    have hXpos : (0 : Real) < X := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hX3)
    have hXleR : (X : Real) ≤ (N : Real) ^ s := by exact_mod_cast hXle
    have hlog := Real.log_le_log hXpos hXleR
    rwa [Real.log_pow (N : Real) s] at hlog
  have hlogMle : Real.log M ≤ (s : Real) * Real.log N := by
    have hMpos : (0 : Real) < M := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hM3)
    have hle : M ≤ N ^ s :=
      Nat.pow_le_pow_right (by omega : 0 < N) (Nat.sub_le s 1)
    have hleR : (M : Real) ≤ (N : Real) ^ s := by exact_mod_cast hle
    have hlog := Real.log_le_log hMpos hleR
    rwa [Real.log_pow (N : Real) s] at hlog
  have h2logX : 2 * Real.log X ≤ 2 * (s : Real) * Real.log N := by linarith
  have h2logM : 2 * Real.log M ≤ 2 * (s : Real) * Real.log N := by linarith
  have hs1 : 1 ≤ s - 1 := by omega
  have hpoint :
      ∀ m ∈ Finset.Icc 1 M,
        (tau s (g * m) : Real) * (tau (s - 1) m : Real) ≤
          ((tau s (g * m) : Real) ^ 2 + (tau (s - 1) m : Real) ^ 2) / 2 := by
    intro m _
    have h := two_mul_le_add_sq (tau s (g * m) : Real) (tau (s - 1) m : Real)
    linarith
  have hsum_am :
      ∑ m ∈ Finset.Icc 1 M,
          (tau s (g * m) : Real) * (tau (s - 1) m : Real) ≤
        (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2) / 2 +
          (∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 := by
    calc
      ∑ m ∈ Finset.Icc 1 M,
            (tau s (g * m) : Real) * (tau (s - 1) m : Real)
          ≤ ∑ m ∈ Finset.Icc 1 M,
              ((tau s (g * m) : Real) ^ 2 + (tau (s - 1) m : Real) ^ 2) / 2 :=
            Finset.sum_le_sum hpoint
      _ = (∑ m ∈ Finset.Icc 1 M,
              ((tau s (g * m) : Real) ^ 2 + (tau (s - 1) m : Real) ^ 2)) / 2 :=
            (Finset.sum_div (Finset.Icc 1 M)
              (fun m => (tau s (g * m) : Real) ^ 2 + (tau (s - 1) m : Real) ^ 2)
              2).symm
      _ = (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2 +
              ∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 := by
            rw [Finset.sum_add_distrib]
      _ = (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2) / 2 +
            (∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 := by
            ring
  have hsq_gm :
      ∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2 ≤
        ∑ n ∈ Finset.Icc 1 X, (tau s n : Real) ^ 2 := by
    have hmaps : ∀ m ∈ Finset.Icc 1 M, g * m ∈ Finset.Icc 1 X := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      have hmM : m ≤ M := (Finset.mem_Icc.1 hm).2
      refine Finset.mem_Icc.2 ⟨?_, ?_⟩
      · calc
          1 ≤ g := hg
          _ ≤ g * m := Nat.le_mul_of_pos_right g hm1
      · calc
          g * m ≤ g * M := Nat.mul_le_mul_left g hmM
          _ = X := rfl
    have hinj :
        ∀ m₁ ∈ Finset.Icc 1 M, ∀ m₂ ∈ Finset.Icc 1 M,
          g * m₁ = g * m₂ → m₁ = m₂ := fun _ _ _ _ h =>
      Nat.eq_of_mul_eq_mul_left hgpos h
    calc
      ∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2
          = ∑ n ∈ (Finset.Icc 1 M).image (fun m => g * m),
              (tau s n : Real) ^ 2 := by
            refine Eq.symm (Finset.sum_image ?_)
            exact fun m₁ hm₁ m₂ hm₂ h => hinj m₁ hm₁ m₂ hm₂ h
      _ ≤ ∑ n ∈ Finset.Icc 1 X, (tau s n : Real) ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
            intro n hn
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn
            exact hmaps m hm
  have hsq1 :
      ∑ n ∈ Finset.Icc 1 X, (tau s n : Real) ^ 2 ≤
        (X : Real) * (2 * Real.log X) ^ (s ^ 2 - 1) :=
    divisor_sum_sq_bound X s hX3 (le_trans (by decide : 1 ≤ 2) hs)
  have hsq2 :
      ∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2 ≤
        (M : Real) * (2 * Real.log M) ^ ((s - 1) ^ 2 - 1) :=
    divisor_sum_sq_bound M (s - 1) hM3 hs1
  have hpow1 :
      (2 * Real.log X) ^ (s ^ 2 - 1) ≤
        (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) :=
    pow_le_pow_left₀ (by positivity) h2logX _
  have hpow2 :
      (2 * Real.log M) ^ ((s - 1) ^ 2 - 1) ≤
        (2 * (s : Real) * Real.log N) ^ ((s - 1) ^ 2 - 1) :=
    pow_le_pow_left₀ (by positivity) h2logM _
  have hexp : (s - 1) ^ 2 - 1 ≤ s ^ 2 - 1 := by
    have : (s - 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
    omega
  have hpow2' :
      (2 * (s : Real) * Real.log N) ^ ((s - 1) ^ 2 - 1) ≤
        (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) :=
    pow_le_pow_right₀ hbase hexp
  have hhalf :
      (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2) / 2 +
          (∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 ≤
        (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) := by
    have h1 :
        (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2) / 2 ≤
          (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      refine (hsq_gm.trans hsq1).trans ?_
      exact mul_le_mul_of_nonneg_left hpow1 (by positivity)
    have h2 :
        (∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 ≤
          (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have hMleX : (M : Real) ≤ (X : Real) := by
        exact_mod_cast (Nat.le_mul_of_pos_left M hgpos)
      calc
        ∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2
            ≤ (M : Real) * (2 * Real.log M) ^ ((s - 1) ^ 2 - 1) := hsq2
        _ ≤ (X : Real) * (2 * Real.log M) ^ ((s - 1) ^ 2 - 1) :=
              mul_le_mul_of_nonneg_right hMleX (by positivity)
        _ ≤ (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) :=
              mul_le_mul_of_nonneg_left (hpow2.trans hpow2') (by positivity)
    calc
      _ ≤ (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) / 2 +
            (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) / 2 :=
          add_le_add h1 h2
      _ = (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) := by ring
  have hfinal_exp :
      (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) ≤
        (2 * (s : Real) * Real.log N) ^ (s ^ 2) :=
    pow_le_pow_right₀ hbase (Nat.sub_le _ _)
  calc
    ∑ m ∈ Finset.Icc 1 M,
          (tau s (g * m) : Real) * (tau (s - 1) m : Real)
        ≤ (∑ m ∈ Finset.Icc 1 M, (tau s (g * m) : Real) ^ 2) / 2 +
            (∑ m ∈ Finset.Icc 1 M, (tau (s - 1) m : Real) ^ 2) / 2 :=
          hsum_am
    _ ≤ (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2 - 1) := hhalf
    _ ≤ (X : Real) * (2 * (s : Real) * Real.log N) ^ (s ^ 2) :=
          mul_le_mul_of_nonneg_left hfinal_exp (by positivity)
    _ = (g : Real) * (N : Real) ^ (s - 1) *
          (2 * (s : Real) * Real.log N) ^ (s ^ 2) := by
          simp [X, M]

theorem fibre_n1_bound (s N g : Nat) (hs : 2 ≤ s) (hN : 3 ≤ N)
    (hg : 1 ≤ g) (hgN : g ≤ N) :
    (((Finset.univ.filter fun x : Sol s N =>
        x.n ⟨0, by omega⟩ = g).card) : Real) ≤
      (g : Real) * (N : Real) ^ (s - 1) *
        (2 * (s : Real) * Real.log N) ^ (s ^ 2) :=
  le_trans (card_fibre_n1_le s N g hs hN hg hgN)
    (tau_mul_sum_bound s g N hs hN hg hgN)

end RMFLean
