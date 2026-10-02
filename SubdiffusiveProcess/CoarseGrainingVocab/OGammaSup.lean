import SubdiffusiveProcess.CoarseGrainingVocab.OGammaTail
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# `OGammaLE` for a finite supremum

Every random-factor tail in the paper is stated for a *supremum* — over scales `n ≤ m`, over
lattice sites, over a ball.  This file supplies the finite case, which is the reusable core:

* `measureReal_sup'_ge_le` — the union bound for the tail of a `Finset.sup'`;
* `min_one_le_rpow_comparison` — `min 1 (K u^{-p}) ≤ K^{3/p} u^{-3}` for `u ≥ 1`, `K ≥ 1`,
  `p ≥ 3`.  The point of the comparison is that the left side is not integrable against `du`
  when `p` is small and `K` is large, while the right side always is; the `min` with `1` is
  what a union bound over `N` terms forces, and it is exactly what the naive
  "sum the tails" estimate loses;
* `integral_cube_tail` — `∫₀^∞ (1+s)^{-3} ds = 1/2`;
* `ogammaLE_sup'` — the conclusion: if each `X i` satisfies `OGammaLE μ 2 A`, then the
  supremum satisfies it at scale `A √p`, for any `p ≥ 3` with `(2·card)^{3/p} ≤ 2`.

The scale grows like `A √(log card)`, which is the correct order — the same square root that
`ogammaLE_sum_range_of_iIndepFun` produces for sums, and for the same reason: a Gaussian tail
absorbs a union bound at logarithmic cost.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology ProbabilityTheory Finset

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.OGamma

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- **Union bound for the tail of a finite supremum.** -/
theorem measureReal_sup'_ge_le [IsFiniteMeasure mu] {iota : Type*} {s : Finset iota}
    (hs : s.Nonempty) {X : iota → Omega → ℝ} (lam : ℝ) :
    mu.real {omega | lam ≤ s.sup' hs (fun i => X i omega)}
      ≤ ∑ i ∈ s, mu.real {omega | lam ≤ X i omega} := by
  have hset : {omega | lam ≤ s.sup' hs (fun i => X i omega)}
      = ⋃ i ∈ s, {omega | lam ≤ X i omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact Finset.le_sup'_iff hs
  rw [hset]
  exact measureReal_biUnion_finset_le s _

/-! ### The comparison function -/

omit [MeasurableSpace Omega] in
/-- `min 1 (K u^{-p}) ≤ K^{3/p} u^{-3}`.  Both branches reduce to `K^{1/p} ≤ u` or its
negation. -/
theorem min_one_le_rpow_comparison {K u p : ℝ} (hK : 1 ≤ K) (hu : 1 ≤ u) (hp : 3 ≤ p) :
    min 1 (K * u ^ (-p)) ≤ K ^ (3/p) * u ^ (-(3:ℝ)) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  have hsplit : K = K ^ (3/p) * K ^ ((p-3)/p) := by
    rw [← Real.rpow_add hK0]
    rw [show 3/p + (p-3)/p = 1 by field_simp; ring]
    exact (Real.rpow_one K).symm
  rcases le_or_gt (K ^ (1/p)) u with hcase | hcase
  · -- `K^{1/p} ≤ u`: the min is the second term
    have hkey : K ^ ((p-3)/p) ≤ u ^ (p-3) := by
      have h1 : K ^ ((p-3)/p) = (K ^ (1/p)) ^ (p-3) := by
        rw [← Real.rpow_mul hK0.le]
        congr 1
        field_simp
      rw [h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hK0.le _) hcase (by linarith)
    refine le_trans (min_le_right _ _) ?_
    calc K * u ^ (-p) = K ^ (3/p) * K ^ ((p-3)/p) * u ^ (-p) := by rw [← hsplit]
      _ ≤ K ^ (3/p) * u ^ (p-3) * u ^ (-p) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey ?_) ?_
          · exact Real.rpow_nonneg hK0.le _
          · exact Real.rpow_nonneg hu0.le _
      _ = K ^ (3/p) * u ^ (-(3:ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hu0]
          congr 2
          ring
  · -- `u < K^{1/p}`: the min is `1`
    have hkey : u ^ (3:ℝ) < K ^ (3/p) := by
      have h1 : (K ^ (1/p)) ^ (3:ℝ) = K ^ (3/p) := by
        rw [← Real.rpow_mul hK0.le]
        congr 1
        field_simp
      rw [← h1]
      exact Real.rpow_lt_rpow hu0.le hcase (by norm_num)
    refine le_trans (min_le_left _ _) ?_
    rw [Real.rpow_neg hu0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hu0 3)]
    linarith

/-! ### `∫₀^∞ (1+s)^{-3} ds = 1/2` -/

omit [MeasurableSpace Omega] in
theorem hasDerivAt_cubePrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun s : ℝ => -(1/2 : ℝ) / (1+s)^2) (1 / (1+x)^3) x := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  have hu : HasDerivAt (fun s : ℝ => (1+s)^2) (2 * (1+x)) x := by
    simpa using ((hasDerivAt_id x).const_add (1:ℝ)).pow 2
  have h := (hasDerivAt_const x (-(1/2):ℝ)).div hu (by positivity)
  convert h using 1
  field_simp
  ring

omit [MeasurableSpace Omega] in
theorem tendsto_cubePrimitive :
    Tendsto (fun s : ℝ => -(1/2 : ℝ) / (1+s)^2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => 1 + s) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have h2 : Tendsto (fun s : ℝ => (1+s)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp h1
  have h3 := (h2.inv_tendsto_atTop).const_mul (-(1/2 : ℝ))
  rw [mul_zero] at h3
  simpa [div_eq_mul_inv] using h3

omit [MeasurableSpace Omega] in
theorem integrableOn_cube_tail : IntegrableOn (fun s : ℝ => 1 / (1+s)^3) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg
    ((hasDerivAt_cubePrimitive le_rfl).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_cubePrimitive (le_of_lt hx))
    (fun x hx => by
      have : (0:ℝ) < 1 + x := by simp at hx; linarith
      positivity)
    tendsto_cubePrimitive

omit [MeasurableSpace Omega] in
theorem integral_cube_tail : ∫ s in Ioi (0:ℝ), 1 / (1+s)^3 = 1/2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0:ℝ)) (f := fun s : ℝ => -(1/2 : ℝ) / (1+s)^2) (f' := fun s : ℝ => 1 / (1+s)^3)
    (m := 0) ((hasDerivAt_cubePrimitive le_rfl).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_cubePrimitive (le_of_lt hx)) integrableOn_cube_tail
    tendsto_cubePrimitive
  simpa using h

omit [MeasurableSpace Omega] in
theorem rpow_neg_three {u : ℝ} (hu : 0 < u) : u ^ (-(3:ℝ)) = 1 / u^3 := by
  rw [Real.rpow_neg hu.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    one_div]

/-- **`OGammaLE` for a finite supremum.**  If each `X i`, `i ∈ s`, satisfies `OGammaLE μ 2 A`,
then so does the supremum at scale `A √p`, for any `p ≥ 3` with `(2 · card s)^{3/p} ≤ 2`.

Since that condition holds as soon as `p ≥ 3 log(2 · card s) / log 2`, the scale is
`A √(log card)` up to an absolute constant — the correct order.  A Gaussian tail absorbs a
union bound at logarithmic cost, which is the same mechanism that gives
`ogammaLE_sum_range_of_iIndepFun` its square root. -/
theorem ogammaLE_sup' [IsProbabilityMeasure mu] {iota : Type*} {s : Finset iota}
    (hs : s.Nonempty) {X : iota → Omega → ℝ} {A p : ℝ} (hA : 0 < A) (hp : 3 ≤ p)
    (hmeas : AEMeasurable (fun omega => s.sup' hs (fun i => X i omega)) mu)
    (hcard : ((2 * s.card : ℝ)) ^ (3/p) ≤ 2)
    (hX : ∀ i ∈ s, SubdiffusiveProcess.OGammaLE mu 2 A (X i)) :
    SubdiffusiveProcess.OGammaLE mu 2 (A * Real.sqrt p) (fun omega => s.sup' hs (fun i => X i omega)) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hsp : (0:ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hB : (0:ℝ) < A * Real.sqrt p := by positivity
  set K : ℝ := 2 * s.card with hKdef
  have hcard1 : (1:ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  have hK1 : (1:ℝ) ≤ K := by rw [hKdef]; linarith
  have hK0 : (0:ℝ) < K := by linarith
  have hKp0 : (0:ℝ) < K ^ (3/p) := Real.rpow_pos_of_pos hK0 _
  refine ogammaLE_of_layercake hB hmeas ?_
    (by simpa [mul_one_div] using integrableOn_cube_tail.const_mul (K ^ (3/p))) ?_ ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with sv hsv
    have : (0:ℝ) < 1 + sv := by simp at hsv; linarith
    positivity
  · rw [integral_const_mul]
    have hint : ∫ a in Ioi (0:ℝ), ((1+a)^3)⁻¹ = 1/2 := by
      simpa [one_div] using integral_cube_tail
    rw [hint]
    linarith
  · intro sv hsv
    have hs0 : (0:ℝ) < sv := hsv
    have hu : (1:ℝ) ≤ 1 + sv := by linarith
    have hu0 : (0:ℝ) < 1 + sv := by linarith
    have hL : (0:ℝ) < Real.log (1+sv) := Real.log_pos (by linarith)
    have hlam : (0:ℝ) < (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)) := by positivity
    -- each summand's tail
    have hone : ∀ i ∈ s,
        mu.real {omega | (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)) ≤ X i omega}
          ≤ 2 * ((1+sv) ^ (-p)) := by
      intro i hi
      have h := measureReal_ge_le_of_ogammaLE (hX i hi) hA (by norm_num) hlam.le
      have harg : (A⁻¹ * ((A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)))) ^ (2:ℝ)
          = p * Real.log (1+sv) := by
        rw [rpow_two]
        have : A⁻¹ * ((A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)))
            = Real.sqrt p * Real.sqrt (Real.log (1+sv)) := by
          field_simp
        rw [this, mul_pow, Real.sq_sqrt hp0.le, Real.sq_sqrt hL.le]
      rw [harg] at h
      have hexp : Real.exp (-(p * Real.log (1+sv))) = (1+sv) ^ (-p) := by
        rw [Real.rpow_def_of_pos hu0]
        congr 1
        ring
      rwa [hexp] at h
    -- union bound, then the comparison
    have hsum : mu.real {omega | (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv))
          ≤ s.sup' hs (fun i => X i omega)} ≤ K * (1+sv) ^ (-p) := by
      refine le_trans (measureReal_sup'_ge_le hs _) ?_
      calc ∑ i ∈ s, mu.real {omega |
              (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)) ≤ X i omega}
          ≤ ∑ _i ∈ s, 2 * ((1+sv) ^ (-p)) := Finset.sum_le_sum hone
        _ = K * (1+sv) ^ (-p) := by
            rw [Finset.sum_const, nsmul_eq_mul, hKdef]; ring
    have hle1 : mu.real {omega | (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv))
          ≤ s.sup' hs (fun i => X i omega)} ≤ 1 := by
      simpa using measureReal_le_one (μ := mu) (s := {omega |
        (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv)) ≤ s.sup' hs (fun i => X i omega)})
    have hcomp := min_one_le_rpow_comparison hK1 hu hp
    rw [rpow_neg_three hu0] at hcomp
    have hfinal : mu.real {omega | (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv))
          ≤ s.sup' hs (fun i => X i omega)} ≤ K ^ (3/p) * (1 / (1+sv)^3) :=
      le_trans (le_min hle1 hsum) hcomp
    have hfin : mu {omega | (A * Real.sqrt p) * Real.sqrt (Real.log (1+sv))
        ≤ s.sup' hs (fun i => X i omega)} ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa [one_div] using hfinal

/-- **The supremum lemma with the scale supplied.**  `p = 5 (1 + log (2 · card s))` meets both
conditions of `ogammaLE_sup'`, so a finite supremum of `OGammaLE μ 2 A` variables satisfies
`OGammaLE μ 2 (A √(5 (1 + log (2 · card s))))` — scale `A √(log card)` up to a constant. -/
theorem ogammaLE_sup'_log [IsProbabilityMeasure mu] {iota : Type*} {s : Finset iota}
    (hs : s.Nonempty) {X : iota → Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hmeas : AEMeasurable (fun omega => s.sup' hs (fun i => X i omega)) mu)
    (hX : ∀ i ∈ s, SubdiffusiveProcess.OGammaLE mu 2 A (X i)) :
    SubdiffusiveProcess.OGammaLE mu 2
      (A * Real.sqrt (5 * (1 + Real.log (2 * s.card)))) 
      (fun omega => s.sup' hs (fun i => X i omega)) := by
  have hcard1 : (1:ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  have hK0 : (0:ℝ) < 2 * (s.card : ℝ) := by linarith
  have hK1 : (1:ℝ) ≤ 2 * (s.card : ℝ) := by linarith
  have hlogK : (0:ℝ) ≤ Real.log (2 * s.card) := Real.log_nonneg hK1
  set p : ℝ := 5 * (1 + Real.log (2 * s.card)) with hpdef
  have hp : (3:ℝ) ≤ p := by rw [hpdef]; linarith
  have hp0 : (0:ℝ) < p := by linarith
  refine ogammaLE_sup' hs hA hp hmeas ?_ hX
  have hrw : ((2 * s.card : ℝ)) ^ (3/p) = Real.exp (Real.log (2 * s.card) * (3/p)) :=
    Real.rpow_def_of_pos hK0 _
  rw [hrw]
  have hexp : Real.log (2 * s.card) * (3/p) ≤ 3/5 := by
    have hden : (0:ℝ) < 5 * (1 + Real.log (2 * s.card)) := by linarith
    have hrw2 : Real.log (2 * s.card) * (3 / (5 * (1 + Real.log (2 * s.card))))
        = 3 * Real.log (2 * s.card) / (5 * (1 + Real.log (2 * s.card))) := by ring
    rw [hpdef, hrw2, div_le_iff₀ hden]
    nlinarith [hlogK]
  calc Real.exp (Real.log (2 * s.card) * (3/p)) ≤ Real.exp (3/5) :=
        Real.exp_le_exp.mpr hexp
    _ ≤ 2 := by
        have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
        rw [← h2]
        exact Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])



theorem aemeasurable_finset_sup' {iota : Type*} {s : Finset iota} (hs : s.Nonempty)
    {f : iota → Omega → ℝ} (hf : ∀ i ∈ s, AEMeasurable (f i) mu) :
    AEMeasurable (fun omega => s.sup' hs (fun i => f i omega)) mu := by
  classical
  choose! g hgmeas hgeq using hf
  refine ⟨fun omega => s.sup' hs (fun i => g i omega), ?_, ?_⟩
  · have hm := Finset.measurable_sup' hs (fun i hi => hgmeas i hi)
    have hfun : (fun omega => s.sup' hs (fun i => g i omega))
        = s.sup' hs g := by
      funext omega
      exact (Finset.sup'_apply hs g omega).symm
    rw [hfun]
    exact hm
  · have hall : ∀ᵐ omega ∂mu, ∀ i ∈ s, f i omega = g i omega := by
      rw [eventually_all_finset]
      exact fun i hi => hgeq i hi
    filter_upwards [hall] with omega homega
    exact Finset.sup'_congr hs rfl fun i hi => homega i hi



theorem ogammaLE_abs [IsProbabilityMeasure mu] {A : ℝ} (hA : 0 < A) {X : Omega → ℝ}
    (hXm : AEMeasurable X mu)
    (hX : SubdiffusiveProcess.OGammaLE mu 2 A X) (hXneg : SubdiffusiveProcess.OGammaLE mu 2 A (fun omega => -X omega)) :
    SubdiffusiveProcess.OGammaLE mu 2 (A * Real.sqrt (5 * (1 + Real.log (2 * (2 : ℕ)))))
      (fun omega => |X omega|) := by
  classical
  set F : Fin 2 → Omega → ℝ := fun i => if i = 0 then X else fun omega => -X omega with hF
  have hne : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hsup : ∀ omega, (Finset.univ : Finset (Fin 2)).sup' hne (fun i => F i omega)
      = |X omega| := by
    intro omega
    refine le_antisymm (Finset.sup'_le hne _ fun i _ => ?_) ?_
    · by_cases hi : i = 0
      · simpa [hF, hi] using le_abs_self (X omega)
      · simpa [hF, hi] using neg_le_abs (X omega)
    · rw [abs_eq_max_neg]
      refine max_le ?_ ?_
      · have h0 := Finset.le_sup' (f := fun i => F i omega) (Finset.mem_univ (0 : Fin 2))
        simp only [hF, if_pos rfl] at h0
        exact h0
      · have h1 := Finset.le_sup' (f := fun i => F i omega) (Finset.mem_univ (1 : Fin 2))
        simp only [hF, if_neg (by decide : ¬((1 : Fin 2) = 0))] at h1
        exact h1
  have hcard : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by simp
  have hmeas : AEMeasurable
      (fun omega => (Finset.univ : Finset (Fin 2)).sup' hne (fun i => F i omega)) mu := by
    refine aemeasurable_finset_sup' hne fun i _ => ?_
    by_cases hi : i = 0
    · simpa [hF, hi] using hXm
    · simpa [hF, hi] using hXm.neg
  have hbounds : ∀ i ∈ (Finset.univ : Finset (Fin 2)), SubdiffusiveProcess.OGammaLE mu 2 A (F i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [hF, hi] using hX
    · simpa [hF, hi] using hXneg
  have hres := ogammaLE_sup'_log hne hA hmeas hbounds
  rw [hcard] at hres
  have hfun : (fun omega => (Finset.univ : Finset (Fin 2)).sup' hne (fun i => F i omega))
      = fun omega => |X omega| := funext hsup
  rw [hfun] at hres
  simpa using hres

end SubdiffusiveProcess.CoarseGrainingVocab.OGamma
