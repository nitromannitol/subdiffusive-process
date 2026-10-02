import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.Probability.OpNormCauchyInProbability

/-!
# Operator-norm continuity of the volume-response operator in the L∞ potential

The volume-source solver `volumeResponseOperator S (expPotentialCoefficient g)` is a symmetric
operator on `DomainL2 Ω` (see `VolumeResponseOperator.lean`), and its quadratic pairing is the
inverse variational response (`volumeResponseOperator_quadratic`).  The potential comparison
`inverseResponse_potential_comparison` bounds the responses of two L∞ potentials multiplicatively
by `exp ‖g - h‖`; this module turns that into an *operator-norm* bound

  `‖Gh - Gg‖ ≤ 2 * (exp ‖h - g‖ - 1) * ‖Gg‖`,

using the polarization identity (`Probability.aux_polarization`, with the crude bound
`‖x ± y‖ ≤ 2` on the unit ball) and the bilinear-to-operator-norm upgrade
(`Probability.aux_opNorm_le_of_inner`).  Consequently `g ↦ volumeResponseOperator S
(expPotentialCoefficient g)` is continuous, and Borel measurable for the Borel σ-algebras on the
parameter and on the operator space.

This matters because the operator space `DomainL2 Ω →L[ℝ] DomainL2 Ω` need not be separable:
pointwise-evaluation measurability of the quadratic forms alone does not give norm-Borel
measurability of an operator-valued map, whereas continuity does (and the bound is uniform, not
merely pointwise).

No compactness, convergence or model-level statement is asserted; the only inputs are the solver,
its quadratic identity and symmetry, and the multiplicative potential comparison.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal InnerProductSpace

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **Quadratic difference bound.**  For two `L∞` potentials `g, h`, the quadratic pairing of the
difference of the volume-response operators is bounded by `(exp ‖h - g‖ - 1)` times the pairing of
the reference operator `Gg`, and hence by `(exp ‖h - g‖ - 1) * ‖Gg‖ * ‖f‖²`. -/
theorem volumeResponseOperator_sub_quadratic_le (S : ResponseSpace Ω)
    (g h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) (f : DomainL2 Ω) :
    |inner ℝ f ((volumeResponseOperator S (expPotentialCoefficient h) -
        volumeResponseOperator S (expPotentialCoefficient g)) f)| ≤
      (Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖ ^ 2 := by
  set a : ℝ :=
    inverseResponse S (expPotentialCoefficient g)
      ((sobolevVolumeLoad f).comp S.space.subtypeL) with ha_def
  set b : ℝ :=
    inverseResponse S (expPotentialCoefficient h)
      ((sobolevVolumeLoad f).comp S.space.subtypeL) with hb_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    exact inverseResponse_nonneg S (expPotentialCoefficient g) _
  have hb : 0 ≤ b := by
    rw [hb_def]
    exact inverseResponse_nonneg S (expPotentialCoefficient h) _
  have hcmp := inverseResponse_potential_comparison S
    ((sobolevVolumeLoad f).comp S.space.subtypeL) g h
  rw [← ha_def, ← hb_def] at hcmp
  have hr : (0 : ℝ) ≤ ‖g - h‖ := norm_nonneg (g - h)
  -- the quadratic pairing of the difference is the difference of the responses
  have hdiff : inner ℝ f ((volumeResponseOperator S (expPotentialCoefficient h) -
      volumeResponseOperator S (expPotentialCoefficient g)) f) = b - a := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, volumeResponseOperator_quadratic,
      volumeResponseOperator_quadratic]
  -- the two one-sided bounds
  have hup : b - a ≤ (Real.exp ‖g - h‖ - 1) * a := by nlinarith [hcmp.2, ha]
  have hlow : -(b - a) ≤ (Real.exp ‖g - h‖ - 1) * a := by
    have hineq : 1 - Real.exp (-‖g - h‖) ≤ Real.exp ‖g - h‖ - 1 := by
      have hmul : Real.exp (-‖g - h‖) * Real.exp ‖g - h‖ = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hle1 : Real.exp (-‖g - h‖) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
      have hnn : 0 ≤ Real.exp ‖g - h‖ - 1 := by
        have := Real.one_le_exp (norm_nonneg (g - h)); linarith
      calc 1 - Real.exp (-‖g - h‖) = Real.exp (-‖g - h‖) * (Real.exp ‖g - h‖ - 1) := by
            rw [mul_sub, hmul, mul_one]
        _ ≤ 1 * (Real.exp ‖g - h‖ - 1) := mul_le_mul_of_nonneg_right hle1 hnn
        _ = Real.exp ‖g - h‖ - 1 := one_mul _
    have h4 : a - b ≤ (1 - Real.exp (-‖g - h‖)) * a := by nlinarith [hcmp.1]
    have h3 : (1 - Real.exp (-‖g - h‖)) * a ≤ (Real.exp ‖g - h‖ - 1) * a :=
      mul_le_mul_of_nonneg_right hineq ha
    have hneg : -(b - a) = a - b := by ring
    rw [hneg]
    exact h4.trans h3
  have habs : |b - a| ≤ (Real.exp ‖g - h‖ - 1) * a := by
    rw [abs_le]
    exact ⟨by linarith [hlow], hup⟩
  -- bound the response at `g` by the operator norm and `‖f‖²`
  have ha_le : a ≤ ‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖ ^ 2 := by
    have hquad := volumeResponseOperator_quadratic S (expPotentialCoefficient g) f
    have h1 : a = inner ℝ f (volumeResponseOperator S (expPotentialCoefficient g) f) := by
      rw [ha_def]
      exact hquad.symm
    calc a = inner ℝ f (volumeResponseOperator S (expPotentialCoefficient g) f) := h1
      _ ≤ |inner ℝ f (volumeResponseOperator S (expPotentialCoefficient g) f)| := le_abs_self _
      _ ≤ ‖f‖ * ‖volumeResponseOperator S (expPotentialCoefficient g) f‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖ ^ 2 := by ring
  rw [hdiff]
  calc |b - a| ≤ (Real.exp ‖g - h‖ - 1) * a := habs
    _ ≤ (Real.exp ‖g - h‖ - 1) *
          (‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ha_le (by
          have := Real.one_le_exp (norm_nonneg (g - h)); linarith)
    _ = (Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖ * ‖f‖ ^ 2 := by
        rw [norm_sub_rev g h]
        ring

/-- **Operator-norm difference bound.**  The difference of the volume-response operators at two
`L∞` potentials is bounded in operator norm by `2 * (exp ‖h - g‖ - 1) * ‖Gg‖`, via polarization
on the unit ball. -/
theorem volumeResponseOperator_sub_norm_le (S : ResponseSpace Ω)
    (g h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ‖volumeResponseOperator S (expPotentialCoefficient h) -
        volumeResponseOperator S (expPotentialCoefficient g)‖ ≤
      2 * (Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖ := by
  set A : DomainL2 Ω →L[ℝ] DomainL2 Ω :=
    volumeResponseOperator S (expPotentialCoefficient h) -
      volumeResponseOperator S (expPotentialCoefficient g) with hA_def
  have hsymA : ∀ x y : DomainL2 Ω, inner ℝ (A x) y = inner ℝ x (A y) := by
    intro x y
    have h1 := volumeResponseOperator_symm S (expPotentialCoefficient h) x y
    have h2 := volumeResponseOperator_symm S (expPotentialCoefficient g) x y
    rw [hA_def]
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [← real_inner_comm (volumeResponseOperator S (expPotentialCoefficient h) x) y,
      ← real_inner_comm (volumeResponseOperator S (expPotentialCoefficient g) x) y, h1, h2]
  have hCnn : 0 ≤ (Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖ :=
    mul_nonneg (by have := Real.one_le_exp (norm_nonneg (h - g)); linarith) (norm_nonneg _)
  have hbound : ∀ x y : DomainL2 Ω, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (A y)| ≤ 2 * ((Real.exp ‖h - g‖ - 1) *
        ‖volumeResponseOperator S (expPotentialCoefficient g)‖) := by
    intro x y hx hy
    have hpol := SubdiffusiveProcess.Probability.aux_polarization A hsymA x y
    have hq1 := volumeResponseOperator_sub_quadratic_le S g h (x + y)
    have hq2 := volumeResponseOperator_sub_quadratic_le S g h (x - y)
    rw [← hA_def] at hq1 hq2
    have hnorm1 : ‖x + y‖ ^ 2 ≤ 4 := by
      nlinarith [norm_add_le x y, hx, hy, norm_nonneg (x + y)]
    have hnorm2 : ‖x - y‖ ^ 2 ≤ 4 := by
      nlinarith [norm_sub_le x y, hx, hy, norm_nonneg (x - y)]
    have hb1 : |inner ℝ (x + y) (A (x + y))| ≤
        ((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4 :=
      hq1.trans (mul_le_mul_of_nonneg_left hnorm1 hCnn)
    have hb2 : |inner ℝ (x - y) (A (x - y))| ≤
        ((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4 :=
      hq2.trans (mul_le_mul_of_nonneg_left hnorm2 hCnn)
    have htri : |inner ℝ (x + y) (A (x + y)) - inner ℝ (x - y) (A (x - y))| ≤
        ((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4 +
          ((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4 :=
      (abs_sub _ _).trans (add_le_add hb1 hb2)
    calc |inner ℝ x (A y)|
        = |4 * inner ℝ x (A y)| / 4 := by
          rw [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
          ring
      _ = |inner ℝ (x + y) (A (x + y)) - inner ℝ (x - y) (A (x - y))| / 4 := by rw [hpol]
      _ ≤ (((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4 +
            ((Real.exp ‖h - g‖ - 1) * ‖volumeResponseOperator S (expPotentialCoefficient g)‖) * 4) / 4 :=
          div_le_div_of_nonneg_right htri (by norm_num)
      _ = 2 * ((Real.exp ‖h - g‖ - 1) *
            ‖volumeResponseOperator S (expPotentialCoefficient g)‖) := by ring
  have hMnn : 0 ≤ 2 * ((Real.exp ‖h - g‖ - 1) *
      ‖volumeResponseOperator S (expPotentialCoefficient g)‖) := mul_nonneg (by norm_num) hCnn
  have hmain : ‖A‖ ≤ 2 * ((Real.exp ‖h - g‖ - 1) *
      ‖volumeResponseOperator S (expPotentialCoefficient g)‖) :=
    SubdiffusiveProcess.Probability.aux_opNorm_le_of_inner hMnn hbound
  rw [hA_def] at hmain
  simpa only [mul_assoc] using hmain

/-- **Continuity of the volume-response operator in the `L∞` potential.** -/
theorem continuousAt_volumeResponseOperator_expPotentialCoefficient (S : ResponseSpace Ω)
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ContinuousAt (fun h => volumeResponseOperator S (expPotentialCoefficient h)) g := by
  have hbound_tendsto : Tendsto (fun h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      2 * (Real.exp ‖h - g‖ - 1) *
        ‖volumeResponseOperator S (expPotentialCoefficient g)‖) (𝓝 g) (𝓝 0) := by
    have hc : Continuous (fun h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
        2 * (Real.exp ‖h - g‖ - 1) *
          ‖volumeResponseOperator S (expPotentialCoefficient g)‖) := by
      fun_prop
    simpa only [sub_self, norm_zero, Real.exp_zero, mul_zero, zero_mul] using hc.tendsto g
  have hsub : Tendsto (fun h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      volumeResponseOperator S (expPotentialCoefficient h) -
        volumeResponseOperator S (expPotentialCoefficient g)) (𝓝 g) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun h => 2 * (Real.exp ‖h - g‖ - 1) *
        ‖volumeResponseOperator S (expPotentialCoefficient g)‖)
      (Filter.Eventually.of_forall fun h => ?_) hbound_tendsto
    exact volumeResponseOperator_sub_norm_le S g h
  exact tendsto_sub_nhds_zero_iff.1 hsub

/-- **Continuity of the volume-response operator in the `L∞` potential** (all parameters). -/
theorem continuous_volumeResponseOperator_expPotentialCoefficient (S : ResponseSpace Ω) :
    Continuous (fun g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      volumeResponseOperator S (expPotentialCoefficient g)) :=
  continuous_iff_continuousAt.mpr fun g =>
    continuousAt_volumeResponseOperator_expPotentialCoefficient S g

/-- **Borel measurability.**  For the Borel σ-algebras on the parameter space and on the
(possibly non-separable) operator space `DomainL2 Ω →L[ℝ] DomainL2 Ω`, the map
`g ↦ volumeResponseOperator S (expPotentialCoefficient g)` is measurable.  The explicit `borel`
instances avoid any typeclass assumption on the ambient σ-algebra of the operator space. -/
theorem borel_measurable_volumeResponseOperator_expPotentialCoefficient (S : ResponseSpace Ω) :
    @Measurable (Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
      (DomainL2 Ω →L[ℝ] DomainL2 Ω) (borel _) (borel _)
      (fun g => volumeResponseOperator S (expPotentialCoefficient g)) :=
  (continuous_volumeResponseOperator_expPotentialCoefficient S).borel_measurable

end SubdiffusiveProcess
