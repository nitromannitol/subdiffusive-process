import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannRecenteringComposition
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepTranslatedNeumannMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDescendantHessianMoments

/-!
# Two-radius fourth-moment fold for Neumann cells

The interior Neumann field used in the lower one-step argument is compared
twice.  First the finite-volume Neumann solution is recentered on a larger
interior parent.  The stationary Neumann solution on that parent is then
compared with its stationary Dirichlet solution.  Thus the literal cell
Hessian has three pieces:

```
  B_large-Neumann <= B_local-Dirichlet + B_local-harmonic + B_outer-harmonic.
```

This module performs the fourth-moment fold and the two successive
arbitrary-gap limits.  It follows the finite-family split pattern in
`Algsuperdiff/Section3/Provider/Diffusivity/ApproximateRecurrence/Closure/
SplitFoldCellMoments.lean`; the second harmonic radius is the GMC-specific
Neumann-to-Dirichlet replacement.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Fourth-power loss for a three-piece nonnegative decomposition. -/
theorem add_add_four_le_sixtyFour_sum
    {D H₁ H₂ : ℝ} (hD : 0 ≤ D) (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) :
    (D + H₁ + H₂) ^ (4 : ℕ) ≤
      64 * D ^ (4 : ℕ) +
        64 * H₁ ^ (4 : ℕ) + 64 * H₂ ^ (4 : ℕ) := by
  have hfirst := add_four_le_eight_sum_four (add_nonneg hD hH₁) hH₂
  have hsecond := add_four_le_eight_sum_four hD hH₁
  calc
    (D + H₁ + H₂) ^ (4 : ℕ) ≤
        8 * ((D + H₁) ^ (4 : ℕ) + H₂ ^ (4 : ℕ)) := hfirst
    _ ≤ 8 * (8 * (D ^ (4 : ℕ) + H₁ ^ (4 : ℕ)) +
        H₂ ^ (4 : ℕ)) := by gcongr
    _ = 64 * D ^ (4 : ℕ) +
        64 * H₁ ^ (4 : ℕ) + 8 * H₂ ^ (4 : ℕ) := by ring
    _ ≤ 64 * D ^ (4 : ℕ) +
        64 * H₁ ^ (4 : ℕ) + 64 * H₂ ^ (4 : ℕ) := by
      have hpow : 0 ≤ H₂ ^ (4 : ℕ) := pow_nonneg hH₂ _
      nlinarith

/-- `ENNReal.ofReal` version of the pointwise two-radius split. -/
theorem ofReal_pow_four_le_of_le_three_piece
    {N D H₁ H₂ : ℝ}
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂)
    (hsplit : N ≤ D + H₁ + H₂) :
    ENNReal.ofReal (N ^ (4 : ℕ)) ≤
      64 * ENNReal.ofReal (D ^ (4 : ℕ)) +
        64 * ENNReal.ofReal (H₁ ^ (4 : ℕ)) +
          64 * ENNReal.ofReal (H₂ ^ (4 : ℕ)) := by
  have hpow : N ^ (4 : ℕ) ≤ (D + H₁ + H₂) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hN hsplit 4
  refine (ENNReal.ofReal_le_ofReal
    (hpow.trans (add_add_four_le_sixtyFour_sum hD hH₁ hH₂))).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
  norm_num

/-- The measurable finite-cell two-radius family.  Its fields are exactly
the four observables entering the Neumann replacement; no independence or
stationarity is hidden in the carrier. -/
structure OneStepTwoRadiusNeumannCellFamily
    (ι Omega : Type*) [MeasurableSpace Omega] (s : Finset ι) where
  neumann : ι → Omega → ℝ
  dirichlet : ι → Omega → ℝ
  localHarmonic : ι → Omega → ℝ
  outerHarmonic : ι → Omega → ℝ
  measurable_neumann : ∀ i ∈ s, Measurable (neumann i)
  measurable_dirichlet : ∀ i ∈ s, Measurable (dirichlet i)
  measurable_localHarmonic : ∀ i ∈ s, Measurable (localHarmonic i)
  measurable_outerHarmonic : ∀ i ∈ s, Measurable (outerHarmonic i)
  neumann_nonneg : ∀ i ∈ s, ∀ omega, 0 ≤ neumann i omega
  dirichlet_nonneg : ∀ i ∈ s, ∀ omega, 0 ≤ dirichlet i omega
  localHarmonic_nonneg : ∀ i ∈ s, ∀ omega, 0 ≤ localHarmonic i omega
  outerHarmonic_nonneg : ∀ i ∈ s, ∀ omega, 0 ≤ outerHarmonic i omega
  split : ∀ i ∈ s, ∀ omega,
    neumann i omega ≤ dirichlet i omega +
      localHarmonic i omega + outerHarmonic i omega

/-- Weak-Hessian witness for a three-piece gradient decomposition. -/
noncomputable def weakHessianOfGradEqAddAdd
    {d : ℕ} {U : Set (Vec d)}
    {u v w₁ w₂ : H1Function U}
    (hgrad : u.grad = fun x => v.grad x + (w₁.grad x + w₂.grad x))
    (Hv : HasWeakHessianOn U v)
    (Hw₁ : HasWeakHessianOn U w₁)
    (Hw₂ : HasWeakHessianOn U w₂) :
    HasWeakHessianOn U u := by
  let w : H1Function U := w₁ + w₂
  let Hw : HasWeakHessianOn U w := weakHessianAdd Hw₁ Hw₂
  have hgrad' : u.grad = fun x => v.grad x + w.grad x := by
    simpa only [w, H1Function.add_grad, Pi.add_apply] using hgrad
  exact weakHessianOfGradEqAdd hgrad' Hv Hw

/-- Literal `B` bound carried by `weakHessianOfGradEqAddAdd`. -/
theorem oneStepCellB_le_of_grad_eq_add_add
    {d : ℕ} (R : TriadicCube d)
    {u v w₁ w₂ : H1Function (openCubeSet R)}
    (hgrad : u.grad = fun x => v.grad x + (w₁.grad x + w₂.grad x))
    (Hv : HasWeakHessianOn (openCubeSet R) v)
    (Hw₁ : HasWeakHessianOn (openCubeSet R) w₁)
    (Hw₂ : HasWeakHessianOn (openCubeSet R) w₂) :
    oneStepCellB R (weakHessianOfGradEqAddAdd hgrad Hv Hw₁ Hw₂) ≤
      oneStepCellB R Hv + oneStepCellB R Hw₁ + oneStepCellB R Hw₂ := by
  let w : H1Function (openCubeSet R) := w₁ + w₂
  let Hw : HasWeakHessianOn (openCubeSet R) w := weakHessianAdd Hw₁ Hw₂
  have hgrad' : u.grad = fun x => v.grad x + w.grad x := by
    simpa only [w, H1Function.add_grad, Pi.add_apply] using hgrad
  calc
    oneStepCellB R (weakHessianOfGradEqAddAdd hgrad Hv Hw₁ Hw₂) ≤
        oneStepCellB R Hv + oneStepCellB R Hw := by
      simpa only [weakHessianOfGradEqAddAdd, Hw, w] using
        oneStepCellB_le_of_grad_eq_add R hgrad' Hv Hw
    _ ≤ oneStepCellB R Hv +
        (oneStepCellB R Hw₁ + oneStepCellB R Hw₂) := by
      gcongr
      exact oneStepCellB_add_le R Hw₁ Hw₂
    _ = _ := by ring

/-- A dependent weak-Hessian realization of the two-radius cell family.
The four functions all live on the same literal triadic cell, and the large
Neumann gradient is the sum of the persistent Dirichlet gradient and the two
harmonic corrections. -/
structure OneStepTwoRadiusNeumannHessianFamily
    (d : ℕ) (ι Omega : Type*) [MeasurableSpace Omega]
    (s : Finset ι) (cell : ι → TriadicCube d) where
  neumann : ∀ i, Omega → H1Function (openCubeSet (cell i))
  dirichlet : ∀ i, Omega → H1Function (openCubeSet (cell i))
  localHarmonic : ∀ i, Omega → H1Function (openCubeSet (cell i))
  outerHarmonic : ∀ i, Omega → H1Function (openCubeSet (cell i))
  grad_split : ∀ i omega,
    (neumann i omega).grad = fun x =>
      (dirichlet i omega).grad x +
        ((localHarmonic i omega).grad x + (outerHarmonic i omega).grad x)
  dirichletHessian : ∀ i omega,
    HasWeakHessianOn (openCubeSet (cell i)) (dirichlet i omega)
  localHarmonicHessian : ∀ i omega,
    HasWeakHessianOn (openCubeSet (cell i)) (localHarmonic i omega)
  outerHarmonicHessian : ∀ i omega,
    HasWeakHessianOn (openCubeSet (cell i)) (outerHarmonic i omega)
  measurable_neumann_grad : ∀ i ∈ s,
    Measurable fun omega => (neumann i omega).gradToHilbertVectorL2
  measurable_dirichlet_grad : ∀ i ∈ s,
    Measurable fun omega => (dirichlet i omega).gradToHilbertVectorL2
  measurable_localHarmonic_grad : ∀ i ∈ s,
    Measurable fun omega => (localHarmonic i omega).gradToHilbertVectorL2
  measurable_outerHarmonic_grad : ∀ i ∈ s,
    Measurable fun omega => (outerHarmonic i omega).gradToHilbertVectorL2

/-- Forget the Sobolev carriers of a two-radius realization and retain its
four measurable literal `B` observables. -/
noncomputable def OneStepTwoRadiusNeumannHessianFamily.toCellFamily
    {d : ℕ} {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell) :
    OneStepTwoRadiusNeumannCellFamily ι Omega s := by
  let HN : ∀ i, ∀ omega,
      HasWeakHessianOn (openCubeSet (cell i)) (F.neumann i omega) :=
    fun i omega => weakHessianOfGradEqAddAdd (F.grad_split i omega)
      (F.dirichletHessian i omega)
      (F.localHarmonicHessian i omega)
      (F.outerHarmonicHessian i omega)
  let BN : ι → Omega → ℝ := fun i omega => oneStepCellB (cell i) (HN i omega)
  let BD : ι → Omega → ℝ := fun i omega =>
    oneStepCellB (cell i) (F.dirichletHessian i omega)
  let BH₁ : ι → Omega → ℝ := fun i omega =>
    oneStepCellB (cell i) (F.localHarmonicHessian i omega)
  let BH₂ : ι → Omega → ℝ := fun i omega =>
    oneStepCellB (cell i) (F.outerHarmonicHessian i omega)
  refine
    { neumann := BN
      dirichlet := BD
      localHarmonic := BH₁
      outerHarmonic := BH₂
      measurable_neumann := ?_
      measurable_dirichlet := ?_
      measurable_localHarmonic := ?_
      measurable_outerHarmonic := ?_
      neumann_nonneg := ?_
      dirichlet_nonneg := ?_
      localHarmonic_nonneg := ?_
      outerHarmonic_nonneg := ?_
      split := ?_ }
  · intro i hi
    exact measurable_oneStepCellB (cell i) (F.neumann i) (HN i)
      (F.measurable_neumann_grad i hi)
  · intro i hi
    exact measurable_oneStepCellB (cell i) (F.dirichlet i)
      (F.dirichletHessian i) (F.measurable_dirichlet_grad i hi)
  · intro i hi
    exact measurable_oneStepCellB (cell i) (F.localHarmonic i)
      (F.localHarmonicHessian i) (F.measurable_localHarmonic_grad i hi)
  · intro i hi
    exact measurable_oneStepCellB (cell i) (F.outerHarmonic i)
      (F.outerHarmonicHessian i) (F.measurable_outerHarmonic_grad i hi)
  · intro i _hi omega
    unfold BN oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · intro i _hi omega
    unfold BD oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · intro i _hi omega
    unfold BH₁ oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · intro i _hi omega
    unfold BH₂ oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · intro i hi omega
    dsimp only [BN, BD, BH₁, BH₂]
    simpa only [HN] using
      oneStepCellB_le_of_grad_eq_add_add (cell i) (F.grad_split i omega)
        (F.dirichletHessian i omega)
        (F.localHarmonicHessian i omega)
        (F.outerHarmonicHessian i omega)

/-- The finite-family fourth moment of the Neumann field is bounded by the
persistent Dirichlet payload and the two harmonic payloads. -/
theorem lintegral_twoRadiusNeumann_four_le
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι)
    (F : OneStepTwoRadiusNeumannCellFamily ι Omega s) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F.neumann i omega ^ (4 : ℕ))) ∂mu ≤
      64 * ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.dirichlet i omega ^ (4 : ℕ))) ∂mu +
        64 * ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.localHarmonic i omega ^ (4 : ℕ))) ∂mu +
        64 * ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.outerHarmonic i omega ^ (4 : ℕ))) ∂mu := by
  let D : Omega → ℝ≥0∞ := fun omega =>
    ((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, ENNReal.ofReal (F.dirichlet i omega ^ (4 : ℕ))
  let H₁ : Omega → ℝ≥0∞ := fun omega =>
    ((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, ENNReal.ofReal (F.localHarmonic i omega ^ (4 : ℕ))
  let H₂ : Omega → ℝ≥0∞ := fun omega =>
    ((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, ENNReal.ofReal (F.outerHarmonic i omega ^ (4 : ℕ))
  have hDmeas : Measurable D := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact (F.measurable_dirichlet i hi).pow_const 4 |>.ennreal_ofReal
  have hH₁meas : Measurable H₁ := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact (F.measurable_localHarmonic i hi).pow_const 4 |>.ennreal_ofReal
  have hH₂meas : Measurable H₂ := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact (F.measurable_outerHarmonic i hi).pow_const 4 |>.ennreal_ofReal
  have hpoint : ∀ omega,
      ((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.neumann i omega ^ (4 : ℕ)) ≤
        64 * D omega + 64 * H₁ omega + 64 * H₂ omega := by
    intro omega
    calc
      _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s,
          (64 * ENNReal.ofReal (F.dirichlet i omega ^ (4 : ℕ)) +
            64 * ENNReal.ofReal (F.localHarmonic i omega ^ (4 : ℕ)) +
            64 * ENNReal.ofReal (F.outerHarmonic i omega ^ (4 : ℕ))) := by
        gcongr with i hi
        exact ofReal_pow_four_le_of_le_three_piece
          (F.neumann_nonneg i hi omega) (F.dirichlet_nonneg i hi omega)
          (F.localHarmonic_nonneg i hi omega)
          (F.outerHarmonic_nonneg i hi omega) (F.split i hi omega)
      _ = 64 * D omega + 64 * H₁ omega + 64 * H₂ omega := by
        dsimp only [D, H₁, H₂]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  calc
    _ ≤ ∫⁻ omega, 64 * D omega + 64 * H₁ omega + 64 * H₂ omega ∂mu :=
      lintegral_mono hpoint
    _ = 64 * ∫⁻ omega, D omega ∂mu +
        64 * ∫⁻ omega, H₁ omega ∂mu +
          64 * ∫⁻ omega, H₂ omega ∂mu := by
      rw [lintegral_add_left
          (f := fun omega => 64 * D omega + 64 * H₁ omega)
          (g := fun omega => 64 * H₂ omega),
        lintegral_add_left (f := fun omega => 64 * D omega)
          (g := fun omega => 64 * H₁ omega),
        lintegral_const_mul' _ _ (by norm_num : (64 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (64 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (64 : ℝ≥0∞) ≠ ∞)]
      all_goals fun_prop
    _ = _ := rfl

/-- Insert separate fourth-moment budgets into the finite two-radius fold. -/
theorem lintegral_twoRadiusNeumann_four_le_of_budgets
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι)
    (F : OneStepTwoRadiusNeumannCellFamily ι Omega s)
    {D H₁ H₂ : ℝ≥0∞}
    (hD : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F.dirichlet i omega ^ (4 : ℕ))) ∂mu ≤ D)
    (hH₁ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F.localHarmonic i omega ^ (4 : ℕ))) ∂mu ≤ H₁)
    (hH₂ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F.outerHarmonic i omega ^ (4 : ℕ))) ∂mu ≤ H₂) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal (F.neumann i omega ^ (4 : ℕ))) ∂mu ≤
      64 * D + 64 * H₁ + 64 * H₂ := by
  calc
    _ ≤ 64 * (∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.dirichlet i omega ^ (4 : ℕ))) ∂mu) +
        64 * (∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.localHarmonic i omega ^ (4 : ℕ))) ∂mu) +
        64 * (∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
          ∑ i ∈ s, ENNReal.ofReal (F.outerHarmonic i omega ^ (4 : ℕ))) ∂mu) :=
      lintegral_twoRadiusNeumann_four_le s F
    _ ≤ 64 * D + 64 * H₁ + 64 * H₂ := by gcongr

/-- Both arbitrary-radius corrections may be removed successively. -/
theorem ennreal_le_of_forall_le_add_two_one_third_pow_four
    {X D C₁ C₂ : ℝ≥0∞} (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hbound : ∀ N₁ N₂ : ℕ,
      X ≤ D + C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ) +
        C₂ * (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ)) :
    X ≤ D := by
  have hfirst : ∀ N₁ : ℕ,
      X ≤ D + C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ) := by
    intro N₁
    apply ennreal_le_of_forall_le_add_one_third_pow_four hC₂
    intro N₂
    simpa only [add_assoc] using hbound N₁ N₂
  exact ennreal_le_of_forall_le_add_one_third_pow_four hC₁ hfirst

/-- Source-scale close for a two-radius family.  Once the Dirichlet fourth
moment is `C_D delta^68` and both harmonic bounds carry arbitrary geometric
gaps, the Neumann family has the same `delta^68` scale. -/
theorem twoRadiusNeumann_four_le_delta_sixtyEight
    {X delta CD C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hbound : ∀ N₁ N₂ : ℕ,
      X ≤ 64 * (CD * delta ^ (68 : ℕ)) +
        64 * (C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ)) +
        64 * (C₂ * (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ))) :
    X ≤ (64 * CD) * delta ^ (68 : ℕ) := by
  apply ennreal_le_of_forall_le_add_two_one_third_pow_four
    (C₁ := 64 * C₁) (C₂ := 64 * C₂)
  · exact ENNReal.mul_ne_top (by norm_num) hC₁
  · exact ENNReal.mul_ne_top (by norm_num) hC₂
  · intro N₁ N₂
    simpa only [mul_assoc, add_assoc] using hbound N₁ N₂

/-- Thermodynamic two-radius aggregation.  The observable on the left is
independent of the auxiliary radii; each pair of radii supplies a measurable
finite-cell realization with the same readout, a persistent Dirichlet
budget, and two vanishing harmonic budgets. -/
theorem twoRadiusNeumann_family_lintegral_le_delta_sixtyEight
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι)
    (F : ℕ → ℕ → OneStepTwoRadiusNeumannCellFamily ι Omega s)
    {X delta CD C₁ C₂ : ℝ≥0∞}
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (hreadout : ∀ N₁ N₂,
      X = ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F N₁ N₂).neumann i omega ^ (4 : ℕ))) ∂mu)
    (hD : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F N₁ N₂).dirichlet i omega ^ (4 : ℕ))) ∂mu ≤
        CD * delta ^ (68 : ℕ))
    (hH₁ : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F N₁ N₂).localHarmonic i omega ^ (4 : ℕ))) ∂mu ≤
        C₁ * (((3 : ℝ≥0∞)⁻¹) ^ N₁) ^ (4 : ℕ))
    (hH₂ : ∀ N₁ N₂,
      ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F N₁ N₂).outerHarmonic i omega ^ (4 : ℕ))) ∂mu ≤
        C₂ * (((3 : ℝ≥0∞)⁻¹) ^ N₂) ^ (4 : ℕ)) :
    X ≤ (64 * CD) * delta ^ (68 : ℕ) := by
  apply twoRadiusNeumann_four_le_delta_sixtyEight hC₁ hC₂
  intro N₁ N₂
  rw [hreadout N₁ N₂]
  exact lintegral_twoRadiusNeumann_four_le_of_budgets s (F N₁ N₂)
    (hD N₁ N₂) (hH₁ N₁ N₂) (hH₂ N₁ N₂)

/-! ## The persistent source-cell member -/

/-- The source-depth Dirichlet theorem, specialized to a single origin cell.
This is the persistent member of the two-radius Neumann family; stationarity
subsequently transports it to every retained cell. -/
theorem exists_measurable_oneStepDirichlet_originCellB_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (p : Vec d) (_hp : vecNormSq p = 1)
        (_hh : 0 < h) (_hscale : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n),
        ∃ B : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
          Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
            ∫⁻ omega, ENNReal.ofReal (B omega ^ (4 : ℕ))
                ∂M.P.toMeasure ≤
              C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  obtain ⟨C, hCtop, hsource⟩ :=
    exists_lintegral_oneStepDirichlet_descendantCellB_source_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p hp hh hscale hsourceScale
  let K : ℕ := oneStepLocalizationScale n M.delta
  obtain ⟨uD, V, hV, huD, hBmeas, hbudget⟩ :=
    hsource M n h K p hp hh hscale hsourceScale le_rfl
  let H : ∀ omega,
      HasWeakHessianOn (openCubeSet (originCube d K))
        (uD omega).toH1Function := fun omega =>
    weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
  let B : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    oneStepCellB (originCube d K) (H omega)
  refine ⟨B, ?_, ?_, ?_⟩
  · simpa only [B, H] using hBmeas
  · intro omega
    unfold B oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · convert hbudget using 1
    apply lintegral_congr
    intro omega
    simp only [K, Nat.sub_self, descendantsAtDepth_zero,
      descendantsAverage, Finset.card_singleton, Nat.cast_one, inv_one,
      Finset.sum_singleton, Finset.mem_singleton, one_mul, B, H]
    congr 2

/-- Stationarity transports the persistent origin-cell `B` observable to
any nonempty finite family of translated source cells without changing its
normalized fourth moment. -/
theorem lintegral_average_comp_translatePotentialSequence_four_eq
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (center : ι → Vec d) (s : Finset ι) (hs : s.Nonempty)
    (B : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ)
    (hB : Measurable B) :
    ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          (B (translatePotentialSequence (center i) omega) ^ (4 : ℕ)))
        ∂M.P.toMeasure =
      ∫⁻ omega, ENNReal.ofReal (B omega ^ (4 : ℕ)) ∂M.P.toMeasure := by
  let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal (B omega ^ (4 : ℕ))
  have hF : Measurable F := (hB.pow_const 4).ennreal_ofReal
  have hcell : ∀ i : ι,
      ∫⁻ omega, F (translatePotentialSequence (center i) omega)
          ∂M.P.toMeasure = ∫⁻ omega, F omega ∂M.P.toMeasure := by
    intro i
    exact (measurePreserving_translatePotentialSequence M (center i)).lintegral_comp hF
  calc
    _ = ((s.card : ℝ≥0∞)⁻¹) * ∑ i ∈ s,
        ∫⁻ omega, F (translatePotentialSequence (center i) omega)
          ∂M.P.toMeasure := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finset_sum]
      intro i _hi
      exact hF.comp (measurable_translatePotentialSequence (center i))
    _ = ((s.card : ℝ≥0∞)⁻¹) * ∑ _i ∈ s,
        ∫⁻ omega, F omega ∂M.P.toMeasure := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcell i
    _ = ∫⁻ omega, F omega ∂M.P.toMeasure := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
      have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast hs.card_ne_zero
      have hcardTop : (s.card : ℝ≥0∞) ≠ ∞ := by finiteness
      rw [ENNReal.inv_mul_cancel hcard0 hcardTop, one_mul]
    _ = _ := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
