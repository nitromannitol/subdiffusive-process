module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineCoupledAbsorption

@[expose] public section

/-!
# Three-step residual absorption

The corrected-flux engine naturally produces a one-half recurrence.  The
affine/residual energy transfer needs one eighth.  This file records the
honest constant walk: three consecutive half-steps give one eighth, with the
three local remainders carrying weights `1`, `1 / 2`, and `1 / 4`.

The manuscript invokes the boundary Caccioppoli estimate as an external
input and does not prescribe an internal iteration count.  This grouped
calculation is therefore an implementation lemma, not an additional source
hypothesis.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Asymmetric Young split used on the inner physical profile. -/
theorem vecNormSq_add_le_fourThirds_add_four (x y : Vec d) :
    vecNormSq (x + y) ≤
      (4 / 3 : ℝ) * vecNormSq x + 4 * vecNormSq y := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hs : 0 ≤ (x i - 3 * y i) ^ 2 := sq_nonneg _
  simp only [Pi.add_apply]
  nlinarith only [hs]

/-- Asymmetric Young split used to read the outer residual profile through
the physical solution. -/
theorem vecNormSq_sub_le_threeHalves_add_three (x y : Vec d) :
    vecNormSq (x - y) ≤
      (3 / 2 : ℝ) * vecNormSq x + 3 * vecNormSq y := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hs : 0 ≤ (x i + 2 * y i) ^ 2 := sq_nonneg _
  simp only [Pi.sub_apply]
  nlinarith only [hs]

private theorem boundaryCrossScaleEnergyProfile_aCutoff_le_weighted_split
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho c₁ c₂ : ℝ)
    (u u₁ u₂ : H1Function (openCubeSet Q))
    (hc₂ : 0 ≤ c₂)
    (hsplit : ∀ x, vecNormSq (u.grad x) ≤
      c₁ * vecNormSq (u₁.grad x) + c₂ * vecNormSq (u₂.grad x)) :
    boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      c₁ * boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u₁.grad x)) +
      c₂ * localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u₂ := by
  let patch := coarseCaccioppoliLocalClosedCube R center rho
  let e : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let e₁ : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u₁.grad x)
  let e₂ : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u₂.grad x)
  have he : MeasureTheory.IntegrableOn e (openCubeSet Q) := by
    simpa only [e] using integrableOn_aCutoff_energy M L omega Q u
  have he₁ : MeasureTheory.IntegrableOn e₁ (openCubeSet Q) := by
    simpa only [e₁] using integrableOn_aCutoff_energy M L omega Q u₁
  have he₂ : MeasureTheory.IntegrableOn e₂ (openCubeSet Q) := by
    simpa only [e₂] using integrableOn_aCutoff_energy M L omega Q u₂
  have hpoint : ∀ x ∈ openCubeSet Q,
      patch.indicator e x ≤
        c₁ * patch.indicator e₁ x + c₂ * e₂ x := by
    intro x hx
    by_cases hxp : x ∈ patch
    · simp only [Set.indicator_of_mem hxp, e, e₁, e₂]
      have hm := mul_le_mul_of_nonneg_left (hsplit x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      nlinarith only [hm]
    · simp only [Set.indicator_of_notMem hxp, mul_zero, zero_add]
      exact mul_nonneg hc₂
        (mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
          (vecNormSq_nonneg _))
  have hmono : volumeAverage (openCubeSet Q) (patch.indicator e) ≤
      volumeAverage (openCubeSet Q) (fun x ↦
        c₁ * patch.indicator e₁ x + c₂ * e₂ x) := by
    apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    · exact he.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)
    · exact ((he₁.indicator
          (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)).const_mul c₁)
        |>.add (he₂.const_mul c₂)
    · exact hpoint
  have hsplitAverage : volumeAverage (openCubeSet Q) (fun x ↦
      c₁ * patch.indicator e₁ x + c₂ * e₂ x) =
      c₁ * volumeAverage (openCubeSet Q) (patch.indicator e₁) +
        c₂ * volumeAverage (openCubeSet Q) e₂ := by
    unfold volumeAverage
    rw [integral_add, integral_const_mul, integral_const_mul]
    · ring
    · exact (he₁.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)).const_mul c₁
    · exact he₂.const_mul c₂
  have he₂Eq : volumeAverage (openCubeSet Q) e₂ =
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u₂ := by
    rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) u₂]
    apply volumeAverage_eq_of_ae_eq
    filter_upwards
        [publicCoeffField_ae_eq_openCubeSet Q (aCutoffFamily M L omega)] with x hx
    simp only [e₂, coefficientEnergyDensity, hx]
    simp [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecNormSq]
  unfold boundaryCrossScaleEnergyProfile
  dsimp only [patch, e, e₁] at hmono hsplitAverage
  rw [hsplitAverage, he₂Eq] at hmono
  exact hmono

/-- Inner asymmetric physical/residual split. -/
theorem boundaryCrossScaleEnergyProfile_aCutoff_le_fourThirds_residual_add_four_affine
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x) :
    boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (4 / 3 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) +
        4 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v := by
  apply boundaryCrossScaleEnergyProfile_aCutoff_le_weighted_split
    M L omega Q R center rho (4 / 3) 4 u uRes v (by norm_num)
  intro x
  rw [hgrad x]
  exact vecNormSq_add_le_fourThirds_add_four _ _

/-- Outer asymmetric residual/physical split. -/
theorem boundaryCrossScaleEnergyProfile_aCutoff_residual_le_threeHalves_physical_add_three_affine
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, uRes.grad x = u.grad x - v.grad x) :
    boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (uRes.grad x)) ≤
      (3 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
        3 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v := by
  apply boundaryCrossScaleEnergyProfile_aCutoff_le_weighted_split
    M L omega Q R center rho (3 / 2) 3 uRes u v (by norm_num)
  intro x
  rw [hgrad x]
  exact vecNormSq_sub_le_threeHalves_add_three _ _

/-- Scalar constant walk showing that a residual quarter-step suffices after
the asymmetric energy splits. -/
theorem affineResidual_quarter_to_physical_half
    {Einner Eouter EinnerRes EouterRes Ev B : ℝ}
    (hinner : Einner ≤ (4 / 3 : ℝ) * EinnerRes + 4 * Ev)
    (hres : EinnerRes ≤ (1 / 4 : ℝ) * EouterRes + B)
    (houter : EouterRes ≤ (3 / 2 : ℝ) * Eouter + 3 * Ev) :
    Einner ≤ (1 / 2 : ℝ) * Eouter + 5 * Ev + (4 / 3 : ℝ) * B := by
  linarith only [hinner, hres, houter]

/-- A residual quarter-step becomes the physical half-step required by the
standard radius iteration.  This is the sharpened-Young alternative to the
one-eighth transfer in `BoundaryAffineCoupledAbsorption`. -/
theorem boundaryCrossScaleEnergyProfile_physical_half_of_affineResidual_quarter
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter B : ℝ}
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    (hres :
      boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 4 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
        5 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v + (4 / 3 : ℝ) * B := by
  have hinner :=
    boundaryCrossScaleEnergyProfile_aCutoff_le_fourThirds_residual_add_four_affine
      M L omega Q R center rhoInner u uRes v hgrad
  have hgradReverse : ∀ x, uRes.grad x = u.grad x - v.grad x := by
    intro x
    rw [hgrad x]
    abel_nf
  have houter :=
    boundaryCrossScaleEnergyProfile_aCutoff_residual_le_threeHalves_physical_add_three_affine
      M L omega Q R center rhoOuter u uRes v hgradReverse
  exact affineResidual_quarter_to_physical_half hinner hres houter

/-- Two corrected-flux half-steps across an arbitrary intermediate radius,
followed by the asymmetric affine transfer.  Choosing the midpoint keeps both
subgaps comparable to the original consecutive-radius gap. -/
theorem boundaryCrossScaleEnergyProfile_physical_half_of_two_residual_half_steps
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d)
    {rhoInner rhoMid rhoOuter B₁ B₂ : ℝ}
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    (hleft :
      boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoMid (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₁)
    (hright :
      boundaryCrossScaleEnergyProfile Q R center rhoMid (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₂) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
        5 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v +
        (4 / 3 : ℝ) * (B₁ + (1 / 2 : ℝ) * B₂) := by
  have hquarter :
      boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 4 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) +
          (B₁ + (1 / 2 : ℝ) * B₂) := by
    linarith only [hleft, hright]
  exact boundaryCrossScaleEnergyProfile_physical_half_of_affineResidual_quarter
    M L omega Q R center u uRes v hgrad hquarter

/-- Three corrected-flux half-steps on the actual residual energy profile,
followed by the coupled affine/residual transfer.  This is the carrier-level
form of the literal `1 / 8` calculation: unlike
`residual_eighth_of_three_half_steps`, it already concludes with the physical
solution and hence can be wired directly into the harmonic-approximation
provider. -/
theorem boundaryCrossScaleEnergyProfile_physical_half_of_three_residual_half_steps
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d)
    {rho₀ rho₁ rho₂ rho₃ B₀ B₁ B₂ : ℝ}
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    (h₀ :
      boundaryCrossScaleEnergyProfile Q R center rho₀ (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho₁ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₀)
    (h₁ :
      boundaryCrossScaleEnergyProfile Q R center rho₁ (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho₂ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₁)
    (h₂ :
      boundaryCrossScaleEnergyProfile Q R center rho₂ (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho₃ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₂) :
    boundaryCrossScaleEnergyProfile Q R center rho₀ (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho₃ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v +
        2 * (B₀ + (1 / 2 : ℝ) * B₁ + (1 / 4 : ℝ) * B₂) := by
  have heighth :
      boundaryCrossScaleEnergyProfile Q R center rho₀ (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 8 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rho₃ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) +
          (B₀ + (1 / 2 : ℝ) * B₁ + (1 / 4 : ℝ) * B₂) := by
    nlinarith only [h₀, h₁, h₂]
  exact boundaryCrossScaleEnergyProfile_physical_half_of_affineResidual_eighth
    M L omega Q R center u uRes v hgrad heighth

/-- Three consecutive one-half recurrences produce the residual one-eighth
step required by the coupled affine-energy transfer. -/
theorem residual_eighth_of_three_half_steps
    {F B : ℕ → ℝ}
    (hhalf : ∀ j : ℕ, F j ≤ (1 / 2 : ℝ) * F (j + 1) + B j)
    (j : ℕ) :
    F j ≤ (1 / 8 : ℝ) * F (j + 3) +
      B j + (1 / 2 : ℝ) * B (j + 1) + (1 / 4 : ℝ) * B (j + 2) := by
  have h₀ := hhalf j
  have h₁ := hhalf (j + 1)
  have h₂ := hhalf (j + 2)
  nlinarith only [h₀, h₁, h₂]

/-- Two consecutive half-steps give the quarter-step consumed by the
asymmetric affine transfer below. -/
theorem residual_quarter_of_two_half_steps
    {F B : ℕ → ℝ}
    (hhalf : ∀ j : ℕ, F j ≤ (1 / 2 : ℝ) * F (j + 1) + B j)
    (j : ℕ) :
    F j ≤ (1 / 4 : ℝ) * F (j + 2) +
      B j + (1 / 2 : ℝ) * B (j + 1) := by
  have h₀ := hhalf j
  have h₁ := hhalf (j + 1)
  nlinarith only [h₀, h₁]

/-- Uniform-remainder specialization of
`residual_eighth_of_three_half_steps`. -/
theorem residual_eighth_of_three_half_steps_le
    {F B : ℕ → ℝ} {A : ℝ}
    (hhalf : ∀ j : ℕ, F j ≤ (1 / 2 : ℝ) * F (j + 1) + B j)
    (hB : ∀ j : ℕ, B j ≤ A)
    (j : ℕ) :
    F j ≤ (1 / 8 : ℝ) * F (j + 3) + (7 / 4 : ℝ) * A := by
  have hstep := residual_eighth_of_three_half_steps hhalf j
  have h₀ := hB j
  have h₁ := hB (j + 1)
  have h₂ := hB (j + 2)
  nlinarith only [hstep, h₀, h₁, h₂]

/-- Actual boundary-profile form of the grouped residual step.  The outer
radius is the third successor; no claim is made that two half-steps suffice. -/
theorem boundaryCrossScaleEnergyProfile_residual_eighth_of_three_half_steps
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d)
    (uRes : H1Function (openCubeSet Q)) (B : ℕ → ℝ)
    (hhalf : ∀ j : ℕ,
      boundaryCrossScaleEnergyProfile Q R center
          (coarseCaccioppoliRadiusSequence j) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center
            (coarseCaccioppoliRadiusSequence (j + 1)) (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (uRes.grad x)) + B j)
    (j : ℕ) :
    boundaryCrossScaleEnergyProfile Q R center
        (coarseCaccioppoliRadiusSequence j) (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
      (1 / 8 : ℝ) *
        boundaryCrossScaleEnergyProfile Q R center
          (coarseCaccioppoliRadiusSequence (j + 3)) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) +
        B j + (1 / 2 : ℝ) * B (j + 1) + (1 / 4 : ℝ) * B (j + 2) := by
  let F : ℕ → ℝ := fun k ↦
    boundaryCrossScaleEnergyProfile Q R center
      (coarseCaccioppoliRadiusSequence k) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (uRes.grad x))
  exact residual_eighth_of_three_half_steps (F := F) hhalf j

/-- Actual boundary-profile form of the two-step residual quarter estimate. -/
theorem boundaryCrossScaleEnergyProfile_residual_quarter_of_two_half_steps
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d)
    (uRes : H1Function (openCubeSet Q)) (B : ℕ → ℝ)
    (hhalf : ∀ j : ℕ,
      boundaryCrossScaleEnergyProfile Q R center
          (coarseCaccioppoliRadiusSequence j) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center
            (coarseCaccioppoliRadiusSequence (j + 1)) (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (uRes.grad x)) + B j)
    (j : ℕ) :
    boundaryCrossScaleEnergyProfile Q R center
        (coarseCaccioppoliRadiusSequence j) (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
      (1 / 4 : ℝ) *
        boundaryCrossScaleEnergyProfile Q R center
          (coarseCaccioppoliRadiusSequence (j + 2)) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) +
        B j + (1 / 2 : ℝ) * B (j + 1) := by
  let F : ℕ → ℝ := fun k ↦
    boundaryCrossScaleEnergyProfile Q R center
      (coarseCaccioppoliRadiusSequence k) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (uRes.grad x))
  exact residual_quarter_of_two_half_steps (F := F) hhalf j

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
