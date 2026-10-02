import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.Normalization

/-!
# Theta-perturbed cutoff Hölder ladder: collared global family

The multiscale response API is indexed by a coefficient family on every
triadic cube, whereas the bounded-multiplier hypothesis controls `theta` only
on the D-050 collar.  We therefore extend the *normalized* multiplier by one
off the collar.  The resulting field is measurable and uniformly near one,
and it agrees with the physical normalized coefficient on every comparison
cube contained in the collar.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Filter MeasureTheory Homogenization Homogenization.Book

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The normalized multiplier, extended by one outside the collar. -/
def localizedNormalizedMultiplier (B : Set (Vec d)) (b : ℝ)
    (theta : Vec d → ℝ) : Vec d → ℝ :=
  B.piecewise (normalizedMultiplier b theta) (fun _ ↦ 1)

/-- The localized normalized cutoff coefficient. -/
def localizedThetaCutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (B : Set (Vec d)) (b : ℝ) (theta : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
    localizedNormalizedMultiplier B b theta x

/-- Measurability of the collar extension. -/
theorem aestronglyMeasurable_localizedNormalizedMultiplier
    {B : Set (Vec d)} (hB : MeasurableSet B) {b : ℝ}
    {theta : Vec d → ℝ} (htheta : ContinuousOn theta B) :
    AEStronglyMeasurable (localizedNormalizedMultiplier B b theta) volume := by
  have hthetaB := htheta.aestronglyMeasurable (μ := volume) hB
  have hnormalizedB : AEStronglyMeasurable (normalizedMultiplier b theta)
      (volume.restrict B) := by
    exact hthetaB.const_mul b⁻¹
  have hone : AEStronglyMeasurable (fun _ : Vec d ↦ (1 : ℝ))
      (volume.restrict Bᶜ) := aestronglyMeasurable_const
  exact AEStronglyMeasurable.piecewise hB hnormalizedB hone

/-- The localized multiplier remains uniformly near one on all of space. -/
theorem localizedNormalizedMultiplier_near_one
    {B : Set (Vec d)} {b epsilon : ℝ} {theta : Vec d → ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon) :
    ∀ x, |localizedNormalizedMultiplier B b theta x - 1| ≤ epsilon := by
  intro x
  by_cases hx : x ∈ B
  · simpa [localizedNormalizedMultiplier, hx, normalizedMultiplier] using hnear x hx
  · simpa [localizedNormalizedMultiplier, hx] using hepsilon0

/-- Cube-wise ellipticity data for the localized normalized coefficient. -/
noncomputable def localizedThetaTriadicCoeffData
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon) :
    ScalarTriadicCoeffData (localizedThetaCutoff M L omega B b theta) where
  onCube Q := by
    let a : Vec d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
    let t : Vec d → ℝ := localizedNormalizedMultiplier B b theta
    let ha : ScalarCoeffOnData (Ch02.cubeDomain Q) a :=
      aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
    have htMeas : AEStronglyMeasurable t volume :=
      aestronglyMeasurable_localizedNormalizedMultiplier hB htheta
    have haMeas : AEStronglyMeasurable a volume :=
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).aestronglyMeasurable
    have hproduct : AEStronglyMeasurable (fun x ↦ a x * t x) volume :=
      haMeas.mul htMeas
    have htNear : ∀ x ∈ (Ch02.cubeDomain Q : Set (Vec d)),
        |t x - 1| ≤ epsilon := by
      intro x _
      exact localizedNormalizedMultiplier_near_one hepsilon0 hnear x
    exact scalarCoeffOnData_mul_nearOne ha hepsilon0 hepsilon1
      (hproduct.restrict (s := openCubeSet Q)) htNear

/-- The public triadic family used by the theta-perturbed homogenization-error
carrier. -/
noncomputable def localizedThetaCoeffFamily
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon) :
    Ch02.TriadicCoeffFamily d :=
  (localizedThetaTriadicCoeffData M L omega hB theta htheta
    hepsilon0 hepsilon1 hnear).toTriadicCoeffFamily

/-- On a comparison cube contained in the collar, the localized coefficient
is literally the normalized physical coefficient. -/
theorem localizedThetaCutoff_eq_normalizedThetaCutoff_on
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} {b : ℝ} {theta : Vec d → ℝ}
    {Q : TriadicCube d} (hQB : openCubeSet Q ⊆ B) :
    ∀ x ∈ openCubeSet Q,
      localizedThetaCutoff M L omega B b theta x =
        normalizedThetaCutoff M L omega b theta x := by
  intro x hx
  simp only [localizedThetaCutoff, normalizedThetaCutoff,
    localizedNormalizedMultiplier, Set.piecewise_eq_of_mem B _ _ (hQB hx)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
