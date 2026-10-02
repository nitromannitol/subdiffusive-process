import SubdiffusiveProcess.Paper.goodext_parent_oscillation
import SubdiffusiveProcess.Sobolev.NativeEnergyMeasureRestriction


open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper
/-- Native global energy recovery supplies the exact local energy premise for the parent oscillation bound. -/
theorem goodext_parent_oscillation_from_native
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Q : Opens (SpatialCoordinates d)) (hq : centeredCube z r hr ≤ Q)
    (aRoot : ℕ → PositiveCoefficient Q)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hab : ∀ n, (aRoot n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] (a n).val)
    (un : ℕ → Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, (un n).toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hlim : TendstoUniformlyOn UN U atTop (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [IsFiniteMeasure mu]
    (henergy : ∀ n, muN n = gradientEnergyMeasure (aRoot n)
      (sobolevGradient (sobolevDataOfH1 (un n))))
    (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
    (hpad : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ parentCell)
    (hrec : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by

  let q : Opens (SpatialCoordinates d) := centeredCube z r hr
  let unLocal : ℕ → weakSobolevGraph q := fun n =>
    ⟨sobolevDataOfH1 ((un n).restrict q.isOpen hq),
      sobolevDataOfH1_mem_weak ((un n).restrict q.isOpen hq)⟩
  have hUNLocal : ∀ n,
      ((unLocal n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n := by
    intro n
    change ((sobolevDataOfH1 ((un n).restrict q.isOpen hq)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n
    calc
      ((sobolevDataOfH1 ((un n).restrict q.isOpen hq)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))]
          ((un n).restrict q.isOpen hq).toFun :=
        sobolevDataOfH1_fst_coeFn ((un n).restrict q.isOpen hq)
      _ =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] (un n).toFun := by
        simpa only [H1Function.restrict] using
          (Filter.EventuallyEq.rfl : (un n).toFun =ᶠ[ae (volume.restrict (q : Set (SpatialCoordinates d)))] (un n).toFun)
      _ =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] UN n :=
        ae_restrict_of_ae_restrict_of_subset hq (hUN n)
  letI hfiniteMuN : ∀ n, IsFiniteMeasure (muN n) := fun n => by
    letI hfiniteRoot : IsFiniteMeasure
        (gradientEnergyMeasure (aRoot n)
          (sobolevGradient (sobolevDataOfH1 (un n)))) :=
      (gradientEnergyMeasure_finite_and_real (aRoot n)
        (sobolevGradient (sobolevDataOfH1 (un n)))).1
    rw [henergy n]
    exact hfiniteRoot
  have hrestrict (n : ℕ) :
      (gradientEnergyMeasure (aRoot n)
        (sobolevGradient (sobolevDataOfH1 (un n)))).restrict (q : Set (SpatialCoordinates d)) =
        gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val) := by
    exact gradientEnergyMeasure_restrict_of_native_data hq (aRoot n) (a n) (hab n)
      (un n) (unLocal n) rfl
  have hmass (n : ℕ) :
      muN n (q : Set (SpatialCoordinates d)) =
        gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val)
          (q : Set (SpatialCoordinates d)) := by
    calc
      muN n (q : Set (SpatialCoordinates d)) =
          (gradientEnergyMeasure (aRoot n)
            (sobolevGradient (sobolevDataOfH1 (un n)))).restrict
              (q : Set (SpatialCoordinates d)) (q : Set (SpatialCoordinates d)) := by
        rw [henergy n]
        exact (Measure.restrict_apply_self _ _).symm
      _ = gradientEnergyMeasure (a n) (sobolevGradient (unLocal n).val)
          (q : Set (SpatialCoordinates d)) :=
        congrArg (fun nu : Measure (SpatialCoordinates d) => nu (q : Set (SpatialCoordinates d)))
          (hrestrict n)
  have henergyLocal : ∀ n,
      ((muN n) (q : Set (SpatialCoordinates d))).toReal =
        localGradientEnergy (a n) q.isOpen.measurableSet (sobolevGradient (unLocal n).val) := by
    intro n
    rw [hmass n]
    exact (gradientEnergyMeasure_finite_and_real (a n)
      (sobolevGradient (unLocal n).val)).2 (q : Set (SpatialCoordinates d))
        q.isOpen.measurableSet
  exact goodext_parent_oscillation hd I Pin z r hr a unLocal UN U hUNLocal hU hlim
    sigma cell hsigma hsigma1 hcell sN s hsN hs hsLim hell muN mu henergyLocal
    parentCell hparent hpad hrec
end Paper
