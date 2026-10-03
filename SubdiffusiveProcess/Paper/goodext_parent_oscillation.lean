module

public import Mathlib.Topology.UrysohnsLemma
public import SubdiffusiveProcess.Paper.goodext_coarse_poincare
public import SubdiffusiveProcess.DirichletForm.LocalEnergyRecoveryBounds
public import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal

noncomputable section
namespace Paper

/-- Uniform source convergence and energy-measure recovery convert coarse oscillation into parent energy. -/
theorem aux_goodext_parent_oscillation_cutoff
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (un : ℕ → weakSobolevGraph (centeredCube z r hr))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hlim : TendstoUniformlyOn UN U atTop (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [hfinN : ∀ n, IsFiniteMeasure (muN n)] [IsFiniteMeasure mu]
    (henergy : ∀ n, (muN n (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      localGradientEnergy (a n) (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (un n).val))
    (parentCell : Set (SpatialCoordinates d)) (hparent : MeasurableSet parentCell)
    (chi : SpatialCoordinates d → ℝ)
    (hchiN : ∀ n, Integrable chi (muN n)) (hchi : Integrable chi mu)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchiQ : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), chi x = 1)
    (hchiP : ∀ x ∉ parentCell, chi x = 0)
    (hrec : Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu))) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        (mu parentCell).toReal := by
  have hmem : ∀ n, MemLp (UN n) 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro n
    exact (memLp_congr_ae (hUN n)).mp (Lp.memLp (un n).val.1)
  have hosc := tendsto_centered_normalizedL2_of_tendstoUniformlyOn
    (centeredCube z r hr : Set (SpatialCoordinates d))
    (centeredCube z r hr).isOpen.measurableSet (centeredCube_volume_pos z hr)
    (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top) UN U hmem hU hlim
  let C := Pin.C ^ 2 * r ^ 2 *
    ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hc0 : 0 < Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1 := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (inv_nonneg.mpr (mul_pos hc0 hcell).le)) (centeredCube_volume_pos z hr).le
  apply oscillation_bound_of_energy_measure_recovery muN mu
    (centeredCube z r hr : Set (SpatialCoordinates d)) parentCell
    (centeredCube z r hr).isOpen.measurableSet hparent chi hchiN hchi
    hchi0 hchi1 hchiQ hchiP hrec sN s hsN hs hsLim _ _ hosc C hC
  intro n
  rw [henergy n]
  exact aux_goodext_coarse_poincare_squared hd I Pin z r hr (a n) (un n) (UN n) (hUN n)
    sigma cell (sN n) hsigma hsigma1 hcell (hsN n) (hell n)

/-- A padded local oscillation is controlled by the recovered energy of its open parent. -/
theorem goodext_parent_oscillation
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (un : ℕ → weakSobolevGraph (centeredCube z r hr))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] UN n)
    (hU : MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hlim : TendstoUniformlyOn UN U atTop (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hell : ∀ n, cell * sN n ≤ I.lam z r hr (a n) z r sigma 2)
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [hfinN : ∀ n, IsFiniteMeasure (muN n)] [IsFiniteMeasure mu]
    (henergy : ∀ n, (muN n (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      localGradientEnergy (a n) (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (un n).val))
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
  obtain ⟨chi, hchiQ, hchiPc, hchiP, hchiBounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (centeredCube_isBounded z hr).isCompact_closure hparent hpad
  have hbound : ∀ x, ‖chi x‖ ≤ (1 : ℝ) := by
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hchiBounds x).1] using (hchiBounds x).2
  have hintN : ∀ n, Integrable chi (muN n) := by
    intro n
    exact (integrable_const (1 : ℝ)).mono' chi.continuous.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hint : Integrable chi mu :=
    (integrable_const (1 : ℝ)).mono' chi.continuous.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact aux_goodext_parent_oscillation_cutoff hd I Pin z r hr a un UN U hUN hU hlim
    sigma cell hsigma hsigma1 hcell sN s hsN hs hsLim hell muN mu henergy
    parentCell hparent.measurableSet chi hintN hint
    (fun x => (hchiBounds x).1) (fun x => (hchiBounds x).2)
    (fun x hx => hchiQ (subset_closure hx))
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun hx' => hx (hchiP hx')))
    (hrec chi chi.continuous hchiPc)

end Paper
