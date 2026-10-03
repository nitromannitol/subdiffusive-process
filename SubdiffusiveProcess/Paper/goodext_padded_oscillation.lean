module

public import SubdiffusiveProcess.Paper.goodext_parent_oscillation_from_graph
public import SubdiffusiveProcess.Sobolev.PaddedPoincareScaling
public import SubdiffusiveProcess.Sobolev.GoodCellEnergyScaling
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

@[expose] public section

/-! Padded-parent oscillation of the good-cell source representative in `lem_goodext`; no trace or response claim. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Padded-parent oscillation of the source representative, from the controlled subsequence,
the eventual lower coefficient on the padded cube and energy-measure recovery. -/
theorem goodext_padded_oscillation
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pin : Paper.in_poincare d hd I)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (envs : ℕ → BilateralField d) (Ns : ℕ → ℕ)
    (GN : ℕ → BilateralField d →
      DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
        DomainL2 (centeredCube Qcentre Qside hQside))
    (hGN : ∀ N omega f, GN N omega f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (U : SpatialCoordinates d → ℝ) (UN : ℕ → SpatialCoordinates d → ℝ)
    (hUN : ∀ n, (GN (Ns n) (envs n) fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] UN n)
    (hUniform : TendstoUniformlyOn UN U atTop
      (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (G0 : DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (hUr : (G0 fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h3qQ : Metric.ball z (3 * r / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (sigma cell tau : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell)
    (sNs : ℕ → ℝ) (s0 : ℝ) (hsNpos : ∀ n, 0 < sNs n) (hs0 : 0 < s0)
    (hsLim : Tendsto sNs atTop (𝓝 s0))
    (hPadLower : ∀ᶠ n in atTop, (cell / (2 * Real.exp tau)) * sNs n ≤
      I.lam z (3 * r) (by positivity)
        (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) z (by positivity)) z (3 * r) sigma 2)
    (Form0 : DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (Gamma0 : DirichletForm.EnergyMeasure Form0) (hdom : G0 fL2 ∈ Form0.domain)
    (hrec : ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x in (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        chi x * (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside).val x *
          ∑ i : Fin d, ((sobolevGradient (responseSolution S
            (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside)
            ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val i) x) ^ 2)
        atTop (𝓝 (∫ x, chi x ∂(Gamma0.measure (G0 fL2)))))
    (zP : SpatialCoordinates d) (Lr : ℝ)
    (hPadParent : Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (Lr / 2)) :
    normalizedL2On (Metric.ball z (3 * r / 2))
      (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
        ∫ y in Metric.ball z (3 * r / 2), U y) ≤
      (Real.sqrt (Pin.C ^ 2 * 18 /
          ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
            Homogenization.Book.Ch02.geometricDiscount 1 1) * cell * (3 : ℝ) ^ d)) *
        Real.exp (tau / 2)) * r ^ ((2 - (d : ℝ)) / 2) * s0 ^ (-(1 : ℝ) / 2) *
        Real.sqrt ((Gamma0.measure (G0 fL2) (Metric.ball zP (Lr / 2))).toReal) := by
  let Q := centeredCube Qcentre Qside hQside
  let aRoot : ℕ → PositiveCoefficient Q := fun n =>
    Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside
  let aPad : ℕ → PositiveCoefficient (centeredCube z (3 * r) (by positivity)) := fun n =>
    Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) z (by positivity)
  let un : ℕ → weakSobolevGraph Q := fun n =>
    ⟨(responseSolution S (aRoot n) ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val,
      S.le_weak (responseSolution S (aRoot n)
        ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).property⟩
  have hUNrep (n : ℕ) : ((un n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Q : Set (SpatialCoordinates d))] UN n := by
    change ((responseSolution S (aRoot n)
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[_] UN n
    rw [← hGN (Ns n) (envs n) fL2]
    exact hUN n
  have hab (n : ℕ) : (aRoot n).val =ᵐ[
      volume.restrict (centeredCube z (3 * r) (by positivity) : Set (SpatialCoordinates d))]
      (aPad n).val := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h3qQ
      (Lane4.cutoffPositiveCoefficient_representative M H (envs n) (Ns n) Qcentre hQside).2.2.2,
      (Lane4.cutoffPositiveCoefficient_representative M H (envs n) (Ns n) z
        (show 0 < 3 * r from mul_pos (by norm_num) hr)).2.2.2] with x hx hy
    exact hx.trans hy.symm
  have hUNlimit : TendstoUniformlyOn UN U atTop
      (centeredCube z (3 * r) (by positivity) : Set (SpatialCoordinates d)) :=
    hUniform.mono (h3qQ.trans subset_closure)
  have hUlp : MemLp U 2 (volume.restrict
      (centeredCube z (3 * r) (by positivity) : Set (SpatialCoordinates d))) := by
    have hUQ : MemLp U 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      (Lp.memLp (G0 fL2)).ae_eq hUr
    exact hUQ.mono_measure (Measure.restrict_mono h3qQ le_rfl)
  have hcellPad : 0 < cell / (2 * Real.exp tau) :=
    div_pos hcell (mul_pos (by norm_num) (Real.exp_pos _))
  let nu := Gamma0.measure (G0 fL2)
  letI nuFinite : IsFiniteMeasure nu := ⟨Gamma0.measure_univ_lt_top _ hdom⟩
  have hdiscount : 0 < Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1 := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  have hParentOscSq := goodext_parent_oscillation_from_graph hd I Pin z (3 * r)
    (by positivity) Q h3qQ aRoot aPad hab un UN U hUNrep hUlp hUNlimit
    sigma (cell / (2 * Real.exp tau)) hsigma hsigma1 hcellPad sNs s0
    hsNpos hs0 hsLim hPadLower nu
    (Metric.ball zP (Lr / 2)) Metric.isOpen_ball
    (by
      change closure (Metric.ball z (3 * r / 2)) ⊆ Metric.ball zP (Lr / 2)
      rw [closure_ball z (ne_of_gt (by positivity : 0 < 3 * r / 2))]
      exact hPadParent)
    hrec
  have hvol := centeredCube_volume_real z (show 0 < 3 * r by positivity)
  have hSq := hParentOscSq.trans (le_of_eq (by
    rw [hvol, padded_poincare_prefactor d Pin.C _ cell r tau hdiscount hcell hr]))
  exact oscillation_le_scaled_sqrt_of_sq_le d _ _ r s0 (nu (Metric.ball zP (Lr / 2))).toReal
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hr hs0 ENNReal.toReal_nonneg hSq


end Paper
