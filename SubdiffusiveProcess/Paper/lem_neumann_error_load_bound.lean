module

public import SubdiffusiveProcess.Paper.lem_load
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
- `lem_load` supplies the fractional load comparison at paper label `mfd:lem-neumann-error`.
- The carried `SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd`
  is the standing published Sobolev input required by `lem_load`; its extension
  field supplies the bounded `H^{3/4}` extension used at paper label `mfd:lem-neumann-error`.
  This is carried as an input, not concluded by this proof step; the source is
  the deferred foundational input recorded in `lem_load` and
  `SubdiffusiveProcess/EllipticRegularity/Inputs.lean`.
- The mean-zero carrier is the concrete `meanZeroSobolevGraph` used by
  the parent; the source representative is tied almost everywhere to the
  face-bump source, not chosen independently.
- CONCLUDED: the pointwise dual-load estimate.  It is a proof step, not a
  new hypothesis of `lem_neumann_error`.
-/
theorem lem_neumann_error_load_bound :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd),
    ∃ Cload : ℝ, 0 < Cload ∧
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
      (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps)) →
    ∀ (N : ℕ) (om : BilateralField d),
    ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
        ((sobolevVolumeLoad (fL2 N om)).comp
          (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)) z| ≤
        Cload * eps ^ (1 / 4 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
            one_pos threeQuarterOrder
            (z : SobolevData (unitNeumannCube d)).1)
    := by
  intro d hd _S
  obtain ⟨Cload, hCload, hbase⟩ := lem_load d hd _S
  refine ⟨Cload, hCload, ?_⟩
  intro rho hrho hnonneg hsupp hnorm pvec hpvec eps heps heps8 fL2 hf N om z
  let zw : weakSobolevGraph (unitNeumannCube d) :=
    ⟨(z : SobolevData (unitNeumannCube d)),
      (mem_meanZeroSobolevGraph_iff (z : SobolevData (unitNeumannCube d))).mp
        z.property |>.1⟩
  have hzmean : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      (z : SobolevData (unitNeumannCube d)).1 x) = 0 :=
    (mem_meanZeroSobolevGraph_iff (z : SobolevData (unitNeumannCube d))).mp
      z.property |>.2
  have hdm : domainMean ((z : SobolevData (unitNeumannCube d)).1) = 0 := by
    simp [domainMean, hzmean]
  have hzero : domainConstantL2 (Ω := unitNeumannCube d) 0 = 0 := by
    apply Lp.ext
    filter_upwards [domainConstantL2_coeFn (Ω := unitNeumannCube d) 0,
      Lp.coeFn_zero ℝ 2 (volume.restrict
        (unitNeumannCube d : Set (SpatialCoordinates d)))] with x hx hz
    rw [hx]
    simpa using hz.symm
  have hcenter :
      (z : SobolevData (unitNeumannCube d)).1 -
          domainConstantL2 (domainMean ((z : SobolevData (unitNeumannCube d)).1)) =
        (z : SobolevData (unitNeumannCube d)).1 := by
    rw [hdm, hzero, sub_zero]
  have hsmooth := hbase rho hrho hnonneg hsupp hnorm pvec hpvec eps heps heps8 zw
  have hleft :
      affineNeumannLoad pvec
            (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) zw) -
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho pvec eps x *
              (zw : SobolevData (unitNeumannCube d)).1 x =
        ((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) z -
          ((sobolevVolumeLoad (fL2 N om)).comp
            (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL) z := by
    change affineNeumannLoad pvec
            (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) zw) -
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho pvec eps x *
              (zw : SobolevData (unitNeumannCube d)).1 x =
        affineNeumannLoad pvec
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) z) -
          (sobolevVolumeLoad (fL2 N om))
            ((meanZeroSobolevGraph (unitNeumannCube d)).subtypeL z)
    rw [sobolevVolumeLoad_apply]
    have haff :
        affineNeumannLoad pvec
            (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) zw) =
          affineNeumannLoad pvec
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) z) := by
      rfl
    rw [haff]
    apply congrArg (fun t =>
      affineNeumannLoad pvec
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) z) - t)
    apply integral_congr_ae
    filter_upwards [hf N om] with x hx
    simpa only [zw, Submodule.subtypeL_apply] using congrArg
      (fun t => t * (z : SobolevData (unitNeumannCube d)).1 x) hx.symm
  have hsmooth' :
      |((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) z -
        ((sobolevVolumeLoad (fL2 N om)).comp
          (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL) z| ≤
        Cload * eps ^ (1 / 4 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
            one_pos threeQuarterOrder
            ((zw : SobolevData (unitNeumannCube d)).1 -
              domainConstantL2 (domainMean ((zw : SobolevData (unitNeumannCube d)).1)))) := by
    rw [← hleft]
    exact hsmooth
  have hcenter' :
      (zw : SobolevData (unitNeumannCube d)).1 -
        domainConstantL2 (domainMean ((zw : SobolevData (unitNeumannCube d)).1)) =
      (z : SobolevData (unitNeumannCube d)).1 := by
    simpa only [zw] using! hcenter
  have hright := congrArg
    (fun v : DomainL2 (unitNeumannCube d) => Cload * eps ^ (1 / 4 : ℝ) *
      Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
        one_pos threeQuarterOrder v)) hcenter'
  simpa only [sub_apply] using! hsmooth'.trans_eq hright

end SubdiffusiveProcess.Paper
