module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyFinish
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevFinalArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMass
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasureFinish
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevProjectionEmbedding

@[expose] public section

/-!
# Provider for the weighted local Sobolev inequality

The exponent is the manuscript one, `p0 = 2 + 1 / (2 * (4 * d - 3))`, which is
the largest exponent compatible with the uniform increment decay
`-(1/2) + d * (1/2 - 1/p0) + 3/(8 * p0) ≤ -(1/4)`.

The normalized weight `b / cubeAverage Q b` is read as a probability measure on
the cube (`weightedSobolevMeasure`).  The frozen mass hypothesis bounds the
triadic cell averages of `b / cubeAverage Q b - 1`, hence the mass of every
descendant cell by `8 * (1 + M) * 3 ^ (3 * j / 8)` times its normalized share.
Against that mass a weighted `L^p0` estimate for the triadic projection
increments converges geometrically, so the cube fluctuation of an `H^1` datum is
controlled by the half-order Besov depth seminorm, which the coarse Poincare
and Caccioppoli vocabulary bounds by the scalar coarse energy.  The constant
mode is removed either from the zero-trace average bound or, in the weighted
mean-zero branch, by centering.  Squaring the resulting `L^p0` bound and
substituting `cubeScaleFactor (originCube d m) = 3 ^ m` produces the frozen
price.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open scoped ENNReal NNReal
noncomputable section


theorem SubdiffusiveProcess.Providers.Section8.weighted_local_sobolev (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p0 C : ℝ, 2 < p0 ∧ 0 < C ∧
      ∀ m : ℤ, ∀ b : Vec d → ℝ,
        let Q := originCube d m
        let U := openCubeSet Q
        CoefficientOn U b →
        ∀ hb : Homogenization.ExactCircIntegrable Q
            (fun x => b x / cubeAverage Q b - 1),
        ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
        (∀ᵐ x ∂volume.restrict U,
          (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b x)) →
        ∀ M : ℝ, 1 ≤ M →
        ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal Q (1 / 8)
            (4 * (d : ℝ)) (fun x => b x / cubeAverage Q b - 1) hb ≤
          ENNReal.ofReal M →
        ∀ f : H1Function U,
          ((∃ g : H10Function U, g.toH1Function = f) ∨
            (∫ x in U, f.toFun x * b x) = 0) →
          (ENNReal.ofReal ((cubeAverage Q b)⁻¹) *
            (volume U)⁻¹ * ∫⁻ x in U,
              ENNReal.ofReal (|f.toFun x| ^ p0 * b x)) ^ (2 / p0) ≤
            ENNReal.ofReal (C * (1 + M) ^ (2 / p0) * ((3 : ℝ) ^ m) ^ 2 *
              (Homogenization.Book.Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹ *
              volumeAverage U (fun x => b x * vecDot (f.grad x) (f.grad x)))

:= by
  classical
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨p0, hp0def⟩ : ∃ p0 : ℝ, p0 = 2 + 1 / (2 * (4 * (d : ℝ) - 3)) := ⟨_, rfl⟩
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ,
      Cp = (2 * (3 : ℝ) ^ (1 / 4 : ℝ)) / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Ce, hCedef⟩ : ∃ Ce : ℝ,
      Ce = WeightedEnergy.weightedLocalSobolevEnergyConstant d := ⟨_, rfl⟩
  have hCp : 0 < Cp := hCpdef ▸ weightedProjection_constant_pos
  have hCe : 0 < Ce := hCedef ▸ WeightedEnergy.weightedLocalSobolevEnergyConstant_pos d
  have hp0 : 2 < p0 := hp0def ▸ weightedSobolev_p0_gt_two hD
  have hp0pos : 0 < p0 := by linarith
  have hbexp : -(1 / 2 : ℝ) + (d : ℝ) * (1 / 2 - 1 / p0) + 3 / (8 * p0) ≤ -(1 / 4 : ℝ) := by
    rw [hp0def]; exact weightedSobolev_increment_exponent hD
  refine ⟨p0, (2 * (Cp * (8 : ℝ) ^ (1 / p0) * Ce + Ce)) ^ 2, hp0,
    weightedSobolev_final_constant_pos hCp hCe, ?_⟩
  intro m b Q U hbCoeff hbInt coeff hcoeff M hM hmass f hf
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hfmeas : AEStronglyMeasurable f.toFun (normalizedCubeMeasure Q) :=
    (WeightedEnergy.h1_memLp_normalizedCubeMeasure Q f).aestronglyMeasurable
  have hfL2 : MemLp f.toFun 2 (normalizedCubeMeasure Q) :=
    WeightedEnergy.h1_memLp_normalizedCubeMeasure Q f
  -- the coarse energy and the two geometric scales
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E =
      (Homogenization.Book.Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹ *
        volumeAverage U (fun x => b x * vecDot (f.grad x) (f.grad x)) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = cubeBesovScaleWeight (-1 / 2) Q := ⟨_, rfl⟩
  have hE : 0 ≤ E :=
    hEdef ▸ WeightedEnergy.scalar_half_energy_nonneg_of_scalarParent Q coeff b hcoeff f
  have hS : 0 ≤ S := hSdef ▸ cubeBesovScaleWeight_nonneg _ _
  have hSsq : S ^ 2 = cubeScaleFactor Q := by
    rw [hSdef]; exact weightedSobolev_scale_half_sq Q
  -- the half-order depth bound and the zero-trace average bound
  have hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 2) 2 f.toFun j ≤
      Ce * S * Real.sqrt E := by
    intro j
    rw [hCedef, hSdef, hEdef]
    exact WeightedEnergy.h1_depthSeminorm_half_le_dimensional_energy Q coeff b hcoeff f j
  have hBdepth : 0 ≤ Ce * S * Real.sqrt E := by positivity
  -- the triadic mass of the weighted measure
  have hK : (0 : ℝ) ≤ 8 * (1 + M) := by linarith
  have hmassν : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      weightedSobolevMeasure Q b (cubeSet R) ≤
        (ENNReal.ofReal (8 * (1 + M)) * (3 : ℝ≥0∞) ^ ((3 / 8 : ℝ) * (j : ℝ))) /
          ((descendantsAtDepth Q j).card : ℝ≥0∞) := by
    intro j R hR
    exact weightedSobolev_measure_cell_bound b hbCoeff hR _ hK
      (weightedSobolev_cell_mass_bound hd m b hbCoeff hbInt M hM0 hmass j R hR)
  -- the weighted projection embedding
  have hA := weightedProjection_embedding Q (weightedSobolevMeasure Q b)
    (weightedSobolevMeasure_absolutelyContinuous Q b) f.toFun hfL2
    (8 * (1 + M)) (Ce * S * Real.sqrt E) p0 hK hBdepth hp0.le hbexp hmassν hdepth
  rw [← hCpdef, ← hSdef] at hA
  have hA0 : 0 ≤ Cp * (8 * (1 + M)) ^ (1 / p0) * S * (Ce * S * Real.sqrt E) := by
    have : (0 : ℝ) ≤ (8 * (1 + M)) ^ (1 / p0) := Real.rpow_nonneg hK _
    positivity
  have hBmean0 : 0 ≤ Ce * S ^ 2 * Real.sqrt E := by positivity
  -- the constant mode
  have hm : |cubeAverage Q f.toFun| ≤ Ce * S ^ 2 * Real.sqrt E ∨
      (∫ x in U, f.toFun x * b x) = 0 := by
    rcases hf with ⟨g, hg⟩ | hz
    · refine Or.inl ?_
      rw [hCedef, hSsq, hEdef, ← hg]
      exact WeightedEnergy.h10_average_le_dimensional_energy Q coeff b hcoeff g
    · exact Or.inr hz
  have hnorm := weightedSobolev_finish_norm_bound Q b f.toFun hbCoeff p0 (by linarith)
    hfmeas _ _ hA0 hBmean0 hA hm
  -- square the weighted norm and compare against the frozen price
  rw [weightedSobolevMeasure_lp_readout Q b f.toFun hbCoeff p0 hp0pos hfmeas]
  refine weightedSobolev_norm_square_bound (by positivity) hnorm ?_
  have hscalar := weightedSobolev_finish_scalar_bound Cp Ce M S E p0 hCp.le hCe.le hM0
    hS hE hp0pos
  refine hscalar.trans (le_of_eq ?_)
  rw [hSsq, weightedSobolev_origin_scale d m, hEdef]
  exact weightedSobolev_energy_factor
