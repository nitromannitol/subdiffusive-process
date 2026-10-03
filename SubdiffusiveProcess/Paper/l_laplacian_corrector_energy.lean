module

public import SubdiffusiveProcess.LaplacianCorrector.FiniteVolumeLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepProjectedEnergyBound
public import Homogenization.PDE.DirichletRHS
public import Homogenization.PDE.NeumannRHS

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem l_laplacian_corrector_energy {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m h : ℕ), 0 < h → h ≤ m + 1 →
        (h : ℝ) ≤ M.delta⁻¹ →
        ∀ p : Vec d, vecNormSq p = 1 →
          (∀ w : (K : ℕ) → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
              H10Function (openCubeSet (originCube d (K : ℤ))),
            (∀ (K : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              IsZeroTraceDirichletRhsWeakSolution (fun _ => (1 : Mat d))
                (openCubeSet (originCube d (K : ℤ))) (w K ω)
                (fun x => -(Real.exp (∑ k ∈ Finset.Ico (m + 1 - h) (m + 1),
                    (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) - 1) • p)) →
            ∃ L : ℝ,
              Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
                  (fun x => vecNormSq ((w K ω).toH1Function.grad x)) ∂M.P.toMeasure)
                atTop (𝓝 L) ∧
              |L - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / d| ≤
                C * M.delta ^ 4 * (h : ℝ) ^ 2) ∧
          (∀ w : (K : ℕ) → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d →
              H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))),
            (∀ (K : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              IsMeanZeroNeumannRhsWeakSolution (fun _ => (1 : Mat d))
                (openCubeSet (originCube d (K : ℤ))) (w K ω)
                (fun x => (Real.exp (∑ k ∈ Finset.Ico (m + 1 - h) (m + 1),
                    (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) - 1) • p)) →
            ∃ L : ℝ,
              Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
                  (fun x => vecNormSq ((w K ω).toH1Function.grad x)) ∂M.P.toMeasure)
                atTop (𝓝 L) ∧
              |L - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / d| ≤
                C * M.delta ^ 4 * (h : ℝ) ^ 2) := by
  refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepProjectedEnergyErrorConst,
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepProjectedEnergyErrorConst_pos, ?_⟩
  intro M m h hh hhm hdelta p hp
  letI : NeZero d := ⟨by have hd := M.shellPrefix.dimension; omega⟩
  have hcoeff : identityCoeffField d = (fun _ : Vec d => (1 : Mat d)) := by
    funext x i j
    simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
  let a := m + 1 - h
  have hupper : a + h = m + 1 := Nat.sub_add_cancel hhm
  constructor
  · intro w hw
    refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepProjectedEnergy M a h p hh,
      ?_, SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_oneStepProjectedEnergy_sub_two_tauSq_mul_div_dimension_le
        M a h p hh hp hdelta⟩
    apply SubdiffusiveProcess.LaplacianCorrector.tendsto_integral_windowDirichletEnergy
      M a h p hh hp w
    intro K omega
    simpa only [SubdiffusiveProcess.LaplacianCorrector.windowMultiplier, hupper,
      hcoeff, a] using hw K omega
  · intro w hw
    refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepProjectedEnergy M a h p hh,
      ?_, SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_oneStepProjectedEnergy_sub_two_tauSq_mul_div_dimension_le
        M a h p hh hp hdelta⟩
    apply SubdiffusiveProcess.LaplacianCorrector.tendsto_integral_windowNeumannEnergy
      M a h p hh hp w
    intro K omega
    simpa only [SubdiffusiveProcess.LaplacianCorrector.windowMultiplier, hupper,
      hcoeff, a] using hw K omega

end Paper
