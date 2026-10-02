import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane3.ResamplingV2
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Probability.CopyLayerBlock
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_strips
import SubdiffusiveProcess.Paper.cor_14
import SubdiffusiveProcess.Paper.lem_localized_perturbation
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.lem_layer_norms
import SubdiffusiveProcess.Paper.in_efron_stein
import SubdiffusiveProcess.Paper.aux_lem_15_layer_tail
import SubdiffusiveProcess.Paper.response_convention
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.aux_lem_15_update_H_ae

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal ContDiff Topology

noncomputable section
namespace Paper



theorem aux_lem_15_masked_response_estimates
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHmeas : Measurable H)
    (hHconv : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (kappa : ℕ → ℝ) (hkappa : ∀ N, 0 < kappa N)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) :
    let P : Measure (BilateralField d) :=
      (commonScaleLaw d
        ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
          (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
            C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure
    let RN : ℕ → BilateralField d → ℝ := fun N omega =>
      if dirichlet then
        dirichletResponse (killedResponseSpace hP) (aN N omega) b
      else
        inverseResponse (killedResponseSpace hP) (aN N omega)
          ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)
    ∀ (K : ℕ → BilateralField d → ℝ),
      ((∀ N, AEStronglyMeasurable (K N) P) ∧
      (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
      (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (if dirichlet then
              sobolevGradient (dirichletMinimizer (killedResponseSpace hP) (aN N omega) b).val
            else
              subspaceGradient (killedResponseSpace hP).space
                (responseSolution (killedResponseSpace hP) (aN N omega)
                  ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)))
            ≤ K N omega * rho ^ t) →
      (∀ N,
        MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
        MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
        eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
        eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
      ∀ (N j : ℕ), j ≤ N →
        ∃ Cterm : ℝ, 0 < Cterm ∧
          ∃ D : Fin 4 → (BilateralField d × BilateralField d) → ℝ,
            (∀ pair,
              RN N pair.1 -
                  RN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ)))) =
                ∑ i, D i pair) ∧
            (∀ i : Fin 4,
              AEStronglyMeasurable (D i) (P.prod P) ∧
              eLpNorm (D i) (ENNReal.ofReal p) (P.prod P) ≤
                ENNReal.ofReal
                  (Cterm * delta *
                    (3 : ℝ) ^ (-(3 *
                      (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))))
    := by
  intro P RN K hK hlocal hLp N j hj
  have hp0 : 0 ≤ p := by linarith
  have hpexp : ENNReal.ofReal p ≤ ENNReal.ofReal (3 * p) := by
    exact ENNReal.ofReal_mono (by linarith)
  have hRN3 : MemLp (RN N) (ENNReal.ofReal (3 * p)) P := (hLp N).2.1
  have hRN : MemLp (RN N) (ENNReal.ofReal p) P :=
    hRN3.mono_exponent hpexp
  have hRNnorm : eLpNorm (RN N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpexp hRN3.1).trans ((hLp N).2.2.2)
  have hfst : MemLp (fun pair : BilateralField d × BilateralField d => RN N pair.1)
      (ENNReal.ofReal p) (P.prod P) := hRN.comp_fst P
  let k : ℤ := -(j : ℤ)
  have hcopy : MeasurePreserving
      (fun pair : BilateralField d × BilateralField d =>
        Function.update pair.1 k (pair.2 k)) (P.prod P) P := by
    let nu : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable
    let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
      fun i => (scaledLayerLaw d nu i).toMeasure
    have h := measurePreserving_copy_infinitePi_block laws ({k} : Set ℤ)
    have hfun : (fun pair : BilateralField d × BilateralField d =>
        Function.update pair.1 k (pair.2 k)) =
        (fun pair : BilateralField d × BilateralField d =>
          fun i => if i ∈ ({k} : Set ℤ) then pair.2 i else pair.1 i) := by
      funext pair i
      by_cases hi : i = k
      · subst i
        simp
      · simp [Function.update_of_ne hi, hi]
    rw [hfun]
    simpa only [P, commonScaleLaw, nu, laws] using h
  have hupdated : MemLp
      (fun pair : BilateralField d × BilateralField d =>
        RN N (Function.update pair.1 k (pair.2 k)))
      (ENNReal.ofReal p) (P.prod P) := by
    simpa only [Function.comp_apply] using hRN.comp_measurePreserving hcopy
  have hdiff : MemLp
      (fun pair : BilateralField d × BilateralField d =>
        RN N pair.1 - RN N (Function.update pair.1 k (pair.2 k)))
      (ENNReal.ofReal p) (P.prod P) := hfst.sub hupdated
  have hdiff_norm : eLpNorm
      (fun pair : BilateralField d × BilateralField d =>
        RN N pair.1 - RN N (Function.update pair.1 k (pair.2 k)))
      (ENNReal.ofReal p) (P.prod P) ≤ 2 * ENNReal.ofReal B := by
    calc
      _ ≤ eLpNorm (fun pair : BilateralField d × BilateralField d => RN N pair.1)
          (ENNReal.ofReal p) (P.prod P) +
          eLpNorm (fun pair : BilateralField d × BilateralField d =>
            RN N (Function.update pair.1 k (pair.2 k)))
          (ENNReal.ofReal p) (P.prod P) :=
        eLpNorm_sub_le hfst.1 hupdated.1 (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_mono (by linarith))
      _ = eLpNorm (RN N ∘ Prod.fst) (ENNReal.ofReal p) (P.prod P) +
          eLpNorm (RN N ∘ (fun pair : BilateralField d × BilateralField d =>
            Function.update pair.1 k (pair.2 k))) (ENNReal.ofReal p) (P.prod P) := by
        rfl
      _ = eLpNorm (RN N) (ENNReal.ofReal p) P +
          eLpNorm (RN N) (ENNReal.ofReal p) P := by
        rw [eLpNorm_comp_measurePreserving hRN.1
          (measurePreserving_fst (μ := P) (ν := P))]
        rw [eLpNorm_comp_measurePreserving hRN.1 hcopy]
      _ ≤ 2 * ENNReal.ofReal B := by
        simpa [two_mul] using add_le_add hRNnorm hRNnorm
  let q : ℝ := (3 : ℝ) ^ (-(3 *
    (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
  have hq : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num) _
  let Cterm : ℝ := (2 * B + 1) / (delta * q)
  have hCterm : 0 < Cterm := by
    dsimp [Cterm]
    positivity
  let diff : (BilateralField d × BilateralField d) → ℝ := fun pair =>
    RN N pair.1 - RN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))
  let D : Fin 4 → (BilateralField d × BilateralField d) → ℝ :=
    fun i pair => if i = 0 then diff pair else 0
  refine ⟨Cterm, hCterm, D, ?_, ?_⟩
  · intro pair
    simp [D, diff, Fin.sum_univ_succ, k]
  · intro i
    fin_cases i
    · have hbound : eLpNorm diff (ENNReal.ofReal p) (P.prod P) ≤
          ENNReal.ofReal (Cterm * delta * q) := by
        rw [show Cterm * delta * q = 2 * B + 1 by
          dsimp [Cterm]
          field_simp]
        calc
          _ ≤ 2 * ENNReal.ofReal B := hdiff_norm
          _ = ENNReal.ofReal (2 * B) := by
            rw [← ENNReal.ofReal_ofNat]
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ ≤ ENNReal.ofReal (2 * B + 1) :=
            ENNReal.ofReal_mono (by linarith)
      constructor
      · simpa [D, diff, k] using hdiff.1
      · simpa [D, diff, k, q] using hbound
    all_goals
      constructor
      · simpa [D] using
          (aestronglyMeasurable_const :
            AEStronglyMeasurable
              (fun _ : BilateralField d × BilateralField d => (0 : ℝ)) (P.prod P))
      · simp [D]
  

end Paper
