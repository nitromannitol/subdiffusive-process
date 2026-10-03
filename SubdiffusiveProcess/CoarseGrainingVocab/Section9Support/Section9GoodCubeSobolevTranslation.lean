module

public import SubdiffusiveProcess.Frozen.Section8.WeightedLocalSobolev
public import Homogenization.Sobolev.H1.Translation

@[expose] public section




set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Translation preserves the weighted power integral of an H¹ function. -/
theorem goodCube_weighted_lintegral_untranslate {d : ℕ} (z : Vec d)
    (U : Set (Vec d)) (b : Vec d → ℝ) (p : ℝ)
    (f : H1Function (translateSet z U)) :
    (∫⁻ x in U, ENNReal.ofReal (|(f.untranslate z).toFun x| ^ p * b (x + z))) =
      ∫⁻ x in translateSet z U, ENNReal.ofReal (|f.toFun x| ^ p * b x) := by
  simpa only [H1Function.untranslate_toFun] using
    (Homogenization.measurePreserving_addRight_restrict_translateSet z U).lintegral_comp_emb
      (Homeomorph.addRight z).measurableEmbedding
      (fun x => ENNReal.ofReal (|f.toFun x| ^ p * b x))

/-- Translation preserves the volume-averaged weighted Dirichlet energy. -/
theorem goodCube_weighted_energy_untranslate {d : ℕ} (z : Vec d)
    (U : Set (Vec d)) (b : Vec d → ℝ)
    (f : H1Function (translateSet z U)) :
    volumeAverage U (fun x => b (x + z) *
        vecDot ((f.untranslate z).grad x) ((f.untranslate z).grad x)) =
      volumeAverage (translateSet z U) (fun x => b x * vecDot (f.grad x) (f.grad x)) := by
  unfold volumeAverage
  rw [Homogenization.volume_translateSet_eq,
    ← Homogenization.setIntegral_comp_addRight_translateSet z U
      (fun x => b x * vecDot (f.grad x) (f.grad x))]
  simp only [H1Function.untranslate_grad]

/-- The Section 8 weighted Sobolev estimate on any translated reference cube. -/
theorem goodCube_weighted_local_sobolev_translated (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p0 C : ℝ, 2 < p0 ∧ 0 < C ∧
      ∀ m : ℤ, ∀ z : Vec d, ∀ b : Vec d → ℝ,
        let Q := originCube d m
        let U := openCubeSet Q
        let b0 : Vec d → ℝ := fun x => b (x + z)
        CoefficientOn U b0 →
        ∀ hb : Homogenization.ExactCircIntegrable Q
            (fun x => b0 x / cubeAverage Q b0 - 1),
        ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
        (∀ᵐ x ∂volume.restrict U,
          (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b0 x)) →
        ∀ M : ℝ, 1 ≤ M →
        ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal Q (1 / 8)
            (4 * (d : ℝ)) (fun x => b0 x / cubeAverage Q b0 - 1) hb ≤
          ENNReal.ofReal M →
        ∀ f : H1Function (translateSet z U),
          ((∃ g : H10Function (translateSet z U), g.toH1Function = f) ∨
            (∫ x in translateSet z U, f.toFun x * b x) = 0) →
          (ENNReal.ofReal ((cubeAverage Q b0)⁻¹) *
            (volume (translateSet z U))⁻¹ * ∫⁻ x in translateSet z U,
              ENNReal.ofReal (|f.toFun x| ^ p0 * b x)) ^ (2 / p0) ≤
            ENNReal.ofReal (C * (1 + M) ^ (2 / p0) * ((3 : ℝ) ^ m) ^ 2 *
              (Homogenization.Book.Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹ *
              volumeAverage (translateSet z U) (fun x => b x * vecDot (f.grad x) (f.grad x))) := by
  obtain ⟨p0, C, _hp0eq, hp0, hC, hmain⟩ := SubdiffusiveProcess.Frozen.Section8.weighted_local_sobolev d hd
  refine ⟨p0, C, hp0, hC, ?_⟩
  intro m z b Q U b0 hcoeff hb coeff haeff M hM hmass f hbranch
  have branch' : (∃ g : H10Function U, g.toH1Function = (f.untranslate z)) ∨
      (∫ x in U, (f.untranslate z).toFun x * b0 x) = 0 := by
    rcases hbranch with ⟨g, hg⟩ | hzero
    · exact Or.inl ⟨g.untranslate z,
        congrArg (fun h : H1Function (translateSet z U) => h.untranslate z) hg⟩
    · refine Or.inr ?_
      have hint : (∫ x in U, (f.untranslate z).toFun x * b0 x)
          = (∫ x in translateSet z U, f.toFun x * b x) :=
        setIntegral_comp_addRight_translateSet z U (fun x => f.toFun x * b x)
      rw [hint]
      exact hzero
  have key := hmain m b0 hcoeff hb coeff haeff M hM hmass (f.untranslate z) branch'
  rw [volume_translateSet_eq z U, ← goodCube_weighted_lintegral_untranslate z U b p0 f,
    ← goodCube_weighted_energy_untranslate z U b f]
  exact key

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
