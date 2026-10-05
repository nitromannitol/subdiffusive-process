module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.FinitePResidualLift
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.MassiveTranslation

@[expose] public section

/-!
# Finite-exponent residual lifts on translated cubes

Translation reduces the massive residual problem on a cube centered at an
arbitrary point to the centered-cube Calderón--Zygmund construction.  A bounded
measurable source and a bounded solution give the exponent `2d` required by the
Hölder-`1/2` interior estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The finite-exponent massive-residual lift on a cube centered at any point. -/
theorem exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn_translateSet
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) (z : Vec d) {m : ℤ}
    {c rho : Vec d → ℝ} {mu rhoMax : ℝ}
    {u : H1Function (translateSet z (openCubeSet (originCube d m)))}
    {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (translateSet z (openCubeSet (originCube d m)))),
      |rho x| ≤ rhoMax)
    (hf : MemL2On (translateSet z (openCubeSet (originCube d m))) f)
    (hresidualq : MemLp (massiveResidual rho mu u f) q.exponent
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))))
    (hu : IsMassiveWeakSolutionOn c rho mu
      (translateSet z (openCubeSet (originCube d m))) u f) :
    ∃ g : Vec d → Vec d,
      IsMassiveResidualLiftOn rho mu (translateSet z (openCubeSet (originCube d m)))
          u f g ∧
        IsDivFormWeakSolutionOn c (translateSet z (openCubeSet (originCube d m)))
          u g ∧
        MemLp (fun x ↦ HilbertVec.ofVec (g x)) q.exponent
          (volume.restrict (translateSet z (openCubeSet (originCube d m)))) := by
  have hmp := measurePreserving_addRight_restrict_translateSet z
    (openCubeSet (originCube d m))
  have hrhoMeas0 : AEStronglyMeasurable (fun x ↦ rho (x + z))
      (volume.restrict (openCubeSet (originCube d m))) :=
    hrhoMeas.comp_measurePreserving hmp
  have hrhoBdd0 : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |rho (x + z)| ≤ rhoMax :=
    hmp.quasiMeasurePreserving.ae hrhoBdd
  have hf0 : MemL2On (openCubeSet (originCube d m)) (fun x ↦ f (x + z)) :=
    hf.comp_measurePreserving hmp
  have hresidual0 : MemLp
      (massiveResidual (fun x ↦ rho (x + z)) mu
        (H1Function.untranslate z u) (fun x ↦ f (x + z))) q.exponent
      (volume.restrict (openCubeSet (originCube d m))) :=
    hresidualq.comp_measurePreserving hmp
  obtain ⟨g0, hgLift0, _hgWeak0, hgLp0⟩ :=
    exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn d q hq
      hrhoMeas0 hrhoBdd0 hf0 hresidual0
      (isMassiveWeakSolutionOn_untranslate z _ hu)
  have hgLift : IsMassiveResidualLiftOn rho mu
      (translateSet z (openCubeSet (originCube d m))) u f (fun x ↦ g0 (x - z)) := by
    have htranslated := isMassiveResidualLiftOn_translate z hgLift0
    intro phi
    simpa only [H1Function.translate_toFun, H1Function.untranslate_toFun,
      sub_add_cancel] using htranslated phi
  refine ⟨fun x ↦ g0 (x - z), hgLift,
    isDivFormWeakSolutionOn_of_isMassiveWeakSolutionOn hu hgLift, ?_⟩
  exact hgLp0.comp_measurePreserving
    (measurePreserving_subRight_restrict_translateSet z (openCubeSet (originCube d m)))

/-- A bounded massive solution with arbitrary bounded `L²` forcing has a
residual lift in the exponent `2d` on any translated cube. -/
theorem exists_schauder_divergence_lift_of_bounded_massiveWeakSolution_translateSet
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (z : Vec d) {m : ℤ}
    {c rho : Vec d → ℝ} {mu rhoMax U F : ℝ}
    {u : H1Function (translateSet z (openCubeSet (originCube d m)))}
    {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (translateSet z (openCubeSet (originCube d m)))),
      |rho x| ≤ rhoMax)
    (hf : MemL2On (translateSet z (openCubeSet (originCube d m))) f)
    (hfBound : ∀ᵐ x ∂(volume.restrict (translateSet z (openCubeSet (originCube d m)))),
      |f x| ≤ F)
    (huBound : ∀ᵐ x ∂(volume.restrict (translateSet z (openCubeSet (originCube d m)))),
      |u.toFun x| ≤ U)
    (hu : IsMassiveWeakSolutionOn c rho mu
      (translateSet z (openCubeSet (originCube d m))) u f) :
    ∃ g : Vec d → Vec d,
      IsMassiveResidualLiftOn rho mu (translateSet z (openCubeSet (originCube d m)))
          u f g ∧
        IsDivFormWeakSolutionOn c (translateSet z (openCubeSet (originCube d m)))
          u g ∧
        MemVectorLpOn (translateSet z (openCubeSet (originCube d m)))
          (2 * (d : ℝ)) g := by
  let q : FiniteLpExponent :=
    { exponent := ENNReal.ofReal (2 * (d : ℝ))
      one_lt := by
        rw [ENNReal.one_lt_ofReal]
        exact_mod_cast (show 1 < 2 * d by omega)
      lt_top := ENNReal.ofReal_lt_top }
  have hqReal : q.exponent.toReal = 2 * (d : ℝ) := by
    change (ENNReal.ofReal (2 * (d : ℝ))).toReal = 2 * (d : ℝ)
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hq : 2 < q.exponent.toReal := by
    rw [hqReal]
    exact_mod_cast (show 2 < 2 * d by omega)
  let hcube := isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  let : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) :=
    hcube.isBoundedDomain.isFiniteMeasure_restrict_volume
  let : IsFiniteMeasure
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))) :=
    ⟨by simpa only [Measure.restrict_apply_univ, volume_translateSet_eq] using
      (measure_lt_top (volume.restrict (openCubeSet (originCube d m))) Set.univ)⟩
  have hdiff : MemL2On (translateSet z (openCubeSet (originCube d m)))
      (fun x ↦ f x - mu * u.toFun x) :=
    hf.sub (u.memL2.const_mul mu)
  have hresidualMeas : AEStronglyMeasurable (massiveResidual rho mu u f)
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))) :=
    hrhoMeas.mul hdiff.aestronglyMeasurable
  have hresidualBound : ∀ᵐ x
      ∂(volume.restrict (translateSet z (openCubeSet (originCube d m)))),
      ‖massiveResidual rho mu u f x‖ ≤ max rhoMax 0 * (F + |mu| * U) := by
    filter_upwards [hrhoBdd, hfBound, huBound] with x hrhoX hfX huX
    calc
      ‖massiveResidual rho mu u f x‖ =
          |rho x| * |f x - mu * u.toFun x| := by
        simp only [massiveResidual, Real.norm_eq_abs, abs_mul]
      _ ≤ max rhoMax 0 * (|f x| + |mu| * |u.toFun x|) := by
        apply mul_le_mul
        · exact hrhoX.trans (le_max_left _ _)
        · calc
            |f x - mu * u.toFun x| ≤ |f x| + |mu * u.toFun x| := abs_sub _ _
            _ = |f x| + |mu| * |u.toFun x| := by rw [abs_mul]
        · positivity
        · positivity
      _ ≤ max rhoMax 0 * (F + |mu| * U) := by gcongr
  have hresidualq : MemLp (massiveResidual rho mu u f) q.exponent
      (volume.restrict (translateSet z (openCubeSet (originCube d m)))) :=
    MemLp.of_bound hresidualMeas (max rhoMax 0 * (F + |mu| * U)) hresidualBound
  obtain ⟨g, hgLift, hgWeak, hgLp⟩ :=
    exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn_translateSet
      d q hq z hrhoMeas hrhoBdd hf hresidualq hu
  refine ⟨g, hgLift, hgWeak, ?_⟩
  simpa only [MemVectorLpOn, hqReal] using hgLp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
