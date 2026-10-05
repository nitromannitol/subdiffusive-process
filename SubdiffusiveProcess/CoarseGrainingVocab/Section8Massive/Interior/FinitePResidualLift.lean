module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.WeakEquationBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.C0CompactSupportExtension
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianAboveTwo
public import Homogenization.Sobolev.W1p.CubeVector

@[expose] public section

/-!
# Finite-exponent lifts of the massive residual

The scalar massive residual is solved by the constant-coefficient Dirichlet
Poisson problem.  The finite-exponent Calderón--Zygmund endpoint upgrades the
Poisson gradient to the vector `Lᵖ` carrier required by the inhomogeneous
small-contrast Schauder estimate.

## References

* `s.fixed.coefficient` and `mfd:sec-speed` (the massive residual).
* `s.fixed.coefficient` and `mfd:sec-speed` (interior regularity input).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped CompactlySupported ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- A massive residual in a finite `Lᵖ` space has a vector divergence lift
in the same `Lᵖ` space.  The lift also converts the massive equation to the
divergence-form weak equation consumed by the Schauder row. -/
theorem exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) {m : ℤ} {c rho : Vec d → ℝ}
    {mu rhoMax : ℝ} {u : H1Function (openCubeSet (originCube d m))}
    {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho
      (volume.restrict (openCubeSet (originCube d m))))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |rho x| ≤ rhoMax)
    (hf : MemL2On (openCubeSet (originCube d m)) f)
    (hresidualq : MemLp (massiveResidual rho mu u f) q.exponent
      (volume.restrict (openCubeSet (originCube d m))))
    (hu : IsMassiveWeakSolutionOn c rho mu
      (openCubeSet (originCube d m)) u f) :
    ∃ g : Vec d → Vec d,
      IsMassiveResidualLiftOn rho mu (openCubeSet (originCube d m)) u f g ∧
        IsDivFormWeakSolutionOn c (openCubeSet (originCube d m)) u g ∧
          MemLp (fun x ↦ HilbertVec.ofVec (g x)) q.exponent
            (volume.restrict (openCubeSet (originCube d m))) := by
  let Q : TriadicCube d := originCube d m
  let F : Vec d → ℝ := massiveResidual rho mu u f
  have hF2 : MemL2On (openCubeSet Q) F := by
    have hdiff : MemL2On (openCubeSet Q) (fun x ↦ f x - mu * u.toFun x) :=
      hf.sub (u.memL2.const_mul mu)
    exact memL2On_mul_of_bounded hrhoMeas hrhoBdd hdiff
  obtain ⟨w, hw⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_isScalarDirichletSolutionOn_one
      (Q := Q) (hD := (0 : H1Function (openCubeSet Q))) hF2
  obtain ⟨w0, _hwValue, hwGrad⟩ := hw.1
  have hwPoisson : CubeDirichletWeakPoissonProblem Q w0 F := by
    intro phi
    have heq := hw.2 phi
    simp_rw [hwGrad] at heq
    simp only [Pi.zero_apply, H1Function.zero_grad, zero_add] at heq
    simp_rw [show ∀ x : Vec d, matVecMul (1 : Mat d) (w0.toH1Function.grad x) =
        w0.toH1Function.grad x from fun x ↦ Matrix.one_mulVec _] at heq
    exact heq
  have hF2Normalized : MemLp F 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hF2.smul_measure ENNReal.ofReal_ne_top
  have hFqNormalized : MemLp F q.exponent (normalizedCubeMeasure Q) := by
    have hrestricted : MemLp F q.exponent
        (cubeBoundedMeasurableDomain Q).restrictedVolume := by
      simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet,
        Q, F] using hresidualq
    have hnormalized := ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff
      q.exponent F).mpr hrestricted
    simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using hnormalized
  obtain ⟨C, _hCtop, hC⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_two_lt
      d q hq
  obtain ⟨H, hHmem, _hHbound⟩ :=
    hC m F hF2Normalized hFqNormalized w0 (by simpa only [Q] using hwPoisson)
  have hrows : ∀ i : Fin d,
      MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
        (normalizedCubeMeasure Q) := by
    rw [memLp_piLp_iff] at hHmem
    intro i
    simpa only [Function.comp_apply, HilbertMat.ofMat, PiLp.toLp_apply] using hHmem i
  let V : CubeVectorW1pFunction Q q := CubeVectorW1pFunction.ofWeakHessian H hrows
  let g : Vec d → Vec d := fun x ↦ -V.toField x
  have hpairing : ∀ phi : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, F x * phi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet Q, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
    intro phi
    have heq := hwPoisson phi
    rw [← heq]
    simp only [g, V, CubeVectorW1pFunction.ofWeakHessian_toField, vecDot_neg_left]
    rw [integral_neg, neg_neg]
  have hLift : IsMassiveResidualLiftOn rho mu (openCubeSet Q) u f g :=
    isMassiveResidualLiftOn_of_integral_pairing hrhoMeas hrhoBdd hf hpairing
  refine ⟨g, hLift, isDivFormWeakSolutionOn_of_isMassiveWeakSolutionOn hu hLift, ?_⟩
  have hVnormalized := V.euclideanMemLp
  have hVcube := memLp_cubeMeasure_of_memLp_normalizedCubeMeasure Q hVnormalized
  rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hVcube
  simpa only [g, Q, HilbertVec.ofVec, Pi.neg_def] using! hVcube.neg

/-- In dimension at least two, a locally bounded massive solution with compact
forcing has a residual lift in the precise exponent `2d` used by the
`alpha = 1/2` Schauder estimate. -/
theorem exists_schauder_divergence_lift_of_bounded_massiveWeakSolution
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) {m : ℤ} {c rho : Vec d → ℝ}
    {mu rhoMax U : ℝ} {u : H1Function (openCubeSet (originCube d m))}
    (f : C_c(Vec d, ℝ))
    (hrhoMeas : AEStronglyMeasurable rho
      (volume.restrict (openCubeSet (originCube d m))))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |rho x| ≤ rhoMax)
    (huBound : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |u.toFun x| ≤ U)
    (hu : IsMassiveWeakSolutionOn c rho mu
      (openCubeSet (originCube d m)) u f) :
    ∃ g : Vec d → Vec d,
      IsMassiveResidualLiftOn rho mu (openCubeSet (originCube d m)) u f g ∧
        IsDivFormWeakSolutionOn c (openCubeSet (originCube d m)) u g ∧
          MemVectorLpOn (openCubeSet (originCube d m)) (2 * (d : ℝ)) g := by
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
  have hfL2 : MemL2On (openCubeSet (originCube d m)) f :=
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
  have hdiff : MemL2On (openCubeSet (originCube d m))
      (fun x ↦ f x - mu * u.toFun x) :=
    hfL2.sub (u.memL2.const_mul mu)
  have hresidualMeas : AEStronglyMeasurable (massiveResidual rho mu u f)
      (volume.restrict (openCubeSet (originCube d m))) :=
    hrhoMeas.mul hdiff.aestronglyMeasurable
  have hresidualBound : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      ‖massiveResidual rho mu u f x‖ ≤
        max rhoMax 0 * (‖compactSupportToC0 f‖ + |mu| * U) := by
    filter_upwards [hrhoBdd, huBound] with x hrhoX huX
    have hfX := BoundedContinuousFunction.norm_coe_le_norm
      (ZeroAtInftyContinuousMap.toBCF (compactSupportToC0 f)) x
    change |f x| ≤ ‖compactSupportToC0 f‖ at hfX
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
      _ ≤ max rhoMax 0 * (‖compactSupportToC0 f‖ + |mu| * U) := by
        gcongr
  have hresidualq : MemLp (massiveResidual rho mu u f) q.exponent
      (volume.restrict (openCubeSet (originCube d m))) :=
    MemLp.of_bound hresidualMeas
      (max rhoMax 0 * (‖compactSupportToC0 f‖ + |mu| * U)) hresidualBound
  obtain ⟨g, hgLift, hgWeak, hgLp⟩ :=
    exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn
      d q hq hrhoMeas hrhoBdd hfL2 hresidualq hu
  refine ⟨g, hgLift, hgWeak, ?_⟩
  simpa only [MemVectorLpOn, hqReal] using hgLp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
