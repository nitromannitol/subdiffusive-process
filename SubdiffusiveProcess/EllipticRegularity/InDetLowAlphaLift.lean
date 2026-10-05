module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.TranslatedFinitePResidualLift
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP

@[expose] public section

/-!
# Residual lifts in `L^{2d}` from a finite-exponent residual

GMC's lift `exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn` builds the vector lift as
`CubeVectorW1pFunction.ofWeakHessian` from a Calderón–Zygmund Hessian in `L^q`, but publishes
only `g ∈ L^q`. Re-running its construction exposes the `W^{1,q}` coordinates of the lift; for
`q ≥ 2d/3` the finite-exponent cube Sobolev embedding (`cubeSobolevEmbedding_finiteLp`,
`W^{1,2d/3} ⊂ L^{2d}`) then gives `g ∈ L^{2d}`, the exponent of the Hölder-`1/2`
small-contrast Schauder representative.
-/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- An open triadic cube is an open axis cube. -/
theorem aux_in_deterministic_lowalpha_openCubeSet_eq_axisCube {d : ℕ}
    (Q : Homogenization.TriadicCube d) :
    openCubeSet Q =
      axisCube (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  have hupper : ∀ j : Fin d,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := fun j => by ring
  simp_rw [hupper]

/-- **Sobolev embedding `W^{1,p} ⊂ L^{2d}` on an open triadic cube**, `p ≥ 2d/3`, `d ≥ 2`. -/
theorem aux_in_deterministic_lowalpha_w1p_memLp_twoD {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    {p : ℝ≥0∞} (hp : ENNReal.ofReal (2 * (d : ℝ) / 3) ≤ p)
    (u : W1pFunction (openCubeSet Q) p) :
    MemLp u.toFun (ENNReal.ofReal (2 * (d : ℝ))) (volume.restrict (openCubeSet Q)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  let pE : FiniteLpExponent :=
    { exponent := ENNReal.ofReal (2 * (d : ℝ) / 3)
      one_lt := by rw [ENNReal.one_lt_ofReal]; linarith
      lt_top := ENNReal.ofReal_lt_top }
  let qE : FiniteLpExponent :=
    { exponent := ENNReal.ofReal (2 * (d : ℝ))
      one_lt := by rw [ENNReal.one_lt_ofReal]; linarith
      lt_top := ENNReal.ofReal_lt_top }
  have hpR : pE.exponent.toReal = 2 * (d : ℝ) / 3 := by
    change (ENNReal.ofReal (2 * (d : ℝ) / 3)).toReal = _
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hqR : qE.exponent.toReal = 2 * (d : ℝ) := by
    change (ENNReal.ofReal (2 * (d : ℝ))).toReal = _
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hpd : pE.exponent.toReal < d := by rw [hpR]; linarith
  have hpq : (qE.exponent.toReal)⁻¹ = pE.exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [hpR, hqR]
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  set z : Homogenization.Vec d :=
    fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q with hz
  set L : ℝ := cubeScaleFactor Q with hL
  have hLpos : 0 < L := by
    rw [hL, cubeScaleFactor]; exact zpow_pos (by norm_num) _
  have hax : openCubeSet Q = axisCube z L :=
    aux_in_deterministic_lowalpha_openCubeSet_eq_axisCube Q
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain.isFiniteMeasure_restrict_volume
  have hmem : MemLp u.toFun pE.exponent (volume.restrict (axisCube z L)) := by
    rw [← hax]; exact u.memLp.mono_exponent hp
  have hgrad : ∀ i : Fin d, MemLp (fun x => u.grad x i) pE.exponent
      (volume.restrict (axisCube z L)) := by
    intro i; rw [← hax]; exact (u.gradMemLp i).mono_exponent hp
  let v : W1pFunction (axisCube z L) pE.exponent :=
    { toFun := u.toFun
      grad := u.grad
      memLp := hmem
      gradMemLp := hgrad
      hasWeakGradient := by rw [← hax]; exact u.hasWeakGradient }
  obtain ⟨C, -, hC⟩ := cubeSobolevEmbedding_finiteLp hd0 pE hpd
  have hbound := hC qE hpq z L hLpos v
  have hfin : (C : ℝ≥0∞) *
      ((∑ i : Fin d, eLpNorm (fun x => v.grad x i) pE.exponent
          (volumeMeasureOn (axisCube z L))) +
        ENNReal.ofReal L⁻¹ * eLpNorm v.toFun pE.exponent (volumeMeasureOn (axisCube z L)))
      < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.sum_lt_top.2 fun i _ => (hgrad i).eLpNorm_lt_top
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmem.eLpNorm_lt_top
  have hq : MemLp u.toFun qE.exponent (volume.restrict (axisCube z L)) :=
    lt_of_le_of_lt hbound hfin
  have hrestr : volume.restrict (openCubeSet Q) = volume.restrict (axisCube z L) := by
    rw [hax]
  rw [hrestr]
  exact hq

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- **The GMC residual lift, with its `L^{2d}` bound exposed** (centered cube).  The
construction is that of `exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn`; the
extra conclusion comes from the `W^{1,q}` coordinates of `CubeVectorW1pFunction.ofWeakHessian`
and the cube Sobolev embedding, for `q ≥ 2d/3`. -/
theorem _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_lowalpha_lift_twoD
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) (hq3 : ENNReal.ofReal (2 * (d : ℝ) / 3) ≤ q.exponent)
    {m : ℤ} {c rho : Vec d → ℝ}
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
          MemLp (fun x ↦ HilbertVec.ofVec (g x)) (ENNReal.ofReal (2 * (d : ℝ)))
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
  rw [memLp_piLp_iff]
  intro i
  have hi := _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_lowalpha_w1p_memLp_twoD hd Q hq3 (V.coord i)
  simpa [g, HilbertVec.ofVec] using! hi.neg

/-- **The translated-cube residual lift, with its `L^{2d}` bound exposed.**  Same statement as
GMC's `exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn_translateSet`, with the
extra hypothesis `q ≥ 2d/3` and the stronger conclusion `g ∈ L^{2d}`. -/
theorem _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_lowalpha_lift_twoD_translateSet
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) (hq3 : ENNReal.ofReal (2 * (d : ℝ) / 3) ≤ q.exponent)
    (z : Vec d) {m : ℤ}
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
        MemVectorLpOn (translateSet z (openCubeSet (originCube d m))) (2 * (d : ℝ)) g := by
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
    _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_lowalpha_lift_twoD d hd q hq hq3
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

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
