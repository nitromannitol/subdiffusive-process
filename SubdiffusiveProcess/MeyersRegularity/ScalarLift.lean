module

public import SubdiffusiveProcess.MeyersRegularity.Basic
public import SubdiffusiveProcess.Analysis.RawLp
public import Homogenization.Sobolev.W1p.CubeVector
public import Homogenization.Sobolev.Foundations.PoincareW1p.Core
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessian
public import Homogenization.Sobolev.W1p.H1GradientUpgrade
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ScalarDivergenceLift

@[expose] public section

/-! Interior Meyers regularity: ScalarLift. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

private theorem cube_memLp_raw {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E} {p : ℝ≥0∞}
    (hf : MemLp f p (normalizedCubeMeasure Q)) :
    MemLp f p (volume.restrict (openCubeSet Q)) := by
  have hm := ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff p f).mp
    (by simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hf)
  simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet] using hm

private theorem cube_norm_bound_raw {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (Q : TriadicCube d) (p : FiniteLpExponent) (f : Vec d → E) (g : Vec d → F)
    (C : ℝ≥0∞) (hb : SubdiffusiveProcess.RawLp.eLpNorm f p.exponent (normalizedCubeMeasure Q) ≤
      C * SubdiffusiveProcess.RawLp.eLpNorm g p.exponent (normalizedCubeMeasure Q)) :
    SubdiffusiveProcess.RawLp.eLpNorm f p.exponent (volume.restrict (openCubeSet Q)) ≤
      C * SubdiffusiveProcess.RawLp.eLpNorm g p.exponent (volume.restrict (openCubeSet Q)) := by
  have hp0 : p.exponent ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans p.one_lt)
  simp only [SubdiffusiveProcess.RawLp.eLpNorm, if_neg hp0, if_neg p.lt_top.ne] at hb ⊢
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    eLpNorm'_smul_measure ENNReal.toReal_nonneg,
    eLpNorm'_smul_measure ENNReal.toReal_nonneg] at hb
  have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  apply (ENNReal.mul_le_mul_iff_right
    (by simp only [ne_eq, ENNReal.rpow_eq_zero_iff]; simp [hc0])
    (ENNReal.rpow_ne_top_of_ne_zero hc0 ENNReal.ofReal_ne_top)).mp
  simpa only [mul_left_comm, mul_assoc] using hb

private theorem eLpNorm_hilbertify_le_sum {d : ℕ} {μ : Measure (Vec d)}
    (f : Vec d → Vec d) (p : FiniteLpExponent)
    (hf : ∀ i, MemLp (fun x => f x i) p.exponent μ) :
    eLpNorm (hilbertifyVecField f) p.exponent μ ≤
      ∑ i : Fin d, eLpNorm (fun x => f x i) p.exponent μ := by
  classical
  let single : Fin d → Vec d → HilbertVec d := fun i x => HilbertVec.ofVec (Pi.single i (f x i))
  have hm : ∀ i, MemLp (single i) p.exponent μ := by
    intro i
    apply MemLp.of_eval_piLp
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [single, HilbertVec.ofVec, PiLp.toLp_apply, Pi.single_eq_same] using hf i
    · simpa only [single, HilbertVec.ofVec, PiLp.toLp_apply,
        Pi.single_eq_of_ne (Ne.symm hij)] using (MemLp.zero' (p := p.exponent) (μ := μ) :
          MemLp (fun _ : Vec d => (0 : ℝ)) p.exponent μ)
  have heq : hilbertifyVecField f = ∑ i : Fin d, single i := by
    funext x
    ext j
    simp [single, hilbertifyVecField]
  rw [heq]
  calc
    _ ≤ ∑ i : Fin d, eLpNorm (single i) p.exponent μ :=
      eLpNorm_sum_le p.one_lt.le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply eLpNorm_congr_norm_ae (hm i).aestronglyMeasurable (hf i).aestronglyMeasurable
      filter_upwards with x
      simp only [single, HilbertVec.ofVec, PiLp.norm_toLp_single]

private theorem exists_cube_scalar_gradient_estimate (d : ℕ) [NeZero d]
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Vec d → ℝ,
      MemLp f 2 (volume.restrict (openCubeSet (originCube d 2))) →
      MemLp f (ENNReal.ofReal p) (volume.restrict (openCubeSet (originCube d 2))) →
      ∀ u : H10Function (openCubeSet (originCube d 2)),
      CubeDirichletWeakPoissonProblem (originCube d 2) u f →
      MemLp (hilbertifyVecField u.toH1Function.grad) (ENNReal.ofReal p)
          (volume.restrict (openCubeSet (originCube d 2))) ∧
        (eLpNorm (hilbertifyVecField u.toH1Function.grad) (ENNReal.ofReal p)
          (volume.restrict (openCubeSet (originCube d 2)))).toReal ≤
            C * (eLpNorm f (ENNReal.ofReal p)
              (volume.restrict (openCubeSet (originCube d 2)))).toReal := by
  classical
  let q : FiniteLpExponent := ⟨ENNReal.ofReal p, by simpa only [ENNReal.one_lt_ofReal] using hp,
    ENNReal.ofReal_lt_top⟩
  let Q := originCube d 2
  obtain ⟨Cz, hCz, hcz⟩ := CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d q
  obtain ⟨Cp, hCp, hpc⟩ := W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) hp
  refine ⟨Cp * (d : ℝ) * (d : ℝ) * Cz.toReal, by positivity, ?_⟩
  intro f hf2 hfp u heq
  have hf2n : MemLp f 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hf2.smul_measure ENNReal.ofReal_ne_top
  have hfpn : MemLp f q.exponent (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hfp.smul_measure ENNReal.ofReal_ne_top
  obtain ⟨H, hH, hb⟩ := hcz 2 f hf2n hfpn u heq
  let M : Vec d → HilbertMat d := fun x => HilbertMat.ofMat (fun i j => H.hess i j x)
  have hM : MemLp M q.exponent (volume.restrict (openCubeSet Q)) := cube_memLp_raw Q hH
  have hbraw : eLpNorm M q.exponent (volume.restrict (openCubeSet Q)) ≤
      Cz * eLpNorm f q.exponent (volume.restrict (openCubeSet Q)) :=
    by
      have hb0 : SubdiffusiveProcess.RawLp.eLpNorm M q.exponent (normalizedCubeMeasure Q) ≤
          Cz * SubdiffusiveProcess.RawLp.eLpNorm f q.exponent (normalizedCubeMeasure Q) := by
        rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (by simpa only [M] using! hH.aestronglyMeasurable),
          SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfpn.aestronglyMeasurable]
        exact hb
      have hraw := cube_norm_bound_raw Q q M f Cz hb0
      rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hM.aestronglyMeasurable,
        SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfp.aestronglyMeasurable] at hraw
      exact hraw
  have hbR : (eLpNorm M q.exponent (volume.restrict (openCubeSet Q))).toReal ≤
      Cz.toReal * (eLpNorm f q.exponent (volume.restrict (openCubeSet Q))).toReal := by
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top hCz.ne hfp.eLpNorm_ne_top) hbraw
  let W : Fin d → W1pFunction (openCubeSet Q) q.exponent := fun i =>
    (H.gradCoordH1Function i).toW1pOfGradMemLp (isOpenBoundedConvexDomain_openCubeSet Q) q
      (fun j => (hM.eval_piLp i).eval_piLp j)
  have hmean : ∀ i : Fin d, MeanZeroOn (openCubeSet Q) (W i).toFun := by
    intro i
    exact congrFun (IsPotentialZeroTraceOn.integral_eq_zero u.isPotentialZeroTraceOn) i
  have hcoord : ∀ i : Fin d,
      (eLpNorm (fun x => u.toH1Function.grad x i) q.exponent
        (volume.restrict (openCubeSet Q))).toReal ≤
      Cp * (d : ℝ) * (eLpNorm M q.exponent (volume.restrict (openCubeSet Q))).toReal := by
    intro i
    have hpi := hpc (W i)
    rw [(W i).subAverageLpSeminorm_eq_valueLpSeminorm_of_meanZero (hmean i)] at hpi
    have hentries : ∀ j : Fin d,
        (eLpNorm (fun x => H.hess i j x) q.exponent (volume.restrict (openCubeSet Q))).toReal ≤
          (eLpNorm M q.exponent (volume.restrict (openCubeSet Q))).toReal := by
      intro j
      apply ENNReal.toReal_mono hM.eLpNorm_ne_top
      have hmeas : AEStronglyMeasurable (fun x => H.hess i j x)
          (volume.restrict (openCubeSet Q)) := by
        have hc : Continuous (fun A : HilbertMat d => A i j) := by fun_prop
        simpa only [M, HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply] using!
          hc.comp_aestronglyMeasurable hM.aestronglyMeasurable
      apply eLpNorm_mono hmeas
      intro x
      exact (HilbertVec.abs_apply_le_norm (M x i) j).trans (PiLp.norm_apply_le (M x) i)
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentries j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc
      _ ≤ Cp * ∑ j : Fin d, (eLpNorm (fun x => H.hess i j x) q.exponent
          (volume.restrict (openCubeSet Q))).toReal := hpi
      _ ≤ Cp * ((d : ℝ) * (eLpNorm M q.exponent (volume.restrict (openCubeSet Q))).toReal) :=
        mul_le_mul_of_nonneg_left hsum hCp
      _ = _ := by ring
  have hcoords : ∀ i, MemLp (fun x => u.toH1Function.grad x i) q.exponent
      (volume.restrict (openCubeSet Q)) := fun i => (W i).memLp
  have hg : MemLp (hilbertifyVecField u.toH1Function.grad) q.exponent
      (volume.restrict (openCubeSet Q)) := MemLp.of_eval_piLp hcoords
  refine ⟨hg, ?_⟩
  have hsumtop : (∑ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) q.exponent
      (volume.restrict (openCubeSet Q))) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (hcoords i).eLpNorm_ne_top)
  have hgrad := ENNReal.toReal_mono hsumtop
    (eLpNorm_hilbertify_le_sum u.toH1Function.grad q hcoords)
  rw [ENNReal.toReal_sum (fun i _ => (hcoords i).eLpNorm_ne_top)] at hgrad
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc
    _ ≤ (d : ℝ) * (Cp * (d : ℝ) * (eLpNorm M q.exponent (volume.restrict (openCubeSet Q))).toReal) :=
      hgrad.trans hsum
    _ ≤ (d : ℝ) * (Cp * (d : ℝ) * (Cz.toReal * (eLpNorm f q.exponent
        (volume.restrict (openCubeSet Q))).toReal)) := by gcongr
    _ = _ := by ring

theorem exists_scalar_divergence_lift (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Vec d → ℝ,
      MemLp h (ENNReal.ofReal p) (volume.restrict (unitBall d 2)) →
      ∃ H : Vec d → Vec d,
        MemLp (hilbertifyVecField H) (ENNReal.ofReal p)
          (volume.restrict (unitBall d (3/2))) ∧
        (eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p)
          (volume.restrict (unitBall d (3/2)))).toReal ≤
          C * (eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal ∧
        ∀ phi : H10Function (unitBall d (3/2)),
          (∫ x in unitBall d (3/2), h x * phi.toH1Function.toFun x) =
            -∫ x in unitBall d (3/2), vecDot (H x) (phi.toH1Function.grad x) := by
  letI : NeZero d := ⟨by omega⟩
  let Q := originCube d 2
  have hBQ : unitBall d 2 ⊆ openCubeSet Q := by
    intro x hx
    have hx' := Meyers.eBall_subset_ball (0 : Vec d) (by norm_num : (0 : ℝ) < 2) hx
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0 : ℝ) < 2)] at hx'
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi := hx' i
    simp only [Real.dist_eq, Pi.zero_apply, sub_zero, abs_lt] at hi
    norm_num
    constructor <;> linarith [hi.1, hi.2]
  have hB12 : unitBall d (3/2) ⊆ unitBall d 2 := Meyers.eBall_mono _ (by norm_num) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := exists_cube_scalar_gradient_estimate d p (by linarith)
  refine ⟨C + 1, by positivity, ?_⟩
  intro h hh
  let f := (unitBall d 2).indicator h
  have hfp : MemLp f (ENNReal.ofReal p) (volume.restrict (openCubeSet Q)) :=
    ((MeasureTheory.memLp_indicator_iff_restrict (Meyers.measurableSet_eBall _ _)).mpr hh).restrict _
  have hf2 : MemLp f 2 (volume.restrict (openCubeSet Q)) := hfp.mono_exponent
    (by exact_mod_cast ENNReal.ofReal_le_ofReal hp)
  obtain ⟨v, hv⟩ := SubdiffusiveProcess.CoarseGrainingVocab.exists_isScalarDirichletSolutionOn_one
    (Q := Q) (hD := (0 : H1Function (openCubeSet Q))) hf2
  obtain ⟨w, hvalue, hgrad⟩ := hv.1
  have hweak : CubeDirichletWeakPoissonProblem Q w f := by
    intro phi
    have heq := hv.2 phi
    simp_rw [hgrad] at heq
    simp only [Pi.zero_apply, H1Function.zero_grad, zero_add] at heq
    simp_rw [show ∀ x : Vec d, matVecMul (1 : Mat d) (w.toH1Function.grad x) =
      w.toH1Function.grad x from fun x => Matrix.one_mulVec _] at heq
    exact heq
  obtain ⟨hg, hgbound⟩ := hbound f hf2 hfp w hweak
  let H : Vec d → Vec d := fun x => -w.toH1Function.grad x
  have hneg : hilbertifyVecField H = -hilbertifyVecField w.toH1Function.grad := by
    funext x
    ext i
    simp [H, hilbertifyVecField]
  have hHraw : MemLp (hilbertifyVecField H) (ENNReal.ofReal p)
      (volume.restrict (openCubeSet Q)) := by rw [hneg]; exact hg.neg
  have hHsmall := hHraw.mono_measure (Measure.restrict_mono (hB12.trans hBQ) le_rfl)
  refine ⟨H, hHsmall, ?_, ?_⟩
  · have hnormf : eLpNorm f (ENNReal.ofReal p) (volume.restrict (openCubeSet Q)) =
        eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2)) := by
      change eLpNorm ((unitBall d 2).indicator h) (ENNReal.ofReal p)
        (volume.restrict (openCubeSet Q)) = _
      rw [eLpNorm_indicator_eq_eLpNorm_restrict (Meyers.measurableSet_eBall _ _),
        Measure.restrict_restrict_of_subset hBQ]
    calc
      _ ≤ (eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p)
          (volume.restrict (openCubeSet Q))).toReal := ENNReal.toReal_mono hHraw.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono (hB12.trans hBQ) le_rfl))
      _ = (eLpNorm (hilbertifyVecField w.toH1Function.grad) (ENNReal.ofReal p)
          (volume.restrict (openCubeSet Q))).toReal := by rw [hneg, eLpNorm_neg]
      _ ≤ C * (eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal :=
        by rw [← hnormf]; exact hgbound
      _ ≤ (C + 1) * (eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal := by
        nlinarith [ENNReal.toReal_nonneg (a := eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2)))]
  · intro phi
    let psi := phi.extendByZeroToOpenSuperset (Meyers.measurableSet_eBall _ _)
      (isOpen_openCubeSet Q) (hB12.trans hBQ)
    have hl : (fun x => f x * psi.toH1Function.toFun x) =
        (unitBall d (3/2)).indicator (fun x => h x * phi.toH1Function.toFun x) := by
      funext x
      by_cases hx : x ∈ unitBall d (3/2)
      · simp only [psi, H10Function.extendByZeroToOpenSuperset_toFun,
          H10Function.zeroExtension_apply_of_mem _ hx, f, Set.indicator_of_mem (hB12 hx),
          Set.indicator_of_mem hx]
      · simp only [psi, H10Function.extendByZeroToOpenSuperset_toFun,
          H10Function.zeroExtension_apply_of_not_mem _ hx, Set.indicator_of_notMem hx, mul_zero]
    have hr : (fun x => vecDot (w.toH1Function.grad x) (psi.toH1Function.grad x)) =
        (unitBall d (3/2)).indicator (fun x => vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)) := by
      funext x
      by_cases hx : x ∈ unitBall d (3/2)
      · simp only [psi, H10Function.extendByZeroToOpenSuperset_grad,
          H10Function.zeroExtensionGrad_apply_of_mem _ hx, Set.indicator_of_mem hx]
      · simp only [psi, H10Function.extendByZeroToOpenSuperset_grad,
          H10Function.zeroExtensionGrad_apply_of_not_mem _ hx, Set.indicator_of_notMem hx, vecDot_zero_right]
    have heq := hweak psi
    rw [hl, hr, integral_indicator (Meyers.measurableSet_eBall _ _),
      integral_indicator (Meyers.measurableSet_eBall _ _),
      Measure.restrict_restrict_of_subset (hB12.trans hBQ)] at heq
    rw [← heq]
    simp only [H, vecDot_neg_left, integral_neg, neg_neg]


end SubdiffusiveProcess.MeyersRegularity
