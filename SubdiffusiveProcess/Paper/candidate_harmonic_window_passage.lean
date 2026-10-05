module

public import SubdiffusiveProcess.Paper.candidate_harmonic_comparison_passage
public import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

@[expose] public section

/-!+# Passing a finite-cutoff harmonic window to the candidate

The deterministic harmonic window, convergence of its error and reference
coefficient, and one uniformly convergent source bank give the exact limiting
comparison. The stochastic extraction of that source bank is separate.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The harmonic window passes along one uniformly convergent source bank with the same physical normalization. -/
theorem candidate_harmonic_window_passage
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Sob : SobolevFoundationalInput d hd)
    (I : in_J d) (alpha beta s Charm E0 : ℝ)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (hCharm : 0 ≤ Charm)
    (hwindow : aux_in_deterministic_core_harm_window d I alpha s Charm E0)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omN : ℕ → BilateralField d) (N : ℕ → ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (uN : ℕ → weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hsolve : ∀ n, ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H (omN n) (N n) Qcentre hQside)
        (uN n).val psi.val = sobolevVolumeLoad fL2 psi.val)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUNc : ∀ n, ContinuousOn (UN n) (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hUNr : ∀ n, ((uN n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] UN n)
    (hUp : MemLp U 2 (volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (hUlim : TendstoUniformlyOn UN U atTop
      (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (l : ℤ) (hrl : r = (3 : ℝ) ^ (-l))
    (hUtrace : IsHolderOn beta
      (frontier (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (SpatialCoordinates d))) U)
    (w : SpatialCoordinates d)
    (hpad : Metric.closedBall c (r / 18) ⊆ Metric.ball w (27 * r / 2))
    (hqdQ : Metric.ball w (27 * r / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (aN : ℕ → ℝ) (a : ℝ) (haN : ∀ n, 0 < aN n) (ha : 0 < a)
    (haLim : Tendsto aN atTop (𝓝 a))
    (errLim epshom Ctotal fsup : ℝ) (hfsup : 0 ≤ fsup)
    (hfbound : ∀ᵐ x ∂volume.restrict (Metric.ball w (27 * r / 2)), |f x| ≤ fsup)
    (hErrLim : Tendsto (fun n => I.err c r hr
      (cutoffPositiveCoefficient M H (omN n) (N n) c hr) c r (aN n) s 2)
        atTop (𝓝 errLim))
    (hErrSmall : errLim < E0) (hErrCoeff : Charm * errLim ≤ epshom)
    (hCtotal : Charm ≤ Ctotal) :
    let qc := centeredCube c (r / 81) (div_pos hr (by norm_num))
    let qi : Set (SpatialCoordinates d) := Metric.ball c (r / 1458)
    let qo : Set (SpatialCoordinates d) := Metric.ball c (r / 18)
    ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
      ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (qc : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
      (∀ psi : killedSobolevGraph qc,
        inner ℝ (sobolevGradient v.val) (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
      normalizedL2On qi (fun x => U x - V x) ≤
        epshom * normalizedL2On qo
          (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
        Ctotal * (r / 9) ^ 2 * a⁻¹ * fsup := by
  let qc := centeredCube c (r / 81) (div_pos hr (by norm_num))
  let qi : Set (SpatialCoordinates d) := Metric.ball c (r / 1458)
  let qo : Set (SpatialCoordinates d) := Metric.ball c (r / 18)
  let qd : Set (SpatialCoordinates d) := Metric.ball w (27 * r / 2)
  let err : ℕ → ℝ := fun n => I.err c r hr
    (cutoffPositiveCoefficient M H (omN n) (N n) c hr) c r (aN n) s 2
  have hqi : qi ⊆ (qc : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hqcQ : closure (qc : Set (SpatialCoordinates d)) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    have hqc : closure (qc : Set (SpatialCoordinates d)) ⊆ Metric.closedBall c (r / 18) :=
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
        (Metric.closedBall_subset_closedBall (by linarith only [hr]))
    exact hqc.trans (hpad.trans hqdQ)
  have hqoQ : qo ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_closedBall.trans (hpad.trans hqdQ)
  have hqiQ := hqi.trans (subset_closure.trans hqcQ)
  have hUNp : ∀ n, MemLp (UN n) 2 (volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :=
    fun n => (Lp.memLp (uN n).val.1).ae_eq (hUNr n)
  have hqotop : volume qo ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hqitop : volume qi ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hqopos : 0 < volume.real qo := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume c (div_pos hr (by norm_num)))) hqotop
  have hqipos : 0 < volume.real qi := ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_ball_pos volume c (div_pos hr (by norm_num)))) hqitop
  have hp : 0 < (d : ℝ) / (1 - alpha) :=
    div_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)) (sub_pos.mpr halpha.2)
  let hfinite : IsFiniteMeasure (volume.restrict qd) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact Metric.isBounded_ball.measure_lt_top⟩
  have hfnorm : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict qd)).toReal / (volume.real qd) ^ (1 / ((d : ℝ) / (1 - alpha))) ≤ fsup := by
    have hn := normalized_eLpNorm_le_of_ae_bound (volume.restrict qd) _ hp f fsup hfsup hfbound
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (hf.mono_measure (Measure.restrict_mono hqdQ le_rfl)).aestronglyMeasurable] at hn
    simpa only [Measure.restrict_apply_univ, measureReal_def] using hn
  let oscN : ℕ → ℝ := fun n => normalizedL2On qo
    (fun x => UN n x - (volume.real qo)⁻¹ * ∫ y in qo, UN n y)
  let osc : ℝ := normalizedL2On qo
    (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y)
  have hosc : Tendsto oscN atTop (𝓝 osc) :=
    tendsto_centered_normalizedL2_of_tendstoUniformlyOn qo Metric.isOpen_ball.measurableSet
      hqopos hqotop UN U
      (fun n => (hUNp n).mono_measure (Measure.restrict_mono hqoQ le_rfl))
      (hUp.mono_measure (Measure.restrict_mono hqoQ le_rfl))
      (hUlim.mono (hqoQ.trans subset_closure))
  let BN : ℕ → ℝ := fun n => Charm * err n * oscN n + Charm * (r / 9) ^ 2 * (aN n)⁻¹ * fsup
  let B : ℝ := Charm * errLim * osc + Charm * (r / 9) ^ 2 * a⁻¹ * fsup
  have hBN : Tendsto BN atTop (𝓝 B) :=
    ((hErrLim.const_mul Charm).mul hosc).add
      (((haLim.inv₀ ha.ne').const_mul (Charm * (r / 9) ^ 2)).mul_const fsup)
  have hbank : ∀ᶠ n in atTop,
      ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
        ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
        (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (qc : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = UN n x) ∧
        (∀ psi : killedSobolevGraph qc,
          inner ℝ (sobolevGradient v.val) (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
        normalizedL2On qi (fun x => UN n x - V x) ≤ BN n := by
    filter_upwards [hErrLim.eventually_lt_const hErrSmall] with n hn
    obtain ⟨v, V, hVc, hVr, hVt, hVh, hVb⟩ :=
      hwindow M H (omN n) (N n) Qcentre Qside hQside f hf fL2 hfL2
        (uN n) (hsolve n) (UN n) (hUNc n) (hUNr n)
        c r hr l hrl w hpad hqdQ (aN n) (haN n) hn.le
    refine ⟨v, V, hVc, hVr, hVt, hVh, hVb.trans ?_⟩
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfnorm
      (mul_nonneg (mul_nonneg hCharm (sq_nonneg _)) (inv_nonneg.mpr (haN n).le)))
  obtain ⟨v, V, hVc, hVr, hVt, hVh, hVb⟩ :=
    candidate_harmonic_comparison_passage hd Sob beta hbeta c (r / 81)
      (div_pos hr (by norm_num)) UN U hUtrace
      (hUlim.mono (hqcQ.trans subset_closure)) qi hqi Metric.isOpen_ball.measurableSet hqipos hqitop
      (fun n => (hUNp n).mono_measure (Measure.restrict_mono hqiQ le_rfl))
      (hUp.mono_measure (Measure.restrict_mono hqiQ le_rfl)) BN B hBN hbank
  refine ⟨v, V, hVc, hVr, hVt, hVh, hVb.trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_right hErrCoeff (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCtotal (sq_nonneg _)) (inv_nonneg.mpr ha.le)) hfsup)

end SubdiffusiveProcess.Paper
