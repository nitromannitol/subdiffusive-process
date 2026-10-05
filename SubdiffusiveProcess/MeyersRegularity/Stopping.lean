module

public import SubdiffusiveProcess.MeyersRegularity.Basic

@[expose] public section

/-! Interior Meyers regularity: Stopping. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

open CubeCalderonZygmund


/-- A weighted norm tail on a local measurable set is unchanged by zero extension from its parent. -/
theorem sqWeighted_tail_indicator_restrict {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {U S : Set α}
    (hU : MeasurableSet U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (f : α → E) (t : ℝ) :
    sqWeightedMeasure (U.indicator f) μ ({x | t < ‖U.indicator f x‖} ∩ S) =
      sqWeightedMeasure f (μ.restrict S) {x | t < ‖f x‖}  := by
  rw [sqWeightedMeasure_indicator_tail_inter_eq_of_subset hU hS hSU]
  change (μ.withDensity (fun x => ENNReal.ofReal (‖f x‖^2)))
    ({x | t < ‖f x‖} ∩ S) =
    ((μ.restrict S).withDensity (fun x => ENNReal.ofReal (‖f x‖^2)))
      {x | t < ‖f x‖}
  rw [← restrict_withDensity hS, Measure.restrict_apply' hS]


theorem exists_stopping_family {d : ℕ} [NeZero d] {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (depth : ℕ) (f : Vec d → F) (g : Vec d → G) (eps M level R : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (heps : 0 < eps) (hM : 1 ≤ M) (hR : 0 < R)
    (hlevel : Real.sqrt (((2 * (R / (10 * (3 : ℝ)^depth)))^d)⁻¹ *
      ((∫ y, ‖f y‖^2 ∂volume) + eps⁻¹^2 * ∫ y, ‖g y‖^2 ∂volume)) < level)
    (target : Set (Vec d)) (htarget : ∀ x ∈ target, M * level < ‖f x‖) :
    ∃ D : Set (Vec d), ∃ radius : Vec d → ℝ, volume Dᶜ = 0 ∧
      ∀ x ∈ target ∩ D, 0 < radius x ∧
        radius x ≤ R / (10 * (3 : ℝ)^depth) ∧
        goodLambdaCombinedEnergy f g eps x (radius x) = level ∧
        ∀ s ∈ Icc (radius x) R, goodLambdaCombinedEnergy f g eps x s ≤ level := by
  have hf_int : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hg_int : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  let rho : ℝ := R / (10 * (3 : ℝ) ^ depth)
  have hdenom : 0 < 10 * (3 : ℝ) ^ depth := by positivity
  have hrho : 0 < rho := div_pos hR hdenom
  have hdenom_one : 1 ≤ 10 * (3 : ℝ) ^ depth := by
    have hpow : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
    nlinarith
  have hrhoR : rho ≤ R := by
    exact div_le_self hR.le hdenom_one
  have hcutoff :
      Real.sqrt (((2 * rho) ^ d)⁻¹ *
        ((∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume)) < level := by
    simpa only [rho] using hlevel
  have hlevel_pos : 0 < level :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have heps_weight_pos : 0 < (eps⁻¹) ^ (2 : ℕ) := by
    exact sq_pos_of_pos (inv_pos.mpr heps)
  have hlarge : ∀ x : Vec d, ∀ s ∈ Icc rho R,
      goodLambdaCombinedEnergy f g eps x s ≤ level := by
    intro x s hs
    exact (goodLambdaCombinedEnergy_le_globalIntegral f g eps hf_int hg_int x hrho hs.1).trans
      hcutoff.le
  let D : Set (Vec d) := {x |
    Tendsto (fun r => goodLambdaCombinedEnergy f g eps x r) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2)))}
  have hDae : ∀ᵐ x ∂volume, x ∈ D := by
    simpa only [D, mem_ofPred_eq] using
      (ae_tendsto_goodLambdaCombinedEnergy_nhdsGT f g eps hf_int hg_int)
  have hDnull : volume Dᶜ = 0 := by
    simpa only [D, mem_ofPred_eq, compl_ofPred] using (ae_iff.mp hDae)
  have hpoint : ∀ x ∈ target ∩ D,
      level < Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2) := by
    intro x hx
    have htail : M * level < ‖f x‖ := htarget x hx.1
    have hlevel_le_tail : level ≤ M * level := by
      nlinarith
    have hlevel_norm : level < ‖f x‖ := hlevel_le_tail.trans_lt htail
    calc
      level < ‖f x‖ := hlevel_norm
      _ = Real.sqrt (‖f x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact le_add_of_nonneg_right (mul_nonneg heps_weight_pos.le (sq_nonneg _))
  have hstop : ∀ x ∈ target ∩ D, ∃ r, 0 < r ∧ r ≤ rho ∧
      goodLambdaCombinedEnergy f g eps x r = level ∧
      ∀ s ∈ Icc r R, goodLambdaCombinedEnergy f g eps x s ≤ level := by
    intro x hx
    exact exists_stoppingRadius_goodLambdaCombinedEnergy_of_largeScaleBound
      f g eps hf_int hg_int x hrho hx.2 (hpoint x hx)
      (hlarge x rho ⟨le_rfl, hrhoR⟩) (hlarge x)
  classical
  let radius : Vec d → ℝ := fun x =>
    if hx : x ∈ target ∩ D then Classical.choose (hstop x hx) else 0
  refine ⟨D, radius, hDnull, ?_⟩
  intro x hx
  have hchosen := Classical.choose_spec (hstop x hx)
  rw [show radius x = Classical.choose (hstop x hx) by
    simp only [radius, dite_eq_left hx]]
  simpa only [rho] using hchosen


theorem one_level_tail {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (hq : 2 < q.exponent.toReal) {U S : Set (Vec d)} (hU : IsOpen U)
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    {eps M level R : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hM : 1 ≤ M) (hR : 0 < R) (u : H1Function U) (H : Vec d → Vec d)
    (hH : MemVectorL2 U H) (hweak : SmoothEquation H u)
    (hparent : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ R / (10 * (3 : ℝ)^depth) →
      axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) ⊆ U)
    (hcutoff : Real.sqrt (((2 * (R / (10 * (3 : ℝ)^depth)))^d)⁻¹ *
      ((∫ y, ‖openParentGradientExtension U u y‖^2 ∂volume) +
        eps⁻¹^2 * ∫ y, ‖hilbertifyVecField (openParentDatumExtension U H) y‖^2 ∂volume))
      < level) :
    sqWeightedMeasure (gradientField u) (volume.restrict S)
        {x | M * level < ‖gradientField u x‖} ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2)) *
        (sqWeightedMeasure (gradientField u) (volume.restrict U)
            {x | level/2 < ‖gradientField u x‖} + ENNReal.ofReal (eps⁻¹^2) *
          sqWeightedMeasure (hilbertifyVecField H) (volume.restrict U)
            {x | eps * level/2 < ‖hilbertifyVecField H x‖}) := by
  have hmain :
      sqWeightedMeasure (openParentGradientExtension U u) volume
        ({x | M * level < ‖openParentGradientExtension U u x‖} ∩ S) ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2)) *
        (sqWeightedMeasure (openParentGradientExtension U u) volume
            ({x | level/2 < ‖openParentGradientExtension U u x‖} ∩ U) +
          ENNReal.ofReal (eps⁻¹^2) *
          sqWeightedMeasure (hilbertifyVecField (openParentDatumExtension U H)) volume
            ({x | eps*level/2 < ‖hilbertifyVecField (openParentDatumExtension U H) x‖} ∩ U)) := by
    let Q : Set (Vec d) := S
    let F : Vec d → HilbertVec d := openParentGradientExtension U u
    let Hext : Vec d → Vec d := openParentDatumExtension U H
    let gext : Vec d → HilbertVec d := hilbertifyVecField Hext
    have hUmeas : MeasurableSet U := hU.measurableSet
    have hF : MemLp F 2 volume := by
      change MemLp (U.indicator (hilbertifyVecField u.grad)) 2 volume
      rw [MeasureTheory.memLp_indicator_iff_restrict hUmeas]
      exact memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
    have hHext : MemLp (hilbertifyVecField Hext) 2 volume := by
      rw [show hilbertifyVecField Hext =
        U.indicator (hilbertifyVecField H) by
          simpa only [Hext] using
            hilbertifyVecField_openParentDatumExtension U H]
      rw [MeasureTheory.memLp_indicator_iff_restrict hUmeas]
      exact memHilbertVectorL2_hilbertifyVecField hH
    have hgext : MemLp gext 2 volume := hHext
    have hcutoff' :
        Real.sqrt (((2 * (R /
          (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
          ((∫ y, ‖F y‖ ^ (2 : ℕ) ∂volume) +
            (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖gext y‖ ^ (2 : ℕ) ∂volume)) < level := by
      simpa only [F, Hext, gext] using hcutoff
    have hlevel_pos : 0 < level :=
      lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff'
    let T : Set (Vec d) := {x | M * level < ‖F x‖} ∩ Q
    obtain ⟨D, radius, hDnull, hradius⟩ :=
      exists_stopping_family depth F gext eps M level R hF hgext heps hM hR
        hcutoff' T (by intro x hx; exact hx.1)
    let K : ℝ≥0∞ := oneStoppingBallCoefficient depth G *
      (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
        ENNReal.ofReal (eps ^ (2 : ℕ)))
    have hvitali : sqWeightedMeasure F volume (T ∩ D) ≤
        K * oneStoppingBallTailControl F gext eps level U := by
      apply measure_le_mul_measure_of_vitali_stopping_family
        (sqWeightedMeasure F volume) (oneStoppingBallTailControl F gext eps level)
        (T ∩ D) U radius
        (R / (10 * (3 : ℝ) ^ depth)) 5 K
      · intro x hx
        exact (hradius x hx).2.1
      · intro x hx
        exact (hradius x hx).1
      · norm_num
      · intro x hx
        obtain ⟨hr, hcutoffx, hstop, hlast⟩ := hradius x hx
        have hxQ : x ∈ S := hx.1.2
        have hsub := hparent x hxQ (radius x) hr hcutoffx
        obtain ⟨_hF, _hHext, hlocalF, hlocalweak⟩ :=
          openParent_axisCube_inputs (sigma0 := (1 : ℝ)) hU hsub u H hH (by simpa only [one_mul, SmoothEquation] using hweak)
        have hball := sqWeightedMeasure_oneStoppingBall_le G hq x hr zero_lt_one
          heps heps1 (lt_of_lt_of_le zero_lt_one hM) hlevel_pos hcutoffx
          F Hext hF hHext
          (openParentLocalSolution U (stoppingComparisonParentCorner x (radius x) depth)
            (stoppingComparisonParentSide (radius x) depth) u hsub)
          (by simpa only [F] using hlocalF)
          (by simpa only [Hext] using hlocalweak)
          (by simpa only [gext, inv_one, one_smul] using hstop)
          (by simpa only [gext, inv_one, one_smul] using hlast)
        have hmono :
            sqWeightedMeasure F volume ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
              sqWeightedMeasure F volume
                ({y | M * level < ‖F y‖} ∩ Metric.closedBall x (5 * radius x)) := by
          apply measure_mono
          intro y hy
          exact ⟨hy.1.1.1, hy.2⟩
        calc
          sqWeightedMeasure F volume
              ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
              sqWeightedMeasure F volume
                ({y | M * level < ‖F y‖} ∩
                  Metric.closedBall x (5 * radius x)) := hmono
          _ ≤ K *
              (sqWeightedMeasure F volume
                  ({y | level / 2 < ‖F y‖} ∩ Metric.closedBall x (radius x)) +
                ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
                  sqWeightedMeasure gext volume
                    ({y | eps * level / 2 < ‖gext y‖} ∩
                      Metric.closedBall x (radius x))) := by
                simpa only [K, gext, inv_one, one_smul] using hball
          _ = K * oneStoppingBallTailControl F gext eps level
              (Metric.closedBall x (radius x)) := by
                rw [oneStoppingBallTailControl_apply F gext eps level
                  measurableSet_closedBall]
      · intro y hy
        rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
        obtain ⟨hr, hcutoffx, _hstop, _hlast⟩ := hradius x hx
        have hsub := hparent x hx.1.2 (radius x) hr hcutoffx
        apply hsub
        rw [stoppingComparisonParent_axisCube_eq_ball x hr depth]
        have hpow : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
        have hmult : 1 < stoppingComparisonParentMultiplier depth := by
          rw [stoppingComparisonParentMultiplier]
          nlinarith
        exact Metric.closedBall_subset_ball (lt_mul_of_one_lt_left hr hmult) hyx
    have hnuD : sqWeightedMeasure F volume Dᶜ = 0 :=
      MeasureTheory.withDensity_absolutelyContinuous volume _ hDnull
    have hTD : sqWeightedMeasure F volume (T ∩ D) =
        sqWeightedMeasure F volume T :=
      MeasureTheory.measure_inter_conull hnuD
    have hkappa : oneStoppingBallTailControl F gext eps level U =
        sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure gext volume
              ({x | eps * level / 2 < ‖gext x‖} ∩ U) :=
      oneStoppingBallTailControl_apply_ambient F gext eps level hUmeas
    change sqWeightedMeasure F volume T ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure gext volume
              ({x | eps * level / 2 < ‖gext x‖} ∩ U))
    calc
      sqWeightedMeasure F volume T =
          sqWeightedMeasure F volume (T ∩ D) := hTD.symm
      _ ≤ K * oneStoppingBallTailControl F gext eps level U := hvitali
      _ = K *
          (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
              sqWeightedMeasure gext volume
                ({x | eps * level / 2 < ‖gext x‖} ∩ U)) := by
            rw [hkappa]
      _ = oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ))) *
          (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ U) +
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
              sqWeightedMeasure gext volume
                ({x | eps * level / 2 < ‖gext x‖} ∩ U)) := by
            rfl
  have hext : hilbertifyVecField (openParentDatumExtension U H) =
      U.indicator (hilbertifyVecField H) :=
    hilbertifyVecField_openParentDatumExtension U H
  change sqWeightedMeasure (U.indicator (gradientField u)) volume
      ({x | M * level < ‖U.indicator (gradientField u) x‖} ∩ S) ≤ _ at hmain
  rw [sqWeighted_tail_indicator_restrict hU.measurableSet hS hSU] at hmain
  change _ ≤ (_ * _) * (sqWeightedMeasure (U.indicator (gradientField u)) volume
      ({x | level/2 < ‖U.indicator (gradientField u) x‖} ∩ U) + _) at hmain
  rw [sqWeighted_tail_indicator_restrict hU.measurableSet hU.measurableSet Subset.rfl,
    hext, sqWeighted_tail_indicator_restrict hU.measurableSet hU.measurableSet Subset.rfl] at hmain
  exact hmain


end SubdiffusiveProcess.MeyersRegularity
