module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SphereQuarterNet

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ProbabilityTheory

noncomputable section


/-- The nonnegative response square, centered by its same-scale stationary
mean.  Keeping this centering explicit is essential: the mean is the third
term in the printed Rosenthal display. -/
noncomputable def centeredCutoffResponseSquareOnCube {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  cutoffResponseOnCube M L p q R omega ^ 2 -
    ∫ eta, cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta ^ 2
      ∂M.P.toMeasure

theorem measurable_centeredCutoffResponseSquareOnCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Measurable (centeredCutoffResponseSquareOnCube M L n p q R) :=
  (measurable_cutoffResponseOnCube M L p q R).pow_const 2 |>.sub measurable_const

theorem centeredCutoffResponseSquareOnCube_eq_originCube_translate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    centeredCutoffResponseSquareOnCube M L n p q R omega =
      centeredCutoffResponseSquareOnCube M L n p q (originCube d (n : ℤ))
        (translatePotentialSequence (triadicCubeShift R) omega) := by
  unfold centeredCutoffResponseSquareOnCube
  rw [cutoffResponseOnCube_eq_originCube_translate M L p q R omega, hRscale]

theorem integral_cutoffResponseOnCube_sq_eq_originCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    ∫ omega, cutoffResponseOnCube M L p q R omega ^ 2 ∂M.P.toMeasure =
      ∫ omega, cutoffResponseOnCube M L p q (originCube d R.scale) omega ^ 2
        ∂M.P.toMeasure := by
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    cutoffResponseOnCube M L p q (originCube d R.scale) omega ^ 2
  have hg : Measurable g :=
    (measurable_cutoffResponseOnCube M L p q
      (originCube d R.scale)).pow_const 2
  calc
    _ = ∫ omega, g (translatePotentialSequence (triadicCubeShift R) omega)
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [cutoffResponseOnCube_eq_originCube_translate M L p q R omega]
    _ = _ := by
      simpa [g, Function.comp_def] using! integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift R))
        (potentialSequenceLaw_stationary M (triadicCubeShift R)) g
        hg.aestronglyMeasurable

theorem integrable_cutoffResponseOnCube_sq_iff_originCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    Integrable (fun omega => cutoffResponseOnCube M L p q R omega ^ 2)
        M.P.toMeasure ↔
      Integrable (fun omega =>
        cutoffResponseOnCube M L p q (originCube d R.scale) omega ^ 2)
        M.P.toMeasure := by
  let T := translatePotentialSequence (triadicCubeShift R)
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    cutoffResponseOnCube M L p q (originCube d R.scale) omega ^ 2
  have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_translatePotentialSequence (triadicCubeShift R),
      potentialSequenceLaw_stationary M (triadicCubeShift R)⟩
  have hg : AEStronglyMeasurable g M.P.toMeasure :=
    ((measurable_cutoffResponseOnCube M L p q
      (originCube d R.scale)).pow_const 2).aestronglyMeasurable
  have hcomp := hT.integrable_comp hg
  have heq : (fun omega => cutoffResponseOnCube M L p q R omega ^ 2) = g ∘ T := by
    funext omega
    rw [cutoffResponseOnCube_eq_originCube_translate M L p q R omega]
    rfl
  rwa [← heq] at hcomp

theorem integral_abs_centeredCutoffResponseSquareOnCube_rpow_eq_originCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (xi : ℝ)
    (hxi : 0 ≤ xi) :
    ∫ omega, |centeredCutoffResponseSquareOnCube M L n p q R omega| ^ xi
        ∂M.P.toMeasure =
      ∫ omega,
        |centeredCutoffResponseSquareOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ xi ∂M.P.toMeasure := by
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    |centeredCutoffResponseSquareOnCube M L n p q
      (originCube d (n : ℤ)) omega| ^ xi
  have hg : Measurable g := by
    simpa only [g, Real.norm_eq_abs, Function.comp_def] using!
      (Real.continuous_rpow_const hxi).measurable.comp
        (measurable_centeredCutoffResponseSquareOnCube M L n p q
          (originCube d (n : ℤ))).norm
  calc
    _ = ∫ omega, g (translatePotentialSequence (triadicCubeShift R) omega)
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [centeredCutoffResponseSquareOnCube_eq_originCube_translate
        M L n p q R hRscale omega]
    _ = _ := by
      simpa [g, Function.comp_def] using! integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift R))
        (potentialSequenceLaw_stationary M (triadicCubeShift R)) g
        hg.aestronglyMeasurable

theorem integrable_abs_centeredCutoffResponseSquareOnCube_rpow_iff_originCube
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (hRscale : R.scale = (n : ℤ)) (xi : ℝ)
    (hxi : 0 ≤ xi) :
    Integrable
        (fun omega =>
          |centeredCutoffResponseSquareOnCube M L n p q R omega| ^ xi)
        M.P.toMeasure ↔
      Integrable
        (fun omega =>
          |centeredCutoffResponseSquareOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ xi) M.P.toMeasure := by
  let T := translatePotentialSequence (triadicCubeShift R)
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    |centeredCutoffResponseSquareOnCube M L n p q
      (originCube d (n : ℤ)) omega| ^ xi
  have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_translatePotentialSequence (triadicCubeShift R),
      potentialSequenceLaw_stationary M (triadicCubeShift R)⟩
  have hg : AEStronglyMeasurable g M.P.toMeasure := by
    have hmeas : Measurable g := by
      simpa only [g, Real.norm_eq_abs, Function.comp_def] using!
        (Real.continuous_rpow_const hxi).measurable.comp
          (measurable_centeredCutoffResponseSquareOnCube M L n p q
            (originCube d (n : ℤ))).norm
    exact hmeas.aestronglyMeasurable
  have hcomp := hT.integrable_comp hg
  have heq : (fun omega =>
      |centeredCutoffResponseSquareOnCube M L n p q R omega| ^ xi) = g ∘ T := by
    funext omega
    rw [centeredCutoffResponseSquareOnCube_eq_originCube_translate
      M L n p q R hRscale omega]
    rfl
  rwa [← heq] at hcomp

private theorem exists_centeredCutoffResponseSquare_thickenedLocal_ae_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (R : TriadicCube d) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((LocalSigmaR (Metric.thickening ε (cubeSet R))).comap
          (aCutoffRegCoeffField M L)) _ Y ∧
      centeredCutoffResponseSquareOnCube M L n p q R =ᵐ[M.P.toMeasure] Y := by
  let P := aCutoffRestrictionLaw M L
  let A := aCutoffRegCoeffField M L
  let hP := aCutoffRestrictionLaw_lawCarrier M L
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet R (-p, q) with
    ⟨Y0, hY0local, hY0eq⟩
  let Z : RegCoeffField d → ℝ := fun a => Y0 a - vecDot p q
  let c : ℝ := ∫ eta,
    cutoffResponseOnCube M L p q (originCube d (n : ℤ)) eta ^ 2
      ∂M.P.toMeasure
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => (Z (A omega)) ^ 2 - c
  refine ⟨Y, ?_, ?_⟩
  · have hZlocal : Ch04.IsRestrictionLocalRandomVariable
        (cubeSet R) (measurableSet_cubeSet R) Z := by
      simpa [Z] using! hY0local.sub
        (Ch04.IsRestrictionLocalRandomVariable.const (cubeSet R)
          (measurableSet_cubeSet R) (vecDot p q))
    have hcomp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        ((RestrictionSigmaR (cubeSet R) (measurableSet_cubeSet R)).comap A) _
        (fun omega => Z (A omega)) :=
      hZlocal.comp (Measurable.of_comap_le le_rfl)
    exact (hcomp.pow_const 2).sub measurable_const |>.mono
      (comap_restrictionSigmaR_le_comap_localSigmaR_thickening A
        (fun omega i j => by
          have hmat : Continuous (fun x : Vec d =>
              scalarMatrix (d := d)
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x)) :=
            (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).smul
              continuous_const
          exact (continuous_apply j).comp ((continuous_apply i).comp hmat))
        (cubeSet R) (measurableSet_cubeSet R) ε hε) le_rfl
  · have hresp :
        (fun a : RegCoeffField d => ResponseJ (cubeSet R) p q a.toFun) =ᵐ[P] Z := by
      exact (hP.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae R p q).trans
        (hY0eq.sub Filter.EventuallyEq.rfl)
    have hpull :
        (fun omega => ResponseJ (cubeSet R) p q (A omega).toFun) =ᵐ[M.P.toMeasure]
          fun omega => Z (A omega) := by
      exact ae_eq_comp (measurable_aCutoffRegCoeffField M L).aemeasurable
        (by simpa [P, aCutoffRestrictionLaw_eq_map, A] using! hresp)
    filter_upwards [hpull] with omega homega
    unfold centeredCutoffResponseSquareOnCube
    dsimp only [Y, c]
    rw [← homega]
    congr 2
    unfold cutoffResponseOnCube
    change ResponseJ (openCubeSet R) p q (A omega).toFun =
      ResponseJ (cubeSet R) p q (A omega).toFun
    exact (responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q
      (A omega).toFun).symm

/-- The literal nonuniform colored-Rosenthal bound for the centered square
observable.  Its first channel is the `xi`th response moment (at
`rho = xi/2`), while `moment X 2` is the centered fourth-moment channel. -/
theorem integral_abs_centeredCutoffResponseSquareAverage_rpow_root_le_rosenthal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (p q : Vec d) {rho : ℝ}
    (hrho : 2 ≤ rho)
    (hsq : Integrable
      (fun omega => cutoffResponseOnCube M L p q
        (originCube d (n : ℤ)) omega ^ 2) M.P.toMeasure)
    (hmoment : Integrable
      (fun omega =>
        |centeredCutoffResponseSquareOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ rho) M.P.toMeasure) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            centeredCutoffResponseSquareOnCube M L n p q R omega| ^ rho
          ∂M.P.toMeasure) ^ rho⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        ∑ c ∈ (descendantsAtScale
            (originCube d (m : ℤ)) (n : ℤ)).image cubeFreshShellColor,
          (2 * rho *
              (∑ R ∈ (descendantsAtScale
                  (originCube d (m : ℤ)) (n : ℤ)).filter
                    (fun Q => cubeFreshShellColor Q = c),
                ∫ omega,
                  |centeredCutoffResponseSquareOnCube M L n p q R omega| ^ rho
                    ∂M.P.toMeasure) ^ rho⁻¹ +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt rho * Real.sqrt
                (∑ R ∈ (descendantsAtScale
                    (originCube d (m : ℤ)) (n : ℤ)).filter
                      (fun Q => cubeFreshShellColor Q = c),
                  moment (centeredCutoffResponseSquareOnCube M L n p q R) 2
                    M.P.toMeasure))) := by
  classical
  let D := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  let X := centeredCutoffResponseSquareOnCube M L n p q
  have hmomentCell : ∀ R ∈ D,
      Integrable (fun omega => |X R omega| ^ rho) M.P.toMeasure := by
    intro R hR
    exact (integrable_abs_centeredCutoffResponseSquareOnCube_rpow_iff_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) rho
        (by linarith)).2 hmoment
  have hmeanCell : ∀ R ∈ D,
      ∫ omega, X R omega ∂M.P.toMeasure = 0 := by
    intro R hR
    have hscale := scale_eq_of_mem_descendantsAtScale hR
    have hsqR : Integrable
        (fun omega => cutoffResponseOnCube M L p q R omega ^ 2)
        M.P.toMeasure := by
      exact (integrable_cutoffResponseOnCube_sq_iff_originCube M L p q R).2
        (by simpa [hscale] using! hsq)
    rw [show X R = fun omega =>
        cutoffResponseOnCube M L p q R omega ^ 2 -
          ∫ eta, cutoffResponseOnCube M L p q
            (originCube d (n : ℤ)) eta ^ 2 ∂M.P.toMeasure by
      funext omega
      rfl]
    rw [integral_sub hsqR (integrable_const _), integral_const,
      probReal_univ, one_smul,
      integral_cutoffResponseOnCube_sq_eq_originCube M L p q R, hscale,
      sub_self]
  have hsum := integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal
    D cubeFreshShellColor hrho
    (by
      intro c _hc
      apply iIndepFun_cutoff_descendants_colorClass_of_ae_thickenedLocal
        M L n m hLn c X
      intro R _hR
      apply exists_centeredCutoffResponseSquare_thickenedLocal_ae_eq
        M L n p q R
      change 0 < (4 * ((d : ℝ) + 1))⁻¹
      positivity)
    (fun R _hR => measurable_centeredCutoffResponseSquareOnCube M L n p q R)
    hmomentCell hmeanCell
  have hscale := integral_abs_const_mul_rpow_rpow_inv
    (μ := M.P.toMeasure) (fun omega => ∑ R ∈ D, X R omega)
    (p := rho) (c := ((D.card : ℝ)⁻¹)) (by linarith) (by positivity)
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Rosenthal at exponent `xi/2` for the literal nonnegative square response.
The centered fluctuation and its nonzero stationary mean remain separate on
the right, matching all three terms in source. -/
theorem integral_abs_cutoffResponseSquareAverage_rpow_root_le_colored_rosenthal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (hLn : L ≤ n) (hnm : n ≤ m) (p q : Vec d) {rho K : ℝ}
    (hrho : 2 ≤ rho) (hK : 0 ≤ K)
    (hsq : Integrable
      (fun omega => cutoffResponseOnCube M L p q
        (originCube d (n : ℤ)) omega ^ 2) M.P.toMeasure)
    (hmoment : Integrable
      (fun omega =>
        |centeredCutoffResponseSquareOnCube M L n p q
          (originCube d (n : ℤ)) omega| ^ rho) M.P.toMeasure)
    (hroot :
      (∫ omega,
          |centeredCutoffResponseSquareOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤ K) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ rho
          ∂M.P.toMeasure) ^ rho⁻¹ ≤
      (((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        (2 * rho *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - rho⁻¹)) *
              ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) ^ rho⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt rho *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt
                  ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ) * K))) +
        ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure := by
  classical
  let D := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  let X := centeredCutoffResponseSquareOnCube M L n p q
  let mu2 : ℝ := ∫ omega,
    cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega ^ 2
      ∂M.P.toMeasure
  let A : ℝ := ((D.card : ℝ)⁻¹) *
    (2 * rho *
        ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - rho⁻¹)) *
          (D.card : ℝ) ^ rho⁻¹ * K) +
      4 * rosenthalBennettIntegralConst *
        (Real.sqrt rho *
          (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
            Real.sqrt (D.card : ℝ) * K)))
  have hrho0 : 0 < rho := by linarith
  have hmomentCell : ∀ R ∈ D,
      Integrable (fun omega => |X R omega| ^ rho) M.P.toMeasure := by
    intro R hR
    exact (integrable_abs_centeredCutoffResponseSquareOnCube_rpow_iff_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) rho
        (by linarith)).2 hmoment
  have hrootCell : ∀ R ∈ D,
      (∫ omega, |X R omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤ K := by
    intro R hR
    rw [integral_abs_centeredCutoffResponseSquareOnCube_rpow_eq_originCube
      M L n p q R (scale_eq_of_mem_descendantsAtScale hR) rho (by linarith)]
    exact hroot
  have hmeanCell : ∀ R ∈ D,
      ∫ omega, X R omega ∂M.P.toMeasure = 0 := by
    intro R hR
    have hscale := scale_eq_of_mem_descendantsAtScale hR
    have hsqR : Integrable
        (fun omega => cutoffResponseOnCube M L p q R omega ^ 2)
        M.P.toMeasure := by
      exact (integrable_cutoffResponseOnCube_sq_iff_originCube M L p q R).2
        (by simpa [hscale] using! hsq)
    rw [show X R = fun omega =>
        cutoffResponseOnCube M L p q R omega ^ 2 - mu2 by
      funext omega
      rfl]
    rw [integral_sub hsqR (integrable_const _), integral_const,
      probReal_univ, one_smul]
    dsimp only [mu2]
    rw [integral_cutoffResponseOnCube_sq_eq_originCube M L p q R, hscale,
      sub_self]
  have hcenter :
      (∫ omega,
          |((D.card : ℝ)⁻¹) * ∑ R ∈ D, X R omega| ^ rho
            ∂M.P.toMeasure) ^ rho⁻¹ ≤ A := by
    have hsum :
        (∫ omega, |∑ R ∈ D, X R omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤
          2 * rho *
              ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - rho⁻¹)) *
                (D.card : ℝ) ^ rho⁻¹ * K) +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt rho *
                (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                  Real.sqrt (D.card : ℝ) * K)) := by
      apply integral_abs_finsetSum_rpow_rpow_inv_le_colored_rosenthal_uniform
        D cubeFreshShellColor hrho hK
      · exact_mod_cast card_image_cubeFreshShellColor_le D
      · intro c _hc
        apply iIndepFun_cutoff_descendants_colorClass_of_ae_thickenedLocal
          M L n m hLn c X
        intro Q _hQ
        apply exists_centeredCutoffResponseSquare_thickenedLocal_ae_eq
          M L n p q Q
        change 0 < (4 * ((d : ℝ) + 1))⁻¹
        positivity
      · intro R _hR
        exact measurable_centeredCutoffResponseSquareOnCube M L n p q R
      · exact hmomentCell
      · exact hmeanCell
      · exact hrootCell
    have hscale := integral_abs_const_mul_rpow_rpow_inv
      (μ := M.P.toMeasure) (fun omega => ∑ R ∈ D, X R omega)
      (p := rho) (c := ((D.card : ℝ)⁻¹)) hrho0 (by positivity)
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hDnonempty : D.Nonempty := by
    apply descendantsAtScale_nonempty
    change (n : ℤ) ≤ (m : ℤ)
    exact_mod_cast hnm
  have hcard : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast hDnonempty.card_ne_zero
  let avgX : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    ((D.card : ℝ)⁻¹) * ∑ R ∈ D, X R omega
  let avgSq : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
      cutoffResponseOnCube M L p q R omega ^ 2
  have havg : avgSq = fun omega => avgX omega + mu2 := by
    funext omega
    dsimp only [avgSq, avgX, X]
    simp only [centeredCutoffResponseSquareOnCube, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    dsimp only [mu2]
    field_simp
    ring
  have hsumInt : Integrable
      (fun omega => |∑ R ∈ D, X R omega| ^ rho) M.P.toMeasure :=
    IndependentSums.integrable_abs_finsetSum_rpow (by linarith)
      (fun R hR => measurable_centeredCutoffResponseSquareOnCube M L n p q R)
      hmomentCell
  have hc0 : 0 ≤ ((D.card : ℝ)⁻¹) := by positivity
  have havgInt : Integrable (fun omega => |avgX omega| ^ rho)
      M.P.toMeasure := by
    have hscaled := hsumInt.const_mul (((D.card : ℝ)⁻¹) ^ rho)
    simpa only [avgX, abs_mul, abs_of_nonneg hc0,
      Real.mul_rpow hc0 (abs_nonneg _)] using! hscaled
  have hmu20 : 0 ≤ mu2 := by
    dsimp only [mu2]
    exact integral_nonneg fun _ => sq_nonneg _
  let B : Bool → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun b =>
    if b then fun _ => mu2 else avgX
  have hBmeas : ∀ b ∈ (Finset.univ : Finset Bool), Measurable (B b) := by
    intro b _
    cases b
    · dsimp only [B, avgX]
      exact measurable_const.mul (Finset.measurable_sum _ fun R _ =>
        measurable_centeredCutoffResponseSquareOnCube M L n p q R)
    · simp [B]
  have hBint : ∀ b ∈ (Finset.univ : Finset Bool),
      Integrable (fun omega => |B b omega| ^ rho) M.P.toMeasure := by
    intro b _
    cases b
    · simpa [B] using! havgInt
    · simp [B]
  have htriangle := IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_sum
    (μ := M.P.toMeasure) (p := rho) (f := B) (s := Finset.univ)
    (by linarith) hBmeas hBint
  have hsumfun : (fun omega => ∑ b ∈ (Finset.univ : Finset Bool), B b omega) =
      avgSq := by
    rw [havg]
    funext omega
    simp [B]
    ring
  have hconst :
      (∫ _omega, |mu2| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ = mu2 := by
    rw [integral_const, probReal_univ, one_smul, abs_of_nonneg hmu20,
      ← Real.rpow_mul hmu20, mul_inv_cancel₀ hrho0.ne', Real.rpow_one]
  have hconst' : (|mu2| ^ rho) ^ rho⁻¹ = mu2 := by
    rw [abs_of_nonneg hmu20, ← Real.rpow_mul hmu20,
      mul_inv_cancel₀ hrho0.ne', Real.rpow_one]
  have havgCenter :
      (∫ omega, |avgX omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤ A := by
    simpa only [avgX] using! hcenter
  simp_rw [congrFun hsumfun] at htriangle
  have hfinal :
      (∫ omega, |avgSq omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤
        A + mu2 := by
    have htri :
        (∫ omega, |avgSq omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤
          mu2 +
            (∫ omega, |avgX omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ := by
      simpa [B, hconst, hconst'] using! htriangle
    calc
      _ ≤ mu2 +
          (∫ omega, |avgX omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ := htri
      _ ≤ mu2 + A := by linarith
      _ = A + mu2 := add_comm _ _
  simpa only [D, avgSq, A, mu2] using! hfinal

/-! ## Moment conversion and numerical budget -/

/-- At exponent `rho = xi/2`, the `xi`th response moment controls both the
`rho`th centered-square channel and, by Lyapunov, its fourth-moment channel.
This is the literal square-observable conversion used in the second induction. -/
theorem centeredCutoffResponseSquare_root_le_two_mul_sq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    {rho delta1 : ℝ} (hrho : 1 ≤ rho)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ (2 * rho))
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ (2 * rho)
            ∂M.P.toMeasure) ^ (2 * rho)⁻¹ ≤ delta1) :
    Integrable
        (fun omega =>
          |centeredCutoffResponseSquareOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ rho) M.P.toMeasure ∧
      (∫ omega,
          |centeredCutoffResponseSquareOnCube M L n p q
            (originCube d (n : ℤ)) omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤
        2 * delta1 ^ 2 := by
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    cutoffResponseOnCube M L p q (originCube d (n : ℤ))
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => f omega ^ 2
  let c : ℝ := ∫ omega, Y omega ∂M.P.toMeasure
  have hrho0 : 0 < rho := zero_lt_one.trans_le hrho
  have htwoRho : 0 < 2 * rho := by positivity
  have hfmeas : Measurable f := measurable_cutoffResponseOnCube M L p q _
  have hYmeas : Measurable Y := hfmeas.pow_const 2
  have hpow : (fun omega => |Y omega| ^ rho) =
      fun omega => |f omega| ^ (2 * rho) := by
    funext omega
    dsimp only [Y]
    rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hYmoment : Integrable (fun omega => |Y omega| ^ rho) M.P.toMeasure := by
    rw [hpow]
    exact hmoment
  have hYrootEq :
      (∫ omega, |Y omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ =
        ((∫ omega, |f omega| ^ (2 * rho) ∂M.P.toMeasure) ^ (2 * rho)⁻¹) ^ 2 := by
    rw [hpow]
    let I : ℝ := ∫ omega, |f omega| ^ (2 * rho) ∂M.P.toMeasure
    have hI0 : 0 ≤ I := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    have hexp : rho⁻¹ = (2 * rho)⁻¹ * (2 : ℝ) := by field_simp
    change I ^ rho⁻¹ = (I ^ (2 * rho)⁻¹) ^ (2 : ℕ)
    rw [hexp, Real.rpow_mul hI0]
    exact Real.rpow_natCast _ 2
  have hYroot :
      (∫ omega, |Y omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤ delta1 ^ 2 := by
    rw [hYrootEq]
    exact pow_le_pow_left₀ (by positivity) hroot 2
  have hc0 : 0 ≤ c := by
    dsimp only [c, Y]
    exact integral_nonneg fun _ => sq_nonneg _
  have hc : c ≤ delta1 ^ 2 := by
    have hlow := IndependentSums.integral_abs_rpow_rpow_inv_le_of_le
      (f := Y) (q := (1 : ℝ)) (p := rho) (by norm_num) hrho hYmeas hYmoment
    have hY0 : ∀ omega, 0 ≤ Y omega := fun _ => sq_nonneg _
    have heq : ∫ omega, Y omega ∂M.P.toMeasure =
        ∫ omega, |Y omega| ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact (abs_of_nonneg (hY0 omega)).symm
    dsimp only [c]
    rw [heq]
    simpa only [Real.rpow_one, inv_one] using! hlow.trans hYroot
  have hcenterInt :=
    IndependentSums.integrable_abs_sub_integral_rpow_of_integrable_abs_rpow
      hrho hYmeas hYmoment
  refine ⟨by
    simpa [centeredCutoffResponseSquareOnCube, f, Y, c] using! hcenterInt, ?_⟩
  let X : Bool → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun b =>
    if b then fun _ => -c else Y
  have hXmeas : ∀ b ∈ (Finset.univ : Finset Bool), Measurable (X b) := by
    intro b _
    cases b <;> simp [X, hYmeas]
  have hXint : ∀ b ∈ (Finset.univ : Finset Bool),
      Integrable (fun omega => |X b omega| ^ rho) M.P.toMeasure := by
    intro b _
    cases b
    · simpa [X] using! hYmoment
    · simp [X]
  have hsum := IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_sum
    (μ := M.P.toMeasure) hrho hXmeas hXint
  have hconst :
      (∫ _omega, |-c| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ = c := by
    rw [integral_const, probReal_univ, one_smul, abs_neg, abs_of_nonneg hc0,
      ← Real.rpow_mul hc0, mul_inv_cancel₀ hrho0.ne', Real.rpow_one]
  have hconst' : (|c| ^ rho) ^ rho⁻¹ = c := by
    rw [abs_of_nonneg hc0, ← Real.rpow_mul hc0,
      mul_inv_cancel₀ hrho0.ne', Real.rpow_one]
  have hsumfun : (fun omega => ∑ b ∈ (Finset.univ : Finset Bool), X b omega) =
      fun omega => Y omega - c := by
    funext omega
    simp [X]
    ring
  simp_rw [congrFun hsumfun] at hsum
  have hsum' :
      (∫ omega, |Y omega - c| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ ≤
        c + (∫ omega, |Y omega| ^ rho ∂M.P.toMeasure) ^ rho⁻¹ := by
    simpa [X, hconst, hconst'] using! hsum
  simpa only [centeredCutoffResponseSquareOnCube, f, Y, c] using!
    hsum'.trans (by nlinarith [hc, hYroot])

private theorem squareResponseRosenthal_rhs_le_dimensional_sqrt_card
    {d : ℕ} {rho K N : ℝ} (hrho : 2 ≤ rho) (hK : 0 ≤ K) (hN : 1 ≤ N) :
    N⁻¹ *
        (2 * rho *
            ((((freshShellColorPeriod d ^ d : ℕ) : ℝ) ^ (1 - rho⁻¹)) *
              N ^ rho⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt rho *
              (Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
                Real.sqrt N * K))) ≤
      (2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
          4 * rosenthalBennettIntegralConst *
            Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ)) *
        rho * K * (Real.sqrt N)⁻¹ := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d072_responseRosenthal_rhs_le_dimensional_sqrt_card (d := d) (xi := rho) (K := K) (N := N) (hxi := hrho) (hK := hK) (hN := hN)

private theorem inv_sqrt_card_descendantsAtScale_originCube_eq_rpow_square
    {d n m : ℕ} (hnm : n ≤ m) :
    (Real.sqrt
      ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ))⁻¹ =
      Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d180_inv_sqrt_card_descendantsAtScale_originCube_eq_rpow (d := d) (n := n) (m := m) (hnm := hnm)

theorem aux_dedup_d113_square_logarithmic_rpow_decay_absorption
    {r gamma A eta C xi H : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hgamma : 0 < gamma)
    (hA : 0 ≤ A) (heta : 0 < eta) (hxi : 1 ≤ xi)
    (hC : (2 * A * eta⁻¹ + 1) *
      (-gamma * Real.log r)⁻¹ ≤ C)
    (hgap : C * Real.log (2 + xi) ≤ H) :
    A * xi * Real.rpow r (gamma * H) ≤ eta := by
  let x := 2 + xi
  let y := A * eta⁻¹
  let B := 2 * y + 1
  let lam := -gamma * Real.log r
  have hx : 2 ≤ x := by dsimp only [x]; linarith
  have hx0 : 0 < x := zero_lt_two.trans_le hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hB : 0 < B := by dsimp only [B]; linarith
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hlam : 0 < lam := by
    dsimp only [lam]
    nlinarith [mul_pos hgamma (neg_pos.mpr hlogr)]
  have hsep : B * Real.log x ≤ lam * H := by
    have hpre : B * lam⁻¹ * Real.log x ≤ H := by
      have hcoef : B * lam⁻¹ =
          (2 * A * eta⁻¹ + 1) * (-gamma * Real.log r)⁻¹ := by
        dsimp only [B, y, lam]
        ring
      calc
        B * lam⁻¹ * Real.log x ≤ C * Real.log x :=
          mul_le_mul_of_nonneg_right (by simpa only [hcoef] using! hC) hlogx
        _ ≤ H := by simpa only [x] using! hgap
    have hm := mul_le_mul_of_nonneg_left hpre hlam.le
    have hcancel : lam * (B * lam⁻¹ * Real.log x) = B * Real.log x := by
      field_simp [hlam.ne']
    nlinarith
  have hdecay : Real.rpow r (gamma * H) ≤ Real.rpow x (-B) := by
    rw [show Real.rpow r (gamma * H) =
        Real.exp (Real.log r * (gamma * H)) from
      Real.rpow_def_of_pos hr0 (gamma * H)]
    rw [show Real.rpow x (-B) = Real.exp (Real.log x * (-B)) from
      Real.rpow_def_of_pos hx0 (-B)]
    apply Real.exp_le_exp.mpr
    have hleft : Real.log r * (gamma * H) = -(lam * H) := by
      dsimp only [lam]
      ring
    rw [hleft]
    nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2x : (1 / 2 : ℝ) ≤ Real.log x :=
    hlog2.trans (Real.log_le_log (by norm_num) hx)
  have hpowY : y ≤ Real.rpow x (2 * y) := by
    rw [show Real.rpow x (2 * y) = Real.exp (Real.log x * (2 * y)) from
      Real.rpow_def_of_pos hx0 (2 * y)]
    calc
      y ≤ 1 + Real.log x * (2 * y) := by
        have h2y : 0 ≤ 2 * y := by positivity
        have hm : (1 / 2 : ℝ) * (2 * y) ≤ Real.log x * (2 * y) :=
          mul_le_mul_of_nonneg_right hlog2x h2y
        nlinarith
      _ ≤ Real.exp (Real.log x * (2 * y)) := by
        simpa only [add_comm] using! Real.add_one_le_exp (Real.log x * (2 * y))
  have hden : y * xi ≤ Real.rpow x B := by
    rw [show B = 1 + 2 * y by dsimp only [B]; ring]
    rw [show Real.rpow x (1 + 2 * y) =
        Real.rpow x 1 * Real.rpow x (2 * y) from
      Real.rpow_add hx0 1 (2 * y)]
    have hxone : Real.rpow x 1 = x := by
      change x ^ (1 : ℝ) = x
      exact Real.rpow_one x
    rw [hxone]
    calc
      y * xi ≤ x * y := by dsimp only [x]; nlinarith
      _ ≤ x * Real.rpow x (2 * y) :=
        mul_le_mul_of_nonneg_left hpowY hx0.le
  have hsmall : y * xi * Real.rpow x (-B) ≤ 1 := by
    rw [show Real.rpow x (-B) = (Real.rpow x B)⁻¹ from
      Real.rpow_neg hx0.le B]
    rw [show y * xi * (Real.rpow x B)⁻¹ =
        (Real.rpow x B)⁻¹ * (y * xi) by ring]
    exact (inv_mul_le_one₀ (Real.rpow_pos_of_pos hx0 B)).2 hden
  have hrewrite : A = eta * y := by
    dsimp only [y]
    field_simp [heta.ne']
  rw [hrewrite]
  calc
    eta * y * xi * Real.rpow r (gamma * H) ≤
        eta * (y * xi * Real.rpow x (-B)) := by
      have hm := mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg hy (by linarith : 0 ≤ xi))
      nlinarith
    _ ≤ eta := by simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left hsmall heta.le

private theorem square_logarithmic_rpow_decay_absorption
    {r gamma A eta C xi H : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hgamma : 0 < gamma)
    (hA : 0 ≤ A) (heta : 0 < eta) (hxi : 1 ≤ xi)
    (hC : (2 * A * eta⁻¹ + 1) *
      (-gamma * Real.log r)⁻¹ ≤ C)
    (hgap : C * Real.log (2 + xi) ≤ H) :
    A * xi * Real.rpow r (gamma * H) ≤ eta := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d113_square_logarithmic_rpow_decay_absorption (r := r) (gamma := gamma) (A := A) (eta := eta) (C := C) (xi := xi) (H := H) (hr0 := hr0) (hr1 := hr1) (hgamma := hgamma) (hA := hA) (heta := heta) (hxi := hxi) (hC := hC) (hgap := hgap)

/-- Per-direction budget after reserving the factor `4 * card(net)` needed to
recover the full unit-sphere supremum from the quarter net. -/
noncomputable def squareResponseQuarterNetEta (d : ℕ) : ℝ :=
  (288 * ((sphereQuarterNet d).points.card : ℝ))⁻¹

theorem squareResponseQuarterNetEta_pos {d : ℕ} [NeZero d] :
    0 < squareResponseQuarterNetEta d := by
  unfold squareResponseQuarterNetEta
  have hcard : 0 < ((sphereQuarterNet d).points.card : ℝ) := by
    exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
  positivity

/-- Dimension-only constant which simultaneously absorbs the colored spatial
fluctuation, the retained second mean, and the finite quarter-net factor in
the square-response update. -/
noncomputable def squareResponseAbsorptionConst (d : ℕ) : ℝ :=
  let A := 2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
    4 * rosenthalBennettIntegralConst *
      Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ)
  let eta := squareResponseQuarterNetEta d
  let Clog := (2 * A * eta⁻¹ + 1) *
    (-((d : ℝ) / 2) * Real.log (1 / 3 : ℝ))⁻¹
  max 72 (max eta⁻¹ Clog)

theorem squareResponseAbsorptionConst_seventyTwo_le (d : ℕ) :
    72 ≤ squareResponseAbsorptionConst d := by
  exact le_max_left _ _

theorem squareResponseQuarterNetEta_inv_le_absorptionConst (d : ℕ) :
    (squareResponseQuarterNetEta d)⁻¹ ≤ squareResponseAbsorptionConst d := by
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- Finite-moment side of the descendant square average.  This is kept
separate from the numerical Rosenthal bound so finite-net aggregation can
convert the real carrier back to `paperENNRealLpNorm`. -/
theorem integrable_abs_cutoffResponseSquareAverage_rpow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L n m : ℕ) (p q : Vec d) {xi : ℝ}
    (hxi : 2 ≤ xi)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure) :
    Integrable (fun omega =>
      |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
          cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2))
      M.P.toMeasure := by
  classical
  let D := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
  have hcell : ∀ R ∈ D, Integrable (fun omega =>
      |cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2))
      M.P.toMeasure := by
    intro R hR
    let T := translatePotentialSequence (triadicCubeShift R)
    let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
      |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
    have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
      ⟨measurable_translatePotentialSequence (triadicCubeShift R),
        potentialSequenceLaw_stationary M (triadicCubeShift R)⟩
    have hg : AEStronglyMeasurable g M.P.toMeasure := by
      exact ((Real.continuous_rpow_const (by linarith)).measurable.comp
        (measurable_cutoffResponseOnCube M L p q _).norm).aestronglyMeasurable
    have hcomp := hT.integrable_comp hg
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have heq : (fun omega =>
        |cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)) = g ∘ T := by
      funext omega
      rw [cutoffResponseOnCube_eq_originCube_translate M L p q R omega,
        hscale]
      dsimp only [g, T, Function.comp_apply]
      rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      ring_nf
    rw [heq]
    exact hcomp.2 hmoment
  have hsum : Integrable (fun omega =>
      |∑ R ∈ D, cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2))
      M.P.toMeasure := by
    apply IndependentSums.integrable_abs_finsetSum_rpow (by linarith)
    · intro R hR
      exact (measurable_cutoffResponseOnCube M L p q R).pow_const 2
    · exact hcell
  have hc0 : 0 ≤ ((D.card : ℝ)⁻¹) := by positivity
  have hscaled := hsum.const_mul (((D.card : ℝ)⁻¹) ^ (xi / 2))
  simpa only [D, abs_mul, abs_of_nonneg hc0,
    Real.mul_rpow hc0 (abs_nonneg _)] using! hscaled

/-- Source, including all numerical arithmetic.  The
`xi`-moment budget supplies the fourth moment by Lyapunov, logarithmic block
separation absorbs the colored spatial factor, and the first-induction
smallness absorbs the retained square mean. -/
theorem cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanBudget
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L n m h : ℕ) (hLn : L ≤ n) (hnm : n ≤ m) (hgap : m - n = h)
    (p q : Vec d) {xi delta1 : ℝ}
    (hxi : 4 ≤ xi)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
            ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1)
    (hmean :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        squareResponseQuarterNetEta d * delta1 ^ 2) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      2 * squareResponseQuarterNetEta d * delta1 ^ 2 := by
  let rho : ℝ := xi / 2
  let N : ℝ :=
    ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)
  let A : ℝ := 2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
    4 * rosenthalBennettIntegralConst *
      Real.sqrt ((freshShellColorPeriod d ^ d : ℕ) : ℝ)
  let eta : ℝ := squareResponseQuarterNetEta d
  let Clog : ℝ := (2 * A * eta⁻¹ + 1) *
    (-((d : ℝ) / 2) * Real.log (1 / 3 : ℝ))⁻¹
  have hrho : 2 ≤ rho := by dsimp only [rho]; linarith
  have hrho1 : 1 ≤ rho := by linarith
  have hxiEq : 2 * rho = xi := by dsimp only [rho]; ring
  have hcenter := centeredCutoffResponseSquare_root_le_two_mul_sq
    M L n p q hrho1 (by simpa only [hxiEq] using! hmoment)
      (by simpa only [hxiEq] using! hroot)
  have htwoMoment :=
    IndependentSums.integrable_abs_rpow_of_integrable_abs_rpow_of_le
      (μ := M.P.toMeasure)
      (f := cutoffResponseOnCube M L p q (originCube d (n : ℤ)))
      (q := (2 : ℝ)) (p := xi) (by norm_num) (by linarith)
      (measurable_cutoffResponseOnCube M L p q _) hmoment
  have hsq : Integrable
      (fun omega => cutoffResponseOnCube M L p q
        (originCube d (n : ℤ)) omega ^ 2) M.P.toMeasure := by
    simpa only [Real.rpow_two, sq_abs] using! htwoMoment
  have hraw := integral_abs_cutoffResponseSquareAverage_rpow_root_le_colored_rosenthal
    M L n m hLn hnm p q hrho (by positivity : 0 ≤ 2 * delta1 ^ 2)
      hsq hcenter.1 hcenter.2
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast (descendantsAtScale_nonempty (originCube d (m : ℤ))
      (by exact_mod_cast hnm : (n : ℤ) ≤ (m : ℤ))).card_pos
  have hsimp := squareResponseRosenthal_rhs_le_dimensional_sqrt_card
    (d := d) hrho (by positivity : 0 ≤ 2 * delta1 ^ 2) hN
  have hbase := hraw.trans (add_le_add hsimp le_rfl)
  rw [inv_sqrt_card_descendantsAtScale_originCube_eq_rpow_square hnm] at hbase
  have hdim : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) M.shellPrefix.dimension)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    have hRB : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst,
        Homogenization.IndependentSums.rosenthalBennettIntegralConst]
      positivity
    positivity
  have hClog : Clog ≤ squareResponseAbsorptionConst d := by
    dsimp only [squareResponseAbsorptionConst, Clog, A, eta]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hfluct0 :
      A * xi * Real.rpow (1 / 3 : ℝ) (((d : ℝ) / 2) * (h : ℝ)) ≤
        eta := by
    exact square_logarithmic_rpow_decay_absorption
      (by norm_num) (by norm_num) (by positivity) hA0
      (by simpa only [eta] using! squareResponseQuarterNetEta_pos (d := d))
      (by linarith)
      (by simpa only [Clog] using! hClog) hlog
  have hbaseEq :
      Real.rpow (1 / 3 : ℝ) (((d : ℝ) / 2) * (h : ℝ)) =
        Real.rpow 3 (-((d : ℝ) / 2) * (h : ℝ)) := by
    rw [show Real.rpow (1 / 3 : ℝ) (((d : ℝ) / 2) * (h : ℝ)) =
        Real.exp (Real.log (1 / 3 : ℝ) * (((d : ℝ) / 2) * (h : ℝ))) from
      Real.rpow_def_of_pos (by norm_num) _]
    rw [show Real.rpow 3 (-((d : ℝ) / 2) * (h : ℝ)) =
        Real.exp (Real.log 3 * (-((d : ℝ) / 2) * (h : ℝ))) from
      Real.rpow_def_of_pos (by norm_num) _]
    rw [show Real.log (1 / 3 : ℝ) = -Real.log 3 by
      rw [one_div, Real.log_inv]]
    congr 1
    ring
  have hfluct :
      A * xi * delta1 ^ 2 *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
        eta * delta1 ^ 2 := by
    have hfluct0' := hfluct0
    rw [hbaseEq] at hfluct0'
    rw [← hgap] at hfluct0'
    nlinarith [mul_nonneg (sq_nonneg delta1)
      (sub_nonneg.mpr hfluct0')]
  have hmean' :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        eta * delta1 ^ 2 := by
    simpa only [eta] using! hmean
  have hcoef : A * rho * (2 * delta1 ^ 2) = A * xi * delta1 ^ 2 := by
    dsimp only [rho]
    ring
  change
      (∫ omega,
          |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
            ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
              cutoffResponseOnCube M L p q R omega ^ 2| ^ rho
            ∂M.P.toMeasure) ^ rho⁻¹ ≤
        A * rho * (2 * delta1 ^ 2) *
            Real.rpow 3 (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) +
          ∫ omega, cutoffResponseOnCube M L p q
            (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure at hbase
  rw [hcoef] at hbase
  simpa only [rho] using! hbase.trans (by linarith [hmean'])

/-- Compatibility wrapper which derives the retained-mean budget from the
same smallness constant used by the spatial Rosenthal estimate. -/
theorem cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanCoeff
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L n m h : ℕ) (hLn : L ≤ n) (hnm : n ≤ m) (hgap : m - n = h)
    (hh : 0 < h) (p q : Vec d) {xi delta1 meanCoeff : ℝ}
    (hxi : 4 ≤ xi)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (hmeanCoeff : 0 ≤ meanCoeff)
    (hmeanSmall : meanCoeff * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
            ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1)
    (hmeanSource :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        meanCoeff * M.delta ^ 4) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      2 * squareResponseQuarterNetEta d * delta1 ^ 2 := by
  have hKpos : 0 < squareResponseAbsorptionConst d :=
    lt_of_lt_of_le (by norm_num) (squareResponseAbsorptionConst_seventyTwo_le d)
  have hhR : 1 ≤ (h : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh)
  have hδsmall : M.delta ^ 2 ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1 := by
    have hprod : 1 ≤ xi * (h : ℝ) := by nlinarith
    calc
      M.delta ^ 2 ≤ (xi * (h : ℝ)) * M.delta ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hprod
      _ = xi * M.delta ^ 2 * (h : ℝ) := by ring
      _ ≤ _ := hsmall
  have hsqBound : M.delta ^ 4 ≤
      ((squareResponseAbsorptionConst d)⁻¹ * delta1) ^ 2 := by
    convert pow_le_pow_left₀ (sq_nonneg _) hδsmall 2 using 1
    all_goals ring
  have hmean :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        squareResponseQuarterNetEta d * delta1 ^ 2 := by
    refine hmeanSource.trans ?_
    calc
      meanCoeff * M.delta ^ 4 ≤
          meanCoeff * ((squareResponseAbsorptionConst d)⁻¹ * delta1) ^ 2 :=
        mul_le_mul_of_nonneg_left hsqBound hmeanCoeff
      _ = (meanCoeff * (squareResponseAbsorptionConst d)⁻¹ ^ 2) *
          delta1 ^ 2 := by ring
      _ ≤ squareResponseQuarterNetEta d * delta1 ^ 2 :=
        mul_le_mul_of_nonneg_right hmeanSmall (sq_nonneg delta1)
  exact cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanBudget
    M L n m h hLn hnm hgap p q hxi hlog hmoment hroot hmean

/-- The quarter-net-budget estimate implies the former fixed-direction
`delta1^2/36` statement after forgetting the reserved finite-net gain. -/
theorem cutoffResponseSquareAverage_rpow_root_le_delta1_sq_div_thirtySix_of_meanCoeff
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L n m h : ℕ) (hLn : L ≤ n) (hnm : n ≤ m) (hgap : m - n = h)
    (hh : 0 < h) (p q : Vec d) {xi delta1 meanCoeff : ℝ}
    (hxi : 4 ≤ xi)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (hmeanCoeff : 0 ≤ meanCoeff)
    (hmeanSmall : meanCoeff * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
            ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1)
    (hmeanSource :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        meanCoeff * M.delta ^ 4) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      (1 / 36 : ℝ) * delta1 ^ 2 := by
  have heta : 2 * squareResponseQuarterNetEta d ≤ (1 / 36 : ℝ) := by
    unfold squareResponseQuarterNetEta
    have hcard : (1 : ℝ) ≤ ((sphereQuarterNet d).points.card : ℝ) := by
      exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
    rw [inv_eq_one_div]
    rw [show 2 * (1 / (288 * ((sphereQuarterNet d).points.card : ℝ))) =
        2 / (288 * ((sphereQuarterNet d).points.card : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) <
      288 * ((sphereQuarterNet d).points.card : ℝ))).2
    nlinarith
  exact
    (cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanCoeff
      M L n m h hLn hnm hgap hh p q hxi hlog hsmall hmeanCoeff hmeanSmall
        hmoment hroot hmeanSource).trans
      (mul_le_mul_of_nonneg_right heta (sq_nonneg delta1))

/-- The unit-coefficient specialization retained for callers whose completed
moment-two induction has the exact radius `delta^2`. -/
theorem cutoffResponseSquareAverage_rpow_root_le_delta1_sq_div_thirtySix
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L n m h : ℕ) (hLn : L ≤ n) (hnm : n ≤ m) (hgap : m - n = h)
    (hh : 0 < h) (p q : Vec d) {xi delta1 : ℝ}
    (hxi : 4 ≤ xi)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (hmoment : Integrable
      (fun omega =>
        |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi)
      M.P.toMeasure)
    (hroot :
      (∫ omega,
          |cutoffResponseOnCube M L p q (originCube d (n : ℤ)) omega| ^ xi
            ∂M.P.toMeasure) ^ xi⁻¹ ≤ delta1)
    (hmeanSource :
      ∫ omega, cutoffResponseOnCube M L p q
          (originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤ M.delta ^ 4) :
    (∫ omega,
        |(((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      (1 / 36 : ℝ) * delta1 ^ 2 := by
  have hK : (squareResponseQuarterNetEta d)⁻¹ ≤
      squareResponseAbsorptionConst d :=
    squareResponseQuarterNetEta_inv_le_absorptionConst d
  have hKpos : 0 < squareResponseAbsorptionConst d :=
    lt_of_lt_of_le (by norm_num) (squareResponseAbsorptionConst_seventyTwo_le d)
  have heta : 0 < squareResponseQuarterNetEta d :=
    squareResponseQuarterNetEta_pos (d := d)
  have hKinv : (squareResponseAbsorptionConst d)⁻¹ ≤
      squareResponseQuarterNetEta d := by
    have hetaInv : 0 < (squareResponseQuarterNetEta d)⁻¹ := inv_pos.mpr heta
    calc
      (squareResponseAbsorptionConst d)⁻¹ =
          1 / squareResponseAbsorptionConst d := by rw [one_div]
      _ ≤ 1 / (squareResponseQuarterNetEta d)⁻¹ :=
        one_div_le_one_div_of_le hetaInv hK
      _ = squareResponseQuarterNetEta d := by rw [one_div, inv_inv]
  have hKinv0 : 0 ≤ (squareResponseAbsorptionConst d)⁻¹ :=
    inv_nonneg.mpr hKpos.le
  have hmeanSmall :
      (1 : ℝ) * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
        squareResponseQuarterNetEta d := by
    rw [one_mul]
    have hetaOne : squareResponseQuarterNetEta d ≤ 1 := by
      unfold squareResponseQuarterNetEta
      have hcard : (1 : ℝ) ≤ ((sphereQuarterNet d).points.card : ℝ) := by
        exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
      rw [inv_le_one₀ (by positivity : (0 : ℝ) <
        288 * ((sphereQuarterNet d).points.card : ℝ))]
      nlinarith
    nlinarith [mul_nonneg hKinv0 (sub_nonneg.mpr hKinv),
      mul_nonneg heta.le (sub_nonneg.mpr hetaOne)]
  exact cutoffResponseSquareAverage_rpow_root_le_delta1_sq_div_thirtySix_of_meanCoeff
    M L n m h hLn hnm hgap hh p q hxi hlog hsmall (by norm_num)
      hmeanSmall hmoment hroot (by simpa using! hmeanSource)

end

end SubdiffusiveProcess.CoarseGrainingVocab
