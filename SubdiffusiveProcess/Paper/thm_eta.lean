import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.JBoundByBesov
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import Homogenization.Book.Ch02.Matrices
import SubdiffusiveProcess.Paper.in_J
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_moments
import SubdiffusiveProcess.Paper.lem_C1
import SubdiffusiveProcess.Paper.lem_conc
import SubdiffusiveProcess.Paper.lem_fmono
import SubdiffusiveProcess.Paper.lem_fmono_annealed_subadditivity
import SubdiffusiveProcess.Paper.in_moments_ellipticity_tail
import SubdiffusiveProcess.Paper.in_moments_response_moment
import SubdiffusiveProcess.Paper.near_extremal_member
import SubdiffusiveProcess.Paper.stationary_defects
import SubdiffusiveProcess.Paper.stationary_family
import SubdiffusiveProcess.Paper.annealed_limit_response_transport
import SubdiffusiveProcess.Paper.annealed_window_convergence
import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffNormalization
import Homogenization.Book.Ch04.Theorems.StationaryExpectations
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.WeightedChildren

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

private theorem aux_thm_eta_envelope_zero_of_near (F g : ℕ → ℝ)
    (hmono : Antitone F) (hpos : ∀ k, 0 ≤ F k)
    (hnear : ∀ k, 1 ≤ k → F (4 * k) ≤ g k + (k : ℝ)⁻¹)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto F atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun k : ℕ => F (4 * k)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun k : ℕ => g k + (k : ℝ)⁻¹) atTop (𝓝 0) := by
      convert hg.add hinv using 1 <;> simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall (fun k => hpos (4 * k))
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      exact hnear k hk
  have hfour : Tendsto (fun k : ℕ => 4 * k) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  exact (tendsto_iff_tendsto_subseq_of_antitone hmono hfour).2 hsub

private theorem aux_thm_eta_symmetric_eq_of_quadratic (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hquad : ∀ x : Fin d → ℝ, x ⬝ᵥ A.mulVec x = x ⬝ᵥ B.mulVec x) : A = B := by
  have hsym (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose = M) :
      (Matrix.toBilin' M).IsSymm := by
    refine ⟨?_⟩
    intro x y
    simp only [Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    have hij : M j i = M i j := by
      have := congrArg (fun N : Matrix (Fin d) (Fin d) ℝ => N i j) hM
      simpa using this
    rw [hij]
    ring
  have hforms : Matrix.toBilin' A = Matrix.toBilin' B :=
    LinearMap.BilinForm.ext_of_isSymm (hsym A hA) (hsym B hB) (by
      intro x
      simpa only [Matrix.toBilin'_apply'] using hquad x)
  exact (Matrix.toBilin' : Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ] _).injective hforms

section

/-- The actual coefficient `A_N^0(omega)` as a Chapter 4 carrier field. -/
def aux_thm_eta_field {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) : RegCoeffField d :=
  aux_annealed_limit_response_transport_scalarRegCoeffField (aux_awc_field model N omega)

theorem aux_thm_eta_field_elliptic {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) :
    Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (aux_thm_eta_field model N omega) :=
  aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic _
    (aux_awc_field_pos model N omega)

theorem aux_thm_eta_measurableSet_elliptic {d : ℕ} :
    MeasurableSet {a : RegCoeffField d |
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a} := by
  classical
  have hEq : {a : RegCoeffField d | Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a} =
      ⋂ Q : TriadicCube d, ⋃ k : ℕ,
        {a : RegCoeffField d |
          AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (cubeSet Q) a.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q)
        (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (Homogenization.Book.Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

theorem aux_thm_eta_measurable_smul {d : ℕ} (c : ℝ) :
    Measurable (fun z : RegCoeffField d => c • z) := by
  apply Homogenization.measurable_of_entryTestR_transport
  · intro y i j
    simpa [RegCoeffField.smul_toFun] using
      (Homogenization.measurable_apply_entry y i j).const_smul c
  · intro i j φ hφ
    exact ⟨c, i, j, φ, hφ, fun z => Homogenization.entryTestR_smul i j c z⟩

theorem aux_thm_eta_cutoffField_eq {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    aux_in_moments_response_moment_cutoffField model N = aux_awc_field model N := by
  funext omega
  ext x
  have hstat := (stationary_family d hd model).1 N omega x
  simp only [aux_in_moments_response_moment_cutoffField, aux_awc_field,
    ContinuousMap.coe_mk]
  rw [hstat]

/-- The scaled actual field has the law of the rescaled GMC cutoff field. -/
theorem aux_thm_eta_scaled_law {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • aux_thm_eta_field model N omega)
      (fun omega => rescaleReg N (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  have h := aux_in_moments_ellipticity_tail_field_law hd model N
  rw [aux_thm_eta_cutoffField_eq hd model N] at h
  exact h

theorem aux_thm_eta_field_aemeasurable {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    AEMeasurable (aux_thm_eta_field model N) (chaosSampleLaw model).toMeasure := by
  have h := (aux_thm_eta_scaled_law hd model N).aemeasurable_fst
  have hc : SubdiffusiveProcess.CoarseGrainingVocab.ahom model N ≠ 0 :=
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne'
  have h2 := (aux_thm_eta_measurable_smul (d := d) (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹).comp_aemeasurable h
  refine h2.congr (Filter.Eventually.of_forall fun omega => ?_)
  apply RegCoeffField.ext
  intro x
  simp only [Function.comp_apply, RegCoeffField.smul_apply, smul_smul, inv_mul_cancel₀ hc,
    one_smul]

/-- The law of the actual field. -/
def aux_thm_eta_law {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Homogenization.Book.Ch04.RestrictionCoeffLaw d :=
  Measure.map (aux_thm_eta_field model N) (chaosSampleLaw model).toMeasure

theorem aux_thm_eta_law_eq {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    aux_thm_eta_law model N =
      Measure.map (fun b : RegCoeffField d => (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ • b)
        (Homogenization.Book.Ch04.restrictionScaleNormalizedLaw N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw model N)) := by
  have hID := aux_thm_eta_scaled_law hd model N
  have hc : SubdiffusiveProcess.CoarseGrainingVocab.ahom model N ≠ 0 :=
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne'
  have hmap : Measure.map
      (fun omega => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • aux_thm_eta_field model N omega)
      (chaosSampleLaw model).toMeasure =
      Homogenization.Book.Ch04.restrictionScaleNormalizedLaw N
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw model N) := by
    rw [hID.map_eq, Homogenization.Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_eq_map,
      Measure.map_map (measurable_rescaleReg N)
        (SubdiffusiveProcess.CoarseGrainingVocab.measurable_aCutoffRegCoeffField model N)]
    rfl
  rw [← hmap, AEMeasurable.map_map_of_aemeasurable
    (aux_thm_eta_measurable_smul _).aemeasurable hID.aemeasurable_fst]
  unfold aux_thm_eta_law
  congr 1
  funext omega
  apply RegCoeffField.ext
  intro x
  simp only [Function.comp_apply, RegCoeffField.smul_apply, smul_smul, inv_mul_cancel₀ hc,
    one_smul]

theorem aux_thm_eta_law_isProbability {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    IsProbabilityMeasure (aux_thm_eta_law model N) :=
  Measure.isProbabilityMeasure_map (aux_thm_eta_field_aemeasurable hd model N)

theorem aux_thm_eta_law_carrier {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Homogenization.Book.Ch04.RestrictionLawCarrier (aux_thm_eta_law model N) := by
  haveI := aux_thm_eta_law_isProbability hd model N
  refine Homogenization.Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [Homogenization.Book.Ch04.AELocallyUniformlyEllipticLaw, aux_thm_eta_law,
    ae_map_iff (aux_thm_eta_field_aemeasurable hd model N) aux_thm_eta_measurableSet_elliptic]
  exact Filter.Eventually.of_forall fun omega => aux_thm_eta_field_elliptic model N omega

theorem aux_thm_eta_law_stationary {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Homogenization.Book.Ch04.RestrictionStationaryLaw (aux_thm_eta_law model N) := by
  have hL := Homogenization.Book.Ch04.RestrictionStationaryLaw.scaleNormalized
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_stationary model N) N
  intro z
  set c : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹
  rw [aux_thm_eta_law_eq hd model N]
  rw [Measure.map_map (measurable_translateReg _) (aux_thm_eta_measurable_smul c)]
  have hcomm : (translateReg (intVecToRealVec z) ∘ fun b : RegCoeffField d => c • b) =
      (fun b : RegCoeffField d => c • b) ∘ translateReg (intVecToRealVec z) := by
    funext b
    apply RegCoeffField.ext
    intro x
    rfl
  rw [hcomm, ← Measure.map_map (aux_thm_eta_measurable_smul c) (measurable_translateReg _),
    hL z]

end

section

/-- Stationary transfer of a translation-covariant cube observable to the origin cube. -/
theorem aux_thm_eta_stat_law {d : ℕ} {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ) (hX : IsTranslationCovariant X)
    {R : TriadicCube d} (hR : 0 ≤ R.scale)
    (hm : AEStronglyMeasurable (fun a : RegCoeffField d =>
      X (cubeSet (originCube d R.scale)) a.toFun) P) :
    (Integrable (fun a : RegCoeffField d => X (cubeSet R) a.toFun) P ↔
      Integrable (fun a : RegCoeffField d => X (cubeSet (originCube d R.scale)) a.toFun) P) ∧
    ∫ a, X (cubeSet R) a.toFun ∂P = ∫ a, X (cubeSet (originCube d R.scale)) a.toFun ∂P := by
  have hshift := Homogenization.Book.Ch04.cubeSet_eq_translateSet_originCube_of_nonneg_scale
    (R := R) hR
  set z := Homogenization.Book.Ch04.scaleTranslationShift R.scale R with hz
  have hfun : (fun a : RegCoeffField d => X (cubeSet R) a.toFun) =
      (fun a : RegCoeffField d => X (cubeSet (originCube d R.scale)) a.toFun) ∘
        translateReg (intVecToRealVec z) := by
    funext a
    simp only [Function.comp_apply]
    rw [hshift, hX]
    rfl
  have hmap : Measure.map (translateReg (intVecToRealVec z)) P = P := hstat z
  have hm' : AEStronglyMeasurable (fun a : RegCoeffField d =>
      X (cubeSet (originCube d R.scale)) a.toFun)
      (Measure.map (translateReg (intVecToRealVec z)) P) := by
    rw [hmap]; exact hm
  constructor
  · rw [hfun, ← integrable_map_measure hm' (measurable_translateReg _).aemeasurable, hmap]
  · rw [hfun]
    change ∫ a, (fun a : RegCoeffField d => X (cubeSet (originCube d R.scale)) a.toFun)
        (translateReg (intVecToRealVec z) a) ∂P = _
    rw [← integral_map (measurable_translateReg _).aemeasurable hm', hmap]

/-- Chaos-level stationary transfer through the law of a random carrier field. -/
theorem aux_thm_eta_stat_chaos {Om : Type*} [MeasurableSpace Om] {mu : Measure Om} {d : ℕ}
    (A : Om → RegCoeffField d) (hA : AEMeasurable A mu)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw (Measure.map A mu))
    (X : Set (Vec d) → CoeffField d → ℝ) (hX : IsTranslationCovariant X)
    {R : TriadicCube d} (hR : 0 ≤ R.scale)
    (hm : AEStronglyMeasurable (fun a : RegCoeffField d =>
      X (cubeSet (originCube d R.scale)) a.toFun) (Measure.map A mu))
    (hmR : AEStronglyMeasurable (fun a : RegCoeffField d =>
      X (cubeSet R) a.toFun) (Measure.map A mu))
    (hint : Integrable (fun w => X (cubeSet (originCube d R.scale)) (A w).toFun) mu) :
    Integrable (fun w => X (cubeSet R) (A w).toFun) mu ∧
      ∫ w, X (cubeSet R) (A w).toFun ∂mu =
        ∫ w, X (cubeSet (originCube d R.scale)) (A w).toFun ∂mu := by
  obtain ⟨hiff, heq⟩ := aux_thm_eta_stat_law hstat X hX hR hm
  have hint' := (integrable_map_measure hm hA).2 hint
  refine ⟨(integrable_map_measure hmR hA).1 (hiff.2 hint'), ?_⟩
  have h1 := integral_map hA hmR
  have h2 := integral_map hA hm
  simp only at h1 h2
  rw [← h1, ← h2, heq]

/-- The squared distance of the inverse-Neumann flux image from a fixed vector. -/
def aux_thm_eta_sepObs {d : ℕ} (q w : Vec d) : Set (Vec d) → CoeffField d → ℝ :=
  fun U a => vecNormSq (matVecMul (coarseBlockMatrix U a).lowerRight q - w)

theorem aux_thm_eta_sepObs_cov {d : ℕ} (q w : Vec d) :
    IsTranslationCovariant (aux_thm_eta_sepObs q w) := by
  intro U z a
  simp only [aux_thm_eta_sepObs]
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]
  rfl

theorem aux_thm_eta_sepObs_aesm {d : ℕ} {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) (q w : Vec d) :
    AEStronglyMeasurable (fun a : RegCoeffField d =>
      aux_thm_eta_sepObs q w (cubeSet Q) a.toFun) P := by
  have hM : AEMeasurable (fun a : RegCoeffField d =>
      ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight : Fin d → Fin d → ℝ)) P := by
    apply aemeasurable_pi_lambda
    intro i
    apply aemeasurable_pi_lambda
    intro j
    exact hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
  have hc : Continuous (fun M : Fin d → Fin d → ℝ =>
      vecNormSq (matVecMul (M : Mat d) q - w)) := by
    unfold vecNormSq vecDot matVecMul
    fun_prop
  exact (hc.measurable.comp_aemeasurable hM).aestronglyMeasurable

theorem aux_thm_eta_J_aesm {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) (p q : Vec d) :
    AEStronglyMeasurable (fun a : RegCoeffField d =>
      (fun (U : Set (Vec d)) (b : CoeffField d) => ResponseJ U p q b) (cubeSet Q) a.toFun) P :=
  hP.aestronglyMeasurable_restrictionResponseJObservableCubeSet Q p q

/-- The Chapter 2 family attached to the actual field. -/
abbrev aux_thm_eta_fam {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) : TriadicCoeffFamily d :=
  Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (aux_thm_eta_field model N omega) (aux_thm_eta_field_elliptic model N omega)

theorem aux_thm_eta_fam_aeeq {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (Q : TriadicCube d) (b : CoeffOn (cubeDomain Q))
    (hb : ∀ x, b.toCoeffField x = scalarMatrix (aux_awc_field model N omega x)) :
    CoeffOn.AEEq ((aux_thm_eta_fam model N omega).coeffOn Q) b := by
  have h : ((aux_thm_eta_fam model N omega).coeffOn Q).toCoeffField = b.toCoeffField := by
    funext x
    rw [hb x]
    rfl
  unfold CoeffOn.AEEq
  rw [h]

theorem aux_thm_eta_J_eq {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Q : TriadicCube d) (b : CoeffOn (cubeDomain Q))
    (hb : ∀ x, b.toCoeffField x = scalarMatrix (aux_awc_field model N omega x)) (p q : Vec d) :
    responseJ (cubeDomain Q) b p q =
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
        (aux_thm_eta_field model N omega) :=
  (aux_awc_responseJ_eq_ofAEEq (aux_thm_eta_fam_aeeq model N omega Q b hb) p q).symm.trans
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      _ _ Q p q)

theorem aux_thm_eta_R_eq {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Q : TriadicCube d) (b : CoeffOn (cubeDomain Q))
    (hb : ∀ x, b.toCoeffField x = scalarMatrix (aux_awc_field model N omega x)) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) b =
      (coarseBlockMatrix (cubeSet Q) (aux_thm_eta_field model N omega).toFun).lowerRight := by
  rw [Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (aux_thm_eta_field_elliptic model N omega) Q, coarseBlockMatrix_lowerRight]
  exact (sigmaStarInvCoarse_eq_ofAEEq (aux_thm_eta_fam_aeeq model N omega Q b hb)).symm

theorem aux_thm_eta_fam_symm {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (Q : TriadicCube d) :
    CoeffOn.IsSymmetric ((aux_thm_eta_fam model N omega).coeffOn Q) := by
  rw [CoeffOn.IsSymmetric]
  filter_upwards [] with x
  exact Homogenization.scalarMatrix_isSymm _

theorem aux_thm_eta_sep_eq {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Q : TriadicCube d) (p q : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.coarseScaleSeparation
        (aux_thm_eta_field model N omega) (aux_thm_eta_field_elliptic model N omega) Q p q =
      matVecMul (coarseBlockMatrix (cubeSet Q) (aux_thm_eta_field model N omega).toFun).lowerRight q
        - p := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.coarseScaleSeparation
  have hk := (responseSymmetricDirichletNeumannTheory _ _
    (aux_thm_eta_fam_symm model N omega Q)).kappa_eq_zero
  rw [hk, Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    (aux_thm_eta_field_elliptic model N omega) Q, coarseBlockMatrix_lowerRight]
  have h0 : matVecMul (0 : Mat d) p = 0 := by
    funext i
    simp [matVecMul]
  rw [h0, add_zero]

end

section

/-- Geometric control of the discounted scale sums. -/
theorem aux_thm_eta_geom (β : ℝ) (hβ : 0 < β) (l m : ℤ) :
    ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-β * ((m - n : ℤ) : ℝ)) ≤
      (1 - (3 : ℝ) ^ (-β))⁻¹ := by
  set r : ℝ := (3 : ℝ) ^ (-β) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ n ∈ Finset.Icc l m,
      (3 : ℝ) ^ (-β * ((m - n : ℤ) : ℝ)) = r ^ (m - n).toNat := by
    intro n hn
    have hmn : 0 ≤ m - n := by
      have := (Finset.mem_Icc.mp hn).2
      omega
    have hcast : ((m - n : ℤ) : ℝ) = (((m - n).toNat : ℕ) : ℝ) := by
      have h := Int.toNat_of_nonneg hmn
      have h' : (((m - n).toNat : ℕ) : ℝ) = (((m - n).toNat : ℤ) : ℝ) := by push_cast; rfl
      rw [h', h]
    rw [hcast, hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [Finset.sum_congr rfl hterm]
  have hinj : Set.InjOn (fun n : ℤ => (m - n).toNat) (Finset.Icc l m : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    simp only at hxy
    omega
  rw [← Finset.sum_image (g := fun n : ℤ => (m - n).toNat) (f := fun j : ℕ => r ^ j) hinj]
  calc ∑ j ∈ (Finset.Icc l m).image (fun n : ℤ => (m - n).toNat), r ^ j
      ≤ ∑' j : ℕ, r ^ j :=
        Summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)
          (summable_geometric_of_lt_one hr0 hr1)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- Weighted Cauchy--Schwarz for square roots. -/
theorem aux_thm_eta_cs {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * Real.sqrt (x i)) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * x i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * Real.sqrt (x i))
  have h1 : ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * Real.sqrt (x i)) =
      ∑ i ∈ s, w i * Real.sqrt (x i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have h2 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have h3 : ∑ i ∈ s, (Real.sqrt (w i) * Real.sqrt (x i)) ^ 2 = ∑ i ∈ s, w i * x i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hx i hi)]
  rw [h1, h2, h3] at h
  exact h

theorem aux_thm_eta_sq5 (a b c e f : ℝ) :
    (a + b + c + e + f) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + f ^ 2) := by
  have h : 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + f ^ 2) - (a + b + c + e + f) ^ 2 =
      (a - b) ^ 2 + (a - c) ^ 2 + (a - e) ^ 2 + (a - f) ^ 2 + (b - c) ^ 2 + (b - e) ^ 2 +
        (b - f) ^ 2 + (c - e) ^ 2 + (c - f) ^ 2 + (e - f) ^ 2 := by ring
  have h0 : 0 ≤ (a - b) ^ 2 + (a - c) ^ 2 + (a - e) ^ 2 + (a - f) ^ 2 + (b - c) ^ 2 +
      (b - e) ^ 2 + (b - f) ^ 2 + (c - e) ^ 2 + (c - f) ^ 2 + (e - f) ^ 2 := by positivity
  linarith

/-- The scalar algebra collecting the four-term display. -/
theorem aux_thm_eta_alg (X cn c2 li A B E Jm w3 w4 W1 W2 SD SS : ℝ)
    (hX : 0 ≤ X) (hc2 : 0 ≤ c2) (hcn : cn = Real.sqrt c2) (hli : 0 ≤ li)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hA2 : A ^ 2 ≤ W1 * SD) (hB2 : B ^ 2 ≤ W2 * SS)
    (hSD : 0 ≤ SD) (hSS : 0 ≤ SS) (hW1 : 0 ≤ W1) (hW2 : 0 ≤ W2)
    (hE : 0 ≤ E) (hE2 : E ^ 2 = 2 * Jm) (hJm : 0 ≤ Jm)
    (hw3 : 0 ≤ w3) (hw4 : 0 ≤ w4) (hw41 : w4 ≤ 1)
    (hXle : X ≤ 2 * Real.sqrt li * A + Real.sqrt 2 * B +
      2 * Real.sqrt 2 * (w3 * Real.sqrt li * E) + 2 * Real.sqrt 2 * (w4 * cn)) :
    (X + cn) ^ 2 ≤ (5 * (4 * W1 + 2 * W2 + 25)) * (1 + li) *
      (SD + SS + w3 ^ 2 * Jm + c2) := by
  have hcn0 : 0 ≤ cn := hcn ▸ Real.sqrt_nonneg _
  have hcn2 : cn ^ 2 = c2 := by rw [hcn, Real.sq_sqrt hc2]
  have hsl : Real.sqrt li ^ 2 = li := Real.sq_sqrt hli
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsl0 : 0 ≤ Real.sqrt li := Real.sqrt_nonneg _
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hT10 : 0 ≤ 2 * Real.sqrt li * A := by positivity
  have hT20 : 0 ≤ Real.sqrt 2 * B := by positivity
  have hT30 : 0 ≤ 2 * Real.sqrt 2 * (w3 * Real.sqrt li * E) := by positivity
  have hT40 : 0 ≤ 2 * Real.sqrt 2 * (w4 * cn) := by positivity
  have hstep1 : (X + cn) ^ 2 ≤ (2 * Real.sqrt li * A + Real.sqrt 2 * B +
      2 * Real.sqrt 2 * (w3 * Real.sqrt li * E) + 2 * Real.sqrt 2 * (w4 * cn) + cn) ^ 2 := by
    have hle : X + cn ≤ 2 * Real.sqrt li * A + Real.sqrt 2 * B +
      2 * Real.sqrt 2 * (w3 * Real.sqrt li * E) + 2 * Real.sqrt 2 * (w4 * cn) + cn := by linarith
    exact pow_le_pow_left₀ (by linarith) hle 2
  have hstep2 := aux_thm_eta_sq5 (2 * Real.sqrt li * A) (Real.sqrt 2 * B)
    (2 * Real.sqrt 2 * (w3 * Real.sqrt li * E)) (2 * Real.sqrt 2 * (w4 * cn)) cn
  have hT1sq : (2 * Real.sqrt li * A) ^ 2 = 4 * li * A ^ 2 := by
    rw [mul_pow, mul_pow, hsl]; ring
  have hT2sq : (Real.sqrt 2 * B) ^ 2 = 2 * B ^ 2 := by
    rw [mul_pow, hs2]
  have hT3sq : (2 * Real.sqrt 2 * (w3 * Real.sqrt li * E)) ^ 2 = 16 * li * (w3 ^ 2 * Jm) := by
    have e : (2 * Real.sqrt 2 * (w3 * Real.sqrt li * E)) ^ 2 =
        4 * Real.sqrt 2 ^ 2 * w3 ^ 2 * Real.sqrt li ^ 2 * E ^ 2 := by ring
    rw [e, hs2, hsl, hE2]
    ring
  have hT4sq : (2 * Real.sqrt 2 * (w4 * cn)) ^ 2 = 8 * w4 ^ 2 * c2 := by
    have e : (2 * Real.sqrt 2 * (w4 * cn)) ^ 2 = 4 * Real.sqrt 2 ^ 2 * w4 ^ 2 * cn ^ 2 := by ring
    rw [e, hs2, hcn2]
    ring
  have hw42 : w4 ^ 2 ≤ 1 := by
    have := mul_le_mul hw41 hw41 hw4 zero_le_one
    nlinarith
  have hA2' : 4 * li * A ^ 2 ≤ 4 * li * (W1 * SD) :=
    mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hc8 : 8 * w4 ^ 2 * c2 ≤ 8 * c2 := by
    have := mul_le_mul_of_nonneg_right hw42 hc2
    linarith
  have hsum : (X + cn) ^ 2 ≤
      5 * (4 * li * (W1 * SD) + 2 * (W2 * SS) + 16 * li * (w3 ^ 2 * Jm) + 8 * c2 + c2) := by
    rw [hT1sq, hT2sq, hT3sq, hT4sq, hcn2] at hstep2
    linarith
  set T := SD + SS + w3 ^ 2 * Jm + c2 with hT
  have hY0 : 0 ≤ w3 ^ 2 * Jm := by positivity
  have hSDT : SD ≤ T := by rw [hT]; linarith
  have hSST : SS ≤ T := by rw [hT]; linarith
  have hYT : w3 ^ 2 * Jm ≤ T := by rw [hT]; linarith
  have hcT : c2 ≤ T := by rw [hT]; linarith
  have hT0 : 0 ≤ T := le_trans hSD hSDT
  have b1 : li * (W1 * SD) ≤ (1 + li) * (W1 * T) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hSDT hW1) (mul_nonneg hW1 hSD)
      (by linarith)
  have b2 : W2 * SS ≤ (1 + li) * (W2 * T) := by
    have h1 : W2 * SS ≤ W2 * T := mul_le_mul_of_nonneg_left hSST hW2
    have h2 : W2 * T ≤ (1 + li) * (W2 * T) := by
      have := mul_nonneg hli (mul_nonneg hW2 hT0)
      linarith
    linarith
  have b3 : li * (w3 ^ 2 * Jm) ≤ (1 + li) * T :=
    mul_le_mul (by linarith) hYT hY0 (by linarith)
  have b4 : c2 ≤ (1 + li) * T := by
    have := mul_nonneg hli hT0
    linarith
  have e : (5 * (4 * W1 + 2 * W2 + 25)) * (1 + li) * T =
      5 * (4 * ((1 + li) * (W1 * T)) + 2 * ((1 + li) * (W2 * T)) + 16 * ((1 + li) * T) +
        9 * ((1 + li) * T)) := by ring
  rw [e]
  linarith

theorem aux_thm_eta_sqrt_le (x : ℝ) (hx : 0 ≤ x) : x.rpow (1 / 2) ≤ 1 + x := by
  have h : x.rpow (1 / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    rfl
  rw [h]
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

end

section

open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov in
/-- The GMC central-child composite at `s = 1/4`, restated on the Chapter 4 observables. -/
theorem aux_thm_eta_composite (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (a : RegCoeffField d)
      (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d),
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q a ≤
        C0 * Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a *
          (Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a *
            (Homogenization.Book.Ch04.lambdaSqCoeffField (originCube d m) (1 / 4)
              (.finite 1) a)⁻¹).rpow (1 / 2) *
          (centredMultiscaleAverageSum a ha m p q +
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 +
        ∑ R ∈ descendantsAtDepth (originCube d m) 1,
          2 * (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q a -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) := by
  obtain ⟨C0, hC0, hcomp⟩ := exists_responseJ_centralChild_le_jBoundByBesovDisplay d
  refine ⟨C0, hC0, fun a ha m p q => ?_⟩
  have hLamS : LambdaS (originCube d m) (1 / 4)
      (Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) =
      Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a := by
    rw [Homogenization.Book.Ch04.LambdaSqCoeffField, dif_pos ha]
    rfl
  have hlamS : lambdaS (originCube d m) (1 / 4)
      (Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) =
      Homogenization.Book.Ch04.lambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a := by
    rw [Homogenization.Book.Ch04.lambdaSqCoeffField, dif_pos ha]
    rfl
  have hexp : (1 / 4 : ℝ) / (1 - 2 * (1 / 4)) = 1 / 2 := by norm_num
  have h1 := hcomp a ha m p q (s := 1 / 4) (by norm_num) le_rfl
  rw [Homogenization.Book.Ch02.ThetaRatio, hLamS, hlamS, hexp, div_eq_mul_inv] at h1
  simpa only [Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet]
    using h1

/-- Weighted square-root sums against a geometric weight budget. -/
theorem aux_thm_eta_wsq (s : Finset ℤ) (w D : ℤ → ℝ) (W : ℝ) (hw : ∀ n ∈ s, 0 ≤ w n)
    (hD : ∀ n ∈ s, 0 ≤ D n) (hW : ∑ n ∈ s, w n ≤ W) :
    (∑ n ∈ s, w n * Real.sqrt (D n)) ^ 2 ≤ W * ∑ n ∈ s, w n * D n ∧
      0 ≤ ∑ n ∈ s, w n * Real.sqrt (D n) ∧ 0 ≤ ∑ n ∈ s, w n * D n := by
  have h0 : 0 ≤ ∑ n ∈ s, w n * D n := Finset.sum_nonneg fun n hn => mul_nonneg (hw n hn) (hD n hn)
  refine ⟨(aux_thm_eta_cs s w D hw hD).trans (mul_le_mul_of_nonneg_right hW h0), ?_, h0⟩
  exact Finset.sum_nonneg fun n hn => mul_nonneg (hw n hn) (Real.sqrt_nonneg _)

/-- The final scalar combination of the composite and the collected display. -/
theorem aux_thm_eta_combine (J C0 Lam li Z K Y S r : ℝ) (hC0 : 0 ≤ C0) (hLam : 0 ≤ Lam)
    (hli : 0 ≤ li) (hZ : 0 ≤ Z) (_hK : 0 ≤ K)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 + Lam * li)
    (hJ : J ≤ C0 * Lam * r * Z + S) (hZle : Z ≤ K * (1 + li) * Y) :
    J ≤ C0 * K * (1 + Lam) * (1 + Lam * li) * (1 + li) * Y + S := by
  have hY : 0 ≤ K * (1 + li) * Y := le_trans hZ hZle
  have h1 : C0 * Lam * r * Z ≤ C0 * (1 + Lam) * (1 + Lam * li) * (K * (1 + li) * Y) := by
    apply mul_le_mul _ hZle hZ (by positivity)
    apply mul_le_mul _ hr hr0 (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  have e : C0 * (1 + Lam) * (1 + Lam * li) * (K * (1 + li) * Y) =
      C0 * K * (1 + Lam) * (1 + Lam * li) * (1 + li) * Y := by ring
  linarith

open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov in
/-- The deterministic central-child bound (paper `mfd:lem-C1`) for an actual elliptic field, at
`s = 1/4`, `r = 1`, written with the four displayed error terms. -/
theorem aux_thm_eta_det (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : RegCoeffField d)
      (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) (m l : ℤ), l ≤ m →
      ∀ (p q : Vec d),
      0 < Homogenization.Book.Ch04.lambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a →
      0 ≤ Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a →
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q a ≤
        C * (1 + Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a) *
          (1 + Homogenization.Book.Ch04.LambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a *
            (Homogenization.Book.Ch04.lambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a)⁻¹) *
          (1 + (Homogenization.Book.Ch04.lambdaSqCoeffField (originCube d m) (1 / 4) (.finite 1) a)⁻¹) *
          ((∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                m n p q a) +
            (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              descendantsAverage (originCube d m) (m - n).toNat
                (coarseMatrixVariationSq a ha (originCube d m) p q)) +
            ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
              Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a +
            vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) +
        ∑ R ∈ descendantsAtDepth (originCube d m) 1,
          2 * (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q a -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) := by
  obtain ⟨C0, hC0, hcomp⟩ := aux_thm_eta_composite d
  have hr1 : (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr2 : (3 : ℝ) ^ (-(1 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hW1pos : 0 < (1 - (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  have hW2pos : 0 < (1 - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  refine ⟨C0 * (5 * (4 * (1 - (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ)))⁻¹ +
    2 * (1 - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ + 25)), by positivity, ?_⟩
  intro a ha m l hlm p q hlam hLam
  have h1 := hcomp a ha m p q
  have h4 := centredMultiscaleAverageSum_le_fourTerm a ha hlm (s := 1 / 4) (by norm_num)
    (by norm_num) (r := .finite 1)
    (Homogenization.Book.Ch02.MultiscaleExponent.isAdmissible_finite.2 le_rfl) p q
  obtain ⟨hA2, hA0, hSD0⟩ := aux_thm_eta_wsq (Finset.Icc l m)
    (fun n => (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)))
    (fun n => Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
      m n p q a) _ (fun n _ => Real.rpow_nonneg (by norm_num) _)
    (fun n _ => Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
      a ha m n p q)
    (aux_thm_eta_geom (1 - 1 / 4) (by norm_num) l m)
  obtain ⟨hB2, hB0, hSS0⟩ := aux_thm_eta_wsq (Finset.Icc l m)
    (fun n => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)))
    (fun n => descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q)) _
    (fun n _ => Real.rpow_nonneg (by norm_num) _)
    (fun n _ => descendantsAverage_nonneg _ _ _ fun R _ =>
      coarseMatrixVariationSq_nonneg a ha _ p q R)
    (by simpa only [neg_mul, one_mul] using aux_thm_eta_geom 1 (by norm_num) l m)
  have hw41 : (3 : ℝ) ^ (-((m - l : ℤ) : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ ((m - l : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hlm)
    linarith
  have halg := aux_thm_eta_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (centredMultiscaleAverageSum_nonneg a ha m p q) (vecNormSq_nonneg _) rfl
    (inv_nonneg.mpr hlam.le) hA0 hB0 hA2 hB2 hSD0 hSS0 hW1pos.le hW2pos.le
    (maximizerEnergyL2Norm_nonneg a ha _ p q)
    (by rw [sq_maximizerEnergyL2Norm,
      maximizerEnergyL2NormSq_eq_two_mul_restrictionResponseJObservableCubeSet])
    (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg _ _ _ _)
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _) hw41 h4
  exact aux_thm_eta_combine _ _ _ _ _ _ _ _ _ hC0.le hLam (inv_nonneg.mpr hlam.le) (sq_nonneg _)
    (by positivity) (Real.rpow_nonneg (mul_nonneg hLam (inv_nonneg.mpr hlam.le)) _)
    (aux_thm_eta_sqrt_le _ (mul_nonneg hLam (inv_nonneg.mpr hlam.le))) h1 halg

end

section

theorem aux_thm_eta_fam_aeeq_family {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Fam : TriadicCoeffFamily d)
    (hFam : ∀ Q : TriadicCube d, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (Fam.coeffOn Q).toCoeffField x = scalarMatrix (aux_awc_field model N omega x)) :
    TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N omega) Fam := by
  intro Q
  change ((aux_thm_eta_fam model N omega).coeffOn Q).toCoeffField =ᵐ[
    volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d))] (Fam.coeffOn Q).toCoeffField
  rw [cubeDomain_coe]
  filter_upwards [hFam Q] with x hx
  rw [hx]
  rfl

theorem aux_thm_eta_Lam_eq {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Fam : TriadicCoeffFamily d)
    (hFam : TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N omega) Fam)
    (Q : TriadicCube d) (s : ℝ) (r : Homogenization.Book.Ch02.MultiscaleExponent) :
    Homogenization.Book.Ch04.LambdaSqCoeffField Q s r (aux_thm_eta_field model N omega) =
        LambdaSq Q s r Fam ∧
      Homogenization.Book.Ch04.lambdaSqCoeffField Q s r (aux_thm_eta_field model N omega) =
        lambdaSq Q s r Fam := by
  constructor
  · rw [Homogenization.Book.Ch04.LambdaSqCoeffField, dif_pos (aux_thm_eta_field_elliptic model N omega)]
    exact LambdaSq_eq_ofAEEq hFam Q s r
  · rw [Homogenization.Book.Ch04.lambdaSqCoeffField, dif_pos (aux_thm_eta_field_elliptic model N omega)]
    exact lambdaSq_eq_ofAEEq hFam Q s r

theorem aux_thm_eta_dsum {d : ℕ} (Q : TriadicCube d) (f : TriadicCube d → ℝ) (c : ℝ) :
    ∑ R ∈ descendantsAtDepth Q 1, 2 * (f R - c) =
      2 * (3 : ℝ) ^ d * (descendantsAverage Q 1 f - c) := by
  have hcard : ((descendantsAtDepth Q 1).card : ℝ) = (3 : ℝ) ^ d := by
    rw [descendantsAtDepth_card]
    push_cast
    ring
  have hne : ((descendantsAtDepth Q 1).card : ℝ) ≠ 0 := by
    rw [hcard]; positivity
  dsimp only [descendantsAverage]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  have h3 : (3 : ℝ) ^ d ≠ 0 := by positivity
  field_simp

theorem aux_thm_eta_vecNormSq_sub_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) ≤ 2 * vecNormSq x + 2 * vecNormSq y := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (x i + y i)]

theorem aux_thm_eta_descAvg_add_const {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (f : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c + f R) = c + descendantsAverage Q j f := by
  have hne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast (descendantsAtDepth_nonempty Q j).card_ne_zero
  dsimp only [descendantsAverage]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov in
theorem aux_thm_eta_var_le {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    descendantsAverage Q j (coarseMatrixVariationSq (aux_thm_eta_field model N omega)
        (aux_thm_eta_field_elliptic model N omega) Q p q) ≤
      2 * aux_thm_eta_sepObs q p (cubeSet Q) (aux_thm_eta_field model N omega).toFun +
        2 * descendantsAverage Q j (fun R =>
          aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N omega).toFun) := by
  rw [← descendantsAverage_mul_left, ← aux_thm_eta_descAvg_add_const]
  apply descendantsAverage_le_descendantsAverage
  intro R _
  unfold coarseMatrixVariationSq aux_thm_eta_sepObs
  rw [aux_thm_eta_sep_eq, aux_thm_eta_sep_eq]
  exact aux_thm_eta_vecNormSq_sub_le _ _

end

section

theorem aux_thm_eta_factor_le (L li A : ℝ) (hL : 0 ≤ L) (hli : 0 ≤ li) (hA : 1 + L + li ≤ A) :
    (1 + L) * (1 + L * li) * (1 + li) ≤ 8 * A ^ 4 := by
  have hA1 : 1 ≤ A := by linarith
  have h1 : 1 + L ≤ 2 * A := by linarith
  have h2 : 1 + li ≤ 2 * A := by linarith
  have h3 : 1 + L * li ≤ 2 * A ^ 2 := by
    have hLA : L ≤ A := by linarith
    have hliA : li ≤ A := by linarith
    have := mul_le_mul hLA hliA hli (by linarith)
    nlinarith
  calc (1 + L) * (1 + L * li) * (1 + li) ≤ (2 * A) * (2 * A ^ 2) * (2 * A) := by
        apply mul_le_mul _ h2 (by positivity) (by positivity)
        exact mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = 8 * A ^ 4 := by ring

/-- Scalar combination for the truncated pointwise bound. -/
theorem aux_thm_eta_pw_combine (J C Lv lv A D S S' Y3 X Dsum : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ 1 + Lv) (hb : 0 ≤ 1 + Lv * lv⁻¹) (hc : 0 ≤ lv⁻¹)
    (hfac : (1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹) ≤ 8 * A ^ 4)
    (hD : 0 ≤ D) (hS0 : 0 ≤ S) (hY3 : 0 ≤ Y3) (hX : 0 ≤ X) (hSS : S ≤ S')
    (hJ : J ≤ C * (1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹) * (D + S + Y3 + X) + Dsum) :
    J ≤ C * 8 * A ^ 4 * (D + S' + Y3 + X) + Dsum := by
  have hY0 : 0 ≤ D + S + Y3 + X := by linarith
  have hYle : D + S + Y3 + X ≤ D + S' + Y3 + X := by linarith
  have hfac0 : 0 ≤ (1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹) :=
    mul_nonneg (mul_nonneg ha hb) (by linarith)
  have e : C * (1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹) * (D + S + Y3 + X) =
      C * ((1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹)) * (D + S + Y3 + X) := by ring
  have h1 : C * ((1 + Lv) * (1 + Lv * lv⁻¹) * (1 + lv⁻¹)) * (D + S + Y3 + X) ≤
      C * (8 * A ^ 4) * (D + S' + Y3 + X) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hfac hC) hYle hY0
    exact mul_nonneg hC (le_trans hfac0 hfac)
  have e2 : C * (8 * A ^ 4) * (D + S' + Y3 + X) = C * 8 * A ^ 4 * (D + S' + Y3 + X) := by ring
  linarith

open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov in
/-- The truncated pointwise bound on `{K_m ≤ A}` for the actual field. -/
theorem aux_thm_eta_pw (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
      (omega : BilateralField d) (m l : ℤ), l ≤ m → ∀ (p q : Vec d)
      (Fam : TriadicCoeffFamily d),
      TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N omega) Fam → ∀ (A : ℝ),
      0 < lambdaSq (originCube d m) (1 / 4) (.finite 1) Fam →
      0 ≤ LambdaSq (originCube d m) (1 / 4) (.finite 1) Fam →
      1 + LambdaSq (originCube d m) (1 / 4) (.finite 1) Fam +
        (lambdaSq (originCube d m) (1 / 4) (.finite 1) Fam)⁻¹ ≤ A →
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q
          (aux_thm_eta_field model N omega) ≤
        C * A ^ 4 *
          ((∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                m n p q (aux_thm_eta_field model N omega)) +
            (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
                  (aux_thm_eta_field model N omega).toFun +
                2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
                  aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N omega).toFun))) +
            ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
              Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
                (aux_thm_eta_field model N omega) +
            aux_thm_eta_sepObs q p (cubeSet (originCube d m))
              (aux_thm_eta_field model N omega).toFun) +
        2 * (3 : ℝ) ^ d *
          (descendantsAverage (originCube d m) 1 (fun R =>
              Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q
                (aux_thm_eta_field model N omega)) -
            Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
              (aux_thm_eta_field model N omega)) := by
  obtain ⟨C, hC, hdet⟩ := aux_thm_eta_det d
  refine ⟨C * 8, by positivity, ?_⟩
  intro model N omega m l hlm p q Fam hFam A hpos hL0 hK
  obtain ⟨hLeq, hleq⟩ := aux_thm_eta_Lam_eq model N omega Fam hFam (originCube d m) (1 / 4)
    (.finite 1)
  have h := hdet (aux_thm_eta_field model N omega) (aux_thm_eta_field_elliptic model N omega)
    m l hlm p q (by rw [hleq]; exact hpos) (by rw [hLeq]; exact hL0)
  rw [hLeq, hleq, aux_thm_eta_dsum] at h
  generalize LambdaSq (originCube d m) (1 / 4) (.finite 1) Fam = Lv at h hL0 hK
  generalize lambdaSq (originCube d m) (1 / 4) (.finite 1) Fam = lv at h hpos hK
  have hli : 0 ≤ lv⁻¹ := inv_nonneg.mpr hpos.le
  have hfac := aux_thm_eta_factor_le _ _ A hL0 hli hK
  -- the error sum
  have hS : ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      descendantsAverage (originCube d m) (m - n).toNat
        (coarseMatrixVariationSq (aux_thm_eta_field model N omega)
          (aux_thm_eta_field_elliptic model N omega) (originCube d m) p q) ≤
      ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
            (aux_thm_eta_field model N omega).toFun +
          2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
            aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N omega).toFun)) :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
      (aux_thm_eta_var_le model N omega (originCube d m) _ p q) (Real.rpow_nonneg (by norm_num) _)
  have hc : vecNormSq (coarseScaleSeparation (aux_thm_eta_field model N omega)
      (aux_thm_eta_field_elliptic model N omega) (originCube d m) p q) =
      aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N omega).toFun := by
    rw [aux_thm_eta_sep_eq]
    rfl
  rw [hc] at h
  have h1 : 0 ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        m n p q (aux_thm_eta_field model N omega) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
        _ (aux_thm_eta_field_elliptic model N omega) m n p q)
  have h2 : 0 ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      descendantsAverage (originCube d m) (m - n).toNat
        (coarseMatrixVariationSq (aux_thm_eta_field model N omega)
          (aux_thm_eta_field_elliptic model N omega) (originCube d m) p q) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (descendantsAverage_nonneg _ _ _ fun R _ => coarseMatrixVariationSq_nonneg _ _ _ p q R)
  have h3 : 0 ≤ ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (aux_thm_eta_field model N omega) :=
    mul_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg _ _ _ _)
  have h4 : 0 ≤ aux_thm_eta_sepObs q p (cubeSet (originCube d m))
      (aux_thm_eta_field model N omega).toFun := vecNormSq_nonneg _
  exact aux_thm_eta_pw_combine _ _ _ _ _ _ _ _ _ _ _ hC.le (by linarith)
    (by have := mul_nonneg hL0 hli; linarith) hli hfac h1 h2 h3 h4 hS h

end

section

theorem aux_thm_eta_quad_nonneg {d : ℕ} (hJ : in_J d) (U : Domain d) (b : CoeffOn U)
    (hb : CoeffOn.IsSymmetric b) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse U b).mulVec x ∧
      0 ≤ x ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).mulVec x := by
  have hR : 0 ≤ x ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).mulVec x := by
    have h := (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef U b).posSemidef.dotProduct_mulVec_nonneg x
    simpa [star_trivial] using h
  have hS : 0 ≤ x ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarCoarse U b).mulVec x := by
    have h := (Homogenization.Book.Ch02.sigmaStarCoarse_posDef U b).posSemidef.dotProduct_mulVec_nonneg x
    simpa [star_trivial] using h
  have hord := (hJ.ord_bounds U b hb x).2.1
  refine ⟨?_, hR⟩
  have e1 : Homogenization.vecDot x (Homogenization.matVecMul
      (Homogenization.Book.Ch02.sigmaStarCoarse U b) x) =
      x ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarCoarse U b).mulVec x := rfl
  have e2 : Homogenization.vecDot x (Homogenization.matVecMul
      (Homogenization.Book.Ch02.sigmaCoarse U b) x) =
      x ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse U b).mulVec x := rfl
  rw [e1, e2] at hord
  linarith

theorem aux_thm_eta_split {d : ℕ} (hJ : in_J d) (U : Domain d) (b : CoeffOn U)
    (hb : CoeffOn.IsSymmetric b) (p q : Fin d → ℝ) :
    responseJ U b p q = (1 / 2 : ℝ) * p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse U b).mulVec p +
      (1 / 2 : ℝ) * q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).mulVec q - p ⬝ᵥ q :=
  hJ.responseJ_split U b hb p q

/-- Unit-slope response control bounds all coarse entries and every response. -/
theorem aux_thm_eta_unit_bounds {d : ℕ} [NeZero d] (hJ : in_J d) (U : Domain d) (b : CoeffOn U)
    (hb : CoeffOn.IsSymmetric b) (Js : ℝ)
    (hJs : ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 → responseJ U b e e ≤ Js) :
    (∀ i j, |Homogenization.Book.Ch02.sigmaCoarse U b i j| ≤ 2 * d * (1 + Js)) ∧
    (∀ i j, |Homogenization.Book.Ch02.sigmaStarInvCoarse U b i j| ≤ 2 * d * (1 + Js)) ∧
    (∀ p q : Fin d → ℝ, responseJ U b p q ≤
      2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) * (1 + Js)) := by
  set P := Homogenization.Book.Ch02.sigmaCoarse U b with hP
  set R := Homogenization.Book.Ch02.sigmaStarInvCoarse U b with hR
  have hPsd : ∀ x, 0 ≤ x ⬝ᵥ P.mulVec x := fun x => (aux_thm_eta_quad_nonneg hJ U b hb x).1
  have hRsd : ∀ x, 0 ≤ x ⬝ᵥ R.mulVec x := fun x => (aux_thm_eta_quad_nonneg hJ U b hb x).2
  have hunit : ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 →
      (1 / 2 : ℝ) * e ⬝ᵥ P.mulVec e ≤ 1 + Js ∧ (1 / 2 : ℝ) * e ⬝ᵥ R.mulVec e ≤ 1 + Js := by
    intro e he
    have hs := aux_thm_eta_split hJ U b hb e e
    have hee : e ⬝ᵥ e = 1 := by rw [← he]; simp [dotProduct, sq]
    have h1 := hJs e he
    have h2 := hPsd e
    have h3 := hRsd e
    constructor <;> linarith
  have hdiag : ∀ (M : Matrix (Fin d) (Fin d) ℝ),
      (∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 → (1 / 2 : ℝ) * e ⬝ᵥ M.mulVec e ≤ 1 + Js) →
      Matrix.trace M ≤ d * (2 * (1 + Js)) := by
    intro M hM
    unfold Matrix.trace
    have : ∀ i ∈ (Finset.univ : Finset (Fin d)), Matrix.diag M i ≤ 2 * (1 + Js) := by
      intro i _
      have h := hM (Pi.single i 1) (aux_awc_single_sq i)
      have e : (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ M.mulVec (Pi.single i 1) = M i i := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e] at h
      simp only [Matrix.diag_apply]
      linarith
    calc ∑ i, Matrix.diag M i ≤ ∑ _i : Fin d, 2 * (1 + Js) := Finset.sum_le_sum this
      _ = d * (2 * (1 + Js)) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h := aux_awc_psd_abs_entry_le_trace P (sigmaCoarse_isSymm U b) hPsd i j
    have := hdiag P (fun e he => (hunit e he).1)
    linarith
  · intro i j
    have h := aux_awc_psd_abs_entry_le_trace R (sigmaStarInvCoarse_isSymm U b) hRsd i j
    have := hdiag R (fun e he => (hunit e he).2)
    linarith
  · intro p q
    have hs := aux_thm_eta_split hJ U b hb p q
    have hp := aux_awc_quad_le_scaled P (1 + Js) (fun e he => (hunit e he).1) p
    have hq := aux_awc_quad_le_scaled R (1 + Js) (fun e he => (hunit e he).2) q
    have hpq : -(p ⬝ᵥ q) ≤ (1 / 2) * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) := by
      have : 0 ≤ ∑ i, (p i + q i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have e : ∑ i, (p i + q i) ^ 2 = (∑ i, p i ^ 2) + ∑ i, q i ^ 2 + 2 * (p ⬝ᵥ q) := by
        simp only [dotProduct, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
        ring_nf
      linarith
    have hJs0 : 0 ≤ Js := by
      have i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      have := hJs (Pi.single i 1) (aux_awc_single_sq i)
      linarith [Homogenization.Book.Ch02.responseJ_nonneg U b (Pi.single i 1) (Pi.single i 1)]
    have hsp : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hprod : 0 ≤ ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) * (1 / 2 + Js) :=
      mul_nonneg (add_nonneg hsp hsq) (by linarith)
    nlinarith

end

section

/-- Expectation of a descendant average of a translation-covariant observable of the actual
field: it is the expectation at the origin cube of the descendant scale. -/
theorem aux_thm_eta_E_descAvg {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (X : Set (Vec d) → CoeffField d → ℝ) (hX : IsTranslationCovariant X)
    (hXm : ∀ Q : TriadicCube d, AEStronglyMeasurable
      (fun a : RegCoeffField d => X (cubeSet Q) a.toFun) (aux_thm_eta_law model N))
    (m : ℤ) (j : ℕ) (hmj : (j : ℤ) ≤ m)
    (hint : Integrable (fun w => X (cubeSet (originCube d (m - j)))
      (aux_thm_eta_field model N w).toFun) (chaosSampleLaw model).toMeasure) :
    Integrable (fun w => descendantsAverage (originCube d m) j
      (fun R => X (cubeSet R) (aux_thm_eta_field model N w).toFun))
      (chaosSampleLaw model).toMeasure ∧
    ∫ w, descendantsAverage (originCube d m) j
        (fun R => X (cubeSet R) (aux_thm_eta_field model N w).toFun)
        ∂(chaosSampleLaw model).toMeasure =
      ∫ w, X (cubeSet (originCube d (m - j))) (aux_thm_eta_field model N w).toFun
        ∂(chaosSampleLaw model).toMeasure := by
  have hA := aux_thm_eta_field_aemeasurable hd model N
  have hstat := aux_thm_eta_law_stationary hd model N
  have hcell : ∀ R ∈ descendantsAtDepth (originCube d m) j,
      Integrable (fun w => X (cubeSet R) (aux_thm_eta_field model N w).toFun)
        (chaosSampleLaw model).toMeasure ∧
      ∫ w, X (cubeSet R) (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure =
        ∫ w, X (cubeSet (originCube d (m - j))) (aux_thm_eta_field model N w).toFun
          ∂(chaosSampleLaw model).toMeasure := by
    intro R hR
    have hsc : R.scale = m - j := by
      have := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [originCube] using this
    have hR0 : 0 ≤ R.scale := by omega
    have h := aux_thm_eta_stat_chaos (aux_thm_eta_field model N) hA hstat X hX hR0
      (hXm _) (hXm R) (by rw [hsc]; exact hint)
    rw [hsc] at h
    exact h
  have hne : ((descendantsAtDepth (originCube d m) j).card : ℝ) ≠ 0 := by
    exact_mod_cast (descendantsAtDepth_nonempty (originCube d m) j).card_ne_zero
  have hsumint : Integrable (fun w => ∑ R ∈ descendantsAtDepth (originCube d m) j,
      X (cubeSet R) (aux_thm_eta_field model N w).toFun) (chaosSampleLaw model).toMeasure :=
    integrable_finset_sum _ fun R hR => (hcell R hR).1
  dsimp only [descendantsAverage]
  refine ⟨hsumint.const_mul _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun R hR => (hcell R hR).1,
    Finset.sum_congr rfl fun R hR => (hcell R hR).2, Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem aux_thm_eta_Jl_law_aesm {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (p q : Vec d) (Q : TriadicCube d) :
    AEStronglyMeasurable (fun a : RegCoeffField d =>
      (fun (U : Set (Vec d)) (b : CoeffField d) => ResponseJ U p q b) (cubeSet Q) a.toFun)
      (aux_thm_eta_law model N) :=
  aux_thm_eta_J_aesm (aux_thm_eta_law_carrier hd model N) Q p q

theorem aux_thm_eta_sep_law_aesm {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (q w : Vec d) (Q : TriadicCube d) :
    AEStronglyMeasurable (fun a : RegCoeffField d =>
      aux_thm_eta_sepObs q w (cubeSet Q) a.toFun) (aux_thm_eta_law model N) :=
  aux_thm_eta_sepObs_aesm (aux_thm_eta_law_carrier hd model N) Q q w

/-- Chaos-level measurability of any law-measurable observable of the actual field. -/
theorem aux_thm_eta_chaos_aesm {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (G : RegCoeffField d → ℝ)
    (hG : AEStronglyMeasurable G (aux_thm_eta_law model N)) :
    AEStronglyMeasurable (fun w => G (aux_thm_eta_field model N w))
      (chaosSampleLaw model).toMeasure :=
  hG.comp_aemeasurable (aux_thm_eta_field_aemeasurable hd model N)

end

section

theorem aux_thm_eta_matVecMul_le {d : ℕ} (M : Mat d) (K : ℝ) (hM : ∀ i j, |M i j| ≤ K)
    (q : Vec d) : vecNormSq (matVecMul M q) ≤ (d : ℝ) ^ 2 * K ^ 2 * vecNormSq q := by
  unfold vecNormSq vecDot matVecMul
  have hrow : ∀ i : Fin d, (∑ j, M i j * q j) * (∑ j, M i j * q j) ≤
      (d : ℝ) * K ^ 2 * ∑ j, q j * q j := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun j => M i j) q
    have hM2 : ∑ j, M i j ^ 2 ≤ (d : ℝ) * K ^ 2 := by
      calc ∑ j, M i j ^ 2 ≤ ∑ _j : Fin d, K ^ 2 := Finset.sum_le_sum fun j _ => by
            have h1 := hM i j
            have h2 := abs_nonneg (M i j)
            have : M i j ^ 2 = |M i j| ^ 2 := (sq_abs _).symm
            rw [this]
            exact pow_le_pow_left₀ h2 h1 2
        _ = (d : ℝ) * K ^ 2 := by simp
    have hq0 : 0 ≤ ∑ j, q j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have e1 : (∑ j, M i j * q j) * (∑ j, M i j * q j) = (∑ j, M i j * q j) ^ 2 := by ring
    have e2 : ∑ j, q j * q j = ∑ j, q j ^ 2 := Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    exact h.trans (mul_le_mul_of_nonneg_right hM2 hq0)
  calc ∑ i, (∑ j, M i j * q j) * (∑ j, M i j * q j)
      ≤ ∑ _i : Fin d, (d : ℝ) * K ^ 2 * ∑ j, q j * q j := Finset.sum_le_sum fun i _ => hrow i
    _ = (d : ℝ) ^ 2 * K ^ 2 * ∑ j, q j * q j := by simp; ring

/-- Bounds for the actual field on an origin cube from a unit-slope response bound. -/
theorem aux_thm_eta_field_bounds {d : ℕ} [NeZero d] (hJ : in_J d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (Q : TriadicCube d) (Js : ℝ)
    (hJs : ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 →
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q e e
        (aux_thm_eta_field model N omega) ≤ Js) :
    (∀ p q : Vec d, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
        (aux_thm_eta_field model N omega) ≤ 2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) * (1 + Js)) ∧
    (∀ i j, |(coarseBlockMatrix (cubeSet Q) (aux_thm_eta_field model N omega).toFun).lowerRight
        i j| ≤ 2 * d * (1 + Js)) ∧
    (∀ q w : Vec d, aux_thm_eta_sepObs q w (cubeSet Q) (aux_thm_eta_field model N omega).toFun ≤
        2 * ((d : ℝ) ^ 2 * (2 * d * (1 + Js)) ^ 2 * vecNormSq q) + 2 * vecNormSq w) := by
  set b := (aux_thm_eta_fam model N omega).coeffOn Q with hb
  have hJeq : ∀ p q : Vec d, responseJ (cubeDomain Q) b p q =
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
        (aux_thm_eta_field model N omega) := fun p q =>
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      _ _ Q p q
  have hLR : (coarseBlockMatrix (cubeSet Q) (aux_thm_eta_field model N omega).toFun).lowerRight =
      Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) b := by
    rw [Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
      (aux_thm_eta_field_elliptic model N omega) Q, coarseBlockMatrix_lowerRight]
  obtain ⟨-, hR, hJb⟩ := aux_thm_eta_unit_bounds hJ (cubeDomain Q) b
    (aux_thm_eta_fam_symm model N omega Q) Js (fun e he => by rw [hJeq]; exact hJs e he)
  refine ⟨fun p q => by rw [← hJeq]; exact hJb p q, fun i j => by rw [hLR]; exact hR i j, ?_⟩
  intro q w
  unfold aux_thm_eta_sepObs
  refine (aux_thm_eta_vecNormSq_sub_le _ _).trans ?_
  have h := aux_thm_eta_matVecMul_le
    (coarseBlockMatrix (cubeSet Q) (aux_thm_eta_field model N omega).toFun).lowerRight
    (2 * d * (1 + Js)) (fun i j => by rw [hLR]; exact hR i j) q
  linarith

theorem aux_thm_eta_sq_one_add_le (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 ≤ 4 + 2 * x ^ 3 := by
  have h := aux_awc_sq_le_one_add_cube x hx
  nlinarith [sq_nonneg (x - 1)]

/-- Integrability from domination by `(1 + g)^2` with a third moment of `g`. -/
theorem aux_thm_eta_int_dom {Om : Type*} [MeasurableSpace Om] {mu : Measure Om}
    [IsFiniteMeasure mu] (f g : Om → ℝ) (hf : AEStronglyMeasurable f mu)
    (hg3 : Integrable (fun w => g w ^ 3) mu) (hg0 : ∀ w, 0 ≤ g w) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ w, |f w| ≤ C * (1 + g w) ^ 2) : Integrable f mu := by
  refine (((integrable_const (4 : ℝ)).add (hg3.const_mul 2)).const_mul C).mono' hf ?_
  filter_upwards with w
  rw [Real.norm_eq_abs]
  refine (hfb w).trans ?_
  exact mul_le_mul_of_nonneg_left (aux_thm_eta_sq_one_add_le _ (hg0 w)) hC

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The unit-slope moment context of the actual field at a fixed cutoff. -/
def aux_thm_eta_MomCtx (_hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (Js : ℤ → BilateralField d → ℝ) : Prop :=
  (∀ n : ℤ, 0 ≤ n → ∀ w (e : Fin d → ℝ), ∑ i, e i ^ 2 = 1 →
    Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n) e e
      (aux_thm_eta_field model N w) ≤ Js n w) ∧
  (∀ n w, 0 ≤ Js n w) ∧
  (∀ n : ℤ, 0 ≤ n → Integrable (fun w => Js n w ^ 3) (chaosSampleLaw model).toMeasure)

theorem aux_thm_eta_int_J (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (n : ℤ) (hn : 0 ≤ n) (p q : Vec d) :
    Integrable (fun w => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
      (originCube d n) p q (aux_thm_eta_field model N w)) (chaosSampleLaw model).toMeasure := by
  obtain ⟨hJs, hJs0, hJs3⟩ := hM
  refine aux_thm_eta_int_dom _ (Js n) (aux_thm_eta_chaos_aesm hd model N _
      (aux_thm_eta_Jl_law_aesm hd model N p q _)) (hJs3 n hn) (hJs0 n)
    (2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2)) (by positivity) fun w => ?_
  have hb := (aux_thm_eta_field_bounds hJ model N w (originCube d n) (Js n w)
    (fun e he => hJs n hn w e he)).1 p q
  have h0 := Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg
    (originCube d n) p q (aux_thm_eta_field model N w)
  rw [abs_of_nonneg h0]
  have hs : 0 ≤ 2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) := by positivity
  have h1 : 1 + Js n w ≤ (1 + Js n w) ^ 2 := by nlinarith [hJs0 n w]
  exact hb.trans (mul_le_mul_of_nonneg_left h1 hs)

theorem aux_thm_eta_int_X (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (n : ℤ) (hn : 0 ≤ n) (q w0 : Vec d) :
    Integrable (fun w => aux_thm_eta_sepObs q w0 (cubeSet (originCube d n))
      (aux_thm_eta_field model N w).toFun) (chaosSampleLaw model).toMeasure := by
  obtain ⟨hJs, hJs0, hJs3⟩ := hM
  refine aux_thm_eta_int_dom _ (Js n) (aux_thm_eta_chaos_aesm hd model N _
      (aux_thm_eta_sep_law_aesm hd model N q w0 _)) (hJs3 n hn) (hJs0 n)
    (2 * ((d : ℝ) ^ 2 * (2 * d) ^ 2 * vecNormSq q) + 2 * vecNormSq w0)
    (by have := vecNormSq_nonneg q; have := vecNormSq_nonneg w0; positivity) fun w => ?_
  have hb := (aux_thm_eta_field_bounds hJ model N w (originCube d n) (Js n w)
    (fun e he => hJs n hn w e he)).2.2 q w0
  have hX0 : 0 ≤ aux_thm_eta_sepObs q w0 (cubeSet (originCube d n))
      (aux_thm_eta_field model N w).toFun := vecNormSq_nonneg _
  rw [abs_of_nonneg hX0]
  refine hb.trans ?_
  have hq := vecNormSq_nonneg q
  have hw := vecNormSq_nonneg w0
  have h0 := hJs0 n w
  have h1 : 1 ≤ (1 + Js n w) ^ 2 := by nlinarith
  have e : 2 * ((d : ℝ) ^ 2 * (2 * d * (1 + Js n w)) ^ 2 * vecNormSq q) =
      2 * ((d : ℝ) ^ 2 * (2 * d) ^ 2 * vecNormSq q) * (1 + Js n w) ^ 2 := by ring
  rw [e]
  have : 2 * vecNormSq w0 ≤ 2 * vecNormSq w0 * (1 + Js n w) ^ 2 := by nlinarith
  nlinarith

/-- Expectation of the response additivity defect. -/
theorem aux_thm_eta_ED (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (m n : ℤ) (hn : 0 ≤ n) (hnm : n ≤ m) (p q : Vec d) :
    Integrable (fun w =>
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q
        (aux_thm_eta_field model N w)) (chaosSampleLaw model).toMeasure ∧
    ∫ w, Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q
        (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure =
      (∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q
        (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) -
      ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure := by
  have hj : ((m - n).toNat : ℤ) ≤ m := by omega
  have hmj : m - ((m - n).toNat : ℤ) = n := by omega
  obtain ⟨hi, he⟩ := aux_thm_eta_E_descAvg hd model N (fun U b => ResponseJ U p q b)
    (Homogenization.Book.Ch04.responseJCubeSet_translation_covariant p q)
    (fun Q => aux_thm_eta_Jl_law_aesm hd model N p q Q) m (m - n).toNat hj
    (by rw [hmj]; exact aux_thm_eta_int_J hd hJ model N Js hM n hn p q)
  rw [hmj] at he
  have hJm := aux_thm_eta_int_J hd hJ model N Js hM m (le_trans hn hnm) p q
  refine ⟨hi.sub hJm, ?_⟩
  show ∫ w, (descendantsAverage (originCube d m) (m - n).toNat
      (fun R => ResponseJ (cubeSet R) p q (aux_thm_eta_field model N w).toFun) -
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (aux_thm_eta_field model N w)) ∂(chaosSampleLaw model).toMeasure = _
  rw [integral_sub hi hJm, he]
  rfl

/-- Expectation of the descendant average of the flux deviation. -/
theorem aux_thm_eta_EXd (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (m n : ℤ) (hn : 0 ≤ n) (hnm : n ≤ m) (q w0 : Vec d) :
    Integrable (fun w => descendantsAverage (originCube d m) (m - n).toNat (fun R =>
      aux_thm_eta_sepObs q w0 (cubeSet R) (aux_thm_eta_field model N w).toFun))
      (chaosSampleLaw model).toMeasure ∧
    ∫ w, descendantsAverage (originCube d m) (m - n).toNat (fun R =>
        aux_thm_eta_sepObs q w0 (cubeSet R) (aux_thm_eta_field model N w).toFun)
        ∂(chaosSampleLaw model).toMeasure =
      ∫ w, aux_thm_eta_sepObs q w0 (cubeSet (originCube d n)) (aux_thm_eta_field model N w).toFun
        ∂(chaosSampleLaw model).toMeasure := by
  have hj : ((m - n).toNat : ℤ) ≤ m := by omega
  have hmj : m - ((m - n).toNat : ℤ) = n := by omega
  obtain ⟨hi, he⟩ := aux_thm_eta_E_descAvg hd model N (aux_thm_eta_sepObs q w0)
    (aux_thm_eta_sepObs_cov q w0) (fun Q => aux_thm_eta_sep_law_aesm hd model N q w0 Q) m
    (m - n).toNat hj (by rw [hmj]; exact aux_thm_eta_int_X hd hJ model N Js hM n hn q w0)
  rw [hmj] at he
  exact ⟨hi, he⟩

end

section

theorem aux_thm_eta_int_wsum {Om : Type*} [MeasurableSpace Om] {mu : Measure Om}
    (s : Finset ℤ) (w : ℤ → ℝ) (f : ℤ → Om → ℝ) (hf : ∀ n ∈ s, Integrable (f n) mu) :
    Integrable (fun x => ∑ n ∈ s, w n * f n x) mu ∧
      ∫ x, ∑ n ∈ s, w n * f n x ∂mu = ∑ n ∈ s, w n * ∫ x, f n x ∂mu := by
  refine ⟨integrable_finset_sum _ fun n hn => (hf n hn).const_mul _, ?_⟩
  rw [integral_finset_sum _ fun n hn => (hf n hn).const_mul _]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

theorem aux_thm_eta_int_add4 {Om : Type*} [MeasurableSpace Om] {mu : Measure Om}
    (f1 f2 f3 f4 : Om → ℝ) (h1 : Integrable f1 mu) (h2 : Integrable f2 mu)
    (h3 : Integrable f3 mu) (h4 : Integrable f4 mu) :
    Integrable (fun x => f1 x + f2 x + f3 x + f4 x) mu ∧
      ∫ x, (f1 x + f2 x + f3 x + f4 x) ∂mu =
        (∫ x, f1 x ∂mu) + (∫ x, f2 x ∂mu) + (∫ x, f3 x ∂mu) + ∫ x, f4 x ∂mu := by
  have h12 : Integrable (fun x => f1 x + f2 x) mu := h1.add h2
  have h123 : Integrable (fun x => f1 x + f2 x + f3 x) mu := h12.add h3
  refine ⟨h123.add h4, ?_⟩
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]

theorem aux_thm_eta_defect_one {d : ℕ} (m : ℤ) (p q : Vec d) (a : RegCoeffField d) :
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1)
        p q a =
      descendantsAverage (originCube d m) 1 (fun R =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q a) -
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a := by
  have h : (m - (m - 1)).toNat = 1 := by omega
  unfold Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
  rw [h]

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Expectation of the collected error `Y` of the truncated bound. -/
theorem aux_thm_eta_EY (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (m l : ℤ) (hl : 0 ≤ l) (hlm : l ≤ m) (p q : Vec d) :
    Integrable (fun w =>
      (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
          Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            m n p q (aux_thm_eta_field model N w)) +
        (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
              (aux_thm_eta_field model N w).toFun +
            2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
              aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))) +
        ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
            (aux_thm_eta_field model N w) +
        aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N w).toFun)
      (chaosSampleLaw model).toMeasure ∧
    ∫ w, ((∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
          Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            m n p q (aux_thm_eta_field model N w)) +
        (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
              (aux_thm_eta_field model N w).toFun +
            2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
              aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))) +
        ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
            (aux_thm_eta_field model N w) +
        aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N w).toFun)
      ∂(chaosSampleLaw model).toMeasure =
      (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
          ((∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n)
              p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) -
            ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m)
              p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure)) +
        (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          (2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d m))
              (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure +
            2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d n))
              (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure)) +
        ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
          ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
            (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure +
        ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N w).toFun
          ∂(chaosSampleLaw model).toMeasure := by
  have hm : 0 ≤ m := le_trans hl hlm
  have hD : ∀ n ∈ Finset.Icc l m, Integrable (fun w =>
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        m n p q (aux_thm_eta_field model N w)) (chaosSampleLaw model).toMeasure ∧
      ∫ w, Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        m n p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure =
      (∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n)
          p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) -
        ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m)
          p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure := by
    intro n hn
    have h := Finset.mem_Icc.mp hn
    exact aux_thm_eta_ED hd hJ model N Js hM m n (by omega) h.2 p q
  have hXm := aux_thm_eta_int_X hd hJ model N Js hM m hm q p
  have hXd : ∀ n ∈ Finset.Icc l m, Integrable (fun w =>
      2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N w).toFun +
        2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
          aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))
      (chaosSampleLaw model).toMeasure ∧
      ∫ w, (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
          (aux_thm_eta_field model N w).toFun +
        2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
          aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))
        ∂(chaosSampleLaw model).toMeasure =
      2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d m))
          (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure +
        2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d n))
          (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure := by
    intro n hn
    have h := Finset.mem_Icc.mp hn
    obtain ⟨hi, he⟩ := aux_thm_eta_EXd hd hJ model N Js hM m n (by omega) h.2 q p
    refine ⟨(hXm.const_mul 2).add (hi.const_mul 2), ?_⟩
    rw [integral_add (hXm.const_mul 2) (hi.const_mul 2), integral_const_mul, integral_const_mul,
      he]
  obtain ⟨hS1i, hS1e⟩ := aux_thm_eta_int_wsum (Finset.Icc l m)
    (fun n => (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)))
    (fun n w => Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
      m n p q (aux_thm_eta_field model N w)) fun n hn => (hD n hn).1
  obtain ⟨hS2i, hS2e⟩ := aux_thm_eta_int_wsum (Finset.Icc l m)
    (fun n => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)))
    (fun n w => 2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
        (aux_thm_eta_field model N w).toFun +
      2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
        aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))
    fun n hn => (hXd n hn).1
  have hJm := (aux_thm_eta_int_J hd hJ model N Js hM m hm p q).const_mul
    (((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2)
  refine ⟨(aux_thm_eta_int_add4 _ _ _ _ hS1i hS2i hJm hXm).1,
    (aux_thm_eta_int_add4 _ _ _ _ hS1i hS2i hJm hXm).2.trans ?_⟩
  rw [hS1e, hS2e, integral_const_mul]
  congr 3
  · exact Finset.sum_congr rfl fun n hn => by rw [(hD n hn).2]
  · exact Finset.sum_congr rfl fun n hn => by rw [(hXd n hn).2]

end

section

theorem aux_thm_eta_Y_nonneg {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (w : BilateralField d) (m l : ℤ) (p q : Vec d) :
    0 ≤ (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
          Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            m n p q (aux_thm_eta_field model N w)) +
        (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
              (aux_thm_eta_field model N w).toFun +
            2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
              aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun))) +
        ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
            (aux_thm_eta_field model N w) +
        aux_thm_eta_sepObs q p (cubeSet (originCube d m)) (aux_thm_eta_field model N w).toFun := by
  have h1 : 0 ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
        m n p q (aux_thm_eta_field model N w) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
        _ (aux_thm_eta_field_elliptic model N w) m n p q)
  have hX : ∀ U : Set (Vec d), 0 ≤ aux_thm_eta_sepObs q p U (aux_thm_eta_field model N w).toFun :=
    fun U => vecNormSq_nonneg _
  have h2 : 0 ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      (2 * aux_thm_eta_sepObs q p (cubeSet (originCube d m))
          (aux_thm_eta_field model N w).toFun +
        2 * descendantsAverage (originCube d m) (m - n).toNat (fun R =>
          aux_thm_eta_sepObs q p (cubeSet R) (aux_thm_eta_field model N w).toFun)) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (mul_nonneg (by norm_num) (hX _))
        (mul_nonneg (by norm_num) (descendantsAverage_nonneg _ _ _ fun R _ => hX _)))
  have h3 : 0 ≤ ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (aux_thm_eta_field model N w) :=
    mul_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg _ _ _ _)
  have h4 := hX (cubeSet (originCube d m))
  linarith

theorem aux_thm_eta_int_add3 {Om : Type*} [MeasurableSpace Om] {mu : Measure Om}
    (f1 f2 f3 : Om → ℝ) (h1 : Integrable f1 mu) (h2 : Integrable f2 mu)
    (h3 : Integrable f3 mu) :
    Integrable (fun x => f1 x + f2 x + f3 x) mu ∧
      ∫ x, (f1 x + f2 x + f3 x) ∂mu = (∫ x, f1 x ∂mu) + (∫ x, f2 x ∂mu) + ∫ x, f3 x ∂mu := by
  have h12 : Integrable (fun x => f1 x + f2 x) mu := h1.add h2
  refine ⟨h12.add h3, ?_⟩
  rw [integral_add h12 h3, integral_add h1 h2]

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The truncated bound integrated over the chaos law: the paper's expectation step on
`{K_m ≤ A}`, with the complement kept as an indicator term. -/
theorem aux_thm_eta_PE (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
      (Js : ℤ → BilateralField d → ℝ), aux_thm_eta_MomCtx hJ model N Js →
      ∀ (m l : ℤ), 0 ≤ l → l ≤ m → 1 ≤ m → ∀ (p q : Vec d)
      (Fam : BilateralField d → TriadicCoeffFamily d),
      (∀ w, TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N w) (Fam w)) →
      (∀ w, 0 < lambdaSq (originCube d m) (1 / 4) (.finite 1) (Fam w)) →
      (∀ w, 0 ≤ LambdaSq (originCube d m) (1 / 4) (.finite 1) (Fam w)) →
      ∀ (A : ℝ) (T : Set (BilateralField d)), MeasurableSet T →
      (∀ w, w ∉ T → 1 + LambdaSq (originCube d m) (1 / 4) (.finite 1) (Fam w) +
        (lambdaSq (originCube d m) (1 / 4) (.finite 1) (Fam w))⁻¹ ≤ A) →
      ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1))
          p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure ≤
        C * A ^ 4 *
          ((∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
            ((∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n)
                p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) -
              ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m)
                p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure)) +
          (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            (2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d m))
                (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure +
              2 * ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d n))
                (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure)) +
          ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 *
            ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m)
              p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure +
          ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d m))
            (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure) +
        2 * (3 : ℝ) ^ d *
          ((∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
              (originCube d (m - 1)) p q (aux_thm_eta_field model N w)
                ∂(chaosSampleLaw model).toMeasure) -
            ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m)
              p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) +
        ∫ w, T.indicator (fun w => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          (originCube d (m - 1)) p q (aux_thm_eta_field model N w)) w
          ∂(chaosSampleLaw model).toMeasure := by
  obtain ⟨C, hC, hpw⟩ := aux_thm_eta_pw d
  refine ⟨C, hC, ?_⟩
  intro model N Js hM m l hl hlm hm1 p q Fam hFam hpos hL0 A T hT hTc
  obtain ⟨hYi, hYe⟩ := aux_thm_eta_EY hd hJ model N Js hM m l hl hlm p q
  have hJ1 := aux_thm_eta_int_J hd hJ model N Js hM (m - 1) (by omega) p q
  have hJm := aux_thm_eta_int_J hd hJ model N Js hM m (by omega) p q
  obtain ⟨hJdi, hJde⟩ := aux_thm_eta_E_descAvg hd model N (fun U b => ResponseJ U p q b)
    (Homogenization.Book.Ch04.responseJCubeSet_translation_covariant p q)
    (fun Q => aux_thm_eta_Jl_law_aesm hd model N p q Q) m 1 (by omega)
    (by simpa using hJ1)
  have hJde' : ∫ w, descendantsAverage (originCube d m) 1 (fun R =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q
        (aux_thm_eta_field model N w)) ∂(chaosSampleLaw model).toMeasure =
      ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1))
        p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure := by
    simpa using hJde
  have hJdi' : Integrable (fun w => descendantsAverage (originCube d m) 1 (fun R =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q
        (aux_thm_eta_field model N w))) (chaosSampleLaw model).toMeasure := hJdi
  have hDi : Integrable (fun w => descendantsAverage (originCube d m) 1 (fun R =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q
        (aux_thm_eta_field model N w)) -
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (aux_thm_eta_field model N w)) (chaosSampleLaw model).toMeasure := hJdi'.sub hJm
  have hsum := aux_thm_eta_int_add3 _ _ _ (hYi.const_mul (C * A ^ 4))
    (hDi.const_mul (2 * (3 : ℝ) ^ d)) (hJ1.indicator hT)
  refine le_trans (integral_mono hJ1 hsum.1 fun w => ?_) (le_of_eq ?_)
  · by_cases hw : w ∈ T
    · rw [Set.indicator_of_mem hw]
      have hY0 := aux_thm_eta_Y_nonneg model N w m l p q
      have hD0 : 0 ≤ descendantsAverage (originCube d m) 1 (fun R =>
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q
            (aux_thm_eta_field model N w)) -
          Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
            (aux_thm_eta_field model N w) := by
        rw [← aux_thm_eta_defect_one]
        exact Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
          _ (aux_thm_eta_field_elliptic model N w) m (m - 1) p q
      have h1 : 0 ≤ C * A ^ 4 := mul_nonneg hC.le (by positivity)
      have h2 : 0 ≤ 2 * (3 : ℝ) ^ d := by positivity
      have := mul_nonneg h1 hY0
      have := mul_nonneg h2 hD0
      linarith
    · rw [Set.indicator_of_notMem hw, add_zero]
      exact hpw model N w m l hlm p q (Fam w) (hFam w) A (hpos w) (hL0 w) (hTc w hw)
  · rw [hsum.2, integral_const_mul, integral_const_mul, hYe, integral_sub hJdi' hJm, hJde']

end

section

theorem aux_thm_eta_ind_le (x M : ℝ) (hx : 0 ≤ x) (hM : 0 < M) : x ≤ M + x ^ 2 / M := by
  rcases le_or_gt x M with h | h
  · have : 0 ≤ x ^ 2 / M := by positivity
    linarith
  · have : x ≤ x ^ 2 / M := by
      rw [le_div_iff₀ hM]
      nlinarith
    linarith

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Uniform integrability of the central-child response from the third moment of `Jsup`. -/
theorem aux_thm_eta_UI (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (Js : ℤ → BilateralField d → ℝ) (hM : aux_thm_eta_MomCtx hJ model N Js)
    (B3 : ℝ) (hB3 : ∀ n : ℤ, 0 ≤ n → ∫ w, Js n w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B3)
    (n : ℤ) (hn : 0 ≤ n) (p q : Vec d) (T : Set (BilateralField d)) (hT : MeasurableSet T)
    (M : ℝ) (hMpos : 0 < M) :
    ∫ w, T.indicator (fun w => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (originCube d n) p q (aux_thm_eta_field model N w)) w ∂(chaosSampleLaw model).toMeasure ≤
      2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) *
        (M * ((chaosSampleLaw model).toMeasure T).toReal + (4 + 2 * B3) / M) := by
  obtain ⟨hJs, hJs0, hJs3⟩ := hM
  set S : ℝ := 2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) with hS
  have hS0 : 0 ≤ S := by positivity
  set μ := (chaosSampleLaw model).toMeasure
  have hpt : ∀ w, T.indicator (fun w => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
      (originCube d n) p q (aux_thm_eta_field model N w)) w ≤
      S * (M * T.indicator (fun _ => (1 : ℝ)) w + (4 + 2 * Js n w ^ 3) / M) := by
    intro w
    have hq : 0 ≤ (4 + 2 * Js n w ^ 3) / M := by
      have := hJs0 n w
      positivity
    by_cases hw : w ∈ T
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, mul_one]
      have hb := (aux_thm_eta_field_bounds hJ model N w (originCube d n) (Js n w)
        (fun e he => hJs n hn w e he)).1 p q
      have h1 := aux_thm_eta_ind_le (1 + Js n w) M (by linarith [hJs0 n w]) hMpos
      have h2 : (1 + Js n w) ^ 2 / M ≤ (4 + 2 * Js n w ^ 3) / M :=
        div_le_div_of_nonneg_right (aux_thm_eta_sq_one_add_le _ (hJs0 n w)) hMpos.le
      calc _ ≤ S * (1 + Js n w) := hb
        _ ≤ S * (M + (4 + 2 * Js n w ^ 3) / M) :=
          mul_le_mul_of_nonneg_left (by linarith) hS0
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero, zero_add]
      exact mul_nonneg hS0 hq
  have hi3 := hJs3 n hn
  have hint : Integrable (fun w => S * (M * T.indicator (fun _ => (1 : ℝ)) w +
      (4 + 2 * Js n w ^ 3) / M)) μ :=
    (((integrable_const (1 : ℝ)).indicator hT).const_mul M |>.add
      (((integrable_const (4 : ℝ)).add (hi3.const_mul 2)).div_const M)).const_mul S
  have hJint : Integrable (fun w => T.indicator (fun w =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (originCube d n) p q (aux_thm_eta_field model N w)) w) μ :=
    (aux_thm_eta_int_J hd hJ model N Js ⟨hJs, hJs0, hJs3⟩ n hn p q).indicator hT
  refine (integral_mono hJint hint hpt).trans ?_
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hS0
  have hind : Integrable (fun w => M * T.indicator (fun _ => (1 : ℝ)) w) μ :=
    ((integrable_const (1 : ℝ)).indicator hT).const_mul M
  have hrest : Integrable (fun w => (4 + 2 * Js n w ^ 3) / M) μ :=
    ((integrable_const (4 : ℝ)).add (hi3.const_mul 2)).div_const M
  have e1 : ∫ w, M * T.indicator (fun _ => (1 : ℝ)) w ∂μ = M * (μ T).toReal := by
    rw [integral_const_mul, integral_indicator hT, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  have e2 : ∫ w, (4 + 2 * Js n w ^ 3) / M ∂μ = (4 + 2 * ∫ w, Js n w ^ 3 ∂μ) / M := by
    rw [integral_div, integral_add (integrable_const 4) (hi3.const_mul 2), integral_const_mul]
    simp [probReal_univ]
  rw [integral_add hind hrest, e1, e2]
  have h3 := hB3 n hn
  have : (4 + 2 * ∫ w, Js n w ^ 3 ∂μ) / M ≤ (4 + 2 * B3) / M :=
    div_le_div_of_nonneg_right (by linarith) hMpos.le
  linarith

end

section

/-- The collected expected error vanishes along the extracted subsequence. -/
theorem aux_thm_eta_ylim (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) (G X : ℕ → ℤ → ℝ)
    (Glim : ℝ)
    (hG : ∀ δ > 0, ∀ᶠ j in atTop, ∀ n : ℤ, 2 * (k j : ℤ) ≤ n → n ≤ 4 * (k j : ℤ) →
      |G j n - Glim| ≤ δ)
    (hX : ∀ δ > 0, ∀ᶠ j in atTop, ∀ n : ℤ, 2 * (k j : ℤ) ≤ n → n ≤ 4 * (k j : ℤ) →
      X j n ≤ δ) :
    ∀ δ > 0, ∀ᶠ j in atTop,
      (∑ n ∈ Finset.Icc (2 * (k j : ℤ)) (4 * (k j : ℤ)),
          (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((4 * (k j : ℤ) - n : ℤ) : ℝ)) *
            (G j n - G j (4 * (k j : ℤ)))) +
        (∑ n ∈ Finset.Icc (2 * (k j : ℤ)) (4 * (k j : ℤ)),
          (3 : ℝ) ^ (-((4 * (k j : ℤ) - n : ℤ) : ℝ)) *
            (2 * X j (4 * (k j : ℤ)) + 2 * X j n)) +
        ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((4 * (k j : ℤ) - 2 * (k j : ℤ) : ℤ) : ℝ))) ^ 2 *
          G j (4 * (k j : ℤ)) +
        X j (4 * (k j : ℤ)) ≤ δ := by
  intro δ hδ
  set W1 : ℝ := (1 - (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ)))⁻¹ with hW1
  set W2 : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ with hW2
  have hW1pos : 0 < W1 := by
    rw [hW1]
    have : (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact inv_pos.mpr (by linarith)
  have hW2pos : 0 < W2 := by
    rw [hW2]
    have : (3 : ℝ) ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact inv_pos.mpr (by linarith)
  set η : ℝ := min 1 (δ / 2 / (2 * W1 + 4 * W2 + 1)) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : (2 * W1 + 4 * W2 + 1) * η ≤ δ / 2 := by
    have h := min_le_right 1 (δ / 2 / (2 * W1 + 4 * W2 + 1))
    rw [← hη] at h
    have hpos : 0 < 2 * W1 + 4 * W2 + 1 := by positivity
    calc (2 * W1 + 4 * W2 + 1) * η ≤ (2 * W1 + 4 * W2 + 1) * (δ / 2 / (2 * W1 + 4 * W2 + 1)) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = δ / 2 := by field_simp
  -- the discarded-scale weight
  have hw3 : Tendsto (fun j => ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) *
      ((4 * (k j : ℤ) - 2 * (k j : ℤ) : ℤ) : ℝ))) ^ 2 * (|Glim| + 1)) atTop (𝓝 0) := by
    have h0 := (aux_awc_rpow_tendsto 3 (by norm_num)).comp hk
    have heq : (fun j => (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((4 * (k j : ℤ) - 2 * (k j : ℤ) : ℤ) : ℝ)))
        = (fun k : ℕ => Real.rpow 3 (-(((3 : ℕ) : ℝ) / 2) * (k : ℝ))) ∘ k := by
      funext j
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring
    rw [← heq] at h0
    simpa using (h0.pow 2).mul_const (|Glim| + 1)
  have hev3 := (tendsto_order.1 hw3).2 (δ / 2) (by positivity)
  filter_upwards [hG η hηpos, hX η hηpos, hev3] with j hGj hXj h3j
  set m : ℤ := 4 * (k j : ℤ) with hm
  set l : ℤ := 2 * (k j : ℤ) with hl
  have hlm : l ≤ m := by omega
  have hGm := hGj m hlm le_rfl
  have hXm := hXj m hlm le_rfl
  have hs1 : ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) *
      (G j n - G j m) ≤ W1 * (2 * η) := by
    calc _ ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ)) * (2 * η) :=
          Finset.sum_le_sum fun n hn => by
            have h := Finset.mem_Icc.mp hn
            have h1 := hGj n h.1 h.2
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
            have := abs_le.mp h1
            have := abs_le.mp hGm
            linarith
      _ = (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - n : ℤ) : ℝ))) * (2 * η) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ W1 * (2 * η) := mul_le_mul_of_nonneg_right
          (aux_thm_eta_geom (1 - 1 / 4) (by norm_num) l m) (by positivity)
  have hs2 : ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      (2 * X j m + 2 * X j n) ≤ W2 * (4 * η) := by
    calc _ ≤ ∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * (4 * η) :=
          Finset.sum_le_sum fun n hn => by
            have h := Finset.mem_Icc.mp hn
            have h1 := hXj n h.1 h.2
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
            linarith
      _ = (∑ n ∈ Finset.Icc l m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ))) * (4 * η) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ W2 * (4 * η) := mul_le_mul_of_nonneg_right
          (by simpa only [neg_mul, one_mul] using aux_thm_eta_geom 1 (by norm_num) l m)
          (by positivity)
  have hs3 : ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((m - l : ℤ) : ℝ))) ^ 2 * G j m ≤ δ / 2 := by
    have hGb : G j m ≤ |Glim| + 1 := by
      have := abs_le.mp hGm
      have := le_abs_self Glim
      linarith
    refine le_trans ?_ h3j.le
    exact mul_le_mul_of_nonneg_left hGb (sq_nonneg _)
  have e : W1 * (2 * η) + W2 * (4 * η) + η = (2 * W1 + 4 * W2 + 1) * η := by ring
  refine (add_le_add (add_le_add (add_le_add hs1 hs2) hs3) hXm).trans ?_
  linarith

/-- The final `ε`-management: truncation level first, then the vanishing errors. -/
theorem aux_thm_eta_alim (C S B c3 : ℝ) (hC : 0 ≤ C) (hS : 0 ≤ S) (hB : 0 ≤ B) (hc3 : 0 ≤ c3)
    (x Y D : ℕ → ℝ) (tau : ℝ → ℕ → ℝ)
    (hPE : ∀ A, 1 ≤ A → ∀ M, 0 < M → ∀ j, x j ≤ C * A ^ 4 * Y j + c3 * D j +
      S * (M * tau A j + B / M))
    (htight : ∀ ε > 0, ∃ A, 1 ≤ A ∧ ∀ j, tau A j ≤ ε)
    (hY : ∀ δ > 0, ∀ᶠ j in atTop, Y j ≤ δ) (hD : ∀ δ > 0, ∀ᶠ j in atTop, D j ≤ δ) :
    ∀ ε > 0, ∀ᶠ j in atTop, x j ≤ ε := by
  intro ε hε
  set M : ℝ := 4 * (S + 1) * (B + 1) / ε with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨A, hA1, hA⟩ := htight (ε / (4 * (S + 1) * M)) (by positivity)
  have hCA : 0 ≤ C * A ^ 4 := mul_nonneg hC (by positivity)
  filter_upwards [hY (ε / (4 * (C * A ^ 4 + 1))) (by positivity),
    hD (ε / (4 * (c3 + 1))) (by positivity)] with j hYj hDj
  have h := hPE A hA1 M hMpos j
  have h1 : C * A ^ 4 * Y j ≤ ε / 4 := by
    calc C * A ^ 4 * Y j ≤ (C * A ^ 4 + 1) * (ε / (4 * (C * A ^ 4 + 1))) := by
          rcases le_or_gt (Y j) 0 with hy | hy
          · have : C * A ^ 4 * Y j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCA hy
            have : 0 ≤ (C * A ^ 4 + 1) * (ε / (4 * (C * A ^ 4 + 1))) := by positivity
            linarith
          · exact mul_le_mul (by linarith) hYj hy.le (by positivity)
      _ = ε / 4 := by field_simp
  have h2 : c3 * D j ≤ ε / 4 := by
    calc c3 * D j ≤ (c3 + 1) * (ε / (4 * (c3 + 1))) := by
          rcases le_or_gt (D j) 0 with hy | hy
          · have : c3 * D j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc3 hy
            have : 0 ≤ (c3 + 1) * (ε / (4 * (c3 + 1))) := by positivity
            linarith
          · exact mul_le_mul (by linarith) hDj hy.le (by positivity)
      _ = ε / 4 := by field_simp
  have h3 : S * (M * tau A j + B / M) ≤ ε / 2 := by
    have ht := hA j
    have e1 : S * (M * tau A j) ≤ ε / 4 := by
      calc S * (M * tau A j) ≤ (S + 1) * (M * (ε / (4 * (S + 1) * M))) := by
            rcases le_or_gt (tau A j) 0 with hy | hy
            · have : S * (M * tau A j) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hS (mul_nonpos_of_nonneg_of_nonpos hMpos.le hy)
              have : 0 ≤ (S + 1) * (M * (ε / (4 * (S + 1) * M))) := by positivity
              linarith
            · exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left ht hMpos.le)
                (by positivity) (by positivity)
        _ = ε / 4 := by field_simp
    have e2 : S * (B / M) ≤ ε / 4 := by
      rw [hM]
      have hSB : S * B ≤ (S + 1) * (B + 1) := by nlinarith
      calc S * (B / (4 * (S + 1) * (B + 1) / ε)) = S * B * ε / (4 * (S + 1) * (B + 1)) := by
            field_simp
        _ ≤ (S + 1) * (B + 1) * ε / (4 * (S + 1) * (B + 1)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hSB hε.le
        _ = ε / 4 := by field_simp
    rw [mul_add]
    linarith
  linarith

end

section

theorem aux_thm_eta_L2_bounds {Om : Type*} [MeasurableSpace Om] {mu : Measure Om}
    [IsProbabilityMeasure mu] (f : Om → ℝ) (hf : AEStronglyMeasurable f mu)
    (hsq : Integrable (fun w => f w ^ 2) mu) (ε : ℝ) (hε : 0 ≤ ε)
    (h : eLpNorm f 2 mu ≤ ENNReal.ofReal ε) :
    ∫ w, f w ^ 2 ∂mu ≤ ε ^ 2 ∧ |∫ w, f w ∂mu| ≤ ε := by
  have hmem : MemLp f 2 mu := (memLp_two_iff_integrable_sq hf).2 hsq
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at h
  have h2 : (∫ w, ‖f w‖ ^ ((2 : ℝ≥0∞).toReal) ∂mu) ^ ((2 : ℝ≥0∞).toReal)⁻¹ ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε).1 h
  have e : (fun w => ‖f w‖ ^ ((2 : ℝ≥0∞).toReal)) = fun w => f w ^ 2 := by
    funext w
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [e, show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num] at h2
  have hI0 : 0 ≤ ∫ w, f w ^ 2 ∂mu := integral_nonneg fun w => sq_nonneg _
  have hsqrt : Real.sqrt (∫ w, f w ^ 2 ∂mu) ≤ ε := by
    rw [Real.sqrt_eq_rpow]
    exact h2
  have hI : ∫ w, f w ^ 2 ∂mu ≤ ε ^ 2 := by
    have := Real.sq_sqrt hI0
    nlinarith [Real.sqrt_nonneg (∫ w, f w ^ 2 ∂mu)]
  refine ⟨hI, ?_⟩
  have hfi : Integrable f mu := hmem.integrable (by norm_num)
  set c := ∫ w, f w ∂mu with hc
  have hvar : 0 ≤ ∫ w, (f w - c) ^ 2 ∂mu := integral_nonneg fun w => sq_nonneg _
  have hexp : ∫ w, (f w - c) ^ 2 ∂mu = ∫ w, f w ^ 2 ∂mu - c ^ 2 := by
    have e1 : (fun w => (f w - c) ^ 2) = fun w => f w ^ 2 - 2 * c * f w + c ^ 2 := by
      funext w; ring
    have i1 : Integrable (fun w => f w ^ 2 - 2 * c * f w) mu := hsq.sub (hfi.const_mul _)
    rw [e1, integral_add i1 (integrable_const _),
      integral_sub hsq (hfi.const_mul _), integral_const_mul, integral_const]
    simp [probReal_univ, ← hc]
    ring
  have : c ^ 2 ≤ ε ^ 2 := by linarith
  exact abs_le_of_sq_le_sq' this hε |> fun h => abs_le.mpr h

theorem aux_thm_eta_quad_diff {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    |x ⬝ᵥ M.mulVec x| ≤ (∑ i, |x i|) ^ 2 * ∑ a, ∑ b, |M a b| := by
  have hx : ∀ i, |x i| ≤ ∑ i, |x i| := fun i =>
    Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have hS : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun a _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [abs_mul, abs_mul]
  have h1 : |x a| * |x b| ≤ (∑ i, |x i|) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hx a) (hx b) (abs_nonneg _) hS
  calc |x a| * (|M a b| * |x b|) = (|x a| * |x b|) * |M a b| := by ring
    _ ≤ (∑ i, |x i|) ^ 2 * |M a b| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem aux_thm_eta_vecNormSq_mat_le {d : ℕ} (M : Mat d) (q : Vec d) :
    vecNormSq (matVecMul M q) ≤ (∑ a, ∑ b, M a b ^ 2) * vecNormSq q := by
  unfold vecNormSq vecDot matVecMul
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun b => M a b) q
  have e1 : (∑ b, M a b * q b) * (∑ b, M a b * q b) = (∑ b, M a b * q b) ^ 2 := by ring
  have e2 : ∑ j, q j * q j = ∑ j, q j ^ 2 := Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  exact h

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The expected response on an origin cube in terms of the annealed matrices. -/
theorem aux_thm_eta_EJ_eq (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0f : ∀ N k w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x))
    (N k : ℕ)
    (hIP : ∀ a b, Integrable (fun w => Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) (chaosSampleLaw model).toMeasure)
    (hIR : ∀ a b, Integrable (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) (chaosSampleLaw model).toMeasure)
    (p q : Vec d) :
    ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ))
        p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure =
      (1 / 2 : ℝ) * p ⬝ᵥ (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).mulVec p +
        (1 / 2 : ℝ) * q ⬝ᵥ (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).mulVec q -
        p ⬝ᵥ q := by
  have hsym : ∀ w, CoeffOn.IsSymmetric (a0 N k w) := by
    intro w
    rw [CoeffOn.IsSymmetric]
    filter_upwards [] with x
    rw [ha0f N k w x]
    exact Homogenization.scalarMatrix_isSymm _
  have hpt : ∀ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
      (originCube d (k : ℤ)) p q (aux_thm_eta_field model N w) =
      (1 / 2 : ℝ) * p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec p +
        (1 / 2 : ℝ) * q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec q - p ⬝ᵥ q := by
    intro w
    rw [← aux_thm_eta_J_eq model N w _ (a0 N k w) (ha0f N k w)]
    exact aux_thm_eta_split hJ _ _ (hsym w) p q
  have hQP := aux_awc_integral_quad (chaosSampleLaw model).toMeasure
    (fun w => Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w))
    hIP p
  have hQR := aux_awc_integral_quad (chaosSampleLaw model).toMeasure
    (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
      (a0 N k w)) hIR q
  have hiP : Integrable (fun w => p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec p)
      (chaosSampleLaw model).toMeasure := by
    simp only [dotProduct, Matrix.mulVec]
    exact integrable_finset_sum _ fun a _ => (integrable_finset_sum _ fun b _ =>
      (hIP a b).mul_const _).const_mul _
  have hiR : Integrable (fun w => q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec q)
      (chaosSampleLaw model).toMeasure := by
    simp only [dotProduct, Matrix.mulVec]
    exact integrable_finset_sum _ fun a _ => (integrable_finset_sum _ fun b _ =>
      (hIR a b).mul_const _).const_mul _
  have i1 : Integrable (fun w => (1 / 2 : ℝ) * p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec p)
      (chaosSampleLaw model).toMeasure := hiP.const_mul _
  have i2 : Integrable (fun w => (1 / 2 : ℝ) * q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec q)
      (chaosSampleLaw model).toMeasure := hiR.const_mul _
  have i12 : Integrable (fun w => (1 / 2 : ℝ) * p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec p +
      (1 / 2 : ℝ) * q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w)).mulVec q)
      (chaosSampleLaw model).toMeasure := i1.add i2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub i12 (integrable_const _), integral_add i1 i2, integral_const_mul,
    integral_const_mul, hQP, hQR, integral_const]
  simp [probReal_univ]

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]



def aux_thm_eta_NodeCtx (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ)))) : Prop :=
  (∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x)) ∧
  (∀ (N k : ℕ) (a b : Fin d), Integrable (fun w => Homogenization.Book.Ch02.sigmaCoarse
    (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) (chaosSampleLaw model).toMeasure) ∧
  (∀ (N k : ℕ) (a b : Fin d), Integrable (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
    (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) (chaosSampleLaw model).toMeasure)

theorem aux_thm_eta_Rsq_int (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (N k : ℕ) (c : ℝ) (a b : Fin d) :
    Integrable (fun w => (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - c) ^ 2)
      (chaosSampleLaw model).toMeasure := by
  obtain ⟨ha0f, -, hIR⟩ := hN
  obtain ⟨hJs, hJs0, hJs3⟩ := hM N
  refine aux_thm_eta_int_dom _ (Js N k) (((hIR N k a b).sub (integrable_const c)).1.pow 2)
    (hJs3 k (by positivity)) (hJs0 k) (8 * (d : ℝ) ^ 2 + 2 * c ^ 2) (by positivity) fun w => ?_
  have hb := (aux_thm_eta_field_bounds hJ model N w (originCube d (k : ℤ)) (Js N k w)
    (fun e he => hJs k (by positivity) w e he)).2.1 a b
  rw [← aux_thm_eta_R_eq model N w _ (a0 N k w) (ha0f N k w)] at hb
  set r := Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
    (a0 N k w) a b
  have h0 := hJs0 k w
  rw [abs_of_nonneg (sq_nonneg _)]
  have hr2 : r ^ 2 ≤ (2 * d * (1 + Js N k w)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have h1 : 1 ≤ (1 + Js N k w) ^ 2 := by nlinarith
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [sq_nonneg (r + c)]

/-- The expected response is close to the limit quadratic form in the two windows. -/
theorem aux_thm_eta_G_close (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (N k : ℕ) (Pl Rl : Matrix (Fin d) (Fin d) ℝ)
    (p q : Vec d) (εP εR : ℝ) (hεR : 0 ≤ εR)
    (hP : ∑ a : Fin d, ∑ b : Fin d, |(∫ w, Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) -
        Pl a b| ≤ εP)
    (hR : ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
        (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal εR) :
    |(∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ))
        p q (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure) -
      ((1 / 2 : ℝ) * p ⬝ᵥ Pl.mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - p ⬝ᵥ q)| ≤
      (1 / 2 : ℝ) * (∑ i, |p i|) ^ 2 * εP + (1 / 2 : ℝ) * (∑ i, |q i|) ^ 2 * ((d : ℝ) ^ 2 * εR) := by
  obtain ⟨ha0f, hIP, hIR⟩ := hN
  rw [aux_thm_eta_EJ_eq hJ model a0 ha0f N k (hIP N k) (hIR N k) p q]
  set EP := Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
    (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure
  set ER := Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
    (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure
  have hRe : ∀ a b, |ER a b - Rl a b| ≤ εR := by
    intro a b
    have hsingle : eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
        (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal εR := by
      refine le_trans ?_ hR
      refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b : Fin d, eLpNorm
        (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure) (fun _ _ => zero_le _) (Finset.mem_univ a))
      exact Finset.single_le_sum (f := fun b => eLpNorm
        (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure) (fun _ _ => zero_le _) (Finset.mem_univ b)
    have hL := (aux_thm_eta_L2_bounds (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b)
      ((hIR N k a b).sub (integrable_const _)).1
      (aux_thm_eta_Rsq_int hd hJ model a0 ⟨ha0f, hIP, hIR⟩ Js hM N k (Rl a b) a b) εR hεR hsingle).2
    rw [integral_sub (hIR N k a b) (integrable_const _), integral_const] at hL
    simpa [ER, probReal_univ] using hL
  have hRsum : ∑ a, ∑ b, |(ER - Rl) a b| ≤ (d : ℝ) ^ 2 * εR := by
    calc ∑ a, ∑ b, |(ER - Rl) a b| ≤ ∑ _a : Fin d, ∑ _b : Fin d, εR :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
            simpa [Matrix.sub_apply] using hRe a b
      _ = (d : ℝ) ^ 2 * εR := by simp; ring
  have hPsum : ∑ a, ∑ b, |(EP - Pl) a b| ≤ εP := by
    simpa [Matrix.sub_apply, EP] using hP
  have e : (1 / 2 : ℝ) * p ⬝ᵥ EP.mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ ER.mulVec q - p ⬝ᵥ q -
      ((1 / 2 : ℝ) * p ⬝ᵥ Pl.mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - p ⬝ᵥ q) =
      (1 / 2 : ℝ) * p ⬝ᵥ (EP - Pl).mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ (ER - Rl).mulVec q := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub]
    ring
  rw [e]
  have h1 := aux_thm_eta_quad_diff (EP - Pl) p
  have h2 := aux_thm_eta_quad_diff (ER - Rl) q
  have hp0 : 0 ≤ (∑ i, |p i|) ^ 2 := sq_nonneg _
  have hq0 : 0 ≤ (∑ i, |q i|) ^ 2 := sq_nonneg _
  have h1' : |p ⬝ᵥ (EP - Pl).mulVec p| ≤ (∑ i, |p i|) ^ 2 * εP :=
    h1.trans (mul_le_mul_of_nonneg_left hPsum hp0)
  have h2' : |q ⬝ᵥ (ER - Rl).mulVec q| ≤ (∑ i, |q i|) ^ 2 * ((d : ℝ) ^ 2 * εR) :=
    h2.trans (mul_le_mul_of_nonneg_left hRsum hq0)
  calc |(1 / 2 : ℝ) * p ⬝ᵥ (EP - Pl).mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ (ER - Rl).mulVec q|
      ≤ |(1 / 2 : ℝ) * p ⬝ᵥ (EP - Pl).mulVec p| + |(1 / 2 : ℝ) * q ⬝ᵥ (ER - Rl).mulVec q| :=
        abs_add_le _ _
    _ = (1 / 2 : ℝ) * |p ⬝ᵥ (EP - Pl).mulVec p| + (1 / 2 : ℝ) * |q ⬝ᵥ (ER - Rl).mulVec q| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ _ := by linarith

/-- The expected flux deviation is small in the `L²` window. -/
theorem aux_thm_eta_X_small (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (N k : ℕ) (Rl : Matrix (Fin d) (Fin d) ℝ)
    (q : Vec d) (εR : ℝ) (hεR : 0 ≤ εR)
    (hR : ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
        (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal εR) :
    ∫ w, aux_thm_eta_sepObs q (Rl.mulVec q) (cubeSet (originCube d (k : ℤ)))
        (aux_thm_eta_field model N w).toFun ∂(chaosSampleLaw model).toMeasure ≤
      (d : ℝ) ^ 2 * εR ^ 2 * vecNormSq q := by
  obtain ⟨ha0f, hIP, hIR⟩ := hN
  have hint : ∀ a b, Integrable (fun w => (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2)
      (chaosSampleLaw model).toMeasure := fun a b =>
    aux_thm_eta_Rsq_int hd hJ model a0 ⟨ha0f, hIP, hIR⟩ Js hM N k (Rl a b) a b
  have hsq : ∀ a b, ∫ w, (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2
      ∂(chaosSampleLaw model).toMeasure ≤ εR ^ 2 := by
    intro a b
    have hsingle : eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
        (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal εR := by
      refine le_trans ?_ hR
      refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b : Fin d, eLpNorm
        (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure) (fun _ _ => zero_le _) (Finset.mem_univ a))
      exact Finset.single_le_sum (f := fun b => eLpNorm
        (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure) (fun _ _ => zero_le _) (Finset.mem_univ b)
    exact (aux_thm_eta_L2_bounds (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b)
      ((hIR N k a b).sub (integrable_const _)).1 (hint a b) εR hεR hsingle).1
  have hpt : ∀ w, aux_thm_eta_sepObs q (Rl.mulVec q) (cubeSet (originCube d (k : ℤ)))
      (aux_thm_eta_field model N w).toFun ≤
      (∑ a, ∑ b, (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2) * vecNormSq q := by
    intro w
    unfold aux_thm_eta_sepObs
    rw [← aux_thm_eta_R_eq model N w _ (a0 N k w) (ha0f N k w)]
    have e : matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w)) q - Rl.mulVec q =
        matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) - Rl) q := by
      funext i
      simp [matVecMul, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    rw [e]
    exact aux_thm_eta_vecNormSq_mat_le _ q
  have hsumint : Integrable (fun w => (∑ a, ∑ b, (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2) * vecNormSq q)
      (chaosSampleLaw model).toMeasure :=
    (integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hint a b).mul_const _
  have hXint : Integrable (fun w => aux_thm_eta_sepObs q (Rl.mulVec q)
      (cubeSet (originCube d (k : ℤ))) (aux_thm_eta_field model N w).toFun)
      (chaosSampleLaw model).toMeasure :=
    aux_thm_eta_int_X hd hJ model N (Js N) (hM N) (k : ℤ) (by positivity) q _
  refine (integral_mono hXint hsumint hpt).trans ?_
  rw [integral_mul_const, integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
    hint a b]
  have hq := vecNormSq_nonneg q
  apply mul_le_mul_of_nonneg_right _ hq
  calc ∑ a, ∫ w, ∑ b, (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2
        ∂(chaosSampleLaw model).toMeasure
      = ∑ a, ∑ b, ∫ w, (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b - Rl a b) ^ 2
        ∂(chaosSampleLaw model).toMeasure :=
        Finset.sum_congr rfl fun a _ => integral_finset_sum _ fun b _ => hint a b
    _ ≤ ∑ _a : Fin d, ∑ _b : Fin d, εR ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hsq a b
    _ = (d : ℝ) ^ 2 * εR ^ 2 := by simp; ring

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The expected response of the actual field on the origin cube of scale `n`. -/
def aux_thm_eta_G (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (p q : Vec d) (n : ℤ) : ℝ :=
  ∫ w, Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q
    (aux_thm_eta_field model N w) ∂(chaosSampleLaw model).toMeasure

/-- The expected flux deviation of the actual field on the origin cube of scale `n`. -/
def aux_thm_eta_X (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (q p : Vec d) (n : ℤ) : ℝ :=
  ∫ w, aux_thm_eta_sepObs q p (cubeSet (originCube d n)) (aux_thm_eta_field model N w).toFun
    ∂(chaosSampleLaw model).toMeasure

theorem aux_thm_eta_hG_seq (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (Nj κ : ℕ → ℕ)
    (Pl Rl : Matrix (Fin d) (Fin d) ℝ)
    (hPw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, |(∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b ∂(chaosSampleLaw model).toMeasure) -
          Pl a b| ≤ ε)
    (hRw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, 2 * κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal ε)
    (p q : Vec d) :
    ∀ δ > 0, ∀ᶠ j in atTop, ∀ n : ℤ, 2 * (κ j : ℤ) ≤ n → n ≤ 4 * (κ j : ℤ) →
      |aux_thm_eta_G model (Nj j) p q n -
        ((1 / 2 : ℝ) * p ⬝ᵥ Pl.mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - p ⬝ᵥ q)| ≤ δ := by
  intro δ hδ
  set Cp := (∑ i, |p i|) ^ 2 with hCp
  set Cq := (∑ i, |q i|) ^ 2 with hCq
  have hCp0 : 0 ≤ Cp := sq_nonneg _
  have hCq0 : 0 ≤ Cq := sq_nonneg _
  set εP : ℝ := δ / (Cp + 1) with hεP
  set εR : ℝ := δ / ((Cq + 1) * ((d : ℝ) ^ 2 + 1)) with hεR
  have hεP0 : 0 < εP := by positivity
  have hεR0 : 0 < εR := by positivity
  filter_upwards [hPw εP hεP0, hRw εR hεR0] with j hPj hRj
  intro n hn1 hn2
  have hn0 : 0 ≤ n := le_trans (by positivity) hn1
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
  have hk1 : κ j ≤ k := by omega
  have hk2 : k ≤ 4 * κ j := by omega
  have hk3 : 2 * κ j ≤ k := by omega
  have h := aux_thm_eta_G_close hd hJ model a0 hN Js hM (Nj j) k Pl Rl p q εP εR hεR0.le
    (hPj k hk1 hk2) (hRj k hk3 hk2)
  refine h.trans ?_
  have h1 : (1 / 2 : ℝ) * Cp * εP ≤ δ / 2 := by
    rw [hεP]
    have : Cp * (δ / (Cp + 1)) ≤ δ := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have h2 : (1 / 2 : ℝ) * Cq * ((d : ℝ) ^ 2 * εR) ≤ δ / 2 := by
    rw [hεR]
    have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    have : Cq * ((d : ℝ) ^ 2 * (δ / ((Cq + 1) * ((d : ℝ) ^ 2 + 1)))) ≤ δ := by
      have e : Cq * ((d : ℝ) ^ 2 * (δ / ((Cq + 1) * ((d : ℝ) ^ 2 + 1)))) =
          δ * (Cq / (Cq + 1)) * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 + 1)) := by
        field_simp
      rw [e]
      have f1 : Cq / (Cq + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have f2 : (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have f3 : 0 ≤ Cq / (Cq + 1) := by positivity
      have f4 : 0 ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 + 1) := by positivity
      calc δ * (Cq / (Cq + 1)) * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 + 1)) ≤ δ * 1 * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left f1 hδ.le) f2 f4 (by positivity)
        _ = δ := by ring
    linarith
  linarith

theorem aux_thm_eta_hX_seq (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (Nj κ : ℕ → ℕ)
    (Rl : Matrix (Fin d) (Fin d) ℝ)
    (hRw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, 2 * κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal ε)
    (q : Vec d) :
    ∀ δ > 0, ∀ᶠ j in atTop, ∀ n : ℤ, 2 * (κ j : ℤ) ≤ n → n ≤ 4 * (κ j : ℤ) →
      aux_thm_eta_X model (Nj j) q (Rl.mulVec q) n ≤ δ := by
  intro δ hδ
  set Q := (d : ℝ) ^ 2 * (vecNormSq q + 1) with hQ
  have hQ0 : 0 < Q := by
    have := vecNormSq_nonneg q
    positivity
  set εR : ℝ := min 1 (δ / Q) with hεR
  have hεR0 : 0 < εR := lt_min one_pos (by positivity)
  filter_upwards [hRw εR hεR0] with j hRj
  intro n hn1 hn2
  have hn0 : 0 ≤ n := le_trans (by positivity) hn1
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
  have h := aux_thm_eta_X_small hd hJ model a0 hN Js hM (Nj j) k Rl q εR hεR0.le
    (hRj k (by omega) (by omega))
  refine h.trans ?_
  have hq := vecNormSq_nonneg q
  have h1 : εR ≤ 1 := min_le_left _ _
  have h2 : εR ≤ δ / Q := min_le_right _ _
  have h3 : εR ^ 2 ≤ εR := by nlinarith
  have h4 : (d : ℝ) ^ 2 * εR ^ 2 * vecNormSq q ≤ Q * εR := by
    have : (d : ℝ) ^ 2 * εR ^ 2 * vecNormSq q ≤ (d : ℝ) ^ 2 * εR * (vecNormSq q + 1) := by
      have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h3 hd2
      nlinarith
    rw [hQ]; nlinarith
  have h5 : Q * εR ≤ δ := by
    have := mul_le_mul_of_nonneg_left h2 hQ0.le
    rwa [mul_div_cancel₀ _ hQ0.ne'] at this
  linarith

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The coarse ellipticity variable `K_k` of the chosen family. -/
def aux_thm_eta_K (Fam : BilateralField d → TriadicCoeffFamily d) (k : ℕ)
    (w : BilateralField d) : ℝ :=
  1 + LambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam w) +
    (lambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam w))⁻¹

theorem aux_thm_eta_hPE_seq (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Js : ℕ → ℤ → BilateralField d → ℝ), (∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) →
      ∀ (B3 : ℝ), (∀ N (n : ℤ), 0 ≤ n →
        ∫ w, Js N n w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B3) →
      ∀ (Fam : ℕ → BilateralField d → TriadicCoeffFamily d),
      (∀ N w, TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N w) (Fam N w)) →
      (∀ N w (k : ℕ), 0 < lambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam N w)) →
      (∀ N w (k : ℕ), 0 ≤ LambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam N w)) →
      ∀ (Nj κ : ℕ → ℕ), (∀ j, 1 ≤ κ j) → ∀ (p q : Vec d) (A : ℝ), 1 ≤ A → ∀ (M : ℝ), 0 < M →
      ∀ j : ℕ,
      aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ) - 1) ≤
        C * A ^ 4 *
          ((∑ n ∈ Finset.Icc (2 * (κ j : ℤ)) (4 * (κ j : ℤ)),
              (3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((4 * (κ j : ℤ) - n : ℤ) : ℝ)) *
                (aux_thm_eta_G model (Nj j) p q n - aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ)))) +
            (∑ n ∈ Finset.Icc (2 * (κ j : ℤ)) (4 * (κ j : ℤ)),
              (3 : ℝ) ^ (-((4 * (κ j : ℤ) - n : ℤ) : ℝ)) *
                (2 * aux_thm_eta_X model (Nj j) q p (4 * (κ j : ℤ)) +
                  2 * aux_thm_eta_X model (Nj j) q p n)) +
            ((3 : ℝ) ^ (-(1 - 1 / 4 : ℝ) * ((4 * (κ j : ℤ) - 2 * (κ j : ℤ) : ℤ) : ℝ))) ^ 2 *
              aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ)) +
            aux_thm_eta_X model (Nj j) q p (4 * (κ j : ℤ))) +
        2 * (3 : ℝ) ^ d * (aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ) - 1) -
          aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ))) +
        2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2) *
          (M * ((chaosSampleLaw model).toMeasure (toMeasurable (chaosSampleLaw model).toMeasure
            {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w})).toReal + (4 + 2 * B3) / M) := by
  obtain ⟨C, hC, hPE⟩ := aux_thm_eta_PE hd hJ
  refine ⟨C, hC, ?_⟩
  intro model Js hM B3 hB3 Fam hFam hpos hL0 Nj κ hκ1 p q A hA M hMpos j
  have hm : (4 * (κ j : ℤ)) = ((4 * κ j : ℕ) : ℤ) := by push_cast; ring
  set T := toMeasurable (chaosSampleLaw model).toMeasure
    {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w} with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hTc : ∀ w, w ∉ T → 1 + LambdaSq (originCube d (4 * (κ j : ℤ))) (1 / 4) (.finite 1)
      (Fam (Nj j) w) + (lambdaSq (originCube d (4 * (κ j : ℤ))) (1 / 4) (.finite 1)
        (Fam (Nj j) w))⁻¹ ≤ A := by
    intro w hw
    have hw' : w ∉ {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w} :=
      fun h => hw (subset_toMeasurable _ _ h)
    simp only [Set.mem_setOf_eq, not_lt, aux_thm_eta_K] at hw'
    rw [hm]
    exact hw'
  have h := hPE model (Nj j) (Js (Nj j)) (hM (Nj j)) (4 * (κ j : ℤ)) (2 * (κ j : ℤ))
    (by positivity) (by omega) (by have := hκ1 j; omega) p q (Fam (Nj j)) (hFam (Nj j))
    (fun w => by rw [hm]; exact hpos (Nj j) w (4 * κ j))
    (fun w => by rw [hm]; exact hL0 (Nj j) w (4 * κ j)) A T hTm hTc
  have hU := aux_thm_eta_UI hd hJ model (Nj j) (Js (Nj j)) (hM (Nj j)) B3 (hB3 (Nj j))
    (4 * (κ j : ℤ) - 1) (by have := hκ1 j; omega) p q T hTm M hMpos
  simp only [aux_thm_eta_G, aux_thm_eta_X]
  linarith

omit [NeZero d] in
theorem aux_thm_eta_tight_seq (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Fam : ℕ → BilateralField d → TriadicCoeffFamily d)
    (htight : ∀ ε > 0, ∃ A : ℝ, 0 < A ∧ ∀ N (k : ℕ),
      (chaosSampleLaw model).toMeasure {w | A < aux_thm_eta_K (Fam N) k w} ≤ ENNReal.ofReal ε)
    (Nj κ : ℕ → ℕ) :
    ∀ ε > 0, ∃ A : ℝ, 1 ≤ A ∧ ∀ j,
      ((chaosSampleLaw model).toMeasure (toMeasurable (chaosSampleLaw model).toMeasure
        {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w})).toReal ≤ ε := by
  intro ε hε
  obtain ⟨A, hA, hAt⟩ := htight ε hε
  refine ⟨max A 1, le_max_right _ _, fun j => ?_⟩
  rw [measure_toMeasurable]
  have hsub : {w | max A 1 < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w} ⊆
      {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w} := fun w hw => by
    simp only [Set.mem_setOf_eq] at hw ⊢
    exact lt_of_le_of_lt (le_max_left _ _) hw
  have h := (measure_mono hsub).trans (hAt (Nj j) (4 * κ j))
  exact ENNReal.toReal_le_of_le_ofReal hε.le h

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The core of the paper's proof: along the extracted subsequence the expected central-child
response at `q` and `p = R q` vanishes, so the limit quadratic form is nonpositive. -/
theorem aux_thm_eta_core (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (B3 : ℝ)
    (hB3 : ∀ N (n : ℤ), 0 ≤ n → ∫ w, Js N n w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B3)
    (Fam : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hFam : ∀ N w, TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N w) (Fam N w))
    (hpos : ∀ N w (k : ℕ), 0 < lambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam N w))
    (hL0 : ∀ N w (k : ℕ), 0 ≤ LambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (Fam N w))
    (htight : ∀ ε > 0, ∃ A : ℝ, 0 < A ∧ ∀ N (k : ℕ),
      (chaosSampleLaw model).toMeasure {w | A < aux_thm_eta_K (Fam N) k w} ≤ ENNReal.ofReal ε)
    (Nj κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop) (hκ1 : ∀ j, 1 ≤ κ j)
    (Pl Rl : Matrix (Fin d) (Fin d) ℝ)
    (hPw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, |(∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b ∂(chaosSampleLaw model).toMeasure) -
          Pl a b| ≤ ε)
    (hRw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, 2 * κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal ε)
    (q : Vec d) :
    (1 / 2 : ℝ) * Rl.mulVec q ⬝ᵥ Pl.mulVec (Rl.mulVec q) + (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q -
      Rl.mulVec q ⬝ᵥ q ≤ 0 := by
  obtain ⟨C, hC, hPEs⟩ := aux_thm_eta_hPE_seq hd hJ
  set p : Vec d := Rl.mulVec q with hp
  set Glim : ℝ := (1 / 2 : ℝ) * p ⬝ᵥ Pl.mulVec p + (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - p ⬝ᵥ q
    with hGlim
  have hB30 : 0 ≤ B3 := by
    have h := hB3 0 0 le_rfl
    have h0 : 0 ≤ ∫ w, Js 0 0 w ^ 3 ∂(chaosSampleLaw model).toMeasure :=
      integral_nonneg fun w => pow_nonneg ((hM 0).2.1 0 w) 3
    linarith
  have hG := aux_thm_eta_hG_seq hd hJ model a0 hN Js hM Nj κ Pl Rl hPw hRw p q
  have hX := aux_thm_eta_hX_seq hd hJ model a0 hN Js hM Nj κ Rl hRw q
  have hY := aux_thm_eta_ylim κ hκ (fun j n => aux_thm_eta_G model (Nj j) p q n)
    (fun j n => aux_thm_eta_X model (Nj j) q p n) Glim hG hX
  have hD : ∀ δ > 0, ∀ᶠ j in atTop, aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ) - 1) -
      aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ)) ≤ δ := by
    intro δ hδ
    filter_upwards [hG (δ / 2) (by positivity)] with j hj
    have h1 := hj (4 * (κ j : ℤ) - 1) (by have := hκ1 j; omega) (by omega)
    have h2 := hj (4 * (κ j : ℤ)) (by omega) le_rfl
    have := abs_le.mp h1
    have := abs_le.mp h2
    linarith
  have hx := aux_thm_eta_alim C (2 * ((∑ i, p i ^ 2) + ∑ i, q i ^ 2)) (4 + 2 * B3)
    (2 * (3 : ℝ) ^ d) hC.le (by positivity) (by positivity) (by positivity)
    (fun j => aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ) - 1)) _
    (fun j => aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ) - 1) -
      aux_thm_eta_G model (Nj j) p q (4 * (κ j : ℤ)))
    (fun A j => ((chaosSampleLaw model).toMeasure (toMeasurable (chaosSampleLaw model).toMeasure
      {w | A < aux_thm_eta_K (Fam (Nj j)) (4 * κ j) w})).toReal)
    (fun A hA M hM' j => hPEs model Js hM B3 hB3 Fam hFam hpos hL0 Nj κ hκ1 p q A hA M hM' j)
    (aux_thm_eta_tight_seq model Fam htight Nj κ) hY hD
  by_contra hcon
  push_neg at hcon
  have hε : 0 < Glim / 3 := by positivity
  obtain ⟨j, hj1, hj2⟩ := ((hx (Glim / 3) hε).and (hG (Glim / 3) hε)).exists
  have h := hj2 (4 * (κ j : ℤ) - 1) (by have := hκ1 j; omega) (by omega)
  have := abs_le.mp h
  simp only at hj1
  linarith

end

section

/-- The limit identity `P = R⁻¹` with `P, R ≥ I` forces `R = I` and `P = I` on quadratic forms. -/
theorem aux_thm_eta_PR_one {d : ℕ} (Pl Rl : Matrix (Fin d) (Fin d) ℝ)
    (hPI : ∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Pl.mulVec x)
    (hRI : ∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Rl.mulVec x)
    (hcore : ∀ q : Fin d → ℝ, (1 / 2 : ℝ) * Rl.mulVec q ⬝ᵥ Pl.mulVec (Rl.mulVec q) +
      (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - Rl.mulVec q ⬝ᵥ q ≤ 0) :
    Rl = 1 ∧ ∀ x : Fin d → ℝ, x ⬝ᵥ Pl.mulVec x = x ⬝ᵥ x := by
  have hRq : ∀ q : Fin d → ℝ, Rl.mulVec q = q := by
    intro q
    set r := Rl.mulVec q with hr
    have h1 := hcore q
    have h2 := hPI r
    have h3 := hRI q
    have hrq : r ⬝ᵥ q = q ⬝ᵥ Rl.mulVec q := dotProduct_comm _ _
    have hsq : (r - q) ⬝ᵥ (r - q) = r ⬝ᵥ r - 2 * (r ⬝ᵥ q) + q ⬝ᵥ q := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm q r]
      ring
    have hle : (r - q) ⬝ᵥ (r - q) ≤ 0 := by
      rw [hsq]
      linarith
    have hnn : ∀ i, (r - q) i = 0 := by
      intro i
      have hsum : (r - q) ⬝ᵥ (r - q) = ∑ j, (r - q) j ^ 2 := by
        simp [dotProduct, sq]
      have h0 : ∑ j, (r - q) j ^ 2 = 0 := by
        have : 0 ≤ ∑ j, (r - q) j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((r - q) j))).1 h0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    funext i
    have := hnn i
    simp only [Pi.sub_apply, sub_eq_zero] at this
    exact this
  have hR1 : Rl = 1 := by
    ext i j
    have h := congrFun (hRq (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    simp only [Matrix.col_apply] at h
    rw [h, Matrix.one_apply]
    simp [Pi.single_apply]
  refine ⟨hR1, fun x => ?_⟩
  have h1 := hcore x
  rw [hRq x] at h1
  have h2 := hPI x
  have h3 : x ⬝ᵥ Rl.mulVec x = x ⬝ᵥ x := by rw [hRq x]
  linarith

/-- Positive semidefinite response-defect matrices: a unit-slope response is bounded by the
trace defect. -/
theorem aux_thm_eta_unit_le_trace {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hsym : S.IsSymm)
    (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (e : Fin d → ℝ) (he : ∑ i, e i ^ 2 = 1) :
    e ⬝ᵥ S.mulVec e ≤ Matrix.trace S := by
  have h := aux_awc_psd_quad_le_trace S hsym hpsd e
  rwa [he, one_mul] at h

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [NeZero d] in
theorem aux_thm_eta_cut_eq (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (w : BilateralField d) (x : SpatialCoordinates d) :
    cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x =
      aux_awc_field model N w x := by
  have h := congrArg (fun F => F w x) (aux_thm_eta_cutoffField_eq hd model N)
  simpa [aux_in_moments_response_moment_cutoffField] using h

omit [NeZero d] in
theorem aux_thm_eta_famAE (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (N : ℕ) (w : BilateralField d) :
    TriadicCoeffFamily.AEEq (aux_thm_eta_fam model N w) (family N w) := by
  apply aux_thm_eta_fam_aeeq_family model N w (family N w)
  intro Q
  filter_upwards [hfamAE N w Q] with x hx
  rw [hx, aux_thm_eta_cut_eq hd model N w x]

omit [NeZero d] in
theorem aux_thm_eta_a0_aeeq (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0f : ∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x))
    (N k : ℕ) (w : BilateralField d) :
    CoeffOn.AEEq (a0 N k w) ((family N w).coeffOn (originCube d (k : ℤ))) := by
  change (a0 N k w).toCoeffField =ᵐ[volumeMeasureOn
    ((cubeDomain (originCube d (k : ℤ)) : Domain d) : Set (Vec d))]
    ((family N w).coeffOn (originCube d (k : ℤ))).toCoeffField
  rw [cubeDomain_coe]
  filter_upwards [hfamAE N w (originCube d (k : ℤ))] with x hx
  rw [ha0f, hx, aux_thm_eta_cut_eq hd model N w x]

omit [NeZero d] in
theorem aux_thm_eta_nodeCtx (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0f : ∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x)) :
    aux_thm_eta_NodeCtx model a0 := by
  have hsub := lem_fmono_annealed_subadditivity d hd model family hfamAE
  dsimp only at hsub
  obtain ⟨hint, -, -, -⟩ := hsub
  refine ⟨ha0f, fun N k a b => ?_, fun N k a b => ?_⟩
  · have e : (fun w => Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) a b) = fun w => Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) a b := by
      funext w
      rw [sigmaCoarse_eq_ofAEEq (aux_thm_eta_a0_aeeq hd model family hfamAE a0 ha0f N k w)]
    rw [e]
    exact (hint N k a b).1
  · have e : (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) = fun w =>
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
            ((family N w).coeffOn (originCube d (k : ℤ))) a b := by
      funext w
      rw [sigmaStarInvCoarse_eq_ofAEEq (aux_thm_eta_a0_aeeq hd model family hfamAE a0 ha0f N k w)]
    rw [e]
    exact (hint N k a b).2

theorem aux_thm_eta_momCtx (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (Jsup : ℕ → ℕ → BilateralField d → ℝ)
    (hJsup : ∀ (N k : ℕ) (w : BilateralField d),
      IsGreatest {v : ℝ | ∃ e : Fin d → ℝ, (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = responseJ (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) e e} (Jsup N k w))
    (hJsupm : ∀ (N k : ℕ), AEStronglyMeasurable (Jsup N k) (chaosSampleLaw model).toMeasure)
    (B1 : ℝ) (hB1 : 0 ≤ B1)
    (hJsupL : ∀ (N k : ℕ), eLpNorm (Jsup N k) (ENNReal.ofReal ((128 * d : ℕ) : ℝ))
      (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B1) :
    (∀ N, aux_thm_eta_MomCtx hJ model N (fun n w => Jsup N n.toNat w)) ∧
      ∀ N (n : ℤ), 0 ≤ n →
        ∫ w, Jsup N n.toNat w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B1 ^ 3 := by
  have hJ0 : ∀ N k w, 0 ≤ Jsup N k w := by
    intro N k w
    have i0 : Fin d := ⟨0, by omega⟩
    have hmem := (hJsup N k w).2 ⟨Pi.single i0 1, aux_awc_single_sq i0, rfl⟩
    exact (Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _).trans hmem
  have hxi : (3 : ℝ) ≤ ((128 * d : ℕ) : ℝ) := by
    have : 3 ≤ 128 * d := by omega
    exact_mod_cast this
  have h3 : ∀ N k, Integrable (fun w => Jsup N k w ^ 3) (chaosSampleLaw model).toMeasure ∧
      ∫ w, Jsup N k w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B1 ^ 3 := fun N k =>
    aux_awc_third_moment (Jsup N k) (hJsupm N k) (hJ0 N k) _ B1 hxi hB1 (hJsupL N k)
  refine ⟨fun N => ⟨?_, fun n w => hJ0 N n.toNat w, fun n _ => (h3 N n.toNat).1⟩,
    fun N n _ => (h3 N n.toNat).2⟩
  intro n hn w e he
  have hnk : n = ((n.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hn).symm
  have hQ : originCube d n = originCube d ((n.toNat : ℕ) : ℤ) := by rw [← hnk]
  rw [hQ]
  have hfam := aux_thm_eta_famAE hd model family hfamAE N w (originCube d ((n.toNat : ℕ) : ℤ))
  rw [← Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
    (aux_thm_eta_field model N w) (aux_thm_eta_field_elliptic model N w),
    aux_awc_responseJ_eq_ofAEEq hfam]
  exact (hJsup N n.toNat w).2 ⟨e, he, rfl⟩

end

section

/-- A unit-slope response is bounded by the sum of the coordinate responses. -/
theorem aux_thm_eta_unit_le_coord {d : ℕ} (hJ : in_J d) (U : Domain d) (b : CoeffOn U)
    (hb : CoeffOn.IsSymmetric b) (e : Fin d → ℝ) (he : ∑ i, e i ^ 2 = 1) :
    responseJ U b e e ≤ ∑ j : Fin d, responseJ U b (Pi.single j 1) (Pi.single j 1) := by
  set P := Homogenization.Book.Ch02.sigmaCoarse U b
  set R := Homogenization.Book.Ch02.sigmaStarInvCoarse U b
  set S : Matrix (Fin d) (Fin d) ℝ := P + R - 2 • (1 : Matrix (Fin d) (Fin d) ℝ) with hS
  have hSx : ∀ x : Fin d → ℝ, responseJ U b x x = (1 / 2 : ℝ) * x ⬝ᵥ S.mulVec x := by
    intro x
    rw [aux_thm_eta_split hJ U b hb x x, hS, Matrix.sub_mulVec, Matrix.add_mulVec,
      dotProduct_sub, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x := by
    intro x
    have := Homogenization.Book.Ch02.responseJ_nonneg U b x x
    rw [hSx] at this
    linarith
  have hsym : S.IsSymm := by
    rw [hS]
    exact ((sigmaCoarse_isSymm U b).add (sigmaStarInvCoarse_isSymm U b)).sub
      (Matrix.isSymm_one.smul 2)
  have hdiag : ∀ j : Fin d, responseJ U b (Pi.single j 1) (Pi.single j 1) = (1 / 2 : ℝ) * S j j := by
    intro j
    rw [hSx]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hSx, Finset.sum_congr rfl fun j _ => hdiag j, ← Finset.mul_sum]
  have := aux_thm_eta_unit_le_trace S hsym hpsd e he
  simp only [Matrix.trace, Matrix.diag] at this
  linarith

/-- `η = 0` from the near-extremal member and a vanishing defect along the subsequence. -/
theorem aux_thm_eta_eta_zero (Fk : ℕ → ℝ) (eta : ℝ) (hconv : Tendsto Fk atTop (𝓝 eta))
    (heta0 : 0 ≤ eta) (g : ℕ → ℝ) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hnear : ∀ j, Fk (4 * κ j) - ((κ j : ℕ) : ℝ)⁻¹ ≤ g j) (hg : Tendsto g atTop (𝓝 0)) :
    eta = 0 := by
  have hfour : Tendsto (fun j => 4 * κ j) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 hκ b] with j hj
    omega
  have h1 : Tendsto (fun j => Fk (4 * κ j)) atTop (𝓝 eta) := hconv.comp hfour
  have hinv : Tendsto (fun j => ((κ j : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hκ
  have h2 : Tendsto (fun j => g j + ((κ j : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using hg.add hinv
  have hle : eta ≤ 0 := le_of_tendsto_of_tendsto' h1 h2 fun j => by linarith [hnear j]
  linarith

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Coordinate responses on the extracted subsequence vanish once `P = R = I`. -/
theorem aux_thm_eta_coord_tendsto (hd : 2 ≤ d) (hJ : in_J d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (Nj κ : ℕ → ℕ) (hκ1 : ∀ j, 1 ≤ κ j)
    (Pl Rl : Matrix (Fin d) (Fin d) ℝ)
    (hPw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, |(∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b ∂(chaosSampleLaw model).toMeasure) -
          Pl a b| ≤ ε)
    (hRw : ∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, 2 * κ j ≤ n → n ≤ 4 * κ j →
      ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (Nj j) n w) a b - Rl a b) 2
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal ε)
    (hR1 : Rl = 1) (hP1 : ∀ x : Fin d → ℝ, x ⬝ᵥ Pl.mulVec x = x ⬝ᵥ x) (i : Fin d) :
    Tendsto (fun j => ∫ w, Homogenization.Book.Ch02.responseJ
      (cubeDomain (originCube d ((4 * κ j : ℕ) : ℤ))) (a0 (Nj j) (4 * κ j) w)
        (Pi.single i 1) (Pi.single i 1) ∂(chaosSampleLaw model).toMeasure) atTop (𝓝 0) := by
  have hG := aux_thm_eta_hG_seq hd hJ model a0 hN Js hM Nj κ Pl Rl hPw hRw
    (Pi.single i 1) (Pi.single i 1)
  have hlim : (1 / 2 : ℝ) * (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ Pl.mulVec (Pi.single i 1) +
      (1 / 2 : ℝ) * (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ Rl.mulVec (Pi.single i 1) -
      (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (Pi.single i 1) = 0 := by
    rw [hP1, hR1, Matrix.one_mulVec]
    ring
  rw [hlim] at hG
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 (hG (ε / 2) (by positivity))
  refine ⟨j0, fun j hj => ?_⟩
  have h := hj0 j hj ((4 * κ j : ℕ) : ℤ) (by have := hκ1 j; push_cast; omega) (by push_cast; omega)
  rw [sub_zero] at h
  rw [Real.dist_eq, sub_zero]
  have e : ∫ w, Homogenization.Book.Ch02.responseJ
      (cubeDomain (originCube d ((4 * κ j : ℕ) : ℤ))) (a0 (Nj j) (4 * κ j) w)
        (Pi.single i 1) (Pi.single i 1) ∂(chaosSampleLaw model).toMeasure =
      aux_thm_eta_G model (Nj j) (Pi.single i 1) (Pi.single i 1) ((4 * κ j : ℕ) : ℤ) := by
    unfold aux_thm_eta_G
    exact integral_congr_ae (Filter.Eventually.of_forall fun w =>
      aux_thm_eta_J_eq model (Nj j) w _ (a0 (Nj j) (4 * κ j) w) (hN.1 _ _ w) _ _)
  rw [e]
  linarith

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [NeZero d] in
/-- The annealed trace defect in matrix form. -/
theorem aux_thm_eta_f_eq (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (N k : ℕ) :
    (1 / 2 : ℝ) * (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
      Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure) =
    Matrix.trace ((Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) +
      (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2 := by
  obtain ⟨-, hIP, hIR⟩ := hN
  set μ := (chaosSampleLaw model).toMeasure
  have hdiag : ∀ i : Fin d,
      (fun w => (Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
          (a0 N k w) + Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i) =
      fun w => (Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
          (a0 N k w) i i + Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) i i) - 2 := by
    intro i
    funext w
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have hsum : ∀ i : Fin d, Integrable (fun w =>
      Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) i i +
      Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) i i) μ :=
    fun i => (hIP N k i i).add (hIR N k i i)
  have hM : ∀ i : Fin d, Integrable (fun w =>
      (Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
          (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i) μ := by
    intro i
    rw [hdiag i]
    exact (hsum i).sub (integrable_const (2 : ℝ))
  rw [aux_awc_integral_trace μ _ hM]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hdiag i, integral_sub (hsum i) (integrable_const (2 : ℝ)),
    integral_add (hIP N k i i) (hIR N k i i)]
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, nsmul_eq_mul, Nat.cast_ofNat,
    mul_one, Matrix.of_apply]
  ring

/-- Uniform bounds on the annealed entries and the `L²` norms of the inverse responses. -/
theorem aux_thm_eta_Kb (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (B3 : ℝ)
    (hB3 : ∀ N (n : ℤ), 0 ≤ n → ∫ w, Js N n w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B3)
    (N k : ℕ) (a b : Fin d) :
    |∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure| ≤ 2 * d * (4 + 2 * B3) ∧
    |∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure| ≤ 2 * d * (4 + 2 * B3) ∧
    eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) 2 (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal (2 * d * (4 + 2 * B3)) := by
  obtain ⟨ha0f, hIP, hIR⟩ := hN
  obtain ⟨hJs, hJs0, hJs3⟩ := hM N
  set μ := (chaosSampleLaw model).toMeasure
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hsym : ∀ w, CoeffOn.IsSymmetric (a0 N k w) := by
    intro w
    rw [CoeffOn.IsSymmetric]
    filter_upwards [] with x
    rw [ha0f N k w x]
    exact Homogenization.scalarMatrix_isSymm _
  have hunit : ∀ w, ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 →
      responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w) e e ≤ Js N k w := by
    intro w e he
    rw [aux_thm_eta_J_eq model N w _ (a0 N k w) (ha0f N k w)]
    exact hJs k hk w e he
  have hent : ∀ w, |Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
      (a0 N k w) a b| ≤ 2 * d * (1 + Js N k w) ∧
      |Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
      (a0 N k w) a b| ≤ 2 * d * (1 + Js N k w) := fun w =>
    ⟨(aux_thm_eta_unit_bounds hJ _ _ (hsym w) _ (hunit w)).1 a b,
      (aux_thm_eta_unit_bounds hJ _ _ (hsym w) _ (hunit w)).2.1 a b⟩
  have hi3 := hJs3 k hk
  have hB := hB3 N k hk
  have hB30 : 0 ≤ B3 := le_trans (integral_nonneg fun w => pow_nonneg (hJs0 k w) 3) hB
  have hdom : Integrable (fun w => 2 * (d : ℝ) * (2 + Js N k w ^ 3)) μ :=
    ((integrable_const (2 : ℝ)).add hi3).const_mul _
  have hdomI : ∫ w, 2 * (d : ℝ) * (2 + Js N k w ^ 3) ∂μ ≤ 2 * d * (4 + 2 * B3) := by
    rw [integral_const_mul, integral_add (integrable_const _) hi3, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    have : 2 + ∫ w, Js N k w ^ 3 ∂μ ≤ 4 + 2 * B3 := by linarith
    exact mul_le_mul_of_nonneg_left this hd0
  have hlin : ∀ w, 2 * (d : ℝ) * (1 + Js N k w) ≤ 2 * (d : ℝ) * (2 + Js N k w ^ 3) := by
    intro w
    have h0 := hJs0 k w
    have h1 := aux_awc_sq_le_one_add_cube (Js N k w) h0
    have h2 : Js N k w ≤ 1 + Js N k w ^ 3 := by nlinarith
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hd0
  refine ⟨?_, ?_, ?_⟩
  · refine (abs_integral_le_integral_abs).trans ?_
    refine le_trans (integral_mono (hIP N k a b).abs hdom fun w =>
      ((hent w).1.trans (hlin w))) hdomI
  · refine (abs_integral_le_integral_abs).trans ?_
    refine le_trans (integral_mono (hIR N k a b).abs hdom fun w =>
      ((hent w).2.trans (hlin w))) hdomI
  · have hsq := aux_thm_eta_Rsq_int hd hJ model a0 ⟨ha0f, hIP, hIR⟩ Js hM N k 0 a b
    simp only [sub_zero] at hsq
    have hdom2 : Integrable (fun w => 4 * (d : ℝ) ^ 2 * (4 + 2 * Js N k w ^ 3)) μ :=
      ((integrable_const (4 : ℝ)).add (hi3.const_mul 2)).const_mul _
    have hpt : ∀ w, (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) ^ 2 ≤
        4 * (d : ℝ) ^ 2 * (4 + 2 * Js N k w ^ 3) := by
      intro w
      have h1 := (hent w).2
      have h2 : (Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) ^ 2 ≤
          (2 * d * (1 + Js N k w)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 := aux_thm_eta_sq_one_add_le (Js N k w) (hJs0 k w)
      have e : (2 * (d : ℝ) * (1 + Js N k w)) ^ 2 = 4 * (d : ℝ) ^ 2 * (1 + Js N k w) ^ 2 := by
        ring
      rw [e] at h2
      have hd2 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 := by positivity
      exact h2.trans (mul_le_mul_of_nonneg_left h3 hd2)
    have hI : ∫ w, (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b) ^ 2 ∂μ ≤
        4 * (d : ℝ) ^ 2 * (4 + 2 * B3) := by
      refine (integral_mono hsq hdom2 hpt).trans ?_
      rw [integral_const_mul, integral_add (integrable_const _) (hi3.const_mul 2),
        integral_const, integral_const_mul]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      have hd2 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hd2
    refine (aux_awc_eLpNorm_two_le _ (hIR N k a b).1 hsq hI).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hX : 1 ≤ 4 + 2 * B3 := by linarith
    have e : Real.sqrt (4 * (d : ℝ) ^ 2 * (4 + 2 * B3)) =
        2 * d * Real.sqrt (4 + 2 * B3) := by
      rw [show 4 * (d : ℝ) ^ 2 * (4 + 2 * B3) = (2 * d) ^ 2 * (4 + 2 * B3) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e]
    have hs : Real.sqrt (4 + 2 * B3) ≤ 4 + 2 * B3 := by
      have h0 : 0 ≤ Real.sqrt (4 + 2 * B3) := Real.sqrt_nonneg _
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 4 + 2 * B3 by linarith)
      nlinarith
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    exact mul_le_mul_of_nonneg_left hs hd0

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_thm_eta_ha0f (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
      ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d)) :
    ∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x) := by
  intro N k w x
  rw [ha0]
  simp [aux_awc_field, scalarMatrix]

omit [NeZero d] in
theorem aux_thm_eta_EP_family (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0f : ∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x))
    (N k : ℕ) (i j : Fin d) :
    (∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) i j
        ∂(chaosSampleLaw model).toMeasure) =
      ∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
        ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure ∧
    (∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) i j ∂(chaosSampleLaw model).toMeasure) =
      ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure := by
  constructor
  · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [sigmaCoarse_eq_ofAEEq (aux_thm_eta_a0_aeeq hd model family hfamAE a0 ha0f N k w)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [sigmaStarInvCoarse_eq_ofAEEq (aux_thm_eta_a0_aeeq hd model family hfamAE a0 ha0f N k w)]

omit [NeZero d] in
theorem aux_thm_eta_f_family (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0f : ∀ (N k : ℕ) w x, (a0 N k w).toCoeffField x = scalarMatrix (aux_awc_field model N w x))
    (N k : ℕ) :
    (1 / 2 : ℝ) * (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
      Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure) =
    Matrix.trace (((fun i j => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) +
      (fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2 := by
  rw [aux_thm_eta_f_eq model a0 (aux_thm_eta_nodeCtx hd model family hfamAE a0 ha0f) N k]
  have hPe : (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) =
      ((fun i j => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    exact (aux_thm_eta_EP_family hd model family hfamAE a0 ha0f N k i j).1
  have hRe : (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) =
      ((fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    exact (aux_thm_eta_EP_family hd model family hfamAE a0 ha0f N k i j).2
  rw [hPe, hRe]

omit [NeZero d] in
/-- Symmetry of the annealed response matrices. -/
theorem aux_thm_eta_EP_symm (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (N k : ℕ) :
    (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).transpose =
      (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) ∧
    (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).transpose =
      (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) := by
  constructor
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have h := sigmaCoarse_isSymm (cubeDomain (originCube d (k : ℤ))) (a0 N k w)
    simpa [Matrix.transpose_apply] using congrFun (congrFun h i) j
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have h := sigmaStarInvCoarse_isSymm (cubeDomain (originCube d (k : ℤ))) (a0 N k w)
    simpa [Matrix.transpose_apply] using congrFun (congrFun h i) j

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- `lem_conc` applied to the actual annealed and random inverse response matrices, re-indexed
along `κ j = φ (j + 1)`. -/
theorem aux_thm_eta_conc (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (B3 : ℝ)
    (hB3 : ∀ N (n : ℤ), 0 ≤ n → ∫ w, Js N n w ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ B3)
    (idx : ℕ → ℕ)
    (hPI : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of fun a b =>
      ∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b
        ∂(chaosSampleLaw model).toMeasure).mulVec x)
    (hRI : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of fun a b =>
      ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).mulVec x)
    (hPunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ n ∈ Finset.Icc k (4 * k), ∑ a : Fin d, ∑ b : Fin d,
        |(∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (n : ℤ)))
            (a0 (idx k) n w) a b ∂(chaosSampleLaw model).toMeasure) -
          ∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d ((4 * k : ℕ) : ℤ)))
            (a0 (idx k) (4 * k) w) a b ∂(chaosSampleLaw model).toMeasure| ≤ eps)
    (hRunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ n ∈ Finset.Icc (2 * k) (4 * k), ∑ a : Fin d, ∑ b : Fin d,
        eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (n : ℤ))) (a0 (idx k) n w) a b -
          ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
            (a0 (idx k) k w) a b ∂(chaosSampleLaw model).toMeasure) 2
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal eps) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ (∀ j, 1 ≤ κ j) ∧
    ∃ Pl Rl : Matrix (Fin d) (Fin d) ℝ,
      (∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Pl.mulVec x) ∧
      (∀ x : Fin d → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ Rl.mulVec x) ∧
      (∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, κ j ≤ n → n ≤ 4 * κ j →
        ∑ a : Fin d, ∑ b : Fin d, |(∫ w, Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (n : ℤ))) (a0 (idx (κ j)) n w) a b
            ∂(chaosSampleLaw model).toMeasure) - Pl a b| ≤ ε) ∧
      (∀ ε > 0, ∀ᶠ j in atTop, ∀ n : ℕ, 2 * κ j ≤ n → n ≤ 4 * κ j →
        ∑ a : Fin d, ∑ b : Fin d, eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (n : ℤ))) (a0 (idx (κ j)) n w) a b - Rl a b) 2
            (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal ε) := by
  set Kb : ℝ := 2 * d * (4 + 2 * B3) with hKbdef
  have hB30 : 0 ≤ B3 := by
    have h := hB3 0 0 le_rfl
    have h0 : 0 ≤ ∫ w, Js 0 0 w ^ 3 ∂(chaosSampleLaw model).toMeasure :=
      integral_nonneg fun w => pow_nonneg ((hM 0).2.1 0 w) 3
    linarith
  have hKb : 0 ≤ Kb := by positivity
  obtain ⟨phi, hphi, Pl, Rl, -, -, hPlI, hRlI, hPw, hRw⟩ :=
    lem_conc (BilateralField d) (chaosSampleLaw model).toMeasure d (by omega)
      (fun j n => Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (idx j) n w) a b ∂(chaosSampleLaw model).toMeasure)
      (fun j n => (aux_thm_eta_EP_symm model a0 (idx j) n).1)
      (fun j n w => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) (a0 (idx j) n w)) id strictMono_id
      (fun j => Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (j : ℤ))) (a0 (idx j) j w) a b ∂(chaosSampleLaw model).toMeasure)
      (fun j => (aux_thm_eta_EP_symm model a0 (idx j) j).2) (fun j a b => rfl) Kb hKb
      (fun j a b => (aux_thm_eta_Kb hd hJ model a0 hN Js hM B3 hB3 (idx j) j a b).2.1)
      (fun j a b => (aux_thm_eta_Kb hd hJ model a0 hN Js hM B3 hB3 (idx j) (4 * j) a b).1)
      (fun j n a b => (aux_thm_eta_Kb hd hJ model a0 hN Js hM B3 hB3 (idx j) n a b).2.2)
      (fun j n x => hPI (idx j) n x) (fun j x => hRI (idx j) j x) hPunif hRunif
  refine ⟨fun j => phi (j + 1), ?_, fun j => ?_, Pl, Rl, hPlI, hRlI, ?_, ?_⟩
  · exact hphi.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  · show 1 ≤ phi (j + 1)
    have := hphi.id_le (j + 1)
    simp only [id] at this
    omega
  · intro ε hε
    obtain ⟨j0, hj0⟩ := hPw ε hε
    refine eventually_atTop.2 ⟨j0, fun j hj n hn1 hn2 => ?_⟩
    exact hj0 (j + 1) (by omega) n (Finset.mem_Icc.2 ⟨hn1, hn2⟩)
  · intro ε hε
    obtain ⟨j0, hj0⟩ := hRw ε hε
    refine eventually_atTop.2 ⟨j0, fun j hj n hn1 hn2 => ?_⟩
    exact hj0 (j + 1) (by omega) n (Finset.mem_Icc.2 ⟨hn1, hn2⟩)

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_thm_eta_int_resp (hd : 2 ≤ d) (hJ : in_J d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (N k : ℕ) (p q : Vec d) :
    Integrable (fun w => responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w) p q)
      (chaosSampleLaw model).toMeasure := by
  have e : (fun w => responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w) p q) =
      fun w => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (originCube d (k : ℤ)) p q (aux_thm_eta_field model N w) := by
    funext w
    exact aux_thm_eta_J_eq model N w _ (a0 N k w) (hN.1 N k w) p q
  rw [e]
  exact aux_thm_eta_int_J hd hJ model N (Js N) (hM N) (k : ℤ) (by positivity) p q

/-- The final per-cutoff bound by the trace defect. -/
theorem aux_thm_eta_final_bound (hd : 2 ≤ d) (hJ : in_J d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (hN : aux_thm_eta_NodeCtx model a0) (Js : ℕ → ℤ → BilateralField d → ℝ)
    (hM : ∀ N, aux_thm_eta_MomCtx hJ model N (Js N)) (N k : ℕ) (e : Fin d → ℝ)
    (he : ∑ i, e i ^ 2 = 1) :
    |∫ w, responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w) e e
        ∂(chaosSampleLaw model).toMeasure| ≤
      ∑ j : Fin d, ∫ w, responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w)
        (Pi.single j 1) (Pi.single j 1) ∂(chaosSampleLaw model).toMeasure := by
  have hsym : ∀ w, CoeffOn.IsSymmetric (a0 N k w) := by
    intro w
    rw [CoeffOn.IsSymmetric]
    filter_upwards [] with x
    rw [hN.1 N k w x]
    exact Homogenization.scalarMatrix_isSymm _
  rw [abs_of_nonneg (integral_nonneg fun w => Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _),
    ← integral_finset_sum _ fun j _ => aux_thm_eta_int_resp hd hJ model a0 hN Js hM N k _ _]
  exact integral_mono (aux_thm_eta_int_resp hd hJ model a0 hN Js hM N k e e)
    (integrable_finset_sum _ fun j _ => aux_thm_eta_int_resp hd hJ model a0 hN Js hM N k _ _)
    fun w => aux_thm_eta_unit_le_coord hJ _ _ (hsym w) e he

end

section

variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Assembly of the proof of `mfd:thm-eta` from the suppliers' outputs at a fixed model. -/
theorem aux_thm_eta_assemble (hd : 2 ≤ d) (hJ : in_J d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (a0 : (N k : ℕ) → BilateralField d → CoeffOn (cubeDomain (originCube d (k : ℤ))))
    (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
      ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d))
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamAE : ∀ (N : ℕ) (w : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N w).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) w N x))
    (Jsup : ℕ → ℕ → BilateralField d → ℝ)
    (hJsup : ∀ (N k : ℕ) (w : BilateralField d),
      IsGreatest {v : ℝ | ∃ e : Fin d → ℝ, (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = responseJ (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) e e} (Jsup N k w))
    (hJsupm : ∀ (N k : ℕ), AEStronglyMeasurable (Jsup N k) (chaosSampleLaw model).toMeasure)
    (B1 : ℝ) (hB1 : 0 ≤ B1)
    (hJsupL : ∀ (N k : ℕ), eLpNorm (Jsup N k) (ENNReal.ofReal ((128 * d : ℕ) : ℝ))
      (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B1)
    (hposL : ∀ (N : ℕ) (w : BilateralField d) (k : ℕ),
      0 < lambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (family N w) ∧
      0 ≤ LambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (family N w))
    (htight : ∀ eps : ℝ, 0 < eps → ∃ A : ℝ, 0 < A ∧ ∀ N k : ℕ,
      (chaosSampleLaw model).toMeasure {w : BilateralField d | A < 1 +
        LambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (family N w) +
          (lambdaSq (originCube d (k : ℤ)) (1 / 4) (.finite 1) (family N w))⁻¹} ≤
        ENNReal.ofReal eps)
    (Fk' : ℕ → ℝ) (eta : ℝ)
    (hLUB' : ∀ k : ℕ, IsLUB (Set.range fun N => Matrix.trace (((fun i j => ∫ w,
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure) +
      (fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2) (Fk' k))
    (heta0 : 0 ≤ eta) (hFanti' : Antitone Fk') (hFconv' : Tendsto Fk' atTop (𝓝 eta))
    (hfanti' : ∀ N k : ℕ, Matrix.trace (((fun i j => ∫ w,
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d ((k + 1 : ℕ) : ℤ)))
          ((family N w).coeffOn (originCube d ((k + 1 : ℕ) : ℤ))) i j
            ∂(chaosSampleLaw model).toMeasure) +
      (fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d ((k + 1 : ℕ) : ℤ)))
          ((family N w).coeffOn (originCube d ((k + 1 : ℕ) : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2 ≤
      Matrix.trace (((fun i j => ∫ w,
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure) +
      (fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
          ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2)
    (hPI' : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ Matrix.mulVec (fun i j => ∫ w,
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure) x)
    (hRI' : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ Matrix.mulVec (fun i j => ∫ w,
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
          ((family N w).coeffOn (originCube d (k : ℤ))) i j ∂(chaosSampleLaw model).toMeasure) x)
    (hW : ∀ (Fk : ℕ → ℝ), (∀ k : ℕ, IsLUB (Set.range fun N => (1 / 2 : ℝ) *
        (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
            (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure))
          (Fk k)) → ∀ (idx : ℕ → ℕ),
      (∀ n : ℕ, 1 ≤ n → Fk (4 * n) - (n : ℝ)⁻¹ ≤ (1 / 2 : ℝ) *
        (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d ((4 * n : ℕ) : ℤ))) (a0 (idx n) (4 * n) w) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d ((4 * n : ℕ) : ℤ)))
            (a0 (idx n) (4 * n) w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
            ∂(chaosSampleLaw model).toMeasure)) →
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∀ n ∈ Finset.Icc k (4 * k), ∑ a : Fin d, ∑ b : Fin d,
          |(∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (n : ℤ)))
              (a0 (idx k) n w) a b ∂(chaosSampleLaw model).toMeasure) -
            ∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d ((4 * k : ℕ) : ℤ)))
              (a0 (idx k) (4 * k) w) a b ∂(chaosSampleLaw model).toMeasure| ≤ eps) ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∀ n ∈ Finset.Icc (2 * k) (4 * k), ∑ a : Fin d, ∑ b : Fin d,
          eLpNorm (fun w => Homogenization.Book.Ch02.sigmaStarInvCoarse
            (cubeDomain (originCube d (n : ℤ))) (a0 (idx k) n w) a b -
            ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
              (a0 (idx k) k w) a b ∂(chaosSampleLaw model).toMeasure) 2
            (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal eps))
    (hSD : ∀ N k : ℕ, (1 / 2 : ℝ) *
        (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
            (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure) =
      ∑ j : Fin d, ∫ w, responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w)
        (Pi.single j 1) (Pi.single j 1) ∂(chaosSampleLaw model).toMeasure) :
    ∃ Fk : ℕ → ℝ,
      (∀ k : ℕ, IsLUB (Set.range fun N => (1 / 2 : ℝ) *
        (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
            (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure))
          (Fk k)) ∧
      Tendsto Fk atTop (𝓝 0) ∧
      ∀ e : Fin d → ℝ, (∑ i, e i ^ 2) = 1 → ∀ eps : ℝ, 0 < eps →
        ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
          |∫ w, responseJ (cubeDomain (originCube d (k : ℤ))) (a0 N k w) e e
            ∂(chaosSampleLaw model).toMeasure| ≤ eps := by
  have ha0f := aux_thm_eta_ha0f model a0 ha0
  have hN := aux_thm_eta_nodeCtx hd model family hfamAE a0 ha0f
  obtain ⟨hMom, hB3⟩ := aux_thm_eta_momCtx hd hJ model family hfamAE Jsup hJsup hJsupm B1 hB1
    hJsupL
  have hfeq := aux_thm_eta_f_family hd model family hfamAE a0 ha0f
  have hF : ∀ k : ℕ, IsLUB (Set.range fun N => (1 / 2 : ℝ) *
      (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
          (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure))
        (Fk' k) := by
    intro k
    simp only [hfeq]
    exact hLUB' k
  have hmono : ∀ N k : ℕ, (1 / 2 : ℝ) *
      (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d ((k + 1 : ℕ) : ℤ))) (a0 N (k + 1) w) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d ((k + 1 : ℕ) : ℤ)))
          (a0 N (k + 1) w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure) ≤
      (1 / 2 : ℝ) *
      (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
          (a0 N k w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure) := by
    intro N k
    rw [hfeq, hfeq]
    exact hfanti' N k
  obtain ⟨idx, hnear, -, -⟩ := near_extremal_member _ Fk' hmono hF hFanti' eta hFconv'
  obtain ⟨hPunif, hRunif⟩ := hW Fk' hF idx hnear
  have hPI : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of fun a b =>
      ∫ w, Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b
        ∂(chaosSampleLaw model).toMeasure).mulVec x := by
    intro N k x
    have e : (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) =
        ((fun i j => ∫ w, Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
            ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      exact (aux_thm_eta_EP_family hd model family hfamAE a0 ha0f N k i j).1
    rw [e]
    exact hPI' N k x
  have hRI : ∀ (N k : ℕ) (x : Fin d → ℝ), x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of fun a b =>
      ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d (k : ℤ)))
        (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure).mulVec x := by
    intro N k x
    have e : (Matrix.of fun a b => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (k : ℤ))) (a0 N k w) a b ∂(chaosSampleLaw model).toMeasure) =
        ((fun i j => ∫ w, Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (originCube d (k : ℤ))) ((family N w).coeffOn (originCube d (k : ℤ))) i j
            ∂(chaosSampleLaw model).toMeasure) : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      exact (aux_thm_eta_EP_family hd model family hfamAE a0 ha0f N k i j).2
    rw [e]
    exact hRI' N k x
  obtain ⟨κ, hκ, hκ1, Pl, Rl, hPlI, hRlI, hPw, hRw⟩ := aux_thm_eta_conc hd hJ model a0 hN _ hMom
    (B1 ^ 3) hB3 idx hPI hRI hPunif hRunif
  have hcore : ∀ q : Fin d → ℝ, (1 / 2 : ℝ) * Rl.mulVec q ⬝ᵥ Pl.mulVec (Rl.mulVec q) +
      (1 / 2 : ℝ) * q ⬝ᵥ Rl.mulVec q - Rl.mulVec q ⬝ᵥ q ≤ 0 := fun q =>
    aux_thm_eta_core hd hJ model a0 hN _ hMom (B1 ^ 3) hB3 family
      (fun N w => aux_thm_eta_famAE hd model family hfamAE N w)
      (fun N w k => (hposL N w k).1) (fun N w k => (hposL N w k).2) htight
      (fun j => idx (κ j)) κ hκ hκ1 Pl Rl hPw hRw q
  obtain ⟨hR1, hP1⟩ := aux_thm_eta_PR_one Pl Rl hPlI hRlI hcore
  have hg : Tendsto (fun j => (1 / 2 : ℝ) *
      (∫ w, Matrix.trace (Homogenization.Book.Ch02.sigmaCoarse
        (cubeDomain (originCube d ((4 * κ j : ℕ) : ℤ))) (a0 (idx (κ j)) (4 * κ j) w) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d ((4 * κ j : ℕ) : ℤ)))
          (a0 (idx (κ j)) (4 * κ j) w) - 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
          ∂(chaosSampleLaw model).toMeasure)) atTop (𝓝 0) := by
    simp only [hSD]
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun i _ =>
      aux_thm_eta_coord_tendsto hd hJ model a0 hN _ hMom (fun j => idx (κ j)) κ hκ1 Pl Rl hPw hRw
        hR1 hP1 i
    simpa using h
  have heta : eta = 0 := aux_thm_eta_eta_zero Fk' eta hFconv' heta0 _ κ hκ
    (fun j => hnear (κ j) (hκ1 j)) hg
  rw [heta] at hFconv'
  refine ⟨Fk', hF, hFconv', fun e he eps heps => ?_⟩
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 hFconv').2 eps heps)
  refine ⟨k0, fun k hk N => ?_⟩
  refine (aux_thm_eta_final_bound hd hJ model a0 hN _ hMom N k e he).trans ?_
  rw [← hSD N k]
  exact ((hF k).1 ⟨N, rfl⟩).trans (hk0 k hk).le

end



theorem thm_eta (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ disorder0 : ℝ, 0 < disorder0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ disorder0 →
      ∀ (U : ℕ → Homogenization.Book.Ch02.Domain d)
        (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
          (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
            (pow_pos (by norm_num) k) :
            Set (SpatialCoordinates d)))
        (a0 : (N k : ℕ) → BilateralField d →
          Homogenization.Book.Ch02.CoeffOn (U k))
        (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
          ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
            (1 : Homogenization.Mat d)),
      let Pm := fun (N k : ℕ) (omega : BilateralField d) =>
        Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega)
      let Rm := fun (N k : ℕ) (omega : BilateralField d) =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega)
      let f := fun (N k : ℕ) => (1 / 2 : ℝ) *
        (∫ omega, Matrix.trace (Pm N k omega + Rm N k omega -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ))
          ∂(chaosSampleLaw model).toMeasure)
      ∃ Fk : ℕ → ℝ,
        (∀ k, IsLUB (Set.range (fun N => f N k)) (Fk k)) ∧
        Tendsto Fk atTop (nhds 0) ∧
        (∀ e : Fin d → ℝ, (∑ i, e i ^ 2) = 1 →
          ∀ eps : ℝ, 0 < eps →
            ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ N : ℕ,
              |∫ omega, Homogenization.Book.Ch02.responseJ (U k)
                  (a0 N k omega) e e ∂(chaosSampleLaw model).toMeasure| ≤ eps) ∧
        (∀ N k : ℕ, Integrable (fun omega =>
          Matrix.trace (Pm N k omega + Rm N k omega -
            2 • (1 : Matrix (Fin d) (Fin d) ℝ)))
          (chaosSampleLaw model).toMeasure) ∧
        (∀ (N k : ℕ) (e : Fin d → ℝ), (∑ i, e i ^ 2) = 1 →
          Integrable (fun omega => Homogenization.Book.Ch02.responseJ (U k)
            (a0 N k omega) e e) (chaosSampleLaw model).toMeasure) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨Cc, hCc, hmom⟩ := in_moments d hd hJ
  obtain ⟨dz, hdz, hmom2⟩ := hmom (128 * d) ⟨64 * d, by ring⟩ le_rfl
  obtain ⟨delta0, hdelta0, hfm⟩ := lem_fmono d hd hJ
  obtain ⟨dw, hdw, hwin⟩ := annealed_window_convergence d hd hJ
  refine ⟨min dz (min delta0 dw), lt_min hdz (lt_min hdelta0 hdw), ?_⟩
  intro instM instB model hmodel U hU a0 ha0
  have hmz : model.delta ≤ dz := le_trans hmodel (min_le_left _ _)
  have hm0 : model.delta ≤ delta0 :=
    le_trans hmodel (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmw : model.delta ≤ dw :=
    le_trans hmodel (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨family, Jsup, -, hfamAE, hJsup, hJsupm, hJsupL, hposL, htight⟩ := hmom2 model hmz
  have hfmono := hfm model hm0 family hfamAE
  dsimp only at hfmono
  obtain ⟨hPI', hRI', hf0', hfanti', Fk', eta, hLUB', heta0, hFanti', hFconv'⟩ := hfmono
  have hW := hwin model hmw U hU a0 ha0
  have hSD := stationary_defects d hd model U hU a0 ha0 hJ
  have hUeq : U = fun k : ℕ => cubeDomain (originCube d (k : ℤ)) := funext (aux_awc_domain U hU)
  subst hUeq
  intro Pm Rm f
  dsimp only at hW hSD
  have hB1 : 0 ≤ Cc * ((128 * d : ℕ) : ℝ) * Real.log (2 + ((128 * d : ℕ) : ℝ)) *
      model.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + ((128 * d : ℕ) : ℝ)) :=
      Real.log_nonneg (by have : (0 : ℝ) ≤ ((128 * d : ℕ) : ℝ) := by positivity
                          linarith)
    have := hCc.le
    positivity
  obtain ⟨F, hF, hFzero, hFsmall⟩ :=
    aux_thm_eta_assemble hd hJ model a0 ha0 family hfamAE Jsup hJsup hJsupm _ hB1 hJsupL
      hposL htight Fk' eta hLUB' heta0 hFanti' hFconv' hfanti' hPI' hRI' hW hSD
  have hN := aux_thm_eta_nodeCtx hd model family hfamAE a0 ha0
  obtain ⟨hMom, _⟩ := aux_thm_eta_momCtx hd hJ model family hfamAE Jsup hJsup hJsupm _ hB1 hJsupL
  refine ⟨F, hF, hFzero, hFsmall, ?_, ?_⟩
  · intro N k
    simp only [Matrix.trace, Matrix.diag, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply_eq]
    exact integrable_finset_sum _ (fun i _ =>
      ((hN.2.1 N k i i).add (hN.2.2 N k i i)).sub
        (integrable_const (2 • (1 : ℝ))))
  · intro N k e he
    exact aux_thm_eta_int_resp hd hJ model a0 hN _ hMom N k e e

end
end Paper
