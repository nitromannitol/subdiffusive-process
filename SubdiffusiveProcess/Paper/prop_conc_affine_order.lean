import SubdiffusiveProcess.Paper.prop_conc_setup
import SubdiffusiveProcess.Paper.prop_conc_actual_affine_identification
import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
import SubdiffusiveProcess.Paper.prop_conc_cutoff_affine_coercivity
import SubdiffusiveProcess.Paper.prop_conc_unit_inverse_trace_moment
import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
import SubdiffusiveProcess.Sobolev.PartitionEnergy
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane3.RelativeResponseSlopes
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

theorem aux_prop_conc_affine_order_cell_moment_uniform_geometry {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1),
      ∃ Cq Cd : ℝ, 0 < Cq ∧ 0 < Cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ deltaq →
        ∀ N n : ℕ,
          AEStronglyMeasurable (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(n : ℤ))
              (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(n : ℤ))
              (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cq * (if n ≤ N then
              (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
            else Real.exp ((Cd * M.delta + Cd * M.delta ^ 2) * (N : ℝ)))) := by
  have hq0 : 0 < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlogs3 : 0 < Real.log (Real.sqrt 3) :=
    Real.log_pos (by rw [Real.lt_sqrt (by norm_num)]; norm_num)
  obtain ⟨δresp, CJ, hδresp, hCJ, hresp⟩ :=
    aux_lem_extension_cell_moment_matched_response hd E q hq
  obtain ⟨CH, hCH0, hpieceM⟩ := aux_lane4_lambda_inv_cell_moment_pieceG_moment hd
  obtain ⟨Cenv, hCenv0, henvM⟩ := aux_lane4_lambda_inv_cell_moment_envMax_moment hd
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ, q' = max q (2 * (d : ℝ)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = aux_lem_extension_cell_moment_aboveRate d (2 * q) := ⟨_, rfl⟩
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ,
      CR = 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 :=
    ⟨_, rfl⟩
  have hBpos : 0 < B := by
    rw [hB]; exact aux_lem_extension_cell_moment_aboveRate_pos d (2 * q) (by positivity)
  have hq'q : q ≤ q' := by rw [hq']; exact le_max_left _ _
  have hq'0 : 0 < q' := by linarith
  have hCRpos : 0 < CR := by rw [hCR]; positivity
  have hdq' : (d : ℝ) / q' ≤ 1 / 2 := by
    rw [div_le_iff₀ hq'0]
    have : 2 * (d : ℝ) ≤ q' := by rw [hq']; exact le_max_right _ _
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max B CR := ⟨_, rfl⟩
  have hBR : B ≤ R := by rw [hR]; exact le_max_left _ _
  have hCRR : CR ≤ R := by rw [hR]; exact le_max_right _ _
  have hR0 : 0 ≤ R := hBpos.le.trans hBR
  set deltaq : ℝ := min δresp (min (1 / q) (min (Real.sqrt (Real.log (3 / 2) / B))
    (Real.sqrt (Real.log (Real.sqrt 3) / CR)))) with hdeltaq
  have hdeltaqpos : 0 < deltaq := lt_min hδresp (lt_min (by positivity)
    (lt_min (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))))
  have hδqB : deltaq ≤ Real.sqrt (Real.log (3 / 2) / B) :=
    hdeltaq ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδqC : deltaq ≤ Real.sqrt (Real.log (Real.sqrt 3) / CR) :=
    hdeltaq ▸ (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδq1 : deltaq ≤ 1 / q := hdeltaq ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hBδ0 : B * deltaq ^ 2 ≤ Real.log (3 / 2) := by
    have h := pow_le_pow_left₀ hdeltaqpos.le hδqB 2
    rw [Real.sq_sqrt (by positivity)] at h
    rw [le_div_iff₀ hBpos] at h
    linarith
  have hCRδ0 : CR * deltaq ^ 2 ≤ Real.log (Real.sqrt 3) := by
    have h := pow_le_pow_left₀ hdeltaqpos.le hδqC 2
    rw [Real.sq_sqrt (by positivity)] at h
    rw [le_div_iff₀ hCRpos] at h
    linarith
  refine ⟨deltaq, hdeltaqpos, ?_⟩
  intro z r hr hr1
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨
    aux_lem_band_L1c_Cq_fn d r CJ B CR (CH (aux_lane4_lambda_inv_cell_moment_rootK z))
      (Cenv (aux_lane4_lambda_inv_cell_moment_rootK z)) q q' deltaq ℓ,
    aux_lem_band_L1c_Cd_fn d R,
    aux_lem_band_L1c_Cq_fn_pos d r CJ B CR (CH _) (Cenv _) q q' deltaq ℓ hr hCJ.le hBpos.le hCRpos.le
      (hCH0 _) (hCenv0 _),
    ?_, ?_⟩
  · unfold aux_lem_band_L1c_Cd_fn; positivity
  · subst hCR
    intro M Rm H hH hδ N n
    have hδresp' : M.delta ≤ δresp := hδ.trans (hdeltaq ▸ min_le_left _ _)
    have hrespM := hresp M hδresp'
    rcases hrespM with ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩
    have hJ0 : ∀ N om, 0 ≤ J N om := by
      intro N om
      obtain ⟨e, _, he⟩ := (hJgreat N om).1
      rw [he]
      exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
    have hCJ0 : 0 ≤ CJ := hCJ.le
    exact aux_lem_band_L1c_rooted_uniform hd E M H hH q q' hq hq'q hdq' Cenv CH hCenv0 hCH0 (henvM M H hH)
      family J ⟨hfamily, hJgreat, hJ0⟩ CJ B R hCJ0 hBpos.le hR0
      (fun K N L w => hB ▸ hpieceM M H hH K N J CJ q hCJ0 hq hJmeas hJnorm L w) hBR hCRR
      deltaq hdeltaqpos.le hδ hBδ0 hCRδ0 (hδ.trans hδq1) z r hr hr1 ℓ hℓ N n



/-- Small disorder, selected before the model, represented space, cell and slope,
prevents every diagonal finite-response limit from vanishing. -/

theorem aux_prop_conc_affine_order_diagonal_limit_positive (d : ℕ) (hd : 2 ≤ d) (I : in_J d) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ →
      ∀ (Rm : in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d),
        MeasurePreserving field P (chaosSampleLaw M).toMeasure →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (N : ℕ → ℕ) (i : Fin d) (f : Ω → ℝ),
        (∀ᵐ ω ∂P, Tendsto (fun n =>
          affineDirichletResponse (centeredCube_isBounded z hr) hP
            (Lane4.cutoffPositiveCoefficient M H (field ω) (N n) z hr) (Pi.single i 1) /
              volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
          atTop (𝓝 (f ω))) →
        ∀ᵐ ω ∂P, 0 < f ω := by
  letI : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨δ, hδpos, hmom⟩ := aux_prop_conc_affine_order_cell_moment_uniform_geometry hd I 1 le_rfl
  refine ⟨δ, hδpos, ?_⟩
  intro mC bC
  have hmC : mC = borel C(SpatialCoordinates d, ℝ) := bC.measurable_eq
  subst mC
  intro M hδ Rm H hIR Ω _ P field hfield z r hr hr1 hP N i f hlim
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, Cd, hC, hCd, hmoment⟩ := hmom z r hr hr1
  let K : ℕ → BilateralField d → ℝ := fun n ω =>
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) 0
      (I.chart z r hr (Lane4.cutoffPositiveCoefficient M H ω (N n) z hr) z r)
  let R : ℕ → Ω → ℝ := fun n ω =>
    affineDirichletResponse (centeredCube_isBounded z hr) hP
      (Lane4.cutoffPositiveCoefficient M H (field ω) (N n) z hr) (Pi.single i 1) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hKm (n : ℕ) : AEStronglyMeasurable (K n) (chaosSampleLaw M).toMeasure := by
    simpa [K] using (hmoment M Rm H hIR hδ (N n) 0).1
  have hKn (n : ℕ) : eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    simpa [K] using (hmoment M Rm H hIR hδ (N n) 0).2
  have hKpos (n : ℕ) (ω : BilateralField d) : 0 ≤ K n ω :=
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
      (originCube d 0) (by simp [originCube]) _
  have hcoer (n : ℕ) (ω : Ω) : 1 ≤ K n (field ω) * R n ω := by
    simpa [R, K] using prop_conc_cutoff_affine_coercivity I M H (field ω) (N n)
      z r hr hP (Pi.single i 1)
  have hRpos (n : ℕ) (ω : Ω) : 0 < R n ω :=
    pos_of_mul_pos_right (zero_lt_one.trans_le (hcoer n ω)) (hKpos n (field ω))
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) P :=
    (((aux_prop_conc_resp_measurable M H hIR.1 (N n) z hr hP (Pi.single i 1)).comp
      hfield.measurable).div_const _).aestronglyMeasurable
  apply aux_prop_conc_limit_positive_of_inverse_moment P R f C hRmeas
    (fun n => Filter.Eventually.of_forall (hRpos n)) ?_ hlim
  intro n
  have hmono : eLpNorm (fun ω => (R n ω)⁻¹) 1 P ≤ eLpNorm (K n ∘ field) 1 P := by
    apply eLpNorm_mono_ae_real
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hRpos n ω))]
    simpa only [one_div] using (div_le_iff₀ (hRpos n ω)).mpr (hcoer n ω)
  exact hmono.trans ((eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞))
    (μ := P) (ν := (chaosSampleLaw M).toMeasure) (g := K n) (f := field)
    (hKm n) hfield).le.trans (hKn n))


/-- Strict trace positivity at a geometry-independent small-disorder threshold.
The threshold is proved by the root inverse moment and selected by affine_order;
no extra hypothesis is added to the principal declaration. -/


theorem aux_prop_conc_affine_order_quad_aesm
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace
      (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (C0 m M : ℝ) (zcell : SpatialCoordinates d) (k : ℕ)
    (cellIdx paddedIdx : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M zcell k
      cellIdx paddedIdx hPk AE AF) :
    (∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AE ω).mulVec v) P) ∧
    (∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AF ω).mulVec v) P) := by
  obtain ⟨⟨-, hfield, -, hIR, -⟩, -, -, -, -, -, -, hAE, hAF⟩ := hyps
  have hmeas : ∀ (N : ℕ) (v : Fin d → ℝ),
      Measurable (fun ω => aux_prop_conc_setup_resp model H zcell k hPk N (field ω) v) := by
    intro N v
    exact ((aux_prop_conc_resp_measurable model H hIR.1 N zcell
      (Real.rpow_pos_of_pos zero_lt_three _) hPk v).comp hfield).div_const _
  constructor
  · intro v
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => (hmeas (NE j) v).aestronglyMeasurable) (hAE.mono fun ω h => h v)
  · intro v
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => (hmeas (NF j) v).aestronglyMeasurable) (hAF.mono fun ω h => h v)

theorem aux_prop_conc_affine_order_psd
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace
      (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (C0 m M : ℝ) (zcell : SpatialCoordinates d) (k : ℕ)
    (cellIdx paddedIdx : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M zcell k
      cellIdx paddedIdx hPk AE AF) :
    ∀ᵐ ω ∂P, ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (AE ω).mulVec v := by
  obtain ⟨-, -, -, -, -, -, -, hAE, -⟩ := hyps
  filter_upwards [hAE] with ω h v
  refine ge_of_tendsto (h v) (Eventually.of_forall fun j => ?_)
  unfold aux_prop_conc_setup_resp affineDirichletResponse
  exact div_nonneg (dirichletResponse_nonneg _ _ _) ENNReal.toReal_nonneg

/-- Strict trace positivity at a geometry-independent small-disorder threshold (single level). -/
theorem aux_prop_conc_affine_order_trace_pos (d : ℕ) (hd : 2 ≤ d) (I : in_J d) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ δ →
      ∀ (Rm : Paper.in_responses d model) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d),
        MeasurePreserving field P (chaosSampleLaw model).toMeasure →
        InfraredCharacterization model H →
      ∀ (zcell : SpatialCoordinates d) (k : ℕ) (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (NE : ℕ → ℕ) (AE : Ω → Matrix (Fin d) (Fin d) ℝ),
        (∀ᵐ ω ∂P, ∀ pvec : Fin d → ℝ,
          Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (NE j) (field ω) pvec)
            atTop (𝓝 (pvec ⬝ᵥ (AE ω).mulVec pvec))) →
        ∀ᵐ ω ∂P, 0 < Matrix.trace (AE ω) := by
  obtain ⟨delta0, hdelta0, hpos⟩ := aux_prop_conc_affine_order_diagonal_limit_positive d hd I
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hdelta Rm H Ω _ P field hfield hIR zcell k hPk NE AE hAE
  have hdiag (i : Fin d) : ∀ᵐ ω ∂P, 0 < (AE ω) i i := by
    apply hpos model hdelta Rm H hIR Ω P field hfield zcell
      ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg k)))
      hPk NE i (fun ω => (AE ω) i i)
    filter_upwards [hAE] with ω hω
    simpa only [SubdiffusiveProcess.Lane3.RelSlopes.single_dotProduct_mulVec_single] using
      hω (Pi.single i (1 : ℝ))
  have hdiag_all : ∀ᵐ ω ∂P, ∀ i : Fin d, 0 < (AE ω) i i := ae_all_iff.mpr hdiag
  letI : NeZero d := ⟨by omega⟩
  filter_upwards [hdiag_all] with ω hω
  exact Finset.sum_pos (fun i _ => hω i) Finset.univ_nonempty


/-- Cell-level identification data at the single observation level `k`: given a response space over the
padded cube equal to the killed graph, a family of solution operators converging to `G` whose quadratic
response values converge to those of `A`, the padded cube identifies the observation-cell matrix. -/
def aux_prop_conc_affine_order_cell_data
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient
        (killedSobolevGraph (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (N : ℕ → ℕ) (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ) : Prop :=
  ∀ (S : ResponseSpace (centeredCube zQ rQ hrQ)),
    S.space = killedSobolevGraph (centeredCube zQ rQ hrQ) →
    ∀ (GN : ℕ → DomainL2 (centeredCube zQ rQ hrQ) →L[ℝ] DomainL2 (centeredCube zQ rQ hrQ))
      (G : DomainL2 (centeredCube zQ rQ hrQ) →L[ℝ] DomainL2 (centeredCube zQ rQ hrQ))
      (A : Matrix (Fin d) (Fin d) ℝ),
    (∀ n f, GN n f = (responseSolution S
      (Lane4.cutoffPositiveCoefficient model H om (N n) zQ hrQ)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
    Tendsto GN atTop (𝓝 G) →
    (∀ p : Fin d → ℝ, Tendsto
      (fun n => aux_prop_conc_setup_resp model H zcell k hPk (N n) om p)
      atTop (𝓝 (p ⬝ᵥ A.mulVec p))) →
    Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zQ rQ hrQ)
      (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d)) G A)

/-- Both padded-cube operator limits identify the normalized observation-cell matrices, on one event
(single level `k`). -/
theorem aux_prop_conc_affine_order_identify (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (C0 m M : ℝ) (zcell : SpatialCoordinates d) (k : ℕ)
        (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
    ∀ᵐ omega ∂P,
      Nonempty (aux_prop_conc_LocalAffineIdentification
        (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))
        (GE paddedIdx omega) (AE omega)) ∧
      Nonempty (aux_prop_conc_LocalAffineIdentification
        (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))
        (GF paddedIdx omega) (AF omega)) := by
  letI canonicalMeasurable : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI canonicalBorel : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_actual_affine_identification
    d hd I Pin X MeyersMorrey Ccamp Sob Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro mC bC
  have hmC : mC = borel C(SpatialCoordinates d, ℝ) := bC.measurable_eq
  subst mC
  intro model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF
    C0 m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨hJoint, -, -, -, hpadded, -, -, hAE, hAF⟩ := hyps
  obtain ⟨_hprob, hfield, hmap, hIR, _hstrict, hS, hGN, hConv⟩ := hJoint
  have hdata (N : ℕ → ℕ) : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      aux_prop_conc_affine_order_cell_data model H om zcell k hPk N
        (z paddedIdx) (r paddedIdx) (hr paddedIdx) := by
    have hr1 : (3 : ℝ) ^ (-(k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
    have h := hs model Rm Sreg It H hIR hdelta zcell ((3 : ℝ) ^ (-(k : ℝ)))
      (Real.rpow_pos_of_pos zero_lt_three _) hr1 (by positivity) hPk N
    simp only [hpadded.1, hpadded.2]
    exact h
  have hEdata : ∀ᵐ om ∂P, aux_prop_conc_affine_order_cell_data model H (field om) zcell k hPk NE
        (z paddedIdx) (r paddedIdx) (hr paddedIdx) := by
    have hmapped := hdata NE
    rw [← hmap] at hmapped
    exact ae_of_ae_map (μ := P) hfield.aemeasurable hmapped
  have hFdata : ∀ᵐ om ∂P, aux_prop_conc_affine_order_cell_data model H (field om) zcell k hPk NF
        (z paddedIdx) (r paddedIdx) (hr paddedIdx) := by
    have hmapped := hdata NF
    rw [← hmap] at hmapped
    exact ae_of_ae_map (μ := P) hfield.aemeasurable hmapped
  filter_upwards [hEdata, hFdata, hConv, hAE, hAF] with om hE hF hConvOm hAEom hAFom
  exact ⟨hE (Sspace paddedIdx) (hS _) (fun n => GN paddedIdx (NE n) om)
      (GE paddedIdx om) (AE om) (fun n f => hGN _ (NE n) om f)
      (hConvOm _).1 hAEom,
    hF (Sspace paddedIdx) (hS _) (fun n => GN paddedIdx (NF n) om)
      (GF paddedIdx om) (AF om) (fun n f => hGN _ (NF n) om f)
      (hConvOm _).2 hAFom⟩

/-- Shared a.s. facts about the limiting affine-energy matrices at the observation level `k`: measurable quadratic
values, positive semidefiniteness of `A_E`, `tr A_E > 0` and the form order `m A_E ≤ A_F ≤ M A_E`. -/
theorem prop_conc_affine_order
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) :
    ∀ (C0 : ℝ) (hC0 : 1 ≤ C0),
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (m M : ℝ)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      (∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AE ω).mulVec v) P) ∧
      (∀ v : Fin d → ℝ, AEStronglyMeasurable (fun ω => v ⬝ᵥ (AF ω).mulVec v) P) ∧
      (∀ᵐ ω ∂P, ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (AE ω).mulVec v) ∧
      (∀ᵐ ω ∂P, 0 < Matrix.trace (AE ω) ∧
        ∀ pvec : Fin d → ℝ,
          m * (pvec ⬝ᵥ (AE ω).mulVec pvec) ≤ pvec ⬝ᵥ (AF ω).mulVec pvec ∧
            pvec ⬝ᵥ (AF ω).mulVec pvec ≤ M * (pvec ⬝ᵥ (AE ω).mulVec pvec)) := by
  intro C0 hC0
  letI canonicalMeasurable : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI canonicalBorel : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨deltaTrace, hdeltaTrace, htrace_all⟩ :=
    aux_prop_conc_affine_order_trace_pos d hd I
  obtain ⟨deltaId, hdeltaId, hident_all⟩ :=
    aux_prop_conc_affine_order_identify d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp
  refine ⟨min deltaTrace deltaId, lt_min hdeltaTrace hdeltaId, ?_⟩
  intro mC bC
  have hmC : mC = borel C(SpatialCoordinates d, ℝ) := bC.measurable_eq
  subst mC
  intro model hdeltaModel Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF m M
    zcell k cellIdx paddedIdx hPk AE AF hyps
  have hmeas := aux_prop_conc_affine_order_quad_aesm d model H Ω P field z r hr Sspace GN GE GF
    NE NF C0 m M zcell k cellIdx paddedIdx hPk AE AF hyps
  have hpsd := aux_prop_conc_affine_order_psd d model H Ω P field z r hr Sspace GN GE GF
    NE NF C0 m M zcell k cellIdx paddedIdx hPk AE AF hyps
  have hident := hident_all model (hdeltaModel.trans (min_le_right _ _)) Rm Sreg It H Ω P field
    z r hr Sspace GN GE GF NE NF C0 m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell, hpaddedIdx, hsymAE, hsymAF, hAE, hAF⟩ := hyps
  have hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure :=
    ⟨hJoint.2.1, hJoint.2.2.1⟩
  have htrace := htrace_all model (hdeltaModel.trans (min_le_left _ _)) Rm H Ω P field hfield
    hJoint.2.2.2.1 zcell k hPk NE AE hAE
  have hmpos : 0 < m :=
    (inv_pos.mpr (zero_lt_one.trans_le hC0)).trans_le hm
  refine ⟨hmeas.1, hmeas.2, hpsd, ?_⟩
  filter_upwards [hident, htrace, horder] with om hidOm htraceOm horderOm
  refine ⟨htraceOm, ?_⟩
  obtain ⟨E⟩ := hidOm.1
  obtain ⟨F⟩ := hidOm.2
  exact prop_conc_local_affine_identified_order
    (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
    (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))
    (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)).isOpen.measurableSet
    (centeredCube_volume_pos zcell (Real.rpow_pos_of_pos zero_lt_three _))
    (GE paddedIdx om) (GF paddedIdx om) (AE om) (AF om)
    E F m M hmpos (hmpos.trans_le hmM)
    (horderOm paddedIdx).1 (horderOm paddedIdx).2

end
end Paper
