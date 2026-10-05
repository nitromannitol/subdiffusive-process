-- Response bank `paper_responses_bank`.


-- Ported verbatim from `prop_as_response_bank`
-- (`import SubdiffusiveProcess.Paper.prop_as_response_bank` is a cycle for ChildA/`lem_finite_stopping_good_steps`,

-- (`aux_rbpf_*`, matching the source) per the general's "any aux_ prefix passes" instruction;
-- only the final theorem is renamed `aux_rbpf_uniform_responses` -> `paper_responses_bank`.
--

-- imports beyond in_responses", but `aux_rbpf_defect_moment`/`_field_identDistrib`/
-- `_source_countable`/`_measurePreserving_shift` genuinely need
-- `SubdiffusiveProcess.Paper.annealed_limit_response_transport`, `SubdiffusiveProcess.Paper.in_moments_response_moment`, and
-- `SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance` (checked: none of these three, nor their own
-- imports, reference `lem_finite_stopping_good_steps`/`finite_interval_packing`/
-- `lem_finite_good_cell`, so no cycle risk from keeping them).
module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Paper.in_responses
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance
public import SubdiffusiveProcess.Paper.annealed_limit_response_transport
public import SubdiffusiveProcess.Paper.in_moments_response_moment
public import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ## The universal constant of `p.coarse.grained.bound` -/

/-- The constant `C` of the published GMC Proposition `p.coarse.grained.bound`
(`SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound`).  It depends on the dimension only,
not on the model, the disorder, the scale, or the moment order. -/
def aux_rbpf_C0 (d : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec
    (SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)))

theorem aux_rbpf_C0_spec (d : ℕ) :
    0 < aux_rbpf_C0 d ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (ξ : ℝ),
        1 ≤ ξ →
        ξ ≤ (aux_rbpf_C0 d)⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ m : ℕ,
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm M.P.toMeasure ξ
              (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d (m : ℤ)))) ≤
            ENNReal.ofReal (aux_rbpf_C0 d * ξ * Real.log (2 + ξ) * M.delta ^ 2) := by
  have h := Classical.choose_spec (Classical.choose_spec
    (SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)))
  refine ⟨h.2.1, ?_⟩
  intro M ξ h1 hξ m
  exact (h.2.2 M ξ h1 hξ m).1

/-! ## The original coefficient field at scale `m` -/

/-- `a_m(x) = exp(∑_{j ≤ m} ω_j(x) - (m+1) τ²)`, the coefficient of `in_responses`,
as a continuous field. -/
def aux_rbpf_origField {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ⟨fun x => Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P), by
    apply Real.continuous_exp.comp
    exact (continuous_finsetSum (Finset.range (m + 1))
      fun j _ => (om (j : ℤ)).continuous).sub continuous_const⟩

theorem aux_rbpf_origField_pos {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (om : BilateralField d) (x : SpatialCoordinates d) :
    0 < aux_rbpf_origField model m om x := Real.exp_pos _

/-- The coarse original field at scale `m` on the bilateral sample space has the
law of the GMC cutoff `aCutoff M m` on the GMC potential sample space, as
regular coefficient fields. -/
theorem aux_rbpf_field_identDistrib {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    IdentDistrib
      (fun om : BilateralField d =>
        aux_annealed_limit_response_transport_scalarRegCoeffField
          (aux_rbpf_origField model m om))
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model m)
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  let τ : ℝ := _root_.SubdiffusiveProcess.Model.tauSq model.P
  let r : ℝ := Real.exp (-(m : ℝ) * τ)
  let T : C(SpatialCoordinates d, ℝ) → Homogenization.RegCoeffField d :=
    fun f => aux_annealed_limit_response_transport_scalarRegCoeffField (r • f)
  have hT : Measurable T :=
    aux_annealed_limit_response_transport_measurable_scalarRegCoeffField.comp
      (continuous_const_smul r).measurable
  have hpos := (aux_annealed_limit_response_transport_positive_field_law
    (model := model) m).symm.comp hT
  have hB : (fun om : BilateralField d =>
      T (⟨fun x => Real.exp (∑ i : Fin (m + 1), (om (i : ℤ)) x - τ), by
        continuity⟩ : C(SpatialCoordinates d, ℝ))) =
      fun om => aux_annealed_limit_response_transport_scalarRegCoeffField
        (aux_rbpf_origField model m om) := by
    funext om
    apply Homogenization.RegCoeffField.ext
    intro x
    change Homogenization.scalarMatrix
        (r * Real.exp (∑ i : Fin (m + 1), (om (i : ℤ)) x - τ)) =
      Homogenization.scalarMatrix
        (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) - ((m : ℝ) + 1) * τ))
    congr 1
    have hsum : (∑ i : Fin (m + 1), (om (i : ℤ)) x) =
        ∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x :=
      Fin.sum_univ_eq_sum_range (fun j => (om (j : ℤ)) x) (m + 1)
    rw [hsum]
    change Real.exp (-(m : ℝ) * τ) * _ = _
    rw [← Real.exp_add]
    congr 1
    ring
  have hG : (fun om : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      T (⟨fun x => Real.exp (∑ i : Fin (m + 1), ((om (i : ℕ)).1.1) x - τ), by
        continuity⟩ : C(SpatialCoordinates d, ℝ))) =
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model m := by
    funext om
    apply Homogenization.RegCoeffField.ext
    intro x
    have h := aux_annealed_limit_response_transport_source_matrix model m om x 1 r τ
      (by simp [r]) rfl
    rw [one_smul] at h
    exact h
  convert hpos using 1
  · exact hB.symm
  · exact hG.symm

/-! ## The countable dense-probe functional on both sides -/

/-- A continuous `ℝ≥0∞`-valued function has the same supremum over a dense
sequence as over the whole separable space. -/
theorem aux_rbpf_iSup_denseSeq {X : Type*} [TopologicalSpace X]
    [SeparableSpace X] [Nonempty X] (f : X → ℝ≥0∞) (hf : Continuous f) :
    (⨆ i : ℕ, f (TopologicalSpace.denseSeq X i)) = ⨆ x, f x := by
  refine le_antisymm (iSup_le fun i => le_iSup f _) (iSup_le fun x => ?_)
  set c := ⨆ i : ℕ, f (TopologicalSpace.denseSeq X i)
  have hcl : IsClosed {y : X | f y ≤ c} := isClosed_le hf continuous_const
  have hsub : closure (Set.range (TopologicalSpace.denseSeq X)) ⊆ {y : X | f y ≤ c} :=
    hcl.closure_subset_iff.mpr (Set.range_subset_iff.mpr fun i =>
      le_iSup (fun i => f (TopologicalSpace.denseSeq X i)) i)
  rw [(TopologicalSpace.denseRange_denseSeq X).closure_range] at hsub
  exact hsub (Set.mem_univ x)

/-- GMC side: the countable probe functional of `in_moments_response_moment`
evaluated on the GMC cutoff field is the normalized defect `ℳ_m(□_m)`. -/
theorem aux_rbpf_source_countable {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (om : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    aux_in_moments_response_moment_countable
        (Homogenization.originCube d (m : ℤ))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model m om) =
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m
        (Homogenization.Book.Ch02.cubeDomain
          (Homogenization.originCube d (m : ℤ))) om := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect_eq_countableRepresentative]
  unfold aux_in_moments_response_moment_countable
  rw [SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefectCountableRepresentative]
  apply iSup_congr
  intro i
  congr 1
  rw [SubdiffusiveProcess.CoarseGrainingVocab.J, Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  simpa [Homogenization.Book.Ch02.cubeDomain_coe] using!
    (Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube
      (Homogenization.originCube d (m : ℤ))
      ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ •
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
      (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) •
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model m om).toFun)

/-- The origin working cube `𝕔_m` is the open realization of `originCube d m`. -/
theorem aux_rbpf_centeredCube_origin {d : ℕ} (m : ℕ) (hr : (0 : ℝ) < 3 ^ m) :
    (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
        Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) := by
  have hsf : Homogenization.cubeScaleFactor (Homogenization.originCube d (m : ℤ)) =
      (3 : ℝ) ^ m := by
    simp [Homogenization.cubeScaleFactor, Homogenization.originCube]
  have hc : Homogenization.cubeCenter (Homogenization.originCube d (m : ℤ)) = 0 := by
    funext i
    simp [Homogenization.cubeCenter, Homogenization.originCube]
  have hr' : 0 < Homogenization.cubeScaleFactor (Homogenization.originCube d (m : ℤ)) := by
    rw [hsf]; exact hr
  rw [← centeredCube_eq_openCubeSet (Homogenization.originCube d (m : ℤ)) hr']
  change Metric.ball _ _ = Metric.ball _ _
  rw [hsf, hc]

/-- Continuity of the normalized scalar probe in the direction, from the
symmetric Dirichlet--Neumann split of the upstream response theory. -/
theorem aux_rbpf_probe_continuous {d : ℕ} (U : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.Book.Ch02.CoeffOn U)
    (hsym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric a) (c : ℝ) :
    Continuous (fun e : Homogenization.Vec d =>
      Homogenization.Book.Ch02.responseJ U a (c⁻¹ • e) (c • e)) := by
  have hTheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a hsym
  have heq : (fun e : Homogenization.Vec d =>
      Homogenization.Book.Ch02.responseJ U a (c⁻¹ • e) (c • e)) =
      fun e => (1 / 2 : ℝ) * Homogenization.vecDot (c⁻¹ • e)
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) (c⁻¹ • e)) +
        (1 / 2 : ℝ) * Homogenization.vecDot (c • e)
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) (c • e)) -
        Homogenization.vecDot (c⁻¹ • e) (c • e) := by
    funext e
    rw [hTheory.response_dirichlet_neumann_split, hTheory.dirichlet_value_by_sigma,
      hTheory.neumann_value_by_sigmaStarInv]
  rw [heq]
  have hdot : ∀ (f g : Homogenization.Vec d → Homogenization.Vec d),
      Continuous f → Continuous g →
        Continuous (fun e => Homogenization.vecDot (f e) (g e)) := by
    intro f g hf hg
    unfold Homogenization.vecDot
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)
  have hs1 : Continuous (fun e : Homogenization.Vec d => c⁻¹ • e) :=
    continuous_const_smul _
  have hs2 : Continuous (fun e : Homogenization.Vec d => c • e) :=
    continuous_const_smul _
  exact ((continuous_const.mul (hdot _ _ hs1
      ((Homogenization.continuous_matVecMul _).comp hs1))).add
    (continuous_const.mul (hdot _ _ hs2
      ((Homogenization.continuous_matVecMul _).comp hs2)))).sub (hdot _ _ hs1 hs2)

/-- MFD side: the countable probe functional evaluated on the original field is
the actual defect maximum `max_{|e|=1} J(𝕔_m, â_m^{-1/2}e, â_m^{1/2}e; a_m)`. -/
theorem aux_rbpf_target_countable {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (om : BilateralField d)
    (t : ℝ)
    (hmax : IsGreatest {s : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        s = Homogenization.ResponseJ
          (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) (by positivity) :
            Set (Homogenization.Vec d))
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
          (fun x => Homogenization.scalarMatrix
            (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
              ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))} t) :
    aux_in_moments_response_moment_countable
        (Homogenization.originCube d (m : ℤ))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
        (aux_annealed_limit_response_transport_scalarRegCoeffField
          (aux_rbpf_origField model m om)) = ENNReal.ofReal t := by
  set Q := Homogenization.originCube d (m : ℤ)
  set c := Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
  set f := aux_rbpf_origField model m om
  let U := Homogenization.Book.Ch02.cubeDomain Q
  let hdata : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U f :=
    Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
        f.continuous (aux_rbpf_origField_pos model m om) U)
  let a := hdata.toCoeffOn
  have hcube : (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) (by positivity) :
      Set (SpatialCoordinates d)) = Homogenization.openCubeSet Q :=
    aux_rbpf_centeredCube_origin m (by positivity)
  have hJ : ∀ p q : Homogenization.Vec d,
      Homogenization.ResponseJ
          (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) (by positivity) :
            Set (Homogenization.Vec d)) p q
          (fun x => Homogenization.scalarMatrix (f x)) =
        Homogenization.Book.Ch02.responseJ U a p q := by
    intro p q
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ, hcube]
    rfl
  have hobs : ∀ p q : Homogenization.Vec d,
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q
          (aux_annealed_limit_response_transport_scalarRegCoeffField f) =
        Homogenization.Book.Ch02.responseJ U a p q := by
    intro p q
    rw [← hJ, hcube]
    exact Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q _
  let g : SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d → ℝ≥0∞ := fun e =>
    ENNReal.ofReal (Homogenization.Book.Ch02.responseJ U a (c⁻¹ • (e : Homogenization.Vec d))
      (c • (e : Homogenization.Vec d)))
  have hg : Continuous g :=
    ENNReal.continuous_ofReal.comp
      ((aux_rbpf_probe_continuous U a hdata.isSymmetric c).comp continuous_subtype_val)
  have hleft : aux_in_moments_response_moment_countable Q
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
      (aux_annealed_limit_response_transport_scalarRegCoeffField f) =
      ⨆ i : ℕ, g (TopologicalSpace.denseSeq
        (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i) := by
    unfold aux_in_moments_response_moment_countable
    apply iSup_congr
    intro i
    rw [hobs]
  rw [hleft, aux_rbpf_iSup_denseSeq g hg]
  refine le_antisymm (iSup_le fun e => ?_) ?_
  · apply ENNReal.ofReal_le_ofReal
    apply hmax.2
    refine ⟨(e : Homogenization.Vec d), e.2, ?_⟩
    exact (hJ _ _).symm
  · obtain ⟨e, he, hte⟩ := hmax.1
    refine le_iSup_of_le (⟨e, he⟩ : SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) ?_
    change ENNReal.ofReal t ≤ ENNReal.ofReal (Homogenization.Book.Ch02.responseJ U a
      (c⁻¹ • e) (c • e))
    rw [hte]
    exact le_of_eq (congrArg ENNReal.ofReal (hJ _ _))

/-! ## Stationarity: every translate `y + 𝕔_m` -/

/-- The reanchored whole-field translation `ω ↦ ω(· + w)` (the `Shift` of the
response-bank statement). -/
def aux_rbpf_shift {d : ℕ} (w : SpatialCoordinates d) (om : BilateralField d) :
    BilateralField d :=
  fun j : ℤ =>
    (om j).comp
      (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_rbpf_measurePreserving_shift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (w : SpatialCoordinates d) :
    MeasurePreserving (aux_rbpf_shift w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d)) := by
    fun_prop
  refine ⟨Measurable.of_eval fun j => hc.comp (measurable_pi_apply j), ?_⟩
  simpa [aux_rbpf_shift] using! prop_as_response_bank_shift_invariance d model w

/-- The working cube `y + 𝕔_m` is the translate of `𝕔_m`. -/
theorem aux_rbpf_centeredCube_translate {d : ℕ}
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (centeredCube y r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet y
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  ext x
  change x ∈ Metric.ball y (r / 2) ↔ ∃ z ∈ Metric.ball (0 : SpatialCoordinates d) (r / 2),
    x = z + y
  constructor
  · intro hx
    refine ⟨x - y, ?_, by abel⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact hx
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, ← sub_zero z, ← dist_eq_norm]
    exact hz

/-- Translation covariance of the probe: the response on `y + 𝕔_m` with field `ω`
is the response on `𝕔_m` with the shifted field. -/
theorem aux_rbpf_response_shift {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d)
    (p q : Homogenization.Vec d) :
    Homogenization.ResponseJ
        (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d)) p q
        (fun x => Homogenization.scalarMatrix
          (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
            ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))) =
      Homogenization.ResponseJ
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) (by positivity) :
          Set (Homogenization.Vec d)) p q
        (fun x => Homogenization.scalarMatrix
          (Real.exp ((∑ j ∈ Finset.range (m + 1), (aux_rbpf_shift y om (j : ℤ)) x) -
            ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))) := by
  rw [aux_rbpf_centeredCube_translate y _ (by positivity),
    Homogenization.ResponseJ_translateSet_eq_translateCoeffField]
  congr 1
  funext x
  change Homogenization.scalarMatrix
      (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) (fun i => x i + y i)) -
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) =
    Homogenization.scalarMatrix
      (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) (cubeDilation y 0 1 x)) -
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))
  have hx : (fun i => x i + y i) = cubeDilation y 0 1 x := by
    funext i
    simp only [cubeDilation, Pi.zero_apply, sub_zero, one_mul]
    ring
  rw [hx]

/-- The pinned defect on `y + 𝕔_m` is the pinned defect on `𝕔_m` of the shifted
field. -/
theorem aux_rbpf_defect_shift {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (hIG : ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
      IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.ResponseJ
            (centeredCube y ((3 : ℝ) ^ m) (by positivity) :
              Set (Homogenization.Vec d))
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
            (fun x => Homogenization.scalarMatrix
              (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))}
        (defect m y om))
    (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) :
    defect m y om = defect m 0 (aux_rbpf_shift y om) := by
  apply (hIG m y om).unique
  have h := hIG m 0 (aux_rbpf_shift y om)
  convert h using 2
  ext t
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, aux_rbpf_response_shift model m y om _ _⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, (aux_rbpf_response_shift model m y om _ _).symm⟩

/-! ## The model-uniform response-moment supplier -/

/-- **Response moments of `in_responses`, from `p.coarse.grained.bound`.**
For the universal constant `C0 = aux_rbpf_C0 d` of the published GMC theorem, every
order `1 ≤ ξ ≤ C0⁻¹ δ⁻² |log δ|⁻¹`, every scale `m` and every centre `y`, the
pinned defect `max_{|e|=1} J(y+𝕔_m, â_m^{-1/2}e, â_m^{1/2}e; a_m)` is in `L^ξ`
and obeys the paper's bound.  Transport: GMC potential sample ↔ bilateral
field law at the coefficient-field level, dense-probe identification of the
defect on both sides, and stationarity of the field law for the centre. -/
theorem aux_rbpf_defect_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (hnn : ∀ m y om, 0 ≤ defect m y om)
    (hIG : ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
      IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.ResponseJ
            (centeredCube y ((3 : ℝ) ^ m) (by positivity) :
              Set (Homogenization.Vec d))
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
            (fun x => Homogenization.scalarMatrix
              (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))}
        (defect m y om))
    (xi : ℝ) (h1 : 1 ≤ xi)
    (hxi : xi ≤ (aux_rbpf_C0 d)⁻¹ * (model.delta ^ 2)⁻¹ *
      |Real.log model.delta|⁻¹)
    (m : ℕ) (y : SpatialCoordinates d) :
    MemLp (defect m y) (ENNReal.ofReal xi) (chaosSampleLaw model).toMeasure ∧
      (∫ om, defect m y om ^ xi ∂(chaosSampleLaw model).toMeasure) ^ (1 / xi) ≤
        aux_rbpf_C0 d * xi * Real.log (2 + xi) *
          model.delta ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  set P := (chaosSampleLaw model).toMeasure with hPdef
  set U0 := Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ))
  have hxipos : 0 < xi := lt_of_lt_of_le zero_lt_one h1
  have hID0 : IdentDistrib (fun om => ENNReal.ofReal (defect m 0 om))
      (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m U0) P model.P.toMeasure := by
    have hfield := aux_rbpf_field_identDistrib model m
    have hΦ : AEMeasurable
        (aux_in_moments_response_moment_countable (Homogenization.originCube d (m : ℤ))
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))
        (Measure.map (fun om : BilateralField d =>
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_rbpf_origField model m om)) P) := by
      rw [hfield.map_eq, ← SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_eq_map]
      exact aux_in_moments_response_moment_countable_aemeasurable _
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_lawCarrier model m) _ _
    have h := hfield.comp_of_aemeasurable hΦ
    convert h using 1
    · funext om
      exact (aux_rbpf_target_countable model m om
        (defect m 0 om) (hIG m 0 om)).symm
    · funext om
      exact (aux_rbpf_source_countable model m om).symm
  have hmeas0 : AEMeasurable (defect m 0) P := by
    have h := (ENNReal.measurable_toReal).comp_aemeasurable hID0.aemeasurable_fst
    refine h.congr (Filter.Eventually.of_forall fun om => ?_)
    simp [ENNReal.toReal_ofReal (hnn m 0 om)]
  have hmp := aux_rbpf_measurePreserving_shift model y
  have hmeas0' : AEMeasurable (defect m 0) (Measure.map
      (aux_rbpf_shift y) P) := by
    rw [hmp.map_eq]; exact hmeas0
  have hcomp : defect m y = defect m 0 ∘ aux_rbpf_shift y :=
    funext fun om => aux_rbpf_defect_shift model defect hIG m y om
  have hshift : IdentDistrib (defect m y) (defect m 0) P P := by
    rw [hcomp]
    refine ⟨hmeas0'.comp_measurable hmp.measurable, hmeas0, ?_⟩
    rw [← AEMeasurable.map_map_of_aemeasurable hmeas0' hmp.measurable.aemeasurable,
      hmp.map_eq]
  have hIDy : IdentDistrib (fun om => ENNReal.ofReal (defect m y om))
      (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m U0) P model.P.toMeasure :=
    (hshift.comp ENNReal.measurable_ofReal).trans hID0
  have hpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm P xi
      (fun om => ENNReal.ofReal (defect m y om)) ≤
      ENNReal.ofReal (aux_rbpf_C0 d * xi * Real.log (2 + xi) *
        model.delta ^ 2) := by
    have hbound := (aux_rbpf_C0_spec d).2 model xi h1 hxi m
    have heq : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm P xi
        (fun om => ENNReal.ofReal (defect m y om)) =
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure xi
          (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect model m U0) := by
      unfold SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
      congr 1
      exact (hIDy.comp (ENNReal.continuous_rpow_const (y := xi)).measurable).lintegral_eq
    rw [heq]
    exact hbound
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.paperENNRealLpNorm_ofReal_eq_eLpNorm_of_nonnegative
    P hxipos (hnn m y)] at hpaper
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hshift.aemeasurable_fst.aestronglyMeasurable] at hpaper
  have hmem : MemLp (defect m y) (ENNReal.ofReal xi) P :=
    lt_of_le_of_lt hpaper ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  have hp0 : ENNReal.ofReal xi ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hxipos
  rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hxipos.le] at hpaper
  have hB : 0 ≤ aux_rbpf_C0 d * xi * Real.log (2 + xi) *
      model.delta ^ 2 := by
    have := (aux_rbpf_C0_spec d).1
    have hlog : 0 ≤ Real.log (2 + xi) := Real.log_nonneg (by linarith)
    positivity
  rw [ENNReal.ofReal_le_ofReal_iff hB] at hpaper
  have hnorm : (fun om => ‖defect m y om‖ ^ xi) = fun om => defect m y om ^ xi := by
    funext om
    rw [Real.norm_of_nonneg (hnn m y om)]
  rw [hnorm] at hpaper
  rw [one_div]
  exact hpaper

/-- The working cube `y + 𝕔_m` as an upstream Chapter 2 domain. -/
def aux_rbpf_cubeDomain {d : ℕ} (m : ℕ) (y : SpatialCoordinates d) :
    Homogenization.Book.Ch02.Domain d where
  carrier := (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (SpatialCoordinates d))
  isDomain := by
    refine ⟨(centeredCube y ((3 : ℝ) ^ m) (by positivity)).isOpen, ?_, ?_⟩
    · exact Homogenization.Bornology.IsBounded.isBoundedDomain
        (centeredCube_isBounded y (by positivity))
    · simpa [centeredCube] using (convex_ball y (((3 : ℝ) ^ m) / 2))
  nonempty := ⟨y, by
    change y ∈ Metric.ball y (((3 : ℝ) ^ m) / 2)
    exact Metric.mem_ball_self (by positivity)⟩

/-- **The paper's `in_responses` package.**  Built from the actual coefficient,
the actual working cubes, the pinned defect maximum and the deterministic
normalization facts, with the universal constant `C = aux_rbpf_C0 d` of
Proposition `p.coarse.grained.bound` (independent of the model) and the full
admissible range `1 ≤ ξ ≤ C⁻¹ δ⁻² |log δ|⁻¹`.  The moment fields are proved
by `aux_rbpf_defect_moment`; no moment hypothesis is used. -/
def aux_rbpf_paperResponses {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (ahom_ordering : ∀ n m : ℕ, n < m →
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq model.P *
            ((m : ℝ) - n)) * SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
    (ahom_le_one : ∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ 1)
    (ahom_lower : ∀ m : ℕ,
      Real.exp (-((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) ≤
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
    (defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (hdefect_nonneg : ∀ m y om, 0 ≤ defect m y om)
    (hdefect_isGreatest :
      ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
        IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = Homogenization.ResponseJ
              (centeredCube y ((3 : ℝ) ^ m) (by positivity) :
                Set (Homogenization.Vec d))
              ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
              (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
              (fun x => Homogenization.scalarMatrix
                (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                  ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))}
          (defect m y om)) :
    in_responses d model where
  coeffAt m om x := Homogenization.scalarMatrix
    (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))
  coeffScalar m om x :=
    Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  coeffScalar_pos m om x := Real.exp_pos _
  coeffScalar_eq m om x := rfl
  coeffAt_eq m om x := rfl
  cubeAt m y := aux_rbpf_cubeDomain m y
  cubeAt_eq m y hr := rfl
  defect := defect
  defect_nonneg := hdefect_nonneg
  defect_isGreatest m y om := hdefect_isGreatest m y om
  C := aux_rbpf_C0 d
  C_pos := (aux_rbpf_C0_spec d).1
  defect_memLp xi h1 hxi m y :=
    (aux_rbpf_defect_moment hd model defect hdefect_nonneg
      hdefect_isGreatest xi h1 hxi m y).1
  moment xi h1 hxi m y :=
    (aux_rbpf_defect_moment hd model defect hdefect_nonneg
      hdefect_isGreatest xi h1 hxi m y).2
  ahom_ordering := ahom_ordering
  ahom_le_one := ahom_le_one
  ahom_lower := ahom_lower
  bRef L m om x :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model (min m L) *
      Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
        ((L : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) /
      Real.exp ((∑ j ∈ Finset.range (min m L + 1), (om (j : ℤ)) x) -
        ((((min m L : ℕ) : ℝ)) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  bRef_eq L m om x := rfl
  refScalar L j z om :=
    (volume.real (centeredCube z ((3 : ℝ) ^ (j + 2)) (by positivity) :
        Set (SpatialCoordinates d)))⁻¹ *
      ∫ x in (centeredCube z ((3 : ℝ) ^ (j + 2)) (by positivity) :
          Set (SpatialCoordinates d)),
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model (min (j + 2) L) *
          Real.exp ((∑ i ∈ Finset.range (L + 1), (om (i : ℤ)) x) -
            ((L : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) /
          Real.exp ((∑ i ∈ Finset.range (min (j + 2) L + 1), (om (i : ℤ)) x) -
            ((((min (j + 2) L : ℕ) : ℝ)) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  refScalar_eq L j z om hr := rfl

/-! ## Admissibility of a fixed order and non-vacuity of the package -/

/-- A fixed order `ξ ≥ 1` is admissible for a constant `K`, i.e.
`ξ ≤ K⁻¹ δ⁻² |log δ|⁻¹`, as soon as `δ ≤ 1/2` and `δ ≤ 1/(Kξ+1)`. -/
theorem aux_rbpf_order_admissible (K xi delta : ℝ) (hK : 0 < K) (hxi : 1 ≤ xi)
    (hpos : 0 < delta) (hhalf : delta ≤ 1 / 2) (hsmall : delta ≤ 1 / (K * xi + 1)) :
    xi ≤ K⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ := by
  have hlt1 : delta < 1 := by linarith
  have hlogneg : Real.log delta < 0 := Real.log_neg hpos hlt1
  have habs : |Real.log delta| = -Real.log delta := abs_of_neg hlogneg
  have habspos : 0 < |Real.log delta| := by rw [habs]; linarith
  have hlog : -Real.log delta ≤ delta⁻¹ - 1 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rwa [Real.log_inv] at this
  have hK' : 0 < K * xi := by positivity
  have h1 : delta * (-Real.log delta) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog hpos.le
    have hdi : delta * (delta⁻¹ - 1) = 1 - delta := by
      rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one]
    linarith
  have h2 : K * xi * delta ≤ 1 := by
    have hC1 : 0 < K * xi + 1 := by linarith
    have h := mul_le_mul_of_nonneg_left hsmall hC1.le
    rw [mul_one_div_cancel hC1.ne'] at h
    have : (K * xi + 1) * delta = K * xi * delta + delta := by ring
    linarith
  have hkey : xi * (K * delta ^ 2 * |Real.log delta|) ≤ 1 := by
    rw [habs]
    have hlogpos : 0 ≤ -Real.log delta := by linarith
    calc xi * (K * delta ^ 2 * (-Real.log delta))
        = (K * xi * delta) * (delta * (-Real.log delta)) := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 h1 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hprod : 0 < K * delta ^ 2 * |Real.log delta| := by positivity
  have heq : K⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ =
      1 / (K * delta ^ 2 * |Real.log delta|) := by
    rw [one_div, mul_inv, mul_inv]
  rw [heq, le_div_iff₀ hprod]
  exact hkey

/-- **Non-vacuity.**  Any fixed order `ξ ≥ 1` lies in the admissible range of the
paper package once `δ ≤ 1/(C0 ξ + 1)`; the moment fields of the package are then
genuine `L^ξ` statements at that order. -/
theorem aux_rbpf_paperResponses_order_mem {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (xi : ℝ) (h1 : 1 ≤ xi) (hsmall : model.delta ≤ 1 / (aux_rbpf_C0 d * xi + 1)) :
    1 ≤ xi ∧ xi ≤ (aux_rbpf_C0 d)⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ :=
  ⟨h1, aux_rbpf_order_admissible (aux_rbpf_C0 d) xi model.delta (aux_rbpf_C0_spec d).1
    h1 model.shellPrefix.delta_pos model.shellPrefix.delta_le_half hsmall⟩



theorem paper_responses_bank (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (ahom_ordering : ∀ n m : ℕ, n < m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ∧
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤
              Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq model.P *
                ((m : ℝ) - n)) * SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
        (ahom_le_one : ∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ 1)
        (ahom_lower : ∀ m : ℕ,
          Real.exp (-((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
        (defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (hdefect_nonneg : ∀ m y om, 0 ≤ defect m y om)
        (hdefect_isGreatest :
          ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
            IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
                Homogenization.vecNormSq e = 1 ∧
                t = Homogenization.ResponseJ
                  (centeredCube y ((3 : ℝ) ^ m) (by positivity) :
                    Set (Homogenization.Vec d))
                  ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
                  (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
                  (fun x => Homogenization.scalarMatrix
                    (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))}
              (defect m y om)),
        ∃ Rm : in_responses d model, Rm.C = C0 ∧ Rm.defect = defect ∧
          ∀ xi : ℝ, 1 ≤ xi → model.delta ≤ 1 / (C0 * xi + 1) →
            1 ≤ xi ∧ xi ≤ Rm.C⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ := by
  refine ⟨aux_rbpf_C0 d, (aux_rbpf_C0_spec d).1, ?_⟩
  intro model ahom_ordering ahom_le_one ahom_lower defect hdefect_nonneg hdefect_isGreatest
  refine ⟨aux_rbpf_paperResponses hd model ahom_ordering ahom_le_one ahom_lower defect
    hdefect_nonneg hdefect_isGreatest, rfl, rfl, ?_⟩
  intro xi h1 hsmall
  exact aux_rbpf_paperResponses_order_mem model xi h1 hsmall

/-- **Satisfiability of the pinned-defect hypothesis** (kept, per instruction, as a directly
usable supplier for whoever needs to CONSTRUCT a `defect`/`hdefect_nonneg`/`hdefect_isGreatest`
triple to feed `paper_responses_bank`, e.g. via `Classical.choose`/`Classical.choose_spec`).
For every model, scale, centre and sample the maximum
`max_{|e|=1} J(y+𝕔_m, â_m^{-1/2}e, â_m^{1/2}e; a_m)` is attained and nonnegative. -/
theorem aux_rbpf_defect_exists {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (y : SpatialCoordinates d)
    (om : BilateralField d) :
    ∃ t : ℝ, 0 ≤ t ∧ IsGreatest {s : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        s = Homogenization.ResponseJ
          (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d))
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
          (fun x => Homogenization.scalarMatrix
            (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
              ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))} t := by
  set c := Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m)
  set f := aux_rbpf_origField model m om
  let U := aux_rbpf_cubeDomain (d := d) m y
  let hdata : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U f :=
    Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
        f.continuous (aux_rbpf_origField_pos model m om) U)
  let a := hdata.toCoeffOn
  have hJ : ∀ p q : Homogenization.Vec d,
      Homogenization.ResponseJ
          (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d)) p q
          (fun x => Homogenization.scalarMatrix (f x)) =
        Homogenization.Book.Ch02.responseJ U a p q := by
    intro p q
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
    rfl
  let S : Set (Homogenization.Vec d) := {e | Homogenization.vecNormSq e = 1}
  have hS : S = Homogenization.euclideanSphere (0 : Homogenization.Vec d) 1 := by
    ext e
    simp [S, Homogenization.euclideanSphere, Homogenization.euclideanSqDist,
      Homogenization.vecNormSq, Homogenization.vecDot]
  have hSc : IsCompact S := by
    rw [hS]
    exact (Homogenization.isCompact_euclideanClosedBall
      (0 : Homogenization.Vec d) (by norm_num)).of_isClosed_subset
      (Homogenization.isClosed_euclideanSphere _ _)
      (Homogenization.euclideanSphere_subset_euclideanClosedBall _ _)
  have hSn : S.Nonempty :=
    ⟨_, (Classical.arbitrary (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d)).2⟩
  have hg := aux_rbpf_probe_continuous U a hdata.isSymmetric c
  obtain ⟨emax, hemax, hmax⟩ := hSc.exists_isMaxOn hSn hg.continuousOn
  refine ⟨Homogenization.Book.Ch02.responseJ U a (c⁻¹ • emax) (c • emax),
    Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _, ⟨emax, hemax, (hJ _ _).symm⟩, ?_⟩
  rintro s ⟨e, he, rfl⟩
  have h := hmax he
  change Homogenization.ResponseJ _ _ _ (fun x => Homogenization.scalarMatrix (f x)) ≤ _
  rw [hJ]
  exact h

end SubdiffusiveProcess.Paper


