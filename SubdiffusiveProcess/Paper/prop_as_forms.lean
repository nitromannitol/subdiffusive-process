module

public import SubdiffusiveProcess.Paper.prop_conc_form_data
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.ResponsePositivity
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.prop_as_response_bank
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.killed_inverse_mosco
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.lem_as_regularity
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.thm_c1
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

open scoped ENNReal NNReal
open TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Recovery sequences remain recovery sequences after a strict reindexing. -/
theorem aux_prop_as_forms_recovery_subseq {E V : Type*} [TopologicalSpace E]
    (π : V → E) (q : ℕ → V → ℝ) (F : E → EReal) (D : Set E)
    (hrec : ∀ u ∈ D, ∃ w : ℕ → V,
      Tendsto (fun n => (π (w n), (q n (w n) : EReal))) atTop (𝓝 (u, F u)))
    (t : ℕ → ℕ) (ht : StrictMono t) :
    ∀ u ∈ D, ∃ w : ℕ → V,
      Tendsto (fun n => (π (w n), (q (t n) (w n) : EReal))) atTop (𝓝 (u, F u)) := by
  intro u hu
  obtain ⟨w, hw⟩ := hrec u hu
  exact ⟨w ∘ t, hw.comp ht.tendsto_atTop⟩


/-- The dual variational lower bound persists under any cofinal reindexing. -/
theorem aux_prop_as_forms_subseq_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hG : Tendsto GN atTop (𝓝 G))
    (t : ℕ → ℕ) (ht : StrictMono t)
    (uN : ℕ → DomainL2 Q) (u : DomainL2 Q)
    (hw : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) :
    limitFormEnergy G u ≤
      liminf (fun n => sInf {e : EReal | ∃ w : S.space, w.val.1 = uN n ∧
        e = (responseForm S (a (t n)) w w : EReal)}) atTop := by
  refine iSup_le fun f => ?_
  have hEval : Continuous (fun T : DomainL2 Q →L[ℝ] DomainL2 Q => T f) :=
    continuous_id.clm_apply continuous_const
  have heval : Tendsto (fun n => GN (t n) f) atTop (𝓝 (G f)) :=
    (hEval.tendsto G).comp (hG.comp ht.tendsto_atTop)
  have hresp : Tendsto (fun n => inverseResponse S (a (t n))
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))) := by
    have hi : Tendsto (fun n => inner ℝ f (GN (t n) f)) atTop
        (𝓝 (inner ℝ f (G f))) := tendsto_const_nhds.inner heval
    apply hi.congr'
    exact Eventually.of_forall fun n => by
      change inner ℝ f (GN (t n) f) =
        inverseResponse S (a (t n)) ((sobolevVolumeLoad f).comp S.space.subtypeL)
      rw [hGN, inverseResponse_eq_load]
      rfl
  refine aux_killed_inverse_mosco_liminf _ _ _ _ _ (hw f) hresp ?_
  intro n
  exact aux_killed_inverse_mosco_dual S (fun n => a (t n)) _
    (fun _ _ => rfl) n uN f


section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_prop_as_forms_recovery_glue {E V : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (π : V → E) (q : ℕ → V → ℝ) (Elim : E → EReal)
    (hrec : ∀ u : E, Elim u < ⊤ → ∃ w : ℕ → V,
      Tendsto (fun n => (π (w n), ((q n (w n) : ℝ) : EReal))) atTop (𝓝 (u, Elim u))) :
    ∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => ⨅ v : {v : V // π v = w N}, ((q N v : ℝ) : EReal)) atTop ≤ Elim u := by
  intro u
  by_cases hu : Elim u < ⊤
  · obtain ⟨w, hw⟩ := hrec u hu
    refine ⟨fun n => π (w n), hw.fst_nhds, ?_⟩
    have hterm : ∀ N, (⨅ v : {v : V // π v = π (w N)},
        ((q N v.1 : ℝ) : EReal)) ≤ ((q N (w N) : ℝ) : EReal) :=
      fun N => iInf_le (fun v : {v : V // π v = π (w N)} => ((q N v.1 : ℝ) : EReal)) ⟨w N, rfl⟩
    calc limsup (fun N => ⨅ v : {v : V // π v = π (w N)},
          ((q N v.1 : ℝ) : EReal)) atTop
        ≤ limsup (fun N => ((q N (w N) : ℝ) : EReal)) atTop :=
          Filter.limsup_le_limsup (Eventually.of_forall hterm)
      _ = Elim u := hw.snd_nhds.limsup_eq
  · refine ⟨fun _ => u, tendsto_const_nhds, ?_⟩
    have htop : Elim u = ⊤ := top_le_iff.mp (not_lt.mp hu)
    rw [htop]
    exact le_top
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_EN_eq_sInf {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H)
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (u : DomainL2 (centeredCube z r hr)) :
    (⨅ v : {v : killedSobolevGraph (centeredCube z r hr) //
        (v : SobolevData (centeredCube z r hr)).1 = u},
      ((_root_.SubdiffusiveProcess.Paper.in_killed_energy M H HI omega N z hr
        (v : killedSobolevGraph (centeredCube z r hr))
        (v : killedSobolevGraph (centeredCube z r hr)) : ℝ) : EReal)) =
    sInf {e : EReal | ∃ w : (killedResponseSpace hP).space, w.val.1 = u ∧
      e = (responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) w w : EReal)} := by
  apply le_antisymm
  · apply le_sInf
    rintro e ⟨w, hw, rfl⟩
    refine (iInf_le (fun v : {v : ↥(killedSobolevGraph (centeredCube z r hr)) // v.val.1 = u} =>
      (in_killed_energy M H HI omega N z hr v.val v.val).toEReal) ⟨w, hw⟩).trans ?_
    apply le_of_eq
    apply congrArg Real.toEReal
    unfold _root_.SubdiffusiveProcess.Paper.in_killed_energy
    rfl
  · apply le_iInf
    intro v
    have hmem : (responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) v.val v.val).toEReal ∈
        {e : EReal | ∃ w : ↥(killedResponseSpace hP).space, w.val.1 = u ∧
          e = (responseForm (killedResponseSpace hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) w w).toEReal} :=
      ⟨v.val, v.2, rfl⟩
    refine (sInf_le hmem).trans ?_
    apply le_of_eq
    apply congrArg Real.toEReal
    unfold _root_.SubdiffusiveProcess.Paper.in_killed_energy
    rfl
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_hCoercive {d : ℕ} (hd : 2 ≤ d)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (K : ℝ)
    (hcoer : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm (a N) (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr))) :
    ∀ (n : ℕ) (v : (killedResponseSpace hP).space),
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * K) *
          responseForm (killedResponseSpace hP) (a n) v v := by
  intro n v
  refine ⟨?_, ?_⟩
  · exact Sf.h1_fractional_finite z r hr ⟨v.val, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  · have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      centeredCube_volume_pos z hr
    have hform : sobolevCoefficientForm (a n) v.val v.val =
        responseForm (killedResponseSpace hP) (a n) v v := by
      rfl
    have h := hcoer n v
    rw [hform] at h
    have hsq : cubeFractionalSqNorm hd z r hr threeQuarterOrder v.val.1 =
        (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v.val.1)).toReal ^ 2
          + ‖v.val.1‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm, cubeFractionalVecSeminormSq,
        Fin.sum_univ_one]
    have hmul := mul_le_mul_of_nonneg_left h hvol.le
    rw [hsq] at hmul
    have h1 : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v.val.1)).toReal ^ 2
          + ‖v.val.1‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
        ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v.val.1)).toReal ^ 2 := by
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hvol)]
      ring
    have h2 : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (K * responseForm (killedResponseSpace hP) (a n) v v) =
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * K *
          responseForm (killedResponseSpace hP) (a n) v v := by
      ring
    rw [h1, h2] at hmul
    exact hmul
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_hresponse_of_tendsto {d : ℕ}
    {Q : TopologicalSpace.Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ (n : ℕ) (f : DomainL2 Q), GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (f : DomainL2 Q) (L : ℝ)
    (h : Tendsto (fun n => inverseResponse S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 L)) :
    CauchySeq (fun n => inner ℝ f (GN n f)) := by
  refine (h.congr fun n => ?_).cauchySeq
  rw [hGN, inverseResponse_eq_load]
  rfl
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_countable_dense_submodule_le {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hS : Dense (S : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)), D ≤ S ∧
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) := by
  classical
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  have : SecondCountableTopology (DomainL2 (centeredCube z r hr)) := by
    change SecondCountableTopology
      (Lp ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    infer_instance
  have hIsep : TopologicalSpace.IsSeparable (S : Set (DomainL2 (centeredCube z r hr))) := by
    exact TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨T, hTS, hTc, hST⟩ :=
    TopologicalSpace.IsSeparable.exists_countable_dense_subset hIsep
  have : Countable T := hTc.to_subtype
  have hTdense : Dense (T : Set (DomainL2 (centeredCube z r hr))) := by
    rw [dense_iff_closure_eq]
    have h1 : closure (S : Set (DomainL2 (centeredCube z r hr))) ⊆
        closure (T : Set (DomainL2 (centeredCube z r hr))) := by
      simpa only [closure_closure] using closure_mono hST
    rw [dense_iff_closure_eq.mp hS] at h1
    exact top_le_iff.mp h1
  refine ⟨Submodule.span ℚ (Set.range (fun t : T => (t : DomainL2 (centeredCube z r hr)))),
    ?_, ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨t, rfl⟩
    exact hTS t.2
  · refine Countable.mono ?_ (Set.countable_range
      (fun c : T →₀ ℚ => c.sum fun i a => a • (i : DomainL2 (centeredCube z r hr))))
    intro x hx
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp hx)
  · refine Dense.mono ?_ hTdense
    intro x hx
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_exists_smooth_dense_submodule {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hdense : Dense {f : DomainL2 (centeredCube z r hr) | ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc})
    (hsub : ∀ S : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      Dense (S : Set (DomainL2 (centeredCube z r hr))) →
      ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)), D ≤ S ∧
        (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧ Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc := by
  let S : Submodule ℚ (DomainL2 (centeredCube z r hr)) :=
    { carrier := {f : DomainL2 (centeredCube z r hr) | ∃ fc : SpatialCoordinates d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc},
      zero_mem' := by
        refine ⟨fun _ : SpatialCoordinates d => (0 : ℝ), contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
        · rw [show tsupport (fun _ : SpatialCoordinates d => (0 : ℝ)) = ∅ from tsupport_zero]
          exact Set.empty_subset _
        · exact Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      add_mem' := by
        intro a b ha hb
        rcases ha with ⟨fc, hdiff, hsupp, hts, heq⟩
        rcases hb with ⟨gc, gdiff, gsupp, gts, geq⟩
        refine ⟨fc + gc, hdiff.add gdiff, hsupp.add gsupp, ?_, ?_⟩
        · exact (tsupport_add fc gc).trans (Set.union_subset hts gts)
        · exact (Lp.coeFn_add a b).trans (heq.add geq),
      smul_mem' := by
        intro c x hx
        rcases hx with ⟨fc, hdiff, hsupp, hts, heq⟩
        refine ⟨(c : ℝ) • fc, hdiff.const_smul (c : ℝ), hsupp.smul_left, ?_, ?_⟩
        · exact (tsupport_smul_subset_right (fun _ : SpatialCoordinates d => (c : ℝ)) fc).trans hts
        · have h1 : (c : ℚ) • x = (c : ℝ) • x := (Rat.cast_smul_eq_qsmul ℝ c x).symm
          rw [h1]
          exact (Lp.coeFn_smul (c : ℝ) x).trans (heq.const_smul (c : ℝ)) }
  have hSdense : Dense (S : Set (DomainL2 (centeredCube z r hr))) := hdense
  obtain ⟨D, hDS, hDc, hDd⟩ := hsub S hSdense
  exact ⟨D, hDc, hDd, fun f => hDS f.2⟩
end



section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_prop_as_forms_existsUnique_of_tendsto {X : Type*} [TopologicalSpace X]
    [T2Space X] (T : ℕ → X) (P : X → Prop) (G : X) (hP : P G)
    (hPT : ∀ G' : X, P G' → Tendsto T atTop (𝓝 G')) :
    ∃! G' : X, P G' := by
  refine ⟨G, hP, ?_⟩
  intro G' hG'
  exact tendsto_nhds_unique (hPT G' hG') (hPT G hP)
end



section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold
theorem aux_prop_as_forms_norm_sub_mul_le_norm (c v : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖v - c * v‖ ≤ ‖v‖ := by
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  calc
    ‖v - c * v‖ = ‖(1 - c) * v‖ := by
      congr 1
      ring
    _ = ‖(1 - c : ℝ)‖ * ‖v‖ := norm_mul (1 - c) v
    _ ≤ 1 * ‖v‖ := by
      gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg h1c]
      linarith
    _ = ‖v‖ := by rw [one_mul]

theorem aux_prop_as_forms_exists_contDiff_tsupport_subset_eLpNorm_sub_le {d : ℕ}
    {U : Set (Fin d → ℝ)} (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    {g : (Fin d → ℝ) → ℝ} (hgL2 : MemLp g 2 (volume.restrict U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin d → ℝ) → ℝ, MemLp φ 2 (volume.restrict U) ∧
      eLpNorm (g - φ) 2 (volume.restrict U) ≤ ENNReal.ofReal ε ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U := by
    obtain ⟨δ, hδpos, hδ⟩ :=
      hgL2.eLpNorm_indicator_le (p := (2 : ENNReal)) (by norm_num)
        ENNReal.ofNat_ne_top (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨K, hKU, hK_compact, hK_closed, hμK⟩ :=
      hUopen.measurableSet.exists_isCompact_isClosed_sdiff_lt (μ := volume)
        hUfinite hδpos.ne'
    rcases exists_compact_closed_between hK_compact hUopen hKU with
      ⟨L, hL_compact, hL_closed, hKL, hLU⟩
    rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Fin d → ℝ)) hK_closed hKL with
      ⟨η, hη_one, hη_zero, hη_range⟩
    let φ : (Fin d → ℝ) → ℝ := fun x => η x * g x
    have hη_cont : ContDiff ℝ (⊤ : ℕ∞) η := η.contMDiff.contDiff
    have hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * g x)
      exact hη_cont.mul hg_cont
    have hφ_support : Function.support φ ⊆ L := by
      intro x hx
      by_contra hxL
      have hz : η x = 0 := hη_zero x hxL
      exact hx (by simp [φ, hz])
    have hφ_compact : HasCompactSupport φ :=
      HasCompactSupport.of_support_subset_isCompact hL_compact hφ_support
    have hφ_tsupport : tsupport φ ⊆ U := by
      have hφ_tsupport_L : tsupport φ ⊆ L := by
        simpa [tsupport] using closure_minimal hφ_support hL_closed
      exact hφ_tsupport_L.trans hLU
    have hφL2 : MemLp φ 2 (volume.restrict U) :=
      hφ_cont.continuous.memLp_of_hasCompactSupport hφ_compact
    refine ⟨φ, hφL2, ?_, hφ_cont, hφ_compact, hφ_tsupport⟩
    have hμsmall : volume.restrict U (U \ K) ≤ δ := by
      rw [Measure.restrict_apply (hUopen.measurableSet.diff hK_closed.measurableSet)]
      simpa [Set.inter_eq_self_of_subset_left (sdiff_subset : U \ K ⊆ U)] using hμK.le
    have hindicator := hδ (U \ K) (hUopen.measurableSet.diff hK_closed.measurableSet) hμsmall
    calc
      eLpNorm (g - φ) 2 (volume.restrict U)
          ≤ eLpNorm ((U \ K).indicator g) 2 (volume.restrict U) := by
            refine eLpNorm_mono_ae (hgL2.aestronglyMeasurable.sub hφL2.aestronglyMeasurable) ?_
            have hmem : ∀ᵐ x ∂ volume.restrict U, x ∈ U :=
              ae_restrict_mem hUopen.measurableSet
            filter_upwards [hmem] with x hxU
            by_cases hxK : x ∈ K
            · have hφx : φ x = g x := by
                have hηx : η x = 1 := hη_one.self_of_nhdsSet x hxK
                simp [φ, hηx]
              simp [hφx, hxK]
            · have hxDiff : x ∈ U \ K := ⟨hxU, hxK⟩
              rw [Set.indicator_of_mem hxDiff]
              exact aux_prop_as_forms_norm_sub_mul_le_norm (η x) (g x) (hη_range x).1 (hη_range x).2
      _ ≤ ENNReal.ofReal ε := hindicator
end



section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold
theorem aux_prop_as_forms_dense_smooth_tsupport_subset {d : ℕ}
    {U : Set (Fin d → ℝ)} (_hUopen : IsOpen U) (_hUfinite : volume U ≠ ⊤)
    (hcut : ∀ {g : (Fin d → ℝ) → ℝ}, MemLp g 2 (volume.restrict U) → ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ {ε : ℝ}, 0 < ε → ∃ φ : (Fin d → ℝ) → ℝ, MemLp φ 2 (volume.restrict U) ∧
        eLpNorm (g - φ) 2 (volume.restrict U) ≤ ENNReal.ofReal ε ∧
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U) :
    Dense {f : Lp ℝ 2 (volume.restrict U) | ∃ fc : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧ tsupport fc ⊆ U ∧
        (f : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U] fc} := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have : IsFiniteMeasureOnCompacts (volume.restrict U) := inferInstance
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (E := Fin d → ℝ) (F := ℝ) (μ := volume.restrict U) (p := (2 : ENNReal))
    ENNReal.ofNat_ne_top
  rw [Metric.dense_iff] at hdense
  obtain ⟨g_lp, hg_ball, g, hg_ae, hg_compact, hg_cont⟩ := hdense f (ε / 2) hε2
  rw [Metric.mem_ball] at hg_ball
  have hfg_lt : dist f g_lp < ε / 2 := by
    rw [dist_comm]
    exact hg_ball
  have hgL2 : MemLp g 2 (volume.restrict U) := (MeasureTheory.Lp.memLp g_lp).ae_eq hg_ae
  obtain ⟨φ, hφL2, hφ_err, hφ_cont, hφ_compact, hφ_tsupport⟩ := hcut hgL2 hg_cont hε2
  refine ⟨hφL2.toLp φ, ?_, ?_⟩
  · exact ⟨φ, hφ_cont, hφ_compact, hφ_tsupport, hφL2.coeFn_toLp⟩
  · have hdist_gφ : dist g_lp (hφL2.toLp φ) ≤ ε / 2 := by
      rw [MeasureTheory.Lp.dist_def]
      have hcongr :
          eLpNorm ((↑↑g_lp : (Fin d → ℝ) → ℝ) - (↑↑(hφL2.toLp φ) : (Fin d → ℝ) → ℝ))
              2 (volume.restrict U) =
            eLpNorm (g - φ) 2 (volume.restrict U) := by
        apply MeasureTheory.eLpNorm_congr_ae
        filter_upwards [hg_ae, hφL2.coeFn_toLp] with x hx1 hx2
        simp only [Pi.sub_apply, hx1, hx2]
      rw [hcongr]
      exact ENNReal.toReal_le_of_le_ofReal hε2.le hφ_err
    calc
      dist (hφL2.toLp φ) f = dist f (hφL2.toLp φ) := dist_comm _ _
      _ ≤ dist f g_lp + dist g_lp (hφL2.toLp φ) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hfg_lt.le hdist_gφ
      _ = ε := by ring
end


/-! ### The small-disorder threshold, fixed once at `s = beta = 3/4` -/

/-- The `delta0` of `lem_as_coarse`, fixed once at `s = beta = 3/4` (both admissible: `3/4 ∈
Ioc 0 1` and `3/4 ∈ Ioo (1/2) 1`), so that `aux_prop_as_forms_hmesh`'s standing small-disorder
hypothesis has a definite (if opaque) threshold, exactly as `lem_as_coarse` itself is later
invoked inside `prop_as_forms`. -/
@[irreducible] noncomputable def aux_prop_as_forms_hmesh_delta0
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) : ℝ :=
  (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose

theorem aux_prop_as_forms_hmesh_delta0_pos
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    0 < aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp := by
  unfold aux_prop_as_forms_hmesh_delta0
  exact (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose_spec.1

/-! ### Step (a): the cutoff coefficient's continuous positive representative -/

/-- `cutoffPositiveCoefficient M H omega N z hr` (the `PositiveCoefficient` used by
`responseForm`) has a.e. the continuous, everywhere-positive, globally-defined representative
`cutoffCoefficient M H omega N`, and the latter is bounded above on the closed cube. -/
theorem aux_prop_as_forms_hmesh_cutoff
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Continuous (cutoffCoefficient M H omega N) ∧
      (∀ x, 0 < cutoffCoefficient M H omega N x) ∧
      (∃ Lam : ℝ, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        cutoffCoefficient M H omega N x ≤ Lam) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x =
          cutoffCoefficient M H omega N x) := by
  refine ⟨_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N,
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N, ?_, ?_⟩
  · have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
      ⟨z, Metric.mem_closedBall_self (by positivity)⟩
    have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
      isCompact_closedBall z (r / 2)
    obtain ⟨x0, -, hx0⟩ := hcompact.exists_isMaxOn hne
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N).continuousOn
    exact ⟨cutoffCoefficient M H omega N x0, isMaxOn_iff.mp hx0⟩
  · have : Fact (((centeredCube z r hr : Set (SpatialCoordinates d))) ⊆
        (closedCube z r hr : Set (SpatialCoordinates d))) :=
      ⟨centeredCube_subset_closedCube z hr⟩
    have hval := normalizedContinuousPositiveCoefficient_coeFn
      (Ω := centeredCube z r hr) (closedCube z r hr)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N z hr)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
    filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
      with x hx hxΩ
    rw [hx hxΩ, div_one]
    rfl

/-! ### The `responseForm`/`sobolevCoefficientForm` identification on `killedResponseSpace` -/

/-- `responseForm` on `killedResponseSpace hP` is literally `sobolevCoefficientForm` evaluated
at the underlying `SobolevData`. -/
theorem aux_prop_as_forms_hmesh_responseForm_eq
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (w : (killedResponseSpace hP).space) :
    responseForm (killedResponseSpace hP) a w w =
      sobolevCoefficientForm a (w : SobolevData Ω) (w : SobolevData Ω) := by
  simp only [responseForm, sobolevCoefficientForm, subspaceGradient,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]






theorem aux_prop_as_forms_hmesh_energy_bridge
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (c : SpatialCoordinates d → ℝ) (hc : Continuous c)
    (Cb : ℝ) (hcb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ‖c x‖ ≤ Cb)
    (hac : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x = c x)
    (w : H10Function (Ω : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm a (sobolevDataOfH1 w.toH1Function) (sobolevDataOfH1 w.toH1Function) =
      energy c (Ω : Set (SpatialCoordinates d)) w.toH1Function := by
  classical
  have hgrad : ∀ i : Fin d,
      ((sobolevDataOfH1 w.toH1Function).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          fun x => w.toH1Function.grad x i :=
    fun i => sobolevDataOfH1_snd_coeFn w.toH1Function i
  have hintg : ∀ i : Fin d,
      Integrable (fun x => c x * (w.toH1Function.grad x i) ^ 2)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    intro i
    have hL2 : Integrable (fun x => (w.toH1Function.grad x i) ^ 2)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (w.toH1Function.gradMemL2 i).integrable_sq
    exact hL2.bdd_mul hc.aestronglyMeasurable.restrict hcb
  have hterm : ∀ i : Fin d,
      (∫ x in (Ω : Set (SpatialCoordinates d)), a.val x *
        ((sobolevDataOfH1 w.toH1Function).2 i x * (sobolevDataOfH1 w.toH1Function).2 i x)) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), c x * (w.toH1Function.grad x i) ^ 2 := by
    intro i
    apply integral_congr_ae
    filter_upwards [hac, hgrad i] with x ha hx
    rw [ha, hx, pow_two]
  rw [sobolevCoefficientForm_apply]
  calc
    (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x *
        ((sobolevDataOfH1 w.toH1Function).2 i x * (sobolevDataOfH1 w.toH1Function).2 i x)) =
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          c x * (w.toH1Function.grad x i) ^ 2 := Finset.sum_congr rfl fun i _ => hterm i
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, c x * (w.toH1Function.grad x i) ^ 2 :=
      (integral_finsetSum Finset.univ (fun i _ => hintg i)).symm
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        c x * vecDot (w.toH1Function.grad x) (w.toH1Function.grad x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i : Fin d, c x * w.toH1Function.grad x i ^ 2) =
        c x * vecDot (w.toH1Function.grad x) (w.toH1Function.grad x)
      unfold vecDot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = energy c (Ω : Set (SpatialCoordinates d)) w.toH1Function := rfl

/-! ### Step (e): the mesh error, in `L²` -/

/-- Transfer of `mesh_interpolator`'s uniform pointwise mesh error to an `L²` bound, via
`MeasureTheory.Lp.norm_le_of_ae_bound`. The bound is uniform in the coefficient. -/
theorem aux_prop_as_forms_hmesh_L2close
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (fc : SpatialCoordinates d → ℝ) (w : SpatialCoordinates d → ℝ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (herr : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |w x - fc x| ≤ bound)
    (Q : DomainL2 (centeredCube z r hr)) (hQ : (Q : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] w)
    (phi : DomainL2 (centeredCube z r hr))
    (hphi : (phi : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] fc) :
    ‖Q - phi‖ ≤ Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
      bound := by
  have hae : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖((Q - phi : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x‖ ≤ bound := by
    filter_upwards [Lp.coeFn_sub Q phi, hQ, hphi,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hsub hQx hphix hxΩ
    rw [hsub]
    simp only [Pi.sub_apply, hQx, hphix]
    exact herr x hxΩ
  have hle := Lp.norm_le_of_ae_bound (μ := volume.restrict
    (centeredCube z r hr : Set (SpatialCoordinates d))) (p := 2) hbound hae
  have hmeas : measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) =
      (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))).toNNReal := by
    simp [measureUnivNNReal, MeasureTheory.measureReal_def]
  rw [hmeas] at hle
  have hvol0 : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ENNReal.toReal_nonneg
  have hcast : ((((volume.real (centeredCube z r hr : Set (SpatialCoordinates d))).toNNReal :
      NNReal) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ) =
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [Real.coe_toNNReal _ hvol0, show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
      ← Real.sqrt_eq_rpow]
  rwa [hcast] at hle

/-- Packaged form of `aux_prop_as_forms_hmesh_cutoff`'s bounds, ready for `mesh_interpolator`:
a single positive lower bound and an upper bound for the cutoff coefficient on the closed
cube. -/
theorem aux_prop_as_forms_hmesh_cutoff_bounds
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H omega N x ∧ cutoffCoefficient M H omega N x ≤ Lam := by
  have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by positivity)⟩
  have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    isCompact_closedBall z (r / 2)
  obtain ⟨xmin, -, hxmin⟩ := hcompact.exists_isMinOn hne
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N).continuousOn
  obtain ⟨xmax, -, hxmax⟩ := hcompact.exists_isMaxOn hne
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N).continuousOn
  exact ⟨cutoffCoefficient M H omega N xmin, cutoffCoefficient M H omega N xmax,
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N xmin,
    fun x hx => ⟨isMinOn_iff.mp hxmin x hx, isMaxOn_iff.mp hxmax x hx⟩⟩

/-! ### Step (d): the genuinely deep coarse-graining fact (OPEN) -/





variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **General additivity of `sobolevDataOfH1`.**  `sobolevDataOfH1` sends the (exact,
pointwise) sum of two `H1Function`s to the `SobolevData` sum, up to the usual `Lp`
a.e.-equality bookkeeping.  Pure assembly from `H1Function.add_toFun`/`add_grad`
(exact pointwise sums) and `sobolevDataOfH1_fst_coeFn`/`_snd_coeFn` (a.e. `Lp`
representatives), in the same style as `sobolevDataOfH1_mem_killed`. -/
theorem aux_prop_as_forms_cb_sobolevDataOfH1_add
    (u v : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 (u + v) = sobolevDataOfH1 u + sobolevDataOfH1 v := by
  refine Prod.ext ?_ ?_
  · show (sobolevDataOfH1 (u + v)).1 = (sobolevDataOfH1 u).1 + (sobolevDataOfH1 v).1
    apply Lp.ext
    have hL : ((sobolevDataOfH1 (u + v)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] (u + v).toFun :=
      sobolevDataOfH1_fst_coeFn (u + v)
    have hRu : ((sobolevDataOfH1 u).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] u.toFun :=
      sobolevDataOfH1_fst_coeFn u
    have hRv : ((sobolevDataOfH1 v).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] v.toFun :=
      sobolevDataOfH1_fst_coeFn v
    have hadd : ((sobolevDataOfH1 u).1 + (sobolevDataOfH1 v).1 :
        Lp ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => (sobolevDataOfH1 u).1 x + (sobolevDataOfH1 v).1 x :=
      Lp.coeFn_add _ _
    filter_upwards [hL, hRu, hRv, hadd] with x hLx hRux hRvx haddx
    rw [hLx, haddx, hRux, hRvx, H1Function.add_toFun]
  · funext i
    show (sobolevDataOfH1 (u + v)).2 i = (sobolevDataOfH1 u).2 i + (sobolevDataOfH1 v).2 i
    apply Lp.ext
    have hL : (((sobolevDataOfH1 (u + v)).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => (u + v).grad x i :=
      sobolevDataOfH1_snd_coeFn (u + v) i
    have hRu : (((sobolevDataOfH1 u).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => u.grad x i :=
      sobolevDataOfH1_snd_coeFn u i
    have hRv : (((sobolevDataOfH1 v).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => v.grad x i :=
      sobolevDataOfH1_snd_coeFn v i
    have hadd : (((sobolevDataOfH1 u).2 i + (sobolevDataOfH1 v).2 i : DomainL2 Ω) :
        SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => ((sobolevDataOfH1 u).2 i : DomainL2 Ω) x + ((sobolevDataOfH1 v).2 i : DomainL2 Ω) x :=
      Lp.coeFn_add _ _
    filter_upwards [hL, hRu, hRv, hadd] with x hLx hRux hRvx haddx
    rw [hLx, haddx, hRux, hRvx, H1Function.add_grad]
    rfl



theorem aux_prop_as_forms_cb_energy_bridge
    (a : PositiveCoefficient Ω) (c : SpatialCoordinates d → ℝ) (hc : Continuous c)
    (Cb : ℝ) (hcb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ‖c x‖ ≤ Cb)
    (hac : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x = c x)
    (w : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm a (sobolevDataOfH1 w) (sobolevDataOfH1 w) =
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy c (Ω : Set (SpatialCoordinates d)) w := by
  classical
  have hgrad : ∀ i : Fin d,
      ((sobolevDataOfH1 w).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => w.grad x i :=
    fun i => sobolevDataOfH1_snd_coeFn w i
  have hintg : ∀ i : Fin d,
      Integrable (fun x => c x * (w.grad x i) ^ 2)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    intro i
    have hL2 : Integrable (fun x => (w.grad x i) ^ 2)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (w.gradMemL2 i).integrable_sq
    exact hL2.bdd_mul hc.aestronglyMeasurable.restrict hcb
  have hterm : ∀ i : Fin d,
      (∫ x in (Ω : Set (SpatialCoordinates d)), a.val x *
        ((sobolevDataOfH1 w).2 i x * (sobolevDataOfH1 w).2 i x)) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), c x * (w.grad x i) ^ 2 := by
    intro i
    apply integral_congr_ae
    filter_upwards [hac, hgrad i] with x ha hx
    rw [ha, hx, pow_two]
  rw [sobolevCoefficientForm_apply]
  calc
    (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x *
        ((sobolevDataOfH1 w).2 i x * (sobolevDataOfH1 w).2 i x)) =
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          c x * (w.grad x i) ^ 2 := Finset.sum_congr rfl fun i _ => hterm i
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, c x * (w.grad x i) ^ 2 :=
      (integral_finsetSum Finset.univ (fun i _ => hintg i)).symm
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        c x * vecDot (w.grad x) (w.grad x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i : Fin d, c x * w.grad x i ^ 2) =
        c x * vecDot (w.grad x) (w.grad x)
      unfold vecDot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy c
        (Ω : Set (SpatialCoordinates d)) w := rfl



theorem aux_prop_as_forms_cb_infimum_le_response
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (c : SpatialCoordinates d → ℝ) (hc : Continuous c)
    (Cb : ℝ) (hcb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ‖c x‖ ≤ Cb)
    (hac : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x = c x)
    (hΩ : MeasurableSet (Ω : Set (SpatialCoordinates d)))
    (hcpos : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ c x)
    (beta : H1Function (Ω : Set (SpatialCoordinates d)))
    (b : weakSobolevGraph Ω) (hb : (b : SobolevData Ω) = sobolevDataOfH1 beta) :
    cellDirichletInfimum c (Ω : Set (SpatialCoordinates d)) beta ≤
      dirichletResponse (killedResponseSpace hP) a b := by
  classical
  set S := killedResponseSpace hP with hS_def
  set w : S.space :=
    responseSolution S a (boundaryCorrectionLoad S a b) with hw_def
  -- `S.space` is `killedSobolevGraph Ω` definitionally.
  set wK : killedSobolevGraph Ω := w with hwK_def
  obtain ⟨v_w, hv_val, hv_grad⟩ := exists_nativeH10Function_of_killedSobolevGraph wK
  set u_H1 : H1Function (Ω : Set (SpatialCoordinates d)) := beta + v_w.toH1Function with hu_def
  have htrace : HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) u_H1 beta := by
    refine ⟨v_w, ?_, ?_⟩
    · intro x
      have := congrFun (H1Function.add_toFun beta v_w.toH1Function) x
      simp [hu_def]
    · intro x
      have := congrFun (H1Function.add_grad beta v_w.toH1Function) x
      simp [hu_def]
  have hmem : energy c (Ω : Set (SpatialCoordinates d)) u_H1 ∈
      {e : ℝ | ∃ u : H1Function (Ω : Set (SpatialCoordinates d)),
        HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) u beta ∧
          e = energy c (Ω : Set (SpatialCoordinates d)) u} :=
    ⟨u_H1, htrace, rfl⟩
  have hbdd : BddBelow {e : ℝ | ∃ u : H1Function (Ω : Set (SpatialCoordinates d)),
      HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) u beta ∧
        e = energy c (Ω : Set (SpatialCoordinates d)) u} := by
    refine ⟨0, ?_⟩
    rintro e ⟨u, -, rfl⟩
    unfold SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy
    apply setIntegral_nonneg hΩ
    intro x hx
    have hvd : 0 ≤ vecDot (u.grad x) (u.grad x) := by
      unfold vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact mul_nonneg (hcpos x hx) hvd
  have hle : cellDirichletInfimum c (Ω : Set (SpatialCoordinates d)) beta ≤
      energy c (Ω : Set (SpatialCoordinates d)) u_H1 := by
    unfold cellDirichletInfimum
    exact csInf_le hbdd hmem
  refine hle.trans ?_
  have hbridge := aux_prop_as_forms_cb_energy_bridge a c hc Cb hcb hac u_H1
  rw [← hbridge]
  have hadd : sobolevDataOfH1 u_H1 = sobolevDataOfH1 beta + sobolevDataOfH1 v_w.toH1Function :=
    aux_prop_as_forms_cb_sobolevDataOfH1_add beta v_w.toH1Function
  have hvwEq : sobolevDataOfH1 v_w.toH1Function = (wK : SobolevData Ω) := by
    refine Prod.ext ?_ ?_
    · apply Lp.ext
      have hL := sobolevDataOfH1_fst_coeFn v_w.toH1Function
      filter_upwards [hL] with x hx
      rw [hx]
      exact congrFun hv_val x
    · funext i
      apply Lp.ext
      have hL := sobolevDataOfH1_snd_coeFn v_w.toH1Function i
      filter_upwards [hL] with x hx
      rw [hx]
      exact congrFun (congrFun hv_grad x) i
  have hbEq : sobolevDataOfH1 u_H1 = (b : SobolevData Ω) + (w : SobolevData Ω) := by
    rw [hadd, hvwEq, hb]
  rw [hbEq]
  exact le_of_eq rfl


/-- Generic extraction of `SubdiffusiveProcess.Paper.lem_as_coarse`'s 4th (`dirichletResponse`) conjunct at
`s = beta = 3/4`, for ANY triadic cube `(z, r)`, reusing the same small-disorder threshold
`aux_prop_as_forms_hmesh_delta0` already fixed for `cell_bound`'s standing inputs. Applied below
to each odd-grid subcell, not just the root cube: `lem_as_coarse`'s own quantifier order allows
any `(z, r)` once the model-level threshold `hsmall` is fixed. -/
theorem aux_prop_as_forms_cb_coarse_spec
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (hsmall : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ)
        (hP : ∃ C0 : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            C0 * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn (3 / 4 : ℝ) (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP)
            (cutoffPositiveCoefficient M H omega N z hr) b ≤
          K * r ^ ((d : ℝ) - 2) * (r ^ (3 / 4 : ℝ) *
            holderSeminorm (3 / 4 : ℝ)
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  have hsmall' := hsmall
  unfold aux_prop_as_forms_hmesh_delta0 at hsmall'
  have hspec := (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose_spec.2
    M Rm Sreg It H HI hsmall' z r hr htri
  filter_upwards [hspec] with omega hω
  obtain ⟨K, hK, hall⟩ := hω
  exact ⟨K, hK, fun N hP G b hGcont hGhold hGb => (hall true).2.2.2 N hP G b hGcont hGhold hGb⟩

/-- Nonnegativity of `holderSeminorm`: either its ratio set is empty (`sSup ∅ = 0`), or every
member is a nonnegative ratio, so any member already witnesses `0 ≤ sSup`. -/
theorem aux_prop_as_forms_cb_holderSeminorm_nonneg
    {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ)
    (hbdd : BddAbove (holderRatioSet beta S G)) :
    0 ≤ holderSeminorm beta S G := by
  rcases (holderRatioSet beta S G).eq_empty_or_nonempty with he | hne
  · unfold holderSeminorm
    rw [he, Real.sSup_empty]
  · obtain ⟨v, hv⟩ := hne
    have hv0 : 0 ≤ v := by
      obtain ⟨x, -, y, -, -, hveq⟩ := hv
      rw [hveq]; positivity
    exact hv0.trans (le_csSup hbdd hv)

/-- **The Lipschitz-to-Hölder conversion.** `fc`'s global derivative supremum `G0` (computed on
the closure of the ROOT cube `centeredCube z r hr`, which contains `fc`'s support, hence bounds
`‖fderiv fc‖` everywhere via the mean value inequality on that convex closure) gives both that
`fc` is genuinely `3/4`-Hölder on the frontier of any odd-grid subcell, and an explicit bound on
its seminorm there in terms of `G0` and the subcell's own side length. The bound goes through the
sup-metric Lipschitz estimate (`abs_sub_le_mul_dist`, since `SpatialCoordinates d` carries
the maximum norm) composed with the standard sup-norm-vs-Euclidean-norm inequality `dist ≤
√(Σ(xⱼ-yⱼ)²)` (`heuclid_ge` below); the sharper Euclidean-vs-`√d·sup` direction is not needed. -/
theorem aux_prop_as_forms_cb_holder
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {fc : SpatialCoordinates d → ℝ} (hfc_smooth : ContDiff ℝ ∞ fc)
    (m : ℕ) (k : OddGridIndex d m) :
    IsHolderOn (3 / 4 : ℝ)
        (frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d))) fc ∧
      holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d))) fc ≤
        sSup ((fun q => ‖fderiv ℝ fc q‖) ''
            closure (centeredCube z r hr : Set (SpatialCoordinates d))) *
          (r / (2 * (m : ℝ) + 1)) ^ (1 / 4 : ℝ) := by
  set G0 : ℝ := sSup ((fun q => ‖fderiv ℝ fc q‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d))) with hG0def
  have hG0nn : 0 ≤ G0 := sSup_fderiv_nonneg hfc_smooth z hr
  set side : ℝ := r / (2 * (m : ℝ) + 1) with hsidedef
  have hsidepos : 0 < side := div_pos hr (by positivity)
  have hbound_sup : ∀ x y : SpatialCoordinates d,
      x ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      y ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      |fc x - fc y| ≤ G0 * dist x y := by
    intro x y hx hy
    have hxc : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      closure_oddGridCell_subset z hr m k (frontier_subset_closure hx)
    have hyc : y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      closure_oddGridCell_subset z hr m k (frontier_subset_closure hy)
    have hbnd : ∀ w ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ‖fderiv ℝ fc w‖ ≤ G0 :=
      fun w hw => le_sSup_image (isCompact_closure_centeredCube z hr)
        (continuous_norm_fderiv hfc_smooth) hw
    have h' : |fc y - fc x| ≤ G0 * dist y x :=
      abs_sub_le_mul_dist hfc_smooth (convex_closure_centeredCube z hr) hbnd hxc hyc
    rwa [abs_sub_comm, dist_comm y x] at h'
  have hdiam : ∀ x y : SpatialCoordinates d,
      x ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      y ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      dist x y ≤ side := by
    intro x y hx hy
    have hcellEq : (oddGridCell z r hr m k : Set (SpatialCoordinates d)) =
        Metric.ball (oddGridCenter z r m k) (side / 2) := rfl
    have hxcl : x ∈ closure (Metric.ball (oddGridCenter z r m k) (side / 2)) := by
      rw [← hcellEq]; exact frontier_subset_closure hx
    have hycl : y ∈ closure (Metric.ball (oddGridCenter z r m k) (side / 2)) := by
      rw [← hcellEq]; exact frontier_subset_closure hy
    have hxb := Metric.closure_ball_subset_closedBall hxcl
    have hyb := Metric.closure_ball_subset_closedBall hycl
    have htri := dist_triangle x (oddGridCenter z r m k) y
    simp only [Metric.mem_closedBall] at hxb hyb
    rw [dist_comm (oddGridCenter z r m k) y] at htri
    linarith
  have heuclid_ge : ∀ x y : SpatialCoordinates d,
      dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    intro x y
    have hnn : (0 : ℝ) ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_nonneg _
    rw [dist_pi_le_iff hnn]
    intro i
    rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)
  have hkey : ∀ x y : SpatialCoordinates d,
      x ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      y ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) → x ≠ y →
      |fc x - fc y| ≤ (G0 * side ^ (1 / 4 : ℝ)) *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (3 / 4 : ℝ) := by
    intro x y hx hy hxy
    have hdsup_pos : 0 < dist x y := dist_pos.mpr hxy
    have hdsup_nn : 0 ≤ dist x y := hdsup_pos.le
    have hsplit : dist x y = dist x y ^ (1 / 4 : ℝ) * dist x y ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hdsup_pos]
      norm_num
    have h1 : |fc x - fc y| ≤ G0 * dist x y := hbound_sup x y hx hy
    have h2 : dist x y ^ (1 / 4 : ℝ) ≤ side ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hdsup_nn (hdiam x y hx hy) (by norm_num)
    have h3 : dist x y ^ (3 / 4 : ℝ) ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow hdsup_nn (heuclid_ge x y) (by norm_num)
    have hp34nn : (0 : ℝ) ≤ dist x y ^ (3 / 4 : ℝ) := Real.rpow_nonneg hdsup_nn _
    calc |fc x - fc y| ≤ G0 * dist x y := h1
      _ = G0 * (dist x y ^ (1 / 4 : ℝ) * dist x y ^ (3 / 4 : ℝ)) := by rw [← hsplit]
      _ ≤ G0 * (side ^ (1 / 4 : ℝ) * dist x y ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hp34nn) hG0nn
      _ ≤ G0 * (side ^ (1 / 4 : ℝ) *
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hsidepos.le _)) hG0nn
      _ = (G0 * side ^ (1 / 4 : ℝ)) *
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (3 / 4 : ℝ) := by ring
  have hMain : ∀ v ∈ holderRatioSet (3 / 4 : ℝ)
      (frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d))) fc,
      v ≤ G0 * side ^ (1 / 4 : ℝ) := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hEuc_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      lt_of_lt_of_le (dist_pos.mpr hxy) (heuclid_ge x y)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hEuc_pos (3 / 4 : ℝ))).mpr (hkey x y hx hy hxy)
  refine ⟨⟨G0 * side ^ (1 / 4 : ℝ), hMain⟩, ?_⟩
  exact Real.sSup_le hMain (mul_nonneg hG0nn (Real.rpow_nonneg hsidepos.le _))



theorem aux_prop_as_forms_cb_percell
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (hsmall : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j)
    (J : ℕ) (k : OddGridIndex d (triadicHalf J)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
        (hfc_supp : HasCompactSupport fc)
        (_hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
        cellDirichletInfimum (cutoffCoefficient M H omega N)
            (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
            ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                (hfc_smooth.of_le (by simp)) hfc_supp).restrict
              (oddGridCell z r hr (triadicHalf J) k).isOpen
              (oddGridCell_subset z hr (triadicHalf J) k)) ≤
          K * (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ ((d : ℝ) - 2) *
            ((r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ (3 / 4 : ℝ) *
              holderSeminorm (3 / 4 : ℝ)
                (frontier (oddGridCell z r hr (triadicHalf J) k :
                  Set (SpatialCoordinates d))) fc) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  have hsidepos : 0 < r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1) := div_pos hr (by positivity)
  have hj' : ∃ j' : ℤ, r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1) = (3 : ℝ) ^ j' := by
    obtain ⟨j, hj⟩ := htri
    refine ⟨j - (J : ℤ), ?_⟩
    rw [cell_side_eq r J, hj, ← zpow_natCast (3 : ℝ) J,
      ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hcoarse := aux_prop_as_forms_cb_coarse_spec hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hsmall
    (oddGridCenter z r (triadicHalf J) k) (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) hsidepos hj'
  filter_upwards [hcoarse] with omega hω
  obtain ⟨K, hK, hall⟩ := hω
  refine ⟨K, hK, ?_⟩
  intro N fc hfc_smooth hfc_supp _hfc_sub
  have : IsFiniteMeasure (volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) :=
    centeredCube_isFiniteMeasure (oddGridCenter z r (triadicHalf J) k)
      (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) hsidepos
  have hPoincare : ∃ K0 : ℝ≥0, ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K0 * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖ := by
    have hdom : IsOpenBoundedConvexDomain
        (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      refine ⟨(oddGridCell z r hr (triadicHalf J) k).isOpen,
        (centeredCube_isBounded _ hsidepos).isBoundedDomain, ?_⟩
      change Convex ℝ (Metric.ball (oddGridCenter z r (triadicHalf J) k)
        ((r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) / 2))
      exact convex_ball _ _
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (oddGridCell z r hr (triadicHalf J) k) hdom).1
  set betaH1 : H1Function (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) :=
    (H1Function.ofContDiff (centeredCube z r hr).isOpen
      (hfc_smooth.of_le (by simp)) hfc_supp).restrict
      (oddGridCell z r hr (triadicHalf J) k).isOpen
      (oddGridCell_subset z hr (triadicHalf J) k) with hbetaH1def
  have hbetaFun : (betaH1 : SpatialCoordinates d → ℝ) = fc := rfl
  set b : weakSobolevGraph (oddGridCell z r hr (triadicHalf J) k) :=
    ⟨sobolevDataOfH1 betaH1, sobolevDataOfH1_mem_weak betaH1⟩ with hbdef
  have hbSob : (b : SobolevData (oddGridCell z r hr (triadicHalf J) k)) =
      sobolevDataOfH1 betaH1 := rfl
  obtain ⟨hCutCont, hCutPos, ⟨Lam, hLam⟩, hCutAe⟩ :=
    aux_prop_as_forms_hmesh_cutoff M H omega N (oddGridCenter z r (triadicHalf J) k) hsidepos
  have habridge := aux_prop_as_forms_cb_infimum_le_response hPoincare
    (cutoffPositiveCoefficient M H omega N (oddGridCenter z r (triadicHalf J) k) hsidepos)
    (cutoffCoefficient M H omega N) hCutCont Lam
    (by
      filter_upwards [ae_restrict_mem
        (oddGridCell z r hr (triadicHalf J) k).isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (hCutPos x)]
      exact hLam x (centeredCube_subset_closedCube (oddGridCenter z r (triadicHalf J) k)
        hsidepos hx))
    hCutAe (oddGridCell z r hr (triadicHalf J) k).isOpen.measurableSet
    (fun x _ => (hCutPos x).le) betaH1 b hbSob
  have hGcont : ContinuousOn fc
      (closedCube (oddGridCenter z r (triadicHalf J) k)
        (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) hsidepos :
        Set (SpatialCoordinates d)) :=
    hfc_smooth.continuous.continuousOn
  obtain ⟨hHolderOn, -⟩ := aux_prop_as_forms_cb_holder z hr hfc_smooth (triadicHalf J) k
  have hbEqfc : ((b : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1 :
      SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))]
        fc := by
    rw [hbSob]
    have hfst := sobolevDataOfH1_fst_coeFn betaH1
    rwa [hbetaFun] at hfst
  have h4 := hall N hPoincare fc b hGcont hHolderOn hbEqfc
  exact habridge.trans h4

/-- The uniform odd-grid cell-energy bound for smooth compactly supported
boundary data. The proof uses the Dirichlet-response estimate, identifies
the competitor infimum, converts the Lipschitz bound to the Euclidean Hölder
bound, and sums the finite cell partition. `aux_prop_as_forms_cb_holder`
supplies the norm conversion. All coefficient and Sobolev inputs remain
explicit in the theorem statement. -/
theorem aux_prop_as_forms_hmesh_cell_bound
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (hsmall : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (J : ℕ)
      (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
      (hfc_supp : HasCompactSupport fc)
      (_hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
      ∃ C : ℝ, ∀ N : ℕ,
        (∑ k : OddGridIndex d (triadicHalf J),
          cellDirichletInfimum (cutoffCoefficient M H omega N)
            (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
            ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                (hfc_smooth.of_le (by simp)) hfc_supp).restrict
              (oddGridCell z r hr (triadicHalf J) k).isOpen
              (oddGridCell_subset z hr (triadicHalf J) k))) ≤ C := by
  have : NeZero d := ⟨by omega⟩
  have hpercell : ∀ (J : ℕ) (k : OddGridIndex d (triadicHalf J)),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
          (hfc_supp : HasCompactSupport fc)
          (hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
          cellDirichletInfimum (cutoffCoefficient M H omega N)
              (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
              ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                  (hfc_smooth.of_le (by simp)) hfc_supp).restrict
                (oddGridCell z r hr (triadicHalf J) k).isOpen
                (oddGridCell_subset z hr (triadicHalf J) k)) ≤
            K * (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ ((d : ℝ) - 2) *
              ((r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ (3 / 4 : ℝ) *
                holderSeminorm (3 / 4 : ℝ)
                  (frontier (oddGridCell z r hr (triadicHalf J) k :
                    Set (SpatialCoordinates d))) fc) ^ 2 :=
    fun J k => aux_prop_as_forms_cb_percell hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hsmall
      z r hr htri J k
  have hall : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (J : ℕ) (k : OddGridIndex d (triadicHalf J)),
      ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
          (hfc_supp : HasCompactSupport fc)
          (hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))),
          cellDirichletInfimum (cutoffCoefficient M H omega N)
              (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
              ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                  (hfc_smooth.of_le (by simp)) hfc_supp).restrict
                (oddGridCell z r hr (triadicHalf J) k).isOpen
                (oddGridCell_subset z hr (triadicHalf J) k)) ≤
            K * (r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ ((d : ℝ) - 2) *
              ((r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) ^ (3 / 4 : ℝ) *
                holderSeminorm (3 / 4 : ℝ)
                  (frontier (oddGridCell z r hr (triadicHalf J) k :
                    Set (SpatialCoordinates d))) fc) ^ 2 :=
    ae_all_iff.mpr fun J => ae_all_iff.mpr fun k => hpercell J k
  filter_upwards [hall] with omega hω J fc hfc_smooth hfc_supp hfc_sub
  choose K hK hbound using hω J
  set G0 : ℝ := sSup ((fun q => ‖fderiv ℝ fc q‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d))) with hG0def
  set side : ℝ := r / (2 * ((triadicHalf J : ℕ) : ℝ) + 1) with hsidedef
  have hsidepos : 0 < side := div_pos hr (by positivity)
  have hG0nn : 0 ≤ G0 := sSup_fderiv_nonneg hfc_smooth z hr
  have hHolder : ∀ k : OddGridIndex d (triadicHalf J),
      holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc ≤
        G0 * side ^ (1 / 4 : ℝ) :=
    fun k => (aux_prop_as_forms_cb_holder z hr hfc_smooth (triadicHalf J) k).2
  have hHolderNonneg : ∀ k : OddGridIndex d (triadicHalf J),
      0 ≤ holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc :=
    fun k => aux_prop_as_forms_cb_holderSeminorm_nonneg _ _ _
      (aux_prop_as_forms_cb_holder z hr hfc_smooth (triadicHalf J) k).1
  refine ⟨∑ k : OddGridIndex d (triadicHalf J),
    K k * side ^ ((d : ℝ) - 2) * (side ^ (3 / 4 : ℝ) * (G0 * side ^ (1 / 4 : ℝ))) ^ 2, ?_⟩
  intro N
  apply Finset.sum_le_sum
  intro k _
  have hbk := hbound k N fc hfc_smooth hfc_supp hfc_sub
  refine hbk.trans ?_
  have hside34nn : (0 : ℝ) ≤ side ^ (3 / 4 : ℝ) := Real.rpow_nonneg hsidepos.le _
  have hstep : side ^ (3 / 4 : ℝ) *
      holderSeminorm (3 / 4 : ℝ)
        (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc ≤
      side ^ (3 / 4 : ℝ) * (G0 * side ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left (hHolder k) hside34nn
  have hstepnn : (0 : ℝ) ≤ side ^ (3 / 4 : ℝ) *
      holderSeminorm (3 / 4 : ℝ)
        (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc :=
    mul_nonneg hside34nn (hHolderNonneg k)
  have hsq : (side ^ (3 / 4 : ℝ) *
        holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc) ^ 2 ≤
      (side ^ (3 / 4 : ℝ) * (G0 * side ^ (1 / 4 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hstepnn hstep 2
  have haNN : (0 : ℝ) ≤ K k * side ^ ((d : ℝ) - 2) :=
    mul_nonneg (hK k).le (Real.rpow_nonneg hsidepos.le _)
  exact mul_le_mul_of_nonneg_left hsq haNN

/-! ### Assembly setup (own heartbeat budget, split off `aux_prop_as_forms_hmesh`) -/

/-- Given the cell bound `hcell` at a fixed `omega` and a fixed smooth compactly-supported
datum `fc`, choose the mesh depth `J` so the (coefficient-independent) mesh error is `< ε`,
build the mesh interpolant `wf n` at that depth for every cutoff level `n` (`mesh_interpolator`),
and package its uniform-in-`N` response bound, its cellwise energy decomposition and its `L^∞`
mesh error all at once. Split out from `aux_prop_as_forms_hmesh` purely for the heartbeat
budget: each of `aux_prop_as_forms_hmesh_setup` and `aux_prop_as_forms_hmesh` gets its own
default `maxHeartbeats`, instead of the combined proof needing an override. -/
theorem aux_prop_as_forms_hmesh_setup
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
    (hfc_supp : HasCompactSupport fc)
    (hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (ε : ℝ) (hε : 0 < ε)
    (hcell : ∀ (J : ℕ)
        (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ ∞ fc)
        (hfc_supp : HasCompactSupport fc),
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ C : ℝ, ∀ N : ℕ,
        (∑ k : OddGridIndex d (triadicHalf J),
          cellDirichletInfimum (cutoffCoefficient M H omega N)
            (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
            ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                (hfc_smooth.of_le (by simp)) hfc_supp).restrict
              (oddGridCell z r hr (triadicHalf J) k).isOpen
              (oddGridCell_subset z hr (triadicHalf J) k))) ≤ C) :
    ∃ (Cmesh G : ℝ), 0 ≤ Cmesh ∧ 0 ≤ G ∧
      ∃ (J : ℕ) (C : ℝ) (wf : ℕ → H10Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ N : ℕ, (∑ k : OddGridIndex d (triadicHalf J),
            cellDirichletInfimum (cutoffCoefficient M H omega N)
              (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
              ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                  (hfc_smooth.of_le (by simp)) hfc_supp).restrict
                (oddGridCell z r hr (triadicHalf J) k).isOpen
                (oddGridCell_subset z hr (triadicHalf J) k))) ≤ C) ∧
        (∀ n : ℕ, energy (cutoffCoefficient M H omega n)
            (centeredCube z r hr : Set (SpatialCoordinates d)) (wf n).toH1Function =
            ∑ k : OddGridIndex d (triadicHalf J), cellDirichletInfimum (cutoffCoefficient M H omega n)
              (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
              ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                  (hfc_smooth.of_le (by simp)) hfc_supp).restrict
                (oddGridCell z r hr (triadicHalf J) k).isOpen
                (oddGridCell_subset z hr (triadicHalf J) k))) ∧
        (∀ n : ℕ, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            |(wf n).toH1Function.toFun x - fc x| ≤ Cmesh * (r / (3 : ℝ) ^ J) * G) ∧
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
            (Cmesh * (r / (3 : ℝ) ^ J) * G) < ε := by
  set G : ℝ := sSup ((fun q => ‖fderiv ℝ fc q‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d))) with hGdef
  have hGnn : 0 ≤ G := sSup_fderiv_nonneg hfc_smooth z hr
  obtain ⟨Cmesh, hCmesh0, hmesh⟩ := mesh_interpolator (d := d) hd
  refine ⟨Cmesh, G, hCmesh0, hGnn, ?_⟩
  set K : ℝ := Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
      Cmesh * G with hKdef
  have hKnn : 0 ≤ K := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCmesh0) hGnn
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, K * r < ε * (3 : ℝ) ^ J := by
    have h3 : Filter.Tendsto (fun J : ℕ => (3 : ℝ) ^ J) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨J, hJ'⟩ := (h3.eventually_gt_atTop (K * r / ε)).exists
    exact ⟨J, by nlinarith [(div_lt_iff₀ hε).mp hJ']⟩
  obtain ⟨C, hC⟩ := hcell J fc hfc_smooth hfc_supp hfc_sub
  have hfinal : Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
      (Cmesh * (r / (3 : ℝ) ^ J) * G) < ε := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ J := by positivity
    rw [show Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
        (Cmesh * (r / (3 : ℝ) ^ J) * G) = K * r / (3 : ℝ) ^ J by rw [hKdef]; ring]
    rw [div_lt_iff₀ h3pos]
    linarith [hJ]
  -- per-`n` uniform coefficient bounds, from step (a)
  have hbdd : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H omega n x ∧ cutoffCoefficient M H omega n x ≤ Lam :=
    fun n => aux_prop_as_forms_hmesh_cutoff_bounds M H omega n z hr
  choose lam Lam hlam hbounds using hbdd
  have hbQ : ∀ n x, x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      lam n ≤ cutoffCoefficient M H omega n x ∧ cutoffCoefficient M H omega n x ≤ Lam n :=
    fun n x hx => hbounds n x (centeredCube_subset_closedCube z hr hx)
  -- the mesh interpolant, for each `n`, at the fixed depth `J`
  have hex : ∀ n : ℕ, ∃ w : H10Function (centeredCube z r hr : Set (SpatialCoordinates d)), _ :=
    fun n => hmesh z r hr J (cutoffCoefficient M H omega n) (lam n) (Lam n) (hlam n)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega n) (hbQ n)
      (H1Function.ofContDiff (centeredCube z r hr).isOpen
        (hfc_smooth.of_le (by simp)) hfc_supp)
      hfc_smooth hfc_supp hfc_sub
  choose wf hwcont hwcell hwsum hwerr using hex
  exact ⟨J, C, wf, hC, hwsum, hwerr, hfinal⟩

/-! ### Main assembly -/

/-- The typed gap: the `hmesh` input of the closed `SubdiffusiveProcess.Paper.prop_killed_inverse`, specialised
to `S := killedResponseSpace hP` and `a n := cutoffPositiveCoefficient M H omega n z hr`, exactly
as needed by `prop_as_forms`'s assembly ("prop_as_forms assembly recipe"). Standing inputs `Jc`, `Pc`, `Xc`, `Sf` are the same
`in_J`/`in_poincare`/`in_extension`/`SobolevFoundationalInput` objects `prop_as_forms`
already binds; `W`, `Cp`, `D` are the standing inputs `SubdiffusiveProcess.Paper.lem_as_coarse` now also requires; `hsmall` is the small-disorder
hypothesis, at the same threshold `prop_as_forms` introduces via `lem_as_coarse`'s own `delta0`.

The one open mathematical gap is isolated in `aux_prop_as_forms_hmesh_cell_bound`. -/
theorem aux_prop_as_forms_hmesh
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (hsmall : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ φ : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → (killedResponseSpace hP).space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm (killedResponseSpace hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε) := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [aux_prop_as_forms_hmesh_cell_bound hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI
    hsmall z r hr htri] with omega hcell
  rintro φ ⟨fc, hfc_smooth, hfc_supp, hfc_sub, hfc_rep⟩ ε hε
  obtain ⟨Cmesh, G, hCmesh0, hGnn, J, C, wf, hC, hwsum, hwerr, hfinal⟩ :=
    aux_prop_as_forms_hmesh_setup hd z r hr M H omega fc hfc_smooth hfc_supp hfc_sub ε hε hcell
  refine ⟨fun n => ⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩,
    C, ?_, ?_⟩
  · intro n
    have step1 := aux_prop_as_forms_hmesh_responseForm_eq hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
      (⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩ :
        (killedResponseSpace hP).space)
    obtain ⟨hcontn, hposn, ⟨Lamn, hLamn⟩, haen⟩ := aux_prop_as_forms_hmesh_cutoff M H omega n z hr
    have hcb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ‖cutoffCoefficient M H omega n x‖ ≤ Lamn := by
      filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (hposn x)]
      exact hLamn x (centeredCube_subset_closedCube z hr hx)
    have step2 := aux_prop_as_forms_hmesh_energy_bridge
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (cutoffCoefficient M H omega n) hcontn
      Lamn hcb haen (wf n)
    have hsum_eq : energy (cutoffCoefficient M H omega n)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (wf n).toH1Function =
        ∑ k : OddGridIndex d (triadicHalf J), cellDirichletInfimum (cutoffCoefficient M H omega n)
          (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
          ((H1Function.ofContDiff (centeredCube z r hr).isOpen
              (hfc_smooth.of_le (by simp)) hfc_supp).restrict
            (oddGridCell z r hr (triadicHalf J) k).isOpen
            (oddGridCell_subset z hr (triadicHalf J) k)) := hwsum n
    rw [step1, step2, hsum_eq]
    exact hC n
  · intro n
    have hQ := sobolevDataOfH1_fst_coeFn (wf n).toH1Function
    have hL2 := aux_prop_as_forms_hmesh_L2close z hr fc (wf n).toH1Function.toFun
      (Cmesh * (r / (3 : ℝ) ^ J) * G)
      (mul_nonneg (mul_nonneg hCmesh0 (by positivity)) hGnn)
      (hwerr n)
      (⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩ :
        (killedResponseSpace hP).space).val.1
      hQ φ hfc_rep
    exact hL2.trans hfinal.le



/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_dense_range_of_symm := SubdiffusiveProcess.LimitFormCore.dense_range_of_symm

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_dual_term_eq := SubdiffusiveProcess.LimitFormCore.dual_term_eq

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_limitFormEnergy_root := SubdiffusiveProcess.LimitFormCore.limitFormEnergy_root

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_form_root := SubdiffusiveProcess.LimitFormCore.form_root

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_domain_eq_range := SubdiffusiveProcess.LimitFormCore.domain_eq_range

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_core_dense := SubdiffusiveProcess.LimitFormCore.core_dense

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold := SubdiffusiveProcess.LimitFormCore.softThreshold

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_zero := SubdiffusiveProcess.LimitFormCore.softThreshold_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_mono_le := SubdiffusiveProcess.LimitFormCore.softThreshold_mono_le

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_isNormalContraction := SubdiffusiveProcess.LimitFormCore.softThreshold_isNormalContraction

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_sub_le := SubdiffusiveProcess.LimitFormCore.softThreshold_sub_le

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_ne_zero := SubdiffusiveProcess.LimitFormCore.softThreshold_ne_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_continuous_softThreshold := SubdiffusiveProcess.LimitFormCore.continuous_softThreshold

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_isFiniteMeasure_cube := SubdiffusiveProcess.LimitFormCore.isFiniteMeasure_cube

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_softThreshold_support := SubdiffusiveProcess.LimitFormCore.softThreshold_support

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_coreSubmodule := SubdiffusiveProcess.LimitFormCore.coreSubmodule

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_isCoreOn := SubdiffusiveProcess.LimitFormCore.isCoreOn

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_isRegular_of_isCoreOn := SubdiffusiveProcess.LimitFormCore.isRegular_of_isCoreOn

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_form_eq_zero_of_bilinear := SubdiffusiveProcess.LimitFormCore.form_eq_zero_of_bilinear

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_DirProp := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_DirProp

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_c2Norm_zero := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_c2Norm_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_holder_pt := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_holder_pt

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_closure_cube := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_closure_cube

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_dist_le_euclid := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_dist_le_euclid

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_killed_holder := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_killed_holder

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_Gf_continuous_hvc := _root_.SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_Gf_continuous_subseq := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_subseq

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_Gf_continuous_Ltwo := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_Ltwo

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_Gf_continuous := _root_.SubdiffusiveProcess.Paper.prop_conc_form_continuity

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_qlocal := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_data_qlocal

/-- Compatibility export of the extracted local form fact. -/
alias aux_prop_as_forms_isStronglyLocal := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_data_isStronglyLocal




/-- **Assembly of `IsRegular`/`IsStronglyLocal` for the limit Dirichlet form**: restated to take the principal's
use-site data directly (the already-computed `prop_killed_inverse` output for `G` -- root,
Mosco, form-density -- the `lem_as_regularity`-shaped uniform Hölder bound `hDreg` for the
`Gf`-continuity step, the coercivity constant, and the two new standing inputs `hcutoffs`/`hunif`)
rather than re-deriving them, since none of that surrounding machinery (`lem_as_coarse`,
`prop_as_response_bank`, the countable dense submodule, `hmesh`) is otherwise needed here: `G` and
its Mosco/root/density data are GIVEN, not re-derived, and `hresponse`-style Cauchy sequences are
not needed since convergence `hGtend` is already assumed. `IsRegular` is assembled via
`aux_prop_as_forms_isCoreOn` + `aux_prop_as_forms_isRegular_of_isCoreOn`; `IsStronglyLocal` via
`aux_prop_as_forms_qlocal` (using `hcutoffs`) + `aux_prop_as_forms_isStronglyLocal` (using `BD`,
`BDQ`). -/
alias aux_prop_as_forms_limit_dirichlet_form := _root_.SubdiffusiveProcess.Paper.prop_conc_form_data


section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_prop_as_forms_form_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (v : (killedResponseSpace hP).space) :
    responseForm (killedResponseSpace hP) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) v v =
      _root_.SubdiffusiveProcess.Paper.in_killed_energy M H HI omega N z hr v v := by
  unfold _root_.SubdiffusiveProcess.Paper.in_killed_energy
  rw [SubdiffusiveProcess.responseForm_apply, SubdiffusiveProcess.sobolevCoefficientForm_apply]
end


/-- Purely arithmetic helper: split a single `min 1 (min δ1 (min δ2 (min δ3 δ4)))` bound into
its four individual `min 1 δi` bounds. Pulled out to a standalone declaration so that
`prop_as_forms`'s own assembly does not have to elaborate the nested `min_le_left`/`min_le_right`
combinator terms itself (heartbeat budget). -/
theorem aux_prop_as_forms_delta4_le (x δ1 δ2 δ3 δ4 : ℝ)
    (h : x ≤ min 1 (min δ1 (min δ2 (min δ3 δ4)))) :
    x ≤ min 1 δ1 ∧ x ≤ min 1 δ2 ∧ x ≤ min 1 δ3 ∧ x ≤ min 1 δ4 := by
  have h1 : x ≤ 1 := h.trans (min_le_left _ _)
  have h2 := h.trans (min_le_right _ _)
  refine ⟨le_min h1 (h2.trans (min_le_left _ _)),
    le_min h1 (h2.trans ((min_le_right _ _).trans (min_le_left _ _))),
    le_min h1 (h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))),
    le_min h1 (h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))⟩


/-- Packages `aux_prop_as_forms_hmesh` across the countable index `I` used by `prop_as_forms`'s
own assembly, as its own top-level declaration (own heartbeat budget) so that `prop_as_forms`'s
proof only has to apply one already-elaborated term at the `hev3` step, instead of re-elaborating
the `ae_all_iff.mpr fun i => aux_prop_as_forms_hmesh ...` application (with its bigger,
standing-input-carrying signature) inline against the rest of that already-large assembly. -/
theorem aux_prop_as_forms_hev3
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (hsmall : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    {I : Type} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i : I,
      ∀ φ : DomainL2 (centeredCube (z i) (r i) (hr i)),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → (killedResponseSpace (hP i)).space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm (killedResponseSpace (hP i))
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n (z i) (hr i)) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε) :=
  ae_all_iff.mpr fun i : I =>
    aux_prop_as_forms_hmesh hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hsmall
      (z i) (r i) (hr i) (htriadic i) (hP i)


/-- The countable dense smooth ℚ-submodule on a single cube, independent of the countable index
`I` and the model `M`/`Rm`/`H`/`HI` -- pulled out of `prop_as_forms`'s own assembly (heartbeat
budget) since it does not depend on any of that per-model data. -/
theorem aux_prop_as_forms_hDex {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ D : Submodule ℚ (DomainL2 (centeredCube z r hr)),
      (D : Set (DomainL2 (centeredCube z r hr))).Countable ∧
      Dense (D : Set (DomainL2 (centeredCube z r hr))) ∧
      ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc := by
  have hopen := (centeredCube z r hr).isOpen
  have hvol : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  exact aux_prop_as_forms_exists_smooth_dense_submodule z r hr
    (aux_prop_as_forms_dense_smooth_tsupport_subset hopen hvol
      (fun {_g} hg hc {_ε} hε => aux_prop_as_forms_exists_contDiff_tsupport_subset_eLpNorm_sub_le
        hopen hvol hg hc hε))
    (aux_prop_as_forms_countable_dense_submodule_le z r hr)


/-- A single a.e.-bounded smooth representative gives an a.e. sup bound for the underlying `L²`
class -- the per-element content of `prop_as_forms`'s `hKDex` step, pulled out of its own
assembly (heartbeat budget) since it is generic in the ambient cube `Ω` and does not depend on
the countable index `I` or the sigma-type packaging. -/
theorem aux_prop_as_forms_hKDex {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (f : DomainL2 Ω) (fc : SpatialCoordinates d → ℝ)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) fc) (hfc : HasCompactSupport fc)
    (hae : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fc) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        |(f : SpatialCoordinates d → ℝ) x| ≤ K := by
  obtain ⟨C, hC⟩ := hfs.continuous.bounded_above_of_compact_support hfc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hae] with x hx
  rw [hx]
  exact (by simpa [Real.norm_eq_abs] using hC x : |fc x| ≤ C).trans (le_max_left _ _)

-- Smooth cutoff construction needs `import Mathlib` or Mathlib.Geometry.Manifold.PartitionOfUnity.
-- Smooth density construction needs `import Mathlib` or Mathlib.Geometry.Manifold.PartitionOfUnity.



def aux_prop_as_forms_HCUT_prop {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
    ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (killedResponseSpace hP).space)
      (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n : ℕ,
        ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        ((chi n).val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
        (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          0 ≤ chic n x ∧ chic n x ≤ 1) ∧
        (∀ x ∈ V, chic n x = 1) ∧
        (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
        responseForm (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (s (t n)) z hr) (chi n) (chi n) ≤ B ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
          0 < rr → rr ≤ 1 →
          ((volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (s (t n)) z hr).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
            (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ ((d : ℝ) - 1 / 2)))

/-- Opaque `Prop` wrapper for the per-model `HUNIF` content, same heartbeat-budget rationale as
`aux_prop_as_forms_HCUT_prop` above. -/
def aux_prop_as_forms_HUNIF_prop {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H) :
    Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (GNi : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNi n f =
        (_root_.SubdiffusiveProcess.Paper.in_killed_inverse M H HI omega (s (t n)) z hr hP f :
          SobolevData (centeredCube z r hr)).1) →
      Tendsto GNi atTop (𝓝 G) →
    ∀ (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
      (_hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u),
    ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
      tsupport f0 ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g ∧
        ∀ x, |g x - f0 x| < ε

/-- The displayed form-convergence statement is proved below with its
explicit representation and energy hypotheses. -/
theorem prop_as_forms
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H)
        (hdelta : M.delta ≤ min 1 delta0)
        (HCUT : aux_prop_as_forms_HCUT_prop M H)
        (HUNIF : aux_prop_as_forms_HUNIF_prop M H HI)
        (zroot : SpatialCoordinates d) (rroot : ℝ) (hrroot : 0 < rroot)
        (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i)
        (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
        (hrat : ∀ (i : I) (k : Fin d), ∃ q : ℚ, z i k = (q : ℝ))
        (hroot : ∀ i, (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ⊆
          (centeredCube zroot rroot hrroot : Set (SpatialCoordinates d)))
        (hP : ∀ i, ∃ K : ℝ≥0,
          ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
            ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
              K * ‖subspaceGradient
                (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖)
        (GN : (i : I) → BilateralField d → ℕ →
          (DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))))
        (hGN : ∀ (i : I) (omega : BilateralField d) (N : ℕ)
            (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
          GN i omega N f =
            (_root_.SubdiffusiveProcess.Paper.in_killed_inverse M H HI omega N (z i) (hr i) (hP i) f :
              SobolevData (centeredCube (z i) (r i) (hr i))).1) ,
    let EN : (i : I) → BilateralField d → ℕ →
        DomainL2 (centeredCube (z i) (r i) (hr i)) → EReal :=
      fun i omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)) //
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 = u},
          ((_root_.SubdiffusiveProcess.Paper.in_killed_energy M H HI omega N (z i) (hr i)
            (v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
            (v : killedSobolevGraph (centeredCube (z i) (r i) (hr i))) : ℝ) : EReal);
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i : I,
      ∃! G : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
        (Tendsto (GN i omega) atTop (𝓝 G) ∧ IsCompactOperator G ∧
          (∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
            inner ℝ (G x) y = inner ℝ x (G y)) ∧
          (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
            0 ≤ inner ℝ x (G x)) ∧
          Function.Injective G) ∧
        (∃ F : _root_.SubdiffusiveProcess.DirichletForm
            (volume.restrict
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            F.toClosedForm.energy u = limitFormEnergy G u) ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
        (∀ (uN : ℕ → DomainL2 (centeredCube (z i) (r i) (hr i)))
            (u : DomainL2 (centeredCube (z i) (r i) (hr i))),
          (∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
            Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
          limitFormEnergy G u ≤
            liminf (fun N => EN i omega N (uN N)) atTop) ∧
        (∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          ∃ w : ℕ → DomainL2 (centeredCube (z i) (r i) (hr i)),
            Tendsto w atTop (𝓝 u) ∧
              limsup (fun N => EN i omega N (w N)) atTop ≤
                limitFormEnergy G u) := by
  obtain ⟨δ1, hδ1, hcoarse⟩ := lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp 1 (3 / 4)
    ⟨one_pos, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  obtain ⟨Cresp, Bset, δ2, Cgeom, _hCresp, _hBne, _h128, _hB1, hδ2, _hδ21, _hCgeom, hbank⟩ :=
    prop_as_response_bank d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨δreg, hδreg, hReg⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp (1 / 2) (3 / 4)
    ((d : ℝ) - 3 / 4) ((d : ℝ) - 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨δ4, hδ4, hδ4eq⟩ :
      ∃ δ4 : ℝ, 0 < δ4 ∧ δ4 = aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp :=
    ⟨_, aux_prop_as_forms_hmesh_delta0_pos hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp, rfl⟩
  refine ⟨min δ1 (min δ2 (min δreg δ4)), lt_min hδ1 (lt_min hδ2 (lt_min hδreg hδ4)), ?_⟩
  intro M Rm Sreg It H HI hdelta HCUT HUNIF zroot rroot hrroot I _ z r hr htriadic hrat hroot hP
    GN hGN EN
  obtain ⟨hd1, hd2, hd3, hd4⟩ := aux_prop_as_forms_delta4_le M.delta δ1 δ2 δreg δ4 hdelta
  have hd4' : M.delta ≤ min 1 (aux_prop_as_forms_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp) := by
    rw [← hδ4eq]; exact hd4
  -- countable dense smooth ℚ-submodules on every cube
  choose Dq hDc hDd hDs using fun i : I => aux_prop_as_forms_hDex (z i) (r i) (hr i)
  have : ∀ i : I, Countable (Dq i) := fun i => (hDc i).to_subtype
  -- bounded smooth sources for the response bank
  choose KD hKD0 hKD using fun p : (Σ i : I, Dq i) =>
    aux_prop_as_forms_hKDex (p.2 : Dq p.1).val (hDs p.1 p.2).choose
      (hDs p.1 p.2).choose_spec.1 (hDs p.1 p.2).choose_spec.2.1
      (hDs p.1 p.2).choose_spec.2.2.2
  have hbankM := (hbank M Sreg It hd2).2 H HI (Σ i : I, Dq i)
    (fun p => z p.1) (fun p => r p.1) (fun p => hr p.1) (fun p => htriadic p.1)
    (fun _ _ => (0 : ℝ)) (fun _ => contDiff_const)
    (fun p => (p.2 : Dq p.1).val) (fun _ => 0) KD (fun _ => 0) hKD0 (fun _ => le_rfl) hKD
    (fun p => by
      filter_upwards [Lp.coeFn_zero ℝ 2
        (volume.restrict (centeredCube (z p.1) (r p.1) (hr p.1) : Set (SpatialCoordinates d)))]
        with x hx
      rw [abs_nonpos_iff]
      simpa using hx)
    (fun p => by
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2
        (volume.restrict (centeredCube (z p.1) (r p.1) (hr p.1) : Set (SpatialCoordinates d))))]
      simp)
    (fun _ => 0)
  obtain ⟨Rlim, -, -, -, -, hae, -⟩ := hbankM
  have hev1 := ae_all_iff.mpr fun i : I =>
    hcoarse M Rm Sreg It H HI hd1 (z i) (r i) (hr i) (htriadic i)
  have hev3 := aux_prop_as_forms_hev3 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hd4' z r hr
    htriadic hP
  have hevReg := ae_all_iff.mpr fun i : I =>
    hReg M Rm Sreg It H HI hd3 (z i) (r i) (hr i)
  obtain ⟨tc, htc, hcutAE⟩ := HCUT id strictMono_id
  obtain ⟨tu, htu, hunifAE⟩ := HUNIF id strictMono_id
  filter_upwards [hev1, hae, hev3, hevReg, hcutAE, hunifAE] with omega h1 h2 h3 h5 h6 h7
  intro i
  obtain ⟨K, hK, hKall⟩ := h1 i
  have hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (z i) (r i) (hr i))),
      cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
          (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
        K * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N (z i) (hr i))
          (v : SobolevData (centeredCube (z i) (r i) (hr i)))
          (v : SobolevData (centeredCube (z i) (r i) (hr i))) := by
    have h := (hKall true).2.1
    simpa using h
  have hGNi : ∀ (n : ℕ) (f : DomainL2 (centeredCube (z i) (r i) (hr i))), GN i omega n f =
      (responseSolution (killedResponseSpace (hP i))
        (cutoffPositiveCoefficient M H omega n (z i) (hr i))
        ((sobolevVolumeLoad f).comp (killedResponseSpace (hP i)).space.subtypeL)).val.1 := by
    intro n f
    rw [hGN]
    rfl
  have hresp : ∀ f : Dq i, CauchySeq (fun n => inner ℝ f.val (GN i omega n f.val)) := by
    intro f
    exact aux_prop_as_forms_hresponse_of_tendsto (killedResponseSpace (hP i))
      (fun n => cutoffPositiveCoefficient M H omega n (z i) (hr i)) (GN i omega) hGNi f.val _
      (h2 ⟨i, f⟩ true 1)
  have hCoerv := aux_prop_as_forms_hCoercive hd Sf (z i) (r i) (hr i) (hP i) _ K hc
  have hpki := prop_killed_inverse d hd (z i) (r i) (hr i) (killedResponseSpace (hP i)) rfl
    (fun n => cutoffPositiveCoefficient M H omega n (z i) (hr i))
    (fun n T hT u => hcontract (z i) (r i) (hr i) _ rfl _ T hT u)
    (GN i omega) hGNi Interp
    (volume.real (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) * K)
    (mul_pos (centeredCube_volume_pos _ _) hK)
    hCoerv
    (Dq i) (hDc i) (hDd i) (hDs i) hresp
    (fun n u => sInf {e : EReal | ∃ w : (killedResponseSpace (hP i)).space, w.val.1 = u ∧
      e = (responseForm (killedResponseSpace (hP i))
        (cutoffPositiveCoefficient M H omega n (z i) (hr i)) w w : EReal)})
    (fun n u => rfl) (h3 i)
  obtain ⟨G, ⟨hG1, hroot, hform, ⟨hGlow, hGrec⟩, hdense⟩, _huniq⟩ := hpki
  obtain ⟨Rroot, hRsymm, hRpos, hRcomp, hRdom⟩ := hroot
  obtain ⟨EForm, hEForm, hHNC⟩ := hform
  obtain ⟨Kreg, hKregPos, hDirNeu⟩ := h5 i
  have hDreg : ∀ N : ℕ, aux_prop_as_forms_DirProp (z i) (r i) (hr i)
      (cutoffPositiveCoefficient M H omega N (z i) (hr i)) Kreg :=
    fun N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hbeq hsolve =>
      ((hDirNeu N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hbeq hsolve).2
  have hcutInst := h6 (z i) (r i) (hr i) (htriadic i) (hP i)
  have hunifInst := h7 (z i) (r i) (hr i) (htriadic i) (hP i)
    (fun n => GN i omega (tu n)) G (fun n f => hGNi (tu n) f)
    (hG1.1.comp htu.tendsto_atTop) EForm hEForm
  have hRegLoc := aux_prop_as_forms_limit_dirichlet_form d hd (z i) (r i) (hr i) (hP i)
    (fun n => cutoffPositiveCoefficient M H omega (tc n) (z i) (hr i))
    (fun n => GN i omega (tc n)) (fun n f => hGNi (tc n) f) G Rroot
    (hG1.1.comp htc.tendsto_atTop) hG1.2.2.1 hG1.2.2.2.2 hRsymm hRcomp hRdom EForm hEForm hHNC
    (aux_prop_as_forms_subseq_lower (killedResponseSpace (hP i))
      (fun n => cutoffPositiveCoefficient M H omega n (z i) (hr i))
      (GN i omega) hGNi G hG1.1 tc htc)
    (aux_prop_as_forms_recovery_subseq (fun v : (killedResponseSpace (hP i)).space => v.val.1)
      (fun n v => responseForm (killedResponseSpace (hP i))
        (cutoffPositiveCoefficient M H omega n (z i) (hr i)) v v)
      (limitFormEnergy G) (limitFormDomain G) hGrec tc htc) hdense
    (volume.real (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) * K)
    (mul_nonneg (centeredCube_volume_pos _ _).le hK.le) (fun n => hCoerv (tc n))
    Interp Kreg hKregPos.le (fun n => hDreg (tc n))
    (BD (z i) (r i) (hr i) EForm) (BDQ (z i) (r i) (hr i) EForm) hcutInst hunifInst
  refine ⟨G, ⟨hG1, hRegLoc, ?_, ?_⟩, ?_⟩
  · intro uN u hw
    refine (hGlow uN u hw).trans (le_of_eq ?_)
    congr 1
    funext N
    exact (aux_prop_as_forms_EN_eq_sInf M H HI omega N (z i) (r i) (hr i) (hP i) (uN N)).symm
  · intro u
    obtain ⟨w, hw, hlim⟩ := aux_prop_as_forms_recovery_glue
      (fun v : (killedResponseSpace (hP i)).space => v.val.1)
      (fun n v => responseForm (killedResponseSpace (hP i))
        (cutoffPositiveCoefficient M H omega n (z i) (hr i)) v v)
      (limitFormEnergy G) (fun u hu => hGrec u hu) u
    refine ⟨w, hw, le_trans (le_of_eq ?_) hlim⟩
    congr 1
  · intro G' hG'
    exact tendsto_nhds_unique hG'.1.1 hG1.1


end SubdiffusiveProcess.Paper
