module

public import SubdiffusiveProcess.Paper.prop_conc_form_data
public import SubdiffusiveProcess.Compactness.OperatorLimits
public import SubdiffusiveProcess.Sobolev.ConditionalResponses
public import SubdiffusiveProcess.Paper.prop_as_forms
public import SubdiffusiveProcess.Paper.thm_c1
public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.prop_as_response_bank
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- Extra imports for the jl_block (Measurable G / joint law) and the Fatou seminorm estimate.


public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Sobolev.ResponsePositivity
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Main.ContinuousPositiveLog
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic



public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.prop_killed_inverse
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

open Filter MeasureTheory Set Topology TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
open scoped BoundedContinuousFunction

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ### Local recovery and mesh-energy helpers

These helpers are local copies of the form-convergence construction, renamed
with the `aux_limiting_local_energy_` prefix. Their explicit recovery,
coercivity and mesh hypotheses keep the two assemblies independently usable. -/

section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_limiting_local_energy_recovery_glue {E V : Type*} [NormedAddCommGroup E]
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
theorem aux_limiting_local_energy_EN_eq_sInf {d : ℕ}
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
    rw [responseForm_apply, sobolevCoefficientForm_apply]
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
    let w : ↥(killedResponseSpace hP).space :=
      ⟨v.val.val, by simpa only [killedResponseSpace] using! v.val.property⟩
    simpa only [sobolevCoefficientForm_apply, w] using!
      responseForm_apply (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) w w
end



section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_limiting_local_energy_hCoercive {d : ℕ} (hd : 2 ≤ d)
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
      rw [responseForm_apply, sobolevCoefficientForm_apply]
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
theorem aux_limiting_local_energy_hresponse_of_tendsto {d : ℕ}
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
theorem aux_limiting_local_energy_countable_dense_submodule_le {d : ℕ}
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
theorem aux_limiting_local_energy_exists_smooth_dense_submodule {d : ℕ}
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
theorem aux_limiting_local_energy_existsUnique_of_tendsto {X : Type*} [TopologicalSpace X]
    [T2Space X] (T : ℕ → X) (P : X → Prop) (G : X) (hP : P G)
    (hPT : ∀ G' : X, P G' → Tendsto T atTop (𝓝 G')) :
    ∃! G' : X, P G' := by
  refine ⟨G, hP, ?_⟩
  intro G' hG'
  exact tendsto_nhds_unique (hPT G' hG') (hPT G hP)
end


-- Smooth cutoff/approximation tools use `import Mathlib` or Mathlib.Geometry.Manifold.PartitionOfUnity.
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold
theorem aux_limiting_local_energy_norm_sub_mul_le_norm (c v : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
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

theorem aux_limiting_local_energy_exists_contDiff_tsupport_subset_eLpNorm_sub_le {d : ℕ}
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
            refine eLpNorm_mono_ae (hgL2.sub hφL2).aestronglyMeasurable ?_
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
              exact aux_limiting_local_energy_norm_sub_mul_le_norm (η x) (g x) (hη_range x).1 (hη_range x).2
      _ ≤ ENNReal.ofReal ε := hindicator
end


-- Smooth cutoff/approximation tools use `import Mathlib` or Mathlib.Geometry.Manifold.PartitionOfUnity.
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold
theorem aux_limiting_local_energy_dense_smooth_tsupport_subset {d : ℕ}
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



/-! ### limiting_local_energy helpers  -/

section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_limiting_local_energy_mosco_unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (En : ℕ → E → EReal) (F1 F2 : E → EReal)
    (hlow1 : ∀ (uN : ℕ → E) (u : E),
      (∀ f : E, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
      F1 u ≤ liminf (fun N => En N (uN N)) atTop)
    (hrec1 : ∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => En N (w N)) atTop ≤ F1 u)
    (hlow2 : ∀ (uN : ℕ → E) (u : E),
      (∀ f : E, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
      F2 u ≤ liminf (fun N => En N (uN N)) atTop)
    (hrec2 : ∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => En N (w N)) atTop ≤ F2 u) :
    F1 = F2 := by
  have key : ∀ (A B : E → EReal),
      (∀ (uN : ℕ → E) (u : E),
        (∀ f : E, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
        A u ≤ liminf (fun N => En N (uN N)) atTop) →
      (∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
        limsup (fun N => En N (w N)) atTop ≤ B u) →
      ∀ u, A u ≤ B u := by
    intro A B hlow hrec u
    obtain ⟨w, hw, hlim⟩ := hrec u
    have hcont : ∀ f : E, Tendsto (fun N => inner ℝ f (w N)) atTop (𝓝 (inner ℝ f u)) :=
      fun f => tendsto_const_nhds.inner hw
    calc A u ≤ liminf (fun N => En N (w N)) atTop := hlow w u hcont
      _ ≤ limsup (fun N => En N (w N)) atTop := Filter.liminf_le_limsup
      _ ≤ B u := hlim
  funext u
  exact le_antisymm (key F1 F2 hlow1 hrec2 u) (key F2 F1 hlow2 hrec1 u)
end

section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_limiting_local_energy_lower_subseq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (En : ℕ → E → EReal) (F : E → EReal)
    (hlow : ∀ (uN : ℕ → E) (u : E), (∀ f : E, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
      F u ≤ liminf (fun N => En N (uN N)) atTop)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∀ (vN : ℕ → E) (u : E), (∀ f : E, Tendsto (fun N => inner ℝ f (vN N)) atTop (𝓝 (inner ℝ f u))) →
      F u ≤ liminf (fun N => En (phi N) (vN N)) atTop := by
  intro vN u hvN
  classical
  set uN : ℕ → E := fun n => if h : ∃ k, phi k = n then vN (Classical.choose h) else u with huN_def
  have huN_phi : ∀ k, uN (phi k) = vN k := by
    intro k
    have hex : ∃ k', phi k' = phi k := ⟨k, rfl⟩
    have hc : Classical.choose hex = k := hphi.injective (Classical.choose_spec hex)
    simp only [uN]
    rw [dite_eq_left hex, hc]
  have hweak : ∀ f : E, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u)) := by
    intro f
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (hvN f) ε hε
    refine ⟨phi K, fun N hN => ?_⟩
    by_cases hex : ∃ k, phi k = N
    · obtain ⟨k, hk⟩ := hex
      have hex' : ∃ k', phi k' = N := ⟨k, hk⟩
      have hkN : K ≤ k := hphi.le_iff_le.mp (by rw [hk]; exact hN)
      have hck : Classical.choose hex' = k :=
        hphi.injective (by rw [Classical.choose_spec hex', hk])
      have hval : uN N = vN k := by
        simp only [uN]
        rw [dite_eq_left hex', hck]
      rw [hval]
      exact hK k hkN
    · have hval : uN N = u := by
        simp only [uN]
        rw [dite_eq_right hex]
      rw [hval, dist_self]
      exact hε
  have hlim : liminf (fun n => En n (uN n)) atTop ≤
      liminf (fun k => En (phi k) (uN (phi k))) atTop := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro m
    apply le_iSup_of_le m
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    exact le_trans (iInf_le (fun j => ⨅ (_ : j ≥ m), En j (uN j)) (phi i))
      (iInf_le (fun _ : phi i ≥ m => En (phi i) (uN (phi i))) (le_trans hi (hphi.id_le i)))
  calc F u ≤ liminf (fun n => En n (uN n)) atTop := hlow uN u hweak
    _ ≤ liminf (fun k => En (phi k) (uN (phi k))) atTop := hlim
    _ = liminf (fun k => En (phi k) (vN k)) atTop := by
        have hfun : (fun k => En (phi k) (uN (phi k))) = fun k => En (phi k) (vN k) := by
          funext k
          rw [huN_phi k]
        rw [hfun]
end

section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_limiting_local_energy_recovery_subseq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (En : ℕ → E → EReal) (F : E → EReal)
    (hrec : ∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => En N (w N)) atTop ≤ F u)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∀ u : E, ∃ w : ℕ → E, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => En (phi N) (w N)) atTop ≤ F u := by
  intro u
  obtain ⟨w, hw, hlim⟩ := hrec u
  refine ⟨fun N => w (phi N), hw.comp hphi.tendsto_atTop, ?_⟩
  refine le_trans ?_ hlim
  rw [Filter.limsup_eq_iInf_iSup_of_nat, Filter.limsup_eq_iInf_iSup_of_nat]
  apply iInf_mono
  intro n
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact le_iSup_of_le (phi k) (le_iSup_of_le (le_trans hk (hphi.id_le k)) le_rfl)
end


section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal
theorem aux_limiting_local_energy_cubeFractionalSqNorm_eq {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalSqNorm hd z r hr s v =
      ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal) ^ 2 +
        ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [Fin.sum_univ_one]

theorem aux_limiting_local_energy_sq_bound {s c n K a V : ℝ} (hV : 0 < V) (hs : s ^ 2 ≤ K * a)
    (hn : n ^ 2 / V ≤ K * a) :
    (s + c * (n / Real.sqrt V)) ^ 2 ≤ (2 * K + 2 * K * c ^ 2) * a := by
  have h1 : (s + c * (n / Real.sqrt V)) ^ 2 ≤ 2 * s ^ 2 + 2 * (c * (n / Real.sqrt V)) ^ 2 := by
    nlinarith [sq_nonneg (s - c * (n / Real.sqrt V))]
  have h3 : (c * (n / Real.sqrt V)) ^ 2 ≤ c ^ 2 * (K * a) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hV.le]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg c)
  nlinarith [h1, h3, hs]

theorem aux_limiting_local_energy_norm_singleton {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (u : DomainL2 (centeredCube z r hr))
    (h : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) < ⊤) :
    cubeFractionalL2Norm hd z r hr s
        (⟨fun _ : Fin 1 => u, h⟩ : CubeFractionalL2 (k := 1) hd z r hr s) =
      (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u)).toReal +
        r ^ (-(s : ℝ)) *
          (‖u‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  have hval : (⟨fun _ : Fin 1 => u, h⟩ : CubeFractionalL2 (k := 1) hd z r hr s).val
      = (fun _ : Fin 1 => u) := rfl
  have hsqrt : Real.sqrt (∑ i : Fin 1, ‖(fun _ : Fin 1 => u) i‖ ^ 2) = ‖u‖ := by
    rw [Fin.sum_univ_one]
    exact Real.sqrt_sq (norm_nonneg u)
  unfold cubeFractionalL2Norm
  rw [hval, hsqrt]

theorem aux_limiting_local_energy_coercive_limit {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (K : ℝ) (hK : 0 < K)
    (E : DomainL2 (centeredCube z r hr) → EReal) (hE0 : ∀ u, 0 ≤ E u)
    (hrec : ∀ u : DomainL2 (centeredCube z r hr), E u < ⊤ →
      ∃ w : ℕ → DomainL2 (centeredCube z r hr), ∃ e : ℕ → ℝ,
        Tendsto w atTop (𝓝 u) ∧ Tendsto (fun n => ((e n : ℝ) : EReal)) atTop (𝓝 (E u)) ∧
        (∀ n, cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
          (fun _ : Fin 1 => w n) < ⊤) ∧
        ∀ n, cubeFractionalSqNorm hd z r hr threeQuarterOrder (w n) ≤ K * e n)
    (hfatou : ∀ (w : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr)),
      Tendsto w atTop (𝓝 u) →
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u) ≤
        liminf (fun n => cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
          (fun _ : Fin 1 => w n)) atTop) :
    ∃ Ccoer : ℝ, K ≤ Ccoer ∧ ∀ u : DomainL2 (centeredCube z r hr), E u ≠ ⊤ →
      ∃ v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
        v.val 0 = u ∧
        (cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 ≤ Ccoer * (E u).toReal := by
  refine ⟨2 * K + 2 * K * (r ^ (-(threeQuarterOrder : ℝ))) ^ 2, ?_, ?_⟩
  · have h1 : 0 ≤ 2 * K * (r ^ (-(threeQuarterOrder : ℝ))) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · intro u hu
    have hlt : E u < ⊤ := lt_top_iff_ne_top.mpr hu
    obtain ⟨w, e, hw_tend, he_tend, hsem_fin, hsq⟩ := hrec u hlt
    have hzero_ne_bot : (0 : EReal) ≠ ⊥ := by
      rw [← EReal.coe_zero]
      exact EReal.coe_ne_bot 0
    have hbot : E u ≠ ⊥ := by
      intro h
      exact hzero_ne_bot (le_antisymm (h ▸ hE0 u) bot_le)
    have hcoe : ((E u).toReal : EReal) = E u := EReal.coe_toReal hu hbot
    have he_tend' : Tendsto e atTop (𝓝 (E u).toReal) := by
      rw [← hcoe] at he_tend
      exact EReal.tendsto_coe.mp he_tend
    have hvol_pos : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      SubdiffusiveProcess.centeredCube_volume_pos z hr
    have hsq' : ∀ n : ℕ,
        ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) ^ 2 +
          ‖w n‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤ K * e n := by
      intro n
      have h := hsq n
      rwa [aux_limiting_local_energy_cubeFractionalSqNorm_eq hd z r hr threeQuarterOrder (w n)] at h
    have hL2n : ∀ n : ℕ,
        ‖w n‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤ K * e n := by
      intro n
      have h := hsq' n
      have hnn : 0 ≤ ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) ^ 2 :=
        sq_nonneg _
      linarith
    have hsem_le : ∀ n : ℕ,
        cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n) ≤
          ENNReal.ofReal (Real.sqrt (K * e n)) := by
      intro n
      have h := hsq' n
      have hsemnn : 0 ≤ ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) :=
        ENNReal.toReal_nonneg
      have hdiv : 0 ≤ ‖w n‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        div_nonneg (sq_nonneg _) hvol_pos.le
      have hsq_le : ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) ^ 2 ≤ K * e n := by
        linarith
      have hKe : 0 ≤ K * e n := le_trans (sq_nonneg _) hsq_le
      have hroot : ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) ≤ Real.sqrt (K * e n) :=
        (Real.le_sqrt hsemnn hKe).mpr hsq_le
      calc cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)
          = ENNReal.ofReal ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => w n)).toReal) :=
            (ENNReal.ofReal_toReal (ne_of_lt (hsem_fin n))).symm
        _ ≤ ENNReal.ofReal (Real.sqrt (K * e n)) := ENNReal.ofReal_le_ofReal hroot
    have hlim : cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u) ≤
        ENNReal.ofReal (Real.sqrt (K * (E u).toReal)) := by
      have hfat := hfatou w u hw_tend
      have hg_tend : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K * e n))) atTop
          (𝓝 (ENNReal.ofReal (Real.sqrt (K * (E u).toReal)))) := by
        have h1 : Tendsto (fun n : ℕ => K * e n) atTop (𝓝 (K * (E u).toReal)) :=
          he_tend'.const_mul K
        have h2 : Tendsto (fun n : ℕ => Real.sqrt (K * e n)) atTop
            (𝓝 (Real.sqrt (K * (E u).toReal))) := (Real.continuous_sqrt.tendsto _).comp h1
        exact (ENNReal.continuous_ofReal.tendsto _).comp h2
      calc cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)
          ≤ liminf (fun n : ℕ => cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
              (fun _ : Fin 1 => w n)) atTop := hfat
        _ ≤ liminf (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K * e n))) atTop := by
            refine liminf_le_liminf (Eventually.of_forall hsem_le) ?_ ?_
            · exact ⟨⊥, Eventually.of_forall (fun n => bot_le)⟩
            · exact ⟨⊤, fun a _ => le_top⟩
        _ = ENNReal.ofReal (Real.sqrt (K * (E u).toReal)) := hg_tend.liminf_eq
    have hsem_u_le : ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)).toReal) ≤
        Real.sqrt (K * (E u).toReal) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlim
      rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    have hsem_sq : ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)).toReal) ^ 2 ≤
        K * (E u).toReal := by
      have hKa : 0 ≤ K * (E u).toReal := mul_nonneg hK.le (EReal.toReal_nonneg (hE0 u))
      have hsemnn : 0 ≤ ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)).toReal) :=
        ENNReal.toReal_nonneg
      have hsq2 : ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)).toReal) ^ 2 ≤
          (Real.sqrt (K * (E u).toReal)) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsem_u_le)
          (add_nonneg hsemnn (Real.sqrt_nonneg (K * (E u).toReal)))]
      calc ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u)).toReal) ^ 2
          ≤ (Real.sqrt (K * (E u).toReal)) ^ 2 := hsq2
        _ = K * (E u).toReal := Real.sq_sqrt hKa
    have hL2_tend : Tendsto (fun n : ℕ => ‖w n‖ ^ 2 /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) atTop
        (𝓝 (‖u‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) :=
      (hw_tend.norm.pow 2).div_const _
    have hL2_bound : ‖u‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        K * (E u).toReal :=
      le_of_tendsto_of_tendsto hL2_tend (he_tend'.const_mul K) (Eventually.of_forall hL2n)
    have hfin : cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => u) < ⊤ :=
      lt_of_le_of_lt hlim (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    refine ⟨⟨fun _ : Fin 1 => u, hfin⟩, rfl, ?_⟩
    rw [aux_limiting_local_energy_norm_singleton hd z r hr threeQuarterOrder u hfin]
    exact aux_limiting_local_energy_sq_bound hvol_pos hsem_sq hL2_bound
end

-- Fatou lower semicontinuity of the Gagliardo seminorm.

-- (helpers renamed aux_ae_prod_fst/snd -> aux_limiting_local_energy_ae_prod_fst/snd,
-- aux_fatou_double -> aux_limiting_local_energy_fatou_double per the integrator's naming rule).
section
open Filter Set
open scoped ENNReal NNReal BigOperators Topology
theorem aux_limiting_local_energy_ae_prod_fst {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂(μ.prod μ), p z.1 := by
  rw [ae_iff] at h ⊢
  have hset : {z : α × α | ¬ p z.1} = {x : α | ¬ p x} ×ˢ (Set.univ : Set α) := by
    ext z
    simp
  rw [hset, Measure.prod_prod, h, zero_mul]

theorem aux_limiting_local_energy_ae_prod_snd {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂(μ.prod μ), p z.2 := by
  rw [ae_iff] at h ⊢
  have hset : {z : α × α | ¬ p z.2} = (Set.univ : Set α) ×ˢ {x : α | ¬ p x} := by
    ext z
    simp
  rw [hset, Measure.prod_prod, h, mul_zero]

theorem aux_limiting_local_energy_mul_liminf_le (A : ℝ≥0∞) (v : ℕ → ℝ≥0∞) :
    A * liminf v atTop ≤ liminf (fun n => A * v n) atTop := by
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun s => iSup_le fun hs => ?_
  refine le_iSup_of_le s (le_iSup_of_le hs ?_)
  refine le_iInf fun a => le_iInf fun ha => ?_
  exact mul_le_mul' le_rfl (le_trans (iInf_le _ a) (iInf_le _ ha))

theorem aux_limiting_local_energy_le_liminf_div_const {b : ℕ → ℝ≥0∞} {B D : ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 B)) : B / D ≤ liminf (fun n => b n / D) atTop := by
  have hcongr : liminf (fun n => b n / D) atTop = liminf (fun n => D⁻¹ * b n) atTop :=
    liminf_congr (Filter.Eventually.of_forall fun n => ENNReal.div_eq_inv_mul)
  rw [ENNReal.div_eq_inv_mul, hcongr]
  calc D⁻¹ * B = D⁻¹ * liminf b atTop := by rw [hb.liminf_eq]
    _ ≤ liminf (fun n => D⁻¹ * b n) atTop := aux_limiting_local_energy_mul_liminf_le D⁻¹ b

theorem aux_limiting_local_energy_liminf_rpow_half {u : ℕ → ℝ≥0∞} :
    (liminf u atTop) ^ (1 / 2 : ℝ) ≤ liminf (fun n => (u n) ^ (1 / 2 : ℝ)) atTop := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
    intro x
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  rw [le_liminf_iff]
  intro y hy
  have hy2 : y ^ (2 : ℝ) < liminf u atTop := by
    rw [← hsq (liminf u atTop)]
    exact ENNReal.rpow_lt_rpow hy (by norm_num)
  obtain ⟨e, hye, hel⟩ := exists_between hy2
  have hiff : (e ≤ liminf u atTop ↔ ∀ z < e, ∀ᶠ n in atTop, z < u n) := le_liminf_iff
  have hget : ∀ᶠ n in atTop, y ^ (2 : ℝ) < u n := hiff.mp (le_of_lt hel) (y ^ (2 : ℝ)) hye
  filter_upwards [hget] with n hn
  have h := ENNReal.rpow_lt_rpow hn (show (0 : ℝ) < 1 / 2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h

theorem aux_limiting_local_energy_fatou_double {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {g : ℕ → α → ℝ} {g₀ : α → ℝ} {D : α × α → ℝ≥0∞} {A : ℝ≥0∞}
    (hg : ∀ n, AEMeasurable (g n) μ) (_hg₀ : AEMeasurable g₀ μ)
    (hD : AEMeasurable D (μ.prod μ))
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    A * (∫⁻ p, ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ∂(μ.prod μ)) ≤
      liminf (fun n => A * (∫⁻ p,
        ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ))) atTop := by
  have hmeas : ∀ n, AEMeasurable (fun p : α × α =>
      ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p) (μ.prod μ) := by
    intro n
    have h1 : AEMeasurable (g n) μ := hg n
    measurability
  have hpoint : ∀ᵐ p ∂(μ.prod μ),
      ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ≤
        liminf (fun n => ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p) atTop := by
    have h1 : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun n => g n p.1) atTop (𝓝 (g₀ p.1)) :=
      aux_limiting_local_energy_ae_prod_fst hconv
    have h2 : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun n => g n p.2) atTop (𝓝 (g₀ p.2)) :=
      aux_limiting_local_energy_ae_prod_snd hconv
    filter_upwards [h1, h2] with p hp1 hp2
    have hb : Tendsto (fun n => ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hp1.sub hp2).pow 2)
    exact aux_limiting_local_energy_le_liminf_div_const hb
  have hF := lintegral_liminf_le' (u := atTop) hmeas
  have hmono := lintegral_mono_ae hpoint
  calc A * (∫⁻ p, ENNReal.ofReal ((g₀ p.1 - g₀ p.2) ^ 2) / D p ∂(μ.prod μ))
      ≤ A * liminf (fun n => ∫⁻ p,
          ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ)) atTop :=
        mul_le_mul' le_rfl (le_trans hmono hF)
    _ ≤ liminf (fun n => A * (∫⁻ p,
          ENNReal.ofReal ((g n p.1 - g n p.2) ^ 2) / D p ∂(μ.prod μ))) atTop :=
        aux_limiting_local_energy_mul_liminf_le A _
end

-- DEEP (deep_fg_lle_seminorm_fatou, running): replace by its proof
theorem aux_limiting_local_energy_seminorm_le_liminf {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (w : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr))
    (hw : Tendsto w atTop (𝓝 u)) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤
      liminf (fun n => cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n)) atTop := by
    classical
    let μ : Measure (SpatialCoordinates d) :=
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    let D : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p =>
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))
    let G : DomainL2 (centeredCube z r hr) → SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
      fun f p => ENNReal.ofReal ((f p.1 - f p.2) ^ 2) / D p
    have hden : AEMeasurable D (μ.prod μ) := by
      show AEMeasurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))) (μ.prod μ)
      measurability
    have hS : ∀ f : DomainL2 (centeredCube z r hr),
        cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f) =
          ((ENNReal.ofReal (s : ℝ) /
              volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
            (∫⁻ p, G f p ∂(μ.prod μ))) ^ (1 / 2 : ℝ) := by
      intro f
      rw [cubeFractionalL2Seminorm]
      congr 1
      congr 1
      rw [MeasureTheory.lintegral_prod _ (by
        have hf : AEMeasurable (⇑f) μ := (Lp.aestronglyMeasurable f).aemeasurable
        show AEMeasurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
          ENNReal.ofReal ((⇑f p.1 - ⇑f p.2) ^ 2) / D p) (μ.prod μ)
        measurability)]
      refine lintegral_congr_ae ?_
      filter_upwards with x
      refine lintegral_congr_ae ?_
      filter_upwards with y
      rw [Fin.sum_univ_one]
    have hmain : ∀ c : ℝ≥0∞,
        liminf (fun n => cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n)) atTop < c →
        cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤ c := by
      intro c hc
      have hfreq : ∃ᶠ n in atTop,
          cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w n) < c :=
        Filter.frequently_lt_of_liminf_lt
          ⟨⊤, fun a _ => le_top⟩ hc
      obtain ⟨φ, hφ, hφlt⟩ := Filter.extraction_of_frequently_atTop hfreq
      have hwφ : Tendsto (fun n => w (φ n)) atTop (𝓝 u) := hw.comp hφ.tendsto_atTop
      have hTIM : TendstoInMeasure μ (fun n : ℕ => ⇑(w (φ n))) atTop (⇑u) :=
        MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
          (f := fun n : ℕ => ⇑(w (φ n))) (g := ⇑u) (l := atTop)
          (by norm_num)
          ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => w (φ n)) u).mp hwφ)
      obtain ⟨ns, -, hnsae⟩ := hTIM.exists_seq_tendsto_ae
      have hfat := aux_limiting_local_energy_fatou_double μ (g := fun i => ⇑(w (φ (ns i)))) (g₀ := ⇑u)
        (D := D) (A := ENNReal.ofReal (s : ℝ) /
          volume (centeredCube z r hr : Set (SpatialCoordinates d)))
        (fun i => (Lp.aestronglyMeasurable (w (φ (ns i)))).aemeasurable)
        (Lp.aestronglyMeasurable u).aemeasurable hden hnsae
      have hlim_eq : liminf (fun i => cubeFractionalL2Seminorm hd z r hr s
            (fun _ : Fin 1 => w (φ (ns i)))) atTop =
          liminf (fun i => ((ENNReal.ofReal (s : ℝ) /
              volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
            (∫⁻ p, G (w (φ (ns i))) p ∂(μ.prod μ))) ^ (1 / 2 : ℝ)) atTop :=
        liminf_congr (Filter.Eventually.of_forall fun i => hS (w (φ (ns i))))
      have hstep : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => u) ≤
          liminf (fun i => cubeFractionalL2Seminorm hd z r hr s
            (fun _ : Fin 1 => w (φ (ns i)))) atTop := by
        rw [hS u, hlim_eq]
        exact le_trans (ENNReal.rpow_le_rpow hfat (by norm_num)) aux_limiting_local_energy_liminf_rpow_half
      refine le_trans hstep ?_
      exact liminf_le_of_frequently_le (Filter.Frequently.of_forall fun i => le_of_lt (hφlt (ns i)))
        ⟨⊥, by filter_upwards with i; exact bot_le⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hLc, hcu⟩ := exists_between hcon
    exact absurd (hmain c hLc) (not_le.mpr hcu)

section
open MeasureTheory Filter Set Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

/-- `aux_limiting_local_energy_hmesh`: coarse-graining mesh estimate under the standing inputs and small-disorder
hypothesis. The disorder threshold depends on `Jc/Pc/Xc/Sf/W/Cp/D`: the estimate
is not asserted for every `M.delta`. The inputs are
`Jc, Pc, Xc, Sf, W, Cp, D, M, Rm, Sreg, It, hsmall`, matching those of
`SubdiffusiveProcess.Paper.limiting_local_energy` and the corresponding estimate for `prop_as_forms`. The conclusion is the almost-sure mesh bound
in the final `∀ᵐ omega, ...` block. The principal proof supplies these inputs
with a fourth minimum witness `δ4`.

The smoothness index is `ContDiff ℝ (⊤ : ℕ∞)`, which denotes smoothness of every
finite order. This is definitionally the same term as `ContDiff ℝ ∞` with the
scoped smoothness notation
`scoped [ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)`,
and avoids confusing it with the analytic index
`ω` in `WithTop ℕ∞`.
-/
@[irreducible] noncomputable def aux_limiting_local_energy_hmesh_delta0
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) : ℝ :=
  (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose

theorem aux_limiting_local_energy_hmesh_delta0_pos
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    0 < aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp := by
  unfold aux_limiting_local_energy_hmesh_delta0
  exact (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose_spec.1

/-! ### Step (a): the cutoff coefficient's continuous positive representative -/

/-- `cutoffPositiveCoefficient M H omega N z hr` (the `PositiveCoefficient` used by
`responseForm`) has a.e. the continuous, everywhere-positive, globally-defined representative
`cutoffCoefficient M H omega N`, and the latter is bounded above on the closed cube. -/
theorem aux_limiting_local_energy_hmesh_cutoff
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
theorem aux_limiting_local_energy_hmesh_responseForm_eq
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (w : (killedResponseSpace hP).space) :
    responseForm (killedResponseSpace hP) a w w =
      sobolevCoefficientForm a (w : SobolevData Ω) (w : SobolevData Ω) := by
  simp only [responseForm, sobolevCoefficientForm, subspaceGradient,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]






theorem aux_limiting_local_energy_hmesh_energy_bridge
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
theorem aux_limiting_local_energy_hmesh_L2close
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

/-- Packaged form of `aux_limiting_local_energy_hmesh_cutoff`'s bounds, ready for `mesh_interpolator`:
a single positive lower bound and an upper bound for the cutoff coefficient on the closed
cube. -/
theorem aux_limiting_local_energy_hmesh_cutoff_bounds
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

/-! ### Step (d): the genuinely deep coarse-graining fact  -/





variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **General additivity of `sobolevDataOfH1`.**  `sobolevDataOfH1` sends the (exact,
pointwise) sum of two `H1Function`s to the `SobolevData` sum, up to the usual `Lp`
a.e.-equality bookkeeping.  Pure assembly from `H1Function.add_toFun`/`add_grad`
(exact pointwise sums) and `sobolevDataOfH1_fst_coeFn`/`_snd_coeFn` (a.e. `Lp`
representatives), in the same style as `sobolevDataOfH1_mem_killed`. -/
theorem aux_limiting_local_energy_cb_sobolevDataOfH1_add
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



theorem aux_limiting_local_energy_cb_energy_bridge
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



theorem aux_limiting_local_energy_cb_infimum_le_response
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
  have hbridge := aux_limiting_local_energy_cb_energy_bridge a c hc Cb hcb hac u_H1
  rw [← hbridge]
  have hadd : sobolevDataOfH1 u_H1 = sobolevDataOfH1 beta + sobolevDataOfH1 v_w.toH1Function :=
    aux_limiting_local_energy_cb_sobolevDataOfH1_add beta v_w.toH1Function
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
`aux_limiting_local_energy_hmesh_delta0` already fixed for `cell_bound`'s standing inputs. Applied below
to each odd-grid subcell, not just the root cube: `lem_as_coarse`'s own quantifier order allows
any `(z, r)` once the model-level threshold `hsmall` is fixed. -/
theorem aux_limiting_local_energy_cb_coarse_spec
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
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
    (hsmall : M.delta ≤ min 1 (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
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
  unfold aux_limiting_local_energy_hmesh_delta0 at hsmall'
  have hspec := (lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).choose_spec.2
    M Rm Sreg It H HI hsmall' z r hr htri
  filter_upwards [hspec] with omega hω
  obtain ⟨K, hK, hall⟩ := hω
  exact ⟨K, hK, fun N hP G b hGcont hGhold hGb => (hall true).2.2.2 N hP G b hGcont hGhold hGb⟩

/-- Nonnegativity of `holderSeminorm`: either its ratio set is empty (`sSup ∅ = 0`), or every
member is a nonnegative ratio, so any member already witnesses `0 ≤ sSup`. -/
theorem aux_limiting_local_energy_cb_holderSeminorm_nonneg
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
sup-metric Lipschitz estimate (`lane2_abs_sub_le_mul_dist`, since `SpatialCoordinates d` carries
the maximum norm) composed with the standard sup-norm-vs-Euclidean-norm inequality `dist ≤
√(Σ(xⱼ-yⱼ)²)` (`heuclid_ge` below); the sharper Euclidean-vs-`√d·sup` direction is not needed. -/
theorem aux_limiting_local_energy_cb_holder
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {fc : SpatialCoordinates d → ℝ} (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
  have hG0nn : 0 ≤ G0 := lane2_sSup_fderiv_nonneg hfc_smooth z hr
  set side : ℝ := r / (2 * (m : ℝ) + 1) with hsidedef
  have hsidepos : 0 < side := div_pos hr (by positivity)
  have hbound_sup : ∀ x y : SpatialCoordinates d,
      x ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      y ∈ frontier (oddGridCell z r hr m k : Set (SpatialCoordinates d)) →
      |fc x - fc y| ≤ G0 * dist x y := by
    intro x y hx hy
    have hxc : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      lane2_closure_oddGridCell_subset z hr m k (frontier_subset_closure hx)
    have hyc : y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      lane2_closure_oddGridCell_subset z hr m k (frontier_subset_closure hy)
    have hbnd : ∀ w ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ‖fderiv ℝ fc w‖ ≤ G0 :=
      fun w hw => lane2_le_sSup_image (lane2_isCompact_closure_centeredCube z hr)
        (lane2_continuous_norm_fderiv hfc_smooth) hw
    have h' : |fc y - fc x| ≤ G0 * dist y x :=
      lane2_abs_sub_le_mul_dist hfc_smooth (lane2_convex_closure_centeredCube z hr) hbnd hxc hyc
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



theorem aux_limiting_local_energy_cb_percell
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
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
    (hsmall : M.delta ≤ min 1 (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j)
    (J : ℕ) (k : OddGridIndex d (triadicHalf J)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
    rw [lane2_cell_side_eq r J, hj, ← zpow_natCast (3 : ℝ) J,
      ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hcoarse := aux_limiting_local_energy_cb_coarse_spec hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hsmall
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
    aux_limiting_local_energy_hmesh_cutoff M H omega N (oddGridCenter z r (triadicHalf J) k) hsidepos
  have habridge := aux_limiting_local_energy_cb_infimum_le_response hPoincare
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
  obtain ⟨hHolderOn, -⟩ := aux_limiting_local_energy_cb_holder z hr hfc_smooth (triadicHalf J) k
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
bound, and sums the finite cell partition. `aux_limiting_local_energy_cb_holder`
supplies the norm conversion. All coefficient and Sobolev inputs remain
explicit in the theorem statement. -/
theorem aux_limiting_local_energy_hmesh_cell_bound
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
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
    (hsmall : M.delta ≤ min 1 (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (J : ℕ)
      (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
        ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
    fun J k => aux_limiting_local_energy_cb_percell hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hsmall
      z r hr htri J k
  have hall : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (J : ℕ) (k : OddGridIndex d (triadicHalf J)),
      ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
  have hG0nn : 0 ≤ G0 := lane2_sSup_fderiv_nonneg hfc_smooth z hr
  have hHolder : ∀ k : OddGridIndex d (triadicHalf J),
      holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc ≤
        G0 * side ^ (1 / 4 : ℝ) :=
    fun k => (aux_limiting_local_energy_cb_holder z hr hfc_smooth (triadicHalf J) k).2
  have hHolderNonneg : ∀ k : OddGridIndex d (triadicHalf J),
      0 ≤ holderSeminorm (3 / 4 : ℝ)
          (frontier (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) fc :=
    fun k => aux_limiting_local_energy_cb_holderSeminorm_nonneg _ _ _
      (aux_limiting_local_energy_cb_holder z hr hfc_smooth (triadicHalf J) k).1
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

/-! ### Assembly setup (own heartbeat budget, split off `aux_limiting_local_energy_hmesh`) -/

/-- Given the cell bound `hcell` at a fixed `omega` and a fixed smooth compactly-supported
datum `fc`, choose the mesh depth `J` so the (coefficient-independent) mesh error is `< ε`,
build the mesh interpolant `wf n` at that depth for every cutoff level `n` (`mesh_interpolator`),
and package its uniform-in-`N` response bound, its cellwise energy decomposition and its `L^∞`
mesh error all at once. Split out from `aux_limiting_local_energy_hmesh` purely for the heartbeat
budget: each of `aux_limiting_local_energy_hmesh_setup` and `aux_limiting_local_energy_hmesh` gets its own
default `maxHeartbeats`, instead of the combined proof needing an override. -/
theorem aux_limiting_local_energy_hmesh_setup
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
    (hfc_supp : HasCompactSupport fc)
    (hfc_sub : tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (ε : ℝ) (hε : 0 < ε)
    (hcell : ∀ (J : ℕ)
        (fc : SpatialCoordinates d → ℝ) (hfc_smooth : ContDiff ℝ (⊤ : ℕ∞) fc)
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
  have hGnn : 0 ≤ G := lane2_sSup_fderiv_nonneg hfc_smooth z hr
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
    fun n => aux_limiting_local_energy_hmesh_cutoff_bounds M H omega n z hr
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
as needed by `prop_as_forms`'s assembly. Standing inputs `Jc`, `Pc`, `Xc`, `Sf` are the same
`in_J`/`in_poincare`/`in_extension`/`SobolevFoundationalInput` objects `prop_as_forms`
already binds; `W`, `Cp`, `D` are the standing inputs `SubdiffusiveProcess.Paper.lem_as_coarse` now also requires; `hsmall` is the small-disorder
hypothesis, at the same threshold `prop_as_forms` introduces via `lem_as_coarse`'s own `delta0`.

The per-cell mathematical estimate is isolated in `aux_limiting_local_energy_hmesh_cell_bound`. -/
theorem aux_limiting_local_energy_hmesh
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @_root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d
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
    (hsmall : M.delta ≤ min 1 (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ φ : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → (killedResponseSpace hP).space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm (killedResponseSpace hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε) := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [aux_limiting_local_energy_hmesh_cell_bound hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI
    hsmall z r hr htri] with omega hcell
  rintro φ ⟨fc, hfc_smooth, hfc_supp, hfc_sub, hfc_rep⟩ ε hε
  obtain ⟨Cmesh, G, hCmesh0, hGnn, J, C, wf, hC, hwsum, hwerr, hfinal⟩ :=
    aux_limiting_local_energy_hmesh_setup hd z r hr M H omega fc hfc_smooth hfc_supp hfc_sub ε hε hcell
  refine ⟨fun n => ⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩,
    C, ?_, ?_⟩
  · intro n
    have step1 := aux_limiting_local_energy_hmesh_responseForm_eq hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
      (⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩ :
        (killedResponseSpace hP).space)
    obtain ⟨hcontn, hposn, ⟨Lamn, hLamn⟩, haen⟩ := aux_limiting_local_energy_hmesh_cutoff M H omega n z hr
    have hcb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ‖cutoffCoefficient M H omega n x‖ ≤ Lamn := by
      filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (hposn x)]
      exact hLamn x (centeredCube_subset_closedCube z hr hx)
    have step2 := aux_limiting_local_energy_hmesh_energy_bridge
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
    have hL2 := aux_limiting_local_energy_hmesh_L2close z hr fc (wf n).toH1Function.toFun
      (Cmesh * (r / (3 : ℝ) ^ J) * G)
      (mul_nonneg (mul_nonneg hCmesh0 (by positivity)) hGnn)
      (hwerr n)
      (⟨sobolevDataOfH1 (wf n).toH1Function, sobolevDataOfH1_mem_killed (wf n)⟩ :
        (killedResponseSpace hP).space).val.1
      hQ φ hfc_rep
    exact hL2.trans hfinal.le


end





/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_dense_range_of_symm := SubdiffusiveProcess.LimitFormCore.dense_range_of_symm

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_dual_term_eq := SubdiffusiveProcess.LimitFormCore.dual_term_eq

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_limitFormEnergy_root := SubdiffusiveProcess.LimitFormCore.limitFormEnergy_root

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_form_root := SubdiffusiveProcess.LimitFormCore.form_root

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_domain_eq_range := SubdiffusiveProcess.LimitFormCore.domain_eq_range

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_core_dense := SubdiffusiveProcess.LimitFormCore.core_dense

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold := SubdiffusiveProcess.LimitFormCore.softThreshold

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_zero := SubdiffusiveProcess.LimitFormCore.softThreshold_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_mono_le := SubdiffusiveProcess.LimitFormCore.softThreshold_mono_le

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_isNormalContraction := SubdiffusiveProcess.LimitFormCore.softThreshold_isNormalContraction

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_sub_le := SubdiffusiveProcess.LimitFormCore.softThreshold_sub_le

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_ne_zero := SubdiffusiveProcess.LimitFormCore.softThreshold_ne_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_continuous_softThreshold := SubdiffusiveProcess.LimitFormCore.continuous_softThreshold

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_isFiniteMeasure_cube := SubdiffusiveProcess.LimitFormCore.isFiniteMeasure_cube

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_softThreshold_support := SubdiffusiveProcess.LimitFormCore.softThreshold_support

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_coreSubmodule := SubdiffusiveProcess.LimitFormCore.coreSubmodule

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_isCoreOn := SubdiffusiveProcess.LimitFormCore.isCoreOn

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_isRegular_of_isCoreOn := SubdiffusiveProcess.LimitFormCore.isRegular_of_isCoreOn

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_form_eq_zero_of_bilinear := SubdiffusiveProcess.LimitFormCore.form_eq_zero_of_bilinear

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_DirProp := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_DirProp

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_c2Norm_zero := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_c2Norm_zero

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_holder_pt := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_holder_pt

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_closure_cube := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_closure_cube

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_dist_le_euclid := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_dist_le_euclid

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_killed_holder := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_cutoff_continuity_killed_holder

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_Gf_continuous_hvc := _root_.SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_Gf_continuous_subseq := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_subseq

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_Gf_continuous_Ltwo := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_continuity_Gf_continuous_Ltwo

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_Gf_continuous := _root_.SubdiffusiveProcess.Paper.prop_conc_form_continuity

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_qlocal := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_data_qlocal

/-- Compatibility export of the extracted local form fact. -/
alias aux_limiting_local_energy_isStronglyLocal := _root_.SubdiffusiveProcess.Paper.aux_prop_conc_form_data_isStronglyLocal






/-! Original represented cutoff and uniform-density predicates. -/
section
variable {d : ℕ}
def aux_limiting_local_energy_HCUTProp [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (s : ℕ → ℕ) (omega : BilateralField d) : Prop :=
  ∀ (K O : Set (SpatialCoordinates d)),
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
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (s n) z hr) (chi n) (chi n) ≤ B ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
        0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (s n) z hr).val y *
            ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ ((d : ℝ) - 1 / 2)))

/-- The `HUNIF` conclusion, folded behind a `def`, same reason as `aux_limiting_local_energy_
HCUTProp`. -/
def aux_limiting_local_energy_HUNIFProp [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (s : ℕ → ℕ) (omega : BilateralField d) : Prop :=
  ∀ (GNi : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
    (∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNi n f =
      (_root_.SubdiffusiveProcess.Paper.in_killed_inverse M H HI omega (s n) z hr hP f :
        SobolevData (centeredCube z r hr)).1) →
    Tendsto GNi atTop (𝓝 G) →
  ∀ (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (_hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u),
  ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
    tsupport f0 ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g ∧
      ∀ x, |g x - f0 x| < ε

/-- Opaque `Prop` wrapper for the PER-MODEL `HCUT` principal binder; `HCUT`/`HUNIF` are per-model inputs threaded under `hdelta`, not a standing input over
every model. Adds back the `∀ᵐ omega ∂..., ∀ z r hr ...`
layer around the already-existing per-cube `aux_limiting_local_energy_HCUTProp`. Same heartbeat
rationale as that def and as `SubdiffusiveProcess.Paper.aux_prop_as_forms_HCUT_prop`: stating the per-model `HCUT`
inline (dependent on the already-bound `M`/`H` in the same telescope as the other per-model
binders `Rm`/`Sreg`/`It`) rather than behind a small opaque `def` measurably inflates the
heartbeat cost of every subsequent `intro`/`have` in this already-large declaration. -/
def aux_limiting_local_energy_HCUT_prop [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖),
      aux_limiting_local_energy_HCUTProp M H z r hr hP (s ∘ t) omega

/-- Opaque `Prop` wrapper for the PER-MODEL `HUNIF` principal binder, same rationale as
`aux_limiting_local_energy_HCUT_prop` above. -/
def aux_limiting_local_energy_HUNIF_prop [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H) :
    Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖),
      aux_limiting_local_energy_HUNIFProp M H HI z r hr hP (s ∘ t) omega

end

alias aux_limiting_local_energy_limit_dirichlet_form := _root_.SubdiffusiveProcess.Paper.prop_conc_form_data


section
open Filter Set MeasureTheory Topology
open scoped ENNReal NNReal BigOperators
-- Local response and potential helpers for the limiting energy construction.
-- Needs imports: Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable, ...BorelSpace.ContinuousLinearMap,
-- SubdiffusiveProcess.Sobolev.{CompactResponses,ResponsePositivity,PotentialResponses}, Main.{NormalizedContinuousPositiveCoefficient,CutoffCoefficient,CutoffPotential,ContinuousPositiveLog}
-- and `open scoped BoundedContinuousFunction`.
/-- A symmetric operator whose quadratic form is bounded by `c ‖h‖²` has norm at most `c`. -/
theorem aux_limiting_local_energy_polar {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y)) (f g : E) :
    4 * inner ℝ g (T f)
      = inner ℝ (f + g) (T (f + g)) - inner ℝ (f - g) (T (f - g)) := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [← hsym f g, ← real_inner_comm (T f) g]
  ring

theorem aux_limiting_local_energy_quad_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y)) (c : ℝ)
    (hq : ∀ h : E, |inner ℝ h (T h)| ≤ c * ‖h‖ ^ 2) (f g : E) :
    2 * |inner ℝ g (T f)| ≤ c * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have h4 := aux_limiting_local_energy_polar T hsym f g
  have hA : |inner ℝ (f + g) (T (f + g))| ≤ c * ‖f + g‖ ^ 2 := hq (f + g)
  have hB : |inner ℝ (f - g) (T (f - g))| ≤ c * ‖f - g‖ ^ 2 := hq (f - g)
  have hpar : ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 = 2 * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  have hsum : c * ‖f + g‖ ^ 2 + c * ‖f - g‖ ^ 2 = 2 * (c * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    rw [← mul_add, hpar]
    ring
  have h1 : 4 * |inner ℝ g (T f)| ≤ c * ‖f + g‖ ^ 2 + c * ‖f - g‖ ^ 2 := by
    have hx : 4 * |inner ℝ g (T f)|
        = |inner ℝ (f + g) (T (f + g)) - inner ℝ (f - g) (T (f - g))| := by
      rw [← h4, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)]
    calc 4 * |inner ℝ g (T f)|
        = |inner ℝ (f + g) (T (f + g)) - inner ℝ (f - g) (T (f - g))| := hx
      _ ≤ |inner ℝ (f + g) (T (f + g))| + |inner ℝ (f - g) (T (f - g))| := abs_sub _ _
      _ ≤ c * ‖f + g‖ ^ 2 + c * ‖f - g‖ ^ 2 := add_le_add hA hB
  have h2 : 4 * |inner ℝ g (T f)| ≤ 2 * (c * (‖f‖ ^ 2 + ‖g‖ ^ 2)) := by
    rw [← hsum]
    exact h1
  linarith

theorem aux_limiting_local_energy_norm_le_of_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y)) (c : ℝ) (hc : 0 ≤ c)
    (hq : ∀ h : E, |inner ℝ h (T h)| ≤ c * ‖h‖ ^ 2) : ‖T‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound T hc ?_
  intro f
  by_cases hf : f = 0
  · have h0 : ‖T f‖ = c * ‖f‖ := by rw [hf, map_zero, norm_zero, mul_zero]
    exact le_of_eq h0
  by_cases hTf : T f = 0
  · rw [hTf, norm_zero]
    exact mul_nonneg hc (norm_nonneg f)
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hTfpos : 0 < ‖T f‖ := norm_pos_iff.mpr hTf
  have hTfne : ‖T f‖ ≠ 0 := ne_of_gt hTfpos
  have hinner : inner ℝ ((‖f‖ / ‖T f‖) • T f) (T f) = ‖f‖ * ‖T f‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
      div_mul_cancel₀ (‖f‖) hTfne]
  have hnorm : ‖(‖f‖ / ‖T f‖) • T f‖ = ‖f‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg f) (le_of_lt hTfpos))]
    exact div_mul_cancel₀ (‖f‖) hTfne
  have hb := aux_limiting_local_energy_quad_bound T hsym c hq f ((‖f‖ / ‖T f‖) • T f)
  rw [hinner, hnorm] at hb
  rw [abs_of_nonneg (mul_nonneg (norm_nonneg f) (norm_nonneg (T f)))] at hb
  have hsq : ‖f‖ ^ 2 + ‖f‖ ^ 2 = 2 * ‖f‖ ^ 2 := by ring
  rw [hsq] at hb
  have hmain : ‖f‖ * ‖T f‖ ≤ c * ‖f‖ ^ 2 := by
    have h2sq : c * (2 * ‖f‖ ^ 2) = 2 * (c * ‖f‖ ^ 2) := by ring
    rw [h2sq] at hb
    linarith
  have h3 : ‖T f‖ * ‖f‖ ≤ (c * ‖f‖) * ‖f‖ := by
    calc ‖T f‖ * ‖f‖ = ‖f‖ * ‖T f‖ := mul_comm (‖T f‖) ‖f‖
      _ ≤ c * ‖f‖ ^ 2 := hmain
      _ = (c * ‖f‖) * ‖f‖ := by ring
  exact le_of_mul_le_mul_right h3 hfpos

/-- Two-sided comparison of nonnegative symmetric quadratic forms bounds the operator distance. -/
theorem aux_limiting_local_energy_norm_sub_le_of_comparison {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A B : E →L[ℝ] E)
    (hsymA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hsymB : ∀ x y : E, inner ℝ (B x) y = inner ℝ x (B y))
    (hposA : ∀ h : E, 0 ≤ inner ℝ h (A h)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlow : ∀ h : E, Real.exp (-δ) * inner ℝ h (A h) ≤ inner ℝ h (B h))
    (hupp : ∀ h : E, inner ℝ h (B h) ≤ Real.exp δ * inner ℝ h (A h)) :
    ‖B - A‖ ≤ (Real.exp δ - 1) * ‖A‖ := by
  have hsym : ∀ x y : E, inner ℝ ((B - A) x) y = inner ℝ x ((B - A) y) := by
    intro x y
    rw [sub_apply, sub_apply,
      inner_sub_left, inner_sub_right, hsymB x y, hsymA x y]
  have hexp1 : (0 : ℝ) ≤ Real.exp δ - 1 := by
    have h := Real.one_le_exp hδ
    linarith
  apply aux_limiting_local_energy_norm_le_of_quadratic (B - A) hsym ((Real.exp δ - 1) * ‖A‖)
  · exact mul_nonneg hexp1 (norm_nonneg A)
  · intro h
    have hq0 : 0 ≤ inner ℝ h (A h) := hposA h
    have hupper : inner ℝ h ((B - A) h) ≤ (Real.exp δ - 1) * inner ℝ h (A h) := by
      rw [sub_apply, inner_sub_right]
      linarith [hupp h]
    have hexpsum : 0 ≤ Real.exp (-δ) + Real.exp δ - 2 := by
      have h1 := Real.add_one_le_exp (-δ)
      have h2 := Real.add_one_le_exp δ
      linarith
    have hmul : 0 ≤ (Real.exp (-δ) + Real.exp δ - 2) * inner ℝ h (A h) :=
      mul_nonneg hexpsum hq0
    have hlower : -((Real.exp δ - 1) * inner ℝ h (A h)) ≤ inner ℝ h ((B - A) h) := by
      rw [sub_apply, inner_sub_right]
      linarith [hlow h, hmul]
    have hinner : |inner ℝ h ((B - A) h)| ≤ (Real.exp δ - 1) * inner ℝ h (A h) := by
      rw [abs_le]
      exact ⟨hlower, hupper⟩
    have hqbound : inner ℝ h (A h) ≤ ‖A‖ * ‖h‖ ^ 2 := by
      have h1 : inner ℝ h (A h) ≤ ‖h‖ * ‖A h‖ := real_inner_le_norm h (A h)
      have h2 : ‖A h‖ ≤ ‖A‖ * ‖h‖ := A.le_opNorm h
      have h3 : ‖h‖ * ‖A h‖ ≤ ‖h‖ * (‖A‖ * ‖h‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg h)
      calc inner ℝ h (A h) ≤ ‖h‖ * ‖A h‖ := h1
        _ ≤ ‖h‖ * (‖A‖ * ‖h‖) := h3
        _ = ‖A‖ * ‖h‖ ^ 2 := by ring
    calc |inner ℝ h ((B - A) h)| ≤ (Real.exp δ - 1) * inner ℝ h (A h) := hinner
      _ ≤ (Real.exp δ - 1) * (‖A‖ * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hqbound hexp1
      _ = ((Real.exp δ - 1) * ‖A‖) * ‖h‖ ^ 2 := by ring

/-- The volume-load pairing of the response is the inverse response. -/
theorem aux_limiting_local_energy_pairing_eq_inverseResponse {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (h : DomainL2 Ω) :
    inner ℝ h (responseSolution S a ((sobolevVolumeLoad h).comp S.space.subtypeL)).val.1 =
      inverseResponse S a ((sobolevVolumeLoad h).comp S.space.subtypeL) := by
  rw [inverseResponse_eq_load]
  rfl

/-- The global log-potential of the normalized cutoff coefficient, infrared field included. -/
noncomputable def aux_limiting_local_energy_logPotential {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
    (H om + ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)))

theorem aux_limiting_local_energy_logPotential_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (aux_limiting_local_energy_logPotential M H N) := by
  unfold aux_limiting_local_energy_logPotential
  exact measurable_const.add
    (hH.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i))))

theorem aux_limiting_local_energy_rootLog_eq {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    continuousPositiveLog (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H om N z hr)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H om N z hr) =
      (aux_limiting_local_energy_logPotential M H N om).restrict
        (closedCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  have hh : Real.log (cutoffCoefficient M H om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        (H om x + ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) x) := by
    rw [cutoffCoefficient, Real.log_mul
      (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
      (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
    simp only [cutoffPotential]
    ring
  have hv : ((aux_limiting_local_energy_logPotential M H N om).restrict
      (closedCube z r hr : Set (SpatialCoordinates d))) x =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        (H om x + ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) x) := by
    rw [ContinuousMap.restrict_apply]
    simp only [aux_limiting_local_energy_logPotential, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.sum_apply]
  simpa only [continuousPositiveLog, _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM,
    ContinuousMap.coe_mk] using! hh.trans hv.symm


theorem aux_limiting_local_energy_coeff_eq {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    [Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr)] :
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr =
      expPotentialCoefficient (compactPotentialToLp (closedCube z r hr)
        ((aux_limiting_local_energy_logPotential M H N om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)))) := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
  rw [aux_limiting_local_energy_rootLog_eq]
  simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]

/-- The volume-response operator of an exponential potential. -/
noncomputable def aux_limiting_local_energy_respOp {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    DomainL2 Ω →L[ℝ] DomainL2 Ω :=
  (existsUnique_volumeResponseOperator S (expPotentialCoefficient g)).exists.choose

theorem aux_limiting_local_energy_respOp_apply {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (f : DomainL2 Ω) :
    aux_limiting_local_energy_respOp S g f =
      (responseSolution S (expPotentialCoefficient g)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
  (existsUnique_volumeResponseOperator S (expPotentialCoefficient g)).exists.choose_spec f

theorem aux_limiting_local_energy_respOp_norm_sub_le {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (g g' : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ‖aux_limiting_local_energy_respOp S g' - aux_limiting_local_energy_respOp S g‖ ≤
      (Real.exp ‖g - g'‖ - 1) * ‖aux_limiting_local_energy_respOp S g‖ := by
  apply aux_limiting_local_energy_norm_sub_le_of_comparison
    (A := aux_limiting_local_energy_respOp S g)
    (B := aux_limiting_local_energy_respOp S g')
    (δ := ‖g - g'‖)
  · intro x y
    rw [aux_limiting_local_energy_respOp_apply S g x,
      aux_limiting_local_energy_respOp_apply S g y]
    exact (real_inner_comm y
      ((responseSolution S (expPotentialCoefficient g)
        ((sobolevVolumeLoad x).comp S.space.subtypeL)).val.1)).trans
      (volumeResponse_pairing_symm S (expPotentialCoefficient g) x y).symm
  · intro x y
    rw [aux_limiting_local_energy_respOp_apply S g' x,
      aux_limiting_local_energy_respOp_apply S g' y]
    exact (real_inner_comm y
      ((responseSolution S (expPotentialCoefficient g')
        ((sobolevVolumeLoad x).comp S.space.subtypeL)).val.1)).trans
      (volumeResponse_pairing_symm S (expPotentialCoefficient g') x y).symm
  · intro h
    rw [aux_limiting_local_energy_respOp_apply S g h]
    exact volumeResponse_pairing_nonneg S (expPotentialCoefficient g) h
  · exact norm_nonneg _
  · intro h
    rw [aux_limiting_local_energy_respOp_apply S g h,
      aux_limiting_local_energy_respOp_apply S g' h,
      aux_limiting_local_energy_pairing_eq_inverseResponse S (expPotentialCoefficient g) h,
      aux_limiting_local_energy_pairing_eq_inverseResponse S (expPotentialCoefficient g') h]
    exact (inverseResponse_potential_comparison S
      ((sobolevVolumeLoad h).comp S.space.subtypeL) g g').1
  · intro h
    rw [aux_limiting_local_energy_respOp_apply S g h,
      aux_limiting_local_energy_respOp_apply S g' h,
      aux_limiting_local_energy_pairing_eq_inverseResponse S (expPotentialCoefficient g) h,
      aux_limiting_local_energy_pairing_eq_inverseResponse S (expPotentialCoefficient g') h]
    exact (inverseResponse_potential_comparison S
      ((sobolevVolumeLoad h).comp S.space.subtypeL) g g').2

theorem aux_limiting_local_energy_respOp_continuous {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) : Continuous (aux_limiting_local_energy_respOp S) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun g' => aux_limiting_local_energy_respOp_norm_sub_le S g g') ?_
  have hcont : Continuous
      (fun g' => (Real.exp ‖g - g'‖ - 1) * ‖aux_limiting_local_energy_respOp S g‖) :=
    ((Real.continuous_exp.comp (continuous_const.sub continuous_id).norm).sub
      continuous_const).mul continuous_const
  have h0 : (Real.exp ‖g - g‖ - 1) * ‖aux_limiting_local_energy_respOp S g‖ = 0 := by
    rw [sub_self, norm_zero, Real.exp_zero, sub_self, zero_mul]
  have ht := hcont.tendsto g
  rwa [h0] at ht

theorem aux_limiting_local_energy_GN_stronglyMeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (GN : BilateralField d → ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGN : ∀ (omega : BilateralField d) (n : ℕ) (f : DomainL2 (centeredCube z r hr)),
      GN omega n f = (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (n : ℕ) : StronglyMeasurable (fun omega => GN omega n) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have heq : (fun omega => GN omega n) = fun omega =>
      aux_limiting_local_energy_respOp (killedResponseSpace hP)
        (compactPotentialToLp (closedCube z r hr)
          ((aux_limiting_local_energy_logPotential M H n omega).restrict
            (closedCube z r hr : Set (SpatialCoordinates d)))) := by
    funext omega
    ext1 f
    rw [hGN, aux_limiting_local_energy_respOp_apply, ← aux_limiting_local_energy_coeff_eq]
  rw [heq]
  exact ((aux_limiting_local_energy_respOp_continuous _).comp
    ((compactPotentialToLp (closedCube z r hr)).continuous.comp
      (ContinuousMap.continuous_restrict _))).comp_stronglyMeasurable
    (aux_limiting_local_energy_logPotential_measurable M H hH n).stronglyMeasurable

open Classical in
/-- Measurability of the inverse limit (`Measurable G`, `mfd:sec-local-form`: "the inverse limit is measurable in the original
layers as the limit of the actual cutoff inverses"). `GN` are the actual cutoff inverse operators. -/
theorem aux_limiting_local_energy_measurable_limit {d : ℕ} (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (GN : BilateralField d → ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGN : ∀ (omega : BilateralField d) (n : ℕ) (f : DomainL2 (centeredCube z r hr)),
      GN omega n f = (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) :
    Measurable (fun omega : BilateralField d =>
      if h : ∃ G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
          Tendsto (GN omega) atTop (𝓝 G') then Classical.choose h else 0) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : CompleteSpace (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)) :=
    inferInstance
  have : IsCompletelyMetrizableSpace
      (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)) :=
    MetricSpace.toIsCompletelyMetrizableSpace
  have hsm : ∀ n, StronglyMeasurable (fun omega => GN omega n) :=
    aux_limiting_local_energy_GN_stronglyMeasurable M H HI.1 z hr hP GN hGN
  have hC : MeasurableSet {omega : BilateralField d | ∃ c, Tendsto (fun n => GN omega n) atTop (𝓝 c)} :=
    StronglyMeasurable.measurableSet_exists_tendsto hsm
  have hlim : StronglyMeasurable (fun omega => limUnder atTop (fun n => GN omega n)) :=
    StronglyMeasurable.limUnder hsm
  have heq : (fun omega : BilateralField d =>
      if h : ∃ G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
          Tendsto (GN omega) atTop (𝓝 G') then Classical.choose h else 0) =
      {omega : BilateralField d | ∃ c, Tendsto (fun n => GN omega n) atTop (𝓝 c)}.indicator
        (fun omega => limUnder atTop (fun n => GN omega n)) := by
    funext omega
    by_cases h : ∃ G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        Tendsto (GN omega) atTop (𝓝 G')
    · rw [dite_eq_left h, Set.indicator_of_mem (show omega ∈ {omega : BilateralField d |
          ∃ c, Tendsto (fun n => GN omega n) atTop (𝓝 c)} from h)]
      exact tendsto_nhds_unique (Classical.choose_spec h) (tendsto_nhds_limUnder h)
    · rw [dite_eq_right h, Set.indicator_of_notMem (show omega ∉ {omega : BilateralField d |
          ∃ c, Tendsto (fun n => GN omega n) atTop (𝓝 c)} from h)]
  rw [heq]
  exact (hlim.indicator hC).measurable


/-! ## Joint-law identification (last conjunct of limiting_local_energy, `mfd:sec-local-form`) -/

/-- The actual cutoff response to a fixed source is strongly measurable in the field. -/
theorem aux_limiting_local_energy_resp_stronglyMeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (n : ℕ) (f : DomainL2 (centeredCube z r hr)) :
    StronglyMeasurable (fun omega : BilateralField d =>
      (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have heq : (fun omega : BilateralField d =>
      (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) =
      fun omega => aux_limiting_local_energy_respOp (killedResponseSpace hP)
        (compactPotentialToLp (closedCube z r hr)
          ((aux_limiting_local_energy_logPotential M H n omega).restrict
            (closedCube z r hr : Set (SpatialCoordinates d)))) f := by
    funext omega
    rw [aux_limiting_local_energy_respOp_apply, ← aux_limiting_local_energy_coeff_eq]
  rw [heq]
  exact ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube z r hr)) f).continuous.comp
    ((aux_limiting_local_energy_respOp_continuous _).comp
      ((compactPotentialToLp (closedCube z r hr)).continuous.comp
        (ContinuousMap.continuous_restrict _)))).comp_stronglyMeasurable
    (aux_limiting_local_energy_logPotential_measurable M H hH n).stronglyMeasurable

/-- Bounded continuous test functions pass to almost-sure limits under the integral. -/
theorem aux_limiting_local_energy_tendsto_integral_bcf {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (X : ℕ → α → β) (X' : α → β)
    (hX : ∀ N, AEMeasurable (X N) ν)
    (hXlim : ∀ᵐ a ∂ν, Tendsto (fun N => X N a) atTop (𝓝 (X' a))) (φ : β →ᵇ ℝ) :
    Tendsto (fun N => ∫ a, φ (X N a) ∂ν) atTop (𝓝 (∫ a, φ (X' a) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    (fun N => AEMeasurable.aestronglyMeasurable
      ((φ.continuous.aemeasurable (μ := Measure.map (X N) ν)).comp_aemeasurable (hX N)))
    (integrable_const _)
    (fun N => Eventually.of_forall fun a => φ.norm_coe_le_norm _) ?_
  filter_upwards [hXlim] with a ha
  exact (φ.continuous.tendsto (X' a)).comp ha

/-- Almost-sure limits of sequences with equal laws have equal laws. -/
theorem aux_limiting_local_energy_map_eq_of_ae_tendsto {α γ β : Type*}
    [MeasurableSpace α] [MeasurableSpace γ]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure γ) [IsProbabilityMeasure μ]
    (X : ℕ → α → β) (X' : α → β) (Y : ℕ → γ → β) (Y' : γ → β)
    (hX : ∀ N, AEMeasurable (X N) ν) (hX' : AEMeasurable X' ν)
    (hY : ∀ N, AEMeasurable (Y N) μ) (hY' : AEMeasurable Y' μ)
    (hlaw : ∀ N, Measure.map (X N) ν = Measure.map (Y N) μ)
    (hXlim : ∀ᵐ a ∂ν, Tendsto (fun N => X N a) atTop (𝓝 (X' a)))
    (hYlim : ∀ᵐ c ∂μ, Tendsto (fun N => Y N c) atTop (𝓝 (Y' c))) :
    Measure.map X' ν = Measure.map Y' μ := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [MeasureTheory.integral_map hX' φ.continuous.aestronglyMeasurable,
    MeasureTheory.integral_map hY' φ.continuous.aestronglyMeasurable]
  have hν := aux_limiting_local_energy_tendsto_integral_bcf ν X X' hX hXlim φ
  have hμ := aux_limiting_local_energy_tendsto_integral_bcf μ Y Y' hY hYlim φ
  have hseq : (fun N => ∫ a, φ (X N a) ∂ν) = fun N => ∫ c, φ (Y N c) ∂μ := by
    funext N
    rw [← MeasureTheory.integral_map (hX N) φ.continuous.aestronglyMeasurable,
      ← MeasureTheory.integral_map (hY N) φ.continuous.aestronglyMeasurable, hlaw N]
  rw [hseq] at hν
  exact tendsto_nhds_unique hν hμ

/-- If `(A, B)` has the law of the graph of a measurable map, then `B = ψ ∘ A` almost surely. -/
theorem aux_limiting_local_energy_ae_eq_of_map_graph {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure α) (μ : Measure β)
    (A : α → β) (B : α → E) (hA : Measurable A) (hB : Measurable B)
    (ψ : β → E) (hψ : Measurable ψ)
    (hlaw : Measure.map (fun a => (A a, B a)) ν = Measure.map (fun c => (c, ψ c)) μ) :
    ∀ᵐ a ∂ν, B a = ψ (A a) := by
  rw [MeasureTheory.ae_iff]
  set S : Set (β × E) := {p : β × E | p.2 = ψ p.1} with hSdef
  have hmeas1 : Measurable (fun a : α => (A a, B a)) := hA.prodMk hB
  have hmeas2 : Measurable (fun c : β => (c, ψ c)) := measurable_id.prodMk hψ
  have hS : MeasurableSet S := by
    rw [hSdef]
    exact measurableSet_eq_fun measurable_snd (hψ.comp measurable_fst)
  have hbad : {a : α | ¬ B a = ψ (A a)} = (fun a : α => (A a, B a)) ⁻¹' Sᶜ := by
    ext a
    simp [hSdef]
  have hempty : (fun c : β => (c, ψ c)) ⁻¹' Sᶜ = ∅ := by
    ext c
    simp [hSdef]
  rw [hbad, ← Measure.map_apply hmeas1 hS.compl, hlaw, Measure.map_apply hmeas2 hS.compl,
    hempty]
  exact measure_empty

/-- Per-probe identification: `Ĝ η (f_i) = G(ω̂ η)(f_i)` almost surely (weak limit + graph). -/
theorem aux_limiting_local_energy_joint_probe {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (G : BilateralField d →
      (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGmeas : Measurable G)
    (hGlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun N => (responseSolution (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
        atTop (𝓝 (G omega f))) :
    let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
    let a : BilateralField d → ℕ → PositiveCoefficient Q :=
      fun omega N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr
    ∀ (cutoff : ℕ → ℕ), StrictMono cutoff →
      ∀ (fprobe : ℕ → DomainL2 Q), DenseRange fprobe →
      ∀ (OmegaHat : Type) [MeasurableSpace OmegaHat]
        (nu : Measure OmegaHat) [IsProbabilityMeasure nu],
      ∀ (omegaHatN : ℕ → OmegaHat → BilateralField d)
        (omegaHat : OmegaHat → BilateralField d)
        (responseHatN : ℕ → OmegaHat → ℕ → DomainL2 Q)
        (Ghat : OmegaHat → (DomainL2 Q →L[ℝ] DomainL2 Q)),
      (∀ N, Measurable (omegaHatN N)) → Measurable omegaHat →
      (∀ N,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measurable (responseHatN N))) →
      (∀ i,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measurable (fun eta => Ghat eta (fprobe i)))) →
      (∀ N,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measure.map (fun eta => (omegaHatN N eta, responseHatN N eta)) nu =
            Measure.map (fun omega : BilateralField d =>
              (omega,
                fun i : ℕ =>
                  (responseSolution (killedResponseSpace (Ω := Q) hP)
                      (a omega (cutoff N))
                      ((sobolevVolumeLoad (fprobe i)).comp
                        (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
              (chaosSampleLaw M).toMeasure)) →
      (∀ᵐ eta ∂nu,
        Tendsto (fun N => omegaHatN N eta) atTop (𝓝 (omegaHat eta)) ∧
          ∀ i, Tendsto (fun N => responseHatN N eta i) atTop
            (𝓝 (Ghat eta (fprobe i)))) →
      ∀ i : ℕ, ∀ᵐ eta ∂nu, Ghat eta (fprobe i) = G (omegaHat eta) (fprobe i) := by
  intro Q a cutoff hcut fprobe hdense OmegaHat instOHat nu instNu omegaHatN omegaHat
    responseHatN Ghat hmeasN hmeas hmeasR hmeasG hlaw hconv i
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let : SecondCountableTopology (DomainL2 Q) := inferInstance
  let : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q)
  have : BorelSpace (DomainL2 Q) := ⟨rfl⟩
  have hmeasψ : Measurable (fun ω : BilateralField d => G ω (fprobe i)) :=
    ((ContinuousLinearMap.apply ℝ (DomainL2 Q) (fprobe i)).continuous.measurable).comp hGmeas
  have hR : ∀ N j : ℕ, Measurable (fun ω : BilateralField d =>
      (responseSolution (killedResponseSpace (Ω := Q) hP) (a ω (cutoff N))
        ((sobolevVolumeLoad (fprobe j)).comp
          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1) :=
    fun N j => (aux_limiting_local_energy_resp_stronglyMeasurable M H HI.1 z hr hP
      (cutoff N) (fprobe j)).measurable
  have hXsm : ∀ N, AEMeasurable (fun eta : OmegaHat =>
      (omegaHatN N eta, responseHatN N eta i)) nu :=
    fun N => ((hmeasN N).prodMk ((measurable_pi_apply i).comp (hmeasR N))).aemeasurable
  have hX'sm : AEMeasurable (fun eta : OmegaHat => (omegaHat eta, Ghat eta (fprobe i))) nu :=
    (hmeas.prodMk (hmeasG i)).aemeasurable
  have hYsm : ∀ N, AEMeasurable (fun ω : BilateralField d =>
      (ω, (responseSolution (killedResponseSpace (Ω := Q) hP) (a ω (cutoff N))
        ((sobolevVolumeLoad (fprobe i)).comp
          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
      (chaosSampleLaw M).toMeasure :=
    fun N => (measurable_id.prodMk (hR N i)).aemeasurable
  have hY'sm : AEMeasurable (fun ω : BilateralField d => (ω, G ω (fprobe i)))
      (chaosSampleLaw M).toMeasure :=
    (measurable_id.prodMk hmeasψ).aemeasurable
  have hproj : Measurable (fun p : BilateralField d × (ℕ → DomainL2 Q) => (p.1, p.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hFN : ∀ N, Measurable (fun eta : OmegaHat => (omegaHatN N eta, responseHatN N eta)) :=
    fun N => (hmeasN N).prodMk (hmeasR N)
  have hGN : ∀ N, Measurable (fun ω : BilateralField d => (ω, fun j : ℕ =>
      (responseSolution (killedResponseSpace (Ω := Q) hP) (a ω (cutoff N))
        ((sobolevVolumeLoad (fprobe j)).comp
          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1)) :=
    fun N => measurable_id.prodMk (Measurable.of_eval fun j => hR N j)
  have hmap : ∀ N, Measure.map (fun eta : OmegaHat => (omegaHatN N eta, responseHatN N eta i))
        nu =
      Measure.map (fun ω : BilateralField d =>
        (ω, (responseSolution (killedResponseSpace (Ω := Q) hP) (a ω (cutoff N))
          ((sobolevVolumeLoad (fprobe i)).comp
            (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
        (chaosSampleLaw M).toMeasure := by
    intro N
    have hc := congrArg
      (Measure.map (fun p : BilateralField d × (ℕ → DomainL2 Q) => (p.1, p.2 i))) (hlaw N)
    rw [Measure.map_map hproj (hFN N), Measure.map_map hproj (hGN N)] at hc
    exact hc
  have hXlim : ∀ᵐ eta ∂nu, Tendsto (fun N => (omegaHatN N eta, responseHatN N eta i)) atTop
      (𝓝 (omegaHat eta, Ghat eta (fprobe i))) := by
    filter_upwards [hconv] with eta h
    exact h.1.prodMk_nhds (h.2 i)
  have hYlim : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, Tendsto (fun N =>
      (ω, (responseSolution (killedResponseSpace (Ω := Q) hP) (a ω (cutoff N))
        ((sobolevVolumeLoad (fprobe i)).comp
          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
      atTop (𝓝 (ω, G ω (fprobe i))) := by
    filter_upwards [hGlim] with ω h
    exact tendsto_const_nhds.prodMk_nhds ((h (fprobe i)).comp hcut.tendsto_atTop)
  have hpair : Measure.map (fun eta : OmegaHat => (omegaHat eta, Ghat eta (fprobe i))) nu =
      Measure.map (fun ω : BilateralField d => (ω, G ω (fprobe i)))
        (chaosSampleLaw M).toMeasure :=
    aux_limiting_local_energy_map_eq_of_ae_tendsto (ν := nu)
      (μ := (chaosSampleLaw M).toMeasure)
      (X := fun N eta => (omegaHatN N eta, responseHatN N eta i))
      (X' := fun eta => (omegaHat eta, Ghat eta (fprobe i)))
      (Y := fun N ω => (ω, (responseSolution (killedResponseSpace (Ω := Q) hP)
        (a ω (cutoff N))
        ((sobolevVolumeLoad (fprobe i)).comp
          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
      (Y' := fun ω => (ω, G ω (fprobe i)))
      (hX := hXsm) (hX' := hX'sm) (hY := hYsm) (hY' := hY'sm)
      (hlaw := hmap) (hXlim := hXlim) (hYlim := hYlim)
  exact aux_limiting_local_energy_ae_eq_of_map_graph (ν := nu)
    (μ := (chaosSampleLaw M).toMeasure)
    (A := omegaHat) (B := fun eta => Ghat eta (fprobe i))
    (hA := hmeas) (hB := hmeasG i)
    (ψ := fun ω => G ω (fprobe i)) (hψ := hmeasψ) (hlaw := hpair)

/-- Joint-law identification (joint-law identification, `mfd:sec-local-form`: "for a represented sequence,
conv_represented_sequence preserves the joint laws of the layers and the inverse-response coordinates;
their limits therefore have the same joint law as the original layers and their measurable limiting
inverse"). Last conjunct of limiting_local_energy for any measurable G that is the a.s. strong limit. -/
theorem aux_limiting_local_energy_joint_law {d : ℕ} (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (G : BilateralField d →
      (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGmeas : Measurable G)
    (hGlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun N => (responseSolution (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
        atTop (𝓝 (G omega f))) :
    let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
    let a : BilateralField d → ℕ → PositiveCoefficient Q :=
      fun omega N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr
    ∀ (cutoff : ℕ → ℕ), StrictMono cutoff →
      ∀ (fprobe : ℕ → DomainL2 Q), DenseRange fprobe →
      ∀ (OmegaHat : Type) [MeasurableSpace OmegaHat]
        (nu : Measure OmegaHat) [IsProbabilityMeasure nu],
      ∀ (omegaHatN : ℕ → OmegaHat → BilateralField d)
        (omegaHat : OmegaHat → BilateralField d)
        (responseHatN : ℕ → OmegaHat → ℕ → DomainL2 Q)
        (Ghat : OmegaHat → (DomainL2 Q →L[ℝ] DomainL2 Q)),
      (∀ N, Measurable (omegaHatN N)) → Measurable omegaHat →
      (∀ N,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measurable (responseHatN N))) →
      (∀ i,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measurable (fun eta => Ghat eta (fprobe i)))) →
      (∀ N,
        (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
          Measure.map (fun eta => (omegaHatN N eta, responseHatN N eta)) nu =
            Measure.map (fun omega : BilateralField d =>
              (omega,
                fun i : ℕ =>
                  (responseSolution (killedResponseSpace (Ω := Q) hP)
                      (a omega (cutoff N))
                      ((sobolevVolumeLoad (fprobe i)).comp
                        (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
              (chaosSampleLaw M).toMeasure)) →
      (∀ᵐ eta ∂nu,
        Tendsto (fun N => omegaHatN N eta) atTop (𝓝 (omegaHat eta)) ∧
          ∀ i, Tendsto (fun N => responseHatN N eta i) atTop
            (𝓝 (Ghat eta (fprobe i)))) →
      ∀ᵐ eta ∂nu,
        Ghat eta = G (omegaHat eta) ∧
          ∀ u : DomainL2 Q,
            limitFormEnergy (Ghat eta) u =
              limitFormEnergy (G (omegaHat eta)) u := by
  intro Q a cutoff hcut fprobe hdense OmegaHat _ nu _ omegaHatN omegaHat responseHatN Ghat
    hmeasN hmeas hmeasR hmeasG hlaw hconv
  have hprobe := aux_limiting_local_energy_joint_probe M H HI z r hr hP G hGmeas hGlim cutoff hcut
    fprobe hdense OmegaHat nu omegaHatN omegaHat responseHatN Ghat hmeasN hmeas hmeasR hmeasG hlaw hconv
  filter_upwards [ae_all_iff.2 hprobe] with eta h
  have hG : Ghat eta = G (omegaHat eta) :=
    ContinuousLinearMap.ext (congrFun
      (hdense.equalizer (Ghat eta).continuous (G (omegaHat eta)).continuous (funext h)))
  exact ⟨hG, fun u => by rw [hG]⟩
end


/-- The six per-sample clauses of limiting_local_energy for the operator limit `G0` supplied by
prop_killed_inverse on one sample (split out for the heartbeat budget). -/
theorem aux_limiting_local_energy_clauses {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (omega : BilateralField d) (K : ℝ) (hK : 0 < K)
    (hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (GNf : ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGNf : ∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNf n f =
      (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (G0 : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hG1 : Tendsto GNf atTop (𝓝 G0))
    (hGlow : ∀ (uN : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G0 u ≤ liminf (fun n => sInf {e : EReal |
        ∃ w : (killedResponseSpace hP).space, w.val.1 = uN n ∧
          e = (responseForm (killedResponseSpace hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) w w : EReal)}) atTop)
    (hGrec : ∀ u ∈ limitFormDomain G0, ∃ w : ℕ → (killedResponseSpace hP).space,
      Tendsto (fun n => ((w n).val.1, ((responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G0 u)))
    (hDFω : ∃ F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∀ u : DomainL2 (centeredCube z r hr),
        F.toClosedForm.energy u = limitFormEnergy G0 u) ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) :
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
    let a : BilateralField d → ℕ → PositiveCoefficient Q :=
      fun omega N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr
    let EN : BilateralField d → ℕ → DomainL2 Q → EReal :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph Q //
            (v : SobolevData Q).1 = u},
          ((sobolevCoefficientForm (a omega N)
              (v : SobolevData Q) (v : SobolevData Q) : ℝ) : EReal)
    (∀ f : DomainL2 Q,
        Tendsto
          (fun N =>
            (responseSolution (killedResponseSpace (Ω := Q) hP)
                (a omega N)
                ((sobolevVolumeLoad f).comp
                  (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G0 f))) ∧
      (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
        (∀ f : DomainL2 Q,
          Tendsto (fun N => inner ℝ f (uN N)) atTop
            (𝓝 (inner ℝ f u))) →
        limitFormEnergy (G0) u ≤
          liminf (fun N => EN omega N (uN N)) atTop) ∧
      (∀ u : DomainL2 Q,
        ∃ w : ℕ → DomainL2 Q,
          Tendsto w atTop (𝓝 u) ∧
            limsup (fun N => EN omega N (w N)) atTop ≤
              limitFormEnergy (G0) u) ∧
      (∃ Ccoer : ℝ, 0 < Ccoer ∧
        (∀ (N : ℕ) (v : killedSobolevGraph Q),
          _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v.val.1 ≤
            Ccoer * sobolevCoefficientForm (a omega N)
              v.val v.val) ∧
        (∀ u : DomainL2 Q,
          limitFormEnergy (G0) u ≠ (⊤ : EReal) →
          ∃ v : CubeFractionalL2 (k := 1) hd z r hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v.val 0 = u ∧
              (cubeFractionalL2Norm hd z r hr
                  _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v) ^ 2 ≤
                Ccoer * (limitFormEnergy (G0) u).toReal)) ∧
      (∃ F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (Q : Set (SpatialCoordinates d))),
        (∀ u : DomainL2 Q,
          F.toClosedForm.energy u = limitFormEnergy (G0) u) ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
      (∀ (phi : ℕ → ℕ), StrictMono phi →
        ∀ F : DomainL2 Q → EReal,
          (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
            (∀ f : DomainL2 Q,
              Tendsto (fun N => inner ℝ f (uN N)) atTop
                (𝓝 (inner ℝ f u))) →
            F u ≤
              liminf (fun N => EN omega (phi N) (uN N)) atTop) →
          (∀ u : DomainL2 Q,
            ∃ w : ℕ → DomainL2 Q,
              Tendsto w atTop (𝓝 u) ∧
                limsup (fun N => EN omega (phi N) (w N)) atTop ≤
                  F u) →
          F = limitFormEnergy (G0)) := by
  intro Q a EN
  have hlow : ∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G0 u ≤ liminf (fun N => EN omega N (uN N)) atTop := by
    intro uN u hw
    refine (hGlow uN u hw).trans (le_of_eq ?_)
    congr 1
    funext N
    exact (aux_limiting_local_energy_EN_eq_sInf M H HI omega N z r hr hP (uN N)).symm
  have hrec : ∀ u : DomainL2 Q, ∃ w : ℕ → DomainL2 Q, Tendsto w atTop (𝓝 u) ∧
      limsup (fun N => EN omega N (w N)) atTop ≤ limitFormEnergy G0 u := by
    intro u
    obtain ⟨w, hw, hlim⟩ := aux_limiting_local_energy_recovery_glue
      (fun v : (killedResponseSpace hP).space => v.val.1)
      (fun n v => responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) v v)
      (limitFormEnergy G0) (fun u hu => hGrec u hu) u
    refine ⟨w, hw, le_trans (le_of_eq ?_) hlim⟩
    congr 1
  refine ⟨fun f => ?_, hlow, hrec, ?_, hDFω, ?_⟩
  · have h := ((ContinuousLinearMap.apply ℝ (DomainL2 Q) f).continuous.tendsto G0).comp hG1
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
    exact hGNf N f
  · obtain ⟨Ccoer, hKC, hlimC⟩ := aux_limiting_local_energy_coercive_limit hd z r hr K hK
      (limitFormEnergy G0) (limitFormEnergy_nonneg G0)
      (fun u hu => by
        obtain ⟨wseq, hwseq⟩ := hGrec u hu
        refine ⟨fun n => (wseq n).val.1, fun n => responseForm (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (wseq n) (wseq n),
          hwseq.fst_nhds, hwseq.snd_nhds, fun n => ?_, fun n => ?_⟩
        · exact Sf.h1_fractional_finite z r hr
            ⟨(wseq n).val, killedSobolevGraph_le_weakSobolevGraph (wseq n).property⟩
        · exact hc n ⟨(wseq n).val, (wseq n).property⟩)
      (fun w u hw => aux_limiting_local_energy_seminorm_le_liminf hd z r hr _ w u hw)
    refine ⟨Ccoer, lt_of_lt_of_le hK hKC, fun N v => ?_, hlimC⟩
    exact (hc N v).trans (mul_le_mul_of_nonneg_right hKC (sobolevCoefficientForm_nonneg _ _))
  · intro phi hphi F hFlow hFrec
    exact aux_limiting_local_energy_mosco_unique (fun N => EN omega (phi N)) F
      (limitFormEnergy G0) hFlow hFrec
      (aux_limiting_local_energy_lower_subseq (EN omega) (limitFormEnergy G0) hlow phi hphi)
      (aux_limiting_local_energy_recovery_subseq (EN omega) (limitFormEnergy G0) hrec phi hphi)


/-- prop_killed_inverse on one sample, with the auxiliary proofs for its inputs (split out for the
heartbeat budget). -/
theorem aux_limiting_local_energy_pki {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (omega : BilateralField d) (K : ℝ) (hK : 0 < K)
    (hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (GNf : ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGNf : ∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNf n f =
      (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDc : (D : Set (DomainL2 (centeredCube z r hr))).Countable)
    (hDd : Dense (D : Set (DomainL2 (centeredCube z r hr))))
    (hDs : ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧
      HasCompactSupport fc ∧ tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc)
    (hresp : ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GNf n f.val)))
    (hmesh : ∀ φ : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → (killedResponseSpace hP).space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) :
    ∃ G0 : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
      Tendsto GNf atTop (𝓝 G0) ∧
      (∀ x y : DomainL2 (centeredCube z r hr), inner ℝ (G0 x) y = inner ℝ x (G0 y)) ∧
      Function.Injective G0 ∧
      (∃ Rroot : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        (∀ x y : DomainL2 (centeredCube z r hr),
          inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
        (∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (Rroot x)) ∧
        Rroot.comp Rroot = G0 ∧ limitFormDomain G0 = Set.range Rroot) ∧
      (∃ EForm : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ u : DomainL2 (centeredCube z r hr),
          EForm.toClosedForm.energy u = limitFormEnergy G0 u) ∧
        _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions EForm) ∧
      (∀ (uN : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr)),
        (∀ f : DomainL2 (centeredCube z r hr),
          Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
        limitFormEnergy G0 u ≤ liminf (fun n => sInf {e : EReal |
          ∃ w : (killedResponseSpace hP).space, w.val.1 = uN n ∧
            e = (responseForm (killedResponseSpace hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) w w : EReal)}) atTop) ∧
      (∀ u ∈ limitFormDomain G0, ∃ w : ℕ → (killedResponseSpace hP).space,
        Tendsto (fun n => ((w n).val.1, ((responseForm (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) : ℝ) : EReal))) atTop
          (𝓝 (u, limitFormEnergy G0 u))) ∧
      (∀ u ∈ limitFormDomain G0, ∀ ε : ℝ, 0 < ε →
        ∃ f : DomainL2 (centeredCube z r hr),
          (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) ∧
          ‖u - G0 f‖ ≤ ε ∧ limitFormEnergy G0 (u - G0 f) ≤ ((ε : ℝ) : EReal)) := by
  have hpki := prop_killed_inverse d hd z r hr (killedResponseSpace hP) rfl
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
    (fun n T hT u => hcontract z r hr _ rfl _ T hT u)
    GNf hGNf Interp
    (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * K)
    (mul_pos (centeredCube_volume_pos _ _) hK)
    (aux_limiting_local_energy_hCoercive hd Sf z r hr hP _ K hc)
    D hDc hDd hDs hresp
    (fun n u => sInf {e : EReal | ∃ w : (killedResponseSpace hP).space, w.val.1 = u ∧
      e = (responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) w w : EReal)})
    (fun n u => rfl) hmesh
  obtain ⟨G0, ⟨hG1, hroot, hform, ⟨hGlow, hGrec⟩, hdense⟩, _huniq⟩ := hpki
  exact ⟨G0, hG1.1, hG1.2.2.1, hG1.2.2.2.2, hroot, hform, hGlow, hGrec, hdense⟩


/-- The almost-sure block of limiting_local_energy for any `Gf` that picks the operator limit
whenever it exists (split out for the heartbeat budget). -/
theorem aux_limiting_local_energy_ae_block {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (GNf : BilateralField d → ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGNf : ∀ (omega : BilateralField d) (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNf omega n f =
      (responseSolution (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (Gf : BilateralField d → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)))
    (hGf : ∀ omega, (∃ G' : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
      Tendsto (GNf omega) atTop (𝓝 G')) → Tendsto (GNf omega) atTop (𝓝 (Gf omega)))
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDc : (D : Set (DomainL2 (centeredCube z r hr))).Countable)
    (hDd : Dense (D : Set (DomainL2 (centeredCube z r hr))))
    (hDs : ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧
      HasCompactSupport fc ∧ tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc)
    (hev1 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData (centeredCube z r hr)).1 ≤
          K * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (hev2 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GNf omega n f.val)))
    (hev3 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ φ : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → (killedResponseSpace hP).space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm (killedResponseSpace hP)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε))
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hevRCU :
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kreg : ℝ, 0 < Kreg ∧
        ∀ N : ℕ, aux_limiting_local_energy_DirProp z r hr
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) Kreg) ∧
      (∃ tc : ℕ → ℕ, StrictMono tc ∧ ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        aux_limiting_local_energy_HCUTProp M H z r hr hP tc omega) ∧
      (∃ tu : ℕ → ℕ, StrictMono tu ∧ ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        aux_limiting_local_energy_HUNIFProp M H HI z r hr hP tu omega)) :
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
    let a : BilateralField d → ℕ → PositiveCoefficient Q :=
      fun omega N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr
    let EN : BilateralField d → ℕ → DomainL2 Q → EReal :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph Q //
            (v : SobolevData Q).1 = u},
          ((sobolevCoefficientForm (a omega N)
              (v : SobolevData Q) (v : SobolevData Q) : ℝ) : EReal)
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ f : DomainL2 Q,
        Tendsto
          (fun N =>
            (responseSolution (killedResponseSpace (Ω := Q) hP)
                (a omega N)
                ((sobolevVolumeLoad f).comp
                  (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1)
          atTop (𝓝 (Gf omega f))) ∧
      (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
        (∀ f : DomainL2 Q,
          Tendsto (fun N => inner ℝ f (uN N)) atTop
            (𝓝 (inner ℝ f u))) →
        limitFormEnergy (Gf omega) u ≤
          liminf (fun N => EN omega N (uN N)) atTop) ∧
      (∀ u : DomainL2 Q,
        ∃ w : ℕ → DomainL2 Q,
          Tendsto w atTop (𝓝 u) ∧
            limsup (fun N => EN omega N (w N)) atTop ≤
              limitFormEnergy (Gf omega) u) ∧
      (∃ Ccoer : ℝ, 0 < Ccoer ∧
        (∀ (N : ℕ) (v : killedSobolevGraph Q),
          _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v.val.1 ≤
            Ccoer * sobolevCoefficientForm (a omega N)
              v.val v.val) ∧
        (∀ u : DomainL2 Q,
          limitFormEnergy (Gf omega) u ≠ (⊤ : EReal) →
          ∃ v : CubeFractionalL2 (k := 1) hd z r hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v.val 0 = u ∧
              (cubeFractionalL2Norm hd z r hr
                  _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v) ^ 2 ≤
                Ccoer * (limitFormEnergy (Gf omega) u).toReal)) ∧
      (∃ F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (Q : Set (SpatialCoordinates d))),
        (∀ u : DomainL2 Q,
          F.toClosedForm.energy u = limitFormEnergy (Gf omega) u) ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
      (∀ (phi : ℕ → ℕ), StrictMono phi →
        ∀ F : DomainL2 Q → EReal,
          (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
            (∀ f : DomainL2 Q,
              Tendsto (fun N => inner ℝ f (uN N)) atTop
                (𝓝 (inner ℝ f u))) →
            F u ≤
              liminf (fun N => EN omega (phi N) (uN N)) atTop) →
          (∀ u : DomainL2 Q,
            ∃ w : ℕ → DomainL2 Q,
              Tendsto w atTop (𝓝 u) ∧
                limsup (fun N => EN omega (phi N) (w N)) atTop ≤
                  F u) →
          F = limitFormEnergy (Gf omega))) := by
  intro Q a EN
  obtain ⟨tc, htc, hcutAE⟩ := hevRCU.2.1
  obtain ⟨tu, htu, hunifAE⟩ := hevRCU.2.2
  filter_upwards [hev1, hev2, hev3, hevRCU.1, hcutAE, hunifAE] with omega h1 h2 h3 h5 h6 h7
  obtain ⟨K, hK, hc⟩ := h1
  obtain ⟨G0, hGtend, hGsymm0, hGinj, hroot, hform, hGlow, hGrec, hdense⟩ :=
    aux_limiting_local_energy_pki hd Sf Interp hcontract M H z r hr hP omega K hK hc
      (GNf omega) (hGNf omega) D hDc hDd hDs h2 h3
  obtain ⟨Rroot, hRsymm, hRpos, hRcomp, hRdom⟩ := hroot
  obtain ⟨EForm, hEForm, hHNC⟩ := hform
  have hGeq : Gf omega = G0 := tendsto_nhds_unique (hGf omega ⟨G0, hGtend⟩) hGtend
  rw [hGeq]
  obtain ⟨Kreg, hKregPos, hDreg⟩ := h5
  have hCoerv := aux_limiting_local_energy_hCoercive hd Sf z r hr hP _ K hc
  have hunifInst := h7 (fun n => GNf omega (tu n)) G0
    (fun n f => hGNf omega (tu n) f) (hGtend.comp htu.tendsto_atTop) EForm hEForm
  have hDFω := aux_limiting_local_energy_limit_dirichlet_form d hd z r hr hP
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (tc n) z hr)
    (fun n => GNf omega (tc n)) (fun n f => hGNf omega (tc n) f) G0
    Rroot (hGtend.comp htc.tendsto_atTop) hGsymm0 hGinj hRsymm hRcomp hRdom EForm hEForm hHNC
    (aux_prop_as_forms_subseq_lower (killedResponseSpace hP)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
      (GNf omega) (hGNf omega) G0 hGtend tc htc)
    (aux_prop_as_forms_recovery_subseq (fun v : (killedResponseSpace hP).space => v.val.1)
      (fun n v => responseForm (killedResponseSpace hP)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) v v)
      (limitFormEnergy G0) (limitFormDomain G0) hGrec tc htc) hdense
    (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * K)
    (mul_nonneg (centeredCube_volume_pos _ _).le hK.le) (fun n => hCoerv (tc n))
    Interp Kreg hKregPos.le (fun n => hDreg (tc n))
    (BD z r hr EForm) (BDQ z r hr EForm) h6 hunifInst
  exact aux_limiting_local_energy_clauses hd Sf M H HI z r hr hP omega K hK hc (GNf omega)
    (hGNf omega) G0 hGtend hGlow hGrec hDFω


/-- The response-bank event: a.s. convergence of the matrix elements on the smooth dense family
(prop_as_response_bank; split out for the heartbeat budget). -/
theorem aux_limiting_local_energy_bank_event (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D0 : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (D : Submodule ℚ (DomainL2 (centeredCube z r hr))),
        (D : Set (DomainL2 (centeredCube z r hr))).Countable →
        (∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧
          HasCompactSupport fc ∧ tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ (GNf : BilateralField d → ℕ → (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))),
        (∀ (omega : BilateralField d) (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNf omega n f =
          (responseSolution (killedResponseSpace hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr)
            ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GNf omega n f.val)) := by
  obtain ⟨Cresp, Bset, δ2, Cgeom, _hCresp, _hBne, _h128, _hB1, hδ2, _hδ21, _hCgeom, hbank⟩ :=
    prop_as_response_bank d hd Jc Pc Xc Sf W Cp D0 hES Step Dbase Interp
  refine ⟨δ2, hδ2, ?_⟩
  intro M Sreg It H HI hd2 z r hr htri hP D hDc hDs GNf hGNf
  have : Countable D := hDc.to_subtype
  have hKDex : ∀ p : D, ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |(p.val : SpatialCoordinates d → ℝ) x| ≤ K := by
    intro p
    obtain ⟨fc, hfs, hfc, _hsub, hae⟩ := hDs p
    obtain ⟨C, hC⟩ := hfs.continuous.bounded_above_of_compact_support hfc
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    filter_upwards [hae] with x hx
    rw [hx]
    have hCx := hC x
    rw [Real.norm_eq_abs] at hCx
    exact hCx.trans (le_max_left _ _)
  choose KD hKD0 hKD using hKDex
  have hbankM := (hbank M Sreg It hd2).2 H HI D
    (fun _ => z) (fun _ => r) (fun _ => hr) (fun _ => htri)
    (fun _ _ => (0 : ℝ)) (fun _ => contDiff_const)
    (fun p => p.val) (fun _ => 0) KD (fun _ => 0) hKD0 (fun _ => le_rfl) hKD
    (fun _ => by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))] with x hx
      rw [abs_nonpos_iff]
      simpa using hx)
    (fun _ => by
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))]
      simp)
    (fun _ => 0)
  obtain ⟨Rlim, -, -, -, -, hae, -⟩ := hbankM
  exact hae.mono fun omega h2 f => aux_limiting_local_energy_hresponse_of_tendsto (killedResponseSpace hP)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega n z hr) (GNf omega) (hGNf omega) f.val _
    (h2 f true 1)

/-- Purely arithmetic helper (same shape/proof as `aux_prop_as_forms_delta4_le`): split a single
`x ≤ min 1 (min δ1 (min δ2 (min δ3 δ4)))` bound into its four individual `min 1 δi` bounds. Pulled
out to a standalone declaration so `limiting_local_energy`'s own already-large proof does not have
to elaborate the nested `min_le_left`/`min_le_right` combinator terms itself (heartbeat budget). -/
theorem aux_limiting_local_energy_delta4_le (x δ1 δ2 δ3 δ4 : ℝ)
    (h : x ≤ min 1 (min δ1 (min δ2 (min δ3 δ4)))) :
    x ≤ min 1 δ1 ∧ x ≤ min 1 δ2 ∧ x ≤ min 1 δ3 ∧ x ≤ min 1 δ4 := by
  have h1 : x ≤ 1 := h.trans (min_le_left _ _)
  have h2 := h.trans (min_le_right _ _)
  refine ⟨le_min h1 (h2.trans (min_le_left _ _)),
    le_min h1 (h2.trans ((min_le_right _ _).trans (min_le_left _ _))),
    le_min h1 (h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))),
    le_min h1 (h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))⟩

/-- The `lem_as_regularity` a.e. event (`hev5`), computed away from `limiting_local_energy`'s own
already-large proof (heartbeat budget: adding this directly to that declaration -- itself already
split as far as `aux_limiting_local_energy_ae_block`/`aux_limiting_local_energy_bank_event` --
pushed it over the default heartbeat limit). Same pattern as `aux_limiting_local_energy_bank_
event`: own `delta0`, own `∀ M ... z r hr htri hP` clause, producing the a.e. fact
`aux_limiting_local_energy_ae_block` consumes as `hev5`.

( `HCUT`/`HUNIF` used to be bundled in here as `hev6`/
`hev7`, taking a closed ∀-model shape as parameters. `HCUT`/`HUNIF` are now
PER-MODEL principal binders of `limiting_local_energy` itself (threaded under `hdelta`, next to
`Rm`/`Sreg`/`It`), so they are no longer available here as a standing, model-independent input --
this helper keeps only the `lem_as_regularity` part it can still supply unconditionally; the
principal now builds `hev6`/`hev7` itself, directly from its own per-model `HCUT`/`HUNIF`, right
after `intro`.) -/
theorem aux_limiting_local_energy_reg_cut_unif_event (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D0 : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kreg : ℝ, 0 < Kreg ∧
        ∀ N : ℕ, aux_limiting_local_energy_DirProp z r hr
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) Kreg := by
  obtain ⟨δreg, hδreg, hReg⟩ := lem_as_regularity d hd Jc Pc Xc W D0 Cp Sf Step Dbase Interp (1 / 2) (3 / 4)
    ((d : ℝ) - 3 / 4) ((d : ℝ) - 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by linarith) (by linarith)
  refine ⟨δreg, hδreg, ?_⟩
  intro M Rm Sreg It H HI hdelta z r hr htri hP
  refine (hReg M Rm Sreg It H HI hdelta z r hr).mono fun omega h => ?_
  obtain ⟨Kreg, hKregPos, hDirNeu⟩ := h
  exact ⟨Kreg, hKregPos, fun N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hbeq hsolve =>
    ((hDirNeu N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hbeq hsolve).2⟩

theorem aux_limiting_local_energy_hDex_helper {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) :
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
  exact aux_limiting_local_energy_exists_smooth_dense_submodule z r hr
    (aux_limiting_local_energy_dense_smooth_tsupport_subset hopen hvol
      (fun {_g} hg hc {_ε} hε => aux_limiting_local_energy_exists_contDiff_tsupport_subset_eLpNorm_sub_le
        hopen hvol hg hc hε))
    (aux_limiting_local_energy_countable_dense_submodule_le z r hr)



noncomputable def aux_limiting_local_energy_Gfun {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    (GNf : BilateralField d → ℕ → (DomainL2 Q →L[ℝ] DomainL2 Q)) :
    BilateralField d → (DomainL2 Q →L[ℝ] DomainL2 Q) :=
  open Classical in
  fun omega =>
    if h : ∃ G' : DomainL2 Q →L[ℝ] DomainL2 Q, Tendsto (GNf omega) atTop (𝓝 G') then
      Classical.choose h else 0

/-- The per-cube specialisation of the PER-MODEL `HCUT`/`HUNIF` principal binders, computed away
from `limiting_local_energy`'s own already-large proof (heartbeat budget: doing the
`simp only [aux_limiting_local_energy_HCUT_prop/HUNIF_prop]` unfold-then-`.mono` step inline, in a
declaration already near the 200000 default from unrelated `Gfun`/mesh content, timed out; moving
it to its own small declaration -- consumed via `have := ...; obtain := that`, not a direct
`obtain := aux_limiting_local_energy_hcut_hunif_event ...` because the intermediate `have` avoids restating the large goal -- keeps the
principal's own tactic sequence cheap). -/
theorem aux_limiting_local_energy_hcut_hunif_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (HCUT : aux_limiting_local_energy_HCUT_prop M H)
    (HUNIF : aux_limiting_local_energy_HUNIF_prop M H HI)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (htri : ∃ j : ℤ, r = (3 : ℝ) ^ j)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖) :
    (∃ tc : ℕ → ℕ, StrictMono tc ∧ ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_limiting_local_energy_HCUTProp M H z r hr hP tc omega) ∧
    (∃ tu : ℕ → ℕ, StrictMono tu ∧ ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_limiting_local_energy_HUNIFProp M H HI z r hr hP tu omega) := by
  obtain ⟨tc, htc, h6⟩ := HCUT id strictMono_id
  obtain ⟨tu, htu, h7⟩ := HUNIF id strictMono_id
  exact ⟨⟨tc, htc, h6.mono (fun omega hh => hh z r hr htri hP)⟩,
    ⟨tu, htu, h7.mono (fun omega hh => hh z r hr htri hP)⟩⟩



theorem limiting_local_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (HCUT : aux_limiting_local_energy_HCUT_prop M H)
          (HUNIF : aux_limiting_local_energy_HUNIF_prop M H HI),
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          (∃ j : ℤ, r = (3 : ℝ) ^ j) →
          (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
            ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
              K * ‖subspaceGradient
                (killedSobolevGraph (centeredCube z r hr)) u‖) →
          let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
          let a : BilateralField d → ℕ → PositiveCoefficient Q :=
            fun omega N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr
          let EN : BilateralField d → ℕ → DomainL2 Q → EReal :=
            fun omega N u =>
              ⨅ v : {v : killedSobolevGraph Q //
                  (v : SobolevData Q).1 = u},
                ((sobolevCoefficientForm (a omega N)
                    (v : SobolevData Q) (v : SobolevData Q) : ℝ) : EReal)
          ∃ G : BilateralField d →
              (DomainL2 Q →L[ℝ] DomainL2 Q),
            Measurable G ∧
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              (∀ f : DomainL2 Q,
                Tendsto
                  (fun N =>
                    (responseSolution (killedResponseSpace (Ω := Q) hP)
                        (a omega N)
                        ((sobolevVolumeLoad f).comp
                          (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1)
                  atTop (𝓝 (G omega f))) ∧
              (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
                (∀ f : DomainL2 Q,
                  Tendsto (fun N => inner ℝ f (uN N)) atTop
                    (𝓝 (inner ℝ f u))) →
                limitFormEnergy (G omega) u ≤
                  liminf (fun N => EN omega N (uN N)) atTop) ∧
              (∀ u : DomainL2 Q,
                ∃ w : ℕ → DomainL2 Q,
                  Tendsto w atTop (𝓝 u) ∧
                    limsup (fun N => EN omega N (w N)) atTop ≤
                      limitFormEnergy (G omega) u) ∧
              (∃ Ccoer : ℝ, 0 < Ccoer ∧
                (∀ (N : ℕ) (v : killedSobolevGraph Q),
                  _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr
                      _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v.val.1 ≤
                    Ccoer * sobolevCoefficientForm (a omega N)
                      v.val v.val) ∧
                (∀ u : DomainL2 Q,
                  limitFormEnergy (G omega) u ≠ (⊤ : EReal) →
                  ∃ v : CubeFractionalL2 (k := 1) hd z r hr
                      _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
                    v.val 0 = u ∧
                      (cubeFractionalL2Norm hd z r hr
                          _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v) ^ 2 ≤
                        Ccoer * (limitFormEnergy (G omega) u).toReal)) ∧
              (∃ F : _root_.SubdiffusiveProcess.DirichletForm
                  (volume.restrict (Q : Set (SpatialCoordinates d))),
                (∀ u : DomainL2 Q,
                  F.toClosedForm.energy u = limitFormEnergy (G omega) u) ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
              (∀ (phi : ℕ → ℕ), StrictMono phi →
                ∀ F : DomainL2 Q → EReal,
                  (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
                    (∀ f : DomainL2 Q,
                      Tendsto (fun N => inner ℝ f (uN N)) atTop
                        (𝓝 (inner ℝ f u))) →
                    F u ≤
                      liminf (fun N => EN omega (phi N) (uN N)) atTop) →
                  (∀ u : DomainL2 Q,
                    ∃ w : ℕ → DomainL2 Q,
                      Tendsto w atTop (𝓝 u) ∧
                        limsup (fun N => EN omega (phi N) (w N)) atTop ≤
                          F u) →
                  F = limitFormEnergy (G omega))) ∧
            (∀ (Omega : Type) [MeasurableSpace Omega]
                (nu : Measure Omega)
                (Psi : Omega → BilateralField d),
              MeasurePreserving Psi nu (chaosSampleLaw M).toMeasure →
              ∀ᵐ eta ∂nu,
                ∀ (phi : ℕ → ℕ), StrictMono phi →
                  ∀ F : DomainL2 Q → EReal,
                    (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
                      (∀ f : DomainL2 Q,
                        Tendsto (fun N => inner ℝ f (uN N)) atTop
                          (𝓝 (inner ℝ f u))) →
                      F u ≤
                        liminf
                          (fun N => EN (Psi eta) (phi N) (uN N)) atTop) →
                    (∀ u : DomainL2 Q,
                      ∃ w : ℕ → DomainL2 Q,
                        Tendsto w atTop (𝓝 u) ∧
                          limsup
                              (fun N => EN (Psi eta) (phi N) (w N)) atTop ≤
                            F u) →
                    F = limitFormEnergy (G (Psi eta))) ∧
            (∀ (cutoff : ℕ → ℕ), StrictMono cutoff →
              ∀ (fprobe : ℕ → DomainL2 Q), DenseRange fprobe →
              ∀ (OmegaHat : Type) [MeasurableSpace OmegaHat]
                (nu : Measure OmegaHat) [IsProbabilityMeasure nu],
              ∀ (omegaHatN : ℕ → OmegaHat → BilateralField d)
                (omegaHat : OmegaHat → BilateralField d)
                (responseHatN : ℕ → OmegaHat → ℕ → DomainL2 Q)
                (Ghat : OmegaHat → (DomainL2 Q →L[ℝ] DomainL2 Q)),
              (∀ N, Measurable (omegaHatN N)) → Measurable omegaHat →
              (∀ N,
                (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
                  Measurable (responseHatN N))) →
              (∀ i,
                (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
                  Measurable (fun eta => Ghat eta (fprobe i)))) →
              (∀ N,
                (letI : MeasurableSpace (DomainL2 Q) := borel (DomainL2 Q);
                  Measure.map (fun eta => (omegaHatN N eta, responseHatN N eta)) nu =
                    Measure.map (fun omega : BilateralField d =>
                      (omega,
                        fun i : ℕ =>
                          (responseSolution (killedResponseSpace (Ω := Q) hP)
                              (a omega (cutoff N))
                              ((sobolevVolumeLoad (fprobe i)).comp
                                (killedResponseSpace (Ω := Q) hP).space.subtypeL)).val.1))
                      (chaosSampleLaw M).toMeasure)) →
              (∀ᵐ eta ∂nu,
                Tendsto (fun N => omegaHatN N eta) atTop (𝓝 (omegaHat eta)) ∧
                  ∀ i, Tendsto (fun N => responseHatN N eta i) atTop
                    (𝓝 (Ghat eta (fprobe i)))) →
              ∀ᵐ eta ∂nu,
                Ghat eta = G (omegaHat eta) ∧
                  ∀ u : DomainL2 Q,
                    limitFormEnergy (Ghat eta) u =
                      limitFormEnergy (G (omegaHat eta)) u) := by
  classical
  -- `have := bigLemma args` then `obtain := that`, not a direct `obtain := bigLemma args`, for
  
  -- `obtain := bigLemma args` vs `have := bigLemma args; obtain := that` finding).
  have hlac := lem_as_coarse d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp 1 (3 / 4)
    ⟨one_pos, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  obtain ⟨δ1, hδ1, hcoarse⟩ := hlac
  have hbe := aux_limiting_local_energy_bank_event d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨δ2, hδ2, hbankev⟩ := hbe
  have hrcu := aux_limiting_local_energy_reg_cut_unif_event d hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  obtain ⟨δ3, hδ3, hRCU⟩ := hrcu
  -- δ4: the repaired `aux_limiting_local_energy_hmesh`'s own small-disorder threshold
  
  -- Kept as the bare (irreducible) expression rather than a `set`/`let`-abstracted local: `set`
  -- would traverse this proof's huge outer `∃ delta0, ...` goal looking for folds, and a `let`
  -- local costs an extra `Meta.letToHave` pass on every later tactic step (the exact heartbeat
  
  have hδ4 : 0 < aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp :=
    aux_limiting_local_energy_hmesh_delta0_pos hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨min δ1 (min δ2 (min δ3 (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp))),
    lt_min hδ1 (lt_min hδ2 (lt_min hδ3 hδ4)), ?_⟩
  intro M Rm Sreg It H HI hdelta HCUT HUNIF z r hr htri hP Q a EN
  have hd4le := aux_limiting_local_energy_delta4_le M.delta δ1 δ2 δ3
    (aux_limiting_local_energy_hmesh_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp) hdelta
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hd4le
  -- the actual cutoff inverse operators and their limit, defined everywhere
  have hGNex : ∀ (omega : BilateralField d) (n : ℕ), ∃ T : DomainL2 Q →L[ℝ] DomainL2 Q,
      ∀ f : DomainL2 Q, T f = (responseSolution (killedResponseSpace hP) (a omega n)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1 :=
    fun omega n => (existsUnique_volumeResponseOperator _ _).exists
  choose GNf hGNf using hGNex
  -- `aux_limiting_local_energy_Gfun Q GNf` (top-level `def`, not a proof-local `let`): see that
  -- def's docstring for the heartbeat-budget rationale. `simp only [aux_limiting_local_energy_Gfun]`
  -- (a cheap syntactic unfold of a named top-level def) is used exactly where the old
  -- `simp only [Gfun]` was, in place of `show`/`change` (a full `isDefEq` check).
  have hmeas : Measurable (aux_limiting_local_energy_Gfun Q GNf) := by
    unfold aux_limiting_local_energy_Gfun
    exact aux_limiting_local_energy_measurable_limit hd M H HI z r hr hP GNf hGNf
  -- the countable dense smooth family on the cube (own declaration, heartbeat budget)
  have hDex := aux_limiting_local_energy_hDex_helper z r hr
  -- renamed from `D` to `Dq` (countable dense ℚ-submodule witness): the standing input `D`
  -- (`lane4_deterministic_good_scale_input`, this theorem's own header binder) is needed
  -- unshadowed below by `aux_limiting_local_energy_hmesh`'s repaired call, matching the same
  -- rename already used for this exact collision in `prop_as_forms_assembly3`.
  obtain ⟨Dq, hDc, hDd, hDs⟩ := hDex
  have hev1 := hcoarse M Rm Sreg It H HI hd1 z r hr htri
  have hev3 := aux_limiting_local_energy_hmesh hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp M Rm Sreg It H HI hd4
    z r hr htri hP
  have hev5 := hRCU M Rm Sreg It H HI hd3 z r hr htri hP
  -- `hev6`/`hev7`: the per-model `HCUT`/`HUNIF` principal binders, specialised to this cube, via
  -- the own small declaration `aux_limiting_local_energy_hcut_hunif_event` (heartbeat budget: see
  -- that theorem's docstring). `have := ...` then `obtain := that`, not a direct
  -- `obtain := aux_limiting_local_energy_hcut_hunif_event ...`.
  have hev67 := aux_limiting_local_energy_hcut_hunif_event M H HI HCUT HUNIF z r hr htri hP
  obtain ⟨hev6, hev7⟩ := hev67
  have hev2 := hbankev M Sreg It H HI hd2 z r hr htri hP Dq hDc hDs GNf hGNf
  have hev1' : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          K * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) :=
    hev1.mono fun omega h1 => by
      obtain ⟨K, hK, hKall⟩ := h1
      exact ⟨K, hK, (hKall true).2.1⟩
  have hGf : ∀ omega, (∃ G' : DomainL2 Q →L[ℝ] DomainL2 Q,
      Tendsto (GNf omega) atTop (𝓝 G')) →
      Tendsto (GNf omega) atTop (𝓝 (aux_limiting_local_energy_Gfun Q GNf omega)) := by
    intro omega hex
    unfold aux_limiting_local_energy_Gfun
    simp only [dite_eq_left hex]
    exact Classical.choose_spec hex
  have hA := aux_limiting_local_energy_ae_block hd Sf Interp hcontract M H HI z r hr hP GNf hGNf
    (aux_limiting_local_energy_Gfun Q GNf) hGf Dq hDc hDd hDs hev1' hev2 hev3 BD BDQ
    ⟨hev5, hev6, hev7⟩
  refine ⟨aux_limiting_local_energy_Gfun Q GNf, hmeas, hA, ?_, ?_⟩
  · -- measure-preserving representations
    intro Omega _ nu Psi hPsi
    exact hPsi.quasiMeasurePreserving.ae (hA.mono fun omega h => h.2.2.2.2.2)
  · -- joint-law identification
    exact aux_limiting_local_energy_joint_law hd M H HI z r hr hP
      (aux_limiting_local_energy_Gfun Q GNf) hmeas (hA.mono fun omega h => h.1)

end SubdiffusiveProcess.Paper

