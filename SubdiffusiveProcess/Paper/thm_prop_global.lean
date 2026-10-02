import SubdiffusiveProcess.Paper.thm_prop_base
import SubdiffusiveProcess.Paper.thm_prop_env
import SubdiffusiveProcess.Paper.inputs_baseline_witness
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

/-- The set of environments on which a cutoff response-operator subsequence converges in operator
norm is measurable (operator-norm Cauchy set of strongly measurable maps into a complete space). -/
theorem aux_thm_prop_global_measurableSet_converges {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (NE : ℕ → ℕ) :
    MeasurableSet {β : BilateralField d |
      ∃ L : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        Tendsto (fun n => volumeResponseOperator S
          (Lane4.cutoffPositiveCoefficient model H β (NE n) z hr)) atTop (𝓝 L)} := by
  have hmeas : ∀ n m, Measurable (fun β : BilateralField d => dist
      (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient model H β (NE n) z hr))
      (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient model H β (NE m) z hr))) :=
    fun n m => measurable_dist_cutoffVolumeResponseOperator model H hH (NE n) (NE m) z r hr S
  have hset : {β : BilateralField d |
      ∃ L : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        Tendsto (fun n => volumeResponseOperator S
          (Lane4.cutoffPositiveCoefficient model H β (NE n) z hr)) atTop (𝓝 L)} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {β : BilateralField d | dist
        (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient model H β (NE n) z hr))
        (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient model H β (NE N) z hr)) <
          1 / ((k : ℝ) + 1)} := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro ⟨L, hL⟩ k
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hL.cauchySeq (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨N, fun n hn => hN n hn⟩
    · intro h
      refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun n hn => (hN n hn).trans hk⟩
  rw [hset]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_lt (hmeas n N) measurable_const

/-- **Proportionality for a fixed-field represented package whose family is global.**
Same conclusion as the root-limited `thm_prop`: for the two subsequential operator limits
`GE`, `GF` (along `NE`, `NF`) of the cutoff responses of one fixed field, on the whole family of
rational triadic cubes, `F = cE` with a deterministic constant `c ∈ [C₀⁻¹, C₀]`, and the endpoints
`m = M = c`.  It is the original-space proportionality `thm_prop_env` transferred to the
represented package: the limits `GE0`, `GF0` on the original space are the operator-norm limits of
the cutoff responses (they exist almost surely because the package converges almost surely and the
convergence set is measurable); the identification with `GE`, `GF` holds almost surely by
uniqueness of limits, and the conclusion is pulled back along the law of `field`. -/
theorem thm_prop_global
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd)
    (Step : Paper.cutoff_good_scale_input d)
    (W : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
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
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
        (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (_It : Paper.in_iteration d model I Sreg)
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m)
        (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ),
          (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
            ∃ i, z i = z' ∧ r i = r')
        (hNonzero : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega),
        ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧
          ∀ᵐ omega ∂P,
            (∀ i : ℕ,
              limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
              ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
                u ∈ limitFormDomain (GE i omega) →
                (limitFormEnergy (GF i omega) u).toReal =
                  c * (limitFormEnergy (GE i omega) u).toReal) ∧
            sSup (aux_thm_prop_lowerSet z r hr GE GF omega) = c ∧
            sInf (aux_thm_prop_upperSet z r hr GE GF omega) = c := by
  classical
  letI mb : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI bb : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨δ0, C0, hδ0, hC0, henv⟩ := thm_prop_env d hd I X Sob Step W Pin D Cp Interp hES
    (inputs_baseline_witness d hd) BD BDQ EM hcontract
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro ms bs
  have hms : ms = mb := @BorelSpace.measurable_eq _ _ ms bs
  subst ms
  intro model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint Rm Sreg It hrat hcomp
    hNonzero
  obtain ⟨hprob, hfm, hmap, hIR, ⟨hNE, hNF⟩, hS, hGN, hlim⟩ := hJoint
  haveI : IsProbabilityMeasure P := hprob
  let A : ∀ i, ℕ → BilateralField d →
      (DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i))) :=
    fun i N β => volumeResponseOperator (Sspace i)
      (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))
  have hGNA : ∀ i N ω, GN i N ω = A i N (field ω) := fun i N ω =>
    ContinuousLinearMap.ext fun f => by
      rw [hGN]
      exact (volumeResponseOperator_apply _ _ f).symm
  let GE0 : (i : ℕ) → BilateralField d →
      (DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i))) :=
    fun i β => if h : ∃ L, Tendsto (fun n => A i (NE n) β) atTop (𝓝 L) then h.choose else 0
  let GF0 : (i : ℕ) → BilateralField d →
      (DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i))) :=
    fun i β => if h : ∃ L, Tendsto (fun n => A i (NF n) β) atTop (𝓝 L) then h.choose else 0
  have hSE : ∀ i, MeasurableSet {β : BilateralField d | ∃ L, Tendsto (fun n => A i (NE n) β) atTop (𝓝 L)} :=
    fun i => aux_thm_prop_global_measurableSet_converges model H hIR.1 (z i) (r i) (hr i) (Sspace i) NE
  have hSF : ∀ i, MeasurableSet {β : BilateralField d | ∃ L, Tendsto (fun n => A i (NF n) β) atTop (𝓝 L)} :=
    fun i => aux_thm_prop_global_measurableSet_converges model H hIR.1 (z i) (r i) (hr i) (Sspace i) NF
  have hPE : ∀ᵐ ω ∂P, ∀ i, ∃ L, Tendsto (fun n => A i (NE n) (field ω)) atTop (𝓝 L) :=
    hlim.mono fun ω h i => ⟨GE i ω, by simpa only [hGNA] using (h i).1⟩
  have hPF : ∀ᵐ ω ∂P, ∀ i, ∃ L, Tendsto (fun n => A i (NF n) (field ω)) atTop (𝓝 L) :=
    hlim.mono fun ω h i => ⟨GF i ω, by simpa only [hGNA] using (h i).2⟩
  have hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (Lane4.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)) := by
    have h1 : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
        ∃ L, Tendsto (fun n => A i (NE n) β) atTop (𝓝 L) := by
      rw [← hmap, ae_all_iff]
      intro i
      exact (ae_map_iff hfm.aemeasurable (hSE i)).2 (hPE.mono fun ω h => h i)
    filter_upwards [h1] with β h i
    have hex := h i
    simp only [GE0, dif_pos hex]
    exact hex.choose_spec
  have hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (Lane4.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)) := by
    have h1 : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
        ∃ L, Tendsto (fun n => A i (NF n) β) atTop (𝓝 L) := by
      rw [← hmap, ae_all_iff]
      intro i
      exact (ae_map_iff hfm.aemeasurable (hSF i)).2 (hPF.mono fun ω h => h i)
    filter_upwards [h1] with β h i
    have hex := h i
    simp only [GF0, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨c, hc1, hc2, hae⟩ := henv model Rm Sreg It H hIR hmodel z r hr Sspace hS hrat hcomp
    NE NF hNE hNF GE0 GF0 hlimE hlimF
  have hae' : ∀ᵐ ω ∂P, ∀ i : ℕ,
      limitFormDomain (GE0 i (field ω)) = limitFormDomain (GF0 i (field ω)) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE0 i (field ω)) →
        (limitFormEnergy (GF0 i (field ω)) u).toReal =
          c * (limitFormEnergy (GE0 i (field ω)) u).toReal := by
    refine ae_of_ae_map hfm.aemeasurable (p := fun β => ∀ i : ℕ,
      limitFormDomain (GE0 i β) = limitFormDomain (GF0 i β) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE0 i β) →
        (limitFormEnergy (GF0 i β) u).toReal = c * (limitFormEnergy (GE0 i β) u).toReal) ?_
    rw [hmap]
    exact hae
  have hid : ∀ᵐ ω ∂P, ∀ i, GE0 i (field ω) = GE i ω ∧ GF0 i (field ω) = GF i ω := by
    filter_upwards [hlim] with ω h i
    have hE : Tendsto (fun n => A i (NE n) (field ω)) atTop (𝓝 (GE i ω)) := by
      simpa only [hGNA] using (h i).1
    have hF : Tendsto (fun n => A i (NF n) (field ω)) atTop (𝓝 (GF i ω)) := by
      simpa only [hGNA] using (h i).2
    have hexE : ∃ L, Tendsto (fun n => A i (NE n) (field ω)) atTop (𝓝 L) := ⟨_, hE⟩
    have hexF : ∃ L, Tendsto (fun n => A i (NF n) (field ω)) atTop (𝓝 L) := ⟨_, hF⟩
    refine ⟨?_, ?_⟩
    · simp only [GE0, dif_pos hexE]
      exact tendsto_nhds_unique hexE.choose_spec hE
    · simp only [GF0, dif_pos hexF]
      exact tendsto_nhds_unique hexF.choose_spec hF
  refine ⟨c, hc1, hc2, ?_⟩
  filter_upwards [hae', hid, hNonzero] with ω h1 h2 h3
  have hprop : ∀ i : ℕ,
      limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE i ω) →
        (limitFormEnergy (GF i ω) u).toReal = c * (limitFormEnergy (GE i ω) u).toReal := by
    intro i
    have h := h1 i
    rw [(h2 i).1, (h2 i).2] at h
    exact h
  exact ⟨hprop, (thm_prop_base z r hr GE GF c ω hprop h3).1,
    (thm_prop_base z r hr GE GF c ω hprop h3).2⟩

end Paper
