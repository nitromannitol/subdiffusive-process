module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.thm_c1_cube_positive_energy
public import SubdiffusiveProcess.Paper.thm_prop_env_energy
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_limit_transfer
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_uniqueness
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources
public import SubdiffusiveProcess.Sobolev.LimitFormUniqueness
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_uniqueness_actual
public import SubdiffusiveProcess.Paper.limit_form_package_side

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- The two-sided energy comparison of the represented limits transfers to the original-space limits. -/
theorem thm_prop_env_transfer
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)))
    (hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hid : ∀ᵐ ω ∂P, ∀ i, GE i ω = GE0 i (field ω) ∧ GF i ω = GF0 i (field ω))
    (hsn : ∀ᵐ omega ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hord : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal) :
    ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      limitFormDomain (GE0 i β) = limitFormDomain (GF0 i β) ∧
      ∀ u ∈ limitFormDomain (GE0 i β),
        m * (limitFormEnergy (GE0 i β) u).toReal ≤ (limitFormEnergy (GF0 i β) u).toReal ∧
        (limitFormEnergy (GF0 i β) u).toReal ≤ M * (limitFormEnergy (GE0 i β) u).toReal := by
  classical
  have hmpq : Measure.QuasiMeasurePreserving field P (chaosSampleLaw model).toMeasure :=
    hmp.quasiMeasurePreserving
  -- (1) On the represented space: pointwise quadratic-form inequality a.e.
  have hq : ∀ᵐ ω ∂P, ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      M⁻¹ * inner ℝ x (GE0 i (field ω) x) ≤ inner ℝ x (GF0 i (field ω) x) ∧
      inner ℝ x (GF0 i (field ω) x) ≤ m⁻¹ * inner ℝ x (GE0 i (field ω) x) := by
    filter_upwards [hord, hsn, hid] with ω hordω hsnω hidω
    intro i x
    obtain ⟨⟨hsG, hpG⟩, hsF, hpF⟩ := hsnω i
    have hsG' : ∀ x y, inner ℝ x (GE i ω y) = inner ℝ y (GE i ω x) := fun x y => by
      rw [real_inner_comm]; exact hsG y x
    have hsF' : ∀ x y, inner ℝ x (GF i ω y) = inner ℝ y (GF i ω x) := fun x y => by
      rw [real_inner_comm]; exact hsF y x
    have hres := (aux_thm_prop_env_compare_to_order (GE i ω) (GF i ω) hsG' hpG hsF' hpF m M hm hM
      (hordω i)) x
    rw [show GE i ω = GE0 i (field ω) from (hidω i).1,
        show GF i ω = GF0 i (field ω) from (hidω i).2] at hres
    exact hres
  -- (2) a.e. limits indexed per `i`
  have hlimE' : ∀ i, ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)) := by
    intro i
    filter_upwards [hlimE] with β hβ
    exact hβ i
  have hlimF' : ∀ i, ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)) := by
    intro i
    filter_upwards [hlimF] with β hβ
    exact hβ i
  -- Measurability of the quadratic forms on the original space
  have hmeasE : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      AEMeasurable (fun β => inner ℝ x (GE0 i β x)) (chaosSampleLaw model).toMeasure := by
    intro i x
    refine aux_env_inner_aemeasurable
      (fun n β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i)))
      (GE0 i) x (fun n => ?_) (hlimE' i)
    have hsm : StronglyMeasurable (fun β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) :=
      stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 (NE n) (z i) (r i) (hr i) (Sspace i)
    have hc : Continuous (fun A : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) => inner ℝ x (A x)) :=
      continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
    exact (hc.comp_stronglyMeasurable hsm).measurable
  have hmeasF : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      AEMeasurable (fun β => inner ℝ x (GF0 i β x)) (chaosSampleLaw model).toMeasure := by
    intro i x
    refine aux_env_inner_aemeasurable
      (fun n β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i)))
      (GF0 i) x (fun n => ?_) (hlimF' i)
    have hsm : StronglyMeasurable (fun β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) :=
      stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 (NF n) (z i) (r i) (hr i) (Sspace i)
    have hc : Continuous (fun A : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) => inner ℝ x (A x)) :=
      continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
    exact (hc.comp_stronglyMeasurable hsm).measurable
  -- Null measurability of the inequality sets
  have hnull : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      NullMeasurableSet {β | M⁻¹ * inner ℝ x (GE0 i β x) ≤ inner ℝ x (GF0 i β x) ∧
        inner ℝ x (GF0 i β x) ≤ m⁻¹ * inner ℝ x (GE0 i β x)}
        (chaosSampleLaw model).toMeasure := by
    intro i x
    have h1 : NullMeasurableSet {β | M⁻¹ * inner ℝ x (GE0 i β x) ≤ inner ℝ x (GF0 i β x)}
        (chaosSampleLaw model).toMeasure :=
      nullMeasurableSet_le ((hmeasE i x).const_mul M⁻¹) (hmeasF i x)
    have h2 : NullMeasurableSet {β | inner ℝ x (GF0 i β x) ≤ m⁻¹ * inner ℝ x (GE0 i β x)}
        (chaosSampleLaw model).toMeasure :=
      nullMeasurableSet_le (hmeasF i x) ((hmeasE i x).const_mul m⁻¹)
    rw [ofPred_and]
    exact h1.inter h2
  -- (3) Countable dense test set
  have hcds : ∀ i, ∃ D : Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))),
      (↑D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))).Countable ∧
        Dense (↑D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) := fun i => by
    obtain ⟨D, hc, hd, -⟩ :=
      SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (z i) (r i) (hr i)
    exact ⟨D, hc, hd⟩
  choose Dsub hDc hDd using hcds
  -- (4) Transfer each countable test from P to P0
  have hkey : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
        M⁻¹ * inner ℝ x (GE0 i β x) ≤ inner ℝ x (GF0 i β x) ∧
        inner ℝ x (GF0 i β x) ≤ m⁻¹ * inner ℝ x (GE0 i β x) := by
    intro i x
    let S : Set (BilateralField d) := {β | M⁻¹ * inner ℝ x (GE0 i β x) ≤ inner ℝ x (GF0 i β x) ∧
        inner ℝ x (GF0 i β x) ≤ m⁻¹ * inner ℝ x (GE0 i β x)}
    have hS : NullMeasurableSet S (chaosSampleLaw model).toMeasure := hnull i x
    have hcomp : ∀ᵐ ω ∂P, field ω ∈ S := by
      filter_upwards [hq] with ω hω
      exact hω i x
    have hz : P (field ⁻¹' Sᶜ) = 0 := by
      rw [MeasureTheory.ae_iff] at hcomp
      have h2 : field ⁻¹' Sᶜ = {ω | ¬ field ω ∈ S} := by
        ext ω; simp
      rw [h2]
      exact hcomp
    have hz0 : (chaosSampleLaw model).toMeasure Sᶜ = 0 := by
      rw [← hmp.measure_preimage hS.compl]
      exact hz
    change ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, β ∈ S
    rw [MeasureTheory.ae_iff]
    exact hz0
  have hall : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i, ∀ x ∈ (Dsub i : Set _),
      M⁻¹ * inner ℝ x (GE0 i β x) ≤ inner ℝ x (GF0 i β x) ∧
      inner ℝ x (GF0 i β x) ≤ m⁻¹ * inner ℝ x (GE0 i β x) := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_ball_iff (hDc i)]
    intro x hx
    exact hkey i x
  -- (5)+(6) Density upgrade and conclusion
  filter_upwards [hall] with β hβ
  intro i
  refine thm_prop_env_energy (GE0 i β) (GF0 i β) m M hm hM (fun u => ?_)
  have hclosed : IsClosed {u : DomainL2 (centeredCube (z i) (r i) (hr i)) |
      M⁻¹ * inner ℝ u (GE0 i β u) ≤ inner ℝ u (GF0 i β u) ∧
      inner ℝ u (GF0 i β u) ≤ m⁻¹ * inner ℝ u (GE0 i β u)} := by
    have hA : Continuous (fun u : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        M⁻¹ * inner ℝ u (GE0 i β u)) :=
      Continuous.mul continuous_const
        (Continuous.inner continuous_id (ContinuousLinearMap.continuous (GE0 i β)))
    have hB : Continuous (fun u : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        inner ℝ u (GF0 i β u)) :=
      Continuous.inner continuous_id (ContinuousLinearMap.continuous (GF0 i β))
    have hC : Continuous (fun u : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        m⁻¹ * inner ℝ u (GE0 i β u)) :=
      Continuous.mul continuous_const
        (Continuous.inner continuous_id (ContinuousLinearMap.continuous (GE0 i β)))
    rw [ofPred_and]
    exact (isClosed_le hA hB).inter (isClosed_le hB hC)
  have hsub : (Dsub i : Set _) ⊆ {u : DomainL2 (centeredCube (z i) (r i) (hr i)) |
      M⁻¹ * inner ℝ u (GE0 i β u) ≤ inner ℝ u (GF0 i β u) ∧
      inner ℝ u (GF0 i β u) ≤ m⁻¹ * inner ℝ u (GE0 i β u)} :=
    fun u hu => hβ i u hu
  exact ((IsClosed.closure_subset_iff hclosed).2 hsub)
    (by rw [(hDd i).closure_eq]; exact Set.mem_univ u)

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Operator proportionality on the represented space transfers to the original space. -/
theorem aux_thm_prop_env_operator_transfer
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF seq : ℕ → ℕ) (hseq : StrictMono seq)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)))
    (hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)))
    (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
    (GNE GNF : (i : ℕ) → ℕ → Ωh →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ωh →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hjoint : aux_conv_represented_env_interface_joint d model H Ωh Ph field env env z r hr Sspace
      GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)))
    (c : ℝ) (hEF : ∀ᵐ w ∂Ph, ∀ i, GE i w = c • GF i w) :
    ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i, GE0 i β = c • GF0 i β := by
  classical
  have : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
  obtain ⟨-, hfm, hfmap, -, -, -, hMP, henvc, -, hGNd, hGNc⟩ := hjoint
  have hmpLim : MeasurePreserving field Ph P0 := ⟨hfm, hfmap⟩
  have hΦmeas : ∀ i N, StronglyMeasurable (fun β => volumeResponseOperator (Sspace i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i))) := fun i N =>
    stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 N (z i) (r i) (hr i) (Sspace i)
  have hper : ∀ i, ∀ᵐ β ∂P0, GE0 i β = c • GF0 i β := by
    intro i
    obtain ⟨D, hDc, hDd, _⟩ :=
      SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (z i) (r i) (hr i)
    have hDadd : ∀ a ∈ (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
        ∀ b ∈ (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
          a + b ∈ (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) :=
      fun a ha b hb => D.add_mem ha hb
    let T : Bool → ℕ → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) :=
      fun b n β => cond b
        (volumeResponseOperator (Sspace i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE (seq n)) (z i) (hr i)))
        (c • volumeResponseOperator (Sspace i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF (seq n)) (z i) (hr i)))
    let L0 : Bool → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) :=
      fun b β => cond b (GE0 i β) (c • GF0 i β)
    let Lh : Bool → Ωh →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) :=
      fun b w => cond b (GE i w) (c • GF i w)
    have hsym : ∀ b n β x y, ⟪T b n β x, y⟫_ℝ = ⟪x, T b n β y⟫_ℝ := by
      intro b n β x y
      cases b
      · simp only [T, cond, smul_apply]
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm]
        exact congrArg (fun t => c * t) (volumeResponseOperator_symm (Sspace i) _ y x)
      · simp only [T, cond]
        rw [real_inner_comm]
        exact volumeResponseOperator_symm (Sspace i) _ y x
    have hquad : ∀ N : ℕ, ∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
        Measurable (fun β => ⟪x, volumeResponseOperator (Sspace i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i)) x⟫_ℝ) := by
      intro N x
      have hc : Continuous (fun A : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) => ⟪x, A x⟫_ℝ) :=
        continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
      exact (hc.comp_stronglyMeasurable (hΦmeas i N)).measurable
    have hmeas : ∀ b n, ∀ x ∈ (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
        Measurable (fun β => ⟪x, T b n β x⟫_ℝ) := by
      intro b n x hx
      cases b
      · have h := (hquad (NF (seq n)) x).const_mul c
        simpa only [T, cond, smul_apply, real_inner_smul_right] using h
      · simpa only [T, cond] using hquad (NE (seq n)) x
    have hmp : ∀ n, MeasurePreserving (env n) Ph P0 := fun n => (hMP n).1
    have horig : ∀ b, ∀ᵐ β ∂P0, Tendsto (fun n => T b n β) atTop (𝓝 (L0 b β)) := by
      intro b
      cases b
      · filter_upwards [hlimF] with β hβ
        have h1 : Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF (seq n)) (z i) (hr i))) atTop
            (𝓝 (GF0 i β)) := (hβ i).comp hseq.tendsto_atTop
        have h2 : Tendsto (fun n => c • volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF (seq n)) (z i) (hr i))) atTop
            (𝓝 (c • GF0 i β)) := h1.const_smul c
        simpa only [T, L0, cond] using h2
      · filter_upwards [hlimE] with β hβ
        have h1 : Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE (seq n)) (z i) (hr i))) atTop
            (𝓝 (GE0 i β)) := (hβ i).comp hseq.tendsto_atTop
        simpa only [T, L0, cond] using h1
    have hrep : ∀ b, ∀ᵐ w ∂Ph, Tendsto (fun n => env n w) atTop (𝓝 (field w)) ∧
        Tendsto (fun n => T b (id n) (env n w)) atTop (𝓝 (Lh b w)) := by
      intro b
      cases b
      · filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.2, ?_⟩
        have hfun : (fun n => T false (id n) (env n w)) = fun n => c • GNF i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          simp only [T, cond, id, smul_apply]
          rw [volumeResponseOperator_apply]
          exact congrArg (fun z => c • z) (h2 i n f).2.symm
        rw [hfun]
        exact (h3 i).2.const_smul c
      · filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.1, ?_⟩
        have hfun : (fun n => T true (id n) (env n w)) = fun n => GNE i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          simp only [T, cond, id]
          rw [volumeResponseOperator_apply]
          exact ((h2 i n f).1).symm
        rw [hfun]
        exact (h3 i).1
    have hEF' : ∀ᵐ w ∂Ph, Lh true w = Lh false w := by
      filter_upwards [hEF] with w hw
      simpa only [Lh, cond] using hw i
    have key := conv_represented_limit_transfer P0 Ph T L0 Lh id strictMono_id env field hsym
      (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))) hDc hDd hDadd hmeas hmp hmpLim
      horig hrep hEF'
    filter_upwards [key] with β hβ
    simpa only [L0, cond] using hβ
  exact ae_all_iff.2 hper

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

/-- Weak-solution identity of a symmetric nonnegative operator against a closed form whose
energy is its dual energy. -/
theorem aux_thm_prop_env_weak_solution {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEdom : E.domain = limitFormDomain G)
    (hEenergy : ∀ u ∈ E.domain, E.form u u = (limitFormEnergy G u).toReal)
    (f : DomainL2 Q) :
    G f ∈ E.domain ∧ ∀ φ ∈ E.domain, E.form (G f) φ = inner ℝ f φ := by
  classical
  -- Finiteness of `limitFormEnergy G` on `E.domain`.
  have hfin_top : ∀ u ∈ E.domain, limitFormEnergy G u ≠ ⊤ := by
    intro u hu
    have hu' : u ∈ limitFormDomain G := by rw [← hEdom]; exact hu
    exact hu'.ne
  have hfin_bot : ∀ u : DomainL2 Q,
      limitFormEnergy G u ≠ ⊥ := fun u =>
    (limitFormEnergy_nonneg G u).trans_lt' (by
      simp) |>.ne'
  -- Step A: `G f ∈ E.domain`.
  have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
    iSup_quadraticDual_apply_image G hsym hpos f
  have hGfdom : G f ∈ E.domain := by
    have hmem : G f ∈ limitFormDomain G := by
      show limitFormEnergy G (G f) < (⊤ : EReal)
      rw [hval]
      exact EReal.coe_lt_top _
    rwa [← hEdom] at hmem
  refine ⟨hGfdom, ?_⟩
  intro φ hφ
  have hnφ : -φ ∈ E.domain := E.domain.neg_mem hφ
  have hGfpφ : G f + φ ∈ E.domain := E.domain.add_mem hGfdom hφ
  have hGfmφ : G f - φ ∈ E.domain := E.domain.sub_mem hGfdom hφ
  -- The common base value `E.form φ φ = (limitFormEnergy G φ).toReal
  --   = (limitFormEnergy G (-φ)).toReal`.
  have hbase_eq : (limitFormEnergy G φ).toReal = (limitFormEnergy G (-φ)).toReal := by
    rw [← hEenergy φ hφ, ← hEenergy (-φ) hnφ,
      E.form_neg_left hφ hnφ, E.form_neg_right hφ hφ, neg_neg]
  -- Shift identity at `G f + φ`, via `quadraticDual_sub_image` with base `φ`, image point `-f`.
  have hA : limitFormEnergy G (G f + φ) =
      limitFormEnergy G φ -
        ((2 * inner ℝ (-f) φ - inner ℝ (-f) (G (-f)) : ℝ) : EReal) := by
    have h := quadraticDual_sub_image G hsym φ (-f)
    have hGf' : G (-f) = -(G f) := map_neg G f
    have heq : φ - G (-f) = G f + φ := by rw [hGf']; abel
    rwa [heq] at h
  have hB : limitFormEnergy G (G f - φ) =
      limitFormEnergy G (-φ) -
        ((2 * inner ℝ (-f) (-φ) - inner ℝ (-f) (G (-f)) : ℝ) : EReal) := by
    have h := quadraticDual_sub_image G hsym (-φ) (-f)
    have hGf' : G (-f) = -(G f) := map_neg G f
    have heq : (-φ) - G (-f) = G f - φ := by rw [hGf']; abel
    rwa [heq] at h
  have hinner_simp1 : inner ℝ (-f) φ = -inner ℝ f φ := inner_neg_left f φ
  have hinner_simp2 : inner ℝ (-f) (-φ) = inner ℝ f φ := inner_neg_neg f φ
  have hinner_simp3 : inner ℝ (-f) (G (-f)) = inner ℝ f (G f) := by
    have hGf' : G (-f) = -(G f) := map_neg G f
    rw [hGf', inner_neg_neg]
  rw [hinner_simp1, hinner_simp3] at hA
  rw [hinner_simp2, hinner_simp3] at hB
  have hAr : (limitFormEnergy G (G f + φ)).toReal =
      (limitFormEnergy G φ).toReal - (2 * (-inner ℝ f φ) - inner ℝ f (G f)) := by
    rw [hA, EReal.toReal_sub (hfin_top φ hφ) (hfin_bot φ)
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hBr : (limitFormEnergy G (G f - φ)).toReal =
      (limitFormEnergy G (-φ)).toReal - (2 * inner ℝ f φ - inner ℝ f (G f)) := by
    rw [hB, EReal.toReal_sub (hfin_top (-φ) hnφ) (hfin_bot (-φ))
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hdiff : (limitFormEnergy G (G f + φ)).toReal -
      (limitFormEnergy G (G f - φ)).toReal = 4 * inner ℝ f φ := by
    rw [hAr, hBr, hbase_eq]; ring
  have hpolar : E.form (G f + φ) (G f + φ) - E.form (G f - φ) (G f - φ) =
      4 * E.form (G f) φ := by
    have h1 := E.form_add_self hGfdom hφ
    have h2 := E.form_add_smul_self (-1 : ℝ) hGfdom hφ
    simp only [neg_one_smul] at h2
    have hsub : G f + (-φ) = G f - φ := by abel
    rw [hsub] at h2
    linarith [h1, h2]
  have hE1 : E.form (G f + φ) (G f + φ) = (limitFormEnergy G (G f + φ)).toReal :=
    hEenergy _ hGfpφ
  have hE2 : E.form (G f - φ) (G f - φ) = (limitFormEnergy G (G f - φ)).toReal :=
    hEenergy _ hGfmφ
  have : 4 * E.form (G f) φ = 4 * inner ℝ f φ := by
    rw [← hpolar, hE1, hE2, hdiff]
  linarith [this]

/-- Source recovery for every regular realization of the limit energy, from symmetry and
nonnegativity of the limit operator alone. -/
theorem aux_thm_prop_env_source
    (d : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (G : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hs : ∀ᵐ om ∂P, ∀ i : ℕ,
      (∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
        inner ℝ (G i om x) y = inner ℝ x (G i om y)) ∧
      (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), 0 ≤ inner ℝ x (G i om x))) :
    ∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
        (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
      (∀ u, E.energy u = limitFormEnergy (G i om) u) →
      ∀ _Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E,
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
      _root_.SubdiffusiveProcess.DirichletForm.IsResolvent E 0 (G i om) := by
  filter_upwards [hs] with om hsn i E hE Gamma hcore
  have hdom := aux_thm_prop_domain_eq_of_energy E (G i om) hE
  have hdiag := aux_thm_prop_form_eq_toReal_energy E (G i om) hE
  intro f
  have hweak := aux_thm_prop_env_weak_solution (G i om) (hsn i).1 (hsn i).2 E hdom hdiag f
  simpa only [zero_mul, zero_add] using hweak

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators

/-- The original-space operator limits form a fixed-field joint package. -/
theorem aux_thm_prop_env_orig_joint
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)))
    (hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β))) :
    in_joint_extracted_candidates d model H (BilateralField d) (chaosSampleLaw model).toMeasure
      (fun β => β) z r hr Sspace
      (fun i N β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i))) GE0 GF0 NE NF := by
  refine ⟨?_, measurable_id, ?_, hH, ⟨hNE, hNF⟩, hS, ?_, ?_⟩
  · exact inferInstance
  · exact Measure.map_id
  · intro i N β f
    exact volumeResponseOperator_apply ..
  · filter_upwards [hlimE, hlimF] with β hE hF i
    exact ⟨hE i, hF i⟩

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The nonvanishing of the limit form on the first cube comes from the constructed form. -/
theorem aux_thm_prop_env_nonzero
    (d : ℕ) (hd : 2 ≤ d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (aE : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i)))
    (hside : ∀ᵐ om ∂P, ∀ i : ℕ,
      Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om)
        (aE i om))) :
    ∀ᵐ om ∂P, aux_thm_prop_nonzero z r hr GE om := by
  filter_upwards [hside] with om h
  obtain ⟨A⟩ := h 0
  obtain ⟨u, hu, hpos⟩ := aux_thm_c1_cube_positive_energy (z 0) (r 0) (hr 0) (GE 0 om) A.form.toClosedForm A.energy_eq
  exact ⟨0, u, hu, hpos⟩

end Part4

end SubdiffusiveProcess.Paper
end
