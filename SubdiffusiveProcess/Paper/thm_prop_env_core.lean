module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.thm_prop_env_endpoints
public import SubdiffusiveProcess.Paper.thm_prop_env_select
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_uniqueness
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators

/-- **The improvement argument of `thm_prop` for one bounded catalogue, in environment form.**
All model-dependent suppliers (`prepared`, `affine`, the concentration `hconc`, the sides, coercivity
and source recovery) are hypotheses here; the endpoint gap is closed through essential endpoints. -/
theorem thm_prop_env_core
    (d : ℕ) (hd : 2 ≤ d) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (g : aux_thm_prop_selection_geometry d)
    (c0 : ℝ) (hc0 : 0 < c0) (p : ℝ) (hp : 0 < p) (Cp : ℝ) (hCp : 0 < Cp) (aexp : ℝ)
    (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / (1 / 32 : ℝ)) *
      (((g.H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (_hfield : Measurable field)
        (_hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
        (aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i)))
        (_hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
        (_hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
        (_hsn : ∀ᵐ omega ∂P, ∀ i : ℕ,
          ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
              inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
            (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
              0 ≤ inner ℝ x (GE i omega x))) ∧
          ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
              inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
            (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
              0 ≤ inner ℝ x (GF i omega x))))
        (_hside : ∀ᵐ om ∂P, ∀ i,
          Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om)
            (aE i om)) ∧
          Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GF i om)
            (aF i om)))
        (_hcoer : ∀ᵐ om ∂P, ∀ i,
          aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GE i om) ∧
          aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GF i om))
        (_hsourceE : ∀ᵐ om ∂P, ∀ i : ℕ,
          ∀ E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∀ u, E.energy u = limitFormEnergy (GE i om) u) →
          ∀ _Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E,
          (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
          _root_.SubdiffusiveProcess.DirichletForm.IsResolvent E 0 (GE i om))
        (_hsourceF : ∀ᵐ om ∂P, ∀ i : ℕ,
          ∀ E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
          (∀ u, E.energy u = limitFormEnergy (GF i om) u) →
          ∀ _Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E,
          (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
          _root_.SubdiffusiveProcess.DirichletForm.IsResolvent E 0 (GF i om))
        (prepared : ∀ m M : ℝ, aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
        (_affine : ∀ m M : ℝ, aux_thm_prop_env_local_affine_data (prepared m M) g c0)
        (_hconc : ∀ m M : ℝ, C0⁻¹ ≤ m → m ≤ M → M ≤ C0 →
          (∀ᵐ om ∂P, ∀ i,
            limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
            ∀ u ∈ limitFormDomain (GE i om),
              m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
              (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal) →
          aux_thm_prop_cell_matrix_moments P field z r (prepared m M).AE (prepared m M).AF
            (prepared m M).ck g.H1 p (Cp * model.delta * (M - m)) aexp),
        ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧ ∀ᵐ omega ∂P, ∀ i : ℕ,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
              (limitFormEnergy (GF i omega) u).toReal =
                c * (limitFormEnergy (GE i omega) u).toReal := by
  obtain ⟨delta0, hdelta0, hsel⟩ := thm_prop_env_select d hd g c0 hc0 p hp Cp hCp aexp haexp
    hpRate
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Ω _ P _ field hfield hlaw z r hr Sspace GE GF aE aF hcomp hnz hsn hside
    hcoer hsourceE hsourceF prepared affine hconc
  refine thm_prop_env_endpoints z r hr P GE GF C0 hC0 hcomp hnz ?_
  intro m M hmC hlt hMC hmmem hMmem hmax1 hmax2
  have hm : 0 < m := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hmC
  have horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal := by
    filter_upwards [hmmem, hMmem, hcomp] with om h1 h2 h3 i
    exact ⟨(h3 i).1, fun u hu => ⟨h1 i u hu, h2 i u hu⟩⟩
  have hmom := hconc m M hmC hlt.le hMC horder
  have hfine := hsel model hmodel Ω P field hfield hlaw z r hr Sspace GE GF aE aF m M hm hlt.le
    horder (prepared m M) (affine m M) hmom
  have hdich := aux_thm_prop_env_dichotomy_of_fine hd m M hm hlt.le hside horder hcoer hsourceE
    hsourceF hfine
  obtain ⟨k1, hk1, hbranch⟩ := aux_thm_prop_env_improve_of_dichotomy C0 hC0 hsn hcomp m M hmC hlt
    hdich
  have hpos : 0 < k1 * (M - m) := mul_pos hk1 (sub_pos.mpr hlt)
  rcases hbranch with h | h
  · exact hmax2 _ hpos (by simpa only [sub_sub_cancel] using h)
  · exact hmax1 _ hpos h

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace

/-- Reindexing the cube family of the environment joint package along `e`. -/
theorem aux_thm_prop_env_joint_reindex
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (e : ℕ → ℕ)
    (hjoint : aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF) :
    aux_conv_represented_env_interface_joint d model H Ω P field envE envF (z ∘ e) (r ∘ e)
      (fun j => hr (e j)) (fun j => Sspace (e j)) (fun j => GNE (e j)) (fun j => GNF (e j))
      (fun j => GE (e j)) (fun j => GF (e j)) NE NF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hjoint
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun j => h9 (e j), ?_, ?_⟩
  · filter_upwards [h10] with om h j n f using h (e j) n f
  · filter_upwards [h11] with om h j using h (e j)

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace

/-- Limits of the environment inverses are symmetric and nonnegative. -/
theorem aux_thm_prop_env_hsn
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hjoint : aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hGN, hconv⟩ := hjoint
  filter_upwards [hGN, hconv] with omega hG hc i
  have hsymE : ∀ N (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GNE i N omega x) y = inner ℝ x (GNE i N omega y) := by
    intro N x y
    rw [(hG i N x).1, (hG i N y).1, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hsymF : ∀ N (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GNF i N omega x) y = inner ℝ x (GNF i N omega y) := by
    intro N x y
    rw [(hG i N x).2, (hG i N y).2, real_inner_comm]
    exact volumeResponse_pairing_symm _ _ y x
  have hposE : ∀ N (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GNE i N omega x) := by
    intro N x
    rw [(hG i N x).1]
    exact volumeResponse_pairing_nonneg _ _ x
  have hposF : ∀ N (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      0 ≤ inner ℝ x (GNF i N omega x) := by
    intro N x
    rw [(hG i N x).2]
    exact volumeResponse_pairing_nonneg _ _ x
  exact ⟨aux_thm_prop_symm_nonneg_of_tendsto _ _ (hc i).1 hsymE hposE,
    aux_thm_prop_symm_nonneg_of_tendsto _ _ (hc i).2 hsymF hposF⟩

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace

/-- **Identification of the represented limits with the original-space limits.**  If the cutoff
sequences have almost sure operator limits `GE0`, `GF0` on the original space, the limits `GE`, `GF`
of the changing-environment sequences on the represented space are the compositions with the limit
field. -/
theorem aux_thm_prop_env_identification
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF seqE seqF : ℕ → ℕ) (hseqE : StrictMono seqE) (hseqF : StrictMono seqF)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)))
    (hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)))
    (hIR : InfraredCharacterization model H)
    (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
    (GNE GNF : (i : ℕ) → ℕ → Ωh →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ωh →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hjoint : aux_conv_represented_env_interface_joint d model H Ωh Ph field env env z r hr Sspace
      GNE GNF GE GF (fun n => NE (seqE n)) (fun n => NF (seqF n))) :
    ∀ᵐ ω ∂Ph, ∀ i, GE i ω = GE0 i (field ω) ∧ GF i ω = GF0 i (field ω) := by
  classical
  have : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
  obtain ⟨-, hfm, hfmap, -, -, -, hMP, henvc, hSpin, hGNd, hGNc⟩ := hjoint
  have hmpLim : MeasurePreserving field Ph P0 := ⟨hfm, hfmap⟩
  have hΦmeas : ∀ i N, StronglyMeasurable (fun β => volumeResponseOperator (Sspace i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i))) := fun i N =>
    stronglyMeasurable_cutoffVolumeResponseOperator model H hIR.1 N (z i) (r i) (hr i) (Sspace i)
  have hper : ∀ i, ∀ᵐ ω ∂Ph, GE i ω = GE0 i (field ω) ∧ GF i ω = GF0 i (field ω) := by
    intro i
    obtain ⟨Dsub, hDc, hDd, -⟩ :=
      SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (z i) (r i) (hr i)
    have hsym : ∀ N β x y, ⟪volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i)) x, y⟫_ℝ =
        ⟪x, volumeResponseOperator (Sspace i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i)) y⟫_ℝ := by
      intro N β x y
      rw [real_inner_comm]
      exact volumeResponseOperator_symm (Sspace i) _ y x
    have hmeas : ∀ N, ∀ x ∈ (Dsub : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
        Measurable (fun β => ⟪x, volumeResponseOperator (Sspace i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (z i) (hr i)) x⟫_ℝ) := by
      intro N x hx
      have hc : Continuous (fun A : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) => ⟪x, A x⟫_ℝ) :=
        continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
      exact (hc.comp_stronglyMeasurable (hΦmeas i N)).measurable
    have hmp : ∀ n, MeasurePreserving (env n) Ph P0 := fun n => (hMP n).1
    have hE := conv_represented_limit_identification P0 Ph
      (fun n β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i)))
      (GE0 i) (GE i) seqE hseqE env field (fun n β x y => hsym (NE n) β x y)
      (Dsub : Set _) hDc hDd (fun a ha b hb => Dsub.add_mem ha hb)
      (fun n x hx => hmeas (NE n) x hx) hmp hmpLim
      (by filter_upwards [hlimE] with β h using h i) (by
        filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.1, ?_⟩
        have hfun : (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n w) (NE (seqE n)) (z i) (hr i))) =
            fun n => GNE i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          rw [volumeResponseOperator_apply]
          exact ((h2 i n f).1).symm
        rw [hfun]
        exact (h3 i).1)
    have hF := conv_represented_limit_identification P0 Ph
      (fun n β => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i)))
      (GF0 i) (GF i) seqF hseqF env field (fun n β x y => hsym (NF n) β x y)
      (Dsub : Set _) hDc hDd (fun a ha b hb => Dsub.add_mem ha hb)
      (fun n x hx => hmeas (NF n) x hx) hmp hmpLim
      (by filter_upwards [hlimF] with β h using h i) (by
        filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.1, ?_⟩
        have hfun : (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n w) (NF (seqF n)) (z i) (hr i))) =
            fun n => GNF i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          rw [volumeResponseOperator_apply]
          exact ((h2 i n f).2).symm
        rw [hfun]
        exact (h3 i).2)
    filter_upwards [hE, hF] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [ae_all_iff.2 hper] with ω h i
  exact h i

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Gluing of proportionality constants over exhaustive subcatalogues, keeping the bounds
`C0⁻¹ ≤ c ≤ C0` of the local constants. -/
theorem aux_thm_prop_env_glue {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (C0 : ℝ) (_hC0 : 1 ≤ C0)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (e : ℕ → ℕ → ℕ) (hcover : ∀ k i, i ≤ k → ∃ j, e k j = i)
    (hpos : ∀ᵐ omega ∂P, ∃ u : DomainL2 (centeredCube (z 0) (r 0) (hr 0)),
      u ∈ limitFormDomain (GE 0 omega) ∧ 0 < (limitFormEnergy (GE 0 omega) u).toReal)
    (hlocal : ∀ k, ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧ ∀ᵐ omega ∂P, ∀ j,
      limitFormDomain (GE (e k j) omega) = limitFormDomain (GF (e k j) omega) ∧
      ∀ u, u ∈ limitFormDomain (GE (e k j) omega) →
        (limitFormEnergy (GF (e k j) omega) u).toReal =
          c * (limitFormEnergy (GE (e k j) omega) u).toReal) :
    ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧ ∀ᵐ omega ∂P, ∀ i,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
      ∀ u, u ∈ limitFormDomain (GE i omega) →
        (limitFormEnergy (GF i omega) u).toReal =
          c * (limitFormEnergy (GE i omega) u).toReal := by
  choose c hcl hcu hprop using hlocal
  have heq : ∀ k, c k = c 0 := by
    intro k
    obtain ⟨j, hj⟩ := hcover k 0 (Nat.zero_le k)
    obtain ⟨j0, hj0⟩ := hcover 0 0 le_rfl
    obtain ⟨omega, hp, hp0, u, hu, hupos⟩ :=
      ((hprop k).and ((hprop 0).and hpos)).exists
    have hk := hp j
    have h0 := hp0 j0
    rw [hj] at hk
    rw [hj0] at h0
    exact (mul_right_cancel₀ (ne_of_gt hupos)) ((hk.2 u hu).symm.trans (h0.2 u hu))
  refine ⟨c 0, hcl 0, hcu 0, ?_⟩
  filter_upwards [ae_all_iff.mpr hprop] with omega h i
  obtain ⟨j, hj⟩ := hcover i i le_rfl
  have hi := h i j
  rwa [hj, heq i] at hi

end Part4

end SubdiffusiveProcess.Paper
end
