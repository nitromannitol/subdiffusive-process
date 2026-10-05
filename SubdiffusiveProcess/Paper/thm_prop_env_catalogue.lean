module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
public import SubdiffusiveProcess.Paper.conv_represented_limit_planes
public import SubdiffusiveProcess.Paper.limit_form_package_controls
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.EllipticRegularity.GoodCellCatalogue
public import SubdiffusiveProcess.Paper.affine_source_cells_env
public import SubdiffusiveProcess.Paper.thm_prop_affine_ellipticity_env_core
public import SubdiffusiveProcess.Paper.represented_same_law_in_measure

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The grids-catalogue retains the plain environment catalogue. -/
theorem aux_thm_prop_env_catalogue_of_grids
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) (E : _root_.SubdiffusiveProcess.Paper.in_J d) (beta0 t0 : ℝ)
    (h : conv_represented_catalogue_grids d hd model H Ω P envE envF z r hr Sspace NE NF alpha eta E beta0 t0) :
    aux_conv_represented_env_interface_catalogue d hd model H Ω P envE envF z r hr Sspace NE NF alpha eta := by
  unfold conv_represented_catalogue_grids at h
  unfold aux_conv_represented_env_interface_catalogue
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root, hsub, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hconj, hgrid, hcollar, hrep⟩ := h
  exact ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root, hsub, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hrep⟩

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The two (field-by-field identical) structures of analytic controls. -/
theorem aux_thm_prop_env_controls_convert {d : ℕ} {hd : 2 ≤ d}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S a)) :
    Nonempty (aux_thm_prop_analytic_controls d hd z r hr S a) := by
  obtain ⟨A⟩ := A
  exact ⟨{ K := A.K, K_pos := A.K_pos, coercive := A.coercive, interpolation := A.interpolation, sources := A.sources, sources_countable := A.sources_countable, sources_dense := A.sources_dense, sources_smooth := A.sources_smooth, mesh := A.mesh, t := A.t, t_lower := A.t_lower, t_upper := A.t_upper, cutoffs := A.cutoffs }⟩

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Environment version of `aux_thm_prop_catalogue_measurable_affine_matrices`: the actual affine
response matrices of every cube converge along `env n om`, for a.e. sample. -/
theorem thm_prop_env_catalogue
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (env : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hH : Measurable H) (henv : ∀ n, Measurable (env n))
    (hCat : aux_conv_represented_env_interface_catalogue d hd model H Ω P env env z r hr Sspace NE NF alpha eta)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖) :
    ∃ AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      (∀ j om, (AE j om).transpose = AE j om) ∧
      (∀ j om, (AF j om).transpose = AF j om) ∧
      (∀ j i k, Measurable (fun om => AE j om i k)) ∧
      (∀ j i k, Measurable (fun om => AF j om i k)) ∧
      ∀ᵐ om ∂P, ∀ j,
        (∀ p : Fin d → ℝ, Tendsto (fun n =>
          affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
            (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ (AE j om).mulVec p))) ∧
        (∀ p : Fin d → ℝ, Tendsto (fun n =>
          affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
            (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ (AF j om).mulVec p))) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
      root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
      ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey,
      sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
      cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have he : ∀ᵐ om ∂P, om ∈ eventE :=
    ae_iff.mpr hRepE.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hf : ∀ᵐ om ∂P, om ∈ eventF :=
    ae_iff.mpr hRepF.2.2.2.2.2.2.2.2.2.1.2.2.1
  have heA : ∀ᵐ om ∂P, ∀ j, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧
      ∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ A.mulVec p)) := by
    filter_upwards [he] with om hom j
    exact aux_thm_prop_represented_affine_matrix d hd model H Ω P
      NE env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (env n om)) responseE
      (fun i n om => catalogConstant i (NE n) (env n om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om hom j (hP j)
  have hfA : ∀ᵐ om ∂P, ∀ j, ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = A ∧
      ∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ A.mulVec p)) := by
    filter_upwards [hf] with om hom j
    exact aux_thm_prop_represented_affine_matrix d hd model H Ω P
      NF env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (env n om)) responseF
      (fun i n om => catalogConstant i (NF n) (env n om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om hom j (hP j)
  obtain ⟨AE, hEsym, hEconv⟩ := aux_thm_prop_choose_symmetric_matrices P _ heA
  obtain ⟨AF, hFsym, hFconv⟩ := aux_thm_prop_choose_symmetric_matrices P _ hfA
  have hME : ∀ j i k, AEMeasurable (fun om => AE j om i k) P := by
    intro j
    exact aux_thm_prop_matrix_limit_aemeasurable P
      (fun n om p => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
        (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
      (fun n p => ((aux_thm_prop_affine_response_measurable model H hH (NE n)
        (z j) (hr j) (hP j) p).comp (henv n)).div_const _)
      (AE j) (hEsym j) (hEconv.mono fun om hom => hom j)
  have hMF : ∀ j i k, AEMeasurable (fun om => AF j om i k) P := by
    intro j
    exact aux_thm_prop_matrix_limit_aemeasurable P
      (fun n om p => affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
        (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
      (fun n p => ((aux_thm_prop_affine_response_measurable model H hH (NF n)
        (z j) (hr j) (hP j) p).comp (henv n)).div_const _)
      (AF j) (hFsym j) (hFconv.mono fun om hom => hom j)
  obtain ⟨BE, hBEmeas, hBEsym, hBEeq⟩ := aux_thm_prop_symmetric_measurable_versions P AE hEsym hME
  obtain ⟨BF, hBFmeas, hBFsym, hBFeq⟩ := aux_thm_prop_symmetric_measurable_versions P AF hFsym hMF
  refine ⟨BE, BF, hBEsym, hBFsym, hBEmeas, hBFmeas, ?_⟩
  filter_upwards [hEconv, hFconv, hBEeq, hBFeq] with om hcE hcF he' hf' j
  rw [he' j, hf' j]
  exact ⟨hcE j, hcF j⟩

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Mass cells and their triple-size parents are catalogue cubes. -/
theorem aux_thm_prop_env_mass_indices
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hCat : aux_conv_represented_env_interface_catalogue d hd model H Ω P envE envF z r hr Sspace NE NF alpha eta) :
    ∀ (jQ H1 Mm n : ℕ) (Cwidth gamma : ℝ)
      (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
      1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma →
      aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k →
      closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      ∃ jC jP : ℕ,
        z jC = aux_thm_prop_mass_center H1 Mm sigma n k ∧
        r jC = aux_thm_prop_mass_side H1 n ∧
        z jP = aux_thm_prop_mass_center H1 Mm sigma n k ∧
        r jP = 3 * aux_thm_prop_mass_side H1 n ∧
        closure (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root,
    _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have hcontain := hRepE.2.2.2.2.2.2.2.2.2.2.1
  have hcomplete := hRepE.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact fun jQ H1 Mm n Cwidth gamma sigma k =>
    aux_thm_prop_mass_catalogue_indices root z r hr hcontain hcomplete jQ H1 Mm n Cwidth gamma sigma k

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Plane-null energy measures of the represented limit forms, for arbitrary package sides. -/
theorem aux_thm_prop_env_planes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hdata : conv_represented_joint_buffered d hd model H Ω P field env env z r hr Sspace
      GNE GNF GE GF NE NF alpha eta)
    (hBounds : aux_conv_represented_env_interface_bounds d hd model H Ω P env env z r hr
      Sspace GE GF NE NF) :
    ∀ᵐ om ∂P, ∀ j,
      (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GE j om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)),
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) ∧
      (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GF j om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)),
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) := by
  refine Filter.Eventually.mono (conv_represented_limit_planes d hd model H Ω P field env env z r hr Sspace GNE GNF GE GF NE NF alpha eta hdata hBounds) ?_
  intro om h j
  exact ⟨fun A u hu i c => (h j).1 A.form A.gamma A.energy_eq A.core u hu i c, fun A u hu i c => (h j).2 A.form A.gamma A.energy_eq A.core u hu i c⟩

end Part4

section Part5
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The actual affine response matrices of the environment catalogue have positive trace. -/
theorem aux_thm_prop_env_trace_positive
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (env : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hCat : aux_conv_represented_env_interface_catalogue d hd model H Ω P env env z r hr Sspace NE NF alpha eta)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AE j om).mulVec p))) ∧
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AF j om).mulVec p)))) :
    ∀ᵐ om ∂P, ∀ j, 0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have he : ∀ᵐ om ∂P, om ∈ eventE :=
    ae_iff.mpr hRepE.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hf : ∀ᵐ om ∂P, om ∈ eventF :=
    ae_iff.mpr hRepF.2.2.2.2.2.2.2.2.2.1.2.2.1
  filter_upwards [he, hf, hconv] with om he hf hc j
  constructor
  · exact (aux_thm_prop_represented_trace_positive d hd model H Ω P
      NE env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (env n om)) responseE
      (fun i n om => catalogConstant i (NE n) (env n om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om he j (hP j) (AE j om) (hc j).1).2
  · exact (aux_thm_prop_represented_trace_positive d hd model H Ω P
      NF env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (env n om)) responseF
      (fun i n om => catalogConstant i (NF n) (env n om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om hf j (hP j) (AF j om) (hc j).2).2

end Part5

end SubdiffusiveProcess.Paper
end
