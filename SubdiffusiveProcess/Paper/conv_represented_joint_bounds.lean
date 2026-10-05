module

public import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_all_cubes

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual buffered joint package supplies both candidates' represented bounds. -/
theorem conv_represented_joint_bounds (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hext : InfraredCharacterization model H → aux_lem_cutoffs_root_uniform_extrema d model H eta)
    (hdata : conv_represented_joint_buffered d hd model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF alpha eta) :
    aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr Sspace GE GF NE NF := by
  classical
  rcases hdata with ⟨hjoint, hcatalogues⟩
  rcases hjoint with ⟨_, _, _, _, _, _, _, _, _, hGN, hlim⟩
  rw [aux_conv_represented_env_interface_bounds, ae_all_iff]
  intro i
  obtain ⟨e, he, hcat⟩ := hcatalogues i
  obtain ⟨j, hj⟩ := he i le_rfl
  obtain ⟨cR, cC, respE, respF, evE, evF, root, hunit, Dcat, hDcat, fcat, trace, traceH1,
    usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, beta, t, I,
    cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot, gridKey, hbuf, hcats⟩ := hcat
  have : ∀ j, Countable (Dcat j) := hDcat
  have htrace : ∀ j b, (traceH1 j b).toFun = trace j b := by
    have hc := hcats.1
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htr, _⟩
    exact fun j b => (htr j b).2
  have hseed : ∀ j k, ∃ b : ℕ, (traceH1 j b).toFun =
      bufferedCollarProfile d (z (e j)) (r (e j)) (r (e j) / (10 * (3 : ℝ) ^ k)) := by
    intro j k
    obtain ⟨b, hb⟩ := hbuf j k j
    exact ⟨b, (htrace j b).trans hb⟩
  have hcE : ∀ j, ∀ᵐ omega ∂P, ∀ g : DomainL2 (centeredCube (z (e j)) (r (e j)) (hr (e j))),
      Tendsto (fun n => (responseSolution (Sspace (e j))
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z (e j)) (hr (e j)))
        ((sobolevVolumeLoad g).comp (Sspace (e j)).space.subtypeL)).val.1)
        atTop (𝓝 (GE (e j) omega g)) := by
    intro j
    filter_upwards [hGN, hlim] with omega hG hL g
    have hc : Tendsto (fun n => GNE (e j) n omega g) atTop (𝓝 (GE (e j) omega g)) :=
      ((continuous_id.clm_apply continuous_const).tendsto (GE (e j) omega)).comp (hL (e j)).1
    exact hc.congr (fun n => (hG (e j) n g).1)
  have hcF : ∀ j, ∀ᵐ omega ∂P, ∀ g : DomainL2 (centeredCube (z (e j)) (r (e j)) (hr (e j))),
      Tendsto (fun n => (responseSolution (Sspace (e j))
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z (e j)) (hr (e j)))
        ((sobolevVolumeLoad g).comp (Sspace (e j)).space.subtypeL)).val.1)
        atTop (𝓝 (GF (e j) omega g)) := by
    intro j
    filter_upwards [hGN, hlim] with omega hG hL g
    have hc : Tendsto (fun n => GNF (e j) n omega g) atTop (𝓝 (GF (e j) omega g)) :=
      ((continuous_id.clm_apply continuous_const).tendsto (GF (e j) omega)).comp (hL (e j)).2
    exact hc.congr (fun n => (hG (e j) n g).2)
  have hE := in_represented_bounds_seq_all_cubes d hd model H Cext beta alpha eta t {1}
    Ω P NE envE ℕ root (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j))
    Dcat fcat (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE I ℕ
    (fun i n omega => cR i (NE n) (envE n omega)) respE
    (fun i n omega => cC i (NE n) (envE n omega)) evE cK eK lK sRK sGK sHK cRK cGK cHK
    ℕ origin gridRoot gridKey hcats.1 hInterp hext hseed (fun j => GE (e j)) hcE
  have hF := in_represented_bounds_seq_all_cubes d hd model H Cext beta alpha eta t {1}
    Ω P NF envF ℕ root (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j))
    Dcat fcat (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF I ℕ
    (fun i n omega => cR i (NF n) (envF n omega)) respF
    (fun i n omega => cC i (NF n) (envF n omega)) evF cK eK lK sRK sGK sHK cRK cGK cHK
    ℕ origin gridRoot gridKey hcats.2 hInterp hext hseed (fun j => GF (e j)) hcF
  filter_upwards [hE, hF] with omega hE hF
  rw [← hj]
  exact ⟨hE j, hF j⟩

end SubdiffusiveProcess.Paper
