module

public import SubdiffusiveProcess.Paper.prop_conc_masked_measure_identification
public import SubdiffusiveProcess.Paper.prop_conc_resampled_form_identification
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_transfer
public import SubdiffusiveProcess.Paper.prop_conc_resampled_layer_coefficient
public import SubdiffusiveProcess.Paper.inputs_classical_countable_bounded_subsequence
public import Mathlib.Tactic

@[expose] public section

/-! Growth of the canonically resampled pair from a tied pair of the resampled environment (stage I of the
growth of the resampled pair).  For fixed `ω` and layer draw `y`: if `Y` is a tied affine pair at `ω`, `Yc`
is a tied affine pair at `η = ω[j ← y]` (tied to the operator limits along the same cutoff sequences) with
ball-growth constant `K`, and the operator-level data of `prop_conc_resampled_form_identification` hold, then
the canonical mask of `Y` by `1_q (y - ω_j)` has the same growth constant `K`.  The auxiliary lemmas give
the almost sure facts (coefficient factorization for all cutoffs, controls along subsequences, transport of
chaos-almost-sure properties to `ω[j ← y]`) that supply those operator-level data for a represented field. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

section Events

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Chaos-almost-sure properties hold at the resampled configuration for almost every `(ω, y)`. -/
theorem aux_prop_conc_resampled_pair_growth_of_tied_eta_ae
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℤ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    {Pc : BilateralField d → Prop} (hPc : ∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, Pc eta) :
    ∀ᵐ omega ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      Pc (Function.update (field omega) j y) :=
  Measure.ae_ae_of_ae_prod
    ((prop_conc_weighted_identification_transfer model j P field hfield).quasiMeasurePreserving.ae hPc)

/-- The coefficient factorization holds for every cutoff containing the layer, for a.e. `(ω, y)`. -/
theorem aux_prop_conc_resampled_pair_growth_of_tied_coef_ae
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization model H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    (j : ℤ) (hj : j ≤ 0) (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ) :
    ∀ᵐ omega ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
        (cutoffPositiveCoefficient model H (Function.update (field omega) j y) N₀ zQ hRQ).val
          =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
          (fun x => Real.exp (y x - field omega j x) *
            (cutoffPositiveCoefficient model H (field omega) N₀ zQ hRQ).val x) := by
  have hc : ∀ N₀ : ℕ, ∀ᵐ omega ∂P,
      ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      (j.natAbs ≤ N₀ →
        (cutoffPositiveCoefficient model H (Function.update (field omega) j y) N₀ zQ hRQ).val
          =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
          (fun x => Real.exp (y x - field omega j x) *
            (cutoffPositiveCoefficient model H (field omega) N₀ zQ hRQ).val x)) := by
    intro N₀
    by_cases hN : j.natAbs ≤ N₀
    · filter_upwards [aux_prop_conc_resampled_layer_coefficient_positive_ae P model H hIR field
        hfield j N₀ hj hN zQ hRQ] with omega hω
      filter_upwards [hω] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall fun omega => Eventually.of_forall fun y h => absurd h hN
  filter_upwards [ae_all_iff.2 hc] with omega hω
  filter_upwards [ae_all_iff.2 hω] with y hy
  exact hy

/-- A tight countable bank whose bounded subsequences carry the analytic controls gives, for a.e. represented
`ω`, controls along a subsequence of each of two cutoff sequences. -/
theorem aux_prop_conc_resampled_pair_growth_of_tied_ctrl_ae
    (hd : 2 ≤ d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ)) (NE NF : ℕ → ℕ)
    {ι : Type} [Countable ι] (F : ι → ℕ → BilateralField d → ℝ) (Cb : ι → ℝ≥0)
    (hmem : ∀ i n, MemLp (F i n) 1 (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ i n, eLpNorm (F i n) 1 (chaosSampleLaw model).toMeasure ≤ Cb i)
    (hcontrol : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      ∀ N : ℕ → ℕ, (∀ i, ∃ B : ℝ, ∀ n, |F i (N n) om| ≤ B) →
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
          (fun n => cutoffPositiveCoefficient model H om (N n) zQ hRQ))) :
    ∀ᵐ omega ∂P,
      (∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
          (fun n => cutoffPositiveCoefficient model H (field omega) (NE (seq n)) zQ hRQ))) ∧
      (∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
          (fun n => cutoffPositiveCoefficient model H (field omega) (NF (seq n)) zQ hRQ))) := by
  have hmemP : ∀ i n, MemLp (fun ω => F i n (field ω)) 1 P := fun i n =>
    (hmem i n).comp_measurePreserving hfield
  have hnormP : ∀ i n, eLpNorm (fun ω => F i n (field ω)) 1 P ≤ Cb i := fun i n => by
    have h := eLpNorm_comp_measurePreserving (p := 1) (hmem i n).aestronglyMeasurable hfield
    exact h.trans_le (hnorm i n)
  have hbdE := inputs_classical_countable_bounded_subsequence P
    (fun i n ω => F i (NE n) (field ω)) Cb (fun i n => hmemP i (NE n)) (fun i n => hnormP i (NE n))
  have hbdF := inputs_classical_countable_bounded_subsequence P
    (fun i n ω => F i (NF n) (field ω)) Cb (fun i n => hmemP i (NF n)) (fun i n => hnormP i (NF n))
  have hcontrolP := hfield.quasiMeasurePreserving.ae hcontrol
  filter_upwards [hbdE, hbdF, hcontrolP] with ω hbE hbF hcP
  obtain ⟨seqE, hseqE, hbE'⟩ := hbE
  obtain ⟨seqF, hseqF, hbF'⟩ := hbF
  exact ⟨⟨seqE, hseqE, hcP (fun n => NE (seqE n)) (fun i => by
      obtain ⟨B, _, hB⟩ := hbE' i
      exact ⟨B, hB⟩)⟩,
    ⟨seqF, hseqF, hcP (fun n => NF (seqF n)) (fun i => by
      obtain ⟨B, _, hB⟩ := hbF' i
      exact ⟨B, hB⟩)⟩⟩

end Events

/-- For fixed `ω` and layer draw `y`, a tied affine pair `Yc` at the resampled configuration with ball-growth
constant `K` transfers its growth to the canonical mask of the tied pair `Y` at `ω` by `1_q (y - ω_j)`. -/
theorem prop_conc_resampled_pair_growth_of_tied
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (C0 m M : ℝ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (omega : BilateralField d) (y : C(SpatialCoordinates d, ℝ)) (j : ℤ)
    (hcoef : ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
      (cutoffPositiveCoefficient model H (Function.update omega j y) N₀ zQ hRQ).val
        =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - omega j x) *
          (cutoffPositiveCoefficient model H omega N₀ zQ hRQ).val x))
    (Y Yc : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M)
    (hYaff : aux_prop_conc_pair_data_affine Y) (hYcaff : aux_prop_conc_pair_data_affine Yc)
    (GE GF GpE GpF : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hGE : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (NE n) zQ hRQ)) atTop (𝓝 GE))
    (hGF : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (NF n) zQ hRQ)) atTop (𝓝 GF))
    (hctrlE : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
        (fun n => cutoffPositiveCoefficient model H omega (NE (seq n)) zQ hRQ)))
    (hctrlF : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
        (fun n => cutoffPositiveCoefficient model H omega (NF (seq n)) zQ hRQ)))
    (hGpE : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (NE n) zQ hRQ))
      atTop (𝓝 GpE))
    (hGpF : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (NF n) zQ hRQ))
      atTop (𝓝 GpF))
    (hYE : ∀ u, Y.E.toClosedForm.energy u = limitFormEnergy GE u)
    (hYF : ∀ u, Y.F.toClosedForm.energy u = limitFormEnergy GF u)
    (hYcE : ∀ u, Yc.E.toClosedForm.energy u = limitFormEnergy GpE u)
    (hYcF : ∀ u, Yc.F.toClosedForm.energy u = limitFormEnergy GpF u)
    (t K : ℝ)
    (hgr : aux_prop_conc_pair_data_growth Yc (aux_prop_conc_pair_data_slopes d) t K) :
    ∀ (hw : Measurable ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
        (fun x => y x - omega j x)))
      (Kw : ℝ)
      (hKw : ∀ x, |(centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
        (fun x => y x - omega j x) x| ≤ Kw),
      aux_prop_conc_pair_data_growth
        (aux_prop_conc_pair_mask_pair Y
          ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
            (fun x => y x - omega j x)) hw Kw hKw)
        (aux_prop_conc_pair_data_slopes d) t K := by
  obtain ⟨hdomE, hdiagE, hdiagF⟩ := prop_conc_resampled_form_identification d hd model H zQ RQ hRQ
    zc rc hrc C0 m M S hS NE NF hNE hNF omega y j hcoef Y Yc GE GF GpE GpF hGE hGF hctrlE hctrlF
    hGpE hGpF hYE hYF hYcE hYcF
  exact fun hw Kw hKw =>
    (prop_conc_masked_measure_identification d hd zQ RQ hRQ zc rc hrc C0 m M Y Yc hYaff hYcaff
      (fun x => y x - omega j x) (y.continuous.sub (omega j).continuous) hdomE hdiagE hdiagF
      hw Kw hKw _ rfl).2.2.2 (aux_prop_conc_pair_data_slopes d) t K hgr

section Tail

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The almost sure conclusion of the growth of the canonically resampled pair, from typed data: the
represented operator limits at `ω` (as in `prop_conc_setup`), the tight control bank, the canonical
operator limits at chaos-a.e. `η`, and a chaos-a.e. tied affine pair `Yc` at `η` with growth constant `K η`.
The quantifier order is that of the growth statement: a.e. `ω`, every tied affine `Y`, a.e. `y`. -/
theorem aux_prop_conc_resampled_pair_growth_of_tied_tail
    (hd : 2 ≤ d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization model H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (C0 m M : ℝ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (GNi : ℕ → Ω → DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (GEi GFi : Ω → DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hGNdef : ∀ N omega f, GNi N omega f =
      (responseSolution S (cutoffPositiveCoefficient model H (field omega) N zQ hRQ)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : ∀ᵐ omega ∂P, Tendsto (fun n => GNi (NE n) omega) atTop (𝓝 (GEi omega)) ∧
      Tendsto (fun n => GNi (NF n) omega) atTop (𝓝 (GFi omega)))
    {ι : Type} [Countable ι] (F : ι → ℕ → BilateralField d → ℝ) (Cb : ι → ℝ≥0)
    (hmem : ∀ i n, MemLp (F i n) 1 (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ i n, eLpNorm (F i n) 1 (chaosSampleLaw model).toMeasure ≤ Cb i)
    (hcontrol : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      ∀ N : ℕ → ℕ, (∀ i, ∃ B : ℝ, ∀ n, |F i (N n) om| ≤ B) →
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
          (fun n => cutoffPositiveCoefficient model H om (N n) zQ hRQ)))
    (GNc : ℕ → BilateralField d →
      DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (GEc GFc : BilateralField d →
      DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hGNcdef : ∀ N eta f, GNc N eta f =
      (responseSolution S (cutoffPositiveCoefficient model H eta N zQ hRQ)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (K : BilateralField d → ℝ) (t : ℝ)
    (hT : ∀ᵐ eta ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => GNc (NE n) eta) atTop (𝓝 (GEc eta)) ∧
      Tendsto (fun n => GNc (NF n) eta) atTop (𝓝 (GFc eta)) ∧ 0 ≤ K eta ∧
      ∃ Yc : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M,
        (∀ u, Yc.E.toClosedForm.energy u = limitFormEnergy (GEc eta) u) ∧
        (∀ u, Yc.F.toClosedForm.energy u = limitFormEnergy (GFc eta) u) ∧
        aux_prop_conc_pair_data_affine Yc ∧
        aux_prop_conc_pair_data_growth Yc (aux_prop_conc_pair_data_slopes d) t (K eta))
    (j : ℤ) (hj : j ≤ 0) :
    ∀ᵐ omega ∂P,
      ∀ Y : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M,
        (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GEi omega) u) →
        (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GFi omega) u) →
        aux_prop_conc_pair_data_affine Y →
        ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
          0 ≤ K (Function.update (field omega) j y) ∧
          ∀ (hw : Measurable ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
              (fun x => y x - field omega j x)))
            (Kw : ℝ)
            (hKw : ∀ x, |(centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
              (fun x => y x - field omega j x) x| ≤ Kw),
            aux_prop_conc_pair_data_growth
              (aux_prop_conc_pair_mask_pair Y
                ((centeredCube zc rc hrc : Set (SpatialCoordinates d)).indicator
                  (fun x => y x - field omega j x)) hw Kw hKw)
              (aux_prop_conc_pair_data_slopes d) t (K (Function.update (field omega) j y)) := by
  have hcoef := aux_prop_conc_resampled_pair_growth_of_tied_coef_ae model H hIR P field hfield j hj
    zQ RQ hRQ
  have hctrl := aux_prop_conc_resampled_pair_growth_of_tied_ctrl_ae hd model H P field hfield zQ RQ
    hRQ S NE NF F Cb hmem hnorm hcontrol
  have heta := aux_prop_conc_resampled_pair_growth_of_tied_eta_ae model j P field hfield hT
  have hopeq : ∀ (N : ℕ → ℕ) (eta : BilateralField d),
      (fun n => volumeResponseOperator S (cutoffPositiveCoefficient model H eta (N n) zQ hRQ)) =
        fun n => GNc (N n) eta := by
    intro N eta
    funext n
    apply ContinuousLinearMap.ext
    intro f
    rw [volumeResponseOperator_apply, hGNcdef]
  filter_upwards [hlim, hcoef, hctrl, heta] with omega hlimω hcoefω hctrlω hetaω
  intro Y hYE hYF hYaff
  filter_upwards [hcoefω, hetaω] with y hcy hey
  obtain ⟨hGpE, hGpF, hK, Yc, hYcE, hYcF, hYcaff, hgr⟩ := hey
  refine ⟨hK, ?_⟩
  have hopω : ∀ (N : ℕ → ℕ),
      (fun n => volumeResponseOperator S (cutoffPositiveCoefficient model H (field omega) (N n) zQ hRQ)) =
        fun n => GNi (N n) omega := by
    intro N
    funext n
    apply ContinuousLinearMap.ext
    intro f
    rw [volumeResponseOperator_apply, hGNdef]
  exact prop_conc_resampled_pair_growth_of_tied d hd model H zQ RQ hRQ zc rc hrc C0 m M S hS NE NF
    hNE hNF (field omega) y j hcy Y Yc hYaff hYcaff (GEi omega) (GFi omega) (GEc _) (GFc _)
    (by rw [hopω NE]; exact hlimω.1) (by rw [hopω NF]; exact hlimω.2) hctrlω.1 hctrlω.2
    (by rw [hopeq NE]; exact hGpE) (by rw [hopeq NF]; exact hGpF) hYE hYF hYcE hYcF _ _ hgr

end Tail

end
end SubdiffusiveProcess.Paper
