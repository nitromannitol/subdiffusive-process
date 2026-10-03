module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.thm_C0

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

/-- The conclusion of `thm_C0` (with the hoisted exponents `t`, `beta` and the represented bounds hypothesis) once
the geometry hypotheses `hLlarge hCdPad` are supplied, as a predicate (text of the header of `thm_C0`). -/
def aux_thm_prop_env_C0core (d : ℕ) (hd : 2 ≤ d) (I : Paper.in_J d)
    (alpha eta t beta : ℝ) : Prop :=
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (Gcatalog : Set Ω)
        (hGcatalogMeas : MeasurableSet Gcatalog)
        (hGcatalogFull : P Gcatalogᶜ = 0),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (Lane4.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (Lane4.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr S GE GF NE NF →
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
        ∀ omega ∈ G, ∀ i : ℕ,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)) ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              C0 * (limitFormEnergy (GE i omega) u).toReal

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

/-- **The two-sided comparison of the limits from `thm_C0`**, for a catalogue of the actual model. -/
theorem aux_thm_prop_env_hcomp_of_core (d : ℕ) (hd : 2 ≤ d) (I : Paper.in_J d)
    (alpha eta t beta : ℝ) (hC0 : aux_thm_prop_env_C0core d hd I alpha eta t beta) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        aux_conv_represented_env_interface_joint d model H Ω P field env env z r hr Sspace
          GNE GNF GE GF NE NF →
        conv_represented_catalogue_grids d hd model H Ω P env env z r hr Sspace NE NF alpha eta
          I beta t →
        aux_conv_represented_env_interface_bounds d hd model H Ω P env env z r hr Sspace GE GF
          NE NF →
        ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega := by
  obtain ⟨delta0, C0, hd0, hC01, hall⟩ := hC0
  refine ⟨delta0, C0, hd0, hC01, ?_⟩
  intro _ _ model hδ Rm Sreg It H Ω _ P _ field env z r hr Sspace GNE GNF GE GF NE NF hjoint hcat hB
  obtain ⟨cR, cC, respE, respF, eventE, eventF, root, hunit, Dcat, hDcat, fcat, trace, traceH1,
    usrcE, usrcF, srcE, srcF, ucellE, ucellF, Cext, beta', t', I', cK, eK, lK, sRK, sGK, sHK,
    cRK, cGK, cHK, origin, gridRoot, gridKey, hanchor, hgrid, hbuf, hE, hF⟩ := hcat
  obtain ⟨rfl, rfl, rfl⟩ := hanchor
  obtain ⟨G, hGm, hG0, hGsub, hG⟩ := hall model hδ Rm Sreg It H Ω P field env env cR cC respE respF
    eventE eventF z r hr Sspace GNE GNF GE GF NE NF Set.univ MeasurableSet.univ (by simp)
    ⟨hjoint.1, hjoint.2.1, hjoint.2.2.1, hjoint.2.2.2.1, hjoint.2.2.2.2.1, hjoint.2.2.2.2.2.1,
      hjoint.2.2.2.2.2.2.1, hjoint.2.2.2.2.2.2.2.1, hjoint.2.2.2.2.2.2.2.2.1,
      hjoint.2.2.2.2.2.2.2.2.2.1, hjoint.2.2.2.2.2.2.2.2.2.2,
      ⟨root, hunit, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcE, srcF, ucellE, ucellF,
        Cext, I', cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot, gridKey, hE, hF⟩⟩ hB
  filter_upwards [ae_iff.mpr hG0] with omega hω i
  have h := hG omega (by simpa using hω) i
  exact ⟨h.2.2.1, h.2.2.2⟩

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

theorem aux_thm_prop_env_C0core_of_thmC0 (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd) (Step : Paper.cutoff_good_scale_input d)
    (W : Lane4.SmallPerturbationInput d) (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (alpha : ℝ) (h1 : 127 / 128 < alpha) (h2 : alpha < 1) :
    aux_thm_prop_env_C0core d hd I alpha (1 / 128) ((d : ℝ) - 1 / 2) (127 / 128) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  obtain ⟨H0, hH0⟩ := aux_thm_prop_Llarge (6 * (d : ℝ)) (1 / 4) (by linarith) (by norm_num)
  have hLlarge := hH0 (H0 + 1) (Nat.le_succ _)
  have hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Nat.card {i : OddGridIndex d (Lane3.subdivisionHalfWidth (H0 + 1)) //
        ¬ Metric.closedBall (oddGridCenter zP R (Lane3.subdivisionHalfWidth (H0 + 1)) i)
            (3 * (R / ((3 : ℝ) ^ (H0 + 1))) / 2) ⊆
          (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
        (6 * (d : ℝ)) * ((3 : ℝ) ^ (H0 + 1)) ^ ((d : ℝ) - 1) := by
    intro zP R hR
    refine (aux_thm_prop_CdPad d hd (H0 + 1) zP R hR).trans ?_
    have hpos : 0 ≤ ((3 : ℝ) ^ (H0 + 1)) ^ ((d : ℝ) - 1) := by positivity
    nlinarith
  have := thm_C0 d hd I X Sob Step W Pin D Cp (1 / 4) (by norm_num) (by norm_num) (32 * d) (1 / 32)
    alpha (1 / 128) (by nlinarith) (by norm_num) (by norm_num) (by linarith) h2 (by norm_num)
    (by norm_num) (by linarith) (H0 + 1) (Nat.succ_pos _) (6 * (d : ℝ)) le_rfl
    ((d : ℝ) - 1 / 2) (127 / 128) (by linarith) (by linarith) (by norm_num) h1
  exact this hLlarge hCdPad


/-- **Two-sided comparison for a catalogue of the actual model** (`thm_C0` with the density scale and
padding count chosen for `6 d`; `t = d - 1/2`, `beta = 127/128`, `eta = 1/128`). -/
theorem thm_prop_env_comparison (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd) (Step : Paper.cutoff_good_scale_input d)
    (W : Lane4.SmallPerturbationInput d) (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (alpha : ℝ) (h1 : 127 / 128 < alpha) (h2 : alpha < 1) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        aux_conv_represented_env_interface_joint d model H Ω P field env env z r hr Sspace
          GNE GNF GE GF NE NF →
        conv_represented_catalogue_grids d hd model H Ω P env env z r hr Sspace NE NF alpha
          (1 / 128) I (127 / 128) ((d : ℝ) - 1 / 2) →
        aux_conv_represented_env_interface_bounds d hd model H Ω P env env z r hr Sspace GE GF
          NE NF →
        ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega := by
  obtain ⟨delta0, C0, hd0, hC01, hall⟩ := aux_thm_prop_env_hcomp_of_core d hd I alpha
    (1 / 128) ((d : ℝ) - 1 / 2) (127 / 128)
    (aux_thm_prop_env_C0core_of_thmC0 d hd I X Sob Step W Pin D Cp alpha h1 h2)
  exact ⟨delta0, C0, hd0, hC01, fun model hδ => hall model hδ⟩

end Part2

end Paper
end
