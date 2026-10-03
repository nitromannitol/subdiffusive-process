module

public import SubdiffusiveProcess.Paper.prop_conc_form_continuity
public import SubdiffusiveProcess.Paper.prop_conc_cutoff_growth_all_cubes

@[expose] public section

/-! Smooth-source continuity for the actual supplied cutoff inverse limits.
The growth bounds are produced here on the original field law; this theorem
does not claim existence of a form core or identify local boundary minima. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

namespace Paper
noncomputable section

/-- Actual cutoff growth supplies continuous zero-boundary representatives of every smooth-source inverse limit. -/
theorem prop_conc_form_continuous_all_cubes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ]
          DomainL2 (centeredCube z r hr))
        (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om (N n) z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧
        HasCompactSupport fc ∧ tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((G f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
  obtain ⟨delta0, hdelta0, hbank⟩ := prop_conc_cutoff_growth_all_cubes d hd I Pin X W Cp Sob
    ((d : ℝ) - 1 / 2) (1 / 2) 1 (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num) le_rfl
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  obtain ⟨_, _, hN⟩ := hbank M Rm Sreg It H hIR hdelta z r hr
  obtain ⟨K, _, hKpos, _, hgrowth⟩ := hN N
  filter_upwards [hgrowth] with om hom
  obtain ⟨seq, hseq, hbound⟩ := hom
  intro GN G hGN hG f hf
  have hD : ∀ n, aux_prop_conc_form_cutoff_continuity_DirProp z r hr
      (cutoffPositiveCoefficient M H om (N (seq n)) z hr) (K om) := by
    intro n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    exact (hbound n F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve).2
  exact prop_conc_form_continuity hd z r hr hP
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr) (K om) (hKpos om).le hD
    (fun n => GN (seq n)) (fun n f => hGN (seq n) f) G
    (hG.comp hseq.tendsto_atTop) f hf

end
end Paper
