module

public import SubdiffusiveProcess.Paper.prop_conc_form_gamma
public import SubdiffusiveProcess.Paper.prop_conc_actual_controls
public import SubdiffusiveProcess.Paper.prop_conc_controlled_affine_identification

@[expose] public section

/-! Actual one-cell affine identification for every supplied operator and response limit.
The disorder threshold precedes the model, cell and cutoff subsequence. The
conclusion uses only the energy measure on the observation cell. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- A response space with the killed graph equals the canonical killed response space. -/
theorem aux_prop_conc_actual_affine_identification_response_space
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (hS : S.space = killedSobolevGraph Q)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖) :
    S = killedResponseSpace hP := by
  cases S with
  | mk space hweak hclosed hp =>
    dsimp only at hS
    subst space
    rfl

/-- Each actual padded-cube operator limit identifies the normalized observation-cell matrix. -/
theorem prop_conc_actual_affine_identification
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (_hr1 : r ≤ 1)
        (h3r : 0 < 3 * r)
        (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (S : ResponseSpace (centeredCube z (3 * r) h3r)),
      S.space = killedSobolevGraph (centeredCube z (3 * r) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r))
        (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube z (3 * r) h3r))
        (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient M H om (N n) z h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      (∀ p : Fin d → ℝ,
        Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded z hr) hP
          (cutoffPositiveCoefficient M H om (N n) z hr) p /
          (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ A.mulVec p))) →
      Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube z (3 * r) h3r)
        (centeredCube z r hr : Set (SpatialCoordinates d)) G A) := by
  obtain ⟨deltaF, hdeltaF, hF⟩ := prop_conc_form_gamma d hd I Pin X W Cp Sob Interp
  obtain ⟨deltaC, hdeltaC, hC⟩ := prop_conc_actual_controls d hd I Pin X W Cp Sob Interp
    ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  refine ⟨min deltaF deltaC, lt_min hdeltaF hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1 h3r hP N
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  let hPQ := centeredCube_killedPoincare z h3r
  filter_upwards [hF M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z (3 * r) h3r hPQ N,
    hC M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z (3 * r) h3r
      (killedResponseSpace hPQ) rfl N] with om hform hcontrols
  intro S hS GN G A hGN hG hA
  have hSeq := aux_prop_conc_actual_affine_identification_response_space S hS hPQ
  subst S
  obtain ⟨E, hE, _hNC, hcore, _hreg, _hloc, Gamma⟩ := hform GN G hGN hG
  obtain ⟨Gamma⟩ := Gamma
  obtain ⟨seq, hseq, ⟨Controls⟩, hcell⟩ := hcontrols
  exact prop_conc_controlled_affine_identification hd z r hr hr1 h3r
    (killedResponseSpace hPQ) rfl
    (fun n => cutoffCoefficient M H om (N (seq n)))
    (fun n => cutoffCoefficient_continuous M H om (N (seq n)))
    (fun n x => cutoffCoefficient_pos M H om (N (seq n)) x)
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z h3r)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z h3r).2.2.2)
    Controls (fun n => GN (seq n)) G (fun n => hGN (seq n)) (hG.comp hseq.tendsto_atTop)
    E hE hcore Gamma ((d : ℝ) - 1 / 2) (3 / 4)
    (by linarith only []) (by linarith only []) (by norm_num) (by norm_num) hcell hP
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr)
    (fun n => (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2)
    A (fun p => (hA p).comp hseq.tendsto_atTop)

end
end Paper
