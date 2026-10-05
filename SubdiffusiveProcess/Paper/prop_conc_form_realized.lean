module

public import SubdiffusiveProcess.Paper.prop_conc_form_injective
public import SubdiffusiveProcess.Paper.inputs_classical_killed_inverse_compact
public import SubdiffusiveProcess.Paper.in_represented_mosco
public import SubdiffusiveProcess.Paper.inputs_contraction_witness
public import SubdiffusiveProcess.Paper.prop_killed_inverse_spectral_square_root
public import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form

@[expose] public section

/-! Realize the quadratic dual energy of each supplied actual inverse limit.
The witness is a Dirichlet form with normal contractions and its spectral root.
Regularity, strong locality, energy measures and boundary minima are not asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The actual supplied inverse limit defines a Dirichlet form with exactly its quadratic dual energy. -/
theorem prop_conc_form_realized
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
          ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
        (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om (N n) z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
        _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E ∧
        Function.Injective G ∧
        ∃ R : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
          (∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) ∧
          (∀ x, 0 ≤ inner ℝ x (R x)) ∧
          R.comp R = G ∧ limitFormDomain G = Set.range R := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_form_injective d hd I Pin X W Cp Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr hP N] with om hom
  intro GN G hGN hG
  have hinj := hom GN G hGN hG
  let a : ℕ → PositiveCoefficient (centeredCube z r hr) :=
    fun n => cutoffPositiveCoefficient M H om (N n) z hr
  have hcompact : IsCompactOperator G := isCompactOperator_of_tendsto hG
    (Filter.Eventually.of_forall fun n =>
      inputs_classical_killed_inverse_compact d hd z r hr hP (a n) (GN n) (hGN n))
  obtain ⟨hsympair, hlower, hrec⟩ := aux_in_represented_mosco_free d hd M H om z r hr
    (killedResponseSpace hP) G N GN hGN hG
  have hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    exact (real_inner_comm (G x) y).symm.trans (hsympair y x)
  have hpos : ∀ x, 0 ≤ inner ℝ x (G x) := by
    intro x
    have happ : Tendsto (fun n => GN n x) atTop (𝓝 (G x)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hG
    have hpair : Tendsto (fun n => inner ℝ x (GN n x)) atTop (𝓝 (inner ℝ x (G x))) :=
      tendsto_const_nhds.inner happ
    apply ge_of_tendsto' hpair
    intro n
    rw [hGN n x]
    exact volumeResponse_pairing_nonneg (killedResponseSpace hP) (a n) x
  have hroot := prop_killed_inverse_spectral_square_root G hcompact hsym hpos hinj
  have hcontract := fun n T hT u => inputs_contraction_witness d z r hr
    (killedResponseSpace hP) rfl (a n) T hT u
  obtain ⟨E, hE, hNC⟩ := prop_killed_inverse_dirichlet_form (killedResponseSpace hP)
    a G hsym hpos hinj hroot ⟨hlower, hrec⟩ hcontract
  exact ⟨E, hE, hNC, hinj, hroot⟩

end
end SubdiffusiveProcess.Paper
