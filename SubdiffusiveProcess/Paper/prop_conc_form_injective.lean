module

public import SubdiffusiveProcess.Paper.prop_conc_mesh_native_subsequence
public import SubdiffusiveProcess.Sobolev.CubeUniformError
public import SubdiffusiveProcess.Sobolev.SmoothSourceDensity
public import SubdiffusiveProcess.Sobolev.ResponseSubsequenceInjectivity

@[expose] public section

/-! Injectivity of every supplied norm limit of the actual killed inverse operators.
Local harmonic mesh approximations supply the required bounded energies along
further subsequences. No uniqueness of different inverse limits is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

namespace Paper
noncomputable section

/-- The actual local mesh approximation makes every supplied killed-inverse norm limit injective. -/
theorem prop_conc_form_injective
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
      Tendsto GN atTop (𝓝 G) → Function.Injective G := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_mesh_native_subsequence d hd I Pin X W Cp Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr N] with om hom
  intro GN G hGN hG
  let D : Set (DomainL2 (centeredCube z r hr)) := {f | ∃ fc : SpatialCoordinates d → ℝ,
    ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc}
  have hD : Dense D := SmoothSources.dense_smooth_compact_support
    (centeredCube z r hr).isOpen (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
  let a : ℕ → PositiveCoefficient (centeredCube z r hr) :=
    fun n => cutoffPositiveCoefficient M H om (N n) z hr
  apply injective_limit_of_volumeResponse_subsequence_approximations
    (killedResponseSpace hP) a G D hD
  · intro f
    have happ : Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hG
    have hpair : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner happ
    apply hpair.congr
    intro n
    rw [hGN n f, inverseResponse_eq_load]
    rfl
  · intro phi hphi eps heps
    obtain ⟨fc, hfc, hcompact, hsupp, hrep⟩ := hphi
    let V : ℝ := Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
    have hV : 0 ≤ V := Real.sqrt_nonneg _
    have hden : 0 < V + 1 := by linarith only [hV]
    let eta : ℝ := eps / (V + 1)
    have heta : 0 < eta := div_pos heps hden
    obtain ⟨seq, hmono, w, B, hw⟩ := hom fc hfc hcompact hsupp eta heta
    let v : ℕ → (killedResponseSpace hP).space := fun n =>
      ⟨sobolevDataOfH1 (w n).toH1Function, sobolevDataOfH1_mem_killed (w n)⟩
    refine ⟨seq, hmono, v, B, ?_, ?_⟩
    · intro n
      have hc := (cutoffPositiveCoefficient_representative M H om (N (seq n)) z hr).2.2.2
      change sobolevCoefficientForm (a (seq n)) (sobolevDataOfH1 (w n).toH1Function)
        (sobolevDataOfH1 (w n).toH1Function) ≤ B
      rw [← energy_eq_sobolevCoefficientForm (a (seq n)) _ hc (w n).toH1Function]
      exact (hw n).1
    · intro n
      have hb := cube_norm_sub_le_of_uniform_error z hr (w n).toH1Function.toFun fc eta heta.le
        (fun x hx => ((hw n).2.2 x hx).le) (v n).val.1 phi
        (sobolevDataOfH1_fst_coeFn (w n).toH1Function) hrep
      refine hb.trans ?_
      change V * (eps / (V + 1)) ≤ eps
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith only [heps]

end
end Paper
