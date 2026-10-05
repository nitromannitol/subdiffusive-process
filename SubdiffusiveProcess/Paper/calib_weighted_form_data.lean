module

public import SubdiffusiveProcess.Paper.calib_weighted_green_limit
public import SubdiffusiveProcess.Paper.prop_conc_masked_form_data
public import SubdiffusiveProcess.Paper.infrared_cutoff_coefficient_reduction
public import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
public import SubdiffusiveProcess.EllipticRegularity.CutoffCoefficientRepresentative
public import SubdiffusiveProcess.VariationalResponses.LimitForm

@[expose] public section

/-! Preparation for the boundary identification of the infrared-free responses: the clipped weight, the uniform
defect of the infrared potentials on a cube, the weighted form of a regular strongly local form, and the
comparison of the three cutoff coefficients involved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ### The clipped weight -/

open Classical in
/-- `-hinf` on the closure of a set, `0` outside: a bounded Borel function agreeing with `-hinf` on the closure. -/
def aux_calib_weighted_form_data_G {d : ℕ} (hinf : C(SpatialCoordinates d, ℝ)) (Q : Set (SpatialCoordinates d))
    (x : SpatialCoordinates d) : ℝ :=
  if x ∈ closure Q then -hinf x else 0

theorem aux_calib_weighted_form_data_G_measurable {d : ℕ} (hinf : C(SpatialCoordinates d, ℝ)) (Q : Set (SpatialCoordinates d)) :
    Measurable (aux_calib_weighted_form_data_G hinf Q) := by
  unfold aux_calib_weighted_form_data_G
  exact Measurable.ite isClosed_closure.measurableSet hinf.continuous.measurable.neg measurable_const

theorem aux_calib_weighted_form_data_G_of_mem {d : ℕ} (hinf : C(SpatialCoordinates d, ℝ)) (Q : Set (SpatialCoordinates d))
    {x : SpatialCoordinates d} (hx : x ∈ closure Q) : aux_calib_weighted_form_data_G hinf Q x = -hinf x := by
  unfold aux_calib_weighted_form_data_G; rw [ite_eq_left hx]

theorem aux_calib_weighted_form_data_G_bounded {d : ℕ} (hinf : C(SpatialCoordinates d, ℝ)) (Q : Set (SpatialCoordinates d))
    (hQ : IsCompact (closure Q)) : ∃ K : ℝ, ∀ x, |aux_calib_weighted_form_data_G hinf Q x| ≤ K := by
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hinf.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  unfold aux_calib_weighted_form_data_G
  split_ifs with hx
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    rw [abs_neg]
    exact this.trans (le_max_left _ _)
  · simp

theorem aux_calib_weighted_form_data_G_continuousOn {d : ℕ} (hinf : C(SpatialCoordinates d, ℝ)) (Q : Set (SpatialCoordinates d)) :
    ContinuousOn (fun x => Real.exp (aux_calib_weighted_form_data_G hinf Q x)) (closure Q) := by
  have hc : ContinuousOn (fun x => Real.exp (-hinf x)) (closure Q) :=
    (Real.continuous_exp.comp hinf.continuous.neg).continuousOn
  refine hc.congr fun x hx => ?_
  rw [aux_calib_weighted_form_data_G_of_mem hinf Q hx]

/-! ### Uniform defect on a compact set -/

/-- Convergence in `C(X, ℝ)` gives a uniform defect bound on every compact set. -/
theorem aux_calib_weighted_form_data_uniform_defect {X : Type*} [TopologicalSpace X] (hinf : C(X, ℝ)) (h : ℕ → C(X, ℝ))
    (hh : Tendsto h atTop (𝓝 hinf)) (K : Set X) (hK : IsCompact K) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ Tendsto D atTop (𝓝 0) ∧
      ∀ n, ∀ x ∈ K, |h n x - hinf x| ≤ D n := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine ⟨fun n => ‖(h n).restrict K - hinf.restrict K‖, fun n => norm_nonneg _, ?_, ?_⟩
  · have h1 : Tendsto (fun n => (h n).restrict K) atTop (𝓝 (hinf.restrict K)) :=
      ((ContinuousMap.continuous_restrict K).tendsto hinf).comp hh
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h1)
  · intro n x hx
    have := ContinuousMap.norm_coe_le_norm ((h n).restrict K - hinf.restrict K) ⟨x, hx⟩
    simpa [Real.norm_eq_abs] using this

/-! ### The weighted form of a regular strongly local form -/

/-- The weighted form `E^{exp g}` of a regular strongly local form: a form with a core, strong locality, an energy
measure and the weighted-form identities. -/
theorem calib_weighted_form_data {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ S, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    ∃ (Eg : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (_Gammag : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg.toClosedForm),
      (∃ S, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eg.toClosedForm (Q : Set (SpatialCoordinates d)) S) ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal Eg.toClosedForm ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm Eg.toClosedForm GammaE
        (fun x => Real.exp (g x)) := by
  have hreg := aux_prop_conc_core_measure_data_isRegular_of_core Q E.toClosedForm hcore
  have halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm :=
    ⟨hreg, _root_.SubdiffusiveProcess.DirichletForm.mul_mem E, _root_.SubdiffusiveProcess.DirichletForm.comp_mem E,
      _root_.SubdiffusiveProcess.DirichletForm.mul_comp_mem E, _root_.SubdiffusiveProcess.DirichletForm.mul_mem_of_bounded E⟩
  obtain ⟨Eg, Gammag, hdom, hform, _hregg, hcoreg, hlocg, _hcross⟩ :=
    lem_borel_weights_form E GammaE g hg K hK hreg hcore hloc halg
  have hexp : ∀ x, |Real.exp (g x)| ≤ Real.exp K := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x))
  have hdiag : ∀ u ∈ E.domain, Eg.form u u = ∫ x, Real.exp (g x) ∂(GammaE.measure u) := by
    intro u hu
    rw [hform u hu u hu, _root_.SubdiffusiveProcess.DirichletForm.aux_signedIntegralOn_cross_self E.toClosedForm
      GammaE u hu (fun x => Real.exp (g x)) ⟨hg.exp, ⟨Real.exp K, hexp⟩⟩, Measure.restrict_univ]
  exact ⟨Eg, Gammag, hcoreg, hlocg, ⟨hdom, hdiag, hform⟩⟩

end SubdiffusiveProcess.Paper
