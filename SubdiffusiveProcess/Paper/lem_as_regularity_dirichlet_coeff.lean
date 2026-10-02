import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_limit
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Main.InfraredCharacterization
import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingForcing

/-! Uniform convergence of the truncated physical coefficients on compact sets, and the
`L²` membership of the datum. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped Topology ENNReal
noncomputable section
namespace Paper

/-- The physical coefficient as a continuous map, as a function of the infrared field. -/
def aux_lem_as_regularity_dirichlet_coeff_Psi {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (N : ℕ) (z0 : SpatialCoordinates d)
    (f : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  let φ : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun y => (3 : ℝ) ^ (-(N : ℤ)) • y + z0, by fun_prop⟩
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
    ((⟨Real.exp, Real.continuous_exp⟩ : C(ℝ, ℝ)).comp
      (f.comp φ +
        ((∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).comp φ) -
          ContinuousMap.const _ (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))))

theorem aux_lem_as_regularity_dirichlet_coeff_Psi_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) (f : C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) :
    aux_lem_as_regularity_dirichlet_coeff_Psi M omega N z0 f y =
      cutoffCoefficient M (fun _ => f) omega N ((3 : ℝ) ^ (-(N : ℤ)) • y + z0) := by
  unfold aux_lem_as_regularity_dirichlet_coeff_Psi cutoffCoefficient cutoffPotential
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.const_apply,
    ContinuousMap.coe_mk, smul_eq_mul]
  congr 2
  ring

theorem aux_lem_as_regularity_dirichlet_coeff_Psi_continuous {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N : ℕ)
    (z0 : SpatialCoordinates d) :
    Continuous (aux_lem_as_regularity_dirichlet_coeff_Psi M omega N z0) := by
  unfold aux_lem_as_regularity_dirichlet_coeff_Psi
  refine continuous_const.smul ((ContinuousMap.continuous_postcomp _).comp ?_)
  exact (ContinuousMap.continuous_precomp _).add continuous_const

/-- Uniform convergence on compact sets of the truncated coefficients. -/
theorem lem_as_regularity_dirichlet_coeff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z0 : SpatialCoordinates d)
    (hlim : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L' : ℕ in atTop, ∀ y ∈ K,
      |cutoffCoefficient M H omega N ((3 : ℝ) ^ (-(N : ℤ)) • y + z0) -
        cutoffCoefficient M (fun om => infraredPartialSum om L') omega N
          ((3 : ℝ) ^ (-(N : ℤ)) • y + z0)| ≤ ε := by
  intro ε hε
  have hΨ := ((aux_lem_as_regularity_dirichlet_coeff_Psi_continuous M omega N z0).tendsto
    (H omega)).comp hlim
  have hU := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hΨ) K hK
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU ε hε] with L' hL' y hy
  have := hL' y hy
  simp only [Function.comp_apply, aux_lem_as_regularity_dirichlet_coeff_Psi_apply, Real.dist_eq]
    at this
  exact this.le

/-- A positive continuous function on a nonempty compact set has positive lower and finite upper
bounds. -/
theorem aux_lem_as_regularity_dirichlet_coeff_bounds {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty) {a : X → ℝ} (hc : Continuous a)
    (hpos : ∀ x, 0 < a x) : ∃ lam0 Lam0 : ℝ, 0 < lam0 ∧ ∀ x ∈ K, lam0 ≤ a x ∧ a x ≤ Lam0 := by
  obtain ⟨xm, hxm, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
  obtain ⟨xM, hxM, hmax⟩ := hK.exists_isMaxOn hKne hc.continuousOn
  exact ⟨a xm, a xM, hpos xm, fun x hx => ⟨hmin hx, hmax hx⟩⟩

end Paper
