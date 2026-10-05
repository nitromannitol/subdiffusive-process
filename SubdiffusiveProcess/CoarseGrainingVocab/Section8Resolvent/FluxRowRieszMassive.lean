module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFourierClassical
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszDensity
public import SubdiffusiveProcess.Frozen.Section8.MassiveNegativeSobolevNormSq

@[expose] public section

/-!
# Massive weighted Fourier-space Riesz construction

This file performs the coordinatewise weighted Riesz construction at the end
of the deterministic stopping-partition localization argument.  Its input is
the global Schwartz-test bound produced by the finite local estimates and
partition exhaustion; its output is the actual Fourier representative used by
the frozen whole-space resolvent row, with the massive negative-Sobolev bound.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The positive massive frequency base `|xi|² + R⁻²`. -/
def fluxRowMassiveFrequencyBase {d : ℕ} (R : ℝ) (xi : Vec d) : ℝ :=
  vecNormSq xi + R⁻¹ ^ 2

/-- The reciprocal of the negative-Sobolev Fourier weight, as an `NNReal`
density for the weighted `L²` test space. -/
def fluxRowMassiveTestDensity {d : ℕ} (R sigma : ℝ) (xi : Vec d) : NNReal :=
  Real.toNNReal (fluxRowMassiveFrequencyBase R xi ^ sigma)

/-- Evaluation embeds scalar Schwartz tests linearly into ordinary
functions. -/
def fluxRowSchwartzTestLinear (d : ℕ) :
    SchwartzMap (Vec d) ℂ →ₗ[ℂ] Vec d → ℂ :=
  { toFun := fun phi ↦ phi
    map_add' := by
      intro phi psi
      funext x
      rfl
    map_smul' := by
      intro c phi
      funext x
      rfl }

theorem fluxRowMassiveFrequencyBase_pos {d : ℕ} {R : ℝ} (hR : 0 < R)
    (xi : Vec d) : 0 < fluxRowMassiveFrequencyBase R xi := by
  unfold fluxRowMassiveFrequencyBase
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  exact add_pos_of_nonneg_of_pos (vecNormSq_nonneg xi) (sq_pos_of_pos hRinv)

theorem fluxRowMassiveTestDensity_pos {d : ℕ} {R sigma : ℝ}
    (hR : 0 < R) (xi : Vec d) : 0 < fluxRowMassiveTestDensity R sigma xi := by
  unfold fluxRowMassiveTestDensity
  rw [Real.toNNReal_pos]
  exact Real.rpow_pos_of_pos (fluxRowMassiveFrequencyBase_pos hR xi) _

theorem measurable_fluxRowMassiveTestDensity {d : ℕ} {R : ℝ} (hR : 0 < R)
    (sigma : ℝ) :
    Measurable (fluxRowMassiveTestDensity (d := d) R sigma) := by
  apply Measurable.real_toNNReal
  apply Continuous.measurable
  apply Continuous.rpow_const
  · unfold fluxRowMassiveFrequencyBase vecNormSq vecDot
    fun_prop
  · intro xi
    exact Or.inl (fluxRowMassiveFrequencyBase_pos hR xi).ne'

theorem coe_fluxRowMassiveTestDensity {d : ℕ} {R sigma : ℝ}
    (hR : 0 < R) (xi : Vec d) :
    (fluxRowMassiveTestDensity R sigma xi : ℝ) =
      fluxRowMassiveFrequencyBase R xi ^ sigma := by
  rw [fluxRowMassiveTestDensity, Real.coe_toNNReal]
  exact (Real.rpow_pos_of_pos (fluxRowMassiveFrequencyBase_pos hR xi) _).le

theorem inv_coe_fluxRowMassiveTestDensity {d : ℕ} {R sigma : ℝ}
    (hR : 0 < R) (xi : Vec d) :
    (fluxRowMassiveTestDensity R sigma xi : ℝ)⁻¹ =
      fluxRowMassiveFrequencyBase R xi ^ (-sigma) := by
  rw [coe_fluxRowMassiveTestDensity hR, Real.rpow_neg
    (fluxRowMassiveFrequencyBase_pos hR xi).le]

/-- **Weighted Fourier-space Riesz construction.**  A coordinatewise global
Schwartz-test estimate produces a single vector-valued Fourier representative
and its massive negative-Sobolev estimate.

The hypotheses `htest` and `hbound` are exactly the analytic outputs of the
stopping-partition localization: `htest` places Schwartz tests in the massive
positive weighted space, while `hbound` is obtained by exhausting the
partition and applying `fluxRowDeterministicLocalization` to finite
subfamilies. -/
theorem exists_fluxHat_massiveNegativeSobolevNormSq_le_of_schwartz_bound
    {d : ℕ} {R sigma : ℝ} (hR : 0 < R) (F : Vec d → Vec d)
    (htest : ∀ phi : SchwartzMap (Vec d) ℂ,
      MemLp (phi : Vec d → ℂ) 2
        (volume.withDensity fun xi ↦ fluxRowMassiveTestDensity R sigma xi))
    (L : Fin d → SchwartzMap (Vec d) ℂ →ₗ[ℂ] ℂ)
    (hphysical : ∀ i phi,
      Integrable
          (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x)
          volume ∧
        L i phi =
          ∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i phi, ‖L i phi‖ ≤
      C i * ‖fluxRowWeightedTestToLp volume
        (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
        htest phi‖) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤ ∑ i, C i ^ 2 := by
  have hex : ∀ i : Fin d,
      ∃ h : Lp ℂ 2
          (volume.withDensity fun xi ↦ fluxRowMassiveTestDensity R sigma xi),
        ‖h‖ ≤ C i ∧
        let representative : Vec d → ℂ := fun xi ↦
          conj (h xi) * (fluxRowMassiveTestDensity R sigma xi : ℂ)
        ∀ phi, Integrable (fun xi ↦ representative xi * phi xi) volume ∧
          L i phi = ∫ xi, representative xi * phi xi ∂volume := by
    intro i
    exact exists_weighted_riesz_density_representative volume
      (fluxRowMassiveTestDensity R sigma)
      (measurable_fluxRowMassiveTestDensity hR sigma)
      (fluxRowSchwartzTestLinear d) htest (L i) (C i) (hC i) (hbound i)
  choose h hh hrepr using hex
  let fluxHat : Vec d → Fin d → ℂ := fun xi i ↦
    conj (h i xi) * (fluxRowMassiveTestDensity R sigma xi : ℂ)
  refine ⟨fluxHat, ?_, ?_⟩
  · intro i phi
    obtain ⟨hleft, hL⟩ := hphysical i phi
    obtain ⟨hright, hRiesz⟩ := hrepr i phi
    exact ⟨hleft, hright, hL.symm.trans hRiesz⟩
  · have hcoordInt : ∀ i : Fin d, Integrable (fun xi ↦
        (fluxRowMassiveTestDensity R sigma xi : ℝ)⁻¹ *
          ‖fluxHat xi i‖ ^ 2) volume := by
      intro i
      exact integrable_inv_density_mul_norm_sq_representative volume
        (fluxRowMassiveTestDensity R sigma)
        (measurable_fluxRowMassiveTestDensity hR sigma)
        (fluxRowMassiveTestDensity_pos hR) (h i)
    rw [massiveNegativeSobolevNormSq]
    calc
      ∫ xi, (vecNormSq xi + R⁻¹ ^ 2) ^ (-sigma) *
          ∑ i, ‖fluxHat xi i‖ ^ 2 ∂volume =
          ∫ xi, ∑ i, (fluxRowMassiveTestDensity R sigma xi : ℝ)⁻¹ *
            ‖fluxHat xi i‖ ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards with xi
        change fluxRowMassiveFrequencyBase R xi ^ (-sigma) *
          ∑ i, ‖fluxHat xi i‖ ^ 2 = _
        rw [← inv_coe_fluxRowMassiveTestDensity hR]
        rw [Finset.mul_sum]
      _ = ∑ i, ∫ xi, (fluxRowMassiveTestDensity R sigma xi : ℝ)⁻¹ *
          ‖fluxHat xi i‖ ^ 2 ∂volume := by
        rw [integral_finsetSum]
        exact fun i _ ↦ hcoordInt i
      _ = ∑ i, ‖h i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_inv_density_mul_norm_sq_representative_eq_norm_sq volume
          (fluxRowMassiveTestDensity R sigma)
          (measurable_fluxRowMassiveTestDensity hR sigma)
          (fluxRowMassiveTestDensity_pos hR) (h i)
      _ ≤ ∑ i, C i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq₀ (norm_nonneg _) (hC i)).2 (hh i)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
