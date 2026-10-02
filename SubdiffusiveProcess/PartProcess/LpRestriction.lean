import SubdiffusiveProcess.PartProcess.Data
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem restrictLp_coe (U : Set X) (u : Lp ℝ 2 m) :
    ⇑(restrictLp U u) =ᵐ[m.restrict U] ⇑u :=
  ((Lp.memLp u).restrict U).coeFn_toLp

theorem restrictLp_add (U : Set X) (u v : Lp ℝ 2 m) :
    restrictLp U (u + v) = restrictLp U u + restrictLp U v := by
  apply Lp.ext
  filter_upwards [restrictLp_coe U (u + v), restrictLp_coe U u,
    restrictLp_coe U v, Lp.coeFn_add (restrictLp U u) (restrictLp U v),
    (Lp.coeFn_add u v).restrict (s := U)] with x h0 h1 h2 h3 h4
  simp only [h0, h3, Pi.add_apply, h1, h2, h4]

theorem restrictLp_smul (U : Set X) (a : ℝ) (u : Lp ℝ 2 m) :
    restrictLp U (a • u) = a • restrictLp U u := by
  apply Lp.ext
  filter_upwards [restrictLp_coe U (a • u), restrictLp_coe U u,
    Lp.coeFn_smul a (restrictLp U u), (Lp.coeFn_smul a u).restrict (s := U)]
    with x h0 h1 h2 h3
  simp only [h0, h2, Pi.smul_apply, h1, h3]

theorem norm_restrictLp_le (U : Set X) (u : Lp ℝ 2 m) :
    ‖restrictLp U u‖ ≤ ‖u‖ := by
  rw [restrictLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).2.ne
    (eLpNorm_mono_measure u Measure.restrict_le_self)

/-- Restriction as a continuous linear map. -/
def restriction (U : Set X) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 (m.restrict U) :=
  LinearMap.mkContinuous
    { toFun := restrictLp U
      map_add' := restrictLp_add U
      map_smul' := restrictLp_smul U }
    1 (by intro u; simpa using norm_restrictLp_le U u)

/-- Extension by zero from the restricted measure. -/
def extendLp (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 (m.restrict U)) : Lp ℝ 2 m :=
  ((memLp_indicator_iff_restrict hU).2 (Lp.memLp u)).toLp (U.indicator u)

theorem extendLp_coe (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 (m.restrict U)) : ⇑(extendLp U hU u) =ᵐ[m] U.indicator u :=
  MemLp.coeFn_toLp _

theorem extendLp_add (U : Set X) (hU : MeasurableSet U)
    (u v : Lp ℝ 2 (m.restrict U)) :
    extendLp U hU (u + v) = extendLp U hU u + extendLp U hU v := by
  classical
  apply Lp.ext
  filter_upwards [extendLp_coe U hU (u + v), extendLp_coe U hU u,
    extendLp_coe U hU v, Lp.coeFn_add (extendLp U hU u) (extendLp U hU v),
    ae_imp_of_ae_restrict (Lp.coeFn_add u v)] with x h0 h1 h2 h3 h4
  rw [h0, h3]
  simp only [Pi.add_apply, h1, h2]
  by_cases hx : x ∈ U
  · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using h4 hx
  · simp [Set.indicator_of_notMem hx]

theorem extendLp_smul (U : Set X) (hU : MeasurableSet U)
    (a : ℝ) (u : Lp ℝ 2 (m.restrict U)) :
    extendLp U hU (a • u) = a • extendLp U hU u := by
  classical
  apply Lp.ext
  filter_upwards [extendLp_coe U hU (a • u), extendLp_coe U hU u,
    Lp.coeFn_smul a (extendLp U hU u), ae_imp_of_ae_restrict (Lp.coeFn_smul a u)]
    with x h0 h1 h2 h3
  rw [h0, h2]
  simp only [Pi.smul_apply, h1]
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx, h3 hx]
  · simp [Set.indicator_of_notMem hx]

theorem norm_extendLp (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 (m.restrict U)) : ‖extendLp U hU u‖ = ‖u‖ := by
  rw [extendLp, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hU, Lp.norm_def]

def extension (U : Set X) (hU : MeasurableSet U) :
    Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := extendLp U hU
      map_add' := extendLp_add U hU
      map_smul' := extendLp_smul U hU }
    1 (by intro u; simp [norm_extendLp])

def extensionIsometry (U : Set X) (hU : MeasurableSet U) :
    Lp ℝ 2 (m.restrict U) →ₗᵢ[ℝ] Lp ℝ 2 m where
  toLinearMap := (extension U hU).toLinearMap
  norm_map' := norm_extendLp U hU

theorem inner_extend (U : Set X) (hU : MeasurableSet U)
    (u v : Lp ℝ 2 (m.restrict U)) :
    inner ℝ (extendLp U hU u) (extendLp U hU v) = inner ℝ u v :=
  (extensionIsometry U hU).inner_map_map u v

theorem inner_restrict_extend (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 m) (v : Lp ℝ 2 (m.restrict U)) :
    inner ℝ u (extendLp U hU v) = inner ℝ (restrictLp U u) v := by
  classical
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℝ (u x) (extendLp U hU v x) ∂m) =
        ∫ x, U.indicator (fun x => inner ℝ (u x) (v x)) x ∂m := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe U hU v] with x hx
      rw [hx]
      by_cases h : x ∈ U <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    _ = ∫ x in U, inner ℝ (u x) (v x) ∂m := integral_indicator hU
    _ = ∫ x in U, inner ℝ (restrictLp U u x) (v x) ∂m := by
      apply integral_congr_ae
      filter_upwards [restrictLp_coe U u] with x hx
      rw [hx]

theorem restrict_extend (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 (m.restrict U)) : restrictLp U (extendLp U hU u) = u := by
  apply Lp.ext
  filter_upwards [restrictLp_coe U (extendLp U hU u),
    (extendLp_coe U hU u).restrict (s := U), ae_restrict_mem hU] with x h0 h1 hx
  rw [h0, h1, Set.indicator_of_mem hx]

theorem extend_restrict (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 m) (hu : ZeroOutside U u) : extendLp U hU (restrictLp U u) = u := by
  classical
  apply Lp.ext
  filter_upwards [extendLp_coe U hU (restrictLp U u),
    ae_imp_of_ae_restrict (restrictLp_coe U u), hu] with x h0 h1 h2
  rw [h0]
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, h1 hx]
  · rw [Set.indicator_of_notMem hx, h2 hx]

theorem zeroOutside_extend (U : Set X) (hU : MeasurableSet U)
    (u : Lp ℝ 2 (m.restrict U)) : ZeroOutside U (extendLp U hU u) := by
  filter_upwards [extendLp_coe U hU u] with x h hx
  rw [h, Set.indicator_of_notMem hx]

theorem zeroOutside_of_tendsto {U : Set X} {u : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (hu : ∀ n, ZeroOutside U (u n)) (hv : Tendsto u atTop (𝓝 v)) :
    ZeroOutside U v := by
  obtain ⟨ns, _, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hlim, ae_all_iff.2 hu] with x hx hzero hxU
  exact tendsto_nhds_unique hx
    (tendsto_const_nhds.congr (fun n => (hzero (ns n) hxU).symm))

end SubdiffusiveProcess.PartProcess
