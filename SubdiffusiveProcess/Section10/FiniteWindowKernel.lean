import Mathlib
import SubdiffusiveProcess.Section10.RandomTestMartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace Paper
def aux_lim_measure_normalized_kernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (k : Kernel Ω X) : Kernel Ω X :=
  ⟨fun w => (1 + k w Set.univ)⁻¹ • k w, by
    apply Measure.measurable_measure.mpr
    intro D hD
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((measurable_const.add (k.measurable_coe MeasurableSet.univ)).inv).mul (k.measurable_coe hD)⟩

theorem aux_lim_measure_normalized_kernel_finite
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (k : Kernel Ω X) (hk : ∀ w, k w Set.univ ≠ ⊤) :
    IsFiniteKernel (aux_lim_measure_normalized_kernel k) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun w => ?_⟩⟩
  have hne_top : 1 + (k w) Set.univ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hk w⟩
  have hne_zero : 1 + (k w) Set.univ ≠ 0 := by simp
  change ((1 + (k w) Set.univ)⁻¹ • k w) Set.univ ≤ 1
  rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.inv_mul_le_iff hne_zero hne_top, mul_one]
  exact le_add_left le_rfl


theorem aux_lim_measure_normalized_kernel_recover
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (k : Kernel Ω X) (hk : ∀ w, k w Set.univ ≠ ⊤)
    [IsFiniteKernel (aux_lim_measure_normalized_kernel k)] :
    (aux_lim_measure_normalized_kernel k).withDensity (fun w _ => 1 + k w Set.univ) = k := by
  apply Kernel.ext
  intro w
  rw [Kernel.withDensity_apply]
  · have h0 : (1 + k w Set.univ) ≠ 0 := by positivity
    have ht : (1 + k w Set.univ) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hk w⟩
    change ((1 + k w Set.univ)⁻¹ • k w).withDensity
        (fun x => 1 + k w Set.univ) = k w
    rw [withDensity_smul_measure, MeasureTheory.withDensity_const, smul_smul,
        ENNReal.inv_mul_cancel h0 ht, one_smul]
  · apply Measurable.const_add
    exact (k.measurable_coe MeasurableSet.univ).comp measurable_fst


theorem aux_lim_measure_finite_kernel_sfinite {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (k : Kernel Ω X)
    (hk : ∀ w, k w Set.univ ≠ ⊤) : IsSFiniteKernel k := by
  haveI := aux_lim_measure_normalized_kernel_finite k hk
  rw [← aux_lim_measure_normalized_kernel_recover k hk]
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _
    (fun w _ => ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hk w⟩)

def aux_lim_measure_window_kernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (mu : Ω → Measure X) (hm : Measurable mu) (U : Set X) (hU : MeasurableSet U) : Kernel Ω X :=
  ⟨fun w => (mu w).restrict U, by
    apply Measure.measurable_measure.mpr
    intro D hD
    simp only [Measure.restrict_apply hD]
    exact (Measure.measurable_coe (hD.inter hU)).comp hm⟩

theorem aux_lim_measure_window_kernel_sfinite {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (mu : Ω → Measure X) (hm : Measurable mu)
    (U : Set X) (hU : MeasurableSet U) (hfin : ∀ w, mu w U ≠ ⊤) :
    IsSFiniteKernel (aux_lim_measure_window_kernel mu hm U hU) := by
  apply aux_lim_measure_finite_kernel_sfinite
  intro w
  simpa [aux_lim_measure_window_kernel] using hfin w

end Paper
