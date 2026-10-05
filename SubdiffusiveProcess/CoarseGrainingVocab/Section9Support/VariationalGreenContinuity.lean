module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalBoundedGain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorGreenStructure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra

@[expose] public section

/-! # Quantitative L² continuity of the variational Green inverse -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A locally bounded density preserves finite restricted volume. -/
theorem variational_weighted_isFiniteMeasure {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) [IsFiniteMeasure (volume.restrict U)]
    {rho : Vec d → ℝ} (hr : CoefficientOn U rho) :
    IsFiniteMeasure ((weightedMeasure rho).restrict U) := by
  obtain ⟨lo, hi, hlo, hb⟩ := hr.2
  have hm := weightedMeasure_restrict_le_smul_volume_restrict hU hi (hb.mono fun _ hx => hx.2)
  refine ⟨?_⟩
  apply (Measure.le_iff.mp hm univ MeasurableSet.univ).trans_lt
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (volume.restrict U) univ)

/-- The difference of two actual Green solutions obeys the same L² operator bound. -/
theorem variational_green_l2_difference {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F) (hPoi : PoincareAssumption c rho U A F)
    {f g : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    (hg : MemLp g 2 ((weightedMeasure rho).restrict U))
    (u v : H10Function U)
    (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f)
    (hv : IsMassiveWeakSolutionOn c rho 0 U v.toH1Function g) :
    eLpNorm (fun x => u.toH1Function.toFun x - v.toH1Function.toFun x) 2
        ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (A * F) * eLpNorm (fun x => f x - g x) 2 ((weightedMeasure rho).restrict U) := by
  obtain ⟨a, lo, hi, hEll, hca⟩ := exists_interior_elliptic_representative hU.isOpen.measurableSet hc
  obtain ⟨rlo, rhi, hrlo, hrb⟩ := hr.2
  have hrabs : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhi := by
    filter_upwards [hrb] with x hx
    rw [abs_of_nonneg (hrlo.le.trans hx.1)]
    exact hx.2
  have hsub := IsMassiveWeakSolutionOn.sub hEll hr.1 hrabs
    (memLp_volume_restrict_of_weighted hU.isOpen.measurableSet hr hf)
    (memLp_volume_restrict_of_weighted hU.isOpen.measurableSet hr hg)
    (interior_massiveWeakSolution_congr_coefficient hca hu)
    (interior_massiveWeakSolution_congr_coefficient hca hv)
  have hsubc := interior_massiveWeakSolution_congr_coefficient hca.symm hsub
  have hmem : MemH10 U (u.toH1Function - v.toH1Function).toFun := by
    simpa only [H1Function.sub_toFun] using! memH10_sub u.memH10 v.memH10
  obtain ⟨w, hw⟩ := variational_h10_upgrade hU.isOpen _ hmem
  have hwsol : IsMassiveWeakSolutionOn c rho 0 U w.toH1Function (f - g) := by
    rw [hw]
    exact hsubc
  have h := (interior_green_energy_l2_bound hU.isOpen.measurableSet hr hA hF hPoi
    (hf.sub hg) w hwsol).2
  simpa only [hw, H1Function.sub_toFun, Pi.sub_apply] using! h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
