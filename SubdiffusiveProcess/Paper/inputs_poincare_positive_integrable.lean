module

public import SubdiffusiveProcess.Paper.in_poincare
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Besov.Negative.ExactDual

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_poincare_positive_integrable_affine_memLp
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    MemLp (fun x : SpatialCoordinates d => v (fun j => z j + r * x j))
      (ENNReal.ofReal 2) (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  let U : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
  let S : Set (SpatialCoordinates d) := Homogenization.openCubeSet (Homogenization.originCube d 0)
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let f : SpatialCoordinates d → ℝ := U.indicator (v : SpatialCoordinates d → ℝ)
  have hU : MeasurableSet U := (centeredCube z r hr).isOpen.measurableSet
  have hf : MemLp f 2 volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hU]
    exact Lp.memLp v
  have hmap : Measure.map T volume = ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
    have hscale := Homogenization.map_smul_volume_restrict (d := d) (a := r) hr
      (Set.univ : Set (SpatialCoordinates d))
    have hscale' : Measure.map (fun x : SpatialCoordinates d => r • x) volume =
        ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
      simpa only [Measure.restrict_univ, Set.smul_set_univ₀ hr.ne'] using hscale
    have hcomp : T = (fun y : SpatialCoordinates d => y + z) ∘
        (fun x => r • x) := by
      funext x
      simp [T, add_comm]
    calc
      Measure.map T volume =
          Measure.map ((fun y : SpatialCoordinates d => y + z) ∘
            (fun x => r • x)) volume := by rw [hcomp]
      _ = (Measure.map (fun x : SpatialCoordinates d => r • x) volume).map
            (fun y => y + z) :=
          (Measure.map_map (g := fun y : SpatialCoordinates d => y + z)
            (f := fun x => r • x) (measurable_id.add measurable_const)
            (measurable_const_smul r)).symm
      _ = ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
          rw [hscale', Measure.map_smul _ (show Measurable (fun y : SpatialCoordinates d => y + z) from by simpa using! measurable_id.add_const z).aemeasurable,
            Measure.IsAddRightInvariant.map_add_right_eq_self (μ := volume) z]
  have hcomp : MemLp (f ∘ T) 2 volume := by
    have hfm : MemLp f 2 (Measure.map T volume) := by
      rw [hmap]
      exact hf.smul_measure (c := ENNReal.ofReal ((r ^ d)⁻¹)) ENNReal.ofReal_ne_top
    exact hfm.comp_of_map (measurable_const.add (measurable_const_smul r)).aemeasurable
  have hTS : ∀ x ∈ S, T x ∈ U := by
    intro x hx
    rw [Homogenization.mem_openCubeSet_originCube_iff] at hx
    change z + r • x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [SubdiffusiveProcess.centeredCube_eq_pi z hr]
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    constructor
    · have hxi := hx i
      simp only [zpow_zero, mul_one] at hxi
      change z i - r / 2 < z i + r * x i
      nlinarith [mul_lt_mul_of_pos_left hxi.1 hr]
    · have hxi := hx i
      simp only [zpow_zero, mul_one] at hxi
      change z i + r * x i < z i + r / 2
      nlinarith [mul_lt_mul_of_pos_left hxi.2 hr]
  have hEq : (fun x : SpatialCoordinates d => v (fun j => z j + r * x j)) =ᵐ[
      volume.restrict S] (f ∘ T) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Homogenization.isOpen_openCubeSet (Homogenization.originCube d 0)).measurableSet] with x hx
    have hxU := hTS x hx
    simp only [Function.comp_apply, f, Set.indicator_of_mem hxU, T]
    rfl
  have hcompR : MemLp (f ∘ T) 2 (volume.restrict S) :=
    MeasureTheory.MemLp.mono_measure Measure.restrict_le_self hcomp
  have hpull : MemLp (fun x : SpatialCoordinates d => v (fun j => z j + r * x j)) 2
      (volume.restrict S) := hcompR.ae_eq hEq.symm
  have hnormalized : MemLp (fun x : SpatialCoordinates d => v (fun j => z j + r * x j))
      (ENNReal.ofReal 2) (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
    rw [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
      Homogenization.volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]
    simpa using hpull.smul_measure
      (c := ENNReal.ofReal ((Homogenization.cubeVolume
        (Homogenization.originCube d 0))⁻¹)) ENNReal.ofReal_ne_top
  exact hnormalized

theorem inputs_poincare_positive_integrable (d : ℕ) (_hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (v : DomainL2 (centeredCube z r hr)),
    Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0)
      (fun x => v (fun j => z j + r * x j))) := by
  intro z r hr v
  have hmem := aux_inputs_poincare_positive_integrable_affine_memLp d z r hr v
  simpa using Homogenization.exactDualOverlapIntegrable
    (Homogenization.originCube d 0) 2 (by norm_num) hmem

end SubdiffusiveProcess.Paper
