module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyCompletedData
public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamilyPolar

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction
open _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

namespace CompletedCoreFamily

variable {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U}
  (M : CompletedCoreFamily F U Γ)

theorem zero (h : Data F U) : M.measure 0 = 0 := by
  let : IsFiniteMeasure (M.measure 0) := M.finite 0
  apply Measure.measure_univ_eq_zero.mp
  have hm := M.mass h 0
  change (M.measure 0 univ).toReal = F.form 0 0 at hm
  rw [F.toClosedForm.form_zero_left F.domain.zero_mem] at hm
  exact (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)

def cross (u v : EnergySpace F.toClosedForm) : SignedMeasure X :=
  letI : IsFiniteMeasure (M.measure (u + v)) := M.finite (u + v)
  letI : IsFiniteMeasure (M.measure (u - v)) := M.finite (u - v)
  (1 / 4 : ℝ) • ((M.measure (u + v)).toSignedMeasure - (M.measure (u - v)).toSignedMeasure)

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
theorem cross_apply [_instPreserved0 : T2Space X] [_instPreserved1 : LocallyCompactSpace X] [_instPreserved2 : BorelSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {Γ : CoreMeasure F U} (M : CompletedCoreFamily F U Γ) (u v : EnergySpace F.toClosedForm) {B : Set X} (hB : MeasurableSet B) :
    M.cross u v B = family_polar (fun z => (M.measure z B).toReal) u v := by
  let : IsFiniteMeasure (M.measure (u + v)) := M.finite (u + v)
  let : IsFiniteMeasure (M.measure (u - v)) := M.finite (u - v)
  simp only [cross, smul_apply, sub_apply, smul_eq_mul,
    Measure.toSignedMeasure_apply_measurable hB, measureReal_def, family_polar]
  ring

theorem cross_symm (h : Data F U) (u v : EnergySpace F.toClosedForm) :
    M.cross u v = M.cross v u := by
  ext B hB
  rw [M.cross_apply u v hB, M.cross_apply v u hB]
  exact family_polar_symm _ (by rw [M.zero h, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero])
    (fun x y => M.parallelogram h x y hB) u v

theorem cross_self (h : Data F U) (u : EnergySpace F.toClosedForm)
    {B : Set X} (hB : MeasurableSet B) : M.cross u u B = (M.measure u B).toReal := by
  rw [M.cross_apply u u hB]
  exact family_polar_self _ (by rw [M.zero h, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero])
    (fun x y => M.parallelogram h x y hB) u

theorem cross_add_right (h : Data F U) (u v w : EnergySpace F.toClosedForm) :
    M.cross u (v + w) = M.cross u v + M.cross u w := by
  ext B hB
  rw [add_apply, M.cross_apply u (v + w) hB,
    M.cross_apply u v hB, M.cross_apply u w hB]
  exact family_polar_add_right _ (by rw [M.zero h, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero])
    (fun x y => M.parallelogram h x y hB) u v w

theorem cross_smul_right (h : Data F U) (c : ℝ) (u v : EnergySpace F.toClosedForm) :
    M.cross u (c • v) = c • M.cross u v := by
  ext B hB
  rw [smul_apply, smul_eq_mul, M.cross_apply u (c • v) hB, M.cross_apply u v hB]
  exact family_polar_smul_right _ (by rw [M.zero h, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero])
    (fun x y => M.parallelogram h x y hB) (M.continuous h hB) c u v

theorem cross_le (h : Data F U) (u v : EnergySpace F.toClosedForm)
    {B : Set X} (hB : MeasurableSet B) :
    |M.cross u v B| ≤ Real.sqrt (M.measure u B).toReal * Real.sqrt (M.measure v B).toReal := by
  rw [M.cross_apply u v hB]
  exact family_polar_bound _ (by rw [M.zero h, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero])
    (fun x y => M.parallelogram h x y hB) (M.continuous h hB)
    (fun _ => ENNReal.toReal_nonneg) u v

theorem cross_univ (h : Data F U) (u v : EnergySpace F.toClosedForm) :
    M.cross u v univ = F.form u.1 v.1 := by
  rw [M.cross_apply u v MeasurableSet.univ, family_polar, M.mass h (u + v), M.mass h (u - v)]
  change (F.form (u.1 + v.1) (u.1 + v.1) - F.form (u.1 - v.1) (u.1 - v.1)) / 4 =
    F.form u.1 v.1
  rw [F.toClosedForm.form_add_left u.1 u.2 v.1 v.2 _ (F.domain.add_mem u.2 v.2),
    F.toClosedForm.form_sub_left u.2 v.2 (F.domain.sub_mem u.2 v.2),
    F.toClosedForm.form_add_right u.2 u.2 v.2,
    F.toClosedForm.form_add_right v.2 u.2 v.2,
    F.toClosedForm.form_sub_right u.2 u.2 v.2,
    F.toClosedForm.form_sub_right v.2 u.2 v.2,
    F.form_symm v.1 v.2 u.1 u.2]
  ring

end CompletedCoreFamily
end SubdiffusiveProcess.DirichletForm.FOTConstruction
