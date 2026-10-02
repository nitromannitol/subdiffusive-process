import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

lemma aux_lem_diff_euler_quadratic_linear_zero {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a) : b = 0 := by
  by_contra hb
  by_cases ha : a ≤ 0
  · have h₁ := h 1
    have h₂ := h (-1)
    norm_num at h₁ h₂
    have hz : b = 0 := by linarith
    exact hb hz
  · have ha' : 0 < a := lt_of_not_ge ha
    have ha0 : a ≠ 0 := ne_of_gt ha'
    have hv := h (-b / a)
    field_simp [ha0] at hv
    nlinarith [sq_pos_of_ne_zero hb]



theorem lem_diff_euler
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ) :
    let Q : Opens (SpatialCoordinates d) := centeredCube zQ rQ hrQ
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      let q : Opens (SpatialCoordinates d) := centeredCube z r hr
      ∀ (hinside : closure (q : Set (SpatialCoordinates d)) ⊆
          (Q : Set (SpatialCoordinates d)))
        (E F : DirichletForm.ClosedForm
          (volume.restrict (Q : Set (SpatialCoordinates d))))
        (GammaE : DirichletForm.EnergyMeasure E)
        (GammaF : DirichletForm.EnergyMeasure F)
        (hdom : E.domain = F.domain)
        (V0 : Submodule ℝ (DomainL2 Q))
        (hzero : DirichletForm.IsKilledDomain E
          (q : Set (SpatialCoordinates d)) V0)
        (c : ℝ)
        (uE uF : DomainL2 Q)
        (huE : uE ∈ E.domain) (huF : uF ∈ F.domain)
        (hminE : ∀ v ∈ V0,
          (GammaE.measure uE (q : Set (SpatialCoordinates d))).toReal ≤
            (GammaE.measure (uE + v) (q : Set (SpatialCoordinates d))).toReal)
        (hminF : ∀ v ∈ V0,
          (GammaF.measure uF (q : Set (SpatialCoordinates d))).toReal ≤
            (GammaF.measure (uF + v) (q : Set (SpatialCoordinates d))).toReal),
      ∀ v ∈ V0,
        (GammaF.cross (uF - uE) v) (q : Set (SpatialCoordinates d)) =
          -((GammaF.cross uE v) (q : Set (SpatialCoordinates d)) -
            c * (GammaE.cross uE v) (q : Set (SpatialCoordinates d))) := by
  dsimp only
  intro z r hr
  intro hinside E F GammaE GammaF hdom V0 hzero c uE uF huE huF hminE hminF
  intro v hv
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hvE : (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ E.domain :=
    hzero.le_domain hv
  have hvF : (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ F.domain := by
    rw [← hdom]
    exact hvE
  have hquadE : ∀ t : ℝ, 0 ≤
      2 * t * (GammaE.cross uE v) (centeredCube z r hr : Set (SpatialCoordinates d)) +
        t ^ 2 * (GammaE.cross v v) (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro t
    have htv : t • (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ V0 := V0.smul_mem t hv
    have htvE := E.domain.smul_mem t hvE
    have hsumE : uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ E.domain :=
      E.domain.add_mem huE htvE
    have hmin := hminE (t • (v : DomainL2 (centeredCube zQ rQ hrQ))) htv
    have hineq : (GammaE.cross uE uE) (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (GammaE.cross (uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
          (uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ))))
          (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      calc
        (GammaE.cross uE uE) (centeredCube z r hr : Set (SpatialCoordinates d)) =
            (GammaE.measure uE (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          GammaE.cross_self uE huE _ hqmeas
        _ ≤ (GammaE.measure (uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hmin
        _ = (GammaE.cross (uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
            (uE + t • (v : DomainL2 (centeredCube zQ rQ hrQ))))
            (centeredCube z r hr : Set (SpatialCoordinates d)) :=
          (GammaE.cross_self _ hsumE _ hqmeas).symm
    have hexpand := GammaE.cross_add_self_apply huE htvE
      (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [GammaE.cross_smul_right t uE huE v hvE] at hexpand
    rw [GammaE.cross_smul_left t hvE htvE] at hexpand
    rw [GammaE.cross_smul_right t v hvE v hvE] at hexpand
    simp only [MeasureTheory.VectorMeasure.smul_apply, smul_eq_mul] at hexpand
    rw [hexpand] at hineq
    nlinarith
  have hcrossE : (GammaE.cross uE v) (centeredCube z r hr : Set (SpatialCoordinates d)) = 0 :=
    aux_lem_diff_euler_quadratic_linear_zero hquadE
  have hquadF : ∀ t : ℝ, 0 ≤
      2 * t * (GammaF.cross uF v) (centeredCube z r hr : Set (SpatialCoordinates d)) +
        t ^ 2 * (GammaF.cross v v) (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro t
    have htv : t • (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ V0 := V0.smul_mem t hv
    have htvF := F.domain.smul_mem t hvF
    have hsumF : uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ)) ∈ F.domain :=
      F.domain.add_mem huF htvF
    have hmin := hminF (t • (v : DomainL2 (centeredCube zQ rQ hrQ))) htv
    have hineq : (GammaF.cross uF uF) (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (GammaF.cross (uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
          (uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ))))
          (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      calc
        (GammaF.cross uF uF) (centeredCube z r hr : Set (SpatialCoordinates d)) =
            (GammaF.measure uF (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          GammaF.cross_self uF huF _ hqmeas
        _ ≤ (GammaF.measure (uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hmin
        _ = (GammaF.cross (uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ)))
            (uF + t • (v : DomainL2 (centeredCube zQ rQ hrQ))))
            (centeredCube z r hr : Set (SpatialCoordinates d)) :=
          (GammaF.cross_self _ hsumF _ hqmeas).symm
    have hexpand := GammaF.cross_add_self_apply huF htvF
      (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [GammaF.cross_smul_right t uF huF v hvF] at hexpand
    rw [GammaF.cross_smul_left t hvF htvF] at hexpand
    rw [GammaF.cross_smul_right t v hvF v hvF] at hexpand
    simp only [MeasureTheory.VectorMeasure.smul_apply, smul_eq_mul] at hexpand
    rw [hexpand] at hineq
    nlinarith
  have hcrossF : (GammaF.cross uF v) (centeredCube z r hr : Set (SpatialCoordinates d)) = 0 :=
    aux_lem_diff_euler_quadratic_linear_zero hquadF
  have huEF : (uE : DomainL2 (centeredCube zQ rQ hrQ)) ∈ F.domain := by
    rw [← hdom]
    exact huE
  have hcross_sub :
      GammaF.cross (uF - uE) v = GammaF.cross uF v - GammaF.cross uE v := by
    have hneg : GammaF.cross (-uE) v = -GammaF.cross uE v := by
      simpa only [neg_one_smul, neg_smul, one_smul] using
        (GammaF.cross_smul_left (-1) huEF hvF)
    rw [sub_eq_add_neg, GammaF.cross_add_left huF (F.domain.neg_mem huEF) hvF, hneg]
    exact sub_eq_add_neg _ _
  calc
    (GammaF.cross (uF - uE) v) (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaF.cross uF v - GammaF.cross uE v)
          (centeredCube z r hr : Set (SpatialCoordinates d)) := congrArg
            (fun μ : SignedMeasure (SpatialCoordinates d) =>
              μ (centeredCube z r hr : Set (SpatialCoordinates d))) hcross_sub
    _ = (GammaF.cross uF v) (centeredCube z r hr : Set (SpatialCoordinates d)) -
        (GammaF.cross uE v) (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      MeasureTheory.VectorMeasure.sub_apply _ _ _
    _ = -((GammaF.cross uE v) (centeredCube z r hr : Set (SpatialCoordinates d)) -
        c * (GammaE.cross uE v) (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      rw [hcrossF, hcrossE]
      ring

end
end Paper
