module

public import SubdiffusiveProcess.Paper.prop_21_catalog_global_weighted_energy
public import SubdiffusiveProcess.Paper.lem_weighted_cluster
public import SubdiffusiveProcess.VariationalResponses.LimitForm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_limitFormEnergy_apply_self
    (H : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hHsym : ∀ x y : DomainL2 Q, inner ℝ (H x) y = inner ℝ x (H y))
    (hHpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (H x))
    (x : DomainL2 Q) :
    limitFormEnergy H (H x) = ((inner ℝ x (H x) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro f
    apply EReal.coe_le_coe_iff.mpr
    have hpos : (0 : ℝ) ≤ inner ℝ (f - x) (H (f - x)) := hHpos (f - x)
    have hsym : inner ℝ x (H f) = inner ℝ f (H x) := by
      rw [real_inner_comm, hHsym]
    simp only [map_sub, inner_sub_left, inner_sub_right] at hpos
    rw [hsym] at hpos
    linarith
  · have hterm : ((inner ℝ x (H x) : ℝ) : EReal)
        = ((2 * inner ℝ x (H x) - inner ℝ x (H x) : ℝ) : EReal) := by
      congr 1
      ring
    rw [hterm]
    exact le_iSup (fun f : DomainL2 Q =>
      ((2 * inner ℝ f (H x) - inner ℝ f (H f) : ℝ) : EReal)) x

lemma aux_inner_map_eq_of_quad_eq
    (F G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hFsym : ∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y))
    (hGsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hquad : ∀ z : DomainL2 Q, inner ℝ z (F z) = inner ℝ z (G z))
    (x y : DomainL2 Q) : inner ℝ x (F y) = inner ℝ x (G y) := by
  have key : ∀ (H : DomainL2 Q →L[ℝ] DomainL2 Q),
      (∀ a b : DomainL2 Q, inner ℝ (H a) b = inner ℝ a (H b)) →
      inner ℝ (x + y) (H (x + y)) - inner ℝ (x - y) (H (x - y))
        = 4 * inner ℝ x (H y) := by
    intro H hH
    have hsym' : inner ℝ y (H x) = inner ℝ x (H y) := by
      rw [real_inner_comm, hH]
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, hsym']
    ring
  have hF' := key F hFsym
  have hG' := key G hGsym
  have h1 := hquad (x + y)
  have h2 := hquad (x - y)
  linarith

lemma aux_quad_eq
    (F G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hFsym : ∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y))
    (hGsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hFpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x))
    (hGpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (henergy : ∀ u : DomainL2 Q,
      limitFormEnergy F u = limitFormEnergy G u)
    (x : DomainL2 Q) : inner ℝ x (F x) = inner ℝ x (G x) := by
  have hF : limitFormEnergy F (F x) = ((inner ℝ x (F x) : ℝ) : EReal) :=
    aux_limitFormEnergy_apply_self F hFsym hFpos x
  have hG : limitFormEnergy G (G x) = ((inner ℝ x (G x) : ℝ) : EReal) :=
    aux_limitFormEnergy_apply_self G hGsym hGpos x
  have hle1 : inner ℝ x (F x) ≤ inner ℝ x (G x) := by
    have ht : ((2 * inner ℝ x (F x) - inner ℝ x (G x) : ℝ) : EReal)
        ≤ limitFormEnergy G (F x) :=
      le_iSup (fun f : DomainL2 Q =>
        ((2 * inner ℝ f (F x) - inner ℝ f (G f) : ℝ) : EReal)) x
    rw [← henergy (F x), hF] at ht
    have := EReal.coe_le_coe_iff.mp ht
    linarith
  have hle2 : inner ℝ x (G x) ≤ inner ℝ x (F x) := by
    have ht : ((2 * inner ℝ x (G x) - inner ℝ x (F x) : ℝ) : EReal)
        ≤ limitFormEnergy F (G x) :=
      le_iSup (fun f : DomainL2 Q =>
        ((2 * inner ℝ f (G x) - inner ℝ f (F f) : ℝ) : EReal)) x
    rw [henergy (G x), hG] at ht
    have := EReal.coe_le_coe_iff.mp ht
    linarith
  exact le_antisymm hle1 hle2

lemma aux_operator_eq
    (F G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hFsym : ∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y))
    (hGsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hFpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x))
    (hGpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (henergy : ∀ u : DomainL2 Q,
      limitFormEnergy F u = limitFormEnergy G u) :
    F = G := by
  refine ContinuousLinearMap.ext (fun y => ?_)
  have hquad : ∀ x : DomainL2 Q, inner ℝ x (F x) = inner ℝ x (G x) :=
    fun x => aux_quad_eq F G hFsym hGsym hFpos hGpos henergy x
  have hzero : inner ℝ (F y - G y) (F y - G y) = 0 := by
    rw [inner_sub_right,
      aux_inner_map_eq_of_quad_eq F G hFsym hGsym hquad (F y - G y) y,
      sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)



theorem prop_21_dual_energy_operator_unique
    (F G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hFsym : ∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y))
    (hGsym : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hFpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x))
    (hGpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (henergy : ∀ u : DomainL2 Q,
      limitFormEnergy F u = limitFormEnergy G u) :
    F = G := by
    exact aux_operator_eq F G hFsym hGsym hFpos hGpos henergy


end SubdiffusiveProcess.Paper
