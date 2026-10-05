module

public import SubdiffusiveProcess.Main.CompactGradientLipschitzObservable
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-! Measurability and the exact Lipschitz bound for the stated compact derivative observable. Internal semantics for `mfd:lem-infrared`. -/

theorem compactGradientLipschitzObservable_lowerSemicontinuous {d : ℕ}
    (K : Compacts (SpatialCoordinates d)) :
    LowerSemicontinuous (compactGradientLipschitzObservable K :
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) := by
  let f : {p : K × K // p.1 ≠ p.2} →
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun p g ↦
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.1 -
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.2‖ /
      ‖(p.1.1 : SpatialCoordinates d) - (p.1.2 : SpatialCoordinates d)‖
  have hf_bdd : ∀ g, BddAbove (Set.range (fun p ↦ f p g)) := by
    intro g
    obtain ⟨C, hC⟩ := g.2.2 (K : Set (SpatialCoordinates d)) K.isCompact
    refine ⟨C, ?_⟩
    rintro a ⟨p, rfl⟩
    have hxy : (p.1.1 : SpatialCoordinates d) ≠ p.1.2 := by
      intro h
      exact p.2 (Subtype.ext h)
    have hdist : 0 < ‖(p.1.1 : SpatialCoordinates d) - p.1.2‖ := by
      rw [← dist_eq_norm]
      exact dist_pos.mpr hxy
    have hLip := hC.dist_le_mul (p.1.1 : SpatialCoordinates d) p.1.1.2
      (p.1.2 : SpatialCoordinates d) p.1.2.2
    apply (div_le_iff₀ hdist).2
    rw [dist_eq_norm, dist_eq_norm] at hLip
    exact hLip
  have hf_cont : ∀ p, Continuous (f p) := by
    intro p
    change Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.1 -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.2‖ /
        ‖(p.1.1 : SpatialCoordinates d) - (p.1.2 : SpatialCoordinates d)‖)
    have hnum : Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.1 -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv g p.1.2) :=
      (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_eval_deriv (d := d)
        (p.1.1 : SpatialCoordinates d)).sub
        (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_eval_deriv (d := d)
          (p.1.2 : SpatialCoordinates d))
    have hden : ‖(p.1.1 : SpatialCoordinates d) - (p.1.2 : SpatialCoordinates d)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
        intro h
        exact p.2 (Subtype.ext h)))
    apply Continuous.div
    · exact hnum.norm
    · exact continuous_const
    · intro _
      exact hden
  have heq : compactGradientLipschitzObservable K =
      fun g ↦ ⨆ p, f p g := by
    funext g
    simp only [compactGradientLipschitzObservable, f, iSup]
    congr 1
    ext a
    constructor
    · rintro ⟨x, y, hxy, rfl⟩
      exact ⟨⟨(x, y), hxy⟩, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.1.1, p.1.2, p.2, rfl⟩
  rw [heq]
  exact lowerSemicontinuous_ciSup hf_bdd
    (fun p ↦ (hf_cont p).lowerSemicontinuous)

theorem compactGradientLipschitzObservable_measurable {d : ℕ}
    (K : Compacts (SpatialCoordinates d)) :
    Measurable (compactGradientLipschitzObservable K :
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) :=
  (compactGradientLipschitzObservable_lowerSemicontinuous K).measurable

theorem deriv_lipschitzOnWith_compactGradientLipschitzObservable {d : ℕ}
    (K : Compacts (SpatialCoordinates d))
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    LipschitzOnWith
      (Real.toNNReal (compactGradientLipschitzObservable K g))
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g) (K : Set (SpatialCoordinates d)) := by
  have hbounded : BddAbove {a : ℝ | ∃ x y : K, x ≠ y ∧
      a = ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1 -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv g y.1‖ / ‖x.1 - y.1‖} := by
    obtain ⟨C, hC⟩ := g.2.2 (K : Set (SpatialCoordinates d)) K.isCompact
    refine ⟨C, ?_⟩
    rintro a ⟨x, y, hxy, rfl⟩
    have hdist : 0 < ‖(x.1 : SpatialCoordinates d) - y.1‖ := by
      rw [← dist_eq_norm]
      exact dist_pos.mpr (fun h ↦ hxy (Subtype.ext h))
    have hLip := hC.dist_le_mul (x : SpatialCoordinates d) x.2
      (y : SpatialCoordinates d) y.2
    apply (div_le_iff₀ hdist).2
    rw [dist_eq_norm, dist_eq_norm] at hLip
    exact hLip
  have hnonneg : 0 ≤ compactGradientLipschitzObservable K g := by
    apply Real.sSup_nonneg
    rintro a ⟨x, y, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hdist : 0 < ‖x - y‖ := by
    rw [← dist_eq_norm]
    exact dist_pos.mpr hxy
  have hsup : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x -
      _root_.SubdiffusiveProcess.Model.PotentialField.deriv g y‖ / ‖x - y‖ ≤
      compactGradientLipschitzObservable K g := by
    apply le_csSup hbounded
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h ↦ hxy (congrArg Subtype.val h), rfl⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hnonneg]
  exact (div_le_iff₀ hdist).mp hsup

end SubdiffusiveProcess
