module

public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-! Continuity and measurability of the stated native compact C1 observable. Internal semantics for `mfd:lem-infrared`. -/

theorem compactPotentialC1Norm_continuous {d : ℕ}
    (K : Compacts (SpatialCoordinates d)) :
    Continuous (compactPotentialC1Norm K :
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) := by
  have norm_comp_continuous {E : Type} [NormedAddCommGroup E]
      (R : _root_.SubdiffusiveProcess.Model.PotentialField d → C(K, E))
      (hR : Continuous R) :
      Continuous (fun g => ‖R g‖) := by
    refine continuous_iff_continuousAt.mpr (fun g => ?_)
    rw [Metric.continuousAt_iff']
    intro ε hε
    have hU : TendstoUniformly (fun g' x => R g' x) (R g)
        (𝓝 g) :=
      ContinuousMap.tendsto_iff_tendstoUniformly.mp hR.continuousAt
    filter_upwards [Metric.tendstoUniformly_iff.mp hU ε hε] with g' hg'
    calc
      dist ‖R g'‖ ‖R g‖ ≤ dist (R g') (R g) := by
        simpa only [dist_eq_norm] using dist_norm_norm_le (R g') (R g)
      _ < ε := (ContinuousMap.dist_lt_iff hε).2 (fun x => by
        simpa only [dist_comm] using hg' x)
  let hval : Continuous
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        (⟨fun x : K => g x.1,
          g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ))) :=
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
      continuous_subtype_val.fst
  let hderiv : Continuous
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        (⟨fun x : K => _root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1,
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.comp
            continuous_subtype_val⟩ :
          C(K, SpatialCoordinates d →L[ℝ] ℝ))) :=
      (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
      continuous_subtype_val.snd
  have hval_norm : Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      ‖(⟨fun x : K => g x.1,
        g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ))‖) :=
    norm_comp_continuous (E := ℝ) _ hval
  have hderiv_norm : Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      ‖(⟨fun x : K => _root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1,
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.comp
          continuous_subtype_val⟩ :
        C(K, SpatialCoordinates d →L[ℝ] ℝ))‖) :=
    norm_comp_continuous (E := SpatialCoordinates d →L[ℝ] ℝ) _ hderiv
  change Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
    ‖g.1.1.restrict (K : Set (SpatialCoordinates d))‖ +
      ‖(_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).restrict
        (K : Set (SpatialCoordinates d))‖)
  exact hval_norm.add hderiv_norm

theorem compactPotentialC1Norm_measurable_comp {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (K : Compacts (SpatialCoordinates d))
    {H : Ω → _root_.SubdiffusiveProcess.Model.PotentialField d}
    (hH : Measurable H) :
    Measurable (fun ω => compactPotentialC1Norm K (H ω)) := by
  exact (compactPotentialC1Norm_continuous K).measurable.comp hH

end SubdiffusiveProcess
