module

public import SubdiffusiveProcess.Probability.SameLawComposition
public import SubdiffusiveProcess.Probability.SubseqInProbability
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib.Tactic
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- All infrared values at the countably many cell centres converge on a common
further subsequence, simultaneously for both (or countably many) represented sides. -/
theorem represented_infrared_subsequence
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (A Cells : Type) [Countable A] [Countable Cells]
    (env : A → ℕ → Ω → BilateralField d)
    (hEnv : ∀ a n, MeasurePreserving (env a n) P (chaosSampleLaw M).toMeasure)
    (hConv : ∀ᵐ omega ∂P, ∀ a, Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
    (z : Cells → SpatialCoordinates d) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᵐ omega ∂P, ∀ a c,
      Tendsto (fun n => H (env a (psi n) omega) (z c)) atTop (𝓝 (H (field omega) (z c))) := by
  let := Encodable.ofCountable (A × Cells)
  have hcomp : ∀ a c, TendstoInMeasure P
      (fun n omega => H (env a n omega) (z c)) atTop
      (fun omega => H (field omega) (z c)) := by
    intro a c
    exact aux_tendstoInMeasure_comp_const (Ω := Ω) (S := BilateralField d)
      (P := P) (μ := (chaosSampleLaw M).toMeasure) (Y := env a) (Y0 := field)
      (V := fun omega => H omega (z c)) (hEnv a) hfield
      (hConv.mono fun omega h => h a)
      (((continuous_eval_const (z c)).measurable.comp hH.1).aestronglyMeasurable)
  let X : ℕ → ℕ → Ω → ℝ := fun j n omega =>
    match Encodable.decode (α := A × Cells) j with
    | none => 0
    | some ac => H (env ac.1 n omega) (z ac.2) - H (field omega) (z ac.2)
  have hX : ∀ j eps, 0 < eps →
      Tendsto (fun n => P {omega | eps ≤ |X j n omega|}) atTop (𝓝 0) := by
    intro j eps heps
    cases hj : Encodable.decode (α := A × Cells) j with
    | none => simpa only [X, hj, abs_zero, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    | some ac => simpa only [X, hj, Real.dist_eq] using
        (tendstoInMeasure_iff_dist.mp (hcomp ac.1 ac.2) eps heps)
  obtain ⟨psi, hpsi, hae⟩ := exists_strictMono_ae_forall_tendsto_zero P X hX id tendsto_id
  refine ⟨psi, hpsi, ?_⟩
  filter_upwards [hae] with omega h
  intro a c
  have he := h (Encodable.encode (a, c))
  simp only [X, Encodable.encodek, id_eq] at he
  have ht := he.add_const (H (field omega) (z c))
  simpa only [sub_add_cancel, zero_add] using ht
end SubdiffusiveProcess.Paper
