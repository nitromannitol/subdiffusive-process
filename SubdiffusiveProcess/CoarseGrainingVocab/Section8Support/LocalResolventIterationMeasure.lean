module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import Homogenization.Sobolev.Foundations.AxisCube

@[expose] public section

/-!
# Local weighted measure facts for resolvent iteration

The local almost-everywhere coefficient bounds give measure comparison, finite positive cube mass,
and full support inside the cube. Continuity then upgrades a product-almost-everywhere density bound
at each positive time to a pointwise diagonal bound.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

variable {d : ℕ} {U K : Set (Vec d)} {rho : Vec d → ℝ}

/-- Local almost-everywhere coefficient bounds restrict to any smaller set. -/
theorem coefficientOn_mono (hUK : U ⊆ K) (h : CoefficientOn K rho) :
    CoefficientOn U rho := by
  rcases h with ⟨hm, lo, hi, hlo, hb⟩
  exact ⟨hm.mono_measure (Measure.restrict_mono hUK le_rfl), lo, hi, hlo,
    ae_restrict_of_ae_restrict_of_subset hUK hb⟩

/-- An almost-everywhere lower density bound gives a lower comparison of restricted measures. -/
theorem smul_volume_restrict_le_weightedMeasure_restrict (hU : MeasurableSet U)
    (lo : ℝ) (hlo : ∀ᵐ x ∂volume.restrict U, lo ≤ rho x) :
    ENNReal.ofReal lo • volume.restrict U ≤ (weightedMeasure rho).restrict U := by
  rw [weightedMeasure, restrict_withDensity hU]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hB]
  have h := lintegral_mono_ae ((ae_restrict_of_ae (s := B) hlo).mono
    (fun x hx => ENNReal.ofReal_le_ofReal hx))
  simpa only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] using h

/-- An almost-everywhere upper density bound gives an upper comparison of restricted measures. -/
theorem weightedMeasure_restrict_le_smul_volume_restrict (hU : MeasurableSet U)
    (hi : ℝ) (hhi : ∀ᵐ x ∂volume.restrict U, rho x ≤ hi) :
    (weightedMeasure rho).restrict U ≤ ENNReal.ofReal hi • volume.restrict U := by
  rw [weightedMeasure, restrict_withDensity hU]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hB]
  have h := lintegral_mono_ae ((ae_restrict_of_ae (s := B) hhi).mono
    (fun x hx => ENNReal.ofReal_le_ofReal hx))
  simpa only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] using h

/-- A positive local density bound makes restricted volume absolutely continuous with respect to the weighted measure. -/
theorem volume_restrict_absolutelyContinuous_weightedMeasure_restrict
    (hU : MeasurableSet U) (hρ : CoefficientOn U rho) :
    volume.restrict U ≪ (weightedMeasure rho).restrict U := by
  rw [weightedMeasure, restrict_withDensity hU]
  apply withDensity_absolutelyContinuous' hρ.1.aemeasurable.ennreal_ofReal
  obtain ⟨lo, hi, hlo, hb⟩ := hρ.2
  filter_upwards [hb] with x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (hlo.trans_le hx.1))

/-- The restricted weighted measure is absolutely continuous with respect to restricted volume. -/
theorem weightedMeasure_restrict_absolutelyContinuous_volume_restrict
    (hU : MeasurableSet U) :
    (weightedMeasure rho).restrict U ≪ volume.restrict U := by
  rw [weightedMeasure, restrict_withDensity hU]
  exact withDensity_absolutelyContinuous _ _

/-- Bounds on every compact set imply bounds on an axis cube via its compact closure. -/
theorem coefficientOn_axisCube (hρ : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho)
    (y : Vec d) (side : ℝ) : CoefficientOn (axisCube y side) rho := by
  exact coefficientOn_mono subset_closure
    (hρ _ (isBoundedDomain_axisCube y side).isBounded.isCompact_closure)

/-- Local coefficient bounds give finite weighted mass to an axis cube. -/
theorem weightedMeasure_axisCube_lt_top
    (hρ : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho)
    (y : Vec d) (side : ℝ) : (weightedMeasure rho) (axisCube y side) < ∞ := by
  have hU := (isOpen_axisCube y side).measurableSet
  obtain ⟨_, lo, hi, hlo, hb⟩ := coefficientOn_axisCube hρ y side
  have hle := weightedMeasure_restrict_le_smul_volume_restrict hU hi
    (hb.mono (fun _ hx => hx.2))
  have hmass := Measure.le_iff'.mp hle Set.univ
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, smul_eq_mul] at hmass
  exact hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (isBoundedDomain_axisCube y side).volume_lt_top)

/-- The midpoint belongs to every axis cube with positive side length. -/
theorem axisCube_nonempty (y : Vec d) (side : ℝ) (hs : 0 < side) :
    (axisCube y side).Nonempty := by
  refine ⟨fun i => y i + side / 2, ?_⟩
  intro i hi
  constructor <;> linarith

/-- An axis cube with positive side length has positive weighted mass. -/
theorem weightedMeasure_axisCube_pos
    (hρ : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho)
    (y : Vec d) (side : ℝ) (hs : 0 < side) :
    0 < (weightedMeasure rho) (axisCube y side) := by
  have hU := (isOpen_axisCube y side).measurableSet
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU
    (coefficientOn_axisCube hρ y side)
  apply pos_iff_ne_zero.mpr
  intro hz
  have hz' : (volume.restrict (axisCube y side)) Set.univ = 0 :=
    hAc (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hz)
  have hp := (isOpen_axisCube y side).measure_pos volume (axisCube_nonempty y side hs)
  exact hp.ne' (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hz')

/-- The real-valued weighted mass of a positive-side axis cube is strictly positive. -/
theorem weightedMeasure_axisCube_toReal_pos
    (hρ : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho)
    (y : Vec d) (side : ℝ) (hs : 0 < side) :
    0 < ((weightedMeasure rho) (axisCube y side)).toReal := by
  exact ENNReal.toReal_pos (weightedMeasure_axisCube_pos hρ y side hs).ne'
    (weightedMeasure_axisCube_lt_top hρ y side).ne

/-- Every open set meeting the domain has positive restricted weighted mass. -/
theorem weightedMeasure_restrict_open_pos (hU : IsOpen U) (hρ : CoefficientOn U rho)
    (V : Set (Vec d)) (hV : IsOpen V) (hne : (V ∩ U).Nonempty) :
    0 < ((weightedMeasure rho).restrict U) V := by
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hρ
  apply pos_iff_ne_zero.mpr
  intro hz
  have hz' := hAc hz
  rw [Measure.restrict_apply hV.measurableSet] at hz'
  exact (hV.inter hU).measure_ne_zero volume hne hz'

/-- A continuous almost-everywhere bound holds throughout an open set for a measure positive on open sets. -/
theorem continuousOn_le_of_ae_restrict {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (ν : Measure α) [ν.IsOpenPosMeasure] (V : Set α) (hV : IsOpen V)
    (f : α → ℝ) (hf : ContinuousOn f V) (M : ℝ)
    (hae : ∀ᵐ x ∂ν.restrict V, f x ≤ M) : ∀ x ∈ V, f x ≤ M := by
  have heq : (fun x => min (f x) M) =ᵐ[ν.restrict V] f :=
    hae.mono (fun _ hx => min_eq_left hx)
  have hpoint := Measure.eqOn_open_of_ae_eq heq hV (continuous_min.comp_continuousOn (hf.prodMk continuousOn_const)) hf
  intro x hx
  exact min_eq_left_iff.mp (hpoint hx)

/-- Local positive density bounds upgrade a product-almost-everywhere continuous bound to every pair of points. -/
theorem continuousOn_le_of_ae_weightedMeasure_prod (hU : IsOpen U)
    (hρ : CoefficientOn U rho) [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (f : Vec d × Vec d → ℝ) (hf : ContinuousOn f (U ×ˢ U)) (M : ℝ)
    (hae : ∀ᵐ z ∂((weightedMeasure rho).restrict U).prod ((weightedMeasure rho).restrict U),
      f z ≤ M) : ∀ z ∈ U ×ˢ U, f z ≤ M := by
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hρ
  have hvol := hae.filter_mono (hAc.prod hAc).ae_le
  rw [Measure.prod_restrict] at hvol
  exact continuousOn_le_of_ae_restrict (volume.prod volume) (U ×ˢ U) (hU.prod hU) f hf M hvol

/-- Joint continuity upgrades the positive-time product-almost-everywhere density bound to the diagonal. -/
theorem continuousOn_density_diagonal_le
    (hρ : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho)
    (y : Vec d) (side : ℝ) (p : ℝ → Vec d → Vec d → ℝ) (bound : ℝ → ℝ)
    (hp : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ axisCube y side ×ˢ axisCube y side))
    (hae : ∀ t : ℝ, 0 < t → ∀ᵐ z ∂
      ((weightedMeasure rho).restrict (axisCube y side)).prod
        ((weightedMeasure rho).restrict (axisCube y side)), p t z.1 z.2 ≤ bound t) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ axisCube y side, p t x x ≤ bound t := by
  let : IsFiniteMeasure ((weightedMeasure rho).restrict (axisCube y side)) :=
    ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using
      weightedMeasure_axisCube_lt_top hρ y side⟩
  intro t ht x hx
  have hslice : ContinuousOn (fun z : Vec d × Vec d => p t z.1 z.2)
      (axisCube y side ×ˢ axisCube y side) :=
    hp.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨ht, hz⟩)
  exact continuousOn_le_of_ae_weightedMeasure_prod (isOpen_axisCube y side)
    (coefficientOn_axisCube hρ y side) _ hslice (bound t) (hae t ht) (x, x) ⟨hx, hx⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
