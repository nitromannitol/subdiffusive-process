import SubdiffusiveProcess.Sobolev.PotentialResponses
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # Continuous potentials on a compact root

The map below is the actual restriction to the observation domain. A zero
extension is used only as a representative off the compact root; when the
root contains the domain, that extension is invisible to restricted volume.
This is a contraction from a separable continuous-function space into L∞.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Zero extension is used only to represent a compact-root potential on ambient space. -/
def compactPotentialExtension (K : Compacts (SpatialCoordinates d)) (f : C(K, ℝ)) :
    SpatialCoordinates d → ℝ := Function.extend Subtype.val f (fun _ => 0)

/-- The representative agrees with the continuous potential everywhere on its root. -/
theorem compactPotentialExtension_apply (K : Compacts (SpatialCoordinates d))
    (f : C(K, ℝ)) (x : K) : compactPotentialExtension K f x = f x :=
  Subtype.coe_injective.extend_apply _ _ _

/-- The representative is zero off its declared root. -/
theorem compactPotentialExtension_outside (K : Compacts (SpatialCoordinates d))
    (f : C(K, ℝ)) {x : SpatialCoordinates d} (hx : x ∉ K) :
    compactPotentialExtension K f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

/-- The representative is Borel measurable; continuity across the root boundary is not claimed. -/
theorem measurable_compactPotentialExtension (K : Compacts (SpatialCoordinates d))
    (f : C(K, ℝ)) : Measurable (compactPotentialExtension K f) :=
  (MeasurableEmbedding.subtype_coe K.isCompact.measurableSet).measurable_extend
    f.continuous.measurable measurable_const

/-- Zero extension does not increase the supremum bound. -/
theorem compactPotentialExtension_norm_le (K : Compacts (SpatialCoordinates d))
    (f : C(K, ℝ)) (x : SpatialCoordinates d) : ‖compactPotentialExtension K f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ K
  · rw [compactPotentialExtension_apply K f ⟨x, hx⟩]
    exact f.norm_coe_le_norm ⟨x, hx⟩
  · rw [compactPotentialExtension_outside K f hx, norm_zero]
    exact norm_nonneg _

/-- Compact-root continuous potentials are genuinely essentially bounded on the observation domain. -/
theorem compactPotentialExtension_memLp (K : Compacts (SpatialCoordinates d)) (f : C(K, ℝ)) :
    MemLp (compactPotentialExtension K f) ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  memLp_top_of_bound (measurable_compactPotentialExtension K f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (compactPotentialExtension_norm_le K f))

/-- The L∞ class of the literal zero extension; restriction to an enclosed domain is identified below. -/
def compactPotentialLp (K : Compacts (SpatialCoordinates d)) (f : C(K, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  (compactPotentialExtension_memLp K f).toLp (compactPotentialExtension K f)

/-- Exact almost-everywhere representative of the compact-root potential. -/
theorem compactPotentialLp_coeFn (K : Compacts (SpatialCoordinates d)) (f : C(K, ℝ)) :
    (compactPotentialLp (Ω := Ω) K f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      compactPotentialExtension K f := (compactPotentialExtension_memLp K f).coeFn_toLp

/-- When the domain lies inside the root, the representative is its actual restriction. -/
theorem compactPotentialLp_on_domain (K : Compacts (SpatialCoordinates d))
    (hΩ : (Ω : Set (SpatialCoordinates d)) ⊆ K) (f : C(K, ℝ)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ Ω, compactPotentialLp (Ω := Ω) K f x = f ⟨x, hΩ hx⟩ := by
  filter_upwards [compactPotentialLp_coeFn (Ω := Ω) K f] with x hx
  intro h
  exact hx.trans (compactPotentialExtension_apply K f ⟨x, hΩ h⟩)

/-- Restriction is linear in the compact-root potential. -/
theorem compactPotentialLp_add (K : Compacts (SpatialCoordinates d)) (f g : C(K, ℝ)) :
    compactPotentialLp (Ω := Ω) K (f + g) = compactPotentialLp K f + compactPotentialLp K g := by
  apply Lp.ext
  filter_upwards [compactPotentialLp_coeFn (Ω := Ω) K (f + g), compactPotentialLp_coeFn (Ω := Ω) K f,
    compactPotentialLp_coeFn (Ω := Ω) K g, Lp.coeFn_add (compactPotentialLp (Ω := Ω) K f) (compactPotentialLp K g)]
    with x hfg hf hg ha
  rw [hfg, ha, Pi.add_apply, hf, hg]
  by_cases hx : x ∈ K
  · rw [compactPotentialExtension_apply K (f + g) ⟨x, hx⟩,
      compactPotentialExtension_apply K f ⟨x, hx⟩, compactPotentialExtension_apply K g ⟨x, hx⟩]
    rfl
  · rw [compactPotentialExtension_outside K (f + g) hx,
      compactPotentialExtension_outside K f hx, compactPotentialExtension_outside K g hx, add_zero]

/-- Restriction commutes with scalar multiplication. -/
theorem compactPotentialLp_smul (K : Compacts (SpatialCoordinates d)) (r : ℝ) (f : C(K, ℝ)) :
    compactPotentialLp (Ω := Ω) K (r • f) = r • compactPotentialLp K f := by
  apply Lp.ext
  filter_upwards [compactPotentialLp_coeFn (Ω := Ω) K (r • f), compactPotentialLp_coeFn (Ω := Ω) K f,
    Lp.coeFn_smul r (compactPotentialLp (Ω := Ω) K f)] with x hrf hf hr
  rw [hrf, hr, Pi.smul_apply, hf]
  by_cases hx : x ∈ K
  · rw [compactPotentialExtension_apply K (r • f) ⟨x, hx⟩, compactPotentialExtension_apply K f ⟨x, hx⟩]
    rfl
  · rw [compactPotentialExtension_outside K (r • f) hx,
      compactPotentialExtension_outside K f hx, smul_zero]

/-- The actual essential-supremum norm is bounded by the compact-root supremum norm. -/
theorem compactPotentialLp_norm_le (K : Compacts (SpatialCoordinates d)) (f : C(K, ℝ)) :
    ‖compactPotentialLp (Ω := Ω) K f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  have he : eLpNormEssSup (⇑(compactPotentialLp (Ω := Ω) K f))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) ≤ ENNReal.ofReal ‖f‖ := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [compactPotentialLp_coeFn (Ω := Ω) K f] with x hx
    rw [hx]
    exact compactPotentialExtension_norm_le K f x
  simpa only [ENNReal.toReal_ofReal (norm_nonneg f)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- Continuous linear restriction of a compact-root continuous potential to L∞. -/
def compactPotentialToLp (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] :
    C(K, ℝ) →L[ℝ] Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  LinearMap.mkContinuous
    { toFun := compactPotentialLp K
      map_add' := compactPotentialLp_add K
      map_smul' := compactPotentialLp_smul K }
    1 (fun f => by simpa only [one_mul] using compactPotentialLp_norm_le (Ω := Ω) K f)

/-- The continuous linear map has exactly the already identified representative. -/
theorem compactPotentialToLp_apply (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (f : C(K, ℝ)) :
    compactPotentialToLp (Ω := Ω) K f = compactPotentialLp K f := rfl

/-- Retained-potential differences do not grow under restriction. -/
theorem compactPotentialToLp_sub_norm_le (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (f g : C(K, ℝ)) :
    ‖compactPotentialToLp (Ω := Ω) K f - compactPotentialToLp K g‖ ≤ ‖f - g‖ := by
  rw [← map_sub]
  exact compactPotentialLp_norm_le K (f - g)

/-- The public restriction map uses an enclosing root and has the actual restricted values. -/
theorem compactPotentialToLp_on_domain (K : Compacts (SpatialCoordinates d))
    [hΩ : Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (f : C(K, ℝ)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ Ω, compactPotentialToLp (Ω := Ω) K f x = f ⟨x, hΩ.out hx⟩ :=
  compactPotentialLp_on_domain K hΩ.out f

/-- Adding a spatial constant to a compact potential scales its actual coefficient
by the exponential of that constant on every enclosed observation domain. -/
theorem expPotentialCoefficient_compact_add_const
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (K : Compacts (SpatialCoordinates d))
    [Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K))] (f : C(K, ℝ)) (c : ℝ) :
    expPotentialCoefficient (compactPotentialToLp (Ω := Ω) K (f + ContinuousMap.const K c)) =
      scalePositiveCoefficient (Real.exp c) (Real.exp_pos c)
        (expPotentialCoefficient (compactPotentialToLp (Ω := Ω) K f)) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [
    expPotentialCoefficient_coeFn
      (compactPotentialToLp (Ω := Ω) K (f + ContinuousMap.const K c)),
    expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Ω) K f),
    scalePositiveCoefficient_coeFn (Real.exp c) (Real.exp_pos c)
      (expPotentialCoefficient (compactPotentialToLp (Ω := Ω) K f)),
    compactPotentialToLp_on_domain (Ω := Ω) K (f + ContinuousMap.const K c),
    compactPotentialToLp_on_domain (Ω := Ω) K f,
    ae_restrict_mem Ω.isOpen.measurableSet] with x hadd_exp hf_exp hscale hadd hf hx
  rw [hadd_exp, hscale, hf_exp, hadd hx, hf hx, ← Real.exp_add]
  simp only [ContinuousMap.coe_add, Pi.add_apply, ContinuousMap.const_apply, add_comm]

end SubdiffusiveProcess
