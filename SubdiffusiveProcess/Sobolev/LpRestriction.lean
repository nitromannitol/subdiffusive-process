import SubdiffusiveProcess.Sobolev.WeakGradient

/-!
# Restriction of the actual domain Lp classes

Restriction changes the measure from volume on an open domain to volume on
an open subdomain. It retains the same function almost everywhere there;
no new values or independent cell functions enter the construction.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U V Ω : Opens (SpatialCoordinates d)} {p : ℝ≥0∞}

/-- The actual Lp restriction along inclusion of open domains. -/
def domainLpRestrict (hU : U ≤ Ω)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    Lp ℝ p (volume.restrict (U : Set (SpatialCoordinates d))) :=
  ((Lp.memLp f).mono_measure (Measure.restrict_mono_set volume hU)).toLp f

/-- Restriction preserves the original representative almost everywhere on the subdomain. -/
theorem domainLpRestrict_coeFn (hU : U ≤ Ω)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (domainLpRestrict hU f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] f := MemLp.coeFn_toLp _

/-- Restriction to the same domain is the identity. -/
theorem domainLpRestrict_refl
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    domainLpRestrict le_rfl f = f := Lp.ext (domainLpRestrict_coeFn le_rfl f)

/-- Nested restriction is exactly direct restriction of the original class. -/
theorem domainLpRestrict_trans (hVU : V ≤ U) (hU : U ≤ Ω)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    domainLpRestrict hVU (domainLpRestrict hU f) = domainLpRestrict (hVU.trans hU) f := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hVU (domainLpRestrict hU f),
    ae_restrict_of_ae_restrict_of_subset hVU (domainLpRestrict_coeFn hU f),
    domainLpRestrict_coeFn (hVU.trans hU) f] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- Restriction cannot increase the Lp norm, including the essential supremum. -/
theorem domainLpRestrict_norm_le (hU : U ≤ Ω)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ‖domainLpRestrict hU f‖ ≤ ‖f‖ := by
  rw [domainLpRestrict, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne
    (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hU))

/-- Addition commutes with actual restriction. -/
theorem domainLpRestrict_add (hU : U ≤ Ω)
    (f g : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    domainLpRestrict hU (f + g) = domainLpRestrict hU f + domainLpRestrict hU g := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hU (f + g),
    ae_restrict_of_ae_restrict_of_subset hU (Lp.coeFn_add f g),
    Lp.coeFn_add (domainLpRestrict hU f) (domainLpRestrict hU g),
    domainLpRestrict_coeFn hU f, domainLpRestrict_coeFn hU g] with x hs ha ht hf hg
  simp only [hs, ha, ht, Pi.add_apply, hf, hg]

/-- Real scalar multiplication commutes with actual restriction. -/
theorem domainLpRestrict_smul (hU : U ≤ Ω) (c : ℝ)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    domainLpRestrict hU (c • f) = c • domainLpRestrict hU f := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hU (c • f),
    ae_restrict_of_ae_restrict_of_subset hU (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (domainLpRestrict hU f), domainLpRestrict_coeFn hU f] with x hs ha ht hf
  simp only [hs, ha, ht, Pi.smul_apply, hf]

end SubdiffusiveProcess
