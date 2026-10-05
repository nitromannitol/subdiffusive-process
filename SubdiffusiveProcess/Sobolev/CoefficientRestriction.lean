module

public import SubdiffusiveProcess.Sobolev.LpRestriction
public import SubdiffusiveProcess.Sobolev.CompactPotential

@[expose] public section

/-!
# One coefficient restricted to nested domains

All subdomain coefficients are restrictions of the same actual L∞ class.
Lower and upper bounds, exponentiation and compact continuous potentials
are compatible with this restriction. The constants may depend on the
finite cutoff; no uniform-in-cutoff ellipticity is asserted.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U V Ω : Opens (SpatialCoordinates d)}

/-- Restriction of the same positive bounded coefficient to an open subdomain. -/
def positiveCoefficientRestrict (hU : U ≤ Ω) (a : PositiveCoefficient Ω) :
    PositiveCoefficient U := by
  refine ⟨domainLpRestrict hU a.val, ?_⟩
  obtain ⟨c, hc, ha⟩ := a.property
  refine ⟨c, hc, ?_⟩
  filter_upwards [domainLpRestrict_coeFn hU a.val,
    ae_restrict_of_ae_restrict_of_subset hU ha] with x he hx
  exact he.symm ▸ hx

/-- The restricted coefficient has the original values almost everywhere on the subdomain. -/
theorem positiveCoefficientRestrict_coeFn (hU : U ≤ Ω) (a : PositiveCoefficient Ω) :
    ((positiveCoefficientRestrict hU a).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] a.val :=
  domainLpRestrict_coeFn hU a.val

/-- The same lower ellipticity constant works on every subdomain. -/
theorem positiveCoefficientRestrict_lower (hU : U ≤ Ω) (a : PositiveCoefficient Ω)
    {c : ℝ} (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x) :
    ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      c ≤ (positiveCoefficientRestrict hU a).val x := by
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    ae_restrict_of_ae_restrict_of_subset hU ha] with x he hx
  exact he.symm ▸ hx

/-- The same upper coefficient bound works on every subdomain. -/
theorem positiveCoefficientRestrict_upper (hU : U ≤ Ω) (a : PositiveCoefficient Ω)
    {M : ℝ} (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ M) :
    ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      (positiveCoefficientRestrict hU a).val x ≤ M := by
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    ae_restrict_of_ae_restrict_of_subset hU ha] with x he hx
  exact he.symm ▸ hx

/-- The root essential-supremum norm is a common upper bound, without a new hypothesis. -/
theorem positiveCoefficientRestrict_le_norm (hU : U ≤ Ω) (a : PositiveCoefficient Ω) :
    ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      (positiveCoefficientRestrict hU a).val x ≤ ‖a.val‖ := by
  apply positiveCoefficientRestrict_upper hU a
  exact (boundedPotential_ae_bound a.val).mono fun x hx => (le_abs_self _).trans hx

/-- Restriction to the original domain gives the original coefficient. -/
theorem positiveCoefficientRestrict_refl (a : PositiveCoefficient Ω) :
    positiveCoefficientRestrict le_rfl a = a :=
  Subtype.ext (domainLpRestrict_refl a.val)

/-- Coefficient restriction is consistent through every intermediate domain. -/
theorem positiveCoefficientRestrict_trans (hVU : V ≤ U) (hU : U ≤ Ω)
    (a : PositiveCoefficient Ω) :
    positiveCoefficientRestrict hVU (positiveCoefficientRestrict hU a) =
      positiveCoefficientRestrict (hVU.trans hU) a :=
  Subtype.ext (domainLpRestrict_trans hVU hU a.val)

/-- Restricting the potential and exponentiating gives exactly the restricted coefficient. -/
theorem positiveCoefficientRestrict_exp (hU : U ≤ Ω)
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    positiveCoefficientRestrict hU (expPotentialCoefficient g) =
      expPotentialCoefficient (domainLpRestrict hU g) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [positiveCoefficientRestrict_coeFn hU (expPotentialCoefficient g),
    ae_restrict_of_ae_restrict_of_subset hU (expPotentialCoefficient_coeFn g),
    expPotentialCoefficient_coeFn (domainLpRestrict hU g), domainLpRestrict_coeFn hU g]
    with x he hg hr hx
  rw [he, hg, hr, hx]

/-- A continuous compact-root potential restricted in stages is its direct subdomain class. -/
theorem domainLpRestrict_compactPotential (hU : U ≤ Ω)
    (K : Compacts (SpatialCoordinates d)) (g : C(K, ℝ)) :
    domainLpRestrict hU (compactPotentialLp (Ω := Ω) K g) =
      compactPotentialLp (Ω := U) K g := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hU (compactPotentialLp (Ω := Ω) K g),
    ae_restrict_of_ae_restrict_of_subset hU (compactPotentialLp_coeFn (Ω := Ω) K g),
    compactPotentialLp_coeFn (Ω := U) K g] with x hr hΩ hU
  exact hr.trans (hΩ.trans hU.symm)

/-- The finite-cutoff exponential of a compact-root potential has the same cell coefficient. -/
theorem positiveCoefficientRestrict_compactPotential (hU : U ≤ Ω)
    (K : Compacts (SpatialCoordinates d)) (g : C(K, ℝ)) :
    positiveCoefficientRestrict hU (expPotentialCoefficient (compactPotentialLp (Ω := Ω) K g)) =
      expPotentialCoefficient (compactPotentialLp (Ω := U) K g) := by
  rw [positiveCoefficientRestrict_exp, domainLpRestrict_compactPotential]

end SubdiffusiveProcess
