module

public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.Sobolev.ReflectionEnergy
public import SubdiffusiveProcess.Sobolev.LpRestriction

@[expose] public section

/-!
# Weak equation transport under even reflection

Let `D` be an `EvenReflectionDomain` with lower half `Ω`, upper half `RΩ`
and doubled domain `U`. For a positive bounded coefficient `a` on `Ω` its even
extension `ã` is `a` on `Ω` and `a ∘ R` on `RΩ` (zero extensions added; the
lower ellipticity constant is preserved because the plane is null).

Energy identity. For Sobolev data `u` on `Ω` and any data `ψ` on `U`,

  `E_ã(ũ, ψ) = E_a(u, ψ|_Ω) + E_a(u, R^*(ψ|_{RΩ}))`,

where `R^*` is the signed pullback `reflectionSobolevData`. Proof: `ũ` is a
sum of two zero extensions and `E` is bilinear; testing a zero extension from
`V` against `ψ` only sees `ψ|_V` and `ã|_V`; on `RΩ` the coefficient is the
reflected coefficient and `sobolevCoefficientForm_reflection` moves everything
back to `Ω`. No integrability is needed beyond the definitions.

Consequences. If `E_a(u, v) = L v` for every `v` in the weak Sobolev graph of
`Ω` (this is the weak Neumann equation: the zero conormal condition is encoded
by testing against all of `H¹(Ω)`, not only `H¹_0(Ω)`), then for every `ψ` in
the weak Sobolev graph of `U`

  `E_ã(ũ, ψ) = L (ψ|_Ω) + L (R^*(ψ|_{RΩ}))`,

using that restriction and signed pullback preserve the weak graph. The
mean-zero version replaces the graph by the mean-zero graph on both sides and
uses `∫_Ω ψ|_Ω + ∫_Ω R^*(ψ|_{RΩ}) = ∫_U ψ`.

Not claimed: no trace, no boundary flux formula, no statement about several
faces or corners (iteration of this lemma is left to the consumer), and no
assertion that `L` is given by a volume or face density.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {V U : Opens (SpatialCoordinates d)}

/-- Restriction of function and gradient data to an open subdomain. -/
def sobolevDataRestrict (hV : V ≤ U) (ψ : SobolevData U) : SobolevData V :=
  (domainLpRestrict hV ψ.1, fun j => domainLpRestrict hV (ψ.2 j))

/-- A test compactly supported in a subdomain is a test on the larger domain. -/
def extendTest (hV : V ≤ U) (φ : 𝓓(V, ℝ)) : 𝓓(U, ℝ) :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hV⟩

theorem extendTest_apply (hV : V ≤ U) (φ : 𝓓(V, ℝ)) (x : SpatialCoordinates d) :
    extendTest hV φ x = φ x := rfl

/-- Restriction preserves the weak-gradient graph. -/
theorem sobolevDataRestrict_mem_weak (hV : V ≤ U) {ψ : SobolevData U}
    (hψ : ψ ∈ weakSobolevGraph U) : sobolevDataRestrict hV ψ ∈ weakSobolevGraph V := by
  rw [mem_weakSobolevGraph_iff] at hψ ⊢
  intro φ j
  have h := hψ (extendTest hV φ) j
  have e1 : (∫ x in (U : Set (SpatialCoordinates d)), extendTest hV φ x * ψ.2 j x) =
      ∫ x in (V : Set (SpatialCoordinates d)), φ x * (sobolevDataRestrict hV ψ).2 j x := by
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero U.isOpen.measurableSet
      (show (V : Set (SpatialCoordinates d)) ⊆ U from hV) (fun x hx => by
        rw [extendTest_apply, image_eq_zero_of_notMem_tsupport
          (fun h => hx.2 (φ.tsupport_subset h)), zero_mul])]
    apply integral_congr_ae
    filter_upwards [domainLpRestrict_coeFn hV (ψ.2 j)] with x hx
    change φ x * ψ.2 j x = φ x * domainLpRestrict hV (ψ.2 j) x
    rw [hx]
  have e2 : (∫ x in (U : Set (SpatialCoordinates d)),
      fderiv ℝ (extendTest hV φ) x (Pi.single j 1) * ψ.1 x) =
      ∫ x in (V : Set (SpatialCoordinates d)),
        fderiv ℝ φ x (Pi.single j 1) * (sobolevDataRestrict hV ψ).1 x := by
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero U.isOpen.measurableSet
      (show (V : Set (SpatialCoordinates d)) ⊆ U from hV) (fun x hx => by
        change fderiv ℝ φ x (Pi.single j 1) * ψ.1 x = 0
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx.2 (φ.tsupport_subset h)),
          ContinuousLinearMap.zero_apply, zero_mul])]
    apply integral_congr_ae
    filter_upwards [domainLpRestrict_coeFn hV ψ.1] with x hx
    change fderiv ℝ φ x (Pi.single j 1) * ψ.1 x =
      fderiv ℝ φ x (Pi.single j 1) * domainLpRestrict hV ψ.1 x
    rw [hx]
  rw [e1, e2] at h
  exact h

/-- Testing a zero extension against data on the large domain only sees the subdomain
restriction, and the coefficient only through its values on the subdomain. -/
theorem sobolevCoefficientForm_zeroExtension (hV : V ≤ U) (b : PositiveCoefficient U)
    (a : PositiveCoefficient V)
    (hab : (b.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] a.val)
    (v : SobolevData V) (ψ : SobolevData U) :
    sobolevCoefficientForm b (zeroExtensionSobolevData hV v) ψ =
      sobolevCoefficientForm a v (sobolevDataRestrict hV ψ) := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc (∫ x in (U : Set (SpatialCoordinates d)),
        b.val x * ((zeroExtensionSobolevData hV v).2 j x * ψ.2 j x))
      = ∫ x in (U : Set (SpatialCoordinates d)),
          (V : Set (SpatialCoordinates d)).indicator (fun x => b.val x * (v.2 j x * ψ.2 j x)) x := by
        apply integral_congr_ae
        filter_upwards [zeroExtensionLp_coeFn hV (v.2 j)] with x hx
        change b.val x * (zeroExtensionLp hV (v.2 j) x * ψ.2 j x) = _
        rw [hx]
        by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
        · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem hxV]
        · rw [Set.indicator_of_notMem hxV, Set.indicator_of_notMem hxV, zero_mul, mul_zero]
    _ = ∫ x in (U : Set (SpatialCoordinates d)) ∩ V, b.val x * (v.2 j x * ψ.2 j x) :=
        setIntegral_indicator V.isOpen.measurableSet
    _ = _ := by
        rw [Set.inter_eq_right.mpr (show (V : Set (SpatialCoordinates d)) ⊆ U from hV)]
        apply integral_congr_ae
        filter_upwards [hab, domainLpRestrict_coeFn hV (ψ.2 j)] with x h1 h2
        change b.val x * (v.2 j x * ψ.2 j x) = a.val x * (v.2 j x * domainLpRestrict hV (ψ.2 j) x)
        rw [h1, h2]

namespace EvenReflectionDomain
variable (D : EvenReflectionDomain d)

/-- The coefficient pulled back to the upper half. -/
def reflectedCoefficient (a : PositiveCoefficient D.Ω) : PositiveCoefficient D.reflected :=
  reflectionCoefficient D.z {D.i} D.preimage_Ω a

/-- The reflected coefficient keeps the original lower ellipticity constant. -/
theorem reflectedCoefficient_lower (a : PositiveCoefficient D.Ω) {c : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)), c ≤ a.val x) :
    ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      c ≤ (D.reflectedCoefficient a).val x := by
  have hm := coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  filter_upwards [reflectionCoefficient_coeFn D.z {D.i} D.preimage_Ω a,
    hm.quasiMeasurePreserving.ae ha] with x he hx
  exact he.symm ▸ hx

/-- The even extension of a positive bounded coefficient. -/
def evenExtensionCoefficient (a : PositiveCoefficient D.Ω) : PositiveCoefficient D.U := by
  refine ⟨zeroExtensionLp D.Ω_le a.val +
    zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val, ?_⟩
  obtain ⟨c, hc, ha⟩ := a.property
  refine ⟨c, hc, ?_⟩
  filter_upwards [Lp.coeFn_add (zeroExtensionLp D.Ω_le a.val)
    (zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val),
    zeroExtensionLp_coeFn D.Ω_le a.val,
    zeroExtensionLp_coeFn D.reflected_le (D.reflectedCoefficient a).val, D.ae_mem_or_mem,
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp ha),
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
        (D.reflectedCoefficient_lower a ha))] with x hadd h1 h2 hmem hΩ hR
  rw [hadd, Pi.add_apply, h1, h2]
  rcases hmem with hx | hx
  · rw [Set.indicator_of_mem (show x ∈ (D.Ω : Set (SpatialCoordinates d)) from hx),
      Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
    exact hΩ hx
  · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
      Set.indicator_of_mem (show x ∈ (D.reflected : Set (SpatialCoordinates d)) from hx), zero_add]
    exact hR hx

/-- On the lower half the even extension is the original coefficient. -/
theorem evenExtensionCoefficient_ae_Ω (a : PositiveCoefficient D.Ω) :
    ((D.evenExtensionCoefficient a).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))] a.val := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset D.Ω_le
    (Lp.coeFn_add (zeroExtensionLp D.Ω_le a.val)
      (zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val)),
    ae_restrict_of_ae_restrict_of_subset D.Ω_le (zeroExtensionLp_coeFn D.Ω_le a.val),
    ae_restrict_of_ae_restrict_of_subset D.Ω_le
      (zeroExtensionLp_coeFn D.reflected_le (D.reflectedCoefficient a).val),
    ae_restrict_mem D.Ω.isOpen.measurableSet] with x hadd h1 h2 hx
  change (zeroExtensionLp D.Ω_le a.val +
    zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val) x = a.val x
  rw [hadd, Pi.add_apply, h1, h2, Set.indicator_of_mem hx,
    Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]

/-- On the upper half the even extension is the reflected coefficient. -/
theorem evenExtensionCoefficient_ae_reflected (a : PositiveCoefficient D.Ω) :
    ((D.evenExtensionCoefficient a).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.reflected : Set (SpatialCoordinates d))]
        (D.reflectedCoefficient a).val := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset D.reflected_le
    (Lp.coeFn_add (zeroExtensionLp D.Ω_le a.val)
      (zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val)),
    ae_restrict_of_ae_restrict_of_subset D.reflected_le (zeroExtensionLp_coeFn D.Ω_le a.val),
    ae_restrict_of_ae_restrict_of_subset D.reflected_le
      (zeroExtensionLp_coeFn D.reflected_le (D.reflectedCoefficient a).val),
    ae_restrict_mem D.reflected.isOpen.measurableSet] with x hadd h1 h2 hx
  change (zeroExtensionLp D.Ω_le a.val +
    zeroExtensionLp D.reflected_le (D.reflectedCoefficient a).val) x =
      (D.reflectedCoefficient a).val x
  rw [hadd, Pi.add_apply, h1, h2, Set.indicator_of_mem hx,
    Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx), zero_add]

/-- The upper-half restriction of data on `U`, pulled back to the lower half with signs. -/
def reflectedRestrict (ψ : SobolevData D.U) : SobolevData D.Ω :=
  reflectionSobolevData D.z {D.i} D.preimage_reflected (sobolevDataRestrict D.reflected_le ψ)

/-- The pulled-back upper restriction lies in the weak graph. -/
theorem reflectedRestrict_mem_weak {ψ : SobolevData D.U} (hψ : ψ ∈ weakSobolevGraph D.U) :
    D.reflectedRestrict ψ ∈ weakSobolevGraph D.Ω :=
  reflectionSobolevData_mem_weak D.z {D.i} D.preimage_reflected
    (sobolevDataRestrict_mem_weak D.reflected_le hψ)

/-- **Energy identity for the even extension.** -/
theorem sobolevCoefficientForm_evenExtension (a : PositiveCoefficient D.Ω) (u : SobolevData D.Ω)
    (ψ : SobolevData D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.evenExtension u) ψ =
      sobolevCoefficientForm a u (sobolevDataRestrict D.Ω_le ψ) +
        sobolevCoefficientForm a u (D.reflectedRestrict ψ) := by
  rw [evenExtension, map_add, ContinuousLinearMap.add_apply,
    sobolevCoefficientForm_zeroExtension D.Ω_le _ a (D.evenExtensionCoefficient_ae_Ω a),
    sobolevCoefficientForm_zeroExtension D.reflected_le _ (D.reflectedCoefficient a)
      (D.evenExtensionCoefficient_ae_reflected a)]
  congr 1
  have h := sobolevCoefficientForm_reflection D.z {D.i} D.preimage_Ω a u (D.reflectedRestrict ψ)
  rw [← h]
  congr 1
  exact (reflectionSobolevData_inverse D.z {D.i} D.preimage_reflected
    (sobolevDataRestrict D.reflected_le ψ)).symm

/-- **Weak equation transport.** A weak Neumann solution on the lower half (tested against
the whole weak graph) has an even extension solving the reflected equation on the doubled
domain, with the load evaluated on the two half restrictions. -/
theorem evenExtension_weak_equation (a : PositiveCoefficient D.Ω) {u : SobolevData D.Ω}
    (L : SobolevData D.Ω →L[ℝ] ℝ)
    (hL : ∀ v ∈ weakSobolevGraph D.Ω, sobolevCoefficientForm a u v = L v)
    {ψ : SobolevData D.U} (hψ : ψ ∈ weakSobolevGraph D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.evenExtension u) ψ =
      L (sobolevDataRestrict D.Ω_le ψ) + L (D.reflectedRestrict ψ) := by
  rw [sobolevCoefficientForm_evenExtension, hL _ (sobolevDataRestrict_mem_weak D.Ω_le hψ),
    hL _ (D.reflectedRestrict_mem_weak hψ)]

section MeanZero
variable [IsFiniteMeasure (volume.restrict (D.U : Set (SpatialCoordinates d)))]

/-- The two half integrals of data on `U` add up to the full integral. -/
theorem integral_restrict_add_reflectedRestrict (ψ : SobolevData D.U) :
    (∫ x in (D.Ω : Set (SpatialCoordinates d)), (sobolevDataRestrict D.Ω_le ψ).1 x) +
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), (D.reflectedRestrict ψ).1 x) =
      ∫ x in (D.U : Set (SpatialCoordinates d)), ψ.1 x := by
  have hint : Integrable ψ.1 (volume.restrict (D.U : Set (SpatialCoordinates d))) :=
    (Lp.memLp ψ.1).integrable one_le_two
  have e1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), (sobolevDataRestrict D.Ω_le ψ).1 x) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), ψ.1 x :=
    integral_congr_ae (domainLpRestrict_coeFn D.Ω_le ψ.1)
  have e2 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), (D.reflectedRestrict ψ).1 x) =
      ∫ x in (D.reflected : Set (SpatialCoordinates d)), ψ.1 x := by
    change (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      reflectionLp D.z {D.i} D.preimage_reflected (domainLpRestrict D.reflected_le ψ.1) x) = _
    rw [integral_reflectionLp]
    exact integral_congr_ae (domainLpRestrict_coeFn D.reflected_le ψ.1)
  rw [e1, e2, ← setIntegral_union D.disjoint_Ω_reflected D.reflected.isOpen.measurableSet
    (hint.mono_measure (Measure.restrict_mono D.Ω_le le_rfl))
    (hint.mono_measure (Measure.restrict_mono D.reflected_le le_rfl))]
  exact setIntegral_congr_set D.union_ae_eq

variable [IsFiniteMeasure (volume.restrict (D.Ω : Set (SpatialCoordinates d)))]

/-- The even extension preserves the mean-zero condition. -/
theorem evenExtension_mem_meanZero {u : SobolevData D.Ω} (hu : u ∈ meanZeroSobolevGraph D.Ω) :
    D.evenExtension u ∈ meanZeroSobolevGraph D.U := by
  rw [mem_meanZeroSobolevGraph_iff] at hu ⊢
  refine ⟨D.evenExtension_mem_weak hu.1, ?_⟩
  have h1 : Integrable (zeroExtensionLp D.Ω_le u.1)
      (volume.restrict (D.U : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  have h2 : Integrable (zeroExtensionLp D.reflected_le (D.reflectedData u).1)
      (volume.restrict (D.U : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  calc (∫ x in (D.U : Set (SpatialCoordinates d)), (D.evenExtension u).1 x)
      = ∫ x in (D.U : Set (SpatialCoordinates d)),
          (zeroExtensionLp D.Ω_le u.1 x + zeroExtensionLp D.reflected_le (D.reflectedData u).1 x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (zeroExtensionLp D.Ω_le u.1)
          (zeroExtensionLp D.reflected_le (D.reflectedData u).1)] with x hx
        exact hx
    _ = (∫ x in (D.Ω : Set (SpatialCoordinates d)), u.1 x) +
          ∫ x in (D.Ω : Set (SpatialCoordinates d)), u.1 x := by
        rw [integral_add h1 h2, integral_zeroExtensionLp, integral_zeroExtensionLp]
        congr 1
        exact integral_reflectionLp D.z {D.i} D.preimage_Ω u.1
    _ = 0 := by rw [hu.2, add_zero]

/-- **Mean-zero weak equation transport.** If the weak equation holds against mean-zero
tests on the lower half, the even extension satisfies it against mean-zero tests on the
doubled domain, with the load evaluated on the (mean-zero) sum of the two half
restrictions. -/
theorem evenExtension_weak_equation_meanZero (a : PositiveCoefficient D.Ω) {u : SobolevData D.Ω}
    (L : SobolevData D.Ω →L[ℝ] ℝ)
    (hL : ∀ v ∈ meanZeroSobolevGraph D.Ω, sobolevCoefficientForm a u v = L v)
    {ψ : SobolevData D.U} (hψ : ψ ∈ meanZeroSobolevGraph D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.evenExtension u) ψ =
      L (sobolevDataRestrict D.Ω_le ψ + D.reflectedRestrict ψ) := by
  rw [sobolevCoefficientForm_evenExtension, ← map_add]
  apply hL
  rw [mem_meanZeroSobolevGraph_iff] at hψ ⊢
  refine ⟨(weakSobolevGraph D.Ω).add_mem (sobolevDataRestrict_mem_weak D.Ω_le hψ.1)
    (D.reflectedRestrict_mem_weak hψ.1), ?_⟩
  have h1 : Integrable (sobolevDataRestrict D.Ω_le ψ).1
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  have h2 : Integrable (D.reflectedRestrict ψ).1
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  calc (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        (sobolevDataRestrict D.Ω_le ψ + D.reflectedRestrict ψ).1 x)
      = ∫ x in (D.Ω : Set (SpatialCoordinates d)),
          ((sobolevDataRestrict D.Ω_le ψ).1 x + (D.reflectedRestrict ψ).1 x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (sobolevDataRestrict D.Ω_le ψ).1
          (D.reflectedRestrict ψ).1] with x hx
        exact hx
    _ = 0 := by
        rw [integral_add h1 h2, D.integral_restrict_add_reflectedRestrict, hψ.2]

end MeanZero
end EvenReflectionDomain
end SubdiffusiveProcess
end
