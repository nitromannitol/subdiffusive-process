module

public import SubdiffusiveProcess.Sobolev.EvenReflectionTest
public import SubdiffusiveProcess.Sobolev.ReflectionGraph

@[expose] public section

/-!
# The even extension is weakly Sobolev on the doubled domain

For an `EvenReflectionDomain` `D` with lower half `Ω`, upper half `RΩ` and
doubled domain `U`, the even extension of Sobolev data `(u, g)` on `Ω` is

  `ũ = 1_Ω u + 1_{RΩ} (u ∘ R)`,  `g̃_j = 1_Ω g_j + 1_{RΩ} s_j (g_j ∘ R)`,

with `s_i = -1` and `s_j = 1` for `j ≠ i`. In Lean this is the sum of the
zero extension of `(u, g)` and the zero extension of the reflected data
`reflectionSobolevData z {i}` on `RΩ`; the plane itself never enters.

Argument for the weak identity. For a test `φ` on `U` and a coordinate `j`,
the pairing against the zero extension of `(u, g)` is `∫_Ω φ g_j + ∫_Ω ∂_j φ u`
and the pairing against the zero extension of the reflected data is, after the
change of variables `x ↦ R x` on `RΩ`, `s_j ∫_Ω (φ ∘ R) g_j + ∫_Ω (∂_j φ ∘ R) u`.
Their sum is `∫_Ω χ g_j + ∫_Ω ∂_j χ u` for the test `χ = φ + s_j (φ ∘ R)` on `U`,
because `∂_j (φ ∘ R) = s_j (∂_j φ) ∘ R` and `s_j ^ 2 = 1`. For `j = i` the test
`χ = φ - φ ∘ R` vanishes on the plane; for `j ≠ i` no condition is needed. In
both cases the interface test lemma `EvenReflectionDomain.weakGradient_identity`
gives zero.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {V U Ω : Opens (SpatialCoordinates d)}

/-- Extension by zero from an open subdomain, as an actual Lp class. -/
def zeroExtensionLp (hV : V ≤ U) {p : ℝ≥0∞}
    (f : Lp ℝ p (volume.restrict (V : Set (SpatialCoordinates d)))) :
    Lp ℝ p (volume.restrict (U : Set (SpatialCoordinates d))) :=
  ((memLp_indicator_iff_restrict V.isOpen.measurableSet).mpr (by
    rw [Measure.restrict_restrict V.isOpen.measurableSet,
      Set.inter_eq_left.mpr (show (V : Set (SpatialCoordinates d)) ⊆ U from hV)]
    exact Lp.memLp f)).toLp ((V : Set (SpatialCoordinates d)).indicator f)

/-- The zero extension is the indicator of the subdomain times the original class. -/
theorem zeroExtensionLp_coeFn (hV : V ≤ U) {p : ℝ≥0∞}
    (f : Lp ℝ p (volume.restrict (V : Set (SpatialCoordinates d)))) :
    (zeroExtensionLp hV f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
        (V : Set (SpatialCoordinates d)).indicator f :=
  MemLp.coeFn_toLp _

/-- Pairing against the zero extension is the pairing on the subdomain. -/
theorem integral_mul_zeroExtensionLp (hV : V ≤ U) (h : SpatialCoordinates d → ℝ)
    (f : DomainL2 V) :
    (∫ x in (U : Set (SpatialCoordinates d)), h x * zeroExtensionLp hV f x) =
      ∫ x in (V : Set (SpatialCoordinates d)), h x * f x := by
  calc _ = ∫ x in (U : Set (SpatialCoordinates d)),
        (V : Set (SpatialCoordinates d)).indicator (fun x => h x * f x) x := by
        apply integral_congr_ae
        filter_upwards [zeroExtensionLp_coeFn hV f] with x hx
        rw [hx]
        by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
        · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem hxV]
        · rw [Set.indicator_of_notMem hxV, Set.indicator_of_notMem hxV, mul_zero]
    _ = ∫ x in (U : Set (SpatialCoordinates d)) ∩ V, h x * f x :=
        setIntegral_indicator V.isOpen.measurableSet
    _ = _ := by rw [Set.inter_eq_right.mpr (show (V : Set (SpatialCoordinates d)) ⊆ U from hV)]

/-- The integral of the zero extension is the subdomain integral. -/
theorem integral_zeroExtensionLp (hV : V ≤ U) (f : DomainL2 V) :
    (∫ x in (U : Set (SpatialCoordinates d)), zeroExtensionLp hV f x) =
      ∫ x in (V : Set (SpatialCoordinates d)), f x := by
  simpa only [one_mul] using integral_mul_zeroExtensionLp hV (fun _ => (1 : ℝ)) f

/-- The distributional test functional, written as explicit integrals. -/
theorem weakGradientTest_apply (φ : 𝓓(Ω, ℝ)) (i : Fin d) (v : SobolevData Ω) :
    weakGradientTest φ i v =
      (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * v.2 i x) +
        (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x (Pi.single i 1) * v.1 x) := by
  change inner ℝ (testL2 φ) (v.2 i) + inner ℝ (testPartialL2 φ i) v.1 = _
  rw [L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [testL2_coeFn φ] with x hx
    simp [hx, mul_comm]
  · apply integral_congr_ae
    filter_upwards [testPartialL2_coeFn φ i] with x hx
    simp [hx, mul_comm]

/-- Zero extension of function and gradient data from a subdomain. -/
def zeroExtensionSobolevData (hV : V ≤ U) (v : SobolevData V) : SobolevData U :=
  (zeroExtensionLp hV v.1, fun j => zeroExtensionLp hV (v.2 j))

/-- Testing the zero extension is testing on the subdomain (with a test not
compactly supported there). -/
theorem weakGradientTest_zeroExtension (hV : V ≤ U) (φ : 𝓓(U, ℝ)) (i : Fin d)
    (v : SobolevData V) :
    weakGradientTest φ i (zeroExtensionSobolevData hV v) =
      (∫ x in (V : Set (SpatialCoordinates d)), φ x * v.2 i x) +
        (∫ x in (V : Set (SpatialCoordinates d)), fderiv ℝ φ x (Pi.single i 1) * v.1 x) := by
  rw [weakGradientTest_apply]
  change (∫ x in (U : Set (SpatialCoordinates d)), φ x * zeroExtensionLp hV (v.2 i) x) +
    (∫ x in (U : Set (SpatialCoordinates d)),
      fderiv ℝ φ x (Pi.single i 1) * zeroExtensionLp hV v.1 x) = _
  rw [integral_mul_zeroExtensionLp, integral_mul_zeroExtensionLp]

/-- Pairing against a reflected class is the reflected pairing on the original domain. -/
theorem integral_mul_reflectionLp (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (h : SpatialCoordinates d → ℝ) (f : DomainL2 Ω) :
    (∫ x in (U : Set (SpatialCoordinates d)), h x * reflectionLp z I hU f x) =
      ∫ y in (Ω : Set (SpatialCoordinates d)), h (coordinateReflection z I y) * f y := by
  calc _ = ∫ x in (U : Set (SpatialCoordinates d)), h x * f (coordinateReflection z I x) := by
        apply integral_congr_ae
        filter_upwards [reflectionLp_coeFn z I hU f] with x hx
        rw [hx]
        rfl
    _ = ∫ x in (U : Set (SpatialCoordinates d)),
        (fun y => h (coordinateReflection z I y) * f y) (coordinateReflection z I x) := by
        congr 1
        funext x
        show h x * f (coordinateReflection z I x) =
          h (coordinateReflection z I (coordinateReflection z I x)) * f (coordinateReflection z I x)
        rw [coordinateReflection_involutive z I x]
    _ = _ := (coordinateReflection_domain_measurePreserving z I hU).integral_comp
        (coordinateReflectionEquiv z I).toHomeomorph.measurableEmbedding
        (fun y => h (coordinateReflection z I y) * f y)

namespace EvenReflectionDomain
variable (D : EvenReflectionDomain d)

/-- Sobolev data on the lower half pulled back to the upper half. -/
def reflectedData (u : SobolevData D.Ω) : SobolevData D.reflected :=
  reflectionSobolevData D.z {D.i} D.preimage_Ω u

/-- The even extension: the lower data plus the zero extension of the reflected data. -/
def evenExtension (u : SobolevData D.Ω) : SobolevData D.U :=
  zeroExtensionSobolevData D.Ω_le u + zeroExtensionSobolevData D.reflected_le (D.reflectedData u)

/-- The even extension has the original values on the lower half and the reflected
values on the upper half. -/
theorem evenExtension_fst_coeFn (u : SobolevData D.Ω) :
    ((D.evenExtension u).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))] fun x =>
        (D.Ω : Set (SpatialCoordinates d)).indicator u.1 x +
          (D.reflected : Set (SpatialCoordinates d)).indicator (u.1 ∘ coordinateReflection D.z {D.i}) x := by
  have hR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d))) ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
    (reflectionLp_coeFn D.z {D.i} D.preimage_Ω u.1))
  filter_upwards [Lp.coeFn_add (zeroExtensionLp D.Ω_le u.1)
    (zeroExtensionLp D.reflected_le (D.reflectedData u).1), zeroExtensionLp_coeFn D.Ω_le u.1,
    zeroExtensionLp_coeFn D.reflected_le (D.reflectedData u).1, hR] with x hadd h1 h2 hx
  change (zeroExtensionLp D.Ω_le u.1 + zeroExtensionLp D.reflected_le (D.reflectedData u).1) x = _
  rw [hadd, Pi.add_apply, h1, h2]
  congr 1
  by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR]
    exact hx hxR
  · rw [Set.indicator_of_notMem hxR, Set.indicator_of_notMem hxR]

/-- The even extension gradient has the original components on the lower half and the
signed reflected components on the upper half. -/
theorem evenExtension_snd_coeFn (u : SobolevData D.Ω) (j : Fin d) :
    ((D.evenExtension u).2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))] fun x =>
        (D.Ω : Set (SpatialCoordinates d)).indicator (u.2 j) x +
          (D.reflected : Set (SpatialCoordinates d)).indicator
            (fun y => coordinateReflectionSign {D.i} j * u.2 j (coordinateReflection D.z {D.i} y)) x := by
  have hR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d))) ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
    (reflectionLp_coeFn D.z {D.i} D.preimage_Ω (u.2 j)))
  have hs := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d))) ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
    (Lp.coeFn_smul (coordinateReflectionSign {D.i} j) (reflectionLp D.z {D.i} D.preimage_Ω (u.2 j))))
  filter_upwards [Lp.coeFn_add (zeroExtensionLp D.Ω_le (u.2 j))
    (zeroExtensionLp D.reflected_le ((D.reflectedData u).2 j)), zeroExtensionLp_coeFn D.Ω_le (u.2 j),
    zeroExtensionLp_coeFn D.reflected_le ((D.reflectedData u).2 j), hR, hs] with x hadd h1 h2 hx hsx
  change (zeroExtensionLp D.Ω_le (u.2 j) + zeroExtensionLp D.reflected_le ((D.reflectedData u).2 j)) x = _
  rw [hadd, Pi.add_apply, h1, h2]
  congr 1
  by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR]
    change (coordinateReflectionSign {D.i} j • reflectionLp D.z {D.i} D.preimage_Ω (u.2 j)) x = _
    rw [hsx hxR, Pi.smul_apply, smul_eq_mul, hx hxR]
    rfl
  · rw [Set.indicator_of_notMem hxR, Set.indicator_of_notMem hxR]

/-- Testing the zero-extended reflected data is the signed reflected pairing on the lower half. -/
theorem weakGradientTest_reflectedData (φ : 𝓓(D.U, ℝ)) (j : Fin d) (u : SobolevData D.Ω) :
    weakGradientTest φ j (zeroExtensionSobolevData D.reflected_le (D.reflectedData u)) =
      coordinateReflectionSign {D.i} j *
        (∫ x in (D.Ω : Set (SpatialCoordinates d)), φ (coordinateReflection D.z {D.i} x) * u.2 j x) +
      (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        fderiv ℝ φ (coordinateReflection D.z {D.i} x) (Pi.single j 1) * u.1 x) := by
  rw [weakGradientTest_zeroExtension]
  congr 1
  · calc (∫ x in (D.reflected : Set (SpatialCoordinates d)), φ x * (D.reflectedData u).2 j x)
        = ∫ x in (D.reflected : Set (SpatialCoordinates d)), coordinateReflectionSign {D.i} j *
            (φ x * reflectionLp D.z {D.i} D.preimage_Ω (u.2 j) x) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_smul (coordinateReflectionSign {D.i} j)
            (reflectionLp D.z {D.i} D.preimage_Ω (u.2 j))] with x hx
          change φ x * (coordinateReflectionSign {D.i} j •
            reflectionLp D.z {D.i} D.preimage_Ω (u.2 j)) x = _
          rw [hx, Pi.smul_apply, smul_eq_mul]
          ring
      _ = _ := by rw [integral_const_mul, integral_mul_reflectionLp]
  · exact integral_mul_reflectionLp D.z {D.i} D.preimage_Ω _ u.1

/-- **Even extension is weakly Sobolev.** The even extension of a weak-gradient pair on
the lower half is a weak-gradient pair on the doubled domain. -/
theorem evenExtension_mem_weak {u : SobolevData D.Ω} (hu : u ∈ weakSobolevGraph D.Ω) :
    D.evenExtension u ∈ weakSobolevGraph D.U := by
  simp only [weakSobolevGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe]
  intro φ j
  rw [evenExtension, map_add, weakGradientTest_zeroExtension, weakGradientTest_reflectedData]
  set s := coordinateReflectionSign {D.i} j with hs
  set ψ : 𝓓(D.U, ℝ) := reflectionTest D.z {D.i} D.symm φ with hψ
  set χ : 𝓓(D.U, ℝ) := φ + s • ψ with hχ
  have hχx : ∀ x, χ x = φ x + s * φ (coordinateReflection D.z {D.i} x) := fun x => rfl
  have hdχ : ∀ x, fderiv ℝ χ x (Pi.single j 1) = fderiv ℝ φ x (Pi.single j 1) +
      fderiv ℝ φ (coordinateReflection D.z {D.i} x) (Pi.single j 1) := by
    intro x
    have hψd : DifferentiableAt ℝ (s • (ψ : SpatialCoordinates d → ℝ)) x :=
      (ψ.contDiff.differentiable (by simp) x).const_smul s
    change fderiv ℝ ((φ : SpatialCoordinates d → ℝ) + s • (ψ : SpatialCoordinates d → ℝ)) x
      (Pi.single j 1) = _
    rw [fderiv_add (φ.contDiff.differentiable (by simp) x) hψd,
      fderiv_const_smul (ψ.contDiff.differentiable (by simp) x), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hψ, reflectionTest_fderiv, ← mul_assoc,
      ← pow_two, hs, coordinateReflectionSign_sq, one_mul]
  have hvan : j = D.i → ∀ x, x D.i = D.z D.i → χ x = 0 := by
    intro hj x hx
    rw [hχx, coordinateReflection_single_eq_self D.z D.i hx, hs, hj, coordinateReflectionSign]
    simp
  have hA := D.weakGradient_identity hu χ j hvan
  have e1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * u.2 j x) =
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), φ x * u.2 j x) +
        s * ∫ x in (D.Ω : Set (SpatialCoordinates d)), φ (coordinateReflection D.z {D.i} x) * u.2 j x := by
    have h1 : Integrable (fun x => φ x * u.2 j x)
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      integrable_mul_domainL2 φ.contDiff.continuous φ.hasCompactSupport _
    have h2 : Integrable (fun x => s * (φ (coordinateReflection D.z {D.i} x) * u.2 j x))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      (integrable_mul_domainL2 ψ.contDiff.continuous ψ.hasCompactSupport (u.2 j)).const_mul s
    rw [← integral_const_mul, ← integral_add h1 h2]
    congr 1
    funext x
    rw [hχx]
    ring
  have e2 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), fderiv ℝ χ x (Pi.single j 1) * u.1 x) =
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x (Pi.single j 1) * u.1 x) +
        ∫ x in (D.Ω : Set (SpatialCoordinates d)),
          fderiv ℝ φ (coordinateReflection D.z {D.i} x) (Pi.single j 1) * u.1 x := by
    have h1 : Integrable (fun x => fderiv ℝ φ x (Pi.single j 1) * u.1 x)
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      integrable_mul_domainL2 (continuous_fderiv_single φ.contDiff j)
        (φ.hasCompactSupport.fderiv_apply ℝ _) _
    have h2 : Integrable (fun x => fderiv ℝ φ (coordinateReflection D.z {D.i} x) (Pi.single j 1) * u.1 x)
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      integrable_mul_domainL2 ((continuous_fderiv_single φ.contDiff j).comp
        (coordinateReflection_isometry D.z {D.i}).continuous)
        ((φ.hasCompactSupport.fderiv_apply ℝ (Pi.single j 1)).comp_homeomorph
          (coordinateReflectionEquiv D.z {D.i}).toHomeomorph) _
    rw [← integral_add h1 h2]
    congr 1
    funext x
    rw [hdχ]
    ring
  rw [e1, e2] at hA
  linarith

end EvenReflectionDomain
end SubdiffusiveProcess
end
