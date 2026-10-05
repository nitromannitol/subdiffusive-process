module

public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.Sobolev.ReflectionGraph
public import SubdiffusiveProcess.Sobolev.KilledGraph

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {V U : Opens (SpatialCoordinates d)}

theorem lane2_zeroExtensionLp_testL2 (hV : V ≤ U) (ψ : 𝓓(V, ℝ)) :
    zeroExtensionLp hV (testL2 ψ) = testL2 (extendTest hV ψ) := by
  apply Lp.ext
  have hVsub : (V : Set (SpatialCoordinates d)) ⊆ U := hV
  have hR := ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' V.isOpen.measurableSet).mp (testL2_coeFn ψ))
  filter_upwards [zeroExtensionLp_coeFn hV (testL2 ψ),
    testL2_coeFn (extendTest hV ψ), hR] with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx, h3 hx]
    rfl
  · rw [Set.indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.tsupport_subset h))).symm

theorem lane2_zeroExtensionLp_testPartialL2 (hV : V ≤ U) (ψ : 𝓓(V, ℝ)) (i : Fin d) :
    zeroExtensionLp hV (testPartialL2 ψ i) = testPartialL2 (extendTest hV ψ) i := by
  apply Lp.ext
  have hR := ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' V.isOpen.measurableSet).mp (testPartialL2_coeFn ψ i))
  filter_upwards [zeroExtensionLp_coeFn hV (testPartialL2 ψ i),
    testPartialL2_coeFn (extendTest hV ψ) i, hR] with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx, h3 hx]
    rfl
  · rw [Set.indicator_of_notMem hx]
    have hz : fderiv ℝ (ψ : SpatialCoordinates d → ℝ) x = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hx (ψ.tsupport_subset h))
    show (0 : ℝ) = fderiv ℝ (extendTest hV ψ : SpatialCoordinates d → ℝ) x (Pi.single i 1)
    change (0 : ℝ) = fderiv ℝ (ψ : SpatialCoordinates d → ℝ) x (Pi.single i 1)
    rw [hz]
    rfl

theorem lane2_zeroExtensionSobolevData_smooth (hV : V ≤ U) (ψ : 𝓓(V, ℝ)) :
    zeroExtensionSobolevData hV (smoothSobolevData ψ) =
      smoothSobolevData (extendTest hV ψ) := by
  apply Prod.ext
  · exact lane2_zeroExtensionLp_testL2 hV ψ
  · funext i
    exact lane2_zeroExtensionLp_testPartialL2 hV ψ i

theorem lane2_zeroExtensionSobolevData_smooth_mem_weak (hV : V ≤ U) (ψ : 𝓓(V, ℝ)) :
    zeroExtensionSobolevData hV (smoothSobolevData ψ) ∈ weakSobolevGraph U := by
  rw [lane2_zeroExtensionSobolevData_smooth]
  exact smoothSobolevData_mem _

theorem lane2_zeroExtensionLp_sub (hV : V ≤ U) (f g : DomainL2 V) :
    zeroExtensionLp hV (f - g) = zeroExtensionLp hV f - zeroExtensionLp hV g := by
  apply Lp.ext
  filter_upwards [zeroExtensionLp_coeFn hV (f - g), zeroExtensionLp_coeFn hV f,
    zeroExtensionLp_coeFn hV g,
    Lp.coeFn_sub (zeroExtensionLp hV f) (zeroExtensionLp hV g),
    ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' V.isOpen.measurableSet).mp (Lp.coeFn_sub f g))]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx, h5 hx]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, sub_zero]

theorem lane2_norm_zeroExtensionLp (hV : V ≤ U) (f : DomainL2 V) :
    ‖zeroExtensionLp hV f‖ = ‖f‖ := by
  have hVsub : (V : Set (SpatialCoordinates d)) ⊆ U := hV
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (zeroExtensionLp_coeFn hV f),
    eLpNorm_indicator_eq_eLpNorm_restrict V.isOpen.measurableSet,
    Measure.restrict_restrict V.isOpen.measurableSet,
    Set.inter_eq_left.mpr hVsub]

theorem lane2_continuous_zeroExtensionLp (hV : V ≤ U) :
    Continuous (fun f : DomainL2 V => zeroExtensionLp hV f) := by
  have hlip : LipschitzWith 1 (fun f : DomainL2 V => zeroExtensionLp hV f) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, ← lane2_zeroExtensionLp_sub,
      lane2_norm_zeroExtensionLp]
    simp
  exact hlip.continuous

theorem lane2_continuous_zeroExtensionSobolevData (hV : V ≤ U) :
    Continuous (zeroExtensionSobolevData hV) := by
  refine Continuous.prodMk ?_ ?_
  · exact (lane2_continuous_zeroExtensionLp hV).comp continuous_fst
  · exact continuous_pi fun j =>
      (lane2_continuous_zeroExtensionLp hV).comp ((continuous_apply j).comp continuous_snd)

/-- **Zero extension of a killed datum is weakly Sobolev.**  The zero-trace
hypothesis is exactly the paper's `v = u - φ ∈ H¹₀(q)`
(`eq:mfd-18`). -/
theorem lane2_zeroExtensionSobolevData_mem_weak_of_killed (hV : V ≤ U)
    {v : SobolevData V} (hv : v ∈ killedSobolevGraph V) :
    zeroExtensionSobolevData hV v ∈ weakSobolevGraph U := by
  have hm : Set.MapsTo (zeroExtensionSobolevData hV)
      (Set.range (smoothSobolevData (Ω := V)))
      (weakSobolevGraph U : Set (SobolevData U)) := by
    rintro w ⟨ψ, rfl⟩
    exact lane2_zeroExtensionSobolevData_smooth_mem_weak hV ψ
  apply hm.closure_left (lane2_continuous_zeroExtensionSobolevData hV)
    (isClosed_weakSobolevGraph (Ω := U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hv

/-- The odd extension across the reflection plane: `evenExtension` with the sign
flipped, as the paper's Dirichlet-subtraction step requires
(`eq:mfd-18`). -/
def EvenReflectionDomain.oddExtension (D : EvenReflectionDomain d)
    (u : SobolevData D.Ω) : SobolevData D.U :=
  zeroExtensionSobolevData D.Ω_le u -
    zeroExtensionSobolevData D.reflected_le (D.reflectedData u)

/-- **The odd extension of a killed datum is weakly Sobolev.**  Unlike the even
extension, this needs the zero trace: with the test `χ = φ - s·ψ` the vanishing
on the reflection plane holds for the tangential directions only. -/
theorem lane2_oddExtension_mem_weak (D : EvenReflectionDomain d)
    {u : SobolevData D.Ω} (hu : u ∈ killedSobolevGraph D.Ω) :
    D.oddExtension u ∈ weakSobolevGraph D.U := by
  have h1 := lane2_zeroExtensionSobolevData_mem_weak_of_killed D.Ω_le hu
  have h2 := lane2_zeroExtensionSobolevData_mem_weak_of_killed D.reflected_le
    (reflectionSobolevData_mem_killed D.z {D.i} D.preimage_Ω hu)
  exact Submodule.sub_mem _ h1 h2

namespace EvenReflectionDomain
variable (D : EvenReflectionDomain d)

/-- The odd extension has the original values on the lower half and the negated
reflected values on the upper half. -/
theorem lane2_oddExtension_fst_coeFn (u : SobolevData D.Ω) :
    ((D.oddExtension u).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))] fun x =>
        (D.Ω : Set (SpatialCoordinates d)).indicator u.1 x -
          (D.reflected : Set (SpatialCoordinates d)).indicator
            (u.1 ∘ coordinateReflection D.z {D.i}) x := by
  have hR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
      (reflectionLp_coeFn D.z {D.i} D.preimage_Ω u.1))
  filter_upwards [Lp.coeFn_sub (zeroExtensionLp D.Ω_le u.1)
    (zeroExtensionLp D.reflected_le (D.reflectedData u).1),
    zeroExtensionLp_coeFn D.Ω_le u.1,
    zeroExtensionLp_coeFn D.reflected_le (D.reflectedData u).1, hR] with x hsub h1 h2 hx
  change (zeroExtensionLp D.Ω_le u.1 -
    zeroExtensionLp D.reflected_le (D.reflectedData u).1) x = _
  rw [hsub, Pi.sub_apply, h1, h2]
  congr 1
  by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR]
    exact hx hxR
  · rw [Set.indicator_of_notMem hxR, Set.indicator_of_notMem hxR]

/-- The odd extension gradient has the original components on the lower half and
the negated signed reflected components on the upper half. -/
theorem lane2_oddExtension_snd_coeFn (u : SobolevData D.Ω) (j : Fin d) :
    ((D.oddExtension u).2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))] fun x =>
        (D.Ω : Set (SpatialCoordinates d)).indicator (u.2 j) x -
          (D.reflected : Set (SpatialCoordinates d)).indicator
            (fun y => coordinateReflectionSign {D.i} j *
              u.2 j (coordinateReflection D.z {D.i} y)) x := by
  have hR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
      (reflectionLp_coeFn D.z {D.i} D.preimage_Ω (u.2 j)))
  have hs := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
      (Lp.coeFn_smul (coordinateReflectionSign {D.i} j)
        (reflectionLp D.z {D.i} D.preimage_Ω (u.2 j))))
  filter_upwards [Lp.coeFn_sub (zeroExtensionLp D.Ω_le (u.2 j))
    (zeroExtensionLp D.reflected_le ((D.reflectedData u).2 j)),
    zeroExtensionLp_coeFn D.Ω_le (u.2 j),
    zeroExtensionLp_coeFn D.reflected_le ((D.reflectedData u).2 j), hR, hs]
    with x hsub h1 h2 hx hsx
  change (zeroExtensionLp D.Ω_le (u.2 j) -
    zeroExtensionLp D.reflected_le ((D.reflectedData u).2 j)) x = _
  rw [hsub, Pi.sub_apply, h1, h2]
  congr 1
  by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR]
    change (coordinateReflectionSign {D.i} j •
      reflectionLp D.z {D.i} D.preimage_Ω (u.2 j)) x = _
    rw [hsx hxR, Pi.smul_apply, smul_eq_mul, hx hxR]
    rfl
  · rw [Set.indicator_of_notMem hxR, Set.indicator_of_notMem hxR]

/-- **Energy identity for the odd extension.**  The coefficient is extended
EVENLY (`evenExtensionCoefficient`, unchanged); the datum is extended oddly, so
the reflected half enters with a minus sign. -/
theorem lane2_sobolevCoefficientForm_oddExtension (a : PositiveCoefficient D.Ω)
    (u : SobolevData D.Ω) (ψ : SobolevData D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.oddExtension u) ψ =
      sobolevCoefficientForm a u (sobolevDataRestrict D.Ω_le ψ) -
        sobolevCoefficientForm a u (D.reflectedRestrict ψ) := by
  rw [oddExtension, map_sub, sub_apply,
    sobolevCoefficientForm_zeroExtension D.Ω_le _ a (D.evenExtensionCoefficient_ae_Ω a),
    sobolevCoefficientForm_zeroExtension D.reflected_le _ (D.reflectedCoefficient a)
      (D.evenExtensionCoefficient_ae_reflected a)]
  congr 1
  have h := sobolevCoefficientForm_reflection D.z {D.i} D.preimage_Ω a u
    (D.reflectedRestrict ψ)
  rw [← h]
  congr 1
  exact (reflectionSobolevData_inverse D.z {D.i} D.preimage_reflected
    (sobolevDataRestrict D.reflected_le ψ)).symm

/-- **Forced weak equation transport across the reflection.**  If `u` solves the
forced equation with load `L` on the lower half, its odd extension solves the
equation for the evenly reflected coefficient with the ODDLY reflected load
`v ↦ L(v|_Ω) - L(R^*(v|_{RΩ}))`.  This is the paper's
"under `S` the forcing is `χ(S) S F(Sx)`" (`eq:mfd-18`)
in weak form. -/
theorem lane2_oddExtension_weak_equation (a : PositiveCoefficient D.Ω)
    {u : SobolevData D.Ω} (L : SobolevData D.Ω →L[ℝ] ℝ)
    (hL : ∀ v ∈ weakSobolevGraph D.Ω, sobolevCoefficientForm a u v = L v)
    {ψ : SobolevData D.U} (hψ : ψ ∈ weakSobolevGraph D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.oddExtension u) ψ =
      L (sobolevDataRestrict D.Ω_le ψ) - L (D.reflectedRestrict ψ) := by
  rw [lane2_sobolevCoefficientForm_oddExtension,
    hL _ (sobolevDataRestrict_mem_weak D.Ω_le hψ),
    hL _ (D.reflectedRestrict_mem_weak hψ)]

/-- The odd extension is continuous on Sobolev data. -/
theorem lane2_continuous_oddExtension : Continuous D.oddExtension := by
  refine Continuous.sub ?_ ?_
  · exact lane2_continuous_zeroExtensionSobolevData D.Ω_le
  · exact (lane2_continuous_zeroExtensionSobolevData D.reflected_le).comp
      (reflectionSobolevData D.z {D.i} D.preimage_Ω).continuous

/-- The odd extension of SMOOTH compactly supported data is again smooth
compactly supported data on the doubled domain: it is the difference of two
`smoothSobolevData` of tests on `U`, because `ψ` vanishes near the reflection
plane. -/
theorem lane2_oddExtension_smooth_mem_killed (ψ : 𝓓(D.Ω, ℝ)) :
    D.oddExtension (smoothSobolevData ψ) ∈ killedSobolevGraph D.U := by
  rw [EvenReflectionDomain.oddExtension]
  refine Submodule.sub_mem _ ?_ ?_
  · rw [lane2_zeroExtensionSobolevData_smooth]
    exact smoothSobolevData_mem_killed _
  · rw [EvenReflectionDomain.reflectedData, reflectionSobolevData_smooth,
      lane2_zeroExtensionSobolevData_smooth]
    exact smoothSobolevData_mem_killed _

/-- **The odd extension of a killed datum is KILLED on the doubled domain.**
This is what makes the multi-face composition an induction: the output of one
reflection is again an admissible input for the next.  The traces on the outer
faces of the doubled domain come from the traces of `u` on the corresponding
faces of `Ω` and its mirror, which vanish; the reflection plane is interior. -/
theorem lane2_oddExtension_mem_killed {u : SobolevData D.Ω}
    (hu : u ∈ killedSobolevGraph D.Ω) :
    D.oddExtension u ∈ killedSobolevGraph D.U := by
  have hm : Set.MapsTo D.oddExtension (Set.range (smoothSobolevData (Ω := D.Ω)))
      (killedSobolevGraph D.U : Set (SobolevData D.U)) := by
    rintro w ⟨ψ, rfl⟩
    exact lane2_oddExtension_smooth_mem_killed D ψ
  apply hm.closure_left (lane2_continuous_oddExtension D)
    (isClosed_killedSobolevGraph (Ω := D.U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hu

end EvenReflectionDomain

end SubdiffusiveProcess
