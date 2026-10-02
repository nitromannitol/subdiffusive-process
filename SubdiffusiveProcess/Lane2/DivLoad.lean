import SubdiffusiveProcess.Lane2.OddIteration

/-!
# Divergence-form loads survive the reflection

The load transported by one odd-extension step is
`L' ψ = L (ψ|_Ω) - L (R* (ψ|_{ρΩ}))`.  When `L` is of divergence form,
`L v = -∫_Ω g · ∇v`, so is `L'`: the field is the ODD reflection

`G = 1_Ω g - 1_{ρΩ} (sign ⊙ g ∘ ρ)`,

the signs being those of the reflected gradient.  This is what lets GMC's
`IsDivFormWeakSolutionOn` be read off the transported equation.
-/

open MeasureTheory Set TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- The odd reflection of a vector field across the reflection plane of `D`. -/
def oddReflectedField (g : SpatialCoordinates d → SpatialCoordinates d) :
    SpatialCoordinates d → SpatialCoordinates d :=
  fun x i =>
    (D.Ω : Set (SpatialCoordinates d)).indicator (fun y => g y i) x -
      (D.reflected : Set (SpatialCoordinates d)).indicator
        (fun y => coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} y) i) x

theorem oddReflectedField_of_mem_Ω (g : SpatialCoordinates d → SpatialCoordinates d)
    {x : SpatialCoordinates d} (hx : x ∈ (D.Ω : Set (SpatialCoordinates d)))
    (i : Fin d) : D.oddReflectedField g x i = g x i := by
  rw [oddReflectedField, Set.indicator_of_mem hx,
    Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), sub_zero]

theorem oddReflectedField_of_mem_reflected
    (g : SpatialCoordinates d → SpatialCoordinates d)
    {x : SpatialCoordinates d} (hx : x ∈ (D.reflected : Set (SpatialCoordinates d)))
    (i : Fin d) : D.oddReflectedField g x i =
      -(coordinateReflectionSign {D.i} i *
        g (coordinateReflection D.z {D.i} x) i) := by
  rw [oddReflectedField, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
    Set.indicator_of_mem hx, zero_sub]

/-- The `i`-th component of the reflected restriction, as a function. -/
theorem reflectedRestrict_snd_coeFn (ψ : SobolevData D.U) (i : Fin d) :
    (((D.reflectedRestrict ψ).2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))] fun x =>
        coordinateReflectionSign {D.i} i *
          ((domainLpRestrict D.reflected_le (ψ.2 i) : DomainL2 D.reflected) :
            SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) := by
  have hsmul := Lp.coeFn_smul (coordinateReflectionSign {D.i} i)
    (reflectionLp D.z {D.i} D.preimage_reflected (domainLpRestrict D.reflected_le (ψ.2 i)))
  have hrefl := reflectionLp_coeFn D.z {D.i} D.preimage_reflected
    (domainLpRestrict D.reflected_le (ψ.2 i))
  filter_upwards [hsmul, hrefl] with x hs hr
  change (coordinateReflectionSign {D.i} i •
    reflectionLp D.z {D.i} D.preimage_reflected
      (domainLpRestrict D.reflected_le (ψ.2 i))) x = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hr]
  rfl

end EvenReflectionDomain

/-- Integrability of the odd-reflected field against an `L²` gradient component,
on the lower half. -/
theorem lane2_oddReflectedField_integrableOn_Ω (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d) (i : Fin d)
    (hgi : MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    (ψ : SobolevData D.U) :
    IntegrableOn (fun x => D.oddReflectedField g x i * (ψ.2 i) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := by
  have hgΩ : MemLp (fun x => g x i) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hgi.mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  have hψΩ : MemLp ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    (Lp.memLp (ψ.2 i)).mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  refine (hgΩ.integrable_mul hψΩ).congr ?_
  filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
  simp only [Pi.mul_apply]
  rw [D.oddReflectedField_of_mem_Ω g hx i]

/-- Integrability of the odd-reflected field against an `L²` gradient component,
on the upper half. -/
theorem lane2_oddReflectedField_integrableOn_reflected (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d) (i : Fin d)
    (hgi : MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    (ψ : SobolevData D.U) :
    IntegrableOn (fun x => D.oddReflectedField g x i * (ψ.2 i) x)
      (D.reflected : Set (SpatialCoordinates d)) volume := by
  have hmpΩ : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hgΩ : MemLp (fun x => g x i) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hgi.mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  have hψR : MemLp ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    (Lp.memLp (ψ.2 i)).mono_measure (Measure.restrict_mono D.reflected_le le_rfl)
  have hgcompR : MemLp (fun x => g (coordinateReflection D.z {D.i} x) i) 2
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    hgΩ.comp_measurePreserving hmpΩ
  have hprod := hgcompR.integrable_mul hψR
  have hsm : Integrable (fun x => -(coordinateReflectionSign {D.i} i *
      (g (coordinateReflection D.z {D.i} x) i *
        ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) x)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    (hprod.const_mul (coordinateReflectionSign {D.i} i)).neg
  refine hsm.congr ?_
  filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
  rw [D.oddReflectedField_of_mem_reflected g hx i]
  ring

/-- Integrability of the odd-reflected field against an `L²` gradient component,
on the doubled domain. -/
theorem lane2_oddReflectedField_integrableOn (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d) (i : Fin d)
    (hgi : MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    (ψ : SobolevData D.U) :
    IntegrableOn (fun x => D.oddReflectedField g x i * (ψ.2 i) x)
      (D.U : Set (SpatialCoordinates d)) volume :=
  (integrableOn_congr_set_ae D.union_ae_eq).mp
    ((lane2_oddReflectedField_integrableOn_Ω D g i hgi ψ).union
      (lane2_oddReflectedField_integrableOn_reflected D g i hgi ψ))

/-- **The divergence-form load transports componentwise.** -/
theorem lane2_divLoad_component (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d) (i : Fin d)
    (hgi : MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    (ψ : SobolevData D.U) :
    (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x)
      - (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((D.reflectedRestrict ψ).2 i) x)
      = ∫ x in (D.U : Set (SpatialCoordinates d)),
        D.oddReflectedField g x i * (ψ.2 i) x := by
  have hψi : MemLp ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))) := Lp.memLp _
  have hmpΩ : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  -- the first integral drops the restriction
  have e1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), g x i * (ψ.2 i) x := by
    refine integral_congr_ae ?_
    filter_upwards [domainLpRestrict_coeFn D.Ω_le (ψ.2 i)] with x hx
    change g x i * (domainLpRestrict D.Ω_le (ψ.2 i)) x = _
    rw [hx]
  -- the second integral is a reflected integral over the upper half
  have e2 : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      g x i * ((D.reflectedRestrict ψ).2 i) x) =
      ∫ x in (D.reflected : Set (SpatialCoordinates d)),
        coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} x) i * (ψ.2 i) x := by
    have h1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((D.reflectedRestrict ψ).2 i) x) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)),
          g x i * (coordinateReflectionSign {D.i} i *
            ((domainLpRestrict D.reflected_le (ψ.2 i) : DomainL2 D.reflected) :
              SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)) := by
      refine integral_congr_ae ?_
      filter_upwards [D.reflectedRestrict_snd_coeFn ψ i] with x hx
      rw [hx]
    have h2 := hmpΩ.integral_comp
      (coordinateReflectionEquiv D.z {D.i}).toHomeomorph.measurableEmbedding
      (fun y => g y i * (coordinateReflectionSign {D.i} i *
        ((domainLpRestrict D.reflected_le (ψ.2 i) : DomainL2 D.reflected) :
          SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} y)))
    rw [h1, ← h2]
    refine integral_congr_ae ?_
    filter_upwards [domainLpRestrict_coeFn D.reflected_le (ψ.2 i)] with x hx
    rw [coordinateReflection_involutive D.z {D.i} x, hx]
    ring
  -- the right-hand side splits over the two halves
  have hGΩ : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      D.oddReflectedField g x i * (ψ.2 i) x) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), g x i * (ψ.2 i) x := by
    refine setIntegral_congr_fun D.Ω.isOpen.measurableSet (fun x hx => ?_)
    rw [D.oddReflectedField_of_mem_Ω g hx i]
  have hGR : (∫ x in (D.reflected : Set (SpatialCoordinates d)),
      D.oddReflectedField g x i * (ψ.2 i) x) =
      -∫ x in (D.reflected : Set (SpatialCoordinates d)),
        coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} x) i * (ψ.2 i) x := by
    rw [← integral_neg]
    refine setIntegral_congr_fun D.reflected.isOpen.measurableSet (fun x hx => ?_)
    rw [D.oddReflectedField_of_mem_reflected g hx i]
    ring
  -- integrability of the two pieces
  have hintΩ := lane2_oddReflectedField_integrableOn_Ω D g i hgi ψ
  have hintR := lane2_oddReflectedField_integrableOn_reflected D g i hgi ψ
  have hsplit : (∫ x in (D.U : Set (SpatialCoordinates d)),
      D.oddReflectedField g x i * (ψ.2 i) x) =
      (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        D.oddReflectedField g x i * (ψ.2 i) x) +
      (∫ x in (D.reflected : Set (SpatialCoordinates d)),
        D.oddReflectedField g x i * (ψ.2 i) x) := by
    rw [← setIntegral_union D.disjoint_Ω_reflected D.reflected.isOpen.measurableSet
      hintΩ hintR]
    exact (setIntegral_congr_set D.union_ae_eq).symm
  rw [e1, e2, hsplit, hGΩ, hGR]
  ring

/-! ## Bounded measurable fields are `L²` on every box -/

theorem lane2_isBounded_openBox (lo hi : SpatialCoordinates d) :
    Bornology.IsBounded (openBox lo hi : Set (SpatialCoordinates d)) := by
  have hball : Bornology.IsBounded
      (Metric.closedBall (α := SpatialCoordinates d)
        (fun j => (lo j + hi j) / 2) (∑ j : Fin d, |hi j - lo j|)) :=
    Metric.isBounded_closedBall
  refine hball.subset ?_
  intro x hx
  have hx' : x ∈ openBox lo hi := hx
  rw [mem_openBox_iff] at hx'
  rw [Metric.mem_closedBall, dist_pi_le_iff
    (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  intro j
  have hj := hx' j
  have hpos : 0 < hi j - lo j := by linarith [hj.1, hj.2]
  have hle : |x j - (lo j + hi j) / 2| ≤ |hi j - lo j| := by
    rw [abs_le, abs_of_pos hpos]
    constructor <;> linarith [hj.1, hj.2]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k : Fin d => |hi k - lo k|) (fun k _ => abs_nonneg _)
    (Finset.mem_univ j))
  simpa [Real.dist_eq] using hle

theorem lane2_memLp_of_bounded_measurable {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) {f : SpatialCoordinates d → ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict S)) {M : ℝ}
    (hbd : ∀ᵐ x ∂(volume.restrict S), ‖f x‖ ≤ M) :
    MemLp f 2 (volume.restrict S) := by
  have hfin : volume S ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hS.isCompact_closure.measure_lt_top)
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  exact (memLp_top_of_bound hmeas M hbd).mono_exponent le_top

/-! ## The divergence-form load of the restrict-minus-reflect combination -/

/-- **The combination identity.**  Pairing a field on the lower half against
`ψ|_Ω - R*(ψ|_{ρΩ})` is the same as pairing its odd reflection against `ψ` on
the doubled domain.  This is the load half of `lane2_divLoad_transport`, stated
without reference to a datum so that both reflection steps can use it. -/
theorem lane2_divLoad_combination (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d)
    (hg : ∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    (ψ : SobolevData D.U) :
    (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i *
        (((sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ).2 i :
          DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)
      = ∫ x in (D.U : Set (SpatialCoordinates d)),
        ∑ i : Fin d, D.oddReflectedField g x i *
          ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) x := by
  classical
  have hgΩ : ∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun i =>
    (hg i).mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  have hIA : ∀ i : Fin d, IntegrableOn
      (fun x => g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
    (hgΩ i).integrable_mul (Lp.memLp ((sobolevDataRestrict D.Ω_le ψ).2 i))
  have hIB : ∀ i : Fin d, IntegrableOn
      (fun x => g x i * ((D.reflectedRestrict ψ).2 i) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
    (hgΩ i).integrable_mul (Lp.memLp ((D.reflectedRestrict ψ).2 i))
  have hIC : ∀ i : Fin d, IntegrableOn
      (fun x => D.oddReflectedField g x i * (ψ.2 i) x)
      (D.U : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_oddReflectedField_integrableOn D g i (hg i) ψ
  have hsplit : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i *
        (((sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ).2 i :
          DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)
      = (∫ x in (D.Ω : Set (SpatialCoordinates d)),
          ∑ i : Fin d, g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x)
        - (∫ x in (D.Ω : Set (SpatialCoordinates d)),
          ∑ i : Fin d, g x i * ((D.reflectedRestrict ψ).2 i) x) := by
    rw [← integral_sub (integrable_finset_sum _ (fun i _ => hIA i))
      (integrable_finset_sum _ (fun i _ => hIB i))]
    refine integral_congr_ae ?_
    have hall : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
        ∀ i : Fin d,
          (((sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ).2 i :
            DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x
            = ((sobolevDataRestrict D.Ω_le ψ).2 i) x
              - ((D.reflectedRestrict ψ).2 i) x :=
      ae_all_iff.2 (fun i => by
        filter_upwards [Lp.coeFn_sub ((sobolevDataRestrict D.Ω_le ψ).2 i)
          ((D.reflectedRestrict ψ).2 i)] with x hx
        exact hx)
    filter_upwards [hall] with x hx
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hx i]; ring)
  rw [hsplit,
    integral_finset_sum _ (fun i _ => hIA i),
    integral_finset_sum _ (fun i _ => hIB i),
    integral_finset_sum _ (fun i _ => hIC i),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => lane2_divLoad_component D g i (hg i) ψ)

/-- **The pullback of a divergence-form load.**  Composing with the reflection
turns the field `g` on the upper half into `σ ⊙ g∘ρ` on the lower half. -/
theorem lane2_divLoad_pullback (D : EvenReflectionDomain d)
    (g : SpatialCoordinates d → SpatialCoordinates d)
    (hg : ∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))))
    (v : SobolevData D.Ω) :
    (∫ x in (D.reflected : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i *
        (((reflectionSobolevData D.z {D.i} D.preimage_Ω v).2 i :
          DomainL2 D.reflected) : SpatialCoordinates d → ℝ) x)
      = ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, (coordinateReflectionSign {D.i} i *
            g (coordinateReflection D.z {D.i} x) i) *
          ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x := by
  classical
  have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  have hgpull : ∀ i : Fin d, MemLp
      (fun x => g (coordinateReflection D.z {D.i} x) i) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun i =>
    (hg i).comp_measurePreserving hmp
  have hIL : ∀ i : Fin d, IntegrableOn
      (fun x => g x i *
        (((reflectionSobolevData D.z {D.i} D.preimage_Ω v).2 i :
          DomainL2 D.reflected) : SpatialCoordinates d → ℝ) x)
      (D.reflected : Set (SpatialCoordinates d)) volume := fun i =>
    (hg i).integrable_mul
      (Lp.memLp ((reflectionSobolevData D.z {D.i} D.preimage_Ω v).2 i))
  have hIR : ∀ i : Fin d, IntegrableOn
      (fun x => (coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} x) i) *
        ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := by
    intro i
    have h := ((hgpull i).integrable_mul (Lp.memLp (v.2 i))).const_mul
      (coordinateReflectionSign {D.i} i)
    refine h.congr (Filter.EventuallyEq.of_eq ?_)
    funext x
    simp only [Pi.mul_apply]
    ring
  rw [integral_finset_sum _ (fun i _ => hIL i),
    integral_finset_sum _ (fun i _ => hIR i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcomp : (∫ x in (D.reflected : Set (SpatialCoordinates d)),
      g x i *
        (((reflectionSobolevData D.z {D.i} D.preimage_Ω v).2 i :
          DomainL2 D.reflected) : SpatialCoordinates d → ℝ) x)
      = ∫ x in (D.reflected : Set (SpatialCoordinates d)),
        g x i * (coordinateReflectionSign {D.i} i *
          ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x)) := by
    refine integral_congr_ae ?_
    have hsmul := Lp.coeFn_smul (coordinateReflectionSign {D.i} i)
      (reflectionLp D.z {D.i} D.preimage_Ω (v.2 i))
    have hrefl := reflectionLp_coeFn D.z {D.i} D.preimage_Ω (v.2 i)
    filter_upwards [hsmul, hrefl] with x hs hr
    have hval : (((reflectionSobolevData D.z {D.i} D.preimage_Ω v).2 i :
        DomainL2 D.reflected) : SpatialCoordinates d → ℝ) x
        = coordinateReflectionSign {D.i} i *
          ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) := by
      show ((coordinateReflectionSign {D.i} i •
        reflectionLp D.z {D.i} D.preimage_Ω (v.2 i) :
          DomainL2 D.reflected) : SpatialCoordinates d → ℝ) x = _
      rw [hs, Pi.smul_apply, smul_eq_mul, hr]
      rfl
    rw [hval]
  rw [hcomp]
  have hcv := hmp.integral_comp
    (coordinateReflectionEquiv D.z {D.i}).toHomeomorph.measurableEmbedding
    (fun y => g y i * (coordinateReflectionSign {D.i} i *
      ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
        (coordinateReflection D.z {D.i} y)))
  rw [← hcv]
  refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
  funext x
  rw [coordinateReflection_involutive D.z {D.i} x]
  ring

/-! ## Divergence-form loads as a carried invariant -/

/-- `L` is the divergence-form load of the field `g` on `U`. -/
def lane2_IsDivLoad {U : Opens (SpatialCoordinates d)}
    (L : SobolevData U → ℝ) (g : SpatialCoordinates d → SpatialCoordinates d) :
    Prop :=
  ∀ ψ : SobolevData U, L ψ = -∫ x in (U : Set (SpatialCoordinates d)),
    ∑ i : Fin d, g x i *
      ((ψ.2 i : DomainL2 U) : SpatialCoordinates d → ℝ) x

/-- A globally bounded measurable field: the class the reflection iteration
keeps, because every box has finite measure and so such a field is `L²` on each
one. -/
structure lane2_BoundedField (g : SpatialCoordinates d → SpatialCoordinates d) :
    Prop where
  meas : ∀ i : Fin d, Measurable (fun x => g x i)
  bdd : ∃ M : ℝ, ∀ (x : SpatialCoordinates d) (i : Fin d), |g x i| ≤ M

theorem lane2_BoundedField.memLp {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) (lo hi : SpatialCoordinates d) (i : Fin d) :
    MemLp (fun x => g x i) 2
      (volume.restrict (openBox lo hi : Set (SpatialCoordinates d))) := by
  obtain ⟨M, hM⟩ := hg.bdd
  exact lane2_memLp_of_bounded_measurable (lane2_isBounded_openBox lo hi)
    (hg.meas i).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa using hM x i))

theorem lane2_BoundedField.memLp_of {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) {U : Opens (SpatialCoordinates d)}
    (hU : Bornology.IsBounded (U : Set (SpatialCoordinates d))) (i : Fin d) :
    MemLp (fun x => g x i) 2
      (volume.restrict (U : Set (SpatialCoordinates d))) := by
  obtain ⟨M, hM⟩ := hg.bdd
  exact lane2_memLp_of_bounded_measurable hU (hg.meas i).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa using hM x i))

/-- The odd reflection of a bounded measurable field is again one. -/
theorem lane2_boundedField_oddReflectedField (D : EvenReflectionDomain d)
    {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) :
    lane2_BoundedField (D.oddReflectedField g) := by
  obtain ⟨M, hM⟩ := hg.bdd
  refine ⟨fun i => ?_, ⟨2 * M + 2 * M, fun x i => ?_⟩⟩
  · refine Measurable.sub ?_ ?_
    · exact (hg.meas i).indicator D.Ω.isOpen.measurableSet
    · refine Measurable.indicator ?_ D.reflected.isOpen.measurableSet
      exact measurable_const.mul
        ((hg.meas i).comp (coordinateReflection_isometry D.z {D.i}).continuous.measurable)
  · have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x i)
    show |(D.Ω : Set (SpatialCoordinates d)).indicator (fun y => g y i) x -
      (D.reflected : Set (SpatialCoordinates d)).indicator
        (fun y => coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} y) i) x| ≤ 2 * M + 2 * M
    refine le_trans (abs_sub _ _) ?_
    have h1 : |(D.Ω : Set (SpatialCoordinates d)).indicator (fun y => g y i) x| ≤ M := by
      by_cases hx : x ∈ (D.Ω : Set (SpatialCoordinates d))
      · rw [Set.indicator_of_mem hx]; exact hM x i
      · rw [Set.indicator_of_notMem hx, abs_zero]; exact hM0
    have h2 : |(D.reflected : Set (SpatialCoordinates d)).indicator
        (fun y => coordinateReflectionSign {D.i} i *
          g (coordinateReflection D.z {D.i} y) i) x| ≤ M := by
      by_cases hx : x ∈ (D.reflected : Set (SpatialCoordinates d))
      · rw [Set.indicator_of_mem hx, abs_mul, coordinateReflectionSign]
        split_ifs <;> simp <;> exact hM _ i
      · rw [Set.indicator_of_notMem hx, abs_zero]; exact hM0
    linarith

/-- The signed pullback of a bounded measurable field is again one. -/
theorem lane2_boundedField_pullback (D : EvenReflectionDomain d)
    {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) :
    lane2_BoundedField (fun x i => coordinateReflectionSign {D.i} i *
      g (coordinateReflection D.z {D.i} x) i) := by
  obtain ⟨M, hM⟩ := hg.bdd
  refine ⟨fun i => measurable_const.mul
    ((hg.meas i).comp
      (coordinateReflection_isometry D.z {D.i}).continuous.measurable), ⟨M, ?_⟩⟩
  intro x i
  rw [abs_mul, coordinateReflectionSign]
  split_ifs <;> simp <;> exact hM _ i

theorem lane2_boundedField_neg {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) :
    lane2_BoundedField (fun x i => -(g x i)) := by
  obtain ⟨M, hM⟩ := hg.bdd
  exact ⟨fun i => (hg.meas i).neg, ⟨M, fun x i => by rw [abs_neg]; exact hM x i⟩⟩

/-- **The upward step on loads.** -/
theorem lane2_divLoad_up (D : EvenReflectionDomain d)
    {g : SpatialCoordinates d → SpatialCoordinates d} (hg : lane2_BoundedField g)
    (hUb : Bornology.IsBounded (D.U : Set (SpatialCoordinates d)))
    {L : SobolevData D.Ω → ℝ} (hL : lane2_IsDivLoad L g) :
    lane2_IsDivLoad (U := D.U)
      (fun ψ => L (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ))
      (D.oddReflectedField g) := by
  intro ψ
  simp only
  rw [hL]
  congr 1
  exact lane2_divLoad_combination D g (fun i => hg.memLp_of hUb i) ψ

/-- **The downward step on loads.**  The field is first pulled back with its
signs, then odd-reflected, then negated -- the negation coming from the choice
of sign that keeps the datum unchanged on the original half. -/
theorem lane2_divLoad_down (D : EvenReflectionDomain d)
    {g : SpatialCoordinates d → SpatialCoordinates d} (hg : lane2_BoundedField g)
    (hUb : Bornology.IsBounded (D.U : Set (SpatialCoordinates d)))
    {L : SobolevData D.reflected → ℝ} (hL : lane2_IsDivLoad L g) :
    lane2_IsDivLoad (U := D.U)
      (fun ψ => -((fun v : SobolevData D.Ω =>
          L (reflectionSobolevData D.z {D.i} D.preimage_Ω v))
        (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ)))
      (fun x i => -(D.oddReflectedField
        (fun y j => coordinateReflectionSign {D.i} j *
          g (coordinateReflection D.z {D.i} y) j) x i)) := by
  intro ψ
  have hRb : Bornology.IsBounded (D.reflected : Set (SpatialCoordinates d)) :=
    hUb.subset D.reflected_le
  have hM : lane2_IsDivLoad (U := D.Ω)
      (fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v))
      (fun y j => coordinateReflectionSign {D.i} j *
        g (coordinateReflection D.z {D.i} y) j) := by
    intro v
    simp only
    rw [hL]
    congr 1
    exact lane2_divLoad_pullback D g (fun i => hg.memLp_of hRb i) v
  have hup := lane2_divLoad_up D (lane2_boundedField_pullback D hg) hUb hM ψ
  simp only at hup ⊢
  rw [hup]
  have hneg : (∫ x in (D.U : Set (SpatialCoordinates d)),
      ∑ i : Fin d, (-(D.oddReflectedField
        (fun y j => coordinateReflectionSign {D.i} j *
          g (coordinateReflection D.z {D.i} y) j) x i)) *
        ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) x)
      = -∫ x in (D.U : Set (SpatialCoordinates d)),
        ∑ i : Fin d, D.oddReflectedField
          (fun y j => coordinateReflectionSign {D.i} j *
            g (coordinateReflection D.z {D.i} y) j) x i *
          ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) x := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
    funext x
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hneg]

end SubdiffusiveProcess
