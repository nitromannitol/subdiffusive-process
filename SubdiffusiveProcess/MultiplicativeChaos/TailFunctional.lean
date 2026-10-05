module

public import SubdiffusiveProcess.MultiplicativeChaos.LayerShift
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# The tail test functional

The event that the limiting chaos gives a cube no mass has to be recognised
inside the sigma-field of the layers beyond a given generation.  The limiting
measure itself is not a tail object -- it depends on every layer -- but the
quantity that decides whether it charges a cube is: the upper limit of the test
integrals of the SHIFTED cutoff densities.  Those depend only on the tail
block, and that is all the zero-one law needs.  No second limiting measure has
to be constructed.
-/

open Filter MeasureTheory
open scoped CompactlySupported ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- The test integral of the cutoff density of the layers beyond generation
`m`. -/
def tailTestMass (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m n : ℕ) (omega : BilateralField d) : ℝ :=
  ∫ x, g x * fineDensity M n (layerShift m omega) x

/-- Its upper limit, which always exists in `ℝ≥0∞`.  The cube is null for the
limiting chaos exactly when this vanishes for every test function under the
cube -- see `tailTestLimsup_eq_zero_iff`. -/
def tailTestLimsup (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m : ℕ) (omega : BilateralField d) : ℝ≥0∞ :=
  limsup (fun n => ENNReal.ofReal (tailTestMass M g m n omega)) atTop

section Measurability

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem stronglyMeasurable_fineDensity_uncurry
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) :
    StronglyMeasurable (fun q : BilateralField d × SpatialCoordinates d =>
      fineDensity M n q.1 q.2) := by
  unfold fineDensity finePotential
  fun_prop

/-- The test integral of the shifted density, read off the tail block alone. -/
def tailTestMassFill (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m n : ℕ)
    (y : (i : tailIndices m) → C(SpatialCoordinates d, ℝ)) : ℝ :=
  ∫ x, g x * fineDensity M n (layerFill m y) x

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem tailTestMass_eq_fill {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m n : ℕ) (omega : BilateralField d) :
    tailTestMass M g m n omega
      = tailTestMassFill M g m n ((tailIndices m).domRestrict omega) := by
  rw [tailTestMass, tailTestMassFill]
  have hfill : layerFill m ((tailIndices m).domRestrict omega) = layerShift m omega := by
    exact (layerFill_restrict m omega)
  rw [hfill]

/-- The test integral of a reindexed cutoff density is measurable in the
reindexed environment.  Stated for an abstract measurable reindexing so that
the shift is never unfolded during unification. -/
theorem measurable_integral_fineDensity_comp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (n : ℕ)
    {Y : Type*} [MeasurableSpace Y] (F : Y → BilateralField d)
    (hF : Measurable F) :
    Measurable (fun y => ∫ x, g x * fineDensity M n (F y) x) := by
  have hjoint : StronglyMeasurable
      (fun q : Y × SpatialCoordinates d => g q.2 * fineDensity M n (F q.1) q.2) := by
    refine StronglyMeasurable.mul ?_ ?_
    · exact (map_continuous g).stronglyMeasurable.comp_measurable measurable_snd
    · exact ((stronglyMeasurable_fineDensity_uncurry M n).measurable.comp
        ((hF.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  exact (hjoint.integral_prod_right').measurable

theorem measurable_tailTestMassFill (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m n : ℕ) :
    Measurable (tailTestMassFill M g m n) :=
  measurable_integral_fineDensity_comp M g n (layerFill m) (measurable_layerFill m)

/-- The upper limit is measurable for the sigma-field of the layers beyond
generation `m`: this is the tail-measurability the zero-one law consumes. -/
theorem measurable_tailTestLimsup_comap
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (g : C_c(SpatialCoordinates d, ℝ)) (m : ℕ) :
    Measurable[MeasurableSpace.comap ((tailIndices m).domRestrict)
        (inferInstance : MeasurableSpace ((i : tailIndices m) →
          C(SpatialCoordinates d, ℝ)))]
      (tailTestLimsup M g m) := by
  have hres : Measurable[MeasurableSpace.comap ((tailIndices m).domRestrict)
      (inferInstance : MeasurableSpace ((i : tailIndices m) →
        C(SpatialCoordinates d, ℝ)))]
      ((tailIndices m).domRestrict (π := fun _ => C(SpatialCoordinates d, ℝ))) :=
    Measurable.of_comap_le le_rfl
  have hstep : ∀ n : ℕ, Measurable[MeasurableSpace.comap ((tailIndices m).domRestrict)
      (inferInstance : MeasurableSpace ((i : tailIndices m) →
        C(SpatialCoordinates d, ℝ)))]
      (fun omega => ENNReal.ofReal (tailTestMass M g m n omega)) := by
    intro n
    have := ((measurable_tailTestMassFill M g m n).comp hres).ennreal_ofReal
    simpa only [Function.comp_def, ← tailTestMass_eq_fill] using this
  exact Measurable.limsup hstep

end Measurability

end SubdiffusiveProcess
