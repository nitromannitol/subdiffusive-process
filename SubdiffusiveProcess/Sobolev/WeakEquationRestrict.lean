module

public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Variational.WeightedL2

@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} {V U : Opens (SpatialCoordinates d)}

/-- Symmetric counterpart of `sobolevCoefficientForm_zeroExtension`: testing data on the
large domain against a zero-extended test function only sees the subdomain restriction of
the data and the coefficient's values there. -/
theorem sobolevCoefficientForm_zeroExtension_test (hV : V ≤ U) (b : PositiveCoefficient U)
    (a : PositiveCoefficient V)
    (hab : (b.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] a.val)
    (u : SobolevData U) (psi : SobolevData V) :
    sobolevCoefficientForm b u (zeroExtensionSobolevData hV psi) =
      sobolevCoefficientForm a (sobolevDataRestrict hV u) psi := by
  rw [sobolevCoefficientForm_symm b u, sobolevCoefficientForm_zeroExtension hV b a hab psi u,
    sobolevCoefficientForm_symm a psi]

/-- A weak `PositiveCoefficient`-equation on a domain `U` restricts to the same equation
(same source `F`, restricted coefficient) on any open subdomain `V ≤ U`. Needed to localize
a solution given on a "Parent" cube down to a smaller cube `Q ⊆ Parent` without redoing the
disorder/RG argument: only the coefficient's pointwise agreement on `V` and the zero-extension
API are used, no new integral estimate. -/
theorem weakEquation_restrict (hV : V ≤ U) (aU : PositiveCoefficient U) (aV : PositiveCoefficient V)
    (hab : (aU.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] aV.val)
    (u : SobolevData U) (F : SpatialCoordinates d → ℝ)
    (hu : ∀ psi : killedSobolevGraph U,
      sobolevCoefficientForm aU u (psi : SobolevData U) =
        ∫ x in (U : Set (SpatialCoordinates d)), F x * (psi : SobolevData U).1 x) :
    ∀ psi : killedSobolevGraph V,
      sobolevCoefficientForm aV (sobolevDataRestrict hV u) (psi : SobolevData V) =
        ∫ x in (V : Set (SpatialCoordinates d)), F x * (psi : SobolevData V).1 x := by
  intro psi
  have hext : zeroExtensionSobolevData hV (psi : SobolevData V) ∈ killedSobolevGraph U :=
    lane2_zeroExtensionSobolevData_mem_killed hV psi.property
  have hrun := hu ⟨zeroExtensionSobolevData hV (psi : SobolevData V), hext⟩
  rw [sobolevCoefficientForm_zeroExtension_test hV aU aV hab u psi] at hrun
  have hfst : (zeroExtensionSobolevData hV (psi : SobolevData V)).1 =
      zeroExtensionLp hV (psi : SobolevData V).1 := rfl
  rw [hfst, integral_mul_zeroExtensionLp hV F (psi : SobolevData V).1] at hrun
  exact hrun

/-- Companion domain-monotonicity fact: restricting the domain of a `PositiveCoefficient`
energy to an open subdomain (with the same coefficient there) can only decrease it. Used to
weaken a Hölder estimate stated in terms of the smaller domain's energy into one valid for
the larger domain's (larger) energy. -/
theorem sobolevCoefficientForm_restrict_le (hV : V ≤ U) (aU : PositiveCoefficient U)
    (aV : PositiveCoefficient V)
    (hab : (aU.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] aV.val)
    (u : SobolevData U) :
    sobolevCoefficientForm aV (sobolevDataRestrict hV u) (sobolevDataRestrict hV u) ≤
      sobolevCoefficientForm aU u u := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  apply Finset.sum_le_sum
  intro i _
  have hcong :
      (∫ x in (V : Set (SpatialCoordinates d)),
        aV.val x * ((sobolevDataRestrict hV u).2 i x * (sobolevDataRestrict hV u).2 i x)) =
      ∫ x in (V : Set (SpatialCoordinates d)), aU.val x * (u.2 i x * u.2 i x) := by
    apply integral_congr_ae
    filter_upwards [hab, domainLpRestrict_coeFn hV (u.2 i)] with x hx1 hx2
    change aV.val x * (domainLpRestrict hV (u.2 i) x * domainLpRestrict hV (u.2 i) x) =
      aU.val x * (u.2 i x * u.2 i x)
    rw [hx2, ← hx1]
  rw [hcong]
  obtain ⟨c, hc, hac⟩ := aU.property
  have hnonneg : 0 ≤ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      fun x => aU.val x * (u.2 i x * u.2 i x) := by
    filter_upwards [hac] with x hx
    have h0 : (0:ℝ) ≤ aU.val x := le_trans hc.le hx
    exact mul_nonneg h0 (mul_self_nonneg _)
  have hintU : Integrable (fun x => aU.val x * (u.2 i x * u.2 i x))
      (volume.restrict (U : Set (SpatialCoordinates d))) := by
    have hraw := integrable_weighted_inner (μ := volume.restrict (U : Set (SpatialCoordinates d)))
      aU.val (u.2 i) (u.2 i)
    simpa [RCLike.inner_apply, sq] using hraw
  exact setIntegral_mono_set hintU hnonneg (Filter.Eventually.of_forall hV)

end SubdiffusiveProcess
