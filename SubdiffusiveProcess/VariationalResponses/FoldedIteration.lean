module

public import SubdiffusiveProcess.VariationalResponses.OddIteration
public import SubdiffusiveProcess.VariationalResponses.FoldedCoefficient

@[expose] public section

/-!
# The iterated even extension is a coordinate fold

The reflection iteration of `SubdiffusiveProcess.VariationalResponses.OddIteration` doubles a
box across the faces that carry the boundary point `x₀`.  Every reflection plane
then passes through `x₀`, so the composite of the even coefficient extensions is
literally `a ∘ coordinateFold x₀ I P`, where `I` is the set of active
coordinates and `P` selects the ones whose face is the UPPER face of the box
(those are folded downward).  That is the form GMC's small-contrast Schauder
estimate consumes: a genuine continuous function with contrast close to `1` on a
small ball.

This file supplies the general-`P` fold calculus, the folded coefficient for a
general orientation, and the two identities saying that one even extension step
inserts one coordinate into the fold.
-/

open MeasureTheory Set TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-! ## The fold calculus for a general orientation -/

theorem lane2_fold_apply_of_notMem_I {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    {j : Fin d} (hj : j ∉ I) (y : SpatialCoordinates d) :
    coordinateFold z I P y j = y j := by
  simp [coordinateFold, hj]

theorem lane2_fold_apply_of_mem_P_of_le {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {j : Fin d} (hjI : j ∈ I) (hjP : j ∈ P)
    {y : SpatialCoordinates d} (h : y j ≤ z j) :
    coordinateFold z I P y j = y j := by
  simp only [coordinateFold, ite_eq_left hjI, coordinateReflectionSign, ite_eq_left hjP,
    abs_of_nonpos (sub_nonpos.mpr h)]
  ring

theorem lane2_fold_apply_of_mem_P_of_ge {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {j : Fin d} (hjI : j ∈ I) (hjP : j ∈ P)
    {y : SpatialCoordinates d} (h : z j ≤ y j) :
    coordinateFold z I P y j = 2 * z j - y j := by
  simp only [coordinateFold, ite_eq_left hjI, coordinateReflectionSign, ite_eq_left hjP,
    abs_of_nonneg (sub_nonneg.mpr h)]
  ring

theorem lane2_fold_apply_of_notMem_P_of_ge {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {j : Fin d} (hjI : j ∈ I) (hjP : j ∉ P)
    {y : SpatialCoordinates d} (h : z j ≤ y j) :
    coordinateFold z I P y j = y j := by
  simp only [coordinateFold, ite_eq_left hjI, coordinateReflectionSign, ite_eq_right hjP,
    abs_of_nonneg (sub_nonneg.mpr h)]
  ring

theorem lane2_fold_apply_of_notMem_P_of_le {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {j : Fin d} (hjI : j ∈ I) (hjP : j ∉ P)
    {y : SpatialCoordinates d} (h : y j ≤ z j) :
    coordinateFold z I P y j = 2 * z j - y j := by
  simp only [coordinateFold, ite_eq_left hjI, coordinateReflectionSign, ite_eq_right hjP,
    abs_of_nonpos (sub_nonpos.mpr h)]
  ring

/-- A point on every active plane is fixed by the fold, whatever the
orientation. -/
theorem lane2_fold_fix {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    {y : SpatialCoordinates d} (h : ∀ j ∈ I, y j = z j) :
    coordinateFold z I P y = y := by
  funext j
  by_cases hj : j ∈ I
  · simp only [coordinateFold, ite_eq_left hj, h j hj, sub_self, abs_zero, mul_zero,
      add_zero]
  · exact lane2_fold_apply_of_notMem_I hj y

/-! ## The folded coefficient for a general orientation -/

/-- **Adapter A for a general orientation.**  `P` lists the active coordinates
whose reflection plane is the upper face of the box, which the fold sends
downward; the remaining active coordinates are folded upward. -/
def foldedCoefficientP (a : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d)
    (I P : Finset (Fin d)) : SpatialCoordinates d → ℝ :=
  fun y => a (coordinateFold z I P y)

theorem continuous_foldedCoefficientP {a : SpatialCoordinates d → ℝ}
    (ha : Continuous a) (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    Continuous (foldedCoefficientP a z I P) :=
  ha.comp (coordinateFold_continuous z I P)

theorem foldedCoefficientP_fix {a : SpatialCoordinates d → ℝ}
    {z : SpatialCoordinates d} {I P : Finset (Fin d)} :
    foldedCoefficientP a z I P z = a z := by
  rw [foldedCoefficientP, lane2_fold_fix (fun _ _ => rfl)]

/-- **Small contrast on a small ball, general orientation.**  The paper's "the
coefficient has small contrast on a sufficiently small ball"
(`eq:mfd-18`) at a fixed cutoff. -/
theorem exists_ball_foldedCoefficientP_smallContrast
    {a : SpatialCoordinates d → ℝ} (ha : Continuous a)
    (z : SpatialCoordinates d) (I P : Finset (Fin d)) (hz : 0 < a z)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ y ∈ Metric.ball z rho,
        |(a z)⁻¹ * foldedCoefficientP a z I P y - 1| ≤ delta := by
  have hcont : Continuous (fun y => (a z)⁻¹ * foldedCoefficientP a z I P y - 1) :=
    (continuous_const.mul (continuous_foldedCoefficientP ha z I P)).sub continuous_const
  have hval : (a z)⁻¹ * foldedCoefficientP a z I P z - 1 = 0 := by
    rw [foldedCoefficientP_fix, inv_mul_cancel₀ (ne_of_gt hz), sub_self]
  have hev : ∀ᶠ y in nhds z,
      |(a z)⁻¹ * foldedCoefficientP a z I P y - 1| ≤ delta := by
    have h0 : Filter.Tendsto (fun y => (a z)⁻¹ * foldedCoefficientP a z I P y - 1)
        (nhds z) (nhds 0) := by
      have h1 := hcont.continuousAt (x := z)
      rw [ContinuousAt, hval] at h1
      exact h1
    have := h0 (Metric.closedBall_mem_nhds (0 : ℝ) hdelta)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq, abs_sub_comm] using hy
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨rho, hrho, hball⟩

/-! ## Inserting one coordinate into the fold -/

theorem lane2_fold_apply_insert_both_of_ne {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i j : Fin d} (hj : j ≠ i) (y : SpatialCoordinates d) :
    coordinateFold z (insert i I) (insert i P) y j = coordinateFold z I P y j := by
  simp [coordinateFold, coordinateReflectionSign, Finset.mem_insert, hj]

theorem lane2_fold_apply_insert_I_of_ne {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i j : Fin d} (hj : j ≠ i) (y : SpatialCoordinates d) :
    coordinateFold z (insert i I) P y j = coordinateFold z I P y j := by
  simp [coordinateFold, Finset.mem_insert, hj]

/-- Below the new plane, inserting the coordinate into both `I` and `P` changes
nothing: the fold is the identity there. -/
theorem lane2_fold_insert_both_of_le {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i : Fin d} (hiI : i ∉ I) {y : SpatialCoordinates d}
    (h : y i ≤ z i) :
    coordinateFold z (insert i I) (insert i P) y = coordinateFold z I P y := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [lane2_fold_apply_of_mem_P_of_le (Finset.mem_insert_self j I)
        (Finset.mem_insert_self j P) h,
      lane2_fold_apply_of_notMem_I hiI]
  · exact lane2_fold_apply_insert_both_of_ne hj y

/-- Above the new plane, inserting the coordinate into both `I` and `P` composes
the old fold with the reflection in that coordinate. -/
theorem lane2_fold_insert_both_of_ge {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i : Fin d} (hiI : i ∉ I) {y : SpatialCoordinates d}
    (h : z i ≤ y i) :
    coordinateFold z (insert i I) (insert i P) y =
      coordinateFold z I P (coordinateReflection z {i} y) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [lane2_fold_apply_of_mem_P_of_ge (Finset.mem_insert_self j I)
        (Finset.mem_insert_self j P) h,
      lane2_fold_apply_of_notMem_I hiI, coordinateReflection_single_apply_self]
  · rw [lane2_fold_apply_insert_both_of_ne hj y]
    simp only [coordinateFold]
    by_cases hjI : j ∈ I
    · rw [ite_eq_left hjI, ite_eq_left hjI, coordinateReflection_single_apply_of_ne _ hj]
    · rw [ite_eq_right hjI, ite_eq_right hjI, coordinateReflection_single_apply_of_ne _ hj]

/-- Above the new plane, inserting the coordinate into `I` only changes nothing:
the upward fold is the identity there. -/
theorem lane2_fold_insert_I_of_ge {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i : Fin d} (hiI : i ∉ I) (hiP : i ∉ P)
    {y : SpatialCoordinates d} (h : z i ≤ y i) :
    coordinateFold z (insert i I) P y = coordinateFold z I P y := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [lane2_fold_apply_of_notMem_P_of_ge (Finset.mem_insert_self j I) hiP h,
      lane2_fold_apply_of_notMem_I hiI]
  · exact lane2_fold_apply_insert_I_of_ne hj y

/-- Below the new plane, inserting the coordinate into `I` only composes the old
fold with the reflection in that coordinate. -/
theorem lane2_fold_insert_I_of_le {z : SpatialCoordinates d}
    {I P : Finset (Fin d)} {i : Fin d} (hiI : i ∉ I) (hiP : i ∉ P)
    {y : SpatialCoordinates d} (h : y i ≤ z i) :
    coordinateFold z (insert i I) P y =
      coordinateFold z I P (coordinateReflection z {i} y) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [lane2_fold_apply_of_notMem_P_of_le (Finset.mem_insert_self j I) hiP h,
      lane2_fold_apply_of_notMem_I hiI, coordinateReflection_single_apply_self]
  · rw [lane2_fold_apply_insert_I_of_ne hj y]
    simp only [coordinateFold]
    by_cases hjI : j ∈ I
    · rw [ite_eq_left hjI, ite_eq_left hjI, coordinateReflection_single_apply_of_ne _ hj]
    · rw [ite_eq_right hjI, ite_eq_right hjI, coordinateReflection_single_apply_of_ne _ hj]

/-! ## One even extension step inserts one coordinate into the fold -/

open SubdiffusiveProcess.EvenReflectionDomain in
/-- **The upward step, on coefficients.**  If the coefficient on the lower half
is the fold of `a` over `(I, P)` and the reflection plane of `D` is the plane
`{x_{D.i} = z_{D.i}}`, then its even extension to the doubled domain is the fold
over `(insert D.i I, insert D.i P)`: the new coordinate is folded DOWNWARD,
because the lower half lies below the new plane. -/
theorem lane2_evenExtensionCoefficient_fold_up (D : EvenReflectionDomain d)
    (a0 : PositiveCoefficient D.Ω)
    {a : SpatialCoordinates d → ℝ} {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    (hiI : D.i ∉ I) (hz : z D.i = D.z D.i)
    (hfold : (a0.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        foldedCoefficientP a z I P) :
    ((D.evenExtensionCoefficient a0).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
        foldedCoefficientP a z (insert D.i I) (insert D.i P) := by
  have hΩ : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
      ((D.evenExtensionCoefficient a0).val : SpatialCoordinates d → ℝ) x =
        foldedCoefficientP a z (insert D.i I) (insert D.i P) x := by
    filter_upwards [D.evenExtensionCoefficient_ae_Ω a0, hfold,
      ae_restrict_mem D.Ω.isOpen.measurableSet] with x h1 h2 hx
    rw [h1, h2]
    simp only [foldedCoefficientP]
    rw [lane2_fold_insert_both_of_le hiI
      (le_of_lt (hz ▸ ((D.mem_iff x).mp hx).2))]
  have hR : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
      ((D.evenExtensionCoefficient a0).val : SpatialCoordinates d → ℝ) x =
        foldedCoefficientP a z (insert D.i I) (insert D.i P) x := by
    have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    filter_upwards [D.evenExtensionCoefficient_ae_reflected a0,
      reflectionCoefficient_coeFn D.z {D.i} D.preimage_Ω a0,
      hmp.quasiMeasurePreserving.ae hfold,
      ae_restrict_mem D.reflected.isOpen.measurableSet] with x h1 h2 h3 hx
    have hrc : D.reflectedCoefficient a0 =
        reflectionCoefficient D.z {D.i} D.preimage_Ω a0 := rfl
    rw [h1, hrc]
    simp only [Function.comp_apply] at h2 h3 ⊢
    rw [h2, h3]
    simp only [foldedCoefficientP]
    rw [lane2_fold_insert_both_of_ge hiI
      (le_of_lt (hz ▸ ((D.mem_reflected_iff x).mp hx).2)),
      coordinateReflection_single_congr z D.z D.i hz]
  filter_upwards [
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hΩ),
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hR),
    D.ae_mem_or_mem] with x h1 h2 hmem
  rcases hmem with hx | hx
  · exact h1 hx
  · exact h2 hx

/-- **The downward step, on coefficients.**  Here the datum's box is the UPPER
half `D.reflected`, so the new coordinate is folded UPWARD: it enters `I` but
not `P`. -/
theorem lane2_evenExtensionCoefficient_fold_down (D : EvenReflectionDomain d)
    (b : PositiveCoefficient D.reflected)
    {a : SpatialCoordinates d → ℝ} {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    (hiI : D.i ∉ I) (hiP : D.i ∉ P) (hz : z D.i = D.z D.i)
    (hfold : (b.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.reflected : Set (SpatialCoordinates d))]
        foldedCoefficientP a z I P) :
    ((D.evenExtensionCoefficient
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b)).val :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
        foldedCoefficientP a z (insert D.i I) P := by
  have hR : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
      ((D.evenExtensionCoefficient
          (reflectionCoefficient D.z {D.i} D.preimage_reflected b)).val :
          SpatialCoordinates d → ℝ) x =
        foldedCoefficientP a z (insert D.i I) P x := by
    filter_upwards [(D.evenExtensionCoefficient_ae_reflected
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b)).trans
        (D.lane2_reflectedCoefficient_reflection_ae b), hfold,
      ae_restrict_mem D.reflected.isOpen.measurableSet] with x h1 h2 hx
    rw [h1, h2]
    simp only [foldedCoefficientP]
    rw [lane2_fold_insert_I_of_ge hiI hiP
      (le_of_lt (hz ▸ ((D.mem_reflected_iff x).mp hx).2))]
  have hΩ : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
      ((D.evenExtensionCoefficient
          (reflectionCoefficient D.z {D.i} D.preimage_reflected b)).val :
          SpatialCoordinates d → ℝ) x =
        foldedCoefficientP a z (insert D.i I) P x := by
    have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
        (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    filter_upwards [D.evenExtensionCoefficient_ae_Ω
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b),
      reflectionCoefficient_coeFn D.z {D.i} D.preimage_reflected b,
      hmp.quasiMeasurePreserving.ae hfold,
      ae_restrict_mem D.Ω.isOpen.measurableSet] with x h1 h2 h3 hx
    rw [h1]
    simp only [Function.comp_apply] at h2 h3 ⊢
    rw [h2, h3]
    simp only [foldedCoefficientP]
    rw [lane2_fold_insert_I_of_le hiI hiP
      (le_of_lt (hz ▸ ((D.mem_iff x).mp hx).2)),
      coordinateReflection_single_congr z D.z D.i hz]
  filter_upwards [
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hΩ),
    ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hR),
    D.ae_mem_or_mem] with x h1 h2 hmem
  rcases hmem with hx | hx
  · exact h1 hx
  · exact h2 hx

end SubdiffusiveProcess
