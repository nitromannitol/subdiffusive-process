import SubdiffusiveProcess.Sobolev.DiagonalDefect




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- A positive coefficient scaled by a positive real is a positive coefficient. -/
def smulPositiveCoefficient {c : ℝ} (hc : 0 < c) (a : PositiveCoefficient Ω) :
    PositiveCoefficient Ω :=
  ⟨c • a.val, by
    obtain ⟨k, hk, hka⟩ := a.2
    refine ⟨c * k, by positivity, ?_⟩
    filter_upwards [hka, Lp.coeFn_smul c a.val] with x hx hs
    rw [hs]
    simpa using mul_le_mul_of_nonneg_left hx hc.le⟩

@[simp] theorem smulPositiveCoefficient_val {c : ℝ} (hc : 0 < c) (a : PositiveCoefficient Ω) :
    (smulPositiveCoefficient hc a).val = c • a.val := rfl

theorem smulPositiveCoefficient_coeFn {c : ℝ} (hc : 0 < c) (a : PositiveCoefficient Ω) :
    (smulPositiveCoefficient hc a).val
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => c * a.val x := by
  filter_upwards [Lp.coeFn_smul c a.val] with x hx
  simpa using hx

/-- Components of a scalar multiple in the killed graph. -/
theorem killed_smul_grad (t : ℝ) (w : killedSobolevGraph Ω) (i : Fin d) :
    ((t • w : killedSobolevGraph Ω) : SobolevData Ω).2 i
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => t * ((w : SobolevData Ω).2 i) x := by
  have : ((t • w : killedSobolevGraph Ω) : SobolevData Ω).2 i
      = t • ((w : SobolevData Ω).2 i) := rfl
  rw [this]
  filter_upwards [Lp.coeFn_smul t ((w : SobolevData Ω).2 i)] with x hx
  simpa using hx

/-- Components of a scalar multiple in the mean-zero graph. -/
theorem meanZero_smul_grad [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (t : ℝ) (w : meanZeroSobolevGraph Ω) (i : Fin d) :
    ((t • w : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => t * ((w : SobolevData Ω).2 i) x := by
  have : ((t • w : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i
      = t • ((w : SobolevData Ω).2 i) := rfl
  rw [this]
  filter_upwards [Lp.coeFn_smul t ((w : SobolevData Ω).2 i)] with x hx
  simpa using hx

/-! ### Dirichlet response scaling -/

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Scaling the coefficient scales the affine Dirichlet response by the same factor. -/
theorem affineDirichletResponse_smulCoeff
    (hOm : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    {c : ℝ} (hc : 0 < c)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hOm hD (smulPositiveCoefficient hc a) p =
      c * affineDirichletResponse hOm hD a p := by
  have hkey : ∀ w : killedSobolevGraph Ω,
      (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          (smulPositiveCoefficient hc a).val x * (p i + (w : SobolevData Ω).2 i x) ^ 2) =
        c * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + (w : SobolevData Ω).2 i x) ^ 2 := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [smulPositiveCoefficient_coeFn hc a] with x hx
    rw [hx]; ring
  have h1 := affineDirichletResponse_isLeast hOm hD (smulPositiveCoefficient hc a) p
  have h2 := affineDirichletResponse_isLeast hOm hD a p
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := h2.1
    refine h1.2 ⟨w, ?_⟩
    exact (hkey w).trans (congrArg (fun z : ℝ => c * z) hw)
  · obtain ⟨w, hw⟩ := h1.1
    have hmem : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (p i + (w : SobolevData Ω).2 i x) ^ 2) ∈
        Set.range fun v : killedSobolevGraph Ω =>
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * (p i + (v : SobolevData Ω).2 i x) ^ 2 := ⟨w, rfl⟩
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (h2.2 hmem) hc.le)
      ((hkey w).symm.trans hw)

/-- Scaling the slope scales the affine Dirichlet response by the square of the factor. -/
theorem affineDirichletResponse_smulSlope
    (hOm : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    {t : ℝ} (ht : t ≠ 0)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hOm hD a (t • p) =
      t ^ 2 * affineDirichletResponse hOm hD a p := by
  have hkey : ∀ v : killedSobolevGraph Ω,
      (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((t • p) i +
            ((t • v : killedSobolevGraph Ω) : SobolevData Ω).2 i x) ^ 2) =
        t ^ 2 * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + (v : SobolevData Ω).2 i x) ^ 2 := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [killed_smul_grad t v i] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := affineDirichletResponse_isLeast hOm hD a (t • p)
  have h2 := affineDirichletResponse_isLeast hOm hD a p
  have htsq : (0:ℝ) < t ^ 2 := by positivity
  refine le_antisymm ?_ ?_
  · obtain ⟨v, hv⟩ := h2.1
    refine h1.2 ⟨t • v, ?_⟩
    exact (hkey v).trans (congrArg (fun z : ℝ => t ^ 2 * z) hv)
  · obtain ⟨w, hw⟩ := h1.1
    have hsm : (t • (t⁻¹ • w) : killedSobolevGraph Ω) = w := by
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    have hmem : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (p i + ((t⁻¹ • w : killedSobolevGraph Ω) : SobolevData Ω).2 i x) ^ 2) ∈
        Set.range fun v : killedSobolevGraph Ω =>
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * (p i + (v : SobolevData Ω).2 i x) ^ 2 := ⟨t⁻¹ • w, rfl⟩
    have heq : t ^ 2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + ((t⁻¹ • w : killedSobolevGraph Ω) : SobolevData Ω).2 i x) ^ 2) =
        affineDirichletResponse hOm hD a (t • p) := by
      have h0 := hkey (t⁻¹ • w)
      rw [hsm] at h0
      exact h0.symm.trans hw
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (h2.2 hmem) htsq.le) heq

/-! ### Inverse-Neumann response scaling -/

/-- Scaling the coefficient scales the inverse-Neumann response by the reciprocal. -/
theorem affineInverseNeumannResponse_smulCoeff
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    {c : ℝ} (hc : 0 < c)
    (a : PositiveCoefficient Ω) (q : Fin d → ℝ) :
    affineInverseNeumannResponse hN (smulPositiveCoefficient hc a) q =
      c⁻¹ * affineInverseNeumannResponse hN a q := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hkey : ∀ u : meanZeroSobolevGraph Ω,
      (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            q i * ((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            (smulPositiveCoefficient hc a).val x *
              (((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x *
                ((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x)) =
        c⁻¹ * (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              q i * (u : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x)) := by
    intro u
    have hlin : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          q i * ((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x) =
        c⁻¹ * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          q i * (u : SobolevData Ω).2 i x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [meanZero_smul_grad c⁻¹ u i] with x hx
      rw [hx]; ring
    have hquad : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          (smulPositiveCoefficient hc a).val x *
            (((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x *
              ((c⁻¹ • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x)) =
        c⁻¹ * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [meanZero_smul_grad c⁻¹ u i, smulPositiveCoefficient_coeFn hc a]
        with x hx ha
      rw [hx, ha]
      field_simp
    rw [hlin, hquad]; ring
  have h1 := affineInverseNeumannResponse_isGreatest hN (smulPositiveCoefficient hc a) q
  have h2 := affineInverseNeumannResponse_isGreatest hN a q
  have hcinv : (0:ℝ) < c⁻¹ := inv_pos.2 hc
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := h1.1
    have hsm : (c⁻¹ • (c • w) : meanZeroSobolevGraph Ω) = w := by
      rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
    have h0 := hkey (c • w)
    rw [hsm] at h0
    have hmem : (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          q i * ((c • w : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x) -
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (((c • w : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x *
            ((c • w : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x)) ∈
        Set.range fun v : meanZeroSobolevGraph Ω =>
          2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              q i * (v : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x) :=
      ⟨c • w, rfl⟩
    exact le_of_eq_of_le (hw.symm.trans h0)
      (mul_le_mul_of_nonneg_left (h2.2 hmem) hcinv.le)
  · obtain ⟨u, hu⟩ := h2.1
    have hmem := h1.2 (Set.mem_range_self (c⁻¹ • u))
    exact le_of_eq_of_le (congrArg (fun z : ℝ => c⁻¹ * z) hu).symm
      ((hkey u).symm.trans_le hmem)

/-- Scaling the slope scales the inverse-Neumann response by the square of the factor. -/
theorem affineInverseNeumannResponse_smulSlope
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    {t : ℝ} (ht : t ≠ 0)
    (a : PositiveCoefficient Ω) (q : Fin d → ℝ) :
    affineInverseNeumannResponse hN a (t • q) =
      t ^ 2 * affineInverseNeumannResponse hN a q := by
  have htsq : (0:ℝ) < t ^ 2 := by positivity
  have hkey : ∀ u : meanZeroSobolevGraph Ω,
      (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            (t • q) i * ((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * (((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x *
              ((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x)) =
        t ^ 2 * (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              q i * (u : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x)) := by
    intro u
    have hlin : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          (t • q) i * ((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x) =
        t ^ 2 * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          q i * (u : SobolevData Ω).2 i x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [meanZero_smul_grad t u i] with x hx
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hquad : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x *
            ((t • u : meanZeroSobolevGraph Ω) : SobolevData Ω).2 i x)) =
        t ^ 2 * ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [meanZero_smul_grad t u i] with x hx
      rw [hx]; ring
    rw [hlin, hquad]; ring
  have h1 := affineInverseNeumannResponse_isGreatest hN a (t • q)
  have h2 := affineInverseNeumannResponse_isGreatest hN a q
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := h1.1
    have hsm : (t • (t⁻¹ • w) : meanZeroSobolevGraph Ω) = w := by
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    have h0 := hkey (t⁻¹ • w)
    rw [hsm] at h0
    exact le_of_eq_of_le (hw.symm.trans h0)
      (mul_le_mul_of_nonneg_left (h2.2 (Set.mem_range_self (t⁻¹ • w))) htsq.le)
  · obtain ⟨u, hu⟩ := h2.1
    have hmem := h1.2 (Set.mem_range_self (t • u))
    exact le_of_eq_of_le (congrArg (fun z : ℝ => t ^ 2 * z) hu).symm
      ((hkey u).symm.trans_le hmem)

/-! ### The paper's normalized slopes -/

/-- The paper's substitution `v = a₀^{-1/2}w` on the Dirichlet side: the response of the
rescaled coefficient `a/α` at unit slope is the response of `a` at slope `α^{-1/2}e`. -/
theorem affineDirichletResponse_normalizedSlope
    (hOm : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    {alpha : ℝ} (halpha : 0 < alpha)
    (aQ : PositiveCoefficient Ω) (e : Fin d → ℝ) :
    affineDirichletResponse hOm hD (smulPositiveCoefficient halpha aQ)
        ((Real.sqrt alpha)⁻¹ • e) =
      affineDirichletResponse hOm hD aQ e := by
  have hs : (0:ℝ) < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hsq : ((Real.sqrt alpha)⁻¹) ^ 2 = alpha⁻¹ := by
    rw [inv_pow, Real.sq_sqrt halpha.le]
  rw [affineDirichletResponse_smulSlope hOm hD (inv_ne_zero (ne_of_gt hs)), hsq,
    affineDirichletResponse_smulCoeff hOm hD halpha, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt halpha), one_mul]

/-- The same substitution on the inverse-Neumann side, at slope `α^{1/2}e`. -/
theorem affineInverseNeumannResponse_normalizedSlope
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    {alpha : ℝ} (halpha : 0 < alpha)
    (aQ : PositiveCoefficient Ω) (e : Fin d → ℝ) :
    affineInverseNeumannResponse hN (smulPositiveCoefficient halpha aQ)
        (Real.sqrt alpha • e) =
      affineInverseNeumannResponse hN aQ e := by
  have hs : (0:ℝ) < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hsq : (Real.sqrt alpha) ^ 2 = alpha := Real.sq_sqrt halpha.le
  rw [affineInverseNeumannResponse_smulSlope hN (ne_of_gt hs), hsq,
    affineInverseNeumannResponse_smulCoeff hN halpha, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt halpha), one_mul]

end SubdiffusiveProcess
