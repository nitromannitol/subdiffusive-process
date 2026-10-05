module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.S09InfraredVersion
public import SubdiffusiveProcess.Lnorm.CutoffPotentialProxy
public import SubdiffusiveProcess.Sobolev.CompactResponses

@[expose] public section

open Filter MeasureTheory Set Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.AuditExports

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The normalized cutoff log coefficient with the specified layer subtracted. -/
def deletedCompactPotential (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N layer : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    C(closedCube z r hr, ℝ) :=
  Lnorm.proxy_contFn (H omega) M N omega z r hr -
    (omega (-(Int.ofNat layer))).restrict (closedCube z r hr)

/-- The actual positive coefficient after deleting one layer, at every cutoff. -/
def deletedPositiveCoefficient (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N layer : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    PositiveCoefficient (centeredCube z r hr) :=
  expPotentialCoefficient (compactPotentialLp (closedCube z r hr)
    (deletedCompactPotential M H N layer omega z r hr))

/-- A continuous representative of the deleted coefficient on its compact cube. -/
def deletedCoefficientCM (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N layer : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    C(closedCube z r hr, ℝ) :=
  (⟨Real.exp, Real.continuous_exp⟩ : C(ℝ, ℝ)).comp
    (deletedCompactPotential M H N layer omega z r hr)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Once the cutoff contains the layer, deletion cancels that coordinate exactly. -/
theorem deletedCompactPotential_eq_erase
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N layer : ℕ) (hN : layer ≤ N)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    deletedCompactPotential M positiveInfraredVersion N layer omega z r hr =
      (positiveInfraredVersion omega +
        ∑ j ∈ (Finset.range (N + 1)).erase layer, omega (-(Int.ofNat j))).restrict
          (closedCube z r hr) -
        ContinuousMap.const _ (Real.log (Lnorm.prop16_kap M N)) := by
  classical
  have hmem : layer ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hN)
  have hsum := Finset.sum_erase_add (Finset.range (N + 1))
    (fun j => omega (-(Int.ofNat j))) hmem
  unfold deletedCompactPotential Lnorm.proxy_contFn
  simp only [Int.ofNat_eq_natCast] at hsum ⊢
  rw [← hsum]
  ext x
  change (positiveInfraredVersion omega x.val +
      ((∑ j ∈ (Finset.range (N + 1)).erase layer, omega (-(Int.ofNat j))) x.val +
        omega (-(Int.ofNat layer)) x.val) - Real.log (Lnorm.prop16_kap M N)) -
      omega (-(Int.ofNat layer)) x.val =
    (positiveInfraredVersion omega x.val +
      (∑ j ∈ (Finset.range (N + 1)).erase layer, omega (-(Int.ofNat j))) x.val) -
        Real.log (Lnorm.prop16_kap M N)
  ring

/-- Deleted compact potentials are measurable in the literal remaining-layer sigma-field. -/
theorem measurable_deletedCompactPotential_remaining
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N layer : ℕ) (hN : layer ≤ N)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    @Measurable _ _ (remainingSigma layer) (borel C(closedCube z r hr, ℝ))
      (fun omega => deletedCompactPotential M positiveInfraredVersion N layer omega z r hr) := by
  classical
  let : MeasurableSpace (BilateralField d) := remainingSigma layer
  let : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  let : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  have heq := funext (fun omega => deletedCompactPotential_eq_erase M N layer hN omega z r hr)
  rw [heq]
  refine Measurable.sub ?_ measurable_const
  refine (ContinuousMap.continuous_restrict _).measurable.comp ?_
  refine (measurable_positiveInfraredVersion_remaining layer).add
    (Finset.measurable_sum _ fun j hj => ?_)
  have hneq : -(Int.ofNat j) ≠ -(Int.ofNat layer) := by
    have := (Finset.mem_erase.mp hj).1
    change -(j : ℤ) ≠ -(layer : ℤ)
    exact fun h => this (Int.ofNat_inj.mp (neg_injective h))
  exact (measurable_pi_apply (⟨-(Int.ofNat j), hneq⟩ : {j : ℤ // j ≠ -(Int.ofNat layer)})).comp
    (comap_measurable (remainingProjection (d := d) layer))

/-- The continuous deleted coefficient itself is remaining-layer measurable. -/
theorem measurable_deletedCoefficientCM_remaining
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N layer : ℕ) (hN : layer ≤ N)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    @Measurable _ _ (remainingSigma layer) (borel C(closedCube z r hr, ℝ))
      (fun omega => deletedCoefficientCM M positiveInfraredVersion N layer omega z r hr) :=
  (ContinuousMap.continuous_postcomp (⟨Real.exp, Real.continuous_exp⟩ : C(ℝ, ℝ))).borel_measurable.comp
    (measurable_deletedCompactPotential_remaining M N layer hN z r hr)

/-- Exact spatial almost-everywhere deletion of the actual normalized coefficient. -/
theorem deletedPositiveCoefficient_coeFn
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N layer : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (deletedPositiveCoefficient M H N layer omega z r hr).val x =
        Real.exp (-omega (-(Int.ofNat layer)) x) *
          (cutoffPositiveCoefficient M H omega N z hr).val x := by
  let K := closedCube z r hr
  let p := Lnorm.proxy_contFn (H omega) M N omega z r hr
  let q := deletedCompactPotential M H N layer omega z r hr
  rw [Lnorm.proxy_pot_eq_coefficient M H N omega z r hr]
  filter_upwards [expPotentialCoefficient_coeFn (compactPotentialLp K q),
    expPotentialCoefficient_coeFn (compactPotentialLp K p),
    compactPotentialLp_on_domain K (centeredCube_subset_closedCube z hr) q,
    compactPotentialLp_on_domain K (centeredCube_subset_closedCube z hr) p,
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hq hp hqr hpr hx
  change (expPotentialCoefficient (compactPotentialLp K q)).val x =
    Real.exp (-omega (-(Int.ofNat layer)) x) *
      (expPotentialCoefficient (compactPotentialLp K p)).val x
  rw [hq, hp, hqr hx, hpr hx]
  change Real.exp (p ⟨x, centeredCube_subset_closedCube z hr hx⟩ -
      omega (-(Int.ofNat layer)) x) = _
  rw [sub_eq_add_neg, Real.exp_add, mul_comm]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The L∞ coefficient is represented by the continuous deleted coefficient. -/
theorem deletedPositiveCoefficient_val_eq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N layer : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (deletedPositiveCoefficient M H N layer omega z r hr).val =
      compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
        (deletedCoefficientCM M H N layer omega z r hr) := by
  apply Lp.ext
  filter_upwards [expPotentialCoefficient_coeFn (compactPotentialLp (closedCube z r hr)
      (deletedCompactPotential M H N layer omega z r hr)),
    compactPotentialLp_on_domain (closedCube z r hr) (centeredCube_subset_closedCube z hr)
      (deletedCompactPotential M H N layer omega z r hr),
    compactPotentialLp_on_domain (closedCube z r hr) (centeredCube_subset_closedCube z hr)
      (deletedCoefficientCM M H N layer omega z r hr),
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x he hp hc hx
  change (expPotentialCoefficient (compactPotentialLp (closedCube z r hr)
    (deletedCompactPotential M H N layer omega z r hr))).val x = _
  rw [he, hp hx, hc hx]
  rfl

/-- Norm-Borel measurability of the deleted L∞ coefficient uses only the remaining layers. -/
theorem measurable_deletedPositiveCoefficient_val_remaining
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N layer : ℕ) (hN : layer ≤ N)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    @Measurable _ _ (remainingSigma layer)
      (borel (Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))))
      (fun omega => (deletedPositiveCoefficient M positiveInfraredVersion N layer omega z r hr).val) := by
  have heq := funext (fun omega => deletedPositiveCoefficient_val_eq M
    positiveInfraredVersion N layer omega z r hr)
  rw [heq]
  exact (Lnorm.proxy_cp_lipschitz z r hr).continuous.borel_measurable.comp
    (measurable_deletedCoefficientCM_remaining M N layer hN z r hr)

/-- Finite deleted scalar inverse responses are remaining-layer measurable. -/
theorem measurable_deleted_scalar_inverse_remaining
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N layer : ℕ) (hN : layer ≤ N)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) :
    Measurable[remainingSigma layer] (fun omega => inverseResponse S
      (deletedPositiveCoefficient M positiveInfraredVersion N layer omega z r hr)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) := by
  let : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  exact (continuous_inverseResponse_compact S (closedCube z r hr)
    ((sobolevVolumeLoad f).comp S.space.subtypeL)).borel_measurable.comp
      (measurable_deletedCompactPotential_remaining M N layer hN z r hr)

/-- Canonical deletion agrees almost surely, at every cutoff, with any characterized infrared field. -/
theorem deletedPositiveCoefficient_ae_eq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (layer : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      deletedPositiveCoefficient M positiveInfraredVersion N layer omega z r hr =
        deletedPositiveCoefficient M H N layer omega z r hr := by
  filter_upwards [positiveInfraredVersion_ae_eq M H hH] with omega heq N
  unfold deletedPositiveCoefficient deletedCompactPotential
  rw [heq]

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The remaining-field sigma-field is a sub-sigma-field of the original sample sigma-field. -/
theorem remainingSigma_le (layer : ℕ) :
    remainingSigma (d := d) layer ≤ (inferInstance : MeasurableSpace (BilateralField d)) := by
  apply Measurable.comap_le
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply j.val

end SubdiffusiveProcess.AuditExports
