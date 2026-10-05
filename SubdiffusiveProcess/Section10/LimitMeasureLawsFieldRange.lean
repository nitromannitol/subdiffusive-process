module

public import SubdiffusiveProcess.Section10.LimitMeasureLawsLocality
public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionIndependence

@[expose] public section

/-!
# Actual field-level spatial independence for local chaos suppliers

The native `PotentialField.localSigma`, the original model's range-dependence
assumption and its actual root-field law supply this independence. Negative
layers expand space by `3^n`, so their dependence range is at most the unit
range. The actual bilateral product law then aggregates all negative layers.
No locality or independence premise is added to a source-root declaration.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Homogenization
open scoped Pointwise ENNReal CompactlySupported

noncomputable section

namespace SubdiffusiveProcess.Section10

/-- The sigma algebra of point evaluations of one continuous field on a set. -/
@[instance_reducible]
def fieldSpatialSigma {d : ℕ} (U : Set (SpatialCoordinates d)) :
    MeasurableSpace C(SpatialCoordinates d, ℝ) :=
  ⨆ x : U, (borel ℝ).comap (fun f => f x)

theorem field_spatial_sigma_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (U : Set (SpatialCoordinates d)) :
    fieldSpatialSigma U ≤ (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
  exact iSup_le fun x => (continuous_eval_const (x : SpatialCoordinates d)).measurable.comap_le

/-- The evaluation view of a scaled native field is measurable from its native
local coefficient sigma algebra on the correspondingly scaled open set. -/
theorem scaled_native_local_comap_le {d : ℕ} [NeZero d]
    (n : ℕ) (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    (fieldSpatialSigma U).comap
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        layerScaling d (-(n : ℤ)) (g.1.1)) ≤
      _root_.SubdiffusiveProcess.Model.PotentialField.localSigma ((3 : ℝ) ^ n • U) := by
  rw [fieldSpatialSigma, MeasurableSpace.comap_iSup]
  refine iSup_le fun x => ?_
  rw [MeasurableSpace.comap_comp]
  have he := SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
    (hU.smul₀ (pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)))
    (Set.smul_mem_smul_set x.property)
  have hfun :
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        (layerScaling d (-(n : ℤ)) (g.1.1)) x) =
      (fun g => g ((3 : ℝ) ^ n • (x : SpatialCoordinates d))) := by
    funext g
    simp only [layerScaling, neg_neg, zpow_natCast]
    rfl
  simpa only [Function.comp_def, hfun] using! he.comap_le

/-- Range independence of each actual negative scaled-layer law, descended
from the original native `M.G1.range_dependence` premise. -/
theorem negative_layer_spatial_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (U V : Set (SpatialCoordinates d)) (hU : IsOpen U) (hV : IsOpen V)
    (hsep : ∀ a ∈ U, ∀ b ∈ V, Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b)) :
    Indep (fieldSpatialSigma U) (fieldSpatialSigma V)
      (scaledLayerLaw d (chaosRootFieldLaw M) (-(n : ℤ))).toMeasure := by
  let : NeZero d := ⟨by have hd := M.shellPrefix.dimension; omega⟩
  have hpow : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
  have hsepScaled : ∀ ⦃a b : SpatialCoordinates d⦄,
      a ∈ (3 : ℝ) ^ n • U → b ∈ (3 : ℝ) ^ n • V →
        Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b) := by
    intro a b ha hb
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp ha
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hb
    rw [← smul_sub, euclideanNorm_smul, abs_of_pos hpos]
    exact (hsep x hx y hy).trans
      (le_mul_of_one_le_left (euclideanNorm_nonneg _) hpow)
  have hn := M.G1.range_dependence ((3 : ℝ) ^ n • U) ((3 : ℝ) ^ n • V)
    (hU.smul₀ (ne_of_gt hpos)).measurableSet (hV.smul₀ (ne_of_gt hpos)).measurableSet
    hsepScaled
  have hlocal := indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hn (scaled_native_local_comap_le n U hU))
    (scaled_native_local_comap_le n V hV)
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → C(SpatialCoordinates d, ℝ) :=
    fun g => layerScaling d (-(n : ℤ)) (g.1.1)
  have hF : Measurable F :=
    (layerScaling d (-(n : ℤ))).continuous.measurable.comp forget.continuous.measurable
  have hpush := (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map hF.aemeasurable
    (field_spatial_sigma_le U) (field_spatial_sigma_le V)).mp hlocal
  have hlaw : (scaledLayerLaw d (chaosRootFieldLaw M) (-(n : ℤ))).toMeasure =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure.map F := by
    exact Measure.map_map (layerScaling d (-(n : ℤ))).continuous.measurable
      forget.continuous.measurable
  rw [hlaw]
  exact hpush

/-- All actual negative-layer spatial sigma algebras retain field-level
finite-range independence under `chaosSampleLaw M`. -/
theorem fine_spatial_sigma_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (U V : Set (SpatialCoordinates d)) (hU : IsOpen U) (hV : IsOpen V)
    (hsep : ∀ a ∈ U, ∀ b ∈ V, Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b)) :
    Indep (fineSpatialSigma U) (fineSpatialSigma V) (chaosSampleLaw M).toMeasure := by
  let coord (n : ℕ) (omega : BilateralField d) := omega (-(n : ℤ))
  let kappa (n : ℕ) : MeasurableSpace (BilateralField d) :=
    MeasurableSpace.comap (coord n) inferInstance
  let a (n : ℕ) := (fieldSpatialSigma U).comap (coord n)
  let b (n : ℕ) := (fieldSpatialSigma V).comap (coord n)
  have hkappa : iIndep kappa (chaosSampleLaw M).toMeasure := by
    have hbase : iIndepFun (fun (j : ℤ) (omega : BilateralField d) => omega j)
        (chaosSampleLaw M).toMeasure :=
      iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
    exact (hbase.precomp (g := fun n : ℕ => -(n : ℤ))
      (fun _ _ h => Int.ofNat_inj.mp (neg_inj.mp h))).iIndep
  have hle (n : ℕ) : kappa n ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
    (measurable_pi_apply (-(n : ℤ))).comap_le
  have ha (n : ℕ) : a n ≤ kappa n :=
    MeasurableSpace.comap_mono (field_spatial_sigma_le U)
  have hb (n : ℕ) : b n ≤ kappa n :=
    MeasurableSpace.comap_mono (field_spatial_sigma_le V)
  have hab (n : ℕ) : Indep (a n) (b n) (chaosSampleLaw M).toMeasure := by
    apply (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map
      (measurable_pi_apply (-(n : ℤ))).aemeasurable
      (field_spatial_sigma_le U) (field_spatial_sigma_le V)).mpr
    rw [show (chaosSampleLaw M).toMeasure.map (coord n) =
        (scaledLayerLaw d (chaosRootFieldLaw M) (-(n : ℤ))).toMeasure from
      Measure.infinitePi_map_eval _ (-(n : ℤ))]
    exact negative_layer_spatial_independent M n U V hU hV hsep
  have hmain := SubdiffusiveProcess.CoarseGrainingVocab.indep_iSup_of_indep_of_iIndep
    hkappa hle ha hb hab
  have hjoin (W : Set (SpatialCoordinates d)) :
      (⨆ n : ℕ, (fieldSpatialSigma W).comap (coord n)) = fineSpatialSigma W := by
    simp only [fieldSpatialSigma, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, fineSpatialSigma, coord, Function.comp_def]
  rwa [hjoin U, hjoin V] at hmain

/-- Concrete bounded R3b consumer: arbitrary Borel restrictions of actual
finite cutoffs are independent when enclosed in separated open source regions.
No independence of final limit restrictions is inferred from continuity. -/
theorem actual_cutoff_restrictions_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N L : ℕ)
    (U V A B : Set (SpatialCoordinates d)) (hU : IsOpen U) (hV : IsOpen V)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hsep : ∀ a ∈ U, ∀ b ∈ V, Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b)) :
    Indep (MeasurableSpace.comap (fun omega => (chaosCutoff M N omega).restrict A) inferInstance)
      (MeasurableSpace.comap (fun omega => (chaosCutoff M L omega).restrict B) inferInstance)
      (chaosSampleLaw M).toMeasure := by
  have hleft := (measurable_chaos_cutoff_restriction_local M N A hA).mono
    (fine_spatial_sigma_mono hAU) le_rfl
  have hright := (measurable_chaos_cutoff_restriction_local M L B hB).mono
    (fine_spatial_sigma_mono hBV) le_rfl
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (fine_spatial_sigma_independent M U V hU hV hsep) hleft.comap_le)
    hright.comap_le

/-- Concrete same-limit consumer: positive compact-test integrals of the
actual restriction maps are independent in separated open source regions.
Only the supplied AE locally weak convergence and local finiteness are used
to pass from finite cutoffs to this very same limit. -/
theorem same_limit_positive_tests_independent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 omega))
    (hc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega))
    (U V : Set (SpatialCoordinates d)) (hU : IsOpen U) (hV : IsOpen V)
    (hsep : ∀ a ∈ U, ∀ b ∈ V, Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b))
    (f g : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfs : Function.support f ⊆ U) (hgs : Function.support g ⊆ V) :
    IndepFun (fun omega => ∫⁻ x, ENNReal.ofReal (f x) ∂(mu0 omega).restrict U)
      (fun omega => ∫⁻ x, ENNReal.ofReal (g x) ∂(mu0 omega).restrict V)
      (chaosSampleLaw M).toMeasure := by
  have hleft := measurable_local_positive_test_limit M U hU.measurableSet f
  have hright := measurable_local_positive_test_limit M V hV.measurableSet g
  have hreps : IndepFun (localPositiveTestLimit M U f) (localPositiveTestLimit M V g)
      (chaosSampleLaw M).toMeasure := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (fine_spatial_sigma_independent M U V hU hV hsep)
        hleft.comap_le) hright.comap_le
  exact hreps.congr
    (same_chaos_limit_positive_test_local M mu0 hl hc U hU.measurableSet f hf hfs)
    (same_chaos_limit_positive_test_local M mu0 hl hc V hV.measurableSet g hg hgs)

end SubdiffusiveProcess.Section10
