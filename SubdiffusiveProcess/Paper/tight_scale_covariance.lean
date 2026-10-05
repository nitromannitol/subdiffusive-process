module

public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- The dilation `x ↦ 3^j x`. -/
def aux_tight_scale_covariance_dil (d : ℕ) (j : ℤ) : C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun x => ((3 : ℝ) ^ j) • x, (by fun_prop)⟩

@[simp] theorem aux_tight_scale_covariance_dil_apply (j : ℤ) (x : SpatialCoordinates d) :
    aux_tight_scale_covariance_dil d j x = ((3 : ℝ) ^ j) • x := rfl

/-- The triadic scale shift: `(S_j ω)(m)(y) = ω(m + j)(3^j y)`. -/
def aux_tight_scale_covariance_scaleShift (j : ℤ) (om : BilateralField d) : BilateralField d :=
  fun m => (om (m + (j : ℤ))).comp (aux_tight_scale_covariance_dil d j)

@[simp] theorem aux_tight_scale_covariance_scaleShift_apply (j : ℤ) (om : BilateralField d) (m : ℤ)
    (y : SpatialCoordinates d) :
    aux_tight_scale_covariance_scaleShift j om m y = om (m + (j : ℤ)) (((3 : ℝ) ^ j) • y) := rfl

/-- Precomposition with the dilation, as a continuous self-map of the field space. -/
def aux_tight_scale_covariance_dilComp (d : ℕ) (j : ℤ) : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ (aux_tight_scale_covariance_dil d j)

theorem aux_tight_scale_covariance_dilComp_apply (j : ℤ) (f : C(SpatialCoordinates d, ℝ)) :
    aux_tight_scale_covariance_dilComp d j f = f.comp (aux_tight_scale_covariance_dil d j) := rfl

section Measure

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_tight_scale_covariance_measurable_dilComp (j : ℤ) : Measurable (aux_tight_scale_covariance_dilComp d j) :=
  (aux_tight_scale_covariance_dilComp d j).continuous.measurable

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The dilation composes the layer scalings: `3^{-(m+j)} · 3^j = 3^{-m}`. -/
theorem aux_tight_scale_covariance_dilComp_comp_layerScaling {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (j : ℤ) (m : ℤ) :
    (aux_tight_scale_covariance_dilComp d j) ∘ (layerScaling d (m + (j : ℤ))) = layerScaling d m := by
  funext f
  ext x
  simp only [Function.comp_apply, aux_tight_scale_covariance_dilComp_apply, layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, aux_tight_scale_covariance_dil_apply]
  congr 1
  rw [smul_smul]
  congr 1
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

theorem aux_tight_scale_covariance_map_scaledLayerLaw_dilComp (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (j : ℤ) (m : ℤ) :
    ((scaledLayerLaw d ν (m + (j : ℤ)) : Measure C(SpatialCoordinates d, ℝ))).map
        (aux_tight_scale_covariance_dilComp d j) = (scaledLayerLaw d ν m : Measure C(SpatialCoordinates d, ℝ)) := by
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (aux_tight_scale_covariance_measurable_dilComp j) (layerScaling d _).continuous.measurable,
    aux_tight_scale_covariance_dilComp_comp_layerScaling]

theorem aux_tight_scale_covariance_chaosSampleLaw_eq (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) : Measure (BilateralField d)) =
      Measure.infinitePi (fun n : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ))) := rfl

/-- **The scale shift preserves the chaos sample law.** -/
theorem aux_tight_scale_covariance_measurePreserving_scaleShift (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℤ) :
    MeasurePreserving (aux_tight_scale_covariance_scaleShift (d := d) j)
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) : Measure (BilateralField d))
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) := by
  rw [aux_tight_scale_covariance_chaosSampleLaw_eq]
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun n =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  have hre := aux_prop_growth_large_root_measurePreserving_reindex_add laws (j : ℤ)
  have hpi : MeasurePreserving (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) =>
      aux_tight_scale_covariance_dilComp d j (x i))
      (Measure.infinitePi (fun m : ℤ => laws (m + (j : ℤ))))
      (Measure.infinitePi laws) := by
    refine ⟨Measurable.of_eval fun i =>
      (aux_tight_scale_covariance_measurable_dilComp j).comp (measurable_pi_apply i), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => aux_tight_scale_covariance_measurable_dilComp j)]
    congr 1
    funext m
    exact aux_tight_scale_covariance_map_scaledLayerLaw_dilComp (chaosRootFieldLaw M) j m
  have hcomp := hpi.comp hre
  convert hcomp using 1
  rfl

end Measure

/-- Translation of all continuous layers. -/
def aux_tight_scale_covariance_translateComp (y : SpatialCoordinates d) :
    C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    ⟨fun x => x + y, continuous_id.add continuous_const⟩

def aux_tight_scale_covariance_translate (y : SpatialCoordinates d)
    (om : BilateralField d) : BilateralField d :=
  fun i => aux_tight_scale_covariance_translateComp y (om i)

@[simp] theorem aux_tight_scale_covariance_translate_apply (y : SpatialCoordinates d)
    (om : BilateralField d) (i : ℤ) (x : SpatialCoordinates d) :
    aux_tight_scale_covariance_translate y om i x = om i (x + y) := rfl

section Translation
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_tight_scale_covariance_translateComp_layerScaling {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (y : SpatialCoordinates d) (i : ℤ) :
    aux_tight_scale_covariance_translateComp y ∘ layerScaling d i =
      layerScaling d i ∘ aux_tight_scale_covariance_translateComp ((3 : ℝ) ^ (-i) • y) := by
  funext f
  ext x
  change f ((3 : ℝ) ^ (-i) • (x + y)) =
    f ((3 : ℝ) ^ (-i) • x + (3 : ℝ) ^ (-i) • y)
  rw [smul_add]

theorem aux_tight_scale_covariance_measurePreserving_translateComp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (y : SpatialCoordinates d) (i : ℤ) :
    MeasurePreserving (aux_tight_scale_covariance_translateComp y)
      (scaledLayerLaw d (chaosRootFieldLaw M) i).toMeasure
      (scaledLayerLaw d (chaosRootFieldLaw M) i).toMeasure := by
  refine ⟨(aux_tight_scale_covariance_translateComp y).continuous.measurable, ?_⟩
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (aux_tight_scale_covariance_translateComp y).continuous.measurable
      (layerScaling d i).continuous.measurable,
    aux_tight_scale_covariance_translateComp_layerScaling,
    ← Measure.map_map (layerScaling d i).continuous.measurable
      (aux_tight_scale_covariance_translateComp ((3 : ℝ) ^ (-i) • y)).continuous.measurable]
  have hroot : (chaosRootFieldLaw M).toMeasure.map
      (aux_tight_scale_covariance_translateComp ((3 : ℝ) ^ (-i) • y)) =
      (chaosRootFieldLaw M).toMeasure :=
    (gmc_zero_field_law_stationary M ((3 : ℝ) ^ (-i) • y)).map_eq
  rw [hroot]

theorem aux_tight_scale_covariance_measurePreserving_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (y : SpatialCoordinates d) :
    MeasurePreserving (aux_tight_scale_covariance_translate y)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  refine ⟨Measurable.of_eval fun i =>
    (aux_tight_scale_covariance_translateComp y).continuous.measurable.comp
      (measurable_pi_apply i), ?_⟩
  change (Measure.infinitePi (fun i : ℤ =>
    (scaledLayerLaw d (chaosRootFieldLaw M) i).toMeasure)).map
    (fun om i => aux_tight_scale_covariance_translateComp y (om i)) = _
  rw [Measure.infinitePi_map_pi _ (fun _ =>
    (aux_tight_scale_covariance_translateComp y).continuous.measurable)]
  congr 1
  funext i
  exact (aux_tight_scale_covariance_measurePreserving_translateComp M y i).map_eq

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_tight_scale_covariance_infraredPartialSum_translate {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (y : SpatialCoordinates d) (om : BilateralField d) (L : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum (aux_tight_scale_covariance_translate y om) L x =
      infraredPartialSum om L (x + y) - infraredPartialSum om L y := by
  simp only [aux_prop_growth_large_root_infraredPartialSum_apply,
    aux_tight_scale_covariance_translate_apply, zero_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem aux_tight_scale_covariance_ae_infrared_translate
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (y : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      H (aux_tight_scale_covariance_translate y om) x = H om (x + y) - H om y := by
  have ht := (aux_tight_scale_covariance_measurePreserving_translate M y).quasiMeasurePreserving.ae hH.2
  filter_upwards [hH.2, ht] with om hom hom' x
  have hleft := ((continuous_eval_const x).tendsto _).comp hom'
  have hright := (((continuous_eval_const (x + y)).tendsto _).comp hom).sub
    (((continuous_eval_const y).tendsto _).comp hom)
  apply tendsto_nhds_unique hleft
  exact hright.congr fun L => (aux_tight_scale_covariance_infraredPartialSum_translate y om L x).symm

theorem aux_tight_scale_covariance_ae_density_translate
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (y : SpatialCoordinates d) (N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H om N (y + x) =
        Real.exp (H om y) * cutoffSpeedDensity M H (aux_tight_scale_covariance_translate y om) N x := by
  filter_upwards [aux_tight_scale_covariance_ae_infrared_translate hH y] with om hom x
  simp only [cutoffSpeedDensity, cutoffPotential, hom,
    aux_tight_scale_covariance_translate_apply, ← Real.exp_add]
  rw [add_comm y x]
  congr 1
  ring
end Translation

theorem aux_tight_scale_covariance_scaleShift_nat (j : ℕ) (om : BilateralField d) :
    aux_tight_scale_covariance_scaleShift (j : ℤ) om =
      aux_prop_growth_large_root_scaleShift j om := by
  funext i
  ext x
  simp only [aux_tight_scale_covariance_scaleShift_apply,
    aux_prop_growth_large_root_scaleShift_apply, zpow_natCast]

theorem aux_tight_scale_covariance_scaleShift_add (j k : ℤ) (om : BilateralField d) :
    aux_tight_scale_covariance_scaleShift j (aux_tight_scale_covariance_scaleShift k om) =
      aux_tight_scale_covariance_scaleShift (j + k) om := by
  funext i
  ext x
  simp only [aux_tight_scale_covariance_scaleShift_apply, smul_smul]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_comm k j, add_assoc]

@[simp] theorem aux_tight_scale_covariance_scaleShift_zero (om : BilateralField d) :
    aux_tight_scale_covariance_scaleShift 0 om = om := by
  funext i
  ext x
  simp only [aux_tight_scale_covariance_scaleShift_apply, add_zero, zpow_zero, one_smul]

section DensityScaling
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_tight_scale_covariance_ae_density_scale_nat
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (j N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ c : ℝ, 0 < c ∧
      ∀ x : SpatialCoordinates d, cutoffSpeedDensity M H om N ((3 : ℝ) ^ j • x) =
        c * cutoffSpeedDensity M H (aux_tight_scale_covariance_scaleShift (j : ℤ) om) (N + j) x := by
  filter_upwards [aux_prop_growth_large_root_ae_infrared_scaleShift hH j] with om hom
  refine ⟨Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P -
    aux_prop_growth_large_root_irAnchor j om), Real.exp_pos _, ?_⟩
  intro x
  rw [aux_tight_scale_covariance_scaleShift_nat]
  unfold cutoffSpeedDensity
  rw [aux_prop_growth_large_root_cutoffPotential_scaleShift H om j N hom x,
    ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem aux_tight_scale_covariance_ae_density_scale
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (N m : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ c : ℝ, 0 < c ∧
      ∀ x : SpatialCoordinates d,
        cutoffSpeedDensity M H om N ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
          c * cutoffSpeedDensity M H
            (aux_tight_scale_covariance_scaleShift ((m : ℤ) - (N : ℤ)) om) m x := by
  by_cases hNm : N ≤ m
  · have hj : ((m - N : ℕ) : ℤ) = (m : ℤ) - (N : ℤ) := Int.ofNat_sub hNm
    have hsum : N + (m - N) = m := Nat.add_sub_of_le hNm
    simpa only [hsum, ← hj, zpow_natCast] using
      aux_tight_scale_covariance_ae_density_scale_nat hH (m - N) N
  · have hmN : m ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNm)
    let j := N - m
    have hj : (j : ℤ) = (N : ℤ) - (m : ℤ) := Int.ofNat_sub hmN
    have hdiff : (m : ℤ) - (N : ℤ) = -(j : ℤ) := by omega
    have hsum : m + j = N := Nat.add_sub_of_le hmN
    have hmp := aux_tight_scale_covariance_measurePreserving_scaleShift M (-(j : ℤ))
    have hae := hmp.quasiMeasurePreserving.ae (aux_tight_scale_covariance_ae_density_scale_nat hH j m)
    filter_upwards [hae] with om hom
    obtain ⟨c, hc, heq⟩ := hom
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    intro x
    have hx := heq ((3 : ℝ) ^ (-(j : ℤ)) • x)
    rw [aux_tight_scale_covariance_scaleShift_add, add_neg_cancel,
      aux_tight_scale_covariance_scaleShift_zero, hsum] at hx
    have hdil : (3 : ℝ) ^ j • ((3 : ℝ) ^ (-(j : ℤ)) • x) = x := by
      rw [smul_smul, ← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
        add_neg_cancel, zpow_zero, one_smul]
    rw [hdil] at hx
    rw [hdiff, hx]
    exact (inv_mul_cancel_left₀ hc.ne' _).symm
end DensityScaling

/-- Paragraph "The local normalization" of the elliptic tightness section
(`tight:eq-local-time`): the local normalization of the cube of physical side `3^m` at cutoff
`N`, centred at `y` in rescaled coordinates, is — after one measure-preserving relabelling,
rescaling and translation `T` of the layers — the standard cutoff-`m` speed density at the
origin, up to the removed random constant `c` ("removing `c` changes neither the generator nor
its law").  Consumers read constants "uniform in `L, m, z`" as constants for the standard
objects uniform in the cutoff. -/
theorem tight_scale_covariance
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (N m : ℕ) (y : SpatialCoordinates d) :
    ∃ T : BilateralField d → BilateralField d,
      MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ c : ℝ, 0 < c ∧
        ∀ x : SpatialCoordinates d,
          cutoffSpeedDensity M H omega N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
            c * cutoffSpeedDensity M H (T omega) m x := by
  let S := aux_tight_scale_covariance_scaleShift (d := d) ((m : ℤ) - (N : ℤ))
  let R := aux_tight_scale_covariance_translate y
  have hS := aux_tight_scale_covariance_measurePreserving_scaleShift M ((m : ℤ) - (N : ℤ))
  have hR := aux_tight_scale_covariance_measurePreserving_translate M y
  refine ⟨S ∘ R, hS.comp hR, ?_⟩
  have hs := hR.quasiMeasurePreserving.ae (aux_tight_scale_covariance_ae_density_scale hH N m)
  filter_upwards [aux_tight_scale_covariance_ae_density_translate hH y N, hs] with om htrans hscale
  obtain ⟨c, hc, heq⟩ := hscale
  refine ⟨Real.exp (H om y) * c, mul_pos (Real.exp_pos _) hc, ?_⟩
  intro x
  rw [htrans, heq]
  exact (mul_assoc _ _ _).symm

end SubdiffusiveProcess.Paper

