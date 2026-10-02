import SubdiffusiveProcess.Paper.tight_static_cut
import SubdiffusiveProcess.Paper.tight_static_coer
import SubdiffusiveProcess.Section9.CutoffTranslatedCubeTail
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import Mathlib.Probability.Independence.InfinitePi
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Paper.lem_extremes
import SubdiffusiveProcess.Geometry.CoordinateFold
import SubdiffusiveProcess.Paper.tight_scale_covariance
import SubdiffusiveProcess.CoarseGrainingVocab.DeltaLogSquaredTail
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment

-- ===== module HLow.Theta =====
section



open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The GMC sample built from native copies: layer `k` is copy `k - N` dilated to scale `3^k`. -/
def aux_hlow_Theta (d : ℕ) (N : ℕ) (η : NativeBilateralPotentialSample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (η ((k : ℤ) - N))

lemma aux_hlow_measurable_Theta (N : ℕ) : Measurable (aux_hlow_Theta d N) := by
  apply measurable_pi_lambda
  intro k
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp (measurable_pi_apply _)

/-- The GMC law is the product of its marginals. -/
lemma aux_hlow_P_eq_infinitePi (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    M.P.toMeasure = Measure.infinitePi
      (fun k => (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure) := by
  have h := M.shellPrefix.independent
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k => SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)] at h
  have hid : M.P.toMeasure.map (fun ω (k : ℕ) => ω k) = M.P.toMeasure := by
    have : (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => fun k : ℕ => ω k) = id := rfl
    rw [this, Measure.map_id]
  rw [hid] at h
  rw [h]
  congr 1

/-- **Θ is measure preserving** from the native product law to `M.P`. -/
lemma aux_hlow_measurePreserving_Theta (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    MeasurePreserving (aux_hlow_Theta d N)
      (Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))
      M.P.toMeasure := by
  refine ⟨aux_hlow_measurable_Theta N, ?_⟩
  set μ := Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
    with hμ
  -- independence of the relabelled, dilated coordinates
  have hind0 : iIndepFun (fun (i : ℤ) (η : NativeBilateralPotentialSample d) => η i) μ :=
    iIndepFun_infinitePi (P := fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
      (X := fun _ => id) (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - (N : ℤ)) := by
    intro a b h; simpa using h
  have hind1 := hind0.precomp hinj
  have hind2 := hind1.comp (fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
    (fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
  have hmeas : ∀ k : ℕ, Measurable (fun η : NativeBilateralPotentialSample d =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (η ((k : ℤ) - N))) := fun k =>
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp (measurable_pi_apply _)
  have hind3 : iIndepFun (fun (k : ℕ) (η : NativeBilateralPotentialSample d) =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (η ((k : ℤ) - N))) μ := hind2
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hmeas] at hind3
  have hind2 := hind3
  change μ.map (fun η k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (η ((k : ℤ) - N))) = _
  rw [hind2, aux_hlow_P_eq_infinitePi M]
  congr 1
  funext k
  -- marginal: zeroPotentialLaw mapped by triadicScale k
  have e : (fun η : NativeBilateralPotentialSample d =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (η ((k : ℤ) - N))) =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k ∘ (fun η => η ((k : ℤ) - N)) := rfl
  rw [e, ← Measure.map_map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
    (measurable_pi_apply ((k : ℤ) - (N : ℤ))), hμ, Measure.infinitePi_map_eval, M.shellPrefix.marginal_scaling k]
  rfl

end Paper
end
end


section



open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}



def aux_hlow_pi (d : ℕ) (η : NativeBilateralPotentialSample d) : BilateralField d :=
  fun j => layerScaling d j
    ((⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
      C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ))) (η j))



def aux_hlow_mass (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) : ℝ≥0∞ :=
  ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
    ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) omega N x)

/-- Pointwise identity of the densities. -/
lemma aux_hlow_density_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (η : NativeBilateralPotentialSample d) (y : SpatialCoordinates d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N (aux_hlow_Theta d N η) y =
      cutoffSpeedDensity M (fun _ => 0) (aux_hlow_pi d η) N (((3 : ℝ) ^ N)⁻¹ • y) := by
  unfold SubdiffusiveProcess.Frozen.Assumptions.aCutoff cutoffSpeedDensity cutoffPotential
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [ContinuousMap.zero_apply, zero_add]
  push_cast
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [aux_hlow_Theta, aux_hlow_pi]
  rw [show N + 1 - 1 - k = N - k by omega]
  have hidx : ((N - k : ℕ) : ℤ) - (N : ℤ) = -Int.ofNat k := by
    rw [Int.ofNat_eq_coe]; push_cast [Nat.cast_sub hk']; ring
  rw [hidx]
  show (η (-Int.ofNat k)).1.1 (((3 : ℝ) ^ (N - k))⁻¹ • y) =
    (η (-Int.ofNat k)).1.1 (((3 : ℝ) ^ (-(-Int.ofNat k))) • (((3 : ℝ) ^ N)⁻¹ • y))
  congr 1
  rw [smul_smul]
  congr 1
  rw [neg_neg, Int.ofNat_eq_coe, zpow_natCast, pow_sub₀ _ (by norm_num : (3 : ℝ) ≠ 0) hk', mul_inv, inv_inv,
    mul_comm]

lemma aux_hlow_continuous_density (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) :
    Continuous (fun x => cutoffSpeedDensity M (fun _ => 0) omega N x) := by
  unfold cutoffSpeedDensity cutoffPotential
  refine Real.continuous_exp.comp (Continuous.sub ?_ continuous_const)
  exact (ContinuousMap.continuous _).add (continuous_finset_sum _ fun j _ => (omega _).continuous)

lemma aux_hlow_axisCube_eq (N : ℕ) :
    Homogenization.axisCube (fun _ : Fin d => -((3 : ℝ) ^ N / 2)) ((3 : ℝ) ^ N) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ N) (by positivity) : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  unfold Homogenization.axisCube
  congr 1
  funext i
  congr 1 <;> simp <;> ring

lemma aux_hlow_volume_axisCube (N : ℕ) :
    (volume (Homogenization.axisCube (0 : Homogenization.Vec d) ((3 : ℝ) ^ N))).toReal = ((3 : ℝ) ^ N) ^ d := by
  unfold Homogenization.axisCube
  rw [Real.volume_pi_Ioo]
  simp only [Pi.zero_apply, zero_add, sub_zero]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]

/-- Change of variables: the centred cube of side `R` against the unit cube. -/
lemma aux_hlow_change_of_variables {R : ℝ} (hR : 0 < R) (g : SpatialCoordinates d → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) R hR : Set (SpatialCoordinates d)), g (R⁻¹ • y) =
      ENNReal.ofReal (R ^ d) *
        ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)), g x := by
  have hmap := map_cubeDilation_restrict (0 : SpatialCoordinates d) (0 : SpatialCoordinates d) hR one_pos
  have hmeas : Measurable (fun y : SpatialCoordinates d => g (R⁻¹ • y)) :=
    hg.comp (measurable_const_smul R⁻¹)
  have h1 : ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      g (R⁻¹ • cubeDilation 0 0 R x) =
      ENNReal.ofReal |(R ^ d)⁻¹| *
        ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) R hR : Set (SpatialCoordinates d)), g (R⁻¹ • y) := by
    rw [← lintegral_map hmeas (continuous_cubeDilation 0 0 R).measurable, hmap, lintegral_smul_measure]
    rfl
  have hdil : ∀ x : SpatialCoordinates d, R⁻¹ • cubeDilation 0 0 R x = x := by
    intro x; funext i
    simp only [Pi.smul_apply, cubeDilation_apply, Pi.zero_apply, sub_zero, zero_add, smul_eq_mul]
    field_simp
  simp_rw [hdil] at h1
  rw [h1, ← mul_assoc, abs_of_pos (inv_pos.2 (pow_pos hR d)), ← ENNReal.ofReal_mul (pow_pos hR d).le,
    mul_inv_cancel₀ (pow_pos hR d).ne', ENNReal.ofReal_one, one_mul]

/-- **The average identity.** -/
lemma aux_hlow_avg_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (η : NativeBilateralPotentialSample d) :
    SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M N (fun _ => -((3 : ℝ) ^ N / 2)) (aux_hlow_Theta d N η) =
      (aux_hlow_mass M N (aux_hlow_pi d η)).toReal := by
  unfold SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage
  have hR : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  rw [aux_hlow_axisCube_eq N, aux_hlow_volume_axisCube N]
  simp_rw [aux_hlow_density_eq M N η]
  rw [aux_hlow_change_of_variables hR
    (fun x => ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) (aux_hlow_pi d η) N x))
    (ENNReal.measurable_ofReal.comp (aux_hlow_continuous_density M N _).measurable)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  unfold aux_hlow_mass
  field_simp

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_measurePreserving_pi (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    MeasurePreserving (aux_hlow_pi d)
      (Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))
      (chaosSampleLaw M).toMeasure :=
  measurePreserving_nativeCopies_commonScaleLaw M

lemma aux_hlow_measurable_mass (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_hlow_mass M N) := by
  unfold aux_hlow_mass
  refine Measurable.lintegral_prod_right' (f := fun p : BilateralField d × SpatialCoordinates d =>
    ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) p.1 N p.2)) ?_
  refine ENNReal.measurable_ofReal.comp ?_
  unfold cutoffSpeedDensity cutoffPotential
  refine Real.measurable_exp.comp (Measurable.sub ?_ measurable_const)
  refine Measurable.add measurable_const (Finset.measurable_sum _ fun j _ => ?_)
  have hev : Measurable (fun q : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d => q.1 q.2) :=
    continuous_eval.measurable
  have h1 : Measurable (fun p : BilateralField d × SpatialCoordinates d => (p.1 (-(Int.ofNat j)), p.2)) :=
    ((measurable_pi_apply (-(Int.ofNat j))).comp measurable_fst).prodMk measurable_snd
  exact hev.comp h1

lemma aux_hlow_measurable_avg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (z : Homogenization.Vec d) :
    Measurable (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M N z) := by
  unfold SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage
  refine Measurable.div_const (Measurable.ennreal_toReal ?_) _
  refine Measurable.lintegral_prod_right'
    (f := fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Homogenization.Vec d =>
      ENNReal.ofReal (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N p.1 p.2)) ?_
  refine ENNReal.measurable_ofReal.comp ?_
  unfold SubdiffusiveProcess.Frozen.Assumptions.aCutoff
  refine Real.measurable_exp.comp (Finset.measurable_sum _ fun k _ => Measurable.sub ?_ measurable_const)
  have hev : Measurable (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d × Homogenization.Vec d => q.1 q.2) := by
    have hc : Continuous (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d × Homogenization.Vec d =>
        q.1.1.1 q.2) :=
      continuous_eval.comp ((continuous_subtype_val.fst.comp continuous_fst).prodMk continuous_snd)
    exact hc.measurable
  have h1 : Measurable (fun p : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Homogenization.Vec d =>
      (p.1 k, p.2)) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  exact hev.comp h1

end Laws



theorem aux_tight_static_hlow_bridge {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ omega, F (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) omega N x)).toReal
      ∂(chaosSampleLaw M).toMeasure =
    ∫⁻ omega', F (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M N (fun _ => -((3 : ℝ) ^ N / 2)) omega')
      ∂M.P.toMeasure := by
  have hpi := aux_hlow_measurePreserving_pi (d := d) M
  have hTh := aux_hlow_measurePreserving_Theta (d := d) M N
  have h1 : Measurable (fun omega : BilateralField d => F (aux_hlow_mass M N omega).toReal) :=
    hF.comp (aux_hlow_measurable_mass M N).ennreal_toReal
  have h2 : Measurable (fun omega' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      F (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M N (fun _ => -((3 : ℝ) ^ N / 2)) omega')) :=
    hF.comp (aux_hlow_measurable_avg M N _)
  change ∫⁻ omega, F (aux_hlow_mass M N omega).toReal ∂(chaosSampleLaw M).toMeasure = _
  rw [← hpi.lintegral_comp h1, ← hTh.lintegral_comp h2]
  refine lintegral_congr fun η => ?_
  show F (aux_hlow_mass M N (aux_hlow_pi d η)).toReal =
    F (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M N (fun _ => -((3 : ℝ) ^ N / 2)) (aux_hlow_Theta d N η))
  rw [aux_hlow_avg_eq M N η]

end Paper
end
end

-- ===== module HLow.Holes =====
section
/-!
# hLow mesh assembly: the cell containment facts (H1)-(H3)
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- **(H1)** Route: `n := Nat.find (∃ n, 3^{-n} ≤ r)` (so `r < 3·3^{-n}`, using `r ≤ 1` when `n = 0`);
`k i := ⌊x i / h⌋` gives `|x i - cc h k i| ≤ h/2` (`HCut.aux_hcut_floor_bounds`), hence
`cell h k ⊆ ball x h ⊆ ball x r` (`HCut.aux_hcut_cell_subset_ball`); the centre lies in the cell, so in
`ball 0 (ρ0/2)`, so `k ∈ aux_hcut_S ρ0 n` (`aux_hcut_mem_S`). -/
lemma aux_hlow_cell_in_ball {rho0 : ℝ} (hrho : 1 ≤ rho0) (x : SpatialCoordinates d) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hsub : Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2)) :
    ∃ n : ℕ, ∃ k ∈ aux_hcut_S (d := d) rho0 n,
      HCut.aux_hcut_cell ((3 : ℝ) ^ n)⁻¹ k ⊆ Metric.ball x r ∧ r < 3 * ((3 : ℝ) ^ n)⁻¹ := by
  classical
  have hex : ∃ n : ℕ, ((3 : ℝ) ^ n)⁻¹ ≤ r := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r⁻¹ (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, by rw [inv_le_comm₀ (by positivity) hr0]; exact hn.le⟩
  set n := Nat.find hex with hndef
  have hn : ((3 : ℝ) ^ n)⁻¹ ≤ r := Nat.find_spec hex
  set h : ℝ := ((3 : ℝ) ^ n)⁻¹ with hhdef
  have hh : 0 < h := by rw [hhdef]; positivity
  obtain ⟨k, hk⟩ := HCut.aux_hcut_exists_closedCell (d := d) hh x
  have hcell : HCut.aux_hcut_cell h k ⊆ Metric.ball x r := by
    intro z hz
    rw [HCut.aux_hcut_mem_cell_iff hh] at hz
    rw [Metric.mem_closedBall, dist_pi_le_iff (half_pos hh).le] at hk
    rw [Metric.mem_ball, dist_pi_lt_iff hr0]
    intro i
    have h1 := hz i
    have h2 := hk i
    rw [Real.dist_eq] at h2 ⊢
    calc |z i - x i| ≤ |z i - HCut.aux_hcut_cc h k i| + |HCut.aux_hcut_cc h k i - x i| := abs_sub_le _ _ _
      _ < h / 2 + h / 2 := by
          have : |HCut.aux_hcut_cc h k i - x i| = |x i - HCut.aux_hcut_cc h k i| := abs_sub_comm _ _
          rw [this]; linarith
      _ = h := by ring
      _ ≤ r := hn
  refine ⟨n, k, ?_, hcell, ?_⟩
  · apply aux_hcut_mem_S hrho
    have hc : HCut.aux_hcut_cc h k ∈ HCut.aux_hcut_cell h k := by
      rw [HCut.aux_hcut_mem_cell_iff hh]; intro i; simp; linarith
    exact Metric.ball_subset_closedBall (hsub (hcell hc))
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; linarith
    · have hmin := Nat.find_min hex (m := n - 1) (by omega)
      have hlt : r < ((3 : ℝ) ^ (n - 1))⁻¹ := lt_of_not_ge hmin
      have e : ((3 : ℝ) ^ (n - 1))⁻¹ = 3 * ((3 : ℝ) ^ n)⁻¹ := by
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        field_simp
      rw [← e]; exact hlt


section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- `cutoffCoefficient` and `cutoffSpeedDensity` differ only by the deterministic `ahom` factor
(literally by `rfl`, since `cutoffCoefficient := ahom⁻¹ * exp(...)` and
`cutoffSpeedDensity := exp(...)` share the exact same `exp(...)` term). -/
private lemma aux_hlow_speedDensity_eq_ahom_mul_coeff (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H om N x =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H om N x := by
  have hCC : cutoffCoefficient M H om N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * cutoffSpeedDensity M H om N x := rfl
  rw [hCC, ← mul_assoc, mul_inv_cancel₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne', one_mul]

/-- The `H`-split, pointwise on a compact `K`: `cutoffSpeedDensity` dominates
`exp(-‖H.restrict K‖) ·` the `H = 0` density, for `x ∈ K`. -/
private lemma aux_hlow_speedDensity_ge_of_mem (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (x : SpatialCoordinates d) (hx : x ∈ (K : Set (SpatialCoordinates d))) :
    Real.exp (-‖(H om).restrict (K : Set (SpatialCoordinates d))‖) *
        cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x ≤
      cutoffSpeedDensity M H om N x := by
  have hEq : cutoffSpeedDensity M H om N x =
      Real.exp (H om x) * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x := by
    unfold cutoffSpeedDensity cutoffPotential
    rw [← Real.exp_add]
    congr 1
    simp only [ContinuousMap.zero_apply, zero_add]
    ring
  have hHx : -‖(H om).restrict (K : Set (SpatialCoordinates d))‖ ≤ H om x := by
    have hb := ContinuousMap.norm_coe_le_norm
      ((H om).restrict (K : Set (SpatialCoordinates d))) (⟨x, hx⟩ : K)
    rw [ContinuousMap.restrict_apply, Real.norm_eq_abs] at hb
    linarith [abs_le.mp hb |>.1]
  have hexp : Real.exp (-‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ≤ Real.exp (H om x) :=
    Real.exp_le_exp.mpr hHx
  have hz0 : 0 ≤ cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x := by
    unfold cutoffSpeedDensity; exact (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_right hexp hz0, hEq]

/-- **(H2)** Level `n ≤ N`. -/
lemma aux_hlow_cell_in (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (y : SpatialCoordinates d) {n N : ℕ} (hnN : n ≤ N) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ d) *
          ENNReal.ofReal (aux_hcut_cellConst M H y n N om *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
            Real.exp (-‖(H (aux_hcut_cellEnv y n om)).restrict
              (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖)) *
          aux_hlow_mass M (N - n) (aux_hcut_cellEnv y n om) ≤
        volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
          (Metric.ball y (((3 : ℝ) ^ n)⁻¹ / 2)) := by
  have hh : (0:ℝ) < ((3 : ℝ) ^ n)⁻¹ := by positivity
  set h : ℝ := ((3 : ℝ) ^ n)⁻¹ with hhdef
  set K : TopologicalSpace.Compacts (SpatialCoordinates d) :=
    closedCube (0 : SpatialCoordinates d) 1 one_pos with hKdef
  filter_upwards [aux_hcut_ae_coeff_cell M Rm hH y hnN] with om hom
  set om' : BilateralField d := aux_hcut_cellEnv y n om with hom'def
  have hcellpos : 0 < aux_hcut_cellConst M H y n N om := aux_hcut_cellConst_pos M Rm H y n N om
  have hratio : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) :=
    div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - n))
  set C : ℝ := aux_hcut_cellConst M H y n N om *
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
      Real.exp (-‖(H om').restrict (K : Set (SpatialCoordinates d))‖) with hCdef
  have hCnonneg : 0 ≤ C := by rw [hCdef]; positivity
  -- the per-point bound, for `x` in the reference cube
  have hpoint : ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      C * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - n) x ≤
        cutoffSpeedDensity M H om N (y + h • x) := by
    intro x hx
    have hxK : x ∈ (K : Set (SpatialCoordinates d)) :=
      centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hx
    have h1 : cutoffCoefficient M H om N (y + h • x) =
        aux_hcut_cellConst M H y n N om * cutoffCoefficient M H om' (N - n) x := hom x
    have h2 : cutoffSpeedDensity M H om N (y + h • x) =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          (aux_hcut_cellConst M H y n N om * cutoffCoefficient M H om' (N - n) x) := by
      rw [← h1]; exact aux_hlow_speedDensity_eq_ahom_mul_coeff M H om N (y + h • x)
    have h3 : cutoffCoefficient M H om' (N - n) x =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n))⁻¹ * cutoffSpeedDensity M H om' (N - n) x := rfl
    have h4 : cutoffSpeedDensity M H om N (y + h • x) =
        aux_hcut_cellConst M H y n N om *
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
          cutoffSpeedDensity M H om' (N - n) x := by
      rw [h2, h3]; ring
    have h5 := aux_hlow_speedDensity_ge_of_mem M H om' (N - n) K x hxK
    have h6 : aux_hcut_cellConst M H y n N om *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
        (Real.exp (-‖(H om').restrict (K : Set (SpatialCoordinates d))‖) *
          cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - n) x) ≤
        aux_hcut_cellConst M H y n N om *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
        cutoffSpeedDensity M H om' (N - n) x :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hcellpos.le hratio.le)
    calc C * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - n) x
        = aux_hcut_cellConst M H y n N om *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
            (Real.exp (-‖(H om').restrict (K : Set (SpatialCoordinates d))‖) *
              cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - n) x) := by
          rw [hCdef]; ring
      _ ≤ aux_hcut_cellConst M H y n N om *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n)) *
            cutoffSpeedDensity M H om' (N - n) x := h6
      _ = cutoffSpeedDensity M H om N (y + h • x) := h4.symm
  -- change of variables
  have hDil : ∀ x : SpatialCoordinates d,
      cubeDilation y (0 : SpatialCoordinates d) h x = y + h • x := by
    intro x; funext i; simp [cubeDilation]
  have hSetEq : (Metric.ball y (h / 2) : Set (SpatialCoordinates d)) =
      (centeredCube y h hh : Set (SpatialCoordinates d)) := rfl
  rw [hSetEq, withDensity_apply _ (centeredCube y h hh).isOpen.measurableSet,
    lintegral_centeredCube_cubeDilation y (0 : SpatialCoordinates d) hh one_pos
      (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))]
  simp only [hDil]
  have hstep1 :
      (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          ENNReal.ofReal (C * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            om' (N - n) x)) =
        ENNReal.ofReal C * aux_hlow_mass M (N - n) om' := by
    rw [show (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          ENNReal.ofReal (C * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            om' (N - n) x)) =
        ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          ENNReal.ofReal C * ENNReal.ofReal
            (cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om' (N - n) x)
      from lintegral_congr fun x => ENNReal.ofReal_mul hCnonneg,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  have hstep2 :
      (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          ENNReal.ofReal (C * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            om' (N - n) x)) ≤
        ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          ENNReal.ofReal (cutoffSpeedDensity M H om N (y + h • x)) :=
    setLIntegral_mono' (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet
      (fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx))
  calc ENNReal.ofReal (h ^ d) * ENNReal.ofReal C * aux_hlow_mass M (N - n) om'
      = ENNReal.ofReal (h ^ d) * (ENNReal.ofReal C * aux_hlow_mass M (N - n) om') := by ring
    _ ≤ ENNReal.ofReal (h ^ d) *
          ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
            ENNReal.ofReal (cutoffSpeedDensity M H om N (y + h • x)) := by
        rw [← hstep1]; exact mul_le_mul_left' hstep2 _

/-- **(H3)** Level `n > N` (any cell side `h ≤ 1`). -/
lemma aux_hlow_cell_out (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H) (N : ℕ)
    (ml : BilateralField d → ℝ)
    (hml : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        ml om ≤ cutoffCoefficient M H om N x)
    (y : SpatialCoordinates d) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ENNReal.ofReal (h ^ d) *
          ENNReal.ofReal (Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            ml (aux_tight_scale_covariance_translate y om)) ≤
        volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
          (Metric.ball y (h / 2)) := by
  filter_upwards [aux_tight_scale_covariance_ae_density_translate hH y N,
    (aux_tight_scale_covariance_measurePreserving_translate M y).quasiMeasurePreserving.ae hml]
    with om htrans hmlT
  set om' : BilateralField d := aux_tight_scale_covariance_translate y om with hom'def
  have hballpt : ∀ z ∈ Metric.ball y (h / 2),
      Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om' ≤
        cutoffSpeedDensity M H om N z := by
    intro z hz
    have hdist : ‖z - y‖ < h / 2 := by
      have := Metric.mem_ball.mp hz
      rwa [dist_eq_norm] at this
    have hxK : (z - y) ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      show dist (z - y) (0 : SpatialCoordinates d) ≤ 1 / 2
      rw [dist_eq_norm, sub_zero]
      linarith
    have heq : y + (z - y) = z := by abel
    have h1 : ml om' ≤ cutoffCoefficient M H om' N (z - y) := hmlT (z - y) hxK
    have h2 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om' ≤
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H om' N (z - y) :=
      mul_le_mul_of_nonneg_left h1 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le
    have h3 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H om' N (z - y) =
        cutoffSpeedDensity M H om' N (z - y) :=
      (aux_hlow_speedDensity_eq_ahom_mul_coeff M H om' N (z - y)).symm
    have h4 : Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om' ≤
        Real.exp (H om y) * cutoffSpeedDensity M H om' N (z - y) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h3 ▸ h2) (Real.exp_pos _).le
    calc Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om'
        ≤ Real.exp (H om y) * cutoffSpeedDensity M H om' N (z - y) := h4
      _ = cutoffSpeedDensity M H om N (y + (z - y)) := (htrans (z - y)).symm
      _ = cutoffSpeedDensity M H om N z := by rw [heq]
  have hvol : volume (Metric.ball y (h / 2)) = ENNReal.ofReal (h ^ d) := centeredCube_volume y hh0
  calc ENNReal.ofReal (h ^ d) *
        ENNReal.ofReal (Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om')
      = ENNReal.ofReal (Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om') *
          volume (Metric.ball y (h / 2)) := by rw [hvol]; ring
    _ = ∫⁻ _z in Metric.ball y (h / 2),
          ENNReal.ofReal (Real.exp (H om y) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * ml om') := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ z in Metric.ball y (h / 2), ENNReal.ofReal (cutoffSpeedDensity M H om N z) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet
          (fun z hz => ENNReal.ofReal_le_ofReal (hballpt z hz))
    _ = volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
          (Metric.ball y (h / 2)) := (withDensity_apply _ Metric.isOpen_ball.measurableSet).symm

end Laws

end Paper
end
end

-- ===== module HLow.Inverse =====
section
/-!
# hLow: inverse moments of the GMC cube average
-/

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace Paper

theorem aux_hlow_inverse_memLp {Omega : Type*} [MeasurableSpace Omega]
    {μ : Measure Omega} [IsProbabilityMeasure μ] {V : Omega → ℝ} {A q : ℝ}
    (hV : Measurable V) (hVpos : ∀ om, 0 < V om)
    (hA : 0 < A) (hq : 0 < q) (hqa : q * A ≤ 1)
    (hX : SubdiffusiveProcess.OGammaLE μ 1 A
      (fun om => |Real.log (V om)| - Real.log 2)) :
    MemLp (fun om => (V om)⁻¹) (ENNReal.ofReal q) μ := by
  let G : Omega → ℝ := fun om =>
    Real.exp (A⁻¹ * max (|Real.log (V om)| - Real.log 2) 0)
  have hGm : Measurable G := by
    dsimp only [G]
    fun_prop
  have hGi : Integrable G μ := by
    simpa only [G, SubdiffusiveProcess.OGammaLE, Real.rpow_one] using hX.1
  have hG : MemLp G 1 μ := memLp_one_iff_integrable.mpr hGi
  have hFm : Measurable (fun om => |(V om)⁻¹| ^ q) := by
    fun_prop
  have hFbound : ∀ om, |(V om)⁻¹| ^ q ≤ (2 : ℝ) ^ q * G om := by
    intro om
    have hV0 : 0 ≤ V om := (hVpos om).le
    have hbase : (V om)⁻¹ ≤ 2 *
        Real.exp (max (|Real.log (V om)| - Real.log 2) 0) := by
      by_cases hsmall : V om ≤ 1 / 2
      · have hlog : Real.log (V om) ≤ Real.log (1 / 2 : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (hVpos om) (by norm_num) hsmall
        have hlog' : Real.log (V om) ≤ -Real.log 2 := by
          simpa [Real.log_div] using hlog
        have hlognonpos : Real.log (V om) ≤ 0 := by
          exact hlog'.trans (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))
        have hneg : 0 ≤ -Real.log (V om) - Real.log 2 := by linarith
        rw [abs_of_nonpos hlognonpos, max_eq_left hneg]
        rw [Real.exp_sub, Real.exp_neg, Real.exp_log (hVpos om),
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        field_simp
        rfl
      · have hhalf : (1 / 2 : ℝ) ≤ V om := le_of_not_ge hsmall
        have hlogabs : |Real.log (V om)| - Real.log 2 ≤
            max (|Real.log (V om)| - Real.log 2) 0 := le_max_left _ _
        have hmax : 1 / V om ≤ 2 * Real.exp (max
            (|Real.log (V om)| - Real.log 2) 0) := by
          have hpos : 0 < Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) := Real.exp_pos _
          have htwo : (1 : ℝ) ≤ 2 * Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) * V om := by
            by_cases hlarge : 0 ≤ |Real.log (V om)| - Real.log 2
            · rw [max_eq_left hlarge]
              calc
                1 ≤ Real.exp (Real.log 2 +
                    (|Real.log (V om)| - Real.log 2) + Real.log (V om)) := by
                  apply Real.one_le_exp
                  nlinarith [neg_le_abs (Real.log (V om))]
                _ = 2 * Real.exp (|Real.log (V om)| - Real.log 2) * V om := by
                  rw [Real.exp_add, Real.exp_add,
                    Real.exp_log (by norm_num : (0 : ℝ) < 2),
                    Real.exp_log (hVpos om)]
            · have hle : |Real.log (V om)| - Real.log 2 ≤ 0 := le_of_not_ge hlarge
              rw [max_eq_right hle]
              simp only [Real.exp_zero]
              nlinarith [hhalf]
          exact (div_le_iff₀ (hVpos om)).2 (by simpa [mul_comm] using htwo)
        simpa [one_div] using hmax
    have hbase_nonneg : 0 ≤ (V om)⁻¹ := inv_nonneg.mpr hV0
    have hexp_nonneg : 0 ≤ Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) := (Real.exp_pos _).le
    have hpow := Real.rpow_le_rpow hbase_nonneg hbase (le_of_lt hq)
    have hqA : q ≤ A⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hA).2
      nlinarith
    have hGpow : Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) ^ q ≤ G om := by
      dsimp only [G]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hmaxnonneg : 0 ≤ max (|Real.log (V om)| - Real.log 2) 0 :=
        le_max_right _ _
      nlinarith
    calc
      |(V om)⁻¹| ^ q ≤ (2 * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0)) ^ q := by
            simpa only [abs_of_nonneg hbase_nonneg] using hpow
      _ = (2 : ℝ) ^ q * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0) ^ q := by
        rw [Real.mul_rpow (by norm_num) hexp_nonneg]
      _ ≤ (2 : ℝ) ^ q * G om := by
        exact mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg (by norm_num) _)
  have hF : MemLp (fun om => |(V om)⁻¹| ^ q) 1 μ := by
    apply (hG.const_mul ((2 : ℝ) ^ q)).of_le hFm.aestronglyMeasurable
    filter_upwards with om
    have hleft : 0 ≤ |(V om)⁻¹| ^ q := Real.rpow_nonneg (abs_nonneg _) _
    have hcoef : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
    have hGnonneg : 0 ≤ G om := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_mul,
      abs_of_nonneg hcoef, abs_of_nonneg hGnonneg] using hFbound om
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  apply (integrable_norm_rpow_iff ((hV.inv).aestronglyMeasurable)
    hq0 hqtop).mp
  simpa only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] using hF.integrable le_rfl

theorem aux_hlow_source_inverse_memLp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p Ctail : ℝ)
    (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)| -
        Real.log 2)) :
    MemLp (fun omega ↦ (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹)
    (ENNReal.ofReal p) M.P.toMeasure := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog : Real.log M.delta ≠ 0 := by
    exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
      (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    positivity
  exact aux_hlow_inverse_memLp
    (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m)
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m)
    hA hp hsmall hsource

theorem aux_hlow_source_inverse_uniform
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) :
    ∃ delta0 Ctail : ℝ, 0 < delta0 ∧ 0 < Ctail ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ m : ℕ,
        p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1 →
        MemLp (fun omega ↦
          (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹)
          (ENNReal.ofReal p) M.P.toMeasure := by
  obtain ⟨Ctail, delta0, hCtail, hdelta0, hsource⟩ :=
    SubdiffusiveProcess.Section9.exists_cutoffOriginCube_logAbs_ogamma d
  refine ⟨delta0, Ctail, hdelta0, hCtail, ?_⟩
  intro M hM m hsmall
  exact aux_hlow_source_inverse_memLp hd M m p Ctail hp hCtail hsmall
    (hsource M hM m)

theorem aux_hlow_inverse_integral_bound {Omega : Type*} [MeasurableSpace Omega]
    {μ : Measure Omega} [IsProbabilityMeasure μ] {V : Omega → ℝ} {A q : ℝ}
    (hV : Measurable V) (hVpos : ∀ om, 0 < V om)
    (hA : 0 < A) (hq : 0 < q) (hqa : q * A ≤ 1)
    (hX : SubdiffusiveProcess.OGammaLE μ 1 A
      (fun om => |Real.log (V om)| - Real.log 2)) :
    ∫ om, |(V om)⁻¹| ^ q ∂μ ≤ (2 : ℝ) ^ q * 2 := by
  let G : Omega → ℝ := fun om =>
    Real.exp (A⁻¹ * max (|Real.log (V om)| - Real.log 2) 0)
  have hGm : Measurable G := by
    dsimp only [G]
    fun_prop
  have hGi : Integrable G μ := by
    simpa only [G, SubdiffusiveProcess.OGammaLE, Real.rpow_one] using hX.1
  have hFm : Measurable (fun om => |(V om)⁻¹| ^ q) := by
    fun_prop
  have hFbound : ∀ om, |(V om)⁻¹| ^ q ≤ (2 : ℝ) ^ q * G om := by
    intro om
    have hV0 : 0 ≤ V om := (hVpos om).le
    have hbase : (V om)⁻¹ ≤ 2 *
        Real.exp (max (|Real.log (V om)| - Real.log 2) 0) := by
      by_cases hsmall : V om ≤ 1 / 2
      · have hlog : Real.log (V om) ≤ Real.log (1 / 2 : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (hVpos om) (by norm_num) hsmall
        have hlog' : Real.log (V om) ≤ -Real.log 2 := by
          simpa [Real.log_div] using hlog
        have hlognonpos : Real.log (V om) ≤ 0 := by
          exact hlog'.trans (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))
        have hneg : 0 ≤ -Real.log (V om) - Real.log 2 := by linarith
        rw [abs_of_nonpos hlognonpos, max_eq_left hneg]
        rw [Real.exp_sub, Real.exp_neg, Real.exp_log (hVpos om),
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        field_simp
        rfl
      · have hhalf : (1 / 2 : ℝ) ≤ V om := le_of_not_ge hsmall
        have hmax : 1 / V om ≤ 2 * Real.exp (max
            (|Real.log (V om)| - Real.log 2) 0) := by
          have hpos : 0 < Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) := Real.exp_pos _
          have htwo : (1 : ℝ) ≤ 2 * Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) * V om := by
            by_cases hlarge : 0 ≤ |Real.log (V om)| - Real.log 2
            · rw [max_eq_left hlarge]
              calc
                1 ≤ Real.exp (Real.log 2 +
                    (|Real.log (V om)| - Real.log 2) + Real.log (V om)) := by
                  apply Real.one_le_exp
                  nlinarith [neg_le_abs (Real.log (V om))]
                _ = 2 * Real.exp (|Real.log (V om)| - Real.log 2) * V om := by
                  rw [Real.exp_add, Real.exp_add,
                    Real.exp_log (by norm_num : (0 : ℝ) < 2),
                    Real.exp_log (hVpos om)]
            · have hle : |Real.log (V om)| - Real.log 2 ≤ 0 := le_of_not_ge hlarge
              rw [max_eq_right hle]
              simp only [Real.exp_zero]
              nlinarith [hhalf]
          exact (div_le_iff₀ (hVpos om)).2 (by simpa [mul_comm] using htwo)
        simpa [one_div] using hmax
    have hbase_nonneg : 0 ≤ (V om)⁻¹ := inv_nonneg.mpr hV0
    have hexp_nonneg : 0 ≤ Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) := (Real.exp_pos _).le
    have hpow := Real.rpow_le_rpow hbase_nonneg hbase (le_of_lt hq)
    have hqA : q ≤ A⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hA).2
      nlinarith
    have hGpow : Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) ^ q ≤ G om := by
      dsimp only [G]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hmaxnonneg : 0 ≤ max (|Real.log (V om)| - Real.log 2) 0 :=
        le_max_right _ _
      nlinarith
    calc
      |(V om)⁻¹| ^ q ≤ (2 * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0)) ^ q := by
            simpa only [abs_of_nonneg hbase_nonneg] using hpow
      _ = (2 : ℝ) ^ q * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0) ^ q := by
        rw [Real.mul_rpow (by norm_num) hexp_nonneg]
      _ ≤ (2 : ℝ) ^ q * G om := by
        exact mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg (by norm_num) _)
  have hFint : Integrable (fun om => |(V om)⁻¹| ^ q) μ := by
    apply hGi.const_mul ((2 : ℝ) ^ q) |>.mono' hFm.aestronglyMeasurable
    filter_upwards with om
    have hleft : 0 ≤ |(V om)⁻¹| ^ q := Real.rpow_nonneg (abs_nonneg _) _
    have hcoef : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
    have hGnonneg : 0 ≤ G om := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_mul,
      abs_of_nonneg hcoef, abs_of_nonneg hGnonneg] using hFbound om
  calc
    ∫ om, |(V om)⁻¹| ^ q ∂μ ≤ ∫ om, (2 : ℝ) ^ q * G om ∂μ :=
      integral_mono_ae hFint
        (hGi.const_mul ((2 : ℝ) ^ q)) (Filter.Eventually.of_forall hFbound)
    _ = (2 : ℝ) ^ q * ∫ om, G om ∂μ := integral_const_mul _ _
    _ ≤ (2 : ℝ) ^ q * 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      simpa only [G, Real.rpow_one] using hX.2

theorem aux_hlow_source_inverse_integral_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p Ctail : ℝ)
    (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)| -
        Real.log 2)) :
    ∫ omega, |(SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹| ^ p
      ∂M.P.toMeasure ≤ (2 : ℝ) ^ p * 2 := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog : Real.log M.delta ≠ 0 := by
    exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
      (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    positivity
  exact aux_hlow_inverse_integral_bound
    (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m)
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m)
    hA hp hsmall hsource

theorem aux_hlow_translated_source_inverse_integral_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (z : Homogenization.Vec d) (p Ctail : ℝ) (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦
        |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega)| -
          Real.log 2)) :
    ∫ omega, |(SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega)⁻¹| ^ p
      ∂M.P.toMeasure ≤ (2 : ℝ) ^ p * 2 := by
  let c : Homogenization.Vec d := fun i ↦ z i + (3 : ℝ) ^ m / 2
  have heq : SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z =
      SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m ∘
        SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence c := by
    funext omega
    exact SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage_eq_origin_translate M m z omega
  have hmeas : Measurable (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z) := by
    rw [heq]
    exact (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m).comp
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence c)
  have hpos : ∀ omega, 0 < SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega := by
    intro omega
    rw [heq]
    exact SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m _
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have hlog : Real.log M.delta ≠ 0 := by
      exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
        (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
    positivity
  exact aux_hlow_inverse_integral_bound hmeas hpos hA hp hsmall hsource


theorem aux_hlow_log_square_threshold (q Ctail : ℝ) (hq : 0 < q)
    (hCtail : 0 < Ctail) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        q * (Ctail * delta ^ 2 * |Real.log delta| ^ 2) ≤ 1 := by
  let A : ℝ := q * Ctail
  have hA : 0 < A := mul_pos hq hCtail
  have hAplus : 0 < A + 1 := by linarith
  obtain ⟨delta0, hdelta0, _, hcal⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_smallDelta_mul_abs_log_le
      (eps := (A + 1)⁻¹) (by positivity)
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hle
  have hcal' := hcal delta hdelta hle
  have hcal_nonneg : 0 ≤ delta * |Real.log delta| := by positivity
  have hcal_rhs_nonneg : 0 ≤ (A + 1)⁻¹ := inv_nonneg.mpr hAplus.le
  have hsq : (delta * |Real.log delta|) ^ 2 ≤ ((A + 1)⁻¹) ^ 2 := by
    nlinarith [sq_nonneg (delta * |Real.log delta| - (A + 1)⁻¹)]
  have hbound : A * ((A + 1)⁻¹) ^ 2 ≤ 1 := by
    rw [inv_pow]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos hAplus)).2
    nlinarith [sq_nonneg A]
  dsimp only [A] at hA hbound ⊢
  calc
    q * (Ctail * delta ^ 2 * |Real.log delta| ^ 2) =
        (q * Ctail) * (delta * |Real.log delta|) ^ 2 := by ring
    _ ≤ (q * Ctail) * ((q * Ctail + 1)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hA.le
    _ ≤ 1 := hbound


end Paper
end
end

-- ===== module HLow.Mom =====
section
/-!
# hLow: per-cell weights and their moments
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- `ahom n / ahom m ≤ exp (2 τ² (m - n))` for `n ≤ m`. -/
lemma aux_hlow_ahom_ratio_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n m : ℕ} (hnm : n ≤ m) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M n / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ahom_ratio_eq_exp_normalizerLogError M m n]
  have herr := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_normalizerLogError_le_of_le M hnm
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 herr).2
  linarith

/-- The unit compact. -/
def aux_hlow_K (d : ℕ) : TopologicalSpace.Compacts (SpatialCoordinates d) :=
  closedCube (0 : SpatialCoordinates d) 1 one_pos

/-- Level-`n ≤ N` cell weight (without the geometric factor `h^{1/2}`). -/
def aux_hlow_Vin (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N n : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
    ((aux_hcut_cellConst M H y n N om)⁻¹ *
      (Real.exp ‖(H (aux_hcut_cellEnv y n om)).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖ *
        ((aux_hlow_mass M (N - n) (aux_hcut_cellEnv y n om)).toReal)⁻¹))

/-- Level-`n > N` cell weight. -/
def aux_hlow_Vout (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ml : BilateralField d → ℝ) (N : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  aux_hcoer_Kout H ml (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ y om

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_measurable_normH {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hHm : Measurable H) :
    Measurable (fun om => ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖) :=
  (continuous_norm.comp (ContinuousMap.continuous_restrict (aux_hlow_K d : Set (SpatialCoordinates d)))).measurable.comp hHm

/-- `cellConst⁻¹` envelope, all levels. -/
lemma aux_hlow_cellConst_inv_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) (n N : ℕ)
    (om : BilateralField d) :
    (aux_hcut_cellConst M H y n N om)⁻¹ ≤
      Real.exp (|H om y|) * aux_prop_growth_large_root_shiftEnv M n (aux_hcut_cellEnv y n om) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold aux_hcut_cellConst aux_prop_growth_large_root_shiftConst aux_prop_growth_large_root_shiftEnv
    simp only [Nat.sub_zero, add_zero, Nat.cast_zero, zero_mul, aux_prop_growth_large_root_irAnchor,
      Finset.range_zero, Finset.sum_empty, sub_zero, abs_zero, Real.exp_zero, mul_one]
    have hpos := aux_prop_growth_large_root_ahom_pos_of M Rm N
    rw [div_self hpos.ne', inv_one, mul_one, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (neg_le_abs _)
  · exact aux_hcoer_cellConst_inv_le M Rm H y hn om

end Laws

end Paper
end
end

-- ===== module HLow.Mom2 =====
section
/-!
# hLow: moments of the per-cell weights
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_avg_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (z : Homogenization.Vec d)
    (om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 < SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z om := by
  rw [SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage_eq_origin_translate M m z om]
  exact SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m _

/-- **Inverse moment of the unit mass**, uniform in the cutoff. -/
lemma aux_hlow_mass_inv_moment (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (r : ℝ)
    (hr : 0 < r) (Ctail : ℝ) (hCtail : 0 < Ctail)
    (hsmall : r * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M k
        (fun _ => -((3 : ℝ) ^ k / 2)) omega)| - Real.log 2)) :
    ∫⁻ om, ENNReal.ofReal (((aux_hlow_mass M k om).toReal)⁻¹ ^ r) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 : ℝ) ^ r * 2) := by
  set z : Homogenization.Vec d := fun _ => -((3 : ℝ) ^ k / 2) with hz
  have hF : Measurable (fun t : ℝ => ENNReal.ofReal (|t⁻¹| ^ r)) :=
    ENNReal.measurable_ofReal.comp ((measurable_inv.abs).pow_const r)
  have hb := aux_tight_static_hlow_bridge hd M k (fun t : ℝ => ENNReal.ofReal (|t⁻¹| ^ r)) hF
  have hL : ∫⁻ om, ENNReal.ofReal (((aux_hlow_mass M k om).toReal)⁻¹ ^ r) ∂(chaosSampleLaw M).toMeasure =
      ∫⁻ om, ENNReal.ofReal (|((aux_hlow_mass M k om).toReal)⁻¹| ^ r) ∂(chaosSampleLaw M).toMeasure := by
    refine lintegral_congr fun om => ?_
    rw [abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)]
  rw [hL]
  change _ = _ at hb
  unfold aux_hlow_mass
  rw [hb]
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have hlog : Real.log M.delta ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hdelta (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num)))
    positivity
  have hmem := aux_hlow_inverse_memLp (aux_hlow_measurable_avg M k z) (aux_hlow_avg_pos M k z) hA hr hsmall
    hsource
  have hint : Integrable (fun om => |(SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M k z om)⁻¹| ^ r)
      M.P.toMeasure := by
    have := hmem.integrable_norm_rpow (by simpa using hr) (by simp)
    refine this.congr (Eventually.of_forall fun om => ?_)
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hr.le]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (aux_hlow_translated_source_inverse_integral_bound hd M k z r Ctail hr hCtail hsmall hsource)

end Paper
end
end

-- ===== module HLow.Mom3 =====
section
/-!
# hLow: moments of `Vin` and `Vout`
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_four_roots (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) :
    (ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal b ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal e ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (a ^ (1 / 4 : ℝ) * b ^ (1 / 4 : ℝ) * c ^ (1 / 4 : ℝ) * e ^ (1 / 4 : ℝ)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), ENNReal.ofReal_rpow_of_nonneg hb (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), ENNReal.ofReal_rpow_of_nonneg he (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-- **Moment of `Vin`.** -/
lemma aux_hlow_Vin_moment (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (R CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (CK : ℝ) (hCK : ∀ (lam : ℝ), 0 ≤ lam →
        Integrable (fun om => Real.exp (lam * ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖))
          (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖)
          ∂(chaosSampleLaw M).toMeasure ≤ 2 * Real.exp (CK * lam ^ 2 * M.delta ^ 2))
    (y : SpatialCoordinates d) (hy : ‖y‖ ≤ R) {n N : ℕ} (hnN : n ≤ N) (p : ℝ) (hp : 1 ≤ p)
    (Ctail : ℝ) (hCtail : 0 < Ctail)
    (hsmall4 : (4 * p) * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : ∀ k : ℕ, SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M k
        (fun _ => -((3 : ℝ) ^ k / 2)) omega)| - Real.log 2))
    (hsmall : Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2)
    (htau : Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ 2) :
    ∫⁻ om, ENNReal.ofReal (aux_hlow_Vin M H N n y om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * 2 *
        (2 * Real.exp (CK * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ (4 * p) * 2) ^ (1 / 4 : ℝ) *
          8 ^ n) := by
  have hp0 : 0 < p := by linarith
  set ratio := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N with hratio
  have hratio0 : 0 ≤ ratio := div_nonneg (aux_prop_growth_large_root_ahom_pos_of M Rm _).le
    (aux_prop_growth_large_root_ahom_pos_of M Rm _).le
  set Kf : BilateralField d → ℝ := fun om' =>
    Real.exp ‖(H om').restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖ *
      ((aux_hlow_mass M (N - n) om').toReal)⁻¹ with hKf
  have hKfm : Measurable Kf :=
    (aux_hlow_measurable_normH hH.1).exp.mul (aux_hlow_measurable_mass M (N - n)).ennreal_toReal.inv
  have hKf0 : ∀ om', 0 ≤ Kf om' := fun om' =>
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 ENNReal.toReal_nonneg)
  have hZm : Measurable (fun om => (aux_hcut_cellConst M H y n N om)⁻¹) :=
    (aux_hcut_measurable_cellConst M hH y n N).inv
  have hZ0 : ∀ om, 0 ≤ (aux_hcut_cellConst M H y n N om)⁻¹ := fun om =>
    inv_nonneg.2 (aux_hcut_cellConst_pos M Rm H y n N om).le
  -- EH
  obtain ⟨hint, hbd⟩ := hCH (4 * p) (by positivity) y hy
  have hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (4 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hZ := aux_hcoer_Z_moment M hH y n _ hZm hZ0 (fun om => aux_hlow_cellConst_inv_le M Rm H y n N om)
    Kf hKfm hKf0 p hp _ hEH
  -- K moment
  obtain ⟨hintK, hbdK⟩ := hCK (4 * p) (by positivity)
  have hK2 : ∫⁻ om, ENNReal.ofReal (Kf om ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (2 * Real.exp (CK * (4 * p) ^ 2 * M.delta ^ 2))) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ((2 : ℝ) ^ (4 * p) * 2)) ^ (1 / 2 : ℝ) := by
    have hcs := aux_hcut_cs_ofReal (chaosSampleLaw M).toMeasure
      (fun om => Real.exp ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖)
      (fun om => ((aux_hlow_mass M (N - n) om).toReal)⁻¹) (aux_hlow_measurable_normH hH.1).exp
      (aux_hlow_measurable_mass M (N - n)).ennreal_toReal.inv (fun om => (Real.exp_pos _).le)
      (fun om => inv_nonneg.2 ENNReal.toReal_nonneg) (2 * p) (by positivity)
    refine hcs.trans ?_
    gcongr
    · have e1 : ∫⁻ om, ENNReal.ofReal
            (Real.exp ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖ ^ (2 * (2 * p)))
            ∂(chaosSampleLaw M).toMeasure =
          ∫⁻ om, ENNReal.ofReal
            (Real.exp (4 * p * ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖))
            ∂(chaosSampleLaw M).toMeasure := by
        refine lintegral_congr fun om => ?_
        rw [← Real.exp_mul]; ring_nf
      rw [e1, ← ofReal_integral_eq_lintegral_ofReal hintK (Eventually.of_forall fun om => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hbdK
    · have h4 : (2 : ℝ) * (2 * p) = 4 * p := by ring
      rw [h4]
      exact aux_hlow_mass_inv_moment hd M (N - n) (4 * p) (by positivity) Ctail hCtail hsmall4 (hsource _)
  -- assemble
  have hpt : ∀ om, ENNReal.ofReal (aux_hlow_Vin M H N n y om ^ p) =
      ENNReal.ofReal (ratio ^ p) *
        ENNReal.ofReal (((aux_hcut_cellConst M H y n N om)⁻¹ * Kf (aux_hcut_cellEnv y n om)) ^ p) := by
    intro om
    unfold aux_hlow_Vin
    rw [← hratio, Real.mul_rpow hratio0 (mul_nonneg (hZ0 om) (hKf0 _)), ENNReal.ofReal_mul (by positivity)]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_left' hZ _).trans ?_
  have hS : ENNReal.ofReal (2 * (2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 +
      (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) ^ n) ≤ ENNReal.ofReal (2 * 4 ^ n) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 4 := by
      linarith
    gcongr
  refine (mul_le_mul_left' (mul_le_mul' (ENNReal.rpow_le_rpow (mul_le_mul_left'
    (ENNReal.rpow_le_rpow hS (by norm_num)) _) (by norm_num))
    (ENNReal.rpow_le_rpow hK2 (by norm_num))) _).trans ?_
  rw [aux_hlow_four_roots _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hratio0 _)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- ratio^p ≤ 2^n and (2·4^n)^{1/4} ≤ 2^{1/4} (√2)^n; 2^n (√2)^n ≤ 3^n
  have hr : ratio ^ p ≤ 2 ^ n := by
    have h1 := aux_hlow_ahom_ratio_le M (Nat.sub_le N n)
    rw [← hratio, Nat.sub_sub_self hnN] at h1
    calc ratio ^ p ≤ (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (n : ℝ))) ^ p :=
          Real.rpow_le_rpow hratio0 h1 hp0.le
      _ = Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ^ n := by
          rw [← Real.exp_mul, ← Real.exp_nat_mul]; ring_nf
      _ ≤ 2 ^ n := pow_le_pow_left₀ (Real.exp_pos _).le htau n
  have h4 : (2 * (4 : ℝ) ^ n) ^ (1 / 4 : ℝ) ≤ 2 * 4 ^ n := by
    have h1 : (1 : ℝ) ≤ 2 * 4 ^ n := by
      have := one_le_pow₀ (M₀ := ℝ) (a := 4) (by norm_num) (n := n); linarith
    calc (2 * (4 : ℝ) ^ n) ^ (1 / 4 : ℝ) ≤ (2 * (4 : ℝ) ^ n) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = 2 * 4 ^ n := Real.rpow_one _
  set a := (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ)
  set c := (2 * Real.exp (CK * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ)
  set e := ((2 : ℝ) ^ (4 * p) * 2) ^ (1 / 4 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hc : 0 ≤ c := by positivity
  have he : 0 ≤ e := by positivity
  have h8 : (2 : ℝ) ^ n * 4 ^ n = 8 ^ n := by rw [← mul_pow]; norm_num
  calc ratio ^ p * (a * (2 * (4 : ℝ) ^ n) ^ (1 / 4 : ℝ) * c * e)
      ≤ 2 ^ n * (a * (2 * 4 ^ n) * c * e) := by gcongr
    _ = a * 2 * c * e * (2 ^ n * 4 ^ n) := by ring
    _ = a * 2 * c * e * 8 ^ n := by rw [h8]

/-- **Moment of `Vout`.** -/
lemma aux_hlow_Vout_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (R CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ R →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (y : SpatialCoordinates d) (hy : ‖y‖ ≤ R) (ml : BilateralField d → ℝ) (hmlm : Measurable ml)
    (hml0 : ∀ om, 0 < ml om) (N : ℕ) (p : ℝ) (hp : 1 ≤ p) (Cml : ℝ) (hCml : 0 ≤ Cml)
    (hmlmom : ∫⁻ om, ENNReal.ofReal ((ml om)⁻¹ ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cml * 81 ^ N))
    (htau : Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ 2) :
    ∫⁻ om, ENNReal.ofReal (aux_hlow_Vout M H ml N y om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p *
        (2 * Real.exp (CH * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) * Cml ^ (1 / 2 : ℝ) * 18 ^ N) := by
  have hp0 : 0 < p := by linarith
  have ha0 := aux_prop_growth_large_root_ahom_pos_of M Rm 0
  have haN := aux_prop_growth_large_root_ahom_pos_of M Rm N
  obtain ⟨hint, hbd⟩ := hCH (2 * p) (by positivity) y hy
  have hEH : ∫⁻ om, ENNReal.ofReal (Real.exp (2 * p * |H om y|)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Real.exp (CH * (2 * p) ^ 2 * M.delta ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun om => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbd
  have h := aux_hcoer_Kout_moment M hH y ml hmlm hml0 (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
    (inv_nonneg.2 haN.le) p hp _ _ hEH hmlmom
  unfold aux_hlow_Vout
  refine h.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK : ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) ^ p ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p * 2 ^ N := by
    have h1 := aux_hlow_ahom_ratio_le M (Nat.zero_le N)
    rw [Nat.sub_zero] at h1
    have h2 : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (N : ℝ)) := by
      rw [div_le_iff₀ haN] at h1
      rw [inv_le_iff_one_le_mul₀ haN]
      calc (1 : ℝ) = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 := by
            field_simp
        _ ≤ _ := by
            rw [mul_assoc]; gcongr
    calc ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) ^ p
        ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ *
            Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (N : ℝ))) ^ p :=
          Real.rpow_le_rpow (inv_nonneg.2 haN.le) h2 hp0.le
      _ = ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p *
            Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ^ N := by
          rw [Real.mul_rpow (inv_nonneg.2 ha0.le) (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_nat_mul]
          congr 2; ring
      _ ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p * 2 ^ N := by
          gcongr
  have h81 : (Cml * 81 ^ N) ^ (1 / 2 : ℝ) = Cml ^ (1 / 2 : ℝ) * 9 ^ N := by
    rw [Real.mul_rpow hCml (by positivity)]
    congr 1
    rw [show (81 : ℝ) ^ N = (9 ^ N) ^ (2 : ℝ) by rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]; norm_num,
      ← Real.rpow_mul (by positivity)]
    norm_num
  rw [h81]
  have h18 : (2 : ℝ) ^ N * 9 ^ N = 18 ^ N := by rw [← mul_pow]; norm_num
  set A := (2 * Real.exp (CH * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ)
  have hA : 0 ≤ A := by positivity
  calc ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) ^ p * (A * (Cml ^ (1 / 2 : ℝ) * 9 ^ N))
      ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p * 2 ^ N * (A * (Cml ^ (1 / 2 : ℝ) * 9 ^ N)) := by
        gcongr
    _ = ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p * A * Cml ^ (1 / 2 : ℝ) * (2 ^ N * 9 ^ N) := by ring
    _ = _ := by rw [h18]

end Paper
end
end

-- ===== module HLow.Sum =====
section
/-!
# hLow: the weighted supremum over grid cells and its moment
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- Unified cell weight. -/
def aux_hlow_V (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ml : ℕ → BilateralField d → ℝ) (N n : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  if n ≤ N then aux_hlow_Vin M H N n y om else aux_hlow_Vout M H (ml N) N y om

/-- The cell term. -/
def aux_hlow_T (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ml : ℕ → BilateralField d → ℝ) (N : ℕ) (rho0 : ℝ) (n : ℕ) (k : Fin d → ℤ) (om : BilateralField d) :
    ℝ≥0∞ := by
  classical
  exact if k ∈ aux_hcut_S (d := d) rho0 n then
    ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ (1 / 2 : ℝ) *
      aux_hlow_V M H ml N n (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) om)
  else 0

/-- The weighted supremum. -/
def aux_hlow_KE (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ml : ℕ → BilateralField d → ℝ) (N : ℕ) (rho0 : ℝ) (om : BilateralField d) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ k : Fin d → ℤ, aux_hlow_T M H ml N rho0 n k om

lemma aux_hlow_geom (rho0 : ℝ) (hrho : 1 ≤ rho0) {p : ℝ} (hp : 2 * (d : ℝ) + 8 ≤ p) (n : ℕ) :
    ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * 18 ^ n ≤
      (2 * rho0 + 3) ^ d * (1 / 4) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hinv : ((3 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hexp : (((3 : ℝ) ^ n)⁻¹) ^ (p / 2) ≤ (((3 : ℝ) ^ n)⁻¹) ^ ((d + 4 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) hinv (by push_cast; linarith)
  rw [Real.rpow_natCast] at hexp
  have hC : (0 : ℝ) ≤ (2 * rho0 + 3) ^ d := by positivity
  calc ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * 18 ^ n
      ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ (d + 4) * 18 ^ n := by gcongr
    _ = (2 * rho0 + 3) ^ d * (18 ^ n * ((((3 : ℝ) ^ n)⁻¹) ^ 4)) := by
        rw [mul_pow, pow_add]
        have e : ((3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ d = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ h3.ne', one_pow]
        calc (2 * rho0 + 3) ^ d * ((3 : ℝ) ^ n) ^ d * ((((3 : ℝ) ^ n)⁻¹) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ 4) * 18 ^ n
            = (2 * rho0 + 3) ^ d * (((3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ d) *
                ((((3 : ℝ) ^ n)⁻¹) ^ 4 * 18 ^ n) := by ring
          _ = _ := by rw [e]; ring
    _ = (2 * rho0 + 3) ^ d * (18 / 81) ^ n := by
        congr 1
        have e81 : (((3 : ℝ) ^ n)⁻¹) ^ 4 = ((81 : ℝ) ^ n)⁻¹ := by
          rw [inv_pow, ← pow_mul, show (81 : ℝ) = 3 ^ 4 by norm_num, ← pow_mul, mul_comm n 4]
        rw [e81, div_pow, div_eq_mul_inv]
    _ ≤ (2 * rho0 + 3) ^ d * (1 / 4) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) n) hC

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_measurable_V (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (N n : ℕ) (y : SpatialCoordinates d) :
    Measurable (aux_hlow_V M H ml N n y) := by
  unfold aux_hlow_V
  split_ifs
  · unfold aux_hlow_Vin
    refine measurable_const.mul ((aux_hcut_measurable_cellConst M hH y n N).inv.mul ?_)
    exact ((aux_hlow_measurable_normH hH.1).exp.mul
      (aux_hlow_measurable_mass M (N - n)).ennreal_toReal.inv).comp (aux_hcut_measurable_cellEnv M y n)
  · unfold aux_hlow_Vout aux_hcoer_Kout
    have hHy : Measurable fun om => H om y := (continuous_eval_const y).measurable.comp hH.1
    exact measurable_const.mul ((hHy.exp.mul ((hmlm N).comp (aux_hcoer_measurable_translate M y))).inv)

lemma aux_hlow_measurable_KE (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (N : ℕ) (rho0 : ℝ) :
    Measurable (aux_hlow_KE M H ml N rho0) := by
  classical
  unfold aux_hlow_KE
  refine Measurable.iSup fun n => Measurable.iSup fun k => ?_
  unfold aux_hlow_T
  split_ifs
  · exact ENNReal.measurable_ofReal.comp (measurable_const.mul (aux_hlow_measurable_V M hH ml hmlm N n _))
  · exact measurable_const

/-- **Moment of the weighted supremum**, given a uniform per-cell moment `Ccell · 18^n`. -/
lemma aux_hlow_KE_moment (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (N : ℕ) {rho0 : ℝ} (hrho : 1 ≤ rho0)
    {p : ℝ} (hp : 2 * (d : ℝ) + 8 ≤ p) (hV0 : ∀ n y om, 0 ≤ aux_hlow_V M H ml N n y om)
    (Ccell : ℝ) (hCcell : 0 ≤ Ccell)
    (hcell : ∀ n (y : SpatialCoordinates d), ‖y‖ ≤ rho0 →
      ∫⁻ om, ENNReal.ofReal (aux_hlow_V M H ml N n y om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Ccell * 18 ^ n)) :
    ∫⁻ om, aux_hlow_KE M H ml N rho0 om ^ p ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (2 * rho0 + 3) ^ d * Ccell) := by
  classical
  have hp0 : 0 < p := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  set F : ℕ → (Fin d → ℤ) → BilateralField d → ℝ≥0∞ := fun n k om => aux_hlow_T M H ml N rho0 n k om ^ p
    with hFdef
  have hFm : ∀ n k, Measurable (F n k) := by
    intro n k
    refine Measurable.pow_const ?_ p
    unfold aux_hlow_T
    split_ifs
    · exact ENNReal.measurable_ofReal.comp (measurable_const.mul (aux_hlow_measurable_V M hH ml hmlm N n _))
    · exact measurable_const
  have hpt : ∀ om, aux_hlow_KE M H ml N rho0 om ^ p ≤ ∑' n, ∑' k, F n k om := by
    intro om
    set X := ∑' n, ∑' k, F n k om
    have hle : aux_hlow_KE M H ml N rho0 om ≤ X ^ p⁻¹ := by
      unfold aux_hlow_KE
      refine iSup_le fun n => iSup_le fun k => ?_
      have e : aux_hlow_T M H ml N rho0 n k om = (F n k om) ^ p⁻¹ := by
        simp only [hFdef]; rw [ENNReal.rpow_rpow_inv hp0.ne']
      rw [e]
      exact ENNReal.rpow_le_rpow ((ENNReal.le_tsum k).trans
        (ENNReal.le_tsum (f := fun n => ∑' k, F n k om) n)) (by positivity)
    calc aux_hlow_KE M H ml N rho0 om ^ p ≤ (X ^ p⁻¹) ^ p := ENNReal.rpow_le_rpow hle hp0.le
      _ = X := ENNReal.rpow_inv_rpow hp0.ne' X
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun n => (Measurable.ennreal_tsum fun k => hFm n k).aemeasurable]
  simp_rw [lintegral_tsum fun k => (hFm _ k).aemeasurable]
  have hlevel : ∀ n, ∑' k, ∫⁻ om, F n k om ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((2 * rho0 + 3) ^ d * Ccell * (1 / 4) ^ n) := by
    intro n
    have hzero : ∀ k ∉ aux_hcut_S (d := d) rho0 n, ∫⁻ om, F n k om ∂(chaosSampleLaw M).toMeasure = 0 := by
      intro k hk
      refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun om => ?_)
      simp only [hFdef, aux_hlow_T, hk, if_false, Pi.zero_apply]
      exact ENNReal.zero_rpow_of_pos hp0
    rw [tsum_eq_sum hzero]
    have hper : ∀ k ∈ aux_hcut_S (d := d) rho0 n, ∫⁻ om, F n k om ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * (Ccell * 18 ^ n)) := by
      intro k hk
      have hy : ‖HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k‖ ≤ rho0 := by
        have h : HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k ∈ Metric.closedBall (0 : SpatialCoordinates d) (rho0 / 2) := by
          unfold aux_hcut_S at hk
          exact (Finset.mem_filter.1 hk).2
        rw [Metric.mem_closedBall, dist_zero_right] at h
        linarith
      have e : ∀ om, F n k om = ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ (p / 2)) *
          ENNReal.ofReal (aux_hlow_V M H ml N n (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) om ^ p) := by
        intro om
        simp only [hFdef, aux_hlow_T, hk, if_true]
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) (hV0 _ _ _)) hp0.le,
          Real.mul_rpow (by positivity) (hV0 _ _ _), ← Real.rpow_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul_left' (hcell n _ hy) _).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
    refine (Finset.sum_le_sum hper).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard := aux_hcut_card_S (d := d) (by linarith : (0 : ℝ) ≤ rho0) n
    have hg := aux_hlow_geom rho0 hrho hp n
    calc ((aux_hcut_S (d := d) rho0 n).card : ℝ) * ((((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * (Ccell * 18 ^ n))
        ≤ ((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * ((((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * (Ccell * 18 ^ n)) := by
          gcongr
      _ = (((2 * rho0 + 3) * (3 : ℝ) ^ n) ^ d * (((3 : ℝ) ^ n)⁻¹) ^ (p / 2) * 18 ^ n) * Ccell := by ring
      _ ≤ ((2 * rho0 + 3) ^ d * (1 / 4) ^ n) * Ccell := by gcongr
      _ = (2 * rho0 + 3) ^ d * Ccell * (1 / 4) ^ n := by ring
  refine (ENNReal.tsum_le_tsum hlevel).trans ?_
  have hC0 : 0 ≤ (2 * rho0 + 3) ^ d * Ccell := by have : (0 : ℝ) ≤ 2 * rho0 + 3 := by linarith
                                                  positivity
  have hs : ∑' n : ℕ, ENNReal.ofReal ((2 * rho0 + 3) ^ d * Ccell * (1 / 4) ^ n) =
      ENNReal.ofReal ((2 * rho0 + 3) ^ d * Ccell) * ∑' n : ℕ, ENNReal.ofReal ((1 / 4) ^ n) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun n => by rw [← ENNReal.ofReal_mul hC0]
  rw [hs]
  have hgeo : ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≤ 2 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)),
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  calc ENNReal.ofReal ((2 * rho0 + 3) ^ d * Ccell) * ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n)
      ≤ ENNReal.ofReal ((2 * rho0 + 3) ^ d * Ccell) * 2 := mul_le_mul_left' hgeo _
    _ = ENNReal.ofReal (2 * (2 * rho0 + 3) ^ d * Ccell) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul hC0]; congr 1; ring

end Laws

end Paper
end
end

-- ===== module HLow.Clause =====
section
/-!
# hLow: the deterministic per-`ω` clause and cell-mass facts
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hlow_mass_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (om : BilateralField d) :
    0 < aux_hlow_mass M N om := by
  unfold aux_hlow_mass
  have hm : Measurable (fun x => ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) om N x)) :=
    ENNReal.measurable_ofReal.comp (aux_hlow_continuous_density M N om).measurable
  rw [setLIntegral_pos_iff hm]
  have hsupp : Function.support (fun x => ENNReal.ofReal (cutoffSpeedDensity M (fun _ => 0) om N x)) =
      Set.univ := by
    ext x
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_univ, iff_true]
    unfold cutoffSpeedDensity; exact Real.exp_pos _
  rw [hsupp, Set.univ_inter, centeredCube_volume]
  simp

lemma aux_hlow_mass_ne_top (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (om : BilateralField d) :
    aux_hlow_mass M N om ≠ ⊤ := by
  unfold aux_hlow_mass
  obtain ⟨C, hC⟩ := (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.exists_bound_of_continuousOn
    (aux_hlow_continuous_density M N om).continuousOn
  refine ne_top_of_le_ne_top (b := ∫⁻ _x in (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ENNReal.ofReal C) ?_ ?_
  · rw [setLIntegral_const, centeredCube_volume]; simp
  · refine setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal ?_
    have := hC x (centeredCube_subset_closedCube 0 one_pos hx)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

/-- **The per-`ω` clause** from the cell bounds. -/
lemma aux_hlow_clause_omega {rho0 : ℝ} (hrho : 1 ≤ rho0) (μ : Measure (SpatialCoordinates d))
    (V : ℕ → (Fin d → ℤ) → ℝ) (hVpos : ∀ n, ∀ k ∈ aux_hcut_S (d := d) rho0 n, 0 < V n k)
    (hcell : ∀ n, ∀ k ∈ aux_hcut_S (d := d) rho0 n,
      ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ d * (V n k)⁻¹) ≤ μ (HCut.aux_hcut_cell ((3 : ℝ) ^ n)⁻¹ k))
    (KE : ℝ≥0∞) (hKE : KE ≠ ⊤)
    (hTle : ∀ n, ∀ k ∈ aux_hcut_S (d := d) rho0 n,
      ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ (1 / 2 : ℝ) * V n k) ≤ KE)
    (x : SpatialCoordinates d) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hsub : Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2)) :
    ENNReal.ofReal ((3 ^ ((d : ℝ) + 1 / 2) * (1 + KE.toReal))⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
      μ (Metric.ball x r) := by
  obtain ⟨n, k, hk, hcb, hr3⟩ := aux_hlow_cell_in_ball hrho x r hr0 hr1 hsub
  set h : ℝ := ((3 : ℝ) ^ n)⁻¹ with hhdef
  have hh : 0 < h := by rw [hhdef]; positivity
  have hV := hVpos n k hk
  refine le_trans ?_ ((hcell n k hk).trans (measure_mono hcb))
  refine ENNReal.ofReal_le_ofReal ?_
  have hT : h ^ (1 / 2 : ℝ) * V n k ≤ KE.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hKE).1 (hTle n k hk)
  have hK0 : 0 ≤ KE.toReal := ENNReal.toReal_nonneg
  set e : ℝ := (d : ℝ) + 1 / 2 with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  have h3e : 0 < (3 : ℝ) ^ e := by positivity
  have hsq : 0 < h ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hh _
  -- r^e ≤ (3h)^e = 3^e h^e
  have hre : r ^ e ≤ (3 : ℝ) ^ e * h ^ e := by
    rw [← Real.mul_rpow (by norm_num) hh.le]
    exact Real.rpow_le_rpow hr0.le hr3.le he0
  have hhe : h ^ e = h ^ d * h ^ (1 / 2 : ℝ) := by
    rw [he, Real.rpow_add hh, Real.rpow_natCast]
  have hden : (3 : ℝ) ^ e * (h ^ (1 / 2 : ℝ) * V n k) ≤ (3 : ℝ) ^ e * (1 + KE.toReal) := by
    gcongr; linarith
  have hpos : 0 < (3 : ℝ) ^ e * (h ^ (1 / 2 : ℝ) * V n k) := by positivity
  calc ((3 : ℝ) ^ e * (1 + KE.toReal))⁻¹ * r ^ e
      ≤ ((3 : ℝ) ^ e * (h ^ (1 / 2 : ℝ) * V n k))⁻¹ * ((3 : ℝ) ^ e * h ^ e) := by
        gcongr
    _ = h ^ d * (V n k)⁻¹ := by
        rw [hhe]; field_simp

end Paper
end
end

-- ===== module HLow.Supplier =====
section
/-!
# hLow: the lower-mass supplier of `tight_static` (clause 1, lower half), standalone
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

lemma aux_hlow_moment_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {q p : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (B : ℝ) (hB : 0 ≤ B) (hp : ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ ≤ ENNReal.ofReal (B ^ (q / p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le hq hqp
  rw [HCut.aux_hcut_lintegral_ofReal_rpow_eq μ hf0 hq]
  rw [HCut.aux_hcut_lintegral_ofReal_rpow_eq μ hf0 hp0] at hp
  have hmono := HCut.aux_hcut_eLpNorm_mono_exp μ hf.aestronglyMeasurable hq hqp
  have h1 : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B ^ (1 / p)) := by
    have := ENNReal.rpow_le_rpow hp (by positivity : (0 : ℝ) ≤ 1 / p)
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hB (by positivity)] at this
  calc eLpNorm f (ENNReal.ofReal q) μ ^ q ≤ eLpNorm f (ENNReal.ofReal p) μ ^ q :=
        ENNReal.rpow_le_rpow hmono hq.le
    _ ≤ ENNReal.ofReal (B ^ (1 / p)) ^ q := ENNReal.rpow_le_rpow h1 hq.le
    _ = ENNReal.ofReal (B ^ (q / p)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le, ← Real.rpow_mul hB]
        congr 2; ring

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

lemma aux_hlow_V_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ml : ℕ → BilateralField d → ℝ)
    (hml0 : ∀ n om, 0 < ml n om) (N n : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_hlow_V M H ml N n y om := by
  unfold aux_hlow_V
  split_ifs
  · unfold aux_hlow_Vin
    have hm := ENNReal.toReal_pos (aux_hlow_mass_pos M (N - n) (aux_hcut_cellEnv y n om)).ne'
      (aux_hlow_mass_ne_top M (N - n) (aux_hcut_cellEnv y n om))
    have := aux_hcut_cellConst_pos M Rm H y n N om
    have h1 := aux_prop_growth_large_root_ahom_pos_of M Rm (N - n)
    have h2 := aux_prop_growth_large_root_ahom_pos_of M Rm N
    positivity
  · unfold aux_hlow_Vout aux_hcoer_Kout
    have h2 := aux_prop_growth_large_root_ahom_pos_of M Rm N
    have := hml0 N (aux_tight_scale_covariance_translate y om)
    positivity

/-- The a.s. cell bound in the `V` form. -/
lemma aux_hlow_cell_V (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hml0 : ∀ n om, 0 < ml n om)
    (hmlb : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml n om ≤ cutoffCoefficient M H om n x)
    (N n : ℕ) (k : Fin d → ℤ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ d *
          (aux_hlow_V M H ml N n (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) om)⁻¹) ≤
        volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
          (HCut.aux_hcut_cell ((3 : ℝ) ^ n)⁻¹ k) := by
  set y := HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k with hy
  have hh0 : (0 : ℝ) < ((3 : ℝ) ^ n)⁻¹ := by positivity
  by_cases hnN : n ≤ N
  · filter_upwards [aux_hlow_cell_in M Rm hH y hnN] with om hom
    unfold HCut.aux_hcut_cell
    refine le_trans (le_of_eq ?_) hom
    unfold aux_hlow_V aux_hlow_Vin
    rw [if_pos hnN]
    set m := aux_hlow_mass M (N - n) (aux_hcut_cellEnv y n om) with hmdef
    have hm0 : 0 < m.toReal := ENNReal.toReal_pos (aux_hlow_mass_pos M _ _).ne' (aux_hlow_mass_ne_top M _ _)
    have hc := aux_hcut_cellConst_pos M Rm H y n N om
    have ha1 := aux_prop_growth_large_root_ahom_pos_of M Rm (N - n)
    have ha2 := aux_prop_growth_large_root_ahom_pos_of M Rm N
    have hmt : m ≠ ⊤ := aux_hlow_mass_ne_top M (N - n) (aux_hcut_cellEnv y n om)
    rw [← ENNReal.ofReal_toReal hmt, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold aux_hlow_K
    rw [Real.exp_neg]
    field_simp
    exact ENNReal.toReal_ofReal ENNReal.toReal_nonneg
  · have hlt : N < n := by omega
    have hh1 : ((3 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    filter_upwards [aux_hlow_cell_out M hH N (ml N) (hmlb N) y hh0 hh1] with om hom
    unfold HCut.aux_hcut_cell
    refine le_trans (le_of_eq ?_) hom
    unfold aux_hlow_V aux_hlow_Vout aux_hcoer_Kout
    rw [if_neg hnN, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have ha2 := aux_prop_growth_large_root_ahom_pos_of M Rm N
    have := hml0 N (aux_tight_scale_covariance_translate y om)
    field_simp

end Laws

end Paper
end
end

-- ===== module HLow.Main =====
section
/-!
# hLow: the lower-mass supplier of `tight_static`
-/

open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

/-- The lower-mass constant. -/
def aux_hlow_Klow (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ml : ℕ → BilateralField d → ℝ) (N : ℕ) (rho0 : ℝ) (om : BilateralField d) : ℝ :=
  3 ^ ((d : ℝ) + 1 / 2) + 3 ^ ((d : ℝ) + 1 / 2) * (aux_hlow_KE M H ml N rho0 om).toReal + 0 * 0

section Laws
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The almost-sure clause. -/
lemma aux_hlow_clause_ae (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hml0 : ∀ n om, 0 < ml n om)
    (hmlb : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml n om ≤ cutoffCoefficient M H om n x)
    (N : ℕ) {rho0 : ℝ} (hrho : 1 ≤ rho0)
    (hfin : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, aux_hlow_KE M H ml N rho0 om ≠ ⊤) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
        ENNReal.ofReal ((aux_hlow_Klow M H ml N rho0 omega)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
          volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
            (Metric.ball x r) := by
  classical
  have hcells : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ, ∀ k : Fin d → ℤ,
      ENNReal.ofReal ((((3 : ℝ) ^ n)⁻¹) ^ d *
          (aux_hlow_V M H ml N n (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) om)⁻¹) ≤
        volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
          (HCut.aux_hcut_cell ((3 : ℝ) ^ n)⁻¹ k) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => aux_hlow_cell_V M Rm hH ml hml0 hmlb N n k
  filter_upwards [hcells, hfin] with om hc hf
  intro x r hr0 hr1 hsub
  have h := aux_hlow_clause_omega hrho
    (volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)))
    (fun n k => aux_hlow_V M H ml N n (HCut.aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ k) om)
    (fun n k _ => aux_hlow_V_pos M Rm H ml hml0 N n _ om)
    (fun n k _ => hc n k) (aux_hlow_KE M H ml N rho0 om) hf
    (fun n k hk => by
      have : aux_hlow_T M H ml N rho0 n k om ≤ aux_hlow_KE M H ml N rho0 om := by
        unfold aux_hlow_KE; exact le_iSup_of_le n (le_iSup_of_le k le_rfl)
      unfold aux_hlow_T at this
      rwa [if_pos hk] at this)
    x r hr0 hr1 hsub
  refine le_trans (le_of_eq ?_) h
  congr 2
  unfold aux_hlow_Klow
  ring

end Laws

section Laws2
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Uniform per-cell moment. -/
lemma aux_hlow_cell_moment (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (rho0 CH : ℝ) (hCH : ∀ (lam : ℝ), 0 ≤ lam → ∀ y : SpatialCoordinates d, ‖y‖ ≤ rho0 →
        Integrable (fun om => Real.exp (lam * |H om y|)) (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * |H om y|) ∂(chaosSampleLaw M).toMeasure ≤
          2 * Real.exp (CH * lam ^ 2 * M.delta ^ 2))
    (CK : ℝ) (hCK : ∀ (lam : ℝ), 0 ≤ lam →
        Integrable (fun om => Real.exp (lam * ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖))
          (chaosSampleLaw M).toMeasure ∧
        ∫ om, Real.exp (lam * ‖(H om).restrict (aux_hlow_K d : Set (SpatialCoordinates d))‖)
          ∂(chaosSampleLaw M).toMeasure ≤ 2 * Real.exp (CK * lam ^ 2 * M.delta ^ 2))
    (p : ℝ) (hp1 : 1 ≤ p) (Ctail : ℝ) (hCtail : 0 < Ctail)
    (hsmall4 : (4 * p) * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : ∀ k : ℕ, SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M k
        (fun _ => -((3 : ℝ) ^ k / 2)) omega)| - Real.log 2))
    (hsmall : Real.exp ((4 * p) ^ 2 * M.delta ^ 2 / 4 + (4 * p) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ 2)
    (htau : Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ 2)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (hml0 : ∀ n om, 0 < ml n om)
    (Cml : ℝ) (hCml : 0 ≤ Cml)
    (hmlmom : ∀ n, ∫⁻ om, ENNReal.ofReal ((ml n om)⁻¹ ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cml * 81 ^ n))
    (N : ℕ) (Cin Cout : ℝ) (hCin0 : 0 ≤ Cin) (hCout0 : 0 ≤ Cout)
    (hCindef : Cin = (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * 2 *
      (2 * Real.exp (CK * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
      ((2 : ℝ) ^ (4 * p) * 2) ^ (1 / 4 : ℝ))
    (hCoutdef : Cout = ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p *
      (2 * Real.exp (CH * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) * Cml ^ (1 / 2 : ℝ))
    (n : ℕ) (y : SpatialCoordinates d) (hy : ‖y‖ ≤ rho0) :
    ∫⁻ om, ENNReal.ofReal (aux_hlow_V M H ml N n y om ^ p) ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cin + Cout) * 18 ^ n) := by
  unfold aux_hlow_V
  have h18 : (0 : ℝ) ≤ 18 ^ n := by positivity
  by_cases hnN : n ≤ N
  · simp only [hnN, if_true]
    refine (aux_hlow_Vin_moment hd M Rm hH rho0 CH hCH CK hCK y hy hnN p hp1 Ctail hCtail hsmall4 hsource
      hsmall htau).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCindef]
    have h8 : (8 : ℝ) ^ n ≤ 18 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    exact (mul_le_mul_of_nonneg_left h8 hCin0).trans
      (mul_le_mul_of_nonneg_right (by linarith) h18)
  · simp only [hnN, if_false]
    refine (aux_hlow_Vout_moment M Rm hH rho0 CH hCH y hy (ml N) (hmlm N) (hml0 N) N p hp1 Cml
      hCml (hmlmom N) htau).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCoutdef]
    have h18N : (18 : ℝ) ^ N ≤ 18 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_left h18N hCout0).trans
      (mul_le_mul_of_nonneg_right (by linarith) h18)

/-- Packaging of the final constant. -/
lemma aux_hlow_Klow_props (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (ml : ℕ → BilateralField d → ℝ) (hmlm : ∀ n, Measurable (ml n)) (hml0 : ∀ n om, 0 < ml n om)
    (hmlb : ∀ n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ml n om ≤ cutoffCoefficient M H om n x)
    (N : ℕ) {rho0 : ℝ} (hrho : 1 ≤ rho0) {p q : ℝ} (hp1 : 1 ≤ p) (hq : 1 ≤ q) (hqp : q ≤ p)
    (CX : ℝ) (hCX0 : 0 ≤ CX)
    (hKEmom : ∫⁻ om, aux_hlow_KE M H ml N rho0 om ^ p ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CX) :
    Measurable (aux_hlow_Klow M H ml N rho0) ∧ (∀ om, 1 ≤ aux_hlow_Klow M H ml N rho0 om) ∧
      (∫⁻ om, ENNReal.ofReal (aux_hlow_Klow M H ml N rho0 om ^ q) ∂(chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((3 ^ ((d : ℝ) + 1 / 2) + 3 ^ ((d : ℝ) + 1 / 2) * CX ^ (1 / p) +
          0 * 0 ^ (1 / p)) ^ p + 1) ^ (q / p))) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
          ENNReal.ofReal ((aux_hlow_Klow M H ml N rho0 omega)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
            volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
              (Metric.ball x r) := by
  have hp0 : 0 < p := by linarith
  have ha01 : (1 : ℝ) ≤ 3 ^ ((d : ℝ) + 1 / 2) := Real.one_le_rpow (by norm_num) (by positivity)
  have hKEm := aux_hlow_measurable_KE M hH ml hmlm N rho0
  obtain ⟨hm, h1, hmomp, hfin⟩ := aux_hcoer_Kcoer_generic (chaosSampleLaw M).toMeasure
    (aux_hlow_KE M H ml N rho0) (fun _ => (0 : ℝ)) hKEm measurable_const (fun _ => le_rfl) hp1 CX 0 hCX0 le_rfl
    hKEmom (by simp [Real.zero_rpow hp0.ne']) (3 ^ ((d : ℝ) + 1 / 2)) (3 ^ ((d : ℝ) + 1 / 2)) 0 ha01
    (by linarith) le_rfl
  refine ⟨hm, h1, ?_, aux_hlow_clause_ae M Rm hH ml hml0 hmlb N hrho hfin⟩
  exact aux_hlow_moment_mono (chaosSampleLaw M).toMeasure _ hm (fun om => (zero_le_one.trans (h1 om)))
    (by linarith) hqp _ (by positivity) hmomp

end Laws2

/-- **The lower-mass supplier of `tight_static`**, standalone with its own disorder threshold. -/
theorem tight_static_low [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M),
        M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ Clow : ℝ, 0 < Clow ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → ∀ N : ℕ,
      ∃ Klow : BilateralField d → ℝ, Measurable Klow ∧ (∀ omega, 1 ≤ Klow omega) ∧
        (∫⁻ omega, ENNReal.ofReal (Klow omega ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Clow ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
            ENNReal.ofReal ((Klow omega)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
              volume.withDensity
                (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
        (Metric.ball x r) := by
  classical
  set p : ℝ := q + 2 * d + 8 with hpdef
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hpd : 2 * (d : ℝ) + 8 ≤ p := by linarith
  have hqp : q ≤ p := by linarith
  obtain ⟨Ctail, δtail, hCtail, hδtail, htail⟩ := SubdiffusiveProcess.Section9.exists_cutoffTranslatedAxisCube_logAbs_ogamma d
  obtain ⟨δsq, hδsq, hsq⟩ := aux_hlow_log_square_threshold (4 * p) Ctail (by positivity) hCtail
  obtain ⟨δm, hδm, Cml, hCml, hml⟩ := aux_hcoer_ml_package hd p hp1
  obtain ⟨CKf, hCKf0, hCKf⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  refine ⟨min δtail (min δsq (min δm (1 / (8 * p)))),
    lt_min hδtail (lt_min hδsq (lt_min hδm (by positivity))), ?_⟩
  intro M Rm hM rho0 hrho
  have hMtail : M.delta ≤ δtail := hM.trans (min_le_left _ _)
  have hMsq : M.delta ≤ δsq := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMm : M.delta ≤ δm := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMs : M.delta ≤ 1 / (8 * p) :=
    hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hsmall, -⟩ := aux_hcoer_small_facts M hp1 hMs
  have htau : Real.exp (2 * p * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.2 ?_) hsmall
    have hτ := (M.G4.tauSq_pos).le
    rw [abs_of_nonneg hτ]
    nlinarith [sq_nonneg (4 * p), sq_nonneg M.delta]
  have hsmall4 := hsq M.delta M.shellPrefix.delta_pos hMsq
  have hsource : ∀ k : ℕ, SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M k
        (fun _ => -((3 : ℝ) ^ k / 2)) omega)| - Real.log 2) := fun k => htail M hMtail k _
  obtain ⟨CH, hCH0, hCHall⟩ := aux_hcut_exp_H_moment hd rho0
  obtain ⟨Cin, hCindef⟩ : ∃ c : ℝ, c = (2 * Real.exp (CH * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) * 2 *
      (2 * Real.exp (CKf (aux_hlow_K d) * (4 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 4 : ℝ) *
      ((2 : ℝ) ^ (4 * p) * 2) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Cout, hCoutdef⟩ : ∃ c : ℝ, c = ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹) ^ p *
      (2 * Real.exp (CH * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) * Cml ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have ha0 := aux_prop_growth_large_root_ahom_pos_of M Rm 0
  have hCin0 : 0 ≤ Cin := by rw [hCindef]; positivity
  have hCout0 : 0 ≤ Cout := by rw [hCoutdef]; positivity
  obtain ⟨CX, hCXdef⟩ : ∃ c : ℝ, c = 2 * (2 * rho0 + 3) ^ d * (Cin + Cout) := ⟨_, rfl⟩
  have hCX0 : 0 ≤ CX := by
    have : (0 : ℝ) ≤ 2 * rho0 + 3 := by linarith
    rw [hCXdef]; positivity
  obtain ⟨a0, ha0def⟩ : ∃ c : ℝ, c = (3 : ℝ) ^ ((d : ℝ) + 1 / 2) := ⟨_, rfl⟩
  have ha01 : 1 ≤ a0 := by rw [ha0def]; exact Real.one_le_rpow (by norm_num) (by positivity)
  refine ⟨((a0 + a0 * CX ^ (1 / p) + 0 * 0 ^ (1 / p)) ^ p + 1) ^ (q / p),
    Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro H hH N
  obtain ⟨ml, hmlm, hml0, hmlb, hmlmom⟩ := hml M hH hMm
  have hV0 : ∀ n y om, 0 ≤ aux_hlow_V M H ml N n y om := fun n y om =>
    (aux_hlow_V_pos M Rm H ml hml0 N n y om).le
  have hcell := aux_hlow_cell_moment hd M Rm hH rho0 CH (hCHall M H hH) (CKf (aux_hlow_K d))
    (fun lam hlam => hCKf M H hH (aux_hlow_K d) lam hlam) p hp1 Ctail hCtail hsmall4 hsource hsmall htau
    ml hmlm hml0 Cml hCml hmlmom N Cin Cout hCin0 hCout0 hCindef hCoutdef
  have hKEmom := aux_hlow_KE_moment M hH ml hmlm N hrho hpd hV0 (Cin + Cout) (by positivity) hcell
  rw [← hCXdef] at hKEmom
  obtain ⟨hm, h1, hmom, hcl⟩ := aux_hlow_Klow_props M Rm hH ml hmlm hml0 hmlb N hrho hp1 hq hqp CX hCX0 hKEmom
  refine ⟨aux_hlow_Klow M H ml N rho0, hm, h1, ?_, hcl⟩
  rw [ha0def]; exact hmom

end Paper
end
end
