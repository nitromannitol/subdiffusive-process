import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators




noncomputable section
namespace Paper



def aux_prop_conc_level_zoom_T {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ))),
    continuous_cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ)))⟩



def aux_prop_conc_level_zoom_Theta {d : ℕ} (k : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j : ℤ => (omega (j - (k : ℤ))).comp (aux_prop_conc_level_zoom_T k z)

/-- The retained coarse potential `G_k`. -/
def aux_prop_conc_level_zoom_Gc {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))

theorem aux_prop_conc_level_zoom_T_zero {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    aux_prop_conc_level_zoom_T k z 0 = z := by
  funext i
  simp [aux_prop_conc_level_zoom_T, cubeDilation]

theorem aux_prop_conc_level_zoom_Theta_eq_zoom {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) :
    aux_prop_conc_level_zoom_Theta (d := d) k z =
      aux_lem_extension_cell_moment_zoom (k : ℤ) z := by
  funext omega j
  ext x
  rw [aux_lem_extension_cell_moment_zoom_apply]
  simp only [aux_prop_conc_level_zoom_Theta, aux_prop_conc_level_zoom_T,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  congr 1
  funext i
  simp [cubeDilation, Pi.smul_apply, smul_eq_mul, add_comm]

/-- **Clause 5.** `Θ_{k,z}` preserves the common-scale layer law. -/
theorem aux_prop_conc_level_zoom_Theta_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_prop_conc_level_zoom_Theta k z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  rw [aux_prop_conc_level_zoom_Theta_eq_zoom]
  exact aux_lem_extension_cell_moment_zoom_measurePreserving M (k : ℤ) z

theorem aux_prop_conc_level_zoom_Theta_apply {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) (j : ℤ)
    (y : SpatialCoordinates d) :
    aux_prop_conc_level_zoom_Theta k z omega j y =
      omega (j - (k : ℤ)) (aux_prop_conc_level_zoom_T k z y) := rfl

/-- The infrared partial sums of the zoomed field split into the retained
coarse layers and the anchored tail of the original field. -/
theorem aux_prop_conc_level_zoom_partialSum_Theta {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) (L : ℕ) :
    infraredPartialSum (aux_prop_conc_level_zoom_Theta k z omega) (L + k) =
      ((∑ j ∈ Finset.range k, omega (-(j : ℤ))).comp
          (aux_prop_conc_level_zoom_T k z) -
        ContinuousMap.const _ ((∑ j ∈ Finset.range k, omega (-(j : ℤ))) z)) +
      ((infraredPartialSum omega L).comp (aux_prop_conc_level_zoom_T k z) -
        ContinuousMap.const _ ((infraredPartialSum omega L) z)) := by
  have hT0 := aux_prop_conc_level_zoom_T_zero (d := d) k z
  ext x
  simp only [infraredPartialSum, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    ContinuousMap.add_apply, aux_prop_conc_level_zoom_Theta_apply, hT0]
  rw [add_comm L k, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have hidx : Int.ofNat (k - 1 - n + 1) - (k : ℤ) = -((n : ℕ) : ℤ) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hidx]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hidx : (Int.ofNat (k + n + 1) - (k : ℤ)) = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hidx]
    ring

/-- **Clause 6.** The infrared field of the zoomed layers is the retained
coarse potential, reanchored at `z`. -/
theorem aux_prop_conc_level_zoom_H_Theta {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (k : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      H (aux_prop_conc_level_zoom_Theta k z omega) =
        (aux_prop_conc_level_zoom_Gc H k omega).comp
            (aux_prop_conc_level_zoom_T k z) -
          ContinuousMap.const _ (aux_prop_conc_level_zoom_Gc H k omega z) := by
  have hMP := aux_prop_conc_level_zoom_Theta_measurePreserving M k z
  have hpull := hMP.quasiMeasurePreserving.ae HI.2
  filter_upwards [HI.2, hpull] with omega hom hTom
  set T := aux_prop_conc_level_zoom_T (d := d) k z with hT
  set F : C(SpatialCoordinates d, ℝ) := ∑ j ∈ Finset.range k, omega (-(j : ℤ)) with hF
  -- the shifted sequence of partial sums of the zoomed field
  have hshift : Tendsto
      (fun L => infraredPartialSum (aux_prop_conc_level_zoom_Theta k z omega) (L + k))
      atTop (𝓝 (H (aux_prop_conc_level_zoom_Theta k z omega))) :=
    (tendsto_add_atTop_iff_nat k).2 hTom
  have hcont : Continuous (fun G : C(SpatialCoordinates d, ℝ) =>
      (F.comp T - ContinuousMap.const _ (F z)) +
        (G.comp T - ContinuousMap.const _ (G z))) := by
    refine continuous_const.add ?_
    exact (ContinuousMap.compRightContinuousMap ℝ T).continuous.sub
      (ContinuousMap.const'.continuous.comp (continuous_eval_const z))
  have hlim : Tendsto
      (fun L => infraredPartialSum (aux_prop_conc_level_zoom_Theta k z omega) (L + k))
      atTop (𝓝 ((F.comp T - ContinuousMap.const _ (F z)) +
        ((H omega).comp T - ContinuousMap.const _ ((H omega) z)))) := by
    have h := (hcont.tendsto (H omega)).comp hom
    refine h.congr' (Eventually.of_forall fun L => ?_)
    simp only [Function.comp_apply]
    rw [aux_prop_conc_level_zoom_partialSum_Theta]
  rw [tendsto_nhds_unique hshift hlim]
  ext x
  simp only [aux_prop_conc_level_zoom_Gc, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    hF]
  ring

-- ===== from LNScale.lean =====


theorem aux_prop_conc_level_zoom_cutoff_coeFn {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val x =
        cutoffCoefficient M H omega N x := by
  letI : Fact (((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hnorm := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr)
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hnorm, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxm
  simpa [cutoffPositiveCoefficient, cutoffCoefficientCM] using hx hxm

/-- The deterministic normalization `κ_N`. -/
def aux_prop_conc_level_zoom_kap {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N

theorem aux_prop_conc_level_zoom_kap_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    0 < aux_prop_conc_level_zoom_kap M N :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)

/-- The cutoff potential of the zoomed field is the original cutoff potential
minus the retained constant `G_k(z)`. -/
theorem aux_prop_conc_level_zoom_pot_identity {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_prop_conc_level_zoom_Theta k z omega) =
      (aux_prop_conc_level_zoom_Gc H k omega).comp
          (aux_prop_conc_level_zoom_T k z) -
        ContinuousMap.const _ (aux_prop_conc_level_zoom_Gc H k omega z))
    (N : ℕ) (hkN : k ≤ N) (y : SpatialCoordinates d) :
    cutoffPotential H omega N (aux_prop_conc_level_zoom_T k z y) =
      cutoffPotential H (aux_prop_conc_level_zoom_Theta k z omega) (N - k) y +
        aux_prop_conc_level_zoom_Gc H k omega z := by
  unfold cutoffPotential
  rw [hH]
  have hsplit : N + 1 = k + (N - k + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, aux_prop_conc_level_zoom_Gc,
    ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    aux_prop_conc_level_zoom_Theta_apply]
  simp only [Int.ofNat_eq_natCast]
  have hsum : ∑ x ∈ Finset.range (N - k + 1),
      omega (-((k + x : ℕ) : ℤ)) (aux_prop_conc_level_zoom_T k z y) =
      ∑ x ∈ Finset.range (N - k + 1),
        omega (-(x : ℤ) - (k : ℤ)) (aux_prop_conc_level_zoom_T k z y) :=
    Finset.sum_congr rfl (fun j _ => by congr 2; push_cast; ring)
  rw [hsum]
  ring

/-- Pointwise coefficient identity on the infrared event. -/
theorem aux_prop_conc_level_zoom_coef_identity {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_prop_conc_level_zoom_Theta k z omega) =
      (aux_prop_conc_level_zoom_Gc H k omega).comp
          (aux_prop_conc_level_zoom_T k z) -
        ContinuousMap.const _ (aux_prop_conc_level_zoom_Gc H k omega z))
    (N : ℕ) (hkN : k ≤ N) (y : SpatialCoordinates d) :
    cutoffCoefficient M H omega N (aux_prop_conc_level_zoom_T k z y) =
      (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
          Real.exp (aux_prop_conc_level_zoom_Gc H k omega z)) *
        cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k z omega) (N - k) y := by
  have hpot := aux_prop_conc_level_zoom_pot_identity H k z omega hH N hkN y
  have hN : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
    rw [Nat.cast_sub hkN]
  unfold cutoffCoefficient aux_prop_conc_level_zoom_kap
  rw [hpot, hN]
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hB := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P =
      cutoffPotential H (aux_prop_conc_level_zoom_Theta k z omega) (N - k) y := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = aux_prop_conc_level_zoom_Gc H k omega z := ⟨_, rfl⟩
  rw [← hτ, ← hP, ← hG]
  have e1 : Real.exp (P + G - ((N : ℝ) + 1) * τ) =
      Real.exp (((N : ℝ) - k + 1) * τ) * Real.exp G *
        Real.exp (P - ((N : ℝ) - k + 1) * τ) / Real.exp (((N : ℝ) + 1) * τ) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [e1]
  field_simp


/-- The normalizer ratio is the exponential of the centered annealed normalizer error. -/
theorem aux_prop_conc_level_zoom_kap_ratio {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) (hkN : k ≤ N) :
    aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N =
      Real.exp (SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.normalizerLogError M N (N - k)) := by
  have hratio := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ahom_ratio_eq_exp_normalizerLogError
    M N (N - k)
  have hNk : ((N - (N - k) : ℕ) : ℝ) = (k : ℝ) := by
    rw [show N - (N - k) = k by omega]
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hB := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
  unfold aux_prop_conc_level_zoom_kap
  rw [hNk] at hratio
  have hN : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by rw [Nat.cast_sub hkN]
  rw [hN]
  have e1 : Real.exp (((N : ℝ) - k + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) =
      Real.exp (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
    rw [show ((N : ℝ) - k + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) by ring,
      Real.exp_add]
    field_simp
  rw [e1, hratio, ← Real.exp_add]
  congr 1
  ring

/-- The normalizer ratio between two cutoff levels `k` apart lies in `[exp(-k τ²), exp(k τ²)]`. -/
theorem aux_prop_conc_level_zoom_kap_ratio_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k N : ℕ) (hkN : k ≤ N) :
    Real.exp (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ≤
        aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N ∧
      aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N ≤
        Real.exp ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  rw [aux_prop_conc_level_zoom_kap_ratio M k N hkN]
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.abs_normalizerLogError_le_of_le M
    (m := N) (n := N - k) (by omega)
  have hNk : ((N - (N - k) : ℕ) : ℝ) = (k : ℝ) := by
    rw [show N - (N - k) = k by omega]
  rw [hNk, abs_le] at h
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [h.1, mul_comm (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) (k : ℝ)])
  · exact Real.exp_le_exp.mpr (by linarith [h.2, mul_comm (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) (k : ℝ)])

/-- Level-`k` shift of the common-scale field (paper `lem-local-normalizations`, layer part):
the shifted field `Θ_{k,z} ω` keeps the layer law, the level-`k` cutoff coefficient on
`z + 3^{-k} Q₀` is a constant multiple of the unit-cell cutoff coefficient of `Θ_{k,z} ω` at cutoff
`N - k`, and the constant is `κ_{N-k}/κ_N · exp G_k(z)`, with `κ_{N-k}/κ_N ∈ [e^{-kτ²}, e^{kτ²}]`. -/
theorem prop_conc_level_zoom
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_prop_conc_level_zoom_Theta k z)
        (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure ∧
    (∀ N : ℕ, k ≤ N →
      Real.exp (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ≤
          aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N ∧
        aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N ≤
          Real.exp ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∧
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, k ≤ N → ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H omega N (aux_prop_conc_level_zoom_T k z y) =
        (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
            Real.exp (aux_prop_conc_level_zoom_Gc H k omega z)) *
          cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k z omega) (N - k) y := by
  refine ⟨aux_prop_conc_level_zoom_Theta_measurePreserving M k z,
    fun N hkN => aux_prop_conc_level_zoom_kap_ratio_bounds M k N hkN, ?_⟩
  filter_upwards [aux_prop_conc_level_zoom_H_Theta M H HI k z] with omega hH
  intro N hkN y
  exact aux_prop_conc_level_zoom_coef_identity M H k z omega hH N hkN y

end Paper
