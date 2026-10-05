module

public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Analysis.RawLp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The norm of a differential on the maximum-norm spatial space is the sum of
the absolute coordinate derivatives: the paper's dual gradient norm. -/
theorem dualNorm_eq_sum_abs {d : ℕ} (L : SpatialCoordinates d →L[ℝ] ℝ) :
    ‖L‖ = ∑ i : Fin d, |L (Pi.single i 1)| := by
  have hL (v : SpatialCoordinates d) :
      L v = ∑ i : Fin d, v i * L (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  apply le_antisymm
  · apply L.opNorm_le_bound (Finset.sum_nonneg fun i _ => abs_nonneg _)
    intro v
    rw [hL, Real.norm_eq_abs, Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, mul_comm |v i|]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [Real.norm_eq_abs] using! norm_le_pi_norm v i
  · let v : SpatialCoordinates d := fun i => if 0 ≤ L (Pi.single i 1) then 1 else -1
    have hv : ‖v‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro i
      dsimp only [v]
      split <;> norm_num
    have hvalue : L v = ∑ i : Fin d, |L (Pi.single i 1)| := by
      rw [hL]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [v]
      split
      · rename_i hi
        rw [one_mul, abs_of_nonneg hi]
      · rename_i hi
        rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]
    have hnonneg : 0 ≤ ∑ i : Fin d, |L (Pi.single i 1)| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    simpa only [hvalue, Real.norm_eq_abs, abs_of_nonneg hnonneg] using! L.unit_le_opNorm v hv

/-- Essential spatial suprema of jointly measurable observables are measurable in
the sample parameter. Superlevel sections provide the measurable representation. -/
theorem measurable_essSup_param {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {f : Ω × X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun ω => essSup (fun x => f (ω, x)) μ) := by
  apply measurable_of_Iic
  intro c
  have hsection : Measurable (fun ω => μ {x | c < f (ω, x)}) :=
    measurable_measure_prodMk_left (measurableSet_lt measurable_const hf)
  have heq : (fun ω => essSup (fun x => f (ω, x)) μ) ⁻¹' Iic c =
      (fun ω => μ {x | c < f (ω, x)}) ⁻¹' {0} := by
    ext ω
    change essSup (fun x => f (ω, x)) μ ≤ c ↔ μ {x | c < f (ω, x)} = 0
    have hae : (∀ᵐ x ∂μ, f (ω, x) ≤ c) ↔ μ {x | c < f (ω, x)} = 0 := by
      simp only [ae_iff, not_le]
    rw [← hae]
    constructor
    · intro h
      exact (ENNReal.ae_le_essSup (fun x => f (ω, x))).mono fun x hx => hx.trans h
    · intro h
      exact essSup_le_of_ae_le c h
  rw [heq]
  exact hsection (measurableSet_singleton 0)

/-- The spatial norm retains the paper's unrestricted essential-supremum formula. -/
def spatialSupNorm {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → F) : ℝ≥0∞ :=
  SubdiffusiveProcess.RawLp.eLpNorm f ⊤ (volume.restrict (centeredCube z r hr : Set _))

/-- The logarithmic differential, with the dual norm of the maximum spatial
norm. This is the paper's gradient norm convention, rather than the maximum of
its individual coordinates. -/
def cutoffLogGradient {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (ω : BilateralField d) (x : SpatialCoordinates d) :
      SpatialCoordinates d →L[ℝ] ℝ :=
  fderiv ℝ (fun y => Real.log (cutoffCoefficient M H ω N y)) x

/-- The paper's named normalized logarithmic-gradient norm. -/
def cutoffGradientExtreme {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (ω : BilateralField d) : ℝ :=
  (3 : ℝ) ^ (-(N : ℤ)) * (spatialSupNorm z r hr (cutoffLogGradient M H N ω)).toReal

/-- The paper's sum of the two named coefficient norms. -/
def cutoffCoefficientExtreme {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (ω : BilateralField d) : ℝ :=
  (SubdiffusiveProcess.RawLp.eLpNorm (cutoffCoefficient M H ω N) ⊤
    (volume.restrict (centeredCube z r hr : Set _))).toReal +
  (SubdiffusiveProcess.RawLp.eLpNorm (fun x => (cutoffCoefficient M H ω N x)⁻¹) ⊤
    (volume.restrict (centeredCube z r hr : Set _))).toReal

theorem measurable_cutoffLogGradient {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      cutoffLogGradient M H N p.1 p.2) := by
  let g : BilateralField d → C(SpatialCoordinates d, ℝ) := fun ω =>
    H ω + ∑ j ∈ Finset.range (N + 1), ω (-(j : ℤ))
  have hg : Measurable g := hH.add
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply _)
  have hd : Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      fderiv ℝ (g p.1) p.2) :=
    (measurable_fderiv_with_param ℝ (f := fun g : C(SpatialCoordinates d, ℝ) =>
      fun x => g x) continuous_eval).comp (hg.prodMap measurable_id)
  have heq (ω : BilateralField d) :
      (fun y => Real.log (cutoffCoefficient M H ω N y)) =
        fun y => (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) + g ω y := by
    funext y
    rw [_root_.SubdiffusiveProcess.Paper.aux_lem_extension_cell_moment_cutoff_log]
    simp only [g, ContinuousMap.add_apply, ContinuousMap.sum_apply]
    ring
  simpa only [cutoffLogGradient, heq, fderiv_const_add] using! hd

theorem measurable_cutoffGradientExtreme {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) :
    Measurable (cutoffGradientExtreme M H z r hr N) := by
  have hm := measurable_essSup_param
    (volume.restrict (centeredCube z r hr : Set _))
    (measurable_cutoffLogGradient M H hH N).enorm
  simpa only [cutoffGradientExtreme, spatialSupNorm, SubdiffusiveProcess.RawLp.eLpNorm_top_exponent,
    eLpNormEssSup, Pi.mul_apply] using!
      (measurable_const.mul hm.ennreal_toReal : Measurable (fun ω =>
        (3 : ℝ) ^ (-(N : ℤ)) * (essSup (fun x => ‖cutoffLogGradient M H N ω x‖ₑ)
          (volume.restrict (centeredCube z r hr : Set _))).toReal))

theorem measurable_cutoffCoefficientExtreme {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) :
    Measurable (cutoffCoefficientExtreme M H z r hr N) := by
  have hcm := _root_.SubdiffusiveProcess.Paper.aux_lem_extension_cell_moment_measurable_cutoffCM M H hH N
  have hm : Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      cutoffCoefficient M H p.1 N p.2) :=
    continuous_eval.measurable.comp (hcm.prodMap measurable_id)
  have h1 := measurable_essSup_param
    (volume.restrict (centeredCube z r hr : Set _)) hm.enorm
  have h2 := measurable_essSup_param
    (volume.restrict (centeredCube z r hr : Set _)) hm.inv.enorm
  simpa only [cutoffCoefficientExtreme, SubdiffusiveProcess.RawLp.eLpNorm_top_exponent,
    eLpNormEssSup, Pi.add_apply, Pi.inv_apply] using!
      h1.ennreal_toReal.add h2.ennreal_toReal

/-- A logarithmic Lipschitz bound controls the dual gradient norm on the open cube. -/
theorem cutoffLogGradient_norm_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (ω : BilateralField d)
    {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x y, x ∈ (closedCube z r hr : Set _) → y ∈ (closedCube z r hr : Set _) →
      |Real.log (cutoffCoefficient M H ω N x) - Real.log (cutoffCoefficient M H ω N y)| ≤
        L * dist x y) (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z r hr : Set _)) :
    ‖cutoffLogGradient M H N ω x‖ ≤ L := by
  apply norm_fderiv_le_of_lip' ℝ hL
  filter_upwards [(centeredCube z r hr).isOpen.mem_nhds hx] with y hy
  rw [Real.norm_eq_abs, ← dist_eq_norm]
  exact h y x (centeredCube_subset_closedCube z hr hy) (centeredCube_subset_closedCube z hr hx)

/-- A finite a.e. spatial bound controls the literal norm and its real value. -/
theorem rawSupNorm_toReal_le {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] (μ : Measure X) {f : X → F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    (SubdiffusiveProcess.RawLp.eLpNorm f ⊤ μ).toReal ≤ C ∧ SubdiffusiveProcess.RawLp.eLpNorm f ⊤ μ < ⊤ := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hb := eLpNormEssSup_le_of_ae_bound h
  exact ⟨(ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal hC), hb.trans_lt ENNReal.ofReal_lt_top⟩

/-- Pointwise-extrema moments for the paper's named gradient and coefficient
norms. The constants retain the quantifier order of `SubdiffusiveProcess.Paper.lem_extremes`. -/
theorem cutoff_extrema_moments :
    ∀ (d : ℕ), 2 ≤ d →
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
    ∃ Cd cd : ℝ, 0 < Cd ∧ 0 < cd ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ (p : ℝ), 1 ≤ p →
      ∃ Cp : ℝ, 0 < Cp ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H → M.delta ≤ cd / p →
        (∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ N,
          spatialSupNorm z r hr (cutoffLogGradient M H N ω) < ⊤ ∧
          SubdiffusiveProcess.RawLp.eLpNorm (cutoffCoefficient M H ω N) ⊤
            (volume.restrict (centeredCube z r hr : Set _)) < ⊤ ∧
          SubdiffusiveProcess.RawLp.eLpNorm (fun x => (cutoffCoefficient M H ω N x)⁻¹) ⊤
            (volume.restrict (centeredCube z r hr : Set _)) < ⊤) ∧
        (∀ N, Measurable (cutoffGradientExtreme M H z r hr N) ∧
          MemLp (cutoffGradientExtreme M H z r hr N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure) ∧
        (∀ N, Measurable (cutoffCoefficientExtreme M H z r hr N) ∧
          MemLp (cutoffCoefficientExtreme M H z r hr N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (cutoffGradientExtreme M H z r hr N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
        (∀ N, eLpNorm (cutoffCoefficientExtreme M H z r hr N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))) := by
  intro d hd _ _
  obtain ⟨Cd, cd, hCd, hcd, hall⟩ := _root_.SubdiffusiveProcess.Paper.lem_extremes d hd
  refine ⟨Cd, cd, hCd, hcd, ?_⟩
  intro z r hr p hp
  obtain ⟨Cp, hCp, hmodels⟩ := hall z r hr p hp
  refine ⟨Cp, hCp, ?_⟩
  intro M H hH hδ
  obtain ⟨D, mlow, mhigh, hD0, hpoint, hDlp, hAlp, hDnorm, hAnorm⟩ := hmodels M H hH hδ
  let ν : Measure (SpatialCoordinates d) := volume.restrict (centeredCube z r hr : Set _)
  have hnamed : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ N,
      cutoffGradientExtreme M H z r hr N ω ≤ D N ω ∧
      cutoffCoefficientExtreme M H z r hr N ω ≤ mhigh N ω + (mlow N ω)⁻¹ ∧
      spatialSupNorm z r hr (cutoffLogGradient M H N ω) < ⊤ ∧
      SubdiffusiveProcess.RawLp.eLpNorm (cutoffCoefficient M H ω N) ⊤ ν < ⊤ ∧
      SubdiffusiveProcess.RawLp.eLpNorm (fun x => (cutoffCoefficient M H ω N x)⁻¹) ⊤ ν < ⊤ := by
    filter_upwards [hpoint] with ω hω N
    obtain ⟨hlog, hlo, hcoeff⟩ := hω N
    have hhigh : 0 ≤ mhigh N ω := by
      have hz : z ∈ (closedCube z r hr : Set _) := by
        change dist z z ≤ r / 2
        rw [dist_self]
        positivity
      exact (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H ω N z).le.trans (hcoeff z hz).2
    have hgrad := rawSupNorm_toReal_le ν (mul_nonneg (hD0 N ω) (by positivity))
      ((ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet).mono fun x hx =>
        cutoffLogGradient_norm_le M H z r hr N ω
          (mul_nonneg (hD0 N ω) (by positivity)) hlog x hx)
    have hupper := rawSupNorm_toReal_le ν hhigh
      ((ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H ω N x)]
        exact (hcoeff x (centeredCube_subset_closedCube z hr hx)).2)
    have hlower := rawSupNorm_toReal_le ν (inv_pos.2 hlo).le
      ((ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H ω N x))]
        exact inv_le_inv₀ (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H ω N x) hlo |>.2
          (hcoeff x (centeredCube_subset_closedCube z hr hx)).1)
    refine ⟨?_, add_le_add hupper.1 hlower.1, hgrad.2, hupper.2, hlower.2⟩
    change (3 : ℝ) ^ (-(N : ℤ)) * (SubdiffusiveProcess.RawLp.eLpNorm _ ⊤ ν).toReal ≤ D N ω
    calc
      _ ≤ (3 : ℝ) ^ (-(N : ℤ)) * (D N ω * (3 : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left hgrad.1 (by positivity)
      _ = D N ω := by
        rw [zpow_neg, zpow_natCast]
        field_simp
  have hDmeas N := measurable_cutoffGradientExtreme M H hH.1 z r hr N
  have hAmeas N := measurable_cutoffCoefficientExtreme M H hH.1 z r hr N
  have hDle N : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
      ‖cutoffGradientExtreme M H z r hr N ω‖ ≤ D N ω := by
    filter_upwards [hnamed] with ω hω
    rw [Real.norm_of_nonneg (by unfold cutoffGradientExtreme; positivity)]
    exact (hω N).1
  have hAle N : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
      ‖cutoffCoefficientExtreme M H z r hr N ω‖ ≤ mhigh N ω + (mlow N ω)⁻¹ := by
    filter_upwards [hnamed] with ω hω
    rw [Real.norm_of_nonneg (by unfold cutoffCoefficientExtreme; positivity)]
    exact (hω N).2.1
  refine ⟨hnamed.mono (fun ω hω N => (hω N).2.2),
    fun N => ⟨hDmeas N, (hDlp N).mono' (hDmeas N).aestronglyMeasurable (hDle N)⟩,
    fun N => ⟨hAmeas N, (hAlp N).mono' (hAmeas N).aestronglyMeasurable (hAle N)⟩,
    fun N => (eLpNorm_mono_ae_real (hDmeas N).aestronglyMeasurable (hDle N)).trans (hDnorm N),
    fun N => (eLpNorm_mono_ae_real (hAmeas N).aestronglyMeasurable (hAle N)).trans (hAnorm N)⟩

end SubdiffusiveProcess.AuditExports
