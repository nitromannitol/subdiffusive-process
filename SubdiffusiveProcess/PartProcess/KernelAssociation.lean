module

public import SubdiffusiveProcess.PartProcess.KernelDuality

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)} [IsLocallyFiniteMeasure m]

/-- A symmetric finite kernel's association on compact tests determines its `L²` action. -/
theorem compactKernelAssociation_Lp
    (R : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsFiniteKernel R]
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (hG : CompactKernelAssociation R G)
    (hsymm : ∀ u v, inner ℝ u (G v) = inner ℝ v (G u))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, (∫⁻ y, ENNReal.ofReal (f y) ∂(R x)) < ⊤) ∧
      (fun x => (∫⁻ y, ENNReal.ofReal (f y) ∂(R x)).toReal) =ᵐ[m] ⇑(G (hfL.toLp f)) := by
  let b := hfL.toLp f
  let u := G b
  let r : (Fin d → ℝ) → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (f y) ∂(R x)
  have hr : Measurable r := hf.ennreal_ofReal.lintegral_kernel
  have hb0 : ∀ᵐ x ∂m, 0 ≤ b x := by
    filter_upwards [hfL.coeFn_toLp] with x hx
    exact hx ▸ hf0 x
  have hu0 : ∀ᵐ x ∂m, 0 ≤ u x := compactKernelAssociation_positive R G hG f hf0 hfL
  have hpair : ∀ h : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ,
      (∀ x, 0 ≤ h x) → (∫⁻ x, ENNReal.ofReal (h x) * r x ∂m) =
        ENNReal.ofReal (inner ℝ (compactToLp m h) u) := by
    intro h hh
    let a := compactToLp m h
    have hGa0 : ∀ᵐ x ∂m, 0 ≤ G a x := compactKernelAssociation_positive R G hG h hh
      (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport)
    have hhm : Measurable (fun x => ENNReal.ofReal (h x)) := h.continuous.measurable.ennreal_ofReal
    have hfm : Measurable (fun x => ENNReal.ofReal (f x)) := hf.ennreal_ofReal
    calc
      (∫⁻ x, ENNReal.ofReal (h x) * r x ∂m) =
          ∫⁻ y, ENNReal.ofReal (f y) ∂(R ∘ₘ m.withDensity
            (fun x => ENNReal.ofReal (h x))) := by
        rw [Measure.lintegral_bind R.aemeasurable hfm.aemeasurable,
          lintegral_withDensity_eq_lintegral_mul _ hhm hfm.lintegral_kernel]
        rfl
      _ = ∫⁻ y, ENNReal.ofReal (f y) ∂m.withDensity
          (fun x => ENNReal.ofReal (G a x)) := by rw [weighted_kernel_density R G hG hsymm h hh]
      _ = ∫⁻ x, ENNReal.ofReal (b x) * ENNReal.ofReal (G a x) ∂m := by
        rw [lintegral_withDensity_eq_lintegral_mul₀'
          (Lp.aestronglyMeasurable (G a)).aemeasurable.ennreal_ofReal hfm.aemeasurable]
        simp only [Pi.mul_apply]
        apply lintegral_congr_ae
        filter_upwards [hfL.coeFn_toLp] with x hx
        rw [hx, mul_comm]
      _ = ENNReal.ofReal (inner ℝ b (G a)) := (ofReal_inner_eq_lintegral b (G a) hb0 hGa0).symm
      _ = ENNReal.ofReal (inner ℝ a u) := congrArg ENNReal.ofReal (hsymm b a)
  have : IsFiniteMeasureOnCompacts (m.withDensity r) := by
    constructor
    intro K hK
    obtain ⟨c, hcK, _, hccomp, hcrange⟩ :=
      exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
    let h : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ := ⟨c, hccomp⟩
    have hh : ∀ x, 0 ≤ h x := fun x => (hcrange x).1
    rw [withDensity_apply _ hK.measurableSet, ← lintegral_indicator hK.measurableSet]
    have hle : (∫⁻ x, K.indicator r x ∂m) ≤ ∫⁻ x, ENNReal.ofReal (h x) * r x ∂m := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · simp only [Set.indicator_of_mem hx]
        rw [show h x = 1 from hcK hx, ENNReal.ofReal_one, one_mul]
      · simp only [Set.indicator_of_notMem hx]
        exact bot_le
    exact hle.trans_lt (by rw [hpair h hh]; exact ENNReal.ofReal_lt_top)
  have : IsLocallyFiniteMeasure (m.withDensity r) := inferInstance
  have : IsLocallyFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (u x))) :=
    isLocallyFiniteMeasure_withDensity_Lp u
  have hmeas : m.withDensity r = m.withDensity (fun x => ENNReal.ofReal (u x)) := by
    apply measure_ext_of_lintegral_nonneg_compact
    intro h hh
    have hhm : Measurable (fun x => ENNReal.ofReal (h x)) := h.continuous.measurable.ennreal_ofReal
    have ha0 : ∀ᵐ x ∂m, 0 ≤ compactToLp m h x := by
      filter_upwards [compactToLp_coe h] with x hx
      exact hx ▸ hh x
    rw [lintegral_withDensity_eq_lintegral_mul _ hr hhm,
      lintegral_withDensity_eq_lintegral_mul₀'
        (Lp.aestronglyMeasurable u).aemeasurable.ennreal_ofReal hhm.aemeasurable]
    calc
      (∫⁻ x, r x * ENNReal.ofReal (h x) ∂m) =
          ENNReal.ofReal (inner ℝ (compactToLp m h) u) := by
        simpa only [mul_comm] using hpair h hh
      _ = ∫⁻ x, ENNReal.ofReal (compactToLp m h x) * ENNReal.ofReal (u x) ∂m :=
        ofReal_inner_eq_lintegral _ u ha0 hu0
      _ = ∫⁻ x, ENNReal.ofReal (u x) * ENNReal.ofReal (h x) ∂m := by
        apply lintegral_congr_ae
        filter_upwards [compactToLp_coe h] with x hx
        rw [hx, mul_comm]
  have heq : r =ᵐ[m] (fun x => ENNReal.ofReal (u x)) :=
    (withDensity_eq_iff_of_sigmaFinite hr.aemeasurable
      (Lp.aestronglyMeasurable u).aemeasurable.ennreal_ofReal).1 hmeas
  constructor
  · filter_upwards [heq] with x hx
    rw [show (∫⁻ y, ENNReal.ofReal (f y) ∂(R x)) = ENNReal.ofReal (u x) from hx]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [heq, hu0] with x hx hpos
    change (r x).toReal = u x
    rw [hx, ENNReal.toReal_ofReal hpos]

end SubdiffusiveProcess.PartProcess
