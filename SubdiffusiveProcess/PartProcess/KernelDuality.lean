module

public import SubdiffusiveProcess.PartProcess.CompactLp
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)} [IsLocallyFiniteMeasure m]

def CompactKernelAssociation
    (R : Kernel (Fin d → ℝ) (Fin d → ℝ)) (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Prop :=
  ∀ g : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ,
    (fun x => ∫ y, g y ∂(R x)) =ᵐ[m] ⇑(G (compactToLp m g))

theorem ofReal_inner_eq_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : Lp ℝ 2 μ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x) (hv : ∀ᵐ x ∂μ, 0 ≤ v x) :
    ENNReal.ofReal (inner ℝ u v) = ∫⁻ x, ENNReal.ofReal (u x) * ENNReal.ofReal (v x) ∂μ := by
  have hi : Integrable (fun x => u x * v x) μ := by
    simpa [RCLike.inner_apply, mul_comm] using L2.integrable_inner (𝕜 := ℝ) u v
  have he : inner ℝ u v = ∫ x, u x * v x ∂μ := by
    simp [L2.inner_def, RCLike.inner_apply, mul_comm]
  rw [he, ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [hu, hv] with x h1 h2
    exact mul_nonneg h1 h2)]
  apply lintegral_congr_ae
  filter_upwards [hu] with x hx
  exact ENNReal.ofReal_mul hx

theorem compactKernelAssociation_positive
    (R : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsFiniteKernel R]
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (hG : CompactKernelAssociation R G)
    (f : (Fin d → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfL : MemLp f 2 m) :
    ∀ᵐ x ∂m, 0 ≤ G (hfL.toLp f) x := by
  obtain ⟨g, hg0, hlim⟩ := exists_nonneg_compactToLp_seq f hf0 hfL
  apply nonneg_of_tendsto_Lp (u := fun n => G (compactToLp m (g n))) _
    ((G.continuous.tendsto _).comp hlim)
  intro n
  filter_upwards [hG (g n)] with x hx
  rw [← hx]
  exact integral_nonneg (hg0 n)

theorem weighted_kernel_density
    (R : Kernel (Fin d → ℝ) (Fin d → ℝ)) [IsFiniteKernel R]
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (hG : CompactKernelAssociation R G)
    (hsymm : ∀ u v, inner ℝ u (G v) = inner ℝ v (G u))
    (h : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ) (hh : ∀ x, 0 ≤ h x) :
    R ∘ₘ (m.withDensity (fun x => ENNReal.ofReal (h x))) =
      m.withDensity (fun x => ENNReal.ofReal (G (compactToLp m h) x)) := by
  let a := compactToLp m h
  have ha0 : ∀ᵐ x ∂m, 0 ≤ a x := by
    filter_upwards [compactToLp_coe h] with x hx
    exact hx ▸ hh x
  have hGa0 : ∀ᵐ x ∂m, 0 ≤ G a x :=
    compactKernelAssociation_positive R G hG h hh
      (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport)
  haveI : IsFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (h x))) :=
    isFiniteMeasure_withDensity_ofReal
      (h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport).2
  haveI : IsLocallyFiniteMeasure (m.withDensity (fun x => ENNReal.ofReal (G a x))) :=
    isLocallyFiniteMeasure_withDensity_Lp (G a)
  apply measure_ext_of_lintegral_nonneg_compact
  intro g hg0
  have hgm : Measurable (fun x => ENNReal.ofReal (g x)) := g.continuous.measurable.ennreal_ofReal
  have hhm : Measurable (fun x => ENNReal.ofReal (h x)) := h.continuous.measurable.ennreal_ofReal
  let b := compactToLp m g
  have hb0 : ∀ᵐ x ∂m, 0 ≤ b x := by
    filter_upwards [compactToLp_coe g] with x hx
    exact hx ▸ hg0 x
  have hGb0 : ∀ᵐ x ∂m, 0 ≤ G b x :=
    compactKernelAssociation_positive R G hG g hg0
      (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport)
  have hRg : (fun x => ∫⁻ y, ENNReal.ofReal (g y) ∂(R x)) =ᵐ[m]
      (fun x => ENNReal.ofReal (G b x)) := by
    filter_upwards [hG g] with x hx
    rw [← ofReal_integral_eq_lintegral_ofReal
      (show Integrable (fun y => g y) (R x) from
        g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
      (Eventually.of_forall hg0), hx]
  calc
    (∫⁻ y, ENNReal.ofReal (g y) ∂(R ∘ₘ m.withDensity (fun x => ENNReal.ofReal (h x)))) =
        ∫⁻ x, ENNReal.ofReal (h x) * ∫⁻ y, ENNReal.ofReal (g y) ∂(R x) ∂m := by
      change (∫⁻ y, ENNReal.ofReal (g y) ∂(m.withDensity
        (fun x => ENNReal.ofReal (h x))).bind R) = _
      rw [Measure.lintegral_bind R.aemeasurable hgm.aemeasurable,
        lintegral_withDensity_eq_lintegral_mul _ hhm hgm.lintegral_kernel]
      rfl
    _ = ∫⁻ x, ENNReal.ofReal (a x) * ENNReal.ofReal (G b x) ∂m := by
      apply lintegral_congr_ae
      filter_upwards [compactToLp_coe h, hRg] with x hx hr
      rw [hr, hx]
    _ = ENNReal.ofReal (inner ℝ a (G b)) := (ofReal_inner_eq_lintegral a (G b) ha0 hGb0).symm
    _ = ENNReal.ofReal (inner ℝ b (G a)) := congrArg ENNReal.ofReal (hsymm a b)
    _ = ∫⁻ x, ENNReal.ofReal (b x) * ENNReal.ofReal (G a x) ∂m :=
      ofReal_inner_eq_lintegral b (G a) hb0 hGa0
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂m.withDensity
        (fun x => ENNReal.ofReal (G a x)) := by
      rw [lintegral_withDensity_eq_lintegral_mul₀'
        (Lp.aestronglyMeasurable (G a)).aemeasurable.ennreal_ofReal
        hgm.aemeasurable]
      simp only [Pi.mul_apply]
      apply lintegral_congr_ae
      filter_upwards [compactToLp_coe g] with x hx
      rw [hx, mul_comm]

end SubdiffusiveProcess.PartProcess
