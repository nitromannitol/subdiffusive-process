import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFourierPairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff




open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.Section8Resolvent.FluxRowFourier

private theorem continuous_classicalFourier {d : ℕ} {f : Vec d → ℂ}
    (hf : Integrable f volume) : Continuous (𝓕 f) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hf

/-- Fubini's weak Fourier identity, in the orientation used by the `L²`
inner product. -/
theorem integral_inner_classicalFourier (d : ℕ) (f : Vec d → ℂ)
    (hf : Integrable f volume) (g : SchwartzMap (Vec d) ℂ) :
    ∫ xi, inner ℂ (g xi) (𝓕 f xi) =
      ∫ x, inner ℂ (𝓕⁻ (g : Vec d → ℂ) x) (f x) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (L := innerₗ (Vec d)) (μ := volume) (ν := volume)
    (innerSL ℂ) Real.continuous_fourierChar continuous_inner hf g.integrable
  have h' : (∫ xi, inner ℂ (𝓕 f xi) (g xi)) =
      ∫ x, inner ℂ (f x) (𝓕⁻ (g : Vec d → ℂ) x) := by
    simpa using h
  calc
    ∫ xi, inner ℂ (g xi) (𝓕 f xi) =
        ∫ xi, star (inner ℂ (𝓕 f xi) (g xi)) :=
      integral_congr_ae (ae_of_all volume fun xi ↦ (inner_conj_symm _ _).symm)
    _ = star (∫ xi, inner ℂ (𝓕 f xi) (g xi)) := integral_conj
    _ = star (∫ x, inner ℂ (f x) (𝓕⁻ (g : Vec d → ℂ) x)) := congrArg star h'
    _ = ∫ x, star (inner ℂ (f x) (𝓕⁻ (g : Vec d → ℂ) x)) := integral_conj.symm
    _ = ∫ x, inner ℂ (𝓕⁻ (g : Vec d → ℂ) x) (f x) :=
      integral_congr_ae (ae_of_all volume fun x ↦ inner_conj_symm _ _)

/-- For `f ∈ L¹ ∩ L²`, the classical Fourier integral is an almost-everywhere
representative of the extended `L²` Fourier transform. -/
theorem euclideanL2FourierTransform_ae_eq_classical (d : ℕ) (f : Vec d → ℂ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    (euclideanL2FourierTransform d (hf2.toLp f) : Vec d → ℂ) =ᵐ[volume] 𝓕 f := by
  have hclassLocal : LocallyIntegrable (𝓕 f) volume :=
    (continuous_classicalFourier hf1).locallyIntegrable
  have hextLocal : LocallyIntegrable
      (euclideanL2FourierTransform d (hf2.toLp f) : Vec d → ℂ) volume :=
    (Lp.memLp (euclideanL2FourierTransform d (hf2.toLp f))).locallyIntegrable (by norm_num)
  apply (ae_eq_of_integral_contDiff_smul_eq hextLocal hclassLocal)
  intro g hg hsupp
  let gc : Vec d → ℂ := fun x ↦ Complex.ofReal (g x)
  have hgc : ContDiff ℝ (↑(⊤ : ℕ∞)) gc := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g)
    exact Complex.ofRealCLM.contDiff.comp hg
  have hgcSupp : HasCompactSupport gc := by
    simpa only [gc, Function.comp_def] using hsupp.comp_left (by simp)
  let phi : SchwartzMap (Vec d) ℂ := hgcSupp.toSchwartzMap hgc
  calc
    ∫ x, g x • (euclideanL2FourierTransform d (hf2.toLp f) : Vec d → ℂ) x =
        ∫ x, inner ℂ (phi x)
          ((euclideanL2FourierTransform d (hf2.toLp f) : Vec d → ℂ) x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [phi, gc, RCLike.inner_apply, mul_comm]
    _ = inner ℂ (phi.toLp 2 volume)
          (euclideanL2FourierTransform d (hf2.toLp f)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [phi.coeFn_toLp 2 volume] with x hx
      rw [hx]
    _ = inner ℂ ((𝓕⁻ phi).toLp 2 volume) (hf2.toLp f) :=
      inner_euclideanL2FourierTransform d phi (hf2.toLp f)
    _ = ∫ x, inner ℂ ((𝓕⁻ phi : SchwartzMap (Vec d) ℂ) x) (f x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(𝓕⁻ phi).coeFn_toLp 2 volume, hf2.coeFn_toLp] with x hx hfx
      rw [hx, hfx]
    _ = ∫ x, inner ℂ (phi x) (𝓕 f x) := by
      simpa only [SchwartzMap.fourierInv_coe] using
        (integral_inner_classicalFourier d f hf1 phi).symm
    _ = ∫ x, g x • 𝓕 f x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [phi, gc, RCLike.inner_apply, mul_comm]

/-- The classical Fourier integral of an `L¹ ∩ L²` function belongs to `L²`. -/
theorem classicalFourier_memLp_two (d : ℕ) (f : Vec d → ℂ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume := by
  exact (memLp_congr_ae (euclideanL2FourierTransform_ae_eq_classical d f hf1 hf2)).mp
    (Lp.memLp (euclideanL2FourierTransform d (hf2.toLp f)))

/-- The equality in `L²` between the extended and classical transforms. -/
theorem euclideanL2FourierTransform_toLp_eq_classical (d : ℕ) (f : Vec d → ℂ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    euclideanL2FourierTransform d (hf2.toLp f) =
      (classicalFourier_memLp_two d f hf1 hf2).toLp (𝓕 f) := by
  calc
    euclideanL2FourierTransform d (hf2.toLp f) =
        (Lp.memLp (euclideanL2FourierTransform d (hf2.toLp f))).toLp
          (euclideanL2FourierTransform d (hf2.toLp f) : Vec d → ℂ) :=
      (Lp.toLp_coeFn _ _).symm
    _ = (classicalFourier_memLp_two d f hf1 hf2).toLp (𝓕 f) :=
      (Lp.memLp (euclideanL2FourierTransform d (hf2.toLp f))).toLp_congr
        (classicalFourier_memLp_two d f hf1 hf2)
        (euclideanL2FourierTransform_ae_eq_classical d f hf1 hf2)

end SubdiffusiveProcess.Section8Resolvent.FluxRowFourier
