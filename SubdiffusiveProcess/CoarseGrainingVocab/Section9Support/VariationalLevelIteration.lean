module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationStampacchia

@[expose] public section

/-!
# Level recursion without an assumed high integrability of the solution

For the variational Green equation, the solution initially belongs only
to weighted L². The positive-level Sobolev estimate itself supplies the
integrability of each truncation needed by the level recursion.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Homogenization Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The Sobolev level estimate gives the real upper-level volume recursion. -/
lemma variational_level_volume_recursion {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {u f : α → ℝ} {p q B : ℝ}
    (hp : 0 < p) (hq : 2 ≤ q) (hbalance : 1/q + 1/p = 1/2) (hB : 0 ≤ B)
    (hu : MemLp u 2 μ) (hf : MemLp f (ENNReal.ofReal q) μ)
    (hLevel : ∀ k : ℝ, 0 ≤ k →
      (eLpNorm (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ)^2 ≤
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x-k) 0) ∂μ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) :
    (l-k)^2 * ((μ {x | l < u x}).toReal)^(2/p) ≤
      B^2 * (eLpNorm f (ENNReal.ofReal q) μ).toReal^2 * (μ {x | k < u x}).toReal := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have htriple : Real.HolderTriple q p 2 := ⟨by simpa only [one_div] using hbalance, hq0, hp⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 2 := by
    simpa only [ENNReal.ofReal_ofNat] using htriple.ennrealOfReal
  have h2q : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq
  have hu2 := hu
  have hf2 := hf.mono_exponent h2q
  let v : α → ℝ := fun x => max (u x-k) 0
  have hv0 (x : α) : 0 ≤ v x := le_max_right _ _
  have hvp : MemLp v (ENNReal.ofReal p) μ :=
    memLp_positiveTruncation_of_level_bound hu2 hf2 hk (hLevel k hk)
  have hv2 : MemLp v 2 μ := memLp_positiveTruncation hu2 hk
  have hfabs : MemLp (fun x => |f x|) 2 μ := by simpa only [Real.norm_eq_abs] using hf2.norm
  let L := ∫⁻ x, ENNReal.ofReal (|f x| * v x) ∂μ
  let V := (eLpNorm v (ENNReal.ofReal p) μ).toReal
  let N := (eLpNorm f (ENNReal.ofReal q) μ).toReal
  let a := (μ {x | k < u x}).toReal
  have hi : Integrable (fun x => |f x| * v x) μ := hfabs.integrable_mul hv2
  have hLN : L ≠ ∞ := by
    dsimp only [L]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (hv0 x))]
    exact ENNReal.ofReal_ne_top
  have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLN) (hLevel k hk)
  have hrealLevel : V^2 ≤ B * L.toReal := by
    simpa only [V, L, v, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] using hR
  have hsupp (x : α) (hx : x ∉ {x | k < u x}) : v x = 0 := by
    exact max_eq_right (sub_nonpos.mpr (not_lt.mp hx))
  have hholder : L ≤ eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ *
      (μ {x | k < u x})^(1/2 : ℝ) := by
    simpa only [L, abs_of_nonneg (hv0 _)] using
      lintegral_abs_mul_le_norms_mul_sqrt_measure hf.aestronglyMeasurable
        hvp.aestronglyMeasurable {x | k < u x} hsupp
  have hhTop : eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ *
      (μ {x | k < u x})^(1/2 : ℝ) ≠ ∞ := by
    have hfn := hf.eLpNorm_lt_top
    have hvn := hvp.eLpNorm_lt_top
    have hsn := measure_lt_top μ {x | k < u x}
    finiteness
  have hrealHolder : L.toReal ≤ N * V * a^(1/2 : ℝ) := by
    simpa only [N, V, a, ENNReal.toReal_mul, ENNReal.toReal_rpow] using
      ENNReal.toReal_mono hhTop hholder
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hhalf0 : 0 ≤ a^(1/2 : ℝ) := Real.rpow_nonneg ha0 _
  have hVN : V ≤ B*N*a^(1/2 : ℝ) := by
    have hC0 : 0 ≤ B*N*a^(1/2 : ℝ) := mul_nonneg (mul_nonneg hB hN0) hhalf0
    have hbound : V^2 ≤ V*(B*N*a^(1/2 : ℝ)) := by
      calc
        V^2 ≤ B*L.toReal := hrealLevel
        _ ≤ B*(N*V*a^(1/2 : ℝ)) := mul_le_mul_of_nonneg_left hrealHolder hB
        _ = _ := by ring
    nlinarith
  have hsqrt : (a^(1/2 : ℝ))^2 = a := by
    rw [← Real.rpow_natCast (a^(1/2 : ℝ)) 2, ← Real.rpow_mul ha0]
    norm_num
  have hVsquare : V^2 ≤ B^2*N^2*a := by
    have hsq := pow_le_pow_left₀ hV0 hVN 2
    simpa only [mul_pow, hsqrt] using hsq
  have hnormLower := positiveTruncation_level_norm_lower μ hu.aestronglyMeasurable hp hkl
  have hnormLowerReal : (l-k)*(μ {x | l < u x}).toReal^(1/p) ≤ V := by
    simpa only [V, v, ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hkl.le)] using
      ENNReal.toReal_mono hvp.eLpNorm_lt_top.ne hnormLower
  have hlow0 : 0 ≤ (l-k)*(μ {x | l < u x}).toReal^(1/p) :=
    mul_nonneg (sub_nonneg.mpr hkl.le) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hsq := pow_le_pow_left₀ hlow0 hnormLowerReal 2
  have hpower : ((μ {x | l < u x}).toReal^(1/p))^2 =
      (μ {x | l < u x}).toReal^(2/p) := by
    rw [← Real.rpow_natCast ((μ {x | l < u x}).toReal^(1/p)) 2,
      ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    push_cast
    ring
  rw [mul_pow, hpower] at hsq
  exact hsq.trans hVsquare

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
