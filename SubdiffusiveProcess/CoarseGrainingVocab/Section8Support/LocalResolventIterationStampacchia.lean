module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L2Space
public import Homogenization.HighContrast.Coupled.Stampacchia.Iteration

@[expose] public section

/-!
# A sharp positive-level Stampacchia estimate

The level estimate and Hölder give a superlinear recursion for upper-level
volumes. Starting the iteration at `sqrt B * ‖f‖q` and using the `Lq` contraction
leaves only a constant depending on the Sobolev exponent. All functions retain
their original almost-everywhere representatives, and the measure need only be finite.
-/
open MeasureTheory Homogenization Filter Set
open scoped ENNReal NNReal Topology
noncomputable section
set_option autoImplicit false
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

/-- The source exponent balances the Sobolev exponent and the level-volume power. -/
lemma stampacchia_exponents {p : ℝ} (hp : 2 < p) :
    0 < 1-2/p ∧ 2 < 2/(1-2/p) ∧
    1/(2/(1-2/p)) + 1/p = 1/2 ∧
    (2/(1-2/p)) * (p/2-1) / 2 = p/2 := by
  have hp0 : 0 < p := by linarith
  have ht : 0 < 1-2/p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  refine ⟨ht, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ ht).mpr
    nlinarith [div_pos (show (0:ℝ)<2 by norm_num) hp0]
  · field_simp
    ring
  · field_simp [show p-2 ≠ 0 by linarith, show -2+p ≠ 0 by linarith]

/-- Every nonnegative-level truncation is dominated in `Lᵖ` by its original function. -/
lemma memLp_positiveTruncation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → ℝ} {p : ENNReal} (hu : MemLp u p μ) {k : ℝ} (hk : 0 ≤ k) :
    MemLp (fun x => max (u x-k) 0) p μ := by
  have hm : AEMeasurable (fun x => max (u x-k) 0) μ :=
    (hu.aemeasurable.sub aemeasurable_const).max aemeasurable_const
  refine hu.mono hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (u x-k) 0)]
  exact max_le ((sub_le_self _ hk).trans (le_abs_self _)) (abs_nonneg _)

/-- Vanishing upper-level volumes give an almost-everywhere upper bound. -/
lemma ae_le_of_deGiorgi_level_decay {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (u : α → ℝ) {m K : ℝ} (hK : 0 < K)
    (hdecay : Tendsto (fun n : ℕ => (μ {x | m + deGiorgiLevel K n < u x}).toReal)
      atTop (𝓝 0)) : ∀ᵐ x ∂μ, u x ≤ m+K := by
  have hz : μ {x | m+K < u x} = 0 := by
    apply measure_eq_zero_of_toReal_tendsto (measure_ne_top _ _) _ hdecay
    intro n
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro x hx
    change m + K < u x at hx
    change m + deGiorgiLevel K n < u x
    linarith [deGiorgiLevel_lt hK n]
  simpa only [ae_iff, not_le] using hz

/-- A level gap bounds the truncation norm from below on the next level set. -/
lemma positiveTruncation_level_norm_lower {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {u : α → ℝ} (hu : AEStronglyMeasurable u μ)
    {p k l : ℝ} (hp : 0 < p) (hkl : k < l) :
    ENNReal.ofReal (l-k) * (μ {x | l < u x}) ^ (1/p) ≤
      eLpNorm (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ := by
  classical
  have hs : NullMeasurableSet {x | l < u x} μ :=
    nullMeasurableSet_lt aemeasurable_const hu.aemeasurable
  calc
    ENNReal.ofReal (l-k) * (μ {x | l < u x}) ^ (1/p) =
        eLpNorm ({x | l < u x}.indicator (fun _ => l-k)) (ENNReal.ofReal p) μ := by
      rw [eLpNorm_indicator_const₀ hs (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal (sub_nonneg.mpr hkl.le)]
    _ ≤ _ := by
      apply eLpNorm_mono (aestronglyMeasurable_const.indicator₀ hs)
      intro x
      by_cases hx : x ∈ {x | l < u x}
      · rw [Set.indicator_of_mem hx]
        simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hkl.le),
          abs_of_nonneg (le_max_right (u x-k) 0)]
        exact (sub_le_sub_right hx.le k).trans (le_max_left _ _)
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _

/-- Chebyshev bounds the real mass of a positive upper-level set. -/
lemma level_volume_le_norm_div_rpow {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {u : α → ℝ} {q t : ℝ} (hq : 0 < q)
    (hu : MemLp u (ENNReal.ofReal q) μ) (ht : 0 < t) :
    (μ {x | t < u x}).toReal ≤ ((eLpNorm u (ENNReal.ofReal q) μ).toReal / t)^q := by
  have hlow := positiveTruncation_level_norm_lower μ hu.aestronglyMeasurable hq ht
  have htrunc : eLpNorm (fun x => max (u x-0) 0) (ENNReal.ofReal q) μ ≤
      eLpNorm u (ENNReal.ofReal q) μ := by
    apply eLpNorm_mono
      (memLp_positiveTruncation hu (le_refl 0)).aestronglyMeasurable
    intro x
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (le_max_right (u x) 0)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hreal : t * (μ {x | t < u x}).toReal^(1/q) ≤
      (eLpNorm u (ENNReal.ofReal q) μ).toReal := by
    simpa only [sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
      ENNReal.toReal_rpow] using ENNReal.toReal_mono hu.eLpNorm_lt_top.ne (hlow.trans htrunc)
  have hdiv : (μ {x | t < u x}).toReal^(1/q) ≤
      (eLpNorm u (ENNReal.ofReal q) μ).toReal / t := by
    rw [le_div_iff₀ ht]
    simpa only [mul_comm] using hreal
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) hdiv hq.le
  simpa only [← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hq.ne', Real.rpow_one] using hpow


/-- Hölder localizes a product to its support with a square-root volume factor. -/
lemma lintegral_abs_mul_le_norms_mul_sqrt_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f v : α → ℝ} {p q : ENNReal}
    [ENNReal.HolderTriple q p 2]
    (hf : AEStronglyMeasurable f μ) (hv : AEStronglyMeasurable v μ)
    (S : Set α) (hS : ∀ x ∉ S, v x = 0) :
    (∫⁻ x, ENNReal.ofReal (|f x| * |v x|) ∂μ) ≤
      eLpNorm f q μ * eLpNorm v p μ * (μ S) ^ (1/2 : ℝ) := by
  have hsupport : Function.support (fun x => ENNReal.ofReal (|f x| *|v x|)) ⊆ S := by
    intro x hx
    by_contra hxS
    exact hx (by simp [hS x hxS])
  rw [← setLIntegral_eq_of_support_subset hsupport]
  have hnorm : (∫⁻ x in S, ENNReal.ofReal (|f x| * |v x|) ∂μ) =
      eLpNorm (fun x => f x*v x) 1 (μ.restrict S) := by
    change _ = eLpNorm (f * v) 1 (μ.restrict S)
    rw [eLpNorm_one_eq_lintegral_enorm (hf.restrict.mul hv.restrict)]
    simp only [Pi.mul_apply, ← ofReal_norm, Real.norm_eq_abs, abs_mul]
  rw [hnorm]
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict S) (p := 1) (q := 2) (by norm_num) (hf.restrict.mul hv.restrict)
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_one, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, div_one, show (1:ℝ)-1/2=1/2 by norm_num] at hcompare
  have hholder := eLpNorm_smul_le_mul_eLpNorm (μ := μ.restrict S) (p := q) (q := p) (r := 2) hf.restrict hv.restrict
  simp only [smul_eq_mul] at hholder
  have hprod : eLpNorm (fun x => f x*v x) 2 (μ.restrict S) ≤ eLpNorm f q μ * eLpNorm v p μ :=
    hholder.trans (mul_le_mul' (eLpNorm_restrict_le f q μ S) (eLpNorm_restrict_le v p μ S))
  exact hcompare.trans (mul_le_mul_left hprod _)

/-- The level estimate upgrades an `L²` truncation to the Sobolev exponent. -/
lemma memLp_positiveTruncation_of_level_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u f : α → ℝ} {p : ENNReal} {B k : ℝ}
    (hu : MemLp u 2 μ) (hf : MemLp f 2 μ) (hk : 0 ≤ k)
    (hlevel : (eLpNorm (fun x => max (u x-k) 0) p μ)^2 ≤
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| *max (u x-k) 0) ∂μ) :
    MemLp (fun x => max (u x-k) 0) p μ := by
  have hv := memLp_positiveTruncation hu hk
  have hfabs : MemLp (fun x => |f x|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hi : Integrable (fun x => |f x| * max (u x-k) 0) μ := hfabs.integrable_mul hv
  have hR : (∫⁻ x, ENNReal.ofReal (|f x| *max (u x-k) 0) ∂μ) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (le_max_right _ _))]
    exact ENNReal.ofReal_lt_top
  have hN := hlevel.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR)
  by_contra hn
  have ht : eLpNorm (fun x => max (u x-k) 0) p μ = ∞ := top_le_iff.mp (not_lt.mp hn)
  simp [ht] at hN

/-- The Sobolev level estimate gives the real upper-level volume recursion. -/
lemma positiveTruncation_level_volume_recursion {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {u f : α → ℝ} {p q B : ℝ}
    (hp : 0 < p) (hq : 2 ≤ q) (hbalance : 1/q + 1/p = 1/2) (hB : 0 ≤ B)
    (hu : MemLp u (ENNReal.ofReal q) μ) (hf : MemLp f (ENNReal.ofReal q) μ)
    (hLevel : ∀ k : ℝ, 0 ≤ k →
      (eLpNorm (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ)^2 ≤
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x-k) 0) ∂μ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) :
    (l-k)^2 * ((μ {x | l < u x}).toReal)^(2/p) ≤
      B^2 * (eLpNorm f (ENNReal.ofReal q) μ).toReal^2 * (μ {x | k < u x}).toReal := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have htriple : Real.HolderTriple q p 2 := ⟨by simpa only [one_div] using hbalance, hq0, hp⟩
  let : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 2 := by
    simpa only [ENNReal.ofReal_ofNat] using htriple.ennrealOfReal
  have h2q : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq
  have hu2 := hu.mono_exponent h2q
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

/-- Real-exponent version of `Homogenization.deGiorgi_admissible`, with the same
critical-power cancellation and constant choice. -/
theorem deGiorgi_admissible_real_exponent
    {d : ℝ} {C_F E₀ L Cd α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hβeq : β = α - 1) (hB : d * β = 2 * α)
    (hCF : 0 ≤ C_F) (hE₀ : 0 < E₀) (hL : 0 < L) (hCd : 0 < Cd)
    (hchoice : C_F * ((4 : ℝ) ^ α) ^ (1 / (2 * β)) ≤ Cd) :
    (((C_F ^ 2 * E₀ ^ 2) / (Cd * L * E₀) ^ 2) ^ α) * ((4 : ℝ) ^ α) * ((L ^ d) ^ β)
      ≤ ((4 : ℝ) ^ α) ^ (-(1 / β)) := by
  set B : ℝ := (4 : ℝ) ^ α with hBdef
  have hBpos : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  -- Abbreviate `t := C_F / Cd`.
  set t : ℝ := C_F / Cd with htdef
  have ht0 : 0 ≤ t := div_nonneg hCF hCd.le
  -- Step 1: `Crec/K² = t² / L²`.
  have hK2 : (Cd * L * E₀) ^ 2 = Cd ^ 2 * L ^ 2 * E₀ ^ 2 := by ring
  have hCd0 : Cd ≠ 0 := hCd.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hE00 : E₀ ≠ 0 := hE₀.ne'
  have hstep1 : (C_F ^ 2 * E₀ ^ 2) / (Cd * L * E₀) ^ 2 = t ^ 2 / L ^ 2 := by
    rw [hK2, htdef, div_pow]
    field_simp
  rw [hstep1]
  -- Step 2: `(t²/L²)^α = t^{2α} · L^{-2α}`.
  have hL2 : (0 : ℝ) ≤ L ^ 2 := by positivity
  have ht2 : (0 : ℝ) ≤ t ^ 2 := by positivity
  have hdiv : (t ^ 2 / L ^ 2) ^ α = (t ^ 2) ^ α / (L ^ 2) ^ α :=
    Real.div_rpow ht2 hL2 α
  -- `(t²)^α = t^{2α}`, `(L²)^α = L^{2α}`.
  have hLd : ((L ^ d) ^ β) = L ^ (d * β) := by
    rw [← Real.rpow_mul hL.le]
  have hL2a : ((L ^ 2) ^ α) = L ^ (2 * α) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
    norm_num
  have ht2a : ((t ^ 2) ^ α) = t ^ (2 * α) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0]
    norm_num
  -- Assemble the `L`-cancellation.
  rw [hdiv, hLd, hL2a, ht2a, hB]
  -- Goal: `t^{2α} / L^{2α} * B * L^{2α} ≤ B^{−1/β}`.
  have hLα_pos : (0 : ℝ) < L ^ (2 * α) := Real.rpow_pos_of_pos hL _
  have hcollapse :
      t ^ (2 * α) / L ^ (2 * α) * B * L ^ (2 * α) = B * t ^ (2 * α) := by
    have hne : L ^ (2 * α) ≠ 0 := hLα_pos.ne'
    field_simp
  rw [hcollapse]
  -- Step 3: `t ≤ B^{-1/(2β)}`, hence `B · t^{2α} ≤ B^{-1/β}`.
  have hBpow : (0 : ℝ) < B ^ (1 / (2 * β)) := Real.rpow_pos_of_pos hBpos _
  have ht_le : t ≤ B ^ (-(1 / (2 * β))) := by
    have h1 : t * B ^ (1 / (2 * β)) ≤ 1 := by
      rw [htdef, div_mul_eq_mul_div, div_le_one hCd]
      exact hchoice
    rw [Real.rpow_neg hBpos.le, ← one_div]
    exact (le_div_iff₀ hBpow).mpr h1
  -- Raise to `2α`.
  have h2α : (0 : ℝ) < 2 * α := by positivity
  have htpow : t ^ (2 * α) ≤ (B ^ (-(1 / (2 * β)))) ^ (2 * α) :=
    Real.rpow_le_rpow ht0 ht_le h2α.le
  have hRHSpow : (B ^ (-(1 / (2 * β)))) ^ (2 * α) = B ^ (-(1 / β) - 1) := by
    rw [← Real.rpow_mul hBpos.le]
    congr 1
    -- `-(1/(2β)) · 2α = -(1/β) - 1`, using `α = β + 1`.
    have hαβ : α = β + 1 := by rw [hβeq]; ring
    rw [hαβ]
    field_simp
    ring
  calc B * t ^ (2 * α)
      ≤ B * (B ^ (-(1 / (2 * β)))) ^ (2 * α) :=
        mul_le_mul_of_nonneg_left htpow hBpos.le
    _ = B * B ^ (-(1 / β) - 1) := by rw [hRHSpow]
    _ = B ^ (1 + (-(1 / β) - 1)) := by
        rw [Real.rpow_add hBpos, Real.rpow_one]
    _ = B ^ (-(1 / β)) := by congr 1; ring


/-- The exponent-dependent constant in the positive-level Stampacchia estimate. -/
noncomputable def stampacchiaConstant (p : ℝ) : ℝ :=
  1 + ((4 : ℝ)^(p/2))^(1/(2*(p/2-1)))

/-- The exponent-dependent Stampacchia constant is strictly positive. -/
lemma stampacchiaConstant_pos (p : ℝ) : 0 < stampacchiaConstant p := by
  unfold stampacchiaConstant
  have h := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (show (0:ℝ)<4 by norm_num) (p/2))
    (1/(2*(p/2-1)))
  linarith

/-- Positive-level Sobolev bounds and an `Lᵠ` contraction give a sharp square-root bound. -/
theorem ae_le_of_positive_level_estimates {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {p B : ℝ} (hp : 2 < p) (hB : 0 < B)
    {u f : α → ℝ}
    (hu : MemLp u (ENNReal.ofReal (2/(1-2/p))) μ)
    (hf : MemLp f (ENNReal.ofReal (2/(1-2/p))) μ)
    (hcontract : eLpNorm u (ENNReal.ofReal (2/(1-2/p))) μ ≤
      eLpNorm f (ENNReal.ofReal (2/(1-2/p))) μ)
    (hLevel : ∀ k : ℝ, 0 ≤ k →
      (eLpNorm (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ)^2 ≤
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x-k) 0) ∂μ) :
    ∀ᵐ x ∂μ, u x ≤ stampacchiaConstant p * Real.sqrt B *
      (eLpNorm f (ENNReal.ofReal (2/(1-2/p))) μ).toReal := by
  let q := 2/(1-2/p)
  let aExp := p/2
  let bExp := aExp-1
  let C := ((4 : ℝ)^aExp)^(1/(2*bExp))
  let N := (eLpNorm f (ENNReal.ofReal q) μ).toReal
  change ∀ᵐ x ∂μ, u x ≤ (1+C)*Real.sqrt B*N
  obtain ⟨htheta, hq2, hbalance, hqb⟩ := stampacchia_exponents hp
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := lt_trans (by norm_num) hq2
  have haExp : 0 < aExp := div_pos hp0 (by norm_num)
  have haExp1 : 1 < aExp := by dsimp only [aExp]; linarith
  have hbExp : 0 < bExp := sub_pos.mpr haExp1
  have hC : 0 < C := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) aExp) _
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases hNz : N = 0
  · have hfn : eLpNorm f (ENNReal.ofReal q) μ = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hNz).resolve_right hf.eLpNorm_lt_top.ne
    have hun : eLpNorm u (ENNReal.ofReal q) μ = 0 := le_antisymm (hcontract.trans_eq hfn) zero_le
    have huz := (eLpNorm_eq_zero_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0))).mp hun
    filter_upwards [huz] with x hx
    simp only [Pi.zero_apply] at hx
    simp only [hx, hNz, mul_zero, le_refl]
  have hN : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
  let L := (Real.sqrt B)⁻¹
  let m := N/L
  let E0 := B*N
  let K := C*L*E0
  let a : ℝ → ℝ := fun k => (μ {x | m+k < u x}).toReal
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hL : 0 < L := inv_pos.mpr hsqrt
  have hm : 0 < m := div_pos hN hL
  have hE0 : 0 < E0 := mul_pos hB hN
  have hK : 0 < K := mul_pos (mul_pos hC hL) hE0
  have hLd : 0 < L^q := Real.rpow_pos_of_pos hL _
  have hNu : (eLpNorm u (ENNReal.ofReal q) μ).toReal ≤ N :=
    ENNReal.toReal_mono hf.eLpNorm_lt_top.ne hcontract
  have hNm : N/m = L := by
    dsimp only [m]
    field_simp
  have hinit : a (deGiorgiLevel K 0) ≤ L^q := by
    have hvol := level_volume_le_norm_div_rpow μ hq0 hu hm
    have hmono := Real.rpow_le_rpow (div_nonneg ENNReal.toReal_nonneg hm.le)
      (div_le_div_of_nonneg_right hNu hm.le) hq0.le
    rw [hNm] at hmono
    simpa only [a, deGiorgiLevel_zero, add_zero] using hvol.trans hmono
  have hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l-k)^2 * (a l)^(2/p) ≤ (B^2*N^2)*a k := by
    intro k l hk hkl
    have h := positiveTruncation_level_volume_recursion μ hp0 hq2.le hbalance hB.le hu hf hLevel
      (show 0 ≤ m+k by linarith) (show m+k < m+l by linarith)
    simpa only [a, N, show m+l-(m+k)=l-k by ring] using h
  have hcritical : q*bExp = 2*aExp := by
    change q*(p/2-1) = 2*(p/2)
    nlinarith [hqb]
  have hadm := deGiorgi_admissible_real_exponent (d := q) (C_F := 1) (E₀ := E0)
    (L := L) (Cd := C) (α := aExp) (β := bExp) haExp hbExp rfl hcritical
    (by norm_num) hE0 hL hC (by simp only [one_mul]; exact le_rfl)
  have hKcond : ((B^2*N^2)/K^2)^aExp * (4:ℝ)^aExp * (L^q)^bExp ≤
      ((4:ℝ)^aExp)^(-(1/bExp)) := by
    simpa only [E0, K, one_pow, one_mul, mul_pow] using hadm
  have hdecay := deGiorgi_levelVolume_tendsto_zero (a := a) (Ld := L^q)
    (Crec := B^2*N^2) (K := K) (α := aExp) (β := bExp) (γ := 2/p) (B := (4:ℝ)^aExp)
    (fun _ => ENNReal.toReal_nonneg) hLd (by positivity) hK haExp1 rfl
    (by dsimp only [aExp]; field_simp) rfl hinit hrec hKcond
  have hAE := ae_le_of_deGiorgi_level_decay μ u hK hdecay
  have hLB : L*B = Real.sqrt B := by
    calc
      L*B = L*(Real.sqrt B)^2 := congrArg (fun z => L*z) (Real.sq_sqrt hB.le).symm
      _ = Real.sqrt B := by dsimp only [L]; field_simp
  have hmEq : m = N*Real.sqrt B := by
    simp only [m, L, div_inv_eq_mul]
  have hKEq : K = C*Real.sqrt B*N := by
    calc
      K = C*(L*B)*N := by dsimp only [K, E0]; ring
      _ = _ := by rw [hLB]
  have hsum : m+K = (1+C)*Real.sqrt B*N := by rw [hmEq, hKEq]; ring
  rwa [hsum] at hAE

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
