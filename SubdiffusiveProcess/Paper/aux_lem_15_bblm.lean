module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_pos_sq (a : ℝ) :
    (max a 0) ^ 2 + (max (-a) 0) ^ 2 = a ^ 2 := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    ring
  · rw [max_eq_right ha, max_eq_left (neg_nonneg.mpr ha)]
    ring

theorem aux_pos_part_sub_le (a b c : ℝ) :
    max (max (a - c) 0 - max (b - c) 0) 0 ≤ max (a - b) 0 := by
  apply max_le
  · rcases le_total c a with ha | ha
    · rw [max_eq_left (sub_nonneg.mpr ha)]
      calc
        a - c - max (b - c) 0 ≤ a - c - (b - c) :=
          sub_le_sub_left (le_max_left _ _) _
        _ = a - b := by ring
        _ ≤ max (a - b) 0 := le_max_left _ _
    · rw [max_eq_right (sub_nonpos.mpr ha)]
      exact (sub_nonpos.mpr (le_max_right _ _)).trans (le_max_right _ _)
  · exact le_max_right _ _

theorem aux_rpow_tangent (a b r : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    a ^ r - b ^ r ≤ r * a ^ (r - 1) * (a - b) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 / r) (w₂ := (r - 1) / r)
    (p₁ := b ^ r) (p₂ := a ^ r)
    (div_nonneg zero_le_one hr0.le)
    (div_nonneg (sub_nonneg.mpr hr) hr0.le)
    (Real.rpow_nonneg hb r) (Real.rpow_nonneg ha r)
    (by field_simp [hr0.ne']; ring)
  have h₁ : (b ^ r) ^ (1 / r) = b := by
    rw [← Real.rpow_mul hb]
    simp [hr0.ne']
  have h₂ : (a ^ r) ^ ((r - 1) / r) = a ^ (r - 1) := by
    rw [← Real.rpow_mul ha]
    congr 1
    field_simp [hr0.ne']
  rw [h₁, h₂] at ht
  have ht' := mul_le_mul_of_nonneg_left ht hr0.le
  have hprod : a ^ r = a ^ (r - 1) * a := by
    calc
      a ^ r = a ^ ((r - 1) + 1) := by congr 1; ring
      _ = a ^ (r - 1) * a ^ (1 : ℝ) :=
        Real.rpow_add' ha (by linarith)
      _ = a ^ (r - 1) * a := by rw [Real.rpow_one]
  have hcancel : r * ((1 / r) * b ^ r + ((r - 1) / r) * a ^ r) =
      b ^ r + (r - 1) * a ^ r := by
    field_simp [hr0.ne']
  rw [hcancel, hprod] at ht'
  rw [hprod]
  nlinarith only [ht']

theorem aux_pos_rpow_difference (a b c p : ℝ) (hp : 2 ≤ p) :
    (max ((max (a - c) 0) ^ (p / 2) -
      (max (b - c) 0) ^ (p / 2)) 0) ^ 2 ≤
      (p / 2) ^ 2 * (max (a - c) 0) ^ (p - 2) * (max (a - b) 0) ^ 2 := by
  let x := max (a - c) 0
  let y := max (b - c) 0
  have hx : 0 ≤ x := le_max_right _ _
  have hy : 0 ≤ y := le_max_right _ _
  have hr : 1 ≤ p / 2 := by linarith
  have hr0 : 0 ≤ p / 2 := by linarith
  have hpow : (x ^ (p / 2 - 1)) ^ 2 = x ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring
  have ht : max (x ^ (p / 2) - y ^ (p / 2)) 0 ≤
      (p / 2) * x ^ (p / 2 - 1) * max (a - b) 0 := by
    apply max_le
    · calc
        x ^ (p / 2) - y ^ (p / 2) ≤ (p / 2) * x ^ (p / 2 - 1) * (x - y) :=
          aux_rpow_tangent x y (p / 2) hx hy hr
        _ ≤ (p / 2) * x ^ (p / 2 - 1) * max (x - y) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _)
            (mul_nonneg hr0 (Real.rpow_nonneg hx _))
        _ ≤ (p / 2) * x ^ (p / 2 - 1) * max (a - b) 0 :=
          mul_le_mul_of_nonneg_left (aux_pos_part_sub_le a b c)
            (mul_nonneg hr0 (Real.rpow_nonneg hx _))
    · exact mul_nonneg (mul_nonneg hr0 (Real.rpow_nonneg hx _)) (le_max_right _ _)
  have ht2 := mul_self_le_mul_self (le_max_right _ _) ht
  change (max (x ^ (p / 2) - y ^ (p / 2)) 0) ^ 2 ≤
    (p / 2) ^ 2 * x ^ (p - 2) * (max (a - b) 0) ^ 2
  calc
    (max (x ^ (p / 2) - y ^ (p / 2)) 0) ^ 2 ≤
        ((p / 2) * x ^ (p / 2 - 1) * max (a - b) 0) ^ 2 := by
      simpa only [pow_two] using ht2
    _ = (p / 2) ^ 2 * x ^ (p - 2) * (max (a - b) 0) ^ 2 := by
      rw [mul_pow, mul_pow, hpow]

theorem aux_integral_weighted_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Integrable (fun x => (f x) ^ a * (g x) ^ b) μ ∧
      (∫ x, (f x) ^ a * (g x) ^ b ∂μ) ≤
        (∫ x, f x ∂μ) ^ a * (∫ x, g x ∂μ) ^ b := by
  have hm : AEStronglyMeasurable (fun x => (f x) ^ a * (g x) ^ b) μ :=
    ((hf.aestronglyMeasurable.aemeasurable.pow_const a).mul
      (hg.aestronglyMeasurable.aemeasurable.pow_const b)).aestronglyMeasurable
  have hn : ∀ x, 0 ≤ (f x) ^ a * (g x) ^ b :=
    fun x => mul_nonneg (Real.rpow_nonneg (hf0 x) a) (Real.rpow_nonneg (hg0 x) b)
  have hi : Integrable (fun x => (f x) ^ a * (g x) ^ b) μ := by
    apply ((hf.const_mul a).add (hg.const_mul b)).mono' hm
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
      exact Real.geom_mean_le_arith_mean2_weighted ha hb (hf0 x) (hg0 x) hab
  refine ⟨hi, ?_⟩
  have h := ENNReal.lintegral_mul_norm_pow_le
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal ha hb hab
  have hleft :
      (∫⁻ x, (ENNReal.ofReal (f x)) ^ a * (ENNReal.ofReal (g x)) ^ b ∂μ) =
        ENNReal.ofReal (∫ x, (f x) ^ a * (g x) ^ b ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) a),
      ENNReal.ofReal_rpow_of_nonneg (hf0 x) ha,
      ENNReal.ofReal_rpow_of_nonneg (hg0 x) hb]
  rw [hleft,
    ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)] at h
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ha,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) hb,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) a)] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (mul_nonneg
      (Real.rpow_nonneg (integral_nonneg hf0) a)
      (Real.rpow_nonneg (integral_nonneg hg0) b))] using ht

theorem aux_integral_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Integrable (fun x => (f x) ^ a) μ ∧
      (∫ x, (f x) ^ a ∂μ) ≤ (∫ x, f x ∂μ) ^ a := by
  have h := aux_integral_weighted_rpow hf (integrable_const (1 : ℝ))
    hf0 (fun _ => zero_le_one) a (1 - a) ha (sub_nonneg.mpr ha1) (by ring)
  simpa using h

theorem aux_centered_sq_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) =
      (∫ x, (F x) ^ 2 ∂μ) - (∫ x, F x ∂μ) ^ 2 := by
  let c := ∫ x, F x ∂μ
  have hi : Integrable F μ := hF.integrable (by norm_num)
  have hs : Integrable (fun x => (F x) ^ 2) μ := hF.integrable_sq
  have heq : (fun x => (F x - c) ^ 2) =
      fun x => (F x) ^ 2 - (2 * c) * F x + c ^ 2 := by
    funext x
    ring
  have hconst : (∫ _ : Ω, c ^ 2 ∂μ) = c ^ 2 := by simp
  change (∫ x, (F x - c) ^ 2 ∂μ) = (∫ x, (F x) ^ 2 ∂μ) - c ^ 2
  have h1 : Integrable (fun x => (F x) ^ 2 - (2 * c) * F x) μ :=
    hs.sub (hi.const_mul (2 * c))
  rw [heq, integral_add h1 (integrable_const (c ^ 2)),
    integral_sub hs (hi.const_mul (2 * c)), integral_const_mul, hconst]
  change (∫ x, (F x) ^ 2 ∂μ) - (2 * c) * c + c ^ 2 =
    (∫ x, (F x) ^ 2 ∂μ) - c ^ 2
  ring

theorem aux_mean_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have h : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  rw [aux_centered_sq_integral hf] at h
  linarith only [h]

theorem aux_measurable_update
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)] (i : Fin m) :
    Measurable (fun z : ((j : Fin m) → Xi j) × Xi i =>
      Function.update z.1 i z.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using
      (measurable_snd : Measurable (fun z : ((j : Fin m) → Xi j) × Xi i => z.2))
  · simpa only [Function.update_of_ne hji, Function.comp_def] using
      (measurable_pi_apply j).comp
        (measurable_fst : Measurable (fun z : ((j : Fin m) → Xi j) × Xi i => z.1))

def aux_swapCoordinate
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)] (i : Fin m) :
    (((j : Fin m) → Xi j) × Xi i) ≃ᵐ (((j : Fin m) → Xi j) × Xi i) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv := by
    intro z
    rcases z with ⟨x, y⟩
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv := by
    intro z
    rcases z with ⟨x, y⟩
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  measurable_toFun := (aux_measurable_update i).prodMk
    ((measurable_pi_apply i).comp measurable_fst)
  measurable_invFun := (aux_measurable_update i).prodMk
    ((measurable_pi_apply i).comp measurable_fst)

theorem aux_swapCoordinate_mp
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    (i : Fin m) :
    MeasurePreserving (aux_swapCoordinate i)
      ((Measure.pi mu).prod (mu i)) ((Measure.pi mu).prod (mu i)) := by
  classical
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove Xi i
    let nu := Measure.pi (fun j : Fin n => mu (i.succAbove j))
    have he : MeasurePreserving e (Measure.pi mu) ((mu i).prod nu) :=
      measurePreserving_piFinSuccAbove mu i
    have hes : MeasurePreserving e.symm ((mu i).prod nu) (Measure.pi mu) :=
      by
        exact he.symm
    have ht : MeasurePreserving
        (fun z : (Xi i × ((j : Fin n) → Xi (i.succAbove j))) × Xi i =>
          ((z.2, z.1.2), z.1.1))
        (((mu i).prod nu).prod (mu i)) (((mu i).prod nu).prod (mu i)) := by
      have h₁ := measurePreserving_prodAssoc (mu i) nu (mu i)
      have h₂ := (MeasurePreserving.id (mu i)).prod
        (Measure.measurePreserving_swap (μ := nu) (ν := mu i))
      have h₃ := Measure.measurePreserving_swap
        (μ := mu i) (ν := (mu i).prod nu)
      exact h₃.comp (h₂.comp h₁)
    have h := (hes.prod (MeasurePreserving.id (mu i))).comp
      (ht.comp (he.prod (MeasurePreserving.id (mu i))))
    convert h using 1
    funext z
    rcases z with ⟨x, y⟩
    change (Function.update x i y, x i) =
      (Fin.insertNth i y (Fin.removeNth i x), x i)
    rw [Fin.insertNth_removeNth]

theorem aux_update_mp
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    (i : Fin m) :
    MeasurePreserving
      (fun z : ((j : Fin m) → Xi j) × Xi i => Function.update z.1 i z.2)
      ((Measure.pi mu).prod (mu i)) (Measure.pi mu) :=
  (measurePreserving_fst (μ := Measure.pi mu) (ν := mu i)).comp
    (aux_swapCoordinate_mp mu i)

theorem aux_memp2_integral_left
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {f : A × B → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 (mu.prod nu)) :
    Measurable (fun b => ∫ a, f (a, b) ∂mu) ∧
      MemLp (fun b => ∫ a, f (a, b) ∂mu) 2 nu := by
  have hm : Measurable (fun b => ∫ a, f (a, b) ∂mu) :=
    hf.stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hm, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_⟩
  have hs := hf2.integrable_sq
  apply hs.integral_prod_right.mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [hs.prod_left_ae] with b hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply aux_mean_sq_le
  exact (memLp_two_iff_integrable_sq
    (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hb

theorem aux_variance_pair
    {A : Type*} [MeasurableSpace A] {mu : Measure A} [IsProbabilityMeasure mu]
    {f : A → ℝ} (hf : MemLp f 2 mu) :
    (∫ x, (f x) ^ 2 ∂mu) - (∫ x, f x ∂mu) ^ 2 =
      (1 / 2 : ℝ) * ∫ x, ∫ y, (f x - f y) ^ 2 ∂mu ∂mu := by
  have hi : Integrable f mu := hf.integrable (by norm_num)
  have hs : Integrable (fun x => (f x) ^ 2) mu := hf.integrable_sq
  have hinner : ∀ x,
      (∫ y, (f x - f y) ^ 2 ∂mu) =
        (f x) ^ 2 - 2 * f x * (∫ y, f y ∂mu) + ∫ y, (f y) ^ 2 ∂mu := by
    intro x
    calc
      (∫ y, (f x - f y) ^ 2 ∂mu) =
          ∫ y, (f x) ^ 2 - (2 * f x) * f y + (f y) ^ 2 ∂mu := by
        congr 1
        funext y
        ring
      _ = (f x) ^ 2 - 2 * f x * (∫ y, f y ∂mu) + ∫ y, (f y) ^ 2 ∂mu := by
        have h1 : Integrable (fun y => (f x) ^ 2 - (2 * f x) * f y) mu :=
          (integrable_const _).sub (hi.const_mul _)
        rw [integral_add h1 hs,
          integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul]
        simp
  simp_rw [hinner]
  have h2 : Integrable (fun x => (f x) ^ 2 - 2 * f x * (∫ y, f y ∂mu)) mu :=
    hs.sub ((hi.const_mul 2).mul_const _)
  rw [integral_add h2 (integrable_const _),
    integral_sub hs ((hi.const_mul 2).mul_const _), integral_mul_const,
    integral_const_mul]
  simp ; ring

theorem aux_coord_diff_memp2
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin m) :
    MemLp (fun z : ((j : Fin m) → Xi j) × Xi i =>
      F z.1 - F (Function.update z.1 i z.2)) 2 ((Measure.pi mu).prod (mu i)) :=
  (hF.comp_measurePreserving
    (measurePreserving_fst (μ := Measure.pi mu) (ν := mu i))).sub
      (hF.comp_measurePreserving (aux_update_mp mu i))

theorem aux_coord_sq_integrable
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin m) :
    Integrable (fun x => ∫ y : Xi i,
      (F x - F (Function.update x i y)) ^ 2 ∂mu i) (Measure.pi mu) :=
  (aux_coord_diff_memp2 mu hF i).integrable_sq.integral_prod_left

theorem aux_outerSwap_mp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    MeasurePreserving (fun z : (A × B) × A => ((z.2, z.1.2), z.1.1))
      ((mu.prod nu).prod mu) ((mu.prod nu).prod mu) := by
  have h₁ := measurePreserving_prodAssoc mu nu mu
  have h₂ := (MeasurePreserving.id mu).prod
    (Measure.measurePreserving_swap (μ := nu) (ν := mu))
  have h₃ := Measure.measurePreserving_swap (μ := mu) (ν := mu.prod nu)
  exact h₃.comp (h₂.comp h₁)

theorem aux_integral_split
    {n : ℕ} {Xi : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin (n + 1)) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    (i : Fin (n + 1)) {F : ((i : Fin (n + 1)) → Xi i) → ℝ}
    (hF : Integrable F (Measure.pi mu)) :
    (∫ x, F x ∂Measure.pi mu) =
      ∫ a : Xi i, ∫ x : (j : Fin n) → Xi (i.succAbove j),
        F (Fin.insertNth i a x)
          ∂Measure.pi (fun j => mu (i.succAbove j)) ∂mu i := by
  let e := MeasurableEquiv.piFinSuccAbove Xi i
  have he : MeasurePreserving e.symm
      ((mu i).prod (Measure.pi (fun j : Fin n => mu (i.succAbove j))))
      (Measure.pi mu) := by
    exact (measurePreserving_piFinSuccAbove mu i).symm
  calc
    (∫ x, F x ∂Measure.pi mu) = ∫ z, F (e.symm z)
        ∂((mu i).prod (Measure.pi (fun j : Fin n => mu (i.succAbove j)))) :=
      (he.integral_comp' F).symm
    _ = ∫ a : Xi i, ∫ x : (j : Fin n) → Xi (i.succAbove j),
        F (Fin.insertNth i a x)
          ∂Measure.pi (fun j => mu (i.succAbove j)) ∂mu i :=
      integral_prod _ ((he.integrable_comp hF.aestronglyMeasurable).mpr hF)

theorem aux_integral_difference_jensen
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {f g : A × B → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (mu.prod nu)) (hg : MemLp g 2 (mu.prod nu)) :
    (∫ b, ((∫ a, f (a, b) ∂mu) - ∫ a, g (a, b) ∂mu) ^ 2 ∂nu) ≤
      ∫ b, ∫ a, (f (a, b) - g (a, b)) ^ 2 ∂mu ∂nu := by
  have hfbar := (aux_memp2_integral_left hfm hf).2
  have hgbar := (aux_memp2_integral_left hgm hg).2
  have hd := (hf.sub hg).integrable_sq
  apply integral_mono_ae (hfbar.sub hgbar).integrable_sq hd.integral_prod_right
  filter_upwards [(hf.integrable (by norm_num)).prod_left_ae,
    (hg.integrable (by norm_num)).prod_left_ae, hd.prod_left_ae] with b hfb hgb hdb
  simp only [Pi.sub_apply] at hdb ⊢
  rw [← integral_sub hfb hgb]
  apply aux_mean_sq_le
  apply (memLp_two_iff_integrable_sq
    ((hfm.sub hgm).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
  exact hdb

theorem aux_variance_split
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {f : A × B → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (mu.prod nu)) :
    (∫ z, (f z) ^ 2 ∂mu.prod nu) - (∫ z, f z ∂mu.prod nu) ^ 2 =
      (1 / 2 : ℝ) * (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂mu ∂nu ∂mu) +
        (∫ b, (∫ a, f (a, b) ∂mu) ^ 2 ∂nu) -
          (∫ b, ∫ a, f (a, b) ∂mu ∂nu) ^ 2 := by
  have hi := hf.integrable (by norm_num)
  have hs := hf.integrable_sq
  have hh := (aux_memp2_integral_left hfm hf).2
  have hf₁ : MemLp (fun z : (A × B) × A => f z.1) 2 ((mu.prod nu).prod mu) :=
    hf.comp_measurePreserving (measurePreserving_fst (μ := mu.prod nu) (ν := mu))
  have hf₂ : MemLp (fun z : (A × B) × A => f (z.2, z.1.2)) 2
      ((mu.prod nu).prod mu) :=
    hf₁.comp_measurePreserving (aux_outerSwap_mp mu nu)
  have hd := (hf₁.sub hf₂).integrable_sq
  have hswap :
      (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂mu ∂nu ∂mu) =
        ∫ b, ∫ a, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂mu ∂mu ∂nu :=
    integral_integral_swap hd.integral_prod_left
  have hpair :
      (1 / 2 : ℝ) * (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂mu ∂nu ∂mu) =
        (∫ z, (f z) ^ 2 ∂mu.prod nu) - (∫ b, (∫ a, f (a, b) ∂mu) ^ 2 ∂nu) := by
    rw [hswap, ← integral_const_mul]
    calc
      (∫ b, (1 / 2 : ℝ) * ∫ a, ∫ a',
          (f (a, b) - f (a', b)) ^ 2 ∂mu ∂mu ∂nu) =
          ∫ b, (∫ a, (f (a, b)) ^ 2 ∂mu) - (∫ a, f (a, b) ∂mu) ^ 2 ∂nu := by
        apply integral_congr_ae
        filter_upwards [hs.prod_left_ae] with b hb
        symm
        apply aux_variance_pair
        exact (memLp_two_iff_integrable_sq
          (hfm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hb
      _ = (∫ z, (f z) ^ 2 ∂mu.prod nu) - (∫ b, (∫ a, f (a, b) ∂mu) ^ 2 ∂nu) := by
        rw [integral_sub hs.integral_prod_right hh.integrable_sq,
          ← integral_prod_symm _ hs]
  rw [integral_prod_symm f hi]
  linarith only [hpair]

theorem aux_coord_average_le
    {n : ℕ} {Xi : Fin n → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin n) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {A : Type*} [MeasurableSpace A] (nu : Measure A) [IsProbabilityMeasure nu]
    {f : A × ((i : Fin n) → Xi i) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (nu.prod (Measure.pi mu)))
    (i : Fin n) :
    (∫ x, ∫ y : Xi i,
      ((∫ a, f (a, x) ∂nu) - (∫ a, f (a, Function.update x i y) ∂nu)) ^ 2
        ∂mu i ∂Measure.pi mu) ≤
      ∫ a, ∫ x, ∫ y : Xi i,
        (f (a, x) - f (a, Function.update x i y)) ^ 2
          ∂mu i ∂Measure.pi mu ∂nu := by
  let P := Measure.pi mu
  let f₁ : A × (((j : Fin n) → Xi j) × Xi i) → ℝ := fun z => f (z.1, z.2.1)
  let f₂ : A × (((j : Fin n) → Xi j) × Xi i) → ℝ :=
    fun z => f (z.1, Function.update z.2.1 i z.2.2)
  have hf₁m : Measurable f₁ :=
    hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hf₂m : Measurable f₂ :=
    hfm.comp (measurable_fst.prodMk ((aux_measurable_update i).comp measurable_snd))
  have hf₁ : MemLp f₁ 2 (nu.prod (P.prod (mu i))) :=
    hf.comp_measurePreserving ((MeasurePreserving.id nu).prod
      (measurePreserving_fst (μ := P) (ν := mu i)))
  have hf₂ : MemLp f₂ 2 (nu.prod (P.prod (mu i))) :=
    hf.comp_measurePreserving ((MeasurePreserving.id nu).prod (aux_update_mp mu i))
  have havg := aux_memp2_integral_left hfm hf
  have hdavg := (aux_coord_diff_memp2 mu havg.2 i).integrable_sq
  have hd := (hf₁.sub hf₂).integrable_sq
  calc
    (∫ x, ∫ y : Xi i,
      ((∫ a, f (a, x) ∂nu) - (∫ a, f (a, Function.update x i y) ∂nu)) ^ 2
        ∂mu i ∂Measure.pi mu) =
        ∫ z, ((∫ a, f₁ (a, z) ∂nu) - ∫ a, f₂ (a, z) ∂nu) ^ 2
          ∂P.prod (mu i) := (integral_prod _ hdavg).symm
    _ ≤ ∫ z, ∫ a, (f₁ (a, z) - f₂ (a, z)) ^ 2 ∂nu ∂P.prod (mu i) :=
      aux_integral_difference_jensen hf₁m hf₂m hf₁ hf₂
    _ = ∫ a, ∫ z, (f₁ (a, z) - f₂ (a, z)) ^ 2 ∂P.prod (mu i) ∂nu :=
      (integral_integral_swap hd).symm
    _ = ∫ a, ∫ x, ∫ y : Xi i,
        (f (a, x) - f (a, Function.update x i y)) ^ 2
          ∂mu i ∂Measure.pi mu ∂nu := by
      apply integral_congr_ae
      filter_upwards [hd.prod_right_ae] with a ha
      exact integral_prod _ ha

theorem aux_efronStein_two :
    ∀ (m : ℕ) (Xi : Fin m → Type*) [∀ i, MeasurableSpace (Xi i)]
      (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
      (F : ((i : Fin m) → Xi i) → ℝ),
      Measurable F → MemLp F 2 (Measure.pi mu) →
      (∫ x, (F x) ^ 2 ∂Measure.pi mu) - (∫ x, F x ∂Measure.pi mu) ^ 2 ≤
        (1 / 2 : ℝ) * ∑ i : Fin m,
          ∫ x, ∫ y : Xi i, (F x - F (Function.update x i y)) ^ 2
            ∂mu i ∂Measure.pi mu := by
  intro m
  induction m with
  | zero =>
    intro Xi _ mu _ F hFm hF
    let x₀ : (i : Fin 0) → Xi i := fun i => Fin.elim0 i
    have hc : F = fun _ => F x₀ := by
      funext x
      exact congrArg F (Subsingleton.elim x x₀)
    rw [hc]
    simp
  | succ n ih =>
    intro Xi _ mu _ F hFm hF
    let i₀ : Fin (n + 1) := 0
    let Y : Fin n → Type _ := fun j => Xi (i₀.succAbove j)
    let nu : (j : Fin n) → Measure (Y j) := fun j => mu (i₀.succAbove j)
    let P := Measure.pi mu
    let Q := Measure.pi nu
    let e := MeasurableEquiv.piFinSuccAbove Xi i₀
    have he : MeasurePreserving e.symm ((mu i₀).prod Q) P := by
      exact (measurePreserving_piFinSuccAbove mu i₀).symm
    let f : Xi i₀ × ((j : Fin n) → Y j) → ℝ := fun z => F (e.symm z)
    have hfm : Measurable f := hFm.comp e.symm.measurable
    have hf : MemLp f 2 ((mu i₀).prod Q) := hF.comp_measurePreserving he
    let h : ((j : Fin n) → Y j) → ℝ := fun x => ∫ a, f (a, x) ∂mu i₀
    have hh := aux_memp2_integral_left hfm hf
    have hind := ih Y nu h hh.1 hh.2
    let D : Fin (n + 1) → ℝ := fun i =>
      ∫ x, ∫ y : Xi i, (F x - F (Function.update x i y)) ^ 2 ∂mu i ∂P
    have hD (i : Fin (n + 1)) : D i =
        ∫ a : Xi i₀, ∫ x : (j : Fin n) → Y j, ∫ y : Xi i,
          (F (e.symm (a, x)) - F (Function.update (e.symm (a, x)) i y)) ^ 2
            ∂mu i ∂Q ∂mu i₀ :=
      aux_integral_split mu i₀ (aux_coord_sq_integrable mu hF i)
    have hu₀ (a y : Xi i₀) (x : (j : Fin n) → Y j) :
        Function.update (e.symm (a, x)) i₀ y = e.symm (y, x) := by
      change Function.update (Fin.insertNth i₀ a x) i₀ y = Fin.insertNth i₀ y x
      simp only [Fin.update_insertNth]
    have hu (j : Fin n) (a : Xi i₀) (x : (k : Fin n) → Y k) (y : Y j) :
        Function.update (e.symm (a, x)) (i₀.succAbove j) y =
          e.symm (a, Function.update x j y) := by
      change Function.update (Fin.insertNth i₀ a x) (i₀.succAbove j) y =
        Fin.insertNth i₀ a (Function.update x j y)
      simp only [Fin.insertNth_update]
    have hD₀ : D i₀ =
        ∫ a, ∫ x, ∫ y, (f (a, x) - f (y, x)) ^ 2 ∂mu i₀ ∂Q ∂mu i₀ := by
      simpa only [hu₀] using hD i₀
    have hDj (j : Fin n) : D (i₀.succAbove j) =
        ∫ a, ∫ x, ∫ y : Y j, (f (a, x) - f (a, Function.update x j y)) ^ 2
          ∂nu j ∂Q ∂mu i₀ := by
      simpa only [hu] using hD (i₀.succAbove j)
    have htail :
        (∑ j : Fin n, ∫ x, ∫ y : Y j,
          (h x - h (Function.update x j y)) ^ 2 ∂nu j ∂Q) ≤
          ∑ j : Fin n, D (i₀.succAbove j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [hDj]
      exact aux_coord_average_le nu (mu i₀) hfm hf j
    have hsum : (∑ i : Fin (n + 1), D i) =
        D i₀ + ∑ j : Fin n, D (i₀.succAbove j) := by
      simpa only [i₀, Fin.zero_succAbove] using Fin.sum_univ_succ D
    have hmean : (∫ z, f z ∂(mu i₀).prod Q) = ∫ x, F x ∂P :=
      he.integral_comp' F
    have hsquare : (∫ z, (f z) ^ 2 ∂(mu i₀).prod Q) = ∫ x, (F x) ^ 2 ∂P :=
      he.integral_comp' (fun x => (F x) ^ 2)
    have hsplit := aux_variance_split hfm hf
    rw [hmean, hsquare, ← hD₀] at hsplit
    change (∫ x, (F x) ^ 2 ∂P) - (∫ x, F x ∂P) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i : Fin (n + 1), D i
    rw [hsum]
    change (∫ x, (h x) ^ 2 ∂Q) - (∫ x, h x ∂Q) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ j : Fin n,
        ∫ x, ∫ y : Y j, (h x - h (Function.update x j y)) ^ 2 ∂nu j ∂Q at hind
    nlinarith only [hsplit, hind, htail]

theorem aux_memLp_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}
    {f : Ω → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (f x) 0) p μ := by
  apply hf.of_le
    (hf.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (le_abs_self _) (abs_nonneg _)

def aux_vPlus
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i))
    (F : ((i : Fin m) → Xi i) → ℝ) (x : (i : Fin m) → Xi i) : ℝ :=
  ∑ i : Fin m, ∫ y : Xi i,
    (max (F x - F (Function.update x i y)) 0) ^ 2 ∂mu i

theorem aux_vPlus_nonneg
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i))
    (F : ((i : Fin m) → Xi i) → ℝ) (x : (i : Fin m) → Xi i) :
    0 ≤ aux_vPlus mu F x := by
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun y => sq_nonneg _

theorem aux_coord_pos_sq_integrable
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin m) :
    Integrable (fun z : ((j : Fin m) → Xi j) × Xi i =>
      (max (F z.1 - F (Function.update z.1 i z.2)) 0) ^ 2)
      ((Measure.pi mu).prod (mu i)) :=
  (aux_memLp_pos (aux_coord_diff_memp2 mu hF i)).integrable_sq

theorem aux_vPlus_measurable
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : Measurable F) :
    Measurable (aux_vPlus mu F) := by
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun z : ((j : Fin m) → Xi j) × Xi i =>
      (max (F z.1 - F (Function.update z.1 i z.2)) 0) ^ 2) :=
    (((hF.comp measurable_fst).sub (hF.comp (aux_measurable_update i))).max
      measurable_const).pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem aux_vPlus_integrable
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu)) :
    Integrable (aux_vPlus mu F) (Measure.pi mu) := by
  apply integrable_finsetSum
  intro i _
  exact (aux_coord_pos_sq_integrable mu hF i).integral_prod_left

theorem aux_coord_pos_exchange
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin m) :
    (∫ x, ∫ y : Xi i, (max (F x - F (Function.update x i y)) 0) ^ 2
      ∂mu i ∂Measure.pi mu) =
      ∫ x, ∫ y : Xi i, (max (F (Function.update x i y) - F x) 0) ^ 2
        ∂mu i ∂Measure.pi mu := by
  let f : (((j : Fin m) → Xi j) × Xi i) → ℝ :=
    fun z => (max (F z.1 - F (Function.update z.1 i z.2)) 0) ^ 2
  have hf : Integrable f ((Measure.pi mu).prod (mu i)) := aux_coord_pos_sq_integrable mu hF i
  have hs := aux_swapCoordinate_mp mu i
  have heq (z : ((j : Fin m) → Xi j) × Xi i) :
      f (aux_swapCoordinate i z) =
        (max (F (Function.update z.1 i z.2) - F z.1) 0) ^ 2 := by
    change (max (F (Function.update z.1 i z.2) -
        F (Function.update (Function.update z.1 i z.2) i (z.1 i))) 0) ^ 2 =
      (max (F (Function.update z.1 i z.2) - F z.1) 0) ^ 2
    rw [Function.update_idem, Function.update_eq_self]
  calc
    (∫ x, ∫ y : Xi i, (max (F x - F (Function.update x i y)) 0) ^ 2
        ∂mu i ∂Measure.pi mu) = ∫ z, f z ∂((Measure.pi mu).prod (mu i)) := (integral_prod f hf).symm
    _ = ∫ z, f (aux_swapCoordinate i z) ∂((Measure.pi mu).prod (mu i)) := (hs.integral_comp' f).symm
    _ = ∫ x, ∫ y : Xi i, (max (F (Function.update x i y) - F x) 0) ^ 2
        ∂mu i ∂Measure.pi mu := by
      have hint : Integrable (fun z => f (aux_swapCoordinate i z))
          ((Measure.pi mu).prod (mu i)) :=
        (hs.integrable_comp hf.aestronglyMeasurable).mpr hf
      rw [integral_prod _ hint]
      simp only [heq]

theorem aux_pair_sq_eq_twice_pos
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (i : Fin m) :
    (∫ x, ∫ y : Xi i, (F x - F (Function.update x i y)) ^ 2
      ∂mu i ∂Measure.pi mu) =
      2 * ∫ x, ∫ y : Xi i, (max (F x - F (Function.update x i y)) 0) ^ 2
        ∂mu i ∂Measure.pi mu := by
  let d : (((j : Fin m) → Xi j) × Xi i) → ℝ :=
    fun z => F z.1 - F (Function.update z.1 i z.2)
  have hd : MemLp d 2 ((Measure.pi mu).prod (mu i)) := aux_coord_diff_memp2 mu hF i
  have hp : Integrable (fun z => (max (d z) 0) ^ 2) ((Measure.pi mu).prod (mu i)) :=
    (aux_memLp_pos hd).integrable_sq
  have hn : Integrable (fun z => (max (-d z) 0) ^ 2) ((Measure.pi mu).prod (mu i)) := by
    simpa only [Pi.neg_apply] using (aux_memLp_pos hd.neg).integrable_sq
  have hsplit : (∫ z, (d z) ^ 2 ∂((Measure.pi mu).prod (mu i))) =
      (∫ z, (max (d z) 0) ^ 2 ∂((Measure.pi mu).prod (mu i))) + ∫ z, (max (-d z) 0) ^ 2 ∂((Measure.pi mu).prod (mu i)) := by
    rw [← integral_add hp hn]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (aux_pos_sq (d z)).symm
  rw [← integral_prod _ hd.integrable_sq]
  rw [hsplit, integral_prod _ hp, integral_prod _ hn]
  have hex := aux_coord_pos_exchange mu hF i
  have hneg (x : (j : Fin m) → Xi j) (y : Xi i) :
      -d (x, y) = F (Function.update x i y) - F x := by
    dsimp only [d]
    ring
  simp only [hneg]
  rw [← hex]
  ring

theorem aux_efronStein_plus
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ}
    (hFm : Measurable F) (hF : MemLp F 2 (Measure.pi mu)) :
    (∫ x, (F x) ^ 2 ∂Measure.pi mu) - (∫ x, F x ∂Measure.pi mu) ^ 2 ≤
      ∫ x, aux_vPlus mu F x ∂Measure.pi mu := by
  have h := aux_efronStein_two m Xi mu F hFm hF
  simp_rw [aux_pair_sq_eq_twice_pos mu hF] at h
  rw [← Finset.mul_sum] at h
  have heq : (∫ x, aux_vPlus mu F x ∂Measure.pi mu) =
      ∑ i : Fin m, ∫ x, ∫ y : Xi i,
        (max (F x - F (Function.update x i y)) 0) ^ 2 ∂mu i ∂Measure.pi mu :=
    integral_finsetSum _ (fun i _ =>
      (aux_coord_pos_sq_integrable mu hF i).integral_prod_left)
  rw [heq]
  nlinarith only [h]

theorem aux_positive_centered_second_moment
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ}
    (hFm : Measurable F) (hF : MemLp F 2 (Measure.pi mu)) :
    (∫ x, (max (F x - ∫ y, F y ∂Measure.pi mu) 0) ^ 2 ∂Measure.pi mu) ≤
      ∫ x, aux_vPlus mu F x ∂Measure.pi mu := by
  have hc : MemLp (fun x => F x - ∫ y, F y ∂Measure.pi mu) 2 (Measure.pi mu) :=
    hF.sub (memLp_const (∫ y, F y ∂Measure.pi mu))
  calc
    (∫ x, (max (F x - ∫ y, F y ∂Measure.pi mu) 0) ^ 2 ∂Measure.pi mu) ≤
        ∫ x, (F x - ∫ y, F y ∂Measure.pi mu) ^ 2 ∂Measure.pi mu := by
      apply integral_mono (aux_memLp_pos hc).integrable_sq hc.integrable_sq
      intro x
      dsimp only
      have heq := aux_pos_sq (F x - ∫ y, F y ∂Measure.pi mu)
      nlinarith [sq_nonneg (max (-(F x - ∫ y, F y ∂Measure.pi mu)) 0)]
    _ = (∫ x, (F x) ^ 2 ∂Measure.pi mu) - (∫ x, F x ∂Measure.pi mu) ^ 2 :=
      aux_centered_sq_integral hF
    _ ≤ ∫ x, aux_vPlus mu F x ∂Measure.pi mu := aux_efronStein_plus mu hFm hF

theorem aux_rpow_rpow_div (x p q : ℝ) (hx : 0 ≤ x) (hp : p ≠ 0) :
    (x ^ p) ^ (q / p) = x ^ q := by
  rw [← Real.rpow_mul hx]
  congr 1
  field_simp [hp]

theorem aux_root_rpow (x p q : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / p)) ^ q = x ^ (q / p) := by
  rw [← Real.rpow_mul hx]
  congr 1
  ring

theorem aux_integrable_power
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hf0 : ∀ x, 0 ≤ f x)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    Integrable (fun x => (f x) ^ p) μ := by
  have h := (memLp_one_iff_integrable).mp
    (hf.norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top)
  have heq : (fun x => ‖f x‖ ^ (ENNReal.ofReal p).toReal) =
      fun x => (f x) ^ p := by
    funext x
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  rw [heq] at h
  exact h

theorem aux_eLpNorm_eq_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hf0 : ∀ x, 0 ≤ f x)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal ((∫ x, (f x) ^ p ∂μ) ^ (1 / p)) := by
  have h := MemLp.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf
  have heq : (fun x => ‖f x‖ ^ (ENNReal.ofReal p).toReal) =
      fun x => (f x) ^ p := by
    funext x
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  rw [heq] at h
  simpa only [ENNReal.toReal_ofReal hp.le, one_div] using h

theorem aux_lower_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable (fun x => (f x) ^ p) μ)
    (q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) :
    Integrable (fun x => (f x) ^ q) μ ∧
      (∫ x, (f x) ^ q ∂μ) ≤ ((∫ x, (f x) ^ p ∂μ) ^ (1 / p)) ^ q := by
  have h := aux_integral_rpow_le hf (fun x => Real.rpow_nonneg (hf0 x) p)
    (q / p) (div_nonneg hq hp.le) ((div_le_one hp).mpr hqp)
  have heq : (fun x => ((f x) ^ p) ^ (q / p)) = fun x => (f x) ^ q := by
    funext x
    exact aux_rpow_rpow_div (f x) p q (hf0 x) hp.ne'
  rw [heq] at h
  refine ⟨h.1, ?_⟩
  rw [aux_root_rpow _ _ _ (integral_nonneg fun x => Real.rpow_nonneg (hf0 x) p)]
  exact h.2

theorem aux_mixed_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable (fun x => (f x) ^ p) μ)
    (hg : Integrable (fun x => (g x) ^ p) μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = p) :
    Integrable (fun x => (f x) ^ a * (g x) ^ b) μ ∧
      (∫ x, (f x) ^ a * (g x) ^ b ∂μ) ≤
        ((∫ x, (f x) ^ p ∂μ) ^ (1 / p)) ^ a *
          ((∫ x, (g x) ^ p ∂μ) ^ (1 / p)) ^ b := by
  have hweights : a / p + b / p = 1 := by
    rw [← add_div, hab, div_self hp.ne']
  have h := aux_integral_weighted_rpow hf hg
    (fun x => Real.rpow_nonneg (hf0 x) p)
    (fun x => Real.rpow_nonneg (hg0 x) p)
    (a / p) (b / p) (div_nonneg ha hp.le) (div_nonneg hb hp.le) hweights
  have heq : (fun x => ((f x) ^ p) ^ (a / p) * ((g x) ^ p) ^ (b / p)) =
      fun x => (f x) ^ a * (g x) ^ b := by
    funext x
    rw [aux_rpow_rpow_div (f x) p a (hf0 x) hp.ne',
      aux_rpow_rpow_div (g x) p b (hg0 x) hp.ne']
  rw [heq] at h
  refine ⟨h.1, ?_⟩
  rw [aux_root_rpow _ _ _ (integral_nonneg fun x => Real.rpow_nonneg (hf0 x) p),
    aux_root_rpow _ _ _ (integral_nonneg fun x => Real.rpow_nonneg (hg0 x) p)]
  exact h.2

theorem aux_half_power_sq (x p : ℝ) (hx : 0 ≤ x) :
    (x ^ (p / 2)) ^ 2 = x ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

theorem aux_mean_half_power_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} {p : ℝ} (hp : 2 ≤ p) (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable (fun x => (g x) ^ p) μ) :
    (∫ x, (g x) ^ (p / 2) ∂μ) ^ 2 ≤
      (∫ x, (g x) ^ (p - 2) ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  have hp0 : 0 < p := by linarith
  have h₁ := (aux_lower_moment hp0 hg0 hg (p - 2) (by linarith) (by linarith)).1
  have h₂ : Integrable (fun x => (g x) ^ 2) μ := by
    simpa only [Real.rpow_two] using
      (aux_lower_moment hp0 hg0 hg 2 (by norm_num) hp).1
  have hcs := (aux_integral_weighted_rpow h₁ h₂
    (fun x => Real.rpow_nonneg (hg0 x) _) (fun x => sq_nonneg (g x))
    (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)).2
  have hfun (x : Ω) :
      ((g x) ^ (p - 2)) ^ (1 / 2 : ℝ) * ((g x) ^ 2) ^ (1 / 2 : ℝ) =
        (g x) ^ (p / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hg0 x), ← Real.rpow_mul (hg0 x),
      ← Real.rpow_add' (hg0 x) (by norm_num; linarith)]
    congr 1
    norm_num ; ring
  simp_rw [hfun] at hcs
  have hs := mul_self_le_mul_self
    (integral_nonneg fun x => Real.rpow_nonneg (hg0 x) _) hcs
  have heq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    simpa only [one_div, Real.rpow_one] using aux_half_power_sq x 1 hx
  calc
    (∫ x, (g x) ^ (p / 2) ∂μ) ^ 2 ≤
        ((∫ x, (g x) ^ (p - 2) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
      simpa only [pow_two] using hs
    _ = (∫ x, (g x) ^ (p - 2) ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
      rw [mul_pow, heq _ (integral_nonneg fun x => Real.rpow_nonneg (hg0 x) _),
        heq _ (integral_nonneg fun x => sq_nonneg (g x))]

theorem aux_vPlus_power_le
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    {F : ((i : Fin m) → Xi i) → ℝ} (hF : MemLp F 2 (Measure.pi mu))
    (p c : ℝ) (hp : 2 ≤ p) :
    ∀ᵐ x ∂Measure.pi mu,
      aux_vPlus mu (fun z => (max (F z - c) 0) ^ (p / 2)) x ≤
        (p / 2) ^ 2 * (max (F x - c) 0) ^ (p - 2) * aux_vPlus mu F x := by
  have hfibers : ∀ i : Fin m, ∀ᵐ x ∂Measure.pi mu,
      Integrable (fun y : Xi i => (max (F x - F (Function.update x i y)) 0) ^ 2)
        (mu i) := fun i => (aux_coord_pos_sq_integrable mu hF i).prod_right_ae
  filter_upwards [ae_all_iff.mpr hfibers] with x hx
  change (∑ i : Fin m, ∫ y : Xi i,
      (max ((max (F x - c) 0) ^ (p / 2) -
        (max (F (Function.update x i y) - c) 0) ^ (p / 2)) 0) ^ 2 ∂mu i) ≤
    (p / 2) ^ 2 * (max (F x - c) 0) ^ (p - 2) *
      ∑ i : Fin m, ∫ y : Xi i, (max (F x - F (Function.update x i y)) 0) ^ 2 ∂mu i
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => sq_nonneg _)
    ((hx i).const_mul ((p / 2) ^ 2 * (max (F x - c) 0) ^ (p - 2)))
  exact Filter.Eventually.of_forall fun y =>
    aux_pos_rpow_difference (F x) (F (Function.update x i y)) c p hp

theorem aux_bblm_positive_finite
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    (p : ℝ) (hp : 2 ≤ p) {F : ((i : Fin m) → Xi i) → ℝ}
    (hFm : Measurable F) (hF : MemLp F (ENNReal.ofReal p) (Measure.pi mu))
    (hV : MemLp (fun x => Real.sqrt (aux_vPlus mu F x))
      (ENNReal.ofReal p) (Measure.pi mu)) :
    eLpNorm (fun x => max (F x - ∫ y, F y ∂Measure.pi mu) 0)
      (ENNReal.ofReal p) (Measure.pi mu) ≤
      ENNReal.ofReal p * eLpNorm (fun x => Real.sqrt (aux_vPlus mu F x))
        (ENNReal.ofReal p) (Measure.pi mu) := by
  let P := Measure.pi mu
  let c := ∫ y, F y ∂P
  let g := fun x => max (F x - c) 0
  let v := fun x => Real.sqrt (aux_vPlus mu F x)
  let A := (∫ x, (g x) ^ p ∂P) ^ (1 / p)
  let B := (∫ x, (v x) ^ p ∂P) ^ (1 / p)
  have hp0 : 0 < p := by linarith
  have hpE : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    calc
      (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp
  have hF2 : MemLp F 2 P := hF.mono_exponent hpE
  have hgm : Measurable g := (hFm.sub measurable_const).max measurable_const
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hv0 : ∀ x, 0 ≤ v x := fun x => Real.sqrt_nonneg _
  have hgp : MemLp g (ENNReal.ofReal p) P := aux_memLp_pos (hF.sub (memLp_const c))
  have hgi : Integrable (fun x => (g x) ^ p) P := aux_integrable_power hp0 hg0 hgp
  have hvi : Integrable (fun x => (v x) ^ p) P := aux_integrable_power hp0 hv0 hV
  have hA0 : 0 ≤ A := Real.rpow_nonneg (integral_nonneg fun x =>
    Real.rpow_nonneg (hg0 x) p) _
  have hB0 : 0 ≤ B := Real.rpow_nonneg (integral_nonneg fun x =>
    Real.rpow_nonneg (hv0 x) p) _
  have hv2 (x : (i : Fin m) → Xi i) : (v x) ^ 2 = aux_vPlus mu F x :=
    Real.sq_sqrt (aux_vPlus_nonneg mu F x)
  have hhalf : (fun x => ((g x) ^ (p / 2)) ^ 2) = fun x => (g x) ^ p := by
    funext x
    exact aux_half_power_sq (g x) p (hg0 x)
  have hh2 : MemLp (fun x => (g x) ^ (p / 2)) 2 P := by
    apply (memLp_two_iff_integrable_sq (hgm.pow_const (p / 2)).aestronglyMeasurable).mpr
    rw [hhalf]
    exact hgi
  have hmixed := aux_mixed_moment hp0 hg0 hv0 hgi hvi (p - 2) 2
    (by linarith) (by norm_num) (by ring)
  have hwint : Integrable (fun x => (g x) ^ (p - 2) * aux_vPlus mu F x) P := by
    simpa only [Real.rpow_two, hv2] using hmixed.1
  have hwbound : (∫ x, (g x) ^ (p - 2) * aux_vPlus mu F x ∂P) ≤
      A ^ (p - 2) * B ^ 2 := by
    simpa only [Real.rpow_two, hv2] using hmixed.2
  have hvmean : (∫ x, aux_vPlus mu F x ∂P) ≤ B ^ 2 := by
    have h := (aux_lower_moment hp0 hv0 hvi 2 (by norm_num) hp).2
    simpa only [Real.rpow_two, hv2] using h
  have hgmean : (∫ x, (g x) ^ 2 ∂P) ≤ B ^ 2 :=
    (aux_positive_centered_second_moment mu hFm hF2).trans hvmean
  have hglower : (∫ x, (g x) ^ (p - 2) ∂P) ≤ A ^ (p - 2) :=
    (aux_lower_moment hp0 hg0 hgi (p - 2) (by linarith) (by linarith)).2
  have hmean : (∫ x, (g x) ^ (p / 2) ∂P) ^ 2 ≤ A ^ (p - 2) * B ^ 2 :=
    (aux_mean_half_power_sq hp hg0 hgi).trans
      (mul_le_mul hglower hgmean (integral_nonneg fun x => sq_nonneg (g x))
        (Real.rpow_nonneg hA0 _))
  have hvar := aux_efronStein_plus mu (hgm.pow_const (p / 2)) hh2
  rw [hhalf] at hvar
  have hvar' :
      (∫ x, aux_vPlus mu (fun z => (g z) ^ (p / 2)) x ∂P) ≤
        (p / 2) ^ 2 * (A ^ (p - 2) * B ^ 2) := by
    calc
      (∫ x, aux_vPlus mu (fun z => (g z) ^ (p / 2)) x ∂P) ≤
          ∫ x, (p / 2) ^ 2 * ((g x) ^ (p - 2) * aux_vPlus mu F x) ∂P := by
        apply integral_mono_ae (aux_vPlus_integrable mu hh2) (hwint.const_mul _)
        filter_upwards [aux_vPlus_power_le mu hF2 p c hp] with x hx
        simpa only [g, mul_assoc] using hx
      _ = (p / 2) ^ 2 * (∫ x, (g x) ^ (p - 2) * aux_vPlus mu F x ∂P) :=
        integral_const_mul _ _
      _ ≤ (p / 2) ^ 2 * (A ^ (p - 2) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hwbound (sq_nonneg _)
  have htotal : (∫ x, (g x) ^ p ∂P) ≤
      (1 + (p / 2) ^ 2) * A ^ (p - 2) * B ^ 2 := by
    nlinarith only [hvar, hvar', hmean]
  have hAeq : A ^ p = ∫ x, (g x) ^ p ∂P := by
    dsimp only [A]
    rw [← Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (hg0 x) p)]
    simp [hp0.ne']
  have hAB : A ≤ p * B := by
    rcases hA0.eq_or_lt with hA | hA
    · rw [← hA]
      exact mul_nonneg hp0.le hB0
    · have hfpos : 0 < A ^ (p - 2) := Real.rpow_pos_of_pos hA _
      have hfactor : A ^ (p - 2) * A ^ 2 = ∫ x, (g x) ^ p ∂P := by
        calc
          A ^ (p - 2) * A ^ 2 = A ^ (p - 2) * A ^ (2 : ℝ) := by
            rw [Real.rpow_two]
          _ = A ^ ((p - 2) + 2) := (Real.rpow_add' hA.le (by linarith)).symm
          _ = A ^ p := by congr 1; ring
          _ = ∫ x, (g x) ^ p ∂P := hAeq
      have hs : A ^ 2 ≤ (1 + (p / 2) ^ 2) * B ^ 2 := by
        refine le_of_mul_le_mul_left ?_ hfpos
        calc
          A ^ (p - 2) * A ^ 2 = ∫ x, (g x) ^ p ∂P := hfactor
          _ ≤ (1 + (p / 2) ^ 2) * A ^ (p - 2) * B ^ 2 := htotal
          _ = A ^ (p - 2) * ((1 + (p / 2) ^ 2) * B ^ 2) := by ring
      have hpbound : 1 + (p / 2) ^ 2 ≤ p ^ 2 := by
        nlinarith only [hp, sq_nonneg (p - 2)]
      have hs' : A ^ 2 ≤ (p * B) ^ 2 := by
        calc
          A ^ 2 ≤ (1 + (p / 2) ^ 2) * B ^ 2 := hs
          _ ≤ p ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right hpbound (sq_nonneg B)
          _ = (p * B) ^ 2 := (mul_pow p B 2).symm
      calc
        A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hA0).symm
        _ ≤ Real.sqrt ((p * B) ^ 2) := Real.sqrt_le_sqrt hs'
        _ = p * B := Real.sqrt_sq (mul_nonneg hp0.le hB0)
  change eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal p * eLpNorm v (ENNReal.ofReal p) P
  rw [aux_eLpNorm_eq_moment hp0 hg0 hgp, aux_eLpNorm_eq_moment hp0 hv0 hV,
    ← ENNReal.ofReal_mul hp0.le]
  exact ENNReal.ofReal_le_ofReal hAB

theorem aux_bblm_positive
    {m : ℕ} {Xi : Fin m → Type*} [∀ i, MeasurableSpace (Xi i)]
    (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)]
    (p : ℝ) (hp : 2 ≤ p) {F : ((i : Fin m) → Xi i) → ℝ}
    (hFm : Measurable F) (hF : MemLp F (ENNReal.ofReal p) (Measure.pi mu)) :
    eLpNorm (fun x => max (F x - ∫ y, F y ∂Measure.pi mu) 0)
      (ENNReal.ofReal p) (Measure.pi mu) ≤
      ENNReal.ofReal p * eLpNorm (fun x => Real.sqrt (aux_vPlus mu F x))
        (ENNReal.ofReal p) (Measure.pi mu) := by
  have hp0 : 0 < p := by linarith
  by_cases hV : eLpNorm (fun x => Real.sqrt (aux_vPlus mu F x))
      (ENNReal.ofReal p) (Measure.pi mu) = ∞
  · rw [hV, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hp0).ne']
    exact le_top
  · apply aux_bblm_positive_finite mu p hp hFm hF
    simpa only [MemLp, eLpNorm,
      ite_eq_left (aux_vPlus_measurable mu hFm).sqrt.aestronglyMeasurable] using
      (lt_top_iff_ne_top.mpr hV)




theorem aux_lem_15_bblm :
    ∀ (p : ℝ), 2 ≤ p → ∃ (Kp : ℝ), 0 < Kp ∧
      ∀ (m : ℕ) (Xi : Fin m → Type) [∀ i, MeasurableSpace (Xi i)]
        (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)],
        let P := Measure.pi mu
        ∀ (F : ((i : Fin m) → Xi i) → ℝ),
          Measurable F → MemLp F (ENNReal.ofReal p) P →
          (eLpNorm (fun x => max (F x - ∫ y, F y ∂P) 0)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal Kp *
              eLpNorm (fun x => Real.sqrt
                (∑ i : Fin m, ∫ y : Xi i,
                  (max (F x - F (Function.update x i y)) 0) ^ 2 ∂mu i))
                (ENNReal.ofReal p) P) ∧
          (eLpNorm (fun x => max ((∫ y, F y ∂P) - F x) 0)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal Kp *
              eLpNorm (fun x => Real.sqrt
                (∑ i : Fin m, ∫ y : Xi i,
                  (max (F (Function.update x i y) - F x) 0) ^ 2 ∂mu i))
                (ENNReal.ofReal p) P)
    := by
  intro p hp
  refine ⟨p, by linarith, ?_⟩
  intro m Xi _ mu _
  dsimp only
  intro F hFm hF
  constructor
  · exact aux_bblm_positive mu p hp hFm hF
  · have h := aux_bblm_positive mu p hp hFm.neg hF.neg
    simpa only [Pi.neg_apply, integral_neg, neg_sub_neg, aux_vPlus] using h

end SubdiffusiveProcess.Paper
