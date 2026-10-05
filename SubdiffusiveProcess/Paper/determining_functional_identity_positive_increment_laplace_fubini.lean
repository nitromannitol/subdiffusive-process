module

public import SubdiffusiveProcess.Main.DiffusionPath
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Data.List.FinRange
public import MarkovProcess.Kernel.Integral
public import MarkovProcess.Kernel.KernelSemigroup
public import MarkovProcess.Kernel.Operator
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_fold_meas
    {α : Type*} [MeasurableSpace α]
    {m : Nat} (P : SubMarkovKernelSemigroup α)
    (f : Fin m → α → ℝ) (s : Fin m → ℝ)
    (l : List (Fin m)) (q : ℝ → α → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hq : Measurable (fun p : ℝ × α => q p.1 p.2)) :
    Measurable (fun p : ℝ × α =>
      l.foldr
        (fun i (r : α → ℝ) => fun z =>
          kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
        (fun z => q p.1 z) p.2) := by
  induction l with
  | nil =>
      simpa using hq
  | cons i l ih =>
      have htail : Measurable (fun p : ℝ × α =>
          l.foldr
            (fun i (r : α → ℝ) => fun z =>
              kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
            (fun z => q p.1 z) p.2) :=
        ih
      have hinput : Measurable (fun p : (ℝ × α) × α =>
          f i p.2 *
            l.foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
              (fun z => q p.1.1 z) p.2) :=
        (hf i).comp measurable_snd |>.mul
          (htail.comp (measurable_fst.fst.prodMk measurable_snd))
      let κ : Kernel (ℝ × α) α :=
        (P (Real.toNNReal (s i))).comap (fun p : ℝ × α => p.2) measurable_snd
      let : IsFiniteKernel (P (Real.toNNReal (s i))) :=
        (P.isSubMarkovKernel _).isFiniteKernel
      have hout := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right
        (κ := κ) (f := fun p : ℝ × α => fun z =>
          f i z *
            l.foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
              (fun z => q p.1 z) z) hinput.stronglyMeasurable
      simpa [κ, Kernel.comap_apply, kernelIntegral] using hout.measurable

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_bound
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {g : α → ℝ} {D : ℝ}
    (hgD : ∀ y, |g y| ≤ D) (t : NNReal) (x : α) :
    |kernelIntegral (P t) g x| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg (g x)).trans (hgD x)
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  calc
    |kernelIntegral (P t) g x| ≤ ∫ _y, D ∂(P t x) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (integrable_const (μ := P t x) D)
      exact Eventually.of_forall hgD
    _ ≤ D := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hD0
      rw [measureReal_def, ← ENNReal.toReal_one]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      exact (P.isSubMarkovKernel t).measure_le_one x Set.univ

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_fold_bound
    {α : Type*} [MeasurableSpace α]
    {m : Nat} (P : SubMarkovKernelSemigroup α)
    (f : Fin m → α → ℝ) (s : Fin m → ℝ)
    {A C : ℝ} (hA : 0 ≤ A) (hfA : ∀ i y, |f i y| ≤ A)
    (l : List (Fin m)) (q : ℝ → α → ℝ)
    (hqC : ∀ t y, |q t y| ≤ C) :
    ∀ t y, |l.foldr
      (fun i (r : α → ℝ) => fun z =>
        kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
      (fun z => q t z) y| ≤ A ^ l.length * C := by
  induction l with
  | nil =>
      intro t y
      simpa using hqC t y
  | cons i l ih =>
      intro t y
      have htail : ∀ z, |l.foldr
          (fun i (r : α → ℝ) => fun z =>
            kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
          (fun z => q t z) z| ≤ A ^ l.length * C :=
        ih t
      have hprod : ∀ z, |f i z *
          l.foldr
            (fun i (r : α → ℝ) => fun z =>
              kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
            (fun z => q t z) z| ≤ A * (A ^ l.length * C) := by
        intro z
        rw [abs_mul]
        gcongr
        exact hfA i z
        exact htail z
      have hk := aux_determining_functional_identity_positive_increment_laplace_fubini_bound P hprod (Real.toNNReal (s i)) y
      convert hk using 1 <;> simp [List.length_cons, pow_succ] ; ring

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_interchange
    {α : Type*} [MeasurableSpace α]
    (κ : Kernel α α) (x : α) (n : Nat) (hn : 0 < n)
    (f : α → ℝ) (a : ℝ → α → ℝ)
    (hf : Measurable f)
    (ha : Measurable (fun p : ℝ × α => a p.1 p.2))
    {D C : ℝ} (hfD : ∀ y, |f y| ≤ D) (haC : ∀ t y, |a t y| ≤ C)
    (hκ : IsFiniteKernel κ) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
      kernelIntegral κ (fun z => f z * a t z) x) =
      kernelIntegral κ (fun z => f z *
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * a t z) x := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let w : ℝ → ℝ := fun t => Real.exp (-(n : ℝ) * t)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let : IsFiniteKernel κ := hκ
  have hw : Integrable w μ := by
    exact exp_neg_integrableOn_Ioi 0 hn'
  have hconst : Integrable (fun _ : α => (D * C : ℝ)) (κ x) := by
    exact integrable_const (μ := κ x) (D * C)
  have hmajor : Integrable (fun p : ℝ × α => w p.1 * (D * C)) (μ.prod (κ x)) := by
    exact hw.mul_prod hconst
  have hmeas : Measurable (fun p : ℝ × α =>
      w p.1 * (f p.2 * a p.1 p.2)) := by
    have hw' : Measurable w := by
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
    exact (hw'.comp measurable_fst).mul
      ((hf.comp measurable_snd).mul ha)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD _)
  have hC0 : 0 ≤ C := (abs_nonneg (a 0 x)).trans (haC _ _)
  have hI : Integrable (fun p : ℝ × α =>
      w p.1 * (f p.2 * a p.1 p.2)) (μ.prod (κ x)) := by
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards with p
    change |w p.1 * (f p.2 * a p.1 p.2)| ≤ w p.1 * (D * C)
    dsimp [w]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
    · exact (hfD _)
    · exact (haC _ _)
  have hprod := integral_prod (fun p : ℝ × α =>
      w p.1 * (f p.2 * a p.1 p.2)) hI
  have hprods := integral_prod_symm (fun p : ℝ × α =>
      w p.1 * (f p.2 * a p.1 p.2)) hI
  change (∫ t, w t * kernelIntegral κ (fun z => f z * a t z) x ∂μ) = _
  change _ = ∫ z, f z * (∫ t, w t * a t z ∂μ) ∂κ x
  calc
    (∫ t, w t * kernelIntegral κ (fun z => f z * a t z) x ∂μ) =
        ∫ t, ∫ z, w t * (f z * a t z) ∂κ x ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [kernelIntegral, integral_const_mul]
    _ = ∫ p, w p.1 * (f p.2 * a p.1 p.2) ∂(μ.prod (κ x)) := hprod.symm
    _ = ∫ z, ∫ t, w t * (f z * a t z) ∂μ ∂κ x := hprods
    _ = ∫ z, f z * (∫ t, w t * a t z ∂μ) ∂κ x := by
      apply integral_congr_ae
      filter_upwards with z
      calc
        ∫ t, w t * (f z * a t z) ∂μ =
            ∫ t, (w t * a t z) * f z ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          ring
        _ = (∫ t, w t * a t z ∂μ) * f z := integral_mul_const _ _
        _ = f z * (∫ t, w t * a t z ∂μ) := by ring

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_outer_interchange
    {α : Type*} [MeasurableSpace α]
    {m : Nat} (P : SubMarkovKernelSemigroup α)
    (f : Fin m → α → ℝ) (s : Fin m → ℝ)
    {A C : ℝ} (hA : 0 ≤ A) (hfA : ∀ i y, |f i y| ≤ A)
    (hf : ∀ i, Measurable (f i))
    (l : List (Fin m)) (q : ℝ → α → ℝ)
    (hqC : ∀ t y, |q t y| ≤ C)
    (hq : Measurable (fun p : ℝ × α => q p.1 p.2))
    {n : Nat} (hn : 0 < n) :
    ∀ x, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
      l.foldr
        (fun i (r : α → ℝ) => fun z =>
          kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
        (fun z => q t z) x) =
      l.foldr
        (fun i (r : α → ℝ) => fun z =>
          kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
        (fun z => ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(n : ℝ) * t) * q t z) x := by
  induction l with
  | nil =>
      intro x
      rfl
  | cons i l ih =>
      intro x
      let qInt : α → ℝ := fun z => ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * q t z
      have htailC : ∀ t y, |l.foldr
          (fun i (r : α → ℝ) => fun z =>
            kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
          (fun z => q t z) y| ≤ A ^ l.length * C :=
        aux_determining_functional_identity_positive_increment_laplace_fubini_fold_bound P f s hA hfA l q hqC
      have htailmeas : Measurable (fun p : ℝ × α =>
          l.foldr
            (fun i (r : α → ℝ) => fun z =>
              kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
            (fun z => q p.1 z) p.2) :=
        aux_determining_functional_identity_positive_increment_laplace_fubini_fold_meas P f s l q hf hq
      have hleft := aux_determining_functional_identity_positive_increment_laplace_fubini_interchange
        (P (Real.toNNReal (s i))) x n hn (f i)
        (fun t y => l.foldr
          (fun i (r : α → ℝ) => fun z =>
            kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
          (fun z => q t z) y)
        (hf i) htailmeas (hfA i) htailC
        ((P.isSubMarkovKernel _).isFiniteKernel)
      calc
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
            (List.cons i l).foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
              (fun z => q t z) x) =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
              kernelIntegral (P (Real.toNNReal (s i)))
                (fun z => f i z *
                  l.foldr
                    (fun i (r : α → ℝ) => fun z =>
                      kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
                    (fun z => q t z) z) x := by
          rfl
        _ = kernelIntegral (P (Real.toNNReal (s i)))
              (fun z => f i z * ∫ t in Set.Ioi (0 : ℝ),
                Real.exp (-(n : ℝ) * t) *
                  l.foldr
                    (fun i (r : α → ℝ) => fun z =>
                      kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
                    (fun z => q t z) z) x := hleft
        _ = kernelIntegral (P (Real.toNNReal (s i)))
              (fun z => f i z *
                l.foldr
                  (fun i (r : α → ℝ) => fun z =>
                    kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
                  (fun z => qInt z) z) x := by
          unfold kernelIntegral
          apply integral_congr_ae
          filter_upwards with z
          simpa [qInt, kernelIntegral] using congrArg (fun v : ℝ => f i z * v) (ih z)
        _ = (List.cons i l).foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (s i))) (fun u => f i u * r u) z)
              (fun z => ∫ t in Set.Ioi (0 : ℝ),
                Real.exp (-(n : ℝ) * t) * q t z) x := by
          simp [qInt, List.foldr]

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_full_fold_meas
    {α : Type*} [MeasurableSpace α]
    {m : Nat} (P : SubMarkovKernelSemigroup α)
    (f : Fin m → α → ℝ) (q : α → ℝ)
    (hf : ∀ i, Measurable (f i)) (hq : Measurable q)
    (l : List (Fin m)) :
    Measurable (fun p : (Fin m → ℝ) × α =>
      l.foldr
        (fun i (r : α → ℝ) => fun z =>
          kernelIntegral (P (Real.toNNReal (p.1 i))) (fun u => f i u * r u) z)
        q p.2) := by
  have hj : IsFiniteKernel P.jointKernel := by
    refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
    intro p
    exact P.isSubMarkovKernel p.1 p.2
  let : IsFiniteKernel P.jointKernel := hj
  induction l with
  | nil =>
      simpa only [List.foldr_nil, Function.comp_def] using hq.comp measurable_snd
  | cons i l ih =>
      have htail : Measurable (fun p : (Fin m → ℝ) × α =>
          l.foldr
            (fun i (r : α → ℝ) => fun z =>
              kernelIntegral (P (Real.toNNReal (p.1 i))) (fun u => f i u * r u) z)
            q p.2) :=
        ih
      have hinput : Measurable (fun p : ((Fin m → ℝ) × α) × α =>
          f i p.2 *
            l.foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (p.1.1 i))) (fun u => f i u * r u) z)
              q p.2) :=
        (hf i).comp measurable_snd |>.mul
          (htail.comp (measurable_fst.fst.prodMk measurable_snd))
      have hmap : Measurable (fun p : (Fin m → ℝ) × α =>
          (Real.toNNReal (p.1 i), p.2)) :=
        have hv : Measurable (fun p : (Fin m → ℝ) × α => p.1 i) :=
          (measurable_pi_apply i).comp measurable_fst
        (measurable_real_toNNReal.comp hv).prodMk measurable_snd
      let K : Kernel ((Fin m → ℝ) × α) α :=
        P.jointKernel.comap (fun p : (Fin m → ℝ) × α =>
          (Real.toNNReal (p.1 i), p.2)) hmap
      have hout := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right
        (κ := K) (f := fun p : (Fin m → ℝ) × α => fun z =>
          f i z *
            l.foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal (p.1 i))) (fun u => f i u * r u) z)
              q z) hinput.stronglyMeasurable
      simpa [K, Kernel.comap_apply, SubMarkovKernelSemigroup.jointKernel,
        kernelIntegral] using hout.measurable

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_finRange_snoc (m : Nat) :
    List.finRange (m + 1) =
      (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  apply List.ext_get
  · simp
  · intro n hn₁ hn₂
    simp only [List.length_finRange, List.length_map, List.length_append,
      List.length_singleton] at hn₁ hn₂
    by_cases h : n < m
    · simp [List.get_eq_getElem, h]
    · have h' : n = m := by omega
      subst n
      apply Fin.ext
      simp [List.get_eq_getElem]

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_resolvent_bound
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α)
    (R : Nat → (α → ℝ) → α → ℝ)
    (hR : ∀ r q x, R r q x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) q x)
    {n : Nat} (hn : 0 < n) {g : α → ℝ} {D : ℝ}
    (hgD : ∀ y, |g y| ≤ D) (x : α) :
    |R n g x| ≤ D / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hR]
  calc
    |∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) g x| ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * D := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hn').mul_const D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (aux_determining_functional_identity_positive_increment_laplace_fubini_bound P hgD (Real.toNNReal t) x) (Real.exp_pos _).le
    _ = D / (n : ℝ) := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hn') 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_resolvent_meas
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α)
    (R : Nat → (α → ℝ) → α → ℝ)
    (hR : ∀ r q x, R r q x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) q x)
    {r : Nat} {g : α → ℝ} (hg : Measurable g) :
    Measurable (R r g) := by
  have hmeas : Measurable (fun p : ℝ × α =>
      Real.exp (-(r : ℝ) * p.1) *
        kernelIntegral (P (Real.toNNReal p.1)) g p.2) := by
    have he : Measurable (fun t : ℝ => Real.exp (-(r : ℝ) * t)) := by
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
    have hm : Measurable (fun p : ℝ × α => (Real.toNNReal p.1, p.2)) :=
      (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
    exact (he.comp measurable_fst).mul
      ((P.measurable_kernelIntegral hg).comp
        hm)
  have hstrong := hmeas.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
  rw [show R r g = (fun y => ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(r : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) g y) from funext (hR r g)]
  simpa using hstrong.measurable

lemma aux_determining_functional_identity_positive_increment_laplace_fubini_product_fold
    {α : Type*} [MeasurableSpace α]
    {m : Nat} (P : SubMarkovKernelSemigroup α)
    (R : Nat → (α → ℝ) → α → ℝ)
    (hR : ∀ r q x, R r q x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) q x)
    (f : Fin m → α → ℝ) (n : Fin m → Nat) (q : α → ℝ)
    {A C : ℝ} (hA : 0 ≤ A) (hfA : ∀ i y, |f i y| ≤ A)
    (hf : ∀ i, Measurable (f i))
    (hqC : ∀ y, |q y| ≤ C) (hq : Measurable q)
    (hn : ∀ i, 0 < n i) (x : α) :
    (∫ s in Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ)),
      Real.exp (-(∑ i : Fin m, (n i : ℝ) * s i)) *
        ((List.finRange m).foldr
          (fun i (r : α → ℝ) => fun y =>
            kernelIntegral (P (Real.toNNReal (s i)))
              (fun z => f i z * r z) y)
          q) x) =
      ((List.finRange m).foldr
        (fun i (r : α → ℝ) => fun y =>
          R (n i) (fun z => f i z * r z) y)
        q) x := by
  induction m generalizing q C with
  | zero =>
      have hs : Set.pi Set.univ (fun _ : Fin 0 => Set.Ioi (0 : ℝ)) = Set.univ := by
        ext s
        simp
      rw [hs]
      simp [Measure.restrict_univ, MeasureTheory.measureReal_def,
        MeasureTheory.volume_pi,
        MeasureTheory.Measure.pi_empty_univ]
  | succ m ih =>
      let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
      let j : Fin (m + 1) := Fin.last m
      let gLast : α → ℝ := fun z => f j z * q z
      have hC0 : 0 ≤ C := (abs_nonneg (q x)).trans (hqC x)
      have hgLast : Measurable gLast :=
        (hf j).mul hq
      have hgLastB : ∀ y, |gLast y| ≤ A * C := by
        intro y
        dsimp [gLast]
        rw [abs_mul]
        gcongr
        exact hfA j y
        exact hqC y
      have hqLastB : ∀ t y, |kernelIntegral (P (Real.toNNReal t)) gLast y| ≤ A * C := by
        intro t y
        exact aux_determining_functional_identity_positive_increment_laplace_fubini_bound P hgLastB (Real.toNNReal t) y
      have hqLast : Measurable (fun p : ℝ × α =>
          kernelIntegral (P (Real.toNNReal p.1)) gLast p.2) := by
        have hm : Measurable (fun p : ℝ × α =>
            (Real.toNNReal p.1, p.2)) :=
          (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
        exact (P.measurable_kernelIntegral hgLast).comp hm
      have hq'B : ∀ y, |R (n j) gLast y| ≤ (A * C) / (n j : ℝ) :=
        aux_determining_functional_identity_positive_increment_laplace_fubini_resolvent_bound P R hR (hn j) hgLastB
      have hq' : Measurable (R (n j) gLast) :=
        aux_determining_functional_identity_positive_increment_laplace_fubini_resolvent_meas P R hR hgLast
      have htailf : ∀ i : Fin m, ∀ y, |f i.castSucc y| ≤ A := by
        intro i y
        exact hfA i.castSucc y
      have htailmeas : ∀ i : Fin m, Measurable (f i.castSucc) := by
        intro i
        exact hf i.castSucc
      have htailn : ∀ i : Fin m, 0 < n i.castSucc := by
        intro i
        exact hn i.castSucc
      have hmeasure :
          (volume : Measure (Fin (m + 1) → ℝ)).restrict
              (Set.univ.pi (fun _ : Fin (m + 1) => Set.Ioi (0 : ℝ))) =
            Measure.pi (fun _ : Fin (m + 1) => μ) := by
        rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
      have hfoldmeas : Measurable (fun p : (Fin (m + 1) → ℝ) × α =>
          (List.finRange (m + 1)).foldr
            (fun i (r : α → ℝ) => fun y =>
              kernelIntegral (P (Real.toNNReal (p.1 i)))
                (fun z => f i z * r z) y)
            q p.2) :=
        aux_determining_functional_identity_positive_increment_laplace_fubini_full_fold_meas P f q hf hq (List.finRange (m + 1))
      have hsum : Measurable (fun s : Fin (m + 1) → ℝ =>
          ∑ i, (n i : ℝ) * s i) := by
        exact Finset.measurable_sum Finset.univ
          (fun i _ => measurable_const.mul (measurable_pi_apply i))
      have hfoldx : Measurable (fun s : Fin (m + 1) → ℝ =>
          (List.finRange (m + 1)).foldr
            (fun i (r : α → ℝ) => fun y =>
              kernelIntegral (P (Real.toNNReal (s i)))
                (fun z => f i z * r z) y)
            q x) :=
        hfoldmeas.comp (measurable_id.prodMk measurable_const)
      have hGmeas : Measurable (fun s : Fin (m + 1) → ℝ =>
          Real.exp (-(∑ i, (n i : ℝ) * s i)) *
            (List.finRange (m + 1)).foldr
              (fun i (r : α → ℝ) => fun y =>
                kernelIntegral (P (Real.toNNReal (s i)))
                  (fun z => f i z * r z) y)
              q x) :=
        (hsum.neg.exp).mul hfoldx
      have hWi : ∀ i : Fin (m + 1), Integrable
          (fun t : ℝ => Real.exp (-(n i : ℝ) * t)) μ := by
        intro i
        exact exp_neg_integrableOn_Ioi 0 (by exact_mod_cast hn i)
      have hW : Integrable
          (fun s : Fin (m + 1) → ℝ =>
            ∏ i, Real.exp (-(n i : ℝ) * s i))
          (Measure.pi (fun _ : Fin (m + 1) => μ)) :=
        Integrable.fintype_prod hWi
      have hGint : Integrable (fun s : Fin (m + 1) → ℝ =>
          Real.exp (-(∑ i, (n i : ℝ) * s i)) *
            (List.finRange (m + 1)).foldr
              (fun i (r : α → ℝ) => fun y =>
                kernelIntegral (P (Real.toNNReal (s i)))
                  (fun z => f i z * r z) y)
              q x)
          (Measure.pi (fun _ : Fin (m + 1) => μ)) := by
        apply (hW.mul_const (A ^ (m + 1) * C)).mono'
          hGmeas.aestronglyMeasurable
        filter_upwards with s
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hfold := aux_determining_functional_identity_positive_increment_laplace_fubini_fold_bound P f (fun i => s i) hA hfA
          (List.finRange (m + 1)) (fun _ y => q y) (fun _ y => hqC y) 0 x
        have hexp : Real.exp (-(∑ i, (n i : ℝ) * s i)) =
            ∏ i, Real.exp (-(n i : ℝ) * s i) := by
          rw [show -(∑ i, (n i : ℝ) * s i) =
              ∑ i, -((n i : ℝ) * s i) by rw [Finset.sum_neg_distrib]]
          convert Real.exp_sum Finset.univ (fun i => -((n i : ℝ) * s i)) using 1 ;
            congr 1 ; ring_nf
        rw [hexp]
        gcongr
        simpa [List.length_finRange] using hfold
      rw [hmeasure]
      let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
      have he := measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => μ) (Fin.last m)
      have he' : MeasurePreserving (e : (Fin (m + 1) → ℝ) → ℝ × (Fin m → ℝ))
          (Measure.pi (fun _ : Fin (m + 1) => μ))
          (μ.prod (Measure.pi (fun _ : Fin m => μ))) := by
        simpa [e, Fin.succAbove_last] using he
      have hGcomp : Integrable
          ((fun s : Fin (m + 1) → ℝ =>
            Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
              (List.finRange (m + 1)).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)))
                    (fun z => f i z * r z) y)
                q x) ∘ (e.symm : (ℝ × (Fin m → ℝ)) → (Fin (m + 1) → ℝ)))
        (μ.prod (Measure.pi (fun _ : Fin m => μ))) :=
        (he'.symm.integrable_comp hGmeas.aestronglyMeasurable).mpr hGint
      have hprod := integral_prod_symm
        (fun p : ℝ × (Fin m → ℝ) =>
          (fun s : Fin (m + 1) → ℝ =>
            Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
              (List.finRange (m + 1)).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)))
                    (fun z => f i z * r z) y)
                q x) (e.symm p))
        hGcomp
      let lTail : List (Fin (m + 1)) :=
        (List.finRange m).map Fin.castSucc
      let qLast : ℝ → α → ℝ := fun t y =>
        kernelIntegral (P (Real.toNNReal t)) gLast y
      have houter : ∀ u : Fin m → ℝ, ∀ y : α,
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n j : ℝ) * t) *
            lTail.foldr
              (fun i (r : α → ℝ) => fun z =>
                kernelIntegral (P (Real.toNNReal ((Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                  (fun v => f i v * r v) z)
              (fun z => qLast t z) y) =
          lTail.foldr
            (fun i (r : α → ℝ) => fun z =>
              kernelIntegral (P (Real.toNNReal ((Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                (fun v => f i v * r v) z)
            (fun z => R (n j) gLast z) y := by
        intro u y
        simpa [lTail, qLast, hR] using
          (aux_determining_functional_identity_positive_increment_laplace_fubini_outer_interchange P f (Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) hA hfA hf
            ((List.finRange m).map Fin.castSucc)
            (fun t z => kernelIntegral (P (Real.toNNReal t)) gLast z)
            hqLastB hqLast (hn j) y)
      have hpoint : ∀ (t : ℝ) (u : Fin m → ℝ),
          (fun s : Fin (m + 1) → ℝ =>
            Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
              (List.finRange (m + 1)).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)))
                    (fun z => f i z * r z) y)
                q x) (e.symm (t, u)) =
          Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
            (Real.exp (-(n j : ℝ) * t) *
              lTail.foldr
                (fun i (r : α → ℝ) => fun z =>
                  kernelIntegral (P (Real.toNNReal ((Fin.snoc
                    (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                    (fun v => f i v * r v) z)
                (fun z => qLast t z) x) := by
        intro t u
        have heval :
            (e.symm (t, u) : Fin (m + 1) → ℝ) =
              Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) u t := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        have hfold :
            (List.finRange (m + 1)).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal ((Fin.snoc
                    (α := fun _ : Fin (m + 1) => ℝ) u t) i)))
                    (fun z => f i z * r z) y)
                q x =
              lTail.foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal ((Fin.snoc
                    (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                    (fun z => f i z * r z) y)
                (fun z => qLast t z) x := by
          rw [aux_determining_functional_identity_positive_increment_laplace_fubini_finRange_snoc, List.foldr_append]
          simp [lTail, qLast, gLast, j, List.foldr_map,
            Fin.snoc_castSucc, Fin.snoc_last]
        have hsum_eq :
            (∑ i : Fin (m + 1), (n i : ℝ) *
                (Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) u t) i) =
              (∑ i : Fin m, (n i.castSucc : ℝ) * u i) + (n j : ℝ) * t := by
          rw [Fin.sum_univ_castSucc]
          simp [Fin.snoc_castSucc, Fin.snoc_last, j]
        rw [heval]
        dsimp
        rw [hsum_eq, hfold]
        rw [show Real.exp (-((∑ i : Fin m, (n i.castSucc : ℝ) * u i) +
              (n j : ℝ) * t)) =
            Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
              Real.exp (-((n j : ℝ) * t)) by
          rw [← Real.exp_add]
          congr 1
          ring]
        ring
      have hcalc :
          (∫ s : (Fin (m + 1) → ℝ),
              Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
                (List.finRange (m + 1)).foldr
                  (fun i (r : α → ℝ) => fun y =>
                    kernelIntegral (P (Real.toNNReal (s i)))
                      (fun z => f i z * r z) y)
                  q x ∂(Measure.pi (fun _ : Fin (m + 1) => μ))) =
            ∫ u : Fin m → ℝ,
              Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
                (∫ t : ℝ, Real.exp (-(n j : ℝ) * t) *
                  lTail.foldr
                    (fun i (r : α → ℝ) => fun z =>
                      kernelIntegral
                        (P (Real.toNNReal ((Fin.snoc
                          (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                        (fun v => f i v * r v) z)
                    (fun z => qLast t z) x ∂μ)
              ∂(Measure.pi (fun _ : Fin m => μ)) := by
        calc
          (∫ s : (Fin (m + 1) → ℝ),
              Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
                (List.finRange (m + 1)).foldr
                  (fun i (r : α → ℝ) => fun y =>
                    kernelIntegral (P (Real.toNNReal (s i)))
                      (fun z => f i z * r z) y)
                  q x ∂(Measure.pi (fun _ : Fin (m + 1) => μ))) =
              ∫ p : ℝ × (Fin m → ℝ),
                (fun s : Fin (m + 1) → ℝ =>
                  Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
                    (List.finRange (m + 1)).foldr
                      (fun i (r : α → ℝ) => fun y =>
                        kernelIntegral (P (Real.toNNReal (s i)))
                          (fun z => f i z * r z) y)
                      q x) (e.symm p)
                ∂(μ.prod (Measure.pi (fun _ : Fin m => μ))) := by
            symm
            exact he'.symm.integral_comp' (fun s =>
              Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
                (List.finRange (m + 1)).foldr
                  (fun i (r : α → ℝ) => fun y =>
                    kernelIntegral (P (Real.toNNReal (s i)))
                      (fun z => f i z * r z) y)
                  q x)
          _ = ∫ u : Fin m → ℝ,
                ∫ t : ℝ,
                  (fun s : Fin (m + 1) → ℝ =>
                    Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
                      (List.finRange (m + 1)).foldr
                        (fun i (r : α → ℝ) => fun z =>
                          kernelIntegral (P (Real.toNNReal (s i)))
                            (fun z => f i z * r z) z)
                        q x) (e.symm (t, u)) ∂μ
                ∂(Measure.pi (fun _ : Fin m => μ)) := hprod
          _ = ∫ u : Fin m → ℝ,
                Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
                  (∫ t : ℝ, Real.exp (-(n j : ℝ) * t) *
                    lTail.foldr
                      (fun i (r : α → ℝ) => fun z =>
                        kernelIntegral
                          (P (Real.toNNReal ((Fin.snoc
                            (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                          (fun v => f i v * r v) z)
                      (fun z => qLast t z) x ∂μ)
                ∂(Measure.pi (fun _ : Fin m => μ)) := by
            apply integral_congr_ae
            filter_upwards with u
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with t
            exact hpoint t u
      let fTail : Fin m → α → ℝ := fun i => f i.castSucc
      let nTail : Fin m → Nat := fun i => n i.castSucc
      let qTail : α → ℝ := R (n j) gLast
      have hIH := ih (f := fTail) (n := nTail) (q := qTail)
        (C := (A * C) / (n j : ℝ))
        (by
          intro i y
          exact htailf i y)
        (by
          intro i
          exact htailmeas i)
        (by
          intro y
          exact hq'B y)
        hq'
        htailn
      have hmeasureTail :
          (volume : Measure (Fin m → ℝ)).restrict
              (Set.univ.pi (fun _ : Fin m => Set.Ioi (0 : ℝ))) =
            Measure.pi (fun _ : Fin m => μ) := by
        rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
      have hIH' :
          (∫ u : (Fin m → ℝ),
            Real.exp (-(∑ i : Fin m, (nTail i : ℝ) * u i)) *
              (List.finRange m).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (u i)))
                    (fun z => fTail i z * r z) y)
                qTail x ∂(Measure.pi (fun _ : Fin m => μ))) =
          (List.finRange m).foldr
            (fun i (r : α → ℝ) => fun y =>
              R (nTail i) (fun z => fTail i z * r z) y)
            qTail x := by
        rw [← hmeasureTail]
        exact hIH
      calc
        (∫ s : (Fin (m + 1) → ℝ),
            Real.exp (-(∑ i : Fin (m + 1), (n i : ℝ) * s i)) *
              (List.finRange (m + 1)).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)))
                    (fun z => f i z * r z) y)
                q x ∂(Measure.pi (fun _ : Fin (m + 1) => μ))) =
          ∫ u : (Fin m → ℝ),
            Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
              (∫ t : ℝ, Real.exp (-(n j : ℝ) * t) *
                lTail.foldr
                  (fun i (r : α → ℝ) => fun z =>
                    kernelIntegral
                      (P (Real.toNNReal ((Fin.snoc
                        (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                      (fun v => f i v * r v) z)
                  (fun z => qLast t z) x ∂μ)
            ∂(Measure.pi (fun _ : Fin m => μ)) := hcalc
        _ = ∫ u : (Fin m → ℝ),
            Real.exp (-(∑ i : Fin m, (n i.castSucc : ℝ) * u i)) *
              (List.finRange m).foldr
                (fun i (r : α → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (u i)))
                    (fun z => fTail i z * r z) y)
                qTail x ∂(Measure.pi (fun _ : Fin m => μ)) := by
            apply integral_congr_ae
            filter_upwards with u
            rw [show (∫ t : ℝ, Real.exp (-(n j : ℝ) * t) *
                lTail.foldr
                  (fun i (r : α → ℝ) => fun z =>
                    kernelIntegral
                      (P (Real.toNNReal ((Fin.snoc
                        (α := fun _ : Fin (m + 1) => ℝ) u (0 : ℝ)) i)))
                      (fun v => f i v * r v) z)
                  (fun z => qLast t z) x ∂μ) =
                (List.finRange m).foldr
                  (fun i (r : α → ℝ) => fun y =>
                    kernelIntegral (P (Real.toNNReal (u i)))
                      (fun z => fTail i z * r z) y)
                  qTail x by
              simpa [μ, lTail, fTail, qTail, List.foldr_map] using houter u x]
        _ = (List.finRange m).foldr
              (fun i (r : α → ℝ) => fun y =>
                R (nTail i) (fun z => fTail i z * r z) y)
              qTail x := hIH'
        _ = ((List.finRange (m + 1)).foldr
              (fun i (r : α → ℝ) => fun y =>
                R (n i) (fun z => f i z * r z) y)
              q) x := by
            rw [aux_determining_functional_identity_positive_increment_laplace_fubini_finRange_snoc, List.foldr_append]
            simp [qTail, gLast, j, fTail, nTail, List.foldr_map]



/-- Fine proof step for the positive-increment Laplace/Fubini calculation in
the determining-functional paragraph.

Carried-input Scope and inputs:
- `P` is the cutoff semigroup and `R` is carried from the whole-space
  resolvent definition  by `hR`.
- `f` is a bounded continuous family, `n` is a positive-integer family,
  and the integration domain is the full positive orthant.
- The inner expression is the successive transition-kernel fold with
  one time increment per factor.
- The conclusion is only the finite Laplace/Fubini-to-resolvent step;
  path-law transport is supplied by a separate fine child.
- This is a proof-step refinement of `determining_functional_identity`.
-/
theorem determining_functional_identity_positive_increment_laplace_fubini
    {d m : Nat}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (_hP : P.IsConservative)
    (R : Nat → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hR : ∀ r q x, R r q x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) q x)
    (f : Fin m → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin m → Nat)
    (hn : ∀ i, 0 < n i)
    (x : SpatialCoordinates d) :
    (∫ s in Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ)),
      Real.exp (-(∑ i : Fin m, (n i : ℝ) * s i)) *
        ((List.finRange m).foldr
          (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
            kernelIntegral (P (Real.toNNReal (s i)) )
              (fun z => f i z * q z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x) =
      ((List.finRange m).foldr
        (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
          R (n i) (fun z => f i z * q z) y)
        (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
  let f' : Fin m → SpatialCoordinates d → ℝ := fun i z => f i z
  let A : ℝ := 1 + ∑ i : Fin m, ‖f i‖
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfA : ∀ i y, |f' i y| ≤ A := by
    intro i y
    dsimp [A, f']
    calc
      |f i y| = ‖f i y‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖f i‖ := (f i).norm_coe_le_norm y
      _ ≤ ∑ j : Fin m, ‖f j‖ := by
        exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j : Fin m, ‖f j‖ := by linarith
  have hf : ∀ i, Measurable (f' i) := by
    intro i
    exact (f i).measurable
  have hqC : ∀ y : SpatialCoordinates d,
      |(fun _ : SpatialCoordinates d => (1 : ℝ)) y| ≤ (1 : ℝ) := by
    intro y
    simp
  have hq : Measurable (fun _ : SpatialCoordinates d => (1 : ℝ)) :=
    measurable_const
  simpa [f'] using
    (aux_determining_functional_identity_positive_increment_laplace_fubini_product_fold
      (α := SpatialCoordinates d) P R hR f' n
      (fun _ : SpatialCoordinates d => (1 : ℝ)) hA hfA hf hqC hq hn x)

end SubdiffusiveProcess.Paper
