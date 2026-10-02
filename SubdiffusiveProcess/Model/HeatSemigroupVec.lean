import Mathlib
import MarkovProcess.Main
import MarkovProcess.Examples.HeatSemigroup
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

/-!
# The `d`-dimensional heat semigroup

`MarkovProcess/Examples/HeatSemigroup.lean` builds the heat semigroup **on the real line only**
("Only one space dimension is treated: the multidimensional heat semigroup is not constructed
here").  The Section 9 vocabulary lives on `Vec d = Fin d → ℝ`, so this module carries that
example over to `Vec d`, keeping the one-dimensional file's proof architecture and reusing its
one-dimensional inputs (`bind_gaussianReal`, `gaussianReal_eq_map_add_sqrt_mul`,
`lintegral_enorm_pow_gaussianReal_lt_top`).  Provenance: every proof below whose name matches a
name in `MarkovProcess/Examples/HeatSemigroup.lean` is that proof with `ℝ` replaced by `Vec d`,
`Real.sqrt t * z` by `Real.sqrt t • z` and `|z|` by `‖z‖`.

## What is built

* `gaussianVec d x v` — the Gaussian with independent coordinates, mean `x`, variance `v`;
* `gaussianVec_eq_map` — its scaling representation `z ↦ x + √v • z` off the standard Gaussian;
* `bind_gaussianVec` — the Chapman–Kolmogorov identity, from the one-dimensional
  `MarkovProcess.bind_gaussianReal` through `lintegral_fin_prod_eq_prod`;
* `heatSemigroupVec d : SubMarkovKernelSemigroup (Vec d)`, with
  `isConservative_heatSemigroupVec`, `isFellerKernelSemigroup_heatSemigroupVec` and
  `hasKolmogorovMoments_heatSemigroupVec` (exponents `4`, `2`);
* `existsUnique_continuousProcess_heatSemigroupVec` — the main theorem of `MarkovProcess`
  applied, and `brownianMotionVec`, the `d`-dimensional Brownian motion as a Markov kernel into
  continuous paths.

The variance at time `t` is `t`, so the generator is `Δ/2`.  A `LocalDiffusion` witness for the
constant coefficient `c = ρ = 1` needs generator `Δ` (see the resolvent clause of
`SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion` against
`SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn`), i.e. the time change
`t ↦ 2t`; nothing here depends on that choice.

`lintegral_fin_prod_eq_prod` is the `ℝ≥0∞` companion of Mathlib's
`MeasureTheory.integral_fin_nat_prod_eq_prod`, which exists only for Bochner integrals.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Model.HeatSemigroupVec

variable {d : ℕ}

/-- The `d`-dimensional Gaussian with independent coordinates. -/
def gaussianVec (d : ℕ) (x : Vec d) (v : NNReal) : Measure (Vec d) :=
  Measure.pi (fun i => gaussianReal (x i) v)

instance isProbabilityMeasure_gaussianVec (x : Vec d) (v : NNReal) :
    IsProbabilityMeasure (gaussianVec d x v) := by
  unfold gaussianVec; infer_instance

theorem gaussianVec_pi (x : Vec d) (v : NNReal) (A : Fin d → Set ℝ) :
    gaussianVec d x v (Set.univ.pi A) = ∏ i, gaussianReal (x i) v (A i) := by
  rw [gaussianVec, Measure.pi_pi]

/-- The scaling representation of the `d`-dimensional Gaussian. -/
theorem gaussianVec_eq_map (x : Vec d) (v : NNReal) :
    gaussianVec d x v
      = (gaussianVec d 0 1).map (fun z : Vec d => x + Real.sqrt v • z) := by
  have hmap : ∀ i : Fin d, (gaussianReal 0 1).map (fun z : ℝ => x i + Real.sqrt v * z)
      = gaussianReal (x i) v := fun i => (gaussianReal_eq_map_add_sqrt_mul (x i) v).symm
  have hsig : ∀ i : Fin d,
      SigmaFinite ((gaussianReal (0:ℝ) 1).map (fun z : ℝ => x i + Real.sqrt v * z)) := by
    intro i; rw [hmap i]; infer_instance
  have := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1)
    (f := fun (i : Fin d) (z : ℝ) => x i + Real.sqrt v * z)
    (hμ := hsig) (fun i => (by fun_prop : Measurable fun z : ℝ => x i + Real.sqrt v * z).aemeasurable)
  have hfun : (fun z : Vec d => x + Real.sqrt v • z)
      = fun (w : Vec d) (i : Fin d) => x i + Real.sqrt v * w i := rfl
  have hbase : (Measure.pi fun i : Fin d => gaussianReal ((0 : Vec d) i) (1 : NNReal))
      = Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1 := rfl
  rw [gaussianVec, gaussianVec, hfun, hbase, this]
  simp only [hmap]


theorem lintegral_fin_prod_eq_prod {E : Type*} [MeasurableSpace E] :
    ∀ {n : ℕ} (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ z, f i z ∂(μ i) := by
  intro n
  induction n with
  | zero => intro μ _ f _; simp
  | succ n ih =>
    intro μ _ f hf
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove μ 0
    have hG : Measurable (fun p : E × (Fin n → E) =>
        f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) := by
      refine (hf 0).comp measurable_fst |>.mul ?_
      exact Finset.measurable_prod _ (fun i _ => (hf i.succ).comp ((measurable_pi_apply i).comp measurable_snd))
    have hcomp := hmp.lintegral_comp hG
    have hlhs : ∀ a : Fin (n+1) → E,
        (fun p : E × (Fin n → E) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
          ((MeasurableEquiv.piFinSuccAbove (fun _ => E) 0) a)
        = ∏ i, f i (a i) := by
      intro a
      rw [Fin.prod_univ_succ]
      simp
      rfl
    have hstep : ∫⁻ (x : Fin (n+1) → E), ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ b : E × (Fin n → E), f 0 b.1 * ∏ i : Fin n, f i.succ (b.2 i)
            ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) := by
      rw [← hcomp]
      exact lintegral_congr fun a => (hlhs a).symm
    have hg2 : AEMeasurable (fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i))
        (Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
      (Finset.measurable_prod (Finset.univ : Finset (Fin n))
        (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable
    rw [hstep, lintegral_prod_mul (f := f 0)
      (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i)) (hf 0).aemeasurable hg2,
      Fin.prod_univ_succ]
    congr 1
    exact ih (fun j => μ (Fin.succAbove 0 j)) (fun j => f j.succ) (fun j => hf j.succ)

/-! ### The kernel -/

/-- The `d`-dimensional Gaussian transition kernel, jointly in time and starting point. -/
def heatKernelVecJoint (d : ℕ) : Kernel (NNReal × Vec d) (Vec d) :=
  (Kernel.id ×ₖ Kernel.const (NNReal × Vec d) (gaussianVec d 0 1)).map
    (fun q : (NNReal × Vec d) × Vec d => q.1.2 + Real.sqrt q.1.1 • q.2)

theorem heatKernelVecJoint_apply (p : NNReal × Vec d) :
    heatKernelVecJoint d p = gaussianVec d p.2 p.1 := by
  have hmeas : Measurable
      (fun q : (NNReal × Vec d) × Vec d => q.1.2 + Real.sqrt q.1.1 • q.2) := by
    fun_prop
  rw [heatKernelVecJoint, Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hmeas (by fun_prop)]
  conv_rhs => rw [gaussianVec_eq_map p.2 p.1]
  rfl

/-- The transition kernel at time `t`. -/
def heatKernelVec (d : ℕ) (t : NNReal) : Kernel (Vec d) (Vec d) :=
  Kernel.comap (heatKernelVecJoint d) (fun x : Vec d => (t, x)) (by fun_prop)

@[simp]
theorem heatKernelVec_apply (t : NNReal) (x : Vec d) :
    heatKernelVec d t x = gaussianVec d x t := by
  rw [heatKernelVec, Kernel.comap_apply, heatKernelVecJoint_apply]

theorem measurable_gaussianVec_left (t : NNReal) :
    Measurable (fun x : Vec d => gaussianVec d x t) := by
  have hfun : (fun x : Vec d => gaussianVec d x t) = fun x => heatKernelVec d t x :=
    funext fun x => (heatKernelVec_apply t x).symm
  rw [hfun]
  exact (heatKernelVec d t).measurable


/-! ### Chapman--Kolmogorov -/


theorem bind_gaussianVec (x : Vec d) (s t : NNReal) :
    (gaussianVec d x s).bind (fun y => gaussianVec d y t) = gaussianVec d x (s + t) := by
  show (gaussianVec d x s).bind (fun y => gaussianVec d y t)
      = Measure.pi fun i => gaussianReal (x i) (s + t)
  refine (Measure.pi_eq fun A hA => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hA) (measurable_gaussianVec_left t).aemeasurable]
  have hinner : ∀ y : Vec d, gaussianVec d y t (Set.univ.pi A)
      = ∏ i, gaussianReal (y i) t (A i) := fun y => gaussianVec_pi y t A
  simp_rw [hinner]
  rw [show gaussianVec d x s = Measure.pi fun i => gaussianReal (x i) s from rfl,
    lintegral_fin_prod_eq_prod (fun i => gaussianReal (x i) s)
      (fun i z => gaussianReal z t (A i))
      (fun i => (Measure.measurable_coe (hA i)).comp (measurable_gaussianReal_left t))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Measure.bind_apply (hA i) (measurable_gaussianReal_left t).aemeasurable,
    bind_gaussianReal]


/-! ### The semigroup -/

instance isMarkovKernel_heatKernelVec (t : NNReal) : IsMarkovKernel (heatKernelVec d t) :=
  ⟨fun x => by rw [heatKernelVec_apply]; infer_instance⟩

theorem gaussianVec_zero (x : Vec d) : gaussianVec d x 0 = Measure.dirac x := by
  have hfun : (fun z : Vec d => x + Real.sqrt ((0 : NNReal) : ℝ) • z) = fun _ : Vec d => x := by
    funext z
    simp
  rw [gaussianVec_eq_map x 0, hfun, Measure.map_const, measure_univ, one_smul]

/-- **The `d`-dimensional heat semigroup**: the transition measure at time `t` from `x` is the
Gaussian with mean `x` and variance `t` in each coordinate, coordinates independent. -/
def heatSemigroupVec (d : ℕ) : SubMarkovKernelSemigroup (Vec d) where
  kernel := heatKernelVec d
  measurable_kernel := by
    have hfun : (fun p : NNReal × Vec d => heatKernelVec d p.1 p.2)
        = fun p => heatKernelVecJoint d p := by
      funext p
      rw [heatKernelVec, Kernel.comap_apply]
    rw [hfun]
    exact (heatKernelVecJoint d).measurable
  kernel_zero := Kernel.ext fun x => by
    rw [heatKernelVec_apply, gaussianVec_zero, Kernel.id_apply]
  kernel_add := fun s t => Kernel.ext fun x => by
    have hfun : ⇑(heatKernelVec d t) = fun y => gaussianVec d y t :=
      funext (heatKernelVec_apply t)
    rw [Kernel.comp_apply, heatKernelVec_apply, heatKernelVec_apply, hfun, bind_gaussianVec]
  isSubMarkovKernel := fun _ => IsSubMarkovKernel.of_isMarkovKernel _

@[simp]
theorem heatSemigroupVec_apply (t : NNReal) (x : Vec d) :
    heatSemigroupVec d t x = gaussianVec d x t :=
  heatKernelVec_apply t x

theorem isConservative_heatSemigroupVec :
    (heatSemigroupVec d).IsConservative := by
  intro t x
  rw [heatSemigroupVec_apply]
  exact measure_univ


/-! ### The Feller property -/

theorem kernelIntegral_heatSemigroupVec (t : NNReal) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    kernelIntegral (heatSemigroupVec d t) f x
      = ∫ z, f (x + Real.sqrt t • z) ∂(gaussianVec d 0 1) := by
  rw [kernelIntegral, heatSemigroupVec_apply, gaussianVec_eq_map]
  exact integral_map (φ := fun z : Vec d => x + Real.sqrt t • z) (f := fun y : Vec d => f y)
    (by fun_prop) f.continuous.aestronglyMeasurable

theorem norm_apply_le_norm_c0 (f : C₀(Vec d, ℝ)) (x : Vec d) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

theorem isCountablyGenerated_cocompact_vec :
    (Filter.cocompact (Vec d)).IsCountablyGenerated := by
  rw [← comap_dist_left_atTop_eq_cocompact (0 : Vec d)]
  infer_instance

theorem integrable_c0_comp (f : C₀(Vec d, ℝ)) (t : NNReal) (x : Vec d) :
    Integrable (fun z => f (x + Real.sqrt t • z)) (gaussianVec d 0 1) := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0 f _

theorem mapsC0_heatSemigroupVec : (heatSemigroupVec d).MapsC0 := by
  intro t f
  have hrep : kernelIntegral (heatSemigroupVec d t) f =
      fun x => ∫ z, f (x + Real.sqrt t • z) ∂(gaussianVec d 0 1) :=
    funext (kernelIntegral_heatSemigroupVec t f)
  rw [hrep]
  constructor
  · refine continuous_of_dominated (F := fun (x z : Vec d) => f (x + Real.sqrt t • z))
      (bound := fun _ => ‖f‖) ?_ ?_ (integrable_const (μ := gaussianVec d 0 1) ‖f‖) ?_
    · exact fun x => (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun x => Filter.Eventually.of_forall fun z => norm_apply_le_norm_c0 f _
    · exact Filter.Eventually.of_forall fun z => f.continuous.comp (by fun_prop)
  · have hcg := isCountablyGenerated_cocompact_vec (d := d)
    refine Filter.tendsto_iff_seq_tendsto.mpr fun u hu => ?_
    have hlim : Filter.Tendsto
        (fun n => ∫ z, f (u n + Real.sqrt t • z) ∂(gaussianVec d 0 1)) atTop
        (nhds (∫ _z : Vec d, (0 : ℝ) ∂(gaussianVec d 0 1))) := by
      refine tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (z : Vec d) => f (u n + Real.sqrt t • z)) (fun _ => ‖f‖)
        (fun _ => (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (integrable_const (μ := gaussianVec d 0 1) ‖f‖)
        (fun _ => Filter.Eventually.of_forall fun _ => norm_apply_le_norm_c0 f _)
        (Filter.Eventually.of_forall fun z => ?_)
      have htranslate : Filter.Tendsto (fun y : Vec d => y + Real.sqrt t • z)
          (Filter.cocompact (Vec d)) (Filter.cocompact (Vec d)) :=
        CocompactMapClass.cocompact_tendsto
          ((Homeomorph.addRight (Real.sqrt t • z)).toCocompactMap)
      exact f.zero_at_infty'.comp (htranslate.comp hu)
    rw [integral_zero] at hlim
    exact hlim


/-- A finite measure on `Vec d` puts arbitrarily little mass far from the origin. -/
theorem exists_measure_norm_ge_lt (nu : Measure (Vec d)) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {z : Vec d | R ≤ ‖z‖}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {z : Vec d | (n : ℝ) ≤ ‖z‖} nu := fun n =>
    ((isClosed_le continuous_const continuous_norm).measurableSet).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ => {z : Vec d | (n : ℝ) ≤ ‖z‖}) := by
    intro n m hnm z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hz
  have hempty : (⋂ n : ℕ, {z : Vec d | (n : ℝ) ≤ ‖z‖}) = (∅ : Set (Vec d)) := by
    refine Set.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact absurd (Set.mem_iInter.mp hz n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {z : Vec d | (n : ℝ) ≤ ‖z‖} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩


/-- The `C₀` orbit displacement of the `d`-dimensional heat semigroup is uniformly small over
short times. -/
theorem exists_norm_c0Operator_sub_le_heatSemigroupVec (f : C₀(Vec d, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : NNReal, (h : ℝ) < delta →
      ‖(heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hfpos : (0 : ℝ) < 4 * (‖f‖ + 1) := by positivity
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_norm_ge_lt (gaussianVec d 0 1)
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set (Vec d) := {z : Vec d | R ≤ ‖z‖} with hS
  have hSmeas : MeasurableSet S :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  set bound : Vec d → ℝ := fun z => eps / 2 + 2 * ‖f‖ * S.indicator (fun _ => (1 : ℝ)) z
    with hbound
  have hindInt : Integrable (S.indicator (fun _ => (1 : ℝ))) (gaussianVec d 0 1) :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound (gaussianVec d 0 1) :=
    (integrable_const (μ := gaussianVec d 0 1) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ z, bound z ∂(gaussianVec d 0 1) ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := gaussianVec d 0 1) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hnorm : 0 ≤ ‖f‖ := norm_nonneg f
    have hkey : 2 * ‖f‖ * ((gaussianVec d 0 1).real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ (gaussianVec d 0 1).real S := measureReal_nonneg
      calc 2 * ‖f‖ * ((gaussianVec d 0 1).real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            apply mul_le_mul _ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh => ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at this
    calc Real.sqrt h * R < (delta0 / R) * R := mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun x => ?_
  show ‖(heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec h f x - f x‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_heatSemigroupVec]
  have hsub : (∫ z, f (x + Real.sqrt h • z) ∂(gaussianVec d 0 1)) - f x =
      ∫ z, (f (x + Real.sqrt h • z) - f x) ∂(gaussianVec d 0 1) := by
    rw [integral_sub (integrable_c0_comp f h x) (integrable_const (f x)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun z => ?_)) hboundIntegral
  by_cases hz : z ∈ S
  · have h1 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ 2 * ‖f‖ := by
      calc ‖f (x + Real.sqrt h • z) - f x‖ ≤ ‖f (x + Real.sqrt h • z)‖ + ‖f x‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_apply_le_norm_c0 f _) (norm_apply_le_norm_c0 f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hz, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (x + Real.sqrt h • z) x < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzR : ‖z‖ < R := lt_of_not_ge (by simpa only [hS, Set.mem_setOf_eq] using hz)
      calc Real.sqrt h * ‖z‖ ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hzR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
    exact h2


/-- The `C₀` orbits of the `d`-dimensional heat semigroup are continuous in time. -/
theorem hasContinuousC0Orbits_heatSemigroupVec :
    (heatSemigroupVec d).HasContinuousC0Orbits mapsC0_heatSemigroupVec := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hkey⟩ :=
    exists_norm_c0Operator_sub_le_heatSemigroupVec f (half_pos heps)
  refine ⟨delta, hdelta, fun a hab => ?_⟩
  have hcontraction : ∀ c e : NNReal, c ≤ e → (e : ℝ) - (c : ℝ) < delta →
      dist ((heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec e f)
        ((heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec c f) ≤ eps / 2 := by
    intro c e hce hlt
    have hdc : c + (e - c) = e := add_tsub_cancel_of_le hce
    have hcoe : ((e - c : NNReal) : ℝ) < delta := by
      rw [NNReal.coe_sub hce]
      exact hlt
    have hop : (heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec e f =
        (heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec c
          ((heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec (e - c) f) := by
      conv_lhs => rw [← hdc]
      rw [SubMarkovKernelSemigroup.c0Operator_add]
      rfl
    rw [dist_eq_norm, hop, ← map_sub]
    calc ‖(heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec c
            ((heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec (e - c) f - f)‖
        ≤ ‖(heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec c‖ *
            ‖(heatSemigroupVec d).c0Operator mapsC0_heatSemigroupVec (e - c) f - f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (eps / 2) := by
          refine mul_le_mul (SubMarkovKernelSemigroup.norm_c0Operator_le _ _ c)
            (hkey _ hcoe) (norm_nonneg _) zero_le_one
      _ = eps / 2 := one_mul _
  have habs : |(a : ℝ) - (b : ℝ)| < delta := by
    rw [← NNReal.dist_eq]
    exact hab
  rcases le_total b a with hba | hab'
  · have := hcontraction b a hba (by
      rw [abs_of_nonneg (by
        have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
        linarith only [this])] at habs
      exact habs)
    linarith only [this, heps]
  · have := hcontraction a b hab' (by
      rw [abs_sub_comm, abs_of_nonneg (by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
        linarith only [this])] at habs
      exact habs)
    rw [dist_comm]
    linarith only [this, heps]

/-- **The `d`-dimensional heat semigroup is a Feller semigroup.** -/
theorem isFellerKernelSemigroup_heatSemigroupVec :
    (heatSemigroupVec d).IsFellerKernelSemigroup :=
  ⟨mapsC0_heatSemigroupVec, hasContinuousC0Orbits_heatSemigroupVec⟩


/-! ### Kolmogorov moments -/

theorem norm_pow_four_le_sum (w : Vec d) : ‖w‖ ^ (4:ℕ) ≤ ∑ i, ‖w i‖ ^ (4:ℕ) := by
  set s : ℝ := ∑ i, ‖w i‖ ^ (4:ℕ) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖w‖ ≤ s ^ ((1:ℝ)/4) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hi : ‖w i‖ ^ (4:ℕ) ≤ s :=
      Finset.single_le_sum (f := fun j => ‖w j‖ ^ (4:ℕ)) (fun j _ => by positivity)
        (Finset.mem_univ i)
    have h1 : (‖w i‖ ^ (4:ℕ) : ℝ) ^ ((1:ℝ)/4) ≤ s ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hi (by norm_num)
    have h2 : (‖w i‖ ^ (4:ℕ) : ℝ) ^ ((1:ℝ)/4) = ‖w i‖ := by
      rw [← Real.rpow_natCast ‖w i‖ 4, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rwa [h2] at h1
  calc ‖w‖ ^ (4:ℕ) ≤ (s ^ ((1:ℝ)/4)) ^ (4:ℕ) := by
        gcongr
    _ = s := by
        rw [← Real.rpow_natCast (s ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hs0]
        norm_num



theorem enorm_pow_four_le_sum (w : Vec d) : ‖w‖ₑ ^ (4:ℕ) ≤ ∑ i, ‖w i‖ₑ ^ (4:ℕ) := by
  have hL : ‖w‖ₑ ^ (4:ℕ) = ENNReal.ofReal (‖w‖ ^ (4:ℕ)) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hR : ∀ i : Fin d, ‖w i‖ₑ ^ (4:ℕ) = ENNReal.ofReal (‖w i‖ ^ (4:ℕ)) := by
    intro i
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hL]
  simp_rw [hR]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (norm_pow_four_le_sum w)

theorem lintegral_enorm_pow_gaussianVec_lt_top :
    ∫⁻ w, ‖w‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1) < ⊤ := by
  have hmeas : ∀ i : Fin d, Measurable (fun w : Vec d => ‖w i‖ₑ ^ (4:ℕ)) := by
    intro i
    exact ((measurable_pi_apply i).enorm).pow_const 4
  have hmarg : ∀ i : Fin d, ∫⁻ w, ‖w i‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1)
      = ∫⁻ z : ℝ, ‖z‖ₑ ^ (4:ℕ) ∂(gaussianReal 0 1) := by
    intro i
    have hmp := MeasureTheory.measurePreserving_eval
      (fun _ : Fin d => gaussianReal (0:ℝ) 1) i
    exact hmp.lintegral_comp (measurable_enorm.pow_const 4)
  calc ∫⁻ w, ‖w‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1)
      ≤ ∫⁻ w, ∑ i, ‖w i‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1) :=
        lintegral_mono enorm_pow_four_le_sum
    _ = ∑ i, ∫⁻ w, ‖w i‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1) :=
        lintegral_finset_sum _ (fun i _ => hmeas i)
    _ < ⊤ := by
        rw [Finset.sum_congr rfl (fun i _ => hmarg i)]
        exact ENNReal.sum_lt_top.mpr
          (fun i _ => lintegral_enorm_pow_gaussianReal_lt_top)



/-- The fourth moment of the standard `d`-dimensional Gaussian. -/
def vecFourthMoment (d : ℕ) : NNReal :=
  (∫⁻ w, ‖w‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1)).toNNReal

theorem coe_vecFourthMoment :
    ((vecFourthMoment d : NNReal) : ℝ≥0∞) = ∫⁻ w, ‖w‖ₑ ^ (4:ℕ) ∂(gaussianVec d 0 1) :=
  ENNReal.coe_toNNReal lintegral_enorm_pow_gaussianVec_lt_top.ne

/-- **The `d`-dimensional heat semigroup satisfies the Kolmogorov moment criterion** with
exponents `p = 4`, `q = 2` and the fourth moment of the standard `d`-dimensional Gaussian as
constant. -/
theorem hasKolmogorovMoments_heatSemigroupVec :
    (heatSemigroupVec d).HasKolmogorovMoments 4 2 (vecFourthMoment d) := by
  refine ⟨by norm_num, by norm_num, fun h y => ?_⟩
  have hmeasint : Measurable (fun z : Vec d => edist z y ^ (4:ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 4
  rw [heatSemigroupVec_apply, gaussianVec_eq_map y h,
    lintegral_map hmeasint (by fun_prop)]
  have hint : ∀ w : Vec d, edist (y + Real.sqrt h • w) y ^ (4:ℝ)
      = ‖(Real.sqrt h : ℝ)‖ₑ ^ (4:ℝ) * ‖w‖ₑ ^ (4:ℝ) := by
    intro w
    rw [edist_eq_enorm_sub, add_sub_cancel_left, enorm_smul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp_rw [hint]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hval : Real.sqrt h ^ (4:ℝ) = (h : ℝ) ^ (2:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h.coe_nonneg]
    norm_num
  have hsq : ‖(Real.sqrt h : ℝ)‖ₑ ^ (4:ℝ) = (h : ℝ≥0∞) ^ (2:ℝ) := by
    calc ‖(Real.sqrt h : ℝ)‖ₑ ^ (4:ℝ)
        = ENNReal.ofReal (Real.sqrt h) ^ (4:ℝ) := by
          rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt h ^ (4:ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
      _ = ENNReal.ofReal ((h : ℝ) ^ (2:ℝ)) := by rw [hval]
      _ = ENNReal.ofReal (h : ℝ) ^ (2:ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg h.coe_nonneg (by norm_num : (0:ℝ) ≤ 2)).symm
      _ = (h : ℝ≥0∞) ^ (2:ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
  rw [hsq, coe_vecFourthMoment]
  have hpow : ∀ w : Vec d, ‖w‖ₑ ^ (4:ℝ) = ‖w‖ₑ ^ (4:ℕ) := by
    intro w
    rw [← ENNReal.rpow_natCast ‖w‖ₑ 4]
    norm_num
  simp_rw [hpow]
  exact le_of_eq (mul_comm _ _)

/-! ### The continuous-path process -/

theorem kolmogorovRegular_heatSemigroupVec :
    (heatSemigroupVec d).KolmogorovRegular isConservative_heatSemigroupVec :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroupVec hasKolmogorovMoments_heatSemigroupVec

/-- **The main theorem of `MarkovProcess`, applied to the `d`-dimensional heat semigroup.** -/
theorem existsUnique_continuousProcess_heatSemigroupVec :
    ∃! Q : Kernel (Vec d) (ContinuousPath (Vec d)), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroupVec d) I :=
  isFellerKernelSemigroup_heatSemigroupVec.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (heatSemigroupVec d) isConservative_heatSemigroupVec hasKolmogorovMoments_heatSemigroupVec

/-- **`d`-dimensional Brownian motion**, as a Markov kernel from the starting point to
continuous paths. -/
def brownianMotionVec (d : ℕ) : Kernel (Vec d) (ContinuousPath (Vec d)) :=
  SubMarkovKernelSemigroup.IsConservative.continuousProcess (heatSemigroupVec d)
    isConservative_heatSemigroupVec

instance isMarkovKernel_brownianMotionVec : IsMarkovKernel (brownianMotionVec d) := by
  unfold brownianMotionVec
  infer_instance

end SubdiffusiveProcess.Model.HeatSemigroupVec
