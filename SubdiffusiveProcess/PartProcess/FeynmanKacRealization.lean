module

public import SubdiffusiveProcess.PartProcess.Data
public import MarkovProcess.Trajectory.FeynmanKacRealResolvent

@[expose] public section

/-! Feynman--Kac identities for a supplied realization. The finite-time argument is adapted
from MarkovProcess.Trajectory.FeynmanKacResolvent (Scott Armstrong, Apache 2.0). -/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubMarkovKernelSemigroup
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

def realFk (S : Data d m) (q : (Fin d → ℝ) → ℝ) (t : NNReal)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ w, Real.exp (-feynmanKacAdditiveFunctional q t w) * f (w t) ∂S.law x

theorem law_map_eval (S : Data d m) (t : NNReal) :
    S.law.map (fun w => w t) = S.semigroup t := by
  let := S.markov

  classical
  let I : Finset NNReal := {t}
  let z : I := ⟨t, Finset.mem_singleton_self t⟩
  let i : Fin I.card := (I.orderIsoOfFin rfl).symm z
  let e : Fin 1 ↪o Fin I.card := OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    simp only [ha, hb, lt_self_iff_false] at hab)
  have hfun : (fun path : ContinuousPath (Fin d → ℝ) ↦ path t) =
      (fun path : I → (Fin d → ℝ) ↦ path z) ∘ ContinuousPath.finsetEvaluation I := rfl
  have hEval : Measurable (ContinuousPath.finsetEvaluation (alpha := (Fin d → ℝ)) I) :=
    measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess t
  rw [hfun, Kernel.map_comp_right S.law hEval
    (measurable_pi_apply z), show S.law.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel S.semigroup I from Kernel.ext (fun x => S.marginals I x), finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I)
      (measurable_pi_apply z)]
  change (finiteTimeKernel S.semigroup (finiteSetTimes I)).map (fun path ↦ path i) = _
  have hfun' : (fun path : Fin I.card → (Fin d → ℝ) ↦ path i) =
      (fun path : Fin 1 → (Fin d → ℝ) ↦ path 0) ∘ FiniteOrderedTimes.restrictPath e := rfl
  rw [hfun', Kernel.map_comp_right _ (FiniteOrderedTimes.measurable_restrictPath e)
    (measurable_pi_apply 0), S.conservative.finiteTimeKernel_map_restrictPath S.semigroup,
    finiteTimeKernel_one_map_eval]
  have htime : ((finiteSetTimes I).restrict e) 0 = t := by
    change ((I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm z) : I) : NNReal) = t
    rw [OrderIso.apply_symm_apply]
  rw [htime]

theorem law_integral_eval (S : Data d m) (t : NNReal) (x : Fin d → ℝ)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    (∫ w, f (w t) ∂S.law x) = ∫ y, f y ∂S.semigroup t x := by
  rw [← law_map_eval S t, Kernel.map_apply _ (show Measurable (fun w : ContinuousPath (Fin d → ℝ) => w t) from
      ContinuousPath.measurable_coordinateProcess t)]
  exact (integral_map (show AEMeasurable (fun w : ContinuousPath (Fin d → ℝ) => w t) (S.law x)
    from (ContinuousPath.measurable_coordinateProcess t).aemeasurable)
      hf.aestronglyMeasurable).symm

theorem law_condExp_shift (S : Data d m) (x : Fin d → ℝ) (t : NNReal)
    (f : ContinuousPath (Fin d → ℝ) → ℝ) (hf : StronglyMeasurable f)
    (C : ℝ) (hC : ∀ w, ‖f w‖ ≤ C) :
    (S.law x)[fun w => f (ContinuousPath.shift t w)|ContinuousPath.canonicalFiltration t]
      =ᵐ[S.law x] fun w => ∫ z, f z ∂S.law (w t) := by
  let := S.markov
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
  · exact S.feller.realization_restrict_map_shift S.semigroup S.conservative
      (ContinuousMap.const NNReal (0 : Fin d → ℝ)) S.law
      (fun I => Kernel.ext (fun x => S.marginals I x)) x t
  · exact hf
  · exact hC

theorem realFk_measurable (S : Data d m) {q : (Fin d → ℝ) → ℝ} (hq : Measurable q)
    (t : NNReal) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (realFk S q t f) := by
  let := S.markov

  have hpath : StronglyMeasurable (fun omega : ContinuousPath (Fin d → ℝ) ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) :=
    (((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := (Fin d → ℝ)) t))).stronglyMeasurable
  exact hpath.integral_kernel.measurable

theorem realFk_measurable_joint (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    Measurable fun p : NNReal × (Fin d → ℝ) => realFk S q p.1 f p.2 := by
  let := S.markov

  let Q : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)) := S.law
  let Q' : Kernel (NNReal × (Fin d → ℝ)) (ContinuousPath (Fin d → ℝ)) :=
    Kernel.comap Q Prod.snd measurable_snd
  have hA : Measurable fun p : (NNReal × (Fin d → ℝ)) × ContinuousPath (Fin d → ℝ) ↦
      feynmanKacAdditiveFunctional q p.1.1 p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : (NNReal × (Fin d → ℝ)) × ContinuousPath (Fin d → ℝ) ↦
      p.2 p.1.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hint : StronglyMeasurable fun p : (NNReal × (Fin d → ℝ)) × ContinuousPath (Fin d → ℝ) ↦
      Real.exp (-feynmanKacAdditiveFunctional q p.1.1 p.2) * f (p.2 p.1.1) :=
    ((hA.neg.exp).mul (hf.comp heval)).stronglyMeasurable
  have hInt := hint.integral_kernel_prod_right' (κ := Q')
  simpa only [Q', Kernel.comap_apply, realFk] using hInt.measurable

theorem realFk_nonneg (S : Data d m) {q : (Fin d → ℝ) → ℝ} {t : NNReal}
    {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : Fin d → ℝ) :
    0 ≤ realFk S q t f x := by
  exact integral_nonneg fun w => mul_nonneg (Real.exp_pos _).le (hf0 _)

theorem realFk_norm_le (S : Data d m) {q : (Fin d → ℝ) → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hfC : ∀ y, |f y| ≤ C)
    (x : Fin d → ℝ) : |realFk S q t f x| ≤ C := by
  let := S.markov
  change ‖∫ w, Real.exp (-feynmanKacAdditiveFunctional q t w) * f (w t) ∂S.law x‖ ≤ C
  calc
    _ ≤ ∫ _, C ∂S.law x := by
      apply norm_integral_le_of_norm_le (integrable_const C)
      exact ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.2
          (neg_nonpos.2 (feynmanKacAdditiveFunctional_nonneg hq0 t w))) (abs_nonneg _)).trans
          (by simpa only [one_mul] using hfC (w t))
    _ = C := by simp only [integral_const, probReal_univ, one_smul]

theorem realFk_le (S : Data d m) {q : (Fin d → ℝ) → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ y, 0 ≤ f y) {C : ℝ}
    (hfC : ∀ y, f y ≤ C) {t : NNReal} (x : Fin d → ℝ) : realFk S q t f x ≤ C :=
  (le_abs_self _).trans (realFk_norm_le S hq0 t
    (fun y => by rw [abs_of_nonneg (hf0 y)]; exact hfC y) x)

theorem realFk_integrable (S : Data d m) {q : (Fin d → ℝ) → ℝ} (hq : Measurable q)
    (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) (x : Fin d → ℝ) :
    Integrable (fun w => Real.exp (-feynmanKacAdditiveFunctional q t w) * f (w t))
      (S.law x) := by
  let := S.markov

  exact Integrable.of_bound
    (((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := (Fin d → ℝ)) t))
      ).stronglyMeasurable).aestronglyMeasurable) C (Eventually.of_forall fun omega ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * |f (omega t)| ≤
            1 * |f (omega t)| := mul_le_mul_of_nonneg_right
              ((Real.exp_le_one_iff).mpr
                (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)
        _ ≤ C := by simpa only [one_mul] using hfC _)

theorem realFk_duhamel (S : Data d m)
    {q : (Fin d → ℝ) → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : Fin d → ℝ) :
    (∫ y, f y ∂S.semigroup t x) - realFk S q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y * realFk S q (t - Real.toNNReal s) f y
        ∂S.semigroup (Real.toNNReal s) x := by
  let := S.markov

  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let mu : Measure (ContinuousPath (Fin d → ℝ)) := S.law x
  let H : ℝ × ContinuousPath (Fin d → ℝ) → ℝ := fun p ↦
    q (p.2 (Real.toNNReal p.1)) *
      Real.exp (-(feynmanKacAdditiveFunctional q t p.2 -
        feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) * f (p.2 t)
  have hevalJoint : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAs : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAt : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) ↦
      feynmanKacAdditiveFunctional q t p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.comp measurable_snd
  have hH : StronglyMeasurable H := by
    exact (((hq.comp hevalJoint).mul ((hAt.sub hAs).neg.exp)).mul
      ((hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := (Fin d → ℝ)) t)).comp
        measurable_snd)).stronglyMeasurable
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hHbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ))
      (omega : ContinuousPath (Fin d → ℝ)) : ‖H (s, omega)‖ ≤ C * D := by
    have hsNN : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hAdiff : 0 ≤ feynmanKacAdditiveFunctional q t omega -
        feynmanKacAdditiveFunctional q (Real.toNNReal s) omega :=
      sub_nonneg.mpr (feynmanKacAdditiveFunctional_mono hq hq0 hqC hsNN omega)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 _),
      abs_of_pos (Real.exp_pos _)]
    calc
      q (omega (Real.toNNReal s)) * Real.exp (-_) * |f (omega t)| ≤
          C * 1 * D := by
        exact mul_le_mul
          (mul_le_mul (hqC _)
            ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr hAdiff))
            (Real.exp_pos _).le hC) (hfD _) (abs_nonneg _) (mul_nonneg hC zero_le_one)
      _ = C * D := by ring
  have hProdInt : Integrable (Function.uncurry fun (s : ℝ)
      (omega : ContinuousPath (Fin d → ℝ)) ↦ H (s, omega))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod mu) := by
    refine Integrable.of_bound hH.aestronglyMeasurable (C * D) ?_
    change ∀ᵐ p : ℝ × ContinuousPath (Fin d → ℝ)
      ∂((volume.restrict (Ioc (0 : ℝ) t)).prod mu), ‖H p‖ ≤ C * D
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hH.norm.measurable measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ hHbound s ⟨hs.1.le, hs.2⟩ omega
  have hInner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      ∫ omega, H (s, omega) ∂mu =
        ∫ y, q y * realFk S q
          (t - Real.toNNReal s) f y ∂(S.semigroup (Real.toNNReal s) x) := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let W : ContinuousPath (Fin d → ℝ) → ℝ := fun omega ↦ q (omega u)
    let F : ContinuousPath (Fin d → ℝ) → ℝ := fun eta ↦
      Real.exp (-feynmanKacAdditiveFunctional q r eta) * f (eta r)
    have hu : u ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := (Fin d → ℝ)) u] W :=
      (hq.comp (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := (Fin d → ℝ)) u)).stronglyMeasurable
    have hF : StronglyMeasurable F := by
      exact (((stronglyMeasurable_feynmanKacAdditiveFunctional hq r).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := (Fin d → ℝ)) r))).stronglyMeasurable
    have hFbound : ∀ eta : ContinuousPath (Fin d → ℝ), ‖F eta‖ ≤ D := by
      intro eta
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 r eta))) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hfD _)
    have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift u omega)) mu :=
      Integrable.of_bound
        (((hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := (Fin d → ℝ)) u))
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ hFbound _)
    have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift u omega)) mu := by
      refine Integrable.of_bound
        ((((hW.mono ((ContinuousPath.canonicalFiltration (alpha := (Fin d → ℝ))).le u)).mul
          (hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := (Fin d → ℝ)) u)))
          ).aestronglyMeasurable) (C * D) ?_
      exact Eventually.of_forall fun omega ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
        exact mul_le_mul (hqC _) (hFbound _) (norm_nonneg _) hC
    have hcond := law_condExp_shift S x u F hF D hFbound
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
    have hfactor : (fun omega ↦ H (s, omega)) =
        fun omega ↦ W omega * F (ContinuousPath.shift u omega) := by
      funext omega
      dsimp only [H, W, F, u, r]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hu,
        feynmanKacAdditiveFunctional_sub hq hq0 hqC hu]
      ring
    rw [hfactor]
    calc
      (∫ omega, W omega * F (ContinuousPath.shift u omega) ∂mu) =
          ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift u eta)|
            ContinuousPath.canonicalFiltration (alpha := (Fin d → ℝ)) u] omega ∂mu := by
              rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := (Fin d → ℝ))).le u)]
      _ = ∫ omega, W omega *
            (∫ eta, F eta ∂S.law (omega u)) ∂mu := by
              refine integral_congr_ae (hpull.trans ?_)
              exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
      _ = ∫ omega, q (omega u) * realFk S q r f (omega u) ∂mu := by
            rfl
      _ = ∫ y, q y * realFk S q r f y ∂(S.semigroup u x) := by
            simpa only [mu] using!
              (law_integral_eval S u x
                (hq.mul (realFk_measurable S hq r hf)))
      _ = ∫ y, q y * realFk S q
            (t - Real.toNNReal s) f y ∂(S.semigroup (Real.toNNReal s) x) := by rfl
  have hPath : (∫ omega, f (omega t) ∂mu) -
      realFk S q t f x =
        ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := by
    have hPlain : Integrable (fun omega : ContinuousPath (Fin d → ℝ) ↦ f (omega t)) mu :=
      Integrable.of_bound
        (((hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := (Fin d → ℝ)) t)).stronglyMeasurable
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
            rw [Real.norm_eq_abs]
            exact hfD _)
    have hWeighted : Integrable (fun omega : ContinuousPath (Fin d → ℝ) ↦
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) mu :=
      have hmeasWeighted : StronglyMeasurable fun omega : ContinuousPath (Fin d → ℝ) ↦
          Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) := by
        have hmeas : Measurable fun omega : ContinuousPath (Fin d → ℝ) ↦
            Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) :=
          ((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
            (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := (Fin d → ℝ)) t))
        exact hmeas.stronglyMeasurable
      Integrable.of_bound hmeasWeighted.aestronglyMeasurable D (Eventually.of_forall fun omega ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_right
            ((Real.exp_le_one_iff).mpr
              (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)).trans
            (by simpa only [one_mul] using hfD _))
    change (∫ omega, f (omega t) ∂mu) -
      (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) ∂mu) = _
    rw [← integral_sub hPlain hWeighted]
    refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
    change f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
      ∫ s in (0 : ℝ)..t, H (s, omega)
    have halg : f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
        (1 - Real.exp (-feynmanKacAdditiveFunctional q t omega)) * f (omega t) := by ring
    rw [halg, one_sub_exp_neg_feynmanKacAdditiveFunctional hq hq0 hqC,
      ← intervalIntegral.integral_mul_const]
  have hEval := law_integral_eval S t x hf
  calc
    (∫ y, f y ∂(S.semigroup t x)) - realFk S q t f x =
        (∫ omega, f (omega t) ∂mu) - realFk S q t f x := by
          rw [hEval]
    _ = ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := hPath
    _ =
        ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu := by
          calc
            (∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu) =
                ∫ omega, (∫ s in Ioc (0 : ℝ) t, H (s, omega)) ∂mu := by
                  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
                  exact intervalIntegral.integral_of_le t.coe_nonneg
            _ = ∫ s in Ioc (0 : ℝ) t, ∫ omega, H (s, omega) ∂mu :=
              (integral_integral_swap hProdInt).symm
            _ = ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu :=
              (intervalIntegral.integral_of_le t.coe_nonneg).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ y, q y *
          realFk S q (t - Real.toNNReal s) f y
          ∂(S.semigroup (Real.toNNReal s) x) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            rw [uIcc_of_le t.coe_nonneg] at hs
            exact hInner s hs

end SubdiffusiveProcess.PartProcess
