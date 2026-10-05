module

public import SubdiffusiveProcess.PartProcess.FeynmanKacRealization

@[expose] public section

/-! Bounded occupation perturbation for a supplied realization. Adapted from
MarkovProcess.Trajectory.FeynmanKacRealResolvent (Scott Armstrong, Apache 2.0). -/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubMarkovKernelSemigroup
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

def realOcc (S : Data d m) (q : (Fin d → ℝ) → ℝ) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * realFk S q (Real.toNNReal t) f x

theorem realOcc_integrable (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : Fin d → ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t) *
      realFk S q (Real.toNNReal t) f x) (Ioi 0) := by

  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((realFk_measurable_joint S hq hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (realFk_norm_le S hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le

theorem realOcc_measurable (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (realOcc S q lam f) := by

  have hjoint : StronglyMeasurable fun p : ℝ × (Fin d → ℝ) ↦
      Real.exp (-lam * p.1) *
        realFk S q (Real.toNNReal p.1) f p.2 :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((realFk_measurable_joint S hq hf).comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
      ) |>.stronglyMeasurable
  exact (hjoint.integral_prod_left' (μ := volume.restrict (Ioi 0))).measurable

theorem ofReal_realFk (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, f y ≤ D) (x : Fin d → ℝ) :
    ENNReal.ofReal (realFk S q t f x) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q t w)) *
        ENNReal.ofReal (f (w t)) ∂S.law x := by
  rw [realFk, ofReal_integral_eq_lintegral_ofReal
    (realFk_integrable S hq hq0 t hf (fun y => by
      rw [abs_of_nonneg (hf0 y)]; exact hfD y) x)
    (ae_of_all _ fun w => mul_nonneg (Real.exp_pos _).le (hf0 _))]
  apply lintegral_congr
  intro w
  exact ENNReal.ofReal_mul (Real.exp_pos _).le

theorem ofReal_realOcc (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {α : ℝ} (hα : 0 < α)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) (x : Fin d → ℝ) :
    ENNReal.ofReal (realOcc S q α f x) = potentialOcc S.law q α f x := by
  rw [realOcc, ofReal_integral_eq_lintegral_ofReal
    (realOcc_integrable S hq hq0 hα hf hfC x)
    (ae_of_all _ fun t => mul_nonneg (Real.exp_pos _).le (realFk_nonneg S hf0 x))]
  apply lintegral_congr
  intro t
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    ofReal_realFk S hq hq0 (Real.toNNReal t) hf hf0
      (fun y => (le_abs_self (f y)).trans (hfC y)) x]

theorem realOcc_eq_toReal (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {α : ℝ} (hα : 0 < α)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) (x : Fin d → ℝ) :
    realOcc S q α f x = (potentialOcc S.law q α f x).toReal := by
  rw [← ofReal_realOcc S hq hq0 hα hf hf0 hfC x]
  exact (ENNReal.toReal_ofReal (show 0 ≤ realOcc S q α f x from
    integral_nonneg fun t => mul_nonneg (Real.exp_pos _).le (realFk_nonneg S hf0 x))).symm

theorem realOcc_zero_eq_kernelResolventReal (S : Data d m)
    (α : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    realOcc S 0 α f = S.semigroup.kernelResolventReal α f := by
  funext x
  unfold realOcc SubMarkovKernelSemigroup.kernelResolventReal
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [realFk, feynmanKacAdditiveFunctional_apply, Pi.zero_apply,
    intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
  rw [law_integral_eval S (Real.toNNReal t) x hf]
  rfl

theorem realOcc_norm_le (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq0 : ∀ y, 0 ≤ q y) {α : ℝ} (hα : 0 < α)
    {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hfC : ∀ y, |f y| ≤ C)
    (x : Fin d → ℝ) : |realOcc S q α f x| ≤ C / α := by
  rw [← Real.norm_eq_abs]
  unfold realOcc
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * C := by
      apply norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hα).mul_const C)
      exact ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (realFk_norm_le S hq0 _ hfC x) (Real.exp_pos _).le
    _ = C / α := by
      rw [integral_mul_const,
        Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hα]
      field_simp

theorem kernelIntegral_mul_realOcc (S : Data d m)
    {q : (Fin d → ℝ) → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C) {lam : ℝ} (hlam : 0 < lam)
    (s : NNReal) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : Fin d → ℝ) :
    kernelIntegral (S.semigroup s) (fun y => q y * realOcc S q lam f y) x =
      ∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        kernelIntegral (S.semigroup s)
          (fun y => q y * realFk S q (Real.toNNReal u) f y) x := by

  let H : (Fin d → ℝ) × ℝ → ℝ := fun p ↦
    q p.1 * Real.exp (-lam * p.2) *
      realFk S q (Real.toNNReal p.2) f p.1
  have hHmeas : StronglyMeasurable H := by
    exact (((hq.comp measurable_fst).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd)).mul
      ((realFk_measurable_joint S hq hf).comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
      )).stronglyMeasurable
  let : IsFiniteKernel (S.semigroup s) := (S.semigroup.isSubMarkovKernel s).isFiniteKernel
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hbase : Integrable (fun p : (Fin d → ℝ) × ℝ ↦
      C * (Real.exp (-lam * p.2) * D))
      ((S.semigroup s x).prod (volume.restrict (Ioi 0))) :=
    (integrable_const (C : ℝ)).mul_prod ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  have hHint : Integrable H ((S.semigroup s x).prod (volume.restrict (Ioi 0))) := by
    apply Integrable.mono' hbase hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 p.1),
        abs_of_pos (Real.exp_pos _)]
      calc
        q p.1 * Real.exp (-lam * p.2) *
            |realFk S q (Real.toNNReal p.2) f p.1| ≤
            C * Real.exp (-lam * p.2) * D := by
          exact mul_le_mul
            (mul_le_mul (hqC p.1) le_rfl (Real.exp_pos _).le hC0)
            (realFk_norm_le S hq0
              (Real.toNNReal p.2) hfD p.1) (abs_nonneg _)
            (mul_nonneg hC0 (Real.exp_pos _).le)
        _ = C * (Real.exp (-lam * p.2) * D) := by ring
  unfold realOcc
  change (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
      realFk S q (Real.toNNReal u) f y) ∂(S.semigroup s x)) = _
  calc
    (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        realFk S q (Real.toNNReal u) f y) ∂(S.semigroup s x)) =
        ∫ y, (∫ u in Ioi (0 : ℝ), H (y, u)) ∂(S.semigroup s x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ by
        dsimp only
        rw [← MeasureTheory.integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _hu
        dsimp only [H]
        ring
    _ = ∫ u in Ioi (0 : ℝ), ∫ y, H (y, u) ∂(S.semigroup s x) :=
      integral_integral_swap hHint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      dsimp only [H]
      calc
        (∫ y, q y * Real.exp (-lam * u) *
            realFk S q (Real.toNNReal u) f y ∂(S.semigroup s x)) =
            ∫ y, Real.exp (-lam * u) *
              (q y * realFk S q (Real.toNNReal u) f y)
              ∂(S.semigroup s x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y ↦ by ring
        _ = Real.exp (-lam * u) *
            ∫ y, q y * realFk S q (Real.toNNReal u) f y
              ∂(S.semigroup s x) := MeasureTheory.integral_const_mul _ _

theorem realOcc_duhamel (S : Data d m)
    {q : (Fin d → ℝ) → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C) {lam : ℝ} (hlam : 0 < lam)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) :
    realOcc S q lam f = S.semigroup.kernelResolventReal lam f -
      S.semigroup.kernelResolventReal lam (fun y => q y * realOcc S q lam f y) := by
  let := S.markov

  funext x
  let H : ℝ × ℝ → ℝ := fun p ↦
    Real.exp (-lam * (p.1 + p.2)) *
      kernelIntegral (S.semigroup (Real.toNNReal p.1))
        (fun y ↦ q y * realFk S q (Real.toNNReal p.2) f y) x
  have hHmeas : Measurable H := by
    have hintegrand : Measurable fun p : (ℝ × ℝ) × (Fin d → ℝ) ↦
        q p.2 * realFk S q (Real.toNNReal p.1.2) f p.2 :=
      (hq.comp measurable_snd).mul
        ((realFk_measurable_joint S hq hf).comp
          (((measurable_real_toNNReal.comp measurable_snd).comp measurable_fst).prodMk
            measurable_snd))
    let K : Kernel (ℝ × ℝ) (Fin d → ℝ) :=
      { toFun := fun p ↦ S.semigroup (Real.toNNReal p.1) x
        measurable' := S.semigroup.measurable_toMeasure.comp
          ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_const) }
    let : IsFiniteKernel K :=
      { exists_univ_le := ⟨1, ENNReal.one_lt_top, fun p ↦ S.semigroup.measure_univ_le_one _ _⟩ }
    have hkernel : Measurable fun p : ℝ × ℝ ↦
        kernelIntegral (S.semigroup (Real.toNNReal p.1))
          (fun y ↦ q y * realFk S q (Real.toNNReal p.2) f y) x := by
      have hlin := hintegrand.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
      simpa only [K, kernelIntegral] using! hlin.measurable
    exact ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.add continuous_snd))).measurable.mul hkernel)
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hinnerBound (s u : ℝ) :
      |kernelIntegral (S.semigroup (Real.toNNReal s))
        (fun y ↦ q y * realFk S q (Real.toNNReal u) f y) x| ≤
          C * D := by
    rw [← Real.norm_eq_abs]
    let : IsFiniteKernel (S.semigroup (Real.toNNReal s)) :=
      (S.semigroup.isSubMarkovKernel (Real.toNNReal s)).isFiniteKernel
    calc
      ‖kernelIntegral (S.semigroup (Real.toNNReal s))
          (fun y ↦ q y * realFk S q (Real.toNNReal u) f y) x‖ ≤
          ∫ _y, C * D ∂(S.semigroup (Real.toNNReal s) x) := by
        apply norm_integral_le_of_norm_le (integrable_const (C * D))
        exact Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 y)]
          exact mul_le_mul (hqC y)
            (realFk_norm_le S hq0 (Real.toNNReal u) hfD y)
            (abs_nonneg _) hC0
      _ ≤ C * D := by
        rw [integral_const, smul_eq_mul]
        apply mul_le_of_le_one_left (mul_nonneg hC0 hD0)
        rw [measureReal_def, ← ENNReal.toReal_one]
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        exact (S.semigroup.isSubMarkovKernel (Real.toNNReal s)).measure_le_one x Set.univ
  have hQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hHquad : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase := (exp_neg_integrableOn_Ioi 0 hlam).mul_prod
      ((exp_neg_integrableOn_Ioi 0 hlam).mul_const (C * D))
    apply Integrable.mono' hbase hHmeas.stronglyMeasurable.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-lam * (p.1 + p.2)) *
            |kernelIntegral (S.semigroup (Real.toNNReal p.1))
              (fun y ↦ q y * realFk S q
                (Real.toNNReal p.2) f y) x| ≤
            Real.exp (-lam * (p.1 + p.2)) * (C * D) :=
          mul_le_mul_of_nonneg_left (hinnerBound p.1 p.2) (Real.exp_pos _).le
        _ = Real.exp (-lam * p.1) * (Real.exp (-lam * p.2) * (C * D)) := by
          rw [show -lam * (p.1 + p.2) = -lam * p.1 + -lam * p.2 by ring,
            Real.exp_add]
          ring
  have hHind : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)
      (volume.prod volume) := by
    apply (integrable_indicator_iff hQ).2
    change Integrable H ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict]
    exact hHquad
  have htriangle := intervalIntegral.integral_timeTriangle_sub hHmeas hHind
  have hFKInt := realOcc_integrable
    S hq hq0 hlam hf hfD x
  have hKernelInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (S.semigroup (Real.toNNReal t)) f x) (Ioi 0) := by
    have hzero := realOcc_integrable
      S measurable_const (fun _ ↦ le_rfl) hlam hf hfD x
    apply hzero.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
    have heval := law_integral_eval S (Real.toNNReal t) x hf
    simp only [realFk, feynmanKacAdditiveFunctional,
      intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
    rw [heval]
    rfl
  have htime (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      Real.exp (-lam * t) *
        (kernelIntegral (S.semigroup (Real.toNNReal t)) f x -
          realFk S q (Real.toNNReal t) f x) =
        ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
    have hfinite := realFk_duhamel
      S hq hq0 hqC hf hfD (Real.toNNReal t) x
    rw [intervalIntegral.integral_of_le (Real.toNNReal t).coe_nonneg,
      integral_Ioc_eq_integral_Ioo, Real.coe_toNNReal t ht.le] at hfinite
    change kernelIntegral (S.semigroup (Real.toNNReal t)) f x -
      realFk S q (Real.toNNReal t) f x = _ at hfinite
    calc
      Real.exp (-lam * t) *
          (kernelIntegral (S.semigroup (Real.toNNReal t)) f x -
            realFk S q (Real.toNNReal t) f x) =
          Real.exp (-lam * t) *
            ∫ s in Ioo (0 : ℝ) t, kernelIntegral (S.semigroup (Real.toNNReal s))
              (fun y ↦ q y * realFk S q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [hfinite]
        congr 2
      _ = ∫ s in Ioo (0 : ℝ) t, Real.exp (-lam * t) *
            kernelIntegral (S.semigroup (Real.toNNReal s))
              (fun y ↦ q y * realFk S q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        have hs0 : 0 ≤ s := hs.1.le
        have hsub0 : 0 ≤ t - s := sub_nonneg.mpr hs.2.le
        have hsub : Real.toNNReal t - Real.toNNReal s = Real.toNNReal (t - s) := by
          apply NNReal.coe_injective
          rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hs.2.le),
            Real.coe_toNNReal t ht.le, Real.coe_toNNReal s hs0,
            Real.coe_toNNReal (t - s) hsub0]
        dsimp only [H]
        rw [hsub]
        congr 2
        ring
  have hcorr : S.semigroup.kernelResolventReal lam
      (fun y ↦ q y * realOcc S q lam f y) x =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [kernelIntegral_mul_realOcc
      S hq hq0 hqC hlam (Real.toNNReal s) hf hfD x]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _hu
    dsimp only [H]
    rw [show -lam * (s + u) = -lam * s + -lam * u by ring, Real.exp_add]
    ring
  have hdiff : S.semigroup.kernelResolventReal lam f x -
      realOcc S q lam f x =
      S.semigroup.kernelResolventReal lam
        (fun y ↦ q y * realOcc S q lam f y) x := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    unfold realOcc
    rw [← integral_sub hKernelInt hFKInt]
    calc
      (∫ t in Ioi (0 : ℝ),
          Real.exp (-lam * t) * kernelIntegral (S.semigroup (Real.toNNReal t)) f x -
            Real.exp (-lam * t) *
              realFk S q (Real.toNNReal t) f x) =
          ∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [← mul_sub]
        exact htime t ht
      _ = ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := htriangle
      _ = _ := hcorr.symm
  simp only [Pi.sub_apply]
  linarith only [hdiff]

end SubdiffusiveProcess.PartProcess
