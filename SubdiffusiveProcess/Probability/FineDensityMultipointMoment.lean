module

public import SubdiffusiveProcess.Probability.FineLayerMultipointMoment
public import SubdiffusiveProcess.Probability.FineDensityMartingale

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem fineDensity_multiPoint_prod_exp_moment_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p)
    (N : ℕ) (x : Fin p → SpatialCoordinates d)
    (hpdelta : (p : ℝ) * M.delta ≤ 1) :
    Integrable
      (fun omega : BilateralField d => ∏ k : Fin p, fineDensity M N omega (x k))
      (chaosSampleLaw M).toMeasure ∧
    (∫ omega : BilateralField d, ∏ k : Fin p, fineDensity M N omega (x k)
        ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((N + 1 : ℝ) *
        ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
          (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  classical
  let μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let ν := chaosRootFieldLaw M
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let S : Finset ℕ := Finset.range (N + 1)
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  let B : ℝ := Real.exp ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2)
  let c : ℝ := Real.exp (-((p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
  let H : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    Real.exp (∑ k : Fin p, f (x k))
  let Hscaled : ℤ → C(SpatialCoordinates d, ℝ) → ℝ := fun j f =>
    Real.exp (∑ k : Fin p, f ((3 : ℝ) ^ (-j) • x k))
  have hHmeas : Measurable H := by
    dsimp [H]
    apply Measurable.exp
    apply Finset.measurable_sum
    intro k hk
    exact (continuous_eval_const (x k)).measurable
  have hlayer (j : ℤ) :
      Integrable (fun f : C(SpatialCoordinates d, ℝ) =>
        Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
          _root_.SubdiffusiveProcess.Model.tauSq M.P)) (laws j) ∧
      (∫ f : C(SpatialCoordinates d, ℝ),
        Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
          _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂laws j) ≤ c * B := by
    have hzero := fineLayer_multiPoint_exp_moment_le p hp M
      (fun k : Fin p => (3 : ℝ) ^ (-j) • x k) hpdelta
    have hscaled_meas : Measurable (Hscaled j) := by
      dsimp [Hscaled]
      apply Measurable.exp
      apply Finset.measurable_sum
      intro k hk
      exact (continuous_eval_const ((3 : ℝ) ^ (-j) • x k)).measurable
    have hscaledν : Integrable (Hscaled j) ν.toMeasure := by
      change Integrable (Hscaled j) (Measure.map forget μ)
      apply (integrable_map_measure hscaled_meas.aestronglyMeasurable
        forget.continuous.measurable.aemeasurable).mpr
      simpa only [Function.comp_apply, Hscaled, ν, chaosRootFieldLaw, μ, forget,
        ContinuousMap.coe_mk, ContinuousMap.compRightContinuousMap_apply,
        ContinuousMap.comp_apply] using! hzero.1
    have hHlayer : Integrable H (laws j) := by
      change Integrable H (Measure.map (layerScaling d j) ν.toMeasure)
      exact (integrable_map_measure hHmeas.aestronglyMeasurable
        (layerScaling d j).continuous.measurable.aemeasurable).mpr
        (by
          simpa only [Function.comp_apply, H, Hscaled, layerScaling,
            ContinuousMap.compRightContinuousMap_apply,
            ContinuousMap.comp_apply] using! hscaledν)
    have hcenter : Integrable (fun f : C(SpatialCoordinates d, ℝ) =>
        c * H f) (laws j) := hHlayer.const_mul c
    have hrewrite (f : C(SpatialCoordinates d, ℝ)) :
        Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
          _root_.SubdiffusiveProcess.Model.tauSq M.P) = c * H f := by
      dsimp [c, H]
      rw [Real.exp_sub]
      rw [Real.exp_neg]
      field_simp
    constructor
    · simpa only [hrewrite] using! hcenter
    · have hi : (∫ f : C(SpatialCoordinates d, ℝ), H f ∂laws j) ≤ B := by
        change (∫ f : C(SpatialCoordinates d, ℝ), H f
          ∂Measure.map (layerScaling d j) ν.toMeasure) ≤ B
        rw [integral_map (layerScaling d j).continuous.measurable.aemeasurable]
        · change (∫ f : C(SpatialCoordinates d, ℝ), Hscaled j f
            ∂Measure.map forget μ) ≤ B
          rw [integral_map forget.continuous.measurable.aemeasurable]
          · simpa only [H, Hscaled, layerScaling,
              ContinuousMap.compRightContinuousMap_apply,
              ContinuousMap.comp_apply, forget, μ] using! hzero.2
          · exact hscaled_meas.aestronglyMeasurable
        · exact hHmeas.aestronglyMeasurable
      rw [show (∫ f : C(SpatialCoordinates d, ℝ),
          Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
            _root_.SubdiffusiveProcess.Model.tauSq M.P) ∂laws j) =
        ∫ f, c * H f ∂laws j by
            apply integral_congr_ae
            filter_upwards with f
            exact hrewrite f]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
  have hindep : iIndepFun
      (fun i : S => fun omega : BilateralField d => omega (-(i : ℤ))) P := by
    have hfull : iIndepFun
        (fun j : ℤ => fun omega : BilateralField d => omega j) P := by
      dsimp only [P, laws]
      exact iIndepFun_infinitePi (fun _ => measurable_id)
    apply hfull.precomp
    intro i₁ i₂ hi
    apply Subtype.ext
    exact_mod_cast (neg_injective hi)
  let F : S → C(SpatialCoordinates d, ℝ) → ℝ := fun i f =>
    Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
      _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hFmeas (i : S) : Measurable (F i) := by
    dsimp [F]
    apply Measurable.exp
    apply Measurable.sub
    · apply Finset.measurable_sum
      intro k hk
      exact (continuous_eval_const (x k)).measurable
    · exact measurable_const
  have hfactor :
      ∫ omega, ∏ i : S, F i (omega (-(i : ℤ))) ∂P =
        ∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P := by
    refine hindep.integral_fun_prod_comp ?_ (fun i => ?_)
    · intro i
      exact (measurable_pi_apply (-(i : ℤ))).aemeasurable
    · exact (hFmeas i).aestronglyMeasurable
  have hindepF : iIndepFun
      (fun i : S => fun omega : BilateralField d =>
        F i (omega (-(i : ℤ)))) P := by
    exact hindep.comp (fun i => F i) (fun i => hFmeas i)
  have hone (i : S) :
      ∫ omega, F i (omega (-(i : ℤ))) ∂P ≤ c * B := by
    have heval := measurePreserving_eval_infinitePi laws (-(i : ℤ))
    change ∫ omega, F i (omega (-(i : ℤ)))
      ∂Measure.infinitePi laws ≤ c * B
    calc
      ∫ omega, F i (omega (-(i : ℤ))) ∂Measure.infinitePi laws =
          ∫ f, F i f ∂Measure.map (fun omega : BilateralField d =>
            omega (-(i : ℤ))) (Measure.infinitePi laws) := by
              rw [integral_map heval.measurable.aemeasurable]
              exact (hFmeas i).aestronglyMeasurable
      _ = ∫ f, F i f ∂laws (-(i : ℤ)) := by rw [heval.map_eq]
      _ ≤ c * B := (hlayer (-(i : ℤ))).2
  have hprod_bound :
      (∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P) ≤ (c * B) ^ (N + 1) := by
    calc
      (∏ i : S, ∫ omega, F i (omega (-(i : ℤ))) ∂P) ≤
          ∏ _i : S, c * B := by
        gcongr with i
        exact hone i
      _ = (c * B) ^ (N + 1) := by simp [S]
  have hexp (omega : BilateralField d) :
      (∏ k : Fin p, fineDensity M N omega (x k)) =
        ∏ i : S, F i (omega (-(i : ℤ))) := by
    simp only [fineDensity, finePotential, F, S]
    calc
      (∏ k : Fin p, Real.exp
          (∑ j ∈ Finset.range (N + 1), (omega (-Int.ofNat j)) (x k) -
            (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
          Real.exp (∑ k : Fin p,
            (∑ j ∈ Finset.range (N + 1), (omega (-Int.ofNat j)) (x k) -
              (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) :=
        (Real.exp_sum _ _).symm
      _ = Real.exp (∑ j ∈ Finset.range (N + 1),
            (∑ k : Fin p, (omega (-Int.ofNat j)) (x k) -
              (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.sum_comm]
        simp only [Finset.card_fin, Finset.card_range, Finset.sum_const]
        ring
      _ = ∏ j ∈ Finset.range (N + 1),
          Real.exp (∑ k : Fin p, (omega (-Int.ofNat j)) (x k) -
            (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
        Real.exp_sum _ _
      _ = ∏ i : S, F i (omega (-(i : ℤ))) := by
        exact (Finset.prod_coe_sort (Finset.range (N + 1))
          (fun j => Real.exp (∑ k : Fin p, (omega (-Int.ofNat j)) (x k) -
            (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))).symm
  constructor
  · rw [show (chaosSampleLaw M).toMeasure = P by rfl]
    rw [show (fun omega : BilateralField d => ∏ k : Fin p,
      fineDensity M N omega (x k)) = fun omega => ∏ i : S,
        F i (omega (-(i : ℤ))) by funext omega; exact hexp omega]
    have hAi (i : S) :
        Integrable (fun omega : BilateralField d => F i (omega (-(i : ℤ)))) P := by
      exact (measurePreserving_eval_infinitePi laws (-(i : ℤ))).integrable_comp_of_integrable
        (hlayer (-(i : ℤ))).1
    have hprod_int : ∀ s : Finset S,
        Integrable (s.prod (fun i => fun omega : BilateralField d =>
          F i (omega (-(i : ℤ))))) P := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa only [Finset.prod_empty] using! (integrable_const (μ := P) (1 : ℝ))
      | @insert i s hi ih =>
          simp only [Finset.prod_insert hi]
          have hind := hindepF.indepFun_finsetProd_of_notMem
            (fun j => (hFmeas j).comp (measurable_pi_apply (-(j : ℤ)))) hi
          have hm := hind.symm.integrable_mul (hAi i) ih
          simpa [Finset.prod_apply, Pi.mul_apply, mul_comm] using! hm
    have heq :
        (Finset.univ.prod (fun i : S => fun omega : BilateralField d =>
          F i (omega (-(i : ℤ))))) =
          (fun omega : BilateralField d =>
            ∏ i : S, F i (omega (-(i : ℤ)))) := by
      funext omega
      simp [Finset.prod_apply]
    rw [← heq]
    exact hprod_int Finset.univ
  · rw [show (chaosSampleLaw M).toMeasure = P by rfl]
    rw [show (fun omega : BilateralField d => ∏ k : Fin p,
      fineDensity M N omega (x k)) = fun omega => ∏ i : S,
        F i (omega (-(i : ℤ))) by funext omega; exact hexp omega]
    rw [hfactor]
    calc
      _ ≤ (c * B) ^ (N + 1) := hprod_bound
      _ = Real.exp ((N + 1 : ℝ) *
          ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
            (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
        dsimp [c, B]
        rw [← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        norm_num [Nat.cast_add, Nat.cast_one]
        ring; simp

end SubdiffusiveProcess
