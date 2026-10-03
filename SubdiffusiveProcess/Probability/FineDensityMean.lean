module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.FineDensity
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw

@[expose] public section

open MeasureTheory ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess

theorem integral_fineDensity_chaosSampleLaw
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (x : SpatialCoordinates d) :
    ∫ omega, fineDensity M N omega x ∂(chaosSampleLaw M).toMeasure = 1 := by
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hsource (y : SpatialCoordinates d) :
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          Real.exp (g y - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂μ = 1 := by
    let I : ℝ := ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Real.exp (g 0) ∂μ
    have hIpos : 0 < I := by
      exact integral_exp_pos M.G4.exponential_integrable
    have hexpTau : Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = I := by
      simpa [I, μ, SubdiffusiveProcess.Frozen.Assumptions.tauSq] using Real.exp_log hIpos
    have hEq :
        ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g y) ∂μ = I := by
      let F0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (g 0)
      have hF0 : Measurable F0 :=
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0).exp
      calc
        ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g y) ∂μ =
            ∫ g, F0 (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g) ∂μ := by
          apply integral_congr_ae
          filter_upwards with g
          simp [F0]
        _ = ∫ g, F0 g
            ∂Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y) μ := by
          exact (integral_map
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate y).aemeasurable
            hF0.aestronglyMeasurable).symm
        _ = I := by rw [M.G1.stationary y]
    calc
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          Real.exp (g y - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂μ =
          Real.exp (-SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
            ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g y) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with g
        rw [Real.exp_sub, Real.exp_neg]
        ring
      _ = Real.exp (-SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * I := by rw [hEq]
      _ = 1 := by
        rw [Real.exp_neg, hexpTau]
        field_simp
  let ν := chaosRootFieldLaw M
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  have hlayer (j : ℤ) :
      ∫ f : C(SpatialCoordinates d, ℝ),
          Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
            ∂(scaledLayerLaw d ν j).toMeasure = 1 := by
    dsimp only [scaledLayerLaw]
    change ∫ f : C(SpatialCoordinates d, ℝ),
        Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂
          Measure.map (layerScaling d j) ν.toMeasure = 1
    rw [integral_map
      (layerScaling d j).continuous.measurable.aemeasurable]
    · change ∫ f : C(SpatialCoordinates d, ℝ),
        Real.exp ((layerScaling d j f) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
          ∂(ν.toMeasure) = 1
      dsimp only [ν, chaosRootFieldLaw]
      change ∫ f : C(SpatialCoordinates d, ℝ),
          Real.exp ((layerScaling d j f) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
            ∂Measure.map forget μ = 1
      rw [integral_map forget.continuous.measurable.aemeasurable]
      · change ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          Real.exp ((layerScaling d j (forget g)) x -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂μ = 1
        simpa only [layerScaling, ContinuousMap.compRightContinuousMap_apply,
          ContinuousMap.comp_apply, forget] using!
          hsource ((3 : ℝ) ^ (-j) • x)
      · exact (Real.continuous_exp.comp
          ((continuous_eval_const x).comp (layerScaling d j).continuous |>.sub
            continuous_const)).measurable.aestronglyMeasurable
    · exact (Real.continuous_exp.comp
        ((continuous_eval_const x).sub continuous_const)).measurable.aestronglyMeasurable
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  let S : Finset ℕ := Finset.range (N + 1)
  have hcoord : iIndepFun
      (fun i : S => fun omega : BilateralField d => omega (-(i : ℤ))) P := by
    have hfull : iIndepFun
        (fun j : ℤ => fun omega : BilateralField d => omega j) P := by
      dsimp only [P, laws]
      exact iIndepFun_infinitePi (fun _ => measurable_id)
    apply hfull.precomp
    intro i₁ i₂ hi
    apply Subtype.ext
    exact_mod_cast (neg_injective hi)
  let G : C(SpatialCoordinates d, ℝ) → ℝ :=
    fun f => Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hG : Measurable G := (Real.continuous_exp.comp
    ((continuous_eval_const x).sub continuous_const)).measurable
  have hindep : iIndepFun
      (fun i : S => fun omega : BilateralField d =>
        Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) P := by
    simpa only [Function.comp_apply, G] using! hcoord.comp (fun _ => G) (fun _ => hG)
  have hfactor :
      ∫ omega, ∏ i : S,
          Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂P =
        ∏ i : S, ∫ omega,
          Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂P := by
    refine hindep.integral_fun_prod_comp ?_ (fun _ => aestronglyMeasurable_id)
    · intro i
      exact (hG.comp (measurable_pi_apply (-(i : ℤ)))).aemeasurable
  have hone (i : S) :
      ∫ omega, Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂P = 1 := by
    have heval := measurePreserving_eval_infinitePi laws (-(i : ℤ))
    calc
      ∫ omega, Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂P =
          ∫ f, Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
            ∂laws (-(i : ℤ)) := by
        rw [← heval.map_eq, integral_map heval.measurable.aemeasurable]
        exact (Real.continuous_exp.comp
          ((continuous_eval_const x).sub continuous_const)).measurable.aestronglyMeasurable
      _ = 1 := hlayer (-(i : ℤ))
  have hexp (omega : BilateralField d) :
      fineDensity M N omega x =
        ∏ i : S, Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    simp only [fineDensity, finePotential, S]
    calc
      Real.exp
          (∑ j ∈ Finset.range (N + 1), (omega (-Int.ofNat j)) x -
            (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
          Real.exp (∑ j ∈ Finset.range (N + 1),
            ((omega (-Int.ofNat j)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        norm_num
      _ = ∏ j ∈ Finset.range (N + 1),
          Real.exp ((omega (-Int.ofNat j)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
        Real.exp_sum _ _
      _ = ∏ i : (Finset.range (N + 1)),
          Real.exp (omega (-(i : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
        exact (Finset.prod_coe_sort (Finset.range (N + 1))
          (fun j => Real.exp (omega (-(j : ℤ)) x -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))).symm
  change ∫ omega, fineDensity M N omega x ∂P = 1
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hfactor]
  simp only [hone, Finset.prod_const_one]

end SubdiffusiveProcess
