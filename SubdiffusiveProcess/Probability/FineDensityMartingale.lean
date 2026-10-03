module

public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.FineDensity
public import SubdiffusiveProcess.Probability.FineDensityMean
public import SubdiffusiveProcess.Probability.LayerConditionalResponse
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

private theorem fineFiltration_eq_fin
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    ∀ N : ℕ,
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
        (inferInstance : MeasurableSpace
          ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))).comap
          (fun (omega : BilateralField d) (j : Fin (N + 1)) ↦
            omega (-(Int.ofNat j))) := by
  intro N
  unfold conditionalFineFiltration
  change (MeasurableSpace.comap (fun _ : BilateralField d =>
    (0 : C(SpatialCoordinates d, ℝ))) inferInstance ⊔
      ⨆ j : Fin (N + 1), MeasurableSpace.comap
        (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) = _
  rw [MeasurableSpace.comap_const, bot_sup_eq]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]
  rfl

private theorem fineDensity_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    ∀ N : ℕ, Measurable (fun omega : BilateralField d => fineDensity M N omega x) := by
  intro N
  unfold fineDensity finePotential
  apply Measurable.exp
  apply Measurable.sub
  · exact Finset.measurable_fun_sum _ (fun j hj =>
      (continuous_eval_const x).measurable.comp (measurable_pi_apply _))
  · exact measurable_const

private theorem fineDensity_integrable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    ∀ N : ℕ, Integrable (fun omega : BilateralField d => fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure := by
  intro N
  apply integrable_of_integral_eq_one
  exact integral_fineDensity_chaosSampleLaw M N x

private theorem fineDensity_adapted
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    Adapted (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (fun N omega ↦ fineDensity M N omega x) := by
  intro N
  let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
    fun omega j ↦ omega (-(Int.ofNat j))
  let g : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ :=
    fun y ↦ Real.exp (∑ j : Fin (N + 1), y j x -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hg : Measurable g := by
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j hj =>
        (continuous_eval_const x).measurable.comp (measurable_pi_apply j))
    · exact measurable_const
  have hfg : (fun omega : BilateralField d ↦ fineDensity M N omega x) = g ∘ Φ := by
    funext omega
    simp only [Function.comp_apply, g, Φ, fineDensity, finePotential]
    congr 1
    have hs : (∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (omega (-(Int.ofNat j))) x) (N + 1))
    exact congrArg (fun z : ℝ => z -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) hs.symm
  have hfil : (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
      (inferInstance : MeasurableSpace ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))).comap Φ := by
    change (MeasurableSpace.comap (fun _ : BilateralField d =>
      (0 : C(SpatialCoordinates d, ℝ))) inferInstance ⊔
        ⨆ j : Fin (N + 1), MeasurableSpace.comap
          (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) = _
    rw [MeasurableSpace.comap_const, bot_sup_eq]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    rfl
  change Measurable[ (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N]
    (fun omega : BilateralField d ↦ fineDensity M N omega x)
  rw [hfil]
  rw [hfg]
  exact hg.comp (comap_measurable Φ)

private theorem fineFiltration_eq_restrict
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    ∀ N : ℕ,
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
        let J : Finset ℤ := (Finset.range (N + 1)).image
          (fun j : ℕ => -(Int.ofNat j))
        (inferInstance : MeasurableSpace ((j : J) → C(SpatialCoordinates d, ℝ))).comap
          (fun (omega : BilateralField d) (j : J) ↦ omega j) := by
  intro N
  let J : Finset ℤ := (Finset.range (N + 1)).image
    (fun j : ℕ => -(Int.ofNat j))
  change (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
    (inferInstance : MeasurableSpace ((j : J) → C(SpatialCoordinates d, ℝ))).comap
      (fun (omega : BilateralField d) (j : J) ↦ omega j)
  change (MeasurableSpace.comap (fun _ : BilateralField d =>
    (0 : C(SpatialCoordinates d, ℝ))) inferInstance ⊔
      ⨆ j : Fin (N + 1), MeasurableSpace.comap
        (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) = _
  rw [MeasurableSpace.comap_const, bot_sup_eq]
  change (⨆ j : Fin (N + 1), MeasurableSpace.comap
      (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) =
    (inferInstance : MeasurableSpace ((j : J) → C(SpatialCoordinates d, ℝ))).comap
      (J : Set ℤ).domRestrict
  have hrestrict : (inferInstance : MeasurableSpace ((j : J) → C(SpatialCoordinates d, ℝ))).comap
      (J : Set ℤ).domRestrict =
      ⨆ i ∈ (J : Set ℤ), (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
        (fun omega : BilateralField d => omega i) := by
    simpa using! comap_restrict_eq_iSup (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (J : Set ℤ)
  rw [hrestrict]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    refine le_iSup_of_le (-(Int.ofNat (j : ℕ))) ?_
    refine le_iSup_of_le ?_ ?_
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr j.isLt, rfl⟩)
    · rfl
  · refine iSup_le fun k => iSup_le fun hk => ?_
    obtain ⟨j, hj, hkj⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hk)
    refine le_iSup_of_le ⟨j, Finset.mem_range.mp hj⟩ ?_
    rw [← hkj]

private theorem fineDensity_succ
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    fineDensity M (N + 1) omega x = fineDensity M N omega x *
      Real.exp (omega (-(Int.ofNat (N + 1))) x -
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  simp only [fineDensity, finePotential, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, Nat.add_assoc]
  rw [Finset.sum_range_succ]
  rw [← Real.exp_add]
  ring

private theorem fineLayerMean
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ)
    (x : SpatialCoordinates d) :
    ∫ f : C(SpatialCoordinates d, ℝ),
      Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure = 1 := by
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
  dsimp only [scaledLayerLaw]
  change ∫ f : C(SpatialCoordinates d, ℝ),
      Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂
        Measure.map (layerScaling d j) (chaosRootFieldLaw M).toMeasure = 1
  rw [integral_map
    (layerScaling d j).continuous.measurable.aemeasurable]
  · change ∫ f : C(SpatialCoordinates d, ℝ),
      Real.exp ((layerScaling d j f) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(chaosRootFieldLaw M).toMeasure = 1
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

theorem conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    (∀ N : ℕ,
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const) N =
        (inferInstance : MeasurableSpace
          ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))).comap
          (fun (omega : BilateralField d) (j : Fin (N + 1)) ↦
            omega (-(Int.ofNat j)))) ∧
    Martingale (fun N omega ↦ fineDensity M N omega x)
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (chaosSampleLaw M).toMeasure := by
  constructor
  · exact fineFiltration_eq_fin M x
  · apply martingale_nat
    · exact (fineDensity_adapted M x).stronglyAdapted
    · exact fineDensity_integrable M x
    · intro N
      let J : Finset ℤ := (Finset.range (N + 1)).image
        (fun j : ℕ => -(Int.ofNat j))
      let K := {j : ℤ // ¬ j ∈ J}
      let e : BilateralField d ≃ᵐ
          ((j : J) → C(SpatialCoordinates d, ℝ)) ×
            ((j : K) → C(SpatialCoordinates d, ℝ)) :=
        MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (fun j : ℤ => j ∈ J)
      let ν := chaosRootFieldLaw M
      let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
        fun j => (scaledLayerLaw d ν j).toMeasure
      have hmeasure : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by
        rfl
      have hk0 : -(Int.ofNat (N + 1)) ∉ J := by
        intro h
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
        have heq0 : Int.ofNat j = Int.ofNat (N + 1) := neg_injective heq
        have heq' : j = N + 1 := by
          exact Int.ofNat_inj.mp heq0
        have hj' : j < N + 1 := Finset.mem_range.mp hj
        omega
      let k0 : K := ⟨-(Int.ofNat (N + 1)), hk0⟩
      have hk0' : -1 + -(N : ℤ) ∉ J := by
        simpa [Int.natCast_add] using hk0
      have hjmem (j : Fin (N + 1)) : (-(Int.ofNat j) : ℤ) ∈ J := by
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr j.isLt, rfl⟩
      have hret (omega : BilateralField d)
          (y : (j : K) → C(SpatialCoordinates d, ℝ)) (j : Fin (N + 1)) :
          (e.symm ((fun k : J => omega k), y)) (-(Int.ofNat j)) =
            omega (-(Int.ofNat j)) := by
        change (Equiv.piEquivPiSubtypeProd (fun j : ℤ => j ∈ J)
          (fun _ : ℤ => C(SpatialCoordinates d, ℝ))).symm
            ((fun k : J => omega k), y) (-(Int.ofNat j)) = omega (-(Int.ofNat j))
        simp only [hjmem j, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
      have hnew (y : (j : K) → C(SpatialCoordinates d, ℝ))
          (omega : BilateralField d) :
          (e.symm ((fun k : J => omega k), y)) (-(Int.ofNat (N + 1))) = y k0 := by
        change (Equiv.piEquivPiSubtypeProd (fun j : ℤ => j ∈ J)
          (fun _ : ℤ => C(SpatialCoordinates d, ℝ))).symm
            ((fun k : J => omega k), y) (-(Int.ofNat (N + 1))) = y k0
        simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
        split <;> simp_all [k0, hk0']
      have hbase (omega : BilateralField d)
          (y : (j : K) → C(SpatialCoordinates d, ℝ)) :
          fineDensity M N (e.symm ((fun k : J => omega k), y)) x =
            fineDensity M N omega x := by
        unfold fineDensity finePotential
        apply congrArg Real.exp
        apply congrArg (fun z : ℝ => z -
          (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x)
          (hret omega y ⟨j, Finset.mem_range.mp hj⟩)
      have hfactor (omega : BilateralField d) :
          ∫ y, fineDensity M (N + 1)
              (e.symm ((fun k : J => omega k), y)) x
              ∂Measure.infinitePi (fun j : K => laws j.1) =
            fineDensity M N omega x := by
        apply (integral_congr_ae (ae_of_all _ (fun y => by
          rw [fineDensity_succ, hbase, hnew]))).trans
        rw [integral_const_mul]
        · rw [show (∫ y, Real.exp (y k0 x -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
              ∂Measure.infinitePi (fun j : K => laws j.1)) = 1 by
            have heval := measurePreserving_eval_infinitePi
              (fun j : K => laws j.1) k0
            calc
              ∫ y, Real.exp (y k0 x -
                  SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
                  ∂Measure.infinitePi (fun j : K => laws j.1) =
                ∫ z, Real.exp (z x -
                  SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂laws k0.1 := by
                    rw [← heval.map_eq,
                      integral_map heval.measurable.aemeasurable]
                    exact (Real.continuous_exp.comp
                      ((continuous_eval_const x).sub continuous_const)).measurable.aestronglyMeasurable
              _ = 1 := fineLayerMean M k0.1 x]
          simp
      have hcond := condExp_layer_restrict_integral laws J
        (fineDensity_integrable M x (N + 1))
      rw [hmeasure, fineFiltration_eq_restrict M x N]
      exact (hcond.trans (Filter.Eventually.of_forall hfactor)).symm


end SubdiffusiveProcess
