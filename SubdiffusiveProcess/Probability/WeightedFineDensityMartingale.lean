import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Probability.InfraredWholePrefixIndependence
import SubdiffusiveProcess.Probability.InfraredFineIndependence
import SubdiffusiveProcess.Probability.FineDensityMartingale
import SubdiffusiveProcess.Probability.WeightedFineDensityIntegrable
import SubdiffusiveProcess.Probability.SeparatedFineLayerFactorization
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Martingale.Basic

open Filter MeasureTheory ProbabilityTheory Topology
noncomputable section
namespace SubdiffusiveProcess

theorem infraredWeightedFineDensity_martingale
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (x : SpatialCoordinates d) :
    Martingale
      (fun N (omega : BilateralField d) =>
        Real.exp (H omega x) * fineDensity M N omega x)
      (conditionalFineFiltration H hH.1)
      (chaosSampleLaw M).toMeasure := by
  apply martingale_nat
  · intro N
    let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
      fun omega j => omega (-(Int.ofNat j))
    let Ψ : BilateralField d →
        C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) :=
      fun omega => (H omega, Φ omega)
    let g : C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ :=
      fun p => Real.exp (p.1 x) * Real.exp ((∑ j : Fin (N + 1), p.2 j x) -
        (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    have hA : Measurable (fun p : C(SpatialCoordinates d, ℝ) ×
        ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) => p.1 x) := by fun_prop
    have hB : Measurable (fun p : C(SpatialCoordinates d, ℝ) ×
        ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) =>
        (∑ j : Fin (N + 1), p.2 j x) - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      fun_prop
    have hg : Measurable g := hA.exp.mul hB.exp
    have hΦmeas : Measurable[(conditionalFineFiltration H hH.1) N] Φ := by
      have heq : (MeasurableSpace.comap Φ inferInstance) =
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance := by
        simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
        rfl
      have hle : MeasurableSpace.comap Φ inferInstance ≤ (conditionalFineFiltration H hH.1) N := by
        change MeasurableSpace.comap Φ inferInstance ≤
          MeasurableSpace.comap H inferInstance ⊔
            ⨆ j : Fin (N + 1), MeasurableSpace.comap
              (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance
        rw [heq]
        exact le_sup_right
      exact (comap_measurable Φ).mono hle le_rfl
    have hHmeas : Measurable[(conditionalFineFiltration H hH.1) N] H := by
      have hle : MeasurableSpace.comap H inferInstance ≤ (conditionalFineFiltration H hH.1) N := by
        change MeasurableSpace.comap H inferInstance ≤
          MeasurableSpace.comap H inferInstance ⊔
            ⨆ j : Fin (N + 1), MeasurableSpace.comap
              (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance
        exact le_sup_left
      exact (comap_measurable H).mono hle le_rfl
    have hΨmeas : Measurable[(conditionalFineFiltration H hH.1) N] Ψ := hHmeas.prodMk hΦmeas
    have hsum : ∀ omega : BilateralField d,
        (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x) =
          ∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x := by
      intro omega
      refine Finset.sum_bij (s := Finset.range (N + 1))
        (t := (Finset.univ : Finset (Fin (N + 1))))
        (fun n hn => ⟨n, by simpa using hn⟩) ?_ ?_ ?_ ?_
      · intro n hn; simp
      · intro a ha b hb hab; exact congrArg Fin.val hab
      · intro b hb; exact ⟨b.1, by simpa using b.2, by simp⟩
      · intro n hn; rfl
    have hfun : (fun omega : BilateralField d => Real.exp (H omega x) * fineDensity M N omega x) =
        (fun omega => g (Ψ omega)) := by
      funext omega
      simp only [g, Ψ, Φ, fineDensity, finePotential]
      rw [hsum omega]
    change StronglyMeasurable[(conditionalFineFiltration H hH.1) N]
      (fun omega : BilateralField d => Real.exp (H omega x) * fineDensity M N omega x)
    rw [hfun]
    exact hg.stronglyMeasurable.comp_measurable hΨmeas
  · intro N
    exact weightedFineDensity_integrable hd M H N x hH
  · intro N
    let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
      fun omega j => omega (-(Int.ofNat j))
    let Ψ : BilateralField d →
        C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) :=
      fun omega => (H omega, Φ omega)
    let freshFactor : BilateralField d → ℝ := fun omega =>
      Real.exp (omega (-(Int.ofNat (N + 1))) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    let g : C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ :=
      fun p => Real.exp (p.1 x) * Real.exp ((∑ j : Fin (N + 1), p.2 j x) -
        (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    have hA : Measurable (fun p : C(SpatialCoordinates d, ℝ) ×
        ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) => p.1 x) := by fun_prop
    have hB : Measurable (fun p : C(SpatialCoordinates d, ℝ) ×
        ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) =>
        (∑ j : Fin (N + 1), p.2 j x) - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      fun_prop
    have hg : Measurable g := hA.exp.mul hB.exp
    have hΦmeas : Measurable[(conditionalFineFiltration H hH.1) N] Φ := by
      have heq : (MeasurableSpace.comap Φ inferInstance) =
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance := by
        simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
        rfl
      have hle : MeasurableSpace.comap Φ inferInstance ≤ (conditionalFineFiltration H hH.1) N := by
        change MeasurableSpace.comap Φ inferInstance ≤
          MeasurableSpace.comap H inferInstance ⊔
            ⨆ j : Fin (N + 1), MeasurableSpace.comap
              (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance
        rw [heq]
        exact le_sup_right
      exact (comap_measurable Φ).mono hle le_rfl
    have hHmeas : Measurable[(conditionalFineFiltration H hH.1) N] H := by
      have hle : MeasurableSpace.comap H inferInstance ≤ (conditionalFineFiltration H hH.1) N := by
        change MeasurableSpace.comap H inferInstance ≤
          MeasurableSpace.comap H inferInstance ⊔
            ⨆ j : Fin (N + 1), MeasurableSpace.comap
              (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance
        exact le_sup_left
      exact (comap_measurable H).mono hle le_rfl
    have hΨmeas : Measurable[(conditionalFineFiltration H hH.1) N] Ψ := hHmeas.prodMk hΦmeas
    have hsum : ∀ omega : BilateralField d,
        (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x) =
          ∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x := by
      intro omega
      refine Finset.sum_bij (s := Finset.range (N + 1))
        (t := (Finset.univ : Finset (Fin (N + 1))))
        (fun n hn => ⟨n, by simpa using hn⟩) ?_ ?_ ?_ ?_
      · intro n hn; simp
      · intro a ha b hb hab; exact congrArg Fin.val hab
      · intro b hb; exact ⟨b.1, by simpa using b.2, by simp⟩
      · intro n hn; rfl
    have hXNmeas : StronglyMeasurable[(conditionalFineFiltration H hH.1) N]
        (fun omega : BilateralField d => Real.exp (H omega x) * fineDensity M N omega x) := by
      have hfun : (fun omega : BilateralField d => Real.exp (H omega x) * fineDensity M N omega x) =
          (fun omega => g (Ψ omega)) := by
        funext omega
        simp only [g, Ψ, Φ, fineDensity, finePotential]
        rw [hsum omega]
      rw [hfun]
      exact hg.stronglyMeasurable.comp_measurable hΨmeas
    have hsucc : ∀ omega : BilateralField d, fineDensity M (N + 1) omega x =
        fineDensity M N omega x * freshFactor omega := by
      intro omega
      have hbase : fineDensity M (N + 1) omega x = fineDensity M N omega x *
          Real.exp (omega (-(Int.ofNat (N + 1))) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
        simp only [fineDensity, finePotential, Nat.cast_add, Nat.cast_one,
          Nat.cast_ofNat, Nat.add_assoc]
        rw [Finset.sum_range_succ]
        rw [← Real.exp_add]
        ring
      simpa [freshFactor] using hbase
    have hXsucc_eq :
        (fun omega : BilateralField d => Real.exp (H omega x) * fineDensity M (N + 1) omega x) =
        (fun omega => (Real.exp (H omega x) * fineDensity M N omega x) * freshFactor omega) := by
      funext omega
      rw [hsucc omega]
      ring
    have hprodInt : Integrable
        (fun omega => (Real.exp (H omega x) * fineDensity M N omega x) * freshFactor omega)
        (chaosSampleLaw M).toMeasure := by
      rw [← hXsucc_eq]
      exact weightedFineDensity_integrable hd M H (N + 1) x hH
    have hfreshMean : ∫ omega, freshFactor omega ∂(chaosSampleLaw M).toMeasure = 1 := by
      have h1 := chaosSampleLaw_prod_exp_sub_tauSq_eq_one_of_fineLayer_separated M 1 (N + 1)
        (fun _ : Fin 1 => x) (fun i k hik => absurd (Subsingleton.elim i k) hik)
      simpa [freshFactor, Fin.prod_univ_one] using h1
    have hfreshInt : Integrable freshFactor (chaosSampleLaw M).toMeasure :=
      integrable_of_integral_eq_one hfreshMean
    have hpull := condExp_mul_of_stronglyMeasurable_left hXNmeas hprodInt hfreshInt
    have hindep0 := infraredCharacterization_indepFun_negCoord_finePrefix M H N hH
    let φ : C(SpatialCoordinates d, ℝ) → ℝ :=
      fun f => Real.exp (f x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    have hφmeas : Measurable φ := by fun_prop
    have hcomp := hindep0.comp hφmeas measurable_id
    have hleft : (φ ∘ (fun omega : BilateralField d => omega (-(Int.ofNat (N + 1)))))
        =ᵐ[(chaosSampleLaw M).toMeasure] freshFactor := by
      filter_upwards [] with omega
      rfl
    have hright : (id ∘ Ψ) =ᵐ[(chaosSampleLaw M).toMeasure] Ψ := by
      filter_upwards [] with omega
      rfl
    have hindepFreshPsi : IndepFun freshFactor Ψ (chaosSampleLaw M).toMeasure :=
      hcomp.congr hleft hright
    have hIndepPair : Indep (MeasurableSpace.comap freshFactor inferInstance)
        (MeasurableSpace.comap Ψ inferInstance) (chaosSampleLaw M).toMeasure := by
      rw [← IndepFun_iff_Indep]
      exact hindepFreshPsi
    have hfreshMeas : Measurable freshFactor := by fun_prop
    have hHsub : MeasurableSpace.comap H inferInstance ≤ MeasurableSpace.comap Ψ inferInstance :=
      (measurable_fst.comp (comap_measurable Ψ)).comap_le
    have hEvalSub : ∀ j : Fin (N + 1),
        MeasurableSpace.comap (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance ≤
          MeasurableSpace.comap Ψ inferInstance := by
      intro j
      exact (((measurable_pi_apply j).comp (measurable_snd)).comp (comap_measurable Ψ)).comap_le
    have hFNsub : (conditionalFineFiltration H hH.1) N ≤ MeasurableSpace.comap Ψ inferInstance := by
      change (MeasurableSpace.comap H inferInstance ⊔
        ⨆ j : Fin (N + 1), MeasurableSpace.comap
          (fun omega : BilateralField d => omega (-(Int.ofNat j))) inferInstance) ≤ _
      exact sup_le hHsub (iSup_le hEvalSub)
    have hΨsub : MeasurableSpace.comap Ψ inferInstance ≤ (conditionalFineFiltration H hH.1) N :=
      hΨmeas.comap_le
    have hFNeqΨ : (conditionalFineFiltration H hH.1) N = MeasurableSpace.comap Ψ inferInstance :=
      le_antisymm hFNsub hΨsub
    have hIndepFinal : Indep (MeasurableSpace.comap freshFactor inferInstance)
        ((conditionalFineFiltration H hH.1) N) (chaosSampleLaw M).toMeasure := by
      rw [← hFNeqΨ] at hIndepPair
      exact hIndepPair
    have hcondFresh : (chaosSampleLaw M).toMeasure[freshFactor |
        (conditionalFineFiltration H hH.1) N] =ᵐ[(chaosSampleLaw M).toMeasure]
        fun _ => ∫ y, freshFactor y ∂(chaosSampleLaw M).toMeasure :=
      condExp_indep_eq hfreshMeas.comap_le ((conditionalFineFiltration H hH.1).le N)
        (comap_measurable freshFactor).stronglyMeasurable hIndepFinal
    have hcondFresh' : (chaosSampleLaw M).toMeasure[freshFactor |
        (conditionalFineFiltration H hH.1) N] =ᵐ[(chaosSampleLaw M).toMeasure] fun _ => (1 : ℝ) := by
      filter_upwards [hcondFresh] with omega homega
      rw [homega, hfreshMean]
    rw [hXsucc_eq]
    filter_upwards [hpull, hcondFresh'] with omega h1 h2
    rw [Pi.mul_apply, h2, mul_one] at h1
    exact h1.symm

end SubdiffusiveProcess
