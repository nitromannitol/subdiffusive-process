import SubdiffusiveProcess.Section10.PhysicalTightnessActualModulus
import SubdiffusiveProcess.Section10.PhysicalTightnessHeadBallCover
import SubdiffusiveProcess.Section10.PhysicalTightnessHeadChaining

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

local instance cemeteryHeadVecStandardBorel (d : ℕ) : StandardBorelSpace (Cemetery (Vec d)) := by
  letI : BorelSpace (Cemetery (Vec d)) := SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  infer_instance


/-- Two uniform local exit times and measurable exceptional sets give an
annealed modulus majorant, at a deterministic positive time. -/
theorem head_annealed_modulus_of_containment {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (law : Kernel (Omega × Vec d) (Path d)) [IsMarkovKernel law]
    (c rho : Omega → Vec d → ℝ)
    (hdata : ∀ᵐ omega ∂mu, LocalDiffusionData (c omega) (rho omega)
      (Kernel.comap law (fun x => (omega, x)) measurable_prodMk_left))
    (hcons : ∀ᵐ omega ∂mu, ∀ x : Vec d, ∀ᵐ w ∂law (omega, x), w.lifetime = ⊤)
    (B : Set (Vec d)) (R T r a : ℝ) (hBR : B ⊆ Metric.ball (0 : Vec d) R)
    (hT : 0 < T) (hr : 0 < r) (ha : 0 < a)
    (Gouter : Omega → ENNReal) (hGouter : Measurable Gouter)
    (houter : ∀ omega, ∀ x ∈ B,
      law (omega, x) {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤
        ENNReal.ofReal T} ≤ Gouter omega)
    (houterInt : ∫⁻ omega, Gouter omega ∂mu ≤ ENNReal.ofReal (a / 4)) :
    ∃ delta : NNReal, 0 < delta ∧ ∃ G : Omega → ENNReal, Measurable G ∧
      (∀ᵐ omega ∂mu, ∀ x ∈ B,
        (law (omega, x)).map (LifetimePath.continuousPathExtension
          (ContinuousMap.const NNReal (0 : Vec d)))
          (ContinuousPath.modulusSet (Real.toNNReal T) (delta : ENNReal)
            (ENNReal.ofReal r))ᶜ ≤ G omega) ∧
      ∫⁻ omega, G omega ∂mu ≤ ENNReal.ofReal a := by
  classical
  have he : 0 < a / 8 := by positivity
  have hepsilon : 0 < a / 4 := by positivity
  obtain ⟨n0, S0, hS0, hS0mass, hfirst⟩ := measurable_uniform_local_exit
    mu law c rho hdata R r (1 / 8) (a / 8) hr (by norm_num) he
  obtain ⟨q, hchain⟩ := head_modulus_bound_of_two_exit_estimates
    R r T (headTime n0 : ℝ) (a / 4) hr hT (headTime_pos n0) hepsilon
  have hbeta : 0 < (a / 4) / (16 * ((q : ℝ) + 1)) := by positivity
  obtain ⟨n1, S1, hS1, hS1mass, hsecond⟩ := measurable_uniform_local_exit
    mu law c rho hdata R r ((a / 4) / (16 * ((q : ℝ) + 1))) (a / 8) hr hbeta he
  let S : Set Omega := S0 ∪ S1
  have hS : MeasurableSet S := hS0.union hS1
  have hSmass : mu S ≤ ENNReal.ofReal (a / 4) := by
    calc
      mu S ≤ mu S0 + mu S1 := measure_union_le S0 S1
      _ ≤ ENNReal.ofReal (a / 8) + ENNReal.ofReal (a / 8) := add_le_add hS0mass hS1mass
      _ = ENNReal.ofReal (a / 4) := by
        rw [← ENNReal.ofReal_add he.le he.le]
        congr 1
        ring
  let G : Omega → ENNReal := fun omega =>
    S.indicator (fun _ => 1) omega + Gouter omega + ENNReal.ofReal (a / 4)
  have hind : Measurable (S.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hS
  have hG : Measurable G := (hind.add hGouter).add measurable_const
  have hindInt : (∫⁻ omega, S.indicator (fun _ => (1 : ENNReal)) omega ∂mu) = mu S := by
    change (∫⁻ omega, S.indicator (1 : Omega → ENNReal) omega ∂mu) = mu S
    exact lintegral_indicator_one hS
  refine ⟨headTime n1, headTime_pos n1, G, hG, ?_, ?_⟩
  · filter_upwards [hdata, hcons, hfirst, hsecond] with omega homega hcon hfirstExit hsecondExit
    intro x hx
    by_cases hbad : omega ∈ S
    · have hprob : (law (omega, x)).map (LifetimePath.continuousPathExtension
          (ContinuousMap.const NNReal (0 : Vec d)))
          (ContinuousPath.modulusSet (Real.toNNReal T) (headTime n1 : ENNReal)
            (ENNReal.ofReal r))ᶜ ≤ 1 := by
        calc
          _ ≤ ((law (omega, x)).map (LifetimePath.continuousPathExtension
              (ContinuousMap.const NNReal (0 : Vec d)))) univ := measure_mono (subset_univ _)
          _ = 1 := by
            rw [Measure.map_apply (LifetimePath.measurable_continuousPathExtension _)
              MeasurableSet.univ, preimage_univ]
            exact measure_univ
      simp only [G, Set.indicator_of_mem hbad]
      exact hprob.trans ((le_add_of_nonneg_right (zero_le _)).trans
        (le_add_of_nonneg_right (zero_le _)))
    · have hnot0 : omega ∉ S0 := fun hmem => hbad (Or.inl hmem)
      have hnot1 : omega ∉ S1 := fun hmem => hbad (Or.inr hmem)
      let law0 : Kernel (Vec d) (Path d) :=
        Kernel.comap law (fun y => (omega, y)) measurable_prodMk_left
      have hfirst0 : ∀ y ∈ Metric.ball (0 : Vec d) R,
          law0 y {w | LifetimePath.exitTime (Metric.ball y (r / 4)) w ≤
            ENNReal.ofReal (headTime n0 : ℝ)} ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
        intro y hy
        simpa only [ENNReal.ofReal_coe_nnreal] using hfirstExit hnot0 y hy
      have hb := hchain (headTime n1) law0 homega.1.1 hcon hfirst0
        (hsecondExit hnot1) x (hBR hx)
      have hbound := hb.trans (add_le_add (houter omega x hx) le_rfl)
      simpa only [G, Set.indicator_of_notMem hbad, zero_add] using hbound
  · change (∫⁻ omega, S.indicator (fun _ => (1 : ENNReal)) omega + Gouter omega +
        ENNReal.ofReal (a / 4) ∂mu) ≤ ENNReal.ofReal a
    rw [lintegral_add_left (hind.add hGouter), lintegral_add_left hind,
      hindInt, lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ ENNReal.ofReal (a / 4) + ENNReal.ofReal (a / 4) + ENNReal.ofReal (a / 4) :=
        add_le_add (add_le_add hSmass houterInt) le_rfl
      _ ≤ ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_add hepsilon.le hepsilon.le,
          ← ENNReal.ofReal_add (by positivity) hepsilon.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For each finite collection of actual cutoff laws, one positive modulus
time controls every starting point in the compact set. -/
theorem actual_finite_head_modulus_of_local_analytic_bank {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (LN : ℕ → Kernel (BilateralField d × Vec d) (Path d))
    (hLN : ∀ N, IsMarkovKernel (LN N))
    (hdata : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusionData (cutoffCoefficient M Hf xi N) (cutoffSpeedDensity M Hf xi N)
        (Kernel.comap (LN N) (fun x => (xi, x)) measurable_prodMk_left))
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega))
 :
    ∀ B : Set (Vec d), IsCompact B → ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∀ k : ℕ,
      ∃ delta : ENNReal, 0 < delta ∧ ∀ N : ℕ, N < k →
        ∃ G : BilateralField d → ENNReal, Measurable G ∧
          (∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B,
            (LN N (xi, x)).map (LifetimePath.continuousPathExtension
              (ContinuousMap.const NNReal (0 : Vec d)))
              (ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹))ᶜ ≤ G xi) ∧
          ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a := by
  classical
  intro B hB n a ha k
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hr : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr hn
  have he : 0 < a / 4 := by positivity
  have hrho : ENNReal.ofReal ((n + 1 : ℝ)⁻¹) = (n + 1 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hn,
      ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have htime : (n : NNReal) ≤ Real.toNNReal (n + 1) := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hn.le, NNReal.coe_natCast]
    linarith
  obtain ⟨R, -, hBR, houter⟩ := actual_annealed_containment_of_local_analytic_bank
    M H hH Hf hHf LN hLN hdata C hC hlocal B hB.isBounded (n + 1) (a / 4) hn he
  have hcons := actual_nonexplosion_of_local_analytic_bank
    M H hH Hf hHf LN hLN hdata C hC hlocal
  have hone : ∀ N : ℕ, ∃ delta : NNReal, 0 < delta ∧
      ∃ G : BilateralField d → ENNReal, Measurable G ∧
        (∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ x ∈ B,
          (LN N (xi, x)).map (LifetimePath.continuousPathExtension
            (ContinuousMap.const NNReal (0 : Vec d)))
            (ContinuousPath.modulusSet (Real.toNNReal (n + 1)) (delta : ENNReal)
              (ENNReal.ofReal ((n + 1 : ℝ)⁻¹)))ᶜ ≤ G xi) ∧
        ∫⁻ xi, G xi ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal a := by
    intro N
    letI := hLN N
    obtain ⟨Gouter, hGouter, hGouterBound, hGouterInt⟩ := houter N
    exact head_annealed_modulus_of_containment (chaosSampleLaw M).toMeasure
      (LN N) (fun xi => cutoffCoefficient M Hf xi N)
      (fun xi => cutoffSpeedDensity M Hf xi N)
      (hdata.mono fun _ hxi => hxi N) (hcons.mono fun _ hxi => hxi N)
      B R (n + 1) ((n + 1 : ℝ)⁻¹) a hBR hn hr ha
      Gouter hGouter hGouterBound hGouterInt
  choose deltaN hdeltaN GN hGN hGNbound hGNint using hone
  let delta : ENNReal := (Finset.range k).inf (fun N => (deltaN N : ENNReal))
  have hdelta : 0 < delta := (Finset.lt_inf_iff (by simp : (0 : ENNReal) < ⊤)).mpr
    (fun N _ => ENNReal.coe_pos.mpr (hdeltaN N))
  refine ⟨delta, hdelta, ?_⟩
  intro N hNk
  have hdeltaLe : delta ≤ (deltaN N : ENNReal) := Finset.inf_le (Finset.mem_range.mpr hNk)
  have hsubset : ContinuousPath.modulusSet (alpha := Vec d) (Real.toNNReal (n + 1))
      (deltaN N : ENNReal) (ENNReal.ofReal ((n + 1 : ℝ)⁻¹)) ⊆
        ContinuousPath.modulusSet (n : NNReal) delta ((n + 1 : ENNReal)⁻¹) := by
    rw [hrho]
    intro p hp s t hs ht hst
    exact hp s t (hs.trans htime) (ht.trans htime) (hst.trans hdeltaLe)
  refine ⟨GN N, hGN N, ?_, hGNint N⟩
  filter_upwards [hGNbound N] with xi hxi
  intro x hx
  exact (measure_mono (compl_subset_compl.mpr hsubset)).trans (hxi x hx)

end SubdiffusiveProcess.Section10.PhysicalTightness
