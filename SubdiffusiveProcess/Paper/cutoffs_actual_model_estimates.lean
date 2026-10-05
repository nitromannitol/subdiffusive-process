module

public import SubdiffusiveProcess.Paper.cutoffs_actual_model_collar
public import SubdiffusiveProcess.Paper.in_cutoffs_actual_model_output
public import SubdiffusiveProcess.Cutoffs.MinimumEnvelope
public import SubdiffusiveProcess.Paper.model_cube_coarse_bank
public import SubdiffusiveProcess.Paper.model_grid_constant_bank
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.Paper.inputs_extension_witness

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Cutoffs
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Upgrade the cutoff majorant's moments without upgrading the B1 record's
source and cell banks. The pre-model threshold is independent of Cext. -/
theorem cutoffs_actual_model_estimates
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (_htlow : (d : ℝ) - 1 < t) (_htupper : t < (d : ℝ))
    (_hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (Cgrad : ℝ) (hCgrad : 0 < Cgrad) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (Cext : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
        (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
        (thetaH1 : ∀ j, T j →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
        (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : ∀ j, T j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (Index : Type) [Countable Index]
        (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
        (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
        (coercivityKey extensionKey lambdaKey : J → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey :
          ∀ j, (D j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
        (gridKey : Grid → Index)
        (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
        (_hrepresented :
          _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
            S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t {1} E
            Index resp respLim constants G coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        in_cutoffs_actual_model_output d M H Ω P cutoff env J j0 z rad hrad
          S T theta thetaH1 alpha eta t Cgrad 1 orders G := by
  classical
  let q : ℝ := 1 + ∑ p ∈ orders, p
  have hsum0 : 0 ≤ ∑ p ∈ orders, p := Finset.sum_nonneg (fun p hp => (horders p hp).le)
  have hq1 : 1 ≤ q := by dsimp [q]; linarith only [hsum0]
  have hqord : ∀ p ∈ orders, p ≤ q := by
    intro p hp
    have := Finset.single_le_sum (f := fun p : ℝ => p) (fun p hp => (horders p hp).le) hp
    dsimp [q]; linarith only [this]
  have hbetaI : beta ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hbeta, hbetaalpha.trans halpha⟩
  obtain ⟨_, _, _, Sob, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := inputs_simultaneous d hd
  let X : in_extension d hd E := Classical.choice (inputs_extension_witness d hd E)
  obtain ⟨_, δr, _, hδr, hresponse⟩ := inputs_responses_witness d hd q hq1
  obtain ⟨δc, hδc, hcube⟩ := model_cube_coarse_bank d hd E beta q hbetaI hq1
  obtain ⟨δg, hδg, hgridbank⟩ := model_grid_constant_bank d hd E X Sob eta q beta heta hq1 hbetaI
  obtain ⟨δe, A, hδe, hA, hext⟩ := aux_lem_cutoffs_damped_extrema d hd z0 R hR eta heta q hq1
  refine ⟨min (min δr δc) (min δg δe), lt_min (lt_min hδr hδc) (lt_min hδg hδe), ?_⟩
  intro M H hM Cext Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1
    usrc srcRep ucell Index _ resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
    Grid _ origin gridRoot gridKey hz0 hrad0 hrepresented
  have hMr := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hMc := hM.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hMg := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMe := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrep := hrepresented
  obtain ⟨_, _, _, hCext, _, hcut, hIR, henv, hlaw, hseq, hsub, hcenter, hscale, hcomplete,
    _, hgridroot, _, _, _, _, _, _, _, _, _, hcm, _, hnonneg, _, hpin, _, _, hJ, _, _⟩ := hrep
  obtain ⟨_, hGm, hG0, _, hbdd⟩ := hseq
  obtain ⟨Rm, _, _⟩ := hresponse M hMr
  obtain ⟨Cb, hCb, hLamMeas, _, hLamPos, hLamBank, _⟩ :=
    hcube M Rm H hIR hMc J z rad hrad hscale
  let g0 : Grid := Classical.choose (hgridroot j0)
  have hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0 := Classical.choose_spec (hgridroot j0)
  obtain ⟨Zg, Cg, Ggrid, hCg, hZgMeas, hZg0, hZgBank, _, hGridM, hGrid0, hGridSpec⟩ :=
    hgridbank M Rm H hIR hMg Unit (fun _ => z j0) (fun _ => rad j0) (fun _ => hrad j0)
      (fun _ => origin g0)
  have hmp : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure :=
    fun n => ⟨henv n, hlaw n⟩
  let G1 : Set Ω := G ∩ ⋂ n : ℕ, env n ⁻¹' Ggrid
  have hG1m : MeasurableSet G1 := hGm.inter (MeasurableSet.iInter fun n => hGridM.preimage (henv n))
  have hG1sub : G1 ⊆ G := inter_subset_left
  have hG1zero : P G1ᶜ = 0 := by
    have hGridAE : ∀ n, ∀ᵐ (om : Ω) ∂P, env n om ∈ Ggrid := by
      intro n
      have hg : ∀ᵐ b ∂(chaosSampleLaw M).toMeasure, b ∈ Ggrid := ae_iff.2 hGrid0
      exact (hmp n).quasiMeasurePreserving.ae hg
    have hGood : ∀ᵐ (om : Ω) ∂P, om ∈ G1 := by
      filter_upwards [ae_iff.2 hG0, ae_all_iff.2 hGridAE] with om hom hgridom
      exact ⟨hom, mem_iInter.2 hgridom⟩
    exact ae_iff.1 hGood
  let bank : Option J → ℕ → Ω → ℝ := fun i n om => match i with
    | none => minimumEnvelope (constants (gridKey g0) n om) (Zg () (cutoff n) (env n om))
    | some j => E.Lam (z j) (rad j) (hrad j)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hrad j))
        (z j) (rad j) ((beta - 1 / 2) / 4) 2
  have hbankMeas : ∀ i n, Measurable (bank i n) := by
    intro i n
    cases i with
    | none => exact measurable_minimumEnvelope (hcm _ n) ((hZgMeas () (cutoff n)).comp (henv n))
    | some j => exact (hLamMeas j (cutoff n)).comp (henv n)
  have hbankMom : ∀ i : Option J, ∀ p ∈ orders, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      MemLp (bank i n) (ENNReal.ofReal p) P ∧
        eLpNorm (bank i n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
    intro i p hp
    cases i with
    | none =>
      refine ⟨Cg (), hCg (), fun n => ?_⟩
      have hZ := hZgBank () (cutoff n) p (horders p hp) (hqord p hp)
      have hZm := hZ.1.comp_measurePreserving (hmp n)
      refine ⟨memLp_minimumEnvelope (hcm _ n) ((hZgMeas () (cutoff n)).comp (henv n))
        (fun om => hZg0 () (cutoff n) (env n om)) hZm, ?_⟩
      erw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
        (measurable_minimumEnvelope (hcm _ n)
          ((hZgMeas () (cutoff n)).comp (henv n))).aestronglyMeasurable]
      have hraw := eLpNorm_minimumEnvelope_le (μ := P) (p := ENNReal.ofReal p)
        (a := fun om => constants (gridKey g0) n om)
        (fun om => hZg0 () (cutoff n) (env n om))
      erw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hZm.aestronglyMeasurable] at hraw
      exact hraw.trans
         ((le_of_eq (eLpNorm_comp_measurePreserving hZ.1.aestronglyMeasurable (hmp n))).trans hZ.2)
    | some j =>
      refine ⟨Cb j, hCb j, fun n => ?_⟩
      have hL := (hLamBank j (cutoff n) p (horders p hp) (hqord p hp)).1
      exact ⟨hL.1.comp_measurePreserving (hmp n),
        (le_of_eq (eLpNorm_comp_measurePreserving hL.1.aestronglyMeasurable (hmp n))).trans hL.2⟩
  have hbankBdd : ∀ i : Option J, ∀ om ∈ G1, ∃ B : ℝ, ∀ n : ℕ, |bank i n om| ≤ B := by
    intro i om hom
    cases i with
    | none =>
      obtain ⟨B, hB⟩ := hbdd (gridKey g0) om hom.1
      refine ⟨max B 0, fun n => ?_⟩
      rw [abs_of_nonneg (minimumEnvelope_nonneg _ _ (hZg0 () (cutoff n) (env n om)))]
      exact (minimumEnvelope_le_left _ _).trans (max_le_max ((le_abs_self _).trans (hB n)) le_rfl)
    | some j =>
      obtain ⟨B, hB⟩ := hbdd (extensionKey j) om hom.1
      refine ⟨B, fun n => ?_⟩
      change |E.Lam _ _ _ _ _ _ _ _| ≤ B
      rw [← (hpin j n om hom.1).1]
      exact hB n
  let κ : ℤ := Classical.choose (hscale j0)
  have hκ : rad j0 = (3 : ℝ) ^ κ := Classical.choose_spec (hscale j0)
  choose jc hjc using fun (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) =>
    aux_cutoffs_odd_cell_catalogue_of_geometry j0 z rad hrad (z j0) (rad j0) (hrad j0) rfl rfl
      hcenter hscale hcomplete Jr k
  let F : Finset (Option J) := insert none ((Finset.range κ.toNat).biUnion fun Jr =>
    Finset.univ.image fun k : OddGridIndex d (triadicHalf Jr) => some (jc Jr k))
  obtain ⟨mlow, mhigh, hae, hXmem, hXbd⟩ := hext M H hIR hMe
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨KN, Ggood, hmG, hGG1, hGnull, hKNmeas, hKN1, hKNmom, hKNbdd, hdom, hX⟩ :=
    aux_cutoffs_common_majorant_core P (chaosSampleLaw M).toMeasure cutoff hcut env henv hlaw
      bank G1 hG1zero hbankMeas orders hbankMom hbankBdd F _ hae _ q hq1 hqord A
      (Real.exp (-(eta * Real.log 3 / 2))) hA (Real.exp_pos _).le
      ((Real.exp_lt_exp.2 (by have := mul_pos heta hlog3; linarith)).trans_eq Real.exp_zero)
      hXmem hXbd
  have hGG : Ggood ⊆ G := hGG1.trans hG1sub
  obtain ⟨Csum, hCsum0, hCsum⟩ := aux_cutoffs_uniform_collar_sum d hd (z j0) (rad j0) (hrad j0) eta
    (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2)
    (by have := Real.rpow_nonneg (hrad j0).le eta; positivity)
  let c : ℝ := max 1 Csum
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  unfold in_cutoffs_actual_model_output
  intro Q S0 aN rawAN
  refine ⟨fun n om => c * KN n om, Ggood, hmG, hGG, hGnull,
    fun n => measurable_const.mul (hKNmeas n), fun n om => (hKN1 n om).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (zero_le_one.trans (hKN1 n om))), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨Cp, hCp, hCpN⟩ := hKNmom p hp
    refine ⟨c * Cp, mul_nonneg hc0 hCp, fun n => ⟨(hCpN n).1.const_mul c, ?_⟩⟩
    have he := eLpNorm_const_smul c (KN n) (ENNReal.ofReal p) P
    calc eLpNorm (fun om => c * KN n om) (ENNReal.ofReal p) P
        = ‖c‖ₑ * eLpNorm (KN n) (ENNReal.ofReal p) P := he
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal Cp := by
        rw [Real.enorm_of_nonneg hc0]
        exact mul_le_mul_of_nonneg_left (hCpN n).2 zero_le
      _ = ENNReal.ofReal (c * Cp) := (ENNReal.ofReal_mul hc0).symm
  · intro om hom
    obtain ⟨B, hB⟩ := hKNbdd om hom
    refine ⟨c * B, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact mul_le_mul_of_nonneg_left (hB ⟨n, rfl⟩) hc0
  · intro om hom
    have homG : om ∈ G := hGG hom
    refine ⟨aux_lem_cutoffs_rep_plateau d hd M H Cext beta alpha eta t {1} Ω P cutoff env
      J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented om homG, ?_⟩
    have hGridKN : ∀ n (kp : ℕ) (j : J), kp ≤ cutoff n →
        rad j = (3 : ℝ) ^ (-(kp : ℤ)) →
        (∃ idx : Fin d → ℤ, z j =
          (fun i => origin g0 i + (3 : ℝ) ^ (-(kp : ℤ)) * (idx i : ℝ))) →
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z (gridRoot g0)) (rad (gridRoot g0)) (hrad (gridRoot g0)) :
            Set (SpatialCoordinates d)) →
        constants (extensionKey j) n om ≤ KN n om * (rad j) ^ (-eta) := by
      intro n kp j hk hrj hzj hsubj
      have hpw : 0 < (rad j) ^ (-eta) := Real.rpow_pos_of_pos (hrad j) _
      have hOld := hJ g0 n kp j om homG hk hrj hzj hsubj
      have hOld' : constants (extensionKey j) n om ≤
          constants (gridKey g0) n om * (rad j) ^ (-eta) :=
        (le_add_of_nonneg_right (hnonneg (lambdaKey j) om homG n)).trans hOld
      obtain ⟨idx, hidx⟩ := hzj
      have hsub0 : (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) := by
        simpa only [hg0.1] using hsubj
      have hidx' : (fun i => origin g0 i + rad j * (idx i : ℝ)) = z j := by
        rw [hrj]
        exact hidx.symm
      have hphys : env n om ∈ Ggrid := mem_iInter.1 (hGG1 hom).2 n
      have hNative := hGridSpec (env n om) hphys () (cutoff n) kp idx hk
        (zpow_pos zero_lt_three _) (by simpa only [← hrj, hidx'] using hsub0)
      have hNat : constants (extensionKey j) n om + constants (lambdaKey j) n om ≤
          Zg () (cutoff n) (env n om) * (rad j) ^ (-eta) := by
        rw [(hpin j n om homG).1, (hpin j n om homG).2, Real.rpow_neg_one]
        let L : SpatialCoordinates d × {r : ℝ // 0 < r} → ℝ := fun c =>
          E.Lam c.1 c.2.val c.2.property
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) c.1 c.2.property)
              c.1 c.2.val ((beta - 1 / 2) / 4) 2 +
            (E.lam c.1 c.2.val c.2.property
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (cutoff n) c.1 c.2.property)
              c.1 c.2.val ((beta - 1 / 2) / 4) 2)⁻¹
        let native : SpatialCoordinates d × {r : ℝ // 0 < r} :=
          ⟨fun i => origin g0 i + (3 : ℝ) ^ (-(kp : ℤ)) * (idx i : ℝ),
            ⟨(3 : ℝ) ^ (-(kp : ℤ)), zpow_pos zero_lt_three _⟩⟩
        have heq : native = (z j, ⟨rad j, hrad j⟩) :=
          Prod.ext hidx.symm (Subtype.ext hrj.symm)
        change L (z j, ⟨rad j, hrad j⟩) ≤ _
        calc L (z j, ⟨rad j, hrad j⟩) = L native := (congrArg L heq).symm
          _ ≤ Zg () (cutoff n) (env n om) * (rad j) ^ (-eta) :=
            hNative.trans_eq (by rw [hrj])
      have hNat' : constants (extensionKey j) n om ≤
          Zg () (cutoff n) (env n om) * (rad j) ^ (-eta) :=
        (le_add_of_nonneg_right (hnonneg (lambdaKey j) om homG n)).trans hNat
      have hmin := le_minimumEnvelope ((div_le_iff₀ hpw).2 hOld') ((div_le_iff₀ hpw).2 hNat')
      have hdom0 := hdom om hom n none (Finset.mem_insert_self _ _)
      exact (div_le_iff₀ hpw).1 (hmin.trans hdom0)
    have hCoarseKN : ∀ n (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)), (Jr : ℤ) < κ →
        constants (extensionKey (jc Jr k)) n om ≤ KN n om := by
      intro n Jr k hJr
      have hkey : some (jc Jr k) ∈ F := Finset.mem_insert_of_mem
        (Finset.mem_biUnion.2 ⟨Jr, Finset.mem_range.2 (by omega),
          Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩)
      have h := hdom om hom n (some (jc Jr k)) hkey
      change E.Lam _ _ _ _ _ _ _ _ ≤ KN n om at h
      rw [← (hpin (jc Jr k) n om homG).1] at h
      exact h
    have hExt : ∀ n : ℕ,
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          cutoffCoefficient M H (env n om) (cutoff n) x ≤ mhigh (cutoff n) (env n om)) ∧
        mhigh (cutoff n) (env n om) ≤ KN n om * (3 : ℝ) ^ ((cutoff n : ℝ) * eta) := by
      intro n
      obtain ⟨hgd, hXn⟩ := hX om hom n
      obtain ⟨hlow, hcube⟩ := hgd (cutoff n)
      have hQ : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)) := by
        intro x hx
        have hb := Metric.closure_ball_subset_closedBall hx
        change x ∈ Metric.closedBall z0 (R / 2)
        rw [← hz0, ← hrad0]
        exact hb
      refine ⟨fun x hx => (hcube x (hQ x hx)).2, ?_⟩
      have hpw : 0 < (3 : ℝ) ^ ((cutoff n : ℝ) * eta) := Real.rpow_pos_of_pos zero_lt_three _
      have hX' : ((3 : ℝ) ^ ((cutoff n : ℝ) * eta))⁻¹ *
          (mhigh (cutoff n) (env n om) + (mlow (cutoff n) (env n om))⁻¹) ≤ KN n om := by
        rw [← Real.rpow_neg (by norm_num)]
        exact hXn
      rw [inv_mul_le_iff₀ hpw] at hX'
      have hinv : 0 < (mlow (cutoff n) (env n om))⁻¹ := inv_pos.2 hlow
      rw [mul_comm (KN n om)]
      linarith only [hX', hinv]
    have hCollar := cutoffs_actual_model_collar d hd M H Cext beta alpha eta t {1}
      Ω P cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
      Cgrad hCgrad Csum hCsum κ hκ g0 hg0 jc hjc om homG KN (fun n => hKN1 n om) hGridKN
      hCoarseKN (fun n => mhigh (cutoff n) (env n om)) (fun n => (hExt n).1) (fun n => (hExt n).2)
    intro Jr rho thetaR hsmooth hrange hzero hone hgradR thetaRH1 hH1
    obtain ⟨collarH, collarS, collarC, hcol⟩ := hCollar Jr thetaR hsmooth hrange
      hzero hone hgradR thetaRH1 hH1
    refine ⟨collarH, collarS, collarC, fun n => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcol n
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9.trans ?_⟩
    have hKn0 : 0 ≤ KN n om := zero_le_one.trans (hKN1 n om)
    have hρpos : 0 < rho := div_pos (hrad j0) (by positivity)
    have hρ0 : 0 ≤ rho ^ (-1 - eta) := Real.rpow_nonneg hρpos.le _
    change Csum * KN n om * rho ^ (-1 - eta) ≤ 1 * (c * KN n om) * rho ^ (-1 - eta)
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hKn0) hρ0

end SubdiffusiveProcess.Paper
