module

public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
public import SubdiffusiveProcess.Paper.conv_represented_model_operators
public import SubdiffusiveProcess.Paper.conv_represented_estimates_transfer
public import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Existence of the environment-form represented package for expanding catalogues.**  From the
actual finite-cutoff data on the original (chaos-law) space (coercivity constants that are
measurable, nonnegative and tight, and for every `k` a finite-cutoff catalogue of the bounded
family of the first `k + 1` cubes), there is one probability space, one common strictly increasing
refinement `seq`, cutoff-dependent environments `env n` of the chaos law and a limit field of the
chaos law such that the exact package `conv_represented_joint_grids` holds for the cutoffs
`NE ∘ seq`, `NF ∘ seq` with `envE = envF = env`. All catalogues share the same environments,
response spaces, operators and refined cutoffs. The catalogue constants are bounded on the
represented space because they converge there. The deterministic trace identities are
retained unchanged under the environment maps and common subsequence. -/
theorem conv_represented_thm_c1_hyp_grids_extra
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (alpha eta : ℝ) (E : Paper.in_J d) (beta0 t0 : ℝ)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (Dop : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (Dop i)]
    (hDdense : ∀ i, Dense (Dop i))
    (hDadd : ∀ i, ∀ x ∈ Dop i, ∀ y ∈ Dop i, x + y ∈ Dop i)
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (Kc : ℕ → ℕ → BilateralField d → ℝ)
    (hKcmeas : ∀ i N, Measurable (Kc i N))
    (hKcnonneg : ∀ i N β, 0 ≤ Kc i N β)
    (hcoer : ∀ i N, ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N β *
            sobolevCoefficientForm
              (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (htightK : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw model).toMeasure {β | Mb < Kc i (NE n) β} ≤ ENNReal.ofReal rho ∧
      (chaosSampleLaw model).toMeasure {β | Mb < Kc i (NF n) β} ≤ ENNReal.ofReal rho)
    (hdata : ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
      conv_represented_env_interface_grids d hd model H (z ∘ e) (r ∘ e)
        (fun j => hr (e j)) (fun j => S (e j)) NE NF alpha eta E beta0 t0)
    {Y : Type} [Countable Y] (Zx : Y → ℕ → BilateralField d → ℝ)
    (hZxmeas : ∀ y n, Measurable (Zx y (NE n)) ∧ Measurable (Zx y (NF n)))
    (hZxtight : ∀ y, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw model).toMeasure {β | Mb < |Zx y (NE n) β|} ≤ ENNReal.ofReal rho ∧
      (chaosSampleLaw model).toMeasure {β | Mb < |Zx y (NF n) β|} ≤ ENNReal.ofReal rho) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
        (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
        (GNE GNF : (i : ℕ) → ℕ → Ωh →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ωh →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))),
        conv_represented_joint_grids d hd model H Ωh Ph field env env z r hr S
          GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta0 t0 ∧
        ∀ᵐ ω ∂Ph, ∀ y, ∃ ZE ZF : ℝ,
          Tendsto (fun n => Zx y (NE (seq n)) (env n ω)) atTop (𝓝 ZE) ∧
          Tendsto (fun n => Zx y (NF (seq n)) (env n ω)) atTop (𝓝 ZF) := by
  classical
  haveI : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
  choose e he hk using hdata
  choose cR cC root hunit Dcat hDcat fcat trace traceH1 usrcE usrcF srcRepE srcRepF ucellE ucellF
    Cext beta t I cK eK lK sRK sGK sHK cRK cGK cHK origin gridRoot gridKey G0E G0F hAnchor hgrid hrm hrt
    hbuf hcores using hk
  haveI hDcatI : ∀ k j, Countable (Dcat k j) := hDcat
  -- moment banks of the constants on both cutoff sequences, for every catalogue
  have hbankE := fun k => aux_conv_represented_estimates_transfer_core_bank d hd model H NE ℕ
    (root k) (z ∘ e k) (r ∘ e k) (fun j => hr (e k j)) (fun j => S (e k j)) (Dcat k) (fcat k)
    (fun _ => ℕ) (trace k) (traceH1 k) (usrcE k) (srcRepE k) (ucellE k) (Cext k) (beta k) alpha
    eta (t k) {1} (I k) ℕ (fun i n β => cR k i (NE n) β) (fun i n β => cC k i (NE n) β)
    (G0E k) (cK k) (eK k) (lK k) (sRK k) (sGK k) (sHK k) (cRK k) (cGK k) (cHK k) ℕ (origin k)
    (gridRoot k) (gridKey k) (hcores k).1
  have hbankF := fun k => aux_conv_represented_estimates_transfer_core_bank d hd model H NF ℕ
    (root k) (z ∘ e k) (r ∘ e k) (fun j => hr (e k j)) (fun j => S (e k j)) (Dcat k) (fcat k)
    (fun _ => ℕ) (trace k) (traceH1 k) (usrcF k) (srcRepF k) (ucellF k) (Cext k) (beta k) alpha
    eta (t k) {1} (I k) ℕ (fun i n β => cR k i (NF n) β) (fun i n β => cC k i (NF n) β)
    (G0F k) (cK k) (eK k) (lK k) (sRK k) (sGK k) (sHK k) (cRK k) (cGK k) (cHK k) ℕ (origin k)
    (gridRoot k) (gridKey k) (hcores k).2
  -- the extra real coordinates: responses (left) and constants (right) of every catalogue
  let Z0 : ((k : ℕ) × (ℕ ⊕ ℕ)) → ℕ → BilateralField d → ℝ := fun q =>
    Sum.elim (fun i N β => cR q.1 i N β) (fun i N β => cC q.1 i N β) q.2
  let Z : (((k : ℕ) × (ℕ ⊕ ℕ)) ⊕ Y) → ℕ → BilateralField d → ℝ := Sum.elim Z0 Zx
  have hZmeas : ∀ x n, Measurable (Z x (NE n)) ∧ Measurable (Z x (NF n)) := by
    rintro (⟨k, (i | i)⟩ | y) n
    · exact (hrm k i n)
    · exact ⟨(hbankE k).1 i n, (hbankF k).1 i n⟩
    · exact hZxmeas y n
  have hL1tight : ∀ (N : ℕ → ℕ) (k i : ℕ)
      (hm : ∀ n, Measurable (cC k i (N n)))
      (hbank : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
        MemLp (cC k i (N n)) (ENNReal.ofReal 1) P0 ∧
        eLpNorm (cC k i (N n)) (ENNReal.ofReal 1) P0 ≤ ENNReal.ofReal B),
      ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n, P0 {β | Mb < |cC k i (N n) β|} ≤
        ENNReal.ofReal rho := by
    intro N k i hm hbank rho hrho
    obtain ⟨B, hB0, hB⟩ := hbank
    obtain ⟨Mb, hMb⟩ := aux_conv_represented_tight_of_bounded_L1_bounded P0
      (fun n => cC k i (N n)) hm B hB0 (fun n => by
        have := (hB n).2
        rwa [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hB n).1.aestronglyMeasurable] at this) rho hrho
    exact ⟨Mb, hMb⟩
  have hZtight : ∀ x, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < |Z x (NE n) β|} ≤ ENNReal.ofReal rho ∧
      P0 {β | Mb < |Z x (NF n) β|} ≤ ENNReal.ofReal rho := by
    rintro (⟨k, (i | i)⟩ | y) rho hrho
    · exact (hrt k) i rho hrho
    · obtain ⟨Mb1, hMb1⟩ := hL1tight NE k i (fun n => (hbankE k).1 i n)
        ((hbankE k).2 i 1 (by simp)) rho hrho
      obtain ⟨Mb2, hMb2⟩ := hL1tight NF k i (fun n => (hbankF k).1 i n)
        ((hbankF k).2 i 1 (by simp)) rho hrho
      refine ⟨max Mb1 Mb2, fun n => ⟨?_, ?_⟩⟩
      · refine le_trans (measure_mono ?_) (hMb1 n)
        intro β hβ
        have hβ' : max Mb1 Mb2 < |cC k i (NE n) β| := hβ
        exact lt_of_le_of_lt (le_max_left _ _) hβ'
      · refine le_trans (measure_mono ?_) (hMb2 n)
        intro β hβ
        have hβ' : max Mb1 Mb2 < |cC k i (NF n) β| := hβ
        exact lt_of_le_of_lt (le_max_right _ _) hβ'
    · exact hZxtight y rho hrho
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, env, envLim, GE, GF, hmp, hmpLim, hconv⟩ :=
    conv_represented_model_operators d hd hInterp model H hH z r hr S hS Dop hDdense hDadd NE NF
      Kc hKcmeas hKcnonneg hcoer htightK Z hZmeas hZtight
  haveI : IsProbabilityMeasure Ph := hPh
  -- convergence of the responses and constants of each catalogue along the represented sequence
  have hlimZ : ∀ (b : Bool) (k : ℕ) (s : Bool), ∀ᵐ w ∂Ph, ∀ i, ∃ l : ℝ,
      Tendsto (fun n => (if s then cC k i (if b then NE (seq n) else NF (seq n)) (env n w)
        else cR k i (if b then NE (seq n) else NF (seq n)) (env n w))) atTop (𝓝 l) := by
    intro b k s
    filter_upwards [hconv] with w hw i
    cases s
    · obtain ⟨ZE, ZF, h1, h2⟩ := hw.2.1 (Sum.inl ⟨k, Sum.inl i⟩)
      cases b
      · exact ⟨ZF, h2⟩
      · exact ⟨ZE, h1⟩
    · obtain ⟨ZE, ZF, h1, h2⟩ := hw.2.1 (Sum.inl ⟨k, Sum.inr i⟩)
      cases b
      · exact ⟨ZF, h2⟩
      · exact ⟨ZE, h1⟩
  have hcat : ∀ k,
      conv_represented_catalogue_grids d hd model H Ωh Ph env env
        (z ∘ e k) (r ∘ e k) (fun j => hr (e k j)) (fun j => S (e k j))
        (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta0 t0 := by
    intro k
    obtain ⟨respLimE, GEv, hcatE⟩ := conv_represented_estimates_transfer d hd model H NE ℕ (root k)
      (z ∘ e k) (r ∘ e k) (fun j => hr (e k j)) (fun j => S (e k j)) (Dcat k) (fcat k)
      (fun _ => ℕ) (trace k) (traceH1 k) (usrcE k) (srcRepE k) (ucellE k) (Cext k) (beta k) alpha
      eta (t k) {1} (I k) ℕ (fun i n β => cR k i (NE n) β) (fun i n β => cC k i (NE n) β)
      (G0E k) (cK k) (eK k) (lK k) (sRK k) (sGK k) (sHK k) (cRK k) (cGK k) (cHK k) ℕ (origin k)
      (gridRoot k) (gridKey k) (hcores k).1 Ph seq hseq env hmp
      (by simpa using hlimZ true k false) (by simpa using hlimZ true k true)
    obtain ⟨respLimF, GFv, hcatF⟩ := conv_represented_estimates_transfer d hd model H NF ℕ (root k)
      (z ∘ e k) (r ∘ e k) (fun j => hr (e k j)) (fun j => S (e k j)) (Dcat k) (fcat k)
      (fun _ => ℕ) (trace k) (traceH1 k) (usrcF k) (srcRepF k) (ucellF k) (Cext k) (beta k) alpha
      eta (t k) {1} (I k) ℕ (fun i n β => cR k i (NF n) β) (fun i n β => cC k i (NF n) β)
      (G0F k) (cK k) (eK k) (lK k) (sRK k) (sGK k) (sHK k) (cRK k) (cGK k) (cHK k) ℕ (origin k)
      (gridRoot k) (gridKey k) (hcores k).2 Ph seq hseq env hmp
      (by simpa using hlimZ false k false) (by simpa using hlimZ false k true)
    exact ⟨cR k, cC k, respLimE, respLimF, GEv, GFv, root k, hunit k,
      Dcat k, hDcat k, fcat k, trace k, traceH1 k,
      fun i g n w => usrcE k i g (seq n) (env n w), fun i g n w => usrcF k i g (seq n) (env n w),
      fun i g n w => srcRepE k i g (seq n) (env n w),
      fun i g n w => srcRepF k i g (seq n) (env n w),
      fun i j n w => ucellE k i j (seq n) (env n w),
      fun i j n w => ucellF k i j (seq n) (env n w),
      Cext k, beta k, t k, I k, cK k, eK k, lK k, sRK k, sGK k, sHK k, cRK k, cGK k, cHK k,
      origin k, gridRoot k, gridKey k, hAnchor k, hgrid k, hbuf k, hcatE, hcatF⟩
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, envLim, env,
    fun i n w => volumeResponseOperator (S i)
      (Lane4.cutoffPositiveCoefficient model H (env n w) (NE (seq n)) (z i) (hr i)),
    fun i n w => volumeResponseOperator (S i)
      (Lane4.cutoffPositiveCoefficient model H (env n w) (NF (seq n)) (z i) (hr i)),
    GE, GF, ⟨⟨⟨hPh, hmpLim.measurable, hmpLim.map_eq, hH, hNE.comp hseq, hNF.comp hseq,
      fun n => ⟨hmp n, hmp n⟩, ?_, hS, ?_, ?_⟩, fun k => ⟨e k, he k, hcat k⟩⟩, ?_⟩⟩
  · filter_upwards [hconv] with w hw
    exact ⟨hw.1, hw.1⟩
  · exact Filter.Eventually.of_forall fun w i n f =>
      ⟨volumeResponseOperator_apply _ _ f, volumeResponseOperator_apply _ _ f⟩
  · filter_upwards [hconv] with w hw i
    exact ⟨(hw.2.2 i).2.1, (hw.2.2 i).2.2⟩
  · filter_upwards [hconv] with w hw y
    exact hw.2.1 (Sum.inr y)

end Paper
