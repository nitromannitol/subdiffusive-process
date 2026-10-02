import SubdiffusiveProcess.Paper.Support.KillingFormParameterContinuity
import SubdiffusiveProcess.Paper.Support.KillingCommonIdentification
import SubdiffusiveProcess.Paper.Support.UniformResolventMosco
import SubdiffusiveProcess.Section9.KilledFormResolventData
import SubdiffusiveProcess.Section9.KilledFormResolventIdentification
import SubdiffusiveProcess.Section9.KilledMinimizerSourceReadout

/-! Supports: mfd_lem_killing.
Internal consumption of the uniform-resolvent proposition's produced data.
Every continuity, congruence and subsequence property needed for killing is
proved here from that actual inverse/trace/minimizer output. The source principal
must call the proved uniform-resolvent producer; this adapter is not that root.
-/
open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_identify_produced_data
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (hin : in_crossing M H PN KN)
    (hpath : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps →
        Tendsto (fun N => (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x)}) atTop (𝓝 0))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hdata : KilledFormResolventData d hd M H KN muFull) :
    KilledFormResolventIdentification d hd M H KN K muFull := by
  classical
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  dsimp only [KilledFormResolventData] at hdata
  rcases hdata with ⟨G, hGmeas, hGconv, hmu, T, Ktrace, Ctrace, lift, J,
    ustar, R, KQ, htrace, hRmeas, hprob, hKm, hregular⟩
  let mu := fun i omega => (muFull omega).restrict
    (closure (determiningCube d i : Set (SpatialCoordinates d)))
  let Elim := fun i omega u => (limitFormEnergy (G i omega) u).toENNReal
  obtain ⟨_phi, _hphi, hGP⟩ := aux_mfd_prop_uniform_resolvent_common_mosco_subsequence
    d M H G hGconv id strictMono_id
  have hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
      letI : CompactSpace (closure (determiningCube d i : Set (SpatialCoordinates d))) :=
        isCompact_iff_compactSpace.mp
          (centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure
      Continuous (fun a : Set.Ioi (0 : ℝ) ×
          C(closure (determiningCube d i : Set (SpatialCoordinates d)), ℝ) =>
        fun x : determiningCube d i =>
          R i a.1.1 (closedSourceExtension (determiningCube d i) a.2) omega x) := by
    filter_upwards [htrace, hmu, hregular, hGP] with omega ht hm hr hgp
    intro i
    letI : IsLocallyFiniteMeasure (muFull omega) := hm.2.1
    have hcl : IsCompact (closure (determiningCube d i : Set (SpatialCoordinates d))) :=
      (centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure
    letI : IsFiniteMeasure (mu i omega) := ⟨by
      simpa only [mu, Measure.restrict_apply_univ] using hcl.measure_lt_top⟩
    rcases ht i with ⟨_hKtr, _hCtr, hT, hliftJ⟩
    apply aux_mfd_lem_killing_form_parameter_continuity hd
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
      (G i omega) (hgp i).2.1 (hgp i).2.2.1 (mu i omega)
      (ae_restrict_mem isClosed_closure.measurableSet) (Ktrace i omega) (Ctrace i omega) (T i omega)
      hT (lift i omega) (fun u hu => (hliftJ u hu).1) (J i omega)
      (fun u hu => (hliftJ u hu).2) (ustar i omega)
      (fun lam f => R i lam f omega) (KQ i omega)
    intro lam hlam f
    rcases (hr i).2.2 lam hlam f with ⟨hfinite, hRf, _hzero, _hbound, hholder, hmin, _huniq⟩
    exact ⟨hfinite, hRf, hholder, fun u hu => (hmin u hu).2.2⟩
  have hcongr : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i lam, 0 < lam →
      ∀ f g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Set.EqOn f g (closure (determiningCube d i : Set (SpatialCoordinates d))) →
          Set.EqOn (R i lam f omega) (R i lam g omega)
            (determiningCube d i : Set (SpatialCoordinates d)) := by
    filter_upwards [hregular] with omega hr
    intro i lam hlam f g hfg
    have hfgmu : (f : SpatialCoordinates d → ℝ) =ᵐ[mu i omega] g := by
      filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with x hx
      exact hfg hx
    rcases (hr i).2.2 lam hlam f with ⟨hfinite, hRf, _hzero, _hbound, _hholder, hmin, _huniq⟩
    rcases (hr i).2.2 lam hlam g with ⟨_hfiniteg, hRg, _hzerog, _hboundg, _hholderg, _hming, huniqg⟩
    exact killed_minimizer_representatives_eqOn_of_source_ae_eq (determiningCube d i)
      (mu i omega) (Elim i omega) (J i omega) lam f g hfgmu
      (ustar i omega lam f) (ustar i omega lam g) hfinite (R i lam f omega) (R i lam g omega)
      hRf hRg (fun u hu => (hmin u hu).2.2) huniqg
  have hzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i lam, 0 < lam → ∀ f,
      ∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0 := by
    filter_upwards [hregular] with omega hr
    intro i lam hlam f
    exact ((hr i).2.2 lam hlam f).2.2.1
  have hid := aux_mfd_lem_killing_identify_common_parameters hd M H PN KN hKN K hK hin
    R hpath hprob hzero hcont hcongr
  dsimp only [KilledFormResolventIdentification]
  refine ⟨G, hGmeas, hGconv, hmu, T, Ktrace, Ctrace, lift, J,
    ustar, R, KQ, htrace, hRmeas, hprob, hKm, ?_⟩
  filter_upwards [hregular, hid] with omega hr hi
  intro i
  refine ⟨(hr i).1, (hr i).2.1, ?_⟩
  intro lam hlam f
  rcases (hr i).2.2 lam hlam f with ⟨hfinite, hRf, hzero, hbound, hholder, hmin, huniq⟩
  exact ⟨hfinite, hRf, hzero, hbound, hholder, hmin, huniq, hi i lam hlam f⟩

end Paper
