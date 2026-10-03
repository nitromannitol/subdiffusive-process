module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.tight_prop
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.tight_fixed_cutoff
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.limit_kernel_path_limit
public import SubdiffusiveProcess.Paper.thm_A_in_probability_paths_cauchy

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_thm_A_in_probability_paths_coe {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d) (x : SpatialCoordinates d) :
    ((jointPathProbabilityMeasure K hK omega x : ProbabilityMeasure (DiffusionPath d)) :
      Measure (DiffusionPath d)) = K (omega, x) := rfl

/-- A kernel that is weakly continuous in the start for almost every environment agrees almost
surely with a Markov kernel that is weakly continuous in the start for every environment
(replace it by constant paths on a measurable null set of environments). -/
theorem aux_thm_A_in_probability_paths_everywhere
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hcont : ∀ᵐ omega ∂μ, Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure K hK omega x)) :
    ∃ (K' : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK' : IsMarkovKernel K'),
      (∀ omega : BilateralField d, Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K' hK' omega x)) ∧
      ∀ᵐ omega ∂μ, ∀ x : SpatialCoordinates d,
        jointPathProbabilityMeasure K' hK' omega x = jointPathProbabilityMeasure K hK omega x := by
  classical
  obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  have hconst : Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      (ContinuousMap.const ℝ≥0 p.2 : DiffusionPath d)) :=
    (ContinuousMap.continuous_const'.measurable).comp measurable_snd
  let K0 : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d) :=
    Kernel.deterministic (fun p : BilateralField d × SpatialCoordinates d =>
      (ContinuousMap.const ℝ≥0 p.2 : DiffusionPath d)) hconst
  haveI : IsMarkovKernel K0 := by infer_instance
  haveI := hK
  let K' : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d) :=
    Kernel.piecewise (measurable_fst hTm) K0 K
  haveI hK' : IsMarkovKernel K' := by infer_instance
  have hK'T : ∀ omega, omega ∈ T → ∀ x, K' (omega, x) = Measure.dirac (ContinuousMap.const ℝ≥0 x) := by
    intro omega hω x
    simp only [K', Kernel.piecewise_apply, Set.mem_preimage, if_pos hω, K0, Kernel.deterministic_apply]
  have hK'F : ∀ omega, omega ∉ T → ∀ x, K' (omega, x) = K (omega, x) := by
    intro omega hω x
    simp only [K', Kernel.piecewise_apply, Set.mem_preimage, if_neg hω]
  refine ⟨K', hK', ?_, ?_⟩
  · intro omega
    by_cases hω : omega ∈ T
    · refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.2 fun g => ?_
      have hint : (fun x : SpatialCoordinates d => ∫ path, g path
          ∂((jointPathProbabilityMeasure K' hK' omega x : ProbabilityMeasure (DiffusionPath d)) :
            Measure (DiffusionPath d))) =
          fun x => g (ContinuousMap.const ℝ≥0 x) := by
        funext x
        rw [aux_thm_A_in_probability_paths_coe, hK'T omega hω x,
          integral_dirac' _ _ g.continuous.measurable.stronglyMeasurable]
      rw [hint]
      exact g.continuous.comp ContinuousMap.continuous_const'
    · have hE : (fun x : SpatialCoordinates d => jointPathProbabilityMeasure K' hK' omega x) =
          fun x => jointPathProbabilityMeasure K hK omega x := by
        funext x
        exact Subtype.ext (hK'F omega hω x)
      rw [hE]
      by_contra hc
      exact hω (hsub hc)
  · have hTae : ∀ᵐ omega ∂μ, omega ∉ T := by
      rw [ae_iff]
      simpa using hT0
    filter_upwards [hTae] with omega hω x
    exact Subtype.ext (hK'F omega hω x)



theorem thm_A_in_probability_paths
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
        (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
        (Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
        (hRmeas : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rlim n p.1 lam f p.2))
        (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ closure (centeredCube (0 : SpatialCoordinates d)
                  ((3 : ℝ) ^ n) (pow_pos (by norm_num) n) : Set (SpatialCoordinates d)),
                eps ≤ |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ n)
                        (pow_pos (by norm_num) n) : Set (SpatialCoordinates d)) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                    ∂(KN N (omega, x))) - Rlim n omega lam f x|} ≤
              ENNReal.ofReal rho),
      (∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
            (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
              ENNReal.ofReal rho) ∧
      ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
      ∃ hK : IsMarkovKernel K,
        (∀ omega : BilateralField d,
          Continuous (fun x : SpatialCoordinates d =>
            jointPathProbabilityMeasure K hK omega x)) ∧
        ∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                  {omega : BilateralField d | ∃ x ∈ B, eps ≤
                    pathLevyProkhorovDist
                      (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                      (jointPathProbabilityMeasure K hK omega x)} ≤
                ENNReal.ofReal rho := by
  classical
  obtain ⟨delta0, hdelta0, htp⟩ := tight_prop (d := d) hd Jc Pc Xc Sf W Cp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hMle H hH PN KN hKN hin hinput Rlim _hRmeas hkilled
  -- lifetime package, tightness and start continuity (as in `mfd_convergence`)
  obtain ⟨L, hL, hLlocal, -⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  have htightNew := htp M Rm Sreg It hMle H hH PN KN hKN hin L hL hLlocal
  have htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon := by
    intro B hB epsilon hepsilon
    obtain ⟨Kset, hKset, hmajorant, -⟩ := htightNew B hB epsilon hepsilon
    refine ⟨Kset, hKset, ?_⟩
    intro N
    obtain ⟨G, -, hG, hGint⟩ := hmajorant N
    exact (lintegral_mono fun omega => iSup_le fun x => iSup_le fun hx =>
      hG omega x hx).trans hGint
  have hbounds := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLlocal
  have hstart := in_cutoff_start_continuity hd M H hH PN KN hKN hin hbounds
  have hcauchy := thm_A_in_probability_paths_cauchy hd M H hH PN KN hKN hin hstart htight
    Rlim hkilled
  obtain ⟨K, hK, hcontK, hconv⟩ := limit_kernel_path_limit M KN hKN hcauchy hstart
  obtain ⟨K', hK', hcont', hae⟩ := aux_thm_A_in_probability_paths_everywhere
    (chaosSampleLaw M).toMeasure K hK hcontK
  refine ⟨hcauchy, K', hK', hcont', ?_⟩
  intro B hB eps heps rho hrho
  obtain ⟨N0, hN0⟩ := hconv B hB eps heps rho hrho
  refine ⟨N0, fun N hN => ?_⟩
  set Z : Set (BilateralField d) := {omega | ¬ ∀ x : SpatialCoordinates d,
    jointPathProbabilityMeasure K' hK' omega x = jointPathProbabilityMeasure K hK omega x} with hZ
  have hZ0 : (chaosSampleLaw M).toMeasure Z = 0 := ae_iff.1 hae
  have hsub : {omega : BilateralField d | ∃ x ∈ B, eps ≤
      pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
        (jointPathProbabilityMeasure K' hK' omega x)} ⊆
      {omega : BilateralField d | ∃ x ∈ B, eps ≤
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x)} ∪ Z := by
    rintro omega ⟨x, hx, hle⟩
    by_cases hω : omega ∈ Z
    · exact Or.inr hω
    · left
      have hall : ∀ y : SpatialCoordinates d,
          jointPathProbabilityMeasure K' hK' omega y = jointPathProbabilityMeasure K hK omega y :=
        not_not.1 hω
      exact ⟨x, hx, by rwa [← hall x]⟩
  calc (chaosSampleLaw M).toMeasure {omega : BilateralField d | ∃ x ∈ B, eps ≤
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K' hK' omega x)}
      ≤ (chaosSampleLaw M).toMeasure ({omega : BilateralField d | ∃ x ∈ B, eps ≤
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x)} ∪ Z) := measure_mono hsub
    _ ≤ (chaosSampleLaw M).toMeasure {omega : BilateralField d | ∃ x ∈ B, eps ≤
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x)} + (chaosSampleLaw M).toMeasure Z :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal rho := by
        rw [hZ0, add_zero]
        exact hN0 N hN

end Paper
