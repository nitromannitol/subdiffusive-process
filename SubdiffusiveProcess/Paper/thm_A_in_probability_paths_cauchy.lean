import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.in_stopped_passage
import SubdiffusiveProcess.Paper.determining_functional_convergence
import SubdiffusiveProcess.Paper.tight_whole_space_resolvent_limit
import SubdiffusiveProcess.Paper.prop_quenched_convergence

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


-- (`aux_mfd_convergence_{Phi,PhiB,RW_continuous,resolvent_path,marg,psi_eq,det_cauchy,fun_cauchy}`,
-- and `aux_mfd_convergence_{exhaust,contain,path_cauchy}` adapted to the cube `centeredCube 0 (3^m)`).

/-- The discounted path functional `path ↦ ∫_0^∞ e^{-λ t} f(path t) dt`. -/
def aux_thm_A_in_probability_paths_cauchy_Phi {d : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * f (path (Real.toNNReal t))

theorem aux_thm_A_in_probability_paths_cauchy_Phi_integrand_le {d : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) (t : ℝ) :
    ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ ≤ ‖f‖ * Real.exp (-lam * t) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le

theorem aux_thm_A_in_probability_paths_cauchy_Phi_abs_le {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    |aux_thm_A_in_probability_paths_cauchy_Phi lam f path| ≤ ‖f‖ / lam := by
  have h := norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖)
    (Eventually.of_forall (aux_thm_A_in_probability_paths_cauchy_Phi_integrand_le lam f path))
  rw [integral_const_mul, aux_in_stopped_passage_exp_Ioi hlam, mul_zero, Real.exp_zero,
    ← div_eq_mul_one_div] at h
  exact h

theorem aux_thm_A_in_probability_paths_cauchy_Phi_continuous {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (aux_thm_A_in_probability_paths_cauchy_Phi (d := d) lam f) := by
  unfold aux_thm_A_in_probability_paths_cauchy_Phi
  refine continuous_of_dominated (bound := fun t => ‖f‖ * Real.exp (-lam * t)) ?_ ?_ ?_ ?_
  · intro path
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (f.continuous.comp (path.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable
  · intro path
    exact Eventually.of_forall (aux_thm_A_in_probability_paths_cauchy_Phi_integrand_le lam f path)
  · exact (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
  · refine Eventually.of_forall fun t => ?_
    exact continuous_const.mul (f.continuous.comp (continuous_eval_const _))

/-- The discounted path functional as a bounded continuous function. -/
def aux_thm_A_in_probability_paths_cauchy_PhiB {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    BoundedContinuousFunction (DiffusionPath d) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨aux_thm_A_in_probability_paths_cauchy_Phi lam f,
      aux_thm_A_in_probability_paths_cauchy_Phi_continuous hlam f⟩ (2 * (‖f‖ / lam)) (by
    intro p q
    rw [Real.dist_eq]
    have h1 := aux_thm_A_in_probability_paths_cauchy_Phi_abs_le hlam f p
    have h2 := aux_thm_A_in_probability_paths_cauchy_Phi_abs_le hlam f q
    calc |aux_thm_A_in_probability_paths_cauchy_Phi lam f p - aux_thm_A_in_probability_paths_cauchy_Phi lam f q|
        ≤ |aux_thm_A_in_probability_paths_cauchy_Phi lam f p| + |aux_thm_A_in_probability_paths_cauchy_Phi lam f q| :=
          abs_sub _ _
      _ ≤ 2 * (‖f‖ / lam) := by linarith)

theorem aux_thm_A_in_probability_paths_cauchy_PhiB_apply {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    aux_thm_A_in_probability_paths_cauchy_PhiB hlam f path = aux_thm_A_in_probability_paths_cauchy_Phi lam f path := rfl

/-- Continuity in the start of the discounted path integral, from continuity of the laws. -/
theorem aux_thm_A_in_probability_paths_cauchy_RW_continuous
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (hc : Continuous (fun x : SpatialCoordinates d => jointPathProbabilityMeasure K hK omega x))
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(K (omega, x))) := by
  have h := ProbabilityMeasure.continuous_iff_forall_continuous_integral.1 hc
    (aux_thm_A_in_probability_paths_cauchy_PhiB hlam f)
  exact h

/-- The semigroup resolvent equals the discounted path integral, given the one-time
marginals. -/
theorem aux_thm_A_in_probability_paths_cauchy_resolvent_path {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (κ : Measure (DiffusionPath d)) [IsProbabilityMeasure κ]
    (hmarg : ∀ t : ℝ≥0, κ.map (fun path : DiffusionPath d => path t) = P t x)
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    P.kernelResolventReal lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂κ := by
  have hev : ∀ t : ℝ≥0, Measurable (fun path : DiffusionPath d => path t) := fun t =>
    ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t
  have hki : ∀ t : ℝ, kernelIntegral (P (Real.toNNReal t)) f x =
      ∫ path, f (path (Real.toNNReal t)) ∂κ := by
    intro t
    unfold kernelIntegral
    rw [← hmarg, integral_map (hev _).aemeasurable f.continuous.aestronglyMeasurable]
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  simp_rw [hki, ← integral_const_mul]
  have hcont : Continuous (fun p : ℝ × DiffusionPath d =>
      Real.exp (-lam * p.1) * f (p.2 (Real.toNNReal p.1))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (f.continuous.comp (continuous_eval.comp
        (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))))
  have hint : Integrable (Function.uncurry fun (t : ℝ) (path : DiffusionPath d) =>
      Real.exp (-lam * t) * f (path (Real.toNNReal t)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod κ) := by
    have h1 : Integrable (fun t : ℝ => ‖f‖ * Real.exp (-lam * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
    refine Integrable.mono' (Integrable.comp_fst h1 κ) hcont.aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    exact aux_thm_A_in_probability_paths_cauchy_Phi_integrand_le lam f p.2 p.1
  exact integral_integral_swap hint

-- ===== from T4b.lean =====

/-- One-time marginals of a path kernel from its finite-dimensional identification. -/
theorem aux_thm_A_in_probability_paths_cauchy_marg
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (omega : BilateralField d) (x : SpatialCoordinates d)
    (h : ∀ I, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) (t : ℝ≥0) :
    (K (omega, x)).map (fun path : DiffusionPath d => path t) = P t x := by
  have heval : ∀ I : Finset ℝ≥0,
      Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) := by
    intro I
    rw [measurable_pi_iff]
    intro s
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d)
      (s : NNReal)
  have hmap : ∀ I : Finset ℝ≥0, (K (omega, x)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x := by
    intro I
    rw [← Kernel.map_apply _ (heval I)]
    exact h I
  exact aux_determining_functional_convergence_marginal P x (K (omega, x)) hmap t


/-- The determining functional in the form of `determining_functional_convergence`
equals the one in `prop_quenched_convergence`. -/
theorem aux_thm_A_in_probability_paths_cauchy_psi_eq {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ) :
    (fun path : DiffusionPath d => ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
      Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
        ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) =
    (fun path : DiffusionPath d =>
      ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-(∑ i : Fin k, ((n i + 1 : ℕ) : ℝ) * s i)) *
          ∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) := by
  funext path
  have hset : Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) =
      {s : Fin k → ℝ | ∀ i, 0 < s i} := by
    ext s
    simp
  have hfil : ∀ i : Fin k, Finset.univ.filter (fun j : Fin k => j ≤ i) = Finset.Iic i := by
    intro i
    ext j
    simp
  rw [hset]
  simp only [hfil]
  push_cast
  rfl

-- ===== from T4c.lean =====
/-- The deterministic finite-cutoff resolvent Cauchy estimate `hdet` of
`determining_functional_convergence`, from the whole-space convergence in probability. -/
theorem aux_thm_A_in_probability_paths_cauchy_det_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hfdd : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ))
    (hR : ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : Nat, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤ |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) -
                  R lam f omega x|} ≤ ENNReal.ofReal rho) :
    ∀ n : Nat, 0 < n →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N N' : Nat, N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
            (PN N' omega).kernelResolventReal (n : ℝ) f x|} ≤
            ENNReal.ofReal rho := by
  intro n hn f B hB eps heps rho hrho
  have hlam : (0 : ℝ) < n := Nat.cast_pos.2 hn
  obtain ⟨N0, hN0⟩ := hR n hlam f B hB (eps / 2) (by positivity) (rho / 2) (by positivity)
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  set μ := (chaosSampleLaw M).toMeasure with hμ
  let Z : Set (BilateralField d) := {omega | ¬ ∀ N I x,
    (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x}
  have hZ : μ Z = 0 := ae_iff.1 hfdd
  let A : ℕ → Set (BilateralField d) := fun N => {omega | ∃ x ∈ B, eps / 2 ≤
    |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) -
      R n f omega x|}
  have hsub : {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
      (PN N' omega).kernelResolventReal (n : ℝ) f x|} ⊆ (A N ∪ A N') ∪ Z := by
    rintro omega ⟨x, hx, hc⟩
    by_cases hω : omega ∈ Z
    · exact Or.inr hω
    · left
      have hI : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x := not_not.1 hω
      have e : ∀ N, (PN N omega).kernelResolventReal (n : ℝ) f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)) := by
        intro N
        haveI := (hKN N).isProbabilityMeasure (omega, x)
        exact aux_thm_A_in_probability_paths_cauchy_resolvent_path (PN N omega) x (KN N (omega, x))
          (aux_thm_A_in_probability_paths_cauchy_marg (KN N) (PN N omega) omega x (fun I => hI N I x)) hlam f
      rw [e N, e N'] at hc
      by_contra hcon
      simp only [Set.mem_union, A, Set.mem_setOf_eq, not_or, not_exists, not_and,
        not_le] at hcon
      have h1 := hcon.1 x hx
      have h2 := hcon.2 x hx
      have h3 := abs_sub_le
        (∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
        (R n f omega x)
        (∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N' (omega, x)))
      rw [abs_sub_comm (R n f omega x)] at h3
      linarith
  calc μ {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
        (PN N' omega).kernelResolventReal (n : ℝ) f x|}
      ≤ μ ((A N ∪ A N') ∪ Z) := measure_mono hsub
    _ ≤ μ (A N) + μ (A N') + μ Z :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) + 0 := by
        rw [hZ]
        exact add_le_add (add_le_add (hN0 N hN) (hN0 N' hN')) le_rfl
    _ = ENNReal.ofReal rho := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- The Cauchy property of the integrated determining functionals, in the form of
`prop_quenched_convergence`, from their convergence in probability. -/
theorem aux_thm_A_in_probability_paths_cauchy_fun_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (Psi : DiffusionPath d → ℝ) (U : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hU : ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B,
              eps ≤ |(∫ path, Psi path ∂(KN N (omega, x))) - U omega x|} ≤
                ENNReal.ofReal rho) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, Psi path ∂(KN N (omega, x))) -
                (∫ path, Psi path ∂(KN N' (omega, x)))|} ≤ ENNReal.ofReal rho := by
  intro B hB eps heps rho hrho
  obtain ⟨N0, hN0⟩ := hU B hB (eps / 2) (by positivity) (rho / 2) (by positivity)
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  let A : ℕ → Set (BilateralField d) := fun N => {omega | ∃ x ∈ B,
    eps / 2 ≤ |(∫ path, Psi path ∂(KN N (omega, x))) - U omega x|}
  have hsub : {omega : BilateralField d | ∃ x ∈ B, eps ≤
      |(∫ path, Psi path ∂(KN N (omega, x))) -
        (∫ path, Psi path ∂(KN N' (omega, x)))|} ⊆ A N ∪ A N' := by
    rintro omega ⟨x, hx, hc⟩
    by_contra hcon
    simp only [Set.mem_union, A, Set.mem_setOf_eq, not_or, not_exists, not_and,
      not_le] at hcon
    have h1 := hcon.1 x hx
    have h2 := hcon.2 x hx
    have h3 := abs_sub_le (∫ path, Psi path ∂(KN N (omega, x))) (U omega x)
      (∫ path, Psi path ∂(KN N' (omega, x)))
    rw [abs_sub_comm (U omega x)] at h3
    linarith
  calc (chaosSampleLaw M).toMeasure {omega : BilateralField d | ∃ x ∈ B, eps ≤
        |(∫ path, Psi path ∂(KN N (omega, x))) -
          (∫ path, Psi path ∂(KN N' (omega, x)))|}
      ≤ (chaosSampleLaw M).toMeasure (A N ∪ A N') := measure_mono hsub
    _ ≤ (chaosSampleLaw M).toMeasure (A N) + (chaosSampleLaw M).toMeasure (A N') :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) :=
        add_le_add (hN0 N hN) (hN0 N' hN')
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- Every bounded set lies in a cube `centeredCube 0 (3^n)`. -/
theorem aux_thm_A_in_probability_paths_cauchy_exhaust (d : ℕ) (U : Set (SpatialCoordinates d))
    (hU : Bornology.IsBounded U) :
    ∃ n : ℕ, U ⊆ (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ n)
      (pow_pos (by norm_num) n) : Set (SpatialCoordinates d)) := by
  obtain ⟨R, hR⟩ := hU.subset_ball (0 : SpatialCoordinates d)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, fun x hx => ?_⟩
  change x ∈ Metric.ball _ _
  have hx' := hR hx
  rw [Metric.mem_ball] at hx' ⊢
  linarith

/-- Compact containment of the exit from a large cube, from expectation tightness. -/
theorem aux_thm_A_in_probability_paths_cauchy_contain
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ ∂μ) ≤
            ENNReal.ofReal epsilon) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ T : ℝ, 0 ≤ T → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ m : ℕ, B ⊆ (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
            (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) ∧
          ∀ N : ℕ, μ {omega | ∃ x ∈ B, eps ≤
            ((KN N (omega, x)) {path | ContinuousPath.exitTime
              (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
                (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
                  ENNReal.ofReal T}).toReal} ≤ ENNReal.ofReal rho := by
  intro B hB T hT eps heps rho hrho
  obtain ⟨Kset, hKc, hKint⟩ := htight B hB (rho * (eps / 2)) (by positivity)
  let Kpos : Set (SpatialCoordinates d) :=
    (fun p : DiffusionPath d × ℝ≥0 => p.1 p.2) '' (Kset ×ˢ Set.Icc 0 (Real.toNNReal T))
  have hKpos : IsCompact Kpos := (hKc.prod isCompact_Icc).image continuous_eval
  obtain ⟨m, hm⟩ := aux_thm_A_in_probability_paths_cauchy_exhaust d (B ∪ Kpos)
    (hB.isBounded.union hKpos.isBounded)
  refine ⟨m, fun x hx => hm (Or.inl hx), fun N => ?_⟩
  have hsub : ∀ path ∈ Kset, ¬ (ContinuousPath.exitTime
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
        (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
          ENNReal.ofReal T) := by
    intro path hpath hle
    have hle' : ContinuousPath.exitTime
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
        ((Real.toNNReal T : ℝ≥0) : ℝ≥0∞) := hle
    obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
      (centeredCube _ _ _).isOpen _ path).1 hle'
    apply hs
    exact hm (Or.inr ⟨(path, (s : ℝ≥0)), ⟨hpath, ⟨zero_le _, s.property⟩⟩, rfl⟩)
  have hset : {omega | ∃ x ∈ B, eps ≤
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T}).toReal} ⊆
      {omega | ∃ x ∈ B, ENNReal.ofReal (eps / 2) < (KN N (omega, x)) Ksetᶜ} := by
    rintro omega ⟨x, hx, hle⟩
    refine ⟨x, hx, ?_⟩
    haveI := (hKN N).isProbabilityMeasure (omega, x)
    have hmono : (KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T} ≤ (KN N (omega, x)) Ksetᶜ :=
      measure_mono fun path hp hK' => hsub path hK' hp
    have h1 : ENNReal.ofReal eps ≤ (KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T} :=
      (ENNReal.ofReal_le_ofReal hle).trans (ENNReal.ofReal_toReal (measure_ne_top _ _)).le
    calc ENNReal.ofReal (eps / 2) < ENNReal.ofReal eps :=
          (ENNReal.ofReal_lt_ofReal_iff heps).2 (by linarith)
      _ ≤ _ := h1.trans hmono
  exact (measure_mono hset).trans (aux_determining_functional_convergence_tight_event μ (KN N)
    B hB Kset hKc (by positivity) (hKint N))




theorem thm_A_in_probability_paths_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ,
            (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
              ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon)
    (Rlim : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
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
          ENNReal.ofReal rho) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho := by
  classical
  have hin' := hin
  unfold in_crossing at hin'
  have hcontWS : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Continuous (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) := by
    filter_upwards [hstart] with omega h
    intro N lam hlam f
    exact aux_thm_A_in_probability_paths_cauchy_RW_continuous (KN N) (hKN N) omega (h N) hlam f
  have hWS := Paper.tight_whole_space_resolvent_limit hd M H hH
    PN KN hKN hin
    (fun _ => (0 : SpatialCoordinates d)) (fun n => (3 : ℝ) ^ n)
    (fun n => pow_pos (by norm_num) n)
    (fun N omega lam f x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (fun m N omega lam f x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
      ∂(KN N (omega, x))) Rlim
    (fun m N omega x T => ((KN N (omega, x)) {path | ContinuousPath.exitTime
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
        (pow_pos (by norm_num) m) : Set (SpatialCoordinates d)) path ≤
          ENNReal.ofReal T}).toReal)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    hcontWS hkilled
    (aux_thm_A_in_probability_paths_cauchy_contain (chaosSampleLaw M).toMeasure KN hKN htight)
  rcases hWS with ⟨R, hR⟩
  have hdetD := aux_thm_A_in_probability_paths_cauchy_det_cauchy M PN KN hKN hin'.2.2 R
    (fun lam hlam f => (hR lam hlam f).2.2.1)
  have hcontD : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N n : ℕ), 0 < n → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Continuous ((PN N omega).kernelResolventReal (n : ℝ) f) := by
    filter_upwards [hin'.2.2, hcontWS] with omega hI hc
    intro N n hn f
    have hlam : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have e : (PN N omega).kernelResolventReal (n : ℝ) f = fun x => ∫ path,
        (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)) := by
      funext x
      haveI := (hKN N).isProbabilityMeasure (omega, x)
      exact aux_thm_A_in_probability_paths_cauchy_resolvent_path (PN N omega) x (KN N (omega, x))
        (aux_thm_A_in_probability_paths_cauchy_marg (KN N) (PN N omega) omega x
          (fun I => hI N I x)) hlam f
    rw [e]
    exact hc N n hlam f
  have htightD : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N : Nat,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂(chaosSampleLaw M).toMeasure) ≤
            ENNReal.ofReal eps := by
    intro B hB eps heps
    obtain ⟨A, hA, hAi⟩ := htight B hB eps heps
    refine ⟨A, hA, fun N => le_of_eq_of_le ?_ (hAi N)⟩
    congr 1
    funext omega
    rw [iSup_subtype']
  have hcauchyQ : ∀ (k : ℕ) (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (n : Fin k → ℕ) (B : Set (SpatialCoordinates d)), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N (omega, x))) -
                (∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N' (omega, x)))|} ≤ ENNReal.ofReal rho := by
    intro k f n B hB eps heps rho hrho
    rw [aux_thm_A_in_probability_paths_cauchy_psi_eq f n]
    have hDF := determining_functional_convergence M H PN KN hKN hin
      (fun N omega n f x => (PN N omega).kernelResolventReal (n : ℝ) f x)
      (fun _ _ _ _ _ => rfl) hcontD hdetD htightD k f (fun i => n i + 1)
      (fun i => Nat.succ_pos _)
      (fun path : DiffusionPath d =>
        ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-(∑ i : Fin k, ((n i + 1 : ℕ) : ℝ) * s i)) *
            ∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
      (fun _ => rfl)
    rcases hDF with ⟨U, -, hU⟩
    exact aux_thm_A_in_probability_paths_cauchy_fun_cauchy M KN _ U hU B hB eps heps rho hrho
  exact prop_quenched_convergence hd M H hH PN KN hKN hin hcauchyQ htight

end Paper
