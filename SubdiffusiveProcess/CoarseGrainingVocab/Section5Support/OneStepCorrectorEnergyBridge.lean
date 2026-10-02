import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryPotentialCutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSolenoidalApproximation

/-!
# Thermodynamic one-step corrector energy

This is the GMC specialization of the Dirichlet--Neumann squeeze in
`Algsuperdiff/Section3/Provider/Corrector/CorrectorLimitFreshShell.lean`.
The finite-cube shell correctors are compared with the already constructed
localized stationary potential and solenoidal fields.  Thus their expected
normalized energies converge to the squared norm of the stationary Helmholtz
projection; no new Helmholtz construction is introduced here.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## Literal stationary forcing -/

/-- The spatial realization of the origin shell forcing is the manuscript's
literal shell multiplier at the spatial point. -/
theorem realize_oneStepOriginForcing_eq_oneStepMultiplierAt
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (omega : Sample d) (x : Vec d) :
    realize (oneStepOriginForcing M n h p) omega x =
      oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p := by
  change oneStepOriginMultiplier M n h (translatePotentialSequence x omega) •
      HilbertVec.ofVec p = _
  congr 1
  dsimp only [oneStepOriginMultiplier, oneStepMultiplierAt,
    cutoffRatioMinusOne, aCutoffAtInt]
  simp only [if_neg (not_lt_of_ge (Int.natCast_nonneg n)),
    Int.toNat_natCast]
  rw [aCutoff_translatePotentialSequence M (n + h) x omega 0,
    aCutoff_translatePotentialSequence M n x omega 0, zero_add]

/-- Vector-carrier version of the literal realization identity. -/
theorem realize_oneStepOriginForcing_toVec_eq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (omega : Sample d) (x : Vec d) :
    (realize (oneStepOriginForcing M n h p) omega x).toVec =
      oneStepMultiplierAt M n h x omega • p := by
  rw [realize_oneStepOriginForcing_eq_oneStepMultiplierAt]
  rfl

/-! ## Finite-cube admissibility -/

/-- The canonical Dirichlet corrector gradient is a zero-trace potential and
its sum with the literal stationary forcing is solenoidal. -/
theorem oneStepTriadicDirichlet_admissible
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) :
    IsPotentialZeroTraceOn (openCubeSet Q)
        (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad ∧
      IsSolenoidalOn (openCubeSet Q) (fun x =>
        (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x +
          (realize (oneStepOriginForcing M n h p) omega x).toVec) := by
  constructor
  · exact (oneStepTriadicDirichletSolution M n h p Q omega hh).isPotentialZeroTraceOn
  · intro phi
    have hweak := oneStepTriadicDirichletSolution_isWeakSolution
      M n h p Q omega hh phi
    have hD : MemVectorL2 (openCubeSet Q)
        (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad :=
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad_memVectorL2
    have hF : MemVectorL2 (openCubeSet Q)
        (fun x => (realize (oneStepOriginForcing M n h p) omega x).toVec) := by
      have hcont : Continuous (fun x => oneStepMultiplierAt M n h x omega • p) :=
        (continuous_oneStepMultiplierAt_sample M n h omega).smul continuous_const
      simpa only [realize_oneStepOriginForcing_toVec_eq] using
        memVectorL2_openCubeSet_of_continuous Q hcont
    have hDint := integrableOn_vecDot_of_memVectorL2 hD
      phi.toH1Function.grad_memVectorL2
    have hFint := integrableOn_vecDot_of_memVectorL2 hF
      phi.toH1Function.grad_memVectorL2
    simp only [vecDot_add_left]
    rw [integral_add hDint hFint]
    have hforce :
        (∫ x in openCubeSet Q,
          vecDot ((realize (oneStepOriginForcing M n h p) omega x).toVec)
            (phi.toH1Function.grad x) ∂volume) =
          ∫ x in openCubeSet Q,
            vecDot (oneStepMultiplierAt M n h x omega • p)
              (phi.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [realize_oneStepOriginForcing_toVec_eq]
    rw [hforce]
    have hneg :
        (∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • p)
            (phi.toH1Function.grad x) ∂volume) =
          -∫ x in openCubeSet Q,
            vecDot (oneStepMultiplierAt M n h x omega • p)
              (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      simp only [neg_smul, vecDot_neg_left]
    simp only [matVecMul_identityCoeffField] at hweak
    rw [hneg] at hweak
    linarith

/-- The canonical Neumann corrector gradient is potential and its sum with
the literal stationary forcing is solenoidal with zero normal trace. -/
theorem oneStepTriadicNeumann_admissible
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) :
    IsPotentialOn (openCubeSet Q)
        (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad ∧
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x =>
        (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad x +
          (realize (oneStepOriginForcing M n h p) omega x).toVec) := by
  constructor
  · exact (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.isPotentialOn
  · intro phi
    letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet Q
    let phi0 : H1MeanZeroFunction (openCubeSet Q) := phi.toMeanZero
    have hweak := oneStepTriadicNeumannSolution_isWeakSolution
      M n h p Q omega hh phi0
    have hgrad : phi0.toH1Function.grad = phi.grad := by
      funext x
      exact H1Function.toMeanZero_grad phi x
    have hD : MemVectorL2 (openCubeSet Q)
        (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad :=
      (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad_memVectorL2
    have hF : MemVectorL2 (openCubeSet Q)
        (fun x => (realize (oneStepOriginForcing M n h p) omega x).toVec) := by
      have hcont : Continuous (fun x => oneStepMultiplierAt M n h x omega • p) :=
        (continuous_oneStepMultiplierAt_sample M n h omega).smul continuous_const
      simpa only [realize_oneStepOriginForcing_toVec_eq] using
        memVectorL2_openCubeSet_of_continuous Q hcont
    have hDint := integrableOn_vecDot_of_memVectorL2 hD phi.grad_memVectorL2
    have hFint := integrableOn_vecDot_of_memVectorL2 hF phi.grad_memVectorL2
    simp only [vecDot_add_left]
    rw [integral_add hDint hFint]
    have hforce :
        (∫ x in openCubeSet Q,
          vecDot ((realize (oneStepOriginForcing M n h p) omega x).toVec)
            (phi.grad x) ∂volume) =
          ∫ x in openCubeSet Q,
            vecDot (oneStepMultiplierAt M n h x omega • p)
              (phi.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [realize_oneStepOriginForcing_toVec_eq]
    rw [hforce, ← hgrad]
    have hneg :
        (∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • p)
            (phi0.toH1Function.grad x) ∂volume) =
          -∫ x in openCubeSet Q,
            vecDot (oneStepMultiplierAt M n h x omega • p)
              (phi0.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      simp only [neg_smul, vecDot_neg_left]
    simp only [matVecMul_identityCoeffField] at hweak
    rw [hneg] at hweak
    linarith

/-! ## Deterministic variational squeeze -/

private theorem vecDot_sub_self_bridge {d : ℕ} (a b : Vec d) :
    vecDot (a - b) (a - b) =
      vecDot a a - 2 * vecDot a b + vecDot b b := by
  simp only [vecDot, Pi.sub_apply]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      show (a i - b i) * (a i - b i) =
        a i * a i - 2 * (a i * b i) + b i * b i by ring,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem vecDot_self_nonneg_bridge {d : ℕ} (a : Vec d) :
    0 ≤ vecDot a a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

private theorem setIntegral_vecDot_eq_zero_of_solenoidal
    {d : ℕ} {U : Set (Vec d)} {g v : Vec d → Vec d}
    (hg : IsSolenoidalOn U g) (hv : IsPotentialZeroTraceOn U v) :
    ∫ x in U, vecDot (g x) (v x) = 0 := by
  obtain ⟨u, rfl⟩ := hv
  exact hg u

private theorem setIntegral_vecDot_eq_zero_of_zeroNormal
    {d : ℕ} {U : Set (Vec d)} {g v : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn U g) (hv : IsPotentialOn U v) :
    ∫ x in U, vecDot (g x) (v x) = 0 := by
  obtain ⟨u, rfl⟩ := hv
  exact hg u

private theorem memVectorL2_of_isPotentialZeroTraceOn_bridge
    {d : ℕ} {U : Set (Vec d)} {v : Vec d → Vec d}
    (hv : IsPotentialZeroTraceOn U v) : MemVectorL2 U v := by
  obtain ⟨u, rfl⟩ := hv
  exact u.toH1Function.grad_memVectorL2

private theorem memVectorL2_of_isPotentialOn_bridge
    {d : ℕ} {U : Set (Vec d)} {v : Vec d → Vec d}
    (hv : IsPotentialOn U v) : MemVectorL2 U v := by
  obtain ⟨u, rfl⟩ := hv
  exact u.grad_memVectorL2

/-- A finite Dirichlet corrector dominates the stationary-potential
competitor after completing the square. -/
theorem setIntegral_dirichlet_energy_ge_flux_difference
    {d : ℕ} {U : Set (Vec d)} {D F v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F)
    (hv : MemVectorL2 U v)
    (hsol : IsSolenoidalOn U fun x => D x + F x)
    (hvpot : IsPotentialZeroTraceOn U v) :
    (∫ x in U, vecDot (F x) (F x)) -
        ∫ x in U, vecDot (v x + F x) (v x + F x) ≤
      ∫ x in U, vecDot (D x) (D x) := by
  have hDv : IntegrableOn (fun x => vecDot (D x) (v x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hv
  have hFv : IntegrableOn (fun x => vecDot (F x) (v x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hv
  have hDD : IntegrableOn (fun x => vecDot (D x) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hD
  have hvv : IntegrableOn (fun x => vecDot (v x) (v x)) U :=
    integrableOn_vecDot_of_memVectorL2 hv hv
  have hFF : IntegrableOn (fun x => vecDot (F x) (F x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hF
  have hzero : (∫ x in U, vecDot (D x) (v x)) +
      ∫ x in U, vecDot (F x) (v x) = 0 := by
    have hsplit : ∫ x in U, vecDot (D x + F x) (v x) =
        (∫ x in U, vecDot (D x) (v x)) +
          ∫ x in U, vecDot (F x) (v x) := by
      rw [← integral_add hDv hFv]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)
    rw [← hsplit]
    exact setIntegral_vecDot_eq_zero_of_solenoidal hsol hvpot
  have hdist : 0 ≤ ∫ x in U, vecDot (D x - v x) (D x - v x) :=
    integral_nonneg fun x => vecDot_self_nonneg_bridge _
  have hdistExp :
      (∫ x in U, vecDot (D x - v x) (D x - v x)) =
        (∫ x in U, vecDot (D x) (D x)) -
          2 * (∫ x in U, vecDot (D x) (v x)) +
          ∫ x in U, vecDot (v x) (v x) := by
    have hpt : ∀ x, vecDot (D x - v x) (D x - v x) =
        vecDot (D x) (D x) - 2 * vecDot (D x) (v x) +
          vecDot (v x) (v x) := fun x => vecDot_sub_self_bridge _ _
    have h1 : ∫ x in U, (vecDot (D x) (D x) -
          2 * vecDot (D x) (v x) + vecDot (v x) (v x)) =
        (∫ x in U, (vecDot (D x) (D x) - 2 * vecDot (D x) (v x))) +
          ∫ x in U, vecDot (v x) (v x) :=
      integral_add (hDD.sub (hDv.const_mul 2)) hvv
    have h2 : ∫ x in U, (vecDot (D x) (D x) - 2 * vecDot (D x) (v x)) =
        (∫ x in U, vecDot (D x) (D x)) -
          ∫ x in U, 2 * vecDot (D x) (v x) :=
      integral_sub hDD (hDv.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (D x) (v x) =
        2 * ∫ x in U, vecDot (D x) (v x) := integral_const_mul 2 _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3]
  have hvar :
      -2 * (∫ x in U, vecDot (F x) (v x)) -
          ∫ x in U, vecDot (v x) (v x) ≤
        ∫ x in U, vecDot (D x) (D x) := by
    rw [hdistExp] at hdist
    linarith
  have hvF : IntegrableOn (fun x => vecDot (v x) (F x)) U :=
    integrableOn_vecDot_of_memVectorL2 hv hF
  have hfluxExp : ∫ x in U, vecDot (v x + F x) (v x + F x) =
      (∫ x in U, vecDot (v x) (v x)) +
        2 * (∫ x in U, vecDot (F x) (v x)) +
        ∫ x in U, vecDot (F x) (F x) := by
    have hpt : ∀ x, vecDot (v x + F x) (v x + F x) =
        vecDot (v x) (v x) + 2 * vecDot (v x) (F x) +
          vecDot (F x) (F x) := by
      intro x
      simp only [vecDot, Pi.add_apply]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        show (v x i + F x i) * (v x i + F x i) =
          v x i * v x i + 2 * (v x i * F x i) + F x i * F x i by ring,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∫ x in U, (vecDot (v x) (v x) +
          2 * vecDot (v x) (F x) + vecDot (F x) (F x)) =
        (∫ x in U, (vecDot (v x) (v x) + 2 * vecDot (v x) (F x))) +
          ∫ x in U, vecDot (F x) (F x) :=
      integral_add (hvv.add (hvF.const_mul 2)) hFF
    have h2 : ∫ x in U, (vecDot (v x) (v x) + 2 * vecDot (v x) (F x)) =
        (∫ x in U, vecDot (v x) (v x)) +
          ∫ x in U, 2 * vecDot (v x) (F x) :=
      integral_add hvv (hvF.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (v x) (F x) =
        2 * ∫ x in U, vecDot (v x) (F x) := integral_const_mul 2 _
    have h4 : ∫ x in U, vecDot (v x) (F x) =
        ∫ x in U, vecDot (F x) (v x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_comm _ _)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3, h4]
  rw [hfluxExp]
  linarith

/-- A finite Neumann corrector is bounded by every zero-normal solenoidal
competitor after subtracting the forcing. -/
theorem setIntegral_neumann_energy_le_flux_difference
    {d : ℕ} {U : Set (Vec d)} {N F J : Vec d → Vec d}
    (hN : MemVectorL2 U N) (hF : MemVectorL2 U F)
    (hJ : MemVectorL2 U J) (hNpot : IsPotentialOn U N)
    (hNsol : IsSolenoidalZeroNormalTraceOn U fun x => N x + F x)
    (hJsol : IsSolenoidalZeroNormalTraceOn U J) :
    (∫ x in U, vecDot (N x) (N x)) ≤
      ∫ x in U, vecDot (J x - F x) (J x - F x) := by
  have hW : MemVectorL2 U fun x => J x - F x := hJ.sub hF
  have hNN := integrableOn_vecDot_of_memVectorL2 hN hN
  have hFN := integrableOn_vecDot_of_memVectorL2 hF hN
  have hJN := integrableOn_vecDot_of_memVectorL2 hJ hN
  have hWN := integrableOn_vecDot_of_memVectorL2 hW hN
  have hWW := integrableOn_vecDot_of_memVectorL2 hW hW
  have hNself : (∫ x in U, vecDot (N x) (N x)) +
      ∫ x in U, vecDot (F x) (N x) = 0 := by
    have hsplit : ∫ x in U, vecDot (N x + F x) (N x) =
        (∫ x in U, vecDot (N x) (N x)) +
          ∫ x in U, vecDot (F x) (N x) := by
      rw [← integral_add hNN hFN]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)
    rw [← hsplit]
    exact setIntegral_vecDot_eq_zero_of_zeroNormal hNsol hNpot
  have hJzero : ∫ x in U, vecDot (J x) (N x) = 0 :=
    setIntegral_vecDot_eq_zero_of_zeroNormal hJsol hNpot
  have hpair : ∫ x in U, vecDot (J x - F x) (N x) =
      ∫ x in U, vecDot (N x) (N x) := by
    have hsplit : ∫ x in U, vecDot (J x - F x) (N x) =
        (∫ x in U, vecDot (J x) (N x)) -
          ∫ x in U, vecDot (F x) (N x) := by
      rw [← integral_sub hJN hFN]
      apply integral_congr_ae
      filter_upwards with x
      simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hsplit, hJzero]
    linarith
  have hdist : 0 ≤ ∫ x in U,
      vecDot (J x - F x - N x) (J x - F x - N x) :=
    integral_nonneg fun x => vecDot_self_nonneg_bridge _
  have hdistExp :
      (∫ x in U, vecDot (J x - F x - N x) (J x - F x - N x)) =
        (∫ x in U, vecDot (J x - F x) (J x - F x)) -
          2 * (∫ x in U, vecDot (J x - F x) (N x)) +
          ∫ x in U, vecDot (N x) (N x) := by
    have hpt : ∀ x, vecDot (J x - F x - N x) (J x - F x - N x) =
        vecDot (J x - F x) (J x - F x) -
          2 * vecDot (J x - F x) (N x) + vecDot (N x) (N x) :=
      fun x => vecDot_sub_self_bridge _ _
    have h1 : ∫ x in U, (vecDot (J x - F x) (J x - F x) -
          2 * vecDot (J x - F x) (N x) + vecDot (N x) (N x)) =
        (∫ x in U, (vecDot (J x - F x) (J x - F x) -
          2 * vecDot (J x - F x) (N x))) +
          ∫ x in U, vecDot (N x) (N x) :=
      integral_add (hWW.sub (hWN.const_mul 2)) hNN
    have h2 : ∫ x in U, (vecDot (J x - F x) (J x - F x) -
          2 * vecDot (J x - F x) (N x)) =
        (∫ x in U, vecDot (J x - F x) (J x - F x)) -
          ∫ x in U, 2 * vecDot (J x - F x) (N x) :=
      integral_sub hWW (hWN.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (J x - F x) (N x) =
        2 * ∫ x in U, vecDot (J x - F x) (N x) := integral_const_mul 2 _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3]
  rw [hdistExp, hpair] at hdist
  linarith

/-- The Dirichlet corrector has no more energy than the Neumann corrector for
the same forcing.  This is the fixed-realization middle inequality in the
Dirichlet--Neumann squeeze. -/
theorem setIntegral_dirichlet_energy_le_neumann_energy
    {d : ℕ} {U : Set (Vec d)} {D N F : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hN : MemVectorL2 U N)
    (hF : MemVectorL2 U F)
    (hDpot : IsPotentialZeroTraceOn U D)
    (hDsol : IsSolenoidalOn U fun x => D x + F x)
    (hNsol : IsSolenoidalZeroNormalTraceOn U fun x => N x + F x) :
    (∫ x in U, vecDot (D x) (D x)) ≤
      ∫ x in U, vecDot (N x) (N x) := by
  have hDD : IntegrableOn (fun x => vecDot (D x) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hD
  have hND : IntegrableOn (fun x => vecDot (N x) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 hN hD
  have hNN : IntegrableOn (fun x => vecDot (N x) (N x)) U :=
    integrableOn_vecDot_of_memVectorL2 hN hN
  have hFD : IntegrableOn (fun x => vecDot (F x) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hD
  have hDself : (∫ x in U, vecDot (D x) (D x)) +
      ∫ x in U, vecDot (F x) (D x) = 0 := by
    have hsplit : ∫ x in U, vecDot (D x + F x) (D x) =
        (∫ x in U, vecDot (D x) (D x)) +
          ∫ x in U, vecDot (F x) (D x) := by
      rw [← integral_add hDD hFD]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)
    rw [← hsplit]
    exact setIntegral_vecDot_eq_zero_of_solenoidal hDsol hDpot
  have hcross : (∫ x in U, vecDot (N x) (D x)) +
      ∫ x in U, vecDot (F x) (D x) = 0 := by
    have hsplit : ∫ x in U, vecDot (N x + F x) (D x) =
        (∫ x in U, vecDot (N x) (D x)) +
          ∫ x in U, vecDot (F x) (D x) := by
      rw [← integral_add hND hFD]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)
    rw [← hsplit]
    exact setIntegral_vecDot_eq_zero_of_zeroNormal hNsol
      (by
        obtain ⟨u, rfl⟩ := hDpot
        exact ⟨u.toH1Function, rfl⟩)
  have hdist : 0 ≤ ∫ x in U,
      vecDot (N x - D x) (N x - D x) :=
    integral_nonneg fun x => vecDot_self_nonneg_bridge _
  have hdistExp :
      (∫ x in U, vecDot (N x - D x) (N x - D x)) =
        (∫ x in U, vecDot (N x) (N x)) -
          2 * (∫ x in U, vecDot (N x) (D x)) +
          ∫ x in U, vecDot (D x) (D x) := by
    have hpt : ∀ x, vecDot (N x - D x) (N x - D x) =
        vecDot (N x) (N x) - 2 * vecDot (N x) (D x) +
          vecDot (D x) (D x) := fun x => vecDot_sub_self_bridge _ _
    have h1 : ∫ x in U, (vecDot (N x) (N x) -
          2 * vecDot (N x) (D x) + vecDot (D x) (D x)) =
        (∫ x in U, (vecDot (N x) (N x) -
          2 * vecDot (N x) (D x))) +
          ∫ x in U, vecDot (D x) (D x) :=
      integral_add (hNN.sub (hND.const_mul 2)) hDD
    have h2 : ∫ x in U, (vecDot (N x) (N x) -
          2 * vecDot (N x) (D x)) =
        (∫ x in U, vecDot (N x) (N x)) -
          ∫ x in U, 2 * vecDot (N x) (D x) :=
      integral_sub hNN (hND.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (N x) (D x) =
        2 * ∫ x in U, vecDot (N x) (D x) := integral_const_mul 2 _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3]
  rw [hdistExp] at hdist
  linarith

/-! ## Canonical finite energies -/

/-- Expected-normalized finite-cube Dirichlet corrector energy. -/
def oneStepDirichletCorrectorEnergy {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  (cubeVolume Q)⁻¹ *
    ‖(oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      |>.gradToHilbertVectorL2‖ ^ 2

/-- Expected-normalized finite-cube Neumann corrector energy. -/
def oneStepNeumannCorrectorEnergy {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  (cubeVolume Q)⁻¹ *
    ‖(oneStepTriadicNeumannSolution M n h p Q omega hh)
      |>.gradToHilbertVectorL2‖ ^ 2

private theorem norm_sq_gradToHilbertVectorL2_eq_setIntegral
    {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    ‖u.gradToHilbertVectorL2‖ ^ 2 =
      ∫ x in U, vecDot (u.grad x) (u.grad x) := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_toHilbertVectorL2OfVecField_eq_integral
    u.grad_memVectorL2 u.grad_memVectorL2

theorem oneStepDirichletCorrectorEnergy_eq_setIntegral
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) :
    oneStepDirichletCorrectorEnergy M n h p Q omega hh =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
        vecDot
          ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x)
          ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x) := by
  rw [oneStepDirichletCorrectorEnergy,
    norm_sq_gradToHilbertVectorL2_eq_setIntegral]

theorem oneStepNeumannCorrectorEnergy_eq_setIntegral
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) :
    oneStepNeumannCorrectorEnergy M n h p Q omega hh =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
        vecDot
          ((oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad x)
          ((oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad x) := by
  change (cubeVolume Q)⁻¹ *
      ‖(oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2‖ ^ 2 = _
  rw [norm_sq_gradToHilbertVectorL2_eq_setIntegral]

theorem integrable_oneStepDirichletCorrectorEnergy
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    Integrable (fun omega =>
      oneStepDirichletCorrectorEnergy M n h p Q omega hh) M.P.toMeasure := by
  have hgrad := memLp_two_oneStepTriadicDirichletGradL2
    M n h p Q hh hp
  have hint : Integrable (fun omega =>
      ‖(oneStepTriadicDirichletSolution M n h p Q omega hh)
        |>.gradToHilbertVectorL2‖ ^ 2)
      M.P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hgrad.1).1 hgrad
  exact (hint.const_mul (cubeVolume Q)⁻¹).congr
    (Filter.Eventually.of_forall fun omega => by
      simp only [oneStepDirichletCorrectorEnergy])

theorem integrable_oneStepNeumannCorrectorEnergy
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    Integrable (fun omega =>
      oneStepNeumannCorrectorEnergy M n h p Q omega hh) M.P.toMeasure := by
  have hgrad := memLp_two_oneStepTriadicNeumannGradL2
    M n h p Q hh hp
  have hint : Integrable (fun omega =>
      ‖(oneStepTriadicNeumannSolution M n h p Q omega hh)
        |>.gradToHilbertVectorL2‖ ^ 2)
      M.P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hgrad.1).1 hgrad
  exact (hint.const_mul (cubeVolume Q)⁻¹).congr
    (Filter.Eventually.of_forall fun omega => by
      simp only [oneStepNeumannCorrectorEnergy])

/-- Pointwise finite-cube ordering for the canonical measurable solution
operators. -/
theorem oneStepDirichletCorrectorEnergy_le_neumannCorrectorEnergy
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h) :
    oneStepDirichletCorrectorEnergy M n h p Q omega hh ≤
      oneStepNeumannCorrectorEnergy M n h p Q omega hh := by
  let D : Vec d → Vec d :=
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad
  let N : Vec d → Vec d :=
    (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad
  let F : Vec d → Vec d := fun x =>
    (realize (oneStepOriginForcing M n h p) omega x).toVec
  have hAdmD := oneStepTriadicDirichlet_admissible M n h p Q omega hh
  have hAdmN := oneStepTriadicNeumann_admissible M n h p Q omega hh
  have hD : MemVectorL2 (openCubeSet Q) D :=
    memVectorL2_of_isPotentialZeroTraceOn_bridge hAdmD.1
  have hN : MemVectorL2 (openCubeSet Q) N :=
    memVectorL2_of_isPotentialOn_bridge hAdmN.1
  have hF : MemVectorL2 (openCubeSet Q) F := by
    have hcont : Continuous (fun x => oneStepMultiplierAt M n h x omega • p) :=
      (continuous_oneStepMultiplierAt_sample M n h omega).smul continuous_const
    simpa only [F, realize_oneStepOriginForcing_toVec_eq] using
      memVectorL2_openCubeSet_of_continuous Q hcont
  have hcmp := setIntegral_dirichlet_energy_le_neumann_energy
    hD hN hF hAdmD.1 hAdmD.2 hAdmN.2
  rw [oneStepDirichletCorrectorEnergy_eq_setIntegral,
    oneStepNeumannCorrectorEnergy_eq_setIntegral]
  exact mul_le_mul_of_nonneg_left hcmp
    (inv_nonneg.2 (cubeVolume_pos Q).le)

/-- Expected finite-cube ordering. -/
theorem integral_oneStepDirichletCorrectorEnergy_le_neumannCorrectorEnergy
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    (∫ omega, oneStepDirichletCorrectorEnergy M n h p Q omega hh
        ∂M.P.toMeasure) ≤
      ∫ omega, oneStepNeumannCorrectorEnergy M n h p Q omega hh
        ∂M.P.toMeasure := by
  exact integral_mono
    (integrable_oneStepDirichletCorrectorEnergy M n h p Q hh hp)
    (integrable_oneStepNeumannCorrectorEnergy M n h p Q hh hp)
    (oneStepDirichletCorrectorEnergy_le_neumannCorrectorEnergy M n h p Q · hh)

/-! ## Young comparisons with the stationary Helmholtz fields -/

private theorem norm_sq_ofVec_bridge {d : ℕ} (v : Vec d) :
    ‖HilbertVec.ofVec v‖ ^ 2 = vecDot v v := by
  rw [← real_inner_self_eq_norm_sq, HilbertVec.inner_def,
    HilbertVec.toVec_ofVec]

private theorem normSq_add_le_young_bridge
    {E : Type*} [NormedAddCommGroup E]
    {delta : ℝ} (hdelta : 0 < delta) (a b : E) :
    ‖a + b‖ ^ 2 ≤
      (1 + delta) * ‖a‖ ^ 2 + (1 + delta⁻¹) * ‖b‖ ^ 2 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d200_normSq_add_le_young (E := E) (delta := delta) (hdelta := hdelta) (a := a) (b := b)

/-- Samplewise Dirichlet comparison after splitting the competitor flux into
the stationary solenoidal remainder and the localization error. -/
theorem oneStepDirichletCorrectorEnergy_ge_young
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h)
    {delta : ℝ} (hdelta : 0 < delta)
    (V : Vec d → Vec d)
    (hVpot : IsPotentialZeroTraceOn (openCubeSet Q) V)
    (hFomega : MemHilbertVectorL2 (cubeSet Q)
      (realize (oneStepOriginForcing M n h p) omega))
    (hPomega : MemHilbertVectorL2 (cubeSet Q)
      (realize (stationaryVectorRepresentative M
        (oneStepPotentialProjection M n h p hh)) omega)) :
    cubeAverage Q (fun x =>
        ‖realize (oneStepOriginForcing M n h p) omega x‖ ^ 2) -
      (1 + delta) * cubeAverage Q (fun x =>
        ‖realize (fun omega' =>
          oneStepOriginForcing M n h p omega' -
            stationaryVectorRepresentative M
              (oneStepPotentialProjection M n h p hh) omega') omega x‖ ^ 2) -
      (1 + delta⁻¹) * cubeAverage Q (fun x =>
        ‖HilbertVec.ofVec (V x) -
          realize (stationaryVectorRepresentative M
            (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2) ≤
      oneStepDirichletCorrectorEnergy M n h p Q omega hh := by
  let F := oneStepOriginForcing M n h p
  let P := stationaryVectorRepresentative M
    (oneStepPotentialProjection M n h p hh)
  let R : Sample d → HilbertVec d := fun omega' => F omega' - P omega'
  let D : Vec d → Vec d :=
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad
  have hres : volume.restrict (cubeSet Q) =
      volume.restrict (openCubeSet Q) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hFU : MemHilbertVectorL2 (openCubeSet Q) (realize F omega) := by
    change MemLp (realize F omega) 2
      (volume.restrict (openCubeSet Q))
    rw [← hres]
    exact hFomega
  have hPU : MemHilbertVectorL2 (openCubeSet Q) (realize P omega) := by
    change MemLp (realize P omega) 2
      (volume.restrict (openCubeSet Q))
    rw [← hres]
    exact hPomega
  have hRU : MemHilbertVectorL2 (openCubeSet Q) (realize R omega) := by
    have heq : (realize R omega : Vec d → HilbertVec d) =
        fun x => realize F omega x - realize P omega x := by
      funext x
      rfl
    rw [heq]
    exact hFU.sub hPU
  have hVU : MemVectorL2 (openCubeSet Q) V :=
    memVectorL2_of_isPotentialZeroTraceOn_bridge hVpot
  have hnegVpot : IsPotentialZeroTraceOn (openCubeSet Q) (fun x => -V x) := by
    obtain ⟨u, hu⟩ := hVpot
    refine ⟨-u, ?_⟩
    funext x
    change (-u.toH1Function).grad x = -V x
    rw [H1Function.neg_grad]
    exact congrArg Neg.neg (congrFun hu x)
  have hAdmD := oneStepTriadicDirichlet_admissible M n h p Q omega hh
  have hDU : MemVectorL2 (openCubeSet Q) D :=
    memVectorL2_of_isPotentialZeroTraceOn_bridge hAdmD.1
  have hFvec : MemVectorL2 (openCubeSet Q)
      (fun x => (realize F omega x).toVec) := by
    simpa using ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
      |>.comp_memLp' hFU)
  have hcmp := setIntegral_dirichlet_energy_ge_flux_difference
    hDU hFvec hVU.neg (by simpa only [D, F] using hAdmD.2) hnegVpot
  have hErrU : MemHilbertVectorL2 (openCubeSet Q) (fun x =>
      HilbertVec.ofVec (V x) - realize P omega x) :=
    (memHilbertVectorL2_hilbertifyVecField hVU).sub hPU
  have hRint : IntegrableOn (fun x => ‖realize R omega x‖ ^ 2)
      (openCubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hRU.aestronglyMeasurable).1 hRU
  have hEint : IntegrableOn (fun x =>
      ‖HilbertVec.ofVec (V x) - realize P omega x‖ ^ 2)
      (openCubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hErrU.aestronglyMeasurable).1 hErrU
  have hyoung : ∫ x in openCubeSet Q,
        vecDot (-V x + (realize F omega x).toVec)
          (-V x + (realize F omega x).toVec) ≤
      (1 + delta) * (∫ x in openCubeSet Q, ‖realize R omega x‖ ^ 2) +
        (1 + delta⁻¹) * (∫ x in openCubeSet Q,
          ‖HilbertVec.ofVec (V x) - realize P omega x‖ ^ 2) := by
    have hlhs : IntegrableOn (fun x =>
        vecDot (-V x + (realize F omega x).toVec)
          (-V x + (realize F omega x).toVec)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 (hVU.neg.add hFvec)
        (hVU.neg.add hFvec)
    have hrhs := (hRint.const_mul (1 + delta)).add
      (hEint.const_mul (1 + delta⁻¹))
    have hmono := integral_mono hlhs hrhs (fun x => by
      rw [← norm_sq_ofVec_bridge]
      have hsplit : HilbertVec.ofVec
          (-V x + (realize F omega x).toVec) =
          realize R omega x -
            (HilbertVec.ofVec (V x) - realize P omega x) := by
        change -HilbertVec.ofVec (V x) + realize F omega x = _
        dsimp only [R]
        simp only [realize_apply]
        abel
      rw [hsplit, sub_eq_add_neg]
      simpa only [Pi.add_apply, norm_neg] using
        (normSq_add_le_young_bridge hdelta (realize R omega x)
          (-(HilbertVec.ofVec (V x) - realize P omega x))))
    refine hmono.trans (le_of_eq ?_)
    have hadd := integral_add (hRint.const_mul (1 + delta))
      (hEint.const_mul (1 + delta⁻¹))
    rw [integral_const_mul, integral_const_mul] at hadd
    simpa only [Pi.add_apply] using hadd
  have hvol : 0 < (cubeVolume Q)⁻¹ := inv_pos.2 (cubeVolume_pos Q)
  rw [oneStepDirichletCorrectorEnergy_eq_setIntegral]
  have hscaledCmp := mul_le_mul_of_nonneg_left hcmp hvol.le
  have hscaledYoung := mul_le_mul_of_nonneg_left hyoung hvol.le
  have hFdot : (∫ x in openCubeSet Q,
      vecDot (realize F omega x).toVec (realize F omega x).toVec) =
      ∫ x in openCubeSet Q, ‖realize F omega x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    exact (HilbertVec.inner_def _ _).symm.trans
      (real_inner_self_eq_norm_sq _)
  rw [hFdot] at hscaledCmp
  simp only [Pi.neg_apply] at hscaledCmp
  simp only [cubeAverage]
  rw [hres]
  dsimp only [D, F, P, R] at hscaledCmp hscaledYoung ⊢
  ring_nf at hscaledCmp hscaledYoung ⊢
  nlinarith

/-- Samplewise Neumann comparison after splitting the admissible localized
flux into the stationary solenoidal representative and its localization
error. -/
theorem oneStepNeumannCorrectorEnergy_le_young
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : Sample d) (hh : 0 < h)
    {delta : ℝ} (hdelta : 0 < delta)
    (J : Vec d → Vec d)
    (hJsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) J)
    (hFomega : MemHilbertVectorL2 (cubeSet Q)
      (realize (oneStepOriginForcing M n h p) omega))
    (hRomega : MemHilbertVectorL2 (cubeSet Q)
      (realize (stationaryVectorRepresentative M
        (oneStepOriginForcingL2 M n h p hh -
          oneStepPotentialProjection M n h p hh)) omega))
    (hErromega : MemHilbertVectorL2 (cubeSet Q) (fun x =>
      HilbertVec.ofVec (J x) -
        realize (stationaryVectorRepresentative M
          (oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh)) omega x)) :
    oneStepNeumannCorrectorEnergy M n h p Q omega hh ≤
      (1 + delta) * cubeAverage Q (fun x =>
        ‖realize (fun omega' =>
          stationaryVectorRepresentative M
              (oneStepOriginForcingL2 M n h p hh -
                oneStepPotentialProjection M n h p hh) omega' -
            oneStepOriginForcing M n h p omega') omega x‖ ^ 2) +
      (1 + delta⁻¹) * cubeAverage Q (fun x =>
        ‖HilbertVec.ofVec (J x) -
          realize (stationaryVectorRepresentative M
            (oneStepOriginForcingL2 M n h p hh -
              oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2) := by
  let F := oneStepOriginForcing M n h p
  let R := stationaryVectorRepresentative M
    (oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh)
  let A : Sample d → HilbertVec d := fun omega' => R omega' - F omega'
  let N : Vec d → Vec d :=
    (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad
  have hres : volume.restrict (cubeSet Q) =
      volume.restrict (openCubeSet Q) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hFU : MemHilbertVectorL2 (openCubeSet Q) (realize F omega) := by
    change MemLp (realize F omega) 2 (volume.restrict (openCubeSet Q))
    rw [← hres]
    exact hFomega
  have hRU : MemHilbertVectorL2 (openCubeSet Q) (realize R omega) := by
    change MemLp (realize R omega) 2 (volume.restrict (openCubeSet Q))
    rw [← hres]
    exact hRomega
  have hAU : MemHilbertVectorL2 (openCubeSet Q) (realize A omega) := by
    have heq : (realize A omega : Vec d → HilbertVec d) =
        fun x => realize R omega x - realize F omega x := by
      funext x
      rfl
    rw [heq]
    exact hRU.sub hFU
  have hAdmN := oneStepTriadicNeumann_admissible M n h p Q omega hh
  have hNU : MemVectorL2 (openCubeSet Q) N :=
    memVectorL2_of_isPotentialOn_bridge hAdmN.1
  have hFvec : MemVectorL2 (openCubeSet Q)
      (fun x => (realize F omega x).toVec) := by
    simpa using ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
      |>.comp_memLp' hFU)
  have hJU : MemVectorL2 (openCubeSet Q) J := by
    have hErr : MemHilbertVectorL2 (openCubeSet Q) (fun x =>
        HilbertVec.ofVec (J x) - realize R omega x) := by
      change MemLp (fun x => HilbertVec.ofVec (J x) - realize R omega x) 2
        (volume.restrict (openCubeSet Q))
      rw [← hres]
      exact hErromega
    have hconverted :=
      (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
        |>.comp_memLp' (hErr.add hRU)
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp) hconverted
  have hcmp := setIntegral_neumann_energy_le_flux_difference
    hNU hFvec hJU hAdmN.1 (by simpa only [N, F] using hAdmN.2) hJsol
  have hErrU : MemHilbertVectorL2 (openCubeSet Q) (fun x =>
      HilbertVec.ofVec (J x) - realize R omega x) :=
    (memHilbertVectorL2_hilbertifyVecField hJU).sub hRU
  have hAint : IntegrableOn (fun x => ‖realize A omega x‖ ^ 2)
      (openCubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hAU.aestronglyMeasurable).1 hAU
  have hEint : IntegrableOn (fun x =>
      ‖HilbertVec.ofVec (J x) - realize R omega x‖ ^ 2)
      (openCubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hErrU.aestronglyMeasurable).1 hErrU
  have hyoung : (∫ x in openCubeSet Q,
        vecDot (J x - (realize F omega x).toVec)
          (J x - (realize F omega x).toVec)) ≤
      (1 + delta) * (∫ x in openCubeSet Q, ‖realize A omega x‖ ^ 2) +
        (1 + delta⁻¹) * (∫ x in openCubeSet Q,
          ‖HilbertVec.ofVec (J x) - realize R omega x‖ ^ 2) := by
    have hlhs : IntegrableOn (fun x =>
        vecDot (J x - (realize F omega x).toVec)
          (J x - (realize F omega x).toVec)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 (hJU.sub hFvec) (hJU.sub hFvec)
    have hrhs := (hAint.const_mul (1 + delta)).add
      (hEint.const_mul (1 + delta⁻¹))
    have hmono := integral_mono hlhs hrhs (fun x => by
      rw [← norm_sq_ofVec_bridge]
      have hsplit : HilbertVec.ofVec
          (J x - (realize F omega x).toVec) =
          realize A omega x +
            (HilbertVec.ofVec (J x) - realize R omega x) := by
        change HilbertVec.ofVec (J x) - realize F omega x = _
        dsimp only [A]
        simp only [realize_apply]
        abel
      rw [hsplit]
      simpa only [Pi.add_apply] using
        (normSq_add_le_young_bridge hdelta (realize A omega x)
          (HilbertVec.ofVec (J x) - realize R omega x)))
    refine hmono.trans (le_of_eq ?_)
    have hadd := integral_add (hAint.const_mul (1 + delta))
      (hEint.const_mul (1 + delta⁻¹))
    rw [integral_const_mul, integral_const_mul] at hadd
    simpa only [Pi.add_apply] using hadd
  rw [oneStepNeumannCorrectorEnergy_eq_setIntegral]
  have hvol : 0 < (cubeVolume Q)⁻¹ := inv_pos.2 (cubeVolume_pos Q)
  have hscaledCmp := mul_le_mul_of_nonneg_left hcmp hvol.le
  have hscaledYoung := mul_le_mul_of_nonneg_left hyoung hvol.le
  simp only [cubeAverage]
  rw [hres]
  dsimp only [N, F, R, A] at hscaledCmp hscaledYoung ⊢
  ring_nf at hscaledCmp hscaledYoung ⊢
  exact hscaledCmp.trans hscaledYoung

/-! ## Expected finite-cube bounds -/

/-- Expected Dirichlet energy is bounded from below by the stationary
projected energy, modulo the explicit localization error. -/
theorem integral_oneStepDirichletCorrectorEnergy_ge_projected_sub_error
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hp : vecNormSq p = 1) {delta : ℝ} (hdelta : 0 < delta)
    (V : Sample d → Vec d → Vec d)
    (hVpot : ∀ᵐ omega ∂M.P.toMeasure,
      IsPotentialZeroTraceOn (openCubeSet Q) (V omega))
    (hVint : Integrable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (V omega x) -
        realize (stationaryVectorRepresentative M
          (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
      M.P.toMeasure) :
    oneStepProjectedEnergy M n h p hh -
        delta * ‖oneStepOriginForcingL2 M n h p hh -
          oneStepPotentialProjection M n h p hh‖ ^ 2 -
        (1 + delta⁻¹) * (cubeVolume Q)⁻¹ *
          (∫ omega, (∫ x in cubeSet Q,
            ‖HilbertVec.ofVec (V omega x) -
              realize (stationaryVectorRepresentative M
                (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
            ∂M.P.toMeasure) ≤
      ∫ omega, oneStepDirichletCorrectorEnergy M n h p Q omega hh
        ∂M.P.toMeasure := by
  let F := oneStepOriginForcing M n h p
  let P := stationaryVectorRepresentative M
    (oneStepPotentialProjection M n h p hh)
  let R : Sample d → HilbertVec d := fun omega => F omega - P omega
  let A : Sample d → ℝ := fun omega => cubeAverage Q
    (fun x => ‖realize F omega x‖ ^ 2)
  let B : Sample d → ℝ := fun omega => cubeAverage Q
    (fun x => ‖realize R omega x‖ ^ 2)
  let E : Sample d → ℝ := fun omega => cubeAverage Q
    (fun x => ‖HilbertVec.ofVec (V omega x) - realize P omega x‖ ^ 2)
  let D : Sample d → ℝ := fun omega =>
    oneStepDirichletCorrectorEnergy M n h p Q omega hh
  have hFm : StronglyMeasurable F :=
    (measurable_oneStepOriginForcing M n h p).stronglyMeasurable
  have hF : MemLp F 2 M.P.toMeasure :=
    memLp_two_oneStepOriginForcing M n h p hh
  have hPm : StronglyMeasurable P :=
    stronglyMeasurable_stationaryVectorRepresentative M _
  have hP : MemLp P 2 M.P.toMeasure :=
    memLp_two_stationaryVectorRepresentative M _
  have hRm : StronglyMeasurable R := hFm.sub hPm
  have hR : MemLp R 2 M.P.toMeasure := hF.sub hP
  have hAfin : Integrable A M.P.toMeasure := by
    have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
    simpa only [A, cubeAverage] using
      (integrable_setIntegral_normSq_realize M hQfin hFm hF).const_mul
        (cubeVolume Q)⁻¹
  have hBfin : Integrable B M.P.toMeasure := by
    have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
    simpa only [B, cubeAverage] using
      (integrable_setIntegral_normSq_realize M hQfin hRm hR).const_mul
        (cubeVolume Q)⁻¹
  have hEfin : Integrable E M.P.toMeasure := by
    have hscaled := hVint.const_mul (cubeVolume Q)⁻¹
    exact hscaled.congr (Filter.Eventually.of_forall fun omega => by
      simp only [E, cubeAverage, P])
  have hDfin : Integrable D M.P.toMeasure :=
    integrable_oneStepDirichletCorrectorEnergy M n h p Q hh hp
  have hae : ∀ᵐ omega ∂M.P.toMeasure,
      A omega - (1 + delta) * B omega - (1 + delta⁻¹) * E omega ≤
        D omega := by
    have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
    filter_upwards [hVpot,
      ae_memLp_two_realize M hQfin hFm hF,
      ae_memLp_two_realize M hQfin hPm hP] with omega hpot hFomega hPomega
    simpa only [A, B, E, D, F, P, R] using
      oneStepDirichletCorrectorEnergy_ge_young
        M n h p Q omega hh hdelta (V omega) hpot hFomega hPomega
  have hmono : ∫ omega,
      (A omega - (1 + delta) * B omega - (1 + delta⁻¹) * E omega)
        ∂M.P.toMeasure ≤ ∫ omega, D omega ∂M.P.toMeasure :=
    integral_mono_ae
      ((hAfin.sub (hBfin.const_mul (1 + delta))).sub
        (hEfin.const_mul (1 + delta⁻¹))) hDfin hae
  have hsplit : ∫ omega,
      (A omega - (1 + delta) * B omega - (1 + delta⁻¹) * E omega)
        ∂M.P.toMeasure =
      (∫ omega, A omega ∂M.P.toMeasure) -
        (1 + delta) * (∫ omega, B omega ∂M.P.toMeasure) -
        (1 + delta⁻¹) * ∫ omega, E omega ∂M.P.toMeasure := by
    calc
      _ = (∫ omega, A omega - (1 + delta) * B omega ∂M.P.toMeasure) -
          ∫ omega, (1 + delta⁻¹) * E omega ∂M.P.toMeasure := by
        simpa only [Pi.sub_apply] using
          integral_sub (hAfin.sub (hBfin.const_mul (1 + delta)))
            (hEfin.const_mul (1 + delta⁻¹))
      _ = ((∫ omega, A omega ∂M.P.toMeasure) -
            ∫ omega, (1 + delta) * B omega ∂M.P.toMeasure) -
          ∫ omega, (1 + delta⁻¹) * E omega ∂M.P.toMeasure := by
        rw [integral_sub hAfin (hBfin.const_mul (1 + delta))]
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  rw [hsplit] at hmono
  have hAeq : ∫ omega, A omega ∂M.P.toMeasure =
      ∫ omega, ‖F omega‖ ^ 2 ∂M.P.toMeasure :=
    integral_cubeAverage_normSq_realize M Q hFm hF
  have hBeq : ∫ omega, B omega ∂M.P.toMeasure =
      ∫ omega, ‖R omega‖ ^ 2 ∂M.P.toMeasure :=
    integral_cubeAverage_normSq_realize M Q hRm hR
  have hEeq : ∫ omega, E omega ∂M.P.toMeasure =
      (cubeVolume Q)⁻¹ * (∫ omega, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (V omega x) - realize P omega x‖ ^ 2)
        ∂M.P.toMeasure) := by
    dsimp only [E, cubeAverage]
    rw [integral_const_mul]
  rw [hAeq, hBeq, hEeq] at hmono
  have hFclass : hF.toLp F = oneStepOriginForcingL2 M n h p hh := rfl
  have hPclass : hP.toLp P = oneStepPotentialProjection M n h p hh :=
    toLp_stationaryVectorRepresentative M _
  have hAnorm : ∫ omega, ‖F omega‖ ^ 2 ∂M.P.toMeasure =
      ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 := by
    rw [integral_normSq_eq_norm_sq_toLp hF, hFclass]
  have hBnorm : ∫ omega, ‖R omega‖ ^ 2 ∂M.P.toMeasure =
      ‖oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh‖ ^ 2 := by
    dsimp only [R]
    rw [integral_normSq_sub_eq_norm_sq_toLp hF hP, hFclass, hPclass]
  rw [hAnorm, hBnorm] at hmono
  have hhelm : ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 -
      ‖oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh‖ ^ 2 =
      oneStepProjectedEnergy M n h p hh := by
    have hpyth := oneStepProjectedEnergy_add_solenoidalRemainder_eq_suffixVariance
      M n h p hh hp
    have hforcing := norm_oneStepOriginForcingL2_sq M n h p hh
    rw [hp, mul_one] at hforcing
    linarith
  dsimp only [D, P] at hmono
  rw [← hhelm]
  linarith

/-- Expected Neumann energy is bounded from above by the stationary projected
energy, modulo the explicit solenoidal localization error. -/
theorem integral_oneStepNeumannCorrectorEnergy_le_projected_add_error
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (hp : vecNormSq p = 1) {delta : ℝ} (hdelta : 0 < delta)
    (J : Sample d → Vec d → Vec d)
    (hJsol : ∀ᵐ omega ∂M.P.toMeasure,
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (J omega))
    (hJmem : ∀ᵐ omega ∂M.P.toMeasure,
      MemHilbertVectorL2 (cubeSet Q) (fun x =>
        HilbertVec.ofVec (J omega x) -
          realize (stationaryVectorRepresentative M
            (oneStepOriginForcingL2 M n h p hh -
              oneStepPotentialProjection M n h p hh)) omega x))
    (hJint : Integrable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (J omega x) -
        realize (stationaryVectorRepresentative M
          (oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
      M.P.toMeasure) :
    (∫ omega, oneStepNeumannCorrectorEnergy M n h p Q omega hh
        ∂M.P.toMeasure) ≤
      (1 + delta) * oneStepProjectedEnergy M n h p hh +
        (1 + delta⁻¹) * (cubeVolume Q)⁻¹ *
          (∫ omega, (∫ x in cubeSet Q,
            ‖HilbertVec.ofVec (J omega x) -
              realize (stationaryVectorRepresentative M
                (oneStepOriginForcingL2 M n h p hh -
                  oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
            ∂M.P.toMeasure) := by
  let F := oneStepOriginForcing M n h p
  let R := stationaryVectorRepresentative M
    (oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh)
  let A : Sample d → HilbertVec d := fun omega => R omega - F omega
  let B : Sample d → ℝ := fun omega => cubeAverage Q
    (fun x => ‖realize A omega x‖ ^ 2)
  let E : Sample d → ℝ := fun omega => cubeAverage Q
    (fun x => ‖HilbertVec.ofVec (J omega x) - realize R omega x‖ ^ 2)
  let N : Sample d → ℝ := fun omega =>
    oneStepNeumannCorrectorEnergy M n h p Q omega hh
  have hFm : StronglyMeasurable F :=
    (measurable_oneStepOriginForcing M n h p).stronglyMeasurable
  have hF : MemLp F 2 M.P.toMeasure :=
    memLp_two_oneStepOriginForcing M n h p hh
  have hRm : StronglyMeasurable R :=
    stronglyMeasurable_stationaryVectorRepresentative M _
  have hR : MemLp R 2 M.P.toMeasure :=
    memLp_two_stationaryVectorRepresentative M _
  have hAm : StronglyMeasurable A := hRm.sub hFm
  have hA : MemLp A 2 M.P.toMeasure := hR.sub hF
  have hBfin : Integrable B M.P.toMeasure := by
    have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
    simpa only [B, cubeAverage] using
      (integrable_setIntegral_normSq_realize M hQfin hAm hA).const_mul
        (cubeVolume Q)⁻¹
  have hEfin : Integrable E M.P.toMeasure := by
    exact (hJint.const_mul (cubeVolume Q)⁻¹).congr
      (Filter.Eventually.of_forall fun omega => by
        simp only [E, cubeAverage, R])
  have hNfin : Integrable N M.P.toMeasure :=
    integrable_oneStepNeumannCorrectorEnergy M n h p Q hh hp
  have hae : ∀ᵐ omega ∂M.P.toMeasure,
      N omega ≤ (1 + delta) * B omega + (1 + delta⁻¹) * E omega := by
    have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
    filter_upwards [hJsol, hJmem,
      ae_memLp_two_realize M hQfin hFm hF,
      ae_memLp_two_realize M hQfin hRm hR]
      with omega hsol hmem hFomega hRomega
    simpa only [N, B, E, F, R, A] using
      oneStepNeumannCorrectorEnergy_le_young
        M n h p Q omega hh hdelta (J omega) hsol hFomega hRomega hmem
  have hmono : ∫ omega, N omega ∂M.P.toMeasure ≤
      ∫ omega, ((1 + delta) * B omega + (1 + delta⁻¹) * E omega)
        ∂M.P.toMeasure :=
    integral_mono_ae hNfin
      ((hBfin.const_mul (1 + delta)).add
        (hEfin.const_mul (1 + delta⁻¹))) hae
  have hsplit : ∫ omega,
      ((1 + delta) * B omega + (1 + delta⁻¹) * E omega)
        ∂M.P.toMeasure =
      (1 + delta) * (∫ omega, B omega ∂M.P.toMeasure) +
        (1 + delta⁻¹) * ∫ omega, E omega ∂M.P.toMeasure := by
    have hadd := integral_add (hBfin.const_mul (1 + delta))
      (hEfin.const_mul (1 + delta⁻¹))
    rw [integral_const_mul, integral_const_mul] at hadd
    simpa only [Pi.add_apply] using hadd
  rw [hsplit] at hmono
  have hBeq : ∫ omega, B omega ∂M.P.toMeasure =
      ∫ omega, ‖A omega‖ ^ 2 ∂M.P.toMeasure :=
    integral_cubeAverage_normSq_realize M Q hAm hA
  have hEeq : ∫ omega, E omega ∂M.P.toMeasure =
      (cubeVolume Q)⁻¹ * (∫ omega, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (J omega x) - realize R omega x‖ ^ 2)
        ∂M.P.toMeasure) := by
    dsimp only [E, cubeAverage]
    rw [integral_const_mul]
  rw [hBeq, hEeq] at hmono
  have hFclass : hF.toLp F = oneStepOriginForcingL2 M n h p hh := rfl
  have hRclass : hR.toLp R = oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh :=
    toLp_stationaryVectorRepresentative M _
  have hAnorm : ∫ omega, ‖A omega‖ ^ 2 ∂M.P.toMeasure =
      oneStepProjectedEnergy M n h p hh := by
    dsimp only [A]
    rw [integral_normSq_sub_eq_norm_sq_toLp hR hF, hRclass, hFclass]
    change ‖(oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh) -
        oneStepOriginForcingL2 M n h p hh‖ ^ 2 = _
    have heq : (oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh) -
          oneStepOriginForcingL2 M n h p hh =
        -oneStepPotentialProjection M n h p hh := by abel
    rw [heq, norm_neg]
    rfl
  rw [hAnorm] at hmono
  dsimp only [N, R] at hmono
  rw [← mul_assoc] at hmono
  exact hmono

/-! ## Thermodynamic squeeze -/

private theorem exists_three_zpow_neg_mul_le_bridge
    (D A c : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ L : ℕ, D * (3 : ℝ) ^ (-(L : ℤ)) * A ≤ c := by
  have hpos : 0 < D * A + 1 := by positivity
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one
    (show 0 < c / (D * A + 1) by positivity)
    (show (3 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨L, ?_⟩
  have hzp : (3 : ℝ) ^ (-(L : ℤ)) = ((3 : ℝ)⁻¹) ^ L := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hzp]
  have hDA : 0 ≤ D * A := mul_nonneg hD hA
  have hstep : D * A * ((3 : ℝ)⁻¹) ^ L ≤
      D * A * (c / (D * A + 1)) :=
    mul_le_mul_of_nonneg_left hL.le hDA
  have hlast : D * A * (c / (D * A + 1)) ≤ c := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith [hc.le, hDA]
  nlinarith

private theorem tendsto_of_eventually_sandwich_bridge
    {u v : ℕ → ℝ} {a : ℝ}
    (huv : ∀ K, u K ≤ v K)
    (hlow : ∀ epsilon, 0 < epsilon →
      ∀ᶠ K in Filter.atTop, a - epsilon ≤ u K)
    (hhigh : ∀ epsilon, 0 < epsilon →
      ∀ᶠ K in Filter.atTop, v K ≤ a + epsilon) :
    Filter.Tendsto u Filter.atTop (nhds a) ∧
      Filter.Tendsto v Filter.atTop (nhds a) := by
  have hclose : ∀ epsilon, 0 < epsilon →
      ∀ᶠ K in Filter.atTop,
        |u K - a| ≤ epsilon ∧ |v K - a| ≤ epsilon := by
    intro epsilon hepsilon
    filter_upwards [hlow epsilon hepsilon, hhigh epsilon hepsilon]
      with K hlo hhi
    have hord := huv K
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  constructor
  · refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      (hclose (epsilon / 2) (by linarith))
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hK k hk).1 (by linarith)
  · refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      (hclose (epsilon / 2) (by linarith))
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hK k hk).2 (by linarith)

/-- The expected normalized Dirichlet and Neumann shell-corrector energies
both converge to the already constructed stationary Helmholtz projected
energy. -/
theorem tendsto_integral_oneStepCorrectorEnergies_originCube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    Filter.Tendsto (fun K : ℕ =>
      ∫ omega, oneStepDirichletCorrectorEnergy M n h p
        (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure)
      Filter.atTop (nhds (oneStepProjectedEnergy M n h p hh)) ∧
    Filter.Tendsto (fun K : ℕ =>
      ∫ omega, oneStepNeumannCorrectorEnergy M n h p
        (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure)
      Filter.atTop (nhds (oneStepProjectedEnergy M n h p hh)) := by
  let PE : ℝ := oneStepProjectedEnergy M n h p hh
  let RE : ℝ := ‖oneStepOriginForcingL2 M n h p hh -
    oneStepPotentialProjection M n h p hh‖ ^ 2
  let Dseq : ℕ → ℝ := fun K =>
    ∫ omega, oneStepDirichletCorrectorEnergy M n h p
      (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure
  let Nseq : ℕ → ℝ := fun K =>
    ∫ omega, oneStepNeumannCorrectorEnergy M n h p
      (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure
  have hPE0 : 0 ≤ PE := oneStepProjectedEnergy_nonneg M n h p hh
  have hRE0 : 0 ≤ RE := sq_nonneg _
  have horder : ∀ K, Dseq K ≤ Nseq K := by
    intro K
    exact integral_oneStepDirichletCorrectorEnergy_le_neumannCorrectorEnergy
      M n h p (originCube d (K : ℤ)) hh hp
  apply tendsto_of_eventually_sandwich_bridge horder
  · intro epsilon hepsilon
    let delta : ℝ := min 1 (epsilon / (3 * (RE + 1)))
    have hdelta : 0 < delta := lt_min one_pos (by positivity)
    have hdeltaRE : delta * RE ≤ epsilon / 3 := by
      have hle : delta ≤ epsilon / (3 * (RE + 1)) := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_right hle hRE0
      have hfinal : epsilon / (3 * (RE + 1)) * RE ≤ epsilon / 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hepsilon.le, hRE0]
      exact hmul.trans hfinal
    let theta : ℝ := epsilon / (3 * (1 + delta⁻¹))
    have htheta : 0 < theta := by positivity
    have hthetaMul : (1 + delta⁻¹) * theta = epsilon / 3 := by
      dsimp only [theta]
      field_simp
    obtain ⟨L, hL⟩ := exists_three_zpow_neg_mul_le_bridge
      (d : ℝ) PE (theta / 3) (Nat.cast_nonneg d) hPE0 (by positivity)
    obtain ⟨V, g, hg0, hgtend, hVpot, hVint, hVbd⟩ :=
      exists_oneStepPotentialProjection_zeroTrace_family_bound
        M n h p hh L (show 0 < theta / 3 by positivity)
    have hgev : ∀ᶠ K : ℕ in Filter.atTop, g K < theta / 3 :=
      Filter.Tendsto.eventually_lt_const (show 0 < theta / 3 by positivity)
        hgtend
    filter_upwards [hgev] with K hgK
    have hmain :=
      integral_oneStepDirichletCorrectorEnergy_ge_projected_sub_error
        M n h p (originCube d (K : ℤ)) hh hp hdelta (V K)
          (hVpot K) (hVint K)
    have herr : (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        (∫ omega, (∫ x in cubeSet (originCube d (K : ℤ)),
          ‖HilbertVec.ofVec (V K omega x) -
            realize (stationaryVectorRepresentative M
              (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
          ∂M.P.toMeasure) ≤ theta := by
      have hb := hVbd K
      dsimp only [PE, oneStepProjectedEnergy] at hL
      linarith
    have hscaled := mul_le_mul_of_nonneg_left herr
      (show 0 ≤ 1 + delta⁻¹ by positivity)
    dsimp only [Dseq, PE, RE]
    dsimp only [PE, RE] at hmain hdeltaRE
    rw [hthetaMul] at hscaled
    linarith
  · intro epsilon hepsilon
    let delta : ℝ := min 1 (epsilon / (3 * (PE + 1)))
    have hdelta : 0 < delta := lt_min one_pos (by positivity)
    have hdeltaPE : delta * PE ≤ epsilon / 3 := by
      have hle : delta ≤ epsilon / (3 * (PE + 1)) := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_right hle hPE0
      have hfinal : epsilon / (3 * (PE + 1)) * PE ≤ epsilon / 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hepsilon.le, hPE0]
      exact hmul.trans hfinal
    let theta : ℝ := epsilon / (3 * (1 + delta⁻¹))
    have htheta : 0 < theta := by positivity
    have hthetaMul : (1 + delta⁻¹) * theta = epsilon / 3 := by
      dsimp only [theta]
      field_simp
    obtain ⟨L, hL⟩ := exists_three_zpow_neg_mul_le_bridge
      (2 * (d : ℝ)) ((‖oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh‖ + 1) ^ 2)
      (theta / 3) (by positivity) (sq_nonneg _) (by positivity)
    obtain ⟨J, g, hg0, hgtend, hJsol, hJint, hJmem, hJbd⟩ :=
      exists_oneStepSolenoidalZeroNormal_family_bound
        M n h p hh L (show 0 < theta / 3 by positivity)
    have hgev : ∀ᶠ K : ℕ in Filter.atTop, g K < theta / 3 :=
      Filter.Tendsto.eventually_lt_const (show 0 < theta / 3 by positivity)
        hgtend
    filter_upwards [hgev] with K hgK
    have hmain :=
      integral_oneStepNeumannCorrectorEnergy_le_projected_add_error
        M n h p (originCube d (K : ℤ)) hh hp hdelta (J K)
          (hJsol K) (hJmem K) (hJint K)
    have herr : (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        (∫ omega, (∫ x in cubeSet (originCube d (K : ℤ)),
          ‖HilbertVec.ofVec (J K omega x) -
            realize (stationaryVectorRepresentative M
              (oneStepOriginForcingL2 M n h p hh -
                oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
          ∂M.P.toMeasure) ≤ theta := by
      have hb := hJbd K
      have hL' : 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (‖oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh‖ + 1) ^ 2) ≤
          theta / 3 := by
        nlinarith [hL]
      linarith
    have hscaled := mul_le_mul_of_nonneg_left herr
      (show 0 ≤ 1 + delta⁻¹ by positivity)
    dsimp only [Nseq, PE]
    dsimp only [PE] at hmain hdeltaPE
    rw [hthetaMul] at hscaled
    linarith

/-! ## Signed principal factors -/



theorem tendsto_oneStepDirichletCorrectorFactor_originCube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    Filter.Tendsto (fun K : ℕ =>
      1 - ∫ omega, oneStepDirichletCorrectorEnergy M n h p
        (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure)
      Filter.atTop (nhds (1 - oneStepProjectedEnergy M n h p hh)) := by
  exact tendsto_const_nhds.sub
    (tendsto_integral_oneStepCorrectorEnergies_originCube
      M n h p hh hp).1

/-- The dual finite-volume factor converges to `1 + PE`. -/
theorem tendsto_oneStepNeumannCorrectorFactor_originCube
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    Filter.Tendsto (fun K : ℕ =>
      1 + ∫ omega, oneStepNeumannCorrectorEnergy M n h p
        (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure)
      Filter.atTop (nhds (1 + oneStepProjectedEnergy M n h p hh)) := by
  exact tendsto_const_nhds.add
    (tendsto_integral_oneStepCorrectorEnergies_originCube
      M n h p hh hp).2

/-- Signed upper principal factor after the thermodynamic passage. -/
theorem oneStepDirichletCorrectorFactor_limit_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    1 - oneStepProjectedEnergy M n h p hh ≤
      1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
        oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 :=
  oneStep_primalProjectedFactor_le M n h p hh hp hscale

/-- Signed lower principal factor after the thermodynamic passage. -/
theorem oneStepNeumannCorrectorFactor_limit_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    1 + oneStepProjectedEnergy M n h p hh ≤
      1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
        oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 :=
  oneStep_dualProjectedFactor_le M n h p hh hp hscale

/-- Every sufficiently large primal cube satisfies the signed principal
factor bound, with an arbitrary thermodynamic tolerance. -/
theorem eventually_oneStepDirichletCorrectorFactor_le_signed
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ K : ℕ in Filter.atTop,
      1 - ∫ omega, oneStepDirichletCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure ≤
        1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 +
          epsilon := by
  have htend := tendsto_oneStepDirichletCorrectorFactor_originCube
    M n h p hh hp
  obtain ⟨K0, hK0⟩ := Metric.tendsto_atTop.1 htend epsilon hepsilon
  have hclose : ∀ᶠ K : ℕ in Filter.atTop,
      |(1 - ∫ omega, oneStepDirichletCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure) -
        (1 - oneStepProjectedEnergy M n h p hh)| < epsilon := by
    exact Filter.eventually_atTop.2 ⟨K0, fun K hK ↦ by
      simpa only [Real.dist_eq] using hK0 K hK⟩
  filter_upwards [hclose] with K hK
  have hlimit := oneStepDirichletCorrectorFactor_limit_le
    M n h p hh hp hscale
  rw [abs_lt] at hK
  linarith

/-- Every sufficiently large dual cube satisfies the signed principal factor
bound, again with an arbitrary thermodynamic tolerance. -/
theorem eventually_oneStepNeumannCorrectorFactor_le_signed
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ K : ℕ in Filter.atTop,
      1 + ∫ omega, oneStepNeumannCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure ≤
        1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          oneStepProjectedEnergyErrorConst * M.delta ^ 4 * (h : ℝ) ^ 2 +
          epsilon := by
  have htend := tendsto_oneStepNeumannCorrectorFactor_originCube
    M n h p hh hp
  obtain ⟨K0, hK0⟩ := Metric.tendsto_atTop.1 htend epsilon hepsilon
  have hclose : ∀ᶠ K : ℕ in Filter.atTop,
      |(1 + ∫ omega, oneStepNeumannCorrectorEnergy M n h p
          (originCube d (K : ℤ)) omega hh ∂M.P.toMeasure) -
        (1 + oneStepProjectedEnergy M n h p hh)| < epsilon := by
    exact Filter.eventually_atTop.2 ⟨K0, fun K hK ↦ by
      simpa only [Real.dist_eq] using hK0 K hK⟩
  filter_upwards [hclose] with K hK
  have hlimit := oneStepNeumannCorrectorFactor_limit_le
    M n h p hh hp hscale
  rw [abs_lt] at hK
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
