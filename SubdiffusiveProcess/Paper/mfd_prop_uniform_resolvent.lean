module

public import SubdiffusiveProcess.Paper.Support.UniformResolventInputProducer
public import SubdiffusiveProcess.Paper.Support.UniformResolventBank

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem mfd_prop_uniform_resolvent
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (hps : ps.Nonempty) (hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 < M.delta → M.delta ≤ delta0 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
    ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
      (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
    let P := (chaosSampleLaw M).toMeasure
    ∃ (G : KilledInverseFamily d (BilateralField d))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
      (∀ i, Measurable (G i)) ∧ Measurable muFull ∧
      (∀ i, TendstoInMeasure P
        (fun N omega => volumeResponseOperator (determiningResponseSpace d i)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))) atTop (G i)) ∧
      (∀ᵐ omega ∂P, MeasuresConvergeLocally
          (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
        IsLocallyFiniteMeasure (muFull omega) ∧ (muFull omega).IsOpenPosMeasure ∧
        NullSingletonClass (muFull omega) ∧
        ∀ i, muFull omega (frontier (determiningCube d i : Set (SpatialCoordinates d))) = 0) ∧
      let mu := fun i omega => (muFull omega).restrict
        (closure (determiningCube d i : Set (SpatialCoordinates d)))
      let Elim := fun i omega u => (limitFormEnergy (G i omega) u).toENNReal
      ∃ (T : ∀ i omega, CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
            (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder →
          Lp ℝ 2 (mu i omega))
        (Ktrace Ctrace : ℕ → BilateralField d → ℝ)
        (lift : ∀ i omega (u : DomainL2 (determiningCube d i)), Elim i omega u ≠ ∞ →
          CubeFractionalL2 (k := 1) hd (rationalTriadicCenter d i)
            (rationalTriadicSide d i) (rationalTriadicSide_pos d i) halfFractionalOrder)
        (J : ∀ i, BilateralField d → DomainL2 (determiningCube d i) → SpatialCoordinates d → ℝ)
        (ustar : ∀ i, BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (determiningCube d i))
        (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          BilateralField d → C(SpatialCoordinates d, ℝ))
        (KQ : ℕ → BilateralField d → ℝ),
        (∀ᵐ omega ∂P, ∀ i, 0 ≤ Ktrace i omega ∧ 0 ≤ Ctrace i omega ∧
          CubeTraceCharacterization hd (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)
            (mu i omega) (Ktrace i omega) (Ctrace i omega) (T i omega) ∧
          ∀ (u : DomainL2 (determiningCube d i)) (hu : Elim i omega u ≠ ∞),
            (lift i omega u hu).val 0 = u ∧
            J i omega u =ᵐ[mu i omega] (T i omega (lift i omega u hu) : SpatialCoordinates d → ℝ)) ∧
        (∀ i lam, 0 < lam → ∀ f, Measurable (R i lam f)) ∧
        (∀ i lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              eps ≤ |killedOccupationResolvent (determiningCube d i) KN N omega lam f x -
                R i lam f omega x|} ≤ ENNReal.ofReal rho) ∧
        (∀ i, Measurable (KQ i) ∧ ∀ p ∈ ps, MemLp (KQ i) (ENNReal.ofReal p) P) ∧
        ∀ᵐ omega ∂P, ∀ i,
          (∀ N lam, 0 < lam → ∀ f,
            ContinuousOn (killedOccupationResolvent (determiningCube d i) KN N omega lam f)
              (closure (determiningCube d i : Set (SpatialCoordinates d))) ∧
            ∀ x ∈ frontier (determiningCube d i : Set (SpatialCoordinates d)),
              killedOccupationResolvent (determiningCube d i) KN N omega lam f x = 0) ∧
          0 ≤ KQ i omega ∧
          ∀ lam, 0 < lam → ∀ f,
            Elim i omega (ustar i omega lam f) ≠ ∞ ∧
            (R i lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
              (ustar i omega lam f : SpatialCoordinates d → ℝ) ∧
            (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              |R i lam f omega x| ≤ ‖f‖ / lam ∧ |R i lam f omega x| ≤ KQ i omega * ‖f‖) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
                |R i lam f omega x - R i lam f omega y| ≤
                  KQ i omega * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            let Func := fun u => (Elim i omega u).toReal +
              lam * (∫ x, J i omega u x ^ 2 ∂(mu i omega)) -
              2 * (∫ x, f x * J i omega u x ∂(mu i omega))
            (∀ u, Elim i omega u ≠ ∞ →
              Integrable (fun x => J i omega u x ^ 2) (mu i omega) ∧
              Integrable (fun x => f x * J i omega u x) (mu i omega) ∧
              Func (ustar i omega lam f) ≤ Func u) ∧
            ∀ u, Elim i omega u ≠ ∞ →
              (∀ v, Elim i omega v ≠ ∞ → Func u ≤ Func v) → u = ustar i omega lam f
 :=
 by
  classical
  have hepsilon1 : epsilon < 1 := by
    refine hepsilon'.trans ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨q, hqbig⟩ := exists_nat_gt (max (2 * ps.max' hps) ((d : ℝ) / epsilon))
  have hqmax : 2 * ps.max' hps < (q : ℝ) := (le_max_left _ _).trans_lt hqbig
  have hmaxge : (1 : ℝ) ≤ ps.max' hps := hps_ge _ (Finset.max'_mem ps hps)
  have hq : (1 : ℝ) ≤ q := by linarith
  have hp : (d : ℝ) < q * epsilon :=
    (div_lt_iff₀ hepsilon).mp ((le_max_right _ _).trans_lt hqbig)
  have hqp : ∀ p ∈ ps, p ≤ (q : ℝ) / 2 := by
    intro p hp
    have h := Finset.le_max' ps p hp
    linarith
  obtain ⟨delta0, hdelta0, hinputs⟩ := aux_mfd_prop_uniform_resolvent_inputs
    d hd epsilon ⟨hepsilon, hepsilon1⟩ q hq hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMpos hMsmall H hH PN KN hKN hin
  let A := Classical.choice (hinputs M hMpos hMsmall H hH PN KN hKN hin)
  let Cp := Classical.choice (inputs_Cp_witness d)
  let Interp := inputs_Interp_witness d hd
  obtain ⟨R, B, hB, hRm, hRprob, hR⟩ := aux_mfd_prop_uniform_resolvent_bank
    d hd Cp Interp epsilon hepsilon hepsilon' q hq M H KN A
  refine ⟨A.G, A.muFull, A.hGmeas, A.hmuMeas, A.hGconv, A.hmu,
    (fun i omega => (A.O i omega).T), A.Kmu, (fun i omega => (A.O i omega).Ctrace), A.lift,
    (fun i omega => (A.O i omega).J), (fun i omega => (A.O i omega).ustar), R, B,
    ?_, hRm, hRprob, ?_, ?_⟩
  · filter_upwards [A.hForm] with omega h i
    rcases h i with ⟨hK, hC, _, hT, hJ, _, _⟩
    exact ⟨hK, hC, hT, fun u hu => ⟨A.hlift i omega u hu, hJ u hu⟩⟩
  · intro i
    exact ⟨(hB i).1, fun p hp => (hB i).2.2.mono_exponent (ENNReal.ofReal_le_ofReal (hqp p hp))⟩
  · filter_upwards [A.hForm, hR] with omega hForm hR i
    refine ⟨(hR i).1, (hB i).2.1 omega, fun lam hlam f => ?_⟩
    rcases (hR i).2 lam hlam f with ⟨hae, hzero, hcontract, hbound, hholder⟩
    have hmin := (hForm i).2.2.2.2.2.2 lam hlam f
    exact ⟨hmin.1, hae, hzero, fun x hx => ⟨hcontract x hx, hbound x hx⟩, hholder, hmin.2⟩

end SubdiffusiveProcess.Paper
