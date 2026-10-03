module

public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-
Trace-preserving compactness and energy passage at paper lines 2777--2778.

Tick list.

* The cube is the concrete closed-form carrier and the local set is the
  physical ball used by the parent candidate statement.
* `uN` and `BN` are the actual finite-cutoff killed solutions and their
  continuous representatives; their a.e. identification and common boundary
  values are carried explicitly.
* The common Holder modulus and one-point bound are the compactness inputs for
  the finite-cutoff representatives. They produce the continuous candidate
  representative here; no candidate trace extension is assumed.
* `hrec` is the joint recovery convergence, `hlimit` keeps the limiting form
  energy finite, and `hGamma`/`hnuBound` are the local energy-measure
  domination supplied by `cor_energy_measures`.
* The finite response-energy bound is carried before the cutoff index and is
  not the desired limiting conclusion.
* The conclusion is the trace-preserving continuous representative together
  with the candidate local energy bound. This is a fine child of
  `candidate_good_estimates`, not a replacement for its sourced Holder,
  harmonic, or calibrated matrix conclusions.
 -/
theorem candidate_good_estimates_trace_passage
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (b : SpatialCoordinates d → ℝ)
    (hb : IsCellBoundaryClass beta z r b)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (a : ℕ → PositiveCoefficient (centeredCube Qcentre Qside hQside))
    (G : DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (GammaE : DirichletForm.EnergyMeasure E)
    (uN : ℕ → S.space)
    (BN : ℕ → SpatialCoordinates d → ℝ)
    (hBNrep : ∀ n : ℕ,
      ((uN n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))]
        BN n)
    (hBNcont : ∀ n : ℕ,
      ContinuousOn (BN n)
        (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (hBNboundary : ∀ n : ℕ, ∀ x ∈ frontier (Metric.ball z (r / 2)),
      BN n x = b x)
    (hEqui : ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : ℕ, ∀ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
          |BN n x - BN n y| ≤ K * dist x y ^ beta)
    (hPoint : ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |BN n x| ≤ K)
    (hEnergy : ∃ E0 : ℝ, 0 ≤ E0 ∧
      ∀ n : ℕ, ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal) ≤ E0)
    (u : DomainL2 (centeredCube Qcentre Qside hQside))
    (hrec : Tendsto
      (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
      (𝓝 (u, limitFormEnergy G u)))
    (hlimit : limitFormEnergy G u < (⊤ : EReal))
    (nu : Measure (SpatialCoordinates d))
    (hGamma : ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
      GammaE.measure u B ≤ nu B)
    (hnuFinite : nu (Metric.ball z (r / 2)) ≠ ⊤)
    (Ctotal Uq : ℝ)
    (hnuBound : (nu (Metric.ball z (r / 2))).toReal ≤
      Ctotal * Uq * r ^ ((d : ℝ) - 2) *
        cellBoundaryQuotientNorm beta z r b ^ 2) :
    ∃ U : SpatialCoordinates d → ℝ,
      u ∈ E.domain ∧
      ContinuousOn U
        (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
      ((u : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
      (∀ x ∈ frontier (Metric.ball z (r / 2)), U x = b x) ∧
      (GammaE.measure u (Metric.ball z (r / 2))).toReal ≤
        Ctotal * Uq * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta z r b ^ 2 := by
  classical
  let K : Set (SpatialCoordinates d) :=
    closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_closure
  have hKnonempty : K.Nonempty := by
    refine ⟨Qcentre, ?_⟩
    apply subset_closure
    change Qcentre ∈ Metric.ball Qcentre (Qside / 2)
    exact Metric.mem_ball_self (by linarith)
  obtain ⟨x₀, hx₀K, K₀, hK₀, hpoint⟩ := hPoint
  obtain ⟨K₁, hK₁, hEqui'⟩ := hEqui
  have hbeta_pos : 0 < beta := by linarith [hbeta.1]
  have hpow' : ContinuousAt (fun t : ℝ => t ^ beta) 0 :=
    (Real.continuous_rpow_const hbeta_pos.le).continuousAt
  have hpow : Tendsto (fun t : ℝ => t ^ beta) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hbeta_pos.ne'] using
      hpow'.tendsto
  have hmod : Tendsto (fun t : ℝ => K₁ * t ^ beta) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have heq : Equicontinuous (fun n (x : K) => BN n x) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => K₁ * t ^ beta) hmod
    intro x y n
    rw [Real.dist_eq]
    exact hEqui' n x.1 x.2 y.1 y.2
  have hbound : ∀ x : K, ∃ M : ℝ, ∀ n, ‖BN n x‖ ≤ M := by
    intro x
    refine ⟨K₀ + K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta, ?_⟩
    intro n
    rw [Real.norm_eq_abs]
    calc
      |BN n (x : SpatialCoordinates d)| =
          |(BN n (x : SpatialCoordinates d) - BN n x₀) + BN n x₀| := by
            congr 1 <;> ring
      _ ≤ |BN n (x : SpatialCoordinates d) - BN n x₀| + |BN n x₀| := by
        simpa only [Real.norm_eq_abs] using
          (norm_add_le (BN n (x : SpatialCoordinates d) - BN n x₀) (BN n x₀))
      _ ≤ K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta + K₀ := by
        exact add_le_add (hEqui' n (x : SpatialCoordinates d) x.2 x₀ hx₀K)
          (hpoint n)
      _ = K₀ + K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta := by ring
  letI : Nonempty K := hKnonempty.to_subtype
  obtain ⟨g, φ, hφ, hgcont, hglim⟩ :=
    exists_pointwise_subseq_of_equicontinuous heq hbound
  let U : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ K then g ⟨x, hx⟩ else b x
  have hUcont : ContinuousOn U K := by
    rw [continuousOn_iff_continuous_restrict]
    simpa [U] using hgcont
  have hrec' := hrec
  rw [nhds_prod_eq] at hrec'
  have hrecLp := hrec'.fst
  have hrecφ : Tendsto (fun n => (uN (φ n)).val.1) atTop (𝓝 u) := by
    exact hrecLp.comp hφ.tendsto_atTop
  have hmeasure : TendstoInMeasure
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
      (fun n => (uN (φ n)).val.1) atTop (u : SpatialCoordinates d → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hrecφ
  obtain ⟨ψ, hψ, huae⟩ := hmeasure.exists_seq_tendsto_ae
  have haeall : ∀ᵐ x ∂(volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))),
      ∀ n : ℕ, (uN n).val.1 x = BN n x := by
    apply ae_all_iff.mpr
    intro n
    exact (hBNrep n).mono (fun _ h => h)
  have hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) := by
    have hQmeas : MeasurableSet
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
      exact measurableSet_ball
    have hQK : ∀ᵐ x ∂(volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))), x ∈ K :=
      ae_restrict_of_forall_mem hQmeas (fun x hx => subset_closure hx)
    filter_upwards [haeall, hQK, huae] with x hx hxK hxu
    have hgpt : Tendsto (fun i => BN (φ (ψ i)) x) atTop
        (𝓝 (g ⟨x, hxK⟩)) := by
      exact (hglim ⟨x, hxK⟩).comp hψ.tendsto_atTop
    have heqseq : (fun i => BN (φ (ψ i)) x) =ᶠ[atTop]
        (fun i => (uN (φ (ψ i))).val.1 x) :=
      Filter.Eventually.of_forall (fun i => (hx (φ (ψ i))).symm)
    have hgeq : (u : SpatialCoordinates d → ℝ) x = g ⟨x, hxK⟩ :=
      tendsto_nhds_unique hxu (Filter.Tendsto.congr' heqseq hgpt)
    simpa [U, hxK] using hgeq
  have hUb : ∀ x ∈ frontier (Metric.ball z (r / 2)), U x = b x := by
    intro x hx
    by_cases hxK : x ∈ K
    · have hgxb : g ⟨x, hxK⟩ = b x := by
        apply tendsto_nhds_unique_of_eventuallyEq (hglim ⟨x, hxK⟩)
          tendsto_const_nhds
        exact Filter.Eventually.of_forall (fun n => hBNboundary (φ n) x hx)
      simpa [U, hxK] using hgxb
    · simp [U, hxK]
  have huDomain : u ∈ E.domain := by
    apply DirichletForm.ClosedForm.mem_domain_of_energy_lt_top
    rw [hE u]
    exact hlimit
  have hlocal : (GammaE.measure u (Metric.ball z (r / 2))).toReal ≤
      (nu (Metric.ball z (r / 2))).toReal := by
    apply ENNReal.toReal_mono hnuFinite
    exact hGamma _ measurableSet_ball
  refine ⟨U, huDomain, ?_, ?_, hUb, ?_⟩
  · simpa [K] using hUcont
  · simpa [K] using hUae
  · exact hlocal.trans hnuBound

end Paper
