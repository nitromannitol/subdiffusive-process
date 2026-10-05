module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.lem_varying_trace
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.killed_zero_extension_bound
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.finite_speed_resolvent_properties
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Paper.cutoff_campanato_bound
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_cutoff_oscillation
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_subsequence_bridge
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Sobolev.MeasureTraceSmoothDensity
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.KilledGraph
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **The `StrongMarkov` identity on continuous paths.**  `hLstrong` is stated on the
lifetime-path carrier `Path d`.  Along `hL` the lifetime-path law is the image of a law on
continuous paths under the infinite-lifetime embedding, which is a measurable embedding, so the
identity transports without any measurability requirement on the integrand; the shift and the
position are then read on the continuous path. -/
theorem aux_prop_uniform_resolvent_soft_sm_transport {d : ℕ}
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (x : SpatialCoordinates d) (T : Path d → ℝ≥0∞)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B)
    (g : Path d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        g (LifetimePath.ofContinuousPath
          (ContinuousPath.shift (T (LifetimePath.ofContinuousPath p)).toNNReal p)) ∂K x =
      ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        (∫⁻ q, g (LifetimePath.ofContinuousPath q)
          ∂K (p (T (LifetimePath.ofContinuousPath p)).toNNReal)) ∂K x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := SpatialCoordinates d)
  have hTm : Measurable T := by
    exact hT.measurable'
  have hS : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTm LifetimePath.measurable_lifetime)
  have h := hSM.2.2 x T hT B hB g hg
  rw [← hL x, Measure.restrict_map hemb.measurable hS, hemb.lintegral_map,
    hemb.lintegral_map] at h
  simp only [SubdiffusiveProcess.Model.LifetimeProcess.shift_ofContinuousPath,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath] at h
  rw [h]
  refine setLIntegral_congr_fun_ae (hemb.measurable hS) (ae_of_all _ fun p _ => ?_)
  rw [← hL, hemb.lintegral_map]


/-- The exact finite-cutoff speed measures in this proposition supply the
absolute-continuity input of the repaired oscillation proof step. -/
theorem aux_prop_uniform_resolvent_actual_muN_restrict_ac
    {d : ℕ} [MeasurableSpace (BilateralField d)]
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (P : Measure (BilateralField d)) :
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ᵐ omega ∂P, ∀ N : ℕ,
      (muN N omega).restrict
        ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume := by
  dsimp
  filter_upwards [] with omega
  intro N
  exact aux_prop_uniform_resolvent_cutoff_oscillation_cutoffSpeedMeasure_restrict_ac
    M H omega N
    (closure ((centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ((centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))

end SubdiffusiveProcess.Paper

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- The level-`Mb` index mask: keep `N` when both samplewise constants are at most `Mb`,
otherwise fall back to index `0`.  It depends on the sample `omega`. -/
def aux_prop_uniform_resolvent_mask_index {Ω : Type*} (Kcoer Khol : ℕ → Ω → ℝ) (Mb : ℕ)
    (omega : Ω) (N : ℕ) : ℕ :=
  open Classical in
  if Kcoer N omega ≤ Mb ∧ Khol N omega ≤ Mb then N else 0

theorem aux_prop_uniform_resolvent_mask_index_of_le {Ω : Type*} (Kcoer Khol : ℕ → Ω → ℝ)
    (Mb : ℕ) (omega : Ω) (N : ℕ) (h1 : Kcoer N omega ≤ Mb) (h2 : Khol N omega ≤ Mb) :
    aux_prop_uniform_resolvent_mask_index Kcoer Khol Mb omega N = N := by
  unfold aux_prop_uniform_resolvent_mask_index
  rw [ite_eq_left ⟨h1, h2⟩]

/-- Along the mask, both constant sequences are bounded for EVERY sample: this is a proved
fact about the masked sequence, not an assumption on the original sequence. -/
theorem aux_prop_uniform_resolvent_mask_bddAbove {Ω : Type*} (Kcoer Khol : ℕ → Ω → ℝ)
    (Mb : ℕ) (omega : Ω) :
    BddAbove (Set.range (fun N =>
        Kcoer (aux_prop_uniform_resolvent_mask_index Kcoer Khol Mb omega N) omega)) ∧
      BddAbove (Set.range (fun N =>
        Khol (aux_prop_uniform_resolvent_mask_index Kcoer Khol Mb omega N) omega)) := by
  classical
  constructor
  · refine ⟨max (Mb : ℝ) (Kcoer 0 omega), ?_⟩
    rintro _ ⟨N, rfl⟩
    by_cases h : Kcoer N omega ≤ Mb ∧ Khol N omega ≤ Mb
    · simp only [aux_prop_uniform_resolvent_mask_index, ite_eq_left h]
      exact le_max_of_le_left h.1
    · simp only [aux_prop_uniform_resolvent_mask_index, ite_eq_right h]
      exact le_max_right _ _
  · refine ⟨max (Mb : ℝ) (Khol 0 omega), ?_⟩
    rintro _ ⟨N, rfl⟩
    by_cases h : Kcoer N omega ≤ Mb ∧ Khol N omega ≤ Mb
    · simp only [aux_prop_uniform_resolvent_mask_index, ite_eq_left h]
      exact le_max_of_le_left h.2
    · simp only [aux_prop_uniform_resolvent_mask_index, ite_eq_right h]
      exact le_max_right _ _

/-- The repaired oscillation child WITHOUT any samplewise-boundedness input on the constants.
Its conclusion is the child's square-mean oscillation bound, uniform over every index `N` whose
two samplewise constants are at most the level `Mb`, for every level `Mb`.  Proof: apply the
repaired child to the `omega`-dependent masked data, whose constants are bounded for every
sample (`aux_prop_uniform_resolvent_mask_bddAbove`). -/
theorem aux_prop_uniform_resolvent_mask_oscillation
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (P : Measure (BilateralField d))
    (muN : ℕ → BilateralField d → Measure (SpatialCoordinates d))
    (E : ℕ → BilateralField d →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → ℝ)
    (RN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (uN0 : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hE : ∀ N omega v w, E N omega v w =
      sobolevCoefficientForm (aN N omega) v.val w.val)
    (hRNmeas : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        AEMeasurable (RN N omega lam f)
          ((muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))
    (hsource : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ x ∂((muN N omega).restrict
          ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))),
          |f x - lam * RN N omega lam f x| ≤ 2 * ‖f‖)
    (Kmu : BilateralField d → ℝ)
    (Kcoer Khol : ℕ → BilateralField d → ℝ)
    (Region : Set (SpatialCoordinates d))
    (hRegionBounded : Bornology.IsBounded Region)
    (hNeighborhood : ∀ x ∈ closure
        ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hfinite : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega (uN N omega lam f) w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega))
    (hzero : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ lam : ℝ,
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d,
          uN0 N omega lam f x =
            Set.indicator
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun y => ((uN N omega lam f : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 y)) x)
    (hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ N, muN N omega (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E N omega v v ∧
        globalFractionalSqNorm (3 / 4)
          (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
            (fun x => (v : SobolevData (centeredCube
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E N omega v v))
    (hHolder : ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
      ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
        (∀ w : killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
          E N omega v w =
            ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              F0 x * (w : SobolevData (centeredCube
                (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x - vc y| ≤ Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
    (hac : ∀ᵐ omega ∂P, ∀ N : ℕ,
      (muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume) :
    ∀ᵐ omega ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, Kcoer N omega ≤ Mb → Khol N omega ≤ Mb →
      ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (uN0 N omega lam f y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, uN0 N omega lam f w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  rw [ae_all_iff]
  intro Mb
  let ψ : BilateralField d → ℕ → ℕ := aux_prop_uniform_resolvent_mask_index Kcoer Khol Mb
  have hchild := prop_uniform_resolvent_cutoff_oscillation hd epsilon hepsilon hepsilon' Qtri hr P
    (fun N omega => muN (ψ omega N) omega) (fun N omega => E (ψ omega N) omega)
    (fun N omega => RN (ψ omega N) omega) (fun N omega => uN (ψ omega N) omega)
    (fun N omega => uN0 (ψ omega N) omega) (fun N omega => aN (ψ omega N) omega)
    (fun N omega v w => hE (ψ omega N) omega v w)
    (by filter_upwards [hRNmeas] with omega h N; exact h (ψ omega N))
    (by filter_upwards [hsource] with omega h N; exact h (ψ omega N))
    Kmu (fun N omega => Kcoer (ψ omega N) omega) (fun N omega => Khol (ψ omega N) omega)
    (ae_of_all _ (fun omega => aux_prop_uniform_resolvent_mask_bddAbove Kcoer Khol Mb omega))
    Region hRegionBounded hNeighborhood
    (by filter_upwards [hfinite] with omega h N; exact h (ψ omega N))
    (by filter_upwards [hzero] with omega h N; exact h (ψ omega N))
    (by filter_upwards [hgrowth] with omega h x hx r hr0 hr1 N; exact h x hx r hr0 hr1 (ψ omega N))
    (by filter_upwards [hcoer] with omega h N; exact h (ψ omega N))
    (by filter_upwards [hHolder] with omega h N; exact h (ψ omega N))
    (by filter_upwards [hac] with omega h N; exact h (ψ omega N))
  filter_upwards [hchild] with omega hK
  obtain ⟨K, hK0, hKb⟩ := hK
  refine ⟨K, hK0, fun N h1 h2 lam hlam f x r hr0 hr1 => ?_⟩
  have hψ : ψ omega N = N := aux_prop_uniform_resolvent_mask_index_of_le Kcoer Khol Mb omega N h1 h2
  have hb := hKb N lam hlam f x r hr0 hr1
  simp only [hψ] at hb
  exact hb

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- Markov's inequality in the form used for the level sets: for `c > 0`,
`P {c < g} * c^p ≤ B^p` whenever `‖g‖_{L^p} ≤ B`. -/
theorem aux_prop_uniform_resolvent_tight_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) (B : ℝ) (hB0 : 0 ≤ B)
    (hmem : MemLp g (ENNReal.ofReal p) P)
    (hB : (eLpNorm g (ENNReal.ofReal p) P).toReal ≤ B) (c : ℝ) (hc : 0 < c) :
    P {ω | c < g ω} * ENNReal.ofReal (c ^ p) ≤ ENNReal.ofReal (B ^ p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hmk := mul_meas_ge_le_pow_eLpNorm' P hq0 hqtop (f := g) (ENNReal.ofReal c)
  rw [hqr] at hmk
  have hsub : {ω | c < g ω} ⊆ {ω | ENNReal.ofReal c ≤ ‖g ω‖ₑ} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω.le.trans (le_abs_self _))
  have hnorm : eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hmem.ne]
    exact ENNReal.ofReal_le_ofReal hB
  calc P {ω | c < g ω} * ENNReal.ofReal (c ^ p)
      = ENNReal.ofReal c ^ p * P {ω | c < g ω} := by
        rw [mul_comm, ENNReal.ofReal_rpow_of_nonneg hc.le hp0.le]
    _ ≤ ENNReal.ofReal c ^ p * P {ω | ENNReal.ofReal c ≤ ‖g ω‖ₑ} := by
        gcongr
    _ ≤ eLpNorm g (ENNReal.ofReal p) P ^ p := hmk
    _ ≤ ENNReal.ofReal B ^ p := by gcongr
    _ = ENNReal.ofReal (B ^ p) := ENNReal.ofReal_rpow_of_nonneg hB0 hp0.le

/-- Uniform tightness of the samplewise constants from the parent's uniform `L^p` moment bound
(`hmom`, at one exponent `p ≥ 1`): for every `rho > 0` there is a natural level `Mb` such that,
uniformly in `N`, the event that one of the two constants exceeds `Mb` has probability at most
`rho`.  Nothing about samplewise boundedness of the ranges is assumed or concluded. -/
theorem aux_prop_uniform_resolvent_tight_levels {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (K1 K2 : ℕ → Ω → ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hbound : ∃ B : ℝ, ∀ N,
      (eLpNorm (K1 N) (ENNReal.ofReal p) P).toReal ≤ B ∧
      (eLpNorm (K2 N) (ENNReal.ofReal p) P).toReal ≤ B)
    (hmem : ∀ N, MemLp (K1 N) (ENNReal.ofReal p) P ∧ MemLp (K2 N) (ENNReal.ofReal p) P) :
    ∀ rho : ℝ, 0 < rho → ∃ Mb : ℕ, ∀ N,
      P {ω | ¬ (K1 N ω ≤ Mb ∧ K2 N ω ≤ Mb)} ≤ ENNReal.ofReal rho := by
  intro rho hrho
  obtain ⟨B, hB⟩ := hbound
  have hB0 : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hB 0).1
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨Mb, hMb⟩ := exists_nat_ge (max 1 (2 * B ^ p / rho))
  refine ⟨Mb, fun N => ?_⟩
  have hc1 : (1 : ℝ) ≤ Mb := le_trans (le_max_left _ _) hMb
  have hc0 : (0 : ℝ) < Mb := lt_of_lt_of_le one_pos hc1
  have hcp : (Mb : ℝ) ≤ (Mb : ℝ) ^ p := by
    calc (Mb : ℝ) = (Mb : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Mb : ℝ) ^ p := Real.rpow_le_rpow_of_exponent_le hc1 hp
  have hcpos : (0 : ℝ) < (Mb : ℝ) ^ p := Real.rpow_pos_of_pos hc0 p
  have hBp : B ^ p ≤ rho / 2 * (Mb : ℝ) ^ p := by
    have h1 : 2 * B ^ p / rho ≤ (Mb : ℝ) ^ p := le_trans (le_max_right _ _) (hMb.trans hcp)
    rw [div_le_iff₀ hrho] at h1
    linarith
  have hhalf : ∀ g : Ω → ℝ, MemLp g (ENNReal.ofReal p) P →
      (eLpNorm g (ENNReal.ofReal p) P).toReal ≤ B →
      P {ω | (Mb : ℝ) < g ω} ≤ ENNReal.ofReal (rho / 2) := by
    intro g hg hgB
    have hm := aux_prop_uniform_resolvent_tight_one P g p hp B hB0 hg hgB Mb hc0
    have hle : P {ω | (Mb : ℝ) < g ω} * ENNReal.ofReal ((Mb : ℝ) ^ p) ≤
        ENNReal.ofReal (rho / 2) * ENNReal.ofReal ((Mb : ℝ) ^ p) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact hm.trans (ENNReal.ofReal_le_ofReal hBp)
    exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hcpos).ne'
      ENNReal.ofReal_ne_top).1 hle
  have hsub : {ω | ¬ (K1 N ω ≤ Mb ∧ K2 N ω ≤ Mb)} ⊆
      {ω | (Mb : ℝ) < K1 N ω} ∪ {ω | (Mb : ℝ) < K2 N ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_and_or, not_le] at hω
    exact hω
  calc P {ω | ¬ (K1 N ω ≤ Mb ∧ K2 N ω ≤ Mb)}
      ≤ P ({ω | (Mb : ℝ) < K1 N ω} ∪ {ω | (Mb : ℝ) < K2 N ω}) := measure_mono hsub
    _ ≤ P {ω | (Mb : ℝ) < K1 N ω} + P {ω | (Mb : ℝ) < K2 N ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) :=
        add_le_add (hhalf _ (hmem N).1 (hB N).1) (hhalf _ (hmem N).2 (hB N).2)
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- From uniform tightness of the level events: almost every sample has SOME level `Mb` at
which infinitely many indices are good (a random, sample-dependent "represented" subsequence).
This is the correct replacement of a deterministic subsequence with bounded constants, which
uniform moment bounds do NOT provide. -/
theorem aux_prop_uniform_resolvent_tight_frequently {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (good : ℕ → ℕ → Ω → Prop)
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℕ, ∀ N,
      P {ω | ¬ good Mb N ω} ≤ ENNReal.ofReal rho) :
    ∀ᵐ ω ∂P, ∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω := by
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (bot_le)
  rw [zero_add]
  obtain ⟨Mb, hMb⟩ := htight ε (by exact_mod_cast hε)
  let S : ℕ → Set Ω := fun n => ⋂ N, ⋂ (_ : n ≤ N), {ω | ¬ good Mb N ω}
  have hmono : Monotone S := by
    intro a b hab ω hω
    simp only [S, Set.mem_iInter] at hω ⊢
    exact fun N hN => hω N (hab.trans hN)
  have hsub : {ω | ¬ ∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω} ⊆ ⋃ n, S n := by
    intro ω hω
    simp only [mem_ofPred_eq, not_exists, Filter.not_frequently] at hω
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (hω Mb)
    exact Set.mem_iUnion.2 ⟨n, by simp only [S, Set.mem_iInter]; exact fun N hN => hn N hN⟩
  calc P {ω | ¬ ∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω} ≤ P (⋃ n, S n) := measure_mono hsub
    _ = ⨆ n, P (S n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal ε := iSup_le fun n =>
        (measure_mono (Set.iInter₂_subset n le_rfl)).trans (hMb n)
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal



theorem aux_prop_uniform_resolvent_mask_prob_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (F : ℕ → Ω → SpatialCoordinates d → ℝ) (G : Ω → SpatialCoordinates d → ℝ)
    (hF : ∀ (N : ℕ) (x : SpatialCoordinates d), Measurable (fun ω => F N ω x))
    (hG : ∀ x : SpatialCoordinates d, Measurable (fun ω => G ω x))
    (hcont : ∀ᵐ ω ∂μ, ∀ N, ContinuousOn (F N ω) K)
    (hcontG : ∀ᵐ ω ∂μ, ContinuousOn (G ω) K)
    (good : ℕ → ℕ → Ω → Prop) (hgoodmeas : ∀ Mb N, MeasurableSet {ω | good Mb N ω})
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℕ, ∀ N,
      μ {ω | ¬ good Mb N ω} ≤ ENNReal.ofReal rho)
    (hconv : ∀ᵐ ω ∂μ, ∀ Mb : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        good Mb N ω → ∀ x ∈ K, |F N ω x - G ω x| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      μ {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|} ≤ ENNReal.ofReal rho := by
  classical
  intro ε hε rho hrho
  obtain ⟨Mb, hMb⟩ := htight (rho / 2) (half_pos hrho)
  let F' : ℕ → Ω → SpatialCoordinates d → ℝ := fun N ω x =>
    if good Mb N ω then F N ω x else G ω x
  have hF' : ∀ (N : ℕ) (x : SpatialCoordinates d), Measurable (fun ω => F' N ω x) :=
    fun N x => Measurable.ite (hgoodmeas Mb N) (hF N x) (hG x)
  have hcont' : ∀ᵐ ω ∂μ, ∀ N, ContinuousOn (F' N ω) K := by
    filter_upwards [hcont, hcontG] with ω h1 h2 N
    by_cases hg : good Mb N ω
    · have : F' N ω = F N ω := by funext x; simp only [F', ite_eq_left hg]
      rw [this]; exact h1 N
    · have : F' N ω = G ω := by funext x; simp only [F', ite_eq_right hg]
      rw [this]; exact h2
  have hconv' : ∀ᵐ ω ∂μ, ∀ ε' : ℝ, 0 < ε' → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ x ∈ K, |F' N ω x - G ω x| < ε' := by
    filter_upwards [hconv] with ω h ε' hε'
    obtain ⟨N0, hN0⟩ := h Mb ε' hε'
    refine ⟨N0, fun N hN x hx => ?_⟩
    by_cases hg : good Mb N ω
    · simp only [F', ite_eq_left hg]; exact hN0 N hN hg x hx
    · simp only [F', ite_eq_right hg, sub_self, abs_zero]; exact hε'
  obtain ⟨N0, hN0⟩ := aux_prop_uniform_resolvent_subsequence_bridge_prob_bound_from_ae μ K hK F' G
    hF' hG hcont' hcontG hconv' ε hε (rho / 2) (half_pos hrho)
  refine ⟨N0, fun N hN => ?_⟩
  have hsub : {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|} ⊆
      {ω | ¬ good Mb N ω} ∪ {ω : Ω | ∃ x ∈ K, ε ≤ |F' N ω x - G ω x|} := by
    intro ω hω
    by_cases hg : good Mb N ω
    · right
      obtain ⟨x, hx, hle⟩ := hω
      exact ⟨x, hx, by simp only [F', ite_eq_left hg]; exact hle⟩
    · left; exact hg
  calc μ {ω : Ω | ∃ x ∈ K, ε ≤ |F N ω x - G ω x|}
      ≤ μ ({ω | ¬ good Mb N ω} ∪ {ω : Ω | ∃ x ∈ K, ε ≤ |F' N ω x - G ω x|}) := measure_mono hsub
    _ ≤ μ {ω | ¬ good Mb N ω} + μ {ω : Ω | ∃ x ∈ K, ε ≤ |F' N ω x - G ω x|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) := add_le_add (hMb N) (hN0 N hN)
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- Deterministic (one sample) step of the two-subsequence criterion along the good indices:
uniform Holder bounds on the good indices plus identification of every uniform cluster (along a
strictly increasing sequence of good indices) with one function `gstar` give uniform convergence
to `gstar` along the good indices. -/
theorem aux_prop_uniform_resolvent_mask_det_conv {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (h : ℕ → SpatialCoordinates d → ℝ) (I : ℕ → Prop)
    (hcont : ∀ N, I N → ContinuousOn (h N) K)
    (hbdd : ∃ B : ℝ, ∀ N, I N → ∀ x ∈ K, |h N x| ≤ B)
    (C : ℝ) (hC : 0 ≤ C)
    (hhold : ∀ N, I N → ∀ x ∈ K, ∀ y ∈ K, |h N x - h N y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (gstar : SpatialCoordinates d → ℝ)
    (hident : ∀ σ : ℕ → ℕ, StrictMono σ → (∀ k, I (σ k)) →
      ∀ g : SpatialCoordinates d → ℝ, ContinuousOn g K →
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K, |h (σ k) x - g x| < eps) →
      ∀ x ∈ K, g x = gstar x) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → I N → ∀ x ∈ K, |h N x - gstar x| < ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hfreq : ∃ᶠ N in atTop, I N ∧ ∃ x ∈ K, ε ≤ |h N x - gstar x| := by
    rw [Filter.frequently_atTop]
    intro N0
    obtain ⟨N, hN, hI, x, hx, hle⟩ := hcon N0
    exact ⟨N, hN, hI, x, hx, hle⟩
  obtain ⟨σ, hσ, hσP⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨τ, hτ, g, hg, hgconv⟩ := aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract
    K hK (fun k => h (σ k)) (fun k => hcont (σ k) (hσP k).1)
    ⟨B, fun k => hB (σ k) (hσP k).1⟩
    ⟨C, hC, fun k => hhold (σ k) (hσP k).1⟩ id strictMono_id
  have hgs : ∀ x ∈ K, g x = gstar x :=
    hident (σ ∘ τ) (hσ.comp hτ) (fun k => (hσP (τ k)).1) g hg (by
      intro eps heps
      obtain ⟨k0, hk0⟩ := hgconv eps heps
      exact ⟨k0, fun k hk x hx => hk0 k hk x hx⟩)
  obtain ⟨k0, hk0⟩ := hgconv ε hε
  obtain ⟨-, x, hx, hle⟩ := hσP (τ k0)
  have hlt := hk0 k0 le_rfl x hx
  rw [hgs x hx] at hlt
  exact absurd hle (not_le.2 hlt)

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- A function with a local Holder bound (distances at most one) is continuous. -/
theorem aux_prop_uniform_resolvent_det_holder_continuous {X : Type*} [PseudoMetricSpace X]
    (v : X → ℝ) (A α : ℝ) (hα : 0 < α)
    (h : ∀ x y : X, dist x y ≤ 1 → |v x - v y| ≤ A * dist x y ^ α) : Continuous v := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hA : 0 ≤ max A 0 := le_max_right _ _
  have hden : 0 < max A 0 + 1 := by linarith
  have hpos : 0 < ε / (2 * (max A 0 + 1)) := by positivity
  refine ⟨min 1 ((ε / (2 * (max A 0 + 1))) ^ (1 / α)), lt_min one_pos (Real.rpow_pos_of_pos hpos _),
    fun y hy => ?_⟩
  have hy1 : dist y x ≤ 1 := (lt_of_lt_of_le hy (min_le_left _ _)).le
  have hy2 : dist y x < (ε / (2 * (max A 0 + 1))) ^ (1 / α) := lt_of_lt_of_le hy (min_le_right _ _)
  have hpow : dist y x ^ α < ε / (2 * (max A 0 + 1)) := by
    have h1 := Real.rpow_lt_rpow dist_nonneg hy2 hα
    rwa [← Real.rpow_mul hpos.le, one_div_mul_cancel hα.ne', Real.rpow_one] at h1
  rw [Real.dist_eq]
  calc |v y - v x| ≤ A * dist y x ^ α := h y x hy1
    _ ≤ max A 0 * dist y x ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg dist_nonneg _)
    _ ≤ max A 0 * (ε / (2 * (max A 0 + 1))) := mul_le_mul_of_nonneg_left hpow.le hA
    _ ≤ (max A 0 + 1) * (ε / (2 * (max A 0 + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- A local order-`1/4` Holder bound (distances at most one) together with a sup bound on `K`
gives a Holder bound at every distance on `K`. -/
theorem aux_prop_uniform_resolvent_det_holder_global {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (u : X → ℝ) (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hloc : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 1 → |u x - u y| ≤ A * dist x y ^ (1 / 4 : ℝ))
    (hsup : ∀ x ∈ K, |u x| ≤ S) :
    ∀ x ∈ K, ∀ y ∈ K, |u x - u y| ≤ (A + 2 * S) * dist x y ^ (1 / 4 : ℝ) := by
  intro x hx y hy
  have hd0 : 0 ≤ dist x y ^ (1 / 4 : ℝ) := Real.rpow_nonneg dist_nonneg _
  by_cases hd : dist x y ≤ 1
  · calc |u x - u y| ≤ A * dist x y ^ (1 / 4 : ℝ) := hloc x hx y hy hd
      _ ≤ (A + 2 * S) * dist x y ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hd0
  · have h1 : 1 ≤ dist x y ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (le_of_lt (not_le.1 hd)) (by norm_num)
    calc |u x - u y| ≤ |u x| + |u y| := abs_sub _ _
      _ ≤ 2 * S := by linarith [hsup x hx, hsup y hy]
      _ ≤ (A + 2 * S) * 1 := by linarith
      _ ≤ (A + 2 * S) * dist x y ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)

/-- Composition with a measurable random index. -/
theorem aux_prop_uniform_resolvent_det_measurable_index {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] (F : ℕ → Ω → β) (hF : ∀ n, Measurable (F n)) (ν : Ω → ℕ)
    (hν : Measurable ν) : Measurable (fun ω => F (ν ω) ω) := by
  intro S hS
  have heq : (fun ω => F (ν ω) ω) ⁻¹' S = ⋃ n, ν ⁻¹' {n} ∩ F n ⁻¹' S := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨ν ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hν (measurableSet_singleton n)).inter (hF n hS)

/-- A family of measurable sets evaluated at a measurable random index. -/
theorem aux_prop_uniform_resolvent_det_measurableSet_index {Ω : Type*} [MeasurableSpace Ω]
    (p : ℕ → Ω → Prop) (hp : ∀ m, MeasurableSet {ω | p m ω}) (ν : Ω → ℕ)
    (hν : Measurable ν) : MeasurableSet {ω | p (ν ω) ω} := by
  have heq : {ω | p (ν ω) ω} = ⋃ m, ν ⁻¹' {m} ∩ {ω | p m ω} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨ν ω, rfl, h⟩, fun ⟨m, hm, h⟩ => hm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun m => (hν (measurableSet_singleton m)).inter (hp m)

/-- The "infinitely often" event of measurable events is measurable. -/
theorem aux_prop_uniform_resolvent_det_measurableSet_frequently {Ω : Type*} [MeasurableSpace Ω]
    (p : ℕ → Ω → Prop) (hp : ∀ N, MeasurableSet {ω | p N ω}) :
    MeasurableSet {ω | ∃ᶠ N in atTop, p N ω} := by
  have heq : {ω | ∃ᶠ N in atTop, p N ω} = ⋂ a : ℕ, ⋃ b : ℕ, ⋃ (_ : a ≤ b), {ω | p b ω} := by
    ext ω
    simp only [mem_ofPred_eq, Filter.frequently_atTop, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
  rw [heq]
  exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
    MeasurableSet.iUnion fun _ => hp b



theorem aux_prop_uniform_resolvent_det_measurable_contmap_of_eval
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SeparableSpace X] [Nonempty X] [MeasurableSpace C(X, ℝ)]
    [BorelSpace C(X, ℝ)] [PolishSpace C(X, ℝ)]
    (F : Ω → C(X, ℝ))
    (hF : ∀ x : X, Measurable (fun ω => F ω x)) : Measurable F := by
  let q : ℕ → X := TopologicalSpace.denseSeq X
  let e : C(X, ℝ) → (ℕ → ℝ) := fun g n => g (q n)
  have hecont : Continuous e := by
    apply continuous_pi
    intro n
    exact continuous_eval_const (q n)
  have heinj : Function.Injective e := by
    intro g h hgh
    apply ContinuousMap.ext
    have heq : (g : X → ℝ) ∘ q = (h : X → ℝ) ∘ q := by
      funext n
      exact congrFun hgh n
    exact congrFun ((TopologicalSpace.denseRange_denseSeq X).equalizer g.continuous h.continuous heq)
  have hemb : MeasurableEmbedding e := hecont.measurableEmbedding heinj
  apply hemb.measurable_comp_iff.mp
  change Measurable (fun ω n => F ω (q n))
  exact measurable_pi_iff.mpr (fun n => hF (q n))

/-- A uniform limit on `K` of functions vanishing at a point of `K` vanishes there. -/
theorem aux_prop_uniform_resolvent_det_limit_zero {X : Type*} (K : Set X) (h : ℕ → X → ℝ)
    (g : X → ℝ) (x : X) (hx : x ∈ K) (h0 : ∀ k, h k x = 0)
    (hconv : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ y ∈ K, |h k y - g y| < eps) :
    g x = 0 := by
  have hle : |g x| ≤ 0 := le_of_forall_pos_lt_add (fun e he => by
    obtain ⟨k0, hk0⟩ := hconv e he
    have hk := hk0 k0 le_rfl x hx
    rw [h0 k0] at hk
    simp only [zero_sub, abs_neg] at hk
    linarith)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- Pointwise limit of a uniform convergence on `K`. -/
theorem aux_prop_uniform_resolvent_det_tendsto_of_unif {X : Type*} (K : Set X) (h : ℕ → X → ℝ)
    (g : X → ℝ)
    (hconv : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ y ∈ K, |h k y - g y| < eps)
    (x : X) (hx : x ∈ K) : Tendsto (fun k => h k x) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨k0, hk0⟩ := hconv e he
  exact ⟨k0, fun k hk => by rw [Real.dist_eq]; exact hk0 k hk x hx⟩

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- The killed occupation integrand of `hRN`, as a function of a path and a time. -/
def aux_prop_uniform_resolvent_point_F {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (p : ContinuousPath (SpatialCoordinates d)) (t : ℝ) : ℝ :=
  Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
    (fun s : ℝ => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t

/-- The killed occupation functional of `hRN` (one path). -/
def aux_prop_uniform_resolvent_point_G {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (p : ContinuousPath (SpatialCoordinates d)) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), aux_prop_uniform_resolvent_point_F Q lam f p t

theorem aux_prop_uniform_resolvent_point_F_measurable {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
      aux_prop_uniform_resolvent_point_F Q lam f q.1 q.2) := by
  have heq : (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
      aux_prop_uniform_resolvent_point_F Q lam f q.1 q.2) =
      Set.indicator {q : ContinuousPath (SpatialCoordinates d) × ℝ |
        ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1}
        (fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))) := by
    funext q
    simp only [aux_prop_uniform_resolvent_point_F, Set.indicator, mem_ofPred_eq]
  rw [heq]
  have hev : Measurable (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
      q.1 (Real.toNNReal q.2)) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  refine Measurable.indicator ?_ ?_
  · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_snd))).mul (hf.comp hev)
  · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst)

/-- Measurability of time integrals of the killed integrand against any s-finite time
measure. -/
theorem aux_prop_uniform_resolvent_point_integral_measurable {d : ℕ}
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (hf : Measurable f) (ν : Measure ℝ) [SFinite ν] :
    Measurable (fun p : ContinuousPath (SpatialCoordinates d) =>
      ∫ t, aux_prop_uniform_resolvent_point_F Q lam f p t ∂ν) :=
  ((aux_prop_uniform_resolvent_point_F_measurable Q hQ lam f hf).stronglyMeasurable.integral_prod_right'
    (ν := ν)).measurable

theorem aux_prop_uniform_resolvent_point_G_measurable {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (aux_prop_uniform_resolvent_point_G Q lam f) :=
  aux_prop_uniform_resolvent_point_integral_measurable Q hQ lam f hf (volume.restrict (Ioi 0))

theorem aux_prop_uniform_resolvent_point_F_norm_le {d : ℕ} (Q : Set (SpatialCoordinates d))
    (lam : ℝ) (_hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (M : ℝ) (hM : ∀ y, |f y| ≤ M)
    (p : ContinuousPath (SpatialCoordinates d)) (t : ℝ) (_ht : 0 ≤ t) :
    ‖aux_prop_uniform_resolvent_point_F Q lam f p t‖ ≤ M * Real.exp (-lam * t) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  unfold aux_prop_uniform_resolvent_point_F
  by_cases hmem : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
  · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact mul_nonneg hM0 (Real.exp_pos _).le

theorem aux_prop_uniform_resolvent_point_F_norm_le_const {d : ℕ} (Q : Set (SpatialCoordinates d))
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (M : ℝ) (hM : ∀ y, |f y| ≤ M)
    (p : ContinuousPath (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    ‖aux_prop_uniform_resolvent_point_F Q lam f p t‖ ≤ M := by
  refine (aux_prop_uniform_resolvent_point_F_norm_le Q lam hlam f M hM p t ht).trans ?_
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h1 : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc M * Real.exp (-lam * t) ≤ M * 1 := mul_le_mul_of_nonneg_left h1 hM0
    _ = M := mul_one M

theorem aux_prop_uniform_resolvent_point_integrableOn {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ y, |f y| ≤ M)
    (p : ContinuousPath (SpatialCoordinates d)) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) :
    IntegrableOn (aux_prop_uniform_resolvent_point_F Q lam f p) S := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-lam * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -lam < 0) 0).const_mul M
  have hpair : Measurable (fun t : ℝ => (p, t)) := measurable_const.prodMk measurable_id
  have hcomp := (aux_prop_uniform_resolvent_point_F_measurable Q hQ lam f hf).comp hpair
  have hmeasF : Measurable (aux_prop_uniform_resolvent_point_F Q lam f p) := by
    simpa only [Function.comp_def] using! hcomp
  have hInt : Integrable (fun t : ℝ => M * Real.exp (-lam * t)) (volume.restrict S) :=
    hint.mono_set hS
  have hAES : AEStronglyMeasurable (aux_prop_uniform_resolvent_point_F Q lam f p)
      (volume.restrict S) := hmeasF.aestronglyMeasurable
  apply Integrable.mono' hInt hAES
  exact ae_restrict_of_forall_mem hSm (fun t ht =>
    aux_prop_uniform_resolvent_point_F_norm_le Q lam hlam f M hM p t (le_of_lt (hS ht)))

/-- Uniform bound on the killed occupation functional. -/
theorem aux_prop_uniform_resolvent_point_G_abs_le {d : ℕ} (Q : Set (SpatialCoordinates d))
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (M : ℝ) (hM : ∀ y, |f y| ≤ M)
    (p : ContinuousPath (SpatialCoordinates d)) :
    |aux_prop_uniform_resolvent_point_G Q lam f p| ≤ M / lam := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-lam * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -lam < 0) 0).const_mul M
  have hval : ∫ t in Ioi (0 : ℝ), M * Real.exp (-lam * t) = M / lam := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -lam < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  rw [← Real.norm_eq_abs, ← hval]
  refine norm_integral_le_of_norm_le hint ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht =>
    aux_prop_uniform_resolvent_point_F_norm_le Q lam hlam f M hM p t (le_of_lt ht))

/-- Translation of a set integral over `Ioi a` to `Ioi 0`. -/
theorem aux_prop_uniform_resolvent_point_integral_Ioi_shift (h : ℝ → ℝ) (a : ℝ) :
    ∫ t in Ioi a, h t = ∫ u in Ioi (0 : ℝ), h (a + u) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self (μ := volume) (Set.indicator (Ioi a) h) a]
  congr 1
  funext u
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (show a + u ∈ Ioi a from by simp only [Set.mem_Ioi]; linarith),
      Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
  · rw [Set.indicator_of_notMem (show a + u ∉ Ioi a from by simp only [Set.mem_Ioi]; linarith),
      Set.indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

/-- Pointwise restart identity of the killed integrand after a deterministic time `s`. -/
theorem aux_prop_uniform_resolvent_point_F_shift {d : ℕ} (Q : Set (SpatialCoordinates d))
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (p : ContinuousPath (SpatialCoordinates d))
    (s : ℝ≥0) (u : ℝ) (hu : 0 < u) :
    aux_prop_uniform_resolvent_point_F Q lam f p ((s : ℝ) + u) =
      if (s : ℝ≥0∞) < ContinuousPath.exitTime Q p then
        Real.exp (-lam * s) *
          aux_prop_uniform_resolvent_point_F Q lam f (ContinuousPath.shift s p) u
      else 0 := by
  have key : ENNReal.ofReal ((s : ℝ) + u) < ContinuousPath.exitTime Q p ↔
      (s : ℝ≥0∞) < ContinuousPath.exitTime Q p ∧
        ENNReal.ofReal u < ContinuousPath.exitTime Q (ContinuousPath.shift s p) := by
    rw [ENNReal.ofReal_add s.coe_nonneg hu.le, ENNReal.ofReal_coe_nnreal]
    have h := ContinuousPath.coe_add_lt_exitTime_iff Q p s u.toNNReal
    rw [ENNReal.coe_add] at h
    exact h
  have hval : Real.exp (-lam * ((s : ℝ) + u)) * f (p (Real.toNNReal ((s : ℝ) + u))) =
      Real.exp (-lam * s) *
        (Real.exp (-lam * u) * f ((ContinuousPath.shift s p) (Real.toNNReal u))) := by
    rw [ContinuousPath.shift_apply, Real.toNNReal_add s.coe_nonneg hu.le, Real.toNNReal_coe,
      ← mul_assoc, ← Real.exp_add]
    ring_nf
  unfold aux_prop_uniform_resolvent_point_F
  by_cases h1 : (s : ℝ≥0∞) < ContinuousPath.exitTime Q p
  · rw [ite_eq_left h1]
    by_cases h2 : ENNReal.ofReal u < ContinuousPath.exitTime Q (ContinuousPath.shift s p)
    · rw [Set.indicator_of_mem (show (s : ℝ) + u ∈ {t : ℝ | ENNReal.ofReal t <
          ContinuousPath.exitTime Q p} from key.2 ⟨h1, h2⟩),
        Set.indicator_of_mem (show u ∈ {t : ℝ | ENNReal.ofReal t <
          ContinuousPath.exitTime Q (ContinuousPath.shift s p)} from h2)]
      exact hval
    · rw [Set.indicator_of_notMem (show (s : ℝ) + u ∉ {t : ℝ | ENNReal.ofReal t <
          ContinuousPath.exitTime Q p} from fun h => h2 (key.1 h).2),
        Set.indicator_of_notMem (show u ∉ {t : ℝ | ENNReal.ofReal t <
          ContinuousPath.exitTime Q (ContinuousPath.shift s p)} from h2), mul_zero]
  · rw [ite_eq_right h1, Set.indicator_of_notMem (show (s : ℝ) + u ∉ {t : ℝ | ENNReal.ofReal t <
          ContinuousPath.exitTime Q p} from fun h => h1 (key.1 h).1)]

/-- Splitting the occupation functional at a deterministic time `s`. -/
theorem aux_prop_uniform_resolvent_point_split {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ y, |f y| ≤ M)
    (p : ContinuousPath (SpatialCoordinates d)) (s : ℝ≥0) :
    aux_prop_uniform_resolvent_point_G Q lam f p =
      (∫ t in Ioc (0 : ℝ) s, aux_prop_uniform_resolvent_point_F Q lam f p t) +
        (if (s : ℝ≥0∞) < ContinuousPath.exitTime Q p then
          Real.exp (-lam * s) *
            aux_prop_uniform_resolvent_point_G Q lam f (ContinuousPath.shift s p)
        else 0) := by
  have hsplit : (∫ t in Ioi (0 : ℝ), aux_prop_uniform_resolvent_point_F Q lam f p t) =
      ∫ t in Ioc (0 : ℝ) s ∪ Ioi (s : ℝ), aux_prop_uniform_resolvent_point_F Q lam f p t := by
    rw [Set.Ioc_union_Ioi_eq_Ioi s.coe_nonneg]
  show (∫ t in Ioi (0 : ℝ), aux_prop_uniform_resolvent_point_F Q lam f p t) = _
  rw [hsplit,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (aux_prop_uniform_resolvent_point_integrableOn Q hQ lam hlam f hf M hM p _
        measurableSet_Ioc (fun t ht => ht.1))
      (aux_prop_uniform_resolvent_point_integrableOn Q hQ lam hlam f hf M hM p _
        measurableSet_Ioi (fun t ht => lt_of_le_of_lt s.coe_nonneg ht))]
  congr 1
  rw [aux_prop_uniform_resolvent_point_integral_Ioi_shift, setIntegral_congr_fun measurableSet_Ioi
    (fun u hu => aux_prop_uniform_resolvent_point_F_shift Q lam f p s u hu)]
  by_cases h1 : (s : ℝ≥0∞) < ContinuousPath.exitTime Q p
  · simp only [ite_eq_left h1]
    rw [integral_const_mul]
    rfl
  · simp only [ite_eq_right h1, integral_zero]

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- Markov identity at a deterministic time `s` on the survival event `{s < τ_Q}`, for bounded
measurable real functionals of continuous paths (from `StrongMarkov` through
`aux_soft_sm_transport`, with the constant stopping time `s`). -/
theorem aux_prop_uniform_resolvent_point_markov {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel K] (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z) (hSM : StrongMarkov L)
    (x : SpatialCoordinates d) (s : ℝ≥0) (g : ContinuousPath (SpatialCoordinates d) → ℝ)
    (hg : Measurable g) (c : ℝ) (hc : ∀ q, |g q| ≤ c) :
    ∫ p, Set.indicator {p : ContinuousPath (SpatialCoordinates d) |
        (s : ℝ≥0∞) < ContinuousPath.exitTime Q p} (fun p => g (ContinuousPath.shift s p)) p ∂K x =
      ∫ p, Set.indicator {p : ContinuousPath (SpatialCoordinates d) |
        (s : ℝ≥0∞) < ContinuousPath.exitTime Q p} (fun p => ∫ q, g q ∂K (p s)) p ∂K x := by
  classical
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := SpatialCoordinates d)
  set S : Set (ContinuousPath (SpatialCoordinates d)) :=
    {p | (s : ℝ≥0∞) < ContinuousPath.exitTime Q p} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQ)
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc (ContinuousPath.shift s (ContinuousPath.shift s
    (ContinuousMap.const _ 0))))
  -- the constant stopping time and the survival event
  let T : Path d → ℝ≥0∞ := fun _ => (s : ℝ≥0∞)
  have hT : IsStoppingTime LifetimePath.canonicalFiltration T :=
    isStoppingTime_const LifetimePath.canonicalFiltration s
  have hτL := LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) Q hQ
  set B : Set (Path d) := {w | (s : ℝ≥0∞) < LifetimePath.exitTime Q w} with hBdef
  have hBc : B = {w : Path d | LifetimePath.exitTime Q w ≤ (s : ℝ≥0∞)}ᶜ := by
    ext w; simp only [hBdef, mem_ofPred_eq, Set.mem_compl_iff, not_le]
  have hBs : MeasurableSet[LifetimePath.canonicalFiltration s] B := by
    rw [hBc]; exact (hτL s).compl
  have hB : MeasurableSet[hT.measurableSpace] B := by
    rw [hT.measurableSet]
    refine ⟨le_iSup LifetimePath.canonicalFiltration s _ hBs, fun i => ?_⟩
    by_cases hsi : s ≤ i
    · convert LifetimePath.canonicalFiltration.mono hsi _ hBs using 1
      refine Set.inter_eq_left.2 (fun w _ => ?_)
      show (s : ℝ≥0∞) ≤ _
      exact ENNReal.coe_le_coe.2 hsi
    · convert @MeasurableSet.empty _ (LifetimePath.canonicalFiltration i) using 1
      refine Set.eq_empty_of_forall_notMem (fun w hw => hsi ?_)
      have h2 : (s : ℝ≥0∞) ≤ _ := hw.2
      exact ENNReal.coe_le_coe.1 h2
  -- the lifted nonnegative functional
  let gL : Path d → ℝ≥0∞ := Function.extend LifetimePath.ofContinuousPath
    (fun q => ENNReal.ofReal (g q + c)) (fun _ => 0)
  have hgL : Measurable gL :=
    hemb.measurable_extend (ENNReal.measurable_ofReal.comp (hg.add_const c)) measurable_const
  have hgL' : ∀ q, gL (LifetimePath.ofContinuousPath q) = ENNReal.ofReal (g q + c) :=
    fun q => hemb.injective.extend_apply _ _ q
  have h := _root_.SubdiffusiveProcess.Paper.aux_prop_uniform_resolvent_soft_sm_transport (⇑K) L hL hSM x T hT B hB gL hgL
  have hpre : LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w : Path d | T w < w.lifetime}) = S := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, mem_ofPred_eq, hBdef, hSdef, T,
      LifetimePath.exitTime_ofContinuousPath, LifetimePath.lifetime_ofContinuousPath,
      ENNReal.coe_lt_top, and_true]
  simp only [hpre, hgL', T, ENNReal.toNNReal_coe] at h
  -- measurability and bounds
  have hshift : Measurable (fun p : ContinuousPath (SpatialCoordinates d) =>
      ContinuousPath.shift s p) :=
    (ContinuousPath.continuous_shift.comp (continuous_const.prodMk continuous_id)).measurable
  have hgs : Measurable (fun p => g (ContinuousPath.shift s p)) := hg.comp hshift
  have hKint : Measurable (fun y => ∫ q, g q ∂K y) :=
    (StronglyMeasurable.integral_kernel_prod_right' (κ := K)
      (f := fun z : SpatialCoordinates d × ContinuousPath (SpatialCoordinates d) => g z.2)
      (hg.comp measurable_snd).stronglyMeasurable).measurable
  have hevs : Measurable (fun p : ContinuousPath (SpatialCoordinates d) => p s) :=
    (continuous_eval_const s).measurable
  have hKs : Measurable (fun p : ContinuousPath (SpatialCoordinates d) => ∫ q, g q ∂K (p s)) :=
    hKint.comp hevs
  have hlow : ∀ q, 0 ≤ g q + c := fun q => by
    have h1 := (abs_le.1 (hc q)).1
    linarith
  have hgint : ∀ y, Integrable g (K y) := fun y =>
    Integrable.of_bound hg.aestronglyMeasurable c
      (ae_of_all _ (fun q => (Real.norm_eq_abs (g q)).symm ▸ hc q))
  have hKbound : ∀ y, |∫ q, g q ∂K y| ≤ c := by
    intro y
    have h1 : ‖∫ q, g q ∂K y‖ ≤ c * (K y).real Set.univ :=
      norm_integral_le_of_norm_le_const
        (ae_of_all _ (fun q => (Real.norm_eq_abs (g q)).symm ▸ hc q))
    rw [Real.norm_eq_abs] at h1
    simpa using h1
  have hlowK : ∀ y, 0 ≤ ∫ q, g q ∂K y + c := fun y => by
    have h1 := (abs_le.1 (hKbound y)).1
    linarith
  have hinner : ∀ y, ∫⁻ q, ENNReal.ofReal (g q + c) ∂K y =
      ENNReal.ofReal (∫ q, g q ∂K y + c) := by
    intro y
    have hi : Integrable (fun q => g q + c) (K y) := (hgint y).add (integrable_const c)
    have h1 := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun q => hlow q))
    rw [← h1, integral_add (hgint y) (integrable_const c), integral_const]
    simp
  simp only [hinner] at h
  have hb1 : Integrable (fun p => g (ContinuousPath.shift s p)) ((K x).restrict S) :=
    Integrable.of_bound hgs.aestronglyMeasurable c
      (ae_of_all _ (fun p => (Real.norm_eq_abs _).symm ▸ hc _))
  have hb2 : Integrable (fun p => ∫ q, g q ∂K (p s)) ((K x).restrict S) :=
    Integrable.of_bound hKs.aestronglyMeasurable c
      (ae_of_all _ (fun p => (Real.norm_eq_abs _).symm ▸ hKbound _))
  have hb1' : Integrable (fun p => g (ContinuousPath.shift s p) + c) ((K x).restrict S) :=
    hb1.add (integrable_const c)
  have hb2' : Integrable (fun p => ∫ q, g q ∂K (p s) + c) ((K x).restrict S) :=
    hb2.add (integrable_const c)
  have e1 := ofReal_integral_eq_lintegral_ofReal hb1'
    (ae_of_all _ (fun p => hlow (ContinuousPath.shift s p)))
  have e2 := ofReal_integral_eq_lintegral_ofReal hb2' (ae_of_all _ (fun p => hlowK (p s)))
  rw [← e1, ← e2] at h
  have hnn1 : 0 ≤ ∫ p in S, (g (ContinuousPath.shift s p) + c) ∂K x :=
    integral_nonneg (fun p => hlow (ContinuousPath.shift s p))
  have hnn2 : 0 ≤ ∫ p in S, (∫ q, g q ∂K (p s) + c) ∂K x :=
    integral_nonneg (fun p => hlowK (p s))
  rw [ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2, integral_add hb1 (integrable_const c),
    integral_add hb2 (integrable_const c)] at h
  have h' := add_right_cancel h
  rw [integral_indicator hSm, integral_indicator hSm]
  exact h'

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- The continuous-path law starts at its starting point (from `StrongMarkov`, clause 2). -/
theorem aux_prop_uniform_resolvent_point_start {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z) (hSM : StrongMarkov L)
    (z : SpatialCoordinates d) : ∀ᵐ q ∂K z, q 0 = z := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have h1 : ∀ᵐ w ∂(L z), LifetimePath.coordinate 0 w = Cemetery.alive z := hSM.2.1 z
  rw [← hL z] at h1
  have h2 := ae_of_ae_map LifetimePath.measurable_ofContinuousPath.aemeasurable h1
  filter_upwards [h2] with q hq
  rw [LifetimePath.coordinate_ofContinuousPath] at hq
  exact Sum.inl_injective hq

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- Killed-density transfer of Lebesgue-null sets: before exiting `Q`, the position at a
positive deterministic time avoids every Lebesgue-null set almost surely. -/
theorem aux_prop_uniform_resolvent_point_killed_null {d : ℕ} (Q : Set (SpatialCoordinates d))
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (ρ : SpatialCoordinates d → ℝ) (pk : ℝ → SpatialCoordinates d → SpatialCoordinates d → ℝ)
    (hkd : IsKilledDensity L ρ Q pk) (x : SpatialCoordinates d) (hx : x ∈ Q) (s : ℝ≥0)
    (hs : 0 < s) (N0 : Set (SpatialCoordinates d)) (hN0 : volume N0 = 0) :
    K x {p | (s : ℝ≥0∞) < ContinuousPath.exitTime Q p ∧ p s ∈ N0} = 0 := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  set B := toMeasurable volume N0 with hBdef
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : volume B = 0 := by rw [hBdef, measure_toMeasurable]; exact hN0
  have h3 := hkd.2.2 (s : ℝ) (by exact_mod_cast hs) x hx B hBm
  have hzero : ∫⁻ y in B ∩ Q, ENNReal.ofReal (pk (s : ℝ) x y)
      ∂(volume.withDensity (fun y => ENNReal.ofReal (ρ y))) = 0 := by
    apply setLIntegral_measure_zero
    exact withDensity_absolutelyContinuous _ _ (measure_mono_null Set.inter_subset_left hB0)
  rw [hzero] at h3
  apply le_antisymm _ (bot_le)
  calc K x {p | (s : ℝ≥0∞) < ContinuousPath.exitTime Q p ∧ p s ∈ N0}
      ≤ K x (LifetimePath.ofContinuousPath ⁻¹'
          {w : Path d | ENNReal.ofReal (s : ℝ) < LifetimePath.exitTime Q w ∧
            LifetimePath.coordinate (Real.toNNReal (s : ℝ)) w ∈ Cemetery.alive '' B}) := by
        apply measure_mono
        intro p hp
        simp only [Set.mem_preimage, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath,
          ENNReal.ofReal_coe_nnreal, Real.toNNReal_coe, LifetimePath.coordinate_ofContinuousPath]
        exact ⟨hp.1, ⟨p s, subset_toMeasurable _ _ hp.2, rfl⟩⟩
    _ ≤ (Measure.map LifetimePath.ofContinuousPath (K x))
          {w : Path d | ENNReal.ofReal (s : ℝ) < LifetimePath.exitTime Q w ∧
            LifetimePath.coordinate (Real.toNNReal (s : ℝ)) w ∈ Cemetery.alive '' B} :=
        Measure.le_map_apply LifetimePath.measurable_ofContinuousPath.aemeasurable _
    _ = 0 := by rw [hL x]; exact h3

/-- A continuous path started inside the open set `Q` needs positive time to leave it. -/
theorem aux_prop_uniform_resolvent_point_exitTime_pos {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (p : ContinuousPath (SpatialCoordinates d)) (hp : p 0 ∈ Q) :
    0 < ContinuousPath.exitTime Q p := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), p t ∈ Q := (p.continuous.tendsto 0) (hQ.mem_nhds hp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hle : ENNReal.ofReal ε ≤ ContinuousPath.exitTime Q p := by
    rw [ContinuousPath.le_exitTime_iff]
    intro v hv
    have hv' : ¬ dist v 0 < ε := fun h => hv (hball h)
    rw [not_lt, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg v.coe_nonneg] at hv'
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hv'
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hle

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Pointwise identification of the occupation resolvent** (the `hpoint` proof step).

Let `K` be a Markov kernel of continuous-path laws whose lifetime-path image `L` is strong Markov
and has a killed density on the bounded open set `Q`.  If the occupation resolvent `RN` (defined
pointwise by the killed occupation integral) agrees Lebesgue-a.e. on `Q` with a continuous `v`
that vanishes off `Q`, then `RN = v` at EVERY point of `closure Q`.  Interior points: Markov
property at a small deterministic time `s`, the killed density to replace `RN` by `v`, and
dominated convergence as `s → 0`; boundary points: the path starts outside `Q`, so the exit time
and the occupation integral vanish. -/
theorem aux_prop_uniform_resolvent_point {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel K] (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z) (hSM : StrongMarkov L)
    (ρ : SpatialCoordinates d → ℝ) (pk : ℝ → SpatialCoordinates d → SpatialCoordinates d → ℝ)
    (hkd : IsKilledDensity L ρ Q pk) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (RN : SpatialCoordinates d → ℝ)
    (hRN : ∀ x, RN x = ∫ path, aux_prop_uniform_resolvent_point_G Q lam f path ∂K x)
    (v : SpatialCoordinates d → ℝ) (hv : Continuous v)
    (hvae : v =ᵐ[volume.restrict Q] RN) (hv0 : ∀ x ∉ Q, v x = 0) :
    ∀ x ∈ closure Q, RN x = v x := by
  classical
  intro x hxK
  have hf : Measurable (fun y => f y) := f.continuous.measurable
  have hM : ∀ y, |f y| ≤ ‖f‖ := fun y => by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
  have hGm := aux_prop_uniform_resolvent_point_G_measurable Q hQo lam (fun y => f y) hf
  have hGb := fun p => aux_prop_uniform_resolvent_point_G_abs_le Q lam hlam (fun y => f y) ‖f‖ hM p
  have h0 := aux_prop_uniform_resolvent_point_start K L hL hSM
  by_cases hxQ : x ∈ Q
  swap
  · -- boundary (and exterior) starting points
    rw [hRN x, hv0 x hxQ]
    apply integral_eq_zero_of_ae
    filter_upwards [h0 x] with p hp
    have hτ : ContinuousPath.exitTime Q p = 0 := by
      apply le_antisymm _ (bot_le)
      have h1 := ContinuousPath.exitTime_le_of_notMem Q p 0 (by rw [hp]; exact hxQ)
      simpa using h1
    show aux_prop_uniform_resolvent_point_G Q lam (fun y => f y) p = 0
    unfold aux_prop_uniform_resolvent_point_G aux_prop_uniform_resolvent_point_F
    simp only [hτ, not_lt_zero, ofPred_false, Set.indicator_empty, integral_zero]
  -- interior starting points
  -- bound on `v`
  obtain ⟨Cv, hCv⟩ := hQb.isCompact_closure.exists_bound_of_continuousOn hv.continuousOn
  have hvb : ∀ y, |v y| ≤ Cv := by
    intro y
    by_cases hy : y ∈ closure Q
    · rw [← Real.norm_eq_abs]; exact hCv y hy
    · have hyQ : y ∉ Q := fun h => hy (subset_closure h)
      rw [hv0 y hyQ, abs_zero]
      exact le_trans (norm_nonneg _) (hCv x hxK)
  -- the null set where `RN ≠ v` inside `Q`
  set N0 : Set (SpatialCoordinates d) := {y | ¬ v y = RN y} ∩ Q with hN0def
  have hN0 : volume N0 = 0 := by
    have h1 := ae_iff.1 hvae
    rwa [Measure.restrict_apply' hQo.measurableSet] at h1
  -- small times
  let sn : ℕ → ℝ≥0 := fun n => Real.toNNReal (1 / ((n : ℝ) + 1))
  have hsn_pos : ∀ n, 0 < sn n := fun n => Real.toNNReal_pos.2 (by positivity)
  have hsn : Tendsto sn atTop (𝓝 0) := by
    have h0' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (continuous_real_toNNReal.tendsto 0).comp h0'
    simpa [sn, Function.comp_def] using h1
  have hsnR : Tendsto (fun n => (sn n : ℝ)) atTop (𝓝 0) := by
    have := NNReal.tendsto_coe.2 hsn
    simpa using this
  -- the decomposition at time `sn n`
  let S : ℕ → Set (ContinuousPath (SpatialCoordinates d)) := fun n =>
    {p | ((sn n : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime Q p}
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQo)
  let A : ℕ → ℝ := fun n => ∫ p, (∫ t in Ioc (0 : ℝ) (sn n),
    aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t) ∂K x
  let I : ℕ → ℝ := fun n => ∫ p, Set.indicator (S n) (fun p => v (p (sn n))) p ∂K x
  have hdec : ∀ n, RN x = A n + Real.exp (-lam * (sn n)) * I n := by
    intro n
    set s := sn n with hs
    have hAm : Measurable (fun p : ContinuousPath (SpatialCoordinates d) =>
        ∫ t in Ioc (0 : ℝ) s, aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t) :=
      aux_prop_uniform_resolvent_point_integral_measurable Q hQo lam (fun y => f y) hf
        (volume.restrict (Ioc 0 s))
    have hAb : ∀ p : ContinuousPath (SpatialCoordinates d),
        ‖∫ t in Ioc (0 : ℝ) s, aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t‖ ≤
          ‖f‖ * s := by
      intro p
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) s)
        (C := ‖f‖) (f := aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p)
        measure_Ioc_lt_top (fun t ht =>
          aux_prop_uniform_resolvent_point_F_norm_le_const Q lam hlam (fun y => f y) ‖f‖ hM p t
            (le_of_lt ht.1))
      rwa [Real.volume_real_Ioc_of_le s.coe_nonneg, sub_zero] at h1
    have hshift : Measurable (fun p : ContinuousPath (SpatialCoordinates d) =>
        ContinuousPath.shift s p) :=
      (ContinuousPath.continuous_shift.comp (continuous_const.prodMk continuous_id)).measurable
    have hTm : Measurable (fun p => Set.indicator (S n)
        (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
          (ContinuousPath.shift s p)) p) :=
      (hGm.comp hshift).indicator (hSm n)
    have hTb : ∀ p, ‖Set.indicator (S n)
        (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
          (ContinuousPath.shift s p)) p‖ ≤ ‖f‖ / lam := by
      intro p
      by_cases hp : p ∈ S n
      · rw [Set.indicator_of_mem hp, Real.norm_eq_abs]; exact hGb _
      · rw [Set.indicator_of_notMem hp, norm_zero]; positivity
    have hpt : ∀ p, aux_prop_uniform_resolvent_point_G Q lam (fun y => f y) p =
        (∫ t in Ioc (0 : ℝ) s, aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t) +
          Real.exp (-lam * s) * Set.indicator (S n)
            (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
              (ContinuousPath.shift s p)) p := by
      intro p
      rw [aux_prop_uniform_resolvent_point_split Q hQo lam hlam (fun y => f y) hf ‖f‖ hM p s]
      congr 1
      by_cases hp : p ∈ S n
      · have hp' : (s : ℝ≥0∞) < ContinuousPath.exitTime Q p := hp
        rw [ite_eq_left hp', Set.indicator_of_mem hp]
      · have hp' : ¬ (s : ℝ≥0∞) < ContinuousPath.exitTime Q p := hp
        rw [ite_eq_right hp', Set.indicator_of_notMem hp, mul_zero]
    have hAi : Integrable (fun p : ContinuousPath (SpatialCoordinates d) =>
        ∫ t in Ioc (0 : ℝ) s, aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t)
        (K x) := Integrable.of_bound hAm.aestronglyMeasurable _ (ae_of_all _ hAb)
    have hTi : Integrable (fun p => Set.indicator (S n)
        (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
          (ContinuousPath.shift s p)) p) (K x) :=
      Integrable.of_bound hTm.aestronglyMeasurable _ (ae_of_all _ hTb)
    have hmk := aux_prop_uniform_resolvent_point_markov Q hQo K L hL hSM x s
      (aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)) hGm (‖f‖ / lam) hGb
    have hnull := aux_prop_uniform_resolvent_point_killed_null Q K L hL ρ pk hkd x hxQ s
      (hsn_pos n) N0 hN0
    have hswap : ∫ p, Set.indicator (S n)
          (fun p => ∫ q, aux_prop_uniform_resolvent_point_G Q lam (fun y => f y) q ∂K (p s)) p
          ∂K x = I n := by
      apply integral_congr_ae
      have hae : ∀ᵐ p ∂K x, p ∉ {p : ContinuousPath (SpatialCoordinates d) |
          (s : ℝ≥0∞) < ContinuousPath.exitTime Q p ∧ p s ∈ N0} :=
        measure_eq_zero_iff_ae_notMem.1 hnull
      filter_upwards [hae] with p hp
      by_cases hpS : p ∈ S n
      · rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpS, ← hRN (p s)]
        have hpQ : p s ∈ Q := ContinuousPath.mem_of_lt_exitTime Q p s hpS
        have hpN : p s ∉ N0 := fun h => hp ⟨hpS, h⟩
        by_contra hne
        exact hpN ⟨fun h => hne h.symm, hpQ⟩
      · rw [Set.indicator_of_notMem hpS, Set.indicator_of_notMem hpS]
    calc RN x = ∫ p, aux_prop_uniform_resolvent_point_G Q lam (fun y => f y) p ∂K x := hRN x
      _ = ∫ p, ((∫ t in Ioc (0 : ℝ) s,
            aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p t) +
          Real.exp (-lam * s) * Set.indicator (S n)
            (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
              (ContinuousPath.shift s p)) p) ∂K x := integral_congr_ae (ae_of_all _ hpt)
      _ = A n + Real.exp (-lam * s) * ∫ p, Set.indicator (S n)
            (fun p => aux_prop_uniform_resolvent_point_G Q lam (fun y => f y)
              (ContinuousPath.shift s p)) p ∂K x := by
          rw [integral_add hAi (hTi.const_mul _), integral_const_mul]
      _ = A n + Real.exp (-lam * s) * I n := by
          rw [← hswap]
          congr 2
  -- `A n → 0`
  have hAle : ∀ n, |A n| ≤ ‖f‖ * sn n := by
    intro n
    have h1 : ‖A n‖ ≤ ‖f‖ * sn n * (K x).real Set.univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ (fun p => by
        have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (sn n))
          (C := ‖f‖) (f := aux_prop_uniform_resolvent_point_F Q lam (fun y => f y) p)
          measure_Ioc_lt_top (fun t ht =>
            aux_prop_uniform_resolvent_point_F_norm_le_const Q lam hlam (fun y => f y) ‖f‖ hM
              p t (le_of_lt ht.1))
        rwa [Real.volume_real_Ioc_of_le (sn n).coe_nonneg, sub_zero] at h2))
    rw [Real.norm_eq_abs] at h1
    simpa using h1
  -- `I n → v x` by dominated convergence
  have hI : Tendsto I atTop (𝓝 (v x)) := by
    have hlim : Tendsto I atTop (𝓝 (∫ _p, v x ∂K x)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => Cv) (fun n => ?_)
        (integrable_const Cv) (fun n => ae_of_all _ (fun p => ?_)) ?_
      · exact ((hv.measurable.comp (continuous_eval_const (sn n)).measurable).indicator
          (hSm n)).aestronglyMeasurable
      · by_cases hp : p ∈ S n
        · rw [Set.indicator_of_mem hp, Real.norm_eq_abs]; exact hvb _
        · rw [Set.indicator_of_notMem hp, norm_zero]; exact le_trans (abs_nonneg _) (hvb x)
      · filter_upwards [h0 x] with p hp
        have hτ : 0 < ContinuousPath.exitTime Q p :=
          aux_prop_uniform_resolvent_point_exitTime_pos Q hQo p (by rw [hp]; exact hxQ)
        have hev : ∀ᶠ n in atTop, p ∈ S n := by
          have h1 : Tendsto (fun n => ((sn n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
            have := ENNReal.tendsto_coe.2 hsn
            simpa using this
          exact (tendsto_order.1 h1).2 _ hτ
        have hcont : Tendsto (fun n => v (p (sn n))) atTop (𝓝 (v x)) := by
          have h1 := (hv.tendsto (p 0)).comp ((p.continuous.tendsto 0).comp hsn)
          rw [hp] at h1
          exact h1
        refine hcont.congr' ?_
        filter_upwards [hev] with n hn
        rw [Set.indicator_of_mem hn]
    simpa using hlim
  -- conclude
  have hexp : Tendsto (fun n => Real.exp (-lam * (sn n))) atTop (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-lam * t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h1 := (hc.tendsto 0).comp hsnR
    simpa [Function.comp_def] using h1
  have hlim1 : Tendsto (fun n => Real.exp (-lam * (sn n)) * I n) atTop (𝓝 (v x)) := by
    simpa using hexp.mul hI
  have hlim2 : Tendsto (fun n => Real.exp (-lam * (sn n)) * I n) atTop (𝓝 (RN x)) := by
    have hbd : Tendsto (fun n => ‖f‖ * (sn n : ℝ)) atTop (𝓝 0) := by
      simpa using hsnR.const_mul ‖f‖
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbd
    have h1 := hdec n
    have h2 := hAle n
    rw [Real.norm_eq_abs]
    calc |Real.exp (-lam * (sn n)) * I n - RN x| = |A n| := by
          rw [h1]; rw [abs_sub_comm]; ring_nf
      _ ≤ ‖f‖ * sn n := h2
  exact tendsto_nhds_unique hlim2 hlim1

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- Masked oscillation bound on the parent's ACTUAL data (parent hypotheses verbatim).
For every level `Mb`, one sample constant `K` controls the square-mean oscillation of the zero
extension of the actual cutoff solution at every `N` whose samplewise constants are at most
`Mb`.  No boundedness of the constant ranges is assumed. -/
theorem aux_prop_uniform_resolvent_mask_campanato
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (_hps : ps.Nonempty)
    (_hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ᵐ omega ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, Kcoer N omega ≤ Mb → Khol N omega ≤ Mb →
      ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) (fun z => ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 z)) y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) (fun z => ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 z)) w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp
  have hQo : IsOpen ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) := (centeredCube (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr).isOpen
  have hQm : MeasurableSet ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) := hQo.measurableSet
  have hacQ : ∀ omega N, (muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume := fun omega N =>
    aux_prop_uniform_resolvent_cutoff_oscillation_cutoffSpeedMeasure_restrict_ac M H omega N _ _
  have hfront : ∀ omega N, cutoffSpeedMeasure M H omega N (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 := by
    intro omega N
    have hv : volume (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 := by
      change volume (frontier (Metric.ball (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri / 2))) = 0
      rw [frontier_ball _ (ne_of_gt (half_pos hr))]
      have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      exact Measure.addHaar_sphere volume _ _
    exact withDensity_absolutelyContinuous _ _ hv
  refine aux_prop_uniform_resolvent_mask_oscillation hd epsilon hepsilon hepsilon' Qtri hr P muN
    (fun N omega => E_N omega N) RN uN
    (fun N omega lam f x => Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) (fun z => ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 z)) x)
    (fun N omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    (fun _ _ _ _ => rfl) ?hRNmeas ?hsource Kmu Kcoer Khol Region hRegionBounded hNeighborhood
    ?hfinite (ae_of_all _ (fun _ _ _ _ _ => rfl)) ?hgrowth ?hcoer ?hHolder
    (ae_of_all _ (fun omega N => hacQ omega N))
  case hRNmeas =>
    filter_upwards [hfinite] with omega hfo N lam hlam f
    obtain ⟨h1, -, -, -⟩ := hfo N lam hlam f
    have hm : AEMeasurable (RN N omega lam f) (volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) :=
      (Lp.aestronglyMeasurable _).aemeasurable.congr h1.symm
    have hac' : (muN N omega).restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) ≪ volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) := by
      have := (hacQ omega N).restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
      rwa [Measure.restrict_restrict hQm, Set.inter_self] at this
    exact hm.mono_ac hac'
  case hsource =>
    filter_upwards [hfinite] with omega hfo N lam hlam f
    obtain ⟨-, h2, -, -⟩ := hfo N lam hlam f
    refine (ae_restrict_iff' hQm).2 (ae_of_all _ (fun x hx => ?_))
    have hb := h2 x hx
    have hfx : |f x| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
    have hl : |lam * RN N omega lam f x| ≤ ‖f‖ := by
      rw [abs_mul, abs_of_pos hlam]
      calc lam * |RN N omega lam f x| ≤ lam * (‖f‖ / lam) :=
            mul_le_mul_of_nonneg_left hb hlam.le
        _ = ‖f‖ := by field_simp
    calc |f x - lam * RN N omega lam f x| ≤ |f x| + |lam * RN N omega lam f x| := abs_sub _ _
      _ ≤ 2 * ‖f‖ := by linarith
  case hfinite =>
    filter_upwards [hfinite] with omega hfo N lam hlam f w
    obtain ⟨-, -, h3, -⟩ := hfo N lam hlam f
    have hae : ∀ᵐ x ∂(muN N omega), x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) := by
      change ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))), x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
      rw [ae_restrict_iff' isClosed_closure.measurableSet]
      refine measure_mono_null ?_ (hfront omega N)
      intro x hx
      rw [hQo.frontier_eq]
      by_contra hc
      exact hx (fun h1 => Classical.byContradiction (fun h2 => hc ⟨h1, h2⟩))
    rw [Measure.restrict_eq_self_of_ae_mem hae]
    exact h3 w
  case hgrowth =>
    filter_upwards [hgrowth] with omega h x hx r hr0 hr1 N
    exact (Measure.restrict_apply_le _ _).trans ((h x hx r hr0 hr1).2 N)
  case hcoer =>
    filter_upwards [hcoerN] with omega h N v
    exact ⟨(h N v).1, (h N v).2.2⟩
  case hHolder =>
    filter_upwards [hHolder] with omega h N F0 hF0 MF hMF hF0b v hv
    obtain ⟨vc, h1, h2, -, h4⟩ := h N F0 hF0 MF hMF hF0b v hv
    exact ⟨vc, h1.symm, h2, h4⟩

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- One-sample core of the masked two-subsequence argument (paper label `mfd:prop-uniform-resolvent`).

`h N` is the `N`-th cutoff resolvent at a fixed sample, `good Mb N` says the samplewise constants
at `N` are at most the level `Mb`.  Assume: at every level the good indices carry one common
continuity / zero-boundary / sup / local Holder package; some level has infinitely many good
indices; and every uniform cluster along a strictly increasing subsequence of GOOD indices of one
level (bounded constants), as a globally continuous function, has Lebesgue class `ustar` on `Q`
(variational identification on a represented subsequence).  Then there is
one continuous limit `g`, of class `ustar`, vanishing on `∂Q`, Holder on `closure Q`, and the good
indices of EVERY level converge to it uniformly on `closure Q`. -/
theorem aux_prop_uniform_resolvent_core {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQo : IsOpen Q) (hQne : Q.Nonempty) (hK : IsCompact (closure Q))
    (h : ℕ → SpatialCoordinates d → ℝ) (good : ℕ → ℕ → Prop) (S : ℝ) (hS : 0 ≤ S)
    (hold : ∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N →
      ContinuousOn (h N) (closure Q) ∧ (∀ x ∈ frontier Q, h N x = 0) ∧
      (∀ x ∈ closure Q, |h N x| ≤ S) ∧
      ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
        |h N x - h N y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (Mb0 : ℕ) (hfreq : ∃ᶠ N in atTop, good Mb0 N)
    (ustar : SpatialCoordinates d → ℝ)
    (ident : ∀ Mb : ℕ, ∀ g : C(SpatialCoordinates d, ℝ),
      (∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, good Mb (σ k)) ∧
        ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
        ∀ x ∈ closure Q, |h (σ k) x - g x| < eps) →
      ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] ustar)) :
    ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g (closure Q) ∧
      (∀ x ∈ frontier Q, g x = 0) ∧ (∀ x ∈ closure Q, |g x| ≤ S) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closure Q, ∀ y ∈ closure Q,
        |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ)) ∧
      (g =ᵐ[volume.restrict Q] ustar) ∧
      ∀ Mb : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → good Mb N →
        ∀ x ∈ closure Q, |h N x - g x| < ε := by
  classical
  set K := closure Q with hKdef
  have hKc : IsClosed K := isClosed_closure
  have hQK : Q ⊆ K := subset_closure
  have hfrK : frontier Q ⊆ K := frontier_subset_closure
  have hQm : MeasurableSet Q := hQo.measurableSet
  -- global Holder package at every level
  have hglob : ∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N →
      ContinuousOn (h N) K ∧ (∀ x ∈ frontier Q, h N x = 0) ∧ (∀ x ∈ K, |h N x| ≤ S) ∧
      ∀ x ∈ K, ∀ y ∈ K, |h N x - h N y| ≤ C * dist x y ^ (1 / 4 : ℝ) := by
    intro Mb
    obtain ⟨C, hC0, hC⟩ := hold Mb
    refine ⟨C + 2 * S, by linarith, fun N hN => ⟨(hC N hN).1, (hC N hN).2.1, (hC N hN).2.2.1, ?_⟩⟩
    exact aux_prop_uniform_resolvent_det_holder_global K (h N) C S hC0 hS (hC N hN).2.2.2
      (hC N hN).2.2.1
  -- every cluster along good indices of any level has class `ustar`
  have ident' : ∀ Mb : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ → (∀ k, good Mb (σ k)) →
      ∀ g' : SpatialCoordinates d → ℝ, ContinuousOn g' K →
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K, |h (σ k) x - g' x| < eps) →
      (∀ x ∈ frontier Q, g' x = 0) ∧ (g' =ᵐ[volume.restrict Q] ustar) := by
    intro Mb σ hσ hgood g' hg' hconv
    obtain ⟨C, -, hC⟩ := hglob Mb
    have hfr : ∀ x ∈ frontier Q, g' x = 0 := fun x hx =>
      aux_prop_uniform_resolvent_det_limit_zero K (fun k => h (σ k)) g' x (hfrK hx)
        (fun k => (hC (σ k) (hgood k)).2.1 x hx) hconv
    have hfrK' : ∀ x ∈ frontier K, g' x = 0 := fun x hx => hfr x (frontier_closure_subset hx)
    let g'' : C(SpatialCoordinates d, ℝ) :=
      ⟨fun x => if x ∈ K then g' x else 0,
        aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous K g' hKc hg' hfrK'⟩
    have hg''eq : ∀ x ∈ K, g'' x = g' x := by
      intro x hx; simp only [g'', ContinuousMap.coe_mk, ite_eq_left hx]
    have hid := ident Mb g'' ⟨σ, hσ, hgood, fun eps heps => by
      obtain ⟨k0, hk0⟩ := hconv eps heps
      exact ⟨k0, fun k hk x hx => by rw [hg''eq x hx]; exact hk0 k hk x hx⟩⟩
    refine ⟨hfr, ?_⟩
    have h1 : g' =ᵐ[volume.restrict Q] (g'' : SpatialCoordinates d → ℝ) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hQm]
      exact Filter.Eventually.of_forall (fun x hx => (hg''eq x (hQK hx)).symm)
    exact h1.trans hid
  -- existence of one cluster along level `Mb0`
  obtain ⟨σ0, hσ0, hσ0g⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨C0, hC00, hC0⟩ := hglob Mb0
  obtain ⟨τ, hτ, g, hg, hgconv⟩ := aux_prop_uniform_resolvent_subsequence_bridge_subseq_uniform_extract
    K hK (fun k => h (σ0 k)) (fun k => (hC0 (σ0 k) (hσ0g k)).1)
    ⟨S, fun k => (hC0 (σ0 k) (hσ0g k)).2.2.1⟩
    ⟨C0, hC00, fun k => (hC0 (σ0 k) (hσ0g k)).2.2.2⟩ id strictMono_id
  have hgconv' : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x ∈ K,
      |h ((σ0 ∘ τ) k) x - g x| < eps := hgconv
  obtain ⟨hgfr, hgae⟩ := ident' Mb0 (σ0 ∘ τ) (hσ0.comp hτ) (fun k => hσ0g (τ k)) g hg hgconv'
  -- pointwise limits along the extracted subsequence
  have htend : ∀ x ∈ K, Tendsto (fun k => h ((σ0 ∘ τ) k) x) atTop (𝓝 (g x)) :=
    aux_prop_uniform_resolvent_det_tendsto_of_unif K (fun k => h ((σ0 ∘ τ) k)) g hgconv'
  have hgS : ∀ x ∈ K, |g x| ≤ S := fun x hx =>
    le_of_tendsto' ((htend x hx).abs) (fun k => (hC0 _ (hσ0g (τ k))).2.2.1 x hx)
  have hgH : ∀ x ∈ K, ∀ y ∈ K, |g x - g y| ≤ C0 * dist x y ^ (1 / 4 : ℝ) := fun x hx y hy =>
    le_of_tendsto' (((htend x hx).sub (htend y hy)).abs)
      (fun k => (hC0 _ (hσ0g (τ k))).2.2.2 x hx y hy)
  refine ⟨g, hg, hgfr, hgS, ⟨C0, hC00, hgH⟩, hgae, ?_⟩
  -- convergence along the good indices of every level
  intro Mb
  obtain ⟨C, hC0', hC⟩ := hglob Mb
  exact aux_prop_uniform_resolvent_mask_det_conv K hK h (good Mb)
    (fun N hN => (hC N hN).1) ⟨S, fun N hN => (hC N hN).2.2.1⟩ C hC0'
    (fun N hN => (hC N hN).2.2.2) g
    (fun σ hσ hgood g' hg' hconv' => by
      obtain ⟨-, hg'ae⟩ := ident' Mb σ hσ hgood g' hg' hconv'
      exact aux_prop_uniform_resolvent_subsequence_bridge_eqOn_of_ae_eq Q K hQo hQne rfl g' g hg' hg
        (hg'ae.trans hgae.symm))

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- Campanato transfer on the fixed cube: a square-mean oscillation bound of order
`r^(2 beta)`, `beta ≥ 1/4`, for the zero extension of an `L²(Q)` class, fed to the parent's
Campanato criterion `hcamp` at `alpha = 1/4`, gives a continuous representative that is locally
`1/4`-Holder with constant `Cc * A` and vanishes off the cube. -/
theorem aux_prop_uniform_resolvent_camp_holder {d : ℕ} (z : SpatialCoordinates d) (s : ℝ)
    (hs : 0 < s) (Cc : ℝ)
    (hC : ∀ (z' : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
        (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
        LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
        (∀ x ∉ (centeredCube z' rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
        (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
              (u y - (volume.real (Metric.ball x r))⁻¹ *
                ∫ w in Metric.ball x r, u w) ^ 2) ≤
            A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ))) →
        ∃ v : SpatialCoordinates d → ℝ,
          v =ᵐ[volume] u ∧
          (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
            |v x - v y| ≤ Cc * A * dist x y ^ (1 / 4 : ℝ)) ∧
          ∀ x ∉ (centeredCube z' rQ hrQ : Set (SpatialCoordinates d)), v x = 0)
    (β : ℝ) (hβ : 1 / 4 ≤ β) (A : ℝ) (hA : 0 ≤ A) (w : DomainL2 (centeredCube z s hs))
    (hbound : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
          (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d)) (fun y => w y) y -
            (volume.real (Metric.ball x r))⁻¹ *
              ∫ w' in Metric.ball x r,
                Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d)) (fun y => w y) w') ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * β)) :
    ∃ v : SpatialCoordinates d → ℝ, Continuous v ∧
      v =ᵐ[volume] Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d)) (fun y => w y) ∧
      (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
        |v x - v y| ≤ Cc * A * dist x y ^ (1 / 4 : ℝ)) ∧
      ∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0 := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hs : Set (SpatialCoordinates d)) with hQ
  have hQm : MeasurableSet Q := (centeredCube z s hs).isOpen.measurableSet
  have hQfin : volume Q ≠ ∞ := (centeredCube_isBounded z hs).measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  have hw2 : MemLp (fun y => w y) 2 (volume.restrict Q) := Lp.memLp w
  have hint : Integrable (fun y => w y) (volume.restrict Q) := hw2.integrable (by norm_num)
  have hint2 : Integrable (fun y => (w y) ^ 2) (volume.restrict Q) := hw2.integrable_sq
  have hli : LocallyIntegrable (Set.indicator Q (fun y => w y)) volume :=
    ((integrable_indicator_iff hQm).2 hint).locallyIntegrable
  have hsq : (fun x => (Set.indicator Q (fun y => w y) x) ^ 2) =
      Set.indicator Q (fun y => (w y) ^ 2) := by
    funext x
    by_cases hx : x ∈ Q
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]; ring
  have hli2 : LocallyIntegrable (fun x => (Set.indicator Q (fun y => w y) x) ^ 2) volume := by
    rw [hsq]; exact ((integrable_indicator_iff hQm).2 hint2).locallyIntegrable
  have hzero : ∀ x ∉ Q, Set.indicator Q (fun y => w y) x = 0 := fun x hx =>
    Set.indicator_of_notMem hx _
  have hb' : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
          (Set.indicator Q (fun y => w y) y - (volume.real (Metric.ball x r))⁻¹ *
            ∫ w' in Metric.ball x r, Set.indicator Q (fun y => w y) w') ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ)) := by
    intro x r hr0 hr1
    refine (hbound x r hr0 hr1).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg A) measureReal_nonneg)
    exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  obtain ⟨v, hvae, hvH, hv0⟩ := hC z s hs (Set.indicator Q (fun y => w y)) A hA hli hli2 hzero hb'
  exact ⟨v, aux_prop_uniform_resolvent_det_holder_continuous v (Cc * A) (1 / 4) (by norm_num) hvH,
    hvae, hvH, hv0⟩

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- Mid-level reduction for `prop_uniform_resolvent` on a generic sample space.

Inputs are exactly what the parent supplies or what two named proof steps would supply:
* `htight` : level tightness of the samplewise constants (proved from `hmom` by
  `aux_prop_uniform_resolvent_tight_levels`);
* `hcampK` : the MASKED oscillation bound (proved from the parent hypotheses by
  `aux_prop_uniform_resolvent_mask_campanato`, i.e. the repaired child on masked data);
* `hfin`   : the first two clauses of the parent's `hfinite`;
* `hcamp`  : the parent's Campanato criterion, verbatim;
* `hpoint` : identification input (Markov/killed-density identification of the occupation resolvent
  with its continuous version,  and "u_N = 0 on ∂Q");
* `hident` : identification input (variational identification of uniform clusters along a
  subsequence on which both samplewise constants are bounded by one level, paper label `mfd:prop-uniform-resolvent`; it
  is implied by the `hidentify` binder of the closed `prop_uniform_resolvent_subsequence_bridge`).
The conclusion is the parent conclusion (on the generic cube `centeredCube z s hs`). -/
theorem aux_prop_uniform_resolvent_reduction
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (β : ℝ) (hβ : 1 / 4 ≤ β)
    (RN : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (w : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube z s hs))
    (ustar : Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube z s hs))
    (Kcoer Khol : ℕ → Ω → ℝ)
    (hmeasK : ∀ N, Measurable (Kcoer N) ∧ Measurable (Khol N))
    (hRNmeas : ∀ (N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
      (x : SpatialCoordinates d), Measurable (fun ω => RN N ω lam f x))
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℕ, ∀ N,
      P {ω | ¬ (Kcoer N ω ≤ Mb ∧ Khol N ω ≤ Mb)} ≤ ENNReal.ofReal rho)
    (hcampK : ∀ᵐ ω ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, Kcoer N ω ≤ Mb → Khol N ω ≤ Mb →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
            (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                (fun y => w N ω lam f y) y -
              (volume.real (Metric.ball x r))⁻¹ *
                ∫ w' in Metric.ball x r,
                  Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                    (fun y => w N ω lam f y) w') ^ 2) ≤
            (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * β))
    (hfin : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (RN N ω lam f =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (w N ω lam f : SpatialCoordinates d → ℝ)) ∧
        ∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)), |RN N ω lam f x| ≤ ‖f‖ / lam)
    (hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0)
    (hpoint : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ v : SpatialCoordinates d → ℝ, Continuous v →
        (v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] RN N ω lam f) →
        (∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0) →
        ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)), RN N ω lam f x = v x)
    (hident : ∀ᵐ ω ∂P, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, Kcoer (σ k) ω ≤ Mb ∧ Khol (σ k) ω ≤ Mb) ∧
            ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
              ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
                |RN (σ k) ω lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (ustar ω lam f : SpatialCoordinates d → ℝ))) :
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        Ω → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube z s hs) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube z s hs) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : Ω |
                ∃ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict ((centeredCube z s hs) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
          (∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            ∀ x ∉ ((centeredCube z s hs) : Set (SpatialCoordinates d)),
              R lam f omega x = 0)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P, ∀ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) := by
  classical
  have hQne : (centeredCube z s hs : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, by change z ∈ Metric.ball z (s / 2); exact Metric.mem_ball_self (half_pos hs)⟩
  have hK : IsCompact (closure (centeredCube z s hs : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hs).isCompact_closure
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hs : Set (SpatialCoordinates d))
    with hQdef
  have hQo : IsOpen Q := (centeredCube z s hs).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQK : Q ⊆ closure Q := subset_closure
  have hfrK : frontier Q ⊆ closure Q := frontier_subset_closure
  have hfrQ : ∀ x ∈ frontier Q, x ∉ Q := fun x hx => by
    rw [hQo.frontier_eq] at hx; exact hx.2
  have hKQ : ∀ x ∈ closure Q, x ∉ Q → x ∈ frontier Q := fun x hx hxQ => by
    rw [hQo.frontier_eq]; exact ⟨hx, hxQ⟩
  obtain ⟨Cc, hCc0, hCc⟩ := hcamp (1 / 4) ⟨by norm_num, by norm_num⟩
  let good : ℕ → ℕ → Ω → Prop := fun Mb N ω => Kcoer N ω ≤ Mb ∧ Khol N ω ≤ Mb
  -- Step A: level-uniform Holder package of the ACTUAL occupation resolvents
  have hHold : ∀ᵐ ω ∂P, ∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N ω →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ (∀ x ∈ frontier Q, RN N ω lam f x = 0) ∧
        (∀ x ∈ closure Q, |RN N ω lam f x| ≤ ‖f‖ / lam) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
          |RN N ω lam f x - RN N ω lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
    filter_upwards [hcampK, hfin, hpoint] with ω hK' hf hp
    intro Mb
    obtain ⟨Kω, hK0, hKb⟩ := hK' Mb
    refine ⟨Cc * Kω, mul_nonneg hCc0.le hK0, fun N hN lam hlam f => ?_⟩
    obtain ⟨v, hvc, hvae, hvH, hv0⟩ := aux_prop_uniform_resolvent_camp_holder z s hs Cc hCc β hβ
      (Kω * ‖f‖) (mul_nonneg hK0 (norm_nonneg f)) (w N ω lam f) (hKb N hN.1 hN.2 lam hlam f)
    have hvRN : v =ᵐ[volume.restrict Q] RN N ω lam f := by
      have h1 : v =ᵐ[volume.restrict Q] (w N ω lam f : SpatialCoordinates d → ℝ) := by
        filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem hQm] with x hx1 hx2
        rw [hx1, Set.indicator_of_mem hx2]
      exact h1.trans (hf N lam hlam f).1.symm
    have hEq : ∀ x ∈ closure Q, RN N ω lam f x = v x := hp N lam hlam f v hvc hvRN hv0
    refine ⟨hvc.continuousOn.congr (fun x hx => hEq x hx), fun x hx => ?_, fun x hx => ?_,
      fun x hx y hy hxy => ?_⟩
    · rw [hEq x (hfrK hx)]; exact hv0 x (hfrQ x hx)
    · by_cases hxQ : x ∈ Q
      · exact (hf N lam hlam f).2 x hxQ
      · rw [hEq x hx, hv0 x hxQ, abs_zero]; exact div_nonneg (norm_nonneg f) hlam.le
    · rw [hEq x hx, hEq y hy]
      calc |v x - v y| ≤ Cc * (Kω * ‖f‖) * dist x y ^ (1 / 4 : ℝ) := hvH x y hxy
        _ = Cc * Kω * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by ring
  -- first output: every cutoff, via the level `⌈max (Kcoer N) (Khol N)⌉`
  have hA : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ ∀ x ∈ frontier Q, RN N ω lam f x = 0 := by
    filter_upwards [hHold] with ω hH N lam hlam f
    obtain ⟨C, -, hC⟩ := hH ⌈max (Kcoer N ω) (Khol N ω)⌉₊
    have hN : good ⌈max (Kcoer N ω) (Khol N ω)⌉₊ N ω :=
      ⟨(le_max_left _ _).trans (Nat.le_ceil _), (le_max_right _ _).trans (Nat.le_ceil _)⟩
    exact ⟨(hC N hN lam hlam f).1, (hC N hN lam hlam f).2.1⟩
  -- Step C: levels, the good sample set, the random represented subsequence
  have hgoodmeas : ∀ Mb N, MeasurableSet {ω | good Mb N ω} := fun Mb N =>
    (measurableSet_le (hmeasK N).1 measurable_const).inter
      (measurableSet_le (hmeasK N).2 measurable_const)
  have hfreq : ∀ᵐ ω ∂P, ∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω :=
    aux_prop_uniform_resolvent_tight_frequently P good htight
  let pω : Ω → Prop := fun ω =>
    (∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N ω →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ (∀ x ∈ frontier Q, RN N ω lam f x = 0) ∧
        (∀ x ∈ closure Q, |RN N ω lam f x| ≤ ‖f‖ / lam) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
          |RN N ω lam f x - RN N ω lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
    (∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω) ∧
    (∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, good Mb (σ k) ω) ∧
            ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
              ∀ x ∈ closure Q, |RN (σ k) ω lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q]
          (ustar ω lam f : SpatialCoordinates d → ℝ)))
  have hpae : ∀ᵐ ω ∂P, pω ω := by
    filter_upwards [hHold, hfreq, hident] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set Good : Set Ω := (toMeasurable P {ω | ¬ pω ω})ᶜ with hGood
  have hGoodmeas : MeasurableSet Good := (measurableSet_toMeasurable P _).compl
  have hGoodzero : P Goodᶜ = 0 := by
    rw [hGood, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hpae
  have hGood_ae : ∀ᵐ ω ∂P, ω ∈ Good := by
    rw [ae_iff]
    simpa using! hGoodzero
  have hGood_p : ∀ ω ∈ Good, pω ω := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P _ hc)
  have hFr : ∀ Mb, MeasurableSet {ω | ∃ᶠ N in atTop, good Mb N ω} := fun Mb =>
    aux_prop_uniform_resolvent_det_measurableSet_frequently (fun N ω => good Mb N ω)
      (fun N => hgoodmeas Mb N)
  have hq : ∀ ω, ∃ Mb : ℕ, (∃ᶠ N in atTop, good Mb N ω) ∨
      ¬ ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω := by
    intro ω
    by_cases h : ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω
    · obtain ⟨Mb', h'⟩ := h
      exact ⟨Mb', Or.inl h'⟩
    · exact ⟨0, Or.inr h⟩
  let lev : Ω → ℕ := fun ω => Nat.find (hq ω)
  have hlev : Measurable lev := by
    refine measurable_find hq (fun k => ?_)
    have heq : {x | (∃ᶠ N in atTop, good k N x) ∨ ¬ ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N x} =
        {x | ∃ᶠ N in atTop, good k N x} ∪ (⋃ Mb', {x | ∃ᶠ N in atTop, good Mb' N x})ᶜ := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
    rw [heq]
    exact (hFr k).union (MeasurableSet.iUnion hFr).compl
  have hlev_spec : ∀ ω, (∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω) →
      ∃ᶠ N in atTop, good (lev ω) N ω := by
    intro ω h
    rcases Nat.find_spec (hq ω) with h1 | h1
    · exact h1
    · exact absurd h h1
  have hr : ∀ ω (k : ℕ), ∃ N : ℕ, (k ≤ N ∧ good (lev ω) N ω) ∨
      ¬ ∃ᶠ M in atTop, good (lev ω) M ω := by
    intro ω k
    by_cases h : ∃ᶠ M in atTop, good (lev ω) M ω
    · obtain ⟨N, hN, hg⟩ := Filter.frequently_atTop.1 h k
      exact ⟨N, Or.inl ⟨hN, hg⟩⟩
    · exact ⟨0, Or.inr h⟩
  let nxt : Ω → ℕ → ℕ := fun ω k => Nat.find (hr ω k)
  have hnxt : ∀ k, Measurable (fun ω => nxt ω k) := by
    intro k
    exact measurable_find (fun ω => hr ω k) (fun N =>
      aux_prop_uniform_resolvent_det_measurableSet_index
        (fun m ω => (k ≤ N ∧ good m N ω) ∨ ¬ ∃ᶠ M in atTop, good m M ω)
        (fun m => ((MeasurableSet.const (k ≤ N)).inter (hgoodmeas m N)).union (hFr m).compl)
        lev hlev)
  have hnxt_spec : ∀ ω, (∃ᶠ M in atTop, good (lev ω) M ω) → ∀ k,
      k ≤ nxt ω k ∧ good (lev ω) (nxt ω k) ω := by
    intro ω h k
    rcases Nat.find_spec (hr ω k) with h1 | h1
    · exact h1
    · exact absurd h h1
  -- Step D: one sample
  have hmain : ∀ ω ∈ Good, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g (closure Q) ∧
        (∀ x ∈ frontier Q, g x = 0) ∧ (∀ x ∈ closure Q, |g x| ≤ ‖f‖ / lam) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closure Q, ∀ y ∈ closure Q,
          |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ)) ∧
        (g =ᵐ[volume.restrict Q] (ustar ω lam f : SpatialCoordinates d → ℝ)) ∧
        (∀ Mb : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → good Mb N ω →
          ∀ x ∈ closure Q, |RN N ω lam f x - g x| < ε) ∧
        (∀ x ∈ closure Q, limsup (fun k => RN (nxt ω k) ω lam f x) atTop = g x) := by
    intro ω hω lam hlam f
    obtain ⟨hH, hF, hI⟩ := hGood_p ω hω
    have hlevF := hlev_spec ω hF
    obtain ⟨g, hgc, hgfr, hgS, hgH, hgae, hgconv⟩ := aux_prop_uniform_resolvent_core Q hQo hQne hK
      (fun N => RN N ω lam f) (fun Mb N => good Mb N ω) (‖f‖ / lam)
      (div_nonneg (norm_nonneg f) hlam.le)
      (fun Mb => by
        obtain ⟨C, hC0, hC⟩ := hH Mb
        exact ⟨C * ‖f‖, mul_nonneg hC0 (norm_nonneg f), fun N hN => hC N hN lam hlam f⟩)
      (lev ω) hlevF (ustar ω lam f) (fun Mb g hg => hI lam hlam f g Mb hg)
    refine ⟨g, hgc, hgfr, hgS, hgH, hgae, hgconv, fun x hx => ?_⟩
    apply Tendsto.limsup_eq
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨N0, hN0⟩ := hgconv (lev ω) e he
    refine ⟨N0, fun k hk => ?_⟩
    obtain ⟨hk1, hk2⟩ := hnxt_spec ω hlevF k
    rw [Real.dist_eq]
    exact hN0 (nxt ω k) (hk.trans hk1) hk2 x hx
  -- Step E: the measurable limit
  let Rfun : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → Ω →
      SpatialCoordinates d → ℝ := fun lam f ω x =>
    if ω ∈ Good ∧ 0 < lam then
      (if x ∈ closure Q then limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) else 0
  have hRcont : ∀ lam f ω, Continuous (Rfun lam f ω) := by
    intro lam f ω
    by_cases hc : ω ∈ Good ∧ 0 < lam
    · obtain ⟨g, hgc, hgfr, -, -, -, -, hlim⟩ := hmain ω hc.1 lam hc.2 f
      have heq : Rfun lam f ω = fun x => if x ∈ closure Q then g x else 0 := by
        funext x
        simp only [Rfun, ite_eq_left hc]
        by_cases hx : x ∈ closure Q
        · rw [ite_eq_left hx, ite_eq_left hx, hlim x hx]
        · rw [ite_eq_right hx, ite_eq_right hx]
      rw [heq]
      exact aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous (closure Q) g
        isClosed_closure hgc (fun x hx => hgfr x (frontier_closure_subset hx))
    · have heq : Rfun lam f ω = fun _ => 0 := by
        funext x
        simp only [Rfun, ite_eq_right hc]
      rw [heq]
      exact continuous_const
  let R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → Ω →
      C(SpatialCoordinates d, ℝ) := fun lam f ω => ⟨Rfun lam f ω, hRcont lam f ω⟩
  have hRg : ∀ ω ∈ Good, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ∀ x ∈ closure Q,
        R lam f ω x = limsup (fun k => RN (nxt ω k) ω lam f x) atTop := by
    intro ω hω lam hlam f x hx
    change Rfun lam f ω x = _
    simp only [Rfun, ite_eq_left (And.intro hω hlam), ite_eq_left hx]
  have hRout : ∀ ω ∉ Good, ∀ lam f x, R lam f ω x = 0 := by
    intro ω hω lam f x
    change Rfun lam f ω x = 0
    simp only [Rfun]
    rw [ite_eq_right (fun h => hω h.1)]
  have hRmeas_eval : ∀ lam f (x : SpatialCoordinates d), Measurable (fun ω => R lam f ω x) := by
    intro lam f x
    change Measurable (fun ω => if ω ∈ Good ∧ 0 < lam then
      (if x ∈ closure Q then limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) else 0)
    have hseq : ∀ k, Measurable (fun ω => RN (nxt ω k) ω lam f x) := fun k =>
      aux_prop_uniform_resolvent_det_measurable_index (fun n ω => RN n ω lam f x)
        (fun n => hRNmeas n lam f x) (fun ω => nxt ω k) (hnxt k)
    have hin : Measurable (fun ω => if x ∈ closure Q then
        limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) := by
      by_cases hx : x ∈ closure Q
      · simp only [ite_eq_left hx]; exact Measurable.limsup hseq
      · simp only [ite_eq_right hx]; exact measurable_const
    exact Measurable.ite (hGoodmeas.inter (MeasurableSet.const (0 < lam))) hin measurable_const
  refine ⟨R, hA, fun lam _ f => aux_prop_uniform_resolvent_det_measurable_contmap_of_eval (R lam f)
    (hRmeas_eval lam f), ?_, ?_, ?_⟩
  · intro lam hlam f
    exact aux_prop_uniform_resolvent_mask_prob_bound P (closure Q) hK
      (fun N ω x => RN N ω lam f x) (fun ω x => R lam f ω x)
      (fun N x => hRNmeas N lam f x) (hRmeas_eval lam f)
      (by filter_upwards [hA] with ω h N; exact (h N lam hlam f).1)
      (ae_of_all _ (fun ω => (R lam f ω).continuous.continuousOn))
      good hgoodmeas htight
      (by
        filter_upwards [hGood_ae] with ω hω
        intro Mb ε hε
        obtain ⟨g, -, -, -, -, -, hgconv, hlim⟩ := hmain ω hω lam hlam f
        obtain ⟨N0, hN0⟩ := hgconv Mb ε hε
        refine ⟨N0, fun N hN hg x hx => ?_⟩
        rw [hRg ω hω lam hlam f x hx, hlim x hx]
        exact hN0 N hN hg x hx)
  · intro lam hlam f
    filter_upwards [hGood_ae] with ω hω
    obtain ⟨g, -, hgfr, hgS, ⟨C, hC0, hgH⟩, hgae, -, hlim⟩ := hmain ω hω lam hlam f
    have hRx : ∀ x ∈ closure Q, R lam f ω x = g x := fun x hx => by
      rw [hRg ω hω lam hlam f x hx, hlim x hx]
    refine ⟨?_, ?_⟩
    · have h1 : (R lam f ω : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := by
        rw [Filter.EventuallyEq, ae_restrict_iff' hQm]
        exact Filter.Eventually.of_forall (fun x hx => hRx x (hQK hx))
      exact h1.trans hgae
    · have hzero : ∀ x ∉ Q, R lam f ω x = 0 := by
        intro x hx
        by_cases hxK : x ∈ closure Q
        · rw [hRx x hxK]; exact hgfr x (hKQ x hxK hx)
        · change Rfun lam f ω x = 0
          simp only [Rfun, ite_eq_left (And.intro hω hlam), ite_eq_right hxK]
      by_cases hf0 : ‖f‖ = 0
      · refine ⟨1, one_pos, fun x hx y hy => ?_, hzero⟩
        have hgx : g x = 0 := by
          have := hgS x hx; rw [hf0, zero_div] at this; exact abs_nonpos_iff.1 this
        have hgy : g y = 0 := by
          have := hgS y hy; rw [hf0, zero_div] at this; exact abs_nonpos_iff.1 this
        rw [hRx x hx, hRx y hy, hgx, hgy, hf0]
        simp
      · have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf0)
        refine ⟨C / ‖f‖ + 1, by positivity, fun x hx y hy => ?_, hzero⟩
        rw [hRx x hx, hRx y hy]
        calc |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ) := hgH x hx y hy
          _ ≤ (C / ‖f‖ + 1) * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
              rw [add_mul, div_mul_cancel₀ C hf0]
              linarith
  · intro lam hlam f
    filter_upwards [hGood_ae] with ω hω x hx
    obtain ⟨g, -, -, hgS, -, -, -, hlim⟩ := hmain ω hω lam hlam f
    rw [hRg ω hω lam hlam f x hx, hlim x hx]
    exact hgS x hx

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- Generic form of the FIRST output of `prop_uniform_resolvent` (every cutoff resolvent
is continuous on the closed cube and vanishes on its frontier), from the masked oscillation
bound, the parent's `hfinite` clauses, the Campanato criterion, and the pointwise
identification step.  No boundedness of the constant ranges, no identification of clusters. -/
theorem aux_prop_uniform_resolvent_first_generic
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (β : ℝ) (hβ : 1 / 4 ≤ β)
    (RN : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (w : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube z s hs))
    (Kcoer Khol : ℕ → Ω → ℝ)
    (hcampK : ∀ᵐ ω ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, Kcoer N ω ≤ Mb → Khol N ω ≤ Mb →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
            (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                (fun y => w N ω lam f y) y -
              (volume.real (Metric.ball x r))⁻¹ *
                ∫ w' in Metric.ball x r,
                  Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                    (fun y => w N ω lam f y) w') ^ 2) ≤
            (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * β))
    (hfin : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (RN N ω lam f =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (w N ω lam f : SpatialCoordinates d → ℝ)) ∧
        ∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)), |RN N ω lam f x| ≤ ‖f‖ / lam)
    (hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0)
    (hpoint : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ v : SpatialCoordinates d → ℝ, Continuous v →
        (v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] RN N ω lam f) →
        (∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0) →
        ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)), RN N ω lam f x = v x) :
    ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure (centeredCube z s hs : Set (SpatialCoordinates d))) ∧
        ∀ x ∈ frontier (centeredCube z s hs : Set (SpatialCoordinates d)), RN N ω lam f x = 0 := by
  have hQo : IsOpen (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    (centeredCube z s hs).isOpen
  have hQm := hQo.measurableSet
  obtain ⟨Cc, hCc0, hCc⟩ := hcamp (1 / 4) ⟨by norm_num, by norm_num⟩
  filter_upwards [hcampK, hfin, hpoint] with ω hK' hf hp
  intro N lam hlam f
  obtain ⟨Kω, hK0, hKb⟩ := hK' ⌈max (Kcoer N ω) (Khol N ω)⌉₊
  obtain ⟨v, hvc, hvae, -, hv0⟩ := aux_prop_uniform_resolvent_camp_holder z s hs Cc hCc β hβ
    (Kω * ‖f‖) (mul_nonneg hK0 (norm_nonneg f)) (w N ω lam f)
    (hKb N ((le_max_left _ _).trans (Nat.le_ceil _)) ((le_max_right _ _).trans (Nat.le_ceil _))
      lam hlam f)
  have hvRN : v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
      RN N ω lam f := by
    have h1 : v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
        (w N ω lam f : SpatialCoordinates d → ℝ) := by
      filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem hQm] with x hx1 hx2
      rw [hx1, Set.indicator_of_mem hx2]
    exact h1.trans (hf N lam hlam f).1.symm
  have hEq := hp N lam hlam f v hvc hvRN hv0
  refine ⟨hvc.continuousOn.congr (fun x hx => hEq x hx), fun x hx => ?_⟩
  rw [hEq x (frontier_subset_closure hx)]
  apply hv0 x
  rw [hQo.frontier_eq] at hx
  exact hx.2

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- CONDITIONAL (not a closure of the parent).  The `prop_uniform_resolvent`
header verbatim, with exactly two additional proof-step inputs inserted before the
conclusion (which is verbatim):
* `hpoint` : the actual occupation resolvent agrees on `closure Q` with every continuous
  function that vanishes off `Q` and equals it a.e. on `Q` (Markov property at deterministic
  times + killed density + path continuity; derivable from `hRN`, `hL`, `hLlocal`, `hLstrong`, boundary part "u_N = 0 on ∂Q");
* `hident` : every uniform cluster of the actual resolvents along a strictly increasing
  subsequence on which `Kcoer` and `Khol` are bounded by one level `Mb` (a represented
  subsequence) has Lebesgue class `ustar` (variational identification, paper label `mfd:prop-uniform-resolvent`; it is
  implied by the `hidentify` input of the closed `prop_uniform_resolvent_subsequence_bridge`).
Everything else, in particular the unavailable `hconstants`, is proved here: masking + tightness
from `hmom` replace any samplewise boundedness of the constant ranges. -/
theorem aux_prop_uniform_resolvent_of_point_ident
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (hps : ps.Nonempty)
    (hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ (_hpoint : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ v : SpatialCoordinates d → ℝ, Continuous v →
          (v =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] RN N omega lam f) →
          (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), v x = 0) →
          ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), RN N omega lam f x = v x)
      (_hident : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
          (∃ σ : ℕ → ℕ, StrictMono σ ∧
              (∀ k, Kcoer (σ k) omega ≤ Mb ∧ Khol (σ k) omega ≤ Mb) ∧
              ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  |RN (σ k) omega lam f x - g x| < eps) →
          ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ))),
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : BilateralField d |
                ∃ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
          (∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            ∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              R lam f omega x = 0)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P, ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp hpoint hident
  have hPprob : IsProbabilityMeasure P := by
    show IsProbabilityMeasure (chaosSampleLaw M).toMeasure
    infer_instance
  obtain ⟨p0, hp0⟩ := hps
  have htight := aux_prop_uniform_resolvent_tight_levels P Kcoer Khol p0 (hps_ge p0 hp0)
    (hmom p0 hp0).2.1 (hmom p0 hp0).2.2
  have hcampK := aux_prop_uniform_resolvent_mask_campanato hd epsilon hepsilon hepsilon' ps
    ⟨p0, hp0⟩ hps_ge Qtri hr M H HI PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas
    hmosco muFull hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar hmin uN
    hfinite SInterp hcamp
  have hβ : (1 / 4 : ℝ) ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  have hfin : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (RN N omega lam f =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
          (((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ))) ∧
        ∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam := by
    filter_upwards [hfinite] with omega h N lam hlam f
    exact ⟨(h N lam hlam f).1, (h N lam hlam f).2.1⟩
  exact aux_prop_uniform_resolvent_reduction P (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (1 / 2 - ((d : ℝ) + 2) * epsilon) hβ RN
    (fun N omega lam f => (uN N omega lam f : SobolevData (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1)
    ustar Kcoer Khol (fun N => ⟨hmeas.2.1 N, hmeas.2.2 N⟩) hRNmeas htight hcampK hfin hcamp
    hpoint hident

end SubdiffusiveProcess.Paper
end

section


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- The pointwise identification proof step `hpoint`, proved from the parent hypotheses
`hRN`, `hL`, `hLlocal` (killed density on the cube), `hLstrong` and `hKN`
(via `aux_prop_uniform_resolvent_point`). -/
theorem aux_prop_uniform_resolvent_hpoint
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    (_hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (_hps : ps.Nonempty)
    (_hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ v : SpatialCoordinates d → ℝ, Continuous v →
          (v =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] RN N omega lam f) →
          (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), v x = 0) →
          ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), RN N omega lam f x = v x := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp
  have hQo : IsOpen ((centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) :=
    (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr).isOpen
  have hQb := centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr
  filter_upwards [hLlocal, hLstrong] with omega hLD hSM
  intro N lam hlam f v hv hvae hv0
  have : IsMarkovKernel (KN N) := hKN N
  let K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (Prod.mk omega) measurable_prodMk_left
  have hKz : ∀ z, K z = KN N (omega, z) := fun z => Kernel.comap_apply _ _ _
  have hLz : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L N omega z := fun z => by
    rw [hKz]; exact hL N omega z
  obtain ⟨pk, hpk, -⟩ := (hLD N).2 _ hQo hQb
  exact aux_prop_uniform_resolvent_point _ hQo hQb K (L N omega) hLz (hSM N) _ pk hpk lam hlam f
    (RN N omega lam f) (fun x => by rw [hRN N omega lam f x, hKz x]; rfl) v hv hvae hv0

/-- The FIRST output of the `prop_uniform_resolvent` conclusion, proved from
the parent hypotheses: almost surely, every actual cutoff occupation resolvent is
continuous on the closed cube and vanishes on its frontier. -/
theorem aux_prop_uniform_resolvent_first_output
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (hps : ps.Nonempty)
    (hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0 := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp
  have hpoint := aux_prop_uniform_resolvent_hpoint hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr M H HI PN KN hKN hin L hL hLlocal
    hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region hRegionBounded hNeighborhood Kmu
    Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ
    ustar hmin uN hfinite SInterp hcamp
  have hcampK := aux_prop_uniform_resolvent_mask_campanato hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr M H HI PN KN hKN hin L hL hLlocal
    hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region hRegionBounded hNeighborhood Kmu
    Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ
    ustar hmin uN hfinite SInterp hcamp
  have hβ : (1 / 4 : ℝ) ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  have hfin : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (RN N omega lam f =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
          (((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ))) ∧
        ∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam := by
    filter_upwards [hfinite] with omega h N lam hlam f
    exact ⟨(h N lam hlam f).1, (h N lam hlam f).2.1⟩
  exact aux_prop_uniform_resolvent_first_generic P (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (1 / 2 - ((d : ℝ) + 2) * epsilon) hβ RN
    (fun N omega lam f => (uN N omega lam f : SobolevData (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1)
    Kcoer Khol hcampK hfin hcamp hpoint

/-- CONDITIONAL (not a closure of the parent): the `prop_uniform_resolvent` header
verbatim with exactly ONE additional input `hident` (variational identification of uniform
clusters along a represented subsequence with bounded constants, paper label `mfd:prop-uniform-resolvent`) inserted
before the verbatim conclusion.  Everything else is proved, including `hpoint`. -/
theorem aux_prop_uniform_resolvent_of_ident
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (hps : ps.Nonempty)
    (hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ (_hident : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
          (∃ σ : ℕ → ℕ, StrictMono σ ∧
              (∀ k, Kcoer (σ k) omega ≤ Mb ∧ Khol (σ k) omega ≤ Mb) ∧
              ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  |RN (σ k) omega lam f x - g x| < eps) →
          ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ))),
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : BilateralField d |
                ∃ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
          (∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            ∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              R lam f omega x = 0)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P, ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp hident
  exact aux_prop_uniform_resolvent_of_point_ident hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr M H HI PN KN hKN hin L hL hLlocal
    hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region hRegionBounded hNeighborhood Kmu
    Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ
    ustar hmin uN hfinite SInterp hcamp
    (aux_prop_uniform_resolvent_hpoint hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr M H HI PN KN hKN hin L hL hLlocal
    hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region hRegionBounded hNeighborhood Kmu
    Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ
    ustar hmin uN hfinite SInterp hcamp) hident

end SubdiffusiveProcess.Paper
end

section

/-!
# Local (vague) convergence ⇒ convergence of integrals over a closed cube with null frontier

Auxiliary argument for the `hident` identification of `prop_uniform_resolvent`.
Generic measure theory; no project-specific hypotheses.
-/


open Filter MeasureTheory Topology Set Metric
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- ε-sandwich for real sequences. -/
theorem aux_prop_uniform_resolvent_ident_sandwich (a : ℕ → ℝ) (A : ℝ)
    (L U : ℕ → ℕ → ℝ) (l u : ℕ → ℝ)
    (hL : ∀ n k, L n k ≤ a k) (hU : ∀ n k, a k ≤ U n k)
    (hLk : ∀ n, Tendsto (L n) atTop (𝓝 (l n))) (hUk : ∀ n, Tendsto (U n) atTop (𝓝 (u n)))
    (hl : Tendsto l atTop (𝓝 A)) (hu : Tendsto u atTop (𝓝 A)) :
    Tendsto a atTop (𝓝 A) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.1 hl (ε / 2) (by linarith)
  obtain ⟨n2, hn2⟩ := Metric.tendsto_atTop.1 hu (ε / 2) (by linarith)
  obtain ⟨k1, hk1⟩ := Metric.tendsto_atTop.1 (hLk (max n1 n2)) (ε / 2) (by linarith)
  obtain ⟨k2, hk2⟩ := Metric.tendsto_atTop.1 (hUk (max n1 n2)) (ε / 2) (by linarith)
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have e1 := hn1 (max n1 n2) (le_max_left _ _)
  have e2 := hn2 (max n1 n2) (le_max_right _ _)
  have e3 := hk1 k (le_of_max_le_left hk)
  have e4 := hk2 k (le_of_max_le_right hk)
  have h1 := hL (max n1 n2) k
  have h2 := hU (max n1 n2) k
  rw [Real.dist_eq, abs_lt] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-- A continuous function vanishing off a compact set of finite measure is integrable. -/
theorem aux_prop_uniform_resolvent_ident_integrable_of_vanish {d : ℕ}
    (ν : Measure (SpatialCoordinates d)) (S : Set (SpatialCoordinates d))
    (hS : IsCompact S) (hνS : ν S < ∞)
    (φ : SpatialCoordinates d → ℝ) (hφ : Continuous φ) (hvan : ∀ x ∉ S, φ x = 0) :
    Integrable φ ν := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hφ.continuousOn
  have hon : IntegrableOn φ S ν := by
    refine Measure.integrableOn_of_bounded (M := C) hνS.ne hφ.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
    exact hC x hx
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro x hx
  by_contra hxS
  exact hx (hvan x hxS)

/-- A continuous function is integrable on a compact set of finite measure. -/
theorem aux_prop_uniform_resolvent_ident_integrableOn {d : ℕ}
    (ν : Measure (SpatialCoordinates d)) (S : Set (SpatialCoordinates d))
    (hS : IsCompact S) (hνS : ν S < ∞)
    (φ : SpatialCoordinates d → ℝ) (hφ : Continuous φ) :
    IntegrableOn φ S ν := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C) hνS.ne hφ.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
  exact hC x hx

/-- Outer cutoff `max 0 (1 - infDist x K / δ)`. -/
def aux_prop_uniform_resolvent_ident_outer {d : ℕ} (K : Set (SpatialCoordinates d)) (δ : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  max 0 (1 - infDist x K / δ)

/-- Inner cutoff `min 1 (infDist x Uᶜ / δ)`. -/
def aux_prop_uniform_resolvent_ident_inner {d : ℕ} (U : Set (SpatialCoordinates d)) (δ : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  min 1 (infDist x Uᶜ / δ)

theorem aux_prop_uniform_resolvent_ident_outer_continuous {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) : Continuous (aux_prop_uniform_resolvent_ident_outer K δ) := by
  unfold aux_prop_uniform_resolvent_ident_outer
  fun_prop

theorem aux_prop_uniform_resolvent_ident_inner_continuous {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) : Continuous (aux_prop_uniform_resolvent_ident_inner U δ) := by
  unfold aux_prop_uniform_resolvent_ident_inner
  fun_prop

theorem aux_prop_uniform_resolvent_ident_outer_nonneg {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) : 0 ≤ aux_prop_uniform_resolvent_ident_outer K δ x :=
  le_max_left _ _

theorem aux_prop_uniform_resolvent_ident_outer_le_one {d : ℕ} (K : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) :
    aux_prop_uniform_resolvent_ident_outer K δ x ≤ 1 := by
  unfold aux_prop_uniform_resolvent_ident_outer
  refine max_le zero_le_one ?_
  have : 0 ≤ infDist x K / δ := div_nonneg infDist_nonneg hδ.le
  linarith

theorem aux_prop_uniform_resolvent_ident_outer_of_mem {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) (hx : x ∈ K) :
    aux_prop_uniform_resolvent_ident_outer K δ x = 1 := by
  unfold aux_prop_uniform_resolvent_ident_outer
  rw [infDist_zero_of_mem hx, zero_div, sub_zero]
  exact max_eq_right zero_le_one

theorem aux_prop_uniform_resolvent_ident_outer_of_le {d : ℕ} (K : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) (hx : δ ≤ infDist x K) :
    aux_prop_uniform_resolvent_ident_outer K δ x = 0 := by
  unfold aux_prop_uniform_resolvent_ident_outer
  refine max_eq_left ?_
  have : 1 ≤ infDist x K / δ := by rw [le_div_iff₀ hδ]; linarith
  linarith

theorem aux_prop_uniform_resolvent_ident_inner_nonneg {d : ℕ} (U : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) :
    0 ≤ aux_prop_uniform_resolvent_ident_inner U δ x :=
  le_min zero_le_one (div_nonneg infDist_nonneg hδ.le)

theorem aux_prop_uniform_resolvent_ident_inner_le_one {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) : aux_prop_uniform_resolvent_ident_inner U δ x ≤ 1 :=
  min_le_left _ _

theorem aux_prop_uniform_resolvent_ident_inner_of_notMem {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) (hx : x ∉ U) :
    aux_prop_uniform_resolvent_ident_inner U δ x = 0 := by
  unfold aux_prop_uniform_resolvent_ident_inner
  rw [infDist_zero_of_mem (show x ∈ Uᶜ from hx), zero_div]
  exact min_eq_right zero_le_one

theorem aux_prop_uniform_resolvent_ident_inner_of_le {d : ℕ} (U : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) (hx : δ ≤ infDist x Uᶜ) :
    aux_prop_uniform_resolvent_ident_inner U δ x = 1 := by
  unfold aux_prop_uniform_resolvent_ident_inner
  refine min_eq_left ?_
  rw [le_div_iff₀ hδ]
  linarith

/-- Outside the closed `δ`-thickening of a nonempty compact `K`, the outer cutoff vanishes. -/
theorem aux_prop_uniform_resolvent_ident_outer_vanish {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hKne : K.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (x : SpatialCoordinates d) (hx : x ∉ cthickening δ K) :
    aux_prop_uniform_resolvent_ident_outer K δ x = 0 := by
  apply aux_prop_uniform_resolvent_ident_outer_of_le K hδ
  obtain ⟨y, hyK, hy⟩ := hK.exists_infDist_eq_dist hKne x
  rw [hy]
  by_contra hlt
  exact hx (mem_cthickening_of_dist_le x y δ K hyK (le_of_lt (not_le.1 hlt)))

/-- The positive-part version of the restricted-integral convergence. -/
theorem aux_prop_uniform_resolvent_ident_restrict_tendsto_nonneg {d : ℕ}
    (νF : ℕ → Measure (SpatialCoordinates d)) (μF : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hνfin : ∀ k, νF k (cthickening δ0 (closure U)) < ∞)
    (hμfin : μF (cthickening δ0 (closure U)) < ∞)
    (hconv : MeasuresConvergeLocally νF μF)
    (hfr : μF (frontier U) = 0)
    (h : SpatialCoordinates d → ℝ) (hh : Continuous h) (hpos : ∀ x, 0 ≤ h x) :
    Tendsto (fun k => ∫ x, h x ∂((νF k).restrict (closure U))) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict (closure U)))) := by
  set K := closure U with hKdef
  set S := cthickening δ0 K with hSdef
  have hKne : K.Nonempty := hUne.mono subset_closure
  have hKcl : IsClosed K := isClosed_closure
  have hKm : MeasurableSet K := hKcl.measurableSet
  have hScpt : IsCompact S := hK.cthickening
  have hKS : K ⊆ S := self_subset_cthickening K
  set δ : ℕ → ℝ := fun n => δ0 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hδ0 (by positivity)
  have hδle : ∀ n, δ n ≤ δ0 := fun n => div_le_self hδ0.le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [hδdef] using h1.const_div_atTop δ0
  -- eventually `δ n < c` for any `c > 0`
  have hδev : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, δ n < c := fun c hc =>
    (tendsto_order.1 hδlim).2 c hc
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn hh.continuousOn
  set χo : ℕ → SpatialCoordinates d → ℝ := fun n =>
    aux_prop_uniform_resolvent_ident_outer K (δ n) with hχo
  set χi : ℕ → SpatialCoordinates d → ℝ := fun n =>
    aux_prop_uniform_resolvent_ident_inner U (δ n) with hχi
  have hχo_app : ∀ n x, χo n x = aux_prop_uniform_resolvent_ident_outer K (δ n) x :=
    fun _ _ => rfl
  have hχi_app : ∀ n x, χi n x = aux_prop_uniform_resolvent_ident_inner U (δ n) x :=
    fun _ _ => rfl
  have hχo_cont : ∀ n, Continuous (χo n) := fun n =>
    aux_prop_uniform_resolvent_ident_outer_continuous K (δ n)
  have hχi_cont : ∀ n, Continuous (χi n) := fun n =>
    aux_prop_uniform_resolvent_ident_inner_continuous U (δ n)
  have hχo_van : ∀ n, ∀ x ∉ S, χo n x = 0 := by
    intro n x hx
    apply aux_prop_uniform_resolvent_ident_outer_vanish K hK hKne (hδpos n)
    intro hx'
    exact hx (cthickening_mono (hδle n) K hx')
  have hχi_van : ∀ n, ∀ x ∉ K, χi n x = 0 := by
    intro n x hx
    exact aux_prop_uniform_resolvent_ident_inner_of_notMem U (δ n) x
      (fun hxU => hx (subset_closure hxU))
  -- compactly supported test functions
  have hcs_o : ∀ n, HasCompactSupport (fun x => h x * χo n x) := by
    intro n
    refine HasCompactSupport.intro hScpt ?_
    intro x hx
    rw [hχo_van n x hx, mul_zero]
  have hcs_i : ∀ n, HasCompactSupport (fun x => h x * χi n x) := by
    intro n
    refine HasCompactSupport.intro hK ?_
    intro x hx
    rw [hχi_van n x hx, mul_zero]
  let Fo : ℕ → C_c(SpatialCoordinates d, ℝ) := fun n =>
    ⟨⟨fun x => h x * χo n x, hh.mul (hχo_cont n)⟩, hcs_o n⟩
  let Fi : ℕ → C_c(SpatialCoordinates d, ℝ) := fun n =>
    ⟨⟨fun x => h x * χi n x, hh.mul (hχi_cont n)⟩, hcs_i n⟩
  -- integrability
  have hint_o : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      Integrable (fun x => h x * χo n x) ν := by
    intro ν hν n
    exact aux_prop_uniform_resolvent_ident_integrable_of_vanish ν S hScpt hν _
      (hh.mul (hχo_cont n)) (fun x hx => by rw [hχo_van n x hx, mul_zero])
  have hint_i : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      Integrable (fun x => h x * χi n x) ν := by
    intro ν hν n
    refine aux_prop_uniform_resolvent_ident_integrable_of_vanish ν S hScpt hν _
      (hh.mul (hχi_cont n)) (fun x hx => ?_)
    rw [hχi_van n x (fun hxK => hx (hKS hxK)), mul_zero]
  have hint_K : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ →
      Integrable (K.indicator h) ν := by
    intro ν hν
    rw [integrable_indicator_iff hKm]
    exact (aux_prop_uniform_resolvent_ident_integrableOn ν S hScpt hν h hh).mono_set hKS
  -- sandwich inequalities
  have hupper : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      ∫ x, h x ∂(ν.restrict K) ≤ ∫ x, h x * χo n x ∂ν := by
    intro ν hν n
    rw [← integral_indicator hKm]
    refine integral_mono (hint_K ν hν) (hint_o ν hν n) (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, hχo_app, aux_prop_uniform_resolvent_ident_outer_of_mem K _ x hx, mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (hpos x) (aux_prop_uniform_resolvent_ident_outer_nonneg K _ x)
  have hlower : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      ∫ x, h x * χi n x ∂ν ≤ ∫ x, h x ∂(ν.restrict K) := by
    intro ν hν n
    rw [← integral_indicator hKm]
    refine integral_mono (hint_i ν hν n) (hint_K ν hν) (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      calc h x * χi n x ≤ h x * 1 :=
            mul_le_mul_of_nonneg_left (aux_prop_uniform_resolvent_ident_inner_le_one U _ x) (hpos x)
        _ = h x := mul_one _
    · rw [indicator_of_notMem hx, hχi_van n x hx, mul_zero]
  -- limits of the cutoff integrals against μF
  have hbound_int : Integrable (S.indicator (fun _ => C)) μF := by
    rw [integrable_indicator_iff hScpt.isClosed.measurableSet]
    exact integrableOn_const hμfin.ne
  have hlim_o : Tendsto (fun n => ∫ x, h x * χo n x ∂μF) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict K))) := by
    rw [← integral_indicator hKm]
    refine tendsto_integral_of_dominated_convergence (S.indicator (fun _ => C))
      (fun n => (hh.mul (hχo_cont n)).aestronglyMeasurable) hbound_int ?_ ?_
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS, Real.norm_eq_abs, abs_mul]
        have h1 : |χo n x| ≤ 1 := by
          rw [abs_of_nonneg (aux_prop_uniform_resolvent_ident_outer_nonneg K _ x)]
          exact aux_prop_uniform_resolvent_ident_outer_le_one K (hδpos n) x
        have h2 : |h x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hxS
        calc |h x| * |χo n x| ≤ C * 1 :=
              mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
          _ = C := mul_one C
      · rw [indicator_of_notMem hxS, hχo_van n x hxS, mul_zero, norm_zero]
    · refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        refine tendsto_const_nhds.congr (fun n => ?_)
        rw [hχo_app, aux_prop_uniform_resolvent_ident_outer_of_mem K _ x hx, mul_one]
      · rw [indicator_of_notMem hx]
        have hpos' : 0 < infDist x K :=
          (hKcl.notMem_iff_infDist_pos hKne).1 hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hδev _ hpos'] with n hn
        rw [hχo_app, aux_prop_uniform_resolvent_ident_outer_of_le K (hδpos n) x hn.le, mul_zero]
  have hUcl : IsClosed Uᶜ := hU.isClosed_compl
  have hlim_i : Tendsto (fun n => ∫ x, h x * χi n x ∂μF) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict K))) := by
    have hae : U.indicator h =ᵐ[μF] K.indicator h := by
      have hnull : μF {x | U.indicator h x ≠ K.indicator h x} = 0 := by
        refine measure_mono_null (fun x hx => ?_) hfr
        simp only [mem_ofPred_eq] at hx
        rw [hU.frontier_eq]
        by_cases hxU : x ∈ U
        · exact absurd (by rw [indicator_of_mem hxU, indicator_of_mem (subset_closure hxU)]) hx
        · by_cases hxK : x ∈ K
          · exact ⟨hxK, hxU⟩
          · exact absurd (by rw [indicator_of_notMem hxU, indicator_of_notMem hxK]) hx
      exact hnull
    rw [← integral_indicator hKm, ← integral_congr_ae hae]
    refine tendsto_integral_of_dominated_convergence (S.indicator (fun _ => C))
      (fun n => (hh.mul (hχi_cont n)).aestronglyMeasurable) hbound_int ?_ ?_
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS, Real.norm_eq_abs, abs_mul]
        have h1 : |χi n x| ≤ 1 := by
          rw [abs_of_nonneg (aux_prop_uniform_resolvent_ident_inner_nonneg U (hδpos n) x)]
          exact aux_prop_uniform_resolvent_ident_inner_le_one U _ x
        have h2 : |h x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hxS
        calc |h x| * |χi n x| ≤ C * 1 :=
              mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
          _ = C := mul_one C
      · rw [indicator_of_notMem hxS, hχi_van n x (fun hxK => hxS (hKS hxK)), mul_zero,
          norm_zero]
    · refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        have hpos' : 0 < infDist x Uᶜ :=
          (hUcl.notMem_iff_infDist_pos hUc).1 (fun h' => h' hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hδev _ hpos'] with n hn
        rw [hχi_app, aux_prop_uniform_resolvent_ident_inner_of_le U (hδpos n) x hn.le, mul_one]
      · rw [indicator_of_notMem hx]
        refine tendsto_const_nhds.congr (fun n => ?_)
        rw [hχi_app, aux_prop_uniform_resolvent_ident_inner_of_notMem U _ x hx, mul_zero]
  exact aux_prop_uniform_resolvent_ident_sandwich
    (fun k => ∫ x, h x ∂((νF k).restrict K)) (∫ x, h x ∂(μF.restrict K))
    (fun n k => ∫ x, h x * χi n x ∂(νF k)) (fun n k => ∫ x, h x * χo n x ∂(νF k))
    (fun n => ∫ x, h x * χi n x ∂μF) (fun n => ∫ x, h x * χo n x ∂μF)
    (fun n k => hlower (νF k) (hνfin k) n) (fun n k => hupper (νF k) (hνfin k) n)
    (fun n => hconv (Fi n)) (fun n => hconv (Fo n)) hlim_i hlim_o

/-- **Restricted weak convergence.** Local (vague) convergence plus a null frontier give
convergence of the integrals of every continuous function over the closed set. -/
theorem aux_prop_uniform_resolvent_ident_restrict_tendsto {d : ℕ}
    (νF : ℕ → Measure (SpatialCoordinates d)) (μF : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hνfin : ∀ k, νF k (cthickening δ0 (closure U)) < ∞)
    (hμfin : μF (cthickening δ0 (closure U)) < ∞)
    (hconv : MeasuresConvergeLocally νF μF)
    (hfr : μF (frontier U) = 0)
    (h : SpatialCoordinates d → ℝ) (hh : Continuous h) :
    Tendsto (fun k => ∫ x, h x ∂((νF k).restrict (closure U))) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict (closure U)))) := by
  have hKS : closure U ⊆ cthickening δ0 (closure U) := self_subset_cthickening _
  have hfinK : ∀ (ν : Measure (SpatialCoordinates d)), ν (cthickening δ0 (closure U)) < ∞ →
      IsFiniteMeasure (ν.restrict (closure U)) := by
    intro ν hν
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hKS).trans_lt hν
  have hp : Continuous (fun x => max (h x) 0) := hh.max continuous_const
  have hm : Continuous (fun x => max (-h x) 0) := hh.neg.max continuous_const
  have hsplit : ∀ (ν : Measure (SpatialCoordinates d)), ν (cthickening δ0 (closure U)) < ∞ →
      ∫ x, h x ∂(ν.restrict (closure U)) =
        ∫ x, max (h x) 0 ∂(ν.restrict (closure U)) -
          ∫ x, max (-h x) 0 ∂(ν.restrict (closure U)) := by
    intro ν hν
    have := hfinK ν hν
    have hK' : IsCompact (closure U) := hK
    have i1 : Integrable (fun x => max (h x) 0) (ν.restrict (closure U)) :=
      aux_prop_uniform_resolvent_ident_integrableOn ν _ hK' ((measure_mono hKS).trans_lt hν) _ hp
    have i2 : Integrable (fun x => max (-h x) 0) (ν.restrict (closure U)) :=
      aux_prop_uniform_resolvent_ident_integrableOn ν _ hK' ((measure_mono hKS).trans_lt hν) _ hm
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    rcases le_total 0 (h x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have t1 := aux_prop_uniform_resolvent_ident_restrict_tendsto_nonneg νF μF U hU hK hUne hUc δ0 hδ0
    hνfin hμfin hconv hfr _ hp (fun x => le_max_right _ _)
  have t2 := aux_prop_uniform_resolvent_ident_restrict_tendsto_nonneg νF μF U hU hK hUne hUc δ0 hδ0
    hνfin hμfin hconv hfr _ hm (fun x => le_max_right _ _)
  rw [hsplit μF hμfin]
  exact (t1.sub t2).congr (fun k => (hsplit (νF k) (hνfin k)).symm)

end SubdiffusiveProcess.Paper
end

section

/-!
# Varying-measure trace passage (paper `eq:mfd-40`, ), from `lem_19`

Auxiliary argument for the `hident` identification of `prop_uniform_resolvent`.

For finite measures `ν k` on the closed cube with a common Frostman growth bound and
bounded Lebesgue density, `lem_19` supplies traces that are the identity on `H^{1/2}`
elements, with one Lipschitz constant; it also supplies the `H^{3/4} → H^{1/2}`
interpolation upgrade.  Together with the smooth density of the cube `H^{1/2}` space and the
completion trace `T` of the limit measure `μ` (pinned by `MeasureTraceCharacterization`),
this gives the passage `∫ (s_k - ψ)² dν_k → ∫ (T z - ψ)² dμ`.
The nodes `lem_19` and `measureTrace_hdense_of_finiteMeasure_supported` are
axiom-clean.
-/


open Filter MeasureTheory Topology Set Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal ContDiff

namespace SubdiffusiveProcess.Paper

/-- `a² ≤ A b²` with `0 ≤ a`, `0 ≤ A` gives `a ≤ √A |b|`. -/
theorem aux_prop_uniform_resolvent_ident_le_sqrt_mul (a b A : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (h : a ^ 2 ≤ A * b ^ 2) : a ≤ Real.sqrt A * |b| := by
  have h1 : Real.sqrt (a ^ 2) ≤ Real.sqrt (A * b ^ 2) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq ha, Real.sqrt_mul hA, Real.sqrt_sq_eq_abs] at h1
  exact h1

/-- A continuous function is in `L²` of a finite measure carried by a compact set. -/
theorem aux_prop_uniform_resolvent_ident_memLp_of_continuous {d : ℕ}
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν] (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hsupp : ν Kᶜ = 0)
    (g : SpatialCoordinates d → ℝ) (hg : Continuous g) :
    MemLp g 2 ν := by
  obtain ⟨C, hC⟩ := bddAbove_def.mp (hK.bddAbove_image hg.norm.continuousOn)
  apply MemLp.of_bound hg.aestronglyMeasurable C
  rw [ae_iff]
  apply measure_mono_null ?_ hsupp
  intro x hx
  by_contra hxK
  have hxK' : x ∈ K := by simpa only [mem_compl_iff, not_not] using hxK
  exact hx (hC _ ⟨x, hxK', rfl⟩)

/-- The `L²` norm square is the integral of the square. -/
theorem aux_prop_uniform_resolvent_ident_L2_norm_sq {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} (f : Lp ℝ 2 μ) : ∫ a, (f a) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext a
  simp [sq]

/-- `‖toLp g - toLp ψ‖² = ∫ (g - ψ)²`. -/
theorem aux_prop_uniform_resolvent_ident_norm_sub_sq {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} (X Ψ : Lp ℝ 2 μ) (g ψ : α → ℝ) (hX : X =ᵐ[μ] g) (hΨ : Ψ =ᵐ[μ] ψ) :
    ‖X - Ψ‖ ^ 2 = ∫ a, (g a - ψ a) ^ 2 ∂μ := by
  rw [← aux_prop_uniform_resolvent_ident_L2_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub X Ψ, hX, hΨ] with a h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- ε/3 assembly: `x_k → Y` from a doubly indexed comparison. -/
theorem aux_prop_uniform_resolvent_ident_eps3 (x : ℕ → ℝ) (Y : ℝ)
    (e : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (c : ℕ → ℝ)
    (hbound : ∀ n k, |x k - Y| ≤ c k + b n + |e n k|)
    (hb : Tendsto b atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (he : ∀ n, Tendsto (e n) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 Y) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.1 hb (ε / 3) (by linarith)
  obtain ⟨k1, hk1⟩ := Metric.tendsto_atTop.1 hc (ε / 3) (by linarith)
  obtain ⟨k2, hk2⟩ := Metric.tendsto_atTop.1 (he n) (ε / 3) (by linarith)
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have e1 := hn n le_rfl
  have e2 := hk1 k (le_of_max_le_left hk)
  have e3 := hk2 k (le_of_max_le_right hk)
  rw [Real.dist_eq, sub_zero] at e1 e2 e3
  rw [Real.dist_eq]
  have := hbound n k
  have h1 : b n ≤ |b n| := le_abs_self _
  have h2 : c k ≤ |c k| := le_abs_self _
  linarith

/-- **Varying-measure trace passage** (`eq:mfd-40`) with a continuous shift `ψ`.

`s k` are `L²(Q)` classes, bounded in the cube `H^{3/4}` norm and converging in `L²(Q)` to the
`H^{1/2}` element `z`; `ν k` are finite measures on the closed cube with one Frostman bound,
bounded Lebesgue densities and bounded masses, converging weakly (against continuous functions)
to `μ`; `T` is the completion trace of `μ`. -/
theorem aux_prop_uniform_resolvent_ident_trace_passage {d : ℕ} (hd : 2 ≤ d)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : MeasureTraceCharacterization hd Qtri hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (z : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w3 k) ≤ B)
    (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ) :
    Tendsto (fun k => ∫ x, (s k x - ψ x) ^ 2 ∂(ν k)) atTop
      (𝓝 (∫ x, (T z x - ψ x) ^ 2 ∂μ)) := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) with hQs
  have hQeq : Qs = Homogenization.openCubeSet Qtri := centeredCube_eq_openCubeSet Qtri hr
  have hKc : IsCompact (closure Qs) := (centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr).isCompact_closure
  have hνfinI : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨⟨C, hC0, htr⟩, hinterp⟩ := lem_19 d hd SInterp (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr t ht
  -- finite-cutoff traces: identity on `H^{1/2}` elements, one Lipschitz constant
  have hTk : ∀ k, ∃ Tk : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (ν k),
      (∀ (u v w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder),
        w.val 0 = u.val 0 - v.val 0 →
        ‖Tk u - Tk v‖ ^ 2 ≤ C * (Kμ + (ν k (closure Qs)).toReal) *
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder w) ^ 2) ∧
      (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder),
          (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Qs] f →
          ∀ hf : MemLp f 2 (ν k), Tk v = hf.toLp f) ∧
      (∀ u : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder,
        MemLp (u.val 0) 2 (ν k) ∧ ∀ hu : MemLp (u.val 0) 2 (ν k), Tk u = hu.toLp (u.val 0)) := by
    intro k
    obtain ⟨D, hD0, hD⟩ := hνdens k
    obtain ⟨Tk, ⟨_, hlip, hsm, _, hden⟩, _⟩ :=
      htr (ν k) Kμ (hνfin k) (hνsupp k) hKμ (hνgrowth k)
    exact ⟨Tk, hlip, hsm, hden D hD0 hD⟩
  choose Tk hTk_lip hTk_sm hTk_id using hTk
  -- interpolation upgrade
  obtain ⟨vhalf, hvhalf, diff, hdiff, hdiff0⟩ :=
    hinterp _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder rfl w3 (z.val 0) B hB
      (by simpa only [hw3] using hs)
  -- smooth approximation of `z` for the limit measure
  have hμsupp' : μ (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    rw [← hQeq]; exact hμsupp
  obtain ⟨a, f, w, hfsm, hfLp, haf, hw, hw0⟩ :=
    measureTrace_hdense_of_finiteMeasure_supported hd Qtri hr μ hμsupp' z
  -- `H^{1/2}` elements with prescribed first coordinate
  obtain ⟨zero, hzero⟩ := hT.1 z z
  obtain ⟨neg, hneg⟩ := hT.1 zero z
  have hS : ∀ k, ∃ Sk : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder,
      Sk.val 0 = s k := by
    intro k
    obtain ⟨Sk, hSk⟩ := hT.1 (diff k) neg
    refine ⟨Sk, ?_⟩
    rw [hSk, hdiff k, hneg, hzero, hw3 k]
    abel
  choose S hSval using hS
  -- constants
  set L : ℝ := Real.sqrt (C * (Kμ + Mbar)) with hLdef
  set Lμ : ℝ := Real.sqrt (Ctr * (Ktr + (μ (closure (Homogenization.openCubeSet Qtri))).toReal))
    with hLμdef
  have hMbar : ∀ k, 0 ≤ Kμ + Mbar := fun k => by
    have := hνmass k
    have : 0 ≤ (ν k (closure Qs)).toReal := ENNReal.toReal_nonneg
    linarith
  have hlipk : ∀ k (u v w' : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖Tk k u - Tk k v‖ ≤ L * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder w'| := by
    intro k u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hC0 (hMbar k)) ?_
    refine (hTk_lip k u v w' hw').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    linarith [hνmass k]
  have hlipμ : ∀ (u v w' : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖T u - T v‖ ≤ Lμ * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder w'| := by
    intro u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hCtr (add_nonneg hKtr ENNReal.toReal_nonneg)) ?_
    exact hT.2.1 u v w' hw'
  -- `L²` representatives
  have hψk : ∀ k, MemLp ψ 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) ψ hψ
  have hψμ : MemLp ψ 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ (closure Qs) hKc hμsupp ψ hψ
  have hfk : ∀ n k, MemLp (f n) 2 (ν k) := fun n k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) (f n)
      (hfsm n).continuous
  -- the quantities
  set X : ℕ → ℝ := fun k => ‖Tk k (S k) - (hψk k).toLp ψ‖ with hXdef
  set Y : ℝ := ‖T z - hψμ.toLp ψ‖ with hYdef
  set e : ℕ → ℕ → ℝ := fun n k =>
    ‖Tk k (a n) - (hψk k).toLp ψ‖ - ‖T (a n) - hψμ.toLp ψ‖ with hedef
  have hbound : ∀ n k, |X k - Y| ≤
      L * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (diff k)| +
        (L + Lμ) * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (w n)| + |e n k| := by
    intro n k
    have h1 : ‖Tk k (S k) - Tk k z‖ ≤
        L * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (diff k)| :=
      hlipk k (S k) z (diff k) (by rw [hdiff k, hSval k, hw3 k])
    have h2 : ‖Tk k z - Tk k (a n)‖ ≤
        L * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (w n)| :=
      hlipk k z (a n) (w n) (hw n)
    have h3 : ‖T z - T (a n)‖ ≤
        Lμ * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (w n)| :=
      hlipμ z (a n) (w n) (hw n)
    have t1 : |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| ≤ ‖Tk k (S k) - Tk k (a n)‖ := by
      have := abs_norm_sub_norm_le (Tk k (S k) - (hψk k).toLp ψ) (Tk k (a n) - (hψk k).toLp ψ)
      simpa [hXdef, sub_sub_sub_cancel_right] using this
    have t2 : ‖Tk k (S k) - Tk k (a n)‖ ≤ ‖Tk k (S k) - Tk k z‖ + ‖Tk k z - Tk k (a n)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have t3 : |‖T (a n) - hψμ.toLp ψ‖ - Y| ≤ ‖T z - T (a n)‖ := by
      have := abs_norm_sub_norm_le (T (a n) - hψμ.toLp ψ) (T z - hψμ.toLp ψ)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (T (a n)) (T z)] at this
      exact this
    have hsplit : X k - Y = (X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k +
        (‖T (a n) - hψμ.toLp ψ‖ - Y) := by
      simp only [hedef]; ring
    rw [hsplit]
    calc |(X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k + (‖T (a n) - hψμ.toLp ψ‖ - Y)|
        ≤ |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| + |e n k| + |‖T (a n) - hψμ.toLp ψ‖ - Y| :=
          abs_add_three _ _ _
      _ ≤ _ := by nlinarith [t1, t2, t3, h1, h2, h3]
  -- the smooth comparison term converges for each fixed `n`
  have he : ∀ n, Tendsto (e n) atTop (𝓝 0) := by
    intro n
    have hTkan : ∀ k, Tk k (a n) = (hfk n k).toLp (f n) := fun k =>
      hTk_sm k (f n) (hfsm n) (a n) (haf n) (hfk n k)
    have hTan : T (a n) = (hfLp n).toLp (f n) :=
      hT.2.2 (f n) (hfsm n) (a n) (haf n) (hfLp n)
    have hsqk : ∀ k, ‖Tk k (a n) - (hψk k).toLp ψ‖ =
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) := by
      intro k
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (Tk k (a n)) ((hψk k).toLp ψ) (f n) ψ
        (by rw [hTkan k]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hsqμ : ‖T (a n) - hψμ.toLp ψ‖ = Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ) := by
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (T (a n)) (hψμ.toLp ψ) (f n) ψ
        (by rw [hTan]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hcont : Continuous (fun x => (f n x - ψ x) ^ 2) :=
      ((hfsm n).continuous.sub hψ).pow 2
    have hlim := (hW _ hcont).sqrt
    have h2 : Tendsto (fun k => Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) -
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ)) atTop (𝓝 0) := by
      have := hlim.sub_const (Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ))
      rwa [sub_self] at this
    refine h2.congr (fun k => ?_)
    simp only [hedef, hsqk, hsqμ]
  have hdiffabs : Tendsto (fun k => L * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder
      (diff k)|) atTop (𝓝 0) := by
    simpa using (hdiff0.abs).const_mul L
  have hwabs : Tendsto (fun n => (L + Lμ) * |cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder
      (w n)|) atTop (𝓝 0) := by
    simpa using (hw0.abs).const_mul (L + Lμ)
  have hXY : Tendsto X atTop (𝓝 Y) :=
    aux_prop_uniform_resolvent_ident_eps3 X Y e _ _ hbound hwabs hdiffabs he
  -- back to integrals
  have hXsq : ∀ k, X k ^ 2 = ∫ x, (s k x - ψ x) ^ 2 ∂(ν k) := by
    intro k
    obtain ⟨hmem, hid⟩ := hTk_id k (S k)
    refine aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ ?_ (MemLp.coeFn_toLp _)
    rw [hid hmem]
    refine (MemLp.coeFn_toLp hmem).trans ?_
    rw [hSval k]
  have hYsq : Y ^ 2 = ∫ x, (T z x - ψ x) ^ 2 ∂μ :=
    aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ (Filter.EventuallyEq.refl _ _)
      (MemLp.coeFn_toLp _)
  rw [← hYsq]
  exact (hXY.pow 2).congr hXsq

end SubdiffusiveProcess.Paper
end

section

/-!
# Deterministic variational identification of `L²` clusters (paper label `mfd:prop-uniform-resolvent`)

Auxiliary argument for the `hident` identification of `prop_uniform_resolvent`.

One sample, one `λ > 0`, one bounded continuous source `f`.  If the finite-cutoff killed
minimizers `u (σ k)` converge in `L²(Q)` to `ubar` along a subsequence on which the `H^{3/4}`
coercivity constants are bounded, then `ubar` is the unique minimizer `ustar` of the limit
functional.  Inputs: Mosco convergence (liminf + recovery), the finite weak equation, the
limit trace `T` / `J`, and the minimizer characterization — exactly the parent data.
-/


open Filter MeasureTheory Topology Set Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-! ### `L²` algebra -/

theorem aux_prop_uniform_resolvent_ident_integrable_mul {α : Type*} {mα : MeasurableSpace α}
    {ν : Measure α} {a b : α → ℝ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    Integrable (fun x => a x * b x) ν := by
  have h1 := (ha.add hb).integrable_sq
  have h2 := (ha.sub hb).integrable_sq
  refine ((h1.sub h2).div_const 4).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The finite-cutoff quadratic identity behind the minimality of the weak solution. -/
theorem aux_prop_uniform_resolvent_ident_quad_identity {α : Type*} {mα : MeasurableSpace α}
    {ν : Measure α} {F g h : α → ℝ} (hF : MemLp F 2 ν) (hg : MemLp g 2 ν) (hh : MemLp h 2 ν)
    (lam : ℝ) :
    lam * ∫ x, (h x) ^ 2 ∂ν - 2 * ∫ x, F x * h x ∂ν -
        (lam * ∫ x, (g x) ^ 2 ∂ν - 2 * ∫ x, F x * g x ∂ν) +
        2 * ∫ x, (F x - lam * g x) * (h x - g x) ∂ν =
      lam * ∫ x, (h x - g x) ^ 2 ∂ν := by
  have iFh : Integrable (fun x => F x * h x) ν := aux_prop_uniform_resolvent_ident_integrable_mul hF hh
  have iFg : Integrable (fun x => F x * g x) ν := aux_prop_uniform_resolvent_ident_integrable_mul hF hg
  have igh : Integrable (fun x => g x * h x) ν := aux_prop_uniform_resolvent_ident_integrable_mul hg hh
  have ig2 : Integrable (fun x => (g x) ^ 2) ν := hg.integrable_sq
  have ih2 : Integrable (fun x => (h x) ^ 2) ν := hh.integrable_sq
  have i1 : Integrable (fun x => F x * h x - F x * g x) ν := iFh.sub iFg
  have i2 : Integrable (fun x => lam * (g x * h x)) ν := igh.const_mul lam
  have i3 : Integrable (fun x => (F x * h x - F x * g x) - lam * (g x * h x)) ν := i1.sub i2
  have i4 : Integrable (fun x => lam * (g x) ^ 2) ν := ig2.const_mul lam
  have i5 : Integrable (fun x => 2 * (g x * h x)) ν := igh.const_mul 2
  have i6 : Integrable (fun x => (h x) ^ 2 - 2 * (g x * h x)) ν := ih2.sub i5
  have hA : ∫ x, (F x - lam * g x) * (h x - g x) ∂ν =
      ∫ x, F x * h x ∂ν - ∫ x, F x * g x ∂ν - lam * ∫ x, g x * h x ∂ν +
        lam * ∫ x, (g x) ^ 2 ∂ν := by
    have e : (fun x => (F x - lam * g x) * (h x - g x)) =
        fun x => ((F x * h x - F x * g x) - lam * (g x * h x)) + lam * (g x) ^ 2 := by
      funext x; ring
    rw [e, integral_add i3 i4, integral_sub i1 i2, integral_sub iFh iFg,
      integral_const_mul, integral_const_mul]
  have hB : ∫ x, (h x - g x) ^ 2 ∂ν =
      ∫ x, (h x) ^ 2 ∂ν - 2 * ∫ x, g x * h x ∂ν + ∫ x, (g x) ^ 2 ∂ν := by
    have e : (fun x => (h x - g x) ^ 2) =
        fun x => ((h x) ^ 2 - 2 * (g x * h x)) + (g x) ^ 2 := by
      funext x; ring
    rw [e, integral_add i6 ig2, integral_sub ih2 i5, integral_const_mul]
  rw [hA, hB]
  ring

/-- `∫ b a = (∫ a² + ∫ b² - ∫ (a - b)²) / 2`. -/
theorem aux_prop_uniform_resolvent_ident_mul_eq {α : Type*} {mα : MeasurableSpace α}
    {ν : Measure α} {a b : α → ℝ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ∫ x, b x * a x ∂ν =
      (∫ x, (a x) ^ 2 ∂ν + ∫ x, (b x) ^ 2 ∂ν - ∫ x, (a x - b x) ^ 2 ∂ν) / 2 := by
  have iba : Integrable (fun x => b x * a x) ν := aux_prop_uniform_resolvent_ident_integrable_mul hb ha
  have ia2 : Integrable (fun x => (a x) ^ 2) ν := ha.integrable_sq
  have ib2 : Integrable (fun x => (b x) ^ 2) ν := hb.integrable_sq
  have i1 : Integrable (fun x => (a x) ^ 2 + (b x) ^ 2) ν := ia2.add ib2
  have i2 : Integrable (fun x => 2 * (b x * a x)) ν := iba.const_mul 2
  have e : (fun x => (a x - b x) ^ 2) = fun x => ((a x) ^ 2 + (b x) ^ 2) - 2 * (b x * a x) := by
    funext x; ring
  rw [e, integral_sub i1 i2, integral_add ia2 ib2, integral_const_mul]
  ring

/-! ### Finite-cutoff minimality from the weak equation -/

theorem aux_prop_uniform_resolvent_ident_finite_min {d : ℕ}
    (U : TopologicalSpace.Opens (SpatialCoordinates d)) (a : PositiveCoefficient U)
    (ν : Measure (SpatialCoordinates d)) (D : ℝ)
    (hν : ν ≤ ENNReal.ofReal D • volume.restrict (U : Set (SpatialCoordinates d)))
    (F : SpatialCoordinates d → ℝ) (hF : MemLp F 2 ν) (lam : ℝ) (hlam : 0 ≤ lam)
    (R : SpatialCoordinates d → ℝ) (u : killedSobolevGraph U)
    (hRu : R =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      ((u : SobolevData U).1 : SpatialCoordinates d → ℝ))
    (hweak : ∀ w : killedSobolevGraph U,
      sobolevCoefficientForm a (u : SobolevData U) (w : SobolevData U) =
        ∫ x, (F x - lam * R x) * (w : SobolevData U).1 x ∂ν)
    (w : killedSobolevGraph U) :
    sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) +
        lam * ∫ x, ((u : SobolevData U).1 x) ^ 2 ∂ν -
        2 * ∫ x, F x * (u : SobolevData U).1 x ∂ν ≤
      sobolevCoefficientForm a (w : SobolevData U) (w : SobolevData U) +
        lam * ∫ x, ((w : SobolevData U).1 x) ^ 2 ∂ν -
        2 * ∫ x, F x * (w : SobolevData U).1 x ∂ν := by
  have hac : ν ≪ volume.restrict (U : Set (SpatialCoordinates d)) :=
    Measure.absolutelyContinuous_of_le_smul hν
  have hmem : ∀ v : killedSobolevGraph U, MemLp ((v : SobolevData U).1 : SpatialCoordinates d → ℝ)
      2 ν := fun v => (Lp.memLp _).of_measure_le_smul ENNReal.ofReal_ne_top hν
  have hRu' : R =ᵐ[ν] ((u : SobolevData U).1 : SpatialCoordinates d → ℝ) := hac.ae_eq hRu
  have hsub : (((w - u : killedSobolevGraph U) : SobolevData U).1 : SpatialCoordinates d → ℝ)
      =ᵐ[ν] fun x => (w : SobolevData U).1 x - (u : SobolevData U).1 x := by
    have h : ((w - u : killedSobolevGraph U) : SobolevData U).1 =
        (w : SobolevData U).1 - (u : SobolevData U).1 := by
      rw [Submodule.coe_sub, Prod.fst_sub]
    rw [h]
    exact hac.ae_eq (Lp.coeFn_sub _ _)
  have hwe := hweak (w - u)
  have hint : ∫ x, (F x - lam * R x) * ((w - u : killedSobolevGraph U) : SobolevData U).1 x ∂ν =
      ∫ x, (F x - lam * (u : SobolevData U).1 x) *
        ((w : SobolevData U).1 x - (u : SobolevData U).1 x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hRu', hsub] with x h1 h2
    rw [h1, h2]
  have hform : sobolevCoefficientForm a (u : SobolevData U) ((w - u : killedSobolevGraph U) :
      SobolevData U) =
      sobolevCoefficientForm a (u : SobolevData U) (w : SobolevData U) -
        sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) := by
    rw [Submodule.coe_sub, map_sub]
  have hnn : 0 ≤ sobolevCoefficientForm a ((w - u : killedSobolevGraph U) : SobolevData U)
      ((w - u : killedSobolevGraph U) : SobolevData U) := sobolevCoefficientForm_nonneg _ _
  have hexp : sobolevCoefficientForm a ((w - u : killedSobolevGraph U) : SobolevData U)
      ((w - u : killedSobolevGraph U) : SobolevData U) =
      sobolevCoefficientForm a (w : SobolevData U) (w : SobolevData U) -
        2 * sobolevCoefficientForm a (u : SobolevData U) (w : SobolevData U) +
        sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) := by
    simp only [Submodule.coe_sub, map_sub, sub_apply]
    rw [sobolevCoefficientForm_symm a (w : SobolevData U) (u : SobolevData U)]
    ring
  have hq := aux_prop_uniform_resolvent_ident_quad_identity hF (hmem u) (hmem w) lam
  have hsq : 0 ≤ ∫ x, ((w : SobolevData U).1 x - (u : SobolevData U).1 x) ^ 2 ∂ν :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [hint] at hwe
  rw [hform] at hwe
  have hsq' := mul_nonneg hlam hsq
  linarith

/-! ### Mosco liminf along a subsequence -/

theorem aux_prop_uniform_resolvent_ident_liminf_subseq {H : Type*} [NormedAddCommGroup H]
    (EN : ℕ → H → ℝ≥0∞) (Elim : H → ℝ≥0∞) (hliminf : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf EN Elim)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (x : ℕ → H) (ubar : H)
    (hx : Tendsto x atTop (𝓝 ubar)) (c : ℝ≥0∞)
    (hfreq : ∃ᶠ k in atTop, EN (σ k) (x k) ≤ c) :
    Elim ubar ≤ c := by
  classical
  let y : ℕ → H := fun N => if h : ∃ k, σ k = N then x (Classical.choose h) else ubar
  have hyσ : ∀ k, y (σ k) = x k := by
    intro k
    have h : ∃ k', σ k' = σ k := ⟨k, rfl⟩
    simp only [y, dite_eq_left h]
    congr 1
    exact hσ.injective (Classical.choose_spec h)
  have hy : Tendsto y atTop (𝓝 ubar) := by
    rw [tendsto_def]
    intro V hV
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hx hV)
    rw [mem_atTop_sets]
    refine ⟨σ k0, fun N hN => ?_⟩
    simp only [mem_preimage]
    by_cases h : ∃ k, σ k = N
    · obtain ⟨k, rfl⟩ := h
      rw [hyσ k]
      exact hk0 k (hσ.le_iff_le.1 hN)
    · simp only [y, dite_eq_right h]
      exact mem_of_mem_nhds hV
  refine (hliminf ubar y hy).trans (liminf_le_of_frequently_le' ?_)
  refine hσ.tendsto_atTop.frequently (p := fun N => EN N (y N) ≤ c) ?_
  refine hfreq.mono (fun k hk => ?_)
  simp only [hyσ k]
  exact hk

/-! ### Recovery representatives -/

theorem aux_prop_uniform_resolvent_ident_recovery_reps {d : ℕ}
    (U : TopologicalSpace.Opens (SpatialCoordinates d)) (a : ℕ → PositiveCoefficient U)
    (EN : ℕ → DomainL2 U → ℝ≥0∞)
    (hEN : ∀ N u, EN N u = ⨅ v : {v : killedSobolevGraph U // (v : SobolevData U).1 = u},
      ENNReal.ofReal (sobolevCoefficientForm (a N) (v.val : SobolevData U) (v.val : SobolevData U)))
    (Elim : DomainL2 U → ℝ≥0∞) (hrec : _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery EN Elim)
    (ustar : DomainL2 U) (hfin : Elim ustar ≠ ⊤) :
    ∃ v : ℕ → killedSobolevGraph U,
      (∀ N, sobolevCoefficientForm (a N) (v N : SobolevData U) (v N : SobolevData U) ≤
        (Elim ustar).toReal + 2) ∧
      Tendsto (fun N => (v N : SobolevData U).1) atTop (𝓝 ustar) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
        sobolevCoefficientForm (a N) (v N : SobolevData U) (v N : SobolevData U) <
          (Elim ustar).toReal + η := by
  classical
  obtain ⟨y, hy, hlim⟩ := hrec ustar
  set A := (Elim ustar).toReal with hAdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hEA : Elim ustar = ENNReal.ofReal A := (ENNReal.ofReal_toReal hfin).symm
  have hrep : ∀ N, ∃ v : killedSobolevGraph U,
      sobolevCoefficientForm (a N) (v : SobolevData U) (v : SobolevData U) ≤ A + 2 ∧
      (EN N (y N) < ENNReal.ofReal (A + 1) →
        (v : SobolevData U).1 = y N ∧
        ENNReal.ofReal (sobolevCoefficientForm (a N) (v : SobolevData U) (v : SobolevData U)) <
          EN N (y N) + ENNReal.ofReal (1 / ((N : ℝ) + 1))) := by
    intro N
    by_cases hN : EN N (y N) < ENNReal.ofReal (A + 1)
    · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((N : ℝ) + 1)) :=
        ENNReal.ofReal_pos.2 (by positivity)
      have hlt : EN N (y N) < EN N (y N) + ENNReal.ofReal (1 / ((N : ℝ) + 1)) :=
        ENNReal.lt_add_right hN.ne_top hpos.ne'
      rw [hEN N (y N)] at hlt
      obtain ⟨⟨v, hv⟩, hvlt⟩ := iInf_lt_iff.1 hlt
      refine ⟨v, ?_, fun _ => ⟨hv, by rw [hEN N (y N)]; exact hvlt⟩⟩
      have h1 : ENNReal.ofReal (sobolevCoefficientForm (a N) (v : SobolevData U)
          (v : SobolevData U)) < ENNReal.ofReal (A + 1) + ENNReal.ofReal 1 := by
        refine hvlt.trans_le ?_
        rw [← hEN N (y N)]
        refine add_le_add hN.le (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      rw [← ENNReal.ofReal_add (by linarith) zero_le_one] at h1
      have h2 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sobolevCoefficientForm_nonneg _ _)).1 h1
      linarith
    · refine ⟨0, ?_, fun h => absurd h hN⟩
      simp only [ZeroMemClass.coe_zero, map_zero]
      linarith
  choose v hvb hvrep using hrep
  have hev1 : ∀ᶠ N in atTop, EN N (y N) < ENNReal.ofReal (A + 1) := by
    refine eventually_lt_of_limsup_lt (hlim.trans_lt ?_)
    rw [hEA]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  refine ⟨v, hvb, ?_, ?_⟩
  · refine hy.congr' ?_
    filter_upwards [hev1] with N hN
    exact ((hvrep N hN).1).symm
  · intro η hη
    have hev2 : ∀ᶠ N in atTop, EN N (y N) < ENNReal.ofReal (A + η / 2) := by
      refine eventually_lt_of_limsup_lt (hlim.trans_lt ?_)
      rw [hEA]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have hev3 : ∀ᶠ N : ℕ in atTop, 1 / ((N : ℝ) + 1) < η / 2 := by
      have h1 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact (tendsto_order.1 h1).2 _ (by linarith)
    filter_upwards [hev1, hev2, hev3] with N h1 h2 h3
    have hb := (hvrep N h1).2
    have hsum : EN N (y N) + ENNReal.ofReal (1 / ((N : ℝ) + 1)) <
        ENNReal.ofReal (A + η / 2) + ENNReal.ofReal (η / 2) :=
      ENNReal.add_lt_add h2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h3)
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)] at hsum
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sobolevCoefficientForm_nonneg _ _)).1
      (hb.trans hsum)
    linarith

end SubdiffusiveProcess.Paper
end

section

/-!
# Deterministic identification `ubar = ustar` (paper label `mfd:prop-uniform-resolvent` )

Auxiliary argument for the `hident` identification of `prop_uniform_resolvent`.
-/


open Filter MeasureTheory Topology Set Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- `x² ≤ K E`, `K ≤ Mb`, `0 ≤ E ≤ Eb` give `x ≤ √(max Mb 0 · Eb)`. -/
theorem aux_prop_uniform_resolvent_ident_norm_bound (x K E Mb Eb : ℝ) (h : x ^ 2 ≤ K * E)
    (hK : K ≤ Mb) (hE0 : 0 ≤ E) (hE : E ≤ Eb) :
    x ≤ Real.sqrt (max Mb 0 * Eb) := by
  have h1 : K * E ≤ max Mb 0 * Eb :=
    (mul_le_mul_of_nonneg_right (hK.trans (le_max_left _ _)) hE0).trans
      (mul_le_mul_of_nonneg_left hE (le_max_right _ _))
  calc x ≤ |x| := le_abs_self x
    _ = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt (max Mb 0 * Eb) := Real.sqrt_le_sqrt (h.trans h1)

/-- **Functional passage**: `λ ∫ s_k² dν_k - 2 ∫ F s_k dν_k → λ ∫ (T z)² dμ - 2 ∫ F (T z) dμ`. -/
theorem aux_prop_uniform_resolvent_ident_functional_passage {d : ℕ} (hd : 2 ≤ d)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : MeasureTraceCharacterization hd Qtri hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (z : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w3 k) ≤ B)
    (lam : ℝ) (F : SpatialCoordinates d → ℝ) (hF : Continuous F) :
    Tendsto (fun k => lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k)) atTop
      (𝓝 (lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ)) := by
  have hKc : IsCompact (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  have h0 := aux_prop_uniform_resolvent_ident_trace_passage hd Qtri hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    (fun _ => 0) continuous_const
  have h1 := aux_prop_uniform_resolvent_ident_trace_passage hd Qtri hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    F hF
  have h2 := hW (fun x => F x ^ 2) (hF.pow 2)
  simp only [sub_zero] at h0
  have hsk : ∀ k, MemLp (s k : SpatialCoordinates d → ℝ) 2 (ν k) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens k
    exact (Lp.memLp _).of_measure_le_smul ENNReal.ofReal_ne_top hD
  have hFk : ∀ k, MemLp F 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) _ hKc (hνsupp k) F hF
  have hFμ : MemLp F 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ _ hKc hμsupp F hF
  have heqk : ∀ k, lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k) =
      lam * ∫ x, (s k x) ^ 2 ∂(ν k) - (∫ x, (s k x) ^ 2 ∂(ν k) + ∫ x, F x ^ 2 ∂(ν k) -
        ∫ x, (s k x - F x) ^ 2 ∂(ν k)) := by
    intro k
    rw [aux_prop_uniform_resolvent_ident_mul_eq (hsk k) (hFk k)]
    ring
  have heqμ : lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ =
      lam * ∫ x, (T z x) ^ 2 ∂μ - (∫ x, (T z x) ^ 2 ∂μ + ∫ x, F x ^ 2 ∂μ -
        ∫ x, (T z x - F x) ^ 2 ∂μ) := by
    rw [aux_prop_uniform_resolvent_ident_mul_eq (Lp.memLp (T z)) hFμ]
    ring
  rw [heqμ]
  exact ((h0.const_mul lam).sub ((h0.add h2).sub h1)).congr (fun k => (heqk k).symm)

/-- **Deterministic identification.** One sample, one `λ > 0`, one bounded continuous `f`:
an `L²(Q)` limit `ubar` of the killed finite-cutoff minimizers along a subsequence with bounded
`H^{3/4}` coercivity constants is the unique limit minimizer `ustar`. -/
theorem aux_prop_uniform_resolvent_ident_deterministic {d : ℕ} (hd : 2 ≤ d)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (a : ℕ → PositiveCoefficient (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (EN : ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hEN : ∀ N u, EN N u = ⨅ v : {v : killedSobolevGraph (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) //
        (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
      ENNReal.ofReal (sobolevCoefficientForm (a N)
        (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
        (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))))
    (Elim : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hliminf : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf EN Elim) (hrec : _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery EN Elim)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : MeasureTraceCharacterization hd Qtri hr μ Ktr Ctr T)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)) → Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hival : ∀ u (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ u (hu : Elim u ≠ ⊤), J u =ᵐ[μ] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (hmin : Elim ustar ≠ ⊤ ∧
      (∀ w, Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂μ) -
            2 * (∫ x, f x * J ustar x ∂μ) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ)) ∧
      (∀ w, Elim w ≠ ⊤ →
        (∀ v, Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂μ) - 2 * (∫ x, f x * J v x ∂μ)) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (R : ℕ → SpatialCoordinates d → ℝ)
    (hRu : ∀ N, R N =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
      ((u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ))
    (hweak : ∀ N (w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      sobolevCoefficientForm (a N)
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)) =
        ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(ν N))
    (henergy : ∀ N, sobolevCoefficientForm (a N)
        (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
        (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) ≤
      ‖f‖ ^ 2 * (ν N (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
        (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm (a N)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (Mb : ℝ) (hMb : ∀ k, Kc (σ k) ≤ Mb)
    (ubar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr))
    (hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1) atTop
      (𝓝 ubar)) :
    ubar = ustar := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) with hQs
  have hKc : IsCompact (closure Qs) :=
    (centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨hustar, hminle, huniq⟩ := hmin
  -- subsequence data
  have hWσ : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν (σ k))) atTop (𝓝 (∫ x, h x ∂μ)) := fun h hh =>
    (hW h hh).comp hσ.tendsto_atTop
  -- energy bound
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = ‖f‖ ^ 2 * Mbar / lam := ⟨_, rfl⟩
  have hform_nn : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr)),
      0 ≤ sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _) :=
    fun N v => sobolevCoefficientForm_nonneg _ _
  have hEbN : ∀ N, sobolevCoefficientForm (a N) (u N : SobolevData _) (u N : SobolevData _)
      ≤ Eb := by
    intro N
    refine (henergy N).trans ?_
    have hm : (ν N Qs).toReal ≤ Mbar := by
      refine le_trans ?_ (hνmass N)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono subset_closure)
    rw [hEb]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) hlam.le
  have hENle : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr)),
      EN N (v : SobolevData _).1 ≤
        ENNReal.ofReal (sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _)) := by
    intro N v
    rw [hEN]
    exact iInf_le_of_le ⟨v, rfl⟩ le_rfl
  -- the cluster has finite limit energy
  have hubar : Elim ubar ≠ ⊤ := by
    have hle : Elim ubar ≤ ENNReal.ofReal Eb :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (Frequently.of_forall fun k =>
          (hENle (σ k) (u (σ k))).trans (ENNReal.ofReal_le_ofReal (hEbN (σ k))))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  -- `H^{3/4}` bounds along the subsequence
  have hu3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (u (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Eb) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (u (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Eb hb (hMb k)
      (hform_nn _ _) (hEbN (σ k))⟩
  choose U3 hU3 hU3b using hu3
  -- passage on the minimizer side
  have hcu := aux_prop_uniform_resolvent_ident_functional_passage hd Qtri hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (u (σ k) : SobolevData _).1) (i ubar hubar)
    (by rw [hival]; exact hconv) U3 hU3 _ hU3b lam f f.continuous
  -- recovery sequence for `ustar`
  obtain ⟨v, hvb, hvconv, hvev⟩ :=
    aux_prop_uniform_resolvent_ident_recovery_reps _ a EN hEN Elim hrec ustar hustar
  obtain ⟨Es, hEs⟩ : ∃ Es : ℝ, Es = (Elim ustar).toReal + 2 := ⟨_, rfl⟩
  have hv3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (v (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Es) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (v (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Es hb (hMb k)
      (hform_nn _ _) (hEs ▸ hvb (σ k))⟩
  choose V3 hV3 hV3b using hv3
  have hcv := aux_prop_uniform_resolvent_ident_functional_passage hd Qtri hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (v (σ k) : SobolevData _).1) (i ustar hustar)
    (by rw [hival]; exact hvconv.comp hσ.tendsto_atTop) V3 hV3 _ hV3b lam f f.continuous
  -- finite-cutoff minimality along the subsequence
  have hfk : ∀ k, MemLp (f : SpatialCoordinates d → ℝ) 2 (ν (σ k)) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν (σ k)) _ hKc (hνsupp (σ k)) f
      f.continuous
  have hmink : ∀ k,
      sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) +
          (lam * ∫ x, ((u (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (u (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(ν (σ k))) ≤
        sobolevCoefficientForm (a (σ k)) (v (σ k) : SobolevData _) (v (σ k) : SobolevData _) +
          (lam * ∫ x, ((v (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (v (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(ν (σ k))) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens (σ k)
    have := aux_prop_uniform_resolvent_ident_finite_min _ (a (σ k)) (ν (σ k)) D hD f (hfk k)
      lam hlam.le (R (σ k)) (u (σ k)) (hRu (σ k)) (hweak (σ k)) (v (σ k))
    linarith
  -- identify the limits with the functional of the parent
  have hJb2 : ∫ x, (J ubar x) ^ 2 ∂μ = ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJb1 : ∫ x, f x * J ubar x ∂μ = ∫ x, f x * T (i ubar hubar) x ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJs2 : ∫ x, (J ustar x) ^ 2 ∂μ = ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  have hJs1 : ∫ x, f x * J ustar x ∂μ = ∫ x, f x * T (i ustar hustar) x ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  obtain ⟨cT, hcT⟩ : ∃ cT : ℝ, cT = lam * ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ubar hubar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨dT, hdT⟩ : ∃ dT : ℝ, dT = lam * ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ustar hustar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (Elim ubar).toReal := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = (Elim ustar).toReal := ⟨_, rfl⟩
  rw [← hcT] at hcu
  rw [← hdT] at hcv
  -- the key inequality `Func ubar ≤ Func ustar`
  have key : A + cT ≤ Bs + dT := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = A + cT - (Bs + dT) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by linarith
    have e1 := (tendsto_order.1 hcu).1 (cT - δ / 4) (by linarith)
    have e2 := (tendsto_order.1 hcv).2 (dT + δ / 4) (by linarith)
    have e3 := hσ.tendsto_atTop.eventually (hvev (δ / 4) (by linarith))
    rw [← hBs] at e3
    have e4 : ∀ᶠ k in atTop,
        sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) <
          A - δ / 4 := by
      filter_upwards [e1, e2, e3] with k h1 h2 h3
      have := hmink k
      linarith
    obtain ⟨k0, hk0⟩ := e4.exists
    have hpos : 0 < A - δ / 4 := lt_of_le_of_lt (hform_nn _ _) hk0
    have hle : Elim ubar ≤ ENNReal.ofReal (A - δ / 4) :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (e4.mono fun k hk => (hENle (σ k) (u (σ k))).trans
          (ENNReal.ofReal_le_ofReal hk.le)).frequently
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal hpos.le, ← hA] at this
    linarith
  -- `ubar` is a minimizer, hence `ubar = ustar`
  refine huniq ubar hubar (fun w hw => ?_)
  have := hminle w hw
  rw [hJb2, hJb1]
  rw [hJs2, hJs1] at this
  rw [hA, hBs, hcT, hdT] at key
  linarith

end SubdiffusiveProcess.Paper
end

section

/-!
# Facts about the actual cube and the actual cutoff speed measures

Auxiliary argument for the `hident` identification of `prop_uniform_resolvent`.
-/


open Filter MeasureTheory Topology Set Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- The open cube is a ball of the sup metric. -/
theorem aux_prop_uniform_resolvent_ident_cube_eq_ball {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) : (centeredCube z r hr : Set (SpatialCoordinates d)) = ball z (r / 2) := rfl

theorem aux_prop_uniform_resolvent_ident_cube_nonempty {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) : (centeredCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
  ⟨z, mem_ball_self (half_pos hr)⟩

theorem aux_prop_uniform_resolvent_ident_cube_compl_nonempty {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ((centeredCube z r hr : Set (SpatialCoordinates d))ᶜ).Nonempty := by
  refine ⟨fun i => z i + r, ?_⟩
  rw [aux_prop_uniform_resolvent_ident_cube_eq_ball, mem_compl_iff, mem_ball, not_lt]
  have i0 : Fin d := ⟨0, by omega⟩
  have h := dist_le_pi_dist (fun i => z i + r) z i0
  rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hr] at h
  linarith

/-- The closed and open cube differ by a Lebesgue-null set. -/
theorem aux_prop_uniform_resolvent_ident_cube_restrict_closure {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) :
    volume.restrict (closure (centeredCube z r hr : Set (SpatialCoordinates d))) =
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [aux_prop_uniform_resolvent_ident_cube_eq_ball, closure_ball z (half_pos hr).ne']
  refine Measure.restrict_congr_set (ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    measurableSet_ball.nullMeasurableSet ?_).symm
  · rw [Real.volume_pi_ball z (half_pos hr), Real.volume_pi_closedBall z (half_pos hr).le]
  · rw [Real.volume_pi_closedBall z (half_pos hr).le]
    exact ENNReal.ofReal_ne_top

/-- The actual cutoff speed density is continuous. -/
theorem aux_prop_uniform_resolvent_ident_density_continuous {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  unfold cutoffSpeedDensity cutoffPotential
  refine Real.continuous_exp.comp (Continuous.sub ?_ continuous_const)
  exact (H omega).continuous.add
    (continuous_finsetSum _ fun j _ => (omega (-(Int.ofNat j))).continuous)

/-- The actual restricted cutoff speed measure has bounded Lebesgue density on the cube. -/
theorem aux_prop_uniform_resolvent_ident_density_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧
      (cutoffSpeedMeasure M H omega N).restrict
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal D • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  set K := closure (centeredCube z r hr : Set (SpatialCoordinates d)) with hK
  have hKc : IsCompact K := (centeredCube_isBounded z hr).isCompact_closure
  have hcont := aux_prop_uniform_resolvent_ident_density_continuous M H omega N
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  unfold cutoffSpeedMeasure
  rw [restrict_withDensity isClosed_closure.measurableSet, ← withDensity_const,
    ← aux_prop_uniform_resolvent_ident_cube_restrict_closure z hr]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with x hx
  simp only [Function.comp_apply]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hC x hx
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- Finite mass on the closed half-thickening of the closed cube from unit-ball bounds. -/
theorem aux_prop_uniform_resolvent_ident_cthickening_finite {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ball x 1 ⊆ Region)
    (ν : Measure (SpatialCoordinates d)) (hball : ∀ x ∈ Region, ν (ball x 1) < ⊤) :
    ν (cthickening (1 / 2) (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) < ⊤ := by
  set K := closure (centeredCube z r hr : Set (SpatialCoordinates d)) with hK
  have hKc : IsCompact K := (centeredCube_isBounded z hr).isCompact_closure
  have hS : IsCompact (cthickening (1 / 2) K) := hKc.cthickening
  refine hS.measure_lt_top_of_nhdsWithin (fun x hx => ?_)
  rw [cthickening_eq_biUnion_closedBall K (by norm_num), closure_closure] at hx
  obtain ⟨y, hyK, hxy⟩ := mem_iUnion₂.1 hx
  have hxR : x ∈ Region := hNeighborhood y hyK (by
    rw [mem_ball]; rw [mem_closedBall] at hxy; linarith)
  exact ⟨ball x 1, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x one_pos), hball x hxR⟩

/-- Uniform convergence on the cube of pointwise representatives gives `L²(Q)` convergence. -/
theorem aux_prop_uniform_resolvent_ident_L2_of_uniform {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (w : ℕ → DomainL2 (centeredCube z r hr)) (R : ℕ → SpatialCoordinates d → ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg : MemLp g 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hR : ∀ k, R k =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] w k)
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |R k x - g x| < ε) :
    Tendsto w atTop (𝓝 (hg.toLp g)) := by
  set C := (measureUnivNNReal (volume.restrict (centeredCube z r hr :
    Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hC0 : 0 ≤ C := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k0, hk0⟩ := hunif (ε / (C + 1)) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  rw [dist_eq_norm]
  have hae : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ‖(w k - hg.toLp g) x‖ ≤ ε / (C + 1) := by
    filter_upwards [Lp.coeFn_sub (w k) (hg.toLp g), MemLp.coeFn_toLp hg, hR k,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x h1 h2 h3 hx
    rw [h1, Pi.sub_apply, h2, ← h3, Real.norm_eq_abs]
    exact (hk0 k hk x hx).le
  have hb := Lp.norm_le_of_ae_bound (by positivity) hae
  have : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  exact lt_of_le_of_lt hb this

/-- A convergent sequence of masses is bounded. -/
theorem aux_prop_uniform_resolvent_ident_mass_bound {d : ℕ}
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (S : Set (SpatialCoordinates d)) (hfin : ∀ k, ν k univ < ⊤) :
    ∃ Mbar : ℝ, ∀ k, (ν k S).toReal ≤ Mbar := by
  have h1 := hW (fun _ => (1 : ℝ)) continuous_const
  obtain ⟨Mbar, hM⟩ := h1.bddAbove_range
  refine ⟨Mbar, fun k => ?_⟩
  have hk := hM ⟨k, rfl⟩
  simp only [integral_const, smul_eq_mul, mul_one] at hk
  refine le_trans ?_ hk
  exact ENNReal.toReal_mono (hfin k).ne (measure_mono (subset_univ S))

end SubdiffusiveProcess.Paper
end

section

/-!
# `hident` for `prop_uniform_resolvent`, proved from the parent hypotheses

Auxiliary identification argument.  The conclusion of
`aux_prop_uniform_resolvent_ident` is verbatim the `hident` binder of the compiled
`aux_prop_uniform_resolvent_of_ident` (`ParentPoint.lean`).
-/


open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- One sample of the identification, on unfolded data: every uniform-on-closure cluster `g` of
the actual resolvents along a subsequence with bounded coercivity constants has `L²(Q)` class
`ustar`.  All inputs are the parent hypotheses at one sample. -/
theorem aux_prop_uniform_resolvent_ident_sample
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region)
    (muFull : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧ muFull (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (Elim : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hmosco : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) //
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))) Elim ∧
      _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) //
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))) Elim)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℝ)
    (hT : 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
      MeasureTraceCharacterization hd Qtri hr (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) Ktrace Ctrace T)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) → Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hival : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim u ≠ ∞),
      (J u) =ᵐ[muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    (hmin : Elim ustar ≠ ∞ ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim w ≠ ∞ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J ustar x ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))) ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim w ≠ ∞ →
        (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim v ≠ ∞ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J v x ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (R : ℕ → SpatialCoordinates d → ℝ)
    (hfinite : ∀ N : ℕ,
      (R N =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] ((u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) =
          ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
        (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (g : C(SpatialCoordinates d, ℝ)) (Mb : ℝ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hbd : ∀ k, Kc (σ k) ≤ Mb)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |R (σ k) x - g x| < eps) :
    (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))] (ustar : SpatialCoordinates d → ℝ) := by
  have hKc : IsCompact (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr).isCompact_closure
  have hlt1 : epsilon < 1 := by
    refine hepsilon'.trans ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have ht : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hReg : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), x ∈ Region := fun x hx =>
    hNeighborhood x hx (Metric.mem_ball_self one_pos)
  have hcth_cut : ∀ N, cutoffSpeedMeasure M H omega N
      (Metric.cthickening (1 / 2) (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) < ⊤ := fun N =>
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).2 N).trans_lt ENNReal.ofReal_lt_top)
  have hcth_full : muFull (Metric.cthickening (1 / 2) (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) < ⊤ :=
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).1).trans_lt ENNReal.ofReal_lt_top)
  have hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun N => ∫ x, h x ∂((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))
        atTop (𝓝 (∫ x, h x ∂(muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))) := fun h hh =>
    aux_prop_uniform_resolvent_ident_restrict_tendsto (fun N => cutoffSpeedMeasure M H omega N)
      muFull ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) (centeredCube _ _ hr).isOpen hKc
      (aux_prop_uniform_resolvent_ident_cube_nonempty _ hr)
      (aux_prop_uniform_resolvent_ident_cube_compl_nonempty hd _ hr) (1 / 2) (by norm_num)
      hcth_cut hcth_full hmu.1 hmu.2.1 h hh
  have : IsFiniteMeasure (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hmu.2.2⟩
  have hsupp : ∀ ν : Measure (SpatialCoordinates d), (ν.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))ᶜ = 0 := by
    intro ν
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet, compl_inter_self,
      measure_empty]
  have hνfin : ∀ N, (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) univ < ⊤ := by
    intro N
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (Metric.self_subset_cthickening _)).trans_lt (hcth_cut N)
  obtain ⟨Mbar, hMbar⟩ := aux_prop_uniform_resolvent_ident_mass_bound
    (fun N => (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) hW (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) hνfin
  have hνgrowth : ∀ N, ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) (Metric.ball x rr) ≤
        ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) := fun N x hx rr hrr hrr1 =>
    (Measure.restrict_apply_le _ _).trans ((hgrowth x (hReg x hx) rr hrr hrr1).2 N)
  have hg2 : MemLp (g : SpatialCoordinates d → ℝ) 2 (volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) := by
    refine aux_prop_uniform_resolvent_ident_memLp_of_continuous _ (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) hKc ?_ g
      g.continuous
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    exact measure_mono_null (fun x hx => hx.1 (subset_closure hx.2)) measure_empty
  have hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1) atTop (𝓝 (hg2.toLp g)) :=
    aux_prop_uniform_resolvent_ident_L2_of_uniform _ hr (fun k => (u (σ k) : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1)
      (fun k => R (σ k)) g hg2 (fun k => (hfinite (σ k)).1) (fun ε hε => by
        obtain ⟨k0, hk0⟩ := hunif ε hε
        exact ⟨k0, fun k hk x hx => hk0 k hk x (subset_closure hx)⟩)
  have heq := aux_prop_uniform_resolvent_ident_deterministic hd Qtri hr SInterp
    ((d : ℝ) - epsilon) ht
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    _ (fun N u => rfl) Elim hmosco.1 hmosco.2
    (fun N => (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) (hsupp muFull) Kmu Mbar hKmu hνfin
    (fun N => hsupp _) hMbar hνgrowth
    (fun N => aux_prop_uniform_resolvent_ident_density_le M H omega N _ hr) hW
    T Ktrace Ctrace hT.1 hT.2.1 hT.2.2 i hival J hJ lam hlam f ustar hmin u R
    (fun N => (hfinite N).1) (fun N => (hfinite N).2.1) (fun N => (hfinite N).2.2) Kc hcoer3
    σ hσ Mb hbd (hg2.toLp g) hconv
  rw [← heq]
  exact (MemLp.coeFn_toLp hg2).symm

/-- **`hident`, proved from the `prop_uniform_resolvent` hypotheses.**  The binder
telescope is the parent header verbatim (as in `aux_prop_uniform_resolvent_of_ident`);
the conclusion is exactly that theorem's extra input `hident`.  Route: paper label `mfd:prop-uniform-resolvent`  (Mosco liminf + recovery, varying-measure trace passage via `lem_19`, finite
minimality from the weak equation, uniqueness of the limit minimizer). -/
theorem aux_prop_uniform_resolvent_ident
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (_hps : ps.Nonempty)
    (_hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
          (∃ σ : ℕ → ℕ, StrictMono σ ∧
              (∀ k, Kcoer (σ k) omega ≤ Mb ∧ Khol (σ k) omega ≤ Mb) ∧
              ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  |RN (σ k) omega lam f x - g x| < eps) →
          ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp
  filter_upwards [hmosco, hmu, hnonneg, hgrowth, hcoerN, hT, hival, hJ, hmin, hfinite]
    with omega hmo hmuo hnno hgro hcoo hTo hivo hJo hmino hfino
  intro lam hlam f g Mb hσ
  obtain ⟨σ, hσmono, hbd, hunif⟩ := hσ
  exact aux_prop_uniform_resolvent_ident_sample hd epsilon hepsilon' Qtri hr M H omega Region
    hNeighborhood (muFull omega) hmuo (Kmu omega) hnno.1 hgro (Elim omega) hmo (T omega)
    (Ktrace omega) (Ctrace omega) hTo (i omega) hivo (J omega) hJo lam hlam f
    (ustar omega lam f) (hmino lam hlam f) (fun N => uN N omega lam f)
    (fun N => RN N omega lam f)
    (fun N => ⟨(hfino N lam hlam f).1, (hfino N lam hlam f).2.2.1, (hfino N lam hlam f).2.2.2⟩)
    (fun N => Kcoer N omega) (fun N v => (hcoo N v).2.1) SInterp g (Mb : ℝ) σ hσmono
    (fun k => (hbd k).1) hunif

end SubdiffusiveProcess.Paper
end

namespace SubdiffusiveProcess.Paper



theorem prop_uniform_resolvent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (ps : Finset ℝ) (hps : ps.Nonempty)
    (hps_ge : ∀ p ∈ ps, (1 : ℝ) ≤ p)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization M H),
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    ∀ (PN : ℕ → BilateralField d →
        SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d))
      (_hKN : ∀ N, IsMarkovKernel (KN N))
      (_hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (_hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
      (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ)
      (_hRN : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        RN N omega lam f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) *
                f (path (Real.toNNReal s))) t)
            ∂(KN N (omega, x)))
      (_hRNmeas : ∀ (N : ℕ) (lam : ℝ)
          (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
        Measurable (fun omega : BilateralField d => RN N omega lam f x))
      (G : BilateralField d → (DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ] DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)))
      (_hGmeas : Measurable G),
    let Elim : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G omega) u).toENNReal
    let E_N : BilateralField d → ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) →
        killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega N v w =>
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
    let EN : BilateralField d → ℕ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞ :=
      fun omega N u =>
        ⨅ v : {v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) // (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
          ENNReal.ofReal (E_N omega N v.val v.val)
    ∀ (_hmosco : ∀ᵐ omega ∂P,
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N => EN omega N) (Elim omega) ∧
        _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N => EN omega N) (Elim omega))
      (muFull : BilateralField d → Measure (SpatialCoordinates d)),
    let mu : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega =>
        (muFull omega).restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    let muN : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
      fun N omega =>
        (cutoffSpeedMeasure M H omega N).restrict
          (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
    ∀ (_hmu : ∀ᵐ omega ∂P,
        MeasuresConvergeLocally
            (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          muFull omega (frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
          muFull omega (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
      (Region : Set (SpatialCoordinates d))
      (_hRegionBounded : Bornology.IsBounded Region)
      (_hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        Metric.ball x 1 ⊆ Region)
      (Kmu : BilateralField d → ℝ)
      (Kcoer Khol : ℕ → BilateralField d → ℝ)
      (_hmeas : Measurable Kmu ∧ (∀ N, Measurable (Kcoer N)) ∧
        ∀ N, Measurable (Khol N))
      (_hnonneg : ∀ᵐ omega ∂P,
        0 ≤ Kmu omega ∧ ∀ N, 0 ≤ Kcoer N omega ∧ 0 ≤ Khol N omega)
      (_hmom : ∀ p ∈ ps,
        MemLp Kmu (ENNReal.ofReal p) P ∧
        (∃ B : ℝ, ∀ N,
          (eLpNorm (Kcoer N) (ENNReal.ofReal p) P).toReal ≤ B ∧
          (eLpNorm (Khol N) (ENNReal.ofReal p) P).toReal ≤ B) ∧
        (∀ N, MemLp (Kcoer N) (ENNReal.ofReal p) P ∧
          MemLp (Khol N) (ENNReal.ofReal p) P))
      (_hgrowth : ∀ᵐ omega ∂P, ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
      (_hcoerN : ∀ᵐ omega ∂P, ∀ N, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
        ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ^ 2 ≤
            Kcoer N omega * E_N omega N v v ∧
        (∃ v3 : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr
            _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
          v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
            Kcoer N omega * E_N omega N v v) ∧
        globalFractionalSqNorm (3 / 4)
            (Set.indicator ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
              (fun x => (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x)) ≤
          ENNReal.ofReal (Kcoer N omega * E_N omega N v v))
      (_hcoerLim : ∀ᵐ omega ∂P, ∃ C3 : ℝ, 0 < C3 ∧
        ∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega u ≠ ∞ →
          ∃ v3 : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr
              _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v3.val 0 = u ∧
            (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr
                _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
              C3 * (Elim omega u).toReal)
      (_hHolder : ∀ᵐ omega ∂P, ∀ N,
        ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
        ∀ MF : ℝ, 0 ≤ MF →
        (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N v w =
              ∫ x in ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                F0 x * (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x) →
          ∃ vc : C(SpatialCoordinates d, ℝ),
            ((vc : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
              ((v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)), vc x = 0) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |vc x| ≤ Khol N omega * MF) ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |vc x - vc y| ≤
                  Khol N omega * MF * dist x y ^ (1 / 2 : ℝ)))
      (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (mu omega))
      (Ktrace Ctrace : BilateralField d → ℝ)
      (_hT : ∀ᵐ omega ∂P,
        0 ≤ Ktrace omega ∧ 0 ≤ Ctrace omega ∧
        MeasureTraceCharacterization hd Qtri hr (mu omega) (Ktrace omega)
          (Ctrace omega) (T omega))
      (i : (omega : BilateralField d) → (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) →
        Elim omega u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
      (_hival : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (i omega u hu).val 0 = u)
      (J : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
      (_hJ : ∀ᵐ omega ∂P, ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim omega u ≠ ∞),
        (J omega u) =ᵐ[mu omega]
          (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
      (ustar : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)),
    let Func : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) → ℝ :=
      fun omega lam f u =>
        (Elim omega u).toReal +
            lam * (∫ x, (J omega u x) ^ 2 ∂(mu omega)) -
          2 * (∫ x, f x * J omega u x ∂(mu omega))
    ∀ (_hmin : ∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Elim omega (ustar omega lam f) ≠ ∞ ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            Func omega lam f (ustar omega lam f) ≤
              Func omega lam f w) ∧
          (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega w ≠ ∞ →
            (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr), Elim omega v ≠ ∞ →
              Func omega lam f w ≤ Func omega lam f v) →
            w = ustar omega lam f))
      (uN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr))
      (_hfinite : ∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          (RN N omega lam f =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            ((uN N omega lam f : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 :
              SpatialCoordinates d → ℝ)) ∧
          (∀ x ∈ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            |RN N omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr),
            E_N omega N (uN N omega lam f) w =
              ∫ x, (f x - lam * RN N omega lam f x) *
                (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x ∂(muN N omega)) ∧
          E_N omega N (uN N omega lam f) (uN N omega lam f) ≤
            ‖f‖ ^ 2 *
              (muN N omega ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
      (_SInterp : CubeFractionalInterpolationInput d hd)
      (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0),
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : BilateralField d |
                ∃ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
          (∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            ∀ x ∉ ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              R lam f omega x = 0)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P, ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) := by
  intro M H HI P PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas Elim E_N EN
    hmosco muFull mu muN hmu Region hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg
    hmom hgrowth hcoerN hcoerLim hHolder T Ktrace Ctrace hT i hival J hJ ustar Func hmin uN
    hfinite SInterp hcamp
  exact aux_prop_uniform_resolvent_of_ident hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr
    M H HI PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region
    hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim
    hHolder T Ktrace Ctrace hT i hival J hJ ustar hmin uN hfinite SInterp hcamp
    (aux_prop_uniform_resolvent_ident hd epsilon hepsilon hepsilon' ps hps hps_ge Qtri hr
      M H HI PN KN hKN hin L hL hLlocal hLstrong RN hRN hRNmeas G hGmeas hmosco muFull hmu Region
      hRegionBounded hNeighborhood Kmu Kcoer Khol hmeas hnonneg hmom hgrowth hcoerN hcoerLim
      hHolder T Ktrace Ctrace hT i hival J hJ ustar hmin uN hfinite SInterp hcamp)

end SubdiffusiveProcess.Paper
