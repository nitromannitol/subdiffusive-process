module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
public import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.s9_actual_uniqueness
public import SubdiffusiveProcess.Paper.in_killed_inverse_inprob_cube
public import SubdiffusiveProcess.Paper.inputs_baseline_witness
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_contraction_witness
public import SubdiffusiveProcess.Lnorm.JointLpExtraction
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Convergence in probability of `T (φ n)` to `G` along a strictly increasing `φ`, from the
`(ε, ρ)` form of convergence in probability of `T N` to `G` (helper of
`lem_local_normalizations_operator_unique`). -/
theorem aux_lem_local_normalizations_operator_unique_inmeasure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*} [NormedAddCommGroup E]
    (T : ℕ → Ω → E) (G : Ω → E)
    (h : ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      μ {x | eps ≤ ‖T N x - G x‖} ≤ ENNReal.ofReal rho)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    TendstoInMeasure μ (fun n => T (φ n)) atTop G := by
  refine tendstoInMeasure_of_ne_top fun ε hε hne => ?_
  lift ε to ℝ≥0 using hne
  have hε' : 0 < (ε : ℝ) := by exact_mod_cast hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ⊤
  · exact Eventually.of_forall fun _ => hδt ▸ le_top
  · have hρ : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
    obtain ⟨N0, hN0⟩ := h (ε : ℝ) hε' δ.toReal hρ
    refine Filter.eventually_atTop.2 ⟨N0, fun n hn => ?_⟩
    have hset : {x | (ε : ℝ≥0∞) ≤ edist (T (φ n) x) (G x)} = {x | (ε : ℝ) ≤ ‖T (φ n) x - G x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq, edist_eq_enorm_sub]
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    rw [hset]
    calc μ {x | (ε : ℝ) ≤ ‖T (φ n) x - G x‖} ≤ ENNReal.ofReal δ.toReal := hN0 (φ n) (hn.trans (hφ.id_le n))
      _ = δ := ENNReal.ofReal_toReal hδt

/-- Operator form of `thm_c1` ("all subsequential limits coincide", `mfd:thm-c1`) for the actual
killed inverses `G_N^{Q_i}` of the cutoff coefficients on cubes `Q_i = centeredCube 0 (r i)` of triadic
side `r i = 3^m`: for any two cutoff subsequences there is a common refinement `τ` along which both
subsequences of killed inverses converge in operator norm, on every cube of the family, to the SAME
limit, on one event of full chaos probability.

Proof.  `s9_actual_uniqueness` (uniqueness of the a.s. subsequential operator limits, the input `hUniq`
of `in_killed_inverse_inprob_cube`, supplied with the standing input witnesses `inputs_*_witness`) gives
convergence in probability of `G_N^{Q_i}` to a measurable random operator `G i`, for every rational
triadic cube.  Convergence in probability along a subsequence has an almost surely convergent
subsequence; the countably many pairs (cube, subsequence) are handled by the diagonal extraction
`ae_diagonal_countable_subseq_index`, and the limit is identified with `0` by uniqueness of limits. -/
theorem lem_local_normalizations_operator_unique
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (_EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ (r : ℕ → ℝ) (hr : ∀ i, 0 < r i), (∀ i, ∃ m : ℤ, r i = (3 : ℝ) ^ m) →
          ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            ∃ G : (i : ℕ) → BilateralField d →
              DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)) →L[ℝ]
                DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i : ℕ,
                Tendsto (fun n => volumeResponseOperator
                    (killedResponseSpace (centeredCube_killedPoincare (0 : SpatialCoordinates d) (hr i)))
                    (cutoffPositiveCoefficient M H omega (φ1 (τ n)) (0 : SpatialCoordinates d) (hr i)))
                  atTop (𝓝 (G i omega)) ∧
                Tendsto (fun n => volumeResponseOperator
                    (killedResponseSpace (centeredCube_killedPoincare (0 : SpatialCoordinates d) (hr i)))
                    (cutoffPositiveCoefficient M H omega (φ2 (τ n)) (0 : SpatialCoordinates d) (hr i)))
                  atTop (𝓝 (G i omega))     := by
  classical
  have hUniq := s9_actual_uniqueness d hd Jc Pc Xc Sf W Cp D hES Step (inputs_baseline_witness d hd)
    Interp (inputs_BD_witness d) (inputs_BDQ_witness d)
    (fun z r hr S hS a T hT u => inputs_contraction_witness d z r hr S hS a T hT u)
  obtain ⟨δ0, hδ0, hcube⟩ := in_killed_inverse_inprob_cube d hd Interp Jc Pc Xc W Cp Sf hUniq
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H HI hM r hr hr3 φ1 φ2 hφ1 hφ2
  have hM0 : M.delta ≤ δ0 := hM.trans (min_le_right _ _)
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let T : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)) :=
    fun i N β => volumeResponseOperator
      (killedResponseSpace (centeredCube_killedPoincare (0 : SpatialCoordinates d) (hr i)))
      (cutoffPositiveCoefficient M H β N (0 : SpatialCoordinates d) (hr i))
  have hex : ∀ i, ∃ G : BilateralField d →
      DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (0 : SpatialCoordinates d) (r i) (hr i)),
      Measurable G ∧ ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        μ {β | eps ≤ ‖T i N β - G β‖} ≤ ENNReal.ofReal rho := fun i =>
    hcube M Rm Sreg It H HI hM0 (0 : SpatialCoordinates d) (r i) (hr i)
      (fun c => ⟨0, by simp⟩) (hr3 i) (centeredCube_killedPoincare (0 : SpatialCoordinates d) (hr i))
  choose G hGm hG using hex
  let φ : Bool → ℕ → ℕ := fun b => if b then φ2 else φ1
  have hφ : ∀ b, StrictMono (φ b) := by
    intro b; cases b
    · exact hφ1
    · exact hφ2
  let X : ℕ × Bool → ℕ → BilateralField d → ℝ :=
    fun t n β => ‖T t.1 (φ t.2 n) β - G t.1 β‖
  have hsub : ∀ (t : ℕ × Bool) (σ : ℕ → ℕ), StrictMono σ → ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∃ L : BilateralField d → ℝ, ∀ᵐ β ∂μ, Tendsto (fun n => X t (σ (τ n)) β) atTop (𝓝 (L β)) := by
    intro t σ hσ
    obtain ⟨τ, hτ, hae⟩ := (aux_lem_local_normalizations_operator_unique_inmeasure μ (T t.1) (G t.1)
      (hG t.1) (φ t.2 ∘ σ) ((hφ t.2).comp hσ)).exists_seq_tendsto_ae
    refine ⟨τ, hτ, fun _ => 0, ?_⟩
    filter_upwards [hae] with β hβ
    exact tendsto_iff_norm_sub_tendsto_zero.1 hβ
  obtain ⟨δ, hδ, L, hL⟩ := SubdiffusiveProcess.Lnorm.ae_diagonal_countable_subseq_index μ X hsub id
    strictMono_id
  have hL0 : ∀ t : ℕ × Bool, ∀ᵐ β ∂μ, L t β = 0 := by
    intro t
    obtain ⟨ns, hns, hae⟩ := (aux_lem_local_normalizations_operator_unique_inmeasure μ (T t.1) (G t.1)
      (hG t.1) (φ t.2 ∘ δ) ((hφ t.2).comp hδ)).exists_seq_tendsto_ae
    filter_upwards [hae, hL] with β h1 h2
    have h1' := tendsto_iff_norm_sub_tendsto_zero.1 h1
    have h2' := (h2 t).comp hns.tendsto_atTop
    exact tendsto_nhds_unique h2' h1'
  refine ⟨δ, hδ, G, ?_⟩
  have hL0' : ∀ᵐ β ∂μ, ∀ t : ℕ × Bool, L t β = 0 := by
    rw [ae_all_iff]; exact hL0
  filter_upwards [hL, hL0'] with β hβ hβ0 i
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.2 ?_, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  · have := hβ (i, false); rw [hβ0 (i, false)] at this; exact this
  · have := hβ (i, true); rw [hβ0 (i, true)] at this; exact this

end SubdiffusiveProcess.Paper
