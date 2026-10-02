import SubdiffusiveProcess.Paper.lem_finite_stopping
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.prop_growth_admissible
import SubdiffusiveProcess.Paper.calib_H0_triadic_root_growth
import SubdiffusiveProcess.Paper.cor_neumann_source
import SubdiffusiveProcess.Paper.fscc_char_holder_neumann
import SubdiffusiveProcess.Paper.fscc_zero_holder_neumann
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
import SubdiffusiveProcess.Paper.lane4_reference_point_moments
import SubdiffusiveProcess.Paper.reference_coefficients
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ChaosRootFieldLaw
import SubdiffusiveProcess.Main.ScaledLayerLaw
import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.InfraredAdmissible
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.MeanZero
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Sobolev.ResponseComparison
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.lfsc_partition_main

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- Assemble the three already estimated parts of a finite sourced stopping
partition on the same good event. The supplier bounds below are the stopped,
residual, and collar estimates; this lemma introduces no cell estimate. -/
private lemma aux_lem_finite_source_comparison_cells_sum_on_event
    {Ω ι : Type*} [DecidableEq ι]
    (good : Ω → Prop) (sample : Ω) (hgood : good sample)
    (cells stopped residual collar : Finset ι)
    (target : Ω → ι → ℝ)
    (stoppedBudget residualBudget collarBudget source factor err amplitude : ℝ)
    (hcover : cells = (stopped ∪ residual) ∪ collar)
    (hsr : Disjoint stopped residual)
    (hsc : Disjoint stopped collar)
    (hrc : Disjoint residual collar)
    (hstopped : good sample → ∑ i ∈ stopped, target sample i ≤ stoppedBudget)
    (hresidual : good sample → ∑ i ∈ residual, target sample i ≤ residualBudget)
    (hcollar : good sample → ∑ i ∈ collar, target sample i ≤ collarBudget)
    (hbudget : stoppedBudget + residualBudget + collarBudget ≤
      factor * source + err * amplitude ^ 2) :
    ∑ i ∈ cells, target sample i ≤ factor * source + err * amplitude ^ 2 := by
  have hsplit :
      (∑ i ∈ cells, target sample i) =
        (∑ i ∈ stopped, target sample i) +
        (∑ i ∈ residual, target sample i) +
        (∑ i ∈ collar, target sample i) := by
    rw [hcover, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hsc, hrc⟩),
      Finset.sum_union hsr]
  rw [hsplit]
  linarith [hstopped hgood, hresidual hgood, hcollar hgood]

/-! ### Per-sample clauses (the principal's two cell clauses, verbatim) -/

/-- The Dirichlet cell clause of the principal, for one sample (paper 4294--4299, 4310--4337). -/
def aux_lem_finite_source_comparison_cells_cellsDir (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
    ∀ b u : weakSobolevGraph Q,
      ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet aSource F b u →
      ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
        ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
          (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
          Pairwise (fun i j =>
            Disjoint (cell i : Set (SpatialCoordinates d))
              (cell j : Set (SpatialCoordinates d))) ∧
          ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
            (Q : Set (SpatialCoordinates d))) ∧
          ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
            ∀ v : killedSobolevGraph (cell i),
              ‖(v : SobolevData (cell i)).1‖ ≤
                K * ‖@subspaceGradient d (cell i)
                  (killedSobolevGraph (cell i)) v‖,
            ∃ U : SpatialCoordinates d → ℝ,
              ContinuousOn U closedQ ∧
              (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
              (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                  |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
            (∑ i : Fin ncell,
              @dirichletResponse d (cell i)
                (@killedResponseSpace d (cell i) (hPcell i))
                (positiveCoefficientRestrict (hle i) aTarget)
                ⟨sobolevDataRestrict (hle i) u.val,
                  sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
              factor * sobolevCoefficientForm aSource u.val u.val +
                err * (Kf + c2Norm closedQ phi) ^ 2

/-- The mean-zero Neumann cell clause of the principal, for one sample. -/
def aux_lem_finite_source_comparison_cells_cellsNeu (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
    ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
      ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
      let cell := fun i => centeredCube (centers i) (sides i) (hside i)
      ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j =>
          Disjoint (cell i : Set (SpatialCoordinates d))
            (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (Q : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
          ∀ v : killedSobolevGraph (cell i),
            ‖(v : SobolevData (cell i)).1‖ ≤
              K * ‖@subspaceGradient d (cell i)
                (killedSobolevGraph (cell i)) v‖,
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U closedQ ∧
            (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                |U x - U y| ≤ (err / 4) * Kf) ∧
          (∑ i : Fin ncell,
            @dirichletResponse d (cell i)
              (@killedResponseSpace d (cell i) (hPcell i))
              (positiveCoefficientRestrict (hle i) aTarget)
              ⟨sobolevDataRestrict (hle i) u.val,
                sobolevDataRestrict_mem_weak (hle i)
                  ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
            factor * sobolevCoefficientForm aSource u.val u.val +
              err * Kf ^ 2

/-! ### The two analytic inputs named by the paper (4310--4329 and 4323--4327) -/

/-- Sourced partition, Dirichlet branch, one sample (paper 4310--4329, 4331): every Dirichlet
source solution has an actual covering triadic partition, sides in `[3^{-N}, smax]`, with the
target-cell energy bound.  No representative, oscillation or Hölder datum. -/
def aux_lem_finite_source_comparison_cells_partDir (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (smax : ℝ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
    ∀ b u : weakSobolevGraph Q,
      ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet aSource F b u →
      ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
        ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
          (∀ i, ((∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧ sides i ≤ smax) ∧
          Pairwise (fun i j =>
            Disjoint (cell i : Set (SpatialCoordinates d))
              (cell j : Set (SpatialCoordinates d))) ∧
          ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
            (Q : Set (SpatialCoordinates d))) ∧
          ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
            ∀ v : killedSobolevGraph (cell i),
              ‖(v : SobolevData (cell i)).1‖ ≤
                K * ‖@subspaceGradient d (cell i)
                  (killedSobolevGraph (cell i)) v‖,
            (∑ i : Fin ncell,
              @dirichletResponse d (cell i)
                (@killedResponseSpace d (cell i) (hPcell i))
                (positiveCoefficientRestrict (hle i) aTarget)
                ⟨sobolevDataRestrict (hle i) u.val,
                  sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
              factor * sobolevCoefficientForm aSource u.val u.val +
                err * (Kf + c2Norm closedQ phi) ^ 2

/-- Sourced partition, mean-zero Neumann branch, one sample. -/
def aux_lem_finite_source_comparison_cells_partNeu (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (smax : ℝ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
    ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
      ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
      let cell := fun i => centeredCube (centers i) (sides i) (hside i)
      ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, ((∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧ sides i ≤ smax) ∧
        Pairwise (fun i j =>
          Disjoint (cell i : Set (SpatialCoordinates d))
            (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (Q : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
          ∀ v : killedSobolevGraph (cell i),
            ‖(v : SobolevData (cell i)).1‖ ≤
              K * ‖@subspaceGradient d (cell i)
                (killedSobolevGraph (cell i)) v‖,
          (∑ i : Fin ncell,
            @dirichletResponse d (cell i)
              (@killedResponseSpace d (cell i) (hPcell i))
              (positiveCoefficientRestrict (hle i) aTarget)
              ⟨sobolevDataRestrict (hle i) u.val,
                sobolevDataRestrict_mem_weak (hle i)
                  ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
            factor * sobolevCoefficientForm aSource u.val u.val +
              err * Kf ^ 2

/-- Hölder representative of every Dirichlet source solution, constant `Kh (‖F‖ + ‖φ‖_{C²})`. -/
def aux_lem_finite_source_comparison_cells_holDir (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (alpha Kh : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
    ∀ b u : weakSobolevGraph Q,
      ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet a F b u →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U closedQ ∧
        (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
        ∀ x ∈ (closedQ : Set (SpatialCoordinates d)), ∀ y ∈ (closedQ : Set (SpatialCoordinates d)),
          |U x - U y| ≤ Kh * (Kf + c2Norm closedQ phi) * dist x y ^ alpha

/-- Hölder representative of every mean-zero Neumann source solution, constant `Kh ‖F‖`. -/
def aux_lem_finite_source_comparison_cells_holNeu (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (alpha Kh : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a F u →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U closedQ ∧
        (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
        ∀ x ∈ (closedQ : Set (SpatialCoordinates d)), ∀ y ∈ (closedQ : Set (SpatialCoordinates d)),
          |U x - U y| ≤ Kh * Kf * dist x y ^ alpha

/-- One Hölder branch at exponent `1/2`: a random constant with cutoff-uniform first moments
(paper 4323--4327: the constants of `prop_growth`/`cor_neumann_source`, localized later at
`3^{εN}`) serving every cutoff `J` on one full-measure event. -/
def aux_lem_finite_source_comparison_cells_holBranch (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Hol : PositiveCoefficient (centeredCube z r hr) → ℝ → ℝ → Prop) : Prop :=
  ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
    (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
    (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cbank) ∧
    ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ,
      Hol (cutoffPositiveCoefficient model Hused omega J z hr) (1 / 2) (K J omega)

/-! ### Deterministic cell geometry and the error arithmetic of paper 4331--4334 -/

theorem aux_lem_finite_source_comparison_cells_closure_cell_subset {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (c : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (hle : centeredCube c s hs ≤ centeredCube z r hr) :
    closure (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  have h1 : closure (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) := closure_mono hle
  have h2 : closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
    rw [show (closedCube z r hr : Set (SpatialCoordinates d)) =
          Metric.closedBall z (r / 2) from rfl,
        show ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)) = Metric.ball z (r / 2) from rfl,
        closure_ball z (ne_of_gt (half_pos hr))]
  exact h2 ▸ h1

theorem aux_lem_finite_source_comparison_cells_dist_le_side {d : ℕ}
    (c : SpatialCoordinates d) {s : ℝ} (hs : 0 < s) {x y : SpatialCoordinates d}
    (hx : x ∈ closure (centeredCube c s hs : Set (SpatialCoordinates d)))
    (hy : y ∈ closure (centeredCube c s hs : Set (SpatialCoordinates d))) :
    dist x y ≤ s := by
  have hsub : closure (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆
      Metric.closedBall c (s / 2) := by
    rw [show ((centeredCube c s hs : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) = Metric.ball c (s / 2) from rfl]
    exact Metric.closure_ball_subset_closedBall
  have hx' := Metric.mem_closedBall.1 (hsub hx)
  have hy' := Metric.mem_closedBall.1 (hsub hy)
  calc dist x y ≤ dist x c + dist c y := dist_triangle x c y
    _ = dist x c + dist y c := by rw [dist_comm c y]
    _ ≤ s / 2 + s / 2 := add_le_add hx' hy'
    _ = s := by ring

/-- The oscillation/error arithmetic of paper 4331--4334 at `ε = α/8`. -/
theorem aux_lem_finite_source_comparison_cells_osc_arith
    (alpha gamma Ceta Cside Kh Lam dxy s : ℝ) (N : ℕ)
    (halpha : 0 < alpha) (hgamma : gamma ≤ alpha / 8) (hCside : 0 ≤ Cside)
    (hCeta : 4 * Cside ^ alpha ≤ Ceta) (hLam : 0 ≤ Lam)
    (hKh : |Kh| ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)))
    (hdxy0 : 0 ≤ dxy) (hdxy : dxy ≤ s) (hs : s ≤ Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) :
    Kh * Lam * dxy ^ alpha ≤ (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) / 4) * Lam := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpowpos : 0 < (3 : ℝ) ^ (-((N : ℝ) / 4)) := Real.rpow_pos_of_pos h3pos _
  have hd1 : dxy ^ alpha ≤ (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) ^ alpha :=
    Real.rpow_le_rpow hdxy0 (hdxy.trans hs) halpha.le
  have hd2 : (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) ^ alpha =
      Cside ^ alpha * (3 : ℝ) ^ (-(alpha * (N : ℝ)) / 4) := by
    rw [Real.mul_rpow hCside hpowpos.le, ← Real.rpow_mul h3pos.le]
    congr 2
    ring
  have hK : Kh ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)) := (le_abs_self Kh).trans hKh
  have hdpos : 0 ≤ dxy ^ alpha := Real.rpow_nonneg hdxy0 alpha
  have hCa : 0 ≤ Cside ^ alpha := Real.rpow_nonneg hCside alpha
  have hexp : (3 : ℝ) ^ (alpha / 8 * (N : ℝ)) * (3 : ℝ) ^ (-(alpha * (N : ℝ)) / 4) ≤
      (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
    rw [← Real.rpow_add h3pos]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : gamma * (N : ℝ) ≤ alpha / 8 * (N : ℝ) := mul_le_mul_of_nonneg_right hgamma hNn
    linarith
  have h3g : 0 ≤ (3 : ℝ) ^ (-gamma * (N : ℝ)) := (Real.rpow_pos_of_pos h3pos _).le
  have h3a : 0 ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)) := (Real.rpow_pos_of_pos h3pos _).le
  calc Kh * Lam * dxy ^ alpha ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)) * Lam * dxy ^ alpha := by
        gcongr
    _ ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)) * Lam *
          (Cside ^ alpha * (3 : ℝ) ^ (-(alpha * (N : ℝ)) / 4)) := by
        rw [← hd2]; gcongr
    _ = Cside ^ alpha * ((3 : ℝ) ^ (alpha / 8 * (N : ℝ)) *
          (3 : ℝ) ^ (-(alpha * (N : ℝ)) / 4)) * Lam := by ring
    _ ≤ Cside ^ alpha * (3 : ℝ) ^ (-gamma * (N : ℝ)) * Lam := by gcongr
    _ ≤ (Ceta / 4) * (3 : ℝ) ^ (-gamma * (N : ℝ)) * Lam := by
        gcongr
        linarith
    _ = (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) / 4) * Lam := by ring

/-- The partition remainder `C_A 3^{-γ_A N}` is dominated at the merged constants. -/
theorem aux_lem_finite_source_comparison_cells_err_mono (CA gA Ceta gamma : ℝ) (N : ℕ)
    (hC : CA ≤ Ceta) (hCA : 0 ≤ CA) (hg : gamma ≤ gA) :
    CA * (3 : ℝ) ^ (-gA * (N : ℝ)) ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
  have h3 : (3 : ℝ) ^ (-gA * (N : ℝ)) ≤ (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : gamma * (N : ℝ) ≤ gA * (N : ℝ) := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg N)
    linarith
  have h0 : 0 ≤ (3 : ℝ) ^ (-gamma * (N : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc CA * (3 : ℝ) ^ (-gA * (N : ℝ)) ≤ CA * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by gcongr
    _ ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by gcongr

theorem aux_lem_finite_source_comparison_cells_c2Norm_nonneg {d : ℕ}
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) : 0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
    exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; positivity)

/-- Dirichlet branch for one sample: partition + Hölder give the principal's clause. -/
theorem aux_lem_finite_source_comparison_cells_sample_dir {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (N : ℕ) (aT aS : PositiveCoefficient (centeredCube z r hr))
    (alpha gamma Ceta CA gA Cside factor Kh : ℝ)
    (halpha : 0 < alpha) (hgamma : gamma ≤ alpha / 8) (hgA : gamma ≤ gA) (hCside : 0 ≤ Cside)
    (hCeta : 4 * Cside ^ alpha ≤ Ceta) (hCAle : CA ≤ Ceta) (hCA : 0 ≤ CA)
    (hKh : |Kh| ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)))
    (hPart : aux_lem_finite_source_comparison_cells_partDir d z r hr N
      (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) aT aS (CA * (3 : ℝ) ^ (-gA * (N : ℝ))) factor)
    (hHol : aux_lem_finite_source_comparison_cells_holDir d z r hr aS alpha Kh) :
    aux_lem_finite_source_comparison_cells_cellsDir d z r hr N aT aS
      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) factor := by
  intro F Kf hKf hF hFb phi hphi b u hb hsol
  have hP := hPart F Kf hKf hF hFb phi hphi b u hb hsol
  have hH := hHol F Kf hKf hF hFb phi hphi b u hb hsol
  rcases hH with ⟨U, hUc, hUeq, hUhol⟩
  rcases hP with ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcover, hPcell, hsum⟩
  have hLam : 0 ≤ Kf + c2Norm (closedCube z r hr) phi :=
    add_nonneg hKf (aux_lem_finite_source_comparison_cells_c2Norm_nonneg _ _)
  refine ⟨ncell, centers, sides, hside, hle, fun i => (hsides i).1, hdisj, hcover, hPcell,
    U, hUc, hUeq, ?_, ?_⟩
  · intro i x hx y hy
    have hxQ := aux_lem_finite_source_comparison_cells_closure_cell_subset z hr (centers i)
      (hside i) (hle i) hx
    have hyQ := aux_lem_finite_source_comparison_cells_closure_cell_subset z hr (centers i)
      (hside i) (hle i) hy
    have hdxy := aux_lem_finite_source_comparison_cells_dist_le_side (centers i) (hside i) hx hy
    calc |U x - U y| ≤ Kh * (Kf + c2Norm (closedCube z r hr) phi) * dist x y ^ alpha :=
          hUhol x hxQ y hyQ
      _ ≤ _ := aux_lem_finite_source_comparison_cells_osc_arith alpha gamma Ceta Cside Kh _
          (dist x y) (sides i) N halpha hgamma hCside hCeta hLam hKh dist_nonneg hdxy
          (hsides i).2
  · refine hsum.trans ?_
    have herr := aux_lem_finite_source_comparison_cells_err_mono CA gA Ceta gamma N hCAle hCA hgA
    have hsq : 0 ≤ (Kf + c2Norm (closedCube z r hr) phi) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right herr hsq
    linarith

/-- Neumann branch for one sample: partition + Hölder give the principal's clause. -/
theorem aux_lem_finite_source_comparison_cells_sample_neu {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (N : ℕ) (aT aS : PositiveCoefficient (centeredCube z r hr))
    (alpha gamma Ceta CA gA Cside factor Kh : ℝ)
    (halpha : 0 < alpha) (hgamma : gamma ≤ alpha / 8) (hgA : gamma ≤ gA) (hCside : 0 ≤ Cside)
    (hCeta : 4 * Cside ^ alpha ≤ Ceta) (hCAle : CA ≤ Ceta) (hCA : 0 ≤ CA)
    (hKh : |Kh| ≤ (3 : ℝ) ^ (alpha / 8 * (N : ℝ)))
    (hPart : aux_lem_finite_source_comparison_cells_partNeu d z r hr N
      (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) aT aS (CA * (3 : ℝ) ^ (-gA * (N : ℝ))) factor)
    (hHol : aux_lem_finite_source_comparison_cells_holNeu d z r hr aS alpha Kh) :
    aux_lem_finite_source_comparison_cells_cellsNeu d z r hr N aT aS
      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) factor := by
  intro F Kf hKf hF hFb hmean u hsol
  have hP := hPart F Kf hKf hF hFb hmean u hsol
  have hH := hHol F Kf hKf hF hFb hmean u hsol
  rcases hH with ⟨U, hUc, hUeq, hUhol⟩
  rcases hP with ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcover, hPcell, hsum⟩
  refine ⟨ncell, centers, sides, hside, hle, fun i => (hsides i).1, hdisj, hcover, hPcell,
    U, hUc, hUeq, ?_, ?_⟩
  · intro i x hx y hy
    have hxQ := aux_lem_finite_source_comparison_cells_closure_cell_subset z hr (centers i)
      (hside i) (hle i) hx
    have hyQ := aux_lem_finite_source_comparison_cells_closure_cell_subset z hr (centers i)
      (hside i) (hle i) hy
    have hdxy := aux_lem_finite_source_comparison_cells_dist_le_side (centers i) (hside i) hx hy
    calc |U x - U y| ≤ Kh * Kf * dist x y ^ alpha := hUhol x hxQ y hyQ
      _ ≤ _ := aux_lem_finite_source_comparison_cells_osc_arith alpha gamma Ceta Cside Kh Kf
          (dist x y) (sides i) N halpha hgamma hCside hCeta hKf hKh dist_nonneg hdxy
          (hsides i).2
  · refine hsum.trans ?_
    have herr := aux_lem_finite_source_comparison_cells_err_mono CA gA Ceta gamma N hCAle hCA hgA
    have hsq : 0 ≤ Kf ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right herr hsq
    linarith

/-- Combine `sample_dir` and `sample_neu` into the folded Dirichlet/Neumann pair. Isolated
in its own declaration (fresh heartbeat budget): the caller's own goal is the fully
`let`-unfolded principal statement, and elaborating this pairing against that huge unfolded
target directly (instead of through the folded `cellsDir`/`cellsNeu` this lemma exposes)
exceeds the per-declaration heartbeat limit. -/
theorem aux_lem_finite_source_comparison_cells_assemble_pair {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (N : ℕ) (aT aS : PositiveCoefficient (centeredCube z r hr))
    (gamma Ceta CA gA Cside factor Kh : ℝ)
    (hgamma : gamma ≤ (1 / 2 : ℝ) / 8) (hgA : gamma ≤ gA) (hCside : 0 ≤ Cside)
    (hCeta : 4 * Cside ^ (1 / 2 : ℝ) ≤ Ceta) (hCAle : CA ≤ Ceta) (hCA : 0 ≤ CA)
    (hKh : |Kh| ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ)))
    (hPartDir : aux_lem_finite_source_comparison_cells_partDir d z r hr N
      (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) aT aS (CA * (3 : ℝ) ^ (-gA * (N : ℝ))) factor)
    (hPartNeu : aux_lem_finite_source_comparison_cells_partNeu d z r hr N
      (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4))) aT aS (CA * (3 : ℝ) ^ (-gA * (N : ℝ))) factor)
    (hHolDir : aux_lem_finite_source_comparison_cells_holDir d z r hr aS (1 / 2 : ℝ) Kh)
    (hHolNeu : aux_lem_finite_source_comparison_cells_holNeu d z r hr aS (1 / 2 : ℝ) Kh) :
    aux_lem_finite_source_comparison_cells_cellsDir d z r hr N aT aS
        (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) factor ∧
      aux_lem_finite_source_comparison_cells_cellsNeu d z r hr N aT aS
        (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) factor :=
  ⟨aux_lem_finite_source_comparison_cells_sample_dir z hr N aT aS (1 / 2 : ℝ) gamma Ceta CA gA
      Cside factor Kh (by norm_num) hgamma hgA hCside hCeta hCAle hCA hKh hPartDir hHolDir,
    aux_lem_finite_source_comparison_cells_sample_neu z hr N aT aS (1 / 2 : ℝ) gamma Ceta CA gA
      Cside factor Kh (by norm_num) hgamma hgA hCside hCeta hCAle hCA hKh hPartNeu hHolNeu⟩

/-- Probability of the merged exceptional event `Bad_A ∪ Bad_K ∪ T`. -/
theorem aux_lem_finite_source_comparison_cells_merged_prob {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B T : Set Ω)
    (CA gA Ctail alpha Ceta gamma : ℝ) (N : ℕ) (hCA : 0 ≤ CA) (hCtail : 0 ≤ Ctail)
    (hgA : gamma ≤ gA) (hga : gamma ≤ alpha / 8) (hC : CA + Ctail ≤ Ceta)
    (hA : P A ≤ ENNReal.ofReal (CA * (3 : ℝ) ^ (-gA * (N : ℝ))))
    (hB : P B ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (alpha / 8) * (N : ℝ))))
    (hT : P T = 0) :
    P (A ∪ B ∪ T) ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := by
  have h3pos : ∀ x : ℝ, 0 ≤ (3 : ℝ) ^ x := fun x => (Real.rpow_pos_of_pos (by norm_num) x).le
  have hB' : P B ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(alpha / 8) * (N : ℝ))) := by
    have : -1 * (alpha / 8) * (N : ℝ) = -(alpha / 8) * (N : ℝ) := by ring
    rwa [this] at hB
  calc P (A ∪ B ∪ T) ≤ P (A ∪ B) + P T := measure_union_le _ _
    _ = P (A ∪ B) := by rw [hT, add_zero]
    _ ≤ P A + P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (CA * (3 : ℝ) ^ (-gA * (N : ℝ))) +
          ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(alpha / 8) * (N : ℝ))) := add_le_add hA hB'
    _ = ENNReal.ofReal (CA * (3 : ℝ) ^ (-gA * (N : ℝ)) +
          Ctail * (3 : ℝ) ^ (-(alpha / 8) * (N : ℝ))) :=
        (ENNReal.ofReal_add (mul_nonneg hCA (h3pos _)) (mul_nonneg hCtail (h3pos _))).symm
    _ ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 := aux_lem_finite_source_comparison_cells_err_mono CA gA CA gamma N le_rfl hCA hgA
        have h2 := aux_lem_finite_source_comparison_cells_err_mono Ctail (alpha / 8) Ctail gamma N
          le_rfl hCtail hga
        have h3 : (CA + Ctail) * (3 : ℝ) ^ (-gamma * (N : ℝ)) ≤
            Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hC (h3pos _)
        linarith

/-! ### From the project's Euclidean `C^α` class to the sup-metric Hölder bound -/

theorem aux_lem_finite_source_comparison_cells_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * dist x y ^ 2 := by
    calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, dist x y ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : |x j - y j| ≤ dist x y := by
            have := dist_le_pi_dist x y j
            rwa [Real.dist_eq] at this
          have h2 : (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
          rw [h2]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (d : ℝ) * dist x y ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * dist x y ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq dist_nonneg]

theorem aux_lem_finite_source_comparison_cells_holderSeminorm_nonneg {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) :
    0 ≤ holderSeminorm alpha S U := by
  unfold holderSeminorm holderRatioSet
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, y, _, _, rfl⟩
  positivity

theorem aux_lem_finite_source_comparison_cells_holderSeminorm_le {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) :
    holderSeminorm alpha S U ≤ cAlphaNorm alpha S U := by
  unfold cAlphaNorm
  have : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} :=
    Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; positivity)
  linarith

/-- `IsHolderOn` + `cAlphaNorm ≤ C` give `|U x - U y| ≤ (√d)^α C dist(x,y)^α`. -/
theorem aux_lem_finite_source_comparison_cells_holder_dist {d : ℕ}
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) (alpha C : ℝ)
    (halpha : 0 < alpha) (hH : IsHolderOn alpha S U) (hC : cAlphaNorm alpha S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤ Real.sqrt d ^ alpha * C * dist x y ^ alpha := by
  intro x hx y hy
  have hsemi : holderSeminorm alpha S U ≤ C :=
    (aux_lem_finite_source_comparison_cells_holderSeminorm_le _ _ _).trans hC
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, dist_self]
    rw [Real.zero_rpow halpha.ne']
    simp
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hepos : 0 < e := by
      rw [he, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon
        push_neg at hcon
        exact hxy (funext hcon)
      have hj' : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.2 hj
        positivity
      exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have heα : 0 < e ^ alpha := Real.rpow_pos_of_pos hepos alpha
    have hratio : |U x - U y| / e ^ alpha ≤ holderSeminorm alpha S U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤ C * e ^ alpha := by
      have := (div_le_iff₀ heα).1 (hratio.trans hsemi)
      linarith
    have h2 : e ^ alpha ≤ Real.sqrt d ^ alpha * dist x y ^ alpha := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
      exact Real.rpow_le_rpow hepos.le (aux_lem_finite_source_comparison_cells_euclid_le x y)
        halpha.le
    have hC0 : 0 ≤ C :=
      (aux_lem_finite_source_comparison_cells_holderSeminorm_nonneg _ _ _).trans hsemi
    calc |U x - U y| ≤ C * e ^ alpha := h1
      _ ≤ C * (Real.sqrt d ^ alpha * dist x y ^ alpha) := by gcongr
      _ = Real.sqrt d ^ alpha * C * dist x y ^ alpha := by ring

/-- A `prop_growth`-shaped Dirichlet output (moments of `K`, and a.s. a `C^{1/2}`
representative with `cAlphaNorm ≤ K (‖F‖ + ‖φ‖_{C²})`) gives one Dirichlet Hölder branch. -/
theorem aux_lem_finite_source_comparison_cells_holDir_branch {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (K : ℕ → BilateralField d → ℝ) (Cb : ℝ)
    (hmem : ∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb)
    (hpt : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, ∀ (J : ℕ)
        (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf → Measurable F →
        (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
        ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
        ∀ b u : weakSobolevGraph (centeredCube z r hr),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient model Hused om J z hr) F b u →
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K J om * (Kf + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi)) :
    aux_lem_finite_source_comparison_cells_holBranch d model Hused z r hr
      (aux_lem_finite_source_comparison_cells_holDir d z r hr) := by
  set c0 : ℝ := Real.sqrt d ^ (1 / 2 : ℝ) with hc0
  have hc0nn : 0 ≤ c0 := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨fun J omega => c0 * K J omega, c0 * Cb, fun J => (hmem J).const_mul c0,
    fun J => ?_, ?_⟩
  · have hs : eLpNorm (fun omega => c0 * K J omega) (ENNReal.ofReal 1)
        (chaosSampleLaw model).toMeasure =
        ‖c0‖ₑ * eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure :=
      eLpNorm_const_smul c0 (K J) _ _
    rw [hs]
    calc ‖c0‖ₑ * eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ‖c0‖ₑ * ENNReal.ofReal Cb := by gcongr; exact hnorm J
      _ = ENNReal.ofReal (c0 * Cb) := by
          rw [Real.enorm_eq_ofReal hc0nn, ENNReal.ofReal_mul hc0nn]
  · filter_upwards [hpt] with omega homega
    intro J F Kf hKf hF hFb phi hphi b u hb hsol
    obtain ⟨U, hUc, hUeq, hUhol, hUnorm⟩ := homega J F Kf hKf hF hFb phi hphi b u hb hsol
    refine ⟨U, hUc.continuousOn, hUeq, ?_⟩
    intro x hx y hy
    have h := aux_lem_finite_source_comparison_cells_holder_dist _ U (1 / 2) _
      (by norm_num) hUhol hUnorm x hx y hy
    calc |U x - U y| ≤ c0 * (K J omega * (Kf + c2Norm (closedCube z r hr) phi)) *
          dist x y ^ (1 / 2 : ℝ) := h
      _ = c0 * K J omega * (Kf + c2Norm (closedCube z r hr) phi) *
          dist x y ^ (1 / 2 : ℝ) := by ring

/-! ### The Hölder input (paper 4323--4327) -/

/-- Dirichlet Hölder branch for the characterized field, on every root cube: `prop_growth`
(sides `≤ 1`) and `prop_growth_large_root` (sides `> 1`), at `α = 1/2`, `t = d - 1/2`,
one moment order `p = 1`. -/
theorem aux_lem_finite_source_comparison_cells_holDir_H
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        aux_lem_finite_source_comparison_cells_holBranch d model H z r hr
          (aux_lem_finite_source_comparison_cells_holDir d z r hr) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨d1, hd1, hG1⟩ := prop_growth d hd E P X W Cp Sf ((d : ℝ) - 1 / 2) (1 / 2) 1
    (fun _ => 1) ht1 ht2 (by norm_num) (by norm_num) (fun _ => le_rfl)
  obtain ⟨d2, hd2, hG2⟩ := prop_growth_large_root d hd E P X W Cp Sf ((d : ℝ) - 1 / 2)
    (1 / 2) 1 (fun _ => 1) ht1 ht2 (by norm_num) (by norm_num) (fun _ => le_rfl)
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro model Rm Sreg It H hH hsmall z r hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨K, Cb, hmem, hnorm, -, hae⟩ :=
      hG1 model Rm Sreg It H hH (hsmall.trans (min_le_left _ _)) z r hr hr1
    refine aux_lem_finite_source_comparison_cells_holDir_branch model H z r hr K (Cb 0)
      (fun J => hmem 0 J) (fun J => hnorm 0 J) ?_
    filter_upwards [hae] with om hom
    intro J F Kf hKf hF hFb phi hphi b u hb hsol
    exact (hom J F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb)
      phi _ hphi le_rfl b u hb hsol).2
  · obtain ⟨K, Cb, hmem, hnorm, -, hae⟩ :=
      hG2 model Rm Sreg It H hH (hsmall.trans (min_le_right _ _)) z r hr (lt_of_not_ge hr1)
    refine aux_lem_finite_source_comparison_cells_holDir_branch model H z r hr K (Cb 0)
      (fun J => hmem 0 J) (fun J => hnorm 0 J) ?_
    filter_upwards [hae] with om hom
    intro J F Kf hKf hF hFb phi hphi b u hb hsol
    exact (hom J F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb)
      phi _ hphi le_rfl b u hb hsol).2

/-- **The Dirichlet Hölder branch with the infrared field removed** (B-D0), paper 4338--4345:
"taking infrared cutoff zero in the same original-field regularity argument" (`A^0 = e^{-H} A`,
i.e. the zeroth infrared truncation `H_0 = 0`, `aux_prop_growth_admissible_zero`).  Cubes of
side `r ≤ 1` (`r = 3^j`, `j ≤ 0`): `prop_growth_admissible` at truncation level `0`.  Cubes of
side `r = 3^j > 1`: `calib_H0_triadic_root_growth` (the scale shift `S_j` sends `A^0_N(3^j ·)` to
the level-`(N+j)` coefficient with the `j` coarsest layers deleted).  Both give the Hölder
conclusion of `prop_growth` at `α = 1/2`, one moment order `p = 1`, and are projected exactly as in
`aux_lem_finite_source_comparison_cells_holDir_H`. -/
theorem aux_lem_finite_source_comparison_cells_holDir_zero
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        aux_lem_finite_source_comparison_cells_holBranch d model
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z r hr
          (aux_lem_finite_source_comparison_cells_holDir d z r hr) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨d1, hd1, hG1⟩ := prop_growth_admissible d hd E P X W Cp Sf ((d : ℝ) - 1 / 2) (1 / 2) 1
    (fun _ => 1) ht1 ht2 (by norm_num) (by norm_num) (fun _ => le_rfl)
  obtain ⟨d2, hd2, hG2⟩ := calib_H0_triadic_root_growth d hd E P X W Cp Sf ((d : ℝ) - 1 / 2)
    (1 / 2) 1 (fun _ => 1) ht1 ht2 (by norm_num) (by norm_num) (fun _ => le_rfl)
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro model Rm Sreg It H _hH hsmall z r hr htri
  by_cases hr1 : r ≤ 1
  · have hzero : (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) =
        fun om => infraredPartialSum om 0 := by
      funext om; simp [infraredPartialSum]
    obtain ⟨K, Cb, hmem, hnorm, -, hae⟩ :=
      hG1 model Rm Sreg It (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Or.inr ⟨0, hzero⟩) (hsmall.trans (min_le_left _ _)) z r hr hr1
    refine aux_lem_finite_source_comparison_cells_holDir_branch model 0 z r hr K (Cb 0)
      (fun J => hmem 0 J) (fun J => hnorm 0 J) ?_
    filter_upwards [hae] with om hom
    intro J F Kf hKf hF hFb phi hphi b u hb hsol
    exact (hom J F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb)
      phi _ hphi le_rfl b u hb hsol).2
  · obtain ⟨j, hj⟩ := htri
    have hr1' : 1 < r := lt_of_not_ge hr1
    have hjpos : 0 < j := by
      by_contra hjn
      push_neg at hjn
      have : (3 : ℝ) ^ j ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hjn
      linarith
    obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hjpos.le).symm⟩
    rw [zpow_natCast] at hj
    subst hj
    have hj'pos : 0 < j' := by exact_mod_cast hjpos
    obtain ⟨K, Cb, hmem, hnorm, -, hae⟩ :=
      hG2 model Rm (hsmall.trans (min_le_right _ _)) j' hj'pos z hr
    refine aux_lem_finite_source_comparison_cells_holDir_branch model 0 z _ hr K (Cb 0)
      (fun J => hmem 0 J) (fun J => hnorm 0 J) ?_
    filter_upwards [hae] with om hom
    intro J F Kf hKf hF hFb phi hphi b u hb hsol
    exact (hom J F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z _ hr).isOpen.measurableSet hFb)
      phi _ hphi le_rfl b u hb hsol).2

/-- Same statement as `aux_lem_finite_source_comparison_cells_holNeu_mono` (defined later in this
file, so not yet in scope here): monotonicity of `holNeu` in the Hölder constant. Duplicated
locally under a fresh name to avoid a forward reference. -/
theorem aux_fscc_holNeuH_holNeu_mono {d : ℕ} {z : SpatialCoordinates d}
    {r : ℝ} {hr : 0 < r} {a : PositiveCoefficient (centeredCube z r hr)} {alpha Kh Kh' : ℝ}
    (h : aux_lem_finite_source_comparison_cells_holNeu d z r hr a alpha Kh) (hle : Kh ≤ Kh') :
    aux_lem_finite_source_comparison_cells_holNeu d z r hr a alpha Kh' := by
  intro F Kf hKf hF hFb hmean u hsol
  obtain ⟨U, hUc, hUeq, hU⟩ := h F Kf hKf hF hFb hmean u hsol
  refine ⟨U, hUc, hUeq, fun x hx y hy => (hU x hx y hy).trans ?_⟩
  have hdist : 0 ≤ dist x y ^ alpha := Real.rpow_nonneg dist_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hKf) hdist

/-- The final `m ≤ J` / `J < m` case split and norm-merge, isolated in its own declaration (same
200000-heartbeat reason as `aux_fscc_holNeuH_core`): the two branch facts are supplied as plain
`Prop`s about *fixed real numbers* `KmVal, KsVal`, not tied to the caller's `if`-defined `Km`/`Ks`
closures, so this elaborates on a small, self-contained goal. -/
theorem aux_fscc_holNeuH_final_merge {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (m J : ℤ) (KmVal KsVal : ℝ)
    (hmJ : m ≤ J → aux_lem_finite_source_comparison_cells_holNeu d z r hr a (1 / 2) KmVal)
    (hsJ : J < m → aux_lem_finite_source_comparison_cells_holNeu d z r hr a (1 / 2) KsVal) :
    aux_lem_finite_source_comparison_cells_holNeu d z r hr a (1 / 2) (‖KmVal‖ + ‖KsVal‖) := by
  by_cases hc : m ≤ J
  · refine aux_fscc_holNeuH_holNeu_mono (hmJ hc) ?_
    have h1 := norm_nonneg KsVal
    have h2 := Real.le_norm_self KmVal
    linarith
  · have hc' : J < m := lt_of_not_ge hc
    refine aux_fscc_holNeuH_holNeu_mono (hsJ hc') ?_
    have h1 := norm_nonneg KmVal
    have h2 := Real.le_norm_self KsVal
    linarith

/-- `SolvesNeumann` only sees its source through `∫ F ψ`; an a.e.-equal source gives the
same solution. -/
theorem aux_fscc_holNeuH_solvesNeumann_congr {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [MeasureTheory.IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    {a : PositiveCoefficient Ω} {F f : SpatialCoordinates d → ℝ}
    (hfF : f =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] F)
    {v : meanZeroSobolevGraph Ω} (hsol : SolvesNeumann a F v) :
    SolvesNeumann a f v := by
  intro ψ
  rw [hsol ψ]
  apply integral_congr_ae
  filter_upwards [hfF] with x hx
  rw [hx]

/-- Split out of `aux_fscc_holNeuH_hSmall_energy`'s micro (`rad ≤ r/2`) branch purely for
heartbeat budget: everything from the second `henergyid` application (transport of the
unit-cube bound back to the root cube) through the final `K1` assembly, given the already
radius-matched unit-cube bound `hfin`. -/
theorem aux_fscc_holNeuH_hSmall_micro_finish {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Dv Mxv C t lam1 : ℝ) (hC : 0 < C) (hDvt0 : 0 ≤ (1 + Dv) ^ t)
    (a1 : PositiveCoefficient (unitNeumannCube d))
    (v1 : meanZeroSobolevGraph (unitNeumannCube d))
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (Kmac1 Kf rad : ℝ) (hrad : 0 < rad)
    (hKmac1bound : Kmac1 ≤ (r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹)
    (x x1 : SpatialCoordinates d)
    (hTx1 : cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x1 = x)
    (K1 : ℝ)
    (hK1def : K1 = r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
      ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv))
    (hfin : localGradientEnergy a1
        (s := Metric.ball x1 (rad / r) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) ≤
      C * ((1 + Dv) ^ t * Kmac1 + Mxv⁻¹⁻¹ * (r ^ 2 * Kf) ^ 2) * (2 * rad / r) ^ t)
    (henergyid : ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
      localGradientEnergy a1
          (s := Metric.ball x rho ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) =
        r ^ ((2 : ℝ) - (d : ℝ)) *
          localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
            (s := Metric.ball (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) (r * rho) ∩
              (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (centeredCube z r hr)))) :
    localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
      K1 * Kf ^ 2 * rad ^ t := by
  have hidr := henergyid x1 (rad / r) (by positivity)
  have hSet4 : Metric.ball (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x1) (r * (rad / r)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hTx1, show r * (rad / r) = rad by field_simp]
  have heq4 := aux_prop_growth_energy_assembly_lge_congr
    (cutoffPositiveCoefficient model H om J z hr)
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    hSet4 (sobolevGradient (v : SobolevData (centeredCube z r hr)))
  rw [heq4] at hidr
  rw [hidr] at hfin
  rw [inv_inv] at hfin
  have hr2d : (0 : ℝ) < r ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos hr _
  have hcast : r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]; norm_num
  have hfin2 : localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
      (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
      r ^ ((d : ℝ) - 2) * (C * ((1 + Dv) ^ t * Kmac1 + Mxv * (r ^ 2 * Kf) ^ 2) *
        (2 * rad / r) ^ t) := by
    have := mul_le_mul_of_nonneg_left hfin hr2d.le
    rwa [← mul_assoc, hcast, one_mul] at this
  refine hfin2.trans ?_
  have hrw : (2 * rad / r) ^ t = ((2 : ℝ) / r) ^ t * rad ^ t := by
    rw [show (2 * rad / r : ℝ) = (2 / r) * rad by ring]
    exact Real.mul_rpow (by positivity) hrad.le
  rw [hrw]
  have hbound1 : (1 + Dv) ^ t * Kmac1 ≤ (1 + Dv) ^ t * ((r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹) :=
    mul_le_mul_of_nonneg_left hKmac1bound hDvt0
  have hstep : C * ((1 + Dv) ^ t * Kmac1 + Mxv * (r ^ 2 * Kf) ^ 2) ≤
      C * (r ^ 4 * Kf ^ 2 * ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hrhs_eq : r ^ 4 * Kf ^ 2 * ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv) =
        (1 + Dv) ^ t * ((r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹) + Mxv * (r ^ 2 * Kf) ^ 2 := by ring
    rw [hrhs_eq]
    exact add_le_add hbound1 (le_refl _)
  calc r ^ ((d : ℝ) - 2) *
        (C * ((1 + Dv) ^ t * Kmac1 + Mxv * (r ^ 2 * Kf) ^ 2) * (((2 : ℝ) / r) ^ t * rad ^ t))
      ≤ r ^ ((d : ℝ) - 2) *
        (C * (r ^ 4 * Kf ^ 2 * ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv)) *
          (((2 : ℝ) / r) ^ t * rad ^ t)) := by
        gcongr
    _ = K1 * Kf ^ 2 * rad ^ t := by
        rw [hK1def]
        have hr42 : r ^ ((d : ℝ) - 2) * r ^ 4 = r ^ ((d : ℝ) + 2) := by
          rw [← Real.rpow_natCast r 4, ← Real.rpow_add hr]
          congr 1
          push_cast
          ring
        rw [← hr42]
        ring

/-- Global-to-unit-cube energy identity used by `aux_fscc_holNeuH_hSmall_energy`: the whole-cube
`sobolevCoefficientForm` on `Q = centeredCube z r hr` equals the rescaled whole-cube energy on the
unit cube, via the transport identity `henergyid` evaluated at the preimage point `x1` and radius
`1` (so both balls cover their whole domain). Split out purely for heartbeat budget. -/
theorem aux_fscc_holNeuH_hSmall_global {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a1 : PositiveCoefficient (unitNeumannCube d))
    (v1 : meanZeroSobolevGraph (unitNeumannCube d))
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (x x1 : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hx1 : x1 ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (hTx1 : cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x1 = x)
    (Kmac1 : ℝ)
    (hKmac1def : Kmac1 = sobolevCoefficientForm a1
      (v1 : SobolevData (unitNeumannCube d)) (v1 : SobolevData (unitNeumannCube d)))
    (henergyid : ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
      localGradientEnergy a1
          (s := Metric.ball x rho ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) =
        r ^ ((2 : ℝ) - (d : ℝ)) *
          localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
            (s := Metric.ball (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) (r * rho) ∩
              (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (centeredCube z r hr)))) :
    sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
      (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) =
      r ^ ((d : ℝ) - 2) * Kmac1 := by
  have hcastinv : r ^ ((2 : ℝ) - (d : ℝ)) * r ^ ((d : ℝ) - 2) = 1 := by
    rw [← Real.rpow_add hr]; norm_num
  have hcover1 : Metric.ball x1 1 ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    apply Set.inter_eq_self_of_subset_right
    intro y hy
    have h1 : dist x1 (fun _ : Fin d => (1/2:ℝ)) < 1 / 2 := hx1
    have h2 : dist y (fun _ : Fin d => (1/2:ℝ)) < 1 / 2 := hy
    show dist y x1 < 1
    calc dist y x1 ≤ dist y (fun _ : Fin d => (1/2:ℝ)) + dist (fun _ : Fin d => (1/2:ℝ)) x1 := dist_triangle _ _ _
      _ = dist y (fun _ : Fin d => (1/2:ℝ)) + dist x1 (fun _ : Fin d => (1/2:ℝ)) := by rw [dist_comm (fun _ : Fin d => (1/2:ℝ)) x1]
      _ < 1 / 2 + 1 / 2 := add_lt_add h2 h1
      _ = 1 := by ring
  have hcoverQ : Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply Set.inter_eq_self_of_subset_right
    intro y hy
    have h1 : dist x z < r / 2 := hx
    have h2 : dist y z < r / 2 := hy
    show dist y x < r
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ = dist y z + dist x z := by rw [dist_comm z x]
      _ < r / 2 + r / 2 := add_lt_add h2 h1
      _ = r := by ring
  have hid := henergyid x1 1 one_pos
  have hSet2 : Metric.ball (cubeDilation z (fun _ : Fin d => (1/2:ℝ)) r x1) (r * 1) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hTx1, show r * (1 : ℝ) = r by ring]; exact hcoverQ
  have heq1 := aux_prop_growth_energy_assembly_lge_congr a1
    (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
    (unitNeumannCube d).isOpen.measurableSet hcover1
    (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
  have heq2 := aux_prop_growth_energy_assembly_lge_congr
    (cutoffPositiveCoefficient model H om J z hr)
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    (centeredCube z r hr).isOpen.measurableSet hSet2
    (sobolevGradient (v : SobolevData (centeredCube z r hr)))
  rw [heq1, heq2] at hid
  rw [localGradientEnergy_domain_eq_sobolevCoefficientForm,
    localGradientEnergy_domain_eq_sobolevCoefficientForm] at hid
  calc sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
        (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))
      = 1 * sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
        (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) :=
        (one_mul _).symm
    _ = (r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - (d : ℝ))) *
          sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) := by
        rw [mul_comm (r ^ ((d : ℝ) - 2)) (r ^ ((2 : ℝ) - (d : ℝ))), hcastinv]
    _ = r ^ ((d : ℝ) - 2) * (r ^ ((2 : ℝ) - (d : ℝ)) *
          sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) :=
        mul_assoc _ _ _
    _ = r ^ ((d : ℝ) - 2) * Kmac1 := by rw [← hid, hKmac1def]

/-- The `rad > r/2` (large-radius) branch of `aux_fscc_holNeuH_hSmall_energy`: bound the
ball-energy trivially by the whole-cube energy (`localGradientEnergy_le`), then bound the
whole-cube energy via `hglobal` + `hKmac1bound`, and absorb the resulting constant into `K1 + K2`
using `rad > r/2` to make `((2:ℝ)/r)^t * rad^t ≥ 1`. Split out purely for heartbeat budget. -/
theorem aux_fscc_holNeuH_hSmall_large_finish {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (t : ℝ) (ht0 : 0 ≤ t)
    (Pc lam1 : ℝ) (hlam1pos : 0 < lam1)
    (K1 K2 Kmac1 Kf rad : ℝ) (hK10 : 0 ≤ K1)
    (hK2def : K2 = r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * ((2 : ℝ) / r) ^ t)
    (hKmac1bound : Kmac1 ≤ (r ^ 2 * Kf) ^ 2 * Pc ^ 2 * lam1⁻¹)
    (hglobal : sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
      (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) =
      r ^ ((d : ℝ) - 2) * Kmac1)
    (x : SpatialCoordinates d) (hrad : 0 < rad) (hradr2 : r / 2 < rad) :
    localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
      (K1 + K2) * Kf ^ 2 * rad ^ t := by
  have hr42 : r ^ ((d : ℝ) - 2) * r ^ 4 = r ^ ((d : ℝ) + 2) := by
    rw [← Real.rpow_natCast r 4, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hglobalbound : sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
      (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) ≤
      r ^ ((d : ℝ) + 2) * Kf ^ 2 * Pc ^ 2 * lam1⁻¹ := by
    rw [hglobal]
    have h1 : r ^ ((d : ℝ) - 2) * Kmac1 ≤
        r ^ ((d : ℝ) - 2) * ((r ^ 2 * Kf) ^ 2 * Pc ^ 2 * lam1⁻¹) :=
      mul_le_mul_of_nonneg_left hKmac1bound (Real.rpow_nonneg hr.le _)
    refine h1.trans (le_of_eq ?_)
    have : (r ^ 2 * Kf) ^ 2 = r ^ 4 * Kf ^ 2 := by ring
    rw [this, ← hr42]
    ring
  have hmono : localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
      (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
      sobolevCoefficientForm (cutoffPositiveCoefficient model H om J z hr)
        (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) :=
    localGradientEnergy_le _ _ _
  refine hmono.trans (hglobalbound.trans ?_)
  have hradpow : (1 : ℝ) ≤ ((2 : ℝ) / r) ^ t * rad ^ t := by
    have h1 : (r / 2) ^ t ≤ rad ^ t := Real.rpow_le_rpow (by positivity) hradr2.le ht0
    have h3 : ((2 : ℝ) / r) ^ t * (r / 2) ^ t = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity),
        show (2 : ℝ) / r * (r / 2) = 1 by field_simp]
      exact Real.one_rpow t
    calc (1 : ℝ) = ((2 : ℝ) / r) ^ t * (r / 2) ^ t := h3.symm
      _ ≤ ((2 : ℝ) / r) ^ t * rad ^ t := by gcongr
  rw [hK2def]
  have hK10' : (0 : ℝ) ≤ K1 * Kf ^ 2 * rad ^ t :=
    mul_nonneg (mul_nonneg hK10 (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le t)
  have hXnn : (0 : ℝ) ≤ r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * Kf ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hradpow hXnn
  calc r ^ ((d : ℝ) + 2) * Kf ^ 2 * Pc ^ 2 * lam1⁻¹
      = r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * Kf ^ 2 * 1 := by ring
    _ ≤ r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * Kf ^ 2 * (((2 : ℝ) / r) ^ t * rad ^ t) := hmul
    _ ≤ K1 * Kf ^ 2 * rad ^ t +
          r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * Kf ^ 2 * (((2 : ℝ) / r) ^ t * rad ^ t) :=
        le_add_of_nonneg_left hK10'
    _ = (K1 + r ^ ((d : ℝ) + 2) * Pc ^ 2 * lam1⁻¹ * ((2 : ℝ) / r) ^ t) * Kf ^ 2 * rad ^ t := by ring

/-- Opaque top-level stand-in for the `ell` scale bound inside `rem_resolved_microscopic`'s
`hbig` hypothesis shape. Pulled out of the `let`-chain (used verbatim, three times, by
`aux_fscc_holNeuH_hSmall_C0` / `aux_fscc_holNeuH_holNeuH_hSmall_final` /
`aux_fscc_holNeuH_holNeuH_hSmall`) purely so that repeated `isDefEq`/`whnf` checks between these
three declarations compare a small opaque application instead of re-copying/re-reducing the same
formula at every call site (heartbeat budget: this alone was timing out `aux_fscc_holNeuH_
holNeuH_hSmall`'s own elaboration and its call site inside `holNeu_H`). -/
noncomputable def aux_fscc_holNeuH_ell (c eps DN : ℝ) : ℝ := c * eps / (1 + DN)

/-- Opaque top-level stand-in for the `gamma` local weighted-gradient-energy functional inside
the same `hbig` hypothesis shape, for the same reason as `aux_fscc_holNeuH_ell`. -/
noncomputable def aux_fscc_holNeuH_gamma {d : ℕ} (A : C(SpatialCoordinates d, ℝ))
    (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) (rr : ℝ) : ℝ :=
  ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rr / 2} ∩
    (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2



theorem aux_fscc_holNeuH_hSmall_energy {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hrJ : (3 : ℝ) ^ J * r ≤ 1)
    (Mxv Dv : ℝ) (hMx : 0 < Mxv) (hDv : 0 ≤ Dv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient model H om J x ∧ cutoffCoefficient model H om J x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient model H om J x) - Real.log (cutoffCoefficient model H om J y)| ≤
        Dv * (3 : ℝ) ^ J * dist x y)
    (C c p1 t1 : ℝ) (hC : 0 < C)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) (rr : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rr / 2} ∩
          (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ ((d : ℝ) - 1 / 2) * eps ^ (t1 - ((d : ℝ) - 1 / 2)) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - ((d : ℝ) - 1 / 2))) * rr ^ ((d : ℝ) - 1 / 2))) :
    0 ≤ r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
          ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * P.C ^ 2 *
            (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ + Mxv) +
        r ^ ((d : ℝ) + 2) * P.C ^ 2 *
          (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ *
          ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) ∧
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient model H om J z hr) F v →
        ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
          localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
            (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
                ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * P.C ^ 2 *
                  (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ + Mxv) +
              r ^ ((d : ℝ) + 2) * P.C ^ 2 *
                (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ *
                ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2)) * Kf ^ 2 * rad ^ ((d : ℝ) - 1 / 2) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set t : ℝ := (d : ℝ) - 1 / 2 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; linarith
  obtain ⟨a1, ha1, -, hNeuTransport⟩ := lem_as_regularity_affine_transport d model H om J z r hr
  obtain ⟨A1, hA1ae, hAK, hlog1⟩ := aux_prop_growth_energy_assembly_unit_coeff model H om J z r hr
    Dv Mxv 1 hDv (by simpa using hrJ) henv hlip
  have haA1 : (a1 : PositiveCoefficient (unitNeumannCube d)).val
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A1 := hA1ae a1 ha1
  set lam1 : ℝ := E.lam (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos a1
    (fun _ : Fin d => (1 / 2 : ℝ)) 1 1 1 with hlam1def
  have hlamEq : lam1 = E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1 :=
    (E.lam_dilation z r hr (cutoffPositiveCoefficient model H om J z hr)
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos a1 ha1 1 1).symm
  clear ha1 hA1ae
  have hMxv0 : 0 ≤ Mxv := hMx.le
  have hMxvi0 : 0 < Mxv⁻¹ := inv_pos.mpr hMx
  have hlam1pos : 0 < lam1 := E.lam_pos _ _ _ _ _ _ _ _
  have hlam1i0 : 0 ≤ lam1⁻¹ := (inv_pos.mpr hlam1pos).le
  have h2rt0 : 0 ≤ ((2 : ℝ) / r) ^ t := Real.rpow_nonneg (by positivity) _
  have hDvt0 : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
  obtain ⟨K1, hK1def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
      ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * P.C ^ 2 * lam1⁻¹ * ((2 : ℝ) / r) ^ t :=
    ⟨_, rfl⟩
  have hrdpos : 0 ≤ r ^ ((d : ℝ) + 2) := Real.rpow_nonneg hr.le _
  have hPC2 : 0 ≤ P.C ^ 2 := sq_nonneg _
  have hK10 : 0 ≤ K1 := by
    rw [hK1def]
    have hinner : 0 ≤ (1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv :=
      add_nonneg (mul_nonneg (mul_nonneg hDvt0 hPC2) hlam1i0) hMxv0
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hC.le) h2rt0) hinner
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hPC2) hlam1i0) h2rt0
  rw [← hlamEq, ← hK1def, ← hK2def]
  refine ⟨add_nonneg hK10 hK20, ?_⟩
  intro F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradr
  obtain ⟨F1, v1, hF1eq, hF1m, hF1b, hF1mean, hsolve1, hv1val, hv1grad, henergyid⟩ :=
    hNeuTransport F Kf hKf hFm hFb hmean v hsol
  clear hNeuTransport hv1val
  obtain ⟨Kmac1, hKmac1def⟩ : ∃ K : ℝ, K = sobolevCoefficientForm a1
      (v1 : SobolevData (unitNeumannCube d)) (v1 : SobolevData (unitNeumannCube d)) :=
    ⟨_, rfl⟩
  have hKmac1nonneg : 0 ≤ Kmac1 := by
    rw [hKmac1def]; exact sobolevCoefficientForm_nonneg a1 _
  have hKmac1bound : Kmac1 ≤ (r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹ := by
    rw [hKmac1def, hlam1def]
    exact aux_cor_neumann_source_global_energy_ae hd E P a1 F1 hF1m (r ^ 2 * Kf)
      (by positivity) hF1b v1 hsolve1
  -- x1 : the preimage of x on the unit cube
  obtain ⟨x1, hx1def⟩ : ∃ y : SpatialCoordinates d, y = cubeDilation (fun _ : Fin d => (1/2:ℝ)) z r⁻¹ x := ⟨_, rfl⟩
  have hTx1 : cubeDilation z (fun _ : Fin d => (1/2:ℝ)) r x1 = x := by
    rw [hx1def]; exact aux_prop_growth_energy_assembly_dilation_inv z (fun _ : Fin d => (1/2:ℝ)) hr x
  have hx1 : x1 ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    have hpre := cubeDilation_preimage_centeredCube z (fun _ : Fin d => (1/2:ℝ)) hr one_pos
    change x1 ∈ (centeredCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d))
    rw [← hpre, Set.mem_preimage, hTx1]
    exact hx
  -- global-scale instance of the transport energy identity
  have hglobal := aux_fscc_holNeuH_hSmall_global model H om J z r hr a1 v1 v x x1 hx hx1 hTx1
    Kmac1 hKmac1def henergyid
  by_cases hcase : rad ≤ r / 2
  · -- micro case: transport, clamp, apply rem_resolved_microscopic's Neumann conjunct
    obtain ⟨f1, hf1m, hf1b, hf1eq⟩ := aux_prop_growth_energy_assembly_clamp
      (unitNeumannCube d : Set (SpatialCoordinates d)) F1 hF1m (r ^ 2 * Kf) (by positivity) hF1b
    have hsolve1' : SolvesNeumann a1 f1 v1 :=
      aux_fscc_holNeuH_solvesNeumann_congr hf1eq hsolve1
    have hDNnn : (0 : ℝ) ≤ Dv := hDv
    have h1DN : (0 : ℝ) < Mxv⁻¹ := hMxvi0
    have hf1b' : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f1 y| ≤ r ^ 2 * Kf :=
      fun y _ => hf1b y
    have hcl := hbig 1 one_pos le_rfl a1 A1 haA1 Dv Mxv⁻¹ Mxv hDNnn h1DN hAK
      (by simpa using hlog1) f1 hf1m (r ^ 2 * Kf) (by positivity) hf1b'
    have hclN := (hcl v1 hsolve1').2
    clear hbig hcl
    have hprecond : ∀ x1' ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x1' i| < C * 1 / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
          A1 y * ∑ i : Fin d, ((v1 : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
          Kmac1 * (1 : ℝ) ^ t1 := by
      intro x1' hx1'
      simp only [mul_one, Real.one_rpow]
      rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
        x1' (by positivity : (0:ℝ) < C)]
      calc localGradientEnergy a1
            (s := Metric.ball x1' (C / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
          ≤ (weightedGradientForm (a1 : PositiveCoefficient (unitNeumannCube d)).val)
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) :=
            localGradientEnergy_le a1 _ _
        _ = Kmac1 := hKmac1def ▸ rfl
    have hr' : (0 : ℝ) < 2 * rad / r := by positivity
    have hr'1 : 2 * rad / r ≤ 1 := by
      rw [div_le_one hr]; linarith
    have hfin := hclN Kmac1 hKmac1nonneg x1 hx1 (hprecond x1 hx1) (2 * rad / r) hr' hr'1
    clear hclN hprecond hr'1 hf1b' hsolve1' hf1eq hf1b hf1m f1 hDNnn h1DN
    beta_reduce at hfin
    rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
      x1 (show (0:ℝ) < 2 * rad / r from hr')] at hfin
    clear hr'
    simp only [Real.one_rpow, mul_one] at hfin
    have hballeq : Metric.ball x1 (2 * rad / r / 2) ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)) =
        Metric.ball x1 (rad / r) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
      have : (2 * rad / r / 2 : ℝ) = rad / r := by ring
      rw [this]
    have heq3 := aux_prop_growth_energy_assembly_lge_congr a1
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      hballeq (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
    rw [heq3] at hfin
    clear heq3 hballeq A1 haA1 hAK hlog1 hx1 hglobal
    clear c p1 t1 ht0 hd2 hd0 henv hlip hMx hrJ
    clear hMxv0 hMxvi0 hlam1pos hlam1i0 h2rt0 hK10 hrdpos hPC2 hK2def
    clear hF1eq hF1m hF1b hF1mean hsolve1 hv1grad
    clear hKf hFm hFb hmean hsol hx hradr F
    clear hKmac1def hKmac1nonneg hx1def hcase
    have hK2nn : 0 ≤ K2 * Kf ^ 2 * rad ^ t :=
      mul_nonneg (mul_nonneg hK20 (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le t)
    refine (aux_fscc_holNeuH_hSmall_micro_finish hd E P model H om J z r hr Dv Mxv C t lam1
      hC hDvt0 a1 v1 v Kmac1 Kf rad hrad hKmac1bound x x1 hTx1 K1 hK1def hfin henergyid).trans ?_
    have heq : (K1 + K2) * Kf ^ 2 * rad ^ t = K1 * Kf ^ 2 * rad ^ t + K2 * Kf ^ 2 * rad ^ t := by
      ring
    rw [heq]
    exact le_add_of_nonneg_right hK2nn
  · -- large-radius case: trivial monotonicity against the global energy
    have hradr2 : r / 2 < rad := lt_of_not_ge hcase
    exact aux_fscc_holNeuH_hSmall_large_finish model H om J z r hr v t ht0 P.C lam1 hlam1pos
      K1 K2 Kmac1 Kf rad hK10 hK2def hKmac1bound hglobal x hrad hradr2




theorem aux_fscc_holNeuH_hSmall_holderSeminorm_dist {d : ℕ}
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) (alpha C : ℝ)
    (halpha : 0 < alpha) (hH : IsHolderOn alpha S U)
    (hsemi : holderSeminorm alpha S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤ Real.sqrt d ^ alpha * C * dist x y ^ alpha := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, dist_self]
    rw [Real.zero_rpow halpha.ne']
    simp
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hepos : 0 < e := by
      rw [he, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon
        push_neg at hcon
        exact hxy (funext hcon)
      have hj' : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.2 hj
        positivity
      exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have heα : 0 < e ^ alpha := Real.rpow_pos_of_pos hepos alpha
    have hratio : |U x - U y| / e ^ alpha ≤ holderSeminorm alpha S U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤ C * e ^ alpha := by
      have := (div_le_iff₀ heα).1 (hratio.trans hsemi)
      linarith
    have h2 : e ^ alpha ≤ Real.sqrt d ^ alpha * dist x y ^ alpha := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
      exact Real.rpow_le_rpow hepos.le (aux_lem_finite_source_comparison_cells_euclid_le x y)
        halpha.le
    have hC0 : 0 ≤ C := (aux_lem_finite_source_comparison_cells_holderSeminorm_nonneg _ _ _).trans
      hsemi
    calc |U x - U y| ≤ C * e ^ alpha := h1
      _ ≤ C * (Real.sqrt d ^ alpha * dist x y ^ alpha) := by gcongr
      _ = Real.sqrt d ^ alpha * C * dist x y ^ alpha := by ring



theorem aux_fscc_holNeuH_hSmall_lam_measurable {d : ℕ} (E : in_J d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a1 : PositiveCoefficient (unitNeumannCube d))
    (ha1 : ∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (cutoffPositiveCoefficient model H om J z hr).val
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x))
    (s : ℝ) (q : ℝ≥0∞) :
    E.lam (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos a1 (fun _ : Fin d => (1 / 2 : ℝ)) 1 s q =
      E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r s q :=
  (E.lam_dilation z r hr (cutoffPositiveCoefficient model H om J z hr)
    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos a1 ha1 s q).symm

/-- **The general-cube Campanato oscillation bound for `hSmall`.** Feeds the general
Caccioppoli-Campanato energy bound `hen` (of the exact shape `aux_fscc_holNeuH_hSmall_energy`
produces, `K * Kf^2 * rad^((d:ℝ)-1/2)`) through the deterministic pathwise estimate, the volume
lower bound, and the final algebra step of `prop_growth_holder_micro_campanato`, at the fixed
`alpha := 1/2`, `t := (d:ℝ)-1/2`, `e := 1/2` (so `hexp : 2+t=2*alpha+d+e` holds for every `d`),
and `eps := r` (the energy bound already holds for every `rad ≤ r`, not just below some
wavelength). -/
theorem aux_fscc_holNeuH_hSmall_campanato {d : ℕ} (Cpo : ℝ) (hCpo : 0 ≤ Cpo)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cpo * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) (K Kf : ℝ) (hK0 : 0 ≤ K) (hKf : 0 ≤ Kf)
    (hen : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
        K * Kf ^ 2 * rad ^ ((d : ℝ) - 1 / 2)) :
    ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
      ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube z r hr)).1 y - setAverage
            (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (v : SobolevData (centeredCube z r hr)).1) ^ 2
          ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        ((1 + Cpo) * (Mx + K) * r ^ ((1 / 2 : ℝ) / 2) * Kf) ^ 2 * rad ^ (2 * (1 / 2 : ℝ)) *
          volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro x hx rad hrad hradr
  set u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨(v : SobolevData (centeredCube z r hr)),
      ((mem_meanZeroSobolevGraph_iff (v : SobolevData (centeredCube z r hr))).mp v.property).1⟩
    with hudef
  have huval : (u : SobolevData (centeredCube z r hr)) = (v : SobolevData (centeredCube z r hr)) :=
    rfl
  have hpw := aux_prop_growth_holder_micro_campanato_pathwise Cpo hCpo hPoinc z hr a Mx hMx hlow u
    rad (K * Kf ^ 2 * rad ^ ((d : ℝ) - 1 / 2)) hrad
    (fun c hc => by rw [huval]; exact hen c hc rad hrad hradr) x hx
  rw [huval] at hpw
  have hV : rad ^ d ≤
      volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    aux_prop_growth_holder_micro_campanato_volume_ge z x hrad (by linarith) hx
  have hres := aux_prop_growth_holder_micro_campanato_final_alg d Cpo Mx K Kf rad r
    (volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))))
    ((d : ℝ) - 1 / 2) (1 / 2) (1 / 2) _
    hCpo hMx hrad hradr (by norm_num) (by push_cast; ring) hV hpw
  rwa [abs_of_nonneg hK0] at hres

/-- **Campanato oscillation decay gives the plain two-point Hölder bound, general cube.**
Combines `CampanatoInput.holder_of_campanato` (needs only `holderSeminorm`, not `cAlphaNorm`)
with `aux_fscc_holNeuH_hSmall_holderSeminorm_dist`. -/
theorem aux_fscc_holNeuH_hSmall_holder_of_campanato {d : ℕ} (Cp : CampanatoInput d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) (Kc Kf : ℝ) (hKc : 0 ≤ Kc) (hKf : 0 ≤ Kf)
    (hcamp : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
      ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube z r hr)).1 y - setAverage
            (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (v : SobolevData (centeredCube z r hr)).1) ^ 2
          ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (Kc * Kf) ^ 2 * rad ^ (2 * (1 / 2 : ℝ)) *
          volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          |U x - U y| ≤ Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * (Kc * Kf)) *
            dist x y ^ (1 / 2 : ℝ) := by
  have hKK : 0 ≤ Kc * Kf := mul_nonneg hKc hKf
  obtain ⟨U, hUc, hUae, hUH, hUsem⟩ :=
    Cp.holder_of_campanato (1 / 2) (by norm_num) (by norm_num) z r hr hr1
      (v : SobolevData (centeredCube z r hr)).1 (Kc * Kf) hKK hcamp
  exact ⟨U, hUc, hUae,
    aux_fscc_holNeuH_hSmall_holderSeminorm_dist _ U (1 / 2) _ (by norm_num) hUH hUsem⟩

/-- **Pointwise `hSmall` assembly.** Combines a Caccioppoli-Campanato energy bound of the exact
shape `aux_fscc_holNeuH_hSmall_energy` produces (taken here as a generic hypothesis `hEn`, so
this lemma does not itself need `rem_resolved_microscopic`'s constant), the scaled Poincaré
input, and Campanato's criterion into the principal's mean-zero Neumann Hölder clause for one
fixed `(z, r, J, om)`. -/
theorem aux_fscc_holNeuH_hSmall_pointwise {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (Mxv : ℝ) (hMx : 0 < Mxv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient model H om J x ∧ cutoffCoefficient model H om J x ≤ Mxv)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hEn : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        SolvesNeumann (cutoffPositiveCoefficient model H om J z hr) F v →
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
        localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
            (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
          K * Kf ^ 2 * rad ^ ((d : ℝ) - 1 / 2))
    (Cpo : ℝ) (hCpo : 0 ≤ Cpo)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cpo * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2) :
    aux_lem_finite_source_comparison_cells_holNeu d z r hr
      (cutoffPositiveCoefficient model H om J z hr) (1 / 2)
      (Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * ((1 + Cpo) * (Mxv + K) *
        r ^ ((1 / 2 : ℝ) / 2)))) := by
  have hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mxv * (cutoffPositiveCoefficient model H om J z hr).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae model H om J z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hymem
    rw [hy]
    have h1 := (henv y (centeredCube_subset_closedCube z hr hymem)).1
    have h2 : Mxv * Mxv⁻¹ ≤ Mxv * cutoffCoefficient model H om J y :=
      mul_le_mul_of_nonneg_left h1 hMx.le
    rwa [mul_inv_cancel₀ hMx.ne'] at h2
  intro F Kf hKf hFm hFb hFint u hsol
  have hcamp := aux_fscc_holNeuH_hSmall_campanato Cpo hCpo hPoinc z hr
    (cutoffPositiveCoefficient model H om J z hr) Mxv hMx.le hlow u K Kf hK0 hKf
    (fun x hx rad hrad hradr => hEn F Kf hKf hFm.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb)
      hFint u hsol x hx rad hrad hradr)
  obtain ⟨U, hUc, hUae, hUdist⟩ := aux_fscc_holNeuH_hSmall_holder_of_campanato Cp z hr hr1 u
    ((1 + Cpo) * (Mxv + K) * r ^ ((1 / 2 : ℝ) / 2)) Kf (by positivity) hKf hcamp
  have heq : Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) *
      ((1 + Cpo) * (Mxv + K) * r ^ ((1 / 2 : ℝ) / 2) * Kf)) =
      Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * ((1 + Cpo) * (Mxv + K) *
        r ^ ((1 / 2 : ℝ) / 2))) * Kf := by ring
  rw [heq] at hUdist
  exact ⟨U, hUc.continuousOn, hUae, hUdist⟩

/-- Isolated `rem_resolved_microscopic` call/destructure (`d, hd, W` only — no other context),
returning its Neumann conjunct with `t` already fixed to `(d:ℝ)-1/2`. Empirically, `obtain`-
destructuring this large an existential is only cheap with a small ambient local context (this
is exactly the call `aux_fscc_holNeuH_hSmall_energy` used to make internally, before it was
hoisted to a parameter); done inline inside `aux_fscc_holNeuH_holNeuH_hSmall` (which by
construction already carries `hReExt`/`hLamMom` in context) it alone exceeds 200000 heartbeats,
even though passing its *result* as a parameter elsewhere is cheap. -/
theorem aux_fscc_holNeuH_hSmall_C0 (d : ℕ) (hd : 2 ≤ d) (W : SmallPerturbationInput d) :
    ∃ C c p1 t1 : ℝ, 0 < C ∧
      (let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := aux_fscc_holNeuH_ell c eps DN
      let gamma := aux_fscc_holNeuH_gamma A
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ ((d : ℝ) - 1 / 2) * eps ^ (t1 - ((d : ℝ) - 1 / 2)) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - ((d : ℝ) - 1 / 2))) * rr ^ ((d : ℝ) - 1 / 2))) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set t : ℝ := (d : ℝ) - 1 / 2 with htdef
  have ht : (d : ℝ) - 1 < t := by rw [htdef]; linarith
  have htd : t < (d : ℝ) := by rw [htdef]; linarith
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  set t1 : ℝ := (t + (d : ℝ)) / 2 with ht1def
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1def]; linarith
  obtain ⟨C, c, hC, hc, hc16, hbig, -⟩ :=
    rem_resolved_microscopic d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  refine ⟨C, c, p1, t1, hC, ?_⟩
  intro q1 eps heps heps1 a A hA DN mN MN hDN hmN hbnd hlp f hf Kf hKf hfb
  exact (hbig eps heps heps1 a A hA DN mN MN hDN hmN hbnd hlp f hf Kf hKf hfb).2.1

/-- Thin re-export of `aux_prop_growth_energy_assembly_root_extremes` at the fixed exponent
`q := 2*((d:ℝ)-1/2)` this file always uses, isolated in its own declaration purely so the main
`holNeu_H` theorem does not re-elaborate this large existential inline (heartbeat budget). -/
theorem aux_fscc_holNeuH_root_extremes_at (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ cd / (2 * (2 * ((d : ℝ) - 1 / 2))) →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ),
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x ∧
                cutoffCoefficient M H om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x) -
                  Real.log (cutoffCoefficient M H om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hext⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd (2 * ((d : ℝ) - 1 / 2)) (by linarith)
  refine ⟨cd, hcd, ?_⟩
  intro M H hH hdelta z r hr hr1
  obtain ⟨D, Mx, CE, hCE0, hDMnn, hReAE, hReMem, -, -⟩ := hext M H hH hdelta z r hr hr1
  exact ⟨D, Mx, hDMnn, hReAE, hReMem⟩

/-- Thin re-export of `lane4_lambda_inv_moments` at the fixed `s := 1/8`, `p := 2` this file
always uses, isolated purely for heartbeat budget (see `aux_fscc_holNeuH_root_extremes_at`);
only `MemLp` is kept (no explicit `eLpNorm` bound), since `hSmall` only ever needs finiteness
of first moments, obtained via `(eLpNorm _ _).toReal` rather than a tracked numeric bound. -/
theorem aux_fscc_holNeuH_lambda_inv_at (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → M.delta ≤ delta0 →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
              (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
  obtain ⟨delta0, hdelta0, hlam⟩ := aux_lane4_lambda_inv_moments_adm d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  refine ⟨delta0 2, hdelta0 2 (by norm_num), ?_⟩
  intro M Rm H hH z r hr hr1 hdelta N
  obtain ⟨Cbound, hLamMem, -⟩ := hlam M Rm H hH z r hr hr1 2 (by norm_num) hdelta
  exact hLamMem N

/-- Domination of `hSmall`'s energy-derived Hölder constant, replacing the `s = 1` inverse
scale by the (larger, and moment-controlled at `s = 1/8`) `Lam18` via `E.lam_mono`. Isolated for
heartbeat budget; pure algebra given `Lam1 ≤ Lam18`. -/
theorem aux_fscc_holNeuH_hSmall_K_mono {d : ℕ} (r C Dv Mxv PC Lam1 Lam18 : ℝ)
    (hr : 0 < r) (hDv : 0 ≤ Dv) (hMxv : 0 ≤ Mxv) (hC : 0 ≤ C) (hPC : 0 ≤ PC)
    (hLam1 : 0 ≤ Lam1) (hLamLe : Lam1 ≤ Lam18) :
    r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
          ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * PC ^ 2 * Lam1 + Mxv) +
        r ^ ((d : ℝ) + 2) * PC ^ 2 * Lam1 * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) ≤
      r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
          ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * PC ^ 2 * Lam18 + Mxv) +
        r ^ ((d : ℝ) + 2) * PC ^ 2 * Lam18 * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) := by
  have h1 : 0 ≤ (1 + Dv) ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ r ^ ((d : ℝ) + 2) := Real.rpow_nonneg hr.le _
  have h3 : 0 ≤ ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg (by positivity) _
  gcongr

/-- **`hSmall`'s moment/measurability step, isolated for heartbeat budget** (the combined
declaration timed out even after extracting `rem_resolved_microscopic`/`root_extremes`/`lambda_
inv_moments`'s own calls — this is genuinely ~90 lines of independent work). Given the root-
independent envelope/log-Lipschitz data `Dre, Mxre` (moments at `q = 2*t`) and the `s = 1/8`
inverse-scale data `Lam18` (moments at `2`), produces a random constant `Ks` with first moments
via the power rule (`MemLp.norm_rpow_div`) and Cauchy-Schwarz
(`aux_rem_resolved_microscopic_product_lq_bound`) alone — no explicit numeric bound is tracked,
`Cs` is just the finite max of `(eLpNorm (Ks J) 1).toReal` over the finitely many `J < m`. -/
theorem aux_fscc_holNeuH_holNeuH_hSmall_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (r C PCsq t Kscale : ℝ) (hr : 0 < r) (ht0 : 0 < t) (ht1 : (1 : ℝ) / 2 ≤ t)
    (m : ℤ) (hm : 0 < m)
    (Dre Mxre Lam18 : ℕ → BilateralField d → ℝ)
    (hDMnn : ∀ N om, 0 ≤ Dre N om ∧ 0 ≤ Mxre N om)
    (hReMem : ∀ N, MemLp (Dre N) (ENNReal.ofReal (2 * t)) (chaosSampleLaw model).toMeasure ∧
      MemLp (Mxre N) (ENNReal.ofReal (2 * t)) (chaosSampleLaw model).toMeasure)
    (hLamMemAll : ∀ N, MemLp (Lam18 N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure) :
    ∃ Ks : ℕ → BilateralField d → ℝ, ∃ Cs : ℝ,
      (∀ J, MemLp (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cs) ∧
      (∀ J : ℕ, (J : ℤ) < m → Ks J = fun om => Kscale *
        (Mxre J om + (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
            ((1 + Dre J om) ^ t * PCsq * Lam18 J om + Mxre J om) +
          r ^ ((d : ℝ) + 2) * PCsq * Lam18 J om * ((2 : ℝ) / r) ^ t))) := by
  set Kenergy : ℕ → BilateralField d → ℝ := fun J om =>
    r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t * ((1 + Dre J om) ^ t * PCsq * Lam18 J om +
        Mxre J om) +
      r ^ ((d : ℝ) + 2) * PCsq * Lam18 J om * ((2 : ℝ) / r) ^ t with hKenergydef
  set Ks0 : ℕ → BilateralField d → ℝ := fun J om => Kscale * (Mxre J om + Kenergy J om)
    with hKs0def
  set Ks : ℕ → BilateralField d → ℝ := fun J om => if (J : ℤ) < m then Ks0 J om else 0
    with hKsdef
  have hle1 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (2 * t) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hle2 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (2 : ℝ) :=
    ENNReal.ofReal_le_ofReal (by norm_num)
  have hDpow : ∀ J, MemLp (fun om => (1 + Dre J om) ^ t) (ENNReal.ofReal 2)
      (chaosSampleLaw model).toMeasure := by
    intro J
    have h1 : MemLp (fun om => 1 + Dre J om) (ENNReal.ofReal (2 * t))
        (chaosSampleLaw model).toMeasure := (memLp_const (1 : ℝ)).add (hReMem J).1
    have h2 := h1.norm_rpow_div (ENNReal.ofReal t)
    have heq : ENNReal.ofReal (2 * t) / ENNReal.ofReal t = ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_div_of_pos ht0]; congr 1; field_simp
    rw [heq] at h2
    have heq2 : (ENNReal.ofReal t).toReal = t := ENNReal.toReal_ofReal ht0.le
    rw [heq2] at h2
    have heqf : (fun om => ‖1 + Dre J om‖ ^ t) = (fun om => (1 + Dre J om) ^ t) := by
      funext om
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hDMnn J om).1] : (0 : ℝ) ≤ 1 + Dre J om)]
    rwa [heqf] at h2
  have hProd : ∀ J, MemLp (fun om => (1 + Dre J om) ^ t * Lam18 J om) (ENNReal.ofReal 1)
      (chaosSampleLaw model).toMeasure := by
    intro J
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw model).toMeasure 1 2
      (by norm_num) (by norm_num) _ _ (hDpow J) (hLamMemAll J)
    exact ⟨(hDpow J).1.mul (hLamMemAll J).1,
      hb.trans_lt (ENNReal.mul_lt_top (hDpow J).eLpNorm_lt_top (hLamMemAll J).eLpNorm_lt_top)⟩
  have hMxmem1 : ∀ J, MemLp (Mxre J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure :=
    fun J => (hReMem J).2.mono_exponent hle1
  have hLam18mem1 : ∀ J, MemLp (Lam18 J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure :=
    fun J => (hLamMemAll J).mono_exponent hle2
  have hKenergymem : ∀ J, MemLp (Kenergy J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
    intro J
    rw [hKenergydef]
    have hsum1 : MemLp (fun om => (1 + Dre J om) ^ t * PCsq * Lam18 J om + Mxre J om)
        (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
      have hp2 := (hProd J).const_mul PCsq
      have heqf : (fun om => PCsq * ((1 + Dre J om) ^ t * Lam18 J om)) =
          (fun om => (1 + Dre J om) ^ t * PCsq * Lam18 J om) := by funext om; ring
      rw [heqf] at hp2
      exact hp2.add (hMxmem1 J)
    have h1 : MemLp (fun om => r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
        ((1 + Dre J om) ^ t * PCsq * Lam18 J om + Mxre J om)) (ENNReal.ofReal 1)
        (chaosSampleLaw model).toMeasure :=
      hsum1.const_mul (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t)
    have h2 : MemLp (fun om => (r ^ ((d : ℝ) + 2) * PCsq * ((2 : ℝ) / r) ^ t) * Lam18 J om)
        (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure :=
      (hLam18mem1 J).const_mul (r ^ ((d : ℝ) + 2) * PCsq * ((2 : ℝ) / r) ^ t)
    have heqf2 : (fun om => (r ^ ((d : ℝ) + 2) * PCsq * ((2 : ℝ) / r) ^ t) * Lam18 J om) =
        (fun om => r ^ ((d : ℝ) + 2) * PCsq * Lam18 J om * ((2 : ℝ) / r) ^ t) := by
      funext om; ring
    rw [heqf2] at h2
    exact h1.add h2
  have hKs0mem : ∀ J, MemLp (Ks0 J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
    intro J
    rw [hKs0def]
    exact ((hMxmem1 J).add (hKenergymem J)).const_mul Kscale
  have hKsmem : ∀ J, MemLp (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
    intro J
    rw [hKsdef]
    by_cases hJm : (J : ℤ) < m
    · simp only [if_pos hJm]; exact hKs0mem J
    · simp only [if_neg hJm]; exact memLp_const 0
  refine ⟨Ks, (Finset.range m.toNat).sup' (Finset.nonempty_range_iff.mpr (by omega))
    (fun J => (eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure).toReal),
    hKsmem, ?_, ?_⟩
  · intro J
    rw [hKsdef]
    by_cases hJm : (J : ℤ) < m
    · have hJlt : J < m.toNat := by omega
      have hfin : eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≠ ⊤ :=
        (hKsmem J).eLpNorm_lt_top.ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (fun J => (eLpNorm (Ks J) (ENNReal.ofReal 1)
          (chaosSampleLaw model).toMeasure).toReal) (Finset.mem_range.mpr hJlt))
    · simp only [if_neg hJm, eLpNorm_zero']
      exact zero_le _
  · intro J hJm
    simp only [hKsdef, if_pos hJm, hKs0def, hKenergydef]

/-- **`hSmall`'s per-`(J,omega)` pointwise assembly, isolated for heartbeat budget** (combining
`aux_fscc_holNeuH_hSmall_energy` + `aux_fscc_holNeuH_hSmall_K_mono` + `aux_fscc_holNeuH_hSmall_
pointwise` inside the caller's already-large local context timed out at `isDefEq`/`whnf`; moved to
its own declaration with a small, fresh context so the same three calls elaborate cheaply). -/
theorem aux_fscc_holNeuH_holNeuH_hSmall_final {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (C c p1 t1 : ℝ) (hC : 0 < C)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := aux_fscc_holNeuH_ell c eps DN
      let gamma := aux_fscc_holNeuH_gamma A
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ ((d : ℝ) - 1 / 2) * eps ^ (t1 - ((d : ℝ) - 1 / 2)) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - ((d : ℝ) - 1 / 2))) * rr ^ ((d : ℝ) - 1 / 2)))
    (Mxv Dv : ℝ) (hMx : 0 < Mxv) (hDv : 0 ≤ Dv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient model H om J x ∧ cutoffCoefficient model H om J x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient model H om J x) - Real.log (cutoffCoefficient model H om J y)| ≤
        Dv * (3 : ℝ) ^ J * dist x y)
    (hrJJ : (3 : ℝ) ^ J * r ≤ 1)
    (Lam18 : ℝ)
    (hLamLe : (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ ≤ Lam18)
    (Cpo : ℝ) (hCpo : 0 ≤ Cpo)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cpo * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2) :
    aux_lem_finite_source_comparison_cells_holNeu d z r hr
      (cutoffPositiveCoefficient model H om J z hr) (1 / 2)
      (Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * (1 + Cpo)) * r ^ ((1 / 2 : ℝ) / 2) *
        (Mxv + (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
            ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * P.C ^ 2 * Lam18 + Mxv) +
          r ^ ((d : ℝ) + 2) * P.C ^ 2 * Lam18 * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2)))) := by
  obtain ⟨hK0, hEn⟩ := aux_fscc_holNeuH_hSmall_energy hd E P model H om J z r hr hrJJ
    Mxv Dv hMx hDv henv hlip C c p1 t1 hC hbig
  have hK'mono := aux_fscc_holNeuH_hSmall_K_mono (d := d) r C Dv Mxv P.C
    (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ Lam18
    hr hDv hMx.le hC.le P.C_pos.le
    (inv_nonneg.mpr (E.lam_pos z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1).le)
    hLamLe
  set Kenergy : ℝ := r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) *
      ((1 + Dv) ^ ((d : ℝ) - 1 / 2) * P.C ^ 2 * Lam18 + Mxv) +
    r ^ ((d : ℝ) + 2) * P.C ^ 2 * Lam18 * ((2 : ℝ) / r) ^ ((d : ℝ) - 1 / 2) with hKenergydef
  have hK'0 : 0 ≤ Kenergy := by rw [hKenergydef]; exact hK0.trans hK'mono
  have hEn' : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        SolvesNeumann (cutoffPositiveCoefficient model H om J z hr) F v →
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
        localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
            (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
          Kenergy * Kf ^ 2 * rad ^ ((d : ℝ) - 1 / 2) := by
    intro F Kf hKf hFm hFb hFint v hsol x hx rad hrad hradr
    have hstep := hEn F Kf hKf hFm hFb hFint v hsol x hx rad hrad hradr
    rw [hKenergydef]
    calc _ ≤ _ := hstep
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hrad.le _)
          exact mul_le_mul_of_nonneg_right hK'mono (sq_nonneg Kf)
  have hHolNeu := aux_fscc_holNeuH_hSmall_pointwise hd E P Cp model H om J z r hr hr1
    Mxv hMx henv Kenergy hK'0 hEn' Cpo hCpo hPoinc
  have heq : Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * ((1 + Cpo) * (Mxv + Kenergy) *
      r ^ ((1 / 2 : ℝ) / 2))) =
      Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * (1 + Cpo)) * r ^ ((1 / 2 : ℝ) / 2) *
        (Mxv + Kenergy) := by ring
  rw [heq] at hHolNeu
  exact hHolNeu

/-- **`hSmall`'s `-j > 0` branch, isolated in its own declaration for heartbeat budget.** Same
proof `aux_fscc_holNeuH_holNeuH_hSmall`'s "case pos" always had; pulled into a fresh top-level
declaration (own 200000-heartbeat budget) since the combined declaration's decl-end `whnf` check
(verifying the whole accumulated proof term against the declared existential) was timing out even
though every individual tactic step is cheap. -/
theorem aux_fscc_holNeuH_holNeuH_hSmall_pos {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredAdmissible model H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ) (hj : r = (3 : ℝ) ^ j)
    (C c p1 t1 : ℝ) (hC : 0 < C)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := aux_fscc_holNeuH_ell c eps DN
      let gamma := aux_fscc_holNeuH_gamma A
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ ((d : ℝ) - 1 / 2) * eps ^ (t1 - ((d : ℝ) - 1 / 2)) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - ((d : ℝ) - 1 / 2))) * rr ^ ((d : ℝ) - 1 / 2)))
    (cdre : ℝ) (hcdre : 0 < cdre)
    (hReExt : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf → M.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))) →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ),
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M Hf om N x ∧
                cutoffCoefficient M Hf om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M Hf om N x) -
                  Real.log (cutoffCoefficient M Hf om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure))
    (hdeltaRe : model.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))))
    (delta0lam : ℝ)
    (hLamMom : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 → M.delta ≤ delta0lam →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
              (E.lam z' r' hr' (cutoffPositiveCoefficient M Hf om N z' hr') z' r' (1 / 8 : ℝ) 1)⁻¹)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure)
    (hdeltaLam : model.delta ≤ delta0lam)
    (hm : 0 < -j) :
    ∃ Ks : ℕ → BilateralField d → ℝ, ∃ Cs : ℝ,
      (∀ J, MemLp (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cs) ∧
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, (J : ℤ) < -j →
        aux_lem_finite_source_comparison_cells_holNeu d z r hr
          (cutoffPositiveCoefficient model H omega J z hr) (1 / 2) (Ks J omega) := by
  set m : ℤ := -j with hmdef
  have hr1 : r ≤ 1 := by
    have h3le1 : (3 : ℝ) ^ j ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    rw [hj]; exact h3le1
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set t : ℝ := (d : ℝ) - 1 / 2 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; linarith
  obtain ⟨Dre, Mxre, hDMnn, hReAE, hReMem⟩ :=
    hReExt model H hH hdeltaRe z r hr hr1
  have hLamMemAll : ∀ N, MemLp (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient model H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹)
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure :=
    fun N => hLamMom model Rm H hH z r hr hr1 hdeltaLam N
  obtain ⟨Cpo, hCpo, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  set Lam18 : ℕ → BilateralField d → ℝ := fun J om =>
    (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r (1 / 8 : ℝ) 1)⁻¹
    with hLam18def
  have hLamLe : ∀ J om, (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ ≤
      Lam18 J om := by
    intro J om
    rw [hLam18def]
    exact inv_anti₀ (E.lam_pos z r hr (cutoffPositiveCoefficient model H om J z hr) z r
      (1 / 8 : ℝ) 1)
      (E.lam_mono z r hr (cutoffPositiveCoefficient model H om J z hr) z r (1 : ℝ≥0∞)
        (1 / 8 : ℝ) (1 : ℝ) (by norm_num))
  have hrJ : ∀ J : ℕ, (J : ℤ) < m → (3 : ℝ) ^ J * r ≤ 1 := by
    intro J hJm
    rw [hj, ← zpow_natCast (3 : ℝ) J, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have ht0' : 0 < t := by rw [htdef]; linarith
  have ht1' : (1 : ℝ) / 2 ≤ t := by rw [htdef]; linarith
  obtain ⟨Ks, Cs, hKsmem, hKsbd, hKsform⟩ := aux_fscc_holNeuH_holNeuH_hSmall_moment model
    r C (P.C ^ 2) t (Real.sqrt d ^ (1 / 2 : ℝ) * (Cp.C (1 / 2) * (1 + Cpo)) *
      r ^ ((1 / 2 : ℝ) / 2)) hr ht0' ht1' m hm Dre Mxre Lam18 hDMnn hReMem hLamMemAll
  refine ⟨Ks, Cs, hKsmem, hKsbd, ?_⟩
  filter_upwards [hReAE] with omega hReAEomega
  intro J hJm
  have hMxpos := (hReAEomega J).1
  have henv := (hReAEomega J).2.1
  have hlip := (hReAEomega J).2.2
  have hrJJ := hrJ J hJm
  simp only [hKsform J hJm]
  exact aux_fscc_holNeuH_holNeuH_hSmall_final hd E P Cp model H omega J z r hr hr1 C c p1 t1 hC
    hbig (Mxre J omega) (Dre J omega) hMxpos (hDMnn J omega).1 henv hlip hrJJ (Lam18 J omega)
    (hLamLe J omega) Cpo hCpo hPoinc

/-- **`hSmall` (H2), the below-wavelength branch of B-NH.** Thin wrapper around
`aux_fscc_holNeuH_holNeuH_hSmall_pos` (heartbeat budget: see that declaration's docstring).
Vacuous when `-j ≤ 0` (`r ≥ 1`, so no `J : ℕ` has `(J:ℤ) < -j`). -/
theorem aux_fscc_holNeuH_holNeuH_hSmall {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredAdmissible model H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ) (hj : r = (3 : ℝ) ^ j)
    (C c p1 t1 : ℝ) (hC : 0 < C)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := aux_fscc_holNeuH_ell c eps DN
      let gamma := aux_fscc_holNeuH_gamma A
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ ((d : ℝ) - 1 / 2) * eps ^ (t1 - ((d : ℝ) - 1 / 2)) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - ((d : ℝ) - 1 / 2))) * rr ^ ((d : ℝ) - 1 / 2)))
    (cdre : ℝ) (hcdre : 0 < cdre)
    (hReExt : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf → M.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))) →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ),
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M Hf om N x ∧
                cutoffCoefficient M Hf om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M Hf om N x) -
                  Real.log (cutoffCoefficient M Hf om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure))
    (hdeltaRe : model.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))))
    (delta0lam : ℝ)
    (hLamMom : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 → M.delta ≤ delta0lam →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
              (E.lam z' r' hr' (cutoffPositiveCoefficient M Hf om N z' hr') z' r' (1 / 8 : ℝ) 1)⁻¹)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure)
    (hdeltaLam : model.delta ≤ delta0lam) :
    ∃ Ks : ℕ → BilateralField d → ℝ, ∃ Cs : ℝ,
      (∀ J, MemLp (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cs) ∧
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, (J : ℤ) < -j →
        aux_lem_finite_source_comparison_cells_holNeu d z r hr
          (cutoffPositiveCoefficient model H omega J z hr) (1 / 2) (Ks J omega) := by
  by_cases hm : 0 < -j
  · exact aux_fscc_holNeuH_holNeuH_hSmall_pos hd E P Cp model Rm H hH z r hr j hj C c p1 t1 hC hbig
      cdre hcdre hReExt hdeltaRe delta0lam hLamMom hdeltaLam hm
  · refine ⟨fun _ _ => 0, 0, fun J => memLp_const 0, fun J => by simp,
      Filter.Eventually.of_forall (fun omega J hJm => absurd hJm (by omega))⟩

/-- **`holNeu_H`'s H1/H2-combination tail, isolated for heartbeat budget.** Same code
`aux_lem_finite_source_comparison_cells_holNeu_H` always had after computing `Km`
(H1's large-`J` branch); pulled into a fresh top-level declaration (own 200000-heartbeat budget)
since the `have hSmall := aux_fscc_holNeuH_holNeuH_hSmall ...` call, embedded in `holNeu_H`'s own
huge accumulated local context (`Kcor`, `hCoreJ`, `hRefMoment`'s innards, `z0`, `w`, `hTeq`,
`hinjQ`, `hq`, ...), was timing out at `isDefEq` even though the same call typechecks fine here in
a small, fresh context. `hmj : m = -j` lets the caller keep its own convenient `m := -j`
abbreviation for building `Km`/`haeKm` while this declaration works with `-j` directly throughout
(via `subst`), avoiding any `m`-vs-`-j` defeq reconciliation inside the large surrounding proof. -/
theorem aux_fscc_holNeuH_holNeu_H_finish {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d) (W : SmallPerturbationInput d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredAdmissible model H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j m : ℤ) (hj : r = (3 : ℝ) ^ j)
    (hmj : m = -j)
    (cdre : ℝ) (hcdre : 0 < cdre)
    (hReExt : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf → M.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))) →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ),
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M Hf om N x ∧
                cutoffCoefficient M Hf om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z' r' hr' : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M Hf om N x) -
                  Real.log (cutoffCoefficient M Hf om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal (2 * ((d : ℝ) - 1 / 2))) (chaosSampleLaw M).toMeasure))
    (hdeltaRe : model.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))))
    (delta0lam : ℝ)
    (hLamMom : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M Hf →
        ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'), r' ≤ 1 → M.delta ≤ delta0lam →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
              (E.lam z' r' hr' (cutoffPositiveCoefficient M Hf om N z' hr') z' r' (1 / 8 : ℝ) 1)⁻¹)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure)
    (hdeltaLam : model.delta ≤ delta0lam)
    (Km : ℕ → BilateralField d → ℝ) (Cref : ℝ) (hCref0 : 0 ≤ Cref)
    (hmemKm : ∀ J, MemLp (Km J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hnormKm : ∀ J, eLpNorm (Km J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cref)
    (haeKm : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, m ≤ (J : ℤ) →
      aux_lem_finite_source_comparison_cells_holNeu d z r hr
        (cutoffPositiveCoefficient model H omega J z hr) (1 / 2) (Km J omega)) :
    aux_lem_finite_source_comparison_cells_holBranch d model H z r hr
      (aux_lem_finite_source_comparison_cells_holNeu d z r hr) := by
  subst hmj
  obtain ⟨Cc0, cc0, p1c0, t1c0, hCc0, hbigc0⟩ := aux_fscc_holNeuH_hSmall_C0 d hd W
  have hSmall : ∃ Ks : ℕ → BilateralField d → ℝ, ∃ Cs : ℝ,
      (∀ J, MemLp (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cs) ∧
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, (J : ℤ) < -j →
        aux_lem_finite_source_comparison_cells_holNeu d z r hr
          (cutoffPositiveCoefficient model H omega J z hr) (1 / 2) (Ks J omega) :=
    aux_fscc_holNeuH_holNeuH_hSmall hd E P Cp model Rm H hH z r hr j hj
      Cc0 cc0 p1c0 t1c0 hCc0 hbigc0
      cdre hcdre hReExt hdeltaRe delta0lam hLamMom hdeltaLam
  obtain ⟨Ks, Cs, hmemKs, hnormKs, haeKs⟩ := hSmall
  refine ⟨fun J omega => ‖Km J omega‖ + ‖Ks J omega‖, |Cref| + |Cs|, ?_, ?_, ?_⟩
  · intro J
    exact (hmemKm J).norm.add (hmemKs J).norm
  · intro J
    calc eLpNorm (fun omega => ‖Km J omega‖ + ‖Ks J omega‖) (ENNReal.ofReal 1)
          (chaosSampleLaw model).toMeasure ≤
        eLpNorm (fun omega => ‖Km J omega‖) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure +
          eLpNorm (fun omega => ‖Ks J omega‖) (ENNReal.ofReal 1)
            (chaosSampleLaw model).toMeasure :=
        eLpNorm_add_le (hmemKm J).norm.1 (hmemKs J).norm.1 (by simp)
      _ = eLpNorm (Km J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure +
          eLpNorm (Ks J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
        rw [eLpNorm_norm, eLpNorm_norm]
      _ ≤ ENNReal.ofReal |Cref| + ENNReal.ofReal |Cs| :=
        add_le_add ((hnormKm J).trans (ENNReal.ofReal_le_ofReal (le_abs_self Cref)))
          ((hnormKs J).trans (ENNReal.ofReal_le_ofReal (le_abs_self Cs)))
      _ = ENNReal.ofReal (|Cref| + |Cs|) := (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm
  · filter_upwards [haeKm, haeKs] with omega hM hS
    intro J
    exact aux_fscc_holNeuH_final_merge z r hr (cutoffPositiveCoefficient model H omega J z hr)
      (-j) (J : ℤ) (Km J omega) (Ks J omega) (hM J) (hS J)
/-- **Remaining typed goal (B-NH)**, paper 4323--4327 with `cor_neumann_source`: the mean-zero
Neumann Hölder branch for the characterized field on every triadic root cube.
`cor_neumann_source` states it on `unitNeumannCube d` only. -/
theorem aux_lem_finite_source_comparison_cells_holNeu_H
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        aux_lem_finite_source_comparison_cells_holBranch d model H z r hr
          (aux_lem_finite_source_comparison_cells_holNeu d z r hr) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨delta0, hdelta0, hChar⟩ :=
    fscc_char_holder_neumann d hd E P X W Cp Sf D (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨cdre, hcdre, hReExt⟩ :=
    aux_fscc_holNeuH_root_extremes_at d hd
  obtain ⟨delta0lam, hdelta0lam, hLamMom⟩ :=
    aux_fscc_holNeuH_lambda_inv_at d hd E
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine ⟨min delta0 (min (cdre / (2 * (2 * ((d : ℝ) - 1 / 2)))) delta0lam),
    lt_min hdelta0 (lt_min (div_pos hcdre (by linarith)) hdelta0lam), ?_⟩
  intro model Rm Sreg It H hH hdelta z r hr hrj
  have hdeltaCor : model.delta ≤ delta0 := hdelta.trans (min_le_left _ _)
  have hdeltaRe : model.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaLam : model.delta ≤ delta0lam :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  clear hdelta
  obtain ⟨j, hj⟩ := hrj
  set m : ℤ := -j with hmdef
  -- the cutoffs `J ≥ m`: `fscc_char_holder_neumann` at `alpha = 1/2`
  obtain ⟨Km, Cb, hmemKm, hnormKm, haeKm⟩ := hChar model Rm Sreg It H hH hdeltaCor z j r hr hj
  exact aux_fscc_holNeuH_holNeu_H_finish hd E P Cp W model Rm H (InfraredAdmissible.of_char hH) z r hr j m hj hmdef
    cdre hcdre hReExt hdeltaRe delta0lam hLamMom hdeltaLam Km (max Cb 0) (le_max_right _ _)
    hmemKm (fun J => (hnormKm J).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) haeKm

/-- **Remaining typed goal (B-N0)**: the mean-zero Neumann Hölder branch with the infrared field
removed, on every triadic root cube (paper 4338--4345). -/
theorem aux_lem_finite_source_comparison_cells_holNeu_zero
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        aux_lem_finite_source_comparison_cells_holBranch d model
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z r hr
          (aux_lem_finite_source_comparison_cells_holNeu d z r hr) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨delta0, hdelta0, hZero⟩ :=
    fscc_zero_holder_neumann d hd E P X W Cp Sf D (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨cdre, hcdre, hReExt⟩ :=
    aux_fscc_holNeuH_root_extremes_at d hd
  obtain ⟨delta0lam, hdelta0lam, hLamMom⟩ :=
    aux_fscc_holNeuH_lambda_inv_at d hd E
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine ⟨min delta0 (min (cdre / (2 * (2 * ((d : ℝ) - 1 / 2)))) delta0lam),
    lt_min hdelta0 (lt_min (div_pos hcdre (by linarith)) hdelta0lam), ?_⟩
  intro model Rm Sreg It _H _hH hdelta z r hr hrj
  have hdeltaCor : model.delta ≤ delta0 := hdelta.trans (min_le_left _ _)
  have hdeltaRe : model.delta ≤ cdre / (2 * (2 * ((d : ℝ) - 1 / 2))) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaLam : model.delta ≤ delta0lam :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  clear hdelta
  obtain ⟨j, hj⟩ := hrj
  set m : ℤ := -j with hmdef
  -- the cutoffs `J ≥ m`: `fscc_zero_holder_neumann` at `alpha = 1/2` (small roots and big roots)
  obtain ⟨Km, Cb, hmemKm, hnormKm, haeKm⟩ := hZero model Rm Sreg It hdeltaCor z j r hr hj
  exact aux_fscc_holNeuH_holNeu_H_finish hd E P Cp W model Rm
    (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (InfraredAdmissible.zero model) z r hr j m hj
    hmdef cdre hcdre hReExt hdeltaRe delta0lam hLamMom hdeltaLam Km (max Cb 0) (le_max_right _ _)
    hmemKm (fun J => (hnormKm J).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) haeKm

theorem aux_lem_finite_source_comparison_cells_holDir_mono {d : ℕ} {z : SpatialCoordinates d}
    {r : ℝ} {hr : 0 < r} {a : PositiveCoefficient (centeredCube z r hr)} {alpha Kh Kh' : ℝ}
    (h : aux_lem_finite_source_comparison_cells_holDir d z r hr a alpha Kh) (hle : Kh ≤ Kh') :
    aux_lem_finite_source_comparison_cells_holDir d z r hr a alpha Kh' := by
  intro F Kf hKf hF hFb phi hphi b u hb hsol
  obtain ⟨U, hUc, hUeq, hU⟩ := h F Kf hKf hF hFb phi hphi b u hb hsol
  refine ⟨U, hUc, hUeq, fun x hx y hy => (hU x hx y hy).trans ?_⟩
  have hL : 0 ≤ Kf + c2Norm (closedCube z r hr) phi :=
    add_nonneg hKf (aux_lem_finite_source_comparison_cells_c2Norm_nonneg _ _)
  have hdist : 0 ≤ dist x y ^ alpha := Real.rpow_nonneg dist_nonneg _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hL) hdist
  exact this

theorem aux_lem_finite_source_comparison_cells_holNeu_mono {d : ℕ} {z : SpatialCoordinates d}
    {r : ℝ} {hr : 0 < r} {a : PositiveCoefficient (centeredCube z r hr)} {alpha Kh Kh' : ℝ}
    (h : aux_lem_finite_source_comparison_cells_holNeu d z r hr a alpha Kh) (hle : Kh ≤ Kh') :
    aux_lem_finite_source_comparison_cells_holNeu d z r hr a alpha Kh' := by
  intro F Kf hKf hF hFb hmean u hsol
  obtain ⟨U, hUc, hUeq, hU⟩ := h F Kf hKf hF hFb hmean u hsol
  refine ⟨U, hUc, hUeq, fun x hx y hy => (hU x hx y hy).trans ?_⟩
  have hdist : 0 ≤ dist x y ^ alpha := Real.rpow_nonneg dist_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hKf) hdist

/-- Two branches (Dirichlet, Neumann) for one coefficient family merge into one constant
`‖K_D‖ + ‖K_N‖` with first-moment bound `C_D + C_N`. -/
theorem aux_lem_finite_source_comparison_cells_merge_pair {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hD : aux_lem_finite_source_comparison_cells_holBranch d model Hused z r hr
      (aux_lem_finite_source_comparison_cells_holDir d z r hr))
    (hN : aux_lem_finite_source_comparison_cells_holBranch d model Hused z r hr
      (aux_lem_finite_source_comparison_cells_holNeu d z r hr)) :
    ∃ (K : ℕ → BilateralField d → ℝ) (Cb : ℝ),
      (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cb) ∧
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ,
        aux_lem_finite_source_comparison_cells_holDir d z r hr
            (cutoffPositiveCoefficient model Hused omega J z hr) (1 / 2) (K J omega) ∧
          aux_lem_finite_source_comparison_cells_holNeu d z r hr
            (cutoffPositiveCoefficient model Hused omega J z hr) (1 / 2) (K J omega) := by
  obtain ⟨KD, CD, mD, nD, aD⟩ := hD
  obtain ⟨KN, CN, mN, nN, aN⟩ := hN
  refine ⟨fun J omega => ‖KD J omega‖ + ‖KN J omega‖, |CD| + |CN|,
    fun J => (mD J).norm.add (mN J).norm, fun J => ?_, ?_⟩
  · have h1 : (1 : ENNReal) ≤ ENNReal.ofReal 1 := by simp
    calc eLpNorm (fun omega => ‖KD J omega‖ + ‖KN J omega‖) (ENNReal.ofReal 1)
          (chaosSampleLaw model).toMeasure
        ≤ eLpNorm (fun omega => ‖KD J omega‖) (ENNReal.ofReal 1)
            (chaosSampleLaw model).toMeasure +
          eLpNorm (fun omega => ‖KN J omega‖) (ENNReal.ofReal 1)
            (chaosSampleLaw model).toMeasure :=
          eLpNorm_add_le (mD J).norm.1 (mN J).norm.1 h1
      _ = eLpNorm (KD J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure +
          eLpNorm (KN J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
          rw [eLpNorm_norm, eLpNorm_norm]
      _ ≤ ENNReal.ofReal |CD| + ENNReal.ofReal |CN| :=
          add_le_add ((nD J).trans (ENNReal.ofReal_le_ofReal (le_abs_self CD)))
            ((nN J).trans (ENNReal.ofReal_le_ofReal (le_abs_self CN)))
      _ = ENNReal.ofReal (|CD| + |CN|) :=
          (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm
  · filter_upwards [aD, aN] with omega hD hN
    intro J
    refine ⟨aux_lem_finite_source_comparison_cells_holDir_mono (hD J) ?_,
      aux_lem_finite_source_comparison_cells_holNeu_mono (hN J) ?_⟩
    · have := norm_nonneg (KN J omega)
      have := Real.le_norm_self (KD J omega)
      linarith
    · have := norm_nonneg (KD J omega)
      have := Real.le_norm_self (KN J omega)
      linarith

/-- **The Hölder input** (paper 4323--4327): one random constant per infrared choice, with
cutoff-uniform first moments, serving both the Dirichlet and the Neumann branch on one
full-measure event, at the exponent `1/2`. -/
theorem aux_lem_finite_source_comparison_cells_holder
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
        (Sreg : in_6_16 d model) (It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∃ (K : Bool → ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ b J, MemLp (K b J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ b J, eLpNorm (K b J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ (J : ℕ) (infrared : Bool),
          aux_lem_finite_source_comparison_cells_holDir d z r hr
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega J z hr) (1 / 2) (K infrared J omega) ∧
            aux_lem_finite_source_comparison_cells_holNeu d z r hr
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega J z hr) (1 / 2) (K infrared J omega) := by
  obtain ⟨d1, hd1, hDH⟩ := aux_lem_finite_source_comparison_cells_holDir_H d hd E P X W Cp Sf
  obtain ⟨d2, hd2, hD0⟩ := aux_lem_finite_source_comparison_cells_holDir_zero d hd E P X W Cp Sf D
  obtain ⟨d3, hd3, hNH⟩ := aux_lem_finite_source_comparison_cells_holNeu_H d hd E P X W Cp Sf D
  obtain ⟨d4, hd4, hN0⟩ :=
    aux_lem_finite_source_comparison_cells_holNeu_zero d hd E P X W Cp Sf D
  refine ⟨min (min d1 d2) (min d3 d4), lt_min (lt_min hd1 hd2) (lt_min hd3 hd4), ?_⟩
  intro model Rm Sreg It H hH hsmall z r hr htri
  have h1 : model.delta ≤ d1 := hsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : model.delta ≤ d2 := hsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : model.delta ≤ d3 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : model.delta ≤ d4 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨K1, C1, m1, n1, a1⟩ := aux_lem_finite_source_comparison_cells_merge_pair model H z r hr
    (hDH model Rm Sreg It H hH h1 z r hr) (hNH model Rm Sreg It H hH h3 z r hr htri)
  obtain ⟨K0, C0, m0, n0, a0⟩ := aux_lem_finite_source_comparison_cells_merge_pair model
    (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) z r hr
    (hD0 model Rm Sreg It H hH h2 z r hr htri) (hN0 model Rm Sreg It H hH h4 z r hr htri)
  refine ⟨fun b => if b then K1 else K0, |C1| + |C0|, ?_, ?_, ?_⟩
  · intro b J
    cases b
    · exact m0 J
    · exact m1 J
  · intro b J
    cases b
    · exact (n0 J).trans (ENNReal.ofReal_le_ofReal (by
        have := abs_nonneg C1; have := le_abs_self C0; linarith))
    · exact (n1 J).trans (ENNReal.ofReal_le_ofReal (by
        have := abs_nonneg C0; have := le_abs_self C1; linarith))
  · filter_upwards [a1, a0] with omega h1 h0
    intro J infrared
    cases infrared
    · exact h0 J
    · exact h1 J

/-! ### The sourced stopping partition (paper 4310--4329) -/



theorem aux_lem_finite_source_comparison_cells_partition
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
        (Sreg : in_6_16 d model) (It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ eta : ℝ, 0 < eta →
      ∃ (Ceta gamma Cside : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧ 0 ≤ Cside ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : ℕ → Prop),
      theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
          (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
      ∀ reverse : Bool,
      (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
        ((Real.exp ((((if reverse then M else N) - H1 * n : ℕ) + 1 : ℝ) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((if reverse then M else N) - H1 * n)) /
          (Real.exp ((((if reverse then M else N : ℕ) : ℝ) + 1) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (if reverse then M else N))) /
        ((Real.exp ((((if reverse then N else M) - H1 * n : ℕ) + 1 : ℝ) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((if reverse then N else M) - H1 * n)) /
          (Real.exp ((((if reverse then N else M : ℕ) : ℝ) + 1) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (if reverse then N else M))) ≤ c) →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
        ∀ omega ∉ Bad, ∀ infrared : Bool,
          aux_lem_finite_source_comparison_cells_partDir d z r hr N
              (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4)))
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then M else N) z hr)
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then N else M) z hr)
              (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
              (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom)) ∧
            aux_lem_finite_source_comparison_cells_partNeu d z r hr N
              (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4)))
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then M else N) z hr)
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then N else M) z hr)
              (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
              (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom)) := by
  exact lfsc_partition_main d hd E P X W Cp Sf D theta htheta



/-- Generic Markov/Chebyshev tail bound at exponent `p`, from an `eLpNorm` bound.
(harvest fg_markov_tail, flash-proved, standard axioms; copied verbatim.) -/
theorem aux_lem_finite_source_comparison_cells_markov_tail {Ω : Type*} [MeasurableSpace Ω]
    (μMT : Measure Ω) (KMT : Ω → ℝ) (hK : AEStronglyMeasurable KMT μMT) (p : ℝ) (hp : 0 < p)
    (B : ℝ) (hB : eLpNorm KMT (ENNReal.ofReal p) μMT ≤ ENNReal.ofReal B)
    (t : ℝ) (ht : 0 < t) :
    μMT {omg | t ≤ |KMT omg|} ≤ ENNReal.ofReal ((B / t) ^ p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hset : {omg : Ω | ENNReal.ofReal t ≤ ‖KMT omg‖ₑ} = {omg : Ω | t ≤ |KMT omg|} := by
    ext omg
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  have htp_pos : 0 < (ENNReal.ofReal t) ^ p :=
    ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ht) (le_of_lt hp)
  have htp_ne_top : (ENNReal.ofReal t) ^ p ≠ ⊤ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt ht) (le_of_lt hp)]
    exact ENNReal.ofReal_ne_top
  have hcheb : (ENNReal.ofReal t) ^ p * μMT {omg : Ω | t ≤ |KMT omg|}
      ≤ (eLpNorm KMT (ENNReal.ofReal p) μMT) ^ p := by
    have h := mul_meas_ge_le_pow_eLpNorm' (μ := μMT) (p := ENNReal.ofReal p) hp0 hptop hK
      (ENNReal.ofReal t)
    rwa [ENNReal.toReal_ofReal (le_of_lt hp), hset] at h
  have hdiv : μMT {omg : Ω | t ≤ |KMT omg|}
      ≤ (eLpNorm KMT (ENNReal.ofReal p) μMT) ^ p / (ENNReal.ofReal t) ^ p := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl htp_pos.ne') (Or.inl htp_ne_top), mul_comm]
    exact hcheb
  by_cases hBneg : B < 0
  · have heLp0 : eLpNorm KMT (ENNReal.ofReal p) μMT = 0 :=
      le_antisymm (hB.trans (le_of_eq (ENNReal.ofReal_of_nonpos (le_of_lt hBneg)))) (zero_le _)
    have hle : μMT {omg : Ω | t ≤ |KMT omg|} ≤ 0 :=
      hdiv.trans (le_of_eq (by rw [heLp0, ENNReal.zero_rpow_of_pos hp, ENNReal.zero_div]))
    rw [le_antisymm hle (zero_le _)]
    exact zero_le _
  · push_neg at hBneg
    have hmono : (eLpNorm KMT (ENNReal.ofReal p) μMT) ^ p ≤ (ENNReal.ofReal B) ^ p :=
      ENNReal.rpow_le_rpow hB (le_of_lt hp)
    have h1 : (eLpNorm KMT (ENNReal.ofReal p) μMT) ^ p / (ENNReal.ofReal t) ^ p
        ≤ (ENNReal.ofReal B) ^ p / (ENNReal.ofReal t) ^ p :=
      ENNReal.div_le_div_right hmono _
    have heq : (ENNReal.ofReal B) ^ p / (ENNReal.ofReal t) ^ p = ENNReal.ofReal ((B / t) ^ p) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hBneg (le_of_lt hp),
        ENNReal.ofReal_rpow_of_nonneg (le_of_lt ht) (le_of_lt hp),
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht p),
        ← Real.div_rpow hBneg (le_of_lt ht) p]
    exact hdiv.trans (h1.trans (le_of_eq heq))

/-- Pure arithmetic step of the assembly: the merged probability/error budget
`Ceta0*3^{-gamma0 N} + 2*(Cb'/t16)` is dominated by `Ceta*3^{-gamma N}` once
`Ceta`, `gamma` are chosen to majorize both the partition's own constants and the
Markov-tail rate. Isolated in its own declaration for the heartbeat budget. -/
theorem aux_lem_finite_source_comparison_cells_final_bound
    (Ceta0 gamma0 Cb' Ceta gamma Cside t16 : ℝ) (N : ℕ)
    (hCeta0 : 0 < Ceta0) (hCb'nonneg : 0 ≤ Cb') (hCside : 0 ≤ Cside)
    (hCetaeq : Ceta = Ceta0 + 2 * Cb' + 4 * Cside ^ (1 / 2 : ℝ))
    (hgamma_le0 : gamma ≤ gamma0) (hgamma_leK : gamma ≤ (1 / 2 : ℝ) / 8)
    (ht16eq : t16 = (3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ))) :
    Ceta0 * (3 : ℝ) ^ (-gamma0 * (N : ℝ)) + (Cb' / t16 + Cb' / t16) ≤
      Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
  have hCside2nonneg : 0 ≤ Cside ^ (1 / 2 : ℝ) := Real.rpow_nonneg hCside _
  have e1 : Ceta0 * (3 : ℝ) ^ (-gamma0 * (N : ℝ)) ≤ Ceta0 * (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
    aux_lem_finite_source_comparison_cells_err_mono Ceta0 gamma0 Ceta0 gamma N le_rfl
      hCeta0.le hgamma_le0
  have e2 : Cb' * (3 : ℝ) ^ (-((1 / 2 : ℝ) / 8) * (N : ℝ)) ≤
      Cb' * (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
    aux_lem_finite_source_comparison_cells_err_mono Cb' ((1 / 2 : ℝ) / 8) Cb' gamma N le_rfl
      hCb'nonneg hgamma_leK
  have ht16eq2 : Cb' / t16 = Cb' * (3 : ℝ) ^ (-((1 / 2 : ℝ) / 8) * (N : ℝ)) := by
    rw [ht16eq, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 2
    ring
  have hrpow_nonneg : 0 ≤ (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [hCetaeq, ht16eq2]
  nlinarith [e1, e2, mul_nonneg (show (0 : ℝ) ≤ 4 * Cside ^ (1 / 2 : ℝ) by nlinarith [hCside2nonneg])
    hrpow_nonneg]

/-- Measure-theoretic assembly step: package the partition's exceptional event `BadA`
together with the Markov-tail exclusions for `K` (both infrared branches, at cutoff `Ns`)
and the a.e.-exceptional set of the Hölder bank into one measurable `Bad`, with the merged
probability bound. Isolated in its own declaration for the heartbeat budget. -/
theorem aux_lem_finite_source_comparison_cells_assemble_bad
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Ns : ℕ) (K : Bool → ℕ → BilateralField d → ℝ) (Cbank : ℝ)
    (hmem : ∀ b J, MemLp (K b J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ b J, eLpNorm (K b J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cbank)
    (hae : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ (J : ℕ) (infrared : Bool),
        aux_lem_finite_source_comparison_cells_holDir d z r hr
          (cutoffPositiveCoefficient model
            (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
            omega J z hr) (1 / 2) (K infrared J omega) ∧
        aux_lem_finite_source_comparison_cells_holNeu d z r hr
          (cutoffPositiveCoefficient model
            (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
            omega J z hr) (1 / 2) (K infrared J omega))
    (BadA : Set (BilateralField d)) (hBadAmeas : MeasurableSet BadA)
    (t16 : ℝ) (ht16pos : 0 < t16)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hBadAbound : (chaosSampleLaw model).toMeasure BadA ≤ ENNReal.ofReal bound)
    (Cb' : ℝ) (hCb'eq : Cb' = max Cbank 0)
    (final : ℝ) (hnum : bound + (Cb' / t16 + Cb' / t16) ≤ final) :
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal final ∧
      ∀ omega ∉ Bad, omega ∉ BadA ∧ (∀ b : Bool, |K b Ns omega| ≤ t16) ∧
        ∀ (J : ℕ) (infrared : Bool),
          aux_lem_finite_source_comparison_cells_holDir d z r hr
            (cutoffPositiveCoefficient model
              (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
              omega J z hr) (1 / 2) (K infrared J omega) ∧
          aux_lem_finite_source_comparison_cells_holNeu d z r hr
            (cutoffPositiveCoefficient model
              (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
              omega J z hr) (1 / 2) (K infrared J omega) := by
  have hKmeasT : AEStronglyMeasurable (K true Ns) (chaosSampleLaw model).toMeasure :=
    (hmem true Ns).aestronglyMeasurable
  have hKmeasF : AEStronglyMeasurable (K false Ns) (chaosSampleLaw model).toMeasure :=
    (hmem false Ns).aestronglyMeasurable
  have htailT := aux_lem_finite_source_comparison_cells_markov_tail
    (chaosSampleLaw model).toMeasure (K true Ns) hKmeasT 1 (by norm_num) Cbank
    (hnorm true Ns) t16 ht16pos
  have htailF := aux_lem_finite_source_comparison_cells_markov_tail
    (chaosSampleLaw model).toMeasure (K false Ns) hKmeasF 1 (by norm_num) Cbank
    (hnorm false Ns) t16 ht16pos
  rw [Real.rpow_one] at htailT htailF
  have hCb'nonneg : 0 ≤ Cb' := hCb'eq ▸ le_max_right _ _
  have htailT' : (chaosSampleLaw model).toMeasure {omega | t16 ≤ |K true Ns omega|} ≤
      ENNReal.ofReal (Cb' / t16) :=
    htailT.trans (ENNReal.ofReal_le_ofReal (by
      rw [hCb'eq]; exact div_le_div_of_nonneg_right (le_max_left Cbank 0) ht16pos.le))
  have htailF' : (chaosSampleLaw model).toMeasure {omega | t16 ≤ |K false Ns omega|} ≤
      ENNReal.ofReal (Cb' / t16) :=
    htailF.trans (ENNReal.ofReal_le_ofReal (by
      rw [hCb'eq]; exact div_le_div_of_nonneg_right (le_max_left Cbank 0) ht16pos.le))
  set tailUnion : Set (BilateralField d) :=
    {omega | t16 ≤ |K true Ns omega|} ∪ {omega | t16 ≤ |K false Ns omega|} with htailUniondef
  set TM : Set (BilateralField d) := toMeasurable (chaosSampleLaw model).toMeasure tailUnion
    with hTMdef
  have hTMmeas : MeasurableSet TM := measurableSet_toMeasurable _ _
  have hTMsup : tailUnion ⊆ TM := subset_toMeasurable _ _
  have hTMeq : (chaosSampleLaw model).toMeasure TM =
      (chaosSampleLaw model).toMeasure tailUnion := measure_toMeasurable _
  have hTMbound : (chaosSampleLaw model).toMeasure TM ≤
      ENNReal.ofReal (Cb' / t16) + ENNReal.ofReal (Cb' / t16) := by
    rw [hTMeq]
    exact (measure_union_le _ _).trans (add_le_add htailT' htailF')
  obtain ⟨Traw, hTrawSup, hTrawMeas, hTrawZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨(BadA ∪ TM) ∪ Traw, (hBadAmeas.union hTMmeas).union hTrawMeas, ?_, ?_⟩
  · have hB0 : (0 : ℝ) ≤ Cb' / t16 := div_nonneg hCb'nonneg ht16pos.le
    calc (chaosSampleLaw model).toMeasure ((BadA ∪ TM) ∪ Traw)
        ≤ (chaosSampleLaw model).toMeasure (BadA ∪ TM) +
            (chaosSampleLaw model).toMeasure Traw := measure_union_le _ _
      _ ≤ ((chaosSampleLaw model).toMeasure BadA + (chaosSampleLaw model).toMeasure TM) +
            (chaosSampleLaw model).toMeasure Traw :=
          add_le_add_left (measure_union_le _ _) _
      _ ≤ ((chaosSampleLaw model).toMeasure BadA +
            (ENNReal.ofReal (Cb' / t16) + ENNReal.ofReal (Cb' / t16))) +
            (chaosSampleLaw model).toMeasure Traw :=
          add_le_add_left (add_le_add_right hTMbound _) _
      _ = (chaosSampleLaw model).toMeasure BadA +
            (ENNReal.ofReal (Cb' / t16) + ENNReal.ofReal (Cb' / t16)) := by
          rw [hTrawZero, add_zero]
      _ ≤ ENNReal.ofReal bound +
            (ENNReal.ofReal (Cb' / t16) + ENNReal.ofReal (Cb' / t16)) :=
          add_le_add_left hBadAbound _
      _ = ENNReal.ofReal (bound + (Cb' / t16 + Cb' / t16)) := by
          rw [ENNReal.ofReal_add hbound0 (add_nonneg hB0 hB0), ENNReal.ofReal_add hB0 hB0]
      _ ≤ ENNReal.ofReal final := ENNReal.ofReal_le_ofReal hnum
  · intro omega homega
    simp only [Set.mem_union, not_or] at homega
    obtain ⟨⟨hA, hTM⟩, hTr⟩ := homega
    refine ⟨hA, ?_, ?_⟩
    · intro b
      have hnotTailUnion : omega ∉ tailUnion := fun h => hTM (hTMsup h)
      rw [htailUniondef] at hnotTailUnion
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnotTailUnion
      cases b
      · exact hnotTailUnion.2.le
      · exact hnotTailUnion.1.le
    · by_contra hcon
      exact hTr (hTrawSup hcon)

/-- Term-mode wrapper target: identical statement to the principal, proved by tactics
here so the principal itself can close by a single (cheap) direct application,
avoiding `obtain`/`rcases` motive computation against the principal's own (large)
goal term. -/
theorem aux_lem_finite_source_comparison_cells_assemble
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      (let L : ℝ := (3 : ℝ) ^ H1
       ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
         (Rm : in_responses d model) (Sreg : in_6_16 d model)
         (It : in_iteration d model E Sreg)
         (H : BilateralField d → C(SpatialCoordinates d, ℝ))
         (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
         (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
         (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
       ∀ (eta : ℝ), 0 < eta →
       ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
       ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
       ∀ (c : ℝ), 0 < c → c ≤ 2 →
       ∀ (S : ℕ → Prop),
       theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
           (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
       ∀ reverse : Bool,
       let Nt : ℕ := if reverse then M else N
       let Ns : ℕ := if reverse then N else M
       let kappa := fun J : ℕ =>
         Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
           SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
         (kappa (Nt - H1 * n) / kappa Nt) / (kappa (Ns - H1 * n) / kappa Ns) ≤ c) →
       ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
         (chaosSampleLaw model).toMeasure Bad ≤
           ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
         ∀ omega ∉ Bad, ∀ infrared : Bool,
         let Hused := if infrared then H else
           (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
         let aTarget := cutoffPositiveCoefficient model Hused omega Nt z hr
         let aSource := cutoffPositiveCoefficient model Hused omega Ns z hr
         let err := Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))
         let factor := c * (1 + Cgeom * eta * L ^ Dgeom)
         let Q := centeredCube z r hr
         let closedQ := closedCube z r hr
         ((∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
             0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
             ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
             ∀ b u : weakSobolevGraph Q,
               ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
               SolvesDirichlet aSource F b u →
               ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
                 ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
                 let cell := fun i => centeredCube (centers i) (sides i) (hside i)
                 ∃ hle : ∀ i, cell i ≤ Q,
                   (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
                     (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
                   Pairwise (fun i j =>
                     Disjoint (cell i : Set (SpatialCoordinates d))
                       (cell j : Set (SpatialCoordinates d))) ∧
                   ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
                     (Q : Set (SpatialCoordinates d))) ∧
                   ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
                     ∀ v : killedSobolevGraph (cell i),
                       ‖(v : SobolevData (cell i)).1‖ ≤
                         K * ‖@subspaceGradient d (cell i)
                           (killedSobolevGraph (cell i)) v‖,
                     ∃ U : SpatialCoordinates d → ℝ,
                       ContinuousOn U closedQ ∧
                       (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                         =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                       (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                         ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                           |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
                     (∑ i : Fin ncell,
                       @dirichletResponse d (cell i)
                         (@killedResponseSpace d (cell i) (hPcell i))
                         (positiveCoefficientRestrict (hle i) aTarget)
                         ⟨sobolevDataRestrict (hle i) u.val,
                           sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
                       factor * sobolevCoefficientForm aSource u.val u.val +
                         err * (Kf + c2Norm closedQ phi) ^ 2) ∧
           (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
             0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
             (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
             ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
             ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
               ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
               let cell := fun i => centeredCube (centers i) (sides i) (hside i)
               ∃ hle : ∀ i, cell i ≤ Q,
                 (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
                   (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
                 Pairwise (fun i j =>
                   Disjoint (cell i : Set (SpatialCoordinates d))
                     (cell j : Set (SpatialCoordinates d))) ∧
                 ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
                   (Q : Set (SpatialCoordinates d))) ∧
                 ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
                   ∀ v : killedSobolevGraph (cell i),
                     ‖(v : SobolevData (cell i)).1‖ ≤
                       K * ‖@subspaceGradient d (cell i)
                         (killedSobolevGraph (cell i)) v‖,
                   ∃ U : SpatialCoordinates d → ℝ,
                     ContinuousOn U closedQ ∧
                     (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                       =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                     (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                       ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                         |U x - U y| ≤ (err / 4) * Kf) ∧
                   (∑ i : Fin ncell,
                     @dirichletResponse d (cell i)
                       (@killedResponseSpace d (cell i) (hPcell i))
                       (positiveCoefficientRestrict (hle i) aTarget)
                       ⟨sobolevDataRestrict (hle i) u.val,
                         sobolevDataRestrict_mem_weak (hle i)
                           ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
                     factor * sobolevCoefficientForm aSource u.val u.val +
                       err * Kf ^ 2))) := by
  have hpartTerm :=
    aux_lem_finite_source_comparison_cells_partition d hd E P X W Cp Sf D theta htheta
  obtain ⟨H1', Dgeom', Cgeom', delta0P, hH1', hDgeom', hCgeom', hdelta0P, hpart⟩ := hpartTerm
  have hholTerm := aux_lem_finite_source_comparison_cells_holder d hd E P X W Cp Sf D
  obtain ⟨delta0H, hdelta0H, hhol⟩ := hholTerm
  refine ⟨H1', Dgeom', Cgeom', min delta0P delta0H, hH1', hDgeom', hCgeom',
    lt_min hdelta0P hdelta0H, ?_⟩
  intro Lval model Rm Sreg It H hH hsmall z r hr htriadic eta heta
  have hsmallP : model.delta ≤ delta0P := hsmall.trans (min_le_left _ _)
  have hsmallH : model.delta ≤ delta0H := hsmall.trans (min_le_right _ _)
  have hpartNTerm := hpart model Rm Sreg It H hH hsmallP z r hr htriadic eta heta
  obtain ⟨Ceta0, gamma0, Cside, N0, hCeta0, hgamma0, hCside, hpartN⟩ := hpartNTerm
  have hholInstTerm := hhol model Rm Sreg It H hH hsmallH z r hr htriadic
  obtain ⟨K, Cbank, hmem, hnorm, hae⟩ := hholInstTerm
  have hCb'nonneg : (0 : ℝ) ≤ max Cbank 0 := le_max_right _ _
  have hgamma_le0 : min gamma0 ((1 / 2 : ℝ) / 8) ≤ gamma0 := min_le_left _ _
  have hgamma_leK : min gamma0 ((1 / 2 : ℝ) / 8) ≤ (1 / 2 : ℝ) / 8 := min_le_right _ _
  have hgamma_pos : (0 : ℝ) < min gamma0 ((1 / 2 : ℝ) / 8) := lt_min hgamma0 (by norm_num)
  have hCside2nonneg : 0 ≤ Cside ^ (1 / 2 : ℝ) := Real.rpow_nonneg hCside _
  have hCeta_pos : (0 : ℝ) < Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ) := by
    nlinarith [hCb'nonneg, hCside2nonneg]
  refine ⟨Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ), min gamma0 ((1 / 2 : ℝ) / 8), N0,
    hCeta_pos, hgamma_pos, ?_⟩
  intro N M hN0 hNM c hc0 hc2 S hcard reverse Ntval Nsval kappaval hratio
  have hpartNInstTerm := hpartN N M hN0 hNM c hc0 hc2 S hcard reverse hratio
  obtain ⟨BadA, hBadAmeas, hBadAbound, hBadAclause⟩ := hpartNInstTerm
  have ht16pos : (0 : ℝ) < (3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnum : Ceta0 * (3 : ℝ) ^ (-gamma0 * (N : ℝ)) +
      (max Cbank 0 / (3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ)) +
        max Cbank 0 / (3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ))) ≤
      (Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ)) *
        (3 : ℝ) ^ (-min gamma0 ((1 / 2 : ℝ) / 8) * (N : ℝ)) :=
    aux_lem_finite_source_comparison_cells_final_bound Ceta0 gamma0 (max Cbank 0)
      (Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ)) (min gamma0 ((1 / 2 : ℝ) / 8)) Cside
      ((3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ))) N
      hCeta0 hCb'nonneg hCside rfl hgamma_le0 hgamma_leK rfl
  have hbound0 : (0 : ℝ) ≤ Ceta0 * (3 : ℝ) ^ (-gamma0 * (N : ℝ)) :=
    mul_nonneg hCeta0.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hAssembleBadTerm :=
    aux_lem_finite_source_comparison_cells_assemble_bad d model H z r hr
      (if reverse then N else M) K Cbank hmem hnorm hae
      BadA hBadAmeas ((3 : ℝ) ^ ((1 / 2 : ℝ) / 8 * (N : ℝ))) ht16pos
      (Ceta0 * (3 : ℝ) ^ (-gamma0 * (N : ℝ))) hbound0 hBadAbound
      (max Cbank 0) rfl
      ((Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ)) *
        (3 : ℝ) ^ (-min gamma0 ((1 / 2 : ℝ) / 8) * (N : ℝ))) hnum
  obtain ⟨Bad, hBadmeas, hBadbound, hBadprop⟩ := hAssembleBadTerm
  refine ⟨Bad, hBadmeas, hBadbound, ?_⟩
  intro omega homega infrared
  have hBadpropTerm := hBadprop omega homega
  obtain ⟨hA, hKbound, hQomega⟩ := hBadpropTerm
  have hPartPair := hBadAclause omega hA infrared
  have hHolPair := hQomega (if reverse then N else M) infrared
  exact aux_lem_finite_source_comparison_cells_assemble_pair z hr N
      (cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega (if reverse then M else N) z hr)
      (cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega (if reverse then N else M) z hr)
      (min gamma0 ((1 / 2 : ℝ) / 8))
      (Ceta0 + 2 * max Cbank 0 + 4 * Cside ^ (1 / 2 : ℝ)) Ceta0 gamma0 Cside
      (c * (1 + Cgeom' * eta * ((3 : ℝ) ^ H1') ^ Dgeom')) (K infrared (if reverse then N else M) omega)
      hgamma_leK hgamma_le0 hCside
      (by nlinarith [hCb'nonneg, hCside2nonneg])
      (by nlinarith [hCb'nonneg, hCside2nonneg]) hCeta0.le
      (hKbound infrared)
      hPartPair.1 hPartPair.2 hHolPair.1 hHolPair.2




theorem lem_finite_source_comparison_cells
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      (let L : ℝ := (3 : ℝ) ^ H1
       ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
         (Rm : in_responses d model) (Sreg : in_6_16 d model)
         (It : in_iteration d model E Sreg)
         (H : BilateralField d → C(SpatialCoordinates d, ℝ))
         (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
         (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
         (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
       ∀ (eta : ℝ), 0 < eta →
       ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
       ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
       ∀ (c : ℝ), 0 < c → c ≤ 2 →
       ∀ (S : ℕ → Prop),
       theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
           (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
       ∀ reverse : Bool,
       let Nt : ℕ := if reverse then M else N
       let Ns : ℕ := if reverse then N else M
       let kappa := fun J : ℕ =>
         Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
           SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
         (kappa (Nt - H1 * n) / kappa Nt) / (kappa (Ns - H1 * n) / kappa Ns) ≤ c) →
       ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
         (chaosSampleLaw model).toMeasure Bad ≤
           ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
         ∀ omega ∉ Bad, ∀ infrared : Bool,
         let Hused := if infrared then H else
           (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
         let aTarget := cutoffPositiveCoefficient model Hused omega Nt z hr
         let aSource := cutoffPositiveCoefficient model Hused omega Ns z hr
         let err := Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))
         let factor := c * (1 + Cgeom * eta * L ^ Dgeom)
         let Q := centeredCube z r hr
         let closedQ := closedCube z r hr
         ((∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
             0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
             ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
             ∀ b u : weakSobolevGraph Q,
               ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
               SolvesDirichlet aSource F b u →
               ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
                 ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
                 let cell := fun i => centeredCube (centers i) (sides i) (hside i)
                 ∃ hle : ∀ i, cell i ≤ Q,
                   (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
                     (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
                   Pairwise (fun i j =>
                     Disjoint (cell i : Set (SpatialCoordinates d))
                       (cell j : Set (SpatialCoordinates d))) ∧
                   ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
                     (Q : Set (SpatialCoordinates d))) ∧
                   ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
                     ∀ v : killedSobolevGraph (cell i),
                       ‖(v : SobolevData (cell i)).1‖ ≤
                         K * ‖@subspaceGradient d (cell i)
                           (killedSobolevGraph (cell i)) v‖,
                     ∃ U : SpatialCoordinates d → ℝ,
                       ContinuousOn U closedQ ∧
                       (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                         =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                       (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                         ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                           |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
                     (∑ i : Fin ncell,
                       @dirichletResponse d (cell i)
                         (@killedResponseSpace d (cell i) (hPcell i))
                         (positiveCoefficientRestrict (hle i) aTarget)
                         ⟨sobolevDataRestrict (hle i) u.val,
                           sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
                       factor * sobolevCoefficientForm aSource u.val u.val +
                         err * (Kf + c2Norm closedQ phi) ^ 2) ∧
           (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
             0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
             (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
             ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
             ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
               ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
               let cell := fun i => centeredCube (centers i) (sides i) (hside i)
               ∃ hle : ∀ i, cell i ≤ Q,
                 (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
                   (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
                 Pairwise (fun i j =>
                   Disjoint (cell i : Set (SpatialCoordinates d))
                     (cell j : Set (SpatialCoordinates d))) ∧
                 ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
                   (Q : Set (SpatialCoordinates d))) ∧
                 ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
                   ∀ v : killedSobolevGraph (cell i),
                     ‖(v : SobolevData (cell i)).1‖ ≤
                       K * ‖@subspaceGradient d (cell i)
                         (killedSobolevGraph (cell i)) v‖,
                   ∃ U : SpatialCoordinates d → ℝ,
                     ContinuousOn U closedQ ∧
                     (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                       =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                     (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                       ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                         |U x - U y| ≤ (err / 4) * Kf) ∧
                   (∑ i : Fin ncell,
                     @dirichletResponse d (cell i)
                       (@killedResponseSpace d (cell i) (hPcell i))
                       (positiveCoefficientRestrict (hle i) aTarget)
                       ⟨sobolevDataRestrict (hle i) u.val,
                         sobolevDataRestrict_mem_weak (hle i)
                           ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
                     factor * sobolevCoefficientForm aSource u.val u.val +
                       err * Kf ^ 2))) :=
  aux_lem_finite_source_comparison_cells_assemble d hd E P X W Cp Sf D theta htheta

end Paper
