module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# Hölder-branch predicates of the sourced stopping partition (Dirichlet and mean-zero Neumann)

The Hölder predicates `holDir` / `holNeu` of `lem_finite_source_comparison_cells` with an arbitrary
exponent, together with the projection of a `prop_growth`-shaped output (`IsHolderOn` +
`cAlphaNorm`) to the sup-metric bound.  Shared by `fscc_zero_holder_dirichlet`,
`fscc_char_holder_dirichlet`, `fscc_char_holder_neumann` and `fscc_zero_holder_neumann`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- Hölder representative of every Dirichlet source solution, constant `Kh (‖F‖ + ‖φ‖_{C²})`
(the predicate `aux_lem_finite_source_comparison_cells_holDir` of `lem_finite_source_comparison_cells`,
with an arbitrary exponent). -/
def aux_fscc_holder_predicates_holDir (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
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

theorem aux_fscc_holder_predicates_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
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

theorem aux_fscc_holder_predicates_holderSeminorm_nonneg {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) :
    0 ≤ holderSeminorm alpha S U := by
  unfold holderSeminorm holderRatioSet
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, y, _, _, rfl⟩
  positivity

theorem aux_fscc_holder_predicates_holderSeminorm_le {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) :
    holderSeminorm alpha S U ≤ cAlphaNorm alpha S U := by
  unfold cAlphaNorm
  have : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} :=
    Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; positivity)
  linarith

/-- `IsHolderOn` + `cAlphaNorm ≤ C` give `|U x - U y| ≤ (√d)^α C dist(x,y)^α`. -/
theorem aux_fscc_holder_predicates_holder_dist {d : ℕ}
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) (alpha C : ℝ)
    (halpha : 0 < alpha) (hH : IsHolderOn alpha S U) (hC : cAlphaNorm alpha S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤ Real.sqrt d ^ alpha * C * dist x y ^ alpha := by
  intro x hx y hy
  have hsemi : holderSeminorm alpha S U ≤ C :=
    (aux_fscc_holder_predicates_holderSeminorm_le _ _ _).trans hC
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
      exact Real.rpow_le_rpow hepos.le (aux_fscc_holder_predicates_euclid_le x y)
        halpha.le
    have hC0 : 0 ≤ C :=
      (aux_fscc_holder_predicates_holderSeminorm_nonneg _ _ _).trans hsemi
    calc |U x - U y| ≤ C * e ^ alpha := h1
      _ ≤ C * (Real.sqrt d ^ alpha * dist x y ^ alpha) := by gcongr
      _ = Real.sqrt d ^ alpha * C * dist x y ^ alpha := by ring

/-- A `prop_growth`-shaped Dirichlet output (first moments of `K` and, almost surely, a
`C^α` representative with `cAlphaNorm ≤ K (‖F‖ + ‖φ‖_{C²})`) gives the Hölder branch of the
predicate above for the coefficient family `cutoffPositiveCoefficient model Hused om J z hr`. -/
theorem fscc_holder_predicates {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (alpha : ℝ) (halpha : 0 < alpha)
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
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K J om * (Kf + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi)) :
    ∃ (K' : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
      (∀ J, MemLp (K' J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
      (∀ J, eLpNorm (K' J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal Cbank) ∧
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ,
        aux_fscc_holder_predicates_holDir d z r hr
          (cutoffPositiveCoefficient model Hused omega J z hr) alpha (K' J omega) := by
  set c0 : ℝ := Real.sqrt d ^ alpha with hc0
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
    have h := aux_fscc_holder_predicates_holder_dist _ U alpha _ halpha hUhol hUnorm x hx y hy
    calc |U x - U y| ≤ c0 * (K J omega * (Kf + c2Norm (closedCube z r hr) phi)) *
          dist x y ^ alpha := h
      _ = c0 * K J omega * (Kf + c2Norm (closedCube z r hr) phi) * dist x y ^ alpha := by ring

/-- Hölder representative of every mean-zero Neumann source solution, constant `Kh ‖F‖`
(the predicate `aux_lem_finite_source_comparison_cells_holNeu` of `lem_finite_source_comparison_cells`,
with an arbitrary exponent). -/
def aux_fscc_holder_predicates_holNeu (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
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

end Paper
