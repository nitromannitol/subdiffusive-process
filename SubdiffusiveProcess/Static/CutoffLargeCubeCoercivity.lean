module

public import SubdiffusiveProcess.Static.CutoffChartCoercivity
public import SubdiffusiveProcess.Static.CoercivityCoverAssembly
public import SubdiffusiveProcess.Static.ZeroExtensionCoercivity

@[expose] public section

/-! # Coercivity on bounded real cubes above a fixed microscopic scale -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_large_cube_coercivity (d J : ℕ) [NeZero d]
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (ht : ((3 : ℝ) ^ J)⁻¹ < a)
    (hb : b ≤ (3 : ℝ) ^ J) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 B : ℝ, 0 < δ0 ∧ 0 < B ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∀ L m : ℕ, L ≤ m → J ≤ m → ∀ s : ℝ, a ≤ s → s ≤ b → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
          ∀ᵐ ω ∂M.P.toMeasure,
            cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) 0 s (K ω) := by
  classical
  let t : ℝ := ((3 : ℝ) ^ J)⁻¹
  let T : ℝ := (3 : ℝ) ^ J
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have hT0 : 0 < T := by dsimp only [T]; positivity
  obtain ⟨δ0, B0, hδ0, hB0, hunit⟩ := exists_uniform_bounded_gap_coercivity d J q hq
  let Bs := 1 + B0 * affineCoercivityPrice d t
  let Bl := 1 + B0 * affineCoercivityPrice d T
  let N : ℝ := (2 * b / t + 2) ^ d
  let F : ℝ := farPairPrice d b t
  let B : ℝ := N * Bs + F + 1 + Bl
  have hBs : 0 < Bs := by dsimp only [Bs]; have := affineCoercivityPrice_pos d ht0; positivity
  have hBl : 0 < Bl := by dsimp only [Bl]; have := affineCoercivityPrice_pos d hT0; positivity
  refine ⟨δ0, B, hδ0, ?_, ?_⟩
  · dsimp only [B, N, F, farPairPrice]
    have hb0 : 0 < b := ha.trans_le hab
    positivity
  intro M hM L m hLm hJm s has hsb z
  have hs : 0 < s := ha.trans_le has
  have hb0 : 0 < b := hs.trans_le hsb
  obtain ⟨Y, hcard, hsub, hcov⟩ := exists_cube_nearPair_cover s t ht0 (ht.trans_le has)
  have hscale : (3 : ℝ) ^ m * t = (3 : ℝ) ^ (m - J) := by
    dsimp only [t]
    exact (pow_sub₀ (3 : ℝ) (by norm_num) hJm).symm
  have hg : L - (m - J) ≤ J := by omega
  have hsmall : ∀ y : Vec d, ∃ K : PotentialSample d → ℝ, Measurable K ∧
      (∀ ω, 1 ≤ K ω) ∧ eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal Bs ∧
      ∀ᵐ ω ∂M.P.toMeasure,
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) y t (K ω) :=
    fun y => exists_cutoff_chart_coercivity M hq hB0 t ht0 hscale z y
      (hunit M hM L (m - J) hg)
  choose W hW hW1 hWn hWc using hsmall
  have hscaleT : (3 : ℝ) ^ m * T = (3 : ℝ) ^ (m + J) := by
    dsimp only [T]
    rw [pow_add]
  obtain ⟨V, hV, hV1, hVn, hVc⟩ := exists_cutoff_chart_coercivity M hq hB0 T hT0
    hscaleT z 0 (hunit M hM L (m + J) (by omega))
  let S : PotentialSample d → ℝ := fun ω => ∑ y ∈ Y, W y ω
  let K : PotentialSample d → ℝ := fun ω => S ω + farPairPrice d s t + 1 + V ω
  have hS : Measurable S := Finset.measurable_sum Y (fun y _ => hW y)
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun y _ => zero_le_one.trans (hW1 y ω)
  have hF0 : 0 ≤ farPairPrice d s t := by unfold farPairPrice; positivity
  have hFbound : farPairPrice d s t ≤ F := by
    dsimp only [F, farPairPrice]
    gcongr
  have hN : (Y.card : ℝ) ≤ N := by
    refine hcard.trans ?_
    dsimp only [N]
    gcongr
  have hSn : eLpNorm S (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal (N * Bs) := by
    have heq : S = ∑ y ∈ Y, W y := by funext ω; simp [S]
    rw [heq]
    refine (eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    refine (Finset.sum_le_sum fun y _ => hWn y).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hN hBs.le)
  have hK : Measurable K := ((hS.add_const _).add_const 1).add hV
  have hK1 : ∀ ω, 1 ≤ K ω := fun ω => by dsimp only [K]; linarith [hS0 ω, hV1 ω]
  refine ⟨K, hK, hK1, ?_, ?_⟩
  · have hSn' : eLpNorm (fun ω => S ω + farPairPrice d s t) (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (N * Bs + F) := by
      refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
      rw [coercivity_norm_const M.P.toMeasure (zero_lt_one.trans_le hq) hF0]
      refine (add_le_add hSn (ENNReal.ofReal_le_ofReal hFbound)).trans_eq ?_
      rw [ENNReal.ofReal_add (by dsimp only [N]; positivity) (by dsimp only [F, farPairPrice]; positivity)]
    have hS1 : eLpNorm (fun ω => S ω + farPairPrice d s t + 1) (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (N * Bs + F + 1) := by
      refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
      rw [coercivity_norm_const M.P.toMeasure (zero_lt_one.trans_le hq) zero_le_one]
      refine (add_le_add hSn' le_rfl).trans_eq ?_
      rw [ENNReal.ofReal_add (by dsimp only [N, F, farPairPrice]; positivity) zero_le_one]
    refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    refine (add_le_add hS1 hVn).trans_eq ?_
    exact (ENNReal.ofReal_add (by dsimp only [N, F, farPairPrice]; positivity) hBl.le).symm
  · have hall : ∀ᵐ ω ∂M.P.toMeasure, ∀ y : {y // y ∈ Y},
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) y.1 t (W y.1 ω) :=
      ae_all_iff.mpr fun y => hWc y.1
    filter_upwards [hall, hVc] with ω hω hωV
    have hh1 := H1_coercivity_of_nearPair_cover s t hs ht0
      (finiteCoercivityCoefficient M L m z ω) Y (fun y => W y ω)
      (fun y _ => zero_le_one.trans (hW1 y ω)) hsub hcov (fun y hy => (hω ⟨y, hy⟩).1)
    have hh10 := H10_coercivity_of_superset measurableSet_ball Metric.isOpen_ball
      (Metric.ball_subset_ball (by change s / 2 ≤ (3 : ℝ) ^ J / 2; linarith : s / 2 ≤ T / 2))
      (finiteCoercivityCoefficient M L m z ω) (ENNReal.ofReal (V ω)) hωV.2
    constructor
    · intro H
      exact (hh1 H).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (by dsimp only [K, S]; linarith [hV1 ω])) _)
    · intro H
      exact (hh10 H).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (by dsimp only [K]; linarith [hS0 ω])) _)

end SubdiffusiveProcess.Static
