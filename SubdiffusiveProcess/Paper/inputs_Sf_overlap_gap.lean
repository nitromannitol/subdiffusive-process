module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import Homogenization.Sobolev.Fractional.ExactOverlapScalarComparison
public import Homogenization.Sobolev.Fractional.GagliardoLeBesov
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import Homogenization.Besov.Negative.ExactFiniteBridge

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_inputs_Sf_overlap_gap_depth_bound
    (d : ℕ) (s : ℝ) (_hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (u : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) u)
    (hmem : MemLp u (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)))
    (hM : (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
      (Homogenization.originCube d 0) (1 - s) 2 u hu j) < ⊤) :
    ∀ j : ℕ,
      Homogenization.cubeBesovOverlapDepthSeminorm (Homogenization.originCube d 0)
        (3 / 4) (2 : ℝ≥0∞) u j ≤
        Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
          (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
            (Homogenization.originCube d 0) (1 - s) 2 u hu j).toReal := by
  intro j
  let Q := Homogenization.originCube d 0
  have hQr : Homogenization.cubeScaleFactor Q = 1 := by simp [Q]
  have hmem' : MemLp u (ENNReal.ofReal (2 : ℝ))
      (Homogenization.normalizedCubeMeasure Q) := by simpa using hmem
  have hcan := Homogenization.exactDualOverlapIntegrable Q 2 (by norm_num) hmem'
  have hchange : Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j =
      Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hcan j :=
    Homogenization.exactOverlapDepthTerm_congr_ae Q (1 - s) 2 hu hcan
      (fun _ _ _ => Filter.EventuallyEq.rfl) j
  have hbridge := Homogenization.exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm
    Q (1 - s) 2 (by norm_num) u hmem' j
  have hterm : Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j =
      ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
        (2 : ℝ≥0∞) u j) := by
    calc
      Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j =
      Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hcan j := hchange
      _ = ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
          (2 : ℝ≥0∞) u j) := by simpa using hbridge
  have hle : ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
      (2 : ℝ≥0∞) u j) ≤
      (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j) := by
    rw [← hterm]
    exact le_iSup (fun j : ℕ => Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j) j
  have hbase_nonneg := Homogenization.cubeBesovOverlapDepthSeminorm_nonneg Q (1 - s)
    (2 : ℝ≥0∞) u j
  have hbase : Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
      (2 : ℝ≥0∞) u j ≤
        (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q (1 - s) 2 u hu j).toReal := by
    calc
      Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) u j =
          (ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
            (2 : ℝ≥0∞) u j)).toReal := by rw [ENNReal.toReal_ofReal hbase_nonneg]
      _ ≤ (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q
          (1 - s) 2 u hu j).toReal := ENNReal.toReal_mono hM.ne hle
  have hwt (a : ℝ) : Homogenization.cubeBesovOverlapDepthWeight Q a j =
      Real.rpow 3 (a * (j : ℝ)) := by
    rw [Homogenization.cubeBesovOverlapDepthWeight_eq_scaleWeight_mul_rpow]
    simp [Homogenization.cubeBesovScaleWeight, hQr]
  have hrel : Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
      (2 : ℝ≥0∞) u j =
      Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
        Homogenization.cubeBesovOverlapDepthSeminorm Q (1 - s)
          (2 : ℝ≥0∞) u j := by
    have hpow : Real.rpow 3 ((3 / 4 : ℝ) * (j : ℝ)) =
        Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
          Real.rpow 3 ((1 - s) * (j : ℝ)) := by
      calc
        Real.rpow 3 ((3 / 4 : ℝ) * (j : ℝ)) =
            Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ) + (1 - s) * (j : ℝ)) := by
              congr 1
              ring
        _ = Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
            Real.rpow 3 ((1 - s) * (j : ℝ)) := by
              exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
    unfold Homogenization.cubeBesovOverlapDepthSeminorm
    rw [hwt (3 / 4), hwt (1 - s)]
    calc
      Real.rpow 3 ((3 / 4 : ℝ) * (j : ℝ)) *
          Homogenization.cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) u j ^
            (1 / (2 : ℝ≥0∞).toReal) =
          (Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
            Real.rpow 3 ((1 - s) * (j : ℝ))) *
            Homogenization.cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) u j ^
              (1 / (2 : ℝ≥0∞).toReal) := by rw [hpow]
      _ = Real.rpow 3 (-((1 / 4 : ℝ) - s) * (j : ℝ)) *
          (Real.rpow 3 ((1 - s) * (j : ℝ)) *
            Homogenization.cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) u j ^
              (1 / (2 : ℝ≥0∞).toReal)) := by ring
  rw [hrel]
  exact mul_le_mul_of_nonneg_left hbase
    (Real.rpow_nonneg (by norm_num) _)

private theorem aux_inputs_Sf_overlap_gap_partial_bound
    (d : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (u : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) u)
    (hmem : MemLp u (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)))
    (hM : (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
      (Homogenization.originCube d 0) (1 - s) 2 u hu j) < ⊤)
    (N : ℕ) :
    (Homogenization.cubeBesovOverlapPartialSeminorm
      (Homogenization.originCube d 0) (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2 ≤
      ((iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
        (Homogenization.originCube d 0) (1 - s) 2 u hu j).toReal) ^ 2 /
        (1 - Real.rpow 3 (-2 * ((1 / 4 : ℝ) - s))) := by
  let Q := Homogenization.originCube d 0
  let M := (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
    Q (1 - s) 2 u hu j).toReal
  let δ := (1 / 4 : ℝ) - s
  let q := Real.rpow 3 (-2 * δ)
  have hδ : 0 < δ := by dsimp [δ]; linarith [hs.2]
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) _
  have hq_lt : q < 1 := by
    dsimp [q, δ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hs.2])
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hdepth := aux_inputs_Sf_overlap_gap_depth_bound d s hs u hu hmem hM
  have hgeom (j : ℕ) :
      (Real.rpow 3 (-δ * (j : ℝ))) ^ 2 = q ^ j := by
    dsimp [q]
    calc
      (Real.rpow 3 (-δ * (j : ℝ))) ^ 2 =
          Real.rpow 3 ((-δ * (j : ℝ)) * 2) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = Real.rpow 3 ((-2 * δ) * (j : ℝ)) := by congr 1 ; ring
      _ = (Real.rpow 3 (-2 * δ)) ^ j := by
            symm
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
  have hpartial :
      (Homogenization.cubeBesovOverlapPartialSeminorm Q (3 / 4)
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2 =
      ∑ j ∈ Finset.range (N + 1),
        (Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
          (2 : ℝ≥0∞) u j) ^ 2 := by
    have h := Homogenization.Gagliardo.ofReal_partialSeminorm_rpow_eq Q (3 / 4)
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) N u
    have ht := congrArg ENNReal.toReal h
    have hBnonneg (j : ℕ) := Homogenization.cubeBesovOverlapDepthSeminorm_nonneg Q
      (3 / 4) (2 : ℝ≥0∞) u j
    have hpartial_nonneg := Homogenization.cubeBesovOverlapPartialSeminorm_nonneg Q
      (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u
    have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [htwo] at ht
    rw [ENNReal.toReal_sum (by
      intro j hj
      exact ENNReal.ofReal_ne_top)] at ht
    rw [Real.rpow_two] at ht
    have hsumreal :
        (∑ j ∈ Finset.range (N + 1),
          (ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
            (2 : ℝ≥0∞) u j ^ 2)).toReal) =
        ∑ j ∈ Finset.range (N + 1),
          (Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
            (2 : ℝ≥0∞) u j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ENNReal.toReal_ofReal (sq_nonneg _)
    calc
      (Homogenization.cubeBesovOverlapPartialSeminorm Q (3 / 4)
          (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2 =
          (ENNReal.ofReal (Homogenization.cubeBesovOverlapPartialSeminorm Q
            (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u ^ 2)).toReal := by
              exact (ENNReal.toReal_ofReal (sq_nonneg _)).symm
      _ = ∑ j ∈ Finset.range (N + 1),
          (ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q
            (3 / 4) (2 : ℝ≥0∞) u j ^ 2)).toReal := ht
      _ = ∑ j ∈ Finset.range (N + 1),
          (Homogenization.cubeBesovOverlapDepthSeminorm Q
            (3 / 4) (2 : ℝ≥0∞) u j) ^ 2 := by
              simpa only [Real.rpow_two] using hsumreal
  have hsumle :
      (∑ j ∈ Finset.range (N + 1),
        (Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
          (2 : ℝ≥0∞) u j) ^ 2) ≤
      ∑ j ∈ Finset.range (N + 1),
        (Real.rpow 3 (-δ * (j : ℝ)) * M) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hnonneg := Homogenization.cubeBesovOverlapDepthSeminorm_nonneg Q (3 / 4)
      (2 : ℝ≥0∞) u j
    have hfactor : 0 ≤ Real.rpow 3 (-δ * (j : ℝ)) * M :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hM_nonneg
    nlinarith [hdepth j]
  have hsumgeom :
      (∑ j ∈ Finset.range (N + 1), q ^ j) ≤ (1 - q)⁻¹ := by
    have hsum := summable_geometric_of_lt_one hq_nonneg hq_lt
    calc
      (∑ j ∈ Finset.range (N + 1), q ^ j) ≤ ∑' j : ℕ, q ^ j :=
        hsum.sum_le_tsum _ (fun j _ => pow_nonneg hq_nonneg _)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq_nonneg hq_lt
  calc
    (Homogenization.cubeBesovOverlapPartialSeminorm Q (3 / 4)
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2 =
        ∑ j ∈ Finset.range (N + 1),
          (Homogenization.cubeBesovOverlapDepthSeminorm Q (3 / 4)
            (2 : ℝ≥0∞) u j) ^ 2 := hpartial
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          (Real.rpow 3 (-δ * (j : ℝ)) * M) ^ 2 := hsumle
    _ = M ^ 2 * ∑ j ∈ Finset.range (N + 1), q ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_pow, hgeom j]
          ring
    _ ≤ M ^ 2 * (1 - q)⁻¹ :=
          mul_le_mul_of_nonneg_left hsumgeom (sq_nonneg M)

theorem inputs_Sf_overlap_gap
    (d : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (u : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) u)
    (hmem : MemLp u (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)))
    (hM : (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
      (Homogenization.originCube d 0) (1 - s) 2 u hu j) < ⊤) :
      (Homogenization.exactOverlapFiniteSeminorm
      (Homogenization.exactOverlapScalarTwoParameters
        (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1))
      (Homogenization.originCube d 0) u hu) ^ 2 ≤
      ENNReal.ofReal (((iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
        (Homogenization.originCube d 0) (1 - s) 2 u hu j).toReal) ^ 2 /
        (1 - Real.rpow 3 (-2 * ((1 / 4 : ℝ) - s)))) := by
  let α : Set.Ioo (0 : ℝ) 1 := ⟨3 / 4, by norm_num, by norm_num⟩
  rw [Homogenization.exactOverlapScalarSeminormTwo_sq_eq_iSup_partialSeminorm α
    (Homogenization.originCube d 0) u hu hmem]
  apply iSup_le
  intro N
  have hpartial := aux_inputs_Sf_overlap_gap_partial_bound d s hs u hu hmem hM N
  have hpartial_nonneg := Homogenization.cubeBesovOverlapPartialSeminorm_nonneg
    (Homogenization.originCube d 0) (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u
  have hpow := ENNReal.ofReal_pow hpartial_nonneg 2
  simpa [α] using (calc
    (ENNReal.ofReal (Homogenization.cubeBesovOverlapPartialSeminorm
        (Homogenization.originCube d 0) (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)) ^ 2 =
        ENNReal.ofReal ((Homogenization.cubeBesovOverlapPartialSeminorm
          (Homogenization.originCube d 0) (3 / 4) (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u) ^ 2) := hpow.symm
    _ ≤ ENNReal.ofReal (((iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm
          (Homogenization.originCube d 0) (1 - s) 2 u hu j).toReal) ^ 2 /
          (1 - Real.rpow 3 (-2 * ((1 / 4 : ℝ) - s)))) :=
        ENNReal.ofReal_le_ofReal hpartial)


end SubdiffusiveProcess.Paper

