import SubdiffusiveProcess.Paper.inputs_Sf_overlap_gap
import SubdiffusiveProcess.Paper.inputs_Sf_physical_gagliardo
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
import Homogenization.Sobolev.Fractional.ExactOverlapScalarComparison
import Homogenization.Sobolev.Fractional.GagliardoLeBesov
import SubdiffusiveProcess.Lane4.CubeDilation
import Homogenization.Besov.Negative.ExactFiniteBridge

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

private theorem aux_inputs_Sf_besov_embedding_pullback_memLp
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    MemLp (fun x : SpatialCoordinates d => v (fun i => z i + r * x i))
      (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  let Q := Homogenization.originCube d 0
  have hQc : Homogenization.cubeCenter Q = (0 : SpatialCoordinates d) := by
    funext i
    simp [Q, Homogenization.cubeCenter, Homogenization.originCube]
  have hQr : Homogenization.cubeScaleFactor Q = 1 := by
    simp [Q, Homogenization.cubeScaleFactor, Homogenization.originCube]
  have hQpos : 0 < Homogenization.cubeScaleFactor Q := by rw [hQr]; norm_num
  have hμQ : Homogenization.normalizedCubeMeasure Q =
      volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) := by
    have hrest := SubdiffusiveProcess.centeredCube_restrict_volume_eq_cubeMeasure Q hQpos
    have hrest' : volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) =
        Homogenization.cubeMeasure Q := by
      simpa only [hQc, hQr] using hrest
    have hvol : Homogenization.cubeVolume Q = 1 := by
      rw [Homogenization.cubeVolume_eq_scaleFactor_pow, hQr]
      simp
    calc
      Homogenization.normalizedCubeMeasure Q =
          ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹) •
            Homogenization.cubeMeasure Q := rfl
      _ = Homogenization.cubeMeasure Q := by rw [hvol]; simp
      _ = volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) :=
        hrest'.symm
  let μ₀ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))
  let μr : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let c : ℝ≥0∞ := ENNReal.ofReal |(r ^ d)⁻¹|
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    SubdiffusiveProcess.Lane4.cubeDilation z 0 r
  have hmap : Measure.map T μ₀ = c • μr := by
    simpa only [T, μ₀, μr, c] using
      SubdiffusiveProcess.Lane4.map_cubeDilation_restrict z 0 hr (by norm_num)
  have hpres : MeasurePreserving T μ₀ (c • μr) :=
    ⟨(SubdiffusiveProcess.Lane4.continuous_cubeDilation z 0 r).measurable, hmap⟩
  have hvscaled : MemLp (fun x : SpatialCoordinates d => (v x : ℝ))
      (2 : ℝ≥0∞) (c • μr) := by
    exact (Lp.memLp v).smul_measure hc
  have hpull : MemLp (fun x : SpatialCoordinates d => (v (T x) : ℝ))
      (2 : ℝ≥0∞) μ₀ := hvscaled.comp_measurePreserving hpres
  rw [hμQ]
  have hfun : (fun x : SpatialCoordinates d => (v (T x) : ℝ)) =
      (fun x => v (fun i => z i + r * x i)) := by
    funext x
    congr 1
    funext i
    simp [T, SubdiffusiveProcess.Lane4.cubeDilation]
  simpa only [μ₀, hfun] using hpull

theorem inputs_Sf_besov_embedding (d : ℕ) (hd : 2 ≤ d)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ v : DomainL2 (centeredCube z r hr),
      (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
          (fun x => v (fun i : Fin d => z i + r * x i))
          (inputs_poincare_positive_integrable d hd z r hr v) j) < ⊤ →
      cubeFractionalSqNorm hd z r hr threeQuarterOrder v ≤
        C * ((r ^ (-(1 - s)) * (iSup fun j : ℕ =>
          Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
            (fun x => v (fun i : Fin d => z i + r * x i))
            (inputs_poincare_positive_integrable d hd z r hr v) j).toReal) ^ 2 +
          ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  letI : NeZero d := ⟨by omega⟩
  let gap : ℝ := 1 - Real.rpow 3 (-2 * ((1 / 4 : ℝ) - s))
  have hgap : 0 < gap := by
    dsimp [gap]
    have h : Real.rpow 3 (-2 * ((1 / 4 : ℝ) - s)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hs.2])
    exact sub_pos.mpr h
  let B : ℝ := ((Homogenization.Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)).toReal
  let D : ℝ := B / gap
  have hD : 0 ≤ D := div_nonneg ENNReal.toReal_nonneg hgap.le
  let C : ℝ := D + 1
  have hC : 0 < C := by dsimp [C]; linarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro z r hr hrle v hfinite
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let u : SpatialCoordinates d → ℝ := fun x => v (fun i => z i + r * x i)
  let hu := inputs_poincare_positive_integrable d hd z r hr v
  let M : ℝ := (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q
    (1 - s) 2 u hu j).toReal
  have hmem := aux_inputs_Sf_besov_embedding_pullback_memLp d z r hr v
  have humeas : Measurable u := ((Lp.stronglyMeasurable v).measurable).comp (by fun_prop)
  have hAlpha := inputs_Sf_overlap_gap d s hs u hu hmem hfinite
  have hG := Homogenization.gagliardo_sq_le_exactOverlapScalarSeminormTwo
    (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1) Q u hu humeas hmem
  have hphys := inputs_Sf_physical_gagliardo d hd z r hr v
  let factor : ℝ := (3 / 4 : ℝ) * r ^ (-(3 / 2) : ℝ)
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  have hfrac : 0 ≤ M ^ 2 / gap := div_nonneg (sq_nonneg M) hgap.le
  have hchain :
      (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v)) ^ 2 ≤
        ENNReal.ofReal factor *
          ((Homogenization.Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
            ENNReal.ofReal (M ^ 2 / gap)) := by
    exact hphys.trans (mul_le_mul_left' (hG.trans
      (mul_le_mul_left' hAlpha _)) _)
  have htop : ENNReal.ofReal factor *
      ((Homogenization.Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        ENNReal.ofReal (M ^ 2 / gap)) ≠ ⊤ := by
    unfold Homogenization.Gagliardo.gagliardoBesovLowerConstant
    finiteness
  have hreal := ENNReal.toReal_mono htop hchain
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfactor, ENNReal.toReal_ofReal hfrac] at hreal
  have hscale : factor ≤ (r ^ (-(1 - s))) ^ 2 := by
    have hpow : r ^ (-(3 / 2) : ℝ) ≤ r ^ (-(1 - s) * 2) :=
      Real.rpow_le_rpow_of_exponent_ge hr hrle (by linarith [hs.2])
    have heq : (r ^ (-(1 - s))) ^ 2 = r ^ (-(1 - s) * 2) := by
      rw [Real.rpow_mul hr.le, Real.rpow_two]
    rw [heq]
    dsimp [factor]
    nlinarith [Real.rpow_nonneg hr.le (-(3 / 2) : ℝ)]
  have hseminorm :
      (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => v)).toReal ^ 2 ≤ C * (r ^ (-(1 - s)) * M) ^ 2 := by
    calc
      _ ≤ factor * (B * (M ^ 2 / gap)) := hreal
      _ ≤ (r ^ (-(1 - s))) ^ 2 * (B * (M ^ 2 / gap)) :=
        mul_le_mul_of_nonneg_right hscale (mul_nonneg ENNReal.toReal_nonneg hfrac)
      _ = D * (r ^ (-(1 - s)) * M) ^ 2 := by dsimp [D]; ring
      _ ≤ C * (r ^ (-(1 - s)) * M) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp [C]
        linarith
  have hleft : cubeFractionalSqNorm hd z r hr threeQuarterOrder v =
      ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => v)).toReal) ^ 2 +
        ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    simp [SubdiffusiveProcess.Lane4.cubeFractionalSqNorm,
      SubdiffusiveProcess.Lane4.cubeFractionalVecSqNorm,
      SubdiffusiveProcess.Lane4.cubeFractionalVecSeminormSq]
  rw [hleft]
  have hL : 0 ≤ ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by positivity
  have hLmul := mul_le_mul_of_nonneg_right hC1 hL
  change _ ≤ C * ((r ^ (-(1 - s)) * M) ^ 2 + _)
  nlinarith [hseminorm]

end Paper

