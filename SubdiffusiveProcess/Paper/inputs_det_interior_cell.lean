module

public import SubdiffusiveProcess.Paper.inputs_det_interior_window
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorScaleGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem inputs_det_interior_cell (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ K : ℝ, 0 < K ∧
      ∀ (s : ℝ) (_hs : 0 < s) (_hsle : s ≤ (1 / 4 : ℝ))
        (m n : ℕ), n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
        (a0 : ℝ), 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ truncatedCube d m ((n : ℤ) - 1) x,
        openCubeAtScale y ((n : ℤ) - 3) ⊆ cube d m →
      let U := truncatedCube d m n x;
      normalizedSetAverage (truncatedCube d m ((n : ℤ) - 4) y)
        (fun q => a q * vecNormSq (u.grad q)) ≤
      K *
          (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun q => u.toFun q - averageOn U u.toFun) ^ 2 +
           s ^ (-12 : ℝ) * a0⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2)) := by
  intro Cerr hCerr
  obtain ⟨C, B, hC, hB, hwin⟩ := inputs_det_interior_window d hd Cerr hCerr
  let P : ℝ := (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ)
  let Kparent : ℝ := 81 * B * (9 : ℝ) ^ d
  let Ksource : ℝ := B *
    ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 * (9 : ℝ) ^ d)
  let K : ℝ := (81 : ℝ) ^ d * P * max Kparent Ksource
  have hmaxC : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hKparent : 0 < Kparent := by
    dsimp [Kparent]
    positivity
  have hKsource : 0 < Ksource := by
    dsimp [Ksource]
    exact mul_pos hB (mul_pos
      (mul_pos (by positivity) (sq_pos_of_pos (caccioppoliExactDatumConstant_pos d)))
      (by positivity))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro s hs hsle m n hnm z hz x hx a data a0 ha0 herr hbd u g hweak hg y hy hpatch U
  have hbase := hwin s hs hsle m n hnm z hz x hx a data a0 ha0 herr hbd u g hweak hg y hy hpatch
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre y (m : ℤ) k
  let Q : Homogenization.TriadicCube d := originCube d k
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  have hratio := volume_ratio_truncatedCube_translated_predTwo_le
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (c := c) hxDomain (by omega)
  have hratio0 : 0 ≤ (volume U).toReal / (volume (translatedCube d k c)).toReal := by
    positivity
  have hG : 0 ≤ (fractionalSeminormOn U s g).toReal := ENNReal.toReal_nonneg
  have hparent := projected_parent_factor_le
    (d := d) (n := n) hB.le ha0.le hratio
    (X := normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun))
  have hsource := projected_source_factor_le
    (d := d) (n := n) hs (caccioppoliExactDatumConstant_pos d).le hratio0 hratio hG
  have hfirst :
      B * a0 * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 ≤
        Kparent *
          (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) := by
    dsimp [U] at hparent
    dsimp [U, k, Kparent]
    simpa only [mul_assoc] using hparent
  have hsecond :
      Real.rpow (s / 2) (-11 : ℝ) * (B * a0⁻¹) *
          (caccioppoliExactDatumConstant d *
            cubeBesovScaleWeight (-s) Q *
            (Real.rpow s (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U s g).toReal))) ^ 2 ≤
        Ksource *
          (Real.rpow s (-12 : ℝ) * a0⁻¹ *
            Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2) := by
    rw [show cubeBesovScaleWeight (-s) Q =
        Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) by
      simpa [Q, k] using cubeBesovScaleWeight_neg_origin_predTwo (d := d) s n]
    have hm := mul_le_mul_of_nonneg_left hsource
      (mul_nonneg hB.le (inv_nonneg.mpr ha0.le))
    calc
      _ = (B * a0⁻¹) *
          (Real.rpow (s / 2) (-11 : ℝ) *
            (caccioppoliExactDatumConstant d *
              Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) *
              (Real.rpow s (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U s g).toReal))) ^ 2) := by ring
      _ ≤ (B * a0⁻¹) *
          ((2 : ℝ) ^ (11 : ℕ) * caccioppoliExactDatumConstant d ^ 2 *
            (9 : ℝ) ^ d * Real.rpow s (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2) := hm
      _ = Ksource *
          (Real.rpow s (-12 : ℝ) * a0⁻¹ *
            Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2) := by
        dsimp [Ksource]
        ring
  have hA0 : 0 ≤ a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
      normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 := by
    positivity
  have hD0 : 0 ≤ Real.rpow s (-12 : ℝ) * a0⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s g).toReal ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr ha0.le))
      (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hsum :
      B * a0 * Real.rpow (3 : ℝ)
            (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
          ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
          normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
        Real.rpow (s / 2) (-11 : ℝ) * (B * a0⁻¹) *
          (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s) Q *
            (Real.rpow s (-(1 / 2 : ℝ)) *
              (Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U s g).toReal))) ^ 2 ≤
        max Kparent Ksource *
          (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
            Real.rpow s (-12 : ℝ) * a0⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
              (fractionalSeminormOn U s g).toReal ^ 2) := by
    calc
      _ ≤ Kparent *
            (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
              normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) ^ 2) +
          Ksource *
            (Real.rpow s (-12 : ℝ) * a0⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
              (fractionalSeminormOn U s g).toReal ^ 2) :=
        add_le_add hfirst hsecond
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right (le_max_left Kparent Ksource) hA0
        have h2 := mul_le_mul_of_nonneg_right (le_max_right Kparent Ksource) hD0
        linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hP.le
  have hout := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hidx : (n : ℤ) - 2 - 2 = (n : ℤ) - 4 := by ring
  refine le_trans (by simpa only [hidx] using hbase) (le_trans hout (le_of_eq ?_))
  dsimp only [K]
  simp only [Real.rpow_eq_pow]
  ring

end SubdiffusiveProcess.Paper
