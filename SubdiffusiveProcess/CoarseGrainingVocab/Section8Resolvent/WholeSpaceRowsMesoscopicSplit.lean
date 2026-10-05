module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsBesovCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

private theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  unfold cubeScaleFactor
  positivity



private theorem cubeBesovOscillation_two_le_two_mul_cubeLpNorm_two'
    (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  unfold cubeBesovOscillation cubeFluctuation
  have hconst : MemLp (fun _ : Vec d => -cubeAverage Q u) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := MeasureTheory.memLp_const _
  have hadd :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q u) := by
    have hfun : (fun x => u x - cubeAverage Q u) =
        fun x => u x + (fun _ : Vec d => -cubeAverage Q u) x := by
      funext x; simp [sub_eq_add_neg]
    rw [hfun]
    exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) u (fun _ : Vec d => -cubeAverage Q u)
      hu hconst (by norm_num)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) u +
            cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q u) := hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) u + ‖cubeAverage Q u‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
            (c := -cubeAverage Q u) (by norm_num)]
          simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u + cubeLpNorm Q (2 : ℝ≥0∞) u := by
          gcongr
          exact norm_cubeAverage_le_cubeLpNorm_two Q u hu
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by ring

/--  transcription of the private
`Homogenization.Book.Ch01.Legacy.cubeBesovDepthAverage_two_le_four_mul_sq_cubeLpNorm_two`
(same file). -/
private theorem cubeBesovDepthAverage_two_le_four_mul_sq_cubeLpNorm_two'
    (Q : TriadicCube d) (u : Vec d → ℝ) (k : ℕ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k ≤
      4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
  have hpoint : ∀ R ∈ descendantsAtDepth Q k,
      (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ) ≤
        (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
    intro R hR
    have huR : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := k) hR hu
    have hosc := cubeBesovOscillation_two_le_two_mul_cubeLpNorm_two' R u huR
    have h0 : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
    have hsq : (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℕ) ≤
        (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by nlinarith
    simpa [Real.rpow_natCast] using hsq
  calc
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k
        ≤ descendantsAverage Q k
            (fun R => (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ)) := by
          unfold cubeBesovDepthAverage
          exact descendantsAverage_le_descendantsAverage Q k hpoint
    _ = descendantsAverage Q k
            (fun R => 4 * (cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ)) := by
          refine congrArg (descendantsAverage Q k) ?_
          funext R; ring
    _ = 4 * cubeL2ScalarDepthAverage Q u k := by
          rw [descendantsAverage_mul_left]; rfl
    _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
          rw [cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q u k hu]

/-- The `L²` branch of the depth split: at **every** depth the positive Besov
depth seminorm is bounded by the depth weight times the plain `L²` norm. -/
private theorem cubeBesovDepthSeminorm_two_le_depthWeight_mul_two_cubeLpNorm
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ) (k : ℕ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u k ≤
      cubeBesovDepthWeight Q s k * (2 * cubeLpNorm Q (2 : ℝ≥0∞) u) := by
  have hA := cubeBesovDepthAverage_two_le_four_mul_sq_cubeLpNorm_two' Q u k hu
  have hnn : 0 ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    have := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u; linarith
  have hsqrt : Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    refine Real.sqrt_le_sqrt hA |>.trans ?_
    rw [show (4 : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) =
      (2 * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) by ring]
    rw [Real.sqrt_sq hnn]
  have hrepr : (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) ^ (1 / (2 : ℝ≥0∞).toReal) =
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) := by
    simp [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]
  unfold cubeBesovDepthSeminorm
  rw [hrepr]
  exact mul_le_mul_of_nonneg_left hsqrt (cubeBesovDepthWeight_nonneg Q s k)

/-- The depth-weight factorisation `(ℓ 3^{-k})^{-c} = ℓ^{-c} (3^{-k})^{-c}`. -/
private theorem depthWeight_eq_mul (Q : TriadicCube d) (c : ℝ) (k : ℕ) :
    cubeBesovDepthWeight Q c k =
      (cubeScaleFactor Q) ^ (-c) * (((3 : ℝ) ^ k)⁻¹) ^ (-c) := by
  have hl : (0 : ℝ) ≤ cubeScaleFactor Q := (cubeScaleFactor_pos' Q).le
  have hr : (0 : ℝ) ≤ (((3 : ℝ) ^ k)⁻¹) := by positivity
  unfold cubeBesovDepthWeight
  rw [div_eq_mul_inv, Real.mul_rpow hl hr]

/-- The **scale-gap identity**: the depth seminorm at smoothness `s` is the depth
seminorm at smoothness `1 - s` times `(ℓ 3^{-k})^{1-2s}`.  This is the source of
the mesoscopic gain: the gradient branch is run at the *large* exponent `1 - s`
(the frozen coarse Poincaré is the negative norm at the *small* exponent `s`),
and the gap `1 - 2s > 0` is what makes fine depths cheap. -/
private theorem depthSeminorm_eq_gap_mul (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ)
    (k : ℕ) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v k =
      (cubeScaleFactor Q / (3 : ℝ) ^ k) ^ (1 - 2 * s) *
        cubeBesovDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) v k := by
  have hx : (0 : ℝ) < cubeScaleFactor Q / (3 : ℝ) ^ k := by
    have := cubeScaleFactor_pos' Q; positivity
  have hw : cubeBesovDepthWeight Q s k =
      (cubeScaleFactor Q / (3 : ℝ) ^ k) ^ (1 - 2 * s) *
        cubeBesovDepthWeight Q (1 - s) k := by
    unfold cubeBesovDepthWeight
    rw [← Real.rpow_add hx]
    ring_nf
  unfold cubeBesovDepthSeminorm
  rw [hw]; ring



theorem cutoffProduct_component_partialNormTop_le_mesoscopic_split
    [NeZero d] (Q : TriadicCube d) (s : ℝ) (M : ℕ)
    (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : 2 * s < 1)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) (i : Fin d) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M
        (fun x => (cubeFluctuation Q (fun y => u y) x • ξ x) i) ≤
      (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
        (beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) *
              ((Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                ∑ j : Fin d,
                  Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                    (fun x => u.grad x j))) +
          beta ^ (-(s / (1 - 2 * s))) *
            (cubeBesovScaleWeight s Q *
              (2 * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y))))) := by
  classical
  have hs1' : s < 1 := by linarith
  have hgap : (0 : ℝ) < 1 - 2 * s := by linarith
  set v : Vec d → ℝ := cubeFluctuation Q (fun x => u x) with hvdef
  set F : Vec d → Vec d := fun x => v x • ξ x with hFdef
  set L2 : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v with hL2def
  set Pg : ℝ :=
    (Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d,
        Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x j) with hPgdef
  set T : ℝ :=
    beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) +
      beta ^ (-(s / (1 - 2 * s))) * (cubeBesovScaleWeight s Q * (2 * L2)) with hTdef
  have hu : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q (fun x => u x)))
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa only [F, Pi.smul_apply] using! hv.smul (p := (2 : ℝ≥0∞)) (q := ∞) (r := (2 : ℝ≥0∞)) hξLp
  have hL2nn : 0 ≤ L2 := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
  -- the corridor at the *large* smoothness `1 - s`
  have hPg : cubeBesovPartialNormTop Q (1 - s) (2 : ℝ≥0∞) M v ≤ Pg := by
    have := Book.Ch01.Legacy.h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm
      Q (1 - s) M u (by linarith) (by linarith)
    simpa [Pg, v, sub_sub_cancel] using this
  have hPgnn : 0 ≤ Pg := by
    refine le_trans ?_ hPg
    exact cubeBesovPartialNormTop_nonneg Q (1 - s) (2 : ℝ≥0∞) M v
  have hbetaPow : (1 : ℝ) ≤ beta ^ (-(s / (1 - 2 * s))) := by
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbeta0 hbeta1 ?_
    have : 0 ≤ s / (1 - 2 * s) := le_of_lt (div_pos hs0 hgap)
    linarith
  have hweight_nn : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have hTnn : 0 ≤ T := by
    have h1 : 0 ≤ beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) := by
      have : (0 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) :=
        Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
      positivity
    have h2 : 0 ≤ beta ^ (-(s / (1 - 2 * s))) * (cubeBesovScaleWeight s Q * (2 * L2)) := by
      have : (0 : ℝ) ≤ beta ^ (-(s / (1 - 2 * s))) := by linarith
      positivity
    simpa [hTdef] using add_nonneg h1 h2
  -- the `L²` piece of the split dominates the plain `L²` term
  have hL2T : cubeBesovScaleWeight s Q * L2 ≤ T := by
    have h1 : cubeBesovScaleWeight s Q * L2 ≤
        beta ^ (-(s / (1 - 2 * s))) * (cubeBesovScaleWeight s Q * (2 * L2)) := by
      have hmul : cubeBesovScaleWeight s Q * L2 ≤ cubeBesovScaleWeight s Q * (2 * L2) := by
        nlinarith [hweight_nn, hL2nn]
      nlinarith [hweight_nn, hL2nn, hbetaPow,
        mul_nonneg hweight_nn (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL2nn)]
    have h2 : 0 ≤ beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) := by
      have : (0 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) :=
        Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
      positivity
    simpa [hTdef] using le_trans h1 (by linarith)
  -- branch bookkeeping at a single depth
  have hT2 : ∀ j ∈ Finset.range (M + 1),
      cubeBesovScaleWeight s Q * cubeBesovPositiveScalarDepthSeminorm Q s v j ≤ T := by
    intro j hj
    have hrewrite : cubeBesovScaleWeight s Q *
        cubeBesovPositiveScalarDepthSeminorm Q s v j =
          cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
      rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
      have hmul : cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
        simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
      calc cubeBesovScaleWeight s Q *
            (cubeBesovScaleWeight (-s) Q * cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j)
          = (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
              cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by ring
        _ = cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by rw [hmul]; ring
    rw [hrewrite]
    set r : ℝ := (((3 : ℝ) ^ j)⁻¹) with hrdef
    have hr0 : 0 < r := by positivity
    have hsplit : r ≤ beta ^ ((1 - 2 * s)⁻¹) ∨ beta ^ ((1 - 2 * s)⁻¹) < r := le_or_gt _ _
    rcases hsplit with hcase | hcase
    · -- coarse of the split: use the gradient branch, which is `beta`-small there
      have hgapPow : r ^ (1 - 2 * s) ≤ beta := by
        have h := Real.rpow_le_rpow hr0.le hcase hgap.le
        have hb : (beta ^ ((1 - 2 * s)⁻¹)) ^ (1 - 2 * s) = beta := by
          rw [← Real.rpow_mul hbeta0.le]
          rw [inv_mul_cancel₀ (ne_of_gt hgap), Real.rpow_one]
        rwa [hb] at h
      have hfac : (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (1 - 2 * s) =
          (cubeScaleFactor Q) ^ (1 - 2 * s) * r ^ (1 - 2 * s) := by
        rw [div_eq_mul_inv, Real.mul_rpow (cubeScaleFactor_pos' Q).le hr0.le]
      have hdepth1 : cubeBesovDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) v j ≤ Pg := by
        refine le_trans ?_ hPg
        refine le_trans ?_ (le_add_of_nonneg_right
          (mul_nonneg (cubeBesovScaleWeight_nonneg (1 - s) Q) (norm_nonneg _)))
        unfold cubeBesovPartialSeminormTop
        exact Finset.le_sup' (s := Finset.range (M + 1))
          (f := fun k => cubeBesovDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) v k) hj
      have hnnfac : (0 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) :=
        Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
      have hnnr : (0 : ℝ) ≤ r ^ (1 - 2 * s) := Real.rpow_nonneg hr0.le _
      have hdnn : 0 ≤ cubeBesovDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) v j := by
        unfold cubeBesovDepthSeminorm
        exact mul_nonneg (cubeBesovDepthWeight_nonneg Q (1 - s) j)
          (Real.rpow_nonneg (cubeBesovDepthAverage_nonneg Q (2 : ℝ≥0∞) v j) _)
      have hbound : cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j ≤
          beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) := by
        rw [depthSeminorm_eq_gap_mul Q s v j, hfac]
        calc (cubeScaleFactor Q) ^ (1 - 2 * s) * r ^ (1 - 2 * s) *
              cubeBesovDepthSeminorm Q (1 - s) (2 : ℝ≥0∞) v j
            ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) * r ^ (1 - 2 * s) * Pg := by
              exact mul_le_mul_of_nonneg_left hdepth1 (by positivity)
          _ ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) * beta * Pg := by
              have := mul_le_mul_of_nonneg_left hgapPow hnnfac
              nlinarith [hPgnn, hnnfac, hnnr]
          _ = beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) := by ring
      have hsecond : 0 ≤ beta ^ (-(s / (1 - 2 * s))) *
          (cubeBesovScaleWeight s Q * (2 * L2)) := by
        have : (0 : ℝ) ≤ beta ^ (-(s / (1 - 2 * s))) := by linarith
        positivity
      simpa [hTdef] using le_trans hbound (by linarith)
    · -- fine of the split: use the `L²` branch, whose weight is `beta^{-s/(1-2s)}`-bounded
      have hrpow : r ^ (-s) ≤ beta ^ (-(s / (1 - 2 * s))) := by
        have hbpos : (0 : ℝ) < beta ^ ((1 - 2 * s)⁻¹) := Real.rpow_pos_of_pos hbeta0 _
        have hle : (beta ^ ((1 - 2 * s)⁻¹)) ^ s ≤ r ^ s :=
          Real.rpow_le_rpow hbpos.le hcase.le hs0.le
        have h1 : r ^ (-s) = (r ^ s)⁻¹ := by
          rw [Real.rpow_neg hr0.le]
        have h2 : (beta ^ ((1 - 2 * s)⁻¹)) ^ (-s) = ((beta ^ ((1 - 2 * s)⁻¹)) ^ s)⁻¹ := by
          rw [Real.rpow_neg hbpos.le]
        have h3 : (beta ^ ((1 - 2 * s)⁻¹)) ^ (-s) = beta ^ (-(s / (1 - 2 * s))) := by
          rw [← Real.rpow_mul hbeta0.le]
          congr 1
          field_simp
        rw [h1, ← h3, h2]
        exact inv_anti₀ (Real.rpow_pos_of_pos hbpos _) hle
      have hL2branch : cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j ≤
          cubeBesovDepthWeight Q s j * (2 * L2) :=
        cubeBesovDepthSeminorm_two_le_depthWeight_mul_two_cubeLpNorm Q s v j hv
      have hwsplit : cubeBesovDepthWeight Q s j =
          cubeBesovScaleWeight s Q * r ^ (-s) := by
        rw [depthWeight_eq_mul Q s j]
        rfl
      have hbound : cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j ≤
          beta ^ (-(s / (1 - 2 * s))) * (cubeBesovScaleWeight s Q * (2 * L2)) := by
        refine le_trans hL2branch ?_
        rw [hwsplit]
        have hnn : 0 ≤ cubeBesovScaleWeight s Q * (2 * L2) := by positivity
        calc cubeBesovScaleWeight s Q * r ^ (-s) * (2 * L2)
            = r ^ (-s) * (cubeBesovScaleWeight s Q * (2 * L2)) := by ring
          _ ≤ beta ^ (-(s / (1 - 2 * s))) * (cubeBesovScaleWeight s Q * (2 * L2)) :=
              mul_le_mul_of_nonneg_right hrpow hnn
      have hfirst : 0 ≤ beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) * Pg) := by
        have : (0 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 - 2 * s) :=
          Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
        positivity
      simpa [hTdef] using le_trans hbound (by linarith)
  have hT1 : ∀ j : ℕ,
      cubeBesovScaleWeight s Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j ≤ T := by
    intro j
    have heq := cubeL2ScalarDepthSeminorm_eq_rpow_mul_cubeLpNorm_two Q (s - 1) v j hv
    have hpow : Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
      nlinarith
    have hle : cubeL2ScalarDepthSeminorm Q (s - 1) v j ≤ L2 := by
      rw [heq]
      exact mul_le_of_le_one_left hL2nn hpow
    exact le_trans (mul_le_mul_of_nonneg_left hle hweight_nn) hL2T
  
  have hsemi :
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M (fun x => F x i) ≤
        2 * (cubeScaleFactor Q * B * T + cubeLpNorm Q ∞ ξ * T) := by
    unfold cubeBesovPartialSeminormTop
    refine Finset.sup'_le (s := Finset.range (M + 1)) (H := ⟨0, by simp⟩)
      (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j) ?_
    intro j hj
    have hcomponent :
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j ≤
          cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j :=
      cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
        Q s F i j hF
    have hdepth :
        cubeBesovPositiveVectorDepthSeminorm Q s F j ≤
          2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
      simpa [F, v] using
        cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
          Q s j v ξ hB hv hξLp hξ hderiv
    have hscaled :
        cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j ≤
          cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j)) :=
      mul_le_mul_of_nonneg_left hdepth hweight_nn
    calc
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j :=
            hcomponent
      _ ≤ cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j)) := hscaled
      _ = 2 * (cubeScaleFactor Q * B *
              (cubeBesovScaleWeight s Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j) +
            cubeLpNorm Q ∞ ξ *
              (cubeBesovScaleWeight s Q *
                cubeBesovPositiveScalarDepthSeminorm Q s v j)) := by ring
      _ ≤ 2 * (cubeScaleFactor Q * B * T + cubeLpNorm Q ∞ ξ * T) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hT1 j)
                (mul_nonneg (cubeScaleFactor_pos' Q).le hB))
              (mul_le_mul_of_nonneg_left (hT2 j hj) (cubeLpNorm_nonneg Q ∞ ξ))
  have havg :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖ ≤
        cubeLpNorm Q ∞ ξ * T := by
    have hraw : ‖cubeAverage Q (fun x => F x i)‖ ≤
        cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) v := by
      have hcoord : ‖cubeAverage Q (fun x => F x i)‖ ≤
          ‖cubeAverageVec Q (fun x => v x • ξ x)‖ := by
        simpa [cubeAverageVec, F] using
          norm_le_pi_norm (cubeAverageVec Q (fun x => v x • ξ x)) i
      exact hcoord.trans
        (norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two Q v ξ hv hξLp)
    calc
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖
          ≤ cubeBesovScaleWeight s Q * (cubeLpNorm Q ∞ ξ * L2) :=
            mul_le_mul_of_nonneg_left hraw hweight_nn
      _ = cubeLpNorm Q ∞ ξ * (cubeBesovScaleWeight s Q * L2) := by ring
      _ ≤ cubeLpNorm Q ∞ ξ * T := mul_le_mul_of_nonneg_left hL2T (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (fun x => F x i)
        = cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M (fun x => F x i) +
            cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖ := rfl
    _ ≤ 2 * (cubeScaleFactor Q * B * T + cubeLpNorm Q ∞ ξ * T) +
          cubeLpNorm Q ∞ ξ * T := add_le_add hsemi havg
    _ = (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) * T := by ring

/-! ## The mesoscopic duality price -/

private theorem memLp_component_of_memLp_vec' {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (i : Fin d) :
    MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  simpa only [Function.comp_apply, ContinuousLinearMap.proj_apply] using!
    (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF

private theorem integrable_mul_of_memLp_two' {Q : TriadicCube d}
    {f g : Vec d → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Integrable (fun x => f x * g x) (normalizedCubeMeasure Q) := by
  have := MemLp.integrable_mul hf hg
  simpa only [Pi.mul_apply] using! this

/-- **The mesoscopic cutoff-product duality price for the fluctuation scalar.**

the whole-cube duality argument's `abs_cubeBesovPairing_cutoffProduct_fluctuation_le` with the depth-split
test bound in place of the whole-cube one.  The `beta`-small factor multiplies
the gradient branch, and only the (`beta`-large) `L²` branch survives at the
coarse depths. -/
theorem abs_cubeBesovPairing_cutoffProduct_fluctuation_mesoscopic_le
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : 2 * s < 1)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) (i : Fin d) :
    |cubeBesovPairing Q (fun x => flux x i)
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => flux x i)) *
        ((2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
          (beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) *
                ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
                    (3 : ℝ) ^ ((d : ℝ) + 1)) *
                  ∑ j : Fin d,
                    Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                      (fun x => u.grad x j))) +
            beta ^ (-(s / (1 - 2 * s))) *
              (cubeBesovScaleWeight s Q *
                (2 * cubeLpNorm Q (2 : ℝ≥0∞)
                  (cubeFluctuation Q (fun y => u y)))))) := by
  classical
  set Bg : ℝ :=
    (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
      (beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) *
            ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
                (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ∑ j : Fin d,
                Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x => u.grad x j))) +
        beta ^ (-(s / (1 - 2 * s))) *
          (cubeBesovScaleWeight s Q *
            (2 * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y)))))
    with hBgdef
  have hfluxi : MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp_vec' hflux i
  have hu2 : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv2 : MemLp (cubeFluctuation Q (fun y => u y)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    convert hu2.sub (MeasureTheory.memLp_const (cubeAverage Q (fun y => u y))) using 1
    funext x
    exact cubeFluctuation_apply Q (fun y => u y) x
  have hprod2 :
      MemLp (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    have hξi : MemLp (fun x => ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa only [Function.comp_apply, ContinuousLinearMap.proj_apply] using!
        (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      hv2.smul (p := (2 : ℝ≥0∞)) (q := ∞) (r := (2 : ℝ≥0∞)) hξi
  have hmem :
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) :=
    cubeBesovDualLocalMemLpGlobal_of_memLp_two Q _ hprod2
  have hq : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) ≤ Bg := by
    intro N
    rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N _ hq,
      hpConj]
    simpa [hBgdef, smul_eq_mul] using
      cutoffProduct_component_partialNormTop_le_mesoscopic_split
        Q s N u ξ hB hξLp hξ hderiv hs0 hs1 hbeta0 hbeta1 i
  have hBg : 0 ≤ Bg := by
    have h0 := hnorm 0
    rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 _ hq,
      hpConj] at h0
    exact le_trans
      (cubeBesovPartialNormTop_nonneg Q s (2 : ℝ≥0∞) 0
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)) h0
  exact Book.Ch01.Legacy.cubeBesovPairing_two_one_le_circNorm_mul_testBound
    Q s (fun x => flux x i) _ hs0 hfluxi hBg hnorm hmem

/-- **The mesoscopic cutoff-product Besov duality price.**

The `beta`-parameterised replacement for
`abs_cubeAverage_vecDot_cutoffProduct_le`: for every `beta ∈ (0,1]` the pairing
of an `L²` flux against `u ξ` is priced by

```
3^{d+s} (Σ_i ‖flux_i‖_{B^{-s}}) *
  ( (2 ℓ B + 3‖ξ‖_∞) (beta ℓ^{1-2s} C_P Σ_i ‖∂_i u‖_{B^{-s}}
                       + beta^{-s/(1-2s)} ℓ^{-s} 2‖u − ⟨u⟩_Q‖_{L̲²})
    + |⟨u⟩_Q| ℓ^{-s} (ℓ B + ‖ξ‖_∞) ).
```

Both negative norms now sit at the **same** exponent `s`, so both are supplied by
the two clauses of `SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` at one and the
same index (the paper's `1/16`).  This is the shape the mesoscopic optimisation
of `WholeSpaceRowsMesoscopic.lean` consumes. -/
theorem abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : 2 * s < 1)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          ∑ i : Fin d,
            Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => flux x i)) *
        ((2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
            (beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) *
                  ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
                      (3 : ℝ) ^ ((d : ℝ) + 1)) *
                    ∑ j : Fin d,
                      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                        (fun x => u.grad x j))) +
              beta ^ (-(s / (1 - 2 * s))) *
                (cubeBesovScaleWeight s Q *
                  (2 * cubeLpNorm Q (2 : ℝ≥0∞)
                    (cubeFluctuation Q (fun y => u y))))) +
          ‖cubeAverage Q (fun y => u y)‖ *
            (cubeBesovScaleWeight s Q *
              (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))) := by
  classical
  have hs1' : s < 1 := by linarith
  set c : ℝ := cubeAverage Q (fun y => u y) with hcdef
  set Bfl : ℝ :=
    (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
      (beta * ((cubeScaleFactor Q) ^ (1 - 2 * s) *
            ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
                (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ∑ j : Fin d,
                Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x => u.grad x j))) +
        beta ^ (-(s / (1 - 2 * s))) *
          (cubeBesovScaleWeight s Q *
            (2 * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y)))))
    with hBfldef
  set Bmn : ℝ :=
    ‖c‖ * (cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))
    with hBmndef
  have hu2 : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv2 : MemLp (cubeFluctuation Q (fun y => u y)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    convert hu2.sub (MeasureTheory.memLp_const (cubeAverage Q (fun y => u y))) using 1
    funext x
    exact cubeFluctuation_apply Q (fun y => u y) x
  have hξi : ∀ i : Fin d,
      MemLp (fun x => ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa only [Function.comp_apply, ContinuousLinearMap.proj_apply] using!
        (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
  have hfluxi : ∀ i : Fin d,
      MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := fun i =>
    memLp_component_of_memLp_vec' hflux i
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  have hvprod : ∀ i : Fin d,
      MemLp (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      hv2.smul (p := (2 : ℝ≥0∞)) (q := ∞) (r := (2 : ℝ≥0∞)) (hξi i)
  have hcprod : ∀ i : Fin d,
      MemLp (fun x => c * ξ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    have : MemLp (fun x => c * ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using! (hξi i).const_smul c
    exact this.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have huprod : ∀ i : Fin d,
      MemLp (fun x => u x * ξ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      hu2.smul (p := (2 : ℝ≥0∞)) (q := ∞) (r := (2 : ℝ≥0∞)) (hξi i)
  have hsplit : ∀ i : Fin d,
      cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i) =
        cubeBesovPairing Q (fun x => flux x i)
            (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) +
          cubeBesovPairing Q (fun x => flux x i) (fun x => c * ξ x i) := by
    intro i
    have h1 := integrable_mul_of_memLp_two' (hfluxi i) (hvprod i)
    have h2 := integrable_mul_of_memLp_two' (hfluxi i) (hcprod i)
    have hpt : ∀ x : Vec d,
        flux x i * (u x • ξ x) i =
          flux x i * (cubeFluctuation Q (fun y => u y) x * ξ x i) +
            flux x i * (c * ξ x i) := by
      intro x
      simp [cubeFluctuation, hcdef, smul_eq_mul]
      ring
    simp only [cubeBesovPairing, cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← MeasureTheory.integral_add h1 h2]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hInt : ∀ i : Fin d,
      Integrable (fun x => flux x i * (u x • ξ x) i) (normalizedCubeMeasure Q) := by
    intro i
    have := integrable_mul_of_memLp_two' (hfluxi i) (huprod i)
    simpa [smul_eq_mul] using this
  have hsum :=
    abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q flux
      (fun x => (u x) • ξ x) hInt
  have hbound : ∀ i : Fin d,
      |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)| ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => flux x i)) * (Bfl + Bmn) := by
    intro i
    have h1 := abs_cubeBesovPairing_cutoffProduct_fluctuation_mesoscopic_le
      Q s flux u ξ hB hflux hξLp hξ hderiv hs0 hs1 hbeta0 hbeta1 i
    have h2 := abs_cubeBesovPairing_cutoffProduct_mean_le Q s c flux ξ hB
      hflux hξLp hξ hderiv hs0 hs1'.le i
    calc
      |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)|
          ≤ |cubeBesovPairing Q (fun x => flux x i)
                (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)| +
              |cubeBesovPairing Q (fun x => flux x i) (fun x => c * ξ x i)| := by
            rw [hsplit i]; exact abs_add_le _ _
      _ ≤ ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * Bfl +
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * Bmn := by
            exact add_le_add (by simpa [hBfldef] using h1) (by simpa [hBmndef] using h2)
      _ = ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * (Bfl + Bmn) := by ring
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))|
        ≤ ∑ i : Fin d,
            |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)| := hsum
    _ ≤ ∑ i : Fin d,
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => flux x i)) * (Bfl + Bmn) :=
          Finset.sum_le_sum fun i _ => hbound i
    _ = ((3 : ℝ) ^ ((d : ℝ) + s) *
            ∑ i : Fin d,
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * (Bfl + Bmn) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]




/-- For `s ≤ 1/3` the sharp split exponent `s/(1-2s)` is at most `1`, so the
split price implies the `beta⁻¹` shape that `MesoscopicCrossPrice` consumes.
At the paper's index `s = 1/16` the exponent is `1/14`. -/
theorem rpow_neg_split_exponent_le_inv {s beta : ℝ} (hs0 : 0 < s) (hs : 3 * s ≤ 1)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    beta ^ (-(s / (1 - 2 * s))) ≤ beta⁻¹ := by
  have hgap : (0 : ℝ) < 1 - 2 * s := by linarith
  have hθ : s / (1 - 2 * s) ≤ 1 := by
    rw [div_le_one hgap]; linarith
  have hmono := Real.rpow_le_rpow_of_exponent_ge hbeta0 hbeta1
    (show -(1 : ℝ) ≤ -(s / (1 - 2 * s)) by linarith)
  simpa [Real.rpow_neg_one] using hmono

/-- **The mesoscopic price in the shape `MesoscopicCrossPrice` consumes.**

Given the two *coarse* conversions of the circ negative Besov norms produced by
the split duality price —

* `hgrad`: the `∇u` factor, i.e. clause 1 of
  `SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare`, in the form
  `C_P Σ_j ‖∂_j u‖_{B^{-s}} ≤ cP √Ea` with `cP ≍ C λ^{-1/2}`;
* `hflux`: the flux factor, i.e. clause 2 of the same anchor for a solenoidal
  field, in the form `Σ_i ‖flux_i‖_{B^{-s}} ≤ cL √Ea` with `cL ≍ C Λ^{1/2}`;

together with the trivial `L²` bounds on the fluctuation and on the mean, the
split price becomes exactly

```
|⟨flux, u ξ⟩| ≤ beta * P * Ea + beta⁻¹ * R * √Ea * √M
```

with `P = 3^{d+s} cL cP (2 ℓ B + 3‖ξ‖_∞) ℓ^{1-2s}` and
`R = 3^{d+s} cL (2 (2 ℓ B + 3‖ξ‖_∞) ℓ^{-s} + ℓ^{-s}(ℓ B + ‖ξ‖_∞))`.  Reading
`cP ≍ λ^{-1/2}`, `cL ≍ Λ^{1/2}`, `B ≍ ℓ^{-2}`, `‖ξ‖_∞ ≍ ℓ^{-1}` gives
`P ≍ (Λ/λ)^{1/2} ℓ^{-2s}` and `R ≍ Λ^{1/2} ℓ^{-1-s}`, which are exactly the
coarse sizes the mesoscopic optimisation of `WholeSpaceRowsMesoscopic.lean`
assumes. -/
theorem abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hfluxLp : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs : 3 * s ≤ 1)
    {Ea M cP : ℝ} (hEa : 0 ≤ Ea)
    {cL : ℝ} (hcL : 0 ≤ cL)
    (hGnonneg : 0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d,
        Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x j))
    (hNnonneg : 0 ≤ ∑ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => flux x i))
    (hgrad : (Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ j : Fin d,
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x j) ≤ cP * Real.sqrt Ea)
    (hflux : ∑ i : Fin d,
        Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => flux x i) ≤ cL * Real.sqrt Ea)
    (hfluc : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y)) ≤ Real.sqrt M)
    (hmean : ‖cubeAverage Q (fun y => u y)‖ ≤ Real.sqrt M)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))| ≤
      beta *
          ((3 : ℝ) ^ ((d : ℝ) + s) * cL * cP *
            (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
              (cubeScaleFactor Q) ^ (1 - 2 * s)) * Ea +
        beta⁻¹ *
          ((3 : ℝ) ^ ((d : ℝ) + s) * cL *
            (2 * (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
                cubeBesovScaleWeight s Q +
              cubeBesovScaleWeight s Q *
                (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))) *
          Real.sqrt Ea * Real.sqrt M := by
  classical
  have hs1 : 2 * s < 1 := by linarith
  have hraw := abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le Q s flux u ξ hB
    hfluxLp hξLp hξ hderiv hs0 hs1 hbeta0 hbeta1
  set K : ℝ := (3 : ℝ) ^ ((d : ℝ) + s) with hKdef
  set N : ℝ := ∑ i : Fin d,
    Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (fun x => flux x i) with hNdef
  set Cxi : ℝ := 2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ with hCxidef
  set ws : ℝ := cubeBesovScaleWeight s Q with hwsdef
  set Cm : ℝ := ws * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ) with hCmdef
  set G : ℝ := (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
      (3 : ℝ) ^ ((d : ℝ) + 1)) *
    ∑ j : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j) with hGdef
  set W2 : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y)) with hW2def
  set A : ℝ := ‖cubeAverage Q (fun y => u y)‖ with hAdef
  set L : ℝ := (cubeScaleFactor Q) ^ (1 - 2 * s) with hLdef
  have hLnn : 0 ≤ L := Real.rpow_nonneg (cubeScaleFactor_pos' Q).le _
  have hwsnn : 0 ≤ ws := cubeBesovScaleWeight_nonneg s Q
  have hlnn : (0 : ℝ) ≤ cubeScaleFactor Q := (cubeScaleFactor_pos' Q).le
  have hxinn : (0 : ℝ) ≤ cubeLpNorm Q ∞ ξ := cubeLpNorm_nonneg Q ∞ ξ
  have hCxinn : 0 ≤ Cxi := by rw [hCxidef]; positivity
  have hCmnn : 0 ≤ Cm := by rw [hCmdef]; positivity
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hsEa : 0 ≤ Real.sqrt Ea := Real.sqrt_nonneg _
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hcPsqrt : 0 ≤ cP * Real.sqrt Ea := le_trans hGnonneg hgrad
  have hbetaInv : (1 : ℝ) ≤ beta⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hbeta0]; simpa using hbeta1
  have hbetaInvnn : (0 : ℝ) ≤ beta⁻¹ := by linarith
  have hθ : beta ^ (-(s / (1 - 2 * s))) ≤ beta⁻¹ :=
    rpow_neg_split_exponent_le_inv hs0 hs hbeta0 hbeta1
  have hθnn : 0 ≤ beta ^ (-(s / (1 - 2 * s))) := Real.rpow_nonneg hbeta0.le _
  -- step 1: sharp exponent to `beta⁻¹`, and the norms to the coarse data
  have h1 : beta * (L * G) ≤ beta * (L * (cP * Real.sqrt Ea)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrad hLnn) hbeta0.le
  have h2 : beta ^ (-(s / (1 - 2 * s))) * (ws * (2 * W2)) ≤
      beta⁻¹ * (ws * (2 * Real.sqrt M)) := by
    have hA1 : ws * (2 * W2) ≤ ws * (2 * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left (by linarith [hfluc]) hwsnn
    have hA2 : 0 ≤ ws * (2 * Real.sqrt M) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hA1 hθnn)
      (mul_le_mul_of_nonneg_right hθ hA2)
  have h3 : A * Cm ≤ Real.sqrt M * Cm := mul_le_mul_of_nonneg_right hmean hCmnn
  have hinner :
      Cxi * (beta * (L * G) + beta ^ (-(s / (1 - 2 * s))) * (ws * (2 * W2))) + A * Cm ≤
        Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
            beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm :=
    add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCxinn) h3
  have hposinner : 0 ≤ Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
      beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm := by
    have hb1 : 0 ≤ beta * (L * (cP * Real.sqrt Ea)) :=
      mul_nonneg hbeta0.le (mul_nonneg hLnn hcPsqrt)
    have hb2 : 0 ≤ beta⁻¹ * (ws * (2 * Real.sqrt M)) := by positivity
    have hb3 : 0 ≤ Real.sqrt M * Cm := mul_nonneg hsM hCmnn
    have := mul_nonneg hCxinn (add_nonneg hb1 hb2)
    linarith
  have hstep2 :
      |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))| ≤
        K * (cL * Real.sqrt Ea) * (Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
            beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm) := by
    refine hraw.trans ?_
    calc K * N * (Cxi * (beta * (L * G) +
            beta ^ (-(s / (1 - 2 * s))) * (ws * (2 * W2))) + A * Cm)
        ≤ K * N * (Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
              beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm) :=
          mul_le_mul_of_nonneg_left hinner (mul_nonneg hKnn hNnonneg)
      _ ≤ K * (cL * Real.sqrt Ea) * (Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
              beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hflux hKnn) hposinner
  refine hstep2.trans ?_
  have hsq : Real.sqrt Ea * Real.sqrt Ea = Ea := Real.mul_self_sqrt hEa
  set X : ℝ := (K * cL * Cm) * Real.sqrt Ea * Real.sqrt M with hXdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have : 0 ≤ K * cL * Cm := by positivity
    positivity
  have hextra : K * (cL * Real.sqrt Ea) * (Real.sqrt M * Cm) ≤ beta⁻¹ * X := by
    have heq : K * (cL * Real.sqrt Ea) * (Real.sqrt M * Cm) = 1 * X := by
      rw [hXdef]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hbetaInv hXnn
  have hmain : K * (cL * Real.sqrt Ea) *
      (Cxi * (beta * (L * (cP * Real.sqrt Ea)) + beta⁻¹ * (ws * (2 * Real.sqrt M)))) =
        beta * (K * cL * cP * Cxi * L) * Ea +
          beta⁻¹ * (K * cL * (2 * Cxi * ws)) * Real.sqrt Ea * Real.sqrt M := by
    have hexp : K * (cL * Real.sqrt Ea) *
        (Cxi * (beta * (L * (cP * Real.sqrt Ea)) + beta⁻¹ * (ws * (2 * Real.sqrt M)))) =
          beta * (K * cL * cP * Cxi * L) * (Real.sqrt Ea * Real.sqrt Ea) +
            beta⁻¹ * (K * cL * (2 * Cxi * ws)) * Real.sqrt Ea * Real.sqrt M := by ring
    rw [hexp, hsq]
  calc K * (cL * Real.sqrt Ea) * (Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
          beta⁻¹ * (ws * (2 * Real.sqrt M))) + Real.sqrt M * Cm)
      = K * (cL * Real.sqrt Ea) *
            (Cxi * (beta * (L * (cP * Real.sqrt Ea)) +
              beta⁻¹ * (ws * (2 * Real.sqrt M)))) +
          K * (cL * Real.sqrt Ea) * (Real.sqrt M * Cm) := by ring
    _ ≤ (beta * (K * cL * cP * Cxi * L) * Ea +
          beta⁻¹ * (K * cL * (2 * Cxi * ws)) * Real.sqrt Ea * Real.sqrt M) +
          beta⁻¹ * X := by rw [hmain]; linarith [hextra]
    _ = beta * (K * cL * cP * Cxi * L) * Ea +
          beta⁻¹ * (K * cL * (2 * Cxi * ws + Cm)) * Real.sqrt Ea * Real.sqrt M := by
          rw [hXdef]; ring

/-! ## The three-set form of the two mesoscopic inputs

the mesoscopic price formulation states `MesoscopicCrossPrice` and `CoarseEnergyBound` with **one** cube
`W`: the price's energy and the coarse energy bound both live on `W`, so the
coarse energy bound reads `t ∫_W a|∇u|² ≤ Gam ∫_W u²`.  No Caccioppoli
inequality has that shape — a Caccioppoli always bounds the energy of a
*strictly smaller* set by the mass of the larger one.  The variants below carry
an intermediate set `V` (in the application, the support of the cutoff, i.e. the
middle seven-eighths of the manuscript's proof), for which

```
t ∫_V a|∇u|² ≤ Gam ∫_W u²
```

is exactly the shape of `l.coarse.grained.Caccioppoli.RHS.ASD`.  Everything
else is unchanged: the abstract optimisation `mesoscopic_mass_contraction` is
stated on plain reals and does not see the sets. -/

/-- The mesoscopic cutoff-product price with the energy carried on an
intermediate set `V` (the cutoff's support). -/
def MesoscopicCrossPriceOn (a : Vec d → ℝ) (W V : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) (chi : Vec d → ℝ) (t P R S : ℝ) : Prop :=
  ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
    |2 * ∫ x in W, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume| ≤
      beta * P * (∫ x in V, a x * vecNormSq (G x) ∂volume) +
        beta⁻¹ * R * Real.sqrt (∫ x in V, a x * vecNormSq (G x) ∂volume) *
          Real.sqrt (∫ x in W, w x ^ 2 ∂volume) +
        beta * S * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume)

/-- The coarse energy bound in genuine Caccioppoli shape: the energy of the
intermediate set `V`, the mass of the outer set `W`. -/
def CoarseEnergyBoundOn (a : Vec d → ℝ) (W V : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) (t Gam : ℝ) : Prop :=
  t * ∫ x in V, a x * vecNormSq (G x) ∂volume ≤ Gam * ∫ x in W, w x ^ 2 ∂volume

/-- **The coarse-grained local `L²` contraction, three-set form.**

Identical to `massive_local_l2_coarse_contraction_of_price` except that the two
named inputs are the `V`-versions above, so that the coarse energy bound is a
genuine Caccioppoli inequality from `V` to `W`.  No `L^∞` bound on the
coefficient enters the constants. -/
theorem massive_local_l2_coarse_contraction_of_price_on
    {a : Vec d → ℝ} {lam Lam t eta P R Ssmall Gam K : ℝ} {W V S : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hS : 0 ≤ Ssmall)
    (hbeta1 : eta ≤ 3 * (P * Gam + Ssmall))
    (hSW : S ⊆ W) (hSmeas : MeasurableSet S)
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ S, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPriceOn a W V u.toFun u.grad chi t P R Ssmall)
    (henergy : CoarseEnergyBoundOn a W V u.toFun u.grad t Gam)
    (hsmall : 81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4) :
    (∫ x in S, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      eta * ∫ x in W, u.toFun x ^ 2 ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  have hMnn : (0 : ℝ) ≤ ∫ x in W, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg hWmeas fun x _ ↦ sq_nonneg _
  have hstep : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      t⁻¹ * (∫ x in S, u.toFun x ^ 2 ∂volume) +
          ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
        beta * P * (∫ x in V, a x * vecNormSq (u.grad x) ∂volume) +
          beta⁻¹ * R * Real.sqrt (∫ x in V, a x * vecNormSq (u.grad x) ∂volume) *
            Real.sqrt (∫ x in W, u.toFun x ^ 2 ∂volume) +
          beta * Ssmall * (t⁻¹ * ∫ x in W, u.toFun x ^ 2 ∂volume) + 0 := by
    intro beta hbeta hbeta1'
    have hforce : |∫ x in W, (fun _ ↦ (0 : ℝ)) x * chi x ^ 2 * u.toFun x ∂volume| ≤ 0 := by
      simp
    have := massive_cutoff_mass_energy_le_of_cross_bound hW hEll haNonneg ht hSW hSmeas
      u hu hchi hchiC hchiS hchi_le hchi_one hK (hprice beta hbeta hbeta1') hforce
    linarith [this]
  have hmain := mesoscopic_mass_contraction (t := t) (eta := eta) (P := P) (R := R)
    (S := Ssmall) (Gam := Gam) (m := ∫ x in S, u.toFun x ^ 2 ∂volume)
    (e := ∫ x in S, a x * vecNormSq (u.grad x) ∂volume)
    (E := ∫ x in V, a x * vecNormSq (u.grad x) ∂volume)
    (M := ∫ x in W, u.toFun x ^ 2 ∂volume) (D := 0)
    ht heta hP hGam hR hS hMnn hbeta1 hstep henergy hsmall
  linarith [hmain]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
