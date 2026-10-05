module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fine proof step for `mfd:prop-killed-inverse`.

Carried-input Scope and inputs:
- `d`, `hd`, `z`, `R`, `hR`, `S`, `a`, and `GN` are the concrete native
  cube and finite killed inverse family.
- `hGN` is the actual killed-response identification supplied by
  `in_killed_inverse`.
- `hInterp` is the published fractional Rellich input on the native cube.
- `hCoercive` is the common represented-sequence coercivity estimate supplied
  by `lem_coercivity` and `conv_represented_sequence`.
- CONCLUDED HERE: the union of the images of the unit ball is relatively
  compact, expressed by compactness of its closure. The finite-net argument and
  the operator limit remain conclusions of the parent.
 -/
theorem prop_killed_inverse_collective_compactness
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ]
      DomainL2 (centeredCube z R hR))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z R hR)), GN n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : S.space),
      cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm S (a n) v v) :
    IsCompact (closure (⋃ n : ℕ,
      (GN n) '' Metric.closedBall (0 : DomainL2 (centeredCube z R hR)) 1)) := by
  have hvol : 0 < volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [Measure.real_def]
    apply ENNReal.toReal_pos
    · exact (Metric.measure_ball_pos volume z (by linarith [hR])).ne'
    · exact (MeasureTheory.measure_ball_ne_top :
        volume (Metric.ball z (R / 2)) ≠ ⊤)
  apply isCompact_closure_of_subseq_tendsto
  intro u hu
  choose m hm using fun n => Set.mem_iUnion.mp (hu n)
  choose f hf huf using fun n =>
    (Set.mem_image (GN (m n))
      (Metric.closedBall (0 : DomainL2 (centeredCube z R hR)) 1) (u n)).mp (hm n)
  let v : ℕ → S.space := fun n =>
    responseSolution S (a (m n))
      ((sobolevVolumeLoad (f n)).comp S.space.subtypeL)
  have huv (n : ℕ) : u n = (v n).val.1 := by
    dsimp [v]
    rw [← huf n, hGN]
  have hf_norm (n : ℕ) : ‖f n‖ ≤ 1 := by
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hf n))
  have hform (n : ℕ) :
      responseForm S (a (m n)) (v n) (v n) = inner ℝ (f n) (v n).val.1 := by
    dsimp [v]
    rw [responseSolution_spec]
    rfl
  have hform_le (n : ℕ) :
      responseForm S (a (m n)) (v n) (v n) ≤ ‖(v n).val.1‖ := by
    rw [hform n]
    calc
      inner ℝ (f n) (v n).val.1 ≤ ‖f n‖ * ‖(v n).val.1‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖(v n).val.1‖ := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hf_norm n) (norm_nonneg _))
  let w : ℕ → CubeFractionalL2 hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder := fun n =>
    ⟨fun _ : Fin 1 => (v n).val.1, (hCoercive (m n) (v n)).1⟩
  let V : ℝ := volume.real (centeredCube z R hR : Set (SpatialCoordinates d))
  let M : ℝ := K / Real.sqrt V + R ^ (-(_root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder : ℝ)) * (K / Real.sqrt V)
  have hw_bound (n : ℕ) :
      cubeFractionalL2Norm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w n) ≤ M := by
    let x : ℝ := ‖(v n).val.1‖
    let y : ℝ :=
      (cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => (v n).val.1)).toReal
    have hx : 0 ≤ x := by exact norm_nonneg _
    have hy : 0 ≤ y := by exact ENNReal.toReal_nonneg
    have henergy : x ^ 2 + V * y ^ 2 ≤ K * x := by
      dsimp [x, y, V]
      exact (hCoercive (m n) (v n)).2 |>.trans
        (mul_le_mul_of_nonneg_left (hform_le n) hK.le)
    have hVy : 0 ≤ V * y ^ 2 := mul_nonneg (le_of_lt hvol) (sq_nonneg _)
    have hxK : x ≤ K := by
      nlinarith [henergy]
    have hyenergy : V * y ^ 2 ≤ K ^ 2 := by
      nlinarith [henergy]
    have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 (by simpa [V] using hvol)
    have hsqrtV_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt (le_of_lt (by simpa [V] using hvol))
    have hprod : Real.sqrt V * y ≤ K := by
      have hprod_nonneg : 0 ≤ Real.sqrt V * y := mul_nonneg hsqrtV.le hy
      nlinarith [hyenergy, hsqrtV_sq]
    have hyK : y ≤ K / Real.sqrt V := by
      apply (le_div_iff₀ hsqrtV).2
      nlinarith [hprod]
    have hnorm : cubeFractionalL2Norm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w n) =
        y + R ^ (-(_root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder : ℝ)) * (x / Real.sqrt V) := by
      unfold cubeFractionalL2Norm w
      simp only [Fin.sum_univ_one, Real.sqrt_sq_eq_abs, abs_norm]
      rfl
    rw [hnorm]
    dsimp [M]
    have hpow : 0 ≤ R ^ (-(_root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder : ℝ)) := by positivity
    have hdiv : x / Real.sqrt V ≤ K / Real.sqrt V := by
      exact div_le_div_of_nonneg_right hxK hsqrtV.le
    gcongr
  obtain ⟨sigma, hsigma, wlim, hwlim⟩ :=
    hInterp.compact_embedding z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (by rfl) w M hw_bound
  refine ⟨wlim, sigma, hsigma, ?_⟩
  have hdist : Tendsto
      (fun n => dist ((v (sigma n)).val.1) wlim) atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using hwlim
  have hconv : Tendsto (fun n => (v (sigma n)).val.1) atTop (𝓝 wlim) :=
    (tendsto_iff_of_dist hdist).2 tendsto_const_nhds
  have heq : u ∘ sigma = fun n => (v (sigma n)).val.1 := by
    funext n
    exact huv (sigma n)
  rw [heq]
  exact hconv

end SubdiffusiveProcess.Paper
