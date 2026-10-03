module

public import SubdiffusiveProcess.Morrey.LpBounds
public import SubdiffusiveProcess.Lane4.InDetCampanatoHolder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentH1
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.ReflectionFiniteP
public import Mathlib.Topology.TietzeExtension

@[expose] public section

/-!
# Morrey's inequality on the unit centered cube

Even reflection gives an H¹ extension to the cube of side three. Local
Poincaré bounds imply Campanato decay on clipped windows in the unit cube.
The existing Campanato representative and modulus theorems give the closed
cube estimate, and Tietze extension gives a globally continuous function.
-/

open MeasureTheory Set Filter
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedL2On)
open scoped ENNReal NNReal Topology Pointwise

noncomputable section
namespace SubdiffusiveProcess.Morrey

theorem origin_cube_ball (d : ℕ) (k : ℤ) :
    openCubeSet (originCube d k) = Metric.ball (0 : Vec d) ((3 : ℝ) ^ k / 2) := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  have hc : cubeCenter (originCube d k) = (0 : Vec d) := by
    ext i
    simp [cubeCenter, originCube]
  rw [hc]
  simp [cubeRadius, cubeScaleFactor, originCube, div_eq_mul_inv, mul_comm]

theorem unit_reflection {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (u : H1Function (Metric.ball (0 : Vec d) (1 / 2)))
    (hg : MemLp (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (1 / 2)))) :
    ∃ v : H1Function (Metric.ball (0 : Vec d) (3 / 2)),
      (∀ x ∈ Metric.ball (0 : Vec d) (1 / 2), v.toFun x = u.toFun x) ∧
      MemLp (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : Vec d) (3 / 2))) ∧
      (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal =
      ((3 : ℝ) ^ d) ^ (1 / p) *
        (eLpNorm (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : Vec d) (1 / 2)))).toReal := by
  have hQ := origin_cube_ball d 0
  have hP := origin_cube_ball d 1
  norm_num only [zpow_zero, zpow_one] at hQ hP
  have hs := @exists_cubeFaceReflectionParentH1Function_originCube d 0
  change ∀ u : H1Function (openCubeSet (originCube d 0)),
    ∃ v : H1Function (openCubeSet (originCube d 1)),
      v.toFun = cubeCoordinateFoldReflectedScalar (originCube d 0) u.toFun ∧
      v.grad = cubeCoordinateFoldReflectedVectorField (originCube d 0) u.grad at hs
  rw [hQ, hP] at hs
  obtain ⟨v, hvf, hvg⟩ := hs u
  let q : FiniteLpExponent :=
    { exponent := ENNReal.ofReal p
      one_lt := lt_of_lt_of_le (by norm_num : (1 : ENNReal) < 2)
        (by simpa using ENNReal.ofReal_le_ofReal hp)
      lt_top := ENNReal.ofReal_lt_top }
  have hL2 := memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
  have hG : MemLp (fun y => HilbertVec.ofVec (u.grad y)) q.exponent
      (volume.restrict (openCubeSet (originCube d 0))) := by
    rw [hQ]
    apply hg.of_le
    · exact hL2.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_of_nonneg (euclideanNorm_nonneg _), euclideanNorm_eq_norm_ofVec]
  have hVG := memLp_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField q hG
  norm_num only [zero_add] at hVG
  have hMem : MemLp (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (3 / 2))) := by
    rw [hvg, ← hP]
    simpa only [euclideanNorm_eq_norm_ofVec] using hVG.norm
  refine ⟨v, ?_, hMem, ?_⟩
  · intro x hx
    rw [hvf]
    exact cubeCoordinateFoldReflectedScalar_eq_self_of_mem_openCubeSet
      (originCube d 0) u.toFun (hQ.symm ▸ hx)
  · have he := eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      (m := 0) u.grad q
    norm_num only [zero_add] at he
    rw [hQ, hP] at he
    rw [hvg]
    simp only [euclideanNorm_eq_norm_ofVec]
    rw [eLpNorm_norm _ (by simpa only [hP] using hVG.aestronglyMeasurable),
      eLpNorm_norm _ (by simpa only [hQ] using hG.aestronglyMeasurable)]
    rw [he, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_pow]
    simp only [ENNReal.toReal_ofNat, q, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]

/-- The dimension-dependent constant in the normalized window oscillation bound. -/
def oscillationConst (d : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ d) * unitMeanZeroPoincareConst d * (d : ℝ)

theorem window_decay {d : ℕ} {p alpha : ℝ} (hp : 2 ≤ p)
    (_halpha : 0 < alpha) (hpa : alpha < 1 - (d : ℝ) / p)
    (v : H1Function (Metric.ball (0 : Vec d) (3 / 2)))
    (hg : MemLp (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))) :
    ∀ (D : ℕ), ∀ x ∈ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)),
      normalizedL2On (campanatoWindow (0 : Vec d) one_pos x D)
        (fun y => v.toFun y - campanatoAvg (0 : Vec d) one_pos v.toFun x D) ≤
      (oscillationConst d *
        (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal) *
        ((3 : ℝ) ^ (-alpha)) ^ D := by
  intro D x hx
  let t : ℝ := (3 : ℝ) ^ (-(D : ℤ))
  let r : ℝ := t / 2
  let B : Set (Vec d) := Metric.ball x r
  let S : Set (Vec d) := B ∩ Metric.ball (0 : Vec d) (1 / 2)
  have ht0 : 0 < t := zpow_pos (by norm_num) _
  have ht1 : t ≤ 1 := Paper.aux_in_deterministic_regularity_three_zpow_le_one D
  have hr : 0 < r := half_pos ht0
  have hBP : B ⊆ Metric.ball (0 : Vec d) (3 / 2) := by
    intro y hy
    have hx0 : dist x (0 : Vec d) < 1 / 2 := Metric.mem_ball.mp hx
    have hyx : dist y x < r := Metric.mem_ball.mp hy
    have hr1 : r ≤ 1 / 2 := by dsimp [r]; linarith
    exact Metric.mem_ball.mpr (by linarith [dist_triangle y x (0 : Vec d)])
  have hlow : r ^ d ≤ volume.real S := by
    exact aux_campanato_cube_inter_volume_ge (0 : Vec d) x one_pos ht0 ht1 hx
  have hSpos : 0 < volume.real S := (pow_pos hr d).trans_le hlow
  have hBfin : volume B ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hBvol : volume.real B = t ^ d := by
    rw [Measure.real, volume_ball_spatial x hr, ENNReal.toReal_ofReal (by positivity)]
    congr 1
    dsimp [r]
    ring
  have hratio : volume.real B / volume.real S ≤ (2 : ℝ) ^ d := by
    rw [div_le_iff₀ hSpos, hBvol]
    have htEq : t = 2 * r := by dsimp [r]; ring
    rw [htEq, mul_pow]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hfB : MemLp v.toFun 2 (volume.restrict B) :=
    v.memL2.mono_measure (Measure.restrict_mono hBP le_rfl)
  have hsub := oscillation_subset (show S ⊆ B from inter_subset_left) hBfin hSpos hfB
  have hball := ball_oscillation_lp v hp hg x hr hBP
  change normalizedL2On B (fun y => v.toFun y - integralAverage B v.toFun) ≤ _ at hball
  rw [hBvol] at hball
  have hscale : r * (t ^ d) ^ (-(1 / p)) ≤ (1 / 2) * t ^ alpha := by
    have he2 : (t ^ d) ^ (-(1 / p)) = t ^ (-(d : ℝ) / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 1
      ring
    have he : r * (t ^ d) ^ (-(1 / p)) = (1 / 2) * t ^ (1 - (d : ℝ) / p) := by
      rw [he2]
      calc
        _ = (1 / 2) * (t ^ (1 : ℝ) * t ^ (-(d : ℝ) / p)) := by
          rw [Real.rpow_one]; dsimp [r]; ring
        _ = _ := by rw [← Real.rpow_add ht0]; congr 1; congr 1; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hpa.le) (by norm_num)
  have htheta : t ^ alpha = ((3 : ℝ) ^ (-alpha)) ^ D :=
    (Paper.aux_in_deterministic_regularity_theta_pow alpha D).symm
  have hCd : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have hM : 0 ≤ (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal := ENNReal.toReal_nonneg
  simp only [campanatoWindow, campanatoAvg, one_mul]
  change normalizedL2On S (fun y => v.toFun y - (volume.real S)⁻¹ * ∫ q in S, v.toFun q) ≤ _
  calc
    _ ≤ Real.sqrt (volume.real B / volume.real S) *
        normalizedL2On B (fun y => v.toFun y - integralAverage B v.toFun) := hsub
    _ ≤ Real.sqrt ((2 : ℝ) ^ d) *
        ((2 * unitMeanZeroPoincareConst d * (d : ℝ)) * r *
          (t ^ d) ^ (-(1 / p)) *
          (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal) := by
      apply mul_le_mul (Real.sqrt_le_sqrt hratio) hball
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _
    _ = (2 * Real.sqrt ((2 : ℝ) ^ d) * unitMeanZeroPoincareConst d * (d : ℝ) *
        (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal) *
          (r * (t ^ d) ^ (-(1 / p))) := by ring
    _ ≤ (2 * Real.sqrt ((2 : ℝ) ^ d) * unitMeanZeroPoincareConst d * (d : ℝ) *
        (eLpNorm (fun y => euclideanNorm (v.grad y)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal) *
          ((1 / 2) * t ^ alpha) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by rw [htheta]; unfold oscillationConst; ring

theorem unit_morrey {d : ℕ} [NeZero d] {p alpha : ℝ} (hp : 2 ≤ p)
    (halpha : 0 < alpha) (hpa : alpha < 1 - (d : ℝ) / p)
    (u : H1Function (Metric.ball (0 : Vec d) (1 / 2)))
    (hg : MemLp (fun y => euclideanNorm (u.grad y)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (1 / 2)))) :
    ∃ U : Vec d → ℝ, Continuous U ∧
      (u.toFun =ᵐ[volume.restrict (Metric.ball (0 : Vec d) (1 / 2))] U) ∧
      ∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2),
        ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2),
          |U x - U y| ≤
            (Paper.aux_in_deterministic_regularity_holderConst d alpha *
              oscillationConst d * ((3 : ℝ) ^ d) ^ (1 / p)) *
            (eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : Vec d) (1 / 2)))).toReal *
              ‖x - y‖ ^ alpha := by
  have hp0 : 0 < p := by linarith
  have ha1 : alpha < 1 := hpa.trans_le (sub_le_self _ (div_nonneg (Nat.cast_nonneg d) hp0.le))
  have ha : alpha ∈ Ioo (0 : ℝ) 1 := ⟨halpha, ha1⟩
  obtain ⟨v, hvEq, hvMem, hvNorm⟩ := unit_reflection hp u hg
  let K : ℝ := oscillationConst d *
    (eLpNorm (fun q => euclideanNorm (v.grad q)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (3 / 2)))).toReal
  have hK : 0 ≤ K := by
    have hCd := unitMeanZeroPoincareConst_nonneg d
    unfold K oscillationConst
    positivity
  have hcamp := window_decay hp halpha hpa v hvMem
  have hQsub : Metric.ball (0 : Vec d) (1 / 2) ⊆ Metric.ball (0 : Vec d) (3 / 2) :=
    Metric.ball_subset_ball (by norm_num)
  have hvL2 : MemLp v.toFun 2 (volume.restrict (Metric.ball (0 : Vec d) (1 / 2))) :=
    v.memL2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Vec d) (1 / 2))) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  obtain ⟨V, hVc, hVae⟩ := aux_campanato_continuous_representative (0 : Vec d) one_pos
    ha hK (hvL2.integrable (by norm_num)) hvL2.integrable_sq hcamp
  have hcampV : ∀ (D : ℕ), ∀ x ∈ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)),
      normalizedL2On (campanatoWindow (0 : Vec d) one_pos x D)
        (fun y => V y - campanatoAvg (0 : Vec d) one_pos V x D) ≤
      K * ((3 : ℝ) ^ (-alpha)) ^ D := by
    intro D x hx
    have hae : V =ᵐ[volume.restrict (campanatoWindow (0 : Vec d) one_pos x D)] v.toFun :=
      hVae.filter_mono (ae_mono (Measure.restrict_mono
        (campanatoWindow_subset (0 : Vec d) one_pos x D) le_rfl))
    have he := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.normalizedL2On_sub_average_eq_of_ae_eq hae
    change normalizedL2On (campanatoWindow (0 : Vec d) one_pos x D)
      (fun y => V y - campanatoAvg (0 : Vec d) one_pos V x D) =
      normalizedL2On (campanatoWindow (0 : Vec d) one_pos x D)
        (fun y => v.toFun y - campanatoAvg (0 : Vec d) one_pos v.toFun x D) at he
    rw [he]
    exact hcamp D x hx
  have hVc' : ContinuousOn V (Metric.closedBall (0 : Vec d) (1 / 2)) := hVc
  have hHol := Paper.aux_in_deterministic_regularity_holder_closedBall
    (0 : Vec d) one_pos ha hVc' hK
    (fun D x hx => by
      simpa only [campanatoWindow, campanatoAvg,
        Paper.aux_in_deterministic_regularity_window,
        Paper.aux_in_deterministic_regularity_avg, centeredCube, volumeAverage] using! hcampV D x hx)
  let f : C(Metric.closedBall (0 : Vec d) (1 / 2), ℝ) := ⟨fun x => V x, hVc'.restrict⟩
  obtain ⟨W, hW⟩ := f.exists_restrict_eq Metric.isClosed_closedBall
  have hWEq : ∀ x ∈ Metric.closedBall (0 : Vec d) (1 / 2), W x = V x := by
    intro x hx
    exact congrArg (fun g : C(Metric.closedBall (0 : Vec d) (1 / 2), ℝ) => g ⟨x, hx⟩) hW
  refine ⟨W, W.continuous, ?_, ?_⟩
  · filter_upwards [hVae, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hrep hx
    rw [hWEq x (Metric.ball_subset_closedBall hx), hrep, hvEq x hx]
  · intro x hx y hy
    rw [hWEq x hx, hWEq y hy]
    have he := hHol x hx y hy
    simpa only [K, hvNorm, dist_eq_norm, div_one, mul_assoc] using he

end SubdiffusiveProcess.Morrey
