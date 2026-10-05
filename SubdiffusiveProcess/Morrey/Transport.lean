module

public import SubdiffusiveProcess.Morrey.UnitCube
public import Homogenization.Sobolev.W1p.Dilation

@[expose] public section

/-!
# Morrey's inequality with uniform cube scaling

Translation and positive dilation transport the unit cube estimate while
retaining the exact gradient Lᵖ norm and Lebesgue volume normalization.
Dimension zero is handled separately by the uniqueness of its spatial point.
-/

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal NNReal Topology Pointwise

noncomputable section
namespace SubdiffusiveProcess.Morrey

theorem affine_cube_eq {d : ℕ} (z : Vec d) {a : ℝ} (ha : 0 < a) :
    translateSet z (a • Metric.ball (0 : Vec d) (1 / 2)) = Metric.ball z (a / 2) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hw
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg ha.le]
    have hy' : ‖y‖ < 1 / 2 := by simpa using Metric.mem_ball.mp hy
    simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_left hy' ha
  · intro hx
    refine ⟨x - z, ?_, by abel⟩
    refine ⟨a⁻¹ • (x - z), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
      have hx' : ‖x - z‖ < a / 2 := Metric.mem_ball.mp hx
      calc
        _ < a⁻¹ * (a / 2) := mul_lt_mul_of_pos_left hx' (inv_pos.mpr ha)
        _ = 1 / 2 := by field_simp
    · simp [smul_smul, ha.ne']

theorem gradient_pullback {d : ℕ} {p a : ℝ} (hp : 2 ≤ p) (ha : 0 < a)
    (z : Vec d) (u : H1Function (translateSet z (a • Metric.ball (0 : Vec d) (1 / 2))))
    (hg : MemLp (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
      (volume.restrict (translateSet z (a • Metric.ball (0 : Vec d) (1 / 2))))) :
    let w := (u.untranslate z).unscale ha
    MemLp (fun q => euclideanNorm (w.grad q)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (1 / 2))) ∧
    (eLpNorm (fun q => euclideanNorm (w.grad q)) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (0 : Vec d) (1 / 2)))).toReal =
    a * (a ^ d) ^ (-(1 / p)) *
      (eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
        (volume.restrict (translateSet z (a • Metric.ball (0 : Vec d) (1 / 2))))).toReal := by
  let Q : Set (Vec d) := Metric.ball (0 : Vec d) (1 / 2)
  let f : Vec d → ℝ := fun y => euclideanNorm (u.grad (y + z))
  have htr := measurePreserving_addRight_restrict_translateSet z (a • Q)
  have hf : MemLp f (ENNReal.ofReal p) (volume.restrict (a • Q)) :=
    hg.comp_measurePreserving htr
  have hetr : eLpNorm f (ENNReal.ofReal p) (volume.restrict (a • Q)) =
      eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
        (volume.restrict (translateSet z (a • Q))) :=
    eLpNorm_comp_measurePreserving hg.aestronglyMeasurable htr
  have hmap := map_smul_volume_restrict ha Q
  have hfm : MemLp f (ENNReal.ofReal p)
      (Measure.map (fun q : Vec d => a • q) (volume.restrict Q)) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hcomp : MemLp (fun q => f (a • q)) (ENNReal.ofReal p) (volume.restrict Q) :=
    hfm.comp_of_map (measurable_const_smul a).aemeasurable
  have hfeq : (fun q => euclideanNorm (((u.untranslate z).unscale ha).grad q)) =
      fun q => a * f (a • q) := by
    funext q
    simp only [H1Function.unscale_grad, H1Function.untranslate_grad,
      euclideanNorm_smul, abs_of_pos ha]
    rfl
  dsimp only
  rw [hfeq]
  refine ⟨hcomp.const_mul a, ?_⟩
  have he := W1pFunction.eLpNorm_comp_smul_eq (p := ENNReal.ofReal p) ha
    ENNReal.ofReal_ne_top hf.aestronglyMeasurable
  have hE : eLpNorm (fun q => a * f (a • q)) (ENNReal.ofReal p) (volume.restrict Q) =
      ENNReal.ofReal a * eLpNorm (fun q => f (a • q)) (ENNReal.ofReal p)
        (volume.restrict Q) := by
    change eLpNorm (a • fun q => f (a • q)) _ _ = _
    simpa only [Real.enorm_eq_ofReal ha.le] using
      eLpNorm_const_smul a (fun q => f (a • q)) (ENNReal.ofReal p) (volume.restrict Q)
  rw [hE, he, hetr, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (a ^ d)⁻¹)]
  have hp0 : 0 ≤ p := by linarith
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0]
  rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  ring

theorem cast_h1_toFun {d : ℕ} {S T : Set (Vec d)} (h : S = T) (u : H1Function S) :
    (h ▸ u).toFun = u.toFun := by
  cases h
  rfl

theorem cast_h1_grad {d : ℕ} {S T : Set (Vec d)} (h : S = T) (u : H1Function S) :
    (h ▸ u).grad = u.grad := by
  cases h
  rfl

theorem scaling_factor (d : ℕ) (p alpha : ℝ) {l : ℝ} (hl : 0 < l) :
    (2 * l) * ((2 * l) ^ d) ^ (-(1 / p)) * ((2 * l)⁻¹) ^ alpha =
      (2 : ℝ) ^ (1 - alpha) * l ^ (1 - alpha) / ((2 * l) ^ d) ^ (1 / p) := by
  let a : ℝ := 2 * l
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : a * (a⁻¹) ^ alpha = a ^ (1 - alpha) := by
    rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    calc
      _ = a ^ (1 : ℝ) * a ^ (-alpha) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ha]; rfl
  have hD : (a ^ d) ^ (-(1 / p)) = ((a ^ d) ^ (1 / p))⁻¹ :=
    Real.rpow_neg (by positivity) _
  calc
    _ = (a * (a⁻¹) ^ alpha) * (a ^ d) ^ (-(1 / p)) := by dsimp [a]; ring
    _ = a ^ (1 - alpha) / (a ^ d) ^ (1 / p) := by rw [hA, hD]; rfl
    _ = _ := by dsimp [a]; rw [Real.mul_rpow (by norm_num) hl.le]

theorem morrey_cube (d : ℕ) (p alpha : ℝ)
    (hp : 2 ≤ p) (halpha : 0 < alpha) (hpa : alpha < 1 - (d : ℝ) / p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x0 : Vec d) (l : ℝ), 0 < l →
      ∀ u : H1Function (Metric.ball x0 l),
        MemLp (fun x => euclideanNorm (u.grad x))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l)) →
        ∃ U : Vec d → ℝ, Continuous U ∧
          (u.toFun =ᵐ[volume.restrict (Metric.ball x0 l)] U) ∧
          ∀ x ∈ Metric.closedBall x0 l, ∀ y ∈ Metric.closedBall x0 l,
            |U x - U y| ≤ C * l ^ (1 - alpha) *
              ((eLpNorm (fun q => euclideanNorm (u.grad q))
                (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l))).toReal /
                (volume.real (Metric.ball x0 l)) ^ (1 / p)) * ‖x - y‖ ^ alpha := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, one_pos, ?_⟩
    intro x0 l hl u _hg
    refine ⟨fun _ => u.toFun x0, continuous_const, ?_, ?_⟩
    · filter_upwards with x
      exact congrArg u.toFun (Subsingleton.elim x x0)
    · intro x _hx y _hy
      rw [sub_self, abs_zero]
      positivity
  · let : NeZero d := ⟨hd⟩
    let B : ℝ := _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_regularity_holderConst d alpha *
      oscillationConst d * ((3 : ℝ) ^ d) ^ (1 / p)
    have hB : 0 ≤ B := by
      have hCh := _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_regularity_holderConst_nonneg d halpha
      have hCd := unitMeanZeroPoincareConst_nonneg d
      unfold B oscillationConst
      positivity
    let C : ℝ := 1 + B * (2 : ℝ) ^ (1 - alpha)
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, hC, ?_⟩
    intro x0 l hl u hg
    let Q : Set (Vec d) := Metric.ball (0 : Vec d) (1 / 2)
    let a : ℝ := 2 * l
    have ha : 0 < a := by dsimp [a]; positivity
    have hEq : translateSet x0 (a • Q) = Metric.ball x0 l := by
      simpa only [a, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
        affine_cube_eq (d := d) x0 ha
    let uA : H1Function (translateSet x0 (a • Q)) := hEq.symm ▸ u
    have huAf : uA.toFun = u.toFun := cast_h1_toFun hEq.symm u
    have huAg : uA.grad = u.grad := cast_h1_grad hEq.symm u
    have hgA : MemLp (fun q => euclideanNorm (uA.grad q)) (ENNReal.ofReal p)
        (volume.restrict (translateSet x0 (a • Q))) := by
      simpa only [huAg, hEq] using hg
    let w : H1Function Q := (uA.untranslate x0).unscale ha
    obtain ⟨hwMem, hwNorm⟩ := gradient_pullback hp ha x0 uA hgA
    obtain ⟨W, hWcont, hWae, hWbound⟩ := unit_morrey hp halpha hpa w hwMem
    let T : Vec d → Vec d := fun x => a⁻¹ • (x - x0)
    refine ⟨fun x => W (T x), hWcont.comp (by dsimp [T]; fun_prop), ?_, ?_⟩
    · have hmap := map_smul_volume_restrict (a := a⁻¹) (inv_pos.mpr ha) (a • Q)
      have hset : a⁻¹ • (a • Q) = Q := by simp [smul_smul, ha.ne']
      rw [hset] at hmap
      have hRepMap : w.toFun =ᵐ[Measure.map (fun q : Vec d => a⁻¹ • q)
          (volume.restrict (a • Q))] W := by
        rw [hmap]
        exact (Measure.ae_ennreal_smul_measure_iff
          (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))).mpr hWae
      have hRep := ae_of_ae_map (measurable_const_smul a⁻¹).aemeasurable hRepMap
      have hRep' : (fun q => uA.toFun (q + x0)) =ᵐ[volume.restrict (a • Q)]
          (fun q => W (a⁻¹ • q)) := by
        simpa only [w, H1Function.unscale_toFun, H1Function.untranslate_toFun,
          smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using! hRep
      have hTr := (measurePreserving_subRight_restrict_translateSet x0 (a • Q)).quasiMeasurePreserving.ae hRep'
      simp only [sub_add_cancel, huAf] at hTr
      rw [hEq] at hTr
      exact hTr
    · intro x hx y hy
      have hTmem : ∀ z ∈ Metric.closedBall x0 l, T z ∈ Metric.closedBall (0 : Vec d) (1 / 2) := by
        intro z hz
        rw [Metric.mem_closedBall, dist_zero_right]
        dsimp [T]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
        have hzn : ‖z - x0‖ ≤ l := Metric.mem_closedBall.mp hz
        calc
          _ ≤ a⁻¹ * l := mul_le_mul_of_nonneg_left hzn (inv_nonneg.mpr ha.le)
          _ = 1 / 2 := by dsimp [a]; field_simp
      have hTdist : ‖T x - T y‖ = a⁻¹ * ‖x - y‖ := by
        have he : T x - T y = a⁻¹ • (x - y) := by
          dsimp [T]
          rw [← smul_sub]
          congr 1
          abel
        rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
      have hvol : volume.real (Metric.ball x0 l) = a ^ d := by
        rw [Measure.real, volume_ball_spatial x0 hl, ENNReal.toReal_ofReal (by positivity)]
      have hGrad : (eLpNorm (fun q => euclideanNorm (w.grad q)) (ENNReal.ofReal p)
          (volume.restrict Q)).toReal = a * (a ^ d) ^ (-(1 / p)) *
          (eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x0 l))).toReal := by
        simpa only [huAg, ← hEq] using hwNorm
      have hFactor : a * (a ^ d) ^ (-(1 / p)) * (a⁻¹) ^ alpha =
          (2 : ℝ) ^ (1 - alpha) * l ^ (1 - alpha) / (a ^ d) ^ (1 / p) :=
        scaling_factor d p alpha hl
      have hbase := hWbound (T x) (hTmem x hx) (T y) (hTmem y hy)
      rw [hTdist, hGrad, Real.mul_rpow (inv_nonneg.mpr ha.le) (norm_nonneg _)] at hbase
      have hcoeff : B * (2 : ℝ) ^ (1 - alpha) ≤ C := by dsimp [C]; linarith
      calc
        |W (T x) - W (T y)| ≤ B *
          (a * (a ^ d) ^ (-(1 / p)) *
            (eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x0 l))).toReal) *
            ((a⁻¹) ^ alpha * ‖x - y‖ ^ alpha) := hbase
        _ = (B * (eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x0 l))).toReal * ‖x - y‖ ^ alpha) *
            (a * (a ^ d) ^ (-(1 / p)) * (a⁻¹) ^ alpha) := by ring
        _ = (B * (2 : ℝ) ^ (1 - alpha)) * l ^ (1 - alpha) *
            ((eLpNorm (fun q => euclideanNorm (u.grad q)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x0 l))).toReal /
              (volume.real (Metric.ball x0 l)) ^ (1 / p)) * ‖x - y‖ ^ alpha := by
          rw [hFactor, hvol]
          ring
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity))
            (by positivity)

end SubdiffusiveProcess.Morrey
