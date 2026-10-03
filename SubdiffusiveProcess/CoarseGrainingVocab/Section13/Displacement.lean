module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section13.ExitMoments

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section13

variable {d : ℕ}

/-- The displacement from `x` at time `s`, taken to be `0` at the cemetery. -/
def displacementAt (x : Vec d) (s : ℝ≥0) (w : Path d) : ℝ≥0∞ :=
  Sum.elim (fun y : Vec d => ENNReal.ofReal (euclideanNorm (y - x)))
    (fun _ => (0 : ℝ≥0∞)) (LifetimePath.coordinate s w)

/-- `sup_{0 <= s <= t} |X_s - x|`. -/
def maxDisplacement (x : Vec d) (t : ℝ) (w : Path d) : ℝ≥0∞ :=
  ⨆ s : {s : ℝ≥0 // (s : ℝ) ≤ t}, displacementAt x s.val w

/-- `P_x[sup_{0 <= s <= t} |X_s - x| >= R]`. -/
def maxDisplacementTail (law : Kernel (Vec d) (Path d)) (x : Vec d) (t R : ℝ) : ℝ≥0∞ :=
  law x {w | ENNReal.ofReal R ≤ maxDisplacement x t w}

/-- `E_x[(sup_{0 <= s <= t} |X_s - x|)^q]`. -/
def displacementMoment (law : Kernel (Vec d) (Path d)) (x : Vec d) (t q : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, (maxDisplacement x t w) ^ q ∂law x

@[simp] theorem displacementAt_delta (x : Vec d) (s : ℝ≥0) (w : Path d)
    (h : LifetimePath.coordinate s w = Cemetery.delta) :
    displacementAt x s w = 0 := by
  simp [displacementAt, h]

@[simp] theorem displacementAt_alive (x y : Vec d) (s : ℝ≥0) (w : Path d)
    (h : LifetimePath.coordinate s w = Cemetery.alive y) :
    displacementAt x s w = ENNReal.ofReal (euclideanNorm (y - x)) := by
  simp [displacementAt, h]

/-- The running maximum is monotone in the time horizon. -/
theorem maxDisplacement_mono (x : Vec d) {t t' : ℝ} (h : t ≤ t') (w : Path d) :
    maxDisplacement x t w ≤ maxDisplacement x t' w :=
  iSup_le fun s => le_iSup_of_le ⟨s.val, s.property.trans h⟩ le_rfl

/-- Hence so is its tail, in the horizon. -/
theorem maxDisplacementTail_mono_time (law : Kernel (Vec d) (Path d)) (x : Vec d)
    {t t' : ℝ} (h : t ≤ t') (R : ℝ) :
    maxDisplacementTail law x t R ≤ maxDisplacementTail law x t' R :=
  measure_mono fun w hw => le_trans hw (maxDisplacement_mono x h w)

/-- The tail is antitone in the radius. -/
theorem maxDisplacementTail_anti_radius (law : Kernel (Vec d) (Path d)) (x : Vec d)
    (t : ℝ) {R R' : ℝ} (h : R ≤ R') :
    maxDisplacementTail law x t R' ≤ maxDisplacementTail law x t R :=
  measure_mono fun _ hw => le_trans (ENNReal.ofReal_le_ofReal h) hw

end SubdiffusiveProcess.CoarseGrainingVocab.Section13
