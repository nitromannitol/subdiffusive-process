module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab

theorem normalizedL2On_eq_sqrt_volumeAverage {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On W f = Real.sqrt (Homogenization.volumeAverage W (fun x => f x ^ 2)) := by
  rfl

theorem averageOn_eq_volumeAverage {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) :
    averageOn W f = Homogenization.volumeAverage W f := by
  rfl

theorem normalizedL2On_eq_sqrt_averageOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On W f = Real.sqrt (averageOn W (fun x => f x ^ 2)) := by
  simp [normalizedL2On, averageOn]

theorem abs_normalizedL2On {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) :
    |normalizedL2On W f| = normalizedL2On W f := by
  simp only [normalizedL2On]
  exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem normalizedL2On_eq_zero_of_volumeAverage_nonpos {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ)
    (h : Homogenization.volumeAverage W (fun x => f x ^ 2) ≤ 0) :
    normalizedL2On W f = 0 := by
  simp only [normalizedL2On]
  exact Real.sqrt_eq_zero'.mpr h

theorem averageOn_congr {d : ℕ} (W : Set (Vec d)) (f g : Vec d → ℝ)
    (h : ∀ x, f x = g x) :
    averageOn W f = averageOn W g := by
  simp only [averageOn]
  exact congrArg _ (funext h)

theorem normalizedL2On_le_of_volumeAverage_le {d : ℕ} (W : Set (Vec d)) (f g : Vec d → ℝ)
    (h : Homogenization.volumeAverage W (fun x => f x ^ 2) ≤ Homogenization.volumeAverage W (fun x => g x ^ 2)) :
    normalizedL2On W f ≤ normalizedL2On W g := by
  simp only [normalizedL2On]
  exact Real.sqrt_le_sqrt h

end SubdiffusiveProcess.CoarseGrainingVocab
