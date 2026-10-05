module

public import SubdiffusiveProcess.PartProcess.FreeResolvent
public import SubdiffusiveProcess.PartProcess.FeynmanKacResolvent

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

/-- Duhamel's equation on bounded nonnegative `L²` inputs. -/
theorem potentialOcc_duhamel_bounded (hm : IsLocallyFiniteMeasure m)
    (hpos : m.IsOpenPosMeasure) (S : Data d m)
    (q : (Fin d → ℝ) → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (B : ℝ) (hB : ∀ x, q x ≤ B) (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent S.form.toClosedForm α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) (C : ℝ) (hfC : ∀ x, |f x| ≤ C)
    (hu : MemLp (fun x => q x * (potentialOcc S.law q α f x).toReal) 2 m) :
    (fun x => (potentialOcc S.law q α f x).toReal) =ᵐ[m]
      fun x => G (hfL.toLp f) x -
        G (hu.toLp (fun y => q y * (potentialOcc S.law q α f y).toReal)) x := by
  let u : (Fin d → ℝ) → ℝ := fun x => (potentialOcc S.law q α f x).toReal
  have hum : Measurable u := by
    let := S.markov
    exact (potentialOcc_measurable S.law q hq α f hf).ennreal_toReal
  have hu0 : ∀ x, 0 ≤ u x := fun x => ENNReal.toReal_nonneg
  have hureal : realOcc S q α f = u := funext (realOcc_eq_toReal S hq hq0 hα hf hf0 hfC)
  have hBu : ∀ x, |q x * u x| ≤ B * (C / α) := by
    intro x
    rw [abs_mul, abs_of_nonneg (hq0 x)]
    have hb0 : 0 ≤ B := (hq0 x).trans (hB x)
    apply mul_le_mul (hB x) _ (abs_nonneg _) hb0
    rw [← congrFun hureal x]
    exact realOcc_norm_le S hq0 hα hfC x
  have hqfree := (free_association hm hpos S α hα G hG
    (fun x => q x * u x) (hq.mul hum)
      (fun x => mul_nonneg (hq0 x) (hu0 x)) hu).2
  have hfree := (free_association hm hpos S α hα G hG f hf hf0 hfL).2
  have hid := realOcc_duhamel S hq hq0 hB hα hf hfC
  have hfreeReal : S.semigroup.kernelResolventReal α f =
      fun x => (potentialOcc S.law 0 α f x).toReal := by
    rw [← realOcc_zero_eq_kernelResolventReal S α hf]
    exact funext (realOcc_eq_toReal S measurable_const (fun _ => le_rfl) hα hf hf0 hfC)
  have hqfreeReal : S.semigroup.kernelResolventReal α (fun x => q x * u x) =
      fun x => (potentialOcc S.law 0 α (fun x => q x * u x) x).toReal := by
    rw [← realOcc_zero_eq_kernelResolventReal S α
      (f := fun x => q x * u x) (hq.mul hum)]
    exact funext (realOcc_eq_toReal S measurable_const (fun _ => le_rfl) hα
      (hq.mul hum) (fun x => mul_nonneg (hq0 x) (hu0 x)) hBu)
  rw [hureal, hfreeReal, hqfreeReal] at hid
  filter_upwards [hfree, hqfree] with x hx hy
  change u x = _
  have hp := congrFun hid x
  simpa only [Pi.sub_apply, hx, hy] using hp

end SubdiffusiveProcess.PartProcess
