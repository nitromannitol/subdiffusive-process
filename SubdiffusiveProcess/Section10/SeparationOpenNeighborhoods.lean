module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PointwiseRangeDependence

@[expose] public section

/-! The uniform squared-separation condition gives separated open
enclosing sets in the native Euclidean norm, also for empty/unbounded sets. -/

open Homogenization MeasureTheory

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Common-radius unions of balls give open neighborhoods separated at the
native finite-dependence range. No boundedness or nonemptiness is assumed. -/
theorem open_neighborhoods_of_squared_separation {d : ℕ}
    (A B : Set (Vec d))
    (hsep : ∃ c : ℝ, (d : ℝ) < c ∧
      ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) :
    ∃ U V : Set (Vec d), IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      ∀ a ∈ U, ∀ b ∈ V, Real.sqrt (d : ℝ) ≤ euclideanNorm (a - b) := by
  obtain ⟨c, hc, hab⟩ := hsep
  have hroot := Real.sqrt_lt_sqrt (Nat.cast_nonneg d) hc
  let eps : ℝ := (Real.sqrt c - Real.sqrt (d : ℝ)) / (2 * (d : ℝ) + 2)
  have heps : 0 < eps := div_pos (sub_pos.mpr hroot) (by positivity)
  have hmul : (2 * (d : ℝ) + 2) * eps = Real.sqrt c - Real.sqrt (d : ℝ) :=
    mul_div_cancel₀ _ (by positivity)
  have hgap : Real.sqrt (d : ℝ) + 2 * (d : ℝ) * eps ≤ Real.sqrt c := by
    nlinarith
  have hcenters : ∀ a ∈ A, ∀ b ∈ B, Real.sqrt c ≤ euclideanNorm (a - b) := by
    intro a ha b hb
    apply Real.sqrt_le_sqrt
    simpa only [vecNormSq, vecDot, Pi.sub_apply, pow_two] using hab a ha b hb
  let U : Set (Vec d) := ⋃ a : A, Metric.ball (a : Vec d) eps
  let V : Set (Vec d) := ⋃ b : B, Metric.ball (b : Vec d) eps
  refine ⟨U, V, isOpen_iUnion (fun _ => Metric.isOpen_ball),
    isOpen_iUnion (fun _ => Metric.isOpen_ball), ?_, ?_, ?_⟩
  · intro a ha
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, Metric.mem_ball_self heps⟩
  · intro b hb
    exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, Metric.mem_ball_self heps⟩
  · intro x hx y hy
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
    obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hy
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.potentialRangeSeparated_ball
      (hgap.trans (hcenters a a.property b b.property)) hxa hyb

end SubdiffusiveProcess.Section10
