module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationTestFunctions

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory Filter Topology
open scoped ZeroAtInfty

/-- Coupled bounded generator inequalities give a quadratic small-time bound. -/
theorem affine_c0Semigroup_coupled_bound {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (f g : hF.c0Semigroup.generatorDomain)
    (A B C D a : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hLf : ∀ y, hF.c0Semigroup.generator f y ≤ C*(a+(A+(f : C₀(Vec d, ℝ)) y)))
    (hLg : ∀ y, hF.c0Semigroup.generator g y ≤
      D*(a*(A+(f : C₀(Vec d, ℝ)) y)+(B+(g : C₀(Vec d, ℝ)) y)))
    (x : Vec d) (hfx : A+(f : C₀(Vec d, ℝ)) x = 0)
    (hgx : B+(g : C₀(Vec d, ℝ)) x = 0) (t : NNReal) :
    B+hF.c0Semigroup t g x ≤
      D*C*a^2*(t : ℝ)^2*Real.exp ((C+D)*(t : ℝ)) := by
  let S := hF.c0Semigroup
  have hfirst (s : NNReal) : A+S s f x ≤ C*a*(s : ℝ)*Real.exp (C*(s : ℝ)) := by
    have hb : ∀ y, S.generator f y ≤ C*((a+A)+(f : C₀(Vec d, ℝ)) y) := by
      intro y
      simpa only [add_assoc] using hLf y
    have h := affine_c0Semigroup_le_exp P hP hF f (a+A) C hb s x
    have h' : a+(A+S s f x) ≤ Real.exp (C*(s : ℝ))*a := by
      simpa only [add_assoc, hfx, add_zero] using h
    have he := mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (C*(s : ℝ))) ha
    nlinarith [he, h']
  let w : ℝ → ℝ := fun s ↦ B+S (Real.toNNReal s) g x
  let dw : ℝ → ℝ := fun s ↦ S (Real.toNNReal s) (S.generator g) x
  let eps : ℝ := D*C*a^2*(t : ℝ)*Real.exp (C*(t : ℝ))
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hw : Continuous w :=
    continuous_const.add ((evalC0CLM x).continuous.comp (S.continuous_operator_toNNReal g))
  have hdw : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt w (dw s) (Set.Ici s) s := by
    intro s hs
    have h := hasDerivWithinAt_affine_c0Orbit S g B x (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.1] at h
    exact h
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t, dw s ≤ D*w s+eps := by
    intro s hs
    let ts := Real.toNNReal s
    letI : IsProbabilityMeasure (P ts x) := ⟨hP ts x⟩
    have hiL : Integrable (fun y ↦ S.generator g y) (P ts x) :=
      (S.generator g).toBCF.integrable (P ts x)
    have hiF : Integrable (fun y ↦ (f : C₀(Vec d, ℝ)) y) (P ts x) :=
      (f : C₀(Vec d, ℝ)).toBCF.integrable (P ts x)
    have hiG : Integrable (fun y ↦ (g : C₀(Vec d, ℝ)) y) (P ts x) :=
      (g : C₀(Vec d, ℝ)).toBCF.integrable (P ts x)
    have hiR : Integrable (fun y ↦ D*(a*(A+(f : C₀(Vec d, ℝ)) y)+
        (B+(g : C₀(Vec d, ℝ)) y))) (P ts x) :=
      ((((integrable_const A).add hiF).const_mul a).add ((integrable_const B).add hiG)).const_mul D
    have hmain : dw s ≤ D*(a*(A+S ts f x)+w s) := by
      exact (integral_mono hiL hiR hLg).trans_eq
        (integral_affine_c0_pair (P ts x) (f : C₀(Vec d, ℝ)) (g : C₀(Vec d, ℝ)) A B a D)
    have hv := hfirst ts
    rw [Real.coe_toNNReal s hs.1] at hv
    have htime : C*a*s*Real.exp (C*s) ≤ C*a*(t : ℝ)*Real.exp (C*(t : ℝ)) := by
      gcongr <;> exact hs.2.le
    have hscaled := mul_le_mul_of_nonneg_left (hv.trans htime) (mul_nonneg hD ha)
    dsimp only [eps]
    nlinarith [hmain, hscaled]
  have hzero : w 0 ≤ 0 := by simpa [w] using hgx.le
  have hfinal := le_mul_time_exp_of_right_deriv_le hD heps t.coe_nonneg
    hw.continuousOn hdw hzero hbound
  have heq : eps*(t : ℝ)*Real.exp (D*(t : ℝ)) =
      D*C*a^2*(t : ℝ)^2*Real.exp ((C+D)*(t : ℝ)) := by
    dsimp only [eps]
    rw [add_mul, Real.exp_add]
    ring
  simpa only [w, Real.toNNReal_coe] using hfinal.trans_eq heq

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
