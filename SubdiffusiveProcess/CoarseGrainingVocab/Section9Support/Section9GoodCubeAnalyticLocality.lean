module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCoefficientLocality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
@[expose] public section

/-! Restricted weighted measures, weak Poisson equations and the good-cube Sobolev display depend only on the coefficient on their domain. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

theorem goodCube_weightedMeasure_restrict_congr
    {d : ℕ} {a b : Vec d → ℝ} {U : Set (Vec d)}
    (hab : a =ᵐ[volume.restrict U] b) :
    (weightedMeasure a).restrict U = (weightedMeasure b).restrict U := by
  have hae : (fun x => ENNReal.ofReal (a x)) =ᵐ[volume.restrict U]
      (fun x => ENNReal.ofReal (b x)) := by
    filter_upwards [hab] with x hx
    rw [hx]
  show (volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict U
      = (volume.withDensity (fun x => ENNReal.ofReal (b x))).restrict U
  rw [restrict_withDensity', restrict_withDensity',
    withDensity_congr_ae hae]

theorem goodCube_massiveWeakSolution_congr_coeff
    {d : ℕ} {a b rho eta : Vec d → ℝ} {U : Set (Vec d)}
    (hab : a =ᵐ[volume.restrict U] b) (hre : rho =ᵐ[volume.restrict U] eta)
    (mu : ℝ) (u : H1Function U) (f : Vec d → ℝ) :
    IsMassiveWeakSolutionOn a rho mu U u f ↔
      IsMassiveWeakSolutionOn b eta mu U u f := by
  constructor
  · intro h φ
    have hae1 : ∀ᵐ x ∂volume.restrict U, rho x * u.toFun x * φ.toH1Function.toFun x
        = eta x * u.toFun x * φ.toH1Function.toFun x := by
      filter_upwards [hre] with x hx
      rw [hx]
    have hae2 : ∀ᵐ x ∂volume.restrict U,
        vecDot (a x • u.grad x) (φ.toH1Function.grad x)
          = vecDot (b x • u.grad x) (φ.toH1Function.grad x) := by
      filter_upwards [hab] with x hx
      rw [hx]
    have hae3 : ∀ᵐ x ∂volume.restrict U, rho x * f x * φ.toH1Function.toFun x
        = eta x * f x * φ.toH1Function.toFun x := by
      filter_upwards [hre] with x hx
      rw [hx]
    rw [← integral_congr_ae hae1, ← integral_congr_ae hae2, ← integral_congr_ae hae3]
    exact h φ
  · intro h φ
    have hae1 : ∀ᵐ x ∂volume.restrict U, eta x * u.toFun x * φ.toH1Function.toFun x
        = rho x * u.toFun x * φ.toH1Function.toFun x := by
      filter_upwards [hre] with x hx
      rw [← hx]
    have hae2 : ∀ᵐ x ∂volume.restrict U,
        vecDot (b x • u.grad x) (φ.toH1Function.grad x)
          = vecDot (a x • u.grad x) (φ.toH1Function.grad x) := by
      filter_upwards [hab] with x hx
      rw [← hx]
    have hae3 : ∀ᵐ x ∂volume.restrict U, eta x * f x * φ.toH1Function.toFun x
        = rho x * f x * φ.toH1Function.toFun x := by
      filter_upwards [hre] with x hx
      rw [← hx]
    rw [← integral_congr_ae hae1, ← integral_congr_ae hae2, ← integral_congr_ae hae3]
    exact h φ

theorem goodCube_sobolevDisplay_congr_coeff
    {d : ℕ} {a b : Vec d → ℝ} (Q : Cube d)
    (hab : a =ᵐ[volume.restrict (cubeSet Q)] b)
    (p A : ℝ) (clock : ℝ → ℝ) :
    GoodCubeSobolevDisplay a p A clock Q ↔ GoodCubeSobolevDisplay b p A clock Q := by
  have hmeas : (volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict (cubeSet Q)
      = (volume.withDensity (fun x => ENNReal.ofReal (b x))).restrict (cubeSet Q) :=
    goodCube_weightedMeasure_restrict_congr hab
  have hmass : weightedMeasure a (cubeSet Q) = weightedMeasure b (cubeSet Q) := by
    have h := congrArg (fun mu : Measure (Vec d) => mu Set.univ)
      (goodCube_weightedMeasure_restrict_congr hab)
    simpa only [Measure.restrict_apply_univ] using h
  have henergy : ∀ g : H1Function (cubeSet Q),
      energy a (cubeSet Q) g = energy b (cubeSet Q) g := by
    intro g
    unfold energy
    refine integral_congr_ae ?_
    filter_upwards [hab] with x hx
    rw [hx]
  have hlp : ∀ f : H10Function (cubeSet Q),
      lpSq a (cubeSet Q) p f.toH1Function.toFun
        = lpSq b (cubeSet Q) p f.toH1Function.toFun := by
    intro f
    unfold lpSq
    rw [hmeas]
  constructor
  · intro h
    unfold GoodCubeSobolevDisplay at h ⊢
    intro f
    rw [← hlp f, ← hmass, ← henergy f.toH1Function]
    exact h f
  · intro h
    unfold GoodCubeSobolevDisplay at h ⊢
    intro f
    rw [hlp f, hmass, henergy f.toH1Function]
    exact h f

/-- An almost-everywhere ambient majorant bounds the outer measure of the exact coefficient-local failure. -/
theorem goodCube_exists_restricted_failure_le_ambient
    {Omega V : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (observe : Omega → V) (P : Omega → Prop)
    (hlocal : ∀ omega omega', observe omega = observe omega' → (P omega ↔ P omega'))
    (Bad : Set Omega) {budget : ℝ≥0∞} (hBad : mu Bad ≤ budget)
    (hgood : ∀ᵐ omega ∂mu, omega ∉ Bad → P omega) :
    ∃ bad : Set V, observe ⁻¹' bad = {omega | ¬ P omega} ∧
      mu (observe ⁻¹' bad) ≤ budget := by
  obtain ⟨bad, hbad⟩ := goodCube_exists_restricted_failure observe P hlocal
  refine ⟨bad, hbad, (measure_mono_ae ?_).trans hBad⟩
  filter_upwards [hgood] with omega homega hmem
  by_contra hnot
  have hfail : ¬ P omega := by simpa only [hbad, mem_ofPred_eq] using hmem
  exact hfail (homega hnot)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
