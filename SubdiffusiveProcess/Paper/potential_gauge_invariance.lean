module

public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.killed_generator_normalization
public import SubdiffusiveProcess.Vocab.Ahom
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import SubdiffusiveProcess.Paper.in_crossing

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- Smoothness index convention: in Mathlib v4.26.0, the bare index in
`ContDiff ℝ ⊤` elaborates in `WithTop ℕ∞` and therefore means `ω` (real-analytic),
not `∞`. Paired with `HasCompactSupport`, that real-analytic condition is satisfied
only by `f = 0`. The smooth condition used here is `ContDiff ℝ (⊤ : ℕ∞)`, whose
index is `∞`; the gauge identity thus applies to the larger class of smooth
compactly supported test functions. -/

theorem aux_potential_gauge_invariance_potential
    {d : Nat} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffPotential Hc omega N x = cutoffPotential H omega N x - c omega := by
  unfold cutoffPotential
  rw [hHc]
  ring

theorem aux_potential_gauge_invariance_exp_shift (a b c : ℝ) :
    Real.exp ((a - c) - b) = Real.exp (-c) * Real.exp (a - b) := by
  rw [show (a - c) - b = (-c) + (a - b) by ring, Real.exp_add]

theorem aux_potential_gauge_invariance_exp_neg_shift (a c : ℝ) :
    Real.exp (-(a - c)) = Real.exp c * Real.exp (-a) := by
  rw [show -(a - c) = c + (-a) by ring, Real.exp_add]

theorem aux_potential_gauge_invariance_coefficient
    {d : Nat} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M Hc omega N x = Real.exp (-(c omega)) * cutoffCoefficient M H omega N x := by
  unfold cutoffCoefficient
  rw [aux_potential_gauge_invariance_potential H c Hc hHc]
  rw [aux_potential_gauge_invariance_exp_shift]
  ring

theorem aux_potential_gauge_invariance_speed_density
    {d : Nat} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffSpeedDensity M Hc omega N x = Real.exp (-(c omega)) *
      cutoffSpeedDensity M H omega N x := by
  unfold cutoffSpeedDensity
  rw [aux_potential_gauge_invariance_potential H c Hc hHc]
  exact aux_potential_gauge_invariance_exp_shift _ _ _

theorem aux_potential_gauge_invariance_fderiv
    {d : Nat} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (f : SpatialCoordinates d → ℝ)
    (i : Fin d) :
    fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
      (fderiv ℝ f y) (Pi.single i 1)) =
      Real.exp (-(c omega)) • fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
        (fderiv ℝ f y) (Pi.single i 1)) := by
  have hfun : (fun y => Real.exp (cutoffPotential Hc omega N y) *
      (fderiv ℝ f y) (Pi.single i 1)) =
      Real.exp (-(c omega)) • (fun y => Real.exp (cutoffPotential H omega N y) *
        (fderiv ℝ f y) (Pi.single i 1)) := by
    funext y
    rw [aux_potential_gauge_invariance_potential H c Hc hHc]
    rw [show cutoffPotential H omega N y - c omega =
      (-(c omega)) + cutoffPotential H omega N y by ring, Real.exp_add]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  exact fderiv_const_smul_field _

theorem aux_potential_gauge_invariance_generator
    {d : Nat} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    Real.exp (-(cutoffPotential Hc omega N x)) *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
            (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
      Real.exp (-(cutoffPotential H omega N x)) *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
            (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) := by
  rw [aux_potential_gauge_invariance_potential H c Hc hHc]
  rw [aux_potential_gauge_invariance_exp_neg_shift]
  have hsum :
      (∑ i : Fin d,
        (fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
          (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
        Real.exp (-(c omega)) *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) := by
    calc
      (∑ i : Fin d,
          (fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
            (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
          ∑ i : Fin d, Real.exp (-(c omega)) *
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [aux_potential_gauge_invariance_fderiv H c Hc hHc]
        rfl
      _ = Real.exp (-(c omega)) *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) := by
        rw [Finset.mul_sum]
  rw [hsum]
  calc
    Real.exp (c omega) * Real.exp (-cutoffPotential H omega N x) *
        (Real.exp (-(c omega)) *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1))) =
        (Real.exp (c omega) * Real.exp (-(c omega))) *
          (Real.exp (-cutoffPotential H omega N x) *
            (∑ i : Fin d,
              (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
                (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1))) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem aux_potential_gauge_invariance_measure
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M Hc omega N =
      ENNReal.ofReal (Real.exp (-(c omega))) • cutoffSpeedMeasure M H omega N := by
  let r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c omega)))
  have hden : (fun x => ENNReal.ofReal (cutoffSpeedDensity M Hc omega N x)) =
      r • (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) := by
    funext x
    rw [aux_potential_gauge_invariance_speed_density M H c Hc hHc]
    dsimp [r]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  unfold cutoffSpeedMeasure
  change volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M Hc omega N x)) =
    r • volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x))
  rw [hden]
  exact withDensity_smul' _ _ (by dsimp [r]; simp)

theorem aux_potential_gauge_invariance_coefficient_form
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u v : SobolevData (centeredCube z r hr)) :
    sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M Hc omega N z hr) u v =
      Real.exp (-(c omega)) *
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u v := by
  let Ω := centeredCube z r hr
  let K := closedCube z r hr
  let : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K)) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  calc
    (∑ i : Fin d,
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M Hc omega N z hr).val x *
            ((u.2 i) x * (v.2 i) x)) =
      ∑ i : Fin d, Real.exp (-(c omega)) *
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x *
            ((u.2 i) x * (v.2 i) x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [
          normalizedContinuousPositiveCoefficient_coeFn K
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M Hc omega N z hr)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M Hc omega N z hr) 1 one_pos,
          normalizedContinuousPositiveCoefficient_coeFn K
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N z hr)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos,
          ae_restrict_mem Ω.isOpen.measurableSet] with x hHc' hH' hx
      have hHc'' := hHc' hx
      have hH'' := hH' hx
      simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM, div_one] at hHc'' hH''
      have hpcHc : (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M Hc omega N z hr).val x =
          cutoffCoefficient M Hc omega N x := by
        simpa [_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient, _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM] using hHc''
      have hpcH : (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x =
          cutoffCoefficient M H omega N x := by
        simpa [_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient, _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM] using hH''
      rw [hpcHc, hpcH, aux_potential_gauge_invariance_coefficient M H c Hc hHc]
      ring
    _ = Real.exp (-(c omega)) *
        (∑ i : Fin d,
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x *
              ((u.2 i) x * (v.2 i) x)) := by
      rw [Finset.mul_sum]

theorem aux_potential_gauge_invariance_weak_solution_scale
    {d : Nat} {a rho : SpatialCoordinates d → ℝ} (q : ℝ)
    {mu : ℝ} {W : Set (SpatialCoordinates d)}
    {u : Homogenization.H1Function W}
    {f : SpatialCoordinates d → ℝ}
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn a rho mu W u f) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
      (fun x => q * a x) (fun x => q * rho x) mu W u f := by
  intro φ
  have hEq := hu φ
  have hmass :
      (∫ x in W, (q * rho x) * u.toFun x * φ.toH1Function.toFun x ∂volume) =
        q * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hen :
      (∫ x in W, Homogenization.vecDot ((q * a x) • u.grad x)
          (φ.toH1Function.grad x) ∂volume) =
        q * ∫ x in W, Homogenization.vecDot (a x • u.grad x)
          (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (q * a x) • u.grad x = q • (a x • u.grad x) by
      exact mul_smul q (a x) (u.grad x)]
    rw [Homogenization.vecDot_smul_left]
  have hrhs :
      (∫ x in W, (q * rho x) * f x * φ.toH1Function.toFun x ∂volume) =
        q * ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hmass, hen, hrhs]
  linear_combination q * hEq

theorem aux_potential_gauge_invariance_crossing
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ) (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) :
    in_crossing M H PN KN ↔ in_crossing M Hc PN KN := by
  constructor
  · intro h
    unfold in_crossing at h ⊢
    rcases h with ⟨hres, hcons, hpaths⟩
    refine ⟨?_, hcons, hpaths⟩
    filter_upwards [hres] with omega hω
    intro N
    obtain ⟨D, hD, hweak, hLap⟩ := hω N
    refine ⟨D, hD, ?_, hLap⟩
    intro mu f W hW
    obtain ⟨u, huval, hu⟩ := hweak mu f W hW
    refine ⟨u, huval, ?_⟩
    have hscaled := aux_potential_gauge_invariance_weak_solution_scale
      (Real.exp (-(c omega))) hu
    have hcoef : (fun x => cutoffCoefficient M Hc omega N x) =
        (fun x => Real.exp (-(c omega)) * cutoffCoefficient M H omega N x) := by
      funext x
      exact aux_potential_gauge_invariance_coefficient M H c Hc hHc omega N x
    have hdensity : (fun x => cutoffSpeedDensity M Hc omega N x) =
        (fun x => Real.exp (-(c omega)) * cutoffSpeedDensity M H omega N x) := by
      funext x
      exact aux_potential_gauge_invariance_speed_density M H c Hc hHc omega N x
    simpa only [hcoef, hdensity] using hscaled
  · intro h
    unfold in_crossing at h ⊢
    rcases h with ⟨hres, hcons, hpaths⟩
    refine ⟨?_, hcons, hpaths⟩
    filter_upwards [hres] with omega hω
    intro N
    obtain ⟨D, hD, hweak, hLap⟩ := hω N
    refine ⟨D, hD, ?_, hLap⟩
    intro mu f W hW
    obtain ⟨u, huval, hu⟩ := hweak mu f W hW
    refine ⟨u, huval, ?_⟩
    have hscaled := aux_potential_gauge_invariance_weak_solution_scale
      (Real.exp (c omega)) hu
    have hcoef : (fun x => cutoffCoefficient M H omega N x) =
        (fun x => Real.exp (c omega) * cutoffCoefficient M Hc omega N x) := by
      funext x
      rw [aux_potential_gauge_invariance_coefficient M H c Hc hHc]
      calc
        cutoffCoefficient M H omega N x =
            (Real.exp (c omega) * Real.exp (-(c omega))) *
              cutoffCoefficient M H omega N x := by
          rw [← Real.exp_add]
          simp
        _ = Real.exp (c omega) *
            (Real.exp (-(c omega)) * cutoffCoefficient M H omega N x) := by ring
    have hdensity : (fun x => cutoffSpeedDensity M H omega N x) =
        (fun x => Real.exp (c omega) * cutoffSpeedDensity M Hc omega N x) := by
      funext x
      rw [aux_potential_gauge_invariance_speed_density M H c Hc hHc]
      calc
        cutoffSpeedDensity M H omega N x =
            (Real.exp (c omega) * Real.exp (-(c omega))) *
              cutoffSpeedDensity M H omega N x := by
          rw [← Real.exp_add]
          simp
        _ = Real.exp (c omega) *
            (Real.exp (-(c omega)) * cutoffSpeedDensity M H omega N x) := by ring
    simpa only [hcoef, hdensity] using hscaled




theorem potential_gauge_invariance
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (c : BilateralField d → ℝ)
    (Hc : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHc : ∀ omega x, Hc omega x = H omega x - c omega) :
    (∀ (omega : BilateralField d) (N : ℕ),
      (∀ (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d),
        Real.exp (-(cutoffPotential Hc omega N x)) *
            (∑ i : Fin d,
              (fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
                (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
          Real.exp (-(cutoffPotential H omega N x)) *
            (∑ i : Fin d,
              (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
                (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1))) ∧
      cutoffSpeedMeasure M Hc omega N =
        ENNReal.ofReal (Real.exp (-(c omega))) • cutoffSpeedMeasure M H omega N ∧
      (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
          (u v : SobolevData (centeredCube z r hr)),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M Hc omega N z hr) u v =
          Real.exp (-(c omega)) *
            sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u v) ∧
      (∀ x : SpatialCoordinates d,
        cutoffCoefficient M Hc omega N x =
          Real.exp (-(c omega)) * cutoffCoefficient M H omega N x)) ∧
    (∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
      in_crossing M H PN KN ↔ in_crossing M Hc PN KN) ∧
    (∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
      (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        ∃ (PC : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KC : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          in_crossing M Hc PC KC ∧
          (∀ N, IsMarkovKernel (KC N)) ∧
          (∀ N omega, PC N omega = PN N omega) ∧
          (∀ N omega x, KC N (omega, x) = KN N (omega, x))) ∧
    (∀ (omega : BilateralField d) (N : ℕ) (f : SpatialCoordinates d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ x : SpatialCoordinates d,
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp (-(cutoffPotential Hc omega N x)) *
              (∑ i : Fin d,
                (fderiv ℝ (fun y => Real.exp (cutoffPotential Hc omega N y) *
                  (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1))) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp (-(cutoffPotential H omega N x)) *
              (∑ i : Fin d,
                (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)))) := by
  have hcross := aux_potential_gauge_invariance_crossing M H c Hc hHc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro omega N
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro f x
      exact aux_potential_gauge_invariance_generator H c Hc hHc omega N f x
    · exact aux_potential_gauge_invariance_measure M H c Hc hHc omega N
    · intro z r hr u v
      exact aux_potential_gauge_invariance_coefficient_form M H c Hc hHc omega N z r hr u v
    · intro x
      exact aux_potential_gauge_invariance_coefficient M H c Hc hHc omega N x
  · intro PN KN
    exact hcross PN KN
  · intro PN KN hKN hin
    refine ⟨PN, KN, ?_, hKN, ?_, ?_⟩
    · exact (hcross PN KN).mp hin
    · intro N omega
      rfl
    · intro N omega x
      rfl
  · intro omega N f hf hcompact x
    rw [aux_potential_gauge_invariance_generator H c Hc hHc omega N f x]

end SubdiffusiveProcess.Paper
