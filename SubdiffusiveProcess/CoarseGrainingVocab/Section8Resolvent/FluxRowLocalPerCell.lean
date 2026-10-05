module

public import SubdiffusiveProcess.Section2.GeneralCoarseGraining
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowLocalDual

@[expose] public section

/-!
# The per-cell coarse-graining estimate for the resolvent flux

This specializes the proved general coarse-graining anchor at the four
parameters used in the whole-space resolvent proof:

`p = 2`, `s₁ = 3 sigma / 4`, `s = sigma`, and
`s₂ = (1 + sigma) / 2`.

The local field on the left is the physical coefficient defect
`(a - alpha I) grad u`, not merely the comparison flux.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The lower fractional order `3 sigma / 4` used by the flux row. -/
def fluxRowLocalLowerOrder (sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨3 * sigma / 4, by constructor <;> nlinarith [hsigma.1, hsigma.2]⟩

/-- The target negative order `sigma`. -/
def fluxRowLocalOrder (sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨sigma, hsigma⟩

/-- The positive datum order `(1 + sigma) / 2`. -/
def fluxRowLocalUpperOrder (sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    FractionalOrder :=
  ⟨(1 + sigma) / 2, by constructor <;> nlinarith [hsigma.1, hsigma.2]⟩

@[simp] theorem fluxRowLocalLowerOrder_value (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    (fluxRowLocalLowerOrder sigma hsigma).1 = 3 * sigma / 4 := rfl

@[simp] theorem fluxRowLocalOrder_value (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    (fluxRowLocalOrder sigma hsigma).1 = sigma := rfl

@[simp] theorem fluxRowLocalUpperOrder_value (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    (fluxRowLocalUpperOrder sigma hsigma).1 = (1 + sigma) / 2 := rfl

/-- The exact right side of the coarse-graining theorem after the
flux-row specialization. -/
noncomputable def fluxRowLocalCoarseGrainingRHS {d : ℕ} [NeZero d]
    (C : ℝ) (m n : ℤ) (hnm : n < m) (a : Ch02.TriadicCoeffFamily d)
    (alpha sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (g : CubeEuclideanWspField (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
    (u : H1Function (openCubeSet (originCube d m))) : ℝ≥0∞ :=
  ENNReal.ofReal
      (C * Real.rpow sigma (-(3 / 2 : ℝ)) * Real.sqrt alpha) *
    paperHomogenizationError (originCube d m) n (3 * sigma / 4)
      .infinity (.finite 1) a alpha *
    weightedLocalSymmetricEnergyLp (originCube d m) n
      (by simpa [originCube] using hnm.le)
      (a.coeffOn (originCube d m)) u
      (fluxRowLocalLowerOrder sigma hsigma)
      (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two +
  ENNReal.ofReal
      (C * Real.rpow sigma (-(11 / 2 : ℝ)) *
        ((1 + sigma) / 2 - sigma)⁻¹ *
        Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ))) *
    (1 + paperHomogenizationError (originCube d m) n
      ((3 * sigma / 4) / 2) .infinity (.finite 2) a alpha ^ 2) *
    paperFractionalSeminorm (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two g.toField

/-- **Per-cell flux estimate.** The constant is selected before every cube,
coefficient, scale, equation, and comparison field. The conclusion controls
the physical root flux `(a - alpha I) grad u` in the local negative norm.

The theorem is the deterministic comparison step; the later energy, source, and graph
estimates are intentionally not folded into this declaration. -/
theorem exists_fluxRowLocal_rootFlux_le_coarseGrainingRHS
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℤ), ∀ hnm : n < m,
      ∀ (a : Ch02.TriadicCoeffFamily d),
        (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
      ∀ (alpha sigma : ℝ), 0 < alpha →
      ∀ (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1),
      ∀ g : CubeEuclideanWspField (originCube d m)
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two,
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m)
            (a.coeffOn (originCube d m)) u g.toField →
        IsScalarForcedEquation (originCube d m) alpha v g.toField →
        HasH10Difference (originCube d m) u v →
        ENNReal.ofReal (Real.rpow 3 (-sigma * (m : ℝ))) *
            paperNegativeFractionalDual (originCube d m)
              (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two
              (centeredCubeRootFluxDefectL2Field m
                (a.coeffOn (originCube d m)) alpha u) ≤
          fluxRowLocalCoarseGrainingRHS C m n hnm a alpha sigma hsigma g u := by
  obtain ⟨C, hC, hmain⟩ :=
    _root_.SubdiffusiveProcess.Section2.general_coarse_graining FiniteLpExponent.two
      (by norm_num) hd
  refine ⟨C, hC, ?_⟩
  intro m n hnm a ha alpha sigma halpha hsigma g u v hu hv huv
  let s1 := fluxRowLocalLowerOrder sigma hsigma
  let s := fluxRowLocalOrder sigma hsigma
  let s2 := fluxRowLocalUpperOrder sigma hsigma
  have hs1pos : 0 < 3 * sigma / 4 := by nlinarith [hsigma.1]
  have hs1s : 3 * sigma / 4 < sigma := by nlinarith [hsigma.1]
  have hss2 : sigma < (1 + sigma) / 2 := by nlinarith [hsigma.2]
  have hs2one : (1 + sigma) / 2 < 1 := by nlinarith [hsigma.2]
  have hbase := hmain m n hnm a ha alpha sigma (3 * sigma / 4)
    ((1 + sigma) / 2) halpha hs1pos hs1s hss2 hs2one
      s rfl s2 rfl g u v hu hv huv
  have hroot := paperNegativeFractionalDual_rootFluxDefect_le_comparison
    (a.coeffOn (originCube d m)) halpha.le u v s
  let Wreal := Real.rpow 3 (-sigma * (m : ℝ))
  let W : ℝ≥0∞ := ENNReal.ofReal Wreal
  have hWreal : 0 ≤ Wreal := Real.rpow_nonneg (by norm_num) _
  have hscaled :
      W * paperNegativeFractionalDual (originCube d m) s
          FiniteLpExponent.two
          (centeredCubeRootFluxDefectL2Field m
            (a.coeffOn (originCube d m)) alpha u) ≤
        ENNReal.ofReal (Wreal * alpha) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeGradientDifferenceL2Field m u v) +
          W * paperNegativeFractionalDual (originCube d m) s
            FiniteLpExponent.two
            (centeredCubeFluxDifferenceL2Field m
              (a.coeffOn (originCube d m)) alpha u v) := by
    calc
      W * paperNegativeFractionalDual (originCube d m) s
          FiniteLpExponent.two
          (centeredCubeRootFluxDefectL2Field m
            (a.coeffOn (originCube d m)) alpha u) ≤
          W * (ENNReal.ofReal alpha *
              paperNegativeFractionalDual (originCube d m) s
                FiniteLpExponent.two
                (centeredCubeGradientDifferenceL2Field m u v) +
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m
                (a.coeffOn (originCube d m)) alpha u v)) :=
        mul_le_mul_right hroot W
      _ = ENNReal.ofReal (Wreal * alpha) *
              paperNegativeFractionalDual (originCube d m) s
                FiniteLpExponent.two
                (centeredCubeGradientDifferenceL2Field m u v) +
            W * paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m
                (a.coeffOn (originCube d m)) alpha u v) := by
        rw [ENNReal.ofReal_mul hWreal]
        ring
  exact hscaled.trans (by
    norm_num at hbase
    simpa [fluxRowLocalCoarseGrainingRHS, s1, s, s2, W, Wreal,
      fluxRowLocalLowerOrder, fluxRowLocalOrder,
      fluxRowLocalUpperOrder] using hbase)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
