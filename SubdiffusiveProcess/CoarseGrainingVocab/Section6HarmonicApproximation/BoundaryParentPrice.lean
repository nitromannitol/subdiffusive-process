module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanTransport

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- All kinematic and fractional terms in the boundary Caccioppoli parent
norm, with the one genuinely PDE-dependent scalar left explicit. -/
theorem sqrt_projected_sub_dirichletSolution_le_windowPrices_add_meanDefect
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)} {s D : ℝ}
    {A : CoeffFamily d} {g0 : Vec d → Vec d}
    (v : DirichletForcedCubeSolution (originCube d k) A g0)
    (u h : H1Function (openCubeSet (originCube d m)))
    (u₀ h₀ : H1Function (openCubeSet (originCube d k)))
    (hv : v.boundaryData = h₀)
    (hu₀ : ∀ x, u₀.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh₀ : ∀ x, h₀.toFun x = h.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh₀grad : ∀ x, h₀.grad x = h.grad
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUmeas : MeasurableSet U) (hU0 : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)
    (hs : 0 < s)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hfrac : fractionalSeminormOn U s h.grad ≠ ⊤) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y => u₀.toFun y - v.toH1.toFun y)) ≤
      2 * Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) +
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
        Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            (volume U).toReal ^ (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s h.grad).toReal +
          euclideanNorm (averageVecOn U h.grad)) +
      |volumeAverage
          (translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k))
          (fun y => u.toFun y - h.toFun y)| +
      cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
        (fun y => v.toH1.toFun y - h₀.toFun y) := by
  have hbase :=
    sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_grad_add_meanDefect
      k v u₀ h₀ hv (averageOn U u.toFun)
  have hUreal : 0 < (volume U).toReal := ENNReal.toReal_pos hU0.ne' hUtop
  have huPrice := normalizedL2On_projected_le_window
    u u₀ (averageOn U u.toFun) hu₀ hPsub hUsub hUreal hPpos
  have hhPrice :=
    sum_normalizedL2On_projected_grad_le_mean_add_fractional
      h h₀ hh₀grad hPsub hUsub hUmeas hU0 hUtop hPpos hs hdiam hfrac
  have hmean := volumeAverage_projected_sub_eq_physical u h u₀ h₀ hu₀ hh₀
  rw [hmean] at hbase
  have hPoin0 : 0 ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ k :=
    mul_nonneg (unitMeanZeroPoincareConst_nonneg d) (zpow_nonneg (by norm_num) _)
  have hu2 := mul_le_mul_of_nonneg_left huPrice (by norm_num : (0 : ℝ) ≤ 2)
  have hh2 := mul_le_mul_of_nonneg_left hhPrice hPoin0
  linarith only [hbase, hu2, hh2]

/-- Squared form of
`sqrt_projected_sub_dirichletSolution_le_windowPrices_add_meanDefect`, ready
for the parent term in the boundary coarse-Caccioppoli inequality. -/
theorem normalizedL2SqOnSet_sub_dirichletSolution_le_windowPrices_add_meanDefect_sq
    {m k : ℤ} {q : Vec d} {U : Set (Vec d)} {s D : ℝ}
    {A : CoeffFamily d} {g0 : Vec d → Vec d}
    (v : DirichletForcedCubeSolution (originCube d k) A g0)
    (u h : H1Function (openCubeSet (originCube d m)))
    (u₀ h₀ : H1Function (openCubeSet (originCube d k)))
    (hv : v.boundaryData = h₀)
    (hu₀ : ∀ x, u₀.toFun x = u.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh₀ : ∀ x, h₀.toFun x = h.toFun
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hh₀grad : ∀ x, h₀.grad x = h.grad
      (x + Section6ExcessDecay.wellPlacedCentre q m k))
    (hPsub : translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k) ⊆ U)
    (hUsub : U ⊆ openCubeSet (originCube d m))
    (hUmeas : MeasurableSet U) (hU0 : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (hPpos : 0 < (volume (translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)
    (hs : 0 < s)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hfrac : fractionalSeminormOn U s h.grad ≠ ⊤) :
    normalizedL2SqOnSet (openCubeSet (originCube d k))
        (fun y => u₀.toFun y - v.toH1.toFun y) ≤
      (2 * Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) +
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
        Real.sqrt ((volume U).toReal /
          (volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            (volume U).toReal ^ (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s h.grad).toReal +
          euclideanNorm (averageVecOn U h.grad)) +
      |volumeAverage
          (translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k))
          (fun y => u.toFun y - h.toFun y)| +
      cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
        (fun y => v.toH1.toFun y - h₀.toFun y)) ^ (2 : ℕ) := by
  let R : ℝ :=
    2 * Real.sqrt ((volume U).toReal /
        (volume (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
      normalizedL2On U (fun y => u.toFun y - averageOn U u.toFun) +
    unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
      Real.sqrt ((volume U).toReal /
        (volume (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
      (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
          (volume U).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn U s h.grad).toReal +
        euclideanNorm (averageVecOn U h.grad)) +
    |volumeAverage
        (translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k))
        (fun y => u.toFun y - h.toFun y)| +
    cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
      (fun y => v.toH1.toFun y - h₀.toFun y)
  have hroot :=
    sqrt_projected_sub_dirichletSolution_le_windowPrices_add_meanDefect
      v u h u₀ h₀ hv hu₀ hh₀ hh₀grad hPsub hUsub hUmeas hU0 hUtop hPpos
        hs hdiam hfrac
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans hroot
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _))]
    at hsq
  simpa only [R] using hsq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
