module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.CorrectorPrice
public import Homogenization.Deterministic.WeakNormInterfaces.Bounds

@[expose] public section

/-!
# A coefficient-free price for the flat boundary comparator

This is the quantitative half of the comparator/mean-control argument. It keeps
the flat harmonic replacement and its zero-trace corrector explicit, and
prices the latter by Dirichlet minimality followed by the scaled cube
Poincare inequality.

The harmless dimension-only constant below is not optimized.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- Dimension-only constant in the flat-comparator `L²` price. -/
noncomputable def flatComparatorPriceConst (d : ℕ) [NeZero d] : ℝ :=
  2 * (d : ℝ) * unitDirichletPoincareConst d

theorem flatComparatorPriceConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ flatComparatorPriceConst d := by
  unfold flatComparatorPriceConst
  exact mul_nonneg
    (mul_nonneg (by positivity) (Nat.cast_nonneg d))
    (unitDirichletPoincareConst_nonneg d)

private theorem integral_grad_corrector_le_four_mul
    {V : Set (Vec d)} {Phi : H1Function V} {rho : H10Function V}
    (hVm : MeasurableSet V)
    (hharm : IsUnitWeaklyHarmonicOn V (Phi + rho.toH1Function)) :
    ∫ y in V, vecDot (rho.toH1Function.grad y) (rho.toH1Function.grad y) ∂volume ≤
      4 * ∫ y in V, vecDot (Phi.grad y) (Phi.grad y) ∂volume := by
  let w : H1Function V := Phi + rho.toH1Function
  have hmin := integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn
    (w := w) (Phi := Phi) hharm rho (fun y => by
      dsimp only [w]
      rw [H1Function.add_grad])
  have hrho : ∀ y, rho.toH1Function.grad y = w.grad y - Phi.grad y := by
    intro y
    dsimp only [w]
    rw [H1Function.add_grad]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hpoint : ∀ y ∈ V,
      vecDot (rho.toH1Function.grad y) (rho.toH1Function.grad y) ≤
        2 * vecDot (w.grad y) (w.grad y) +
          2 * vecDot (Phi.grad y) (Phi.grad y) := by
    intro y _
    rw [hrho y]
    unfold vecDot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hs : 0 ≤ (w.grad y i + Phi.grad y i) ^ 2 := sq_nonneg _
    simp only [Pi.sub_apply]
    nlinarith only [hs]
  have hrhoInt := integrableOn_vecDot_self
    (W := V) (F := rho.toH1Function.grad) (fun i => rho.toH1Function.gradMemL2 i)
  have hwInt := integrableOn_vecDot_self
    (W := V) (F := w.grad) (fun i => w.gradMemL2 i)
  have hPhiInt := integrableOn_vecDot_self
    (W := V) (F := Phi.grad) (fun i => Phi.gradMemL2 i)
  have hmajor : IntegrableOn (fun y =>
      2 * vecDot (w.grad y) (w.grad y) +
        2 * vecDot (Phi.grad y) (Phi.grad y)) V volume :=
    (hwInt.const_mul 2).add (hPhiInt.const_mul 2)
  have hmono := setIntegral_mono_on hrhoInt hmajor hVm hpoint
  have hmajorEq :
      ∫ y in V, (2 * vecDot (w.grad y) (w.grad y) +
          2 * vecDot (Phi.grad y) (Phi.grad y)) ∂volume =
        2 * ∫ y in V, vecDot (w.grad y) (w.grad y) ∂volume +
          2 * ∫ y in V, vecDot (Phi.grad y) (Phi.grad y) ∂volume := by
    rw [integral_add (hwInt.const_mul 2) (hPhiInt.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hmajorEq] at hmono
  linarith only [hmin, hmono]

/-- A flat harmonic replacement on a translated cube, with the comparator
error bounded by the datum gradient on that same cube. -/
theorem exists_flatComparator_translatedCube_le [NeZero d]
    {m k : ℤ} {c : Vec d}
    (hsub : translateSet c (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m))
    (Phi : H1Function (openCubeSet (originCube d m))) :
    ∃ (w : H1Function (translateSet c (openCubeSet (originCube d k))))
      (rho : H10Function (translateSet c (openCubeSet (originCube d k)))),
      IsUnitWeaklyHarmonicOn (translateSet c (openCubeSet (originCube d k))) w ∧
      (∀ y, w.toFun y = Phi.toFun y + rho.toH1Function.toFun y) ∧
      (∀ y, w.grad y = Phi.grad y + rho.toH1Function.grad y) ∧
      normalizedL2On (translateSet c (openCubeSet (originCube d k)))
          (fun y => Phi.toFun y - w.toFun y) ≤
        flatComparatorPriceConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            normalizedL2On (translateSet c (openCubeSet (originCube d k)))
              (fun y => Phi.grad y i) := by
  classical
  let V : Set (Vec d) := translateSet c (openCubeSet (originCube d k))
  have hV : IsOpenBoundedConvexDomain V :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet c
  have hVne : V.Nonempty := by
    obtain ⟨y, hy⟩ := Homogenization.Book.Ch02.openCubeSet_nonempty (originCube d k)
    exact ⟨y + c, y, hy, rfl⟩
  let PhiV : H1Function V := Phi.restrict hV.isOpen hsub
  obtain ⟨rho, hharm⟩ :=
    exists_h10Witness_isUnitWeaklyHarmonicOn hV hVne PhiV
  refine ⟨PhiV + rho.toH1Function, rho, hharm, ?_, ?_, ?_⟩
  · intro y
    rw [H1Function.add_toFun]
    rfl
  · intro y
    rw [H1Function.add_grad]
    rfl
  · have hVm : MeasurableSet V := hV.isOpen.measurableSet
    have hVpos : 0 < (volume V).toReal := by
      rw [show volume V = volume (openCubeSet (originCube d k)) by
        exact volume_translateSet_eq c _]
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d k)
    have hVeq : V = translatedCube d k c := by
      dsimp only [V]
      rw [translatedCube, cube,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
    have hPoin := eLpNorm_le_dirichletPoincare_translatedCube hVm
      (show V ⊆ translatedCube d k c by rw [hVeq]) rho
    have henergy := integral_grad_corrector_le_four_mul hVm hharm
    have hrhoSum := sum_toReal_eLpNorm_coord_le
      (W := V) (F := rho.toH1Function.grad) (fun i => rho.toH1Function.gradMemL2 i)
    have hPhiEnergy := integral_vecDot_self_eq_sum_sq
      (W := V) (F := PhiV.grad) (fun i => PhiV.gradMemL2 i)
    have hroot : Real.sqrt
        (∫ y in V, vecDot (rho.toH1Function.grad y)
          (rho.toH1Function.grad y) ∂volume) ≤
        2 * ∑ i : Fin d,
          (eLpNorm (fun y => PhiV.grad y i) 2 (volume.restrict V)).toReal := by
      have hsq := Real.sqrt_le_sqrt henergy
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      calc
        Real.sqrt (∫ y in V, vecDot (rho.toH1Function.grad y)
              (rho.toH1Function.grad y) ∂volume)
            ≤ Real.sqrt (4 * ∫ y in V,
                vecDot (PhiV.grad y) (PhiV.grad y) ∂volume) := hsq
        _ = 2 * Real.sqrt (∫ y in V,
                vecDot (PhiV.grad y) (PhiV.grad y) ∂volume) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
        _ = 2 * Real.sqrt (∑ i : Fin d,
              (eLpNorm (fun y => PhiV.grad y i) 2
                (volume.restrict V)).toReal ^ 2) := by rw [hPhiEnergy]
        _ ≤ 2 * ∑ i : Fin d,
              (eLpNorm (fun y => PhiV.grad y i) 2
                (volume.restrict V)).toReal := by
              gcongr
              exact Homogenization.finset_sqrt_sum_sq_le_sum_of_nonneg Finset.univ _
                (fun i _ => ENNReal.toReal_nonneg)
    have hrhoGrad : ∑ i : Fin d,
        (eLpNorm (fun y => rho.toH1Function.grad y i) 2
          (volume.restrict V)).toReal ≤
        2 * (d : ℝ) * ∑ i : Fin d,
          (eLpNorm (fun y => PhiV.grad y i) 2 (volume.restrict V)).toReal := by
      calc
        ∑ i : Fin d, (eLpNorm (fun y => rho.toH1Function.grad y i) 2
              (volume.restrict V)).toReal
            ≤ (d : ℝ) * Real.sqrt
                (∫ y in V, vecDot (rho.toH1Function.grad y)
                  (rho.toH1Function.grad y) ∂volume) := hrhoSum
        _ ≤ (d : ℝ) * (2 * ∑ i : Fin d,
              (eLpNorm (fun y => PhiV.grad y i) 2
                (volume.restrict V)).toReal) :=
            mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg d)
        _ = 2 * (d : ℝ) * ∑ i : Fin d,
              (eLpNorm (fun y => PhiV.grad y i) 2
                (volume.restrict V)).toReal := by ring
    have hraw : (eLpNorm rho.toH1Function.toFun 2
          (volume.restrict V)).toReal ≤
        flatComparatorPriceConst d * (3 : ℝ) ^ k *
          ∑ i : Fin d,
            (eLpNorm (fun y => PhiV.grad y i) 2 (volume.restrict V)).toReal := by
      refine hPoin.trans ?_
      have hcoef : 0 ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ k :=
        mul_nonneg (unitDirichletPoincareConst_nonneg d) (zpow_nonneg (by norm_num) _)
      have hmul := mul_le_mul_of_nonneg_left hrhoGrad hcoef
      calc
        unitDirichletPoincareConst d * (3 : ℝ) ^ k *
              ∑ i : Fin d, (eLpNorm (fun y => rho.toH1Function.grad y i) 2
                (volume.restrict V)).toReal
            ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ k *
              (2 * (d : ℝ) * ∑ i : Fin d,
                (eLpNorm (fun y => PhiV.grad y i) 2
                  (volume.restrict V)).toReal) := hmul
        _ = flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ i : Fin d, (eLpNorm (fun y => PhiV.grad y i) 2
                (volume.restrict V)).toReal := by
              rw [flatComparatorPriceConst]
              ring
    have hdiff : (fun y => Phi.toFun y - (PhiV + rho.toH1Function).toFun y) =
        fun y => -rho.toH1Function.toFun y := by
      funext y
      rw [H1Function.add_toFun]
      change Phi.toFun y - (Phi.toFun y + rho.toH1Function.toFun y) =
        -rho.toH1Function.toFun y
      ring
    rw [hdiff, normalizedL2On_neg]
    rw [normalizedL2On_eq_toReal_eLpNorm_div rho.toH1Function.memL2]
    rw [div_le_iff₀ (Real.sqrt_pos.2 hVpos)]
    have hnorm : ∀ i : Fin d,
        (eLpNorm (fun y => PhiV.grad y i) 2 (volume.restrict V)).toReal =
          normalizedL2On V (fun y => Phi.grad y i) * Real.sqrt (volume V).toReal := by
      intro i
      have hdict := normalizedL2On_eq_toReal_eLpNorm_div (PhiV.gradMemL2 i)
      rw [eq_div_iff (Real.sqrt_ne_zero'.2 hVpos)] at hdict
      simpa only [PhiV, H1Function.restrict] using! hdict.symm
    rw [Finset.sum_congr rfl (fun i _ => hnorm i), ← Finset.sum_mul] at hraw
    simpa only [V, mul_assoc] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
