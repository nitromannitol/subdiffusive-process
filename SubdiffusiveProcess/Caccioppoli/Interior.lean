import SubdiffusiveProcess.Caccioppoli.Boundary
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

theorem exists_interior_caccioppoli_besov (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (openCubeSet Q)),
        (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
        IsForcedEquation Q a u g →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) u.toFun +
                Real.rpow t (-10 : ℝ) *
                  Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_boundary_caccioppoli_with_datum d
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u hsymm hu hs hs1 ht hth hst hpatch hg
  have hx : x ∈ openCubeSet Q := hpatch (mem_openCubeAtScale_center x _)
  have htrace := (interiorForcedCaccioppoliDatum x u hu hpatch).zeroTraceOnBoundaryPatch
  have htrace' : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale x (Q.scale - 1)) (fun y => u.toFun y - (0 : H1Function (openCubeSet Q)).toFun y) := by
    simpa using htrace
  have hhReg : ForceBesovRegularity Q (2 * t) (0 : Vec d → Vec d) :=
    forceBesovRegularity_zero Q (2 * t)
  have hb' := hb u 0 0 hsymm hu htrace' (by simp [volumeAverage])
    hs hs1 ht hth hst hx hg (by simpa using hhReg)
  have havg0 : cubeAverageVec Q (0 : Homogenization.Vec d → Homogenization.Vec d) = 0 := by
    ext i
    simp [Homogenization.cubeAverageVec, cubeAverage]
  simpa [havg0, Homogenization.vecDot, H1Function.zero_toFun, H1Function.zero_grad, scaleNormalizedPositiveBesovVectorNormTwo,
    cubeAverageVec, cubeAverage, vecNormSq, cubeBesovPositiveVectorSeminormTwo_zero] using hb'

theorem exists_originCube_caccioppoli_besov (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d)
          (u : H1Function (openCubeSet (originCube d 0)))
          (g : Vec d → Vec d),
          (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
          IsForcedEquation (originCube d 0) a u g →
          ForceBesovRegularity (originCube d 0) (2 * t) g →
            coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 ≤
              caccioppoliWithRHSPrefactor C (originCube d 0) a s t *
                (Ch02.lambdaS (originCube d 0) t a *
                    cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) u.toFun ^ 2 +
                  Real.rpow t (-10 : ℝ) *
                    Real.rpow (Ch02.lambdaS (originCube d 0) t a) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d 0) (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ := exists_interior_caccioppoli_besov d
  refine ⟨C, hC, ?_⟩
  intro s t hs hs_one ht ht_half hst a u g hsymm hu hg
  let Q₀ : TriadicCube d := originCube d 0
  let Q₁ : TriadicCube d := originCube d (-1)
  have hQ₁Q₀ : openCubeSet Q₁ ⊆ openCubeSet Q₀ := by
    simpa [Q₀, Q₁] using
      (openCubeSet_originCube_subset_of_scale_le (d := d)
        (k := (-1 : ℤ)) (l := 0) (by norm_num))
  let u₁ : H1Function (openCubeSet Q₁) :=
    u.restrict (isOpen_openCubeSet Q₁) (by simpa [Q₀] using hQ₁Q₀)
  let energy : Vec d → ℝ :=
    coefficientEnergyDensity (a.coeffOn Q₁).toCoeffField u₁.grad
  let B : ℝ :=
    caccioppoliWithRHSPrefactor C Q₀ a s t *
      (Ch02.lambdaS Q₀ t a * cubeLpNorm Q₀ (2 : ℝ≥0∞) u.toFun ^ 2 +
        Real.rpow t (-10 : ℝ) *
          Real.rpow (Ch02.lambdaS Q₀ t a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q₀ (2 * t) g ^ 2)
  have hint_open : MeasureTheory.IntegrableOn energy (openCubeSet Q₁) := by
    simpa [energy] using
      integrableOn_coefficientEnergyDensity_coeffOn Q₁ (a.coeffOn Q₁) u₁
  have hint_cube : MeasureTheory.IntegrableOn energy (cubeSet Q₁) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint_open
  have hpartition : cubeAverage Q₁ energy =
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q₁ 1 energy hint_cube
  have hchildren : ∀ R ∈ descendantsAtDepth Q₁ 1, cubeAverage R energy ≤ B := by
    intro R hR
    have hRscale : R.scale = -2 := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [Q₁] using hscale
    have hxQ₁ : cubeCenter R ∈ openCubeSet Q₁ :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_openCubeSet R)
    have hpatch : openCubeAtScale (cubeCenter R) (Q₀.scale - 1) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -1) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀] using hgeom
    have hsmall : openCubeAtScale (cubeCenter R) (Q₀.scale - 2) ⊆
        openCubeSet Q₀ := by
      have hgeom := openCubeAtScale_subset_origin_succ_succ
        (d := d) (k := -2) (n := -2) (x := cubeCenter R)
        (by simpa [Q₁] using hxQ₁) (by norm_num)
      simpa [Q₀] using hgeom
    have hcore : caccioppoliCoreSet Q₀ (cubeCenter R) = openCubeSet R := by
      rw [caccioppoliCoreSet_eq_openCubeAtScale hsmall]
      have hscaleQ₀ : Q₀.scale - 2 = R.scale := by
        change 0 - 2 = R.scale
        omega
      rw [hscaleQ₀, openCubeAtScale_cubeCenter]
    have hloc := hlocal (Q := Q₀) (a := a) (s := s) (t := t)
      (x := cubeCenter R) (g := g) u hsymm hu hs hs_one ht ht_half hst hpatch hg
    have hrestrict : Ch02.CoeffOn.RestrictsTo (a.coeffOn Q₀) (a.coeffOn Q₁) :=
      a.restrictsTo_of_subset hQ₁Q₀
    have hcoeffR : (a.coeffOn Q₁).toCoeffField
        =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
          (a.coeffOn Q₀).toCoeffField :=
      ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hrestrict
    have henergyR : energy =ᵐ[MeasureTheory.volume.restrict (cubeSet R)]
        coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad := by
      filter_upwards [hcoeffR] with x hx
      simp [energy, u₁, H1Function.restrict, coefficientEnergyDensity, hx]
    have havg : cubeAverage R energy =
        cubeAverage R (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) :=
      cubeAverage_eq_of_ae_eq_on_cubeSet henergyR
    rw [hcore] at hloc
    unfold localizedCoeffEnergyValue normalizedSetAverage at hloc
    rw [volumeAverage_openCubeSet_eq_cubeAverage] at hloc
    rw [havg]
    rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
      Q₀ u.toFun u.memL2_normalizedCubeMeasure] at hloc
    change cubeAverage R
      (coefficientEnergyDensity (a.coeffOn Q₀).toCoeffField u.grad) ≤ _ at hloc
    have hQ₀scale : Q₀.scale = 0 := rfl
    rw [hQ₀scale] at hloc
    norm_num at hloc
    simpa [boundaryCaccioppoliWithRHSRHS, B, Q₀] using hloc
  have havg_le : descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤ B := by
    calc
      descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) ≤
          descendantsAverage Q₁ 1 (fun _ => B) :=
        descendantsAverage_le_descendantsAverage Q₁ 1 hchildren
      _ = B := descendantsAverage_const Q₁ 1 B
  have henergy_nonneg : 0 ≤ ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
    exact MeasureTheory.integral_nonneg_of_ae
      (by
        simpa [energy] using
          ae_nonneg_coefficientEnergyDensity_coeffOn_normalizedCubeMeasure
            Q₁ (a.coeffOn Q₁) u₁)
  have hnorm : coefficientEnergyNorm Q₁ a u.grad ^ 2 = cubeAverage Q₁ energy := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    unfold coefficientEnergyNorm
    have hint_eq :
        (∫ x, vecDot (u.grad x)
            (matVecMul ((a.coeffOn Q₁).toCoeffField x) (u.grad x))
            ∂normalizedCubeMeasure Q₁) =
          ∫ x, energy x ∂normalizedCubeMeasure Q₁ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simpa [energy, u₁, H1Function.restrict] using
        (coefficientEnergyDensity_eq_unsymmetrized
          (a.coeffOn Q₁).toCoeffField u.grad x).symm
    rw [hint_eq, Real.sq_sqrt henergy_nonneg]
  calc
    coefficientEnergyNorm (originCube d (-1)) a u.grad ^ 2 =
        cubeAverage Q₁ energy := by simpa [Q₁] using hnorm
    _ = descendantsAverage Q₁ 1 (fun R => cubeAverage R energy) := hpartition
    _ ≤ B := havg_le
    _ = _ := by simp [B, Q₀]

end
end SubdiffusiveProcess.Caccioppoli
