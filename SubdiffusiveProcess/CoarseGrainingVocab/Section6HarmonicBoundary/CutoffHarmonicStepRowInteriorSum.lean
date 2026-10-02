/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowInteriorSum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowInteriorPrice




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The summed interior half of the step row.**

For every cover scale `k ≤ n − 4` matched to the radius gap
(`14·3^{k-2} ≤ R − ρ ≤ 27·3^k`, which by `WindowStepAbsorption.exists_coverScale_le_gap`
is achievable for every gap), the total cutoff energy carried by the **interior
class** of cells of the window of radius `ρ` is bounded by the four printed
budgets with the step row's own normalization `(3ⁿ)^d (3ⁿ)³ / (R − ρ)³`.

No per-cell window-normalized estimate is used, and no volume ratio other than
the dimension-only `9^{-d}` and the overlap count `28^d` occurs. -/
theorem exists_interiorCellSum_le_budgets_atScale (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ k : ℤ, k ≤ (n : ℤ) - 4 →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ rho R : ℝ, 0 ≤ rho → rho < R → R ≤ 4 * (3 : ℝ) ^ n / 9 →
        rho + 14 * (3 : ℝ) ^ (k - 2) ≤ R → R - rho ≤ 27 * (3 : ℝ) ^ k →
        ∑ idx ∈ (windowBox (k - 2) x rho).filter
            (fun idx => openCubeAtScale (cellCentre (k - 2) idx) (k - 1) ⊆
              cube d (m : ℤ)),
          (∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx),
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
          K * ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 *
            harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g /
            (R - rho) ^ 3 := by
  obtain ⟨Kc, hKc, hprice⟩ :=
    exists_interiorCellEnergy_setIntegral_le_parentIntegrals_atScale d
  refine ⟨59049 * Kc * (28 : ℝ) ^ d, by positivity, ?_⟩
  intro M sOrder hs L m n hnm k hk z x omega hz hx hgood u h g hdir hg hh
    rho R hrho hlt hR hgap hgap2
  classical
  set j : ℤ := k - 2 with hjdef
  have hjk : j + 2 = k := by omega
  have hkm : k ≤ (m : ℤ) := by omega
  have hkm2 : j + 2 ≤ (m : ℤ) := by omega
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hNpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hgapPos : 0 < R - rho := by linarith
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hUdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set c0 : ℝ := averageOn U u.toFun with hc0def
  set s : ℝ := sOrder.1 with hsdef
  have hs0 : 0 < s := sOrder.2.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hxcube : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  -- geometry: every parent sits in the budget window
  have hRlt : R < (3 : ℝ) ^ n / 2 := by linarith
  have hUsub : U ⊆ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x
  have hPU : ∀ idx ∈ windowBox j x rho,
      stepRowParent (d := d) j (m : ℤ) idx ⊆ U := by
    intro idx hidx p hp
    have h1 : p ∈ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2) :=
      stepRowParent_subset_supWindow hkm2 idx hp
    have h2 : p ∈ supWindow x (rho + 14 * (3 : ℝ) ^ j) :=
      supWindow_cellCentre_subset_supWindow hidx h1
    have h3 : p ∈ cube d (m : ℤ) := stepRowParent_subset_cube hkm2 idx hp
    exact boundaryWindow_subset_truncatedCube x hRlt
      (boundaryWindow_mono (m : ℤ) x (by linarith) ⟨h2, h3⟩)
  -- integrability of the oscillation density on the budget window
  have huLp : MemLp u.toFun 2 (volume.restrict U) :=
    u.memL2.mono_measure (Measure.restrict_mono hUsub le_rfl)
  have hoscInt : IntegrableOn (fun p => (u.toFun p - c0) ^ 2) U :=
    Section6ExcessDecay.integrableOn_sub_const_sq_truncatedCube x huLp c0
  have hUmeas : MeasurableSet U := Section6ExcessDecay.measurableSet_truncatedCube d _ _ _
  set G : Vec d → ℝ := U.indicator (fun p => (u.toFun p - c0) ^ 2) with hGdef
  have hG0 : ∀ p, 0 ≤ G p := fun p =>
    Set.indicator_nonneg (fun q _ => sq_nonneg _) p
  have hGint : Integrable G := hoscInt.integrable_indicator hUmeas
  -- the oscillation leg of the summation
  have hoscSum : ∑ idx ∈ windowBox j x rho,
      (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) ≤
      (28 : ℝ) ^ d * ∫ p in U, (u.toFun p - c0) ^ 2 := by
    have hrewrite : ∀ idx ∈ windowBox j x rho,
        (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) =
          ∫ p in stepRowParent (d := d) j (m : ℤ) idx, G p := by
      intro idx hidx
      rw [hGdef, setIntegral_indicator hUmeas,
        Set.inter_eq_self_of_subset_left (hPU idx hidx)]
    rw [Finset.sum_congr rfl hrewrite]
    refine (sum_setIntegral_parents_le j x rho hG0 _
      (measurableSet_stepRowParent j (m : ℤ)) (fun idx _ =>
        stepRowParent_subset_supWindow hkm2 idx) hGint.integrableOn).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hGdef, setIntegral_indicator hUmeas]
    exact setIntegral_mono_set hoscInt (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (HasSubset.Subset.eventuallyLE Set.inter_subset_right)
  -- the datum leg of the summation
  have hAcube0 : volume (cube d (m : ℤ)) ≠ 0 := by
    have hreal : 0 < (volume (cube d (m : ℤ))).toReal := by
      rw [cube, volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d (m : ℤ))
    exact (ENNReal.toReal_ne_zero.mp hreal.ne').1
  have hAcubeTop : volume (cube d (m : ℤ)) ≠ ∞ := by
    rw [cube]; exact (volume_openCubeSet_lt_top (originCube d (m : ℤ))).ne
  have hfrac : MemFractionalOn (cube d (m : ℤ)) s g := by
    change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ))) s g ≠ ⊤
    rw [fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have hU0 : volume U ≠ 0 := by
    have hpos : 0 < (volume (truncatedCube d (m : ℤ) (n : ℤ) x)).toReal :=
      Section6ExcessDecay.volume_toReal_truncatedCube_pos (m := (m : ℤ)) (j := (n : ℤ))
        x hxcube (by omega)
    exact (ENNReal.toReal_ne_zero.mp hpos.ne').1
  have hUtop : volume U ≠ ∞ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hUfin : fractionalSeminormOn U s g ≠ ⊤ :=
    memFractionalOn_mono_set hUsub hAcube0 hAcubeTop hU0 hfrac
  set T : Finset (Fin d → ℤ) := (windowBox j x rho).filter
    (fun idx => openCubeAtScale (cellCentre j idx) (k - 1) ⊆ cube d (m : ℤ)) with hTdef
  have hTsub : T ⊆ windowBox j x rho := Finset.filter_subset _ _
  -- the interior class has centres in the domain, hence genuine parents
  have hcentre : ∀ idx ∈ T, cellCentre (d := d) j idx ∈ cube d (m : ℤ) := by
    intro idx hidx
    have hpatch := (Finset.mem_filter.mp hidx).2
    exact cellCentre_mem_cube_of_openCubeAtScale_subset (by rwa [show j + 1 = k - 1 by omega])
  have hnear : ∀ idx ∈ T, stepRowNear (d := d) j (m : ℤ) idx := by
    intro idx hidx i
    have hmem := hcentre idx hidx
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hmem
    have hi := hmem i
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hPeq : ∀ idx ∈ T, stepRowParent (d := d) j (m : ℤ) idx =
      translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre (cellCentre j idx) (m : ℤ) k) := by
    intro idx hidx
    rw [stepRowParent, if_pos (hnear idx hidx), hjk]
  have hPvol : ∀ idx ∈ T,
      (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal = ((3 : ℝ) ^ k) ^ d := by
    intro idx hidx
    rw [hPeq idx hidx]
    exact Section6BoundedMultiplier.volume_translatedCube_toReal k _
  have hdatumSum : ∑ idx ∈ T,
      (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
        (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx) s g).toReal ^ 2 ≤
      (28 : ℝ) ^ d * ((volume U).toReal *
        (fractionalSeminormOn U s g).toReal ^ 2) := by
    refine sum_volume_toReal_mul_fractionalSeminormOn_toReal_sq_le' j T s g _
      (measurableSet_stepRowParent j (m : ℤ))
      (fun idx _ => stepRowParent_subset_supWindow hkm2 idx) ?_ ?_ U hUmeas
      (fun idx hidx => hPU idx (hTsub hidx)) hU0 hUtop hUfin
    · intro idx hidx
      have hpos : 0 < (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal := by
        rw [hPvol idx hidx]; positivity
      exact (ENNReal.toReal_ne_zero.mp hpos.ne').1
    · intro idx hidx
      rw [hPeq idx hidx]
      exact Section6BoundedMultiplier.volume_translatedCube_ne_top k _
  -- the per-cell interior price
  have hcellrow : ∀ idx ∈ T,
      (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx),
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      Kc * Real.rpow (3 : ℝ) (2 * s * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
        (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
            (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) +
          Real.rpow s (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
            ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
              (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx)
                s g).toReal ^ 2)) := by
    intro idx hidx
    have hqcube := hcentre idx hidx
    have hpatch := (Finset.mem_filter.mp hidx).2
    have hidxbox := hTsub hidx
    have hqwin : cellCentre (d := d) j idx ∈ supWindow x (4 * (3 : ℝ) ^ n / 9) := by
      have hself : cellCentre (d := d) j idx ∈
          supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2) := by
        intro i
        have : (0 : ℝ) < (3 : ℝ) ^ (j + 3) := zpow_pos (by norm_num) _
        simp only [sub_self, abs_zero]
        linarith
      have h2 := supWindow_cellCentre_subset_supWindow hidxbox hself
      exact supWindow_mono (by linarith) h2
    have hparent := translatedCube_wellPlacedCentre_subset_truncatedCube_of_supWindow
      (n := n) hqcube hkm hk hqwin
    have := hprice M sOrder hs L m n hnm k (by omega) z x (cellCentre j idx)
      omega hz hx hqcube hparent hpatch hgood u h g c0 hdir hg hh
    rw [hPeq idx hidx]
    exact this
  -- sum the per-cell prices
  set A : ℝ := Real.rpow (3 : ℝ) (2 * s * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hcoef1 : 0 ≤ sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) :=
    mul_nonneg hsigma.le (Real.rpow_nonneg (by norm_num) _)
  have hcoef2 : 0 ≤ Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (inv_nonneg.mpr hsigma.le))
      (Real.rpow_nonneg (by norm_num) _)
  have hsum1 := Finset.sum_le_sum hcellrow
  rw [← Finset.mul_sum] at hsum1
  have hsplit : ∑ idx ∈ T,
      (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
          (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) +
        Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
          ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
            (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx)
              s g).toReal ^ 2)) =
      sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
          (∑ idx ∈ T, ∫ p in stepRowParent (d := d) j (m : ℤ) idx,
            (u.toFun p - c0) ^ 2) +
        Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
          (∑ idx ∈ T, (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
            (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx)
              s g).toReal ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at hsum1
  -- pass to the window integrals
  have hoscT : ∑ idx ∈ T, (∫ p in stepRowParent (d := d) j (m : ℤ) idx,
      (u.toFun p - c0) ^ 2) ≤ (28 : ℝ) ^ d * ∫ p in U, (u.toFun p - c0) ^ 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsub ?_) hoscSum
    intro idx _ _
    exact integral_nonneg fun p => sq_nonneg _
  have hstep1 : ∑ idx ∈ T,
      (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx),
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      Kc * A * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
          ((28 : ℝ) ^ d * ∫ p in U, (u.toFun p - c0) ^ 2) +
        Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
          ((28 : ℝ) ^ d * ((volume U).toReal *
            (fractionalSeminormOn U s g).toReal ^ 2))) := by
    refine hsum1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add (mul_le_mul_of_nonneg_left hoscT hcoef1)
      (mul_le_mul_of_nonneg_left hdatumSum hcoef2)
  refine hstep1.trans ?_
  -- ## the exponent bookkeeping
  set Uvol := ((volume U).toReal : ℝ) with hUvoldef
  have hUvol0 : 0 < Uvol :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos (m := (m : ℤ)) (j := (n : ℤ))
      x hxcube (by omega)
  have hUvolub : Uvol ≤ ((3 : ℝ) ^ (n : ℤ)) ^ d :=
    (Section6ExcessDecay.volume_toReal_truncatedCube_bounds (m := (m : ℤ)) (j := (n : ℤ))
      x hxcube (by omega)).2
  set NL2 : ℝ := normalizedL2On U (fun p => u.toFun p - c0) ^ 2 with hNL2def
  have hNL20 : 0 ≤ NL2 := sq_nonneg _
  have hoscEq : (∫ p in U, (u.toFun p - c0) ^ 2) = Uvol * NL2 := by
    rw [hNL2def, normalizedL2On_sq_eq_volumeAverage U _
      (integral_nonneg fun p => sq_nonneg _), hUvoldef, ← mul_assoc,
      mul_inv_cancel₀ hUvol0.ne', one_mul]
  set Gv : ℝ := (fractionalSeminormOn U s g).toReal ^ 2 with hGvdef
  have hGv0 : 0 ≤ Gv := sq_nonneg _
  -- the two printed budgets
  set Leg1 : ℝ := sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * NL2 with hLeg1def
  set Leg3 : ℝ := Real.rpow s (-12 : ℝ) * sigma⁻¹ *
    Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gv with hLeg3def
  have hLeg10 : 0 ≤ Leg1 := by
    rw [hLeg1def]; exact mul_nonneg (mul_nonneg hsigma.le (by positivity)) hNL20
  have hLeg30 : 0 ≤ Leg3 := by
    rw [hLeg3def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) hGv0
  have hbudEq : harmonicPhysicalFourBudgets M L m n z x omega s u h g =
      Leg1 +
        (if BoundaryTouches U (cube d (m : ℤ)) then
          sigma * vecNormSq (averageVecOn U h.grad) else 0) +
        Leg3 +
        (if BoundaryTouches U (cube d (m : ℤ)) then
          sigma * Real.rpow s (-4 : ℝ) * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s h.grad).toReal ^ 2 else 0) := rfl
  have hbud : Leg1 + Leg3 ≤
      harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
    rw [hbudEq]
    have h2 : (0 : ℝ) ≤ (if BoundaryTouches U (cube d (m : ℤ)) then
        sigma * vecNormSq (averageVecOn U h.grad) else 0) := by
      split
      · exact mul_nonneg hsigma.le (vecNormSq_nonneg _)
      · exact le_rfl
    have h4 : (0 : ℝ) ≤ (if BoundaryTouches U (cube d (m : ℤ)) then
        sigma * Real.rpow s (-4 : ℝ) * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
          (fractionalSeminormOn U s h.grad).toReal ^ 2 else 0) := by
      split
      · exact mul_nonneg (mul_nonneg (mul_nonneg hsigma.le
          (Real.rpow_nonneg hs0.le _)) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
      · exact le_rfl
    linarith only [h2, h4]
  -- the exponent identities
  have hjjval : ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) = ((n : ℝ) + 2 - (k : ℝ)) := by
    have hnn : (0 : ℤ) ≤ (n : ℤ) + 2 - k := by omega
    have hz2 : ((((n : ℤ) + 2 - k).toNat : ℕ) : ℤ) = (n : ℤ) + 2 - k :=
      Int.toNat_of_nonneg hnn
    have hr : ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) = (((n : ℤ) + 2 - k : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hz2
    rw [hr]
    push_cast
    ring
  set Delta : ℝ := (n : ℝ) - (k : ℝ) with hDeltadef
  have hDelta0 : (4 : ℝ) ≤ Delta := by
    have hkr : ((k : ℤ) : ℝ) ≤ (n : ℝ) - 4 := by exact_mod_cast hk
    rw [hDeltadef]
    linarith only [hkr]
  have hrp : ∀ a b : ℝ, Real.rpow (3 : ℝ) a * Real.rpow (3 : ℝ) b =
      Real.rpow (3 : ℝ) (a + b) := fun a b => (Real.rpow_add (by norm_num) a b).symm
  have hrpow_one : Real.rpow (3 : ℝ) (1 : ℝ) = 3 := Real.rpow_one 3
  have hrpow_sub : ∀ a b : ℝ, Real.rpow (3 : ℝ) (a - b) =
      Real.rpow (3 : ℝ) a / Real.rpow (3 : ℝ) b :=
    fun a b => Real.rpow_sub (by norm_num) a b
  have hrpow_nat : Real.rpow (3 : ℝ) ((n : ℕ) : ℝ) = (3 : ℝ) ^ n :=
    Real.rpow_natCast 3 n
  have hrpow_int : Real.rpow (3 : ℝ) ((k : ℤ) : ℝ) = (3 : ℝ) ^ k :=
    Real.rpow_intCast 3 k
  have hzpow1 : (3 : ℝ) ^ (-(2 * (n : ℤ))) = Real.rpow (3 : ℝ) (-(2 * (n : ℝ))) := by
    rw [show ((-(2 * (n : ℤ)) : ℤ)) = ((-(2 * (n : ℤ)) : ℤ)) from rfl,
      ← Real.rpow_intCast (3 : ℝ) (-(2 * (n : ℤ)))]
    norm_num
  -- oscillation leg
  have hosc_id : A * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
      ((28 : ℝ) ^ d * (Uvol * NL2))) =
      ((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ)
        (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta)) * Leg1 := by
    have hA : A = Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) := by
      rw [hAdef, hjjval]
    have hL : Leg1 = sigma * Real.rpow (3 : ℝ) (-(2 * (n : ℝ))) * NL2 := by
      rw [hLeg1def, hzpow1]
    have hkey : Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) *
        Real.rpow (3 : ℝ) (-(2 * (n : ℝ))) =
        Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
          Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) := by
      rw [hrp, hrp, hDeltadef]
      congr 1
      ring
    rw [hA, hL]
    calc Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
          (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
            ((28 : ℝ) ^ d * (Uvol * NL2)))
        = (28 : ℝ) ^ d * Uvol *
            (Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ))) * (sigma * NL2) := by ring
      _ = (28 : ℝ) ^ d * Uvol *
            (Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) *
              Real.rpow (3 : ℝ) (-(2 * (n : ℝ)))) * (sigma * NL2) := by
            rw [hkey]
      _ = _ := by ring
  -- datum leg
  have hdat_id : A * (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) * ((28 : ℝ) ^ d * (Uvol * Gv))) =
      ((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ) (4 * s)) * Leg3 := by
    rw [hLeg3def, hAdef, hjjval]
    have hkey : Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
        Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) =
        Real.rpow (3 : ℝ) (4 * s) * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
      rw [hrp, hrp]
      congr 1
      ring
    calc Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
          (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
            ((28 : ℝ) ^ d * (Uvol * Gv)))
        = (28 : ℝ) ^ d * Uvol *
            (Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) *
            (Real.rpow s (-12 : ℝ) * sigma⁻¹ * Gv) := by ring
      _ = (28 : ℝ) ^ d * Uvol *
            (Real.rpow (3 : ℝ) (4 * s) * Real.rpow (3 : ℝ) (2 * s * (n : ℝ))) *
            (Real.rpow s (-12 : ℝ) * sigma⁻¹ * Gv) := by rw [hkey]
      _ = _ := by ring
  rw [hoscEq]
  -- both exponents are below `3Δ + 1`
  have hexp1 : Real.rpow (3 : ℝ)
      (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) ≤
      3 * Real.rpow (3 : ℝ) (3 * Delta) := by
    have hDeq : (n : ℝ) + 2 - (k : ℝ) = Delta + 2 := by rw [hDeltadef]; ring
    have hle : 2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta ≤ 1 + 3 * Delta := by
      rw [hDeq]
      have hcoef : 2 * s ≤ (1 / 2 : ℝ) := by linarith only [hs4]
      have hdelta : 0 ≤ Delta := le_trans (by norm_num) hDelta0
      have hstep := mul_le_mul_of_nonneg_right hcoef
        (add_nonneg hdelta (by norm_num : (0 : ℝ) ≤ 2))
      linarith only [hstep, hDelta0]
    calc Real.rpow (3 : ℝ) (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta)
        ≤ Real.rpow (3 : ℝ) (1 + 3 * Delta) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 3 * Real.rpow (3 : ℝ) (3 * Delta) := by
          rw [← hrp 1 (3 * Delta), hrpow_one]
  have hexp2 : Real.rpow (3 : ℝ) (4 * s) ≤ 3 * Real.rpow (3 : ℝ) (3 * Delta) := by
    have h1 : Real.rpow (3 : ℝ) (4 * s) ≤ 3 := by
      have hstep : Real.rpow (3 : ℝ) (4 * s) ≤ Real.rpow (3 : ℝ) (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs4])
      rwa [hrpow_one] at hstep
    have h2 : (1 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * Delta) :=
      Real.one_le_rpow (by norm_num) (by linarith only [hDelta0])
    exact h1.trans (le_mul_of_one_le_right (by norm_num) h2)
  -- the gap conversion
  have hDeltaval : Real.rpow (3 : ℝ) Delta = (3 : ℝ) ^ n / (3 : ℝ) ^ k := by
    rw [hDeltadef, hrpow_sub, hrpow_nat, hrpow_int]
  have hDeltale : Real.rpow (3 : ℝ) Delta ≤ 27 * (3 : ℝ) ^ n / (R - rho) := by
    rw [hDeltaval, div_le_div_iff₀ h3k hgapPos]
    calc (3 : ℝ) ^ n * (R - rho) ≤ (3 : ℝ) ^ n * (27 * (3 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hgap2 hNpos.le
      _ = 27 * (3 : ℝ) ^ n * (3 : ℝ) ^ k := by ring
  have hcube : Real.rpow (3 : ℝ) (3 * Delta) ≤
      19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3 := by
    have hpow : Real.rpow (3 : ℝ) (3 * Delta) = (Real.rpow (3 : ℝ) Delta) ^ 3 := by
      rw [show (3 : ℝ) * Delta = Delta + Delta + Delta by ring, ← hrp, ← hrp]
      ring
    rw [hpow]
    calc (Real.rpow (3 : ℝ) Delta) ^ 3
        ≤ (27 * (3 : ℝ) ^ n / (R - rho)) ^ 3 :=
          pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hDeltale 3
      _ = 19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3 := by
          rw [div_pow]; ring
  -- assemble
  have hUvolub' : Uvol ≤ ((3 : ℝ) ^ n) ^ d := by
    refine hUvolub.trans (le_of_eq ?_)
    rw [zpow_natCast]
  have hne : (R - rho) ≠ 0 := ne_of_gt hgapPos
  have hcoefosc : (28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ)
      (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) ≤
      (28 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d * (3 * Real.rpow (3 : ℝ) (3 * Delta)) := by
    refine mul_le_mul ?_ hexp1 (Real.rpow_nonneg (by norm_num) _) (by positivity)
    exact mul_le_mul_of_nonneg_left hUvolub' (by positivity)
  have hcoefdat : (28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ) (4 * s) ≤
      (28 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d * (3 * Real.rpow (3 : ℝ) (3 * Delta)) := by
    refine mul_le_mul ?_ hexp2 (Real.rpow_nonneg (by norm_num) _) (by positivity)
    exact mul_le_mul_of_nonneg_left hUvolub' (by positivity)
  set Cfac := ((28 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d *
    (3 * Real.rpow (3 : ℝ) (3 * Delta)) : ℝ) with hCfacdef
  have hmain : Kc * A * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
        ((28 : ℝ) ^ d * (Uvol * NL2)) +
      Real.rpow s (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
        ((28 : ℝ) ^ d * (Uvol * Gv))) ≤
      Kc * Cfac * (Leg1 + Leg3) := by
    have hexpand : Kc * A * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
          ((28 : ℝ) ^ d * (Uvol * NL2)) +
        Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
          ((28 : ℝ) ^ d * (Uvol * Gv))) =
        Kc * ((A * (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
            ((28 : ℝ) ^ d * (Uvol * NL2)))) +
          (A * (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
            Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) *
            ((28 : ℝ) ^ d * (Uvol * Gv))))) := by ring
    rw [hexpand, hosc_id, hdat_id]
    have hb1 : ((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ)
        (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta)) * Leg1 ≤ Cfac * Leg1 :=
      mul_le_mul_of_nonneg_right hcoefosc hLeg10
    have hb2 : ((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ) (4 * s)) * Leg3 ≤
        Cfac * Leg3 := mul_le_mul_of_nonneg_right hcoefdat hLeg30
    have := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hKc.le
    calc Kc * (((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ)
            (2 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta)) * Leg1 +
          ((28 : ℝ) ^ d * Uvol * Real.rpow (3 : ℝ) (4 * s)) * Leg3)
        ≤ Kc * (Cfac * Leg1 + Cfac * Leg3) := this
      _ = Kc * Cfac * (Leg1 + Leg3) := by ring
  refine hmain.trans ?_
  -- final constant
  have hbud0 : 0 ≤ harmonicPhysicalFourBudgets M L m n z x omega s u h g :=
    le_trans (add_nonneg hLeg10 hLeg30) hbud
  have hCfac0 : (0 : ℝ) ≤ Cfac := by
    rw [hCfacdef]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
  have hstep : Kc * Cfac * (Leg1 + Leg3) ≤
      Kc * Cfac * harmonicPhysicalFourBudgets M L m n z x omega s u h g :=
    mul_le_mul_of_nonneg_left hbud (mul_nonneg hKc.le hCfac0)
  refine hstep.trans ?_
  have hCfacle : Cfac ≤ (28 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d *
      (3 * (19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3)) := by
    rw [hCfacdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hcube (by norm_num)
  have hfinal : Kc * Cfac * harmonicPhysicalFourBudgets M L m n z x omega s u h g ≤
      Kc * ((28 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d *
        (3 * (19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3))) *
        harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCfacle hKc.le) hbud0
  refine hfinal.trans (le_of_eq ?_)
  field_simp
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
