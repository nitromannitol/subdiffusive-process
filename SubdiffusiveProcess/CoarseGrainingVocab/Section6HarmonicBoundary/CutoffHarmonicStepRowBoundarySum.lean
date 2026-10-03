/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowBoundarySum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowResidualMean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



def BoundaryStepCellParentRow (d : ℕ) (Cbd : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), n + 5 ≤ m →
  ∀ k : ℤ, k ≤ (n : ℤ) - 4 →
  ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    q ∈ cube d (m : ℤ) →
    q ∈ supWindow x (4 * (3 : ℝ) ^ n / 9) →
    translatedCube d k (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) ⊆
      truncatedCube d (m : ℤ) (n : ℤ) x →
    ¬ (openCubeAtScale q (k - 1) ⊆ cube d (m : ℤ)) →
    omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d) (c0 : ℝ),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
    let P := translatedCube d k
      (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)
    let sigma := tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z)
    (∫ p in truncatedCube d (m : ℤ) (k - 2) q,
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      (1 / (16 * (28 : ℝ) ^ d)) *
          (∫ p in P,
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) +
        Cbd * Real.rpow (3 : ℝ)
            (4 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
          (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
              (∫ p in P, (u.toFun p - c0) ^ 2) +
            Real.rpow (3 : ℝ)
                (8 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                (Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
                ((volume P).toReal *
                  (fractionalSeminormOn P sOrder.1 g).toReal ^ 2) +
            Real.rpow (3 : ℝ)
                (8 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                (sigma * Real.rpow sOrder.1 (-4 : ℝ) *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * ((k : ℤ) : ℝ))) *
                ((volume P).toReal *
                  (fractionalSeminormOn P sOrder.1 h.grad).toReal ^ 2) +
            Real.rpow (3 : ℝ)
                (8 * sOrder.1 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) * sigma *
              (∫ p in P, vecNormSq (h.grad p))) +
        Cbd * ((3 : ℝ) ^ (k - 2)) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 *
          harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g


/-- **The summed boundary half of the step row.**

The parent-local boundary row, summed over the boundary class of the cover of
the window of radius `ρ`.  The feedback is returned as the *unsummed* parent
sum, which `StepRowWindowStep` collapses to `(1/16) · windowCutoffEnergy … R`
by bounded overlap; the price is the four printed budgets in the step row's own
normalization. -/
theorem exists_boundaryCellSum_le_parentFeedback_add_budgets_atScale
    (d : ℕ) [NeZero d] {Cbd : ℝ} (hCbd : 0 ≤ Cbd)
    (hrow : BoundaryStepCellParentRow d Cbd) :
    ∃ K : ℝ, 0 ≤ K ∧
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
            (fun idx => ¬ (openCubeAtScale (cellCentre (k - 2) idx) (k - 1) ⊆
              cube d (m : ℤ))),
          (∫ p in truncatedCube d (m : ℤ) (k - 2) (cellCentre (k - 2) idx),
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
          (1 / (16 * (28 : ℝ) ^ d)) *
              (∑ idx ∈ windowBox (k - 2) x rho,
                ∫ p in stepRowParent (d := d) (k - 2) (m : ℤ) idx,
                  SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                    vecNormSq (u.grad p)) +
            K * ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 *
              harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g /
              (R - rho) ^ 3 := by
  classical
  obtain ⟨Cdat, hCdat, hdatbud⟩ :=
    exists_setIntegral_vecNormSq_grad_le_windowBudgets d
  refine ⟨2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1), by positivity, ?_⟩
  intro M sOrder hs L m n hnm k hk z x omega hz hx hgood u h g hdir hg hh
    rho R hrho hlt hR hgap hgap2
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
  set E : Vec d → ℝ := fun p =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p) with hEdef
  have hE0 : ∀ p, 0 ≤ E p := fun p => cutoffEnergyDensity_nonneg M L omega u p
  have hs0 : 0 < s := sOrder.2.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hxcube : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  set Bud : ℝ := harmonicPhysicalFourBudgets M L m n z x omega s u h g with hBuddef
  have hBud0 : 0 ≤ Bud :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0
      (Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _) u h g
  set T : Finset (Fin d → ℤ) := (windowBox j x rho).filter
    (fun idx => ¬ (openCubeAtScale (cellCentre j idx) (k - 1) ⊆
      cube d (m : ℤ))) with hTdef
  have hTsub : T ⊆ windowBox j x rho := Finset.filter_subset _ _
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
  have hfeedback0 : 0 ≤ ∑ idx ∈ windowBox j x rho,
      ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p :=
    Finset.sum_nonneg fun idx _ => integral_nonneg fun p => hE0 p
  -- the degenerate case: no cell of the boundary class carries mass
  by_cases hex : ∃ idx ∈ T, cellCentre (d := d) j idx ∈ cube d (m : ℤ)
  case neg =>
    have hzero : ∀ idx ∈ T,
        (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx), E p) = 0 := by
      intro idx hidx
      have hq : cellCentre (d := d) j idx ∉ cube d (m : ℤ) := by
        intro hmem
        exact hex ⟨idx, hidx, hmem⟩
      rw [truncatedCube_cellCentre_eq_empty_of_notMem_cube (by omega) hq,
        Measure.restrict_empty, integral_zero_measure]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    have h1 : 0 ≤ (1 / (16 * (28 : ℝ) ^ d)) *
        (∑ idx ∈ windowBox j x rho,
          ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) :=
      mul_nonneg (by positivity) hfeedback0
    have h2 : 0 ≤ 2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) *
        ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3 := by
      apply div_nonneg _ (by positivity)
      have hc : (0 : ℝ) ≤ 2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) *
          ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 := by positivity
      exact mul_nonneg hc hBud0
    linarith
  case pos =>
  obtain ⟨idx0, hidx0T, hidx0q⟩ := hex
  -- the centres of the mass-carrying boundary cells are `near`
  have hnear : ∀ idx : Fin d → ℤ, cellCentre (d := d) j idx ∈ cube d (m : ℤ) →
      stepRowNear (d := d) j (m : ℤ) idx := by
    intro idx hq i
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hq
    have hi := hq i
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2, h3j]
  have hPeq : ∀ idx : Fin d → ℤ, cellCentre (d := d) j idx ∈ cube d (m : ℤ) →
      stepRowParent (d := d) j (m : ℤ) idx =
        translatedCube d k (Section6ExcessDecay.wellPlacedCentre
          (cellCentre j idx) (m : ℤ) k) := by
    intro idx hq
    rw [stepRowParent, if_pos (hnear idx hq), hjk]
  -- the printed boundary indicator
  have htouch : BoundaryTouches U (cube d (m : ℤ)) := by
    have hnot0 := (Finset.mem_filter.mp hidx0T).2
    have hb := boundaryTouches_translatedCube_wellPlacedCentre
      (q := cellCentre (d := d) j idx0) hkm hnot0
    rw [← hPeq idx0 hidx0q] at hb
    exact Section6Holder.BoundaryTouches.mono (hPU idx0 (hTsub hidx0T)) hb

  -- measure-theoretic data on the budget window
  have hUmeas : MeasurableSet U :=
    Section6ExcessDecay.measurableSet_truncatedCube d _ _ _
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos
      (m := (m : ℤ)) (j := (n : ℤ)) x hxcube (by omega)
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ∞ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hAcube0 : volume (cube d (m : ℤ)) ≠ 0 := by
    have hreal : 0 < (volume (cube d (m : ℤ))).toReal := by
      rw [cube, volume_openCubeSet_toReal]
      exact cubeVolume_pos (originCube d (m : ℤ))
    exact (ENNReal.toReal_ne_zero.mp hreal.ne').1
  have hAcubeTop : volume (cube d (m : ℤ)) ≠ ∞ := by
    rw [cube]; exact (volume_openCubeSet_lt_top (originCube d (m : ℤ))).ne
  have hfracg : MemFractionalOn (cube d (m : ℤ)) s g := by
    change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ))) s g ≠ ⊤
    rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have hUfin : fractionalSeminormOn U s g ≠ ⊤ :=
    memFractionalOn_mono_set hUsub hAcube0 hAcubeTop hU0 hfracg
  have hUfinH : fractionalSeminormOn U s h.grad ≠ ⊤ :=
    memFractionalOn_mono_set hUsub hAcube0 hAcubeTop hU0 hh
  have huLp : MemLp u.toFun 2 (volume.restrict U) :=
    u.memL2.mono_measure (Measure.restrict_mono hUsub le_rfl)
  have hoscInt : IntegrableOn (fun p => (u.toFun p - c0) ^ 2) U :=
    Section6ExcessDecay.integrableOn_sub_const_sq_truncatedCube x huLp c0
  have hdatInt : IntegrableOn (fun p => vecNormSq (h.grad p)) U := by
    have hL2 : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) h.grad :=
      h.grad_memVectorL2
    have hfull : IntegrableOn (fun p => vecNormSq (h.grad p))
        (openCubeSet (originCube d (m : ℤ))) := by
      simpa only [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hL2 hL2
    exact hfull.mono_set hUsub
  -- restrict to the mass-carrying boundary cells
  set T' : Finset (Fin d → ℤ) := T.filter
    (fun idx => cellCentre (d := d) j idx ∈ cube d (m : ℤ)) with hT'def
  have hT'subT : T' ⊆ T := Finset.filter_subset _ _
  have hT'sub : T' ⊆ windowBox j x rho := hT'subT.trans hTsub
  have hT'centre : ∀ idx ∈ T', cellCentre (d := d) j idx ∈ cube d (m : ℤ) :=
    fun idx hidx => (Finset.mem_filter.mp hidx).2
  have hsumeq : ∑ idx ∈ T',
      (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx), E p) =
      ∑ idx ∈ T, (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx), E p) := by
    refine Finset.sum_filter_of_ne ?_
    intro idx _ hne
    by_contra hq
    apply hne
    rw [truncatedCube_cellCentre_eq_empty_of_notMem_cube (by omega) hq,
      Measure.restrict_empty, integral_zero_measure]
  rw [← hsumeq]
  -- the four summation legs
  set Gosc : Vec d → ℝ := U.indicator (fun p => (u.toFun p - c0) ^ 2) with hGoscdef
  have hGosc0 : ∀ p, 0 ≤ Gosc p := fun p =>
    Set.indicator_nonneg (fun q _ => sq_nonneg _) p
  have hGoscInt : Integrable Gosc := hoscInt.integrable_indicator hUmeas
  have hoscSum : ∑ idx ∈ T',
      (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) ≤
      (28 : ℝ) ^ d * ∫ p in U, (u.toFun p - c0) ^ 2 := by
    have hbox : ∑ idx ∈ windowBox j x rho,
        (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) ≤
        (28 : ℝ) ^ d * ∫ p in U, (u.toFun p - c0) ^ 2 := by
      have hrewrite : ∀ idx ∈ windowBox j x rho,
          (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) =
            ∫ p in stepRowParent (d := d) j (m : ℤ) idx, Gosc p := by
        intro idx hidx
        rw [hGoscdef, setIntegral_indicator hUmeas,
          Set.inter_eq_self_of_subset_left (hPU idx hidx)]
      rw [Finset.sum_congr rfl hrewrite]
      refine (sum_setIntegral_parents_le j x rho hGosc0 _
        (measurableSet_stepRowParent j (m : ℤ)) (fun idx _ =>
          stepRowParent_subset_supWindow hkm2 idx) hGoscInt.integrableOn).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hGoscdef, setIntegral_indicator hUmeas]
      exact setIntegral_mono_set hoscInt
        (Filter.Eventually.of_forall fun p => sq_nonneg _)
        (HasSubset.Subset.eventuallyLE Set.inter_subset_right)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hT'sub ?_) hbox
    intro idx _ _
    exact integral_nonneg fun p => sq_nonneg _
  set Gdat : Vec d → ℝ := U.indicator (fun p => vecNormSq (h.grad p)) with hGdatdef
  have hGdat0 : ∀ p, 0 ≤ Gdat p := fun p =>
    Set.indicator_nonneg (fun q _ => vecNormSq_nonneg _) p
  have hGdatInt : Integrable Gdat := hdatInt.integrable_indicator hUmeas
  have hdatSum : ∑ idx ∈ T',
      (∫ p in stepRowParent (d := d) j (m : ℤ) idx, vecNormSq (h.grad p)) ≤
      (28 : ℝ) ^ d * ∫ p in U, vecNormSq (h.grad p) := by
    have hbox : ∑ idx ∈ windowBox j x rho,
        (∫ p in stepRowParent (d := d) j (m : ℤ) idx, vecNormSq (h.grad p)) ≤
        (28 : ℝ) ^ d * ∫ p in U, vecNormSq (h.grad p) := by
      have hrewrite : ∀ idx ∈ windowBox j x rho,
          (∫ p in stepRowParent (d := d) j (m : ℤ) idx, vecNormSq (h.grad p)) =
            ∫ p in stepRowParent (d := d) j (m : ℤ) idx, Gdat p := by
        intro idx hidx
        rw [hGdatdef, setIntegral_indicator hUmeas,
          Set.inter_eq_self_of_subset_left (hPU idx hidx)]
      rw [Finset.sum_congr rfl hrewrite]
      refine (sum_setIntegral_parents_le j x rho hGdat0 _
        (measurableSet_stepRowParent j (m : ℤ)) (fun idx _ =>
          stepRowParent_subset_supWindow hkm2 idx) hGdatInt.integrableOn).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hGdatdef, setIntegral_indicator hUmeas]
      exact setIntegral_mono_set hdatInt
        (Filter.Eventually.of_forall fun p => vecNormSq_nonneg _)
        (HasSubset.Subset.eventuallyLE Set.inter_subset_right)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hT'sub ?_) hbox
    intro idx _ _
    exact integral_nonneg fun p => vecNormSq_nonneg _
  have hPvol : ∀ idx ∈ T',
      (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal = ((3 : ℝ) ^ k) ^ d := by
    intro idx hidx
    rw [hPeq idx (hT'centre idx hidx)]
    exact Section6BoundedMultiplier.volume_translatedCube_toReal k _
  have hPne : ∀ idx ∈ T', volume (stepRowParent (d := d) j (m : ℤ) idx) ≠ 0 := by
    intro idx hidx
    have hpos : 0 < (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal := by
      rw [hPvol idx hidx]; positivity
    exact (ENNReal.toReal_ne_zero.mp hpos.ne').1
  have hPtop : ∀ idx ∈ T', volume (stepRowParent (d := d) j (m : ℤ) idx) ≠ ∞ := by
    intro idx hidx
    rw [hPeq idx (hT'centre idx hidx)]
    exact Section6BoundedMultiplier.volume_translatedCube_ne_top k _
  have hforceSum : ∑ idx ∈ T',
      (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
        (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx) s g).toReal ^ 2 ≤
      (28 : ℝ) ^ d * ((volume U).toReal *
        (fractionalSeminormOn U s g).toReal ^ 2) :=
    sum_volume_toReal_mul_fractionalSeminormOn_toReal_sq_le' j T' s g _
      (measurableSet_stepRowParent j (m : ℤ))
      (fun idx _ => stepRowParent_subset_supWindow hkm2 idx) hPne hPtop U hUmeas
      (fun idx hidx => hPU idx (hT'sub hidx)) hU0 hUtop hUfin
  have hsemiSum : ∑ idx ∈ T',
      (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
        (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx) s h.grad).toReal ^ 2 ≤
      (28 : ℝ) ^ d * ((volume U).toReal *
        (fractionalSeminormOn U s h.grad).toReal ^ 2) :=
    sum_volume_toReal_mul_fractionalSeminormOn_toReal_sq_le' j T' s h.grad _
      (measurableSet_stepRowParent j (m : ℤ))
      (fun idx _ => stepRowParent_subset_supWindow hkm2 idx) hPne hPtop U hUmeas
      (fun idx hidx => hPU idx (hT'sub hidx)) hU0 hUtop hUfinH
  -- the per-cell parent-local boundary row
  set A : ℝ := Real.rpow (3 : ℝ)
    (4 * s * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  set E8 : ℝ := Real.rpow (3 : ℝ)
    (8 * s * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) with hE8def
  have hE80 : 0 < E8 := Real.rpow_pos_of_pos (by norm_num) _
  set co1 : ℝ := sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) with hco1def
  set co2 : ℝ := E8 * (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
    Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) with hco2def
  set co3 : ℝ := E8 * (sigma * Real.rpow s (-4 : ℝ) *
    Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) with hco3def
  set co4 : ℝ := E8 * sigma with hco4def
  have hco10 : 0 ≤ co1 :=
    mul_nonneg hsigma.le (Real.rpow_nonneg (by norm_num) _)
  have hco20 : 0 ≤ co2 :=
    mul_nonneg hE80.le
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (inv_nonneg.mpr hsigma.le))
        (Real.rpow_nonneg (by norm_num) _))
  have hco30 : 0 ≤ co3 :=
    mul_nonneg hE80.le
      (mul_nonneg (mul_nonneg hsigma.le (Real.rpow_nonneg hs0.le _))
        (Real.rpow_nonneg (by norm_num) _))
  have hco40 : 0 ≤ co4 := mul_nonneg hE80.le hsigma.le
  have hcellrow : ∀ idx ∈ T',
      (∫ p in truncatedCube d (m : ℤ) j (cellCentre j idx), E p) ≤
        (1 / (16 * (28 : ℝ) ^ d)) *
            (∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) +
          Cbd * A * (co1 *
                (∫ p in stepRowParent (d := d) j (m : ℤ) idx,
                  (u.toFun p - c0) ^ 2) +
              co2 * ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
                (fractionalSeminormOn
                  (stepRowParent (d := d) j (m : ℤ) idx) s g).toReal ^ 2) +
              co3 * ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
                (fractionalSeminormOn
                  (stepRowParent (d := d) j (m : ℤ) idx) s h.grad).toReal ^ 2) +
              co4 * (∫ p in stepRowParent (d := d) j (m : ℤ) idx,
                vecNormSq (h.grad p))) +
          Cbd * ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * Bud := by
    intro idx hidx
    have hq := hT'centre idx hidx
    have hnot := (Finset.mem_filter.mp (hT'subT hidx)).2
    have hidxbox := hT'sub hidx
    have hqwin : cellCentre (d := d) j idx ∈ supWindow x (4 * (3 : ℝ) ^ n / 9) := by
      have hself : cellCentre (d := d) j idx ∈
          supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2) := by
        intro i
        have hpos : (0 : ℝ) < (3 : ℝ) ^ (j + 3) := zpow_pos (by norm_num) _
        simp only [sub_self, abs_zero]
        linarith
      have h2 := supWindow_cellCentre_subset_supWindow hidxbox hself
      exact supWindow_mono (by linarith) h2
    have hparent := translatedCube_wellPlacedCentre_subset_truncatedCube_of_supWindow
      (n := n) hq hkm hk hqwin
    have hraw := hrow M sOrder hs L m n hnm k hk z x (cellCentre j idx) omega
      hz hx hq hqwin hparent hnot hgood u h g c0 hdir hg hh
    simp only [hEdef]
    rw [hPeq idx hq]
    exact hraw
  have hsum := Finset.sum_le_sum hcellrow
  set S1 : ℝ := ∑ idx ∈ T',
    (∫ p in stepRowParent (d := d) j (m : ℤ) idx, (u.toFun p - c0) ^ 2) with hS1def
  set S2 : ℝ := ∑ idx ∈ T',
    (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
      (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx) s g).toReal ^ 2
    with hS2def
  set S3 : ℝ := ∑ idx ∈ T',
    (volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
      (fractionalSeminormOn (stepRowParent (d := d) j (m : ℤ) idx) s h.grad).toReal ^ 2
    with hS3def
  set S4 : ℝ := ∑ idx ∈ T',
    (∫ p in stepRowParent (d := d) j (m : ℤ) idx, vecNormSq (h.grad p)) with hS4def
  have hdistrib : ∑ idx ∈ T',
      ((1 / (16 * (28 : ℝ) ^ d)) *
          (∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) +
        Cbd * A * (co1 *
              (∫ p in stepRowParent (d := d) j (m : ℤ) idx,
                (u.toFun p - c0) ^ 2) +
            co2 * ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
              (fractionalSeminormOn
                (stepRowParent (d := d) j (m : ℤ) idx) s g).toReal ^ 2) +
            co3 * ((volume (stepRowParent (d := d) j (m : ℤ) idx)).toReal *
              (fractionalSeminormOn
                (stepRowParent (d := d) j (m : ℤ) idx) s h.grad).toReal ^ 2) +
            co4 * (∫ p in stepRowParent (d := d) j (m : ℤ) idx,
              vecNormSq (h.grad p))) +
          Cbd * ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * Bud) =
      (1 / (16 * (28 : ℝ) ^ d)) *
          (∑ idx ∈ T', ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) +
        Cbd * A * (co1 * S1 + co2 * S2 + co3 * S3 + co4 * S4) +
        (T'.card : ℝ) *
          (Cbd * ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * Bud) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      hS1def, hS2def, hS3def, hS4def, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdistrib] at hsum
  refine hsum.trans ?_
  have hfeed : ∑ idx ∈ T', (∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) ≤
      ∑ idx ∈ windowBox j x rho,
        ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hT'sub ?_
    intro idx _ _
    exact integral_nonneg fun p => hE0 p
  have hprice_final : Cbd * A * (co1 * S1 + co2 * S2 + co3 * S3 + co4 * S4) ≤
      (14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1)) *
        (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) := by
    clear_value A E8 co1 co2 co3 co4
    -- ## the exponent bookkeeping
    set Uv : ℝ := (volume U).toReal with hUvdef
    have hUv0 : 0 < Uv := hUpos
    have hUvle : Uv ≤ ((3 : ℝ) ^ n) ^ d := by
      have hb := (Section6ExcessDecay.volume_toReal_truncatedCube_bounds
        (m := (m : ℤ)) (j := (n : ℤ)) x hxcube (by omega)).2
      refine hb.trans (le_of_eq ?_)
      rw [zpow_natCast]
    set NL2 : ℝ := normalizedL2On U (fun p => u.toFun p - c0) ^ 2 with hNL2def
    have hNL20 : 0 ≤ NL2 := sq_nonneg _
    set Gv : ℝ := (fractionalSeminormOn U s g).toReal ^ 2 with hGvdef
    have hGv0 : 0 ≤ Gv := sq_nonneg _
    set Hv : ℝ := (fractionalSeminormOn U s h.grad).toReal ^ 2 with hHvdef
    have hHv0 : 0 ≤ Hv := sq_nonneg _
    set DatInt : ℝ := ∫ p in U, vecNormSq (h.grad p) with hDatIntdef
    have hoscEq : (∫ p in U, (u.toFun p - c0) ^ 2) = Uv * NL2 := by
      rw [hNL2def, normalizedL2On_sq_eq_volumeAverage U _
        (integral_nonneg fun p => sq_nonneg _), hUvdef, ← mul_assoc,
        mul_inv_cancel₀ hUv0.ne', one_mul]
    set Leg1 : ℝ := sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * NL2 with hLeg1def
    set Leg3 : ℝ := Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gv with hLeg3def
    set Leg4 : ℝ := sigma * Real.rpow s (-4 : ℝ) *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Hv with hLeg4def
    have hLeg10 : 0 ≤ Leg1 := by
      rw [hLeg1def]; exact mul_nonneg (mul_nonneg hsigma.le (by positivity)) hNL20
    have hLeg30 : 0 ≤ Leg3 := by
      rw [hLeg3def]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
        (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) hGv0
    have hLeg40 : 0 ≤ Leg4 := by
      rw [hLeg4def]
      exact mul_nonneg (mul_nonneg (mul_nonneg hsigma.le (Real.rpow_nonneg hs0.le _))
        (Real.rpow_nonneg (by norm_num) _)) hHv0
    have hbudEq : Bud = Leg1 +
        (if BoundaryTouches U (cube d (m : ℤ)) then
          sigma * vecNormSq (averageVecOn U h.grad) else 0) + Leg3 +
        (if BoundaryTouches U (cube d (m : ℤ)) then Leg4 else 0) := rfl
    have h134 : Leg1 + Leg3 + Leg4 ≤ Bud := by
      rw [hbudEq, if_pos htouch, if_pos htouch]
      have h2 : (0 : ℝ) ≤ sigma * vecNormSq (averageVecOn U h.grad) :=
        mul_nonneg hsigma.le (vecNormSq_nonneg _)
      linarith only [h2]
    have hdat := hdatbud M s hs0 hs4 L m n (by omega) z x omega hxcube u h g
      hUfinH htouch
    have hdatle : sigma * DatInt ≤ Cdat * (Uv * Bud) := by
      rw [hDatIntdef, hUvdef, hsigmadef, hBuddef, hUdef, hsdef]
      simpa only [mul_assoc] using hdat
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
      rw [hDeltadef]; linarith only [hkr]
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
      rw [← Real.rpow_intCast (3 : ℝ) (-(2 * (n : ℤ)))]
      norm_num
    have hAval : A = Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) := by
      rw [hAdef, hjjval]
    have hE8val : E8 = Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) := by
      rw [hE8def, hjjval]
    have hosc_id : A * (co1 * (Uv * NL2)) =
        (Uv * Real.rpow (3 : ℝ)
          (4 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta)) * Leg1 := by
      have hL : Leg1 = sigma * Real.rpow (3 : ℝ) (-(2 * (n : ℝ))) * NL2 := by
        rw [hLeg1def, hzpow1]
      have hkey : Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) *
          Real.rpow (3 : ℝ) (-(2 * (n : ℝ))) =
          Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
            Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) := by
        rw [hrp, hrp, hDeltadef]
        congr 1
        ring
      rw [hAval, hL, hco1def]
      calc Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
            (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) * (Uv * NL2))
          = Uv * (Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ))) * (sigma * NL2) := by ring
        _ = Uv * (Real.rpow (3 : ℝ)
              (4 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) *
              Real.rpow (3 : ℝ) (-(2 * (n : ℝ)))) * (sigma * NL2) := by rw [hkey]
        _ = _ := by ring
    set Wexp : ℝ := 12 * s * ((n : ℝ) + 2 - (k : ℝ)) - 2 * s * Delta with hWexpdef
    have hkeyS : Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
        Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) *
        Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ)) =
        Real.rpow (3 : ℝ) Wexp * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
      rw [hrp, hrp, hrp, hWexpdef, hDeltadef]
      congr 1
      ring
    have hforce_id : A * (co2 * (Uv * Gv)) =
        (Uv * Real.rpow (3 : ℝ) Wexp) * Leg3 := by
      rw [hAval, hco2def, hE8val, hLeg3def]
      calc Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
            (Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) * (Uv * Gv))
          = Uv * (Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) *
              (Real.rpow s (-12 : ℝ) * sigma⁻¹ * Gv) := by ring
        _ = Uv * (Real.rpow (3 : ℝ) Wexp *
              Real.rpow (3 : ℝ) (2 * s * (n : ℝ))) *
              (Real.rpow s (-12 : ℝ) * sigma⁻¹ * Gv) := by rw [hkeyS]
        _ = _ := by ring
    have hsemi_id : A * (co3 * (Uv * Hv)) =
        (Uv * Real.rpow (3 : ℝ) Wexp) * Leg4 := by
      rw [hAval, hco3def, hE8val, hLeg4def]
      calc Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
            (Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              (sigma * Real.rpow s (-4 : ℝ) *
                Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) * (Uv * Hv))
          = Uv * (Real.rpow (3 : ℝ) (4 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (8 * s * ((n : ℝ) + 2 - (k : ℝ))) *
              Real.rpow (3 : ℝ) (2 * s * ((k : ℤ) : ℝ))) *
              (sigma * Real.rpow s (-4 : ℝ) * Hv) := by ring
        _ = Uv * (Real.rpow (3 : ℝ) Wexp *
              Real.rpow (3 : ℝ) (2 * s * (n : ℝ))) *
              (sigma * Real.rpow s (-4 : ℝ) * Hv) := by rw [hkeyS]
        _ = _ := by ring
    set W : ℝ := 729 * Real.rpow (3 : ℝ) (3 * Delta) with hWdef
    have hW0 : 0 ≤ W := by
      rw [hWdef]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    have hr729 : Real.rpow (3 : ℝ) (6 : ℝ) = 729 := by norm_num
    have hWexpEq : W = Real.rpow (3 : ℝ) (6 + 3 * Delta) := by
      rw [hWdef, ← hrp 6 (3 * Delta), hr729]
    have hDeq : (n : ℝ) + 2 - (k : ℝ) = Delta + 2 := by rw [hDeltadef]; ring
    have hexp1 : Real.rpow (3 : ℝ)
        (4 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta) ≤ W := by
      have hle : 4 * s * ((n : ℝ) + 2 - (k : ℝ)) + 2 * Delta ≤ 6 + 3 * Delta := by
        rw [hDeq]
        have hstep : 4 * s * (Delta + 2) ≤ (1 : ℝ) * (Delta + 2) :=
          mul_le_mul_of_nonneg_right (by linarith only [hs4])
            (by linarith only [hDelta0])
        linarith only [hstep]
      rw [hWexpEq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    have hexp2 : Real.rpow (3 : ℝ) Wexp ≤ W := by
      have hle : Wexp ≤ 6 + 3 * Delta := by
        rw [hWexpdef, hDeq]
        have hstep : 12 * s * (Delta + 2) ≤ (3 : ℝ) * (Delta + 2) :=
          mul_le_mul_of_nonneg_right (by linarith only [hs4])
            (by linarith only [hDelta0])
        have hneg : (0 : ℝ) ≤ 2 * s * Delta := by
          have : (0 : ℝ) ≤ Delta := by linarith only [hDelta0]
          positivity
        linarith only [hstep, hneg]
      rw [hWexpEq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    have hexpA : A * E8 ≤ W := by
      have hprod : A * E8 = Real.rpow (3 : ℝ) (12 * s * ((n : ℝ) + 2 - (k : ℝ))) := by
        rw [hAval, hE8val, hrp]
        congr 1
        ring
      have hle : 12 * s * ((n : ℝ) + 2 - (k : ℝ)) ≤ 6 + 3 * Delta := by
        rw [hDeq]
        have hstep : 12 * s * (Delta + 2) ≤ (3 : ℝ) * (Delta + 2) :=
          mul_le_mul_of_nonneg_right (by linarith only [hs4])
            (by linarith only [hDelta0])
        linarith only [hstep]
      rw [hprod, hWexpEq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
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
    have hWle : W ≤ 729 * (19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3) := by
      rw [hWdef]
      exact mul_le_mul_of_nonneg_left hcube (by norm_num)
    have h1 : co1 * S1 ≤ co1 * ((28 : ℝ) ^ d * (Uv * NL2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hco10
      rw [← hoscEq]
      exact hoscSum
    have h2 : co2 * S2 ≤ co2 * ((28 : ℝ) ^ d * (Uv * Gv)) :=
      mul_le_mul_of_nonneg_left hforceSum hco20
    have h3 : co3 * S3 ≤ co3 * ((28 : ℝ) ^ d * (Uv * Hv)) :=
      mul_le_mul_of_nonneg_left hsemiSum hco30
    have h4 : co4 * S4 ≤ co4 * ((28 : ℝ) ^ d * DatInt) :=
      mul_le_mul_of_nonneg_left hdatSum hco40
    have hprice : co1 * S1 + co2 * S2 + co3 * S3 + co4 * S4 ≤
        (28 : ℝ) ^ d * (co1 * (Uv * NL2) + co2 * (Uv * Gv) + co3 * (Uv * Hv) +
          co4 * DatInt) := by
      calc
        _ ≤ co1 * ((28 : ℝ) ^ d * (Uv * NL2)) +
            co2 * ((28 : ℝ) ^ d * (Uv * Gv)) +
            co3 * ((28 : ℝ) ^ d * (Uv * Hv)) +
            co4 * ((28 : ℝ) ^ d * DatInt) :=
          add_le_add (add_le_add (add_le_add h1 h2) h3) h4
        _ = _ := by ring
    have hmul : Cbd * A * (co1 * S1 + co2 * S2 + co3 * S3 + co4 * S4) ≤
        Cbd * A * ((28 : ℝ) ^ d * (co1 * (Uv * NL2) + co2 * (Uv * Gv) +
          co3 * (Uv * Hv) + co4 * DatInt)) :=
      mul_le_mul_of_nonneg_left hprice (mul_nonneg hCbd hA0.le)
    refine hmul.trans ?_
    have hexpand : Cbd * A * ((28 : ℝ) ^ d * (co1 * (Uv * NL2) + co2 * (Uv * Gv) +
          co3 * (Uv * Hv) + co4 * DatInt)) =
        Cbd * (28 : ℝ) ^ d * (A * (co1 * (Uv * NL2)) + A * (co2 * (Uv * Gv)) +
          A * (co3 * (Uv * Hv)) + A * (co4 * DatInt)) := by ring
    rw [hexpand]
    have hUW0 : 0 ≤ Uv * W := mul_nonneg hUv0.le hW0
    have hkey : A * (co1 * (Uv * NL2)) + A * (co2 * (Uv * Gv)) +
        A * (co3 * (Uv * Hv)) + A * (co4 * DatInt) ≤
        (1 + Cdat) * (Uv * W * Bud) := by
      have e1 : A * (co1 * (Uv * NL2)) ≤ Uv * W * Leg1 := by
        rw [hosc_id]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp1 hUv0.le) hLeg10
      have e2 : A * (co2 * (Uv * Gv)) ≤ Uv * W * Leg3 := by
        rw [hforce_id]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp2 hUv0.le) hLeg30
      have e3 : A * (co3 * (Uv * Hv)) ≤ Uv * W * Leg4 := by
        rw [hsemi_id]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp2 hUv0.le) hLeg40
      have e4 : A * (co4 * DatInt) ≤ W * (Cdat * (Uv * Bud)) := by
        have hstep : A * (co4 * DatInt) = (A * E8) * (sigma * DatInt) := by
          rw [hco4def]; ring
        rw [hstep]
        refine le_trans (mul_le_mul_of_nonneg_left hdatle
          (mul_nonneg hA0.le hE80.le)) ?_
        exact mul_le_mul_of_nonneg_right hexpA
          (mul_nonneg hCdat.le (mul_nonneg hUv0.le hBud0))
      have e5 : Uv * W * Leg1 + Uv * W * Leg3 + Uv * W * Leg4 ≤ Uv * W * Bud := by
        simpa only [mul_add] using mul_le_mul_of_nonneg_left h134 hUW0
      have e6 : W * (Cdat * (Uv * Bud)) = Cdat * (Uv * W * Bud) := by ring
      calc
        _ ≤ Uv * W * Leg1 + Uv * W * Leg3 + Uv * W * Leg4 +
            W * (Cdat * (Uv * Bud)) :=
          add_le_add (add_le_add (add_le_add e1 e2) e3) e4
        _ ≤ Uv * W * Bud + W * (Cdat * (Uv * Bud)) :=
          add_le_add e5 le_rfl
        _ = _ := by rw [e6]; ring
    have hstep := mul_le_mul_of_nonneg_left hkey
      (mul_nonneg hCbd (by positivity : (0 : ℝ) ≤ (28 : ℝ) ^ d))
    refine hstep.trans ?_
    have hUWB : Uv * W * Bud ≤
        ((3 : ℝ) ^ n) ^ d * (729 * (19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3)) * Bud :=
      mul_le_mul_of_nonneg_right (mul_le_mul hUvle hWle hW0 (by positivity)) hBud0
    set Gp : ℝ := ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3
      with hGpdef
    have hGp0 : 0 ≤ Gp := by
      rw [hGpdef]
      exact div_nonneg (mul_nonneg (by positivity) hBud0) (by positivity)
    have hGpeq : ((3 : ℝ) ^ n) ^ d *
        (729 * (19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3)) * Bud =
        14348907 * Gp := by
      rw [hGpdef]
      field_simp
      ring
    have hfin : Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * (Uv * W * Bud)) ≤
        Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * (14348907 * Gp)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCbd (by positivity))
      refine mul_le_mul_of_nonneg_left ?_ (add_nonneg zero_le_one hCdat.le)
      rw [← hGpeq]
      exact hUWB
    refine hfin.trans ?_
    have hconst : Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * 14348907) ≤
        14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) := by
      have hid : 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) =
          Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * 14348907) +
            14348907 * (28 : ℝ) ^ d * (Cdat + 1) := by ring
      have hcd : (0 : ℝ) ≤ Cdat + 1 := add_nonneg hCdat.le zero_le_one
      have hpos : (0 : ℝ) ≤ 14348907 * (28 : ℝ) ^ d * (Cdat + 1) := by positivity
      rw [hid]
      exact le_add_of_nonneg_right hpos
    calc Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * (14348907 * Gp))
        = (Cbd * (28 : ℝ) ^ d * ((1 + Cdat) * 14348907)) * Gp := by ring
      _ ≤ (14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1)) * Gp :=
          mul_le_mul_of_nonneg_right hconst hGp0

  -- the residual-mean budget leg
  have hcard : (T'.card : ℝ) * ((3 : ℝ) ^ j) ^ d ≤ ((3 : ℝ) ^ n) ^ d := by
    have hc1 : (T'.card : ℝ) ≤ (((windowBox j x rho).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hT'sub
    have hc2 := card_windowBox_le j x hrho
    have hpos : (0 : ℝ) ≤ ((3 : ℝ) ^ j) ^ d := by positivity
    have hmul : (T'.card : ℝ) * ((3 : ℝ) ^ j) ^ d ≤
        (2 * rho / (3 : ℝ) ^ j + 2) ^ d * ((3 : ℝ) ^ j) ^ d :=
      mul_le_mul_of_nonneg_right (hc1.trans hc2) hpos
    refine hmul.trans ?_
    rw [← mul_pow]
    have hval : (2 * rho / (3 : ℝ) ^ j + 2) * (3 : ℝ) ^ j =
        2 * rho + 2 * (3 : ℝ) ^ j := by field_simp
    rw [hval]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have hjsmall : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ n / 81 := by
      have h1 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ ((n : ℤ) - 6) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (3 : ℝ) ^ ((n : ℤ) - 6) = (3 : ℝ) ^ n / 729 := by
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
        norm_num
      rw [h2] at h1
      linarith only [h1, hNpos]
    linarith only [hjsmall, hgap, hR, hNpos, h3j]
  have hdepth : ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 ≤
      19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3 := by
    have hval : (3 : ℝ) ^ ((n : ℤ) - k) = (3 : ℝ) ^ n / (3 : ℝ) ^ k := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    have hle : (3 : ℝ) ^ ((n : ℤ) - k) ≤ 27 * (3 : ℝ) ^ n / (R - rho) := by
      rw [hval, div_le_div_iff₀ h3k hgapPos]
      calc (3 : ℝ) ^ n * (R - rho) ≤ (3 : ℝ) ^ n * (27 * (3 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hgap2 hNpos.le
        _ = 27 * (3 : ℝ) ^ n * (3 : ℝ) ^ k := by ring
    calc ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3
        ≤ (27 * (3 : ℝ) ^ n / (R - rho)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hle 3
      _ = 19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3 := by
          rw [div_pow]; ring
  have hextra : (T'.card : ℝ) *
      (Cbd * ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * Bud) ≤
      (19683 * Cbd) *
        (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) := by
    have hstep : (T'.card : ℝ) *
        (Cbd * ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * Bud) =
        ((T'.card : ℝ) * ((3 : ℝ) ^ j) ^ d) *
          (((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * (Cbd * Bud)) := by ring
    rw [hstep]
    have hA : ((T'.card : ℝ) * ((3 : ℝ) ^ j) ^ d) *
          (((3 : ℝ) ^ ((n : ℤ) - k)) ^ 3 * (Cbd * Bud)) ≤
        (((3 : ℝ) ^ n) ^ d) *
          ((19683 * ((3 : ℝ) ^ n) ^ 3 / (R - rho) ^ 3) * (Cbd * Bud)) := by
      refine mul_le_mul hcard ?_
        (mul_nonneg (by positivity) (mul_nonneg hCbd hBud0)) (by positivity)
      exact mul_le_mul_of_nonneg_right hdepth (mul_nonneg hCbd hBud0)
    refine hA.trans (le_of_eq ?_)
    field_simp
  -- assemble the three parts
  have hGp0' : (0 : ℝ) ≤
      ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3 :=
    div_nonneg (mul_nonneg (by positivity) hBud0) (by positivity)
  have hfeedstep : (1 / (16 * (28 : ℝ) ^ d)) *
      (∑ idx ∈ T', ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) ≤
      (1 / (16 * (28 : ℝ) ^ d)) *
        (∑ idx ∈ windowBox j x rho,
          ∫ p in stepRowParent (d := d) j (m : ℤ) idx, E p) :=
    mul_le_mul_of_nonneg_left hfeed (by positivity)
  have h28one : (1 : ℝ) ≤ (28 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hconsttot : 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) + 19683 * Cbd ≤
      2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) := by
    have hcd1 : (1 : ℝ) ≤ Cdat + 1 := le_add_of_nonneg_left hCdat.le
    have hA1 : (0 : ℝ) ≤ 14348907 * (Cbd + 1) :=
      mul_nonneg (by norm_num) (add_nonneg hCbd zero_le_one)
    have hA2 : (0 : ℝ) ≤ 14348907 * (Cbd + 1) * (28 : ℝ) ^ d :=
      mul_nonneg hA1 (by positivity)
    have hstep3 : 14348907 * (Cbd + 1) ≤ 14348907 * (Cbd + 1) * (28 : ℝ) ^ d :=
      le_mul_of_one_le_right hA1 h28one
    have hstep4 : 14348907 * (Cbd + 1) * (28 : ℝ) ^ d ≤
        14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) :=
      le_mul_of_one_le_right hA2 hcd1
    linarith only [hCbd, hstep3, hstep4]
  have hKtot : (14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) + 19683 * Cbd) *
      (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) ≤
      (2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1)) *
        (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) :=
    mul_le_mul_of_nonneg_right hconsttot hGp0'
  have hform : (2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1)) *
      (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) =
      2 * 14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) *
        ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3 := by
    ring
  have hsplit2 : (14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1) + 19683 * Cbd) *
      (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) =
      (14348907 * (Cbd + 1) * (28 : ℝ) ^ d * (Cdat + 1)) *
          (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) +
        (19683 * Cbd) *
          (((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 * Bud / (R - rho) ^ 3) := by
    ring
  linarith only [hfeedstep, hprice_final, hextra, hKtot, hform.ge, hform.le,
    hsplit2.ge, hsplit2.le]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
