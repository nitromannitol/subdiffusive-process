module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.CutoffHarmonicBoundaryInput
public import SubdiffusiveProcess.Analysis.SmoothDualInteriorLeg

@[expose] public section

/-!
# The harmonic-approximation boundary comparison on the K-free loop

Upstream `Section6CutoffHarmonic.harmonicComparisonClauseV6_of_cellRow` proves the full
(interior + boundary) harmonic-approximation estimate at displayed powers
`s^-2, s^-8, s^-4` from the sharp (paper-dual) loop.  Its only paper-dual factor is the
leading `(s/2)^(-1/2)` of the sharp loop carrier.

This file re-runs that proof on the K-free loop of
`SubdiffusiveProcess.Analysis.SmoothDualCutoffEntry`:

* `aux_b12bd_boundaryComparison_le_smoothLoopBound`: twin of
  `exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy`, one leaf swapped;
* `aux_b12bd_collapse_term1` and `aux_b12bd_loopBound_le`: the collapse, split into bounded
  lemmas (upstream needs `maxHeartbeats 2000000`; here everything runs at the default);
The downstream clause assembled from these estimates has the **original powers**
`s^(-3/2)` (oscillation), `s^(-3/2)·s^(-3/2)` (boundary gradient), `s^(-15/2)` (force) and
`s^(-7/2)` (boundary datum), on the cutoff event `goodEvent M (some L)`.

The boundary input is the proved upstream cell row
(`Section6CutoffHarmonic.exists_boundaryStepCellParentRow` →
`exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow` →
`exists_boundaryWeightedEnergySlot_of_cellRow`), which carries no paper-dual factor.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualComparison
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Analysis

/-! ### The loop application on the K-free carrier -/

/-- Twin of `Section6CutoffHarmonic.exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy`
on the K-free loop.  Only the loop leaf and the carrier change. -/
theorem aux_b12bd_boundaryComparison_le_smoothLoopBound
    (d : ℕ) [NeZero d] :
    ∃ (C : ℝ≥0∞) (Cd : ℝ), C < ∞ ∧ 0 < Cd ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      let Q := originCube d ((n : ℤ) - 2)
      let U := truncatedCube d (m : ℤ) (n : ℤ) x
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      let E := Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z)
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d (m : ℤ)) u h g →
        MemCubeEuclideanFullWsp (originCube d (m : ℤ)) s2
          FiniteLpExponent.two g →
      ∀ (S : ℝ),
        (∀ u0 : H1Function (openCubeSet Q),
          (∀ p, u0.grad p = u.grad (p + y)) →
          weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn Q)
              u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S) →
      ∀ (uD v : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        (∀ p, uD.toFun p = u.toFun p) →
        IsWeaklyHarmonicOn (fun _ ↦ (1 : ℝ))
          (translatedCube d ((n : ℤ) - 2) y) v →
        HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD →
        normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
            (fun p ↦ u.toFun p - v.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2 E S
            (Cd * Real.rpow s (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s g).toReal)
            Q (fun p ↦ g (p + y)) := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual_neZero d
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  refine ⟨C, Cd, hCtop, hCd, ?_⟩
  intro M s hs L m n hnm z x y omega hz hx hD hgood
  dsimp only
  intro u h g hdir hg S hweighted
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro uD v huD hharm htrace
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hsubOpen : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD hp).2
  obtain ⟨g0, hg0, hg0eq, u0, _v0, hu0forced, _hv0, _huv0, hu0val,
      hu0grad⟩ :=
    exists_localSourceComparisonDatum_of_dirichlet_retained M L omega m
      ((n : ℤ) - 2) y ⟨s, by
        exact (mul_pos (by norm_num)
          (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
        by linarith [hs.2]⟩ u h g hdir hg
      hsubOpen _ hsigma
  have hS := hweighted u0 hu0grad
  have hDforce := hforce ⟨s, by
      exact (mul_pos (by norm_num)
        (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
      by linarith [hs.2]⟩ m n hnm z x y
    hx hD g g0 hg hg0 hg0eq
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hharm' : IsUnitWeaklyHarmonicOn
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))) v := by
    exact isUnitWeaklyHarmonicOn_iff.mpr hharm
  have htrace' : MemH10
      (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))))
        (fun p ↦ v.toFun p - u.toFun p) := by
    exact memH10_sub_physical_of_hasZeroTraceDifferenceOn htrace huD
  have hg0fun : (fun p ↦ g (p + y)) = g0 := (funext hg0eq).symm
  rw [hg0fun]
  exact hloop M s hs L n omega y z hcontain hgood g0 hg0 u0 hu0forced
    u.toFun v hharm' htrace' hu0val S _ hS hDforce

/-! ### The collapse, split into bounded lemmas -/

/-- The energy leg of the collapse with the boundary weighted-energy slot:
`S1² · S1 = S1³` on `W` and on the boundary gradient `AH`, `S1³ · S1¹² = S1¹⁵` on the force
`G`, and `S1³ · S1⁴ = S1⁷` on the boundary datum `Hd`.  No paper-dual factor. -/
theorem aux_b12bd_collapse_term1
    {A cs sgi Ct p2 R e3 E Sv V Er Ck S1 N3 T W AH G Hd Cerr : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (hCk : 0 ≤ Ck)
    (hR : 0 < R) (hS1 : 0 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T)
    (hEr : 0 ≤ Er) (hG : 0 ≤ G) (hHd : 0 ≤ Hd) (hErC : Er ≤ Cerr)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hp2 : p2 = 2 * S1 ^ 2)
    (he3 : e3 ≤ 3)
    (hE0 : 0 ≤ E) (hE : E ≤ V * 3 * Er)
    (hSv0 : 0 ≤ Sv)
    (hSv : Sv ≤ 2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
      S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd)) :
    A * cs * sgi * (Ct * p2 * R * e3 * E * Sv) ≤
      (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * (N3 * AH) +
        (4 * A * Ct * V * Ck) * Cerr * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G +
        (4 * A * Ct * V * Ck) * Cerr * S1 ^ 7 * N3 * T * Hd := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  subst hcs hsgi hp2
  have hstep : A * (N3 / 9) * (R * R)⁻¹ * (Ct * (2 * S1 ^ 2) * R * e3 * E * Sv) ≤
      A * (N3 / 9) * (R * R)⁻¹ *
        (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
          (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
            S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd))) := by
    have hbase : 0 ≤ A * (N3 / 9) * (R * R)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hbase
    have h1 : Ct * (2 * S1 ^ 2) * R * e3 ≤ Ct * (2 * S1 ^ 2) * R * 3 :=
      mul_le_mul_of_nonneg_left he3 (by positivity)
    have h2 : Ct * (2 * S1 ^ 2) * R * e3 * E ≤
        Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) :=
      mul_le_mul h1 hE hE0 (by positivity)
    exact mul_le_mul h2 hSv hSv0 (by positivity)
  refine hstep.trans ?_
  have heq : A * (N3 / 9) * (R * R)⁻¹ *
      (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
        (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
          S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd))) =
      (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * (N3 * AH) +
        (4 * A * Ct * V * Ck) * Er * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) +
        (4 * A * Ct * V * Ck) * Er * (S1 ^ 7 * N3 * T * Hd) := by
    field_simp
    ring
  rw [heq]
  have hbase : 0 ≤ 4 * A * Ct * V * Ck := by positivity
  have hcap := mul_le_mul_of_nonneg_left hErC hbase
  have hrestG : 0 ≤ S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by positivity
  have hrestH : 0 ≤ S1 ^ 7 * N3 * T * Hd := by positivity
  have hG' := mul_le_mul_of_nonneg_right hcap hrestG
  have hH' := mul_le_mul_of_nonneg_right hcap hrestH
  calc (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * (N3 * AH) +
        (4 * A * Ct * V * Ck) * Er * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) +
        (4 * A * Ct * V * Ck) * Er * (S1 ^ 7 * N3 * T * Hd) ≤
      (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * (N3 * AH) +
        (4 * A * Ct * V * Ck) * Cerr * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) +
        (4 * A * Ct * V * Ck) * Cerr * (S1 ^ 7 * N3 * T * Hd) :=
      add_le_add (add_le_add le_rfl hG') hH'
    _ = _ := by ring

/-- Energy-leg constant (chosen before any model data). -/
noncomputable def aux_b12bd_constX (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞) (Ck : ℝ) : ℝ :=
  4 * (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
    Cloop.toReal * Real.sqrt (192 * (d : ℝ)) * Ck

/-- Force-leg constant (chosen before any model data). -/
noncomputable def aux_b12bd_constF (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    (Ck Cdslot Cerr Cb : ℝ) : ℝ :=
  aux_b12bd_constX d Cloop Ck * Cerr +
    (64 / 9) * (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
      Cloop.toReal * Cdslot * (1 + 9 * (Real.sqrt (192 * (d : ℝ)) * 3 * Cerr) ^ 2) +
    (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
      Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb

theorem aux_b12bd_constX_nonneg (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞) {Ck : ℝ}
    (hCk : 0 ≤ Ck) : 0 ≤ aux_b12bd_constX d Cloop Ck := by
  unfold aux_b12bd_constX
  positivity

theorem aux_b12bd_constF_nonneg (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    {Ck Cdslot Cerr Cb : ℝ} (hCk : 0 ≤ Ck) (hCdslot : 0 ≤ Cdslot) (hCerr : 0 ≤ Cerr)
    (hCb : 0 ≤ Cb) :
    0 ≤ aux_b12bd_constF d Cloop Ck Cdslot Cerr Cb := by
  have hX := aux_b12bd_constX_nonneg d Cloop hCk
  have hUD : 0 ≤ unitDirichletPoincareConst d := unitDirichletPoincareConst_nonneg d
  unfold aux_b12bd_constF
  positivity

/-- The boundary weighted-energy slot in the polynomial variables:
`dirichletWeightedEnergyFactor (s/3) (s/2) ≤ 2 S1`, `3^{-n} = N3⁻¹`, `s^{-6} = S1¹²`,
`s^{-2} = S1⁴`, `3^{sn} = T`. -/
theorem aux_b12bd_slot_le {n : ℕ} {s sigma Ck Wq AH Gq Hd : ℝ}
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma) (hCk : 0 ≤ Ck)
    (hWq0 : 0 ≤ Wq) (hAH0 : 0 ≤ AH) (hGq0 : 0 ≤ Gq) (hHd0 : 0 ≤ Hd) :
    Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
        (Real.sqrt sigma * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
          sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
          Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd))) ≤
      2 * s ^ (-(1 / 2 : ℝ)) * Ck *
        (Real.sqrt sigma * ((3 : ℝ) ^ (n : ℕ))⁻¹ * Wq + Real.sqrt sigma * AH +
          (s ^ (-(1 / 2 : ℝ))) ^ 12 * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * (n : ℝ)) * Gq +
          (s ^ (-(1 / 2 : ℝ))) ^ 4 * Real.sqrt sigma * (3 : ℝ) ^ (s * (n : ℝ)) * Hd) := by
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set R : ℝ := Real.sqrt sigma with hRdef
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  have hR : 0 < R := Real.sqrt_pos.mpr hsigma
  have hRR : R * R = sigma := Real.mul_self_sqrt hsigma.le
  have hN3 : 0 < N3 := by rw [hN3def]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hpowN : (3 : ℝ) ^ (-(n : ℤ)) = N3⁻¹ := by
    rw [hN3def, zpow_neg, zpow_natCast]
  have hs6 : Real.rpow s (-6 : ℝ) = S1 ^ 12 := by
    rw [hS1def, rpow_neg_half_pow hs0 12]; congr 1; norm_num
  have hs2 : Real.rpow s (-2 : ℝ) = S1 ^ 4 := by
    rw [hS1def, rpow_neg_half_pow hs0 4]; congr 1; norm_num
  have hrp : Real.rpow (3 : ℝ) (s * (n : ℝ)) = T := rfl
  have hRne : R ≠ 0 := ne_of_gt hR
  have hB : R * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
        sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
        Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd) =
      R * N3⁻¹ * Wq + R * AH + S1 ^ 12 * R⁻¹ * T * Gq + S1 ^ 4 * R * T * Hd := by
    rw [hrp, hpowN, hs6, hs2, ← hRR]
    field_simp
  have hB0 : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℤ)) * Wq := by positivity
    have h3 : (0 : ℝ) ≤ sigma⁻¹ *
        (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) :=
      mul_nonneg (inv_nonneg.mpr hsigma.le)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
          (Real.rpow_nonneg (by norm_num) _)) hGq0)
    have h4 : (0 : ℝ) ≤ Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
        (Real.rpow_nonneg (by norm_num) _)) hHd0
    linarith
  have hdw := dirichletWeightedEnergyFactor_third_half_le hs0 hs4
  have hnn : 0 ≤ R * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd)) :=
    mul_nonneg hR.le (mul_nonneg hCk hB0)
  calc Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
        (R * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
          sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
          Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd))) ≤
        (2 * S1) * (R * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
          sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
          Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd))) :=
      mul_le_mul_of_nonneg_right hdw hnn
    _ = 2 * S1 * Ck * (R * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
          sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
          Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd)) := by ring
    _ = _ := by rw [hB]

/-- **The K-free boundary collapse.**  The smooth loop carrier with the boundary
weighted-energy slot, the datum slot and the Besov slot collapses onto the original powers:
`s^(-3/2)` on the oscillation, `s^(-3/2)·s^(-3/2)` on the boundary gradient, `s^(-15/2)` on
the force and `s^(-7/2)` on the boundary datum.  Pure real arithmetic on `0 < s ≤ 1/4`. -/
theorem aux_b12bd_loopBound_le
    {d : ℕ} [NeZero d] (Cloop : ℝ≥0∞) {Ck Cdslot Cerr Cb : ℝ}
    (hCk : 0 < Ck) (hCdslot : 0 < Cdslot) (hCb : 0 < Cb)
    (n : ℕ) {s sigma Er Wq AH Gq Hd : ℝ} (hs0 : 0 < s) (hs4 : s ≤ 1 / 4)
    (hsigma : 0 < sigma) (hEr0 : 0 ≤ Er) (hErC : Er ≤ Cerr)
    (hWq0 : 0 ≤ Wq) (hAH0 : 0 ≤ AH) (hGq0 : 0 ≤ Gq) (hHd0 : 0 ≤ Hd)
    (smid s1 s2 : FractionalOrder) (hsmid : smid.1 = s / 2) (hs1 : s1.1 = s / 3)
    (hs2 : s2.1 = s)
    (Q : TriadicCube d) (g : Vec d → Vec d)
    (hBv : scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g ≤
      Cb * (3 : ℝ) ^ (s * (n : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Gq) :
    flatComparatorSmoothGoodEventLoopBound Cloop d n sigma smid s1 s2
        (Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er))
        (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
          (Real.sqrt sigma * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
            sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
            Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd))))
        (Cdslot * Real.rpow s (-(1 / 2 : ℝ)) * Gq) Q g ≤
      aux_b12bd_constX d Cloop Ck * s ^ (-3 / 2 : ℝ) * Er * Wq +
        aux_b12bd_constX d Cloop Ck * s ^ (-3 / 2 : ℝ) * Er *
          ((3 : ℝ) ^ (n : ℕ) * AH) +
        aux_b12bd_constF d Cloop Ck Cdslot Cerr Cb * s ^ (-15 / 2 : ℝ) *
          sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq +
        aux_b12bd_constX d Cloop Ck * Cerr * s ^ (-7 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Hd := by
  obtain ⟨sm, hsm⟩ := smid
  obtain ⟨t1, ht1⟩ := s1
  obtain ⟨t2, ht2⟩ := s2
  dsimp only at hsmid hs1 hs2
  subst sm t1 t2
  -- the three slots
  set V : ℝ := Real.sqrt (192 * (d : ℝ)) with hVdef
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Sfull : ℝ := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
    (Real.sqrt sigma * (Ck * ((3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd))) with hSfulldef
  set Dfull : ℝ := Cdslot * Real.rpow s (-(1 / 2 : ℝ)) * Gq with hDfulldef
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hE0 : 0 ≤ Efull := by rw [hEfulldef]; positivity
  have hSv := aux_b12bd_slot_le (n := n) hs0 hs4 hsigma hCk.le hWq0 hAH0 hGq0 hHd0
  rw [← hSfulldef] at hSv
  have hSv0 : 0 ≤ Sfull := by
    rw [hSfulldef]
    refine mul_nonneg (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCk.le ?_))
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℤ)) * Wq := by positivity
    have h3 : (0 : ℝ) ≤ sigma⁻¹ *
        (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) :=
      mul_nonneg (inv_nonneg.mpr hsigma.le)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
          (Real.rpow_nonneg (by norm_num) _)) hGq0)
    have h4 : (0 : ℝ) ≤ Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
        (Real.rpow_nonneg (by norm_num) _)) hHd0
    linarith
  have hD0 : 0 ≤ Dfull := by
    rw [hDfulldef]
    exact mul_nonneg (mul_nonneg hCdslot.le (Real.rpow_nonneg hs0.le _)) hGq0
  have hreadout := flatComparatorSmoothGoodEventLoopBound_le_realReadout
    Cloop d n sigma ⟨s / 2, hsm⟩ ⟨s / 3, ht1⟩ ⟨s, ht2⟩ Efull Sfull Dfull Q g
    (by dsimp only; linarith) hsigma hE0 hSv0 hD0
  refine hreadout.trans ?_
  dsimp only
  -- the polynomial variables
  set A : ℝ := (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal with hAdef
  set Ct : ℝ := Cloop.toReal with hCtdef
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hCt0 : 0 ≤ Ct := ENNReal.toReal_nonneg
  have hR : 0 < R := Real.sqrt_pos.mpr hsigma
  have hRR : R * R = sigma := Real.mul_self_sqrt hsigma.le
  have hS12 : (2 : ℝ) ≤ S1 := two_le_rpow_neg_half hs0 hs4
  have hS11 : (1 : ℝ) ≤ S1 := by linarith
  have hS10 : (0 : ℝ) ≤ S1 := by linarith
  have hN3 : 0 < N3 := by rw [hN3def]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hS2 : S1 ^ 2 = s⁻¹ := by
    rw [hS1def, rpow_neg_half_pow hs0 2,
      show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hS9 : S1 ^ 9 = s ^ (-(9 / 2 : ℝ)) := by
    rw [hS1def, rpow_neg_half_pow hs0 9]
    congr 1
    norm_num
  have hRRinv : (R * R)⁻¹ = sigma⁻¹ := by rw [hRR]
  have hcsB : (3 : ℝ) ^ ((n : ℤ) - 2) = N3 / 9 := by
    rw [hN3def,
      show ((n : ℤ) - 2) = ((n : ℕ) : ℤ) + (-2 : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
    ring
  have hcsA : centeredCubeScale ((n : ℤ) - 2) = N3 / 9 := by
    simpa only [centeredCubeScale] using hcsB
  -- elementary factor bounds
  have hthree : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (3 : ℝ) ^ a ≤ 3 := by
    intro a _ha1 ha2
    calc (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 3 := Real.rpow_one 3
  have hEB : Efull ≤ V * 3 * Er := by
    rw [hEfulldef]
    have h := hthree (s / 8 * (4 : ℝ)) (by positivity) (by linarith)
    calc V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) ≤ V * (3 * Er) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h hEr0) hV0
      _ = V * 3 * Er := by ring
  have hEC : Efull ≤ V * 3 * Cerr :=
    hEB.trans (mul_le_mul_of_nonneg_left hErC (by positivity))
  have he3 : (3 : ℝ) ^ (s / 3 : ℝ) ≤ 3 := hthree _ (by positivity) (by linarith)
  have hp2 : (s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by
    rw [hS2]
    field_simp
  have hpinv : (s - s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by
    rw [hS2, show s - s / 2 = s / 2 by ring]
    field_simp
  have hp9 : (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ 32 * S1 ^ 9 := by
    have hc : (2 : ℝ) ^ (-(-(9 / 2 : ℝ))) ≤ 32 := by
      rw [neg_neg]
      have h5 : (2 : ℝ) ^ ((5 : ℕ) : ℝ) = 32 := by
        rw [Real.rpow_natCast]; norm_num
      calc (2 : ℝ) ^ (9 / 2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 32 := h5
    have h := rpow_half_le_two_mul_rpow (c := 32) hs0 hc
    rw [hS9]
    exact h
  have hq30 : (0 : ℝ) ≤ 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 := by positivity
  have hq3 : 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 ≤
      1 + 9 * (V * 3 * Cerr) ^ 2 := by
    have hbase : (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull ≤ 3 * (V * 3 * Cerr) :=
      mul_le_mul (hthree _ (by positivity) (by linarith)) hEC hE0 (by norm_num)
    have hnn : 0 ≤ (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull := by positivity
    have hsq := pow_le_pow_left₀ hnn hbase 2
    refine le_trans (add_le_add (le_refl (1 : ℝ)) hsq) (le_of_eq ?_)
    ring
  have ht30 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have ht3 : (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) ≤ T := by
    rw [hTdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : ((((n : ℤ) - 3 : ℤ)) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact mul_le_mul_of_nonneg_left hcast hs0.le
  -- the three legs
  have h1 := aux_b12bd_collapse_term1 (A := A) (cs := centeredCubeScale ((n : ℤ) - 2))
    (sgi := sigma⁻¹) (Ct := Ct) (p2 := (s / 2)⁻¹) (R := R) (e3 := (3 : ℝ) ^ (s / 3))
    (E := Efull) (Sv := Sfull) (V := V) (Er := Er) (Ck := Ck) (S1 := S1) (N3 := N3)
    (T := T) (W := Wq) (AH := AH) (G := Gq) (Hd := Hd) (Cerr := Cerr)
    hA0 hCt0 hV0 hCk.le hR hS10 hN3 hT0 hEr0 hGq0 hHd0 hErC
    hcsA hRRinv.symm hp2 he3 hE0 hEB hSv0 hSv
  have h2 := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualComparison.aux_smoothCollapse_term2 (A := A) (cs := centeredCubeScale ((n : ℤ) - 2))
    (sgi := sigma⁻¹) (Ct := Ct) (p9 := (s / 2) ^ (-(9 / 2 : ℝ)))
    (pinv := (s - s / 2)⁻¹) (q3 := 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2)
    (t3 := (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ))) (Dv := Dfull) (Cdc := Cdslot)
    (CY1 := 1 + 9 * (V * 3 * Cerr) ^ 2) (R := R) (S1 := S1) (N3 := N3) (T := T)
    (G := Gq)
    hA0 hCt0 hCdslot.le (by positivity) hR hS11 hN3 hT0 hGq0
    hcsA hRRinv.symm hp9 hpinv hq30 hq3 ht30 ht3 rfl
  have h3 := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualComparison.aux_smoothCollapse_term3 (UD := unitDirichletPoincareConst d)
    (cs := (3 : ℝ) ^ ((n : ℤ) - 2)) (dd := (d : ℝ)) (sgi := sigma⁻¹)
    (SC := Real.sqrt (Fintype.card (Fin d) : ℝ))
    (Bv := scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g) (CB := Cb)
    (R := R) (S1 := S1) (N3 := N3) (T := T) (G := Gq)
    (unitDirichletPoincareConst_nonneg d) (by positivity) (Real.sqrt_nonneg _)
    hCb.le hR hS11 hN3 hT0 hGq0 hcsB hRRinv.symm hBv
  -- power dictionary
  have hS3 : S1 ^ 3 = s ^ (-3 / 2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 3]
    congr 1
  have hS7 : S1 ^ 7 = s ^ (-7 / 2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 7]
    congr 1
  have hS15 : S1 ^ 15 = s ^ (-15 / 2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 15]
    congr 1
  have hN3T : N3 * T = (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := by
    rw [hN3def, hTdef, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hX : aux_b12bd_constX d Cloop Ck = 4 * A * Ct * V * Ck := rfl
  have hF : aux_b12bd_constF d Cloop Ck Cdslot Cerr Cb =
      (4 * A * Ct * V * Ck) * Cerr + (64 / 9) * A * Ct * Cdslot *
        (1 + 9 * (V * 3 * Cerr) ^ 2) +
      (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
        Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb := rfl
  rw [hRRinv] at h1 h2 h3
  have hkey : A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
        (Ct * (s / 2)⁻¹ * R * (3 : ℝ) ^ (s / 3) * Efull * Sfull +
          Ct * (s / 2) ^ (-(9 / 2 : ℝ)) * (s - s / 2)⁻¹ *
            (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
            (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull) +
      unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g) ≤
      (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * Wq +
        (4 * A * Ct * V * Ck) * S1 ^ 3 * Er * (N3 * AH) +
        ((4 * A * Ct * V * Ck) * Cerr + (64 / 9) * A * Ct * Cdslot *
            (1 + 9 * (V * 3 * Cerr) ^ 2) +
          (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
            Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb) * S1 ^ 15 * sigma⁻¹ *
          (N3 * T) * Gq +
        (4 * A * Ct * V * Ck) * Cerr * S1 ^ 7 * (N3 * T) * Hd := by
    rw [mul_add]
    refine le_trans (add_le_add (add_le_add h1 h2) h3) (le_of_eq ?_)
    ring
  refine le_trans hkey (le_of_eq ?_)
  rw [hX, hF, hS3, hS7, hS15, hN3T]

end SubdiffusiveProcess.Analysis
