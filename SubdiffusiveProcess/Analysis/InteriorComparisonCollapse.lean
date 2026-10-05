module

public import SubdiffusiveProcess.Analysis.SmoothDualCutoffEntry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.CollapseArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ComparisonDatumRetained

@[expose] public section




namespace SubdiffusiveProcess.InteriorComparisonCollapse

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualComparison
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

/-! ### The three polynomial legs of the K-free collapse -/

/-- Oscillation and energy-forcing leg: `S1² · S1 = S1³` on `W`, and
`S1³ · S1¹² = S1¹⁵` on `G`.  No paper-dual factor. -/
theorem aux_icc_collapse_term1
    {A cs sgi Ct p2 R e3 E Sv V Er SK S1 N3 T W G Cerr : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (hSK : 0 ≤ SK)
    (hR : 0 < R) (hS1 : 0 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T)
    (hEr : 0 ≤ Er) (hG : 0 ≤ G) (hErC : Er ≤ Cerr)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hp2 : p2 = 2 * S1 ^ 2)
    (he3 : e3 ≤ 3)
    (hE0 : 0 ≤ E) (hE : E ≤ V * 3 * Er)
    (hSv0 : 0 ≤ Sv)
    (hSv : Sv ≤ 2 * S1 * SK * (R * N3⁻¹ * W + S1 ^ 12 * R⁻¹ * T * G)) :
    A * cs * sgi * (Ct * p2 * R * e3 * E * Sv) ≤
      (4 * A * Ct * V * SK) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * SK) * Cerr * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  subst hcs hsgi hp2
  have hstep : A * (N3 / 9) * (R * R)⁻¹ * (Ct * (2 * S1 ^ 2) * R * e3 * E * Sv) ≤
      A * (N3 / 9) * (R * R)⁻¹ *
        (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
          (2 * S1 * SK * (R * N3⁻¹ * W + S1 ^ 12 * R⁻¹ * T * G))) := by
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
        (2 * S1 * SK * (R * N3⁻¹ * W + S1 ^ 12 * R⁻¹ * T * G))) =
      (4 * A * Ct * V * SK) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * SK) * Er * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) := by
    field_simp
    ring
  rw [heq]
  have hbase : 0 ≤ 4 * A * Ct * V * SK := by positivity
  have hrest : 0 ≤ S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by positivity
  have hsecond := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hErC hbase) hrest
  calc (4 * A * Ct * V * SK) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * SK) * Er * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) ≤
      (4 * A * Ct * V * SK) * S1 ^ 3 * Er * W +
        (4 * A * Ct * V * SK) * Cerr * (S1 ^ 15 * (R * R)⁻¹ * N3 * T * G) :=
      add_le_add le_rfl hsecond
    _ = _ := by ring

/-- Direct-forcing leg through the datum slot: `S1⁹ · S1² · S1 = S1¹²`, absorbed
into `S1¹⁵` on the corridor (`1 ≤ S1`). -/
theorem aux_dedup_d065_aux_icc_collapse_term2
    {A cs sgi Ct p9 pinv q3 t3 Dv Cdc CY1 R S1 N3 T G : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hCdc : 0 ≤ Cdc) (hCY1 : 0 ≤ CY1)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hp9 : p9 ≤ 32 * S1 ^ 9)
    (hpinv : pinv = 2 * S1 ^ 2)
    (hq30 : 0 ≤ q3) (hq3 : q3 ≤ CY1)
    (ht30 : 0 ≤ t3) (ht3 : t3 ≤ T)
    (hDv : Dv = Cdc * S1 * G) :
    A * cs * sgi * (Ct * p9 * pinv * q3 * t3 * Dv) ≤
      ((64 / 9) * A * Ct * Cdc * CY1) * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  have hS10 : (0 : ℝ) ≤ S1 := le_trans zero_le_one hS1
  subst hcs hsgi hpinv hDv
  have hstep : A * (N3 / 9) * (R * R)⁻¹ *
        (Ct * p9 * (2 * S1 ^ 2) * q3 * t3 * (Cdc * S1 * G)) ≤
      A * (N3 / 9) * (R * R)⁻¹ *
        (Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T * (Cdc * S1 * G)) := by
    have hbase : 0 ≤ A * (N3 / 9) * (R * R)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hbase
    have h1 : Ct * p9 ≤ Ct * (32 * S1 ^ 9) :=
      mul_le_mul_of_nonneg_left hp9 hCt
    have h2 : Ct * p9 * (2 * S1 ^ 2) ≤ Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : Ct * p9 * (2 * S1 ^ 2) * q3 ≤
        Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 :=
      mul_le_mul h2 hq3 hq30 (by positivity)
    have h4 : Ct * p9 * (2 * S1 ^ 2) * q3 * t3 ≤
        Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T :=
      mul_le_mul h3 ht3 ht30 (by positivity)
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  refine hstep.trans ?_
  have heq : A * (N3 / 9) * (R * R)⁻¹ *
      (Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T * (Cdc * S1 * G)) =
      ((64 / 9) * A * Ct * Cdc * CY1) * ((R * R)⁻¹ * N3 * T * G) * S1 ^ 12 := by
    field_simp
    ring
  rw [heq]
  have hpow : S1 ^ 12 ≤ S1 ^ 15 := pow_le_pow_right₀ hS1 (by norm_num)
  have hbase : 0 ≤ ((64 / 9) * A * Ct * Cdc * CY1) * ((R * R)⁻¹ * N3 * T * G) := by
    positivity
  calc ((64 / 9) * A * Ct * Cdc * CY1) * ((R * R)⁻¹ * N3 * T * G) * S1 ^ 12 ≤
      ((64 / 9) * A * Ct * Cdc * CY1) * ((R * R)⁻¹ * N3 * T * G) * S1 ^ 15 :=
      mul_le_mul_of_nonneg_left hpow hbase
    _ = _ := by ring

theorem aux_icc_collapse_term2
    {A cs sgi Ct p9 pinv q3 t3 Dv Cdc CY1 R S1 N3 T G : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hCdc : 0 ≤ Cdc) (hCY1 : 0 ≤ CY1)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hp9 : p9 ≤ 32 * S1 ^ 9)
    (hpinv : pinv = 2 * S1 ^ 2)
    (hq30 : 0 ≤ q3) (hq3 : q3 ≤ CY1)
    (ht30 : 0 ≤ t3) (ht3 : t3 ≤ T)
    (hDv : Dv = Cdc * S1 * G) :
    A * cs * sgi * (Ct * p9 * pinv * q3 * t3 * Dv) ≤
      ((64 / 9) * A * Ct * Cdc * CY1) * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by exact SubdiffusiveProcess.InteriorComparisonCollapse.aux_dedup_d065_aux_icc_collapse_term2 (A := A) (cs := cs) (sgi := sgi) (Ct := Ct) (p9 := p9) (pinv := pinv) (q3 := q3) (t3 := t3) (Dv := Dv) (Cdc := Cdc) (CY1 := CY1) (R := R) (S1 := S1) (N3 := N3) (T := T) (G := G) (hA := hA) (hCt := hCt) (hCdc := hCdc) (hCY1 := hCY1) (hR := hR) (hS1 := hS1) (hN3 := hN3) (hT := hT) (hG := hG) (hcs := hcs) (hsgi := hsgi) (hp9 := hp9) (hpinv := hpinv) (hq30 := hq30) (hq3 := hq3) (ht30 := ht30) (ht3 := ht3) (hDv := hDv)

/-- Direct forcing comparison to the unit harmonic function: one explicit
datum-price `S1`, absorbed into `S1¹⁵`. -/
theorem aux_dedup_d089_aux_icc_collapse_term3
    {UD cs dd sgi SC Bv CB R S1 N3 T G : ℝ}
    (hUD : 0 ≤ UD) (hdd : 0 ≤ dd) (hSC : 0 ≤ SC) (hCB : 0 ≤ CB)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hBv : Bv ≤ CB * T * S1 * G) :
    UD * cs * dd * sgi * (SC * Bv) ≤
      ((1 / 9) * UD * dd * SC * CB) * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  have hS10 : (0 : ℝ) ≤ S1 := le_trans zero_le_one hS1
  subst hcs hsgi
  have hstep : UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * Bv) ≤
      UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * (CB * T * S1 * G)) := by
    have hbase : 0 ≤ UD * (N3 / 9) * dd * (R * R)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hBv hSC) hbase
  refine hstep.trans ?_
  have heq : UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * (CB * T * S1 * G)) =
      ((1 / 9) * UD * dd * SC * CB) * ((R * R)⁻¹ * N3 * T * G) * S1 := by
    field_simp
  rw [heq]
  have hpow : S1 ≤ S1 ^ 15 := by
    simpa using pow_le_pow_right₀ hS1 (show 1 ≤ 15 by norm_num)
  have hbase : 0 ≤ ((1 / 9) * UD * dd * SC * CB) * ((R * R)⁻¹ * N3 * T * G) := by
    positivity
  calc ((1 / 9) * UD * dd * SC * CB) * ((R * R)⁻¹ * N3 * T * G) * S1 ≤
      ((1 / 9) * UD * dd * SC * CB) * ((R * R)⁻¹ * N3 * T * G) * S1 ^ 15 :=
      mul_le_mul_of_nonneg_left hpow hbase
    _ = _ := by ring

theorem aux_icc_collapse_term3
    {UD cs dd sgi SC Bv CB R S1 N3 T G : ℝ}
    (hUD : 0 ≤ UD) (hdd : 0 ≤ dd) (hSC : 0 ≤ SC) (hCB : 0 ≤ CB)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (hBv : Bv ≤ CB * T * S1 * G) :
    UD * cs * dd * sgi * (SC * Bv) ≤
      ((1 / 9) * UD * dd * SC * CB) * S1 ^ 15 * (R * R)⁻¹ * N3 * T * G := by exact SubdiffusiveProcess.InteriorComparisonCollapse.aux_dedup_d089_aux_icc_collapse_term3 (UD := UD) (cs := cs) (dd := dd) (sgi := sgi) (SC := SC) (Bv := Bv) (CB := CB) (R := R) (S1 := S1) (N3 := N3) (T := T) (G := G) (hUD := hUD) (hdd := hdd) (hSC := hSC) (hCB := hCB) (hR := hR) (hS1 := hS1) (hN3 := hN3) (hT := hT) (hG := hG) (hcs := hcs) (hsgi := hsgi) (hBv := hBv)

/-! ### The K-free collapse of the loop carrier -/

/-- Oscillation-leg constant (chosen before any model data). -/
noncomputable def aux_icc_constX (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    (Kslot : ℝ) : ℝ :=
  4 * (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
    Cloop.toReal * Real.sqrt (192 * (d : ℝ)) * Real.sqrt Kslot

/-- Force-leg constant (chosen before any model data). -/
noncomputable def aux_icc_constF (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    (Kslot Cdslot Cerr Cb : ℝ) : ℝ :=
  aux_icc_constX d Cloop Kslot * Cerr +
    (64 / 9) * (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
      Cloop.toReal * Cdslot * (1 + 9 * (Real.sqrt (192 * (d : ℝ)) * 3 * Cerr) ^ 2) +
    (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
      Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb

theorem aux_icc_constX_nonneg (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    (Kslot : ℝ) : 0 ≤ aux_icc_constX d Cloop Kslot := by
  unfold aux_icc_constX
  positivity

theorem aux_icc_constF_nonneg (d : ℕ) [NeZero d] (Cloop : ℝ≥0∞)
    {Kslot Cdslot Cerr Cb : ℝ} (hCdslot : 0 ≤ Cdslot) (hCerr : 0 ≤ Cerr)
    (hCb : 0 ≤ Cb) :
    0 ≤ aux_icc_constF d Cloop Kslot Cdslot Cerr Cb := by
  have hX := aux_icc_constX_nonneg d Cloop Kslot
  have hUD : 0 ≤ unitDirichletPoincareConst d := unitDirichletPoincareConst_nonneg d
  unfold aux_icc_constF
  positivity

/-- **The K-free collapse.**  The smooth loop carrier with the interior
energy, datum and Besov slots collapses onto `s^(-3/2)` (oscillation) and
`s^(-15/2)` (force).  Pure real arithmetic on the corridor `0 < s ≤ 1/4`. -/
theorem aux_icc_loopBound_le
    {d : ℕ} [NeZero d] (Cloop : ℝ≥0∞) {Kslot Cdslot Cerr Cb : ℝ}
    (hKslot : 0 < Kslot) (hCdslot : 0 < Cdslot) (hCb : 0 < Cb)
    (n : ℕ) {s sigma Er Wq Gq : ℝ} (hs0 : 0 < s) (hs4 : s ≤ 1 / 4)
    (hsigma : 0 < sigma) (hEr0 : 0 ≤ Er) (hErC : Er ≤ Cerr)
    (hWq0 : 0 ≤ Wq) (hGq0 : 0 ≤ Gq)
    (smid s1 s2 : FractionalOrder) (hsmid : smid.1 = s / 2) (hs1 : s1.1 = s / 3)
    (hs2 : s2.1 = s)
    (Q : TriadicCube d) (g : Vec d → Vec d)
    (hBv : scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g ≤
      Cb * (3 : ℝ) ^ (s * (n : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Gq) :
    flatComparatorSmoothGoodEventLoopBound Cloop d n sigma smid s1 s2
        (Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er))
        (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
          Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
            Real.rpow s (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2)))
        (Cdslot * Real.rpow s (-(1 / 2 : ℝ)) * Gq) Q g ≤
      aux_icc_constX d Cloop Kslot * s ^ (-3 / 2 : ℝ) * Er * Wq +
        aux_icc_constF d Cloop Kslot Cdslot Cerr Cb * s ^ (-15 / 2 : ℝ) *
          sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by
  obtain ⟨sm, hsm⟩ := smid
  obtain ⟨t1, ht1⟩ := s1
  obtain ⟨t2, ht2⟩ := s2
  dsimp only at hsmid hs1 hs2
  subst sm t1 t2
  have hCerr0 : 0 ≤ Cerr := hEr0.trans hErC
  -- the three slots
  set V : ℝ := Real.sqrt (192 * (d : ℝ)) with hVdef
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Sfull : ℝ := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
    Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
      Real.rpow s (-12 : ℝ) * sigma⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2))
    with hSfulldef
  set Dfull : ℝ := Cdslot * Real.rpow s (-(1 / 2 : ℝ)) * Gq with hDfulldef
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hEr0' := hEr0
  have hE0 : 0 ≤ Efull := by rw [hEfulldef]; positivity
  have hSv0 : 0 ≤ Sfull := by
    rw [hSfulldef]
    exact mul_nonneg (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      (Real.sqrt_nonneg _)
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
  set SK : ℝ := Real.sqrt Kslot with hSKdef
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hCt0 : 0 ≤ Ct := ENNReal.toReal_nonneg
  have hSK0 : 0 ≤ SK := Real.sqrt_nonneg _
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
  have hS24 : S1 ^ 24 = s ^ (-12 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 24]
    congr 1
    norm_num
  have hRRinv : (R * R)⁻¹ = sigma⁻¹ := by rw [hRR]
  have hpow1 : (3 : ℝ) ^ (-(2 * (n : ℤ))) = (N3 * N3)⁻¹ := by
    rw [hN3def, zpow_neg,
      show (2 * (n : ℤ)) = ((n : ℕ) : ℤ) + ((n : ℕ) : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
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
  -- the parent-energy slot
  have ha0 : (0 : ℝ) ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 :=
    mul_nonneg (mul_nonneg hsigma.le (zpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hb0 : (0 : ℝ) ≤ Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hsqa : Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2) =
      R * N3⁻¹ * Wq := by
    have hid : sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 = (R * N3⁻¹ * Wq) ^ 2 := by
      rw [hpow1, ← hRR]
      field_simp
    rw [hid, Real.sqrt_sq (by positivity)]
  have hsqb : Real.sqrt (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2) = S1 ^ 12 * R⁻¹ * T * Gq := by
    have hT2 : T ^ 2 = Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
      rw [hTdef, ← Real.rpow_natCast ((3 : ℝ) ^ (s * (n : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      change (3 : ℝ) ^ (s * (n : ℝ) * ((2 : ℕ) : ℝ)) = (3 : ℝ) ^ (2 * s * (n : ℝ))
      congr 1
      push_cast
      ring
    have hRinv2 : (R⁻¹) ^ 2 = sigma⁻¹ := by
      rw [← hRR]
      field_simp
    have hid : Real.rpow s (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2 =
        (S1 ^ 12 * R⁻¹ * T * Gq) ^ 2 := by
      rw [← hT2, ← hRinv2]
      change s ^ (-12 : ℝ) * (R⁻¹) ^ 2 * T ^ 2 * Gq ^ 2 = _
      rw [← hS24]
      ring
    rw [hid, Real.sqrt_sq (by positivity)]
  have hSv : Sfull ≤ 2 * S1 * SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by
    have hsum : Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
        Real.rpow s (-12 : ℝ) * sigma⁻¹ * Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) *
          Gq ^ 2)) ≤
        SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by
      rw [Real.sqrt_mul hKslot.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      calc Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
              Real.rpow s (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2) ≤
            Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2) +
              Real.sqrt (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2) :=
            sqrt_add_le_add_sqrt' ha0 hb0
        _ = R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq := by rw [hsqa, hsqb]
    have hdw := dirichletWeightedEnergyFactor_third_half_le hs0 hs4
    rw [hSfulldef]
    calc Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
          Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
            Real.rpow s (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * Gq ^ 2)) ≤
          (2 * S1) * (SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq)) :=
        mul_le_mul hdw hsum (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * S1 * SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by ring
  -- the three legs
  have h1 := aux_icc_collapse_term1 (A := A) (cs := centeredCubeScale ((n : ℤ) - 2))
    (sgi := sigma⁻¹) (Ct := Ct) (p2 := (s / 2)⁻¹) (R := R) (e3 := (3 : ℝ) ^ (s / 3))
    (E := Efull) (Sv := Sfull) (V := V) (Er := Er) (SK := SK) (S1 := S1) (N3 := N3)
    (T := T) (W := Wq) (G := Gq) (Cerr := Cerr)
    hA0 hCt0 hV0 hSK0 hR hS10 hN3 hT0 hEr0 hGq0 hErC
    hcsA hRRinv.symm hp2 he3 hE0 hEB hSv0 hSv
  have h2 := aux_icc_collapse_term2 (A := A) (cs := centeredCubeScale ((n : ℤ) - 2))
    (sgi := sigma⁻¹) (Ct := Ct) (p9 := (s / 2) ^ (-(9 / 2 : ℝ)))
    (pinv := (s - s / 2)⁻¹) (q3 := 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2)
    (t3 := (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ))) (Dv := Dfull) (Cdc := Cdslot)
    (CY1 := 1 + 9 * (V * 3 * Cerr) ^ 2) (R := R) (S1 := S1) (N3 := N3) (T := T)
    (G := Gq)
    hA0 hCt0 hCdslot.le (by positivity) hR hS11 hN3 hT0 hGq0
    hcsA hRRinv.symm hp9 hpinv hq30 hq3 ht30 ht3 rfl
  have h3 := aux_icc_collapse_term3 (UD := unitDirichletPoincareConst d)
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
  have hS15 : S1 ^ 15 = s ^ (-15 / 2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 15]
    congr 1
  have hN3T : N3 * T = (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := by
    rw [hN3def, hTdef, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hX : aux_icc_constX d Cloop Kslot = 4 * A * Ct * V * SK := rfl
  have hF : aux_icc_constF d Cloop Kslot Cdslot Cerr Cb =
      (4 * A * Ct * V * SK) * Cerr + (64 / 9) * A * Ct * Cdslot *
        (1 + 9 * (V * 3 * Cerr) ^ 2) +
      (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
        Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb := rfl
  rw [hRRinv] at h1 h2 h3
  have hRHS : (4 * A * Ct * V * SK) * S1 ^ 3 * Er * Wq +
      ((4 * A * Ct * V * SK) * Cerr + (64 / 9) * A * Ct * Cdslot *
          (1 + 9 * (V * 3 * Cerr) ^ 2) +
        (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb) * S1 ^ 15 * sigma⁻¹ * (N3 * T) * Gq =
      aux_icc_constX d Cloop Kslot * s ^ (-3 / 2 : ℝ) * Er * Wq +
        aux_icc_constF d Cloop Kslot Cdslot Cerr Cb * s ^ (-15 / 2 : ℝ) *
          sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by
    rw [hX, hF, hS3, hS15, hN3T]
  have hkey : A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
        (Ct * (s / 2)⁻¹ * R * (3 : ℝ) ^ (s / 3) * Efull * Sfull +
          Ct * (s / 2) ^ (-(9 / 2 : ℝ)) * (s - s / 2)⁻¹ *
            (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
            (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull) +
      unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g) ≤
      (4 * A * Ct * V * SK) * S1 ^ 3 * Er * Wq +
        ((4 * A * Ct * V * SK) * Cerr + (64 / 9) * A * Ct * Cdslot *
            (1 + 9 * (V * 3 * Cerr) ^ 2) +
          (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
            Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb) * S1 ^ 15 * sigma⁻¹ *
          (N3 * T) * Gq := by
    rw [mul_add]
    refine le_trans (add_le_add (add_le_add h1 h2) h3) (le_of_eq ?_)
    ring
  exact le_trans hkey (le_of_eq hRHS)

/-! ### The window shrink -/

/-- The inner window `x + 𝔠_{n-4}` costs at most `9^d` against the
comparison cube `y + 𝔠_{n-2}`. -/
theorem aux_dedup_d069_aux_icc_windowShrink {d : ℕ} [NeZero d] {m n : ℕ} (hnm : n + 5 ≤ m)
    {x y : Vec d} (hxDomain : x ∈ cube d (m : ℤ))
    {uD v : H1Function (translatedCube d ((n : ℤ) - 2) y)} {u : Vec d → ℝ}
    (hfval : ∀ q, uD.toFun q = u q)
    (hcov : truncatedCube d (m : ℤ) ((n : ℤ) - 4) x ⊆
      translatedCube d ((n : ℤ) - 2) y) :
    normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun q ↦ u q - v.toFun q) ≤
      (9 : ℝ) ^ d * normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
        (fun q ↦ u q - v.toFun q) := by
  have hvolW : (volume (translatedCube d ((n : ℤ) - 2) y)).toReal =
      ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    simp only [originCube]
  have hWpos : 0 < (volume (translatedCube d ((n : ℤ) - 2) y)).toReal := by
    rw [hvolW]; positivity
  have hVpos : 0 < (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hshrink := Section6HarmonicApproximation.normalizedL2On_sub_physical_le_of_subset
    (uD := uD) (v := v) (u := u) hfval hcov hWpos hVpos
  have hratio : (volume (translatedCube d ((n : ℤ) - 2) y)).toReal /
      (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal ≤ (81 : ℝ) ^ d := by
    have hlow :=
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hxDomain
        (show (n : ℤ) - 4 - 1 ≤ (m : ℤ) by omega)).1
    have hlowpos : (0 : ℝ) < ((3 : ℝ) ^ ((n : ℤ) - 4 - 2)) ^ d := by positivity
    have hquot : ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d /
        ((3 : ℝ) ^ ((n : ℤ) - 4 - 2)) ^ d = (81 : ℝ) ^ d := by
      rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
        show (n : ℤ) - 2 - ((n : ℤ) - 4 - 2) = 4 by ring]
      norm_num
    rw [hvolW, ← hquot]
    exact div_le_div_of_nonneg_left (by positivity) hlowpos hlow
  have hratio9 : Real.sqrt ((volume (translatedCube d ((n : ℤ) - 2) y)).toReal /
      (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal) ≤ (9 : ℝ) ^ d := by
    have h81 : ((9 : ℝ) ^ d) ^ 2 = (81 : ℝ) ^ d := by
      rw [← pow_mul, show d * 2 = 2 * d by ring, pow_mul]
      norm_num
    have hq := Real.sqrt_le_sqrt hratio
    rwa [← h81, Real.sqrt_sq (by positivity)] at hq
  exact hshrink.trans (mul_le_mul_of_nonneg_right hratio9
    (Section6Iteration.normalizedL2On_nonneg _ _))

theorem aux_icc_windowShrink {d : ℕ} [NeZero d] {m n : ℕ} (hnm : n + 5 ≤ m)
    {x y : Vec d} (hxDomain : x ∈ cube d (m : ℤ))
    {uD v : H1Function (translatedCube d ((n : ℤ) - 2) y)} {u : Vec d → ℝ}
    (hfval : ∀ q, uD.toFun q = u q)
    (hcov : truncatedCube d (m : ℤ) ((n : ℤ) - 4) x ⊆
      translatedCube d ((n : ℤ) - 2) y) :
    normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun q ↦ u q - v.toFun q) ≤
      (9 : ℝ) ^ d * normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
        (fun q ↦ u q - v.toFun q) := by exact SubdiffusiveProcess.InteriorComparisonCollapse.aux_dedup_d069_aux_icc_windowShrink (d := d) (m := m) (n := n) (hnm := hnm) (x := x) (y := y) (hxDomain := hxDomain) (uD := uD) (v := v) (u := u) (hfval := hfval) (hcov := hcov)

end

end SubdiffusiveProcess.InteriorComparisonCollapse
