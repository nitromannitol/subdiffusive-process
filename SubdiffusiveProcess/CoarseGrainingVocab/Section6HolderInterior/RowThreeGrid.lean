import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.IterationAppliedGate
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeCoefficients
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingRowsRaised

/-!
# Row 3's long branch: the grid-centred excess estimate

`interiorStepSeven_of_short_and_scaledGrid` reduces frozen row 3 to two
hypotheses.  `RowThreeShort.interiorRowThree_short` discharges `hshort`; this
module discharges `hgrid`, the grid-centred estimate at windows `(n+1, ell-1)`.

The chain is the excess conjunct of
`exists_interiorHolderIterationAppliedGate` at base `n + 1` and top `ell - 1`,
with

* the stopping rows raised from base `n` to base `n + 1`
  (`StoppingRowsRaised.stopping_rows_raised`, rate `2 * lambda`);
* the gate supplied by `WindowMonotone.interiorGate_of_descendant`, since the
  grid centre `z` is a descendant of the frozen base point `x` at scale `n + 1`
  (this is what the containment hypothesis `U_{m,n}(x) ⊆ U_{m,n+1}(z)` gives);
* the ratio row from `RowOneInstantiation.stoppedRatio_row`;
* the recurrence row bounded uniformly by `Keps * epsilon`
  (`IterationEpsilonBound.holderIterationEpsilon_le_const`);
* the three coefficient comparisons of `RowThreeCoefficients`.

Every constant here is **absolute**: row 3 carries the short-window hypothesis
`m - n ≤ (1 - alpha)⁻¹`, so `lambda * (m - n) ≤ C₁⁻¹ ≤ 1` and there is no
gap-uniformity work to do (Addendum 27).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Two geometric facts -/

/-- The centred cubes are symmetric about the origin. -/
theorem neg_mem_cube {j : ℤ} {p : Vec d} (hp : p ∈ cube d j) : -p ∈ cube d j := by
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp ⊢
  intro i
  have h := hp i
  simp only [Pi.neg_apply]
  constructor <;> linarith [h.1, h.2]

/-- Membership in a truncated window is symmetric in centre and point. -/
theorem mem_truncatedCube_symm {m j : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedCube d m j z) (hz : z ∈ cube d m) :
    z ∈ truncatedCube d m j x := by
  refine ⟨?_, hz⟩
  rw [mem_translatedCube_iff]
  have hsub : x - z ∈ cube d j :=
    mem_translatedCube_iff.mp (truncatedCube_subset_translatedCube d m j z hx)
  have := neg_mem_cube hsub
  simpa [neg_sub] using this

/-! ### The prefactor bound -/

/-- The iteration's prefactor is bounded by an absolute constant once the bad
count and the exponent are. -/
theorem rowThree_prefactor_le {theta Citer kR card A Abound cardBound : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) (hCiter : 0 ≤ Citer)
    (hkR : 0 ≤ kR) (hcard : card ≤ cardBound) (hA : A ≤ Abound) :
    theta ^ (-Citer * kR * card) * Real.exp A ≤
      theta ^ (-Citer * kR * cardBound) * Real.exp Abound := by
  have hmono : theta ^ (-Citer * kR * card) ≤ theta ^ (-Citer * kR * cardBound) := by
    refine Real.rpow_le_rpow_of_exponent_ge htheta0 htheta1 ?_
    have hc : 0 ≤ Citer * kR := mul_nonneg hCiter hkR
    nlinarith [hc, hcard]
  have hexp : Real.exp A ≤ Real.exp Abound := Real.exp_le_exp.mpr hA
  exact mul_le_mul hmono hexp (Real.exp_pos _).le
    (Real.rpow_nonneg htheta0.le _)


/-! ### The grid core, over abstract reals -/

/-- **Row 3's long branch as arithmetic.**  The iteration's excess row, with the
prefactor and the three coefficients bounded, is the `hgrid` inequality. -/
theorem interiorRowThree_gridCore
    {exN1 P Cpre thetaGap R Keps C2 alpha Kforce exponential
      exTop oscTop D tailInv seminorm outer oscf Crow : ℝ} {n ell : ℕ}
    (hchain : exN1 ≤ P * (thetaGap * exTop +
      R * (3 : ℝ) ^ (-((ell : ℝ) - 1)) * oscTop + (1 + R) * D))
    (hP : P ≤ Cpre) (hCpre : 0 ≤ Cpre)
    (hthetaGap : thetaGap = ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (ell - n - 2))
    (hell : n + 2 ≤ ell)
    (hR : R = Keps * (C2⁻¹ * Real.sqrt (1 - alpha)))
    (hKeps0 : 0 ≤ Keps) (hC2 : 1 ≤ C2)
    (halpha1 : 1 - alpha ≤ 1)
    (houter : 0 < outer) (hoscf : 0 < oscf)
    (htail : 0 ≤ tailInv) (hsem : 0 ≤ seminorm) (hD0 : 0 ≤ D)
    (hD : D ≤ 5 / 2 * Kforce * exponential * tailInv *
      ((3 : ℝ) ^ (((ell : ℝ) - 1) / 2) * seminorm))
    (hexTop : 0 ≤ exTop) (hoscTop : 0 ≤ oscTop)
    (hc1 : Cpre * (3 : ℝ) ^ ((1 : ℝ) / 2) * outer ^ 2 ≤ Crow)
    (hc2 : Cpre * Keps * C2⁻¹ * 3 * (outer * oscf) ≤ Crow)
    (hc3 : Cpre * (1 + Keps) * (5 / 2 * Kforce * exponential) *
      (3 : ℝ) ^ (-(1 : ℝ) / 2) * outer ≤ Crow) :
    exN1 ≤
      (interiorStepSevenFirstCoefficient Crow n ell / outer ^ 2) * exTop +
        (Crow * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) /
          (outer * oscf)) * oscTop +
        Crow * tailInv * (3 : ℝ) ^ ((ell : ℝ) / 2) * seminorm / outer := by
  have hC2inv : (0 : ℝ) ≤ C2⁻¹ := inv_nonneg.mpr (by linarith only [hC2])
  have hC2inv1 : C2⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith only [hC2])]; exact hC2
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt (1 - alpha) ≤ 1 := by
    have h2 := Real.sqrt_le_sqrt halpha1
    simpa using h2
  have hR0 : 0 ≤ R := by
    rw [hR]; exact mul_nonneg hKeps0 (mul_nonneg hC2inv hsqrt0)
  have hRmax : R ≤ Keps := by
    rw [hR]
    have : C2⁻¹ * Real.sqrt (1 - alpha) ≤ 1 := by nlinarith only
      [hC2inv, hC2inv1, hsqrt0, hsqrt1]
    calc Keps * (C2⁻¹ * Real.sqrt (1 - alpha)) ≤ Keps * 1 :=
          mul_le_mul_of_nonneg_left this hKeps0
      _ = Keps := by ring
  refine interiorRowThree_shapeMatch (top := (ell : ℝ) - 1) hchain ?_ ?_ ?_
    hexTop hoscTop
  · rw [hthetaGap]
    exact rowThree_firstCoeff_le hP hCpre
      (Real.rpow_nonneg (by norm_num) _)
      (le_of_eq (by norm_num)) houter hell hc1
  · exact rowThree_oscCoeff_le hP hCpre hR0 (le_of_eq hR) houter hoscf hc2
  · exact rowThree_defectCoeff_le hP hCpre hR0 hRmax htail hsem houter hD0 hD hc3


/-! ### The grid-centred excess estimate -/

/-- **Row 3's `hgrid`, discharged.**  The excess conjunct of the gated iteration
at base `n + 1` and top `ell - 1`, recombined into the shape
`interiorStepSeven_of_short_and_scaledGrid` consumes. -/
theorem exists_interiorRowThreeGrid (d : ℕ) [NeZero d] (step : ℕ)
    (hExcess : InteriorHolderExcessDecayInput d) :
    ∃ C2 Cmin : ℝ, 1 ≤ C2 ∧ 0 ≤ Cmin ∧
      ∀ C1 : ℝ, 1 ≤ C1 → ∀ Crow : ℝ, Cmin ≤ Crow →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
          Section6Stopping.holderStoppingLambda C1 alpha →
        Section6Stopping.holderStoppingLambda C1 alpha < 1 →
      ∀ L m : ℕ, m ≤ L →
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
          (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
      ∀ n : ℕ,
        (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → n + 2 < ell →
      ∀ x ∈ cube d ((m : ℤ) - 1), ∀ z : Vec d, OnTriadicGrid n z →
      z ∈ cube d m →
      truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
      truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
        excess (n + 1) (truncatedCube d m (n + 1) z) u.toFun ≤
          (interiorStepSevenFirstCoefficient Crow n ell /
              holderOffGridOuterFactor d ^ 2) *
            excess ((ell : ℤ) - 1)
              (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun +
          (interiorStepSevenOscillationCoefficient Crow alpha ell /
              (holderOffGridOuterFactor d *
                holderOffGridOscillationFactor d)) *
            normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
              (fun y ↦ u.toFun y -
                averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun) +
          interiorStepSevenRemainder M Crow L ω m ell g /
            holderOffGridOuterFactor d := by
  classical
  obtain ⟨Cstep, K, Citer, hCstep, hK, hCiter, hiter⟩ :=
    exists_interiorHolderIterationAppliedGate d hExcess
  obtain ⟨k, C2, hk, hC2, hth⟩ :=
    Section6Holder.exists_holderContractionParameters d Cstep hCstep
  obtain ⟨hthetaIoo, hthetak, hcontract⟩ := hth
  set theta : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hthetaDef
  set Keps : ℝ := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K with hKepsDef
  set Kforce : ℝ := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
    Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
    with hKforceDef
  have hKeps0 : 0 ≤ Keps := by rw [hKepsDef]; positivity
  have hKforce0 : 0 ≤ Kforce := by
    have := Section6ExcessDecay.fractionalHolderConst_nonneg d
    rw [hKforceDef]; positivity
  set outer : ℝ := holderOffGridOuterFactor d with houterDef
  set oscf : ℝ := holderOffGridOscillationFactor d with hoscfDef
  have houter : 0 < outer := holderOffGridOuterFactor_pos d
  have hoscf : 0 < oscf := holderOffGridOscillationFactor_pos d
  set Emax : ℝ := Real.exp (ratioRate d) with hEmaxDef
  set Abound : ℝ := Citer * ((k : ℝ) + 1) * ((k : ℝ) + 4) + Citer * (6 * Keps)
    with hAboundDef
  set Cpre : ℝ := theta ^ (-Citer * ((k : ℝ) + 1) * ((k : ℝ) + 4)) *
    Real.exp Abound with hCpreDef
  have htheta0 : (0 : ℝ) < theta := hthetaIoo.1
  have hCpre0 : 0 ≤ Cpre := by
    rw [hCpreDef]
    exact mul_nonneg (Real.rpow_nonneg htheta0.le _) (Real.exp_pos _).le
  set Cmin : ℝ :=
    Cpre * (3 : ℝ) ^ ((1 : ℝ) / 2) * outer ^ 2 +
      (Cpre * Keps * C2⁻¹ * 3 * (outer * oscf) +
        Cpre * (1 + Keps) * (5 / 2 * Kforce * Emax) *
          (3 : ℝ) ^ (-(1 : ℝ) / 2) * outer) with hCminDef
  have hC2pos : (0 : ℝ) < C2 := lt_of_lt_of_le zero_lt_one hC2
  have hEmax0 : (0 : ℝ) ≤ Emax := (Real.exp_pos _).le
  have hrp1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hrp2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hC2inv : (0 : ℝ) ≤ C2⁻¹ := inv_nonneg.mpr (by linarith only [hC2])
  have hterm1 : 0 ≤ Cpre * (3 : ℝ) ^ ((1 : ℝ) / 2) * outer ^ 2 :=
    mul_nonneg (mul_nonneg hCpre0 hrp1) (sq_nonneg _)
  have hterm2 : 0 ≤ Cpre * Keps * C2⁻¹ * 3 * (outer * oscf) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCpre0 hKeps0) hC2inv)
      (by norm_num)) (mul_nonneg houter.le hoscf.le)
  have hterm3 : 0 ≤ Cpre * (1 + Keps) * (5 / 2 * Kforce * Emax) *
      (3 : ℝ) ^ (-(1 : ℝ) / 2) * outer :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCpre0
      (by linarith only [hKeps0]))
      (mul_nonneg (mul_nonneg (by norm_num) hKforce0) hEmax0)) hrp2) houter.le
  refine ⟨C2, Cmin, hC2,
    by rw [hCminDef]; linarith only [hterm1, hterm2, hterm3], ?_⟩
  intro C1 hC1 Crow hCmin M hsmall alpha halpha hepsIcc hdelta heps8 hlam1 L m hmL ω u g
    hsol hg n hstop hwindow ell hnell hellm hlong x hx z hzgrid hzcube hsubN
    hsubEll
  set lam : ℝ := Section6Stopping.holderStoppingLambda C1 alpha with hlamDef
  set eps : ℝ := Section6Stopping.holderStoppingEpsilon C2 alpha with hepsDef
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one hC1
  have hlam0 : 0 ≤ lam := by
    rw [hlamDef, Section6Stopping.holderStoppingLambda]
    have h1 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha.2]
    exact mul_nonneg (inv_nonneg.mpr hC1pos.le) h1
  have heps0 : 0 ≤ eps := by
    rw [hepsDef, Section6Stopping.holderStoppingEpsilon]
    exact mul_nonneg (inv_nonneg.mpr (by linarith only [hC2]))
      (Real.sqrt_nonneg _)
  have hepsC2 : eps ≤ C2⁻¹ := by
    rw [hepsDef, Section6Stopping.holderStoppingEpsilon]
    have hsq : Real.sqrt (1 - alpha) ≤ 1 := by
      have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha.1]
      have h2 := Real.sqrt_le_sqrt h1
      simpa using h2
    have hinv : (0 : ℝ) ≤ C2⁻¹ := inv_nonneg.mpr (by linarith only [hC2])
    calc C2⁻¹ * Real.sqrt (1 - alpha) ≤ C2⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsq hinv
      _ = C2⁻¹ := by ring
  -- basic scale facts
  have hnm5 : (n : ℤ) ≤ (m : ℤ) - 5 :=
    base_scale_le_of_stopping M alpha lam eps step m n ω hstop
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by omega
  have hnmRle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnmZ
  have hnmR : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := sub_nonneg.mpr hnmRle
  -- the short-window budget
  have hlamgap : lam * ((m : ℝ) - (n : ℝ)) ≤ 1 := by
    rcases eq_or_lt_of_le halpha.2 with heq | hlt
    · have : lam = 0 := by
        rw [hlamDef, Section6Stopping.holderStoppingLambda, ← heq]; ring
      rw [this]; simp
    · have hpos : (0 : ℝ) < 1 - alpha := by linarith only [hlt]
      have hkey : (1 - alpha) * ((m : ℝ) - (n : ℝ)) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hwindow hpos.le
        rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at h
      have hinv1 : C1⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hC1pos]; exact hC1
      have hlameq : lam = C1⁻¹ * (1 - alpha) := by
        rw [hlamDef, Section6Stopping.holderStoppingLambda]
      have hinv0 : (0 : ℝ) ≤ C1⁻¹ := inv_nonneg.mpr hC1pos.le
      have hprod0 : (0 : ℝ) ≤ (1 - alpha) * ((m : ℝ) - (n : ℝ)) :=
        mul_nonneg hpos.le hnmR
      rw [hlameq, mul_assoc]
      nlinarith only [hkey, hinv1, hinv0, hprod0]
  -- the interior gate at the grid centre
  have hxm : x ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hx
  have hxin : x ∈ truncatedCube d (m : ℤ) ((n : ℕ) + 1 : ℕ) z :=
    hsubN (mem_truncatedCube_self (n : ℤ) hxm)
  have hzin : z ∈ truncatedCube d (m : ℤ) (((n : ℕ) + 1 : ℕ) : ℤ) x :=
    mem_truncatedCube_symm hxin hzcube
  have hellZ : (ell : ℤ) + 5 ≤ (m : ℤ) := by exact_mod_cast hellm
  have hnlZ : (n : ℤ) + 2 < (ell : ℤ) := by exact_mod_cast hlong
  have hn1m5 : (((n : ℕ) + 1 : ℕ) : ℤ) ≤ (m : ℤ) - 5 := by
    push_cast
    omega
  have hgate : ∀ j : ℕ, j ≤ ell - 1 →
      ¬ BoundaryTouches (truncatedCube d (m : ℤ) (j : ℤ) z) (cube d (m : ℤ)) := by
    intro j hj
    refine interiorGate_of_descendant hx hzin hn1m5 ?_
    have hjZ : (j : ℤ) ≤ ((ell - 1 : ℕ) : ℤ) := by exact_mod_cast hj
    have hcast : ((ell - 1 : ℕ) : ℤ) = (ell : ℤ) - 1 := by
      have : 1 ≤ ell := by omega
      omega
    rw [hcast] at hjZ
    omega
  -- the stopping rows at the grid centre, raised to base `n + 1`
  obtain ⟨hctrlZ, _hctrl0⟩ :=
    stoppedControls_pair M C1 C2 alpha step m n ω hstop z hzgrid hzcube
  have hinfl : lam * ((m : ℝ) - (n : ℝ)) ≤
      (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ)) := by
    refine stopping_inflation_of_gap hlam0 (by omega) ?_
    have hnl : (n : ℝ) + 2 < (ell : ℝ) := by exact_mod_cast hlong
    have hlm : (ell : ℝ) + 5 ≤ (m : ℝ) := by exact_mod_cast hellm
    push_cast
    linarith
  obtain ⟨herrRaised, hfailRaised⟩ :=
    stopping_rows_raised M eps lam (2 * lam) n (n + 1) m z ω (by omega)
      hctrlZ.1 hctrlZ.2 hinfl
  -- the ratio row
  have hratio0 := stoppedRatio_row (L := L) M C1 C2 alpha step m n (ell - 1) ω
    (by omega) hmL (by omega) hlam0 hlam1 heps0 hdelta z hzcube hstop hzgrid
  have hratio : ∀ j ∈ Finset.Icc (n + 1) (ell - 1),
      tailCoefficientCubeAverage M L m ω /
          tailAverage M L (j + 2) ω (translatedCube d (j + 2 : ℕ) z) ≤ Emax := by
    intro j hj
    have hjmem : j ∈ Finset.Icc n (ell - 1) := by
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    refine (hratio0 j hjmem).trans ?_
    rw [hEmaxDef]
    refine Real.exp_le_exp.mpr ?_
    have hr0 := ratioRate_nonneg d
    have : ratioRate d * (lam * ((m : ℝ) - (n : ℝ))) ≤ ratioRate d * 1 :=
      mul_le_mul_of_nonneg_left hlamgap hr0
    calc ratioRate d * lam * ((m : ℝ) - (n : ℝ))
        = ratioRate d * (lam * ((m : ℝ) - (n : ℝ))) := by ring
      _ ≤ ratioRate d * 1 := this
      _ = ratioRate d := by ring
  -- the gated iteration at base `n + 1`, top `ell - 1`
  have hcontr := hcontract eps heps0 hepsC2
  have hlam'0 : (0 : ℝ) ≤ 2 * lam := by linarith only [hlam0]
  have hdelta' : M.delta ^ 2 ≤ 2 * lam := by linarith only [hdelta, hlam0]
  have heps8' : eps ^ 8 ≤ 2 * lam := by linarith only [heps8, hlam0]
  have hout := hiter M hsmall eps hepsIcc (2 * lam) hlam'0 hdelta' heps8'
    k hk theta hthetaIoo hthetak hcontr L m (n + 1) (ell - 1)
    (by omega) (by omega) hmL z hzcube hgate ω herrRaised hfailRaised
    Emax hEmax0 hratio u g hsol hg
  dsimp only at hout
  rw [← hKepsDef, ← hKforceDef,
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m ω] at hout
  set Kmean : ℝ := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) with hKmeanDef
  set Kboundary : ℝ := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
    (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) with hKboundaryDef
  set tailInv : ℝ := (tailAverage M L m ω (cube d (m : ℤ)))⁻¹ with htailInvDef
  set seminorm : ℝ := holderSeminormOn (cube d (m : ℤ)) (1 / 2) g with hseminormDef
  set topForcing : ℝ := tailInv * (3 : ℝ) ^ ((m : ℝ) / 2) * seminorm
    with htopForcingDef
  have htail0 : 0 ≤ tailInv := by
    rw [htailInvDef]
    exact inv_nonneg.mpr (tailAverage_nonneg _ _ _ _ _)
  have hsem0 : 0 ≤ seminorm := by
    rw [hseminormDef]; exact Section6ExcessDecay.holderSeminormOn_nonneg hg
  have hKmean0 : 0 ≤ Kmean := by rw [hKmeanDef]; positivity
  have hKboundary0 : 0 ≤ Kboundary := by rw [hKboundaryDef]; positivity
  have htopForcing0 : 0 ≤ topForcing := by
    rw [htopForcingDef]
    exact mul_nonneg (mul_nonneg htail0 (Real.rpow_nonneg (by norm_num) _)) hsem0
  -- the `R` row
  have hR0 : (0 : ℝ) ≤ Keps * eps := mul_nonneg hKeps0 heps0
  have hRb : ∀ j ∈ Finset.Icc ((n + 1 : ℕ) : ℤ) ((ell - 1 : ℕ) : ℤ),
      holderIterationEpsilon Keps M eps Section6Stopping.holderStoppingS z ω j ≤
        Keps * eps :=
    fun j _ ↦ holderIterationEpsilon_le_const M z ω j hKeps0 heps0
  have hexc := hout.2 (Keps * eps) hR0 hRb
  -- the exponent bound
  have hgapR : (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ)) ≤ 2 := by
    have hstep : (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ)) ≤
        2 * (lam * ((m : ℝ) - (n : ℝ))) := by
      push_cast
      nlinarith only [hlam0, hnmR]
    linarith only [hstep, hlamgap]
  have hgapR' : (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1) ≤ 2 := by
    have heq : ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1) = (m : ℝ) - (n : ℝ) := by
      push_cast; ring
    rw [heq]
    linarith only [hlamgap]
  have hAle := holderIterationExponent_le hKeps0 hCiter.le M m (n + 1) (ell - 1) k
    hlam'0 hdelta' heps8' z ω (by omega) (by omega) herrRaised hfailRaised
  dsimp only at hAle
  have hCiter0 : (0 : ℝ) ≤ Citer := hCiter.le
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hA : Citer * ((k : ℝ) + 1) *
        (((holderBadScales M eps Section6Stopping.holderStoppingS
          (n + 1) (ell - 1) k z ω).card : ℝ) + 1) +
      Citer * ∑ j ∈ Finset.Icc ((n + 1 : ℕ) : ℤ) ((ell - 1 : ℕ) : ℤ),
        holderIterationEpsilon Keps M eps Section6Stopping.holderStoppingS z ω j
      ≤ Abound := by
    refine hAle.trans ?_
    rw [hAboundDef]
    have h1 : Citer * ((k : ℝ) + 1) *
        ((k : ℝ) + 2 + (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ))) ≤
        Citer * ((k : ℝ) + 1) * ((k : ℝ) + 4) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCiter0 hk1)
      linarith only [hgapR]
    have h2 : Citer * (3 * Keps * (2 * lam) *
          ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1)) ≤ Citer * (6 * Keps) := by
      refine mul_le_mul_of_nonneg_left ?_ hCiter0
      have hkey : 3 * Keps * ((2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1)) ≤
          3 * Keps * 2 :=
        mul_le_mul_of_nonneg_left hgapR' (by linarith only [hKeps0])
      calc 3 * Keps * (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1)
          = 3 * Keps * ((2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ) + 1)) := by ring
        _ ≤ 3 * Keps * 2 := hkey
        _ = 6 * Keps := by ring
    linarith only [h1, h2]
  -- the bad-count bound
  have hfailShift := (sum_shiftTwo_goodFailure_le M eps
    Section6Stopping.holderStoppingS z ω
    (n := n + 1) (top := ell - 1) (domain := m) (by omega)).trans_lt hfailRaised
  have hcard0 := holderBadScales_card_lt_of_bound M eps
    Section6Stopping.holderStoppingS
    (1 + (2 * lam) * ((m : ℝ) - ((n + 1 : ℕ) : ℝ))) (n + 1) (ell - 1) k z ω
    hfailShift
  have hcard : (((holderBadScales M eps Section6Stopping.holderStoppingS
      (n + 1) (ell - 1) k z ω).card : ℝ) + 1) ≤ (k : ℝ) + 4 := by
    linarith only [hcard0, hgapR]
  -- the defect sum
  have hDbound := sum_holderIterationDefect_le
    (forcingConst := Kforce) (meanConst := Kmean) (boundaryConst := Kboundary)
    (exponential := Emax) (topForcing := topForcing) (hLinfty := 0)
    (topBoundary := 0) (K := Keps) (epsilon := eps)
    (s := Section6Stopping.holderStoppingS)
    (E := ∑ j ∈ Finset.Icc (n + 1) (ell - 1),
      holderRecurrenceEpsilon Keps M eps Section6Stopping.holderStoppingS j z ω)
    hKforce0 hKmean0 hKboundary0 hEmax0 htopForcing0 le_rfl le_rfl hKeps0 heps0
    M m (n + 1) (ell - 1) z ω (by omega) le_rfl
  simp only [mul_zero, zero_mul, add_zero] at hDbound
  -- collapse the two powers of `3`
  have hellR : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have h1 : 1 ≤ ell := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hpow : (3 : ℝ) ^ (-(((m : ℝ) - ((ell - 1 : ℕ) : ℝ)) / 2)) *
      (3 : ℝ) ^ ((m : ℝ) / 2) = (3 : ℝ) ^ (((ell : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hellR]
    congr 1
    ring
  have hD : (∑ j ∈ Finset.Icc ((n + 1 : ℕ) : ℤ) ((ell - 1 : ℕ) : ℤ),
      holderIterationDefect Kforce Kmean Kboundary Emax topForcing 0 0 Keps M eps
        Section6Stopping.holderStoppingS m z ω j) ≤
      5 / 2 * Kforce * Emax * tailInv *
        ((3 : ℝ) ^ (((ell : ℝ) - 1) / 2) * seminorm) := by
    refine hDbound.trans (le_of_eq ?_)
    rw [htopForcingDef]
    calc 5 / 2 * Kforce *
          (3 : ℝ) ^ (-(((m : ℝ) - ((ell - 1 : ℕ) : ℝ)) / 2)) * Emax *
          (tailInv * (3 : ℝ) ^ ((m : ℝ) / 2) * seminorm)
        = 5 / 2 * Kforce * Emax * tailInv *
          (((3 : ℝ) ^ (-(((m : ℝ) - ((ell - 1 : ℕ) : ℝ)) / 2)) *
            (3 : ℝ) ^ ((m : ℝ) / 2)) * seminorm) := by ring
      _ = 5 / 2 * Kforce * Emax * tailInv *
          ((3 : ℝ) ^ (((ell : ℝ) - 1) / 2) * seminorm) := by rw [hpow]
  have hD0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc ((n + 1 : ℕ) : ℤ) ((ell - 1 : ℕ) : ℤ),
      holderIterationDefect Kforce Kmean Kboundary Emax topForcing 0 0 Keps M eps
        Section6Stopping.holderStoppingS m z ω j := by
    refine Finset.sum_nonneg (fun j _ ↦ ?_)
    exact holderIterationDefect_nonneg hKforce0 hKmean0 hKboundary0 hEmax0
      htopForcing0 le_rfl le_rfl hKeps0 heps0 M m z ω j
  -- shape conversions inside the chain
  have hzcast : ((ell - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) =
      ((ell - n - 2 : ℕ) : ℤ) := by omega
  have hgapPow : theta ^ (((ell - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) =
      theta ^ (ell - n - 2) := by
    rw [hzcast, zpow_natCast]
  have hoscPow : (3 : ℝ) ^ (-((ell - 1 : ℕ) : ℤ)) =
      (3 : ℝ) ^ (-((ell : ℝ) - 1)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-((ell - 1 : ℕ) : ℤ))]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ ell)]
    ring
  rw [hgapPow, hoscPow] at hexc
  -- the goal in `ell - 1` form
  rw [show ((ell : ℤ) - 1) = ((ell - 1 : ℕ) : ℤ) by omega]
  have hthetaGap : theta ^ (ell - n - 2) =
      ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (ell - n - 2) := by rw [hthetaDef]
  refine interiorRowThree_gridCore (Cpre := Cpre) (Keps := Keps) (C2 := C2)
    (Kforce := Kforce) (exponential := Emax) (tailInv := tailInv)
    (seminorm := seminorm) (outer := outer) (oscf := oscf) (Crow := Crow)
    hexc ?_ hCpre0 hthetaGap (by omega) ?_ hKeps0 hC2 ?_ houter hoscf
    htail0 hsem0 hD0 hD ?_ ?_ ?_ ?_ ?_
  · -- the prefactor
    exact rowThree_prefactor_le htheta0 (le_of_lt hthetaIoo.2) hCiter0 hk1
      hcard hA
  · rw [hepsDef, Section6Stopping.holderStoppingEpsilon]
  · linarith only [halpha.1]
  · exact excess_nonneg _ _ _
  · exact Section6Iteration.normalizedL2On_nonneg _ _
  · rw [hCminDef] at hCmin; linarith only [hterm2, hterm3, hCmin]
  · rw [hCminDef] at hCmin; linarith only [hterm1, hterm3, hCmin]
  · rw [hCminDef] at hCmin; linarith only [hterm1, hterm2, hCmin]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
