module

public import SubdiffusiveProcess.Analysis.SmoothDualBoundaryKFree

@[expose] public section




open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Analysis

/-- Clause 1 of `product_threshold_regularities` with the threshold-6 cutoff event and
without the `τ²` premise (the two changes are the only differences; checked by script). -/
def aux_b12bd_ClauseSix (d : ℕ) [NeZero d] : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-3 / 2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-15 / 2 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)

end SubdiffusiveProcess.Analysis

section Proof

open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch

namespace SubdiffusiveProcess.Analysis

/-- Final constant bookkeeping of the collapse (pure real arithmetic): one constant
`D·(X + F + X·Cerr + 1)` dominates the four legs, and the boundary-gradient leg pays one
extra `S3 = s^(-3/2) ≥ 1`. -/
theorem aux_b12bd_final_le {D X F Cerr S3 S7 S15 Er Wq NAH sgi P Gq Hd Lhs : ℝ}
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hF : 0 ≤ F) (hCerr : 0 ≤ Cerr) (hS3 : 1 ≤ S3)
    (hS7 : 0 ≤ S7) (hS15 : 0 ≤ S15) (hEr : 0 ≤ Er) (hWq : 0 ≤ Wq) (hNAH : 0 ≤ NAH)
    (hsgi : 0 ≤ sgi) (hP : 0 ≤ P) (hGq : 0 ≤ Gq) (hHd : 0 ≤ Hd)
    (hmain : Lhs ≤ D * (X * S3 * Er * Wq + X * S3 * Er * NAH +
      F * S15 * sgi * P * Gq + X * Cerr * S7 * P * Hd)) :
    Lhs ≤ D * (X + F + X * Cerr + 1) * S3 * Er * (Wq + S3 * NAH) +
      D * (X + F + X * Cerr + 1) * S15 * sgi * P * Gq +
      D * (X + F + X * Cerr + 1) * S7 * P * Hd := by
  set K : ℝ := D * (X + F + X * Cerr + 1) with hKdef
  have hXC : 0 ≤ X * Cerr := mul_nonneg hX hCerr
  have hK1 : D * X ≤ K := mul_le_mul_of_nonneg_left (by linarith) hD
  have hK2 : D * F ≤ K := mul_le_mul_of_nonneg_left (by linarith) hD
  have hK3 : D * (X * Cerr) ≤ K := mul_le_mul_of_nonneg_left (by linarith) hD
  have hS30 : 0 ≤ S3 := le_trans zero_le_one hS3
  have hNAH' : NAH ≤ S3 * NAH := le_mul_of_one_le_left hNAH hS3
  have t1 : (D * X) * (S3 * Er * Wq) ≤ K * (S3 * Er * Wq) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have t2 : (D * X) * (S3 * Er * NAH) ≤ K * (S3 * Er * (S3 * NAH)) :=
    mul_le_mul hK1 (mul_le_mul_of_nonneg_left hNAH' (by positivity)) (by positivity)
      (le_trans (by positivity) hK1)
  have t3 : (D * F) * (S15 * sgi * P * Gq) ≤ K * (S15 * sgi * P * Gq) :=
    mul_le_mul_of_nonneg_right hK2 (by positivity)
  have t4 : (D * (X * Cerr)) * (S7 * P * Hd) ≤ K * (S7 * P * Hd) :=
    mul_le_mul_of_nonneg_right hK3 (by positivity)
  calc Lhs ≤ D * (X * S3 * Er * Wq + X * S3 * Er * NAH +
        F * S15 * sgi * P * Gq + X * Cerr * S7 * P * Hd) := hmain
    _ = (D * X) * (S3 * Er * Wq) + (D * X) * (S3 * Er * NAH) +
        (D * F) * (S15 * sgi * P * Gq) + (D * (X * Cerr)) * (S7 * P * Hd) := by ring
    _ ≤ K * (S3 * Er * Wq) + K * (S3 * Er * (S3 * NAH)) +
        K * (S15 * sgi * P * Gq) + K * (S7 * P * Hd) :=
      add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    _ = K * S3 * Er * (Wq + S3 * NAH) + K * S15 * sgi * P * Gq + K * S7 * P * Hd := by ring

/-- **The full harmonic-approximation clause on the threshold-6 cutoff event at the original
powers.**  Both regimes: the two `BoundaryTouches` legs come from the two boundary legs of
the proved upstream weighted-energy slot.  The constant is chosen before the model. -/
theorem aux_b12bd_boundaryClause_six (d : ℕ) [NeZero d] : aux_b12bd_ClauseSix d := by
  classical
  obtain ⟨Cbd, hCbd, hbrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryStepCellParentRow d
  obtain ⟨Crow, hCrow, hrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow
      d hCbd hbrow
  obtain ⟨Ck, hCk, hslot⟩ :=
    Section6CutoffHarmonic.exists_boundaryWeightedEnergySlot_of_cellRow d hCrow hrow
  obtain ⟨Cloop, Cdslot, _hCloopTop, hCdslot, hloop⟩ :=
    aux_b12bd_boundaryComparison_le_smoothLoopBound d
  obtain ⟨Cerr, hCerr, herr⟩ :=
    Section6HolderBelowCutoff.exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  obtain ⟨Cb, hCb, hbesov⟩ :=
    Section6HarmonicInterior.exists_interiorForceBesov_le_windowSeminorm d
  have hX0 := aux_b12bd_constX_nonneg d Cloop hCk.le
  have hF0 := aux_b12bd_constF_nonneg d Cloop hCk.le hCdslot.le hCerr.le hCb.le
  set X := aux_b12bd_constX d Cloop Ck with hXdef
  set F := aux_b12bd_constF d Cloop Ck Cdslot Cerr Cb with hFdef
  have hXC0 : 0 ≤ X * Cerr := mul_nonneg hX0 hCerr.le
  refine ⟨(9 : ℝ) ^ d * (X + F + X * Cerr + 1), by positivity, ?_⟩
  intro M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
    hfval hfgrad
  refine ⟨(Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).1,
    (Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).2, ?_⟩
  intro v hharm htrace
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s := (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hslt : s < 1 := by linarith
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hUdef
  set sigma : ℝ :=
    tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set Er : ℝ := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErdef
  set Wq : ℝ := normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) with hWqdef
  set Gq : ℝ := (fractionalSeminormOn U s g).toReal with hGqdef
  set AH : ℝ := if BoundaryTouches U (cube d (m : ℤ)) then
    Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0 with hAHdef
  set Hd : ℝ := if BoundaryTouches U (cube d (m : ℤ)) then
    (fractionalSeminormOn U s h.grad).toReal else 0 with hHddef
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z ω)
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hWq0 : 0 ≤ Wq := Section6Iteration.normalizedL2On_nonneg _ _
  have hGq0 : 0 ≤ Gq := ENNReal.toReal_nonneg
  have hAH0 : 0 ≤ AH := by rw [hAHdef]; split <;> positivity
  have hHd0 : 0 ≤ Hd := by
    rw [hHddef]
    split
    · exact ENNReal.toReal_nonneg
    · exact le_refl 0
  set K : ℝ := (9 : ℝ) ^ d * (X + F + X * Cerr + 1) with hKdef
  have hAHleg : (if BoundaryTouches U (cube d (m : ℤ)) then
      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
        Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) =
      s ^ (-3 / 2 : ℝ) * ((3 : ℝ) ^ n * AH) := by
    rw [hAHdef]
    split <;> ring
  have hHdleg : (if BoundaryTouches U (cube d (m : ℤ)) then
      K * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) *
        (fractionalSeminormOn U s h.grad).toReal else 0) =
      K * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Hd := by
    rw [hHddef]
    split <;> ring
  rw [hAHleg, hHdleg]
  have hS3 : (1 : ℝ) ≤ s ^ (-3 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 (by linarith) (by norm_num)
  have hP0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _
    (by
      have h7 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
      have h15 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
      have hsi : (0 : ℝ) ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
      have hS30 : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := le_trans zero_le_one hS3
      positivity) ?_
  intro hgood
  have hErC : Er ≤ Cerr := herr M s hs L (n + 2) ω z hgood
  obtain ⟨sOrder, hsval, hgWsp⟩ := hgex
  have hsO : sOrder = (⟨s, hs0, hslt⟩ : FractionalOrder) := Subtype.ext hsval
  rw [hsO] at hgWsp
  -- the weighted-energy slot, with the boundary datum leg in product form
  set Bq : ℝ := (3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Hd with hBqdef
  have hBeq : (3 : ℝ) ^ (-(n : ℤ)) * Wq + AH +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      (if BoundaryTouches U (cube d (m : ℤ)) then
        Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (fractionalSeminormOn U s h.grad).toReal else 0) = Bq := by
    rw [hBqdef, hHddef]
    split <;> simp
  set Sfull : ℝ :=
    Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
      (Real.sqrt sigma * (Ck * Bq)) with hSfulldef
  have hslotS : ∀ u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2))),
      (∀ p, u0.grad p = u.grad (p + y)) →
      weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
        ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
        ((aCutoffFamily M L (translatePotentialSample y ω)).coeffOn
          (originCube d ((n : ℤ) - 2))) u0
        (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
        (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
        FiniteLpExponent.two ≤ ENNReal.ofReal Sfull := by
    intro u0 hu0grad
    have hraw := hslot M (⟨s, hs0, hslt⟩ : FractionalOrder) hs L m n hnm z x y ω
      hz hx hloc hgood u h g hdir hgWsp hh u0 hu0grad
      (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
      (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
      (by dsimp only; linarith)
    dsimp only at hraw
    rw [hBeq] at hraw
    exact hraw
  -- the K-free loop
  have hL := hloop M s hs L m n hnm z x y ω hz hx hloc hgood u h g hdir
    hgWsp Sfull hslotS uD v hfval hharm htrace
  -- the Besov slot and the collapse
  have hBv := hbesov (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc g hgWsp
    (s / 2) (by dsimp only; linarith)
  have hC := aux_b12bd_loopBound_le Cloop hCk hCdslot hCb n hs0 hs4
    hsigma hEr0 hErC hWq0 hAH0 hGq0 hHd0
    (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s, hs0, hslt⟩ : FractionalOrder) rfl rfl rfl (originCube d ((n : ℤ) - 2))
    (fun p ↦ g (p + y)) hBv
  -- the window shrink
  have hshrink := Section6HolderBelowCutoff.SmoothDualScratch.aux_smoothInterior_windowShrink
    hnm hxDomain (uD := uD) (v := v) (u := u.toFun) hfval hcov
  have hmain := hshrink.trans
    (mul_le_mul_of_nonneg_left (hL.trans hC) (by positivity))
  exact aux_b12bd_final_le (by positivity) hX0 hF0 hCerr.le hS3
    (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hs0.le _) hEr0 hWq0
    (by positivity) (inv_nonneg.mpr hsigma.le) hP0 hGq0 hHd0 hmain

end SubdiffusiveProcess.Analysis

end Proof


