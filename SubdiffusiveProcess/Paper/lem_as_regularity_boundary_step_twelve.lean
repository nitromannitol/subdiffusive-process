module

public import SubdiffusiveProcess.Paper.obl_ramp_threshold12_transfer
public import SubdiffusiveProcess.Analysis.BoundaryExcessBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowSeminorms
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap

@[expose] public section

/-! Normalize the arbitrary-coefficient boundary comparison into the excess recurrence.
The error budget remains an explicit input; no stopping event is asserted here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Fractional forcing on a truncated cube is controlled by the top half-Holder seminorm. -/
theorem aux_lem_as_regularity_boundary_step_twelve_forcing {d : ℕ} (hd : 1 ≤ d)
    {m n : ℕ} {x : Vec d} (hx : x ∈ cube d m) {f : Vec d → Vec d}
    (hf : MemHolder (cube d m) (1 / 2) f) :
    (3 : ℝ) ^ ((1 / 4 : ℝ) * n) *
      (fractionalSeminormOn (truncatedCube d m n x) (1 / 4) f).toReal ≤
      (fractionalHolderConst d * Real.sqrt (1 / 4)) * (3 : ℝ) ^ ((n : ℝ) / 2) *
        holderSeminormOn (cube d m) (1 / 2) f := by
  have h := three_rpow_mul_fractionalSeminormOn_truncatedCube_le_holderSeminormOn
    (j := (n : ℤ)) hd hx (by norm_num : (0 : ℝ) < 1/4) le_rfl
    (memHolder_mono hf (truncatedCube_subset_cube d m n x))
  have hmono := Section6Holder.holderSeminormOn_mono (by norm_num : (0:ℝ)<1/2) hf
    (truncatedCube_subset_cube d m n x)
  simp only [Int.cast_natCast] at h
  have hCf := fractionalHolderConst_nonneg d
  exact h.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

/-- At a boundary window the cutoff field on the threshold-12 good event yields a standard excess
step with explicit forcing (the threshold-12 transfer `obl_ramp_threshold12_transfer`; no standing
input). -/
theorem lem_as_regularity_boundary_step_twelve (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 6 ≤ k → ∃ B : ℝ, 0 < B ∧
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 2048 * M.delta ^ 2 ≤ 1 →
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ ((1 / 4 : ℝ) / 8) * Real.log 3 / 16 →
    ∀ eta : ℝ, eta ∈ Icc (32 * M.delta ^ 2) 1 →
    ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
    ∀ x z : Vec d, x ∈ cube d m → z ∈ cube d m →
      x ∈ truncatedCube d m (n - 3) z →
    ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
    ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z eta (1 / 32) →
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
      (∃ sOrder : FractionalOrder, sOrder.1 = (1 / 4 : ℝ) ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      MemHolder (cube d m) (1 / 2) g →
      MemHolder (cube d m) (1 / 2) h.grad →
    ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
      excess ((n : ℤ) - k) (truncatedCube d m ((n : ℤ) - k) x) u.toFun ≤
        (A * (3 : ℝ) ^ (-(k : ℝ) / 2) + B * eta) *
          excess n (truncatedCube d m n x) u.toFun +
        B * section6HomogenizationError M (1 / 32) L (n + 2) ω z * Real.sqrt (vecNormSq ell.slope) +
        B * (section6HomogenizationError M (1 / 32) L (n + 2) ω z * vectorSupNormOn (cube d m) h.grad +
          (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ ((n : ℝ) / 2) *
            holderSeminormOn (cube d m) (1 / 2) g +
          (3 : ℝ) ^ ((n : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) h.grad) := by
  classical
  obtain ⟨A, hA, hstep⟩ := (obl_ramp_threshold12_transfer d).2.2.1
  refine ⟨A, hA, ?_⟩
  intro k hk
  let pk := (3:ℝ)^((1+(d:ℝ)/2)*k)
  let b1 := A*pk*(1/4:ℝ)^(-3/2:ℝ)
  let b3 := b1*(1/4:ℝ)^(-3/2:ℝ)
  let b4 := A*(1/4:ℝ)^(-15/2:ℝ)*pk*(fractionalHolderConst d*Real.sqrt (1/4))
  let b5 := A*(1/4:ℝ)^(-3:ℝ)*pk
  have hpk : 0 ≤ pk := Real.rpow_nonneg (by norm_num) _
  have hb1 : 0 ≤ b1 := by dsimp only [b1]; positivity
  have hb3 : 0 ≤ b3 := by dsimp only [b3]; positivity
  have hb4 : 0 ≤ b4 := by
    have hcf := fractionalHolderConst_nonneg d
    dsimp only [b4]
    positivity
  have hb5 : 0 ≤ b5 := by dsimp only [b5]; positivity
  obtain ⟨B,hB,hbudget⟩ := boundary_excess_budget b1 b1 b3 b4 b5 hb1 hb1 hb3 hb4 hb5
  refine ⟨B,hB,?_⟩
  intro M hM htau eta heta L m n hkn hnm x z hx hz hxz ω hgood u h g hsol hg hgh hhh ell hell
  have hs1 : (1 / 4 : ℝ) ∈ Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := ⟨by linarith, le_rfl⟩
  have hepsI : eta ∈ Icc (8 * (1 / 4 : ℝ)⁻¹ * M.delta ^ 2) 1 :=
    ⟨by norm_num; linarith [heta.1], heta.2⟩
  have hgood' : ω ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z eta
      ((1 / 4 : ℝ) / 8) := by
    simpa only [show (1 / 4 : ℝ) / 8 = 1 / 32 by norm_num] using hgood
  have hraw := hstep M (1 / 4) hs1 htau eta hepsI k (by omega) L m n hkn hnm x hx z hz hxz ω u h g
    hsol hg hhh ell hell
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.indicatorValue_of_mem hgood'] at hraw
  simp only [show (1 / 4 : ℝ) / 8 = 1 / 32 by norm_num] at hraw
  have heta0 : 0 ≤ eta := le_trans (by positivity) heta.1
  have hErr0 : 0 ≤ section6HomogenizationError M (1 / 32) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTinv0 : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg M L (n + 2) ω _)
  set Err : ℝ := section6HomogenizationError M (1 / 32) L (n + 2) ω z with hErrdef
  set Tinv : ℝ := (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ with hTinvdef
  have hd1 : 1 ≤ d := by omega
  have hEn : 0 ≤ excess n (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hMean := Section6Holder.vectorSupNormOn_cube_nonneg hhh
  have hG := holderSeminormOn_nonneg hgh
  have hH := holderSeminormOn_nonneg hhh
  have hmean := Section6Holder.sqrt_vecNormSq_averageVecOn_truncatedCube_le_vectorSupNormOn_cube
    (j := (n:ℤ)) h hx (by omega) hhh
  have hfg := aux_lem_as_regularity_boundary_step_twelve_forcing (n := n) hd1 hx hgh
  have hsem := Section6Holder.holderSeminormOn_mono (by norm_num : (0:ℝ)<1/2) hhh
    (truncatedCube_subset_cube d m n x)
  have hmean' : (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      (1/4:ℝ)^(-3/2:ℝ)*Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) else 0) ≤
      (1/4:ℝ)^(-3/2:ℝ)*vectorSupNormOn (cube d m) h.grad := by
    split_ifs
    · exact mul_le_mul_of_nonneg_left hmean (by positivity)
    · positivity
  have hholder' : (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      A*(1/4:ℝ)^(-3:ℝ)*pk*(3:ℝ)^((n:ℝ)/2)*holderSeminormOn (truncatedCube d m n x) (1/2) h.grad else 0) ≤
      b5*(3:ℝ)^((n:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad := by
    split_ifs
    · exact mul_le_mul_of_nonneg_left hsem (by positivity)
    · positivity
  have hforce := mul_le_mul_of_nonneg_left hfg
    (show 0 ≤ A*(1/4:ℝ)^(-15/2:ℝ)*pk*Tinv from mul_nonneg (by positivity) hTinv0)
  have hmean'' := mul_le_mul_of_nonneg_left hmean'
    (mul_nonneg hb1 hErr0)
  have hnormalized : excess ((n:ℤ)-k) (truncatedCube d m ((n:ℤ)-k) x) u.toFun ≤
      (A*((3:ℝ)^(-(k:ℝ)/2))+b1*eta)*excess n (truncatedCube d m n x) u.toFun +
      b1*Err*Real.sqrt (vecNormSq ell.slope) + b3*Err*vectorSupNormOn (cube d m) h.grad +
      b4*Tinv*(3:ℝ)^((n:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
      b5*(3:ℝ)^((n:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad := by
    dsimp only [b1,b3,b4,b5,pk] at hholder' hforce hmean'' ⊢
    nlinarith only [hraw,hholder',hforce,hmean'']
  exact hbudget A ((3:ℝ)^(-(k:ℝ)/2)) eta _ _ _ _ _ Tinv ((3:ℝ)^((n:ℝ)/2)) Err _
    heta0 hEn hSl hMean hG hH hTinv0 (by positivity) hErr0 hnormalized

end Paper
