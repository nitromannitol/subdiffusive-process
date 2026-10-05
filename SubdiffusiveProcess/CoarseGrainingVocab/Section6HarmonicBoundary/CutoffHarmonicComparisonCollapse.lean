
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.ComparisonCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicBoundaryCellRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicSharpLoopApplication

@[expose] public section

/-!
# Clause (C) of the v6 harmonic anchor at a finite cutoff, from the cell row

Cutoff companions of `Section6HarmonicBoundary.HarmonicComparisonClauseV6` and
`Section6HarmonicBoundary.harmonicComparisonClauseV6_of_cellRow`: the binder
`m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`, exactly as
prescribed.

The changed leaves are the cutoff sharp-loop application, the cutoff
weighted-energy slot from the cutoff cell row, and the cutoff error cap; the
three private arithmetic collapse legs of the original module are deterministic
and are restated there, not here.

re-running  with
`G^{(L)}` and `𝒢^{(L)}`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]



def HarmonicComparisonClauseV6 (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M (some L) (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-8 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)

private theorem harmonicComparisonConstant_pos
    {A Ct V Ck Cerr Cdslot UD dim cardRoot Cbz : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (hCk : 0 ≤ Ck)
    (hCerr : 0 ≤ Cerr) (hCdslot : 0 ≤ Cdslot) (hUD : 0 ≤ UD)
    (hdim : 0 ≤ dim) (hcardRoot : 0 ≤ cardRoot) (hCbz : 0 ≤ Cbz) :
    0 < (8 * A * Ct * V * Ck) * (1 + Cerr) +
      ((128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)) +
      ((1 / 9) * UD * dim * cardRoot * Cbz) + 1 := by
  exact add_pos_of_nonneg_of_pos (by positivity) zero_lt_one

private theorem harmonicComparisonReadout_nonneg
    {C S E W N A R T G H : ℝ}
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hG : 0 ≤ G) (hH : 0 ≤ H) :
    0 ≤ C * S ^ 4 * E * W + C * S ^ 4 * E * (S ^ 3 * N * A) +
      C * S ^ 16 * (R * R)⁻¹ * N * T * G + C * S ^ 8 * N * T * H := by
  positivity

private theorem harmonicComparisonBq_nonneg (B : Prop) [Decidable B] (n : ℕ)
    {sigma s Wq Gq meanGrad semiGrad : ℝ}
    (hsigma : 0 ≤ sigma) (hs : 0 ≤ s) (hW : 0 ≤ Wq) (hG : 0 ≤ Gq)
    (hmean : 0 ≤ meanGrad) (hsemi : 0 ≤ semiGrad) :
    0 ≤ (3 : ℝ) ^ (-(n : ℤ)) * Wq + (if B then meanGrad else 0) +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      (if B then Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        semiGrad else 0) := by
  have hp6 := Real.rpow_nonneg hs (-6 : ℝ)
  have hp2 := Real.rpow_nonneg hs (-2 : ℝ)
  have hp3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (s * (n : ℝ))
  have hpz : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) := le_of_lt (zpow_pos (by norm_num) _)
  have hinv := inv_nonneg.mpr hsigma
  split_ifs <;> positivity

private theorem harmonicComparisonCombine
    {P0 Q0 X1 Y1 Z1 CXv CYv CZv Cerr S1 Er Wq N3 AH R T Gq Hd : ℝ}
    (hCXv0 : 0 ≤ CXv) (hN3 : 0 ≤ N3)
    (hT0 : 0 ≤ T) (hGq0 : 0 ≤ Gq) (hHd0 : 0 ≤ Hd) (hR0 : 0 ≤ R)
    (hErC : Er ≤ Cerr)
    (h1 : P0 * (Q0 * X1) ≤
      CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
      CXv * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
      CXv * Er * S1 ^ 8 * N3 * T * Hd)
    (h2 : P0 * (Q0 * Y1) ≤ CYv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq)
    (h3 : Z1 ≤ CZv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq) :
    P0 * (Q0 * (X1 + Y1)) + Z1 ≤
      CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
      (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
      CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by
  have hstep : CXv * Er ≤ CXv * Cerr := mul_le_mul_of_nonneg_left hErC hCXv0
  have hup3 : CXv * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq ≤
      CXv * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq := by
    have hrest : (0 : ℝ) ≤ S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq := by positivity
    calc CXv * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq
        = (CXv * Er) * (S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq) := by ring
      _ ≤ (CXv * Cerr) * (S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq) :=
          mul_le_mul_of_nonneg_right hstep hrest
      _ = CXv * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq := by ring
  have hup4 : CXv * Er * S1 ^ 8 * N3 * T * Hd ≤
      CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by
    have hrest : (0 : ℝ) ≤ S1 ^ 8 * N3 * T * Hd := by positivity
    calc CXv * Er * S1 ^ 8 * N3 * T * Hd
        = (CXv * Er) * (S1 ^ 8 * N3 * T * Hd) := by ring
      _ ≤ (CXv * Cerr) * (S1 ^ 8 * N3 * T * Hd) :=
          mul_le_mul_of_nonneg_right hstep hrest
      _ = CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by ring
  have h1' : P0 * (Q0 * X1) ≤
      CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
        CXv * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
        CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by
    linarith only [h1, hup3, hup4]
  calc P0 * (Q0 * (X1 + Y1)) + Z1
      = P0 * (Q0 * X1) + P0 * (Q0 * Y1) + Z1 := by ring
    _ ≤ (CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
          CXv * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
          CXv * Cerr * S1 ^ 8 * N3 * T * Hd) +
        CYv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
        CZv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
        add_le_add (add_le_add h1' h2) h3
    _ = CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
          (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
          CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by ring

private theorem harmonicComparisonAbsorption (d : ℕ)
    {Ctot CXv CYv CZv Cerr S1 Er Wq N3 AH R T Gq Hd : ℝ}
    (hCXv0 : 0 ≤ CXv) (hCYv0 : 0 ≤ CYv) (hCZv0 : 0 ≤ CZv)
    (hCerr : 0 < Cerr) (hS11 : 1 ≤ S1) (hEr0 : 0 ≤ Er) (hWq0 : 0 ≤ Wq)
    (hN3 : 0 ≤ N3) (hAH0 : 0 ≤ AH) (hR0 : 0 ≤ R) (hT0 : 0 ≤ T)
    (hGq0 : 0 ≤ Gq) (hHd0 : 0 ≤ Hd)
    (hCtotval : Ctot = (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1)) :
    (9 : ℝ) ^ d * (CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
      (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
      CXv * Cerr * S1 ^ 8 * N3 * T * Hd) ≤
      Ctot * S1 ^ 4 * Er * Wq + Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) +
      Ctot * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
      Ctot * S1 ^ 8 * N3 * T * Hd := by
  have hS10 : 0 ≤ S1 := zero_le_one.trans hS11
  -- the final constant comparison
  have hP1 : (0 : ℝ) ≤ S1 ^ 4 * Er * Wq := by positivity
  have hP2 : (0 : ℝ) ≤ S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) := by positivity
  have hP3 : (0 : ℝ) ≤ S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq := by positivity
  have hP4 : (0 : ℝ) ≤ S1 ^ 8 * N3 * T * Hd := by positivity
  have hCerr0 : (0 : ℝ) ≤ Cerr := hCerr.le
  have hprod : (0 : ℝ) ≤ CXv * Cerr := mul_nonneg hCXv0 hCerr0
  have hb1 : (9 : ℝ) ^ d * CXv ≤ Ctot := by
    rw [hCtotval]
    exact mul_le_mul_of_nonneg_left (by linarith only [hprod, hCYv0, hCZv0])
      (by positivity)
  have hb2 : (9 : ℝ) ^ d * (CXv * Cerr + CYv + CZv) ≤ Ctot := by
    rw [hCtotval]
    exact mul_le_mul_of_nonneg_left (by linarith only [hCXv0]) (by positivity)
  have hb3 : (9 : ℝ) ^ d * (CXv * Cerr) ≤ Ctot := by
    rw [hCtotval]
    exact mul_le_mul_of_nonneg_left (by linarith only [hCXv0, hCYv0, hCZv0])
      (by positivity)
  have hleg2 : (9 : ℝ) ^ d * (CXv * S1 ^ 4 * Er * N3 * AH) ≤
      Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) := by
    have hmono : S1 ^ 4 * Er * N3 * AH ≤ S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) := by
      have hone : (1 : ℝ) ≤ S1 ^ 3 := one_le_pow₀ hS11
      have hbase : (0 : ℝ) ≤ S1 ^ 4 * Er * (N3 * AH) := by positivity
      calc S1 ^ 4 * Er * N3 * AH = (S1 ^ 4 * Er * (N3 * AH)) * 1 := by ring
        _ ≤ (S1 ^ 4 * Er * (N3 * AH)) * S1 ^ 3 :=
            mul_le_mul_of_nonneg_left hone hbase
        _ = S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) := by ring
    calc (9 : ℝ) ^ d * (CXv * S1 ^ 4 * Er * N3 * AH)
        = ((9 : ℝ) ^ d * CXv) * (S1 ^ 4 * Er * N3 * AH) := by ring
      _ ≤ ((9 : ℝ) ^ d * CXv) * (S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ Ctot * (S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH)) :=
          mul_le_mul_of_nonneg_right hb1 hP2
      _ = Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) := by ring
  calc (9 : ℝ) ^ d * (CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
        (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
        CXv * Cerr * S1 ^ 8 * N3 * T * Hd)
      = ((9 : ℝ) ^ d * CXv) * (S1 ^ 4 * Er * Wq) +
        (9 : ℝ) ^ d * (CXv * S1 ^ 4 * Er * N3 * AH) +
        ((9 : ℝ) ^ d * (CXv * Cerr + CYv + CZv)) *
          (S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq) +
        ((9 : ℝ) ^ d * (CXv * Cerr)) * (S1 ^ 8 * N3 * T * Hd) := by ring
    _ ≤ Ctot * (S1 ^ 4 * Er * Wq) +
        Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) +
        Ctot * (S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq) +
        Ctot * (S1 ^ 8 * N3 * T * Hd) := by
        refine add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right hb1 hP1) hleg2)
          (mul_le_mul_of_nonneg_right hb2 hP3))
          (mul_le_mul_of_nonneg_right hb3 hP4)
    _ = Ctot * S1 ^ 4 * Er * Wq + Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) +
        Ctot * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
        Ctot * S1 ^ 8 * N3 * T * Hd := by ring


private theorem harmonicComparisonScalarBounds (n : ℕ)
    {s S1 V Er Cerr Efull T : ℝ}
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4)
    (hS1def : S1 = s ^ (-(1 / 2 : ℝ)))
    (hS2 : S1 ^ 2 = s⁻¹) (hS9 : S1 ^ 9 = s ^ (-(9 / 2 : ℝ)))
    (hV0 : 0 ≤ V) (hEr0 : 0 ≤ Er) (hErC : Er ≤ Cerr)
    (hEfulldef : Efull = V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er))
    (hTdef : T = (3 : ℝ) ^ (s * (n : ℝ))) :
    (0 ≤ Efull)
    ∧ (Efull ≤ V * 3 * Er)
    ∧ (Efull ≤ V * 3 * Cerr)
    ∧ ((0 : ℝ) ≤ (3 : ℝ) ^ (s / 3 : ℝ))
    ∧ ((3 : ℝ) ^ (s / 3 : ℝ) ≤ 3)
    ∧ ((s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * S1)
    ∧ ((0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)))
    ∧ ((s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2)
    ∧ ((s - s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2)
    ∧ ((0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)))
    ∧ ((s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ 32 * S1 ^ 9)
    ∧ ((0 : ℝ) ≤ 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2)
    ∧ (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 ≤
      1 + 9 * (V * 3 * Cerr) ^ 2)
    ∧ ((0 : ℝ) ≤ (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)))
    ∧ ((3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) ≤ T) := by
  -- the elementary factor bounds
  have hthree : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (3 : ℝ) ^ a ≤ 3 := by
    intro a _ha1 ha2
    calc (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 3 := Real.rpow_one 3
  have hE0 : 0 ≤ Efull := by rw [hEfulldef]; positivity
  have hEB : Efull ≤ V * 3 * Er := by
    rw [hEfulldef]
    have h := hthree (s / 8 * (4 : ℝ)) (by positivity) (by linarith only [hs0, hs4])
    calc V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) ≤ V * (3 * Er) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hEr0) hV0
      _ = V * 3 * Er := by ring
  have hEC : Efull ≤ V * 3 * Cerr :=
    hEB.trans (mul_le_mul_of_nonneg_left hErC (by positivity))
  have he30 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have he3 : (3 : ℝ) ^ (s / 3 : ℝ) ≤ 3 := hthree _ (by positivity) (by linarith only [hs0, hs4])
  have hp1 : (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * S1 := by
    have hc : (2 : ℝ) ^ (-(-(1 / 2 : ℝ))) ≤ 2 := by
      rw [neg_neg]
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [hS1def]
    exact rpow_half_le_two_mul_rpow hs0 hc
  have hp10 : (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hp2 : (s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by rw [hS2]; field_simp
  have hpinv : (s - s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by
    rw [hS2, show s - s / 2 = s / 2 by ring]; field_simp
  have hp90 : (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hp9 : (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ 32 * S1 ^ 9 := by
    have hc : (2 : ℝ) ^ (-(-(9 / 2 : ℝ))) ≤ 32 := by
      rw [neg_neg]
      have h5 : (2 : ℝ) ^ ((5 : ℕ) : ℝ) = 32 := by rw [Real.rpow_natCast]; norm_num
      calc (2 : ℝ) ^ (9 / 2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 32 := h5
    have hq := rpow_half_le_two_mul_rpow (c := 32) hs0 hc
    rw [hS9]
    exact hq
  have hq30 : (0 : ℝ) ≤ 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 := by positivity
  have hq3 : 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 ≤
      1 + 9 * (V * 3 * Cerr) ^ 2 := by
    have hbase : (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull ≤ 3 * (V * 3 * Cerr) :=
      mul_le_mul (hthree _ (by positivity) (by linarith only [hs0, hs4])) hEC hE0 (by norm_num)
    have hnn : 0 ≤ (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull := by positivity
    have hsq := pow_le_pow_left₀ hnn hbase 2
    refine le_trans (add_le_add (le_refl (1 : ℝ)) hsq) (le_of_eq ?_)
    ring
  have ht30 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have ht3 : (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) ≤ T := by
    rw [hTdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : ((((n : ℤ) - 3 : ℤ)) : ℝ) ≤ (n : ℝ) := by push_cast; linarith only
    exact mul_le_mul_of_nonneg_left hcast hs0.le
  exact ⟨hE0, hEB, hEC, he30, he3, hp1, hp10, hp2, hpinv, hp90, hp9, hq30, hq3, ht30, ht3⟩

private theorem harmonicComparisonCoefficients_nonneg
    {A Ct V Ck Cerr Cdslot UD dim cardRoot Cbz : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (hCk : 0 ≤ Ck)
    (hCdslot : 0 ≤ Cdslot) (hUD : 0 ≤ UD)
    (hdim : 0 ≤ dim) (hcardRoot : 0 ≤ cardRoot) (hCbz : 0 ≤ Cbz) :
    0 ≤ 8 * A * Ct * V * Ck ∧
    0 ≤ (128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2) ∧
    0 ≤ (1 / 9) * UD * dim * cardRoot * Cbz := by
  constructor
  · positivity
  constructor <;> positivity

/-- **Clause (C) of the frozen v6 harmonic anchor, modulo the boundary-cell
row.**  Both regimes are covered: the two `BoundaryTouches` legs of the frozen
right-hand side are produced by the two boundary legs of the weighted-energy
slot. -/
theorem harmonicComparisonClauseV6_of_cellRow (d : ℕ) [NeZero d] {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hrow : BoundaryCellManuscriptRow d Cb) :
    HarmonicComparisonClauseV6 d := by
  classical
  obtain ⟨Cloop, Cdslot, hCloopTop, hCdslot, hloop⟩ :=
    exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy d
  obtain ⟨Ck, hCk, hslot⟩ := exists_boundaryWeightedEnergySlot_of_cellRow d hCb hrow
  obtain ⟨Cerr, hCerr, herr⟩ :=
    exists_section6HomogenizationError_le_of_goodEvent (d := d)
  obtain ⟨Cbz, hCbz, hbesov⟩ := exists_interiorForceBesov_le_windowSeminorm d
  have hA0 : (0 : ℝ) ≤ (flatComparatorSharpSpectralConstant d).toReal :=
    ENNReal.toReal_nonneg
  have hCt0 : (0 : ℝ) ≤ Cloop.toReal := ENNReal.toReal_nonneg
  have hUD0 : (0 : ℝ) ≤ unitDirichletPoincareConst d :=
    unitDirichletPoincareConst_nonneg d
  refine ⟨(9 : ℝ) ^ d *
      ((8 * (flatComparatorSharpSpectralConstant d).toReal * Cloop.toReal *
          Real.sqrt (192 * (d : ℝ)) * Ck) * (1 + Cerr) +
        ((128 / 9) * (flatComparatorSharpSpectralConstant d).toReal *
          Cloop.toReal * Cdslot *
          (1 + 9 * (Real.sqrt (192 * (d : ℝ)) * 3 * Cerr) ^ 2)) +
        ((1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) * Cbz) + 1),
      mul_pos (pow_pos (by norm_num) _)
        (harmonicComparisonConstant_pos hA0 hCt0 (Real.sqrt_nonneg _)
          hCk.le hCerr.le hCdslot.le hUD0 (Nat.cast_nonneg _)
          (Real.sqrt_nonneg _) hCbz.le), ?_⟩
  intro M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
    hfval hfgrad v hharm htrace
  -- corridor parameters
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s := (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hslt : s < 1 := by linarith only [hs0, hs4]
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hUdef
  set sigma : ℝ :=
    tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set Er : ℝ := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErdef
  set Wq : ℝ := normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun)
    with hWqdef
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
  -- the polynomial variables
  set A : ℝ := (flatComparatorSharpSpectralConstant d).toReal with hAdef
  set Ct : ℝ := Cloop.toReal with hCtdef
  set V : ℝ := Real.sqrt (192 * (d : ℝ)) with hVdef
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  have hR : 0 < R := Real.sqrt_pos.mpr hsigma
  have hRR : R * R = sigma := Real.mul_self_sqrt hsigma.le
  have hS12 : (2 : ℝ) ≤ S1 := two_le_rpow_neg_half hs0 hs4
  have hS11 : (1 : ℝ) ≤ S1 := le_trans (by norm_num) hS12
  have hS10 : (0 : ℝ) ≤ S1 := le_trans zero_le_one hS11
  have hN3 : 0 < N3 := by rw [hN3def]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  -- power dictionary
  have hS4 : S1 ^ 4 = s ^ (-2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 4]; congr 1; norm_num
  have hS8 : S1 ^ 8 = s ^ (-4 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 8]; congr 1; norm_num
  have hS16 : S1 ^ 16 = s ^ (-8 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 16]; congr 1; norm_num
  have hS3 : S1 ^ 3 = s ^ (-3 / 2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 3]
    norm_num
  have hS2 : S1 ^ 2 = s⁻¹ := by
    rw [hS1def, rpow_neg_half_pow hs0 2,
      show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hS9 : S1 ^ 9 = s ^ (-(9 / 2 : ℝ)) := by
    rw [hS1def, rpow_neg_half_pow hs0 9]; congr 1; norm_num
  have hS24 : S1 ^ 24 = s ^ (-12 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 24]; congr 1; norm_num
  have hRRinv : (R * R)⁻¹ = sigma⁻¹ := by rw [hRR]
  have hN3T : N3 * T = (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := by
    rw [hN3def, hTdef, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  -- the frozen right-hand side, in the polynomial variables
  set Ctot : ℝ := (9 : ℝ) ^ d *
      ((8 * A * Ct * V * Ck) * (1 + Cerr) +
        ((128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)) +
        ((1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) * Cbz) + 1) with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by
    rw [hCtotdef]
    exact mul_nonneg (by positivity)
      (harmonicComparisonConstant_pos hA0 hCt0 hV0 hCk.le hCerr.le
        hCdslot.le hUD0 (Nat.cast_nonneg _) (Real.sqrt_nonneg _) hCbz.le).le
  have hAHleg : (if BoundaryTouches U (cube d (m : ℤ)) then
      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
        Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) =
      S1 ^ 3 * N3 * AH := by
    rw [hS3, hAHdef, hN3def]
    split <;> ring
  have hHdleg : (if BoundaryTouches U (cube d (m : ℤ)) then
      Ctot * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) *
        (fractionalSeminormOn U s h.grad).toReal else 0) =
      Ctot * S1 ^ 8 * N3 * T * Hd := by
    rw [hS8, hHddef, ← hN3T]
    split <;> ring
  rw [hAHleg, hHdleg,
    show Ctot * s ^ (-2 : ℝ) * Er * (Wq + S1 ^ 3 * N3 * AH) =
      Ctot * S1 ^ 4 * Er * Wq + Ctot * S1 ^ 4 * Er * (S1 ^ 3 * N3 * AH) by
      rw [hS4]; ring,
    show Ctot * s ^ (-8 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq =
      Ctot * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq by
      rw [hS16, hRRinv, ← hN3T]; ring]
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _
    (harmonicComparisonReadout_nonneg hCtot0 hS10 hEr0 hWq0 hN3.le hAH0
      hR.le hT0 hGq0 hHd0) ?_
  intro hgood
  -- the error cap on the good event
  have hErC : Er ≤ Cerr := herr M s hs L (n + 2) ω z hgood
  -- the fractional datum at the anchor's own order
  obtain ⟨sOrder, hsval, hgWsp⟩ := hgex
  have hsO : sOrder = (⟨s, hs0, hslt⟩ : FractionalOrder) := Subtype.ext hsval
  rw [hsO] at hgWsp
  -- the weighted-energy slot
  set Bq : ℝ := (3 : ℝ) ^ (-(n : ℤ)) * Wq +
      (if BoundaryTouches U (cube d (m : ℤ)) then
        Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) +
      sigma⁻¹ * (Real.rpow s (-6 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) * Gq) +
      (if BoundaryTouches U (cube d (m : ℤ)) then
        Real.rpow s (-2 : ℝ) * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (fractionalSeminormOn U s h.grad).toReal else 0) with hBqdef
  set Sfull : ℝ :=
    Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
      (Real.sqrt sigma * (Ck * Bq)) with hSfulldef
  have hslotS : ∀ u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2))),
      (∀ p, u0.grad p = u.grad (p + y)) →
      weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
        ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
        ((aCutoffFamily M L (translatePotentialSample y ω)).coeffOn
          (originCube d ((n : ℤ) - 2))) u0
        (⟨s / 3, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
        (⟨s / 2, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
        FiniteLpExponent.two ≤ ENNReal.ofReal Sfull := by
    intro u0 hu0grad
    exact hslot M (⟨s, hs0, hslt⟩ : FractionalOrder) hs L m n hnm z x y ω
      hz hx hloc hgood u h g hdir hgWsp hh u0 hu0grad
      (⟨s / 3, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
      (⟨s / 2, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
      (by dsimp only; linarith only [hs0, hs4])
  -- the sharp loop
  have hL := hloop M s hs L m n hnm z x y ω hz hx hloc hgood u h g hdir
    hgWsp Sfull hslotS uD v hfval hharm htrace
  -- the window shrink
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
    (uD := uD) (v := v) (u := u.toFun) hfval hcov hWpos hVpos
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
  -- the readout carriers
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Dfull : ℝ := Cdslot * S1 * Gq with hDfulldef
  set CXv : ℝ := 8 * A * Ct * V * Ck with hCXvdef
  set CYv : ℝ := (128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)
    with hCYvdef
  set CZv : ℝ := (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
    Real.sqrt (Fintype.card (Fin d) : ℝ) * Cbz with hCZvdef
  obtain ⟨hCXv0, hCYv0, hCZv0⟩ : 0 ≤ CXv ∧ 0 ≤ CYv ∧ 0 ≤ CZv :=
    harmonicComparisonCoefficients_nonneg hA0 hCt0 hV0 hCk.le
      hCdslot.le hUD0 (Nat.cast_nonneg _) (Real.sqrt_nonneg _) hCbz.le
  obtain ⟨hE0, hEB, hEC, he30, he3, hp1, hp10, hp2, hpinv, hp90, hp9, hq30, hq3, ht30, ht3⟩ :=
    harmonicComparisonScalarBounds n hs0 hs4 hS1def hS2 hS9 hV0 hEr0 hErC
      hEfulldef hTdef
  -- the weighted-energy slot in the polynomial variables
  have hpowN : (3 : ℝ) ^ (-(n : ℤ)) = N3⁻¹ := by
    rw [hN3def, zpow_neg, zpow_natCast]
  have hBq0 : 0 ≤ Bq := by
    rw [hBqdef]
    exact harmonicComparisonBq_nonneg (BoundaryTouches U (cube d (m : ℤ))) n
      hsigma.le hs0.le hWq0 hGq0 (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hs6 : Real.rpow s (-6 : ℝ) = S1 ^ 12 := by
    rw [hS1def, rpow_neg_half_pow hs0 12]; congr 1; norm_num
  have hs2 : Real.rpow s (-2 : ℝ) = S1 ^ 4 := hS4.symm
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRBq : R * Bq = R * N3⁻¹ * Wq + R * AH +
      S1 ^ 12 * R⁻¹ * T * Gq + S1 ^ 4 * R * T * Hd := by
    have hrp : Real.rpow (3 : ℝ) (s * (n : ℝ)) = (3 : ℝ) ^ (s * (n : ℝ)) := rfl
    rw [hBqdef, hAHdef, hHddef, hrp, hTdef, hpowN, hs6, hs2, ← hRR]
    clear_value R S1 N3 Wq Gq
    split_ifs <;> field_simp [hRne]
    ring
  have hSv0 : 0 ≤ Sfull := by
    rw [hSfulldef]
    exact mul_nonneg (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCk.le hBq0))
  have hSv : Sfull ≤ 2 * S1 * Ck * (R * N3⁻¹ * Wq + R * AH +
      S1 ^ 12 * R⁻¹ * T * Gq + S1 ^ 4 * R * T * Hd) := by
    rw [← hRBq, hSfulldef]
    have hdw := dirichletWeightedEnergyFactor_third_half_le hs0 hs4
    have hnn : 0 ≤ Real.sqrt sigma * (Ck * Bq) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCk.le hBq0)
    calc Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
          (Real.sqrt sigma * (Ck * Bq)) ≤
          (2 * S1) * (Real.sqrt sigma * (Ck * Bq)) :=
        mul_le_mul_of_nonneg_right hdw hnn
      _ = 2 * S1 * Ck * (R * Bq) := by rw [hRdef]; ring
  -- the direct forcing slot
  set Bsv : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo
    (originCube d ((n : ℤ) - 2)) (s / 2 : ℝ) (fun p ↦ g (p + y)) with hBsvdef
  have hglocalS : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d ((n : ℤ) - 2)) (⟨s, hs0, hslt⟩ : FractionalOrder)
      FiniteLpExponent.two (fun p ↦ g (p + y)) := by
    refine memCubeEuclideanFullWsp_translate_of_subset
      (originCube d ((n : ℤ) - 2)) (originCube d (m : ℤ)) y _
      FiniteLpExponent.two g ?_ hgWsp
    intro p hp
    refine (hloc ?_).2
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
    exact hp
  have hbesovReg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) s
      (fun p ↦ g (p + y)) :=
    (cubeEuclideanWspField_forceSobolevRegularity
      (⟨s, hs0, hslt⟩ : FractionalOrder)
      { toField := fun p ↦ g (p + y)
        euclideanMemLp := hglocalS.1
        euclideanMemWsp := hglocalS.2 }).toForceBesovRegularity hs0 hslt.le
  have hBv0 : 0 ≤ Bsv :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ _ _
      (cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le _ _
        (show (s / 2 : ℝ) ≤ s by linarith only [hs0, hs4]) hbesovReg.partialSeminorms_bddAbove)
  have hBv : Bsv ≤ Cbz * T * S1 * Gq :=
    hbesov (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc g hgWsp
      (s / 2) (by linarith only [hs0, hs4])
  -- the three summands of the loop readout
  have hcsB : (3 : ℝ) ^ ((n : ℤ) - 2) = N3 / 9 := by
    rw [hN3def, show ((n : ℤ) - 2) = ((n : ℕ) : ℤ) + (-2 : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
    ring
  have hcsA : centeredCubeScale ((n : ℤ) - 2) = N3 / 9 := by
    simpa only [centeredCubeScale] using hcsB
  set P0 : ℝ := A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ with hP0def
  set Q0 : ℝ := (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) with hQ0def
  set X1 : ℝ := Ct * (s / 2 : ℝ)⁻¹ * R * (3 : ℝ) ^ (s / 3 : ℝ) * Efull * Sfull
    with hX1def
  set Y1 : ℝ := Ct * (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) * (s - s / 2 : ℝ)⁻¹ *
    (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
    (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull with hY1def
  set Z1 : ℝ := unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * (d : ℝ) *
    sigma⁻¹ * (Real.sqrt (Fintype.card (Fin d) : ℝ) * Bsv) with hZ1def
  -- the collapse itself
  have hkey : P0 * (Q0 * (X1 + Y1)) + Z1 ≤
      CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
        (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
        CXv * Cerr * S1 ^ 8 * N3 * T * Hd := by
    have h1 : P0 * (Q0 * X1) ≤
        CXv * S1 ^ 4 * Er * Wq + CXv * S1 ^ 4 * Er * N3 * AH +
          CXv * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq +
          CXv * Er * S1 ^ 8 * N3 * T * Hd :=
      bcollapse_term1 hA0 hCt0 hV0 hCk.le hR hS10 hN3 hT0 hEr0 hWq0 hGq0 hAH0
        hHd0 hcsA hRRinv.symm hp10 hp1 hp2 he30 he3 hE0 hEB hSv0 hSv
    have h2 : P0 * (Q0 * Y1) ≤ CYv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
      bcollapse_term2 hA0 hCt0 hCdslot.le (by positivity) hR hS11 hN3 hT0 hGq0
        hcsA hRRinv.symm hp10 hp1 hp90 hp9 hpinv hq30 hq3 ht30 ht3 rfl
    have h3 : Z1 ≤ CZv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
      bcollapse_term3 hUD0 (by positivity) (Real.sqrt_nonneg _) hCbz.le hR hS11
        hN3 hT0 hGq0 hcsB hRRinv.symm hBv0 hBv
    exact harmonicComparisonCombine hCXv0 hN3.le hT0 hGq0 hHd0 hR.le
      hErC h1 h2 h3
  -- assemble
  have hreadout := flatComparatorSharpGoodEventLoopBound_le_realReadout
    Cloop d n sigma (⟨s / 2, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
    (⟨s / 3, by positivity, by linarith only [hs0, hs4]⟩ : FractionalOrder)
    (⟨s, hs0, hslt⟩ : FractionalOrder) Efull Sfull Dfull
    (originCube d ((n : ℤ) - 2)) (fun p ↦ g (p + y))
    (by dsimp only; linarith only [hs0, hs4]) hsigma hE0 hSv0
    (mul_nonneg (mul_nonneg hCdslot.le hS10) hGq0)
  refine le_trans (le_trans hshrink
    (mul_le_mul hratio9 (hL.trans hreadout)
      (Section6Iteration.normalizedL2On_nonneg _ _) (pow_nonneg (by norm_num) _)))
    (le_trans (mul_le_mul_of_nonneg_left hkey (pow_nonneg (by norm_num) _)) ?_)
  have hCtotval : Ctot =
      (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1) := by
    simp only [hCtotdef, hCXvdef, hCYvdef, hCZvdef]
  exact harmonicComparisonAbsorption d hCXv0 hCYv0 hCZv0 hCerr hS11 hEr0
    hWq0 hN3.le hAH0 hR.le hT0 hGq0 hHd0 hCtotval

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
