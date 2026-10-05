module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_repair_err_good_scale_localization

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

attribute [local instance] Classical.propDecidable

lemma aux_lem_repair_err_good_scale_transport_min
    (eps a b c : ℝ) (heps : 0 ≤ eps) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min eps (32 * a + b + c) ≤ 32 * min eps (a + b + c) := by
  by_cases h : eps ≤ a + b + c
  · rw [min_eq_left h]
    calc
      min eps (32 * a + b + c) ≤ eps := min_le_left _ _
      _ ≤ 32 * eps := by
        calc
          eps = 1 * eps := by ring
          _ ≤ 32 * eps :=
            mul_le_mul_of_nonneg_right (by norm_num) heps
  · have h' : a + b + c ≤ eps := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h']
    have hB : 32 * a + b + c ≤ 32 * (a + b + c) := by
      have hb' : b ≤ 32 * b := by
        calc
          b = 1 * b := by ring
          _ ≤ 32 * b := mul_le_mul_of_nonneg_right (by norm_num) hb
      have hc' : c ≤ 32 * c := by
        calc
          c = 1 * c := by ring
          _ ≤ 32 * c := mul_le_mul_of_nonneg_right (by norm_num) hc
      calc
        32 * a + b + c ≤ 32 * a + 32 * b + c :=
          add_le_add (add_le_add le_rfl hb') le_rfl
        _ ≤ 32 * a + 32 * b + 32 * c := add_le_add le_rfl hc'
        _ = 32 * (a + b + c) := by ring
    calc
      min eps (32 * a + b + c) ≤ 32 * a + b + c := min_le_right _ _
      _ ≤ 32 * (a + b + c) := hB



theorem lem_repair_err_good_scale_transport :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cg : ℝ, 0 < Cg ∧
    ∀ (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
      let s0 : ℝ := It.s0
      let eps : ℝ := It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)
      64 * M.delta ^ 2 ≤ s0 → s0⁻¹ * M.delta ^ 2 ≤ eps → eps ≤ 1 →
      ∀ (L m j : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (om : BilateralField d),
        j + 2 ≤ L → j + 2 ≤ m → It.good (j + 2) z eps s0 om →
        Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
            E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
            ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 ≤
          Cg * min eps (M.delta ^ 2 + eps ^ 8 + It.score (j + 2) z s0 om) := by
  intro d hd _ _
  let : NeZero d := ⟨by omega⟩
  let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
      d (fun [NeZero d] => _root_.SubdiffusiveProcess.Section6.harmonic_approximation_good_scales_interior d))
  let c1 := Classical.choose H
  let c2 := Classical.choose (Classical.choose_spec H)
  let cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
  let c0 := max (max 46 c1) (max (1024 * c2 ^ 2) cmin)
  have hH := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  let h1 : (1 : ℝ) ≤ c1 := le_trans (by norm_num) hH.1
  let h2 : (1 : ℝ) ≤ c2 := le_trans h1 hH.2.1
  let Ct := Classical.choose
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_uncutGammaOneTail d 21 h1 h2)
  let Ce := Classical.choose
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d)
  let Sdim : ℝ := ((d : ℝ) + 1) ^ 2 *
    max 1 (Classical.choose (_root_.SubdiffusiveProcess.Section6.cutoff_holder_regularity d))
  let Cstar : ℝ := max Sdim (max c0 (max Ct Ce))
  let D : ℝ := Real.sqrt (1 + 3 * (d : ℝ) /
    ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1))
  let Cg : ℝ := 32 * (|Cstar| + 1) * (|D| + 1)
  refine ⟨Cg, ?_, ?_⟩
  · positivity
  · intro E M Sreg It alpha halpha hdelta s0 eps h64 heps heps1
      L m j z hR om hjL hjm hgood
    have hs0eq : s0 = 1 / 32 := It.s0_eq
    have hs0 : s0 ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [hs0eq]
      norm_num
    have hepsnonneg : 0 ≤ eps := by
      have hleft : 0 ≤ s0⁻¹ * M.delta ^ 2 := by positivity
      exact le_trans hleft heps
    have hSregC : Sreg.C = Sdim := by
      simpa [Sdim] using Sreg.C_eq_dimensional
    have hItC0 : It.C = max Sreg.C (max c0 (max Ct Ce)) := by
      exact It.C_eq (inferInstance : NeZero d)
    have hItC : It.C = Cstar := by
      rw [hItC0, hSregC]
    have hCnonneg : 0 ≤ It.C := le_of_lt It.C_pos
    have hCbd : It.C ≤ |Cstar| + 1 := by
      rw [hItC]
      exact le_trans (le_abs_self Cstar) (by linarith)
    have hRj : (0 : ℝ) < 3 ^ (j + 2) := by positivity
    have hs0half : s0 ≤ (1 / 2 : ℝ) := by
      rw [hs0eq]
      norm_num
    have hloc := lem_repair_err_good_scale_localization d hd E M Sreg L m j z hR hRj om
      (It.ref L j z om) s0 2 hjm hs0 (by norm_num) (It.ref_pos L j z om)
    have hgooderr := It.good_error L j z hRj eps om h64 hs0half heps heps1 hgood hjL
    have hDnonneg : 0 ≤ Real.sqrt (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s0) - 1)) := Real.sqrt_nonneg _
    have hDeq : Real.sqrt (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s0) - 1)) = D := by
      rw [hs0eq]
    have hDbd : Real.sqrt (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s0) - 1)) ≤ |D| + 1 := by
      rw [hDeq]
      exact le_trans (le_abs_self D) (by linarith)
    let A : ℝ := M.delta ^ 2 + eps ^ 8 + It.score (j + 2) z s0 om
    let B : ℝ := s0⁻¹ * M.delta ^ 2 + eps ^ 8 + It.score (j + 2) z s0 om
    have hA : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (add_nonneg (by positivity) (by positivity))
        (It.score_nonneg (j + 2) z s0 om)
    have hscale : min eps B ≤ 32 * min eps A := by
      dsimp [A, B]
      have hs0inv : s0⁻¹ = 32 := by
        rw [hs0eq]
        norm_num
      rw [hs0inv]
      exact aux_lem_repair_err_good_scale_transport_min eps (M.delta ^ 2)
        (eps ^ 8) (It.score (j + 2) z s0 om) hepsnonneg
        (pow_nonneg hepsnonneg 8)
        (It.score_nonneg (j + 2) z s0 om)
    have hminA : 0 ≤ min eps A := le_min hepsnonneg hA
    rw [hloc]
    calc
      Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
          E.err z ((3 : ℝ) ^ (j + 2)) hRj
            (Sreg.cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hRj) z
            ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2
          ≤ Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              (It.C * min eps B) :=
        mul_le_mul_of_nonneg_left hgooderr hDnonneg
      _ ≤ (|D| + 1) * (It.C * (32 * min eps A)) := by
        calc
          Real.sqrt (1 + 3 * (d : ℝ) /
              ((3 : ℝ) ^ (1 - 2 * s0) - 1)) * (It.C * min eps B)
              ≤ Real.sqrt (1 + 3 * (d : ℝ) /
                ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
                  (It.C * (32 * min eps A)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hscale hCnonneg) hDnonneg
          _ ≤ (|D| + 1) * (It.C * (32 * min eps A)) :=
            mul_le_mul_of_nonneg_right hDbd
              (mul_nonneg hCnonneg (mul_nonneg (by norm_num) hminA))
      _ ≤ Cg * min eps A := by
        calc
          (|D| + 1) * (It.C * (32 * min eps A)) ≤
              ((|D| + 1) * (|Cstar| + 1)) * (32 * min eps A) :=
            calc
              (|D| + 1) * (It.C * (32 * min eps A)) =
                  ((|D| + 1) * It.C) * (32 * min eps A) :=
                (mul_assoc _ _ _).symm
              _ ≤ ((|D| + 1) * (|Cstar| + 1)) * (32 * min eps A) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hCbd
                    (show 0 ≤ |D| + 1 from
                      add_nonneg (abs_nonneg _) (by norm_num)))
                  (show 0 ≤ (32 : ℝ) * min eps A from
                    mul_nonneg (by norm_num) hminA)
          _ = Cg * min eps A := by
            dsimp [Cg]
            ring

end SubdiffusiveProcess.Paper

