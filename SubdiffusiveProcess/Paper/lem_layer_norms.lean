import Mathlib
import SubdiffusiveProcess.Paper.lem_layer_norms_peeling
import SubdiffusiveProcess.Paper.lem_layer_norms_moments
import SubdiffusiveProcess.Paper.lem_layer_norms_absorption

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Paper



theorem lem_layer_norms :
    ∀ (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 1 ≤ Cc),
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ p : ℝ, 0 < p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ k lam : ℝ, 0 ≤ k → 0 ≤ lam → ∃ Cpk : ℝ, 0 < Cpk ∧
    ∀ gam : ℝ, 0 < gam → ∃ Cpkg : ℝ, 0 < Cpkg ∧
    ∀ (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P],
    ∀ disorder : ℝ, 0 < disorder → disorder ≤ 1 →
    ∀ S : ℕ → Om → ℝ,
    (∀ j, AEStronglyMeasurable (S j) P) →
    (∀ j omega, 0 ≤ S j omega) →
    ∀ covers : ℕ → ℝ,
    (∀ j, 1 ≤ covers j) →
    (∀ j, covers j ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))) →
    (∀ (j : ℕ) (s : ℝ), 0 ≤ s →
      P {omega | s < S j omega} ≤
        ENNReal.ofReal (2 * covers j * Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))))) →
    (∀ j : ℕ,
      let a := disorder * Real.sqrt (Cc * Real.log (2 * covers j))
      let X := fun omega => max (S j omega - a) 0
      (∀ omega, 0 ≤ X omega ∧ S j omega ≤ a + X omega) ∧
      (∀ s : ℝ, 0 ≤ s → P {omega | s < X omega} ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2 / (Cc * disorder ^ 2)))))) ∧
    (∀ j : ℕ,
      let r := (3 : ℝ) ^ (-(j : ℝ))
      let B := Cpk * disorder ^ k * (1 + abs (Real.log r)) ^ (k / 2) *
        Real.exp (C0 * lam * disorder * Real.sqrt (1 + abs (Real.log r)) +
          Cp * lam ^ 2 * disorder ^ 2)
      eLpNorm (fun omega => (S j omega) ^ k * Real.exp (lam * S j omega))
        (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
      B ≤ Cpkg * disorder ^ k * r ^ (-gam)) := by
  intro d hd Cc hCc
  obtain ⟨C0, hC0, hC0rest⟩ := lem_layer_norms_moments d hd Cc hCc
  refine ⟨C0, hC0, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hCprest⟩ := hC0rest p hp
  refine ⟨Cp, hCp, ?_⟩
  intro k lam hk hlam
  obtain ⟨Cpk, hCpk, hCpkrest⟩ := hCprest k lam hk hlam
  refine ⟨Cpk, hCpk, ?_⟩
  intro gam hgam
  obtain ⟨Cpkg, hCpkg, hCpkgrest⟩ :=
    lem_layer_norms_absorption C0 Cp Cpk hC0 hCp hCpk k lam hk hlam gam hgam
  refine ⟨Cpkg, hCpkg, ?_⟩
  intro Om _ P _ disorder hdisorder hdisorder_le S hSmeas hSnonneg covers hcovers
    hcoverbound htail
  have hpeel :=
    lem_layer_norms_peeling Cc hCc Om P disorder hdisorder hdisorder_le S hSmeas
      hSnonneg covers hcovers htail
  have hmoment :=
    hCpkrest Om P disorder hdisorder hdisorder_le S hSmeas hSnonneg covers hcovers
      hcoverbound (fun j => (hpeel j).2)
  constructor
  · exact hpeel
  · intro j
    dsimp
    constructor
    · exact hmoment j
    · exact hCpkgrest disorder hdisorder hdisorder_le j

end Paper
