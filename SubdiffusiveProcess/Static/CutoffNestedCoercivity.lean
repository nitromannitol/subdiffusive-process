module

public import SubdiffusiveProcess.Static.LocalEstimateClauses
public import SubdiffusiveProcess.Static.AnchoredLawTransport
public import SubdiffusiveProcess.Static.LocalNormalization
public import SubdiffusiveProcess.Static.CutoffCoercivityTail

@[expose] public section

/-! # The exact physical nested-coercivity supplier for Section 8 -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_uniform_local_coercivity (d p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂localAnchoredLaw M,
            localCoercivityEstimates
              (SubdiffusiveProcess.Static.localCoefficient M L m z ω)
              c s0 s1 (K ω) 5 := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, ?_⟩
    intro M _
    have hh := M.shellPrefix.dimension
    omega
  let : NeZero d := ⟨hd⟩
  obtain ⟨δf, hδf, hf⟩ := exists_uniform_finite_nested_coercivity d p c s0 s1 hs q hq
  obtain ⟨δt, hδt, ht⟩ := exists_uniform_tail_nested_coercivity d p c s0 s1 hs q hq
  refine ⟨min δf δt, lt_min hδf hδt, ?_⟩
  intro M hM
  obtain ⟨Cf, hCf, hfM⟩ := hf M (hM.trans (min_le_left _ _))
  obtain ⟨Ct, hCt, htM⟩ := ht M (hM.trans (min_le_right _ _))
  refine ⟨Cf + Ct, add_pos hCf hCt, ?_⟩
  intro L m z
  have hfinite : ∀ L : ℕ, L ≤ m → ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧
      (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal (Cf + Ct) ∧
      ∀ᵐ ω ∂localAnchoredLaw M,
        localCoercivityEstimates (SubdiffusiveProcess.Static.localCoefficient M (L : WithTop ℕ) m z ω)
          c s0 s1 (K ω) 5 := by
    intro L hLm
    obtain ⟨K, hK, hK1, hKmom, hKc⟩ := hfM L m hLm z
    exact ⟨K, hK, hK1, hKmom.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hCt.le)), hKc⟩
  have htail : (m : WithTop ℕ) ≤ L → ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧
      (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal (Cf + Ct) ∧
      ∀ᵐ ω ∂localAnchoredLaw M,
        localCoercivityEstimates (SubdiffusiveProcess.Static.localCoefficient M L m z ω)
          c s0 s1 (K ω) 5 := by
    intro hmL
    obtain ⟨K, hK, hK1, hKmom, hKc⟩ := htM L m hmL z
    exact ⟨K, hK, hK1, hKmom.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hCf.le)), hKc⟩
  cases L using WithTop.recTopCoe
  · exact htail le_top
  · rename_i L
    rcases le_total L m with hLm | hmL
    · exact hfinite L hLm
    · exact htail (WithTop.coe_le_coe.mpr hmL)

end SubdiffusiveProcess.Static
