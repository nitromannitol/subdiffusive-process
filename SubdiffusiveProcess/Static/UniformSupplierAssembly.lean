module

public import SubdiffusiveProcess.Static.LocalConstantAssembly
public import SubdiffusiveProcess.Static.AnchoredLawTransport
public import SubdiffusiveProcess.Static.LocalNormalization

@[expose] public section

/-! # Quantifier-preserving assembly of physical static suppliers -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A small-disorder threshold before the model, and a moment bound uniform
in cutoff, physical scale and real centre after the model. -/
def UniformLocalMomentSupplier {d : ℕ} (q : ℝ)
    (P : GMCModel d → WithTop ℕ → ℕ → Vec d → AnchoredC11Sample d → ℝ → Prop) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
    ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
        (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
        ∀ᵐ ω ∂localAnchoredLaw M, P M L m z ω (K ω)

/-- Three independently proved uniform suppliers have one disorder
threshold and one measurable constant, at the same prescribed moment order. -/
theorem uniformLocalMomentSupplier_estimates {d p : ℕ}
    (y0 : Vec d) (ρ0 : ℝ) (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (q B : ℝ)
    (hmass : UniformLocalMomentSupplier q (fun M L m z ω K =>
      localMassEstimates (localDensity M L m z ω) y0 ρ0 K))
    (hcoer : UniformLocalMomentSupplier q (fun M L m z ω K =>
      localCoercivityEstimates (localCoefficient M L m z ω) c s0 s1 K B))
    (hcut : UniformLocalMomentSupplier q (fun M L m z ω K =>
      localHarmonicCutoffEstimates (localCoefficient M L m z ω) c s0 s1 K B)) :
    UniformLocalMomentSupplier q (fun M L m z ω K =>
      estimates (localDensity M L m z ω) (localCoefficient M L m z ω)
        y0 ρ0 c s0 s1 K B) := by
  obtain ⟨δm, hδm, hmass⟩ := hmass
  obtain ⟨δc, hδc, hcoer⟩ := hcoer
  obtain ⟨δh, hδh, hcut⟩ := hcut
  let δ0 := min δm (min δc δh)
  have hδ0 : 0 < δ0 := lt_min hδm (lt_min hδc hδh)
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM
  have hm : M.delta ≤ δm := hM.trans (min_le_left _ _)
  have hc : M.delta ≤ δc := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh : M.delta ≤ δh := hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cm, hCm, hmom⟩ := hmass M hm
  obtain ⟨Cc, hCc, hcmom⟩ := hcoer M hc
  obtain ⟨Ch, hCh, hhmom⟩ := hcut M hh
  refine ⟨Cm + (Cc + Ch), by positivity, ?_⟩
  intro L m z
  exact exists_common_static_constant (localAnchoredLaw M)
    (localDensity M L m z) (localCoefficient M L m z) y0 ρ0 c s0 s1 hs q B
    hCm.le hCc.le hCh.le (hmom L m z) (hcmom L m z) (hhmom L m z)

end SubdiffusiveProcess.Static
