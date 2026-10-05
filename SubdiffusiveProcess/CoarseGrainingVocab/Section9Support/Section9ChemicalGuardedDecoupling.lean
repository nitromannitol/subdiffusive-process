module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTruncationTail


@[expose] public section

/-!
# Guarded finite-scale decoupling

The large-distance guard  is retained.
`exists_drsConditionP3Guarded` constructs independent event replacements and a
uniform natural threshold for the original event-probability hypotheses. It
uses no approximation or decoupling hypothesis.

This module treats the sigma-algebras of the original event generators whose
centres lie in the two balls. Applying it to good-site indicators also requires
accounting for the spatial influence boxes; those indicators involve centres
outside the ball. The distinction is explicit in `DRSConditionP3Guarded`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MeasureTheory Set ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section

/-- Finite-scale decoupling above a prescribed distance guard. -/
def DRSConditionP3Guarded {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cdep R0 : ℕ) (cP : ℝ) : Prop :=
  ∀ (L R : ℕ), 1 ≤ L → R0 ≤ R →
    ∀ (A B : Set Ω) (x1 x2 : Lattice d),
      R * L ≤ latticeDist x1 x2 →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B →
      ∃ (j0 : ℕ) (A' B' : Set Ω),
        100 * (Cdep * 3 ^ j0) ≤ R * L ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A' ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B' ∧
        mu (A' \ A) + mu (A \ A') + mu (B' \ B) + mu (B \ B') ≤
          ENNReal.ofReal (Real.exp (-(cP * ((R * L : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) ∧
        mu (A' ∩ B') = mu A' * mu B'


/-- Independent replacements with the full stretched-exponential error bound. -/
theorem drsConditionP3Guarded_of_probability {d Cdep : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales μ E)
    (hr : MultiscaleFiniteRangeIndependentEvents μ (fun j => Cdep*3^j) E)
    {Cp A : ℝ} (hCp : 0 ≤ Cp) (hA : Real.log 2 ≤ A)
    (hp : ∀ j z, μ (E j z) ≤ ENNReal.ofReal (Cp*Real.exp (-(A*3^((3:ℝ)*j/2)))))
    (habs : 2*(Real.log (max 1 (4*Cp*(21:ℝ)^d))+d) ≤ A/((100*(Cdep+1):ℕ):ℝ)^((3:ℝ)/2)) :
    DRSConditionP3Guarded μ E Cdep (100*(Cdep+1))
      (A/(2*((100*(Cdep+1):ℕ):ℝ)^((3:ℝ)/2))) := by
  intro L R hL hR U V x y hxy hU hV
  obtain ⟨j, _hlower, hupper, hcut, hsep⟩ := guarded_cutoff hL hR
  obtain ⟨U', hU', heU⟩ :=
    exists_event_truncation_measure μ E (latticeBallFinset x (10*L)) j hE hU
  obtain ⟨V', hV', heV⟩ :=
    exists_event_truncation_measure μ E (latticeBallFinset y (10*L)) j hE hV
  have hi := indep_event_truncations_of_separated_balls μ E hE hsc hr (hsep.trans_le hxy)
  refine ⟨j, U', V', hcut, hU', hV', ?_, (Indep_iff _ _ _).mp hi U' V' hU' hV'⟩
  let T : ℝ≥0∞ := ENNReal.ofReal
    (2*((((20*L+1)^d:ℕ):ℝ)*Cp)*Real.exp (-(A*3^((3:ℝ)*(j+1)/2))))
  have ht : ∀ z : Lattice d,
      (∑' n : ℕ, ∑ u ∈ latticeBallFinset z (10*L), μ (E (n+j+1) u)) ≤ T := by
    intro z
    have h := finite_event_tail_le μ E (latticeBallFinset z (10*L)) hCp hA j hp
    simpa only [card_latticeBallFinset, show 2*(10*L)+1 = 20*L+1 by omega] using h
  refine (two_errors_le (heU.trans (ht x)) (heV.trans (ht y))).trans ?_
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  dsimp [T]
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd := two_ball_tail_decay hCp hA d L R (100*(Cdep+1)) j hL
    (by omega) (by omega) hupper habs
  convert hd using 1
  ring

/-- A natural threshold absorbs the entropy uniformly in the radius. -/
theorem exists_decoupling_threshold (d D : ℕ) (Cp c : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∃ q0 : ℕ, ∀ q : ℝ, (q0 : ℝ) ≤ q →
      Real.log 2 ≤ c*q ∧
      2*(Real.log (max 1 (4*Cp*(21:ℝ)^d))+d) ≤ c*q/(D:ℝ)^((3:ℝ)/2) := by
  set X : ℝ := max (Real.log 2)
      (2*(Real.log (max 1 (4*Cp*(21:ℝ)^d))+d)*(D:ℝ)^((3:ℝ)/2)) with hX
  obtain ⟨q0, hq⟩ := exists_uniform_threshold (X := X) hc
  refine ⟨q0, fun q hq0 => ?_⟩
  have hXq : X ≤ c*q := hq q hq0
  have h1 : Real.log 2 ≤ c*q := (le_max_left _ _).trans hXq
  refine ⟨h1, ?_⟩
  have hDp : (0:ℝ) < (D:ℝ)^((3:ℝ)/2) := by positivity
  have h2 : 2*(Real.log (max 1 (4*Cp*(21:ℝ)^d))+d)*(D:ℝ)^((3:ℝ)/2) ≤ c*q :=
    (le_max_right _ _).trans hXq
  exact (le_div_iff₀ hDp).mpr h2

/-- Guarded P3 with constants uniform over all admissible fields and all radii. -/
theorem exists_drsConditionP3Guarded (d Cdep : ℕ) (Cprob cprob : ℝ)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ cP : ℝ, 0 < cP ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : ℕ → Lattice d → Set Ω) (q : ℝ), (q0 : ℝ) ≤ q →
        (∀ j z, μ (E j z) ≤
          ENNReal.ofReal (Cprob*Real.exp (-cprob*q*3^((3:ℝ)*j/2)))) →
        IndependentEventScales μ E →
        MultiscaleFiniteRangeIndependentEvents μ (fun j => Cdep*3^j) E →
        TranslationInvariantEventLaw μ E →
        DRSConditionP3Guarded μ E Cdep (100*(Cdep+1)) (cP*q) := by
  let D : ℕ := 100*(Cdep+1)
  have hD : 0 < D := by dsimp [D]; omega
  obtain ⟨q0, hq0⟩ := exists_decoupling_threshold d D Cprob cprob hcprob hD
  refine ⟨q0, cprob/(2*(D:ℝ)^((3:ℝ)/2)), by positivity, ?_⟩
  intro Ω _ μ _ E q hq hp hsc hr hlaw
  obtain ⟨hlog, habs⟩ := hq0 q hq
  have hp' : ∀ j z, μ (E j z) ≤
      ENNReal.ofReal (Cprob*Real.exp (-((cprob*q)*3^((3:ℝ)*j/2)))) := by
    intro j z
    simpa only [neg_mul] using hp j z
  have h := drsConditionP3Guarded_of_probability μ E hlaw.1 hsc hr hCprob.le hlog hp' habs
  convert h using 1
  dsimp [D]
  ring

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
