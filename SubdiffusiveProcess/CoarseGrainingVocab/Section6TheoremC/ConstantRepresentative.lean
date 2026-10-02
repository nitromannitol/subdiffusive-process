import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- An almost-everywhere equality restricts to any subset. -/
theorem eventuallyEq_restrict {f g : Vec d → ℝ} (h : f =ᵐ[volume] g)
    (W : Set (Vec d)) : f =ᵐ[volume.restrict W] g :=
  h.filter_mono (ae_mono Measure.restrict_le_self)

/-- **S12.**  An almost-everywhere constant function has a continuous
representative that is constant and agrees with every pointwise-equal local
witness almost everywhere on that witness's window.

Stated for an arbitrary window and an arbitrary pointwise-equal companion, so
that it applies verbatim to the frozen clause's `H1Function` witnesses. -/
theorem exists_constant_continuous_representative {u : Vec d → ℝ} {c : ℝ}
    (hu : u =ᵐ[volume] fun _ ↦ c) :
    ∃ uRep : Vec d → ℝ,
      Continuous uRep ∧
      uRep =ᵐ[volume] u ∧
      (∀ (W : Set (Vec d)) (g : Vec d → ℝ), (∀ x, g x = u x) →
        uRep =ᵐ[volume.restrict W] g) ∧
      ∃ c' : ℝ, ∀ x, uRep x = c' := by
  refine ⟨fun _ ↦ c, continuous_const, hu.symm, ?_, c, fun _ ↦ rfl⟩
  intro W g hg
  have hgu : g = u := funext hg
  rw [hgu]
  exact eventuallyEq_restrict hu.symm W

/-- The same conclusion in the exact shape of the frozen Liouville clause: the
coherence conjunct is quantified over the `H1Function` witnesses `um` on the
centered cubes, and carries a harmonicity hypothesis which is not needed. -/
theorem exists_constant_continuous_representative_frozenShape
    {u : Vec d → ℝ} {c : ℝ} (hu : u =ᵐ[volume] fun _ ↦ c)
    (P : ∀ m : ℤ, H1Function (openCubeSet (originCube d m)) → Prop) :
    ∃ uRep : Vec d → ℝ,
      Continuous uRep ∧
      uRep =ᵐ[volume] u ∧
      (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
        (∀ x, um.toFun x = u x) → P m um →
        uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
      ∃ c' : ℝ, ∀ x, uRep x = c' := by
  obtain ⟨uRep, hcont, hae, hcoh, hconst⟩ :=
    exists_constant_continuous_representative hu
  refine ⟨uRep, hcont, hae, ?_, hconst⟩
  intro m um hum _
  exact hcoh (openCubeSet (originCube d m)) um.toFun hum

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
