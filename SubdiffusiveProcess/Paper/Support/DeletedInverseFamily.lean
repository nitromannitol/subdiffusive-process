module

public import SubdiffusiveProcess.Paper.Support.BorelWeightedInverse

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.AuditRepairs

/-- Actual form and inverse constructed from one base form and one continuous log weight. -/
structure DeletedInverseData {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (ell : SpatialCoordinates d → ℝ) where
  form : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  gamma : DirichletForm.EnergyMeasure form.toClosedForm
  operator : DomainL2 Q →L[ℝ] DomainL2 Q
  domain_eq : form.domain = E.domain
  resolvent : DirichletForm.IsResolvent form.toClosedForm 0 operator
  symmetric : ∀ f g : DomainL2 Q, inner ℝ f (operator g) = inner ℝ (operator f) g
  injective : Function.Injective operator
  inverse : ∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ u : DomainL2 Q,
    u ∈ E.domain ∧ t = 2 * inner ℝ f u -
      ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂Gamma.measure u}
    (inner ℝ f (operator f))
  energy_eq : ∀ u : DomainL2 Q, form.energy u = limitFormEnergy operator u
  bilinear : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    form.form u v = DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
      (fun x => Real.exp (-ell x))
  regular : DirichletForm.IsRegular form.toClosedForm
  locality : DirichletForm.IsStronglyLocal form.toClosedForm
  cross : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ B : Set (SpatialCoordinates d),
    MeasurableSet B → gamma.cross u v B = DirichletForm.signedIntegralOn
      (Gamma.cross u v) B (fun x => Real.exp (-ell x))
  diagonal : ∀ u ∈ E.domain, form.form u u =
    ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell x) ∂Gamma.measure u

theorem exists_deleted_inverse_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (Gbase : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hbase : ∀ u, E.energy u = limitFormEnergy Gbase u)
    (hcore : ∃ C : Set (DomainL2 Q), DirichletForm.IsCoreOn E.toClosedForm (Q : Set _) C)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hsupp : ∀ u ∈ E.domain, Gamma.measure u (Q : Set _)ᶜ = 0)
    (ell : SpatialCoordinates d → ℝ)
    (hell : ContinuousOn ell (closure (Q : Set _)) ∧ ∃ K : ℝ, ∀ x ∈ (Q : Set _), |ell x| ≤ K) :
    Nonempty (DeletedInverseData Q E Gamma ell) := by
  obtain ⟨D, ΓD, G, hdom, hres, hsym, hinj, hinv, henergy, hbil, hreg, hlocal,
    hcross, hdiag⟩ := weighted_inverse_exists Q E Gamma Gbase hbase hcore hloc hsupp ell hell
  exact ⟨⟨D, ΓD, G, hdom, hres, hsym, hinj, hinv, henergy, hbil, hreg, hlocal, hcross, hdiag⟩⟩

/-- Pointwise choice gives one original-space inverse family and its full data on
the unweighted good event, before proving its convergence or measurability. -/
theorem exists_deleted_inverse_family
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : Ω → _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, DirichletForm.EnergyMeasure (E ω).toClosedForm)
    (Gbase : Ω → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hbase : ∀ᵐ ω ∂P, ∀ u, (E ω).energy u = limitFormEnergy (Gbase ω) u)
    (hregular : ∀ᵐ ω ∂P,
      (∃ C : Set (DomainL2 Q), DirichletForm.IsCoreOn (E ω).toClosedForm (Q : Set _) C) ∧
      DirichletForm.IsStronglyLocal (E ω).toClosedForm ∧
      (∀ u ∈ (E ω).domain, (Gamma ω).measure u (Q : Set _)ᶜ = 0))
    (ell : Ω → SpatialCoordinates d → ℝ)
    (hell : ∀ ω, ContinuousOn (ell ω) (closure (Q : Set _)) ∧
      ∃ K : ℝ, ∀ x ∈ (Q : Set _), |ell ω x| ≤ K) :
    ∃ G : Ω → DomainL2 Q →L[ℝ] DomainL2 Q,
      ∀ᵐ ω ∂P, ∃ D : DeletedInverseData Q (E ω) (Gamma ω) (ell ω), D.operator = G ω := by
  classical
  let good : Ω → Prop := fun ω =>
    (∀ u, (E ω).energy u = limitFormEnergy (Gbase ω) u) ∧
    (∃ C : Set (DomainL2 Q), DirichletForm.IsCoreOn (E ω).toClosedForm (Q : Set _) C) ∧
    DirichletForm.IsStronglyLocal (E ω).toClosedForm ∧
    (∀ u ∈ (E ω).domain, (Gamma ω).measure u (Q : Set _)ᶜ = 0)
  have hchoice : ∀ ω, ∃ G : DomainL2 Q →L[ℝ] DomainL2 Q,
      good ω → ∃ D : DeletedInverseData Q (E ω) (Gamma ω) (ell ω), D.operator = G := by
    intro ω
    by_cases hg : good ω
    · obtain ⟨D⟩ := exists_deleted_inverse_data Q (E ω) (Gamma ω) (Gbase ω)
        hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (ell ω) (hell ω)
      exact ⟨D.operator, fun _ => ⟨D, rfl⟩⟩
    · exact ⟨0, fun hg' => False.elim (hg hg')⟩
  choose G hG using hchoice
  refine ⟨G, ?_⟩
  filter_upwards [hbase, hregular] with ω hb hr
  exact hG ω ⟨hb, hr⟩

end SubdiffusiveProcess.AuditRepairs
