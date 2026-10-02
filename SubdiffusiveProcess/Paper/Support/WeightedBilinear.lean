import SubdiffusiveProcess.Paper.prop_21





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- Polarization upgrades the actual weighted diagonal energy identity to
its bilinear energy-measure identity on the native form domain. -/
theorem aux_mfd_prop_21_weighted_bilinear
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (E Erho : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE Grho : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ u, E.energy u = limitFormEnergy GE u)
    (hrhoform : ∀ u, Erho.energy u = limitFormEnergy Grho u)
    (GammaE : DirichletForm.EnergyMeasure E)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (hdomGrho : limitFormDomain Grho = limitFormDomain GE)
    (hGrhoEnergy : ∀ u ∈ limitFormDomain GE,
      limitFormEnergy Grho u = (((∫ x in (Q : Set (SpatialCoordinates d)),
        rho x ∂(GammaE.measure u)) : ℝ) : EReal)) :
    ∀ u ∈ limitFormDomain GE, ∀ v ∈ limitFormDomain GE,
      Erho.form u v = DirichletForm.signedIntegralOn (GammaE.cross u v)
        (Q : Set (SpatialCoordinates d)) rho := by
  have hbilinear : ∀ u ∈ limitFormDomain GE, ∀ v ∈ limitFormDomain GE,
      Erho.form u v =
        DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho := by
    have mem_domain_of_energy_eq : ∀ (u : DomainL2 Q),
        Erho.energy u < (⊤ : EReal) → u ∈ Erho.domain := by
      intro u hu
      by_contra hnot
      have htop : Erho.energy u = (⊤ : EReal) := by
        simp [DirichletForm.ClosedForm.energy, hnot]
      exact (ne_of_lt hu) (by simpa [htop] using (hrhoform u).symm)
    have hdiag : ∀ u ∈ limitFormDomain GE,
        Erho.form u u =
          ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u) := by
      intro u hu
      have huG : u ∈ limitFormDomain Grho := hdomGrho ▸ hu
      have huE : Erho.energy u < (⊤ : EReal) := by
        rw [hrhoform u]
        exact huG
      have huD : u ∈ Erho.domain := mem_domain_of_energy_eq u huE
      have he : ((Erho.form u u : ℝ) : EReal) =
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
            : EReal) := by
        calc
          ((Erho.form u u : ℝ) : EReal) = Erho.energy u := by
            simp [DirichletForm.ClosedForm.energy, huD]
          _ = limitFormEnergy Grho u := hrhoform u
          _ = (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
            : EReal) := hGrhoEnergy u hu
      exact_mod_cast he
    have mem_E_domain_of_energy_eq : ∀ (u : DomainL2 Q),
        E.energy u < (⊤ : EReal) → u ∈ E.domain := by
      intro u hu
      by_contra hnot
      have htop : E.energy u = (⊤ : EReal) := by
        simp [DirichletForm.ClosedForm.energy, hnot]
      exact (ne_of_lt hu) (by simpa [htop] using (hEform u).symm)
    have hGE_add : ∀ u v : DomainL2 Q, u ∈ limitFormDomain GE →
        v ∈ limitFormDomain GE → u + v ∈ limitFormDomain GE := by
      intro u v hu hv
      have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
        rw [hEform u]
        exact hu)
      have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
        rw [hEform v]
        exact hv)
      have huvE : u + v ∈ E.domain := E.domain.add_mem huE hvE
      change limitFormEnergy GE (u + v) < (⊤ : EReal)
      rw [← hEform (u + v)]
      simp [DirichletForm.ClosedForm.energy, huvE]
    have hGE_sub : ∀ u v : DomainL2 Q, u ∈ limitFormDomain GE →
        v ∈ limitFormDomain GE → u - v ∈ limitFormDomain GE := by
      intro u v hu hv
      have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
        rw [hEform u]
        exact hu)
      have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
        rw [hEform v]
        exact hv)
      have huvE : u - v ∈ E.domain := E.domain.sub_mem huE hvE
      change limitFormEnergy GE (u - v) < (⊤ : EReal)
      rw [← hEform (u - v)]
      simp [DirichletForm.ClosedForm.energy, huvE]
    intro u hu v hv
    have huG : u ∈ limitFormDomain Grho := hdomGrho ▸ hu
    have hvG : v ∈ limitFormDomain Grho := hdomGrho ▸ hv
    have huD : u ∈ Erho.domain := by
      apply mem_domain_of_energy_eq u
      rw [hrhoform u]
      exact huG
    have hvD : v ∈ Erho.domain := by
      apply mem_domain_of_energy_eq v
      rw [hrhoform v]
      exact hvG
    have huvD : u + v ∈ Erho.domain := Erho.domain.add_mem huD hvD
    have huvG : u + v ∈ limitFormDomain GE := hGE_add u v hu hv
    have humvD : u - v ∈ Erho.domain := Erho.domain.sub_mem huD hvD
    have humvG : u - v ∈ limitFormDomain GE := hGE_sub u v hu hv
    have hformpolar : Erho.form u v =
        (Erho.form (u + v) (u + v) - Erho.form (u - v) (u - v)) / 4 := by
      have hplus : Erho.form (u + v) (u + v) =
          Erho.form u u + 2 * Erho.form u v + Erho.form v v := by
        calc
          Erho.form (u + v) (u + v) =
              Erho.form u (u + v) + Erho.form v (u + v) :=
            Erho.form_add_left u huD v hvD (u + v) huvD
          _ = Erho.form (u + v) u + Erho.form (u + v) v := by
            rw [Erho.form_symm u huD (u + v) huvD,
              Erho.form_symm v hvD (u + v) huvD]
          _ = (Erho.form u u + Erho.form v u) +
              (Erho.form u v + Erho.form v v) := by
            rw [Erho.form_add_left u huD v hvD u huD,
              Erho.form_add_left u huD v hvD v hvD]
          _ = Erho.form u u + 2 * Erho.form u v + Erho.form v v := by
            rw [Erho.form_symm v hvD u huD]
            ring
      have hminus : Erho.form (u - v) (u - v) =
          Erho.form u u - 2 * Erho.form u v + Erho.form v v := by
        have hneg : (-v : DomainL2 Q) ∈ Erho.domain := Erho.domain.neg_mem hvD
        have hsumneg : u + (-v : DomainL2 Q) ∈ Erho.domain := Erho.domain.add_mem huD hneg
        have hneg_u : Erho.form (-v) u = -Erho.form v u := by
          simpa using (Erho.form_smul_left (-1) v hvD u huD)
        have hv_neg : Erho.form v (-v) = -Erho.form v v := by
          calc
            Erho.form v (-v) = Erho.form (-v) v := Erho.form_symm v hvD (-v) hneg
            _ = -Erho.form v v := by
              simpa using (Erho.form_smul_left (-1) v hvD v hvD)
        have hu_neg : Erho.form u (-v) = -Erho.form u v := by
          calc
            Erho.form u (-v) = Erho.form (-v) u := Erho.form_symm u huD (-v) hneg
            _ = -Erho.form v u := hneg_u
            _ = -Erho.form u v := by rw [Erho.form_symm v hvD u huD]
        have hneg_neg : Erho.form (-v) (-v) = Erho.form v v := by
          calc
            Erho.form (-v) (-v) = -Erho.form v (-v) := by
              simpa using (Erho.form_smul_left (-1) v hvD (-v) hneg)
            _ = Erho.form v v := by rw [hv_neg]; ring
        calc
          Erho.form (u - v) (u - v) =
              Erho.form (u + (-v)) (u + (-v)) := by rw [sub_eq_add_neg]
          _ = Erho.form u (u + (-v)) + Erho.form (-v) (u + (-v)) :=
            Erho.form_add_left u huD (-v) hneg (u + (-v)) hsumneg
          _ = Erho.form (u + (-v)) u + Erho.form (u + (-v)) (-v) := by
            rw [Erho.form_symm u huD (u + (-v)) hsumneg,
              Erho.form_symm (-v) hneg (u + (-v)) hsumneg]
          _ = (Erho.form u u + Erho.form (-v) u) +
              (Erho.form u (-v) + Erho.form (-v) (-v)) := by
            rw [Erho.form_add_left u huD (-v) hneg u huD,
              Erho.form_add_left u huD (-v) hneg (-v) hneg]
          _ = Erho.form u u - 2 * Erho.form u v + Erho.form v v := by
            rw [hneg_u, hu_neg, hneg_neg, Erho.form_symm v hvD u huD]
            ring
      rw [hplus, hminus]
      ring
    have hQcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
      rw [hQcube]
      exact (centeredCube_isBounded z0 hR).isCompact_closure
    have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
      rw [hEform u]
      exact hu)
    have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
      rw [hEform v]
      exact hv)
    have huvE : u + v ∈ E.domain := E.domain.add_mem huE hvE
    have humvE : u - v ∈ E.domain := E.domain.sub_mem huE hvE
    letI : IsFiniteMeasure (GammaE.measure (u + v)) :=
      ⟨GammaE.measure_univ_lt_top (u + v) huvE⟩
    letI : IsFiniteMeasure (GammaE.measure (u - v)) :=
      ⟨GammaE.measure_univ_lt_top (u - v) humvE⟩
    have hcrossplus : GammaE.cross (u + v) (u + v) =
        (GammaE.measure (u + v)).toSignedMeasure := by
      ext B hB
      rw [GammaE.cross_self (u + v) huvE B hB,
        Measure.toSignedMeasure_apply_measurable hB]
      rfl
    have hcrossminus : GammaE.cross (u - v) (u - v) =
        (GammaE.measure (u - v)).toSignedMeasure := by
      ext B hB
      rw [GammaE.cross_self (u - v) humvE B hB,
        Measure.toSignedMeasure_apply_measurable hB]
      rfl
    have hplusInt : Integrable rho
        ((GammaE.measure (u + v)).restrict (Q : Set (SpatialCoordinates d))) := by
      exact (hrhocont.integrableOn_compact (μ := GammaE.measure (u + v)) hQcompact).integrable.mono_measure
        (Measure.restrict_mono_set _ subset_closure)
    have hminusInt : Integrable rho
        ((GammaE.measure (u - v)).restrict (Q : Set (SpatialCoordinates d))) := by
      exact (hrhocont.integrableOn_compact (μ := GammaE.measure (u - v)) hQcompact).integrable.mono_measure
        (Measure.restrict_mono_set _ subset_closure)
    have hcrosspolar : GammaE.cross u v =
        (1 / 4 : ℝ) •
          (GammaE.cross (u + v) (u + v) - GammaE.cross (u - v) (u - v)) := by
      ext B hB
      rw [GammaE.cross_eq_polarization huE hvE B]
      simp [VectorMeasure.sub_apply, smul_eq_mul]
      ring
    have hcrossint : DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho =
        (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u + v)) -
          ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - v))) / 4 := by
      rw [hcrosspolar,
        aux_prop_21_signedIntegralOn_nonneg_smul _ _ (by norm_num)]
      rw [hcrossplus, hcrossminus]
      rw [aux_prop_21_signedIntegralOn_toSignedMeasure_sub
        (GammaE.measure (u + v)) (GammaE.measure (u - v))
        (Q : Set (SpatialCoordinates d)) (Q.isOpen.measurableSet) rho hplusInt hminusInt]
      ring
    calc
      Erho.form u v =
          (Erho.form (u + v) (u + v) - Erho.form (u - v) (u - v)) / 4 := hformpolar
      _ =
          (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u + v)) -
            ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - v))) / 4 := by
        rw [hdiag (u + v) huvG, hdiag (u - v) humvG]
      _ = DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho := hcrossint.symm
  exact hbilinear

end SubdiffusiveProcess.AuditRepairs
