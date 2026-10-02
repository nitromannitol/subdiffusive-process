import SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-! Transport energy-measure calculus across equal form domains and equal domain form values.
No equality of form values outside the domain is required or asserted. -/
open MeasureTheory Set
namespace DirichletForm
noncomputable section
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Equal diagonal energies on the same domain determine every bilinear value on that domain. -/
theorem ClosedForm.form_eq_of_diagonal_eq (E F : ClosedForm m)
    (hdom : E.domain = F.domain)
    (hdiag : ∀ u ∈ E.domain, E.form u u = F.form u u)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u v = F.form u v := by
  have hsum := hdiag (u + v) (E.domain.add_mem hu hv)
  rw [E.form_add_self hu hv, F.form_add_self (hdom ▸ hu) (hdom ▸ hv),
    hdiag u hu, hdiag v hv] at hsum
  linarith only [hsum]

/-- Two forms with a common domain and prescribed common diagonal have equal extended energies. -/
theorem ClosedForm.energy_eq_of_common_diagonal
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (E F H : DirichletForm.ClosedForm mu) (J : Lp ℝ 2 mu → ℝ)
    (hEF : E.domain = F.domain) (hEH : E.domain = H.domain)
    (hF : ∀ u ∈ E.domain, F.form u u = J u)
    (hH : ∀ u ∈ E.domain, H.form u u = J u) :
    ∀ u, F.energy u = H.energy u := by
  intro u
  by_cases hu : u ∈ E.domain
  · rw [F.energy_of_mem (hEF ▸ hu), H.energy_of_mem (hEH ▸ hu), hF u hu, hH u hu]
  · have huf : u ∉ F.domain := by rw [← hEF]; exact hu
    have huh : u ∉ H.domain := by rw [← hEH]; exact hu
    rw [F.energy_of_notMem huf, H.energy_of_notMem huh]

/-- Energy measures transport unchanged between forms that agree on their common domain. -/
def EnergyMeasure.ofFormEq {E F : ClosedForm m} (Gamma : EnergyMeasure E)
    (hdom : E.domain = F.domain)
    (hform : ∀ u ∈ E.domain, ∀ v ∈ E.domain, E.form u v = F.form u v) :
    EnergyMeasure F where
  measure := Gamma.measure
  cross := Gamma.cross
  measure_univ_lt_top := fun u hu => Gamma.measure_univ_lt_top u (hdom.symm ▸ hu)
  measure_univ := fun u hu => (Gamma.measure_univ u (hdom.symm ▸ hu)).trans
    (hform u (hdom.symm ▸ hu) u (hdom.symm ▸ hu))
  cross_symm := fun u hu v hv => Gamma.cross_symm u (hdom.symm ▸ hu) v (hdom.symm ▸ hv)
  cross_self := fun u hu => Gamma.cross_self u (hdom.symm ▸ hu)
  cross_add_right := fun u hu v hv w hw =>
    Gamma.cross_add_right u (hdom.symm ▸ hu) v (hdom.symm ▸ hv) w (hdom.symm ▸ hw)
  cross_smul_right := fun c u hu v hv => Gamma.cross_smul_right c u (hdom.symm ▸ hu) v (hdom.symm ▸ hv)
  cross_univ := fun u hu v hv =>
    (Gamma.cross_univ u (hdom.symm ▸ hu) v (hdom.symm ▸ hv)).trans
      (hform u (hdom.symm ▸ hu) v (hdom.symm ▸ hv))
  abs_cross_le := fun u hu v hv => Gamma.abs_cross_le u (hdom.symm ▸ hu) v (hdom.symm ▸ hv)
  locality := fun u hu v hv => Gamma.locality u (hdom.symm ▸ hu) v (hdom.symm ▸ hv)
  regular := fun u hu => Gamma.regular u (hdom.symm ▸ hu)
  measure_compl_tsupport := fun u hu => Gamma.measure_compl_tsupport u (hdom.symm ▸ hu)
  chain_rule := fun u hu uc huc hrep Phi hPhi hzero w hw =>
    Gamma.chain_rule u (hdom.symm ▸ hu) uc huc hrep Phi hPhi hzero w (hdom.symm ▸ hw)
  leibniz := fun u v hu hv uc vc huc hvc hurep hvrep Phi hPhi w hw =>
    Gamma.leibniz u v ⟨hdom.symm ▸ hu.1, hu.2⟩ ⟨hdom.symm ▸ hv.1, hv.2⟩
      uc vc huc hvc hurep hvrep Phi hPhi w (hdom.symm ▸ hw)
  defining_identity := by
    intro u phi hu hphi uc phic huc hphic hurep hphirep uphi u2 huphi hu2 huphirep hu2rep
    have hid := Gamma.defining_identity u phi
      ⟨hdom.symm ▸ hu.1, hu.2⟩ ⟨hdom.symm ▸ hphi.1, hphi.2⟩
      uc phic huc hphic hurep hphirep uphi u2 (hdom.symm ▸ huphi) (hdom.symm ▸ hu2)
      huphirep hu2rep
    rw [hform u (hdom.symm ▸ hu.1) uphi (hdom.symm ▸ huphi),
      hform u2 (hdom.symm ▸ hu2) phi (hdom.symm ▸ hphi.1)] at hid
    exact hid

end
end DirichletForm
