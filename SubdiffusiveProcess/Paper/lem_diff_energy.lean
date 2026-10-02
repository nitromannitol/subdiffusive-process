import SubdiffusiveProcess.Paper.lem_diff_euler
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane3.DiffCauchySchwarz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

private theorem aux_lem_diff_energy_unit_set_cases (s : Set Unit) :
    s = ∅ ∨ s = Set.univ := by
  rcases Set.eq_empty_or_nonempty s with hs | hs
  · exact Or.inl hs
  · right
    apply Set.eq_univ_of_univ_subset
    intro x hx
    rcases hs with ⟨y, hy⟩
    convert hy using 1

private def aux_lem_diff_energy_local
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} (E : DirichletForm.ClosedForm m)
    (Gamma : DirichletForm.EnergyMeasure E)
    (D : Submodule ℝ (Lp ℝ 2 m))
    (hD : ∀ u : D, (u : Lp ℝ 2 m) ∈ E.domain)
    (B : Set X) (hB : MeasurableSet B) :
    SubdiffusiveProcess.Lane3.LocalEnergy D Unit := by
  classical
  exact
    { gam := fun u v s =>
        if s = Set.univ then Gamma.cross (u : Lp ℝ 2 m) (v : Lp ℝ 2 m) B else 0
      gam_symm := by
        intro u v s
        by_cases hs : s = Set.univ
        · rw [if_pos hs, if_pos hs]
          exact congrArg (fun ν : SignedMeasure X => ν B)
            (Gamma.cross_symm (u : Lp ℝ 2 m) (hD u) (v : Lp ℝ 2 m) (hD v))
        · rw [if_neg hs, if_neg hs]
      gam_add_left := by
        intro u v w s
        by_cases hs : s = Set.univ
        · rw [if_pos hs, if_pos hs, if_pos hs]
          simpa only [VectorMeasure.add_apply] using
            congrArg (fun ν : SignedMeasure X => ν B)
              (Gamma.cross_add_left (hD u) (hD v) (hD w))
        · rw [if_neg hs, if_neg hs, if_neg hs]
          exact (zero_add 0).symm
      gam_smul_left := by
        intro c u v s
        by_cases hs : s = Set.univ
        · rw [if_pos hs, if_pos hs]
          simpa only [VectorMeasure.smul_apply, smul_eq_mul] using
            congrArg (fun ν : SignedMeasure X => ν B)
              (Gamma.cross_smul_left c (hD u) (hD v))
        · rw [if_neg hs, if_neg hs]
          simp
      gam_nonneg := by
        intro u s
        have hdiag : 0 ≤ Gamma.cross (u : Lp ℝ 2 m) (u : Lp ℝ 2 m) B := by
          rw [Gamma.cross_self (u : Lp ℝ 2 m) (hD u) B hB]
          exact ENNReal.toReal_nonneg
        by_cases hs : s = Set.univ
        · rw [if_pos hs]
          exact hdiag
        · rw [if_neg hs]
      gam_mono := by
        intro u s t hst
        have hdiag : 0 ≤ Gamma.cross (u : Lp ℝ 2 m) (u : Lp ℝ 2 m) B := by
          rw [Gamma.cross_self (u : Lp ℝ 2 m) (hD u) B hB]
          exact ENNReal.toReal_nonneg
        have hne : (∅ : Set Unit) ≠ Set.univ := by
          intro h
          have hempty : (default : Unit) ∈ (∅ : Set Unit) := by
            rw [h]
            trivial
          exact hempty
        rcases aux_lem_diff_energy_unit_set_cases s with rfl | rfl <;>
          rcases aux_lem_diff_energy_unit_set_cases t with rfl | rfl
        · rfl
        · rw [if_neg hne, if_pos rfl]
          exact hdiag
        · simp at hst
        · rfl
      gam_add_disjoint := by
        intro u v s t hs ht hdisj
        have hne : (∅ : Set Unit) ≠ Set.univ := by
          intro h
          have hempty : (default : Unit) ∈ (∅ : Set Unit) := by
            rw [h]
            trivial
          exact hempty
        rcases aux_lem_diff_energy_unit_set_cases s with rfl | rfl <;>
          rcases aux_lem_diff_energy_unit_set_cases t with rfl | rfl <;>
          simp_all
    }



theorem lem_diff_energy
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ) :
    let Q : Opens (SpatialCoordinates d) := centeredCube zQ rQ hrQ
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      let q : Opens (SpatialCoordinates d) := centeredCube z r hr
      ∀ (hinside : closure (q : Set (SpatialCoordinates d)) ⊆
          (Q : Set (SpatialCoordinates d)))
        (E F : DirichletForm.ClosedForm
          (volume.restrict (Q : Set (SpatialCoordinates d))))
        (GammaE : DirichletForm.EnergyMeasure E)
        (GammaF : DirichletForm.EnergyMeasure F)
        (hdom : E.domain = F.domain)
        (V0 : Submodule ℝ (DomainL2 Q))
        (hzero : DirichletForm.IsKilledDomain E
          (q : Set (SpatialCoordinates d)) V0)
        (m M c : ℝ) (hm : 0 < m) (hmc : m ≤ c) (hcM : c ≤ M)
        (horder : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
          MeasurableSet A →
            m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
              (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal)
        (uE uF : DomainL2 Q)
        (huE : uE ∈ E.domain) (huF : uF ∈ F.domain)
        (htrace : uF - uE ∈ V0)
        (hEuler : ∀ v ∈ V0,
          (GammaF.cross (uF - uE) v) (q : Set (SpatialCoordinates d)) =
            -((GammaF.cross uE v) (q : Set (SpatialCoordinates d)) -
              c * (GammaE.cross uE v) (q : Set (SpatialCoordinates d)))),
      (GammaE.measure (uF - uE) (q : Set (SpatialCoordinates d))).toReal ≤
        ((M - m) / m) ^ (2 : ℕ) *
          (GammaE.measure uE (q : Set (SpatialCoordinates d))).toReal := by
  dsimp
  intro z r hr hinside E F GammaE GammaF hdom V0 hzero m M c hm hmc hcM
    horder uE uF huE huF htrace hEuler
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hwE : uF - uE ∈ E.domain := hzero.le_domain htrace
  have hFmem : ∀ x : E.domain,
      (x : DomainL2 (centeredCube zQ rQ hrQ)) ∈ F.domain := by
    intro x
    rw [← hdom]
    exact x.property
  let ue : E.domain := ⟨uE, huE⟩
  let w : E.domain := ⟨uF - uE, hwE⟩
  let EE : SubdiffusiveProcess.Lane3.LocalEnergy E.domain Unit :=
    aux_lem_diff_energy_local E GammaE E.domain (fun x => x.property)
      (centeredCube z r hr : Set (SpatialCoordinates d)) hq
  let FF : SubdiffusiveProcess.Lane3.LocalEnergy E.domain Unit :=
    aux_lem_diff_energy_local F GammaF E.domain hFmem
      (centeredCube z r hr : Set (SpatialCoordinates d)) hq
  have hcoercive : m * EE.form w w ≤ FF.form w w := by
    dsimp [EE, FF, SubdiffusiveProcess.Lane3.LocalEnergy.form,
      aux_lem_diff_energy_local, w]
    simp only [if_pos rfl]
    change m * GammaE.cross (uF - uE) (uF - uE)
        (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      GammaF.cross (uF - uE) (uF - uE)
        (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [GammaE.cross_self (uF - uE) hwE _ hq,
      GammaF.cross_self (uF - uE) (hFmem w) _ hq]
    exact (horder (uF - uE) hwE (centeredCube z r hr : Set (SpatialCoordinates d)) hq).1
  have hlower : ∀ (x : E.domain) (s : Set Unit), MeasurableSet s →
      m * EE.gam x x s ≤ FF.gam x x s := by
    intro x s hs
    by_cases hsu : s = Set.univ
    · subst s
      dsimp [EE, FF, aux_lem_diff_energy_local]
      simp only [if_pos rfl]
      change m * GammaE.cross (x : DomainL2 (centeredCube zQ rQ hrQ))
          (x : DomainL2 (centeredCube zQ rQ hrQ))
          (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        GammaF.cross (x : DomainL2 (centeredCube zQ rQ hrQ))
          (x : DomainL2 (centeredCube zQ rQ hrQ))
          (centeredCube z r hr : Set (SpatialCoordinates d))
      rw [GammaE.cross_self (x : DomainL2 (centeredCube zQ rQ hrQ)) x.property _ hq,
        GammaF.cross_self (x : DomainL2 (centeredCube zQ rQ hrQ)) (hFmem x) _ hq]
      exact (horder (x : DomainL2 (centeredCube zQ rQ hrQ)) x.property
        (centeredCube z r hr : Set (SpatialCoordinates d)) hq).1
    · simp [EE, FF, aux_lem_diff_energy_local, hsu]
  have hupper : ∀ (x : E.domain) (s : Set Unit), MeasurableSet s →
      FF.gam x x s ≤ M * EE.gam x x s := by
    intro x s hs
    by_cases hsu : s = Set.univ
    · subst s
      dsimp [EE, FF, aux_lem_diff_energy_local]
      simp only [if_pos rfl]
      change GammaF.cross (x : DomainL2 (centeredCube zQ rQ hrQ))
          (x : DomainL2 (centeredCube zQ rQ hrQ))
          (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        M * GammaE.cross (x : DomainL2 (centeredCube zQ rQ hrQ))
          (x : DomainL2 (centeredCube zQ rQ hrQ))
          (centeredCube z r hr : Set (SpatialCoordinates d))
      rw [GammaF.cross_self (x : DomainL2 (centeredCube zQ rQ hrQ)) (hFmem x) _ hq,
        GammaE.cross_self (x : DomainL2 (centeredCube zQ rQ hrQ)) x.property _ hq]
      exact (horder (x : DomainL2 (centeredCube zQ rQ hrQ)) x.property
        (centeredCube z r hr : Set (SpatialCoordinates d)) hq).2
    · simp [EE, FF, aux_lem_diff_energy_local, hsu]
  have hcs0 :=
    SubdiffusiveProcess.Lane3.diff_measure_cauchy_schwarz EE FF m M c hmc hcM
      hlower hupper ue w Set.univ MeasurableSet.univ
  have hCS :
      |FF.form ue w - c * EE.form ue w| ≤
        (M - m) * Real.sqrt (EE.form ue ue * EE.form w w) := by
    simpa [SubdiffusiveProcess.Lane3.LocalEnergy.diffGam,
      SubdiffusiveProcess.Lane3.LocalEnergy.form] using hcs0
  have heuler' : FF.form w w = -(FF.form ue w - c * EE.form ue w) := by
    simpa [EE, FF, ue, w, SubdiffusiveProcess.Lane3.LocalEnergy.form,
      aux_lem_diff_energy_local] using (hEuler (uF - uE) htrace)
  have hmain :=
    SubdiffusiveProcess.Lane3.minimizer_difference_energy_le EE FF m M c hm hmc hcM
      ue w hcoercive heuler' hCS
  have hmain' :
      GammaE.cross (uF - uE) (uF - uE)
          (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        ((M - m) / m) ^ (2 : ℕ) *
          GammaE.cross uE uE (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    simpa [EE, ue, w, SubdiffusiveProcess.Lane3.LocalEnergy.form,
      aux_lem_diff_energy_local] using hmain
  rw [GammaE.cross_self (uF - uE) hwE _ hq,
    GammaE.cross_self uE huE _ hq] at hmain'
  exact hmain'

end
end Paper
