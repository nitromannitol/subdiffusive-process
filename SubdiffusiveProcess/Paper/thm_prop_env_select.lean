module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.thm_prop_env_endpoints

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

section FamilyNoHd

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}

/-- The remaining cell-selection content of a directed D.1.L branch (environment form: the limit
sides carry an arbitrary coefficient sequence). -/
def aux_thm_prop_env_fine_candidates (hd : 2 ≤ d) (m M : ℝ) : Prop :=
  ∀ᵐ om ∂P, ∀ i,
    ∀ (E : aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om) (aE i om))
      (F : aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GF i om) (aF i om)),
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
    ∀ hu : GE i om f ∈ E.form.domain,
    ∀ c : ℝ, 0 < c → Nonempty (aux_thm_prop_fine_cells
      (centeredCube (z i) (r i) (hr i)) E.form F.form E.gamma F.gamma m M
      ⟨GE i om f, hu⟩ c)


end FamilyNoHd

section Family

variable {d : ℕ} {hd : 2 ≤ d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}
    {m M : ℝ}

/-- Exact local-affine supplier target at the selected finite shifted grids (environment form). -/
def aux_thm_prop_env_source_cell_approximation
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω) : Prop :=
  ∀ᵐ om ∂P, ∀ jQ,
    ∀ E : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om) (aE jQ om),
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
    ∀ hu : GE jQ om f ∈ E.form.domain, ∀ c : ℝ, 0 < c →
    ∃ baseMesh : ℝ, 0 < baseMesh ∧
      ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let mu := E.gamma.measure (GE jQ om f) + ENNReal.ofReal c •
        volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
      (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
          (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
        (⇑(GE jQ om f) =ᵐ[volume.restrict
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
        aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
          E.form.toClosedForm E.gamma (GE jQ om f) U c
          (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
            (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
              Set (SpatialCoordinates d))


def aux_thm_prop_env_boundary_selection
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (Uset : ℕ → Prop) : Prop :=
  ∀ᵐ om ∂P, ∀ jQ,
    ∀ (E : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om) (aE jQ om))
      (F : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GF jQ om) (aF jQ om)),
    ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
    ∀ hu : GE jQ om f ∈ E.form.domain, ∀ c : ℝ, 0 < c →
    ∃ baseMesh : ℝ, 0 < baseMesh ∧
      ∀ (n : ℕ), 1 ≤ n → Uset n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
      ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let mu := E.gamma.measure (GE jQ om f) + ENNReal.ofReal c •
        volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
      (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
        ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
          (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
      Nonempty (aux_thm_prop_boundary_cell_data (centeredCube (z jQ) (r jQ) (hr jQ))
        E.form F.form E.gamma F.gamma m M ⟨GE jQ om f, hu⟩ c
        (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
          (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
            Set (SpatialCoordinates d)))

theorem aux_thm_prop_env_fine_candidates_from_boundary_selection
    (hm : 0 < m) (hM : 0 < M)
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (Uset : ℕ → Prop) (hU : (1 / 2 : ℝ) ≤ Lane3.upperDensity Uset)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hplanes : ∀ᵐ om ∂P, ∀ i,
      ∀ E : aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om) (aE i om), ∀ u ∈ E.form.domain,
        ∀ (j : Fin d) (a : ℝ), E.gamma.measure u {x | x j = a} = 0)
    (hbad : ∀ i, ∀ᵐ om ∂P, ∃ B : (Fin d → Fin g.Mm) → ℝ,
      (∀ sigma, 0 ≤ B sigma) ∧
      ∀ sigma x, x ∈ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n
            (aux_thm_prop_mass_point_idx g.H1 g.Mm sigma n x))} : ℝ) ≤
          (1 / 32 : ℝ) * (J : ℝ) + B sigma)
    (hlocal : aux_thm_prop_env_boundary_selection (hd := hd) 
      (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (aE := aE) (aF := aF) (m := m) (M := M) g Good Uset) :
    aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (GF := GF)
      (aE := aE) (aF := aF) hd m M := by
  have hbadAll := ae_all_iff.mpr hbad
  filter_upwards [horder, hplanes, hbadAll, hlocal] with om ho hp hb hl i E F f hfs hu c hc
  have hEdom := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFdom := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hdom : E.form.domain = F.form.domain :=
    SetLike.coe_injective (hEdom.trans ((ho i).1.trans hFdom.symm))
  have hEe := aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFe := aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hforms : ∀ w ∈ E.form.domain,
      m * E.form.form w w ≤ F.form.form w w ∧ F.form.form w w ≤ M * E.form.form w w := by
    intro w hw
    rw [hEe w hw, hFe w (hdom ▸ hw)]
    exact (ho i).2 w (hEdom ▸ hw)
  obtain ⟨Ccore, hcore⟩ := E.core
  have hsupp := aux_thm_prop_energy_measure_support E.gamma
    (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet hcore hu
  obtain ⟨B, hB, hcount⟩ := hb i
  obtain ⟨baseMesh, hbase, hcells⟩ := hl i E F f hfs hu c hc
  exact aux_thm_prop_fine_cells_of_boundary_estimates d hd (z i) (r i) (hr i)
    E.form F.form (GE i om) (GF i om) hdom hEdom hFdom hEe hFe E.core F.core
    E.gamma F.gamma m M hm hM hforms ⟨GE i om f, hu⟩ c hc hsupp (hp i E _ hu)
    g Uset hU (fun sigma n k => om ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k))
    B hB hcount baseMesh hbase _ rfl hcells

end Family

structure aux_thm_prop_env_selection_data
    (d : ℕ) (hd : 2 ≤ d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i)))
    (m M : ℝ) where
  AE : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  ck : ℝ → ℝ
  measurableE : ∀ j i k, Measurable (fun om => AE j om i k)
  measurableF : ∀ j i k, Measurable (fun om => AF j om i k)
  mass_indices : ∀ (jQ H1 Mm n : ℕ) (Cwidth gamma : ℝ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
    1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma →
    aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k →
    closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
    ∃ jC jP : ℕ,
      z jC = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jC = aux_thm_prop_mass_side H1 n ∧
      z jP = aux_thm_prop_mass_center H1 Mm sigma n k ∧
      r jP = 3 * aux_thm_prop_mass_side H1 n ∧
      closure (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
  minima : ∀ᵐ om ∂P, ∀ jQ jP jC, z jC = z jP → r jP = 3 * r jC →
    (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
    (∀ A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om) (aE jQ om), ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ (AE jC om).mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty) ∧
    (∀ A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GF jQ om) (aF jQ om), ∀ (p : Fin d → ℝ) (c : ℝ),
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c))
        ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ (AF jC om).mulVec p)) ∧
      (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
        A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
        (fun x => (∑ i, p i * x i) + c)).Nonempty)
  planes : ∀ᵐ om ∂P, ∀ j,
    (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GE j om) (aE j om), ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
      A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) ∧
    (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GF j om) (aF j om), ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
      A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0)

section Family2

theorem aux_thm_prop_env_mass_cell_available
    {d : ℕ} {hd : 2 ≤ d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}
    {m M : ℝ}
    (prepared : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
    (jQ H1 Mm n : ℕ) (Cwidth gamma : ℝ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (hwidth : 1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma)
    (hpad : aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k)
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) :
    aux_thm_prop_cell_available z r (aux_thm_prop_mass_center H1 Mm sigma n k)
      (aux_thm_prop_mass_side H1 n) := by
  obtain ⟨jC, jP, hzC, hrC, hzP, hrP, _⟩ :=
    prepared.mass_indices jQ H1 Mm n Cwidth gamma sigma k hwidth hpad hparent
  exact ⟨(jC, jP), hzC, hrC, hzP, hrP⟩

structure aux_thm_prop_env_local_affine_data
    {d : ℕ} {hd : 2 ≤ d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}
    {m M : ℝ}
    (prepared : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
    (g : aux_thm_prop_selection_geometry d) (c0 : ℝ) where
  Good : ℕ → SpatialCoordinates d → Set Ω
  measurable : ∀ n zc, MeasurableSet (Good n zc)
  chain : ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
    ∃ Bbase : Ω → ℝ, Measurable Bbase ∧ (∀ om, 0 ≤ Bbase om) ∧
      ∀ᵐ om ∂P, ∀ J : ℕ, 1 ≤ J →
      ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth g.H1),
        (Nat.card {j : Fin J // ¬ om ∈ Good (j.val + 1)
          (descendantCenter (subdivisionHalfWidth g.H1)
            (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k) 1 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
          ((1 / 32 : ℝ) / 2) * (J : ℝ) + Bbase om
  ellipticity : ∀ᵐ om ∂P, ∀ n zc,
    aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
    om ∈ Good n zc →
    let jC := (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1
    0 < Matrix.trace (prepared.AE jC om) ∧
      ∀ p : Fin d → ℝ,
        c0 * Matrix.trace (prepared.AE jC om) * (p ⬝ᵥ p) ≤
          p ⬝ᵥ (prepared.AE jC om).mulVec p
  approximationE : aux_thm_prop_env_source_cell_approximation
    (hd := hd) (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (aE := aE) g Good
  approximationF : aux_thm_prop_env_source_cell_approximation
    (hd := hd) (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GF) (aE := aF) g Good

end Family2

section Family3

variable {d : ℕ} {hd : 2 ≤ d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}
    {m M : ℝ}
    (prepared : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
    (g : aux_thm_prop_selection_geometry d)

theorem aux_thm_prop_env_mass_cell_minima :
    ∀ᵐ om ∂P, ∀ (jQ n : ℕ) (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
      aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
      closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      let zc := aux_thm_prop_mass_center g.H1 g.Mm sigma n k
      let s := aux_thm_prop_mass_side g.H1 n
      let q := (centeredCube zc s (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))
      let jC := (aux_thm_prop_cell_index z r zc s).1
      (∀ E : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om) (aE jQ om), ∀ (p : Fin d → ℝ) (b : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          E.form.toClosedForm E.gamma q (fun x => (∑ i, p i * x i) + b))
          ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p))) ∧
      (∀ F : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GF jQ om) (aF jQ om), ∀ (p : Fin d → ℝ) (b : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          F.form.toClosedForm F.gamma q (fun x => (∑ i, p i * x i) + b))
          ((volume q).toReal * (p ⬝ᵥ (prepared.AF jC om).mulVec p))) := by
  filter_upwards [prepared.minima] with om hmin jQ n sigma k hpad hparent
  let zc := aux_thm_prop_mass_center g.H1 g.Mm sigma n k
  let s := aux_thm_prop_mass_side g.H1 n
  have havail := aux_thm_prop_env_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have hs := aux_thm_prop_cell_index_spec z r zc s havail
  let jC := (aux_thm_prop_cell_index z r zc s).1
  let jP := (aux_thm_prop_cell_index z r zc s).2
  have hzc : z jC = zc := hs.1
  have hrc : r jC = s := hs.2.1
  have hzp : z jP = zc := hs.2.2.1
  have hrp : r jP = 3 * s := hs.2.2.2
  have hz : z jC = z jP := hs.1.trans hs.2.2.1.symm
  have hradius : r jP = 3 * r jC := hs.2.2.2.trans (congrArg (3 * ·) hs.2.1.symm)
  have hpQ : (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
    have hthree := aux_thm_prop_mass_padded_threefold g.H1 g.Mm n g.width g.gamma
      sigma k g.padded_width hpad
    have hsub := subset_closure.trans (hthree.trans (subset_closure.trans hparent))
    simpa only [hzp, hrp] using hsub
  have hm := hmin jQ jP jC hz hradius hpQ
  constructor
  · intro E p b
    simpa only [hzc, hrc] using (hm.1 E p b).1
  · intro F p b
    simpa only [hzc, hrc] using (hm.2 F p b).1

theorem aux_thm_prop_env_extra_good_concentration
    (c0 : ℝ) (hc0 : 0 < c0) (hmM : m ≤ M)
    (affine : aux_thm_prop_env_local_affine_data prepared g c0) :
    ∀ᵐ om ∂P, ∀ n zc,
      aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
      om ∈ aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck
        g.H1 affine.Good c0 m M n zc →
      let s := aux_thm_prop_mass_side g.H1 n
      let jC := (aux_thm_prop_cell_index z r zc s).1
      let q := (centeredCube zc s (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))
      ∀ p : Fin d → ℝ,
        |(volume q).toReal * (p ⬝ᵥ (prepared.AF jC om).mulVec p) -
          prepared.ck s * ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p))| ≤
          (1 / 8 : ℝ) * (M - m) *
            ((volume q).toReal * (p ⬝ᵥ (prepared.AE jC om).mulVec p)) := by
  filter_upwards [affine.ellipticity] with om hell n zc havail hgood
  have hs := aux_thm_prop_cell_index_spec z r zc (aux_thm_prop_mass_side g.H1 n) havail
  have hsmall := hgood.2
  simp only [aux_thm_prop_cell_relative_matrix_eq z r prepared.AE prepared.AF
    prepared.ck zc _ havail] at hsmall
  obtain ⟨htr, hcoer⟩ := hell n zc havail hgood.1
  dsimp only
  intro p
  have htest := aux_thm_prop_concentration_matrix_test
    (prepared.AE (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (prepared.AF (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (aux_thm_prop_relative_matrix prepared.AE prepared.AF prepared.ck r
      (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1 om)
    (prepared.ck (r (aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1))
    (volume (centeredCube zc (aux_thm_prop_mass_side g.H1 n)
      (aux_thm_prop_grid_side_pos g.H1 n) : Set (SpatialCoordinates d))).toReal
    (1 / 8) c0 m M (by norm_num) hc0 hmM
    (centeredCube_volume_pos zc (aux_thm_prop_grid_side_pos g.H1 n)) htr hcoer rfl hsmall p
  simpa only [hs.2.1, mul_assoc] using htest

end Family3

section Family4

variable {d : ℕ} {hd : 2 ≤ d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}
    {m M : ℝ}
    (prepared : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
    (g : aux_thm_prop_selection_geometry d) (c0 : ℝ) (hc0 : 0 < c0) (hmM : m ≤ M)
    (affine : aux_thm_prop_env_local_affine_data prepared g c0)

include hc0 hmM

theorem aux_thm_prop_env_boundary_selection_U :
    aux_thm_prop_env_boundary_selection (hd := hd) 
      (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (aE := aE) (aF := aF) (m := m) (M := M) g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)
      (fun n => prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) := by
  have hmin := aux_thm_prop_env_mass_cell_minima prepared g
  have hconc := aux_thm_prop_env_extra_good_concentration prepared g c0 hc0 hmM affine
  filter_upwards [hmin, hconc, affine.approximationE] with om hmins hconcs happs
    jQ E F f hfs hu c hc
  obtain ⟨baseMesh, hbase, happ⟩ := happs jQ E f hfs hu c hc
  refine ⟨baseMesh, hbase, ?_⟩
  intro n hn hU hmesh sigma k hgood hpad hparent
  dsimp only
  intro hmass
  obtain ⟨U, hUcont, hrep, herror⟩ := happ n hn hmesh sigma k hgood.1 hpad hparent hmass
  have hminimum := hmins jQ n sigma k hpad hparent
  have havail := aux_thm_prop_env_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have htest := hconcs n _ havail hgood
  exact aux_thm_prop_boundary_cell_U (centeredCube (z jQ) (r jQ) (hr jQ))
    E.form F.form E.gamma F.gamma m M (prepared.ck (aux_thm_prop_mass_side g.H1 n))
    _ _ _ (hminimum.1 E) (hminimum.2 F) htest hU ⟨GE jQ om f, hu⟩ U hUcont hrep c herror

theorem aux_thm_prop_env_boundary_selection_V (hm : 0 < m) :
    aux_thm_prop_env_boundary_selection (hd := hd) 
      (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GF) (GF := GE) (aE := aF) (aF := aE) (m := M⁻¹) (M := m⁻¹) g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)
      (fun n => ¬ prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) := by
  have hmin := aux_thm_prop_env_mass_cell_minima prepared g
  have hconc := aux_thm_prop_env_extra_good_concentration prepared g c0 hc0 hmM affine
  filter_upwards [hmin, hconc, affine.approximationF] with om hmins hconcs happs
    jQ F E f hfs hu c hc
  obtain ⟨baseMesh, hbase, happ⟩ := happs jQ F f hfs hu c hc
  refine ⟨baseMesh, hbase, ?_⟩
  intro n hn hV hmesh sigma k hgood hpad hparent
  dsimp only
  intro hmass
  obtain ⟨U, hUcont, hrep, herror⟩ := happ n hn hmesh sigma k hgood.1 hpad hparent hmass
  have hminimum := hmins jQ n sigma k hpad hparent
  have havail := aux_thm_prop_env_mass_cell_available prepared jQ g.H1 g.Mm n
    g.width g.gamma sigma k g.padded_width hpad hparent
  have htest := hconcs n _ havail hgood
  exact aux_thm_prop_boundary_cell_V (centeredCube (z jQ) (r jQ) (hr jQ))
    E.form F.form E.gamma F.gamma m M (prepared.ck (aux_thm_prop_mass_side g.H1 n))
    _ _ _ (hminimum.1 E) (hminimum.2 F) htest hm hmM (le_of_lt (lt_of_not_ge hV))
    ⟨GF jQ om f, hu⟩ U hUcont hrep c herror


theorem aux_thm_prop_env_fine_dichotomy_from_local_estimates
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hbad : aux_thm_prop_mass_good_counts P z r hr g
      (aux_thm_prop_extra_good z r prepared.AE prepared.AF prepared.ck g.H1 affine.Good c0 m M)) :
    aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GE) (GF := GF)
      (aE := aE) (aF := aF) hd m M ∨
    aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace) (GE := GF) (GF := GE)
      (aE := aF) (aF := aE) hd M⁻¹ m⁻¹ := by
  have hU := aux_thm_prop_env_boundary_selection_U prepared g c0 hc0 hmM affine
  have hV := aux_thm_prop_env_boundary_selection_V prepared g c0 hc0 hmM affine hm
  rcases aux_thm_prop_half_density
      (fun n => prepared.ck (aux_thm_prop_mass_side g.H1 n) ≤ (m + M) / 2) with hdens | hdens
  · left
    exact aux_thm_prop_env_fine_candidates_from_boundary_selection hm hM g _ _ hdens horder
      (prepared.planes.mono fun om h i => (h i).1) hbad hU
  · right
    exact aux_thm_prop_env_fine_candidates_from_boundary_selection (inv_pos.mpr hM)
      (inv_pos.mpr hm) g _ _ hdens (aux_thm_prop_order_swap m M hm hM horder)
      (prepared.planes.mono fun om h i => (h i).2) hbad hV

end Family4

section Directed

variable {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i))}
    {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}

theorem aux_thm_prop_env_directed_dichotomy (hd : 2 ≤ d)
    (hsource : ∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ E : DirichletForm.ClosedForm
        (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
      (∀ u, E.energy u = limitFormEnergy (GE i om) u) →
      ∀ Gamma : DirichletForm.EnergyMeasure E,
      (∃ C, DirichletForm.IsCoreOn E
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
      DirichletForm.IsResolvent E 0 (GE i om))
    (hside : ∀ᵐ om ∂P, ∀ i,
      Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om) (aE i om)) ∧
      Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GF i om) (aF i om)))
    (m M : ℝ) (hmM : m ≤ M) (hM : 0 < M)
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hcoer : ∀ᵐ om ∂P, ∀ i,
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GE i om) ∧
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GF i om))
    (hfine : aux_thm_prop_env_fine_candidates (P := P)
      (z := z) (r := r) (hr := hr) (Sspace := Sspace)
      (GE := GE) (GF := GF) (aE := aE) (aF := aF) hd m M) :
    ∀ᵐ om ∂P, ∀ i,
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
      ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps →
        aux_thm_prop_localSaving M (M - m)
          (limitFormEnergy (GE i om) (GE i om f)).toReal
          (limitFormEnergy (GF i om) (GE i om f)).toReal
          (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
          c eps := by
  filter_upwards [hside, horder, hcoer, hfine, hsource] with om hs ho hc hf hsrc i f hfs c hcpos
  obtain ⟨E⟩ := (hs i).1
  obtain ⟨F⟩ := (hs i).2
  have hEdom := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFdom := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hdom : E.form.domain = F.form.domain := by
    apply SetLike.coe_injective
    exact hEdom.trans ((ho i).1.trans hFdom.symm)
  have hres := hsrc i E.form.toClosedForm E.energy_eq E.gamma E.core f
  have hu : GE i om f ∈ E.form.domain := hres.1
  have hweak : ∀ w ∈ E.form.domain, E.form.form (GE i om f) w = inner ℝ f w := by
    simpa only [zero_mul, zero_add] using hres.2
  obtain ⟨sE, KE, hsE, _hsE1, hKE, hcoerE⟩ :=
    (hc i).1 E.form.toClosedForm E.energy_eq E.gamma
  obtain ⟨sF, KF, hsF, _hsF1, hKF, hcoerF⟩ :=
    (hc i).2 F.form.toClosedForm F.energy_eq F.gamma
  have hEe := aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm (GE i om) E.energy_eq
  have hFe := aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm (GF i om) F.energy_eq
  have hforms : ∀ w ∈ E.form.domain, F.form.form w w ≤ M * E.form.form w w := by
    intro w hw
    have hwF : w ∈ F.form.domain := hdom ▸ hw
    rw [hEe w hw, hFe w hwF]
    exact ((ho i).2 w (hEdom ▸ hw)).2
  obtain ⟨cells⟩ := hf i E F f hfs hu c hcpos
  have hsaving := aux_thm_prop_localSaving_of_fine_cells
    (centeredCube (z i) (r i) (hr i))
    (centeredCube_isBounded (z i) (hr i)).measure_lt_top.ne
    E.form F.form (GE i om) (GF i om) E.energy_eq F.energy_eq hdom E.gamma F.gamma
    E.core F.core m M hmM hM hforms f ⟨GE i om f, hu⟩ hweak sE KE sF KF
    (by linarith) hKE (by linarith) hKF hcoerE hcoerF c hcpos cells
  have huF : GE i om f ∈ F.form.domain := hdom ▸ hu
  simpa only [hEe _ hu, hFe _ huF] using hsaving

end Directed

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

/-- The fine-cell dichotomy of the environment form: relative concentration (`hmom`), the local
affine data and the selection data give the two directed fine-cell branches; the disorder
threshold `deltaCount` precedes the model. -/
theorem thm_prop_env_select
    (d : ℕ) (hd : 2 ≤ d) (g : aux_thm_prop_selection_geometry d)
    (c0 : ℝ) (hc0 : 0 < c0) (p : ℝ) (hp : 0 < p) (Cp : ℝ) (hCp : 0 < Cp) (aexp : ℝ)
    (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / (1 / 32 : ℝ)) *
      (((g.H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (hfield : Measurable field)
        (hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)))
        (aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i)))
        (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
        (horder : ∀ᵐ om ∂P, ∀ i,
          limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
          ∀ u ∈ limitFormDomain (GE i om),
            m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
            (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
        (prepared : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF aE aF m M)
        (affine : aux_thm_prop_env_local_affine_data prepared g c0)
        (hmom : aux_thm_prop_cell_matrix_moments P field z r prepared.AE prepared.AF prepared.ck
          g.H1 p (Cp * model.delta * (M - m)) aexp),
        aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
          (GE := GE) (GF := GF) (aE := aE) (aF := aF) hd m M ∨
        aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
          (GE := GF) (GF := GE) (aE := aF) (aF := aE) hd M⁻¹ m⁻¹ := by
  obtain ⟨delta0, hdelta0, hCount⟩ := aux_thm_prop_matrix_mass_counts d hd g c0 hc0 p hp Cp hCp
    aexp haexp hpRate
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel Ω _ P _ field hfield hlaw z r hr Sspace GE GF aE aF m M hm hmM horder
    prepared affine hmom
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hbad := hCount model hmodel Ω P field hfield hlaw z r hr prepared.AE prepared.AF
    prepared.ck prepared.measurableE prepared.measurableF m M hmM affine.Good affine.chain hmom
  exact aux_thm_prop_env_fine_dichotomy_from_local_estimates prepared g c0 hc0 hmM affine hm hM
    horder hbad



section Tail

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
  {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
  {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
    DomainL2 (centeredCube (z i) (r i) (hr i))}
  {aE aF : (i : ℕ) → Ω → ℕ → PositiveCoefficient (centeredCube (z i) (r i) (hr i))}

/-- Both directed branches close, for deterministic `0 < m ≤ M`. -/
theorem aux_thm_prop_env_dichotomy_of_fine
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hside : ∀ᵐ om ∂P, ∀ i,
      Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GE i om)
        (aE i om)) ∧
      Nonempty (aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i) (GF i om)
        (aF i om)))
    (horder : ∀ᵐ om ∂P, ∀ i,
      limitFormDomain (GE i om) = limitFormDomain (GF i om) ∧
      ∀ u ∈ limitFormDomain (GE i om),
        m * (limitFormEnergy (GE i om) u).toReal ≤ (limitFormEnergy (GF i om) u).toReal ∧
        (limitFormEnergy (GF i om) u).toReal ≤ M * (limitFormEnergy (GE i om) u).toReal)
    (hcoer : ∀ᵐ om ∂P, ∀ i,
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GE i om) ∧
      aux_thm_prop_coercive_candidate (centeredCube (z i) (r i) (hr i)) (GF i om))
    (hsourceE : ∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ E : DirichletForm.ClosedForm
        (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
      (∀ u, E.energy u = limitFormEnergy (GE i om) u) →
      ∀ Gamma : DirichletForm.EnergyMeasure E,
      (∃ C, DirichletForm.IsCoreOn E
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
      DirichletForm.IsResolvent E 0 (GE i om))
    (hsourceF : ∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ E : DirichletForm.ClosedForm
        (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
      (∀ u, E.energy u = limitFormEnergy (GF i om) u) →
      ∀ Gamma : DirichletForm.EnergyMeasure E,
      (∃ C, DirichletForm.IsCoreOn E
        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) C) →
      DirichletForm.IsResolvent E 0 (GF i om))
    (hfine :
      aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
        (GE := GE) (GF := GF) (aE := aE) (aF := aF) hd m M ∨
      aux_thm_prop_env_fine_candidates (P := P) (z := z) (r := r) (hr := hr) (Sspace := Sspace)
        (GE := GF) (GF := GE) (aE := aF) (aF := aE) hd M⁻¹ m⁻¹) :
    (∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
      ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps →
        aux_thm_prop_localSaving M (M - m)
          (limitFormEnergy (GE i om) (GE i om f)).toReal
          (limitFormEnergy (GF i om) (GE i om f)).toReal
          (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
          c eps) ∨
    (∀ᵐ om ∂P, ∀ i : ℕ,
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
      ∀ c : ℝ, 0 < c → ∀ eps : ℝ, 0 < eps →
        aux_thm_prop_localSaving m⁻¹ (m⁻¹ - M⁻¹)
          (limitFormEnergy (GF i om) (GF i om f)).toReal
          (limitFormEnergy (GE i om) (GF i om f)).toReal
          (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
          c eps) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  rcases hfine with hU | hV
  · left
    exact aux_thm_prop_env_directed_dichotomy hd hsourceE hside m M hmM hM horder hcoer hU
  · right
    have hsideSwap := hside.mono fun _ h i => (h i).symm
    have hcoerSwap := hcoer.mono fun _ h i => (h i).symm
    exact aux_thm_prop_env_directed_dichotomy (GE := GF) (GF := GE) (aE := aF) (aF := aE)
      hd hsourceF hsideSwap M⁻¹ m⁻¹ (inv_anti₀ hm hmM) (inv_pos.mpr hm)
      (aux_thm_prop_order_swap m M hm hM horder) hcoerSwap hV

end Tail

end Part1

end Paper
end
