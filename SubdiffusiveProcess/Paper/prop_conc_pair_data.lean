import SubdiffusiveProcess.Paper.lem_relvar
import SubdiffusiveProcess.DirichletForm.LocalResponsePair

/-! Deterministic variational data of the two limiting forms on one padded cube, together with
their local relative response for a common weight.  Definitions only; no existence is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- The local energy of `v` on `q` for the common weight `exp g`, in the energy measure `Gamma`. -/
def aux_prop_conc_pair_data_wenergy {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (Gamma : DirichletForm.EnergyMeasure E) (q : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (v : DomainL2 Q) : ℝ :=
  (∫⁻ x in q, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)).toReal

/-- The form pair of a typical configuration on the padded cube `Q ⊇ closure q`, with its energy
measures, the killed domain `D` of the observation cell `q = centeredCube z r hr`, the local
minimizers/responses `P` in one common affine trace class, and the form order `m ≤ F/E ≤ M`. -/
structure prop_conc_pair_data {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (C0 m M : ℝ) where
  hd : 2 ≤ d
  hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ), Q = centeredCube zQ rQ hrQ
  hinside : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))
  E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  GammaE : DirichletForm.EnergyMeasure E.toClosedForm
  GammaF : DirichletForm.EnergyMeasure F.toClosedForm
  D : Submodule ℝ (DomainL2 Q)
  P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF
    (centeredCube z r hr : Set (SpatialCoordinates d)) D
  hEc : ∃ S, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) S
  hFc : ∃ S, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) S
  hEl : DirichletForm.IsStronglyLocal E.toClosedForm
  hFl : DirichletForm.IsStronglyLocal F.toClosedForm
  hC0 : 1 ≤ C0
  hm : C0⁻¹ ≤ m
  hmM : m ≤ M
  hM : M ≤ C0
  horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v
  CE : ℝ
  CF : ℝ
  hCE : 0 < CE
  hCF : 0 < CF
  hcoE : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ CE * E.form v v
  hcoF : ∀ v ∈ F.domain, ‖v‖ ^ 2 ≤ CF * F.form v v
  hDpos : 0 < ∑ i : Fin d, P.QE (Pi.single i 1)

/-- The least `exp g`-weighted `E`-energy on `q` in the affine trace class of slope `p`. -/
def aux_prop_conc_pair_data_wInfE {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (g : SpatialCoordinates d → ℝ)
    (p : Fin d → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ v ∈ X.E.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
    e = aux_prop_conc_pair_data_wenergy X.GammaE (centeredCube z r hr : Set (SpatialCoordinates d)) g v}

/-- The least `exp g`-weighted `F`-energy on `q` in the same affine trace class. -/
def aux_prop_conc_pair_data_wInfF {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (g : SpatialCoordinates d → ℝ)
    (p : Fin d → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ v ∈ X.F.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
    e = aux_prop_conc_pair_data_wenergy X.GammaF (centeredCube z r hr : Set (SpatialCoordinates d)) g v}

/-- The relative response `(F_g(p) - c E_g(p)) / ∑_i E_g(e_i)` of the `exp g`-weighted pair. -/
def aux_prop_conc_pair_data_theta {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ)
    (g : SpatialCoordinates d → ℝ) : ℝ :=
  (aux_prop_conc_pair_data_wInfF X g p - c * aux_prop_conc_pair_data_wInfE X g p) /
    ∑ i : Fin d, aux_prop_conc_pair_data_wInfE X g (Pi.single i 1)

/-- The affine trace class of the pair is realized by functions continuous up to the boundary of the
padded cube whose values on the frontier of `q` are the affine function `p · x`. -/
def aux_prop_conc_pair_data_affine {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) : Prop :=
  ∀ p : Fin d → ℝ, ∃ V : SpatialCoordinates d → ℝ,
    ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
    (⇑(X.P.boundary p : DomainL2 Q) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
    ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = ∑ i, p i * x i

/-- The polarizing slope family `{e_i} ∪ {e_i + e_j}` of `lem_relvar`. -/
def aux_prop_conc_pair_data_slopes (d : ℕ) : Finset (Fin d → ℝ) :=
  Finset.univ.image (fun i : Fin d => (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∪
    Finset.univ.image (fun ij : Fin d × Fin d =>
      (Pi.single ij.1 (1 : ℝ) : Fin d → ℝ) + Pi.single ij.2 (1 : ℝ))

theorem aux_prop_conc_pair_data_mem_slopes (d : ℕ) (p : Fin d → ℝ) :
    p ∈ aux_prop_conc_pair_data_slopes d ↔ (∃ i : Fin d, p = Pi.single i (1 : ℝ)) ∨
      (∃ i j : Fin d, p = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) := by
  simp only [aux_prop_conc_pair_data_slopes, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, j, rfl⟩)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, j, rfl⟩)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, j, rfl⟩

/-- The normalized energy measure `ν` of the coordinate/slope minimizers of `X`. -/
def aux_prop_conc_pair_data_nu {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (slopes : Finset (Fin d → ℝ)) :
    Measure (SpatialCoordinates d) :=
  ENNReal.ofReal (∑ i : Fin d, X.P.QE (Pi.single i 1))⁻¹ •
    ∑ p ∈ slopes, (X.GammaE.measure (X.P.boundary p) + X.GammaE.measure (X.P.uF p))

/-- The normalized difference measure `ζ` of the two minimizers of `X`. -/
def aux_prop_conc_pair_data_zeta {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (slopes : Finset (Fin d → ℝ)) :
    Measure (SpatialCoordinates d) :=
  ENNReal.ofReal (∑ i : Fin d, X.P.QE (Pi.single i 1))⁻¹ •
    ∑ p ∈ slopes, X.GammaE.measure (X.P.uF p - X.P.boundary p)

/-- Growth `ν(B_ρ(x) ∩ q) ≤ K (ρ/r)^t` for `ρ ≤ r` (cell units). -/
def aux_prop_conc_pair_data_growth {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (slopes : Finset (Fin d → ℝ))
    (t K : ℝ) : Prop :=
  ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ r →
    (aux_prop_conc_pair_data_nu X slopes
      (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal ≤
      K * (rho / r) ^ t

end
end Paper
