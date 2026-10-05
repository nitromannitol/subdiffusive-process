module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumMeasurability

@[expose] public section

/-!
# The discrete minimum is an infimum over a countable, sample-free family

This file discharges obligation **(M2)** of `DirichletInfimumMeasurability.lean`.

`kuhnDirichletInf B S U p` is an infimum over `kuhnSlopeSet U S`, which is
uncountable.  But the discrete energy depends on the slope assignment only
through its restriction to the *finite* mesh `S`, so it is a continuous function
on the finite-dimensional space `{T // T in S} -> Vec d`; a subset of such a
space admits a countable dense subset, and a countable dense subset of the slope
set is `eps`-optimal *for every coefficient simultaneously* -- the coefficient
enters only through the continuity of one and the same energy functional.

* `kuhnDiscreteEnergyOnMesh` is the energy read on the restriction, and
  `continuous_kuhnDiscreteEnergyOnMesh` is its continuity;
* **`exists_countable_eps_optimal_kuhnSlopes`** produces the countable family:
  it depends on `U` and the mesh only, never on the coefficient or the sample;
* **`measurable_kuhnDirichletInf`** and **`measurable_dirichletInfOn`** are the
  consequences.  The only hypothesis left is (M1), the measurability of the
  finitely many cellwise suprema `omega |-> cellSup (B omega) T`.

## Scope

Nothing here is probabilistic; the separability argument is carried out once,
for the deterministic mesh, and the sample enters only in the last two
statements through (M1).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set TopologicalSpace

noncomputable section

variable {d : ℕ}

/-! ## The energy as a function on a finite-dimensional space -/

theorem continuous_vecNormSq : Continuous (vecNormSq : Vec d → ℝ) := by
  have hrw : (vecNormSq : Vec d → ℝ) = fun x => ∑ i, x i * x i := rfl
  rw [hrw]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

/-- The discrete energy read on the restriction of the slope assignment to the
mesh: a continuous function of finitely many vectors. -/
def kuhnDiscreteEnergyOnMesh (B : Vec d → ℝ) (S : Finset (KuhnCell d))
    (U : Set (Vec d)) (p : Vec d) (y : {T // T ∈ S} → Vec d) : ℝ :=
  ∑ T : {T // T ∈ S},
    volume.real (U ∩ (T : KuhnCell d).openCarrier) *
      (cellSup B (T : KuhnCell d) * vecNormSq (p + y T))

theorem kuhnDiscreteEnergy_eq_onMesh (B : Vec d → ℝ) (S : Finset (KuhnCell d))
    (U : Set (Vec d)) (p : Vec d) (q : KuhnCell d → Vec d) :
    kuhnDiscreteEnergy B S U p q =
      kuhnDiscreteEnergyOnMesh B S U p (fun T => q (T : KuhnCell d)) :=
  (Finset.sum_coe_sort S _).symm

theorem continuous_kuhnDiscreteEnergyOnMesh (B : Vec d → ℝ) (S : Finset (KuhnCell d))
    (U : Set (Vec d)) (p : Vec d) :
    Continuous (kuhnDiscreteEnergyOnMesh B S U p) := by
  refine continuous_finsetSum _ fun T _ => ?_
  exact continuous_const.mul (continuous_const.mul
    (continuous_vecNormSq.comp (continuous_const.add (continuous_apply T))))

/-! ## A countable, coefficient-free `eps`-optimal family -/

/-- **(M2).**  There is a countable family of admissible slope assignments,
depending on `U` and the mesh only, which realizes `Q_{R,pi}(p)` up to `eps` for
*every* continuous nonnegative coefficient and every `p`.

The family is a countable dense subset of the slope set, read through the
restriction to the finite mesh; density plus the continuity of the energy give
`eps`-optimality, and neither the density nor the continuity involves the
coefficient. -/
theorem exists_countable_eps_optimal_kuhnSlopes (U : Set (Vec d))
    (S : Finset (KuhnCell d)) :
    ∃ D : ℕ → KuhnCell d → Vec d,
      (∀ m, D m ∈ kuhnSlopeSet U S) ∧
      ∀ (B : Vec d → ℝ) (p : Vec d), ∀ eps > 0, ∃ m,
        kuhnDiscreteEnergy B S U p (D m) < kuhnDirichletInf B S U p + eps := by
  classical
  set r : (KuhnCell d → Vec d) → ({T // T ∈ S} → Vec d) :=
    fun q T => q (T : KuhnCell d) with hr
  set Λ : Set ({T // T ∈ S} → Vec d) := r '' kuhnSlopeSet U S with hΛ
  obtain ⟨t, htΛ, htc, htd⟩ :=
    (IsSeparable.of_separableSpace Λ).exists_countable_dense_subset
  have hΛne : Λ.Nonempty := (kuhnSlopeSet_nonempty U S).image r
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hΛne
    have : y ∈ closure t := htd hy
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, closure_empty] at this
    exact this
  obtain ⟨g, hg⟩ := htc.exists_eq_range htne
  have hgΛ : ∀ m, g m ∈ Λ := fun m => htΛ (by rw [hg]; exact ⟨m, rfl⟩)
  choose D hD hDr using hgΛ
  refine ⟨D, hD, fun B p eps heps => ?_⟩
  obtain ⟨c, hc⟩ := exists_kuhnCompetitor_kuhnDiscreteEnergy_lt B (S := S) (U := U) p
    (half_pos heps)
  set O : Set ({T // T ∈ S} → Vec d) :=
    kuhnDiscreteEnergyOnMesh B S U p ⁻¹'
      Set.Iio (kuhnDiscreteEnergyOnMesh B S U p (r c.slope) + eps / 2) with hO
  have hOopen : IsOpen O :=
    (continuous_kuhnDiscreteEnergyOnMesh B S U p).isOpen_preimage _ isOpen_Iio
  have hqO : r c.slope ∈ O := by
    simp only [hO, Set.mem_preimage, Set.mem_Iio]
    linarith [half_pos heps]
  have hmem : r c.slope ∈ closure t := htd ⟨c.slope, ⟨c, rfl⟩, rfl⟩
  obtain ⟨y, hyO, hyt⟩ := mem_closure_iff.mp hmem O hOopen hqO
  obtain ⟨m, rfl⟩ : ∃ m, g m = y := by
    rw [hg] at hyt
    exact hyt
  refine ⟨m, ?_⟩
  have hDeq : kuhnDiscreteEnergy B S U p (D m) =
      kuhnDiscreteEnergyOnMesh B S U p (g m) := by
    rw [kuhnDiscreteEnergy_eq_onMesh]
    exact congrArg (kuhnDiscreteEnergyOnMesh B S U p) (hDr m)
  have hslope : kuhnDiscreteEnergy B S U p c.slope =
      kuhnDiscreteEnergyOnMesh B S U p (r c.slope) :=
    kuhnDiscreteEnergy_eq_onMesh B S U p c.slope
  simp only [hO, Set.mem_preimage, Set.mem_Iio] at hyO
  rw [hDeq]
  rw [hslope] at hc
  linarith

/-! ## Measurability, modulo (M1) -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurability of `Q_{R,pi}(p)`**, assuming only (M1). -/
theorem measurable_kuhnDirichletInf {B : Ω → Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {p : Vec d} (hB : ∀ ω, Continuous (B ω))
    (hB0 : ∀ ω x, 0 ≤ B ω x)
    (hcell : ∀ T ∈ S, Measurable fun ω => cellSup (B ω) T) :
    Measurable fun ω => kuhnDirichletInf (B ω) S U p := by
  obtain ⟨D, hD, hopt⟩ := exists_countable_eps_optimal_kuhnSlopes U S
  refine measurable_kuhnDirichletInf_of_iInf D
    (fun m => measurable_kuhnDiscreteEnergy hcell) fun ω => ?_
  exact kuhnDirichletInf_eq_iInf (hB ω) (hB0 ω) p D hD (hopt (B ω) p)

/-- **Measurability of the Dirichlet minimum, modulo (M1).**  The
continuum Dirichlet minimum `omega |-> dirichletInfOn (B omega) U p` is
measurable as soon as each cellwise supremum is.  With
`B omega = shellFactor M 0 omega` this is the statement that `q_*`  needs in order to be an expectation. -/
theorem measurable_dirichletInfOn {n : ℕ} {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} {B : Ω → Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x) (p : Vec (n + 1))
    (hcell : ∀ T : KuhnCell (n + 1), Measurable fun ω => cellSup (B ω) T) :
    Measurable fun ω => dirichletInfOn (B ω) U p :=
  measurable_dirichletInfOn_of_measurable_kuhnDirichletInf hU hUQ hB hB0 p
    fun _ => measurable_kuhnDirichletInf hB hB0 fun T _ => hcell T

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
