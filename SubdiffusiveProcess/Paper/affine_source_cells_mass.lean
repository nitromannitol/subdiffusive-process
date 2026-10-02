import SubdiffusiveProcess.Paper.thm_prop_base
import SubdiffusiveProcess.Paper.mass_grid_cells
import SubdiffusiveProcess.Paper.affine_source_cells_env
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.affine_source_cells_mass_roots

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A closed sup-ball around the child centre of radius `ρ ≤ W' + r/2` lies in the open parent cube, when the
child cell is padded by `W'` coordinatewise. -/
theorem aux_affine_source_cells_mass_ball_sub {d : ℕ} (L r W' rho : ℝ) (hr : 0 < r)
    (hL : 0 < L) (hrho : 0 ≤ rho) (lo lop z zP : Fin d → ℝ)
    (hz : ∀ i, z i = lo i + r / 2) (hzP : ∀ i, zP i = lop i + L * r / 2)
    (hpad : ∀ i, W' < lo i - lop i ∧ W' < lop i + L * r - (lo i + r))
    (hrho' : rho ≤ W' + r / 2) :
    Metric.closedBall z rho ⊆ Metric.ball zP (L * r / 2) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hrho] at hx
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
  intro i
  have h1 := hx i
  have h3 := hpad i
  rw [Real.dist_eq, abs_le] at h1
  rw [Real.dist_eq, abs_lt, hzP i]
  rw [hz i] at h1
  constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2]

/-- Geometry of one padded mass cell (`n = n' + 1`), padding width `W ≥ 81`: the open parent cube lies in the
killed cube, the comparison ball of the good-cell catalogue (side `3^{-(k - gH)}`, `gH = ⌊γ H1⌋ + 4`) lies in
the parent, and so does every root of the catalogue (in particular they lie in the killed cube). -/
theorem aux_affine_source_cells_mass_cell_geom {d : ℕ} (H1 Mm n' : ℕ) (hH1 : 1 ≤ H1)
    (gamma W : ℝ) (hgamma : 0 ≤ gamma) (hW : 81 ≤ W)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) (Q : Set (SpatialCoordinates d))
    (hpad : aux_thm_prop_mass_padded H1 Mm W gamma sigma (n' + 1) k)
    (hparent : closure (aux_thm_prop_mass_parent H1 Mm sigma (n' + 1) k) ⊆ Q) :
    Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) ⊆ Q ∧
    Metric.closedBall (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
        ((3 : ℝ) ^ (-(((H1 * (n' + 1) : ℕ) : ℤ) - ((Nat.floor (gamma * (H1 : ℝ)) + 4 : ℕ) : ℤ))) / 2) ⊆
      Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) ∧
    ∀ U : Fin 3 × (Fin d → Fin 3),
      closure (centeredCube (gcat_rootCentre (Nat.floor (gamma * (H1 : ℝ)) + 4) (H1 * (n' + 1))
        (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k) U)
        (gcat_rootSide (Nat.floor (gamma * (H1 : ℝ)) + 4) (H1 * (n' + 1)) U)
        (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆ Q := by
  have hn : 1 ≤ n' + 1 := by omega
  have hside := aux_mass_grid_cells_side_eq H1 (n' + 1)
  have hpar := aux_mass_grid_cells_parent_side H1 (n' + 1) hn
  simp only [Nat.add_sub_cancel] at hpar hpad
  have hr : 0 < aux_thm_prop_mass_side H1 (n' + 1) := by unfold aux_thm_prop_mass_side; positivity
  have hL : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  -- the parent cube is in the killed cube
  have hQ : Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
      ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) ⊆ Q := by
    have h := aux_mass_grid_cells_parent_ball_in_Q H1 Mm (n' + 1) hn sigma k Q hparent
    simp only [Nat.add_sub_cancel] at h
    rw [hside] at h
    exact h
  -- numeric comparison
  set gH : ℕ := Nat.floor (gamma * (H1 : ℝ)) + 4 with hgH
  have hgam : (3 : ℝ) ^ Nat.floor (gamma * (H1 : ℝ)) ≤ ((3 : ℝ) ^ H1) ^ gamma := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (3 : ℝ) H1, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc (Nat.floor (gamma * (H1 : ℝ)) : ℝ) ≤ gamma * (H1 : ℝ) := Nat.floor_le (by positivity)
      _ = (H1 : ℝ) * gamma := by ring
  have hS : (3 : ℝ) ^ (-(((H1 * (n' + 1) : ℕ) : ℤ) - (gH : ℤ))) =
      (3 : ℝ) ^ gH * aux_thm_prop_mass_side H1 (n' + 1) := by
    rw [hside, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    ring
  have hSle : (3 : ℝ) ^ (-(((H1 * (n' + 1) : ℕ) : ℤ) - (gH : ℤ))) ≤
      W * ((3 : ℝ) ^ H1) ^ gamma * aux_thm_prop_mass_side H1 (n' + 1) := by
    rw [hS, hgH, pow_add]
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ Nat.floor (gamma * (H1 : ℝ)) := by positivity
    have h2 : 81 * (3 : ℝ) ^ Nat.floor (gamma * (H1 : ℝ)) ≤ W * ((3 : ℝ) ^ H1) ^ gamma := by
      nlinarith [mul_le_mul hW hgam h1 (by linarith)]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right h2 hr.le]
  have hball : ∀ rho : ℝ, 0 ≤ rho →
      rho ≤ W * ((3 : ℝ) ^ H1) ^ gamma * aux_thm_prop_mass_side H1 (n' + 1) + aux_thm_prop_mass_side H1 (n' + 1) / 2 →
      Metric.closedBall (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k) rho ⊆
        Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
          ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) := by
    intro rho hrho hrho'
    rw [← hside]
    refine aux_affine_source_cells_mass_ball_sub ((3 : ℝ) ^ H1)
      (aux_thm_prop_mass_side H1 (n' + 1)) (W * ((3 : ℝ) ^ H1) ^ gamma *
        aux_thm_prop_mass_side H1 (n' + 1)) rho hr hL hrho
      (aux_thm_prop_mass_lo H1 Mm sigma (n' + 1) k)
      (aux_thm_prop_mass_lo H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
      (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
      (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
      (fun i => rfl) (fun i => by simp only [aux_thm_prop_mass_center, hpar]) ?_ hrho'
    intro i
    obtain ⟨h1, h2⟩ := hpad i
    simp only [Nat.add_sub_cancel] at h1 h2
    rw [hpar] at h2
    exact ⟨h1, h2⟩
  have hSpos : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((H1 * (n' + 1) : ℕ) : ℤ) - (gH : ℤ))) := by positivity
  refine ⟨hQ, ?_, ?_⟩
  · refine hball _ (by positivity) ?_
    nlinarith [hSle, hr]
  · intro U
    refine (aux_affine_source_cells_mass_root_sub gH (H1 * (n' + 1)) _ U).trans ?_
    refine (Metric.closedBall_subset_closedBall
      (aux_affine_source_cells_mass_rootSide_le gH (H1 * (n' + 1)) (by omega) U)).trans ?_
    exact (hball _ hSpos (by nlinarith [hSle, hr])).trans hQ


/-- The parent centre lies on the lattice `origin + (L r) Z^d` with origin `sigma/M + 1/2`, and the child centre is
its odd-grid child (`n = n' + 1`). -/
theorem aux_affine_source_cells_mass_tuple {d : ℕ} (H1 Mm n' : ℕ)
    (sigma : Fin d → Fin Mm) (k : Fin d → ℤ) :
    aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k) =
      (fun i => (fun i => ((sigma i).val : ℝ) / (Mm : ℝ) + 1 / 2) i +
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ))) *
          (((aux_thm_prop_mass_parent_idx H1 k i - ((3 : ℤ) ^ (H1 * n') - 1) / 2 : ℤ)) : ℝ)) ∧
    aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k =
      oddGridCenter (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ))) (subdivisionHalfWidth H1)
        (aux_mass_grid_cells_digit H1 k) := by
  have hn : 1 ≤ n' + 1 := by omega
  have hside := aux_mass_grid_cells_side_eq H1 (n' + 1)
  have hpar := aux_mass_grid_cells_parent_side H1 (n' + 1) hn
  simp only [Nat.add_sub_cancel] at hpar
  constructor
  · funext i
    have h := aux_mass_grid_cells_parent_center H1 Mm (n' + 1) sigma k i
    simp only [Nat.add_sub_cancel] at h
    rw [h, hpar, hside]
  · have h := aux_mass_grid_cells_child_center H1 Mm (n' + 1) sigma k hn
    simp only [Nat.add_sub_cancel] at h
    rw [← h, hpar, hside]

/-- Hyperplanes are Lebesgue null. -/
theorem aux_affine_source_cells_mass_volume_plane {d : ℕ} (i : Fin d) (a : ℝ) :
    (volume : Measure (SpatialCoordinates d)) {x : SpatialCoordinates d | x i = a} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i a

/-- From the mass-set inequality of `source_cell_approximation` to the inequality for the open cubes
(`λ`-form of `lem_affine`), using that `Γ + c dx` charges no hyperplane. -/
theorem aux_affine_source_cells_mass_mu_to_lambda {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E' : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gam' : DirichletForm.EnergyMeasure E'.toClosedForm) (u : DomainL2 Q)
    (hu : u ∈ E'.toClosedForm.domain)
    (hplane : ∀ (i : Fin d) (a : ℝ), Gam'.measure u {x : SpatialCoordinates d | x i = a} = 0)
    (c : ℝ) (hc : 0 < c) (H1 Mm n' : ℕ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ)
    (Lz : ℝ)
    (hparQ : Metric.ball (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
      ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hcellQ : Metric.ball (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
      ((3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hmu : ((Gam'.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (aux_thm_prop_mass_parent H1 Mm sigma (n' + 1) k)).toReal ≤
      Lz * ((Gam'.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)))
        (aux_thm_prop_mass_cell H1 Mm sigma (n' + 1) k)).toReal) :
    ((Gam'.measure u) (Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2))).toReal +
      c * (volume (Metric.ball
        (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
        ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2))).toReal ≤
    Lz * (((Gam'.measure u) (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
        ((3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2))).toReal +
      c * (volume (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
        ((3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2))).toReal) := by
  have hn : 1 ≤ n' + 1 := by omega
  have hside := aux_mass_grid_cells_side_eq H1 (n' + 1)
  have hpar := aux_mass_grid_cells_parent_side H1 (n' + 1) hn
  simp only [Nat.add_sub_cancel] at hpar
  set mu : Measure (SpatialCoordinates d) :=
    Gam'.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d)) with hmudef
  have hplane' : ∀ (i : Fin d) (a : ℝ), mu {x : SpatialCoordinates d | x i = a} = 0 := by
    intro i a
    rw [hmudef, Measure.add_apply, hplane i a, Measure.smul_apply, Measure.restrict_apply' Q.isOpen.measurableSet]
    have h0 : volume ({x : SpatialCoordinates d | x i = a} ∩ (Q : Set (SpatialCoordinates d))) = 0 :=
      measure_mono_null Set.inter_subset_left (aux_affine_source_cells_mass_volume_plane i a)
    rw [h0]
    simp
  have hfin : Gam'.measure u Set.univ ≠ ⊤ := (Gam'.measure_univ_lt_top u hu).ne
  have hnufin : ∀ A : Set (SpatialCoordinates d), Gam'.measure u A ≠ ⊤ := fun A =>
    ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ A))
  -- parent
  have hP := aux_mass_grid_cells_measure_eq H1 Mm n' sigma
    (aux_thm_prop_mass_parent_idx H1 k) mu hplane'
  have hC := aux_mass_grid_cells_measure_eq H1 Mm (n' + 1) sigma k mu hplane'
  have hsideP : aux_thm_prop_mass_side H1 n' = (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) := by
    rw [hpar, hside]
  have hsideC := hside
  change mu (aux_thm_prop_mass_cell H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k)) = _ at hP
  rw [hsideP] at hP
  rw [hsideC] at hC
  change (mu (aux_thm_prop_mass_cell H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))).toReal ≤ _ at hmu
  rw [hP, hC] at hmu
  have hmeasP : MeasurableSet (Metric.ball
      (aux_thm_prop_mass_center H1 Mm sigma n' (aux_thm_prop_mass_parent_idx H1 k))
      ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2)) := Metric.isOpen_ball.measurableSet
  have hmeasC : MeasurableSet (Metric.ball (aux_thm_prop_mass_center H1 Mm sigma (n' + 1) k)
      ((3 : ℝ) ^ (-((H1 * (n' + 1) : ℕ) : ℤ)) / 2)) := Metric.isOpen_ball.measurableSet
  rw [hmudef, aux_mass_grid_cells_mu_toReal (Gam'.measure u) (Q : Set (SpatialCoordinates d)) _ c hc.le hmeasP hparQ (hnufin _) measure_ball_lt_top.ne,
    aux_mass_grid_cells_mu_toReal (Gam'.measure u) (Q : Set (SpatialCoordinates d)) _ c hc.le hmeasC hcellQ (hnufin _) measure_ball_lt_top.ne] at hmu
  exact hmu


/-- **Mass cells to the finite mesh of `lem_affine`.**  From the a.s. conclusion `Concl` of the Layer-1 core for
one killed cube `jQ` (arbitrary sides, arbitrary `c`) to the conclusion of `source_cell_approximation` for
arbitrary raw sides: the mass cell `(n = n' + 1, sigma, k)` is the mesh cell `(n', sigma, parent lattice index,
odd-grid digit)`, its catalogue index explicitly pairs `cell_index` with the observation depth, the padding (width `≥ 81`) gives the parent, comparison
ball and root inclusions, hyperplanes are null for `Γ`, and the constant is `2 · 3/2048 = 3/1024`. -/
theorem affine_source_cells_mass {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (jQ : ℕ)
    (GEj : Ω → DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
      DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ) (hwidth : 81 ≤ g.width)
    (Grid : Type) (origin : Grid → SpatialCoordinates d)
    (gridChoice : Fin (Fintype.card (Fin d → Fin g.Mm)) → Grid)
    (hgc : ∀ sigma : Fin d → Fin g.Mm,
      origin (gridChoice (Fintype.equivFin (Fin d → Fin g.Mm) sigma)) =
        fun i => ((sigma i).val : ℝ) / (g.Mm : ℝ) + 1 / 2)
    (ZLim DLim : (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errLim ratioLim : (ℕ × ℕ) → Unit → BilateralField d → ℝ)
    (hConcl : aux_affine_source_cells_env_Concl (z jQ) (r jQ) (hr jQ) P field GEj g.gamma
      g.zeta (3 / 2048) g.H1 k0 lambdaLim cell epshom cdet Grid origin
      (Fintype.card (Fin d → Fin g.Mm)) gridChoice
      (fun c : ℕ × ℕ => g.H1 * c.2) (fun c => z c.1) ZLim DLim loLim hiLim errLim
      ratioLim)
    (hmass : ∀ (H1 Mm n : ℕ) (Cwidth gamma : ℝ) (sigma : Fin d → Fin Mm) (k : Fin d → ℤ),
      1 ≤ Cwidth * ((3 : ℝ) ^ H1) ^ gamma →
      aux_thm_prop_mass_padded H1 Mm Cwidth gamma sigma n k →
      closure (aux_thm_prop_mass_parent H1 Mm sigma n k) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      ∃ jC jP : ℕ,
        z jC = aux_thm_prop_mass_center H1 Mm sigma n k ∧ r jC = aux_thm_prop_mass_side H1 n ∧
        z jP = aux_thm_prop_mass_center H1 Mm sigma n k ∧ r jP = 3 * aux_thm_prop_mass_side H1 n ∧
        closure (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)))
    (hGood : ∀ n zc, aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
      ∀ om ∈ Good n zc, field om ∈ gcat_good k0 lambdaLim cell epshom cdet
        (ZLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (DLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (loLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (hiLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (errLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (ratioLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))) :
    ∀ᵐ omega ∂P,
      ∀ (E' : _root_.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GEj omega) u) →
      (∃ C, DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      (∀ u ∈ E'.toClosedForm.domain, ∀ (i : Fin d) (a : ℝ),
        Gam'.measure u {x : SpatialCoordinates d | x i = a} = 0) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ hu : GEj omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
      ∃ baseMesh : ℝ, 0 < baseMesh ∧
        ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
        ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        omega ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
        aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
        closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
        let mu := Gam'.measure (GEj omega f) + ENNReal.ofReal c •
          volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
        (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
          ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
            (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
          (⇑(GEj omega f) =ᵐ[volume.restrict
            (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
          aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
            E'.toClosedForm Gam' (GEj omega f) U c
            (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
              (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
                Set (SpatialCoordinates d)) := by
  unfold aux_affine_source_cells_env_Concl at hConcl
  filter_upwards [hConcl] with omega hω
  intro E' Gam' hE' hcore' hplane f hf hu c hc
  obtain ⟨fc, hfcs, hfcc, hfts, hfae⟩ := hf
  obtain ⟨baseMesh, hpos, hcells⟩ := hω E' Gam' hE' hcore' f ⟨fc, hfcs, hfae⟩ hu c hc
  refine ⟨baseMesh, hpos, ?_⟩
  intro n hn hbm sigma k hgood hpad hparent mu hmu
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hH1 := g.H1_pos
  obtain ⟨jC, jP, hjC1, hjC2, hjP1, hjP2, hjPQ⟩ :=
    hmass g.H1 g.Mm (n' + 1) g.width g.gamma sigma k g.padded_width hpad hparent
  have havail : aux_thm_prop_cell_available z r
      (aux_thm_prop_mass_center g.H1 g.Mm sigma (n' + 1) k)
      (aux_thm_prop_mass_side g.H1 (n' + 1)) := ⟨(jC, jP), hjC1, hjC2, hjP1, hjP2⟩
  have hgm := hGood (n' + 1) _ havail omega hgood
  obtain ⟨hcz, hcr, -, -⟩ := aux_thm_prop_cell_index_spec z r _ _ havail
  have hgeom := aux_affine_source_cells_mass_cell_geom g.H1 g.Mm n' hH1 g.gamma
    g.width g.gamma_mem.1.le hwidth sigma k _ hpad hparent
  have htuple := aux_affine_source_cells_mass_tuple g.H1 g.Mm n' sigma k
  have hside := aux_mass_grid_cells_side_eq g.H1 (n' + 1)
  have hzP' : (fun i => origin (gridChoice (Fintype.equivFin (Fin d → Fin g.Mm) sigma)) i +
      ((3 : ℝ) ^ g.H1 * (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ))) *
        (((aux_thm_prop_mass_parent_idx g.H1 k i - ((3 : ℤ) ^ (g.H1 * n') - 1) / 2 : ℤ)) : ℝ)) =
      aux_thm_prop_mass_center g.H1 g.Mm sigma n' (aux_thm_prop_mass_parent_idx g.H1 k) := by
    rw [hgc]
    exact htuple.1.symm
  have hz' : oddGridCenter (fun i => origin (gridChoice (Fintype.equivFin (Fin d → Fin g.Mm) sigma)) i +
      ((3 : ℝ) ^ g.H1 * (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ))) *
        (((aux_thm_prop_mass_parent_idx g.H1 k i - ((3 : ℤ) ^ (g.H1 * n') - 1) / 2 : ℤ)) : ℝ))
      ((3 : ℝ) ^ g.H1 * (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ))) (subdivisionHalfWidth g.H1)
      (aux_mass_grid_cells_digit g.H1 k) =
      aux_thm_prop_mass_center g.H1 g.Mm sigma (n' + 1) k := by
    rw [hzP']
    exact htuple.2.symm
  have hcl := hcells n' (Fintype.equivFin (Fin d → Fin g.Mm) sigma)
    (fun i => aux_thm_prop_mass_parent_idx g.H1 k i - ((3 : ℤ) ^ (g.H1 * n') - 1) / 2)
    (aux_mass_grid_cells_digit g.H1 k)
    ((aux_thm_prop_cell_index z r (aux_thm_prop_mass_center g.H1 g.Mm sigma (n' + 1) k)
      (aux_thm_prop_mass_side g.H1 (n' + 1))).1, n' + 1)
  have h1 := hcz.trans hz'.symm
  have h2 : g.H1 * (n' + 1) = g.H1 * (n' + 1) := rfl
  have h3 := hgeom.1
  have h4 := hgeom.2.1
  have h5 := hgeom.2.2
  have hparQ := h3
  have hcellQ : Metric.ball (aux_thm_prop_mass_center g.H1 g.Mm sigma (n' + 1) k)
      ((3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ)) / 2) ⊆
      (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) := by
    refine Metric.ball_subset_closedBall.trans ?_
    refine (Metric.closedBall_subset_closedBall ?_).trans (hgeom.2.1.trans hgeom.1)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hlam := aux_affine_source_cells_mass_mu_to_lambda
    (centeredCube (z jQ) (r jQ) (hr jQ)) E' Gam' (GEj omega f) hu (fun i a => hplane _ hu i a) c hc
    g.H1 g.Mm n' sigma k (((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta)) hparQ hcellQ hmu
  rw [← hzP'] at h3 h4 hlam
  rw [← hz'] at h4 h5 hlam
  obtain ⟨U, hU1, hU2, hU3⟩ := hcl h1 h2 h3 h4 h5
  have hbm' : (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ)) ≤ baseMesh := by
    rw [← hside]
    exact hbm
  obtain ⟨pc, hpc⟩ := hU3 hbm' hgm hlam
  obtain ⟨Lambda, hglb, hne, hle⟩ := hpc
  have hq : (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma (n' + 1) k)
      (aux_thm_prop_mass_side g.H1 (n' + 1)) (aux_thm_prop_grid_side_pos g.H1 (n' + 1)) :
        Set (SpatialCoordinates d)) =
      Metric.ball (oddGridCenter (fun i => origin (gridChoice (Fintype.equivFin (Fin d → Fin g.Mm) sigma)) i +
      ((3 : ℝ) ^ g.H1 * (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ))) *
        (((aux_thm_prop_mass_parent_idx g.H1 k i - ((3 : ℤ) ^ (g.H1 * n') - 1) / 2 : ℤ)) : ℝ))
      ((3 : ℝ) ^ g.H1 * (3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ))) (subdivisionHalfWidth g.H1)
      (aux_mass_grid_cells_digit g.H1 k))
      ((3 : ℝ) ^ (-((g.H1 * (n' + 1) : ℕ) : ℤ)) / 2) := by
    rw [hz', ← hside]
    rfl
  refine ⟨U, hU1, hU2, pc, Lambda, ?_, ?_, ?_⟩
  · rw [hq]
    exact hglb
  · rw [hq]
    exact hne
  · rw [hq]
    refine hle.trans (le_of_eq ?_)
    ring


end Paper
end
