import SubdiffusiveProcess.Paper.thm_prop_base
import SubdiffusiveProcess.Paper.conv_represented_env_interface
import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids
import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
import SubdiffusiveProcess.Paper.conv_represented_limit_planes
import SubdiffusiveProcess.Paper.limit_form_package_controls
import SubdiffusiveProcess.Paper.limit_form_package_side
import SubdiffusiveProcess.Lane4.GoodCellCatalogue
import SubdiffusiveProcess.Paper.affine_source_cells_env
import SubdiffusiveProcess.Paper.represented_same_law_in_measure
import SubdiffusiveProcess.Paper.thm_prop_affine_ellipticity_env_core
import SubdiffusiveProcess.Paper.thm_prop_env_measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The coarse-grained chart matrix of the cutoff coefficient on a cell is its normalized affine response. -/
theorem aux_thm_prop_env_chart_response_cutoff {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) :
    p ⬝ᵥ (Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H omega N z hr) z r).coeffOn
        (Homogenization.originCube d 0))).mulVec p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H omega N z hr) p /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  exact aux_thm_prop_chart_matrix_response I z r hr hP
    (Lane4.cutoffPositiveCoefficient M H omega N z hr)
    (cutoffCoefficient M H omega N)
    (Lane4.cutoffCoefficient_continuous M H omega N)
    (fun x => Lane4.cutoffCoefficient_pos M H omega N x)
    (aux_lem_replace_large_cube_cutoff_positive_coe M H omega N z hr) p

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The reference scalar `s_N` converges along a cutoff sequence: only the deterministic ratio moves. -/
theorem aux_thm_prop_env_sN_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) (k : ℕ) (e : ℝ)
    (hkappa : Tendsto (fun n =>
      (let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
       kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n))) atTop (𝓝 e))
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    Tendsto (fun n => SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z omega) atTop
      (𝓝 (e * Real.exp (H omega z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), omega (-j) z))) := by
  have hev : ∀ᶠ n in atTop, (k : ℤ) ≤ (phi n : ℤ) := by
    have h := hphi.eventually_ge_atTop k
    filter_upwards [h] with n hn
    exact_mod_cast hn
  let kappa : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
  have hfun : (fun n => kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n) *
      Real.exp (H omega z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), omega (-j) z)) =ᶠ[atTop]
      (fun n => SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z omega) := by
    filter_upwards [hev] with n hn
    simp only [SubdiffusiveProcess.gcat_sN, if_pos hn, if_pos (Int.natCast_nonneg k), kappa]
  refine Tendsto.congr' hfun ?_
  simpa only [kappa] using
    hkappa.mul_const (Real.exp (H omega z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), omega (-j) z))

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- For large cutoffs `s_N` factors into a deterministic ratio and a field factor. -/
theorem aux_thm_prop_env_sN_factor {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N k : ℕ) (hk : k ≤ N)
    (z : SpatialCoordinates d) (β : BilateralField d) :
    SubdiffusiveProcess.gcat_sN M H N (k : ℤ) z β =
      (let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
       kappa (((N : ℤ) - (k : ℤ)).toNat) / kappa N) *
        Real.exp (H β z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), β (-j) z) := by
  unfold SubdiffusiveProcess.gcat_sN
  rw [if_pos (by exact_mod_cast hk)]
  dsimp only
  rw [if_pos (Int.natCast_nonneg k)]

end Part2

section Part3
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The self-root coarse chart matrix array of a cell, read at the cell itself. -/
theorem aux_thm_prop_env_root_self_matrix {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Zs : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (harr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim)
    (r : ℝ) (hr : 0 < r) (hrk : r = (3 : ℝ) ^ (-(k : ℤ)))  :
    ∀ i j : Fin d, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => ((SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r).coeffOn
            (Homogenization.originCube d 0))) i j) atTop
      (fun β => AELim (0, fun _ => 1) β i j) := by
  intro i j
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := harr
  let U0 : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
  have hshift : SubdiffusiveProcess.gcat_shift (d := d) (fun _ => (1 : Fin 3)) = 0 := by
    funext t
    simp [SubdiffusiveProcess.gcat_shift]
  have hlev : SubdiffusiveProcess.gcat_rootLevel gH k U0 = (k : ℤ) := by
    simp only [U0, SubdiffusiveProcess.gcat_rootLevel, SubdiffusiveProcess.gcat_factor]
    simp
  have hside : SubdiffusiveProcess.gcat_rootSide gH k U0 = r := by
    rw [SubdiffusiveProcess.gcat_rootSide, hlev]
    exact hrk.symm
  have hcent : SubdiffusiveProcess.gcat_rootCentre gH k z U0 = z := by
    simp only [SubdiffusiveProcess.gcat_rootCentre, U0, hshift, smul_zero, add_zero]
  have key : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      zc = z → rc = r → ∀ (N : ℕ) (β : BilateralField d),
      I.chart zc rc hrc (Lane4.cutoffPositiveCoefficient M H β N zc hrc) zc rc
        = I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β N z hr) z r := by
    intro zc rc hrc hz hrr N β
    subst hz
    subst hrr
    rfl
  refine TendstoInMeasure.congr (fun n => Filter.Eventually.of_forall (fun β => ?_))
    (Filter.Eventually.of_forall (fun _ => rfl)) (h5 U0 i j)
  have hkey := key (SubdiffusiveProcess.gcat_rootCentre gH k z U0)
    (SubdiffusiveProcess.gcat_rootSide gH k U0) (zpow_pos (by norm_num) _) hcent hside (phi n) β
  rw [hkey, hlev, hcent]

end Part3

section Part4
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The self-root array of a cell, read at the cell itself: `lam/s_N` and `Lam/s_N` for the cutoff coefficient converge in measure. -/
theorem aux_thm_prop_env_root_self_arrays {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Zs : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (harr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim)
    (r : ℝ) (hr : 0 < r) (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => I.lam z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β) atTop
      (loLim (0, fun _ => 1)) ∧
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => I.Lam z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β) atTop
      (hiLim (0, fun _ => 1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := harr
  have hlev : gcat_rootLevel gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)) = (k : ℤ) := by
    simp only [gcat_rootLevel, gcat_factor]
    norm_num
  have hside : gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)) = r := by
    rw [gcat_rootSide, hlev]
    exact hrk.symm
  have hcent : gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)) = z := by
    have hsh : gcat_shift ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)).2 = 0 := by
      funext i
      simp only [gcat_shift]
      norm_num
    rw [gcat_rootCentre, hside, hsh, smul_zero, add_zero]
  have key : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      zc = z → rc = r → ∀ (N : ℕ) (β : BilateralField d),
      I.lam zc rc hrc (Lane4.cutoffPositiveCoefficient M H β N zc hrc) zc rc sigma 2 =
      I.lam z r hr (Lane4.cutoffPositiveCoefficient M H β N z hr) z r sigma 2 := by
    intro zc rc hrc hz hrr N β
    subst hz
    subst hrr
    rfl
  have keyL : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      zc = z → rc = r → ∀ (N : ℕ) (β : BilateralField d),
      I.Lam zc rc hrc (Lane4.cutoffPositiveCoefficient M H β N zc hrc) zc rc sigma 2 =
      I.Lam z r hr (Lane4.cutoffPositiveCoefficient M H β N z hr) z r sigma 2 := by
    intro zc rc hrc hz hrr N β
    subst hz
    subst hrr
    rfl
  constructor
  · rw [show (fun n β => I.lam z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r sigma 2 /
        gcat_sN M H (phi n) (k : ℤ) z β)
      = (fun n omega => I.lam (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (zpow_pos (by norm_num) _)
          (Lane4.cutoffPositiveCoefficient M H omega (phi n)
            (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (zpow_pos (by norm_num) _))
          (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) sigma 2 /
        gcat_sN M H (phi n) (gcat_rootLevel gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) omega) from by
      funext n β
      rw [key (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
            (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) _ hcent hside (phi n) β,
        hlev, hcent]]
    exact h3 ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))
  · rw [show (fun n β => I.Lam z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r sigma 2 /
        gcat_sN M H (phi n) (k : ℤ) z β)
      = (fun n omega => I.Lam (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (zpow_pos (by norm_num) _)
          (Lane4.cutoffPositiveCoefficient M H omega (phi n)
            (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (zpow_pos (by norm_num) _))
          (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) sigma 2 /
        gcat_sN M H (phi n) (gcat_rootLevel gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) omega) from by
      funext n β
      rw [keyL (gcat_rootCentre gH k z ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
            (gcat_rootSide gH k ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))) _ hcent hside (phi n) β,
        hlev, hcent]]
    exact h4 ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3))

end Part4

section Part5
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The quadratic form of the normalized coarse chart matrices converges in measure. -/
theorem aux_thm_prop_env_Q_inMeasure {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Zs : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (harr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim)
    (r : ℝ) (hr : 0 < r) (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) 
    (p : Fin d → ℝ) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => p ⬝ᵥ (((SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r).coeffOn
            (Homogenization.originCube d 0)))).mulVec p) atTop
      (fun β => p ⬝ᵥ (AELim (0, fun _ => 1) β).mulVec p) := by
  let A : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun n β =>
    (SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β)⁻¹ •
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r).coeffOn
          (Homogenization.originCube d 0))
  let B : BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun β => AELim (0, fun _ => 1) β
  change TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n β => p ⬝ᵥ (A n β).mulVec p) atTop
    (fun β => p ⬝ᵥ (B β).mulVec p)
  have hconv : ∀ i j : Fin d,
      TendstoInMeasure (chaosSampleLaw M).toMeasure (fun n β => (A n β) i j) atTop
        (fun β => (B β) i j) :=
    fun i j => aux_thm_prop_env_root_self_matrix I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim harr r hr hrk i j
  have hmul_const : ∀ (c : ℝ) (F : ℕ → BilateralField d → ℝ) (G : BilateralField d → ℝ),
      TendstoInMeasure (chaosSampleLaw M).toMeasure F atTop G →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n β => F n β * c) atTop (fun β => G β * c) := by
    intro c F G hF
    rw [tendstoInMeasure_iff_dist] at hF ⊢
    intro ε hε
    have hpos : (0 : ℝ) < |c| + 1 := by positivity
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n => (chaosSampleLaw M).toMeasure {β | ε / (|c| + 1) ≤ dist (F n β) (G β)})
      tendsto_const_nhds (hF (ε / (|c| + 1)) (div_pos hε hpos))
      (Eventually.of_forall fun n => zero_le _) ?_
    refine Eventually.of_forall fun n => measure_mono ?_
    intro β hβ
    simp only [Set.mem_setOf_eq] at hβ ⊢
    rw [div_le_iff₀ hpos]
    calc ε ≤ dist (F n β * c) (G β * c) := hβ
      _ = |F n β - G β| * |c| := by
            rw [Real.dist_eq]
            have hsub : F n β * c - G β * c = (F n β - G β) * c := by ring
            rw [hsub, abs_mul]
      _ ≤ |F n β - G β| * (|c| + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg c]) (abs_nonneg _)
      _ = dist (F n β) (G β) * (|c| + 1) := by rw [Real.dist_eq]
  have hscaled : ∀ i j : Fin d,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n β => ((A n β) i j * p i) * p j) atTop
        (fun β => ((B β) i j * p i) * p j) := by
    intro i j
    exact hmul_const (p j) _ _ (hmul_const (p i) _ _ (hconv i j))
  have hinner : ∀ i : Fin d,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n β => ∑ j, ((A n β) i j * p i) * p j) atTop
        (fun β => ∑ j, ((B β) i j * p i) * p j) :=
    fun i => aux_env_tendstoInMeasure_finset_sum Finset.univ
      (fun j n β => ((A n β) i j * p i) * p j)
      (fun j β => ((B β) i j * p i) * p j) (fun j _ => hscaled i j)
  have hsum : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => ∑ i, ∑ j, ((A n β) i j * p i) * p j) atTop
      (fun β => ∑ i, ∑ j, ((B β) i j * p i) * p j) :=
    aux_env_tendstoInMeasure_finset_sum Finset.univ
      (fun i n β => ∑ j, ((A n β) i j * p i) * p j)
      (fun i β => ∑ j, ((B β) i j * p i) * p j) (fun i _ => hinner i)
  refine TendstoInMeasure.congr ?_ ?_ hsum
  · intro n
    refine EventuallyEq.of_eq (funext fun β => ?_)
    exact (aux_thm_prop_matrix_quadratic_eq (A n β) p).symm
  · refine EventuallyEq.of_eq (funext fun β => ?_)
    exact (aux_thm_prop_matrix_quadratic_eq (B β) p).symm

end Part5

section Part6
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The normalized affine response is `s_N` times the quadratic form of the normalized chart matrix. -/
theorem aux_thm_prop_env_resp_eq_sN_mul {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (β : BilateralField d) (N k : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) :
    affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H β N z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      SubdiffusiveProcess.gcat_sN M H N (k : ℤ) z β *
        (p ⬝ᵥ (((SubdiffusiveProcess.gcat_sN M H N (k : ℤ) z β)⁻¹ •
          Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β N z hr) z r).coeffOn
              (Homogenization.originCube d 0)))).mulVec p) := by
  have hpos : 0 < SubdiffusiveProcess.gcat_sN M H N (k : ℤ) z β := by
    unfold SubdiffusiveProcess.gcat_sN
    split_ifs with h
    · apply mul_pos
      · apply div_pos
        · exact mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
        · exact mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
      · exact Real.exp_pos _
    · exact one_pos
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      aux_thm_prop_env_chart_response_cutoff I M H β N z r hr hP p,
      Measure.real_def, mul_inv_cancel_left₀ (ne_of_gt hpos)]

end Part6

section Part7
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- The normalized affine response of a cell converges in measure on the original space. -/
theorem thm_prop_env_cell_arrays {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Zs : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (harr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim)
    (r : ℝ) (hr : 0 < r) (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) 
    (hHm : Measurable H) (hAEm : ∀ i j : Fin d, Measurable (fun β => AELim (0, fun _ => 1) β i j))
    (hphi : Tendsto phi atTop atTop) (e : ℝ)
    (hkappa : Tendsto (fun n =>
      (let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
       kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n))) atTop (𝓝 e))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) atTop
      (fun β => (Real.exp (H β z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), β (-j) z) * (e * 1)) *
        (p ⬝ᵥ (AELim (0, fun _ => 1) β).mulVec p)) := by
  let sm : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun n β =>
    Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((I.chart z r hr (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) z r).coeffOn
        (Homogenization.originCube d 0))
  let entry : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun n β =>
    (SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β)⁻¹ • sm n β
  let w : BilateralField d → ℝ :=
    fun β => Real.exp (H β z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), β (-j) z)
  let ρ : ℕ → ℝ := fun n =>
    (let kappa : ℕ → ℝ := fun J =>
       Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
         SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
     kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n))
  let Q : ℕ → BilateralField d → ℝ := fun n β => p ⬝ᵥ (entry n β).mulVec p
  let Qlim : BilateralField d → ℝ := fun β => p ⬝ᵥ (AELim (0, fun _ => 1) β).mulVec p
  have hvol : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := rfl
  have hsinz : ∀ n β, SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β ≠ 0 := by
    intro n β
    rw [SubdiffusiveProcess.gcat_sN]
    split
    · dsimp only
      apply mul_ne_zero
      · apply div_ne_zero
        · exact ne_of_gt (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
        · exact ne_of_gt (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
      · exact ne_of_gt (Real.exp_pos _)
    · norm_num
  have hscale : ∀ (c : ℝ) (B : Matrix (Fin d) (Fin d) ℝ),
      p ⬝ᵥ (c • B).mulVec p = c * (p ⬝ᵥ B.mulVec p) := by
    intro c B
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hdot : ∀ (A : Matrix (Fin d) (Fin d) ℝ),
      p ⬝ᵥ A.mulVec p = ∑ i, ∑ j, (p i * p j) * A i j := by
    intro A
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hresp : ∀ n β, p ⬝ᵥ (sm n β).mulVec p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) p /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro n β
    dsimp only [sm]
    exact aux_thm_prop_env_chart_response_cutoff I M H β (phi n) z r hr hP p
  have hQeq : ∀ n β, Q n β =
      (SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β)⁻¹ *
        (affineDirichletResponse (centeredCube_isBounded z hr) hP
          (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) p /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro n β
    dsimp only [Q, entry]
    rw [hscale, hresp n β]
  have hEq : ∀ n β,
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H β (phi n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β * Q n β := by
    intro n β
    rw [hQeq n β, ← hvol]
    rw [← mul_assoc, mul_inv_cancel₀ (hsinz n β), one_mul]
  have hQ'lim : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => ∑ i, ∑ j, (p i * p j) * (entry n β) i j) atTop
      (fun β => ∑ i, ∑ j, (p i * p j) * (AELim (0, fun _ => 1) β) i j) := by
    apply aux_env_tendstoInMeasure_finset_sum Finset.univ
    intro i _
    apply aux_env_tendstoInMeasure_finset_sum Finset.univ
    intro j _
    have hroot := (aux_thm_prop_env_root_self_matrix I M H s sigma gH cbuf Zs Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim harr r hr hrk) i j
    have h2 := aux_env_tendstoInMeasure_mul2
      (P := (chaosSampleLaw M).toMeasure)
      (X := fun n β => (entry n β) i j)
      (Y := fun β => (AELim (0, fun _ => 1) β) i j)
      hroot (hAEm i j).aemeasurable (fun _ => (1 : ℝ)) 1 tendsto_const_nhds
      (fun _ => p i * p j) measurable_const
    simpa only [one_mul] using h2
  have hQlim : TendstoInMeasure (chaosSampleLaw M).toMeasure Q atTop Qlim := by
    refine TendstoInMeasure.congr'
      (f := fun n β => ∑ i, ∑ j, (p i * p j) * (entry n β) i j)
      (g := fun β => ∑ i, ∑ j, (p i * p j) * (AELim (0, fun _ => 1) β) i j) ?_ ?_ hQ'lim
    · filter_upwards with n
      filter_upwards with β
      exact (hdot (entry n β)).symm
    · filter_upwards with β
      exact (hdot (AELim (0, fun _ => 1) β)).symm
  have hQlimm : AEMeasurable Qlim (chaosSampleLaw M).toMeasure := by
    have hm : Measurable (fun β => ∑ i, ∑ j, (p i * p j) * (AELim (0, fun _ => 1) β) i j) := by
      apply Finset.measurable_sum
      intro i _
      apply Finset.measurable_sum
      intro j _
      exact (hAEm i j).const_mul _
    have heq : Qlim = fun β => ∑ i, ∑ j, (p i * p j) * (AELim (0, fun _ => 1) β) i j := by
      funext β
      exact hdot _
    rw [heq]
    exact hm.aemeasurable
  have hw : Measurable w := by
    dsimp only [w]
    apply Real.measurable_exp.comp
    apply Measurable.add
    · exact ((continuous_eval_const z).measurable).comp hHm
    · apply Finset.measurable_sum
      intro j _
      exact ((continuous_eval_const z).measurable).comp (measurable_pi_apply (-j))
  have hρ : Tendsto ρ atTop (𝓝 e) := hkappa
  have hev : ∀ᶠ n in atTop, k ≤ phi n := hphi.eventually (eventually_ge_atTop k)
  have hsn : ∀ᶠ n in atTop, ∀ β, SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β = ρ n * w β := by
    filter_upwards [hev] with n hn β
    have hle : (k : ℤ) ≤ ((phi n : ℕ) : ℤ) := by exact_mod_cast hn
    have h1 : SubdiffusiveProcess.gcat_sN M H (phi n) (k : ℤ) z β =
        (let kappa : ℕ → ℝ := fun J =>
           Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
             SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)) * w β := by
      rw [show w β = Real.exp (H β z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), β (-j) z) from rfl]
      simp only [SubdiffusiveProcess.gcat_sN, if_pos hle, Int.natCast_nonneg, ↓reduceIte]
    rw [h1]
  have hmain : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => w β * (ρ n * Q n β)) atTop
      (fun β => w β * (e * Qlim β)) :=
    aux_env_tendstoInMeasure_mul2 (P := (chaosSampleLaw M).toMeasure)
      Q Qlim hQlim hQlimm ρ e hρ w hw
  refine TendstoInMeasure.congr'
    (f := fun n β => w β * (ρ n * Q n β))
    (g := fun β => w β * (e * Qlim β)) ?_ ?_ hmain
  · filter_upwards [hsn] with n hn
    apply Filter.EventuallyEq.of_eq
    funext β
    rw [hEq n β, hn β]
    ring
  · apply Filter.EventuallyEq.of_eq
    funext β
    dsimp only [w, Qlim]
    ring

end Part7

end Paper
end
