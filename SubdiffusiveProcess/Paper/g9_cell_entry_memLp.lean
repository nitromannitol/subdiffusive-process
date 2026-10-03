module

public import SubdiffusiveProcess.Paper.chart_coords_measurable
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_moment_uniform
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace Paper

/-! ### Geometry: a sub-cube of the origin is a descendant of the origin at its own scale. -/

theorem aux_g9_cell_entry_memLp_cubeScaleFactor_pos {d : ℕ} (Q : Homogenization.TriadicCube d) :
    0 < Homogenization.cubeScaleFactor Q := by
  unfold Homogenization.cubeScaleFactor
  exact zpow_pos (by norm_num) _

theorem aux_g9_cell_entry_memLp_openCubeSet_subset_cubeSet {d : ℕ}
    (Q : Homogenization.TriadicCube d) :
    Homogenization.openCubeSet Q ⊆ Homogenization.cubeSet Q := by
  intro x hx i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

/-- The "index center" point of a triadic cube lies in its own open cube set. -/
theorem aux_g9_cell_entry_memLp_center_mem {d : ℕ} (Q : Homogenization.TriadicCube d) :
    (fun i => (Q.index i : ℝ) * Homogenization.cubeScaleFactor Q) ∈ Homogenization.openCubeSet Q := by
  have hpos := aux_g9_cell_entry_memLp_cubeScaleFactor_pos Q
  intro i
  constructor <;> nlinarith

/-- `openCubeSet` as a coordinatewise product of open intervals. -/
theorem aux_g9_cell_entry_memLp_openCubeSet_eq_pi {d : ℕ} (Q : Homogenization.TriadicCube d) :
    Homogenization.openCubeSet Q =
      Set.univ.pi (fun i : Fin d => Set.Ioo
        (((Q.index i : ℝ) - 1 / 2) * Homogenization.cubeScaleFactor Q)
        (((Q.index i : ℝ) + 1 / 2) * Homogenization.cubeScaleFactor Q)) := by
  ext x
  simp only [Homogenization.openCubeSet, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]

/-- If `R`'s open cube is contained in the open origin cube (scale `0`), then `R.scale ≤ 0`. -/
theorem aux_g9_cell_entry_memLp_scale_le_zero {d : ℕ} (hd : 2 ≤ d)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    R.scale ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hRfactor : 0 < Homogenization.cubeScaleFactor R :=
    aux_g9_cell_entry_memLp_cubeScaleFactor_pos R
  rw [aux_g9_cell_entry_memLp_openCubeSet_eq_pi, aux_g9_cell_entry_memLp_openCubeSet_eq_pi] at hR
  have hne : (Set.univ.pi (fun i : Fin d => Set.Ioo
      (((R.index i : ℝ) - 1 / 2) * Homogenization.cubeScaleFactor R)
      (((R.index i : ℝ) + 1 / 2) * Homogenization.cubeScaleFactor R))).Nonempty := by
    rw [Set.univ_pi_nonempty_iff]
    intro i
    exact Set.nonempty_Ioo.mpr (by nlinarith)
  have hR' := (Set.pi_subset_pi_iff.mp hR).resolve_right hne.ne_empty
  have i0 : Fin d := ⟨0, by omega⟩
  have hcontain := hR' i0 (Set.mem_univ i0)
  have hlt : (((R.index i0 : ℝ) - 1 / 2) * Homogenization.cubeScaleFactor R) <
      (((R.index i0 : ℝ) + 1 / 2) * Homogenization.cubeScaleFactor R) := by nlinarith
  have hsub := (Set.Ioo_subset_Ioo_iff hlt).mp hcontain
  have hQfactor : Homogenization.cubeScaleFactor (Homogenization.originCube d 0) = 1 := by
    norm_num [Homogenization.cubeScaleFactor, Homogenization.originCube]
  have hQindex : (Homogenization.originCube d 0).index i0 = 0 := rfl
  rw [hQfactor, hQindex] at hsub
  obtain ⟨hlo, hhi⟩ := hsub
  push_cast at hlo hhi
  have h1le : (1 : ℤ) ≤ R.scale := hcon
  have h3le : (3 : ℝ) ^ (1 : ℤ) ≤ (3 : ℝ) ^ R.scale := zpow_le_zpow_right₀ (by norm_num) h1le
  have hfactor3 : (3 : ℝ) ≤ Homogenization.cubeScaleFactor R := by
    unfold Homogenization.cubeScaleFactor; simpa using h3le
  nlinarith

/-- A triadic cube whose open cube set is contained in the open origin cube (scale `0`) is a
descendant of the origin cube at its own scale. -/
theorem aux_g9_cell_entry_memLp_mem_descendantsAtScale {d : ℕ} (hd : 2 ≤ d)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) R.scale := by
  have hscale : R.scale ≤ 0 := aux_g9_cell_entry_memLp_scale_le_zero hd R hR
  have hscale' : R.scale ≤ (Homogenization.originCube d 0).scale := by
    simpa [Homogenization.originCube] using hscale
  set n : ℕ := ((Homogenization.originCube d 0).scale - R.scale).toNat with hndef
  have hx : (fun i => (R.index i : ℝ) * Homogenization.cubeScaleFactor R) ∈
      Homogenization.openCubeSet R := aux_g9_cell_entry_memLp_center_mem R
  have hxQ : (fun i => (R.index i : ℝ) * Homogenization.cubeScaleFactor R) ∈
      Homogenization.cubeSet (Homogenization.originCube d 0) :=
    aux_g9_cell_entry_memLp_openCubeSet_subset_cubeSet _ (hR hx)
  obtain ⟨S, hSmem, hxS⟩ := Homogenization.exists_mem_descendantsAtDepth_of_mem_cubeSet n hxQ
  have hxR : (fun i => (R.index i : ℝ) * Homogenization.cubeScaleFactor R) ∈
      Homogenization.cubeSet R := aux_g9_cell_entry_memLp_openCubeSet_subset_cubeSet _ hx
  have hSscale : S.scale = (Homogenization.originCube d 0).scale - (n : ℤ) :=
    Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hSmem
  have hSscale' : S.scale = R.scale := by
    rw [hSscale, hndef, Int.toNat_of_nonneg (by omega)]
    ring
  have hSR : S = R := by
    by_contra hne
    have hdisj := Homogenization.disjoint_cubeSet_of_scale_eq_of_ne hSscale' hne
    exact (Set.disjoint_left.mp hdisj) hxS hxR
  subst hSR
  rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth (Homogenization.originCube d 0)
    hscale', ← hndef]
  exact hSmem

/-! ### Deterministic entry bounds by the coarse matrix norms. -/

theorem aux_g9_cell_entry_memLp_sigmaStarInv_entry_le {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d) (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (i j : Fin d) :
    |Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
        (F.coeffOn R) i j| ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F := by
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  rw [Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  exact Homogenization.Book.Ch02.abs_entry_le_matrixOperatorNorm _ i j

theorem aux_g9_cell_entry_memLp_sigma_entry_le {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (I : Paper.in_J d) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube w r hr)) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (i j : Fin d) :
    |Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr a w r).coeffOn R) i j| ≤
      Homogenization.Book.Ch02.coarseBMatrixNorm R (I.chart w r hr a w r) := by
  have heq := aux_core_sigmaCoarse_eq_bCoarse_R hd I w r hr a R hR
  unfold Homogenization.Book.Ch02.coarseBMatrixNorm
  rw [Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm, heq]
  exact Homogenization.Book.Ch02.abs_entry_le_matrixOperatorNorm _ i j

/-- Paper 2749--2753, cell-level entries: for every triadic cube `R` of the unit root, both coarse
entries `sigma(R)` and `sigma_*^{-1}(R)` of the unit chart `F K ω` are integrable, for every
cutoff `K`, below one disorder threshold. -/
theorem g9_cell_entry_memLp {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (R : Homogenization.TriadicCube d),
        Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ (b : Bool) (i j : Fin d) (K : ℕ),
        MemLp (fun omega => if b then
              Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
                ((aux_U2_unitChart I M H omega K).coeffOn R) i j
            else Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
                ((aux_U2_unitChart I M H omega K).coeffOn R) i j)
          1 (chaosSampleLaw M).toMeasure := by
  obtain ⟨delta0, A, hdelta0, hA, Cfn, hCfn_pos, hCfn_mono, hbound⟩ :=
    lem_prefix_limit_g9_cell_moment_uniform hd I Pc Xc W Sf D Cresp hCresp 1 (le_refl 1)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM Rm hRm Sreg It H hH R hR b i j K
  have hHm : Measurable H := hH.1
  have hmemR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-(((-R.scale).toNat : ℕ) : ℤ)) := by
    have h1 := aux_g9_cell_entry_memLp_mem_descendantsAtScale hd R hR
    have hs := aux_g9_cell_entry_memLp_scale_le_zero hd R hR
    have h2 : (-(((-R.scale).toNat : ℕ) : ℤ)) = R.scale := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    rwa [h2]
  have hbM := hbound M hM Rm hRm Sreg It H hH
  dsimp only at hbM
  obtain ⟨hbmoments, -⟩ := hbM
  obtain ⟨hbSigmaStarInv, hbB, -⟩ := hbmoments ((-R.scale).toNat) R hmemR K
  rw [ENNReal.ofReal_one] at hbSigmaStarInv hbB
  have hBmeas : Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) := by
    apply aux_measlam_matrixNorm
    intro i' j'
    exact aux_core_bCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i' j'
  have hSigmaStarInvMeas : Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) := by
    apply aux_measlam_matrixNorm
    intro i' j'
    exact aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i' j'
  have hBMemLp : MemLp (fun omega =>
      Homogenization.Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
      (chaosSampleLaw M).toMeasure :=
    lt_of_le_of_lt hbB ENNReal.ofReal_lt_top
  have hSigmaStarInvMemLp : MemLp (fun omega =>
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
      (chaosSampleLaw M).toMeasure :=
    lt_of_le_of_lt hbSigmaStarInv ENNReal.ofReal_lt_top
  by_cases hb : b = true
  · subst hb
    show MemLp (fun omega =>
        Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) i j) 1 (chaosSampleLaw M).toMeasure
    have hentryMeas : Measurable (fun omega : BilateralField d =>
        Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) i j) := by
      have heqfun : (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
            ((aux_U2_unitChart I M H omega K).coeffOn R) i j) =
          (fun omega : BilateralField d =>
            Homogenization.Book.Ch02.bCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((aux_U2_unitChart I M H omega K).coeffOn R) i j) := by
        funext omega
        unfold aux_U2_unitChart
        rw [aux_core_sigmaCoarse_eq_bCoarse_R hd I 0 1 one_pos
          (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) R hR]
      rw [heqfun]
      exact aux_core_bCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i j
    refine MemLp.mono' hBMemLp hentryMeas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro omega
    exact aux_g9_cell_entry_memLp_sigma_entry_le hd I 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) R hR i j
  · have hb' : b = false := by cases b <;> simp_all
    subst hb'
    show MemLp (fun omega =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) i j) 1 (chaosSampleLaw M).toMeasure
    have hentryMeas : Measurable (fun omega : BilateralField d =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) i j) :=
      aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i j
    refine MemLp.mono' hSigmaStarInvMemLp hentryMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro omega
    exact aux_g9_cell_entry_memLp_sigmaStarInv_entry_le R (aux_U2_unitChart I M H omega K) i j

end Paper
