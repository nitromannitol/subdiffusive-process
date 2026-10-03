module

public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.chart_coords_measurable
public import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity
public import SubdiffusiveProcess.Paper.rem_bank_response_moments
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport

@[expose] public section

/-!
# Per-cube pinned coarse constants: measurability, positivity and uniform moment bank

For a countable family of cubes `z j + r j Q_0` of TRIADIC radius `r j = 3^{k_j}` (`k_j : ℤ`: large cubes,
the unit cube and all cells) the two pinned constants of the represented catalogue,
`U_N(j)(β) = Λ_{σ/2,2}(cell; A_N^β)` and `L_N(j)(β) = λ_{σ/2,2}(cell; A_N^β)^{-1}` with the
cell-local coefficient `cutoffPositiveCoefficient M H β N (z j) (hr j)` and `σ/2 = (β − 1/2)/4`, are

* measurable functions of the field `β` (installed `chart_coords_measurable`), strictly positive
  (`in_J.Lam_pos`, `in_J.lam_pos`), hence pinned by equality *everywhere*;
* uniformly bounded in `L^{q'}` (`0 < q' ≤ q`) along the cutoff `N`, for EVERY `N ≥ 0`:
  `N ≥ k` by `lem_extension_cell_moment` (cell as its own root), and `N < k` (the cell is finer than the
  wavelength `3^{-N}`) by the below-wavelength envelope `4d(hi²/lo + 1/lo)` of the actual coefficient
  (`aux_model_cube_coarse_bank_below`), whose moment is the compact-infrared plus microscopic
  ultraviolet exponential moment;
* for cubes of side `3^m > 1`: `Lam_dilation`/`lam_dilation` reduce to the unit cell with the pulled-back coefficient;
  the two-sided a.e. comparison with the scale-shifted unit coefficient at cutoff `N + m` (environment factor `F` of the
  installed large-cube coercivity, reverse direction proved here), the monotone comparison of the coarse constants for
  a.e.-ordered coefficients (`b_norm_le_mul`/`sigmaStarInv_norm_le_mul` on every descendant), Hölder with `F ∈ L^{2q}` and
  the measure-preserving scale shift give `Sum_big(N) ≤ F · Sum_unit(N+m)∘S` and an `L^q` bound uniform in `N`;
* uniformly tight in `N`.

The disorder threshold `δ0` is that of `lem_extension_cell_moment`, chosen before the model and the
cubes; the per-cube constant `Cb j` may depend on the cube.  No estimate is a premise.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Pointwise physical bounds for the cell coefficient below the cutoff wavelength. -/
theorem aux_model_cube_coarse_bank_extremes {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d))
    (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (k N : ℕ) (hk : ρ = (3 : ℝ) ^ (-(k : ℤ)))
    (hKρ : (Metric.closedBall z ρ : Set (SpatialCoordinates d)) ⊆ (K : Set (SpatialCoordinates d)))
    (hNk : N < k) (om : BilateralField d)
    (zz : SpatialCoordinates d)
    (hzz : zz = (3 : ℝ) ^ (N : ℤ) •
      (z + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter (Homogenization.originCube d 0))) :
    ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      Real.exp (-(‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
          aux_lem_extension_cell_moment_physicalLogNorm M N zz om)) ≤
        cutoffCoefficient M H om N (fun i => z i + ρ * x i) ∧
      cutoffCoefficient M H om N (fun i => z i + ρ * x i) ≤
        Real.exp (‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
          aux_lem_extension_cell_moment_physicalLogNorm M N zz om) := by
  intro x hx
  set Q0 := Homogenization.originCube d 0 with hQ0
  have hQ0mem : Q0 ∈ Homogenization.descendantsAtScale Q0 (Q0.scale - ((0 : ℕ) : ℤ)) := by
    simp [Homogenization.descendantsAtScale_self]
  have hξ := aux_lem_extension_cell_moment_descendant_micro_mem N k 0 (by omega) Q0 hQ0mem x hx
  have hid := aux_lem_extension_cell_moment_descendant_micro_identity N k Q0 z x
  have hxroot : (fun i => z i + ρ * x i) ∈ (Metric.closedBall z ρ : Set (SpatialCoordinates d)) := by
    have := aux_lem_extension_cell_moment_cellAffine_mem z ρ hρ hx
    change dist (fun i => z i + ρ * x i) z ≤ ρ
    change dist (fun i => z i + ρ * x i) z < ρ / 2 at this
    linarith
  have hyK : (fun i => z i + ρ * x i) ∈ (K : Set (SpatialCoordinates d)) := hKρ hxroot
  have hHpt : |H om (fun i => z i + ρ * x i)| ≤
      ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
    ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨_, hyK⟩
  have hlog := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H N zz _ hξ om
  have hid' : (3 : ℝ) ^ (-(N : ℤ)) •
      ((3 : ℝ) ^ ((N : ℤ) - (k : ℤ)) • (x - Homogenization.cubeCenter Q0) + zz) =
      fun i => z i + ρ * x i := by
    rw [hzz, hk]; exact hid
  rw [hid'] at hlog
  have hpos : 0 < cutoffCoefficient M H om N (fun i => z i + ρ * x i) :=
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hbound : |Real.log (cutoffCoefficient M H om N (fun i => z i + ρ * x i))| ≤
      ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
        aux_lem_extension_cell_moment_physicalLogNorm M N zz om :=
    hlog.trans (add_le_add hHpt (le_refl _))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  constructor
  · exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hpos)
  · exact (Real.exp_log hpos).symm.trans_le (Real.exp_le_exp.mpr hhi)

/-- Deterministic coarse-graining envelope for a cell whose coefficient lies between `lo` and `hi`:
the discounted series have unit total weight. -/
theorem aux_model_cube_coarse_bank_pointwise {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (hbd : ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      lo ≤ cutoffCoefficient M H om N (fun i => z i + ρ * x i) ∧
        cutoffCoefficient M H om N (fun i => z i + ρ * x i) ≤ hi) :
    E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2 +
        (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2)⁻¹ ≤
      4 * (d : ℝ) * lo⁻¹ * hi ^ 2 + 4 * (d : ℝ) * lo⁻¹ := by
  have hsub : (centeredCube z ρ hρ : Set (SpatialCoordinates d)) ⊆
      (centeredCube z ρ hρ : Set (SpatialCoordinates d)) := subset_rfl
  have hsq : 0 < s * 2 := by have := hs.1; linarith
  have hloinv : 0 < lo⁻¹ := inv_pos.mpr hlo
  have henv1 : 0 ≤ 4 * (d : ℝ) * lo⁻¹ * hi ^ 2 := by positivity
  have henv2 : 0 ≤ 4 * (d : ℝ) * lo⁻¹ := by positivity
  have hdesc : ∀ (n : ℕ) (Q : Homogenization.TriadicCube d),
      Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ)) →
      Homogenization.Book.Ch02.coarseBMatrixNorm Q
          (E.chart z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ) ≤
        4 * (d : ℝ) * lo⁻¹ * hi ^ 2 ∧
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
          (E.chart z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ) ≤
        4 * (d : ℝ) * lo⁻¹ := by
    intro n Q hQ
    have hk' : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
        (Homogenization.originCube d 0).scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hQsub := Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
    exact aux_lem_extension_cell_moment_chart_envelope E M H om N z ρ hρ z ρ hρ hsub Q hQsub
      hlo hle (fun x hx => hbd x (hQsub hx))
  have hmax : ∀ n : ℕ,
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ) ≤
        4 * (d : ℝ) * lo⁻¹ * hi ^ 2 ∧
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (E.chart z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ) ≤
        4 * (d : ℝ) * lo⁻¹ := by
    intro n
    constructor
    · unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
        Homogenization.Book.Ch02.finsetSupReal
      refine Real.sSup_le ?_ henv1
      rintro _ ⟨Q, hQ, rfl⟩
      exact (hdesc n Q (Finset.mem_coe.mp hQ)).1
    · unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        Homogenization.Book.Ch02.finsetSupReal
      refine Real.sSup_le ?_ henv2
      rintro _ ⟨Q, hQ, rfl⟩
      exact (hdesc n Q (Finset.mem_coe.mp hQ)).2
  have hW : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n :=
    fun n => aux_lem_extension_cell_moment_weight_nonneg hs.1.le n
  have hWsum : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 2 n) :=
    Homogenization.summable_geometricWeight hsq
  have hWone : ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n = 1 :=
    Homogenization.tsum_geometricWeight_eq_one hsq
  have hseries : ∀ (f : ℕ → ℝ) (c : ℝ), 0 ≤ c → (∀ n, f n ≤ c) →
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n * f n ≤ c := by
    intro f c hc hf
    by_cases hsm : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 2 n * f n)
    · calc ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n * f n
          ≤ ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n * c :=
            Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hf n) (hW n)) hsm
              (hWsum.mul_right c)
        _ = c := by rw [tsum_mul_right, hWone, one_mul]
    · rw [tsum_eq_zero_of_not_summable hsm]; exact hc
  rw [aux_lem_extension_cell_moment_Lam_eq_tsum E z ρ hρ _ z ρ hρ hsub s hs,
    aux_lem_extension_cell_moment_lam_inv_eq_tsum E z ρ hρ _ z ρ hρ hsub s hs]
  exact add_le_add (hseries _ _ henv1 fun n => (hmax n).1) (hseries _ _ henv2 fun n => (hmax n).2)

/-- **Below-wavelength moment bound**: for a cell of side `ρ = 3^{-k}` and every cutoff `N < k`
(the cell is finer than the wavelength `3^{-N}`), the sum `Λ_{s,2} + λ_{s,2}⁻¹` of the cell-local
coefficient has a finite `L^p` norm, bounded by a constant depending on the cell (not on `N`). -/
theorem aux_model_cube_coarse_bank_below {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s p : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 0 < p)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : ρ = (3 : ℝ) ^ (-(k : ℤ))) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ N : ℕ, N < k →
      eLpNorm (fun om => E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2 +
          (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C0 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  let K : Compacts (SpatialCoordinates d) := ⟨Metric.closedBall z ρ, isCompact_closedBall _ _⟩
  have hCK : 0 ≤ C K := hC K
  set Cfl := aux_lem_extension_cell_moment_nativeFluctuationConst d with hCfl
  have hCfl0 : 0 < Cfl := aux_lem_extension_cell_moment_nativeFluctuationConst_pos d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let Ex : ℝ := Real.log 4 / p + 4 * p * 3 ^ 2 * C K * M.delta ^ 2 +
    (2 * 3 * Real.log 2 + p * 3 ^ 2 * Cfl ^ 2) * M.delta ^ 2 * (k : ℝ)
  refine ⟨8 * (d : ℝ) * Real.exp Ex, by positivity, ?_⟩
  intro N hNk
  set Q0 := Homogenization.originCube d 0 with hQ0
  let zz : SpatialCoordinates d := (3 : ℝ) ^ (N : ℤ) •
      (z + (3 : ℝ) ^ (-(k : ℤ)) • Homogenization.cubeCenter Q0)
  let G : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
      aux_lem_extension_cell_moment_physicalLogNorm M N zz om
  have hG0 : ∀ om, 0 ≤ G om := fun om => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpoint : ∀ om,
      E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2 +
        (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2)⁻¹ ≤
      (8 * (d : ℝ)) * Real.exp (3 * G om) := by
    intro om
    have hb := aux_model_cube_coarse_bank_extremes M H K z ρ hρ k N hk
      (fun y hy => hy) hNk om zz rfl
    have hloG : 0 < Real.exp (-(G om)) := Real.exp_pos _
    have hleG : Real.exp (-(G om)) ≤ Real.exp (G om) :=
      Real.exp_le_exp.mpr (by have := hG0 om; linarith)
    have h := aux_model_cube_coarse_bank_pointwise E M H om N z ρ hρ s hs hloG hleG hb
    refine h.trans ?_
    have hloinv : (Real.exp (-(G om)))⁻¹ = Real.exp (G om) := by
      rw [Real.exp_neg, inv_inv]
    rw [hloinv]
    have hh : Real.exp (G om) * Real.exp (G om) ^ 2 = Real.exp (3 * G om) := by
      rw [show 3 * G om = G om + G om + G om by ring,
        Real.exp_add (G om + G om) (G om), Real.exp_add (G om) (G om)]
      ring
    have hh' : Real.exp (G om) ≤ Real.exp (3 * G om) :=
      Real.exp_le_exp.mpr (by have := hG0 om; linarith)
    calc 4 * (d : ℝ) * Real.exp (G om) * Real.exp (G om) ^ 2 + 4 * (d : ℝ) * Real.exp (G om)
        = 4 * (d : ℝ) * (Real.exp (G om) * Real.exp (G om) ^ 2) + 4 * (d : ℝ) * Real.exp (G om) := by
          ring
      _ ≤ 4 * (d : ℝ) * Real.exp (3 * G om) + 4 * (d : ℝ) * Real.exp (3 * G om) := by
          rw [hh]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh' (by positivity))
      _ = _ := by ring
  have hnorm : eLpNorm (fun om =>
      E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2 +
        (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2)⁻¹)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (8 * (d : ℝ)) *
        eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure := by
    have hm := chart_coords_measurable d hd E M H hH.1 N z ρ hρ
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((hm.2.1 s hs).add (hm.1 s hs).inv).aestronglyMeasurable
    filter_upwards with om
    have hpos : 0 < E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2 +
        (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ s 2)⁻¹ :=
      add_pos (E.Lam_pos _ _ _ _ _ _ _ _) (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _))
    erw [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpoint om
  have hGe : eLpNorm (fun om => Real.exp (3 * G om)) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (Real.log 4 / p + 4 * p * 3 ^ 2 * C K * M.delta ^ 2 +
        (2 * 3 * Real.log 2 + p * 3 ^ 2 * Cfl ^ 2) * M.delta ^ 2 * ((N : ℝ) + 1))) :=
    hCM M H hH K N zz 3 p (by norm_num) hp
  have hNl : (N : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show N + 1 ≤ k by omega)
  have hcoef : 0 ≤ (2 * 3 * Real.log 2 + p * 3 ^ 2 * Cfl ^ 2) * M.delta ^ 2 := by
    have : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    positivity
  have hexp : Real.exp (Real.log 4 / p + 4 * p * 3 ^ 2 * C K * M.delta ^ 2 +
        (2 * 3 * Real.log 2 + p * 3 ^ 2 * Cfl ^ 2) * M.delta ^ 2 * ((N : ℝ) + 1)) ≤
      Real.exp Ex := by
    refine Real.exp_le_exp.mpr ?_
    dsimp only [Ex]
    have := mul_le_mul_of_nonneg_left hNl hcoef
    linarith
  calc _ ≤ ENNReal.ofReal (8 * (d : ℝ)) *
        ENNReal.ofReal (Real.exp (Real.log 4 / p + 4 * p * 3 ^ 2 * C K * M.delta ^ 2 +
          (2 * 3 * Real.log 2 + p * 3 ^ 2 * Cfl ^ 2) * M.delta ^ 2 * ((N : ℝ) + 1))) :=
        hnorm.trans (mul_le_mul_right hGe _)
    _ ≤ ENNReal.ofReal (8 * (d : ℝ)) * ENNReal.ofReal (Real.exp Ex) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hexp) _
    _ = ENNReal.ofReal (8 * (d : ℝ) * Real.exp Ex) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-- **One cell, every cutoff**: the sum `Λ_{σ/2,2} + λ_{σ/2,2}⁻¹` of the cell-local coefficient of a
cell of side `ρ = 3^{-k}` has an `L^q` norm bounded uniformly in the cutoff `N` (all `N ≥ 0`:
`lem_extension_cell_moment` for `N ≥ k`, the below-wavelength envelope for `N < k`).  The threshold
`δ0` is chosen before the model and the cell. -/
theorem aux_model_cube_coarse_bank_cube {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (beta q : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ),
        ρ = (3 : ℝ) ^ (-(k : ℤ)) →
      ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ N : ℕ,
        eLpNorm (fun om => E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ
              ((beta - 1 / 2) / 4) 2 +
            (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ
              ((beta - 1 / 2) / 4) 2)⁻¹)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hq0 : 0 < q := by linarith
  obtain ⟨deltaq, Cd, hdq, hCd, hb⟩ := lem_extension_cell_moment d hd E beta (d / q + 1) q hbeta
    (by positivity) hq (by
      have : q * (d / q + 1) = d + q := by field_simp
      linarith)
  have hs : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 :=
    aux_lem_extension_cell_moment_order hbeta
  refine ⟨deltaq, hdq, ?_⟩
  intro M Rm H hH hδ z ρ hρ k hk
  subst hk
  obtain ⟨Cq, hCq, hcell⟩ := hb M Rm H hH hδ z ((3 : ℝ) ^ (-(k : ℤ))) hρ
  obtain ⟨C0, hC0, hbelow⟩ := aux_model_cube_coarse_bank_below hd E ((beta - 1 / 2) / 4) q hs hq0
    M H hH z ((3 : ℝ) ^ (-(k : ℤ))) hρ k rfl
  refine ⟨max (Cq * Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (k : ℝ))) C0, le_max_of_le_right
    hC0.le, ?_⟩
  intro N
  by_cases hkN : k ≤ N
  · have h := (hcell 1 (fun _ => z) N k 0 (fun _ => 0) hkN (by
      show (centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * ((0 : ℤ) : ℝ))
        ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Opens (SpatialCoordinates d)) ≤ _
      simp only [Int.cast_zero, mul_zero, add_zero]
      exact le_rfl)).2
    simp only [Int.cast_zero, mul_zero, add_zero] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hbelow N (by omega)).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))




/-- Per-descendant comparison of the coarse norms of two charts whose coefficients are
almost-everywhere ordered on the cell. -/
theorem aux_model_cube_coarse_bank_large_chart_compare {d : ℕ} [NeZero d] (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a b : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (F : ℝ) (hF : 0 < F)
    (hab : ∀ᵐ x ∂volume.restrict (centeredCube w r' hr' : Set (SpatialCoordinates d)),
      a.val x ≤ F * b.val x)
    (hba : ∀ᵐ x ∂volume.restrict (centeredCube w r' hr' : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val x)
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Homogenization.Book.Ch02.coarseBMatrixNorm Q (E.chart z r hr a w r') ≤
        F * Homogenization.Book.Ch02.coarseBMatrixNorm Q (E.chart z r hr b w r') ∧
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q (E.chart z r hr a w r') ≤
        F * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q (E.chart z r hr b w r') := by
  open Homogenization Homogenization.Book.Ch02 in
  have hca := E.chart_eq z r hr a w r' hr' hsub Q hQ
  have hcb := E.chart_eq z r hr b w r' hr' hsub Q hQ
  have hQmeas : MeasurableSet (Homogenization.openCubeSet Q) :=
    Homogenization.measurableSet_openCubeSet Q
  have hmaps : ∀ x ∈ Homogenization.openCubeSet Q,
      (fun i => w i + r' * x i) ∈ (centeredCube w r' hr' : Set (SpatialCoordinates d)) :=
    fun x hx => aux_lem_extension_cell_moment_affine_mem w r' hr' (hQ hx)
  have hv1 := aux_lem_extension_cell_moment_ae_restrict_comp
    (aux_lem_extension_cell_moment_qmp_affine w r' hr')
    (centeredCube w r' hr').isOpen.measurableSet hQmeas hmaps
    (P := fun y => a.val y ≤ F * b.val y) hab
  have hv2 := aux_lem_extension_cell_moment_ae_restrict_comp
    (aux_lem_extension_cell_moment_qmp_affine w r' hr')
    (centeredCube w r' hr').isOpen.measurableSet hQmeas hmaps
    (P := fun y => b.val y ≤ F * a.val y) hba
  have hident : ∀ e : Homogenization.Vec d, Homogenization.matVecMul (1 : Homogenization.Mat d) e = e := by
    intro e
    ext i
    simp [Homogenization.matVecMul, Matrix.one_apply]
  have hasym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric
      ((E.chart z r hr a w r').coeffOn Q) :=
    hca.mono fun x hx => by
      rw [hx]; exact Homogenization.scalarMatrix_isSymm _
  have hbsym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric
      ((E.chart z r hr b w r').coeffOn Q) :=
    hcb.mono fun x hx => by
      rw [hx]; exact Homogenization.scalarMatrix_isSymm _
  have hLab : ∀ᵐ x ∂Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q),
      Homogenization.MatLoewnerLE (((E.chart z r hr a w r').coeffOn Q).toCoeffField x)
        (F • ((E.chart z r hr b w r').coeffOn Q).toCoeffField x) := by
    filter_upwards [hca, hcb, hv1, ae_restrict_mem hQmeas] with x hxa hxb hord hxQ
    intro e
    simp only [hxa, hxb, Homogenization.smul_matVecMul, hident, Homogenization.vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_right hord (Homogenization.vecNormSq_nonneg e)
    change _ ≤ _
    change _ * Homogenization.vecDot e e ≤ _ * Homogenization.vecDot e e at h
    nlinarith
  have hLba : ∀ᵐ x ∂Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q),
      Homogenization.MatLoewnerLE (((E.chart z r hr b w r').coeffOn Q).toCoeffField x)
        (F • ((E.chart z r hr a w r').coeffOn Q).toCoeffField x) := by
    filter_upwards [hca, hcb, hv2, ae_restrict_mem hQmeas] with x hxa hxb hord hxQ
    intro e
    simp only [hxa, hxb, Homogenization.smul_matVecMul, hident, Homogenization.vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_right hord (Homogenization.vecNormSq_nonneg e)
    change _ * Homogenization.vecDot e e ≤ _ * Homogenization.vecDot e e at h
    nlinarith
  exact ⟨aux_lem_extension_cell_moment_b_norm_le_mul (Homogenization.Book.Ch02.cubeDomain Q) _ _
      hasym hbsym F hF hLab,
    aux_lem_extension_cell_moment_sigmaStarInv_norm_le_mul
      (Homogenization.Book.Ch02.cubeDomain Q) _ _ hasym hbsym F hF hLba⟩

/-- Comparison of the coarse ellipticities of two almost-everywhere ordered coefficients:
`a ≤ F b` bounds `Λ(a)` by `F Λ(b)`, and `b ≤ F a` bounds `λ(a)⁻¹` by `F λ(b)⁻¹`. -/
theorem aux_model_cube_coarse_bank_large_compare {d : ℕ} [NeZero d] (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a b : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (F : ℝ) (hF : 0 < F)
    (hab : ∀ᵐ x ∂volume.restrict (centeredCube w r' hr' : Set (SpatialCoordinates d)),
      a.val x ≤ F * b.val x)
    (hba : ∀ᵐ x ∂volume.restrict (centeredCube w r' hr' : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val x)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.Lam z r hr a w r' s 2 ≤ F * E.Lam z r hr b w r' s 2 ∧
      (E.lam z r hr a w r' s 2)⁻¹ ≤ F * (E.lam z r hr b w r' s 2)⁻¹ := by
  have hW : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n :=
    fun n => aux_lem_extension_cell_moment_weight_nonneg hs.1.le n
  have hdesc : ∀ (n : ℕ) (Q : Homogenization.TriadicCube d),
      Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ)) →
      Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    intro n Q hQ
    have hk' : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
        (Homogenization.originCube d 0).scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    exact Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
  have hseries : ∀ (f g : ℕ → ℝ), (∀ n, 0 ≤ g n) → (∀ n, f n ≤ F * g n) →
      ∑' n, g n ≠ 0 →
      ∑' n, f n ≤ F * ∑' n, g n := by
    intro f g hg0 hfg hne
    have hgs : Summable g := by
      by_contra hns
      exact hne (tsum_eq_zero_of_not_summable hns)
    by_cases hfs : Summable f
    · calc ∑' n, f n ≤ ∑' n, F * g n := Summable.tsum_le_tsum hfg hfs (hgs.mul_left F)
        _ = F * ∑' n, g n := tsum_mul_left
    · rw [tsum_eq_zero_of_not_summable hfs]
      exact mul_nonneg hF.le (tsum_nonneg hg0)
  constructor
  · rw [aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr a w r' hr' hsub s hs,
      aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr b w r' hr' hsub s hs]
    have hne : ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr b w r') ≠ 0 := by
      rw [← aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr b w r' hr' hsub s hs]
      exact (E.Lam_pos _ _ _ _ _ _ _ _).ne'
    have hle : ∀ n : ℕ,
        Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') ≤
        F * Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr b w r') := by
      intro n
      unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
        Homogenization.Book.Ch02.finsetSupReal
      refine Real.sSup_le ?_ (mul_nonneg hF.le (Real.sSup_nonneg ?_))
      · rintro _ ⟨Q, hQ, rfl⟩
        have hQ' := Finset.mem_coe.mp hQ
        refine (aux_model_cube_coarse_bank_large_chart_compare E z r hr a b w r' hr' hsub F hF hab hba Q
          (hdesc n Q hQ')).1.trans ?_
        exact mul_le_mul_of_nonneg_left
          (aux_lem_extension_cell_moment_le_finsetSupReal _
            (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R (E.chart z r hr b w r')) hQ')
          hF.le
      · rintro _ ⟨Q, hQ, rfl⟩
        exact Homogenization.Book.Ch02.coarseBMatrixNorm_nonneg _ _
    exact hseries _ _ (fun n => mul_nonneg (hW n)
        (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _))
      (fun n => by
        calc _ ≤ Homogenization.Book.Ch02.geometricWeight s 2 n * (F * _) :=
              mul_le_mul_of_nonneg_left (hle n) (hW n)
          _ = _ := by ring)
      hne
  · rw [aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr a w r' hr' hsub s hs,
      aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr b w r' hr' hsub s hs]
    have hne : ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr b w r') ≠ 0 := by
      rw [← aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr b w r' hr' hsub s hs]
      exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).ne'
    have hle : ∀ n : ℕ,
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') ≤
        F * Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ)) (E.chart z r hr b w r') := by
      intro n
      unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        Homogenization.Book.Ch02.finsetSupReal
      refine Real.sSup_le ?_ (mul_nonneg hF.le (Real.sSup_nonneg ?_))
      · rintro _ ⟨Q, hQ, rfl⟩
        have hQ' := Finset.mem_coe.mp hQ
        refine (aux_model_cube_coarse_bank_large_chart_compare E z r hr a b w r' hr' hsub F hF hab hba Q
          (hdesc n Q hQ')).2.trans ?_
        exact mul_le_mul_of_nonneg_left
          (aux_lem_extension_cell_moment_le_finsetSupReal _
            (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
              (E.chart z r hr b w r')) hQ') hF.le
      · rintro _ ⟨Q, hQ, rfl⟩
        exact Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg _ _
    exact hseries _ _ (fun n => mul_nonneg (hW n)
        (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _))
      (fun n => by
        calc _ ≤ Homogenization.Book.Ch02.geometricWeight s 2 n * (F * _) :=
              mul_le_mul_of_nonneg_left (hle n) (hW n)
          _ = _ := by ring)
      hne



/-- Reverse of `aux_rem_bank_response_moments_lc_upShift_cutoff_le` (infrared-free coefficient):
the large-cube coefficient is bounded by the shifted unit coefficient. -/
theorem aux_model_cube_coarse_bank_large_upShift_cutoff_ge {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d)
    (K : Compacts (SpatialCoordinates d))
    (hy : aux_rem_bank_response_moments_lc_upMap k z y ∈ K) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        omega N (aux_rem_bank_response_moments_lc_upMap k z y) ≤
      Real.exp ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
        ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
          (K : Set (SpatialCoordinates d))‖) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) y := by
  have hneg : -(∑ a ∈ Finset.range k,
      omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) ≤
      ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro a ha
    exact (neg_le_abs _).trans (by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using
        ((omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨aux_rem_bank_response_moments_lc_upMap k z y, hy⟩)
  have hratio : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ 1 := by
    rw [div_le_one (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)]
    by_cases hk : k = 0
    · simp [hk]
    · exact (Rm.ahom_ordering N (N + k) (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk))).1
  rw [aux_rem_bank_response_moments_lc_upShift_cutoff_factor]
  have hposN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hposNk : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k) := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + k)
  have hc0 : 0 ≤ cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N
      (aux_rem_bank_response_moments_lc_upMap k z y) :=
    (mul_pos (inv_pos.2 hposN) (Real.exp_pos _)).le
  set c0 := cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N
      (aux_rem_bank_response_moments_lc_upMap k z y) with hc0def
  set S := ∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)
    with hS
  set NS := ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖
    with hNS
  set τ2 := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P with hτ
  set a0 := SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  set a1 := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k)
  -- goal: c0 ≤ exp(k τ² + NS) * ((a0 / a1) * exp(S - k τ²) * c0)
  have hexp : Real.exp ((k : ℝ) * τ2 + NS) * Real.exp (S - (k : ℝ) * τ2) ≥ 1 := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    linarith
  have hr1 : 1 ≤ a0 / a1 := by
    rw [one_le_div hposNk]
    have := hratio
    rw [div_le_one hposN] at this
    -- ahom (N+k) ≤ ahom N gives a1 ≤ a0
    exact this
  have key : 1 ≤ (Real.exp ((k : ℝ) * τ2 + NS) * Real.exp (S - (k : ℝ) * τ2)) * (a0 / a1) :=
    one_le_mul_of_one_le_of_one_le hexp hr1
  calc c0 ≤ ((Real.exp ((k : ℝ) * τ2 + NS) * Real.exp (S - (k : ℝ) * τ2)) * (a0 / a1)) * c0 :=
        le_mul_of_one_le_left hc0 key
    _ = _ := by ring

/-- Reverse of `aux_rem_bank_response_moments_lc_coefficients_le` (infrared version): the large-cube
coefficient, pulled back to the unit cube, is a.e. bounded by the same environment factor times the
scale-shifted unit coefficient. -/
theorem aux_model_cube_coarse_bank_large_coefficients_ge {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) (N : ℕ) (omega : BilateralField d) :
    ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val (cubeDilation z 0 ((3 : ℝ) ^ k) y) ≤
        aux_rem_bank_response_moments_lc_environment_factor M H k z hr omega *
          (cutoffPositiveCoefficient M H (aux_rem_bank_response_moments_lc_upShift k z omega)
            (N + k) 0 one_pos).val y := by
  have hq := lane4_dilation_quasi_measure_preserving d z 0 ((3 : ℝ) ^ k) hr one_pos
  filter_upwards [aux_rem_bank_response_moments_lc_cutoff_positive_coe M H
      (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) 0 one_pos,
    hq.ae (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H omega N z hr),
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
    with y hyunit hybig hy
  rw [hyunit, hybig]
  have hyeq := congrFun (aux_rem_bank_response_moments_lc_upMap_eq k z) y
  rw [← hyeq]
  have hyK := centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hy
  have hxK : aux_rem_bank_response_moments_lc_upMap k z y ∈
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)) := by
    rw [hyeq]
    exact centeredCube_subset_closedCube z hr (cubeDilation_mapsTo z 0 hr one_pos y hy)
  have hcoarse := aux_model_cube_coarse_bank_large_upShift_cutoff_ge M Rm N k z y omega
    (closedCube z ((3 : ℝ) ^ k) hr) hxK
  have hu : -(H (aux_rem_bank_response_moments_lc_upShift k z omega) y) ≤
      ‖(H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ := by
    exact (neg_le_abs _).trans (ContinuousMap.norm_coe_le_norm
      ((H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ⟨y, hyK⟩)
  have hb : H omega (aux_rem_bank_response_moments_lc_upMap k z y) ≤
      ‖(H omega).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖ :=
    (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
          ⟨aux_rem_bank_response_moments_lc_upMap k z y, hxK⟩)
  rw [aux_rem_bank_response_moments_lc_cutoff_infrared_mul M H omega N,
    aux_rem_bank_response_moments_lc_cutoff_infrared_mul M H
      (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) y]
  refine (mul_le_mul_of_nonneg_left hcoarse (Real.exp_pos _).le).trans ?_
  have hpos : 0 ≤ cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) y :=
    (mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + k))) (Real.exp_pos _)).le
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
  have hfac : Real.exp (H omega (aux_rem_bank_response_moments_lc_upMap k z y) +
        ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
            (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖)) ≤
      aux_rem_bank_response_moments_lc_environment_factor M H k z hr omega *
        Real.exp (H (aux_rem_bank_response_moments_lc_upShift k z omega) y) := by
    dsimp only [aux_rem_bank_response_moments_lc_environment_factor]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith only [hu, hb]
  exact mul_le_mul_of_nonneg_right hfac hpos


/-- **Large cell, every cutoff**: for a cell of side `R = 3^m` (`m : ℕ`) the sum `Λ + λ⁻¹` of the
cell-local coefficient is dominated by the environment factor times the sum for the scale-shifted unit
cell at cutoff `N + m` (dilation covariance `Lam_dilation`/`lam_dilation`, two-sided coefficient
comparison, monotonicity of the coarse constants), hence bounded in `L^q` uniformly in `N`. -/
theorem aux_model_cube_coarse_bank_large {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 0 < q)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cx : ℝ) (hCx : 0 ≤ Cx)
    (hunit : ∀ N' : ℕ,
      eLpNorm (fun om => E.Lam (0 : SpatialCoordinates d) 1 one_pos
            (cutoffPositiveCoefficient M H om N' 0 one_pos) 0 1 s 2 +
          (E.lam (0 : SpatialCoordinates d) 1 one_pos
            (cutoffPositiveCoefficient M H om N' 0 one_pos) 0 1 s 2)⁻¹)
        (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cx)
    (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : ρ = (3 : ℝ) ^ m) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ N : ℕ,
      eLpNorm (fun om => E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ)
            z ρ s 2 +
          (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ)
            z ρ s 2)⁻¹)
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
  subst hm
  have hR := hρ
  haveI : NeZero d := ⟨by omega⟩
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμ
  let F : BilateralField d → ℝ := aux_rem_bank_response_moments_lc_environment_factor M H m z hR
  have hFmeas : Measurable F :=
    aux_rem_bank_response_moments_lc_environment_factor_measurable M H hH m z hR
  have hFmem : MemLp F (ENNReal.ofReal (2 * q)) μ :=
    aux_rem_bank_response_moments_envFactor_memLp hd M H hH m z hR (2 * q) (by positivity)
  have hFtop : eLpNorm F (ENNReal.ofReal (2 * q)) μ ≠ ⊤ := hFmem.eLpNorm_ne_top
  let Cf : ℝ := (eLpNorm F (ENNReal.ofReal (2 * q)) μ).toReal
  have hCf : 0 ≤ Cf := ENNReal.toReal_nonneg
  have hFn : eLpNorm F (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal Cf := by
    dsimp only [Cf]; rw [ENNReal.ofReal_toReal hFtop]
  let S : BilateralField d → BilateralField d := aux_rem_bank_response_moments_lc_upShift m z
  have hSmp : MeasurePreserving S μ μ :=
    aux_rem_bank_response_moments_lc_upShift_measurePreserving M m z
  refine ⟨Cf * Cx, mul_nonneg hCf hCx, ?_⟩
  intro N
  let X : BilateralField d → ℝ := fun om' =>
    E.Lam (0 : SpatialCoordinates d) 1 one_pos (cutoffPositiveCoefficient M H om' (N + m) 0 one_pos)
        0 1 s 2 +
      (E.lam (0 : SpatialCoordinates d) 1 one_pos
        (cutoffPositiveCoefficient M H om' (N + m) 0 one_pos) 0 1 s 2)⁻¹
  have hXmeas : Measurable X := by
    have h1 := (chart_coords_measurable d hd E M H hH.1 (N + m) (0 : SpatialCoordinates d) 1
      one_pos)
    exact (h1.2.1 s hs).add (h1.1 s hs).inv
  have hpoint : ∀ om : BilateralField d,
      E.Lam z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR) z ((3 : ℝ) ^ m) s 2 +
        (E.lam z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR)
          z ((3 : ℝ) ^ m) s 2)⁻¹ ≤ F om * X (S om) := by
    intro om
    obtain ⟨ah, hah⟩ := lane4_dilation_coefficient_transport d z 0 ((3 : ℝ) ^ m) hR one_pos
      (cutoffPositiveCoefficient M H om N z hR)
    have hLam := E.Lam_dilation z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR)
      0 one_pos ah hah s 2
    have hlam := E.lam_dilation z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR)
      0 one_pos ah hah s 2
    have hFpos : 0 < F om :=
      aux_rem_bank_response_moments_lc_environment_factor_pos M H m z hR om
    have hge := aux_model_cube_coarse_bank_large_coefficients_ge M Rm H m z hR N om
    have hle := aux_rem_bank_response_moments_lc_coefficients_le M Rm H m z hR true N om
    have hab : ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        ah.val x ≤ F om *
          (cutoffPositiveCoefficient M H (S om) (N + m) 0 one_pos).val x := by
      filter_upwards [hah, hge] with x h1 h2
      rw [h1]; exact h2
    have hba : ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H (S om) (N + m) 0 one_pos).val x ≤ F om * ah.val x := by
      filter_upwards [hah, hle] with x h1 h2
      rw [h1]; exact h2
    obtain ⟨hL1, hL2⟩ := aux_model_cube_coarse_bank_large_compare E 0 1 one_pos ah
      (cutoffPositiveCoefficient M H (S om) (N + m) 0 one_pos) 0 1 one_pos subset_rfl (F om) hFpos
      hab hba s hs
    rw [hLam, hlam]
    calc _ ≤ F om * E.Lam 0 1 one_pos (cutoffPositiveCoefficient M H (S om) (N + m) 0 one_pos)
            0 1 s 2 + F om * (E.lam 0 1 one_pos
              (cutoffPositiveCoefficient M H (S om) (N + m) 0 one_pos) 0 1 s 2)⁻¹ :=
          add_le_add hL1 hL2
      _ = _ := by dsimp only [X]; ring
  have hnn : ∀ om : BilateralField d, 0 < F om * X (S om) := by
    intro om
    have hFpos : 0 < F om :=
      aux_rem_bank_response_moments_lc_environment_factor_pos M H m z hR om
    exact mul_pos hFpos (add_pos (E.Lam_pos _ _ _ _ _ _ _ _) (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)))
  have hXS : eLpNorm (fun om => X (S om)) (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal Cx := by
    change eLpNorm (X ∘ S) (ENNReal.ofReal (2 * q)) μ ≤ _
    rw [eLpNorm_comp_measurePreserving hXmeas.aestronglyMeasurable hSmp]
    exact hunit (N + m)
  have hprod := aux_lem_extension_cell_moment_eLpNorm_mul μ q hq F (fun om => X (S om))
    hFmeas.aestronglyMeasurable (hXmeas.comp hSmp.measurable).aestronglyMeasurable
  calc _ ≤ eLpNorm (fun om => F om * X (S om)) (ENNReal.ofReal q) μ :=
        eLpNorm_mono_real
          (((chart_coords_measurable d hd E M H hH.1 N z ((3 : ℝ) ^ m) hR).2.1 s hs).add
            ((chart_coords_measurable d hd E M H hH.1 N z ((3 : ℝ) ^ m) hR).1 s hs).inv).aestronglyMeasurable fun om => by
          have hpos : 0 < E.Lam z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR)
              z ((3 : ℝ) ^ m) s 2 +
            (E.lam z ((3 : ℝ) ^ m) hR (cutoffPositiveCoefficient M H om N z hR)
              z ((3 : ℝ) ^ m) s 2)⁻¹ :=
            add_pos (E.Lam_pos _ _ _ _ _ _ _ _) (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _))
          erw [Real.norm_of_nonneg hpos.le]
          exact hpoint om
    _ ≤ _ := hprod
    _ ≤ ENNReal.ofReal Cf * ENNReal.ofReal Cx := mul_le_mul' hFn hXS
    _ = ENNReal.ofReal (Cf * Cx) := by rw [← ENNReal.ofReal_mul hCf]


/-- **One cube of triadic radius, every cutoff** (`r = 3^k`, `k : ℤ`): small cells and the unit cube by
`aux_model_cube_coarse_bank_cube`, large cubes by `aux_model_cube_coarse_bank_large` with the unit cell at
the doubled exponent. -/
theorem aux_model_cube_coarse_bank_cubeZ {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (beta q : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (k : ℤ),
        ρ = (3 : ℝ) ^ k →
      ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ N : ℕ,
        eLpNorm (fun om => E.Lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ
              ((beta - 1 / 2) / 4) 2 +
            (E.lam z ρ hρ (cutoffPositiveCoefficient M H om N z hρ) z ρ
              ((beta - 1 / 2) / 4) 2)⁻¹)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
  have hq2 : 1 ≤ 2 * q := by linarith
  obtain ⟨δ1, hδ1, h1⟩ := aux_model_cube_coarse_bank_cube hd E beta q hbeta hq
  obtain ⟨δ2, hδ2, h2⟩ := aux_model_cube_coarse_bank_cube hd E beta (2 * q) hbeta hq2
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm H hH hδ z ρ hρ k hk
  have hs : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := aux_lem_extension_cell_moment_order hbeta
  by_cases hk0 : k ≤ 0
  · obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = -(k' : ℤ) := ⟨(-k).toNat, by omega⟩
    exact h1 M Rm H hH (hδ.trans (min_le_left _ _)) z ρ hρ k' (by rw [hk, hk'])
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    obtain ⟨Cx, hCx0, hCx⟩ := h2 M Rm H hH (hδ.trans (min_le_right _ _)) 0 1 one_pos 0
      (by norm_num)
    exact aux_model_cube_coarse_bank_large hd E ((beta - 1 / 2) / 4) q hs (by linarith) M Rm H hH Cx
      hCx0 hCx z ρ hρ m (by rw [hk, hm, zpow_natCast])

/-- **Per-cube pinned coarse constants** (clauses E/G): see the module docstring. -/
theorem model_cube_coarse_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (beta q : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (J : Type) [Countable J] (z : J → SpatialCoordinates d) (r : J → ℝ)
        (hr : ∀ j, 0 < r j), (∀ j, ∃ k : ℤ, r j = (3 : ℝ) ^ k) →
      ∃ Cb : J → ℝ, (∀ j, 0 ≤ Cb j) ∧
        (∀ j N, Measurable (fun β : BilateralField d =>
          E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
            (z j) (r j) ((beta - 1 / 2) / 4) 2)) ∧
        (∀ j N, Measurable (fun β : BilateralField d =>
          (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
            (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)))) ∧
        (∀ j N (β : BilateralField d),
          0 < E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
            (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
          0 < (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
            (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) ∧
        (∀ j N, ∀ q' : ℝ, 0 < q' → q' ≤ q →
          (MemLp (fun β : BilateralField d =>
            E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q')
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun β : BilateralField d =>
            E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q')
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb j)) ∧
          (MemLp (fun β : BilateralField d =>
            (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q')
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun β : BilateralField d =>
            (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q')
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb j))) ∧
        (∀ j, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β : BilateralField d | Mb <
            E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2} ≤ ENNReal.ofReal rho ∧
          (chaosSampleLaw M).toMeasure {β : BilateralField d | Mb <
            (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
              (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))} ≤ ENNReal.ofReal rho)
  := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, hcube⟩ := aux_model_cube_coarse_bank_cubeZ hd E beta q hbeta hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm H hH hδ J _ z r hr hrad
  choose k hk using hrad
  choose Cb hCb0 hCb using fun j => hcube M Rm H hH hδ (z j) (r j) (hr j) (k j) (hk j)
  refine ⟨Cb, hCb0, ?_⟩
  have hs : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := aux_lem_extension_cell_moment_order hbeta
  have hmeasLam : ∀ j N, Measurable (fun β : BilateralField d =>
      E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) := fun j N =>
    (chart_coords_measurable d hd E M H hH.1 N (z j) (r j) (hr j)).2.1 _ hs
  have hmeaslam : ∀ j N, Measurable (fun β : BilateralField d =>
      E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) := fun j N =>
    (chart_coords_measurable d hd E M H hH.1 N (z j) (r j) (hr j)).1 _ hs
  have hLeq : ∀ j N, (fun β : BilateralField d =>
      (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) = fun β : BilateralField d =>
      (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2)⁻¹ := fun j N => by
    funext β; exact Real.rpow_neg_one _
  have hmeasL : ∀ j N, Measurable (fun β : BilateralField d =>
      (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) := fun j N => by
    rw [hLeq j N]; exact (hmeaslam j N).inv
  have hposU : ∀ j N (β : BilateralField d),
      0 < E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2 := fun j N β => E.Lam_pos _ _ _ _ _ _ _ _
  have hposL : ∀ j N (β : BilateralField d),
      0 < (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)) := fun j N β => by
    rw [Real.rpow_neg_one]; exact inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)
  -- L^q bounds at the top exponent, transferred by domination
  have hUq : ∀ j N, eLpNorm (fun β : BilateralField d =>
      E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cb j) := fun j N =>
    (eLpNorm_mono_real (hmeasLam j N).aestronglyMeasurable fun β => by
      rw [Real.norm_of_nonneg (hposU j N β).le]
      have := hposL j N β
      rw [Real.rpow_neg_one] at this
      exact le_add_of_nonneg_right (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le).trans (hCb j N)
  have hLq : ∀ j N, eLpNorm (fun β : BilateralField d =>
      (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
        (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb j) := fun j N =>
    (eLpNorm_mono_real (hmeasL j N).aestronglyMeasurable fun β => by
      rw [Real.norm_of_nonneg (hposL j N β).le, Real.rpow_neg_one]
      exact le_add_of_nonneg_left (E.Lam_pos _ _ _ _ _ _ _ _).le).trans (hCb j N)
  have hprob : IsProbabilityMeasure (chaosSampleLaw M).toMeasure := inferInstance
  have hmonoU : ∀ j N, ∀ q' : ℝ, 0 < q' → q' ≤ q →
      (MemLp (fun β : BilateralField d =>
        E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q')
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun β : BilateralField d =>
        E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q')
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb j)) := by
    intro j N q' hq' hq'q
    have hqq : ENNReal.ofReal q' ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq'q
    have hmem : MemLp (fun β : BilateralField d =>
        E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure :=
      lt_of_le_of_lt (hUq j N) ENNReal.ofReal_lt_top
    exact ⟨hmem.mono_exponent hqq,
      (eLpNorm_le_eLpNorm_of_exponent_le hqq).trans (hUq j N)⟩
  have hmonoL : ∀ j N, ∀ q' : ℝ, 0 < q' → q' ≤ q →
      (MemLp (fun β : BilateralField d =>
        (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q')
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun β : BilateralField d =>
        (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q')
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb j)) := by
    intro j N q' hq' hq'q
    have hqq : ENNReal.ofReal q' ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq'q
    have hmem : MemLp (fun β : BilateralField d =>
        (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure :=
      lt_of_le_of_lt (hLq j N) ENNReal.ofReal_lt_top
    exact ⟨hmem.mono_exponent hqq,
      (eLpNorm_le_eLpNorm_of_exponent_le hqq).trans (hLq j N)⟩
  refine ⟨hmeasLam, hmeasL, fun j N β => ⟨hposU j N β, hposL j N β⟩,
    fun j N q' hq' hq'q => ⟨hmonoU j N q' hq' hq'q, hmonoL j N q' hq' hq'q⟩, ?_⟩
  intro j rho hrho
  have hCbj : 0 ≤ Cb j := hCb0 j
  obtain ⟨M1, hM1⟩ := aux_model_triadic_cube_coercivity_tail (chaosSampleLaw M).toMeasure
    (fun N β => E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2) (hmeasLam j) (Cb j) hCbj
    (fun N => by
      have := (hmonoU j N 1 one_pos hq).2
      rwa [ENNReal.ofReal_one] at this) rho hrho
  obtain ⟨M2, hM2⟩ := aux_model_triadic_cube_coercivity_tail (chaosSampleLaw M).toMeasure
    (fun N β => (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) (hmeasL j) (Cb j) hCbj
    (fun N => by
      have := (hmonoL j N 1 one_pos hq).2
      rwa [ENNReal.ofReal_one] at this) rho hrho
  refine ⟨max M1 M2, fun N => ⟨le_trans (measure_mono ?_) (hM1 N), le_trans (measure_mono ?_) (hM2 N)⟩⟩
  · intro β hβ
    simp only [Set.mem_setOf_eq] at hβ ⊢
    exact lt_of_le_of_lt (le_max_left _ _) hβ
  · intro β hβ
    simp only [Set.mem_setOf_eq] at hβ ⊢
    exact lt_of_le_of_lt (le_max_right _ _) hβ

end Paper
