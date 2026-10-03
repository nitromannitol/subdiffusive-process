module

public import SubdiffusiveProcess.Paper.lfgc_near_pass
public import SubdiffusiveProcess.Paper.lfgc_cutoff_charts

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The root statistic of the single-point tests

For a finite family of roots `i : Fin T` at level `n + offset i`, centre
`z + 3^{-n} • shift i` and side `3^{-(n + offset i)}` (the parametrisation of lem_band),
`aux_lfgc_root_stat_bandCoords` is lem_band's coordinate vector, `aux_lfgc_root_stat_selOf` selects the inverse lower ellipticity,
upper ellipticity, top-cube `σ` entries and error, and `aux_lfgc_root_stat_phiStat K c = min 1 (K ‖aux_lfgc_root_stat_selOf c‖)`.
`aux_lfgc_root_stat_nearAll` says every root chart is `θ`-near the unit chart.  This file relates the three.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ}

/-- lem_band's coordinate index. -/
abbrev aux_lfgc_root_stat_CoordIdx (d : ℕ) := Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)

/-- The selected coordinates. -/
abbrev aux_lfgc_root_stat_SelIdx (d : ℕ) := Fin 3 ⊕ (Fin d × Fin d)

/-- Selection of the coordinates used by the tests. -/
def aux_lfgc_root_stat_selOf {T : ℕ} (c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) : Fin T × aux_lfgc_root_stat_SelIdx d → ℝ
  | (i, Sum.inl j) =>
      if j = 0 then c i (Sum.inl 2) else if j = 1 then c i (Sum.inl 1) else c i (Sum.inr (Sum.inr 0))
  | (i, Sum.inr ab) => c i (Sum.inr (Sum.inl (true, ab)))

/-- The saturated root statistic. -/
noncomputable def aux_lfgc_root_stat_phiStat (K : ℝ) {T : ℕ} (c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) : ℝ :=
  min 1 (K * ‖aux_lfgc_root_stat_selOf c‖)

theorem aux_lfgc_root_stat_norm_selOf_sub_le {T : ℕ} (c c' : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) :
    ‖aux_lfgc_root_stat_selOf c - aux_lfgc_root_stat_selOf c'‖ ≤ ‖c - c'‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun p => ?_
  obtain ⟨i, j⟩ := p
  have key : ∀ a : aux_lfgc_root_stat_CoordIdx d, ‖c i a - c' i a‖ ≤ ‖c - c'‖ := fun a =>
    (norm_le_pi_norm (c i - c' i) a).trans (norm_le_pi_norm (c - c') i)
  rcases j with j | ab
  · simp only [Pi.sub_apply, aux_lfgc_root_stat_selOf]
    split_ifs <;> exact key _
  · simp only [Pi.sub_apply, aux_lfgc_root_stat_selOf]; exact key _

theorem aux_lfgc_root_stat_phiStat_lipschitz (K : ℝ) (hK : 0 ≤ K) (T : ℕ) :
    LipschitzWith (Real.toNNReal K) (aux_lfgc_root_stat_phiStat (d := d) K (T := T)) := by
  refine LipschitzWith.of_dist_le_mul fun c c' => ?_
  rw [Real.coe_toNNReal K hK, Real.dist_eq, dist_eq_norm]
  unfold aux_lfgc_root_stat_phiStat
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le (mul_nonneg hK (norm_nonneg _)) ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine (abs_norm_sub_norm_le _ _).trans ?_
  exact aux_lfgc_root_stat_norm_selOf_sub_le c c'

theorem aux_lfgc_root_stat_phiStat_zero (K : ℝ) (T : ℕ) : aux_lfgc_root_stat_phiStat (d := d) K (0 : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) = 0 := by
  unfold aux_lfgc_root_stat_phiStat
  have : aux_lfgc_root_stat_selOf (0 : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) = 0 := by
    funext p; obtain ⟨i, j⟩ := p
    rcases j with j | ab
    · simp only [aux_lfgc_root_stat_selOf]; split_ifs <;> rfl
    · rfl
  rw [this, norm_zero, mul_zero, min_eq_right zero_le_one]

theorem aux_lfgc_root_stat_phiStat_nonneg (K : ℝ) (hK : 0 ≤ K) {T : ℕ} (c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) :
    0 ≤ aux_lfgc_root_stat_phiStat K c :=
  le_min zero_le_one (mul_nonneg hK (norm_nonneg _))

theorem aux_lfgc_root_stat_phiStat_le_one (K : ℝ) {T : ℕ} (c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ) : aux_lfgc_root_stat_phiStat K c ≤ 1 :=
  min_le_left _ _

theorem aux_lfgc_root_stat_norm_selOf_lt_of_phiStat_lt {K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) {T : ℕ}
    {c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ} (h : aux_lfgc_root_stat_phiStat K c < t) : ‖aux_lfgc_root_stat_selOf c‖ < t / K := by
  unfold aux_lfgc_root_stat_phiStat at h
  rcases min_lt_iff.mp h with h1 | h2
  · linarith
  · rw [lt_div_iff₀ hK]; linarith

theorem aux_lfgc_root_stat_phiStat_le_of_norm_le {K θ : ℝ} (hK : 0 ≤ K) {T : ℕ} {c : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ}
    (h : ‖aux_lfgc_root_stat_selOf c‖ ≤ θ) : aux_lfgc_root_stat_phiStat K c ≤ K * θ :=
  (min_le_right _ _).trans (mul_le_mul_of_nonneg_left h hK)

/-! ### Root data and lem_band's coordinates -/

/-- The unit coefficient on every triadic cube. -/
noncomputable def aux_lfgc_root_stat_unitCoeff (n : ℤ) (w : SpatialCoordinates d) :
    PositiveCoefficient (centeredCube w ((3 : ℝ) ^ (-n)) (by positivity)) :=
  ⟨(memLp_top_const (1 : ℝ)).toLp _, 1, one_pos, by
    filter_upwards [MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))] with x hx
    rw [hx]⟩

theorem aux_lfgc_root_stat_unitCoeff_val (n : ℤ) (w : SpatialCoordinates d) :
    (aux_lfgc_root_stat_unitCoeff n w).val =ᵐ[volume.restrict
      (centeredCube w ((3 : ℝ) ^ (-n)) (by positivity) : Set (SpatialCoordinates d))]
      (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- lem_band's coordinate vector (verbatim transcription). -/
noncomputable def aux_lfgc_root_stat_bandCoords (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (omega : BilateralField d) : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ :=
  fun i =>
    let m := n + offset i
    let w := z + ((3 : ℝ) ^ (-n)) • shift i
    let r := (3 : ℝ) ^ (-m)
    let aN := Lane4.cutoffPositiveCoefficient M H omega N w (by positivity : 0 < (3 : ℝ) ^ (-m))
    let ref := Paper.aux_lem_band_U2_reference M H N m w omega
    Sum.elim
      (fun j => if j = 0 then
        I.lam w r (by positivity) aN w r sigma 2 / ref -
          I.lam w r (by positivity) (aux_lfgc_root_stat_unitCoeff m w) w r sigma 2
      else if j = 1 then
        I.Lam w r (by positivity) aN w r sigma 2 / ref -
          I.Lam w r (by positivity) (aux_lfgc_root_stat_unitCoeff m w) w r sigma 2
      else ref / I.lam w r (by positivity) aN w r sigma 2 -
        (I.lam w r (by positivity) (aux_lfgc_root_stat_unitCoeff m w) w r sigma 2)⁻¹)
      (Sum.elim
        (fun ij =>
          (if ij.1 then (Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0))
            ((I.chart w r (by positivity) aN w r).coeffOn (originCube d 0))) ij.2.1 ij.2.2 / ref
          else ref * (Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d 0))
            ((I.chart w r (by positivity) aN w r).coeffOn (originCube d 0))) ij.2.1 ij.2.2) -
          (if ij.2.1 = ij.2.2 then 1 else 0))
        (fun j => if j = 0 then I.err w r (by positivity) aN w r ref s 2
          else Paper.aux_lem_band_U2_reference M H N n z omega / ref - 1))

/-- The root chart of the cutoff coefficient. -/
noncomputable def aux_lfgc_root_stat_rootChart (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (m : ℤ) (w : SpatialCoordinates d) : TriadicCoeffFamily d :=
  I.chart w ((3 : ℝ) ^ (-m)) (by positivity)
    (Lane4.cutoffPositiveCoefficient M H omega N w (by positivity : 0 < (3 : ℝ) ^ (-m)))
    w ((3 : ℝ) ^ (-m))

/-- Every root chart is `θ`-near the unit chart. -/
def aux_lfgc_root_stat_nearAll (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (θ : ℝ) (omega : BilateralField d) : Prop :=
  ∀ i : Fin T, aux_lfgc_near_tests_NearChart sigma
    (aux_lfgc_root_stat_rootChart I M H omega N (n + offset i) (z + ((3 : ℝ) ^ (-n)) • shift i))
    (Paper.aux_lem_band_U2_reference M H N (n + offset i) (z + ((3 : ℝ) ^ (-n)) • shift i) omega) θ

/-- The selected coordinates of lem_band are the near-unit deviations of the root charts. -/
theorem lfgc_root_stat [NeZero d] (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ) (z : SpatialCoordinates d)
    (omega : BilateralField d) (i : Fin T) :
    let m := n + offset i
    let w := z + ((3 : ℝ) ^ (-n)) • shift i
    let F := aux_lfgc_root_stat_rootChart I M H omega N m w
    let ref := Paper.aux_lem_band_U2_reference M H N m w omega
    aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inl 0) =
        ref / Paper.aux_lem_band_U2_lamF sigma F - 1 ∧
    aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inl 1) =
        Paper.aux_lem_band_U2_LamF sigma F / ref - 1 ∧
    aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inl 2) =
        Paper.aux_lem_band_U2_errF sigma F ref ∧
    ∀ a b : Fin d,
      aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inr (a, b)) =
        Paper.aux_lem_band_U2_sigF a b F / ref - (if a = b then (1 : ℝ) else 0) := by
  intro m w F ref
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  have hE := Paper.aux_lem_band_U2_chart_isOne I w ((3 : ℝ) ^ (-m)) hr (aux_lfgc_root_stat_unitCoeff m w)
    (aux_lfgc_root_stat_unitCoeff_val m w)
  have hlam1 : I.lam w ((3 : ℝ) ^ (-m)) hr (aux_lfgc_root_stat_unitCoeff m w) w ((3 : ℝ) ^ (-m)) sigma 2 = 1 := by
    rw [Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma,
      Paper.aux_lem_band_U2_isOne_lamF sigma hsigma _ hE]
  have hLam1 : I.Lam w ((3 : ℝ) ^ (-m)) hr (aux_lfgc_root_stat_unitCoeff m w) w ((3 : ℝ) ^ (-m)) sigma 2 = 1 := by
    rw [Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma,
      Paper.aux_lem_band_U2_isOne_LamF sigma hsigma _ hE]
  have hrefpos : 0 < ref := Paper.aux_lem_band_U2_reference_pos M H N m w omega
  refine ⟨?_, ?_, ?_, fun a b => ?_⟩
  · simp only [aux_lfgc_root_stat_selOf, aux_lfgc_root_stat_bandCoords, if_true, Sum.elim_inl]
    show ref / I.lam w ((3 : ℝ) ^ (-m)) hr _ w _ sigma 2 -
      (I.lam w ((3 : ℝ) ^ (-m)) hr (aux_lfgc_root_stat_unitCoeff m w) w _ sigma 2)⁻¹ = _
    rw [hlam1, inv_one, Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma]
    rfl
  · simp only [aux_lfgc_root_stat_selOf, aux_lfgc_root_stat_bandCoords, Sum.elim_inl]
    show I.Lam w ((3 : ℝ) ^ (-m)) hr _ w _ sigma 2 / ref -
      I.Lam w ((3 : ℝ) ^ (-m)) hr (aux_lfgc_root_stat_unitCoeff m w) w _ sigma 2 = _
    rw [hLam1, Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma]
    rfl
  · simp only [aux_lfgc_root_stat_selOf, aux_lfgc_root_stat_bandCoords, Sum.elim_inr]
    show I.err w ((3 : ℝ) ^ (-m)) hr _ w _ ref sigma 2 = _
    rw [Paper.aux_lem_band_U2_err_eq I w _ hr _ ref hrefpos sigma hsigma]
    rfl
  · simp only [aux_lfgc_root_stat_selOf, aux_lfgc_root_stat_bandCoords, Sum.elim_inr, Sum.elim_inl, if_true]
    rfl

end Paper
