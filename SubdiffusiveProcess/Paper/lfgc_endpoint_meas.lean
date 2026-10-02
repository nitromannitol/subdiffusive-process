import SubdiffusiveProcess.Paper.lfgc_root_tail2
import SubdiffusiveProcess.Lfgc.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The endpoint statistic depends only on a finite layer window

For the truncated infrared field `S_L ω` (the anchored partial sum), the root statistic
depends only on the layers `-N, …, max L 3` (for roots of level at least `-3`); it is
measurable, hence measurable for every layer window containing these indices.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_endpoint_meas_cutoffPositiveCoefficient_congr (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega omega' : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h : ∀ x, cutoffCoefficient M H omega N x = cutoffCoefficient M H' omega' N x) :
    Lane4.cutoffPositiveCoefficient M H omega N z hr =
      Lane4.cutoffPositiveCoefficient M H' omega' N z hr := by
  have hCM : Lane4.cutoffCoefficientCM M H omega N z hr = Lane4.cutoffCoefficientCM M H' omega' N z hr := by
    ext x; exact h x
  unfold Lane4.cutoffPositiveCoefficient
  congr 1

theorem aux_lfgc_endpoint_meas_measurable_infraredPartialSum (L : ℕ) :
    Measurable (fun omega : BilateralField d => infraredPartialSum omega L) := by
  unfold infraredPartialSum
  refine Finset.measurable_sum _ fun n _ => ?_
  refine (measurable_pi_apply _).sub ?_
  exact (ContinuousMap.continuous_const'.measurable).comp
    ((continuous_eval_const _).measurable.comp (measurable_pi_apply _))

end Paper
namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- lem_band's coordinates with the coefficient and reference supplied as functions. -/
noncomputable def aux_lfgc_endpoint_meas_bandCoordsGen (I : Paper.in_J d) (s sigma : ℝ) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (n : ℤ)
    (z : SpatialCoordinates d)
    (coefW : ∀ (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      PositiveCoefficient (centeredCube w r hr))
    (refW : ℤ → SpatialCoordinates d → ℝ) : Fin T → aux_lfgc_root_stat_CoordIdx d → ℝ :=
  fun i =>
    let m := n + offset i
    let w := z + ((3 : ℝ) ^ (-n)) • shift i
    let r := (3 : ℝ) ^ (-m)
    let aN := coefW w r (by positivity : 0 < (3 : ℝ) ^ (-m))
    let ref := refW m w
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
          else refW n z / ref - 1))

theorem aux_lfgc_endpoint_meas_bandCoords_eq_gen (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    aux_lfgc_root_stat_bandCoords I M H s sigma T offset shift N n z omega =
      aux_lfgc_endpoint_meas_bandCoordsGen I s sigma T offset shift n z
        (fun w r hr => Lane4.cutoffPositiveCoefficient M H omega N w hr)
        (fun m w => Paper.aux_lem_band_U2_reference M H N m w omega) := rfl

theorem aux_lfgc_endpoint_meas_bandCoordsGen_congr (I : Paper.in_J d) (s sigma : ℝ) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (n : ℤ)
    (z : SpatialCoordinates d)
    (coefW coefW' : ∀ (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      PositiveCoefficient (centeredCube w r hr))
    (refW refW' : ℤ → SpatialCoordinates d → ℝ) (hcoef : coefW = coefW')
    (hroot : ∀ i : Fin T, refW (n + offset i) (z + ((3 : ℝ) ^ (-n)) • shift i) =
      refW' (n + offset i) (z + ((3 : ℝ) ^ (-n)) • shift i))
    (hz : refW n z = refW' n z) :
    aux_lfgc_endpoint_meas_bandCoordsGen I s sigma T offset shift n z coefW refW =
      aux_lfgc_endpoint_meas_bandCoordsGen I s sigma T offset shift n z coefW' refW' := by
  subst hcoef
  funext i
  simp only [aux_lfgc_endpoint_meas_bandCoordsGen]
  rw [hroot i, hz]

end Paper
namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Each selected coordinate is measurable when the infrared field is. -/
theorem aux_lfgc_endpoint_meas_selOf_coord_measurable (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (q : Fin T × aux_lfgc_root_stat_SelIdx d) :
    Measurable (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) q) := by
  obtain ⟨i, j⟩ := q
  set m := n + offset i
  set w := z + ((3 : ℝ) ^ (-n)) • shift i
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  have e := fun omega => lfgc_root_stat I M H sigma hsigma T offset shift N n z omega i
  obtain ⟨cm1, cm2, cm3, -, cm5⟩ := Paper.chart_coords_measurable d hd I M H hH N w _ hr
  have href := aux_lfgc_root_tail_measurable_reference M H hH N m w
  have hrefpos := Paper.aux_lem_band_U2_reference_pos M H N m w
  have hlamm : Measurable (fun omega => Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) := by
    have ee : (fun omega => Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) =
        (fun omega => I.lam w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M H omega N w hr)
          w ((3 : ℝ) ^ (-m)) sigma 2) :=
      funext fun omega => (Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma).symm
    rw [ee]; exact cm1 sigma hsigma
  have hLamm : Measurable (fun omega => Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) := by
    have ee : (fun omega => Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) =
        (fun omega => I.Lam w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M H omega N w hr)
          w ((3 : ℝ) ^ (-m)) sigma 2) :=
      funext fun omega => (Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma).symm
    rw [ee]; exact cm2 sigma hsigma
  rcases j with j | ⟨a, b⟩
  · fin_cases j
    · have ee : (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inl 0)) =
          fun omega => Paper.aux_lem_band_U2_reference M H N m w omega /
            Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w) - 1 :=
        funext fun omega => (e omega).1
      simp only [Fin.zero_eta]; rw [ee]; exact (href.div hlamm).sub_const 1
    · have ee : (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inl 1)) =
          fun omega => Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w) /
            Paper.aux_lem_band_U2_reference M H N m w omega - 1 :=
        funext fun omega => (e omega).2.1
      simp only [Fin.mk_one]; rw [ee]; exact (hLamm.div href).sub_const 1
    · have ee : (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)
          (i, Sum.inl ⟨2, by norm_num⟩)) =
          fun omega => I.err w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M H omega N w hr)
              w ((3 : ℝ) ^ (-m)) (Paper.aux_lem_band_U2_reference M H N m w omega) sigma 2 := by
        funext omega
        have : ((⟨2, by norm_num⟩ : Fin 3)) = 2 := rfl
        rw [this, (e omega).2.2.1]
        exact (Paper.aux_lem_band_U2_err_eq I w _ hr _ _ (hrefpos omega) sigma hsigma).symm
      rw [ee]; exact cm5 sigma hsigma _ href (fun omega => hrefpos omega)
  · have ee : (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) (i, Sum.inr (a, b))) =
        fun omega => Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0))
          ((I.chart w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M H omega N w hr) w
            ((3 : ℝ) ^ (-m))).coeffOn (originCube d 0)) a b /
          Paper.aux_lem_band_U2_reference M H N m w omega - (if a = b then (1 : ℝ) else 0) :=
      funext fun omega => (e omega).2.2.2 a b
    rw [ee]; exact ((cm3 a b).div href).sub_const _

theorem aux_lfgc_endpoint_meas_rootX_measurable (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ)
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (K : ℝ) :
    Measurable (aux_lfgc_root_impl_rootX I M sigma T offset shift N n z K H) := by
  have hv : Measurable (fun omega => aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)) :=
    measurable_pi_iff.mpr fun q => aux_lfgc_endpoint_meas_selOf_coord_measurable hd I M H hH sigma hsigma T offset shift N n z q
  unfold aux_lfgc_root_impl_rootX aux_lfgc_root_stat_phiStat
  exact measurable_const.min (measurable_const.mul (continuous_norm.measurable.comp hv))

end Paper
namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_endpoint_meas_infraredPartialSum_congr (L : ℕ) (omega omega' : BilateralField d)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ L → omega (j : ℤ) = omega' (j : ℤ)) :
    infraredPartialSum omega L = infraredPartialSum omega' L := by
  unfold infraredPartialSum
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  have := h (n + 1) (by omega) (by omega)
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at this ⊢
  rw [this]

theorem aux_lfgc_endpoint_meas_reference_congr (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (m : ℤ) (w : SpatialCoordinates d)
    (omega omega' : BilateralField d) (hH : H omega = H omega')
    (hret : ∀ j : ℤ, (0 ≤ m → 0 ≤ j ∧ j < m) → (m < 0 → m ≤ j ∧ j < 0) →
      omega (-j) = omega' (-j)) :
    Paper.aux_lem_band_U2_reference M H N m w omega =
      Paper.aux_lem_band_U2_reference M H N m w omega' := by
  unfold Paper.aux_lem_band_U2_reference Paper.aux_lem_band_U2_retained
  have hr : (if 0 ≤ m then ∑ j ∈ Finset.Ico (0 : ℤ) m, omega (-j) w
      else -∑ j ∈ Finset.Ico m (0 : ℤ), omega (-j) w) =
      (if 0 ≤ m then ∑ j ∈ Finset.Ico (0 : ℤ) m, omega' (-j) w
      else -∑ j ∈ Finset.Ico m (0 : ℤ), omega' (-j) w) := by
    by_cases hm : 0 ≤ m
    · simp only [hm, if_true]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ico.mp hj
      rw [hret j (fun _ => hj') (fun h => absurd hm (not_le.mpr h))]
    · simp only [hm, if_false]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_Ico.mp hj
      rw [hret j (fun h => absurd h hm) (fun _ => hj')]
  rw [hH, hr]

/-- The endpoint statistic is measurable for any window containing `[-N, max L 3]`. -/
theorem lfgc_endpoint_meas (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (K : ℝ) (L : ℕ) (hoff : ∀ i, -3 ≤ offset i ∧ offset i ≤ 0)
    (hn : 0 ≤ n) (hnN : n ≤ (N : ℤ)) (lo hi : ℤ) (hlo : lo ≤ -(N : ℤ)) (hhi : (L : ℤ) ≤ hi)
    (hhi3 : 3 ≤ hi) :
    Measurable[layerWindow C(SpatialCoordinates d, ℝ) (Set.Icc lo hi)]
      (aux_lfgc_root_impl_rootX I M sigma T offset shift N n z K (fun omega => infraredPartialSum omega L)) := by
  refine measurable_layerWindow_of_depends
    (aux_lfgc_endpoint_meas_rootX_measurable hd I M _ (aux_lfgc_endpoint_meas_measurable_infraredPartialSum L) sigma hsigma T offset shift N n z K)
    fun omega omega' hagree => ?_
  have hH : infraredPartialSum omega L = infraredPartialSum omega' L :=
    aux_lfgc_endpoint_meas_infraredPartialSum_congr L omega omega' fun j hj1 hjL =>
      hagree j ⟨by omega, by omega⟩
  unfold aux_lfgc_root_impl_rootX
  congr 1
  rw [aux_lfgc_endpoint_meas_bandCoords_eq_gen, aux_lfgc_endpoint_meas_bandCoords_eq_gen]
  refine aux_lfgc_endpoint_meas_bandCoordsGen_congr I sigma sigma T offset shift n z _ _ _ _ ?_ (fun i => ?_) ?_
  · funext w r hr
    refine aux_lfgc_endpoint_meas_cutoffPositiveCoefficient_congr M _ _ omega omega' N w hr fun x => ?_
    unfold cutoffCoefficient cutoffPotential
    have hsum : ∑ j ∈ Finset.range (N + 1), (omega (-Int.ofNat j)) x =
        ∑ j ∈ Finset.range (N + 1), (omega' (-Int.ofNat j)) x := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [hagree (-(Int.ofNat j)) ⟨by simp; omega, by simp; omega⟩]
    simp only [hH, hsum]
  · refine aux_lfgc_endpoint_meas_reference_congr M _ N _ _ omega omega' hH fun j h1 h2 => hagree (-j) ⟨?_, ?_⟩
    · rcases le_or_lt 0 (n + offset i) with hm | hm
      · have := (h1 hm).2; have := (hoff i).2; omega
      · have := (h2 hm).1; omega
    · rcases le_or_lt 0 (n + offset i) with hm | hm
      · have := (h1 hm).1; omega
      · have := (h2 hm).1; have := (hoff i).1; omega
  · refine aux_lfgc_endpoint_meas_reference_congr M _ N _ _ omega omega' hH fun j h1 h2 => hagree (-j) ⟨?_, ?_⟩
    · have := (h1 hn).2; omega
    · have := (h1 hn).1; omega

end Paper
