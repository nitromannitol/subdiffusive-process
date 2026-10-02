import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
import SubdiffusiveProcess.Paper.lane4_weak_gradient_chain_rule
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_as_coarse
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Bridge


set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Pointwise

namespace Paper

theorem aux_killed_zero_extension_bound_s1
    {d : Nat}
    (hd : 2 ≤ d)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d)
    (r : ℝ)
    (hr : 0 < r)
    (hr1 : r ≤ OfNat.ofNat (nat_lit 1)) :
    ∀ (w : ↥(killedSobolevGraph (centeredCube z r hr))), globalFractionalSqNorm (OfNat.ofNat (nat_lit 3) / OfNat.ofNat (nat_lit 4)) ((SetLike.coe (centeredCube z r hr)).indicator fun (x : SpatialCoordinates d) => w.val.1.val.cast x) ≤ ENNReal.ofReal (_S.C * cubeFractionalSqNorm hd z r hr threeQuarterOrder w.val.1) := by
  intro w
  have hzero := _S.zeroExtension z r hr hr1 w
  rcases hzero with ⟨V, hV_ae, hV_zero, hV_bound⟩
  set f : SpatialCoordinates d → ℝ := fun x => ((w : SobolevData (centeredCube z r hr)).1) x with hf
  have h_boundary_null : volume ((closedCube z r hr : Set (SpatialCoordinates d)) \
      (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := by
    have h_subset : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (closedCube z r hr : Set (SpatialCoordinates d)) :=
      centeredCube_subset_closedCube z hr
    have h_meas : NullMeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) volume :=
      (centeredCube z r hr).isOpen.measurableSet.nullMeasurableSet
    have h_fin : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
      rw [centeredCube_volume z hr]
      exact ENNReal.ofReal_ne_top
    have h_closed_vol : volume (closedCube z r hr : Set (SpatialCoordinates d)) = ENNReal.ofReal (r ^ d) := by
      calc
        volume (closedCube z r hr : Set (SpatialCoordinates d)) = volume (Metric.closedBall z (r / 2)) := rfl
        _ = ENNReal.ofReal ((2 * (r / 2)) ^ Fintype.card (Fin d)) :=
          Real.volume_pi_closedBall z (by positivity)
        _ = ENNReal.ofReal (r ^ d) := by
          have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
          rw [hcard]
          ring
    rw [measure_diff h_subset h_meas h_fin, centeredCube_volume z hr, h_closed_vol]
    simp
  have h_diff_null : volume {x | ((SetLike.coe (centeredCube z r hr)).indicator f) x ≠ V x} = 0 := by
    have h_diff : {x | ((SetLike.coe (centeredCube z r hr)).indicator f) x ≠ V x} ⊆
        ({x | f x ≠ V x} ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ∪
        ((closedCube z r hr : Set (SpatialCoordinates d)) \ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      intro x hx
      by_cases hx_open : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
      · left
        refine ⟨?_, hx_open⟩
        simpa [Set.indicator_of_mem hx_open] using hx
      · right
        have hx_indicator_zero : ((SetLike.coe (centeredCube z r hr)).indicator f) x = 0 :=
          Set.indicator_of_not_mem hx_open _
        have hx_V_ne_zero : V x ≠ 0 := by
          intro hVzero
          apply hx
          rw [hx_indicator_zero, hVzero]
        have hx_closed : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
          by_contra hx_not_closed
          apply hx_V_ne_zero
          exact hV_zero x hx_not_closed
        exact ⟨hx_closed, hx_open⟩
    have h_null1 : volume ({x | f x ≠ V x} ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := by
      have hV_ae_measure : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
          {x | f x ≠ V x} = 0 := by
        simpa [f] using hV_ae
      have hV_ae_imp : ∀ᵐ x ∂volume,
          x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) → f x = V x :=
        ae_imp_of_ae_restrict hV_ae_measure
      rw [ae_iff] at hV_ae_imp
      change volume {x | f x ≠ V x ∧ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))} = 0
      simpa [and_comm] using hV_ae_imp
    have h_null2 : volume ((closedCube z r hr : Set (SpatialCoordinates d)) \
        (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := h_boundary_null
    exact measure_mono_null h_diff (measure_union_null h_null1 h_null2)
  have h_ae_eq : ((SetLike.coe (centeredCube z r hr)).indicator f) =ᵐ[volume] V := h_diff_null
  have h_norm_eq : globalFractionalSqNorm (OfNat.ofNat (nat_lit 3) / OfNat.ofNat (nat_lit 4))
      ((SetLike.coe (centeredCube z r hr)).indicator f) =
      globalFractionalSqNorm (3 / 4) V := by
    unfold globalFractionalSqNorm
    have h_ae : ((SetLike.coe (centeredCube z r hr)).indicator f) =ᵐ[volume] V := h_diff_null
    have h_sq_ae_eq : (fun x => ENNReal.ofReal ((((SetLike.coe (centeredCube z r hr)).indicator f) x) ^ 2)) =ᵐ[volume]
        (fun x => ENNReal.ofReal ((V x) ^ 2)) := by
      filter_upwards [h_ae] with x hx
      simp [hx]
    have hL2 : (∫⁻ x, ENNReal.ofReal ((((SetLike.coe (centeredCube z r hr)).indicator f) x) ^ 2)) =
        (∫⁻ x, ENNReal.ofReal ((V x) ^ 2)) :=
      lintegral_congr_ae h_sq_ae_eq
    have h_const : (OfNat.ofNat (nat_lit 3) / OfNat.ofNat (nat_lit 4) : ℝ) = (3 / 4 : ℝ) := by norm_num
    rw [h_const]
    have h_ae_prod : (fun (q : SpatialCoordinates d × SpatialCoordinates d) =>
        (((SetLike.coe (centeredCube z r hr)).indicator f) q.1 -
          ((SetLike.coe (centeredCube z r hr)).indicator f) q.2)) =ᵐ[volume.prod volume]
        (fun (q : SpatialCoordinates d × SpatialCoordinates d) => V q.1 - V q.2) := by
      let μ : Measure (SpatialCoordinates d) := volume
      have h_fst : ((SetLike.coe (centeredCube z r hr)).indicator f) ∘ Prod.fst =ᵐ[μ.prod μ] V ∘ Prod.fst :=
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp h_ae
      have h_snd : ((SetLike.coe (centeredCube z r hr)).indicator f) ∘ Prod.snd =ᵐ[μ.prod μ] V ∘ Prod.snd :=
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp h_ae
      filter_upwards [h_fst, h_snd] with q hq1 hq2
      change ((SetLike.coe (centeredCube z r hr)).indicator f) q.1 = V q.1 at hq1
      change ((SetLike.coe (centeredCube z r hr)).indicator f) q.2 = V q.2 at hq2
      rw [hq1, hq2]
    have h_gagliardo_ae : (fun (q : SpatialCoordinates d × SpatialCoordinates d) =>
        ENNReal.ofReal ((((SetLike.coe (centeredCube z r hr)).indicator f) q.1 -
          ((SetLike.coe (centeredCube z r hr)).indicator f) q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) =ᵐ[volume.prod volume]
        (fun (q : SpatialCoordinates d × SpatialCoordinates d) =>
        ENNReal.ofReal ((V q.1 - V q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) := by
      filter_upwards [h_ae_prod] with q hq
      simp [hq]
    have hGagliardo : (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((((SetLike.coe (centeredCube z r hr)).indicator f) q.1 -
          ((SetLike.coe (centeredCube z r hr)).indicator f) q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) =
        (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((V q.1 - V q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) :=
      lintegral_congr_ae h_gagliardo_ae
    rw [hL2, hGagliardo]
  rw [h_norm_eq]
  exact hV_bound

theorem aux_killed_zero_extension_bound_h10_cast_toFun
    {d : Nat} {U V : Set (SpatialCoordinates d)}
    (h : U = V) (u : Homogenization.H10Function U) :
    ((h ▸ u : Homogenization.H10Function V) : SpatialCoordinates d → ℝ) = (u : SpatialCoordinates d → ℝ) := by
  cases h
  rfl

theorem aux_killed_zero_extension_bound_lintegral_dilation
    {d : Nat} (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (φ : SpatialCoordinates d → ℝ≥0∞) :
    (∫⁻ x, φ (cubeDilation z z' r x)) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ x, φ x := by
  have h := lintegral_map_equiv (μ := (volume : Measure (SpatialCoordinates d))) φ
    (cubeDilationEquiv z z' hr.ne')
  have hmap : Measure.map (cubeDilationEquiv z z' hr.ne')
      (volume : Measure (SpatialCoordinates d)) =
      ENNReal.ofReal |(r ^ d)⁻¹| • volume := by
    simpa [cubeDilationEquiv_apply] using map_cubeDilation_volume z z' hr.ne'
  rw [hmap, lintegral_smul_measure] at h
  simpa [cubeDilationEquiv_apply, abs_of_pos (by positivity : 0 < (r ^ d)⁻¹)] using h.symm

theorem aux_killed_zero_extension_bound_l2_dilation
    {d : Nat} (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F G : SpatialCoordinates d → ℝ)
    (hFG : ∀ x, G x = F (cubeDilation z z' r x)) :
    (∫⁻ x, ENNReal.ofReal ((F x) ^ 2)) =
      ENNReal.ofReal (r ^ d) * ∫⁻ x, ENNReal.ofReal ((G x) ^ 2) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  have hchange : (∫⁻ x, ENNReal.ofReal ((G x) ^ 2)) =
      c * ∫⁻ x, ENNReal.ofReal ((F x) ^ 2) := by
    calc
      (∫⁻ x, ENNReal.ofReal ((G x) ^ 2)) =
          ∫⁻ x, ENNReal.ofReal ((F (cubeDilation z z' r x)) ^ 2) := by
            apply lintegral_congr
            intro x
            rw [hFG]
      _ = c * ∫⁻ x, ENNReal.ofReal ((F x) ^ 2) :=
        aux_killed_zero_extension_bound_lintegral_dilation z z' r hr
          (fun x => ENNReal.ofReal ((F x) ^ 2))
  have hfac : ENNReal.ofReal (r ^ d) * c = 1 := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ d)]
    rw [mul_inv_cancel₀ (by positivity : (r ^ d) ≠ 0)]
    simp
  calc
    (∫⁻ x, ENNReal.ofReal ((F x) ^ 2)) = 1 *
        (∫⁻ x, ENNReal.ofReal ((F x) ^ 2)) := by simp
    _ = (ENNReal.ofReal (r ^ d) * c) *
        (∫⁻ x, ENNReal.ofReal ((F x) ^ 2)) := by rw [hfac]
    _ = ENNReal.ofReal (r ^ d) *
        (c * ∫⁻ x, ENNReal.ofReal ((F x) ^ 2)) := by rw [mul_assoc]
    _ = ENNReal.ofReal (r ^ d) * ∫⁻ x, ENNReal.ofReal ((G x) ^ 2) := by
      rw [← hchange]

theorem aux_killed_zero_extension_bound_product_lintegral_dilation
    {d : Nat} (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (φ : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞) :
    (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
      φ (cubeDilation z z' r q.1, cubeDilation z z' r q.2)) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ENNReal.ofReal ((r ^ d)⁻¹) *
        ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, φ q := by
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z z' r
  let e : (SpatialCoordinates d × SpatialCoordinates d) ≃ᵐ
      (SpatialCoordinates d × SpatialCoordinates d) :=
    MeasurableEquiv.prodCongr (cubeDilationEquiv z z' hr.ne')
      (cubeDilationEquiv z z' hr.ne')
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  have hT : Measure.map T (volume : Measure (SpatialCoordinates d)) = c • volume := by
    dsimp [T, c]
    simpa [abs_of_pos (by positivity : 0 < (r ^ d))] using map_cubeDilation_volume z z' hr.ne'
  have he : Measure.map e (volume.prod volume) = (c • volume).prod (c • volume) := by
    change Measure.map (Prod.map T T) (volume.prod volume) = _
    rw [← Measure.map_prod_map volume volume
      (continuous_cubeDilation z z' r).measurable (continuous_cubeDilation z z' r).measurable]
    exact congrArg₂ Measure.prod hT hT
  have h := lintegral_map_equiv (μ := (volume.prod volume)) φ e
  rw [he, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at h
  simpa [e, T, c] using h.symm

theorem aux_killed_zero_extension_bound_double_dilation
    {d : Nat} (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s) (F G : SpatialCoordinates d → ℝ)
    (hFG : ∀ x, G x = F (cubeDilation z z' r x)) :
    (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((F q.1 - F q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
            ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) *
        (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
          ENNReal.ofReal ((G q.1 - G q.2) ^ 2) /
            ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
              ((d : ℝ) + 2 * s)) := by
  let p : ℝ := (d : ℝ) + 2 * s
  let c : ℝ≥0∞ := ENNReal.ofReal (r ^ p)
  let ci : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  let a : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hc0 : c ≠ 0 := by
    dsimp [c]
    simp [Real.rpow_pos_of_pos hr]
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hfac : a * ci = 1 := by
    dsimp [a, ci]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ d)]
    rw [mul_inv_cancel₀ (by positivity : (r ^ d) ≠ 0)]
    simp
  have hc_eq : (ENNReal.ofReal r) ^ p = c := by
    dsimp [c]
    rw [← ENNReal.ofReal_rpow_of_pos hr]
  let Kf : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((F q.1 - F q.2) ^ 2) /
      ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ p
  let Kg : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((G q.1 - G q.2) ^ 2) /
      ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ p
  have hkernel : ∀ x y : SpatialCoordinates d,
      Kf (cubeDilation z z' r x, cubeDilation z z' r y) =
        c⁻¹ * Kg (x, y) := by
    intro x y
    dsimp [Kf, Kg]
    have hnum : (F (cubeDilation z z' r x) - F (cubeDilation z z' r y)) ^ 2 =
        (G x - G y) ^ 2 := by
      rw [hFG x, hFG y]
    have hdist := sqrt_sum_sq_cubeDilation z z' hr x y
    have hdist' : Real.sqrt (∑ j : Fin d,
        (z j + r * (x j - z' j) - (z j + r * (y j - z' j))) ^ 2) =
        r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      simpa [cubeDilation] using hdist
    rw [hnum, hdist', ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp.le, hc_eq,
      div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
    ring
  have hchange := aux_killed_zero_extension_bound_product_lintegral_dilation
    z z' r hr Kf
  have htrans :
      (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        Kf (cubeDilation z z' r q.1, cubeDilation z z' r q.2)) =
      c⁻¹ * (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kg q) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)]
    exact lintegral_congr (fun q => hkernel q.1 q.2)
  have hfac2 : (a * ci) * (a * ci) = 1 := by
    simpa [hfac]
  have hDF :
      (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kf q) =
        a * a * c⁻¹ * (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kg q) := by
    calc
      (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kf q) =
          1 * (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kf q) := by simp
      _ = ((a * ci) * (a * ci)) *
          (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kf q) := by
        rw [hfac2]
      _ = a * a * (ci * ci *
          (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kf q)) := by ring
      _ = a * a *
          (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
            Kf (cubeDilation z z' r q.1, cubeDilation z z' r q.2)) := by
        rw [← hchange]
      _ = a * a * (c⁻¹ * (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kg q)) := by
        rw [htrans]
      _ = a * a * c⁻¹ *
          (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d, Kg q) := by ring
  have hconst : a * a * c⁻¹ = ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) := by
    dsimp [a, c, p]
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < r ^ ((d : ℝ) + 2 * s)),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_neg hr.le, ← Real.rpow_add hr, ← Real.rpow_add hr]
    ring_nf
  rw [hconst] at hDF
  simpa [Kf, Kg, p] using hDF
theorem aux_killed_zero_extension_bound_transport
    {d : Nat} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (w : killedSobolevGraph (centeredCube z r hr)) :
    ∃ wu : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
    ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 : SpatialCoordinates d → ℝ) x =
          ((w : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            (cubeDilation z (0 : SpatialCoordinates d) r x) := by
  obtain ⟨uH, huHval, huHgrad⟩ :=
    exists_nativeH10Function_of_killedSobolevGraph w
  let target : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  have hscale := aux_lane4_weak_gradient_chain_rule_cube_sets
    d z (0 : SpatialCoordinates d) r hr one_pos
  have hscale' : Homogenization.translateSet (-z)
      (centeredCube z r hr : Set (SpatialCoordinates d)) = r • target := by
    simpa [target, Homogenization.translateSet] using hscale
  let uShift : Homogenization.H10Function
      (Homogenization.translateSet (-z)
        (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    uH.translate (-z)
  let uScale : Homogenization.H10Function (r • target) := hscale' ▸ uShift
  let vH : Homogenization.H10Function target := uScale.unscale hr
  obtain ⟨wu, hwu_val, hwu_grad⟩ :=
    exists_killedSobolevGraph_of_nativeH10 vH
  refine ⟨wu, hwu_val.mono ?_⟩
  intro x hx
  have hvHval : vH.toH1Function.toFun =
      fun x => ((w : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        (cubeDilation z (0 : SpatialCoordinates d) r x) := by
    have harg (x : SpatialCoordinates d) : r • (x - (0 : SpatialCoordinates d)) + z =
        cubeDilation z (0 : SpatialCoordinates d) r x := by
      funext j
      simp [cubeDilation, Pi.smul_apply]
      ring
    funext y
    have huScale_val : (uScale : SpatialCoordinates d → ℝ) =
        (uShift : SpatialCoordinates d → ℝ) :=
      aux_killed_zero_extension_bound_h10_cast_toFun hscale' uShift
    have harg' : r • y + z = cubeDilation z (0 : SpatialCoordinates d) r y := by
      simpa using harg y
    simp [vH, uScale, uShift, target,
      Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.translate,
      Homogenization.H1Function.unscale, harg, harg', huHval, huScale_val]
  exact hx.trans (congrFun hvHval x)

theorem aux_killed_zero_extension_bound_global_congr_ae
    {d : Nat} (s : ℝ) (f g : SpatialCoordinates d → ℝ)
    (hfg : f =ᵐ[volume] g) :
    globalFractionalSqNorm s f = globalFractionalSqNorm s g := by
  have hL2 : (∫⁻ x, ENNReal.ofReal ((f x) ^ 2)) =
      ∫⁻ x, ENNReal.ofReal ((g x) ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  let μ : Measure (SpatialCoordinates d) := volume
  have h_fst : (f ∘ Prod.fst) =ᵐ[μ.prod μ] (g ∘ Prod.fst) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hfg
  have h_snd : (f ∘ Prod.snd) =ᵐ[μ.prod μ] (g ∘ Prod.snd) :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hfg
  have hD :
      (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((f q.1 - f q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
            ((d : ℝ) + 2 * s)) =
      ∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((g q.1 - g q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
            ((d : ℝ) + 2 * s) := by
    apply lintegral_congr_ae
    filter_upwards [h_fst, h_snd] with q hq1 hq2
    change f q.1 = g q.1 at hq1
    change f q.2 = g q.2 at hq2
    rw [hq1, hq2]
  unfold globalFractionalSqNorm
  rw [hL2, hD]

theorem aux_killed_zero_extension_bound_indicator_dilation_ae
    {d : Nat} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f g : SpatialCoordinates d → ℝ)
    (hfg : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z (0 : SpatialCoordinates d) r x)) :
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)).indicator g =ᵐ[volume]
      fun x => (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f
        (cubeDilation z (0 : SpatialCoordinates d) r x) := by
  rw [ae_restrict_iff' (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet] at hfg
  filter_upwards [hfg] with x hx
  by_cases hxQ : x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxQ,
      Set.indicator_of_mem (cubeDilation_mapsTo z (0 : SpatialCoordinates d) hr one_pos x hxQ)]
    exact hx hxQ
  · have hnot : cubeDilation z (0 : SpatialCoordinates d) r x ∉
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      intro hT
      apply hxQ
      rw [← cubeDilation_preimage_centeredCube z (0 : SpatialCoordinates d) hr one_pos]
      exact hT
    rw [Set.indicator_of_notMem hxQ, Set.indicator_of_notMem hnot]

theorem aux_killed_zero_extension_bound_cube_norm_dilation_bound
    {d : Nat} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : DomainL2 (centeredCube z r hr))
    (v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hr1 : 1 < r)
    (hsemi :
      (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => u)) ^ (2 : ℕ) =
        ENNReal.ofReal (r ^ (-(2 * (threeQuarterOrder : ℝ)))) *
          (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos
            threeQuarterOrder (fun _ : Fin 1 => v)) ^ (2 : ℕ))
    (hL2 :
      (∑ i : Fin 1, ‖(fun _ : Fin 1 => u) i‖ ^ 2) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (∑ i : Fin 1, ‖(fun _ : Fin 1 => v) i‖ ^ 2) /
          volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) :
    cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos
        threeQuarterOrder v ≤
      r ^ (3 / 2 : ℝ) * cubeFractionalSqNorm hd z r hr
        threeQuarterOrder u := by
  let P : ℝ≥0∞ := cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
    (fun _ : Fin 1 => u)
  let U : ℝ≥0∞ := cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos
    threeQuarterOrder (fun _ : Fin 1 => v)
  let q : ℝ := r ^ (3 / 2 : ℝ)
  have hq : 0 < q := Real.rpow_pos_of_pos hr _
  have hqone : 1 ≤ q := by
    dsimp [q]
    exact Real.one_le_rpow (le_of_lt hr1) (by norm_num)
  have hsemi' : P.toReal ^ 2 = q⁻¹ * U.toReal ^ 2 := by
    have h := congrArg ENNReal.toReal hsemi
    have hexp : -(2 * (threeQuarterOrder : ℝ)) = -(3 / 2 : ℝ) := by
      norm_num [threeQuarterOrder]
    have hcoef : r ^ (-(2 * (threeQuarterOrder : ℝ))) = q⁻¹ := by
      rw [hexp, Real.rpow_neg hr.le]
    simpa [P, U, hcoef, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ q⁻¹)]
      using h
  have hsemi_bound : U.toReal ^ 2 ≤ q * P.toReal ^ 2 := by
    calc
      U.toReal ^ 2 = 1 * U.toReal ^ 2 := by simp
      _ = (q * q⁻¹) * U.toReal ^ 2 := by
        rw [mul_inv_cancel₀ (ne_of_gt hq)]
      _ = q * (q⁻¹ * U.toReal ^ 2) := by rw [mul_assoc]
      _ = q * (P.toReal ^ 2) := congrArg (fun t : ℝ => q * t) hsemi'.symm
      _ ≤ q * (P.toReal ^ 2) := le_rfl
  let Lp : ℝ := (∑ i : Fin 1, ‖(fun _ : Fin 1 => u) i‖ ^ 2) /
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  let Lu : ℝ := (∑ i : Fin 1, ‖(fun _ : Fin 1 => v) i‖ ^ 2) /
    volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))
  have hL2' : Lp = Lu := hL2
  have hLu : 0 ≤ Lu := by
    dsimp [Lu]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (ENNReal.toReal_nonneg)
  have hnorm :
      U.toReal ^ 2 + Lu ≤ q * (P.toReal ^ 2 + Lp) := by
    calc
      U.toReal ^ 2 + Lu ≤ q * P.toReal ^ 2 + q * Lu := by
        exact add_le_add hsemi_bound
          (by simpa using (mul_le_mul_of_nonneg_right hqone hLu))
      _ = q * (P.toReal ^ 2 + Lu) := by ring
      _ = q * (P.toReal ^ 2 + Lp) := by rw [hL2']
  simpa [cubeFractionalSqNorm, cubeFractionalVecSqNorm,
    cubeFractionalVecSeminormSq, P, U, Lp, Lu, q] using hnorm



theorem killed_zero_extension_bound {d : Nat} (hd : 2 ≤ d)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ Cext : ℝ, 0 < Cext ∧
      ((∀ w : killedSobolevGraph (centeredCube z r hr),
        globalFractionalSqNorm (3 / 4)
          (Set.indicator (centeredCube z r hr : Set (SpatialCoordinates d))
            (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
          ENNReal.ofReal (Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (w : SobolevData (centeredCube z r hr)).1)) ∧
      (∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (omega : BilateralField d) (KN : Nat → ℝ),
        (∀ N, 0 ≤ KN N) →
        (∀ N (w : killedSobolevGraph (centeredCube z r hr)),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (w : SobolevData (centeredCube z r hr)).1 ≤
            KN N * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
              (w : SobolevData (centeredCube z r hr))
              (w : SobolevData (centeredCube z r hr))) →
        (∃ B : ℝ, ∀ N, KN N ≤ B) →
        ∃ K : ℝ, 0 ≤ K ∧
          ∀ N (w : killedSobolevGraph (centeredCube z r hr)),
            globalFractionalSqNorm (3 / 4)
              (Set.indicator (centeredCube z r hr : Set (SpatialCoordinates d))
                (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
              ENNReal.ofReal
                (K * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
                  (w : SobolevData (centeredCube z r hr))
                  (w : SobolevData (centeredCube z r hr))))) := by
  -- (1) The killed datum has zero Sobolev trace, so its zero extension obeys the displayed
  -- fractional `H^{3/4}` norm bound on the cube. This is the bounded zero-extension input
  -- carried by the published `SobolevFoundationalInput` required by `lem_coercivity`
  -- (`SobolevFoundationalInput.zeroExtension`), applied on the unit cube.
  have h_ext_unit (hr1 : r ≤ 1) :
      ∀ w : ↥(killedSobolevGraph (centeredCube z r hr)),
        globalFractionalSqNorm (3 / 4)
            ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
              (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
          ENNReal.ofReal (_S.C * cubeFractionalSqNorm hd z r hr threeQuarterOrder
            ((w : SobolevData (centeredCube z r hr)).1)) := by
    exact aux_killed_zero_extension_bound_s1 hd _S z r hr hr1
  -- (2) Transport the unit-cube bound to the fixed cube of radius `r` by `cubeDilation`:
  -- `lane4_weak_gradient_chain_rule` ties the transported gradients and
  -- `lane4_gagliardo_dilation_scaling` scales the `L²` and double-integral terms; the
  -- constant `Cext` is chosen after the fixed `r` and absorbs the scaling factors
  -- (delegate note; the conclusion is not restricted to `r ≤ 1`).
  have h_ext : ∃ Cext : ℝ, 0 < Cext ∧
      ∀ w : ↥(killedSobolevGraph (centeredCube z r hr)),
        globalFractionalSqNorm (3 / 4)
            ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
              (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
          ENNReal.ofReal (Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
            ((w : SobolevData (centeredCube z r hr)).1)) := by
    by_cases hr1 : r ≤ 1
    · exact ⟨_S.C, _S.C_pos, h_ext_unit hr1⟩
    · have hrgt : 1 < r := lt_of_not_ge hr1
      let Cext : ℝ := _S.C * (r ^ d) * r ^ (3 / 2 : ℝ)
      have hCext_pos : 0 < Cext := by
        dsimp [Cext]
        exact mul_pos (mul_pos _S.C_pos (pow_pos hr _)) (Real.rpow_pos_of_pos hr _)
      refine ⟨Cext, hCext_pos, ?_⟩
      intro w
      let Qr : Set (SpatialCoordinates d) := centeredCube z r hr
      let Q1 : Set (SpatialCoordinates d) :=
        centeredCube (0 : SpatialCoordinates d) 1 one_pos
      let f0 : SpatialCoordinates d → ℝ :=
        Qr.indicator (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)
      obtain ⟨wu, hwu⟩ := aux_killed_zero_extension_bound_transport z r hr w
      let g1 : SpatialCoordinates d → ℝ :=
        fun x => ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) x
      let g0 : SpatialCoordinates d → ℝ :=
        fun x => f0 (cubeDilation z (0 : SpatialCoordinates d) r x)
      have hind : Q1.indicator g1 =ᵐ[volume] g0 := by
        simpa [Qr, Q1, f0, g0, g1] using
          (aux_killed_zero_extension_bound_indicator_dilation_ae z r hr
            ((w : SobolevData (centeredCube z r hr)).1)
            ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
            hwu)
      have hglobal_ind := aux_killed_zero_extension_bound_global_congr_ae
        (3 / 4 : ℝ) (Q1.indicator g1) g0 hind
      have hsc := lane4_gagliardo_dilation_scaling d 1 hd z
        (0 : SpatialCoordinates d) r hr one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w : SobolevData (centeredCube z r hr)).1)
        (fun _ : Fin 1 => (wu : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) (by
            intro i
            simpa [g1] using hwu)
      obtain ⟨hsemi, hL2⟩ := hsc
      have hcube := aux_killed_zero_extension_bound_cube_norm_dilation_bound hd z r hr
        ((w : SobolevData (centeredCube z r hr)).1)
        ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
        hrgt hsemi hL2
      have hunit := aux_killed_zero_extension_bound_s1 hd _S
        (0 : SpatialCoordinates d) 1 one_pos le_rfl wu
      have hL2g := aux_killed_zero_extension_bound_l2_dilation z
        (0 : SpatialCoordinates d) r hr f0 g0 (by
          intro x
          rfl)
      have hDg := aux_killed_zero_extension_bound_double_dilation z
        (0 : SpatialCoordinates d) r hr (3 / 4 : ℝ) (by norm_num) f0 g0 (by
          intro x
          rfl)
      have hcoef : ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (3 / 4))) ≤
          ENNReal.ofReal (r ^ d) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hrgt) (by norm_num)
      have hglobal_scale : globalFractionalSqNorm (3 / 4) f0 ≤
          ENNReal.ofReal (r ^ d) * globalFractionalSqNorm (3 / 4) g0 := by
        unfold globalFractionalSqNorm
        rw [hL2g, hDg]
        have hnonneg : 0 ≤ (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
            ENNReal.ofReal ((g0 q.1 - g0 q.2) ^ 2) /
              ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^
                ((d : ℝ) + 2 * (3 / 4))) := bot_le
        calc
          ENNReal.ofReal (r ^ d) * (∫⁻ x, ENNReal.ofReal ((g0 x) ^ 2)) +
              ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (3 / 4))) *
                (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
                  ENNReal.ofReal ((g0 q.1 - g0 q.2) ^ 2) /
                    ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
                      (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) ≤
            ENNReal.ofReal (r ^ d) * (∫⁻ x, ENNReal.ofReal ((g0 x) ^ 2)) +
              ENNReal.ofReal (r ^ d) *
                (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
                  ENNReal.ofReal ((g0 q.1 - g0 q.2) ^ 2) /
                    ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
                      (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4))) := by
                exact add_le_add le_rfl
                  (mul_le_mul_of_nonneg_right hcoef hnonneg)
          _ = ENNReal.ofReal (r ^ d) *
              ((∫⁻ x, ENNReal.ofReal ((g0 x) ^ 2)) +
                (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
                  ENNReal.ofReal ((g0 q.1 - g0 q.2) ^ 2) /
                    ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
                      (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * (3 / 4)))) := by
                rw [mul_add]
      calc
        globalFractionalSqNorm (3 / 4)
            ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
              (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) =
            globalFractionalSqNorm (3 / 4) f0 := by rfl
        _ ≤ ENNReal.ofReal (r ^ d) * globalFractionalSqNorm (3 / 4) g0 :=
          hglobal_scale
        _ = ENNReal.ofReal (r ^ d) *
            globalFractionalSqNorm (3 / 4) (Q1.indicator g1) := by
          rw [hglobal_ind]
        _ ≤ ENNReal.ofReal (r ^ d) *
            ENNReal.ofReal (_S.C * cubeFractionalSqNorm hd
              (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
              ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) := by
          exact mul_le_mul_of_nonneg_left hunit
            (bot_le : 0 ≤ ENNReal.ofReal (r ^ d))
        _ ≤ ENNReal.ofReal
            (Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
              ((w : SobolevData (centeredCube z r hr)).1)) := by
          have hC : 0 ≤ _S.C := le_of_lt _S.C_pos
          have hrpow : 0 ≤ r ^ (3 / 2 : ℝ) := le_of_lt
            (Real.rpow_pos_of_pos hr _)
          have hunit_nonneg : 0 ≤ cubeFractionalSqNorm hd
              (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
              ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) := by
            dsimp [cubeFractionalSqNorm]
            exact add_nonneg (sq_nonneg _) (div_nonneg
              (Finset.sum_nonneg (fun i _ => sq_nonneg _)) ENNReal.toReal_nonneg)
          have hcub : 0 ≤ cubeFractionalSqNorm hd z r hr threeQuarterOrder
              ((w : SobolevData (centeredCube z r hr)).1) := by
            dsimp [cubeFractionalSqNorm]
            exact add_nonneg (sq_nonneg _) (div_nonneg
              (Finset.sum_nonneg (fun i _ => sq_nonneg _)) ENNReal.toReal_nonneg)
          have hprod : _S.C * (r ^ d) *
              cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos
                threeQuarterOrder
                ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) ≤
              _S.C * (r ^ d) * (r ^ (3 / 2 : ℝ)) *
                cubeFractionalSqNorm hd z r hr threeQuarterOrder
                  ((w : SobolevData (centeredCube z r hr)).1) := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left hcube
                (mul_nonneg hC (pow_nonneg (le_of_lt hr) d)))
          have hreal : (r ^ d) * (_S.C *
              cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos
                threeQuarterOrder
                ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) ≤
              Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
                ((w : SobolevData (centeredCube z r hr)).1) := by
            calc
              (r ^ d) * (_S.C * cubeFractionalSqNorm hd
                  (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
                  ((wu : SobolevData
                    (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)) =
                  _S.C * (r ^ d) * cubeFractionalSqNorm hd
                    (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
                    ((wu : SobolevData
                      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1) := by ring
              _ ≤ _S.C * (r ^ d) * (r ^ (3 / 2 : ℝ)) *
                  cubeFractionalSqNorm hd z r hr threeQuarterOrder
                    ((w : SobolevData (centeredCube z r hr)).1) := hprod
              _ = Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
                  ((w : SobolevData (centeredCube z r hr)).1) := by
                    dsimp [Cext]
          let Uval : ℝ := cubeFractionalSqNorm hd
            (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
            ((wu : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
          let Pval : ℝ := cubeFractionalSqNorm hd z r hr threeQuarterOrder
            ((w : SobolevData (centeredCube z r hr)).1)
          have hfinal : ENNReal.ofReal (r ^ d) * ENNReal.ofReal (_S.C * Uval) ≤
              ENNReal.ofReal (Cext * Pval) := by
            calc
              ENNReal.ofReal (r ^ d) * ENNReal.ofReal (_S.C * Uval) =
                  ENNReal.ofReal ((r ^ d) * (_S.C * Uval)) := by
                rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ d)]
              _ ≤ ENNReal.ofReal (Cext * Pval) := by
                apply ENNReal.ofReal_le_ofReal
                simpa [Uval, Pval] using hreal
          simpa [Uval, Pval] using hfinal
  obtain ⟨Cext, hCext_pos, hCext⟩ := h_ext
  refine ⟨Cext, hCext_pos, hCext, ?_⟩
  -- (3) Combine with the coercivity interface of `lem_coercivity`; on a sequence with a
  -- bounded coercivity constant this gives one constant. (`lem_as_coarse` supplies the
  -- full-cutoff pathwise bound on those constants; here that interface is the hypothesis
  -- `∃ B, ∀ N, KN N ≤ B`.)
  intro M H omega KN hKN_nonneg hcoerc hbound
  obtain ⟨B, hB⟩ := hbound
  have hB_nonneg : 0 ≤ B := le_trans (hKN_nonneg 0) (hB 0)
  have hK_nonneg : 0 ≤ Cext * B := mul_nonneg (le_of_lt hCext_pos) hB_nonneg
  refine ⟨Cext * B, hK_nonneg, ?_⟩
  -- (4) Assembly: `hCext` gives the zero-extension bound, `hcoerc` the coercivity
  -- inequality, and `hB` the uniform bound on the coercivity constants.
  intro N w
  have h_cube_nonneg : 0 ≤ cubeFractionalSqNorm hd z r hr threeQuarterOrder
      (w : SobolevData (centeredCube z r hr)).1 := by
    dsimp [cubeFractionalSqNorm]
    refine add_nonneg (pow_two_nonneg _) ?_
    have hvol : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      ENNReal.toReal_nonneg
    refine div_nonneg ?_ hvol
    refine Finset.sum_nonneg (fun i _ => pow_two_nonneg _)
  have h_coeff_nonneg : 0 ≤ sobolevCoefficientForm
      (cutoffPositiveCoefficient M H omega N z hr)
      (w : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube z r hr)) :=
    sobolevCoefficientForm_nonneg _ _
  have hCext_nonneg : 0 ≤ Cext := le_of_lt hCext_pos
  have h_mul1 : Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
      (w : SobolevData (centeredCube z r hr)).1 ≤
    Cext * (KN N * sobolevCoefficientForm
      (cutoffPositiveCoefficient M H omega N z hr)
      (w : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube z r hr))) := by
    gcongr
    exact hcoerc N w
  have h_mul2 : Cext * (KN N * sobolevCoefficientForm
      (cutoffPositiveCoefficient M H omega N z hr)
      (w : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube z r hr))) ≤
    (Cext * B) * sobolevCoefficientForm
      (cutoffPositiveCoefficient M H omega N z hr)
      (w : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube z r hr)) := by
    calc
      Cext * (KN N * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr)
        (w : SobolevData (centeredCube z r hr))
        (w : SobolevData (centeredCube z r hr))) =
        (Cext * KN N) * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr)
        (w : SobolevData (centeredCube z r hr))
        (w : SobolevData (centeredCube z r hr)) := by ring
      _ ≤ (Cext * B) * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr)
        (w : SobolevData (centeredCube z r hr))
        (w : SobolevData (centeredCube z r hr)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB N) hCext_nonneg)
          h_coeff_nonneg
  calc
    globalFractionalSqNorm (3 / 4)
      ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
        (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
      ENNReal.ofReal (Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
        (w : SobolevData (centeredCube z r hr)).1) := hCext w
    _ ≤ ENNReal.ofReal (Cext * (KN N * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr)
        (w : SobolevData (centeredCube z r hr))
        (w : SobolevData (centeredCube z r hr)))) :=
      ENNReal.ofReal_le_ofReal h_mul1
    _ ≤ ENNReal.ofReal ((Cext * B) * sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr)
        (w : SobolevData (centeredCube z r hr))
        (w : SobolevData (centeredCube z r hr))) :=
      ENNReal.ofReal_le_ofReal h_mul2

end Paper
