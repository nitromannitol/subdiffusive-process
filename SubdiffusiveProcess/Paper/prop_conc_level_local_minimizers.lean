import SubdiffusiveProcess.Paper.prop_conc_level_zoom
import SubdiffusiveProcess.Paper.prop_conc_affine_minimizer_dilation
import SubdiffusiveProcess.Paper.prop_conc_uniform_coordinate_macro_growth
import SubdiffusiveProcess.Paper.prop_conc_coordinate_limit_growth
import SubdiffusiveProcess.Paper.prop_conc_controlled_affine_minimizer_growth
import SubdiffusiveProcess.Paper.prop_conc_actual_controls_with_moment
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer
import SubdiffusiveProcess.Lane2.LocalAffineLimitData
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- The dilation multiplies sup-distances by `r`. -/
theorem aux_prop_conc_level_geometry_dist {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a b : SpatialCoordinates d) :
    dist (cubeDilation z (0 : SpatialCoordinates d) r a) (cubeDilation z 0 r b) = r * dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  have : cubeDilation z (0 : SpatialCoordinates d) r a - cubeDilation z 0 r b = r • (a - b) := by
    funext i
    simp [cubeDilation]
    ring
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

/-- Preimage of a level-cell ball under the dilation is a unit-cell ball. -/
theorem aux_prop_conc_level_geometry_preimage {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) (y : SpatialCoordinates d) (rho : ℝ) :
    cubeDilation z (0 : SpatialCoordinates d) r ⁻¹'
        (Metric.ball (cubeDilation z (0 : SpatialCoordinates d) r y) rho ∩
          (centeredCube z r hr : Set (SpatialCoordinates d))) =
      Metric.ball y (rho / r) ∩ (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball]
  rw [aux_prop_conc_level_geometry_dist z hr, ← cubeDilation_preimage_centeredCube z 0 hr h1,
    Set.mem_preimage]
  constructor
  · rintro ⟨h, hu⟩
    exact ⟨by rw [lt_div_iff₀ hr]; linarith [h], hu⟩
  · rintro ⟨h, hu⟩
    exact ⟨by rw [lt_div_iff₀ hr] at h; linarith [h], hu⟩


/-- The pulled-back cutoff coefficient of the level cell is a constant multiple of the unit-cell
cutoff coefficient of the shifted field. -/
theorem aux_prop_conc_level_growth_coefficient_tie {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) (Nn : ℕ) (hkN : k ≤ Nn)
    (hcoef : ∀ N : ℕ, k ≤ N → ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (aux_prop_conc_level_zoom_T k zcell y) =
        (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (N - k) y) :
    ∀ᵐ y ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om Nn zcell hr).val (cubeDilation zcell 0 r y) =
        (aux_prop_conc_level_zoom_kap M (Nn - k) / aux_prop_conc_level_zoom_kap M Nn *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nn - k)
          (0 : SpatialCoordinates d) one_pos).val y := by
  have hq := lane4_dilation_quasi_measure_preserving d zcell (0 : SpatialCoordinates d) r hr one_pos
  have hA := hq.ae (aux_prop_conc_level_zoom_cutoff_coeFn M H om Nn zcell hr)
  have hB := aux_prop_conc_level_zoom_cutoff_coeFn M H
    (aux_prop_conc_level_zoom_Theta k zcell om) (Nn - k) (0 : SpatialCoordinates d) (r := 1) one_pos
  filter_upwards [hA, hB] with y hy1 hy2
  have hT : cubeDilation zcell (0 : SpatialCoordinates d) r y =
      aux_prop_conc_level_zoom_T k zcell y := by
    subst hrk
    rfl
  rw [hy1, hy2, hT]
  exact hcoef Nn hkN y


/-- Level-cell growth of the affine cutoff energy measure, from the unit-cell bank of the shifted field,
for a cutoff sequence along which the normalizer ratio converges. -/
theorem aux_prop_conc_level_growth_eventually {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrk : r = (3 : ℝ) ^ (-(k : ℤ))) (t : ℝ) (ht0 : 0 ≤ t)
    (hcoef : ∀ N : ℕ, k ≤ N → ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (aux_prop_conc_level_zoom_T k zcell y) =
        (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (N - k) y)
    (K0 : ℕ → ℝ)
    (hK0g : ∀ (hP0 : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
          C * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
        (N : ℕ) (x : SpatialCoordinates d) (rho : ℝ),
        x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos → 0 < rho → rho ≤ 1 →
        (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
        (aux_prop_conc_coordinate_limit_growth_measure
          (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
          (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) N
            (0 : SpatialCoordinates d) one_pos) : Measure (SpatialCoordinates d))
          (Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) ≤ ENNReal.ofReal (K0 N * rho ^ t))
    (Nseq : ℕ → ℕ) (hN : Tendsto Nseq atTop atTop) (Kb rho : ℝ) (hrho : 0 < rho)
    (hrhoN : Tendsto (fun n => aux_prop_conc_level_zoom_kap M (Nseq n - k) /
      aux_prop_conc_level_zoom_kap M (Nseq n)) atTop (𝓝 rho))
    (hKb : ∀ n, |K0 (Nseq n - k)| ≤ Kb)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
      ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
    (i : Fin d) :
    ∀ x ∈ centeredCube zcell r hr, ∀ rho' : ℝ, 0 < rho' → rho' ≤ 1 →
      ∀ᶠ n in atTop,
        aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient M H om (Nseq n) zcell hr) (Pi.single i 1)
          (Metric.ball x rho' ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal ((2 * rho * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) *
          (r ^ d * Kb / r ^ t)) * rho' ^ t) := by
  classical
  have hKb0 : 0 ≤ Kb := (abs_nonneg _).trans (hKb 0)
  obtain ⟨hP0⟩ : Nonempty (∃ C : ℝ≥0, ∀ v : killedSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖) :=
    ⟨centeredCube_killedPoincare (0 : SpatialCoordinates d) one_pos⟩
  set G : ℝ := aux_prop_conc_level_zoom_Gc H k om zcell with hG
  have hexpG : 0 < Real.exp G := Real.exp_pos _
  have hkap : ∀ n, 0 < aux_prop_conc_level_zoom_kap M (Nseq n - k) /
      aux_prop_conc_level_zoom_kap M (Nseq n) := fun n =>
    div_pos (aux_prop_conc_level_zoom_kap_pos M _) (aux_prop_conc_level_zoom_kap_pos M _)
  have hev1 : ∀ᶠ n in atTop, k ≤ Nseq n := hN.eventually_ge_atTop k
  have hev2 : ∀ᶠ n in atTop, aux_prop_conc_level_zoom_kap M (Nseq n - k) /
      aux_prop_conc_level_zoom_kap M (Nseq n) ≤ 2 * rho :=
    (hrhoN.eventually (Iic_mem_nhds (by linarith : rho < 2 * rho)))
  have hcut : Tendsto (fun n => (3 : ℝ) ^ (-((Nseq n - k : ℕ) : ℤ))) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹) (by norm_num : (3 : ℝ)⁻¹ < 1)).comp
        ((tendsto_sub_atTop_nat k).comp hN)
    simpa only [Function.comp_def, zpow_neg, zpow_natCast, inv_pow] using h
  have hr0 : 0 < r ^ t := Real.rpow_pos_of_pos hr t
  -- core case: radius at most `r`
  have hcore : ∀ x ∈ centeredCube zcell r hr, ∀ rho0 : ℝ, 0 < rho0 → rho0 ≤ r →
      ∀ᶠ n in atTop,
        aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient M H om (Nseq n) zcell hr) (Pi.single i 1)
          (Metric.ball x rho0 ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal ((2 * rho * Real.exp G * (r ^ d * Kb / r ^ t)) * rho0 ^ t) := by
    intro x hx rho0 hrho0 hrho0r
    let y : SpatialCoordinates d := (cubeDilationEquiv zcell (0 : SpatialCoordinates d) hr.ne').symm x
    have hxy : cubeDilation zcell (0 : SpatialCoordinates d) r y = x :=
      (cubeDilationEquiv zcell (0 : SpatialCoordinates d) hr.ne').apply_symm_apply x
    have hy : y ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      rw [← cubeDilation_preimage_centeredCube zcell 0 hr one_pos, Set.mem_preimage, hxy]
      exact hx
    have hratio_pos : 0 < rho0 / r := div_pos hrho0 hr
    have hratio_le : rho0 / r ≤ 1 := (div_le_one hr).2 hrho0r
    have hsmall := (tendsto_order.mp hcut).2 (rho0 / r) hratio_pos
    filter_upwards [hev1, hev2, hsmall] with n hn1 hn2 hn3
    let lam : ℝ := aux_prop_conc_level_zoom_kap M (Nseq n - k) /
      aux_prop_conc_level_zoom_kap M (Nseq n) * Real.exp G
    have hlam : 0 < lam := mul_pos (hkap n) hexpG
    have hab := aux_prop_conc_level_growth_coefficient_tie M H om zcell k r hr hrk (Nseq n) hn1 hcoef
    have hmeas := (prop_conc_affine_minimizer_dilation zcell r hr one_pos
      (cutoffPositiveCoefficient M H om (Nseq n) zcell hr)
      (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nseq n - k)
        (0 : SpatialCoordinates d) one_pos) lam hlam hab hP hP0 (Pi.single i 1)).2
      (Metric.ball x rho0 ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube zcell r hr).isOpen.measurableSet)
    rw [hmeas, ← hxy, aux_prop_conc_level_geometry_preimage zcell hr one_pos y rho0]
    have hunit : (aux_prop_conc_affine_cutoff_growth_measure
        (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
        (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nseq n - k)
          (0 : SpatialCoordinates d) one_pos) (Pi.single i 1))
        (Metric.ball y (rho0 / r) ∩
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (K0 (Nseq n - k) * (rho0 / r) ^ t) := by
      refine le_trans ?_ (hK0g hP0 (Nseq n - k) y (rho0 / r) hy hratio_pos hratio_le hn3.le)
      let mu : Fin d → Measure (SpatialCoordinates d) := fun j : Fin d =>
        aux_prop_conc_affine_cutoff_growth_measure
          (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
          (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nseq n - k)
            (0 : SpatialCoordinates d) one_pos) (Pi.single j 1)
      change mu i _ ≤ (∑ j, mu j) _
      rw [Measure.finset_sum_apply]
      exact Finset.single_le_sum (fun j _ => zero_le (mu j _)) (Finset.mem_univ i)
    have hK0n : K0 (Nseq n - k) ≤ Kb := (le_abs_self _).trans (hKb n)
    have hlam2 : lam ≤ 2 * rho * Real.exp G := mul_le_mul_of_nonneg_right hn2 hexpG.le
    calc _ ≤ ENNReal.ofReal (r ^ d * lam) *
          ENNReal.ofReal (K0 (Nseq n - k) * (rho0 / r) ^ t) := mul_le_mul_right hunit _
      _ = ENNReal.ofReal (r ^ d * lam * (K0 (Nseq n - k) * (rho0 / r) ^ t)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hdiv : (rho0 / r) ^ t = rho0 ^ t / r ^ t := Real.div_rpow hrho0.le hr.le t
        have h1 : lam * K0 (Nseq n - k) ≤ (2 * rho * Real.exp G) * Kb :=
          (mul_le_mul_of_nonneg_left hK0n hlam.le).trans
            (mul_le_mul_of_nonneg_right hlam2 hKb0)
        have hnn : 0 ≤ r ^ d / r ^ t * rho0 ^ t := by positivity
        have e1 : r ^ d * lam * (K0 (Nseq n - k) * (rho0 / r) ^ t) =
            (lam * K0 (Nseq n - k)) * (r ^ d / r ^ t * rho0 ^ t) := by
          rw [hdiv]; field_simp
        have e2 : 2 * rho * Real.exp G * (r ^ d * Kb / r ^ t) * rho0 ^ t =
            ((2 * rho * Real.exp G) * Kb) * (r ^ d / r ^ t * rho0 ^ t) := by
          field_simp
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right h1 hnn
  intro x hx rho' hrho' hrho'1
  by_cases hle : rho' ≤ r
  · exact hcore x hx rho' hrho' hle
  · push_neg at hle
    have hsub : (centeredCube zcell r hr : Set (SpatialCoordinates d)) ⊆ Metric.ball x r := by
      intro u hu
      have hu' : u ∈ Metric.ball zcell (r / 2) := hu
      have hx' : x ∈ Metric.ball zcell (r / 2) := hx
      rw [Metric.mem_ball] at hu' hx' ⊢
      calc dist u x ≤ dist u zcell + dist zcell x := dist_triangle _ _ _
        _ = dist u zcell + dist x zcell := by rw [dist_comm zcell x]
        _ < r / 2 + r / 2 := add_lt_add hu' hx'
        _ = r := by ring
    have hsub' : (centeredCube zcell r hr : Set (SpatialCoordinates d)) ⊆ Metric.ball x rho' :=
      hsub.trans (Metric.ball_subset_ball hle.le)
    have hball : Metric.ball x rho' ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)) =
        Metric.ball x r ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)) := by
      rw [Set.inter_eq_right.mpr hsub', Set.inter_eq_right.mpr hsub]
    rw [hball]
    filter_upwards [hcore x hx r hr le_rfl] with n hn
    refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
    have hB : 0 ≤ 2 * rho * Real.exp G * (r ^ d * Kb / r ^ t) := by positivity
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hle.le ht0) hB


/-- Level-cell version of the unit-cell sample lemma: analytic controls, the all-cell bounds and an
eventual cutoff growth bound give every coordinate minimizer with that growth constant. -/
theorem aux_prop_conc_level_local_minimizers_sample
    {d : ℕ} (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube zcell (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube zcell (3 * r) h3r))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (N : ℕ → ℕ) (Bg : ℝ)
    (Controls : aux_prop_conc_controlled_forms_analytic_controls d hd zcell (3 * r) h3r S
      (fun n => cutoffPositiveCoefficient M H om (N n) zcell h3r))
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds zcell (3 * r) h3r
      (fun n => cutoffCoefficient M H om (N n)) t (3 / 4))
    (hgrowth : ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
        ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
          C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
        (i : Fin d), ∀ x ∈ centeredCube zcell r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∀ᶠ n in atTop,
          aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded zcell hr) hP
            (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1)
            (Metric.ball x rho ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (Bg * rho ^ t)) :
    ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * r) h3r))
      (G : DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * r) h3r))
      (E : _root_.DirichletForm
        (volume.restrict (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d))))
      (Gamma : DirichletForm.EnergyMeasure E.toClosedForm),
    (∀ n f, GN n f =
      (responseSolution S (cutoffPositiveCoefficient M H om (N n) zcell h3r)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
    Tendsto GN atTop (𝓝 G) →
    (∀ v, E.energy v = limitFormEnergy G v) →
    (∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C) →
    ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
        ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
          C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
      (L : Fin d → ℝ),
    (∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1))
        atTop (𝓝 (L i))) →
    ∀ i : Fin d, Nonempty (DirichletForm.LocalAffineMinimizer zcell r hr h3r
      E Gamma (Pi.single i 1) (L i) Bg t) := by
  intro GN G E Gamma hGN hG hE hcore hP L hL i
  obtain ⟨U, Uc, hm, hc, hae, hb, hf, ho, he, hmin, hgr⟩ :=
    prop_conc_controlled_affine_minimizer_growth hd zcell r hr hr1 h3r S hS
      (fun n => cutoffCoefficient M H om (N n))
      (fun n => cutoffCoefficient_continuous M H om (N n))
      (fun n x => cutoffCoefficient_pos M H om (N n) x)
      (fun n => cutoffPositiveCoefficient M H om (N n) zcell h3r)
      (fun n => (cutoffPositiveCoefficient_representative M H om (N n) zcell h3r).2.2.2)
      Controls (fun n => GN n) G (fun n => hGN n) hG
      E hE hcore Gamma t (3 / 4) ht htd (by norm_num) (by norm_num) hcell hP
      (fun n => cutoffPositiveCoefficient M H om (N n) zcell hr)
      (fun n => (cutoffPositiveCoefficient_representative M H om (N n) zcell hr).2.2.2)
      (Pi.single i 1) (L i) Bg t (hL i) (hgrowth hP i)
  exact ⟨⟨U, Uc, hm, hc, hae, hb, hf, ho, he, hmin, hgr⟩⟩


/-- Actual level-`k` coordinate minimizers: growth constant `2 ρ e^{G_k(z)} r^{d-t} K(ω)` with `K`
a measurable moment-bounded majorant (constants before the model, cell and cutoff sequence),
for every cutoff sequence along which the normalizer ratio `κ_{N-k}/κ_N` converges to `ρ`. -/
theorem prop_conc_level_local_minimizers
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t p : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r),
        r = (3 : ℝ) ^ (-(k : ℝ)) →
      ∀ (S : ResponseSpace (centeredCube zcell (3 * r) h3r)),
        S.space = killedSobolevGraph (centeredCube zcell (3 * r) h3r) →
      ∀ (N : ℕ → ℕ), Tendsto N atTop atTop →
      ∀ rho : ℝ, 0 < rho →
        Tendsto (fun n => aux_prop_conc_level_zoom_kap M (N n - k) /
          aux_prop_conc_level_zoom_kap M (N n)) atTop (𝓝 rho) →
      ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ om, 0 ≤ K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
              DomainL2 (centeredCube zcell (3 * r) h3r))
          (G : DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
              DomainL2 (centeredCube zcell (3 * r) h3r))
          (E : _root_.DirichletForm
            (volume.restrict (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d))))
          (Gamma : DirichletForm.EnergyMeasure E.toClosedForm),
        (∀ n f, GN n f =
          (responseSolution S (cutoffPositiveCoefficient M H om (N n) zcell h3r)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
        Tendsto GN atTop (𝓝 G) →
        (∀ v, E.energy v = limitFormEnergy G v) →
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C) →
        ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
            ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
              C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
          (L : Fin d → ℝ),
        (∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
          (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1))
            atTop (𝓝 (L i))) →
        ∀ i : Fin d, Nonempty (DirichletForm.LocalAffineMinimizer zcell r hr h3r
          E Gamma (Pi.single i 1) (L i)
          (2 * rho * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) *
            (r ^ d * K om / r ^ t)) t) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨deltaC, hdeltaC, hcontrols⟩ := prop_conc_actual_controls_with_moment
    d hd I Pin X W Cp Sob Interp t (3 / 4) ht htd (by norm_num) (by norm_num)
  obtain ⟨deltaG, BG, hdeltaG, hBG, hbank⟩ :=
    prop_conc_uniform_coordinate_macro_growth d hd t p ht htd hp
  refine ⟨min deltaC deltaG, 2 * (BG + 1), lt_min hdeltaC hdeltaG, by positivity, ?_⟩
  intro M Rm Sreg It H hIR hdelta zcell k r hr h3r hrk S hS N hN rho hrho hrhoN
  have hrk' : r = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hrk, show (-(k : ℝ)) = (((-(k : ℤ) : ℤ)) : ℝ) by push_cast; ring, Real.rpow_intCast]
  have hr1 : r ≤ 1 := by
    rw [hrk']
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have ht0 : 0 ≤ t := by
    have hdim : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ht, hdim]
  obtain ⟨K0, hK0m, hK00, hK0n, hK0g⟩ :=
    hbank M Sreg H hIR (hdelta.trans (min_le_right _ _))
  obtain ⟨hmp, -, hcoefAE⟩ := prop_conc_level_zoom d M H hIR k zcell
  let BN : ℝ≥0 := ⟨BG, hBG⟩
  have hBN : (BN : ℝ≥0∞) = ENNReal.ofReal BG := ENNReal.ofReal_coe_nnreal.symm
  have hKcomp (n : ℕ) : eLpNorm (fun om => K0 (n - k) (aux_prop_conc_level_zoom_Theta k zcell om))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BG := by
    have := eLpNorm_comp_measurePreserving (hK0m (n - k)).aestronglyMeasurable hmp
      (p := ENNReal.ofReal p)
    exact (this.le).trans (hK0n (n - k))
  have hmem (n : ℕ) : MemLp (fun om => K0 (n - k) (aux_prop_conc_level_zoom_Theta k zcell om))
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    ⟨((hK0m (n - k)).comp hmp.measurable).aestronglyMeasurable,
      (hKcomp n).trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨Kb, hKbm, hKb0, hKbn, hC⟩ :=
    hcontrols M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) zcell (3 * r) h3r
      S hS (fun n om => K0 (n - k) (aux_prop_conc_level_zoom_Theta k zcell om)) p hp BN hmem
      (fun n => by simpa only [hBN] using hKcomp n) N
  refine ⟨Kb, hKbm, hKb0, hKbn, ?_⟩
  have hK0g' := hmp.quasiMeasurePreserving.ae hK0g
  filter_upwards [hC, hK0g', hcoefAE] with om hom hg hcoef
  obtain ⟨seq, hseq, hKbound, ⟨Controls⟩, hcell⟩ := hom
  intro GN G E Gamma hGN hG hE hcore hP L hL i
  exact aux_prop_conc_level_local_minimizers_sample hd M H om zcell r hr hr1 h3r S hS t ht htd
    (N ∘ seq) _ Controls hcell
    (fun hP' i' => aux_prop_conc_level_growth_eventually M H om zcell k r hr hrk' t ht0 hcoef
      (fun n => K0 n (aux_prop_conc_level_zoom_Theta k zcell om))
      (fun hP0 => hg hP0)
      (N ∘ seq) (hN.comp hseq.tendsto_atTop) (Kb om) rho hrho (hrhoN.comp hseq.tendsto_atTop)
      (fun n => hKbound n) hP' i')
    (fun n => GN (seq n)) G E Gamma (fun n f => hGN (seq n) f)
    (hG.comp hseq.tendsto_atTop) hE hcore hP L (fun i' => (hL i').comp hseq.tendsto_atTop) i

end
end Paper
