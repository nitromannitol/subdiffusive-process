module

public import SubdiffusiveProcess.Paper.cor_neumann_source

@[expose] public section

/-! All-depth cell variance bounds yield ball Campanato bounds when the function has
qualitative Campanato regularity at a higher exponent. The higher-exponent constant
need not be uniform. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric Filter SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal BigOperators Topology
noncomputable section
namespace Paper

/-- A fine enough triadic scale absorbs any fixed constant at a positive exponent. -/
theorem aux_lem_as_regularity_campanato_cells_scale (K gap rad : ℝ) (hgap : 0 < gap)
    (hrad : 0 < rad) : ∃ n : ℕ,
    aux_prop_growth_holder_macro_campanato_side n ≤ rad ∧
    K * aux_prop_growth_holder_macro_campanato_side n ^ gap ≤ 1 := by
  have hq0 : 0 ≤ (3 : ℝ) ^ (-gap) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (3 : ℝ) ^ (-gap) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hgap)
  have hlim : Tendsto (fun n : ℕ => K * ((3 : ℝ) ^ (-gap)) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul K
  have hlim' : Tendsto (fun n : ℕ => ((3 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq (n : ℕ) : aux_prop_growth_holder_macro_campanato_side n ^ gap =
      ((3 : ℝ) ^ (-gap)) ^ n := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  obtain ⟨n, hn, hk⟩ := ((hlim'.eventually (gt_mem_nhds hrad)).and
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))).exists
  refine ⟨n, ?_, ?_⟩
  · simpa only [aux_prop_growth_holder_macro_campanato_side, inv_pow] using hn.le
  · rw [heq]
    exact hk.le

/-- All-depth cell estimates and nonuniform smoother regularity imply a uniform ball estimate. -/
theorem lem_as_regularity_campanato_cells {d : ℕ} (alpha alpha0 : ℝ)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (haa0 : alpha < alpha0) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (X : ℝ), 0 ≤ X →
    ∀ (v : meanZeroSobolevGraph (unitNeumannCube d)) (Kf Km : ℝ), 0 ≤ Kf → 0 ≤ Km →
      (∀ j : ℕ, ∀ kk : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j kk →
        aux_prop_growth_holder_macro_campanato_var
          (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
          ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (aux_prop_growth_holder_macro_campanato_side j ^ alpha * (X * Kf)) ^ 2 *
            volume.real (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)) →
      (∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
            (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (v : SobolevData (unitNeumannCube d)).1) ^ 2
            ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
          (Km * Kf) ^ 2 * rad ^ (2 * alpha0) *
            volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))) →
      ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
            (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (v : SobolevData (unitNeumannCube d)).1) ^ 2
            ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
          (Cd * (X + 1) * Kf) ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  obtain ⟨Kd, hKd, hunit⟩ := aux_prop_growth_holder_macro_campanato_unit (d := d) alpha ha ha1
  let Y := (2 : ℝ) ^ (alpha + (d : ℝ) / 2)
  have hY : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
  refine ⟨1 + Kd * (1 + Y), by positivity, ?_⟩
  intro X hX v Kf Km hKf hKm hcell hmic x hx rad hrad hrad1
  obtain ⟨n, hnrad, hKmN⟩ := aux_lem_as_regularity_campanato_cells_scale Km (alpha0-alpha) rad
    (sub_pos.mpr haa0) hrad
  let s := aux_prop_growth_holder_macro_campanato_side n
  have hs : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos n
  have hs1 : s ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one n
  have hball : (unitNeumannCube d : Set (SpatialCoordinates d)) =
      ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := centeredCube_coe_eq_ball _ _ _
  have hH2 : ∀ p ∈ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2), ∀ r : ℝ, s ≤ r → r ≤ s →
      aux_prop_growth_holder_macro_campanato_var
        (ball p r ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
        Kf ^ 2 * r ^ (2 * alpha) *
          volume.real (ball p r ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) := by
    intro p hp r hr1 hr2
    have hrs : r = s := le_antisymm hr2 hr1
    subst r
    have hh := hmic p (show p ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) from hball.symm ▸ hp) s hs hs1
    rw [aux_prop_growth_holder_macro_campanato_target_eq
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      Set.inter_subset_right] at hh
    simp only [hball] at hh
    have hpow : (Km * Kf) ^ 2 * s ^ (2 * alpha0) =
        (Km * s ^ (alpha0-alpha)) ^ 2 * (Kf ^ 2 * s ^ (2 * alpha)) := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (s ^ (alpha0-alpha)) 2,
        ← Real.rpow_mul hs.le]
      simp only [Nat.cast_ofNat]
      rw [show Km ^ 2 * s ^ ((alpha0-alpha)*2) * (Kf ^ 2 * s ^ (2*alpha)) =
        Km ^ 2 * Kf ^ 2 * (s ^ ((alpha0-alpha)*2) * s ^ (2*alpha)) by ring,
        ← Real.rpow_add hs, show (alpha0-alpha)*2 + 2*alpha = 2*alpha0 by ring]
    have hsq : (Km * s ^ (alpha0-alpha)) ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ Km * s ^ (alpha0-alpha)) hKmN 2
    refine hh.trans ?_
    rw [hpow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ Kf ^ 2 * s ^ (2*alpha)))
      measureReal_nonneg
  have hzero := hcell 0 (fun _ => 0) (by intro i; norm_num [aux_prop_growth_holder_macro_campanato_Adm])
  have hcell0 : aux_prop_growth_holder_macro_campanato_cell (fun _ : Fin d => (1/2:ℝ)) 0 (fun _ => 0) =
      ball (fun _ : Fin d => (1/2:ℝ)) (1/2) := by
    unfold aux_prop_growth_holder_macro_campanato_cell aux_prop_growth_holder_macro_campanato_center
      aux_prop_growth_holder_macro_campanato_side
    norm_num only [pow_zero, inv_one, Int.cast_zero, mul_zero, add_zero]
  rw [aux_prop_growth_holder_macro_campanato_cell_volume, aux_prop_growth_holder_macro_campanato_side,
    pow_zero, inv_one, Real.one_rpow, one_mul, one_pow, mul_one, hcell0] at hzero
  have hh := hunit (fun _ => (1/2:ℝ)) _ (Lp.memLp _) n 0 1 (X*Kf) Kf (X*Kf) s
    zero_le_one (mul_nonneg hX hKf) hKf (mul_nonneg hX hKf) hs le_rfl
    (fun j _ _ k hk => by simpa only [one_mul] using! hcell j k hk) hH2 hzero
    x (show x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) from hx |> fun h => hball ▸ h) rad hnrad hrad1
  have hconst := aux_cor_neumann_source_macro_arith Kd Y X 1 Kf (zero_le_one.trans hKd) hY hX zero_le_one hKf
  have hconst' : Kd * (1*(X*Kf)+Kf+Y*(X*Kf)) ≤ (1+Kd*(1+Y))*(X+1)*Kf := by
    have hx1 : X + 1 ≥ 1 := by linarith only [hX]
    nlinarith only [hconst, mul_nonneg hX hKf]
  rw [aux_prop_growth_holder_macro_campanato_target_eq
    (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
    Set.inter_subset_right]
  simp only [hball]
  simp only [pow_zero, mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hconst' 2) (by positivity)) measureReal_nonneg)

end Paper
