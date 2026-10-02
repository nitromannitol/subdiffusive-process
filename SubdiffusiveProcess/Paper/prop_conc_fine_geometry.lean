import SubdiffusiveProcess.Paper.lem_15
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic

/-! Level-`k` geometry of `lem-strips` for the fine-layer step of `prop-conc`: the strip and core masses of a
finite measure with the cell-normalized growth `ν(B_ρ(x) ∩ q) ≤ K (ρ/s)^t` on a cell `q` of side `s`, with
constants independent of the position `z` and of the side `s`.  The proof is the dilation `x ↦ x/s` applied
to `aux_lem_15_u_geom` (the unit-cell form of `lem_strips`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Strip and core masses (anchor `0`, box side `ell`, strip width `w`) of every finite measure with the
cell-normalized growth on the cell `q = centeredCube z s`. -/
def aux_prop_conc_fine_geometry_CellBound {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (t ell w Astrip Acore : ℝ) : Prop :=
  ∀ (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu] (Kv : ℝ), 0 ≤ Kv →
    (∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ s →
      nu (Metric.ball x rho ∩ (centeredCube z s hs : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (Kv * (rho / s) ^ t)) →
    nu ((centeredCube z s hs : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w) ≤
        ENNReal.ofReal (Astrip * Kv) ∧
      ∀ idx : Fin d → ℤ,
        nu ((centeredCube z s hs : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i + (idx i : ℝ) * ell ≤ x i ∧
            x i < (0 : SpatialCoordinates d) i + ((idx i : ℝ) + 1) * ell})
          ≤ ENNReal.ofReal (Acore * Kv)

theorem aux_prop_conc_fine_geometry_dil_ball {d : ℕ} (s : ℝ) (hs : 0 < s) (xt : SpatialCoordinates d)
    (rad : ℝ) :
    (fun y : SpatialCoordinates d => s⁻¹ • y) ⁻¹' Metric.ball xt rad =
      Metric.ball (s • xt) (s * rad) := by
  ext y
  simp only [mem_preimage, Metric.mem_ball]
  have h : dist (s⁻¹ • y) xt = s⁻¹ * dist y (s • xt) := by
    have : xt = s⁻¹ • (s • xt) := by rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    conv_lhs => rw [this]
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  rw [h]
  exact inv_mul_lt_iff₀ hs

theorem aux_prop_conc_fine_geometry_dil_cube {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    (fun y : SpatialCoordinates d => s⁻¹ • y) ⁻¹'
        (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) =
      (centeredCube z s hs : Set (SpatialCoordinates d)) := by
  have h := aux_prop_conc_fine_geometry_dil_ball s hs (s⁻¹ • z) (1 / 2)
  rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at h
  have h2 : s * (1 / 2) = s / 2 := by ring
  rw [h2] at h
  exact h

theorem aux_prop_conc_fine_geometry_dil_strip {d : ℕ} (s : ℝ) (hs : 0 < s) (ell w : ℝ) :
    (fun y : SpatialCoordinates d => s⁻¹ • y) ⁻¹' aux_lem_15_u_stripSet 0 ell w =
      aux_lem_15_u_stripSet 0 (s * ell) (s * w) := by
  ext y
  simp only [mem_preimage, aux_lem_15_u_stripSet, mem_setOf_eq, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, zero_add]
  refine exists_congr fun i => exists_congr fun j => ?_
  have h : s⁻¹ * y i - (j : ℝ) * ell = s⁻¹ * (y i - (j : ℝ) * (s * ell)) := by
    field_simp
  rw [h, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  have h2 : (j : ℝ) * (s * ell) = ((j : ℝ) * (s * ell)) := rfl
  constructor
  · intro h1
    have := (inv_mul_le_iff₀ hs).mp (by simpa [mul_comm] using h1)
    simpa [mul_comm] using this
  · intro h1
    have : |y i - (j : ℝ) * (s * ell)| ≤ s * w := h1
    have := (inv_mul_le_iff₀ hs).mpr this
    simpa [mul_comm] using this

theorem aux_prop_conc_fine_geometry_dil_box {d : ℕ} (s : ℝ) (hs : 0 < s) (ell : ℝ)
    (idx : Fin d → ℤ) :
    (fun y : SpatialCoordinates d => s⁻¹ • y) ⁻¹'
        {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i + (idx i : ℝ) * ell ≤ x i ∧
          x i < (0 : SpatialCoordinates d) i + ((idx i : ℝ) + 1) * ell} =
      {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i + (idx i : ℝ) * (s * ell) ≤ x i ∧
        x i < (0 : SpatialCoordinates d) i + ((idx i : ℝ) + 1) * (s * ell)} := by
  ext y
  simp only [mem_preimage, mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have := (le_inv_mul_iff₀ hs).mp h1
      linarith [this, mul_comm s ell, mul_comm (idx i : ℝ) (s * ell)]
    · have := (inv_mul_lt_iff₀ hs).mp h2
      linarith [this, mul_comm s ell, mul_comm ((idx i : ℝ) + 1) (s * ell)]
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_mul_iff₀ hs]
      linarith [mul_comm s ell, mul_comm (idx i : ℝ) (s * ell)]
    · rw [inv_mul_lt_iff₀ hs]
      linarith [mul_comm s ell, mul_comm ((idx i : ℝ) + 1) (s * ell)]

/-- **Level-`k` strips and cores.**  The dimensional constant `Cd` is chosen before `t`, and `r0` after `t` only;
neither depends on the cell position `z`, the cell side `s`, or the relative wavelength `rs ≤ r0`.  With
box side `ell = s rs^{(t-d+1)/(t+1)}` and strip width `w = s (Cs rs)`, both masses are `≤ Cd K rs^b`. -/
theorem prop_conc_fine_geometry (d : ℕ) (hd : 1 ≤ d) (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ t : ℝ, (d : ℝ) - 1 < t →
      0 < t * (t - (d : ℝ) + 1) / (t + 1) ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
        ∀ (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (rs : ℝ), 0 < rs → rs ≤ r0 →
          (0 < s * rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ∧
            s * rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ s ∧
            s * (Cs * rs) < s * rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ∧
          aux_prop_conc_fine_geometry_CellBound z s hs t (s * rs ^ ((t - (d : ℝ) + 1) / (t + 1)))
            (s * (Cs * rs)) (Cd * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1)))
            (Cd * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1))) := by
  obtain ⟨Cd, hCd, hgeo⟩ := aux_lem_15_u_geom d hd Cs hCs
  refine ⟨Cd, hCd, fun t ht => ?_⟩
  obtain ⟨hb, r0, hr0, hr01, hR⟩ := hgeo t ht
  refine ⟨hb, r0, hr0, hr01, fun z s hs rs hrs hrs0 => ?_⟩
  obtain ⟨⟨hell, hell1, hwl⟩, hSB⟩ := hR (s⁻¹ • z) 1 one_pos rs hrs hrs0
  rw [max_self, one_pow, mul_one] at hSB
  refine ⟨⟨mul_pos hs hell, mul_le_of_le_one_right hs.le hell1, mul_lt_mul_of_pos_left hwl hs⟩, ?_⟩
  intro nu hfin Kv hK hgrowth
  set dil : SpatialCoordinates d → SpatialCoordinates d := fun y => s⁻¹ • y with hdil_def
  have hdil : Measurable dil := (continuous_const_smul s⁻¹).measurable
  haveI : IsFiniteMeasure (nu.map dil) := Measure.isFiniteMeasure_map _ _
  have hq : dil ⁻¹' (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) =
      (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    aux_prop_conc_fine_geometry_dil_cube z s hs
  have hgr : ∀ x ∈ (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        (nu.map dil) (Metric.ball x rad ∩ (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))
          ≤ ENNReal.ofReal (Kv * rad ^ t) := by
    intro x hx rad hrad hrad1
    have hmeas : MeasurableSet (Metric.ball x rad ∩
        (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))) :=
      Metric.isOpen_ball.measurableSet.inter (centeredCube (s⁻¹ • z) 1 one_pos).isOpen.measurableSet
    rw [Measure.map_apply hdil hmeas, preimage_inter, hq, hdil_def,
      aux_prop_conc_fine_geometry_dil_ball s hs x rad]
    have hxq : s • x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)) := by
      rw [← hq]
      show s⁻¹ • (s • x) ∈ (centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
      rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
      exact hx
    have := hgrowth (s • x) hxq (s * rad) (mul_pos hs hrad) (by nlinarith)
    rwa [mul_div_cancel_left₀ _ hs.ne'] at this
  obtain ⟨hstrip, hcore⟩ := hSB (nu.map dil) Kv hK hgr
  refine ⟨?_, fun idx => ?_⟩
  · calc nu ((centeredCube z s hs : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 (s * rs ^ ((t - (d : ℝ) + 1) / (t + 1))) (s * (Cs * rs)))
        = nu (dil ⁻¹' ((centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) ∩
            aux_lem_15_u_stripSet 0 (rs ^ ((t - (d : ℝ) + 1) / (t + 1))) (Cs * rs))) := by
          rw [preimage_inter, hq, hdil_def, aux_prop_conc_fine_geometry_dil_strip s hs]
      _ ≤ (nu.map dil) _ := Measure.le_map_apply hdil.aemeasurable _
      _ ≤ _ := hstrip
  · calc nu ((centeredCube z s hs : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i +
              (idx i : ℝ) * (s * rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ≤ x i ∧
            x i < (0 : SpatialCoordinates d) i +
              ((idx i : ℝ) + 1) * (s * rs ^ ((t - (d : ℝ) + 1) / (t + 1)))})
        = nu (dil ⁻¹' ((centeredCube (s⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) ∩
            {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i +
                (idx i : ℝ) * rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ x i ∧
              x i < (0 : SpatialCoordinates d) i +
                ((idx i : ℝ) + 1) * rs ^ ((t - (d : ℝ) + 1) / (t + 1))})) := by
          rw [preimage_inter, hq, hdil_def, aux_prop_conc_fine_geometry_dil_box s hs]
      _ ≤ (nu.map dil) _ := Measure.le_map_apply hdil.aemeasurable _
      _ ≤ _ := hcore idx

end
end Paper
