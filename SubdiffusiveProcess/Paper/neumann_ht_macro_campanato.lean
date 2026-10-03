module

public import SubdiffusiveProcess.Paper.neumann_ht_macro_cells
public import SubdiffusiveProcess.Paper.neumann_ht_micro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato

@[expose] public section

/-! Campanato decay at all radii for the top-block-removed coefficient: the macro half (per-cell
variances chained by `aux_prop_growth_holder_macro_campanato_unit`) glued to the micro half at the
wavelength `3^{-(N+j)}`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

theorem neumann_ht_macro_campanato (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ Kmac N om) ∧
          (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
              ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ,
                (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) ≤ rad → rad ≤ 1 →
                ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                    ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                      (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                      (v : SobolevData (unitNeumannCube d)).1) ^ 2
                    ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
                  (Kmac N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                    volume.real (Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  obtain ⟨Kd, hKd1, hunit⟩ := aux_prop_growth_holder_macro_campanato_unit (d := d) alpha ha0 ha1.le
  obtain ⟨delta1, hdelta1, hcell⟩ :=
    neumann_ht_macro_cells d hd E _P _X _W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    neumann_ht_micro_campanato d hd E _P _X _W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It hdelta j hj
  obtain ⟨Xc, CX, hXc0, hXcL, hXcB, hcellE⟩ :=
    hcell M Rm Sreg It (hdelta.trans (min_le_left _ _)) j hj
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It (hdelta.trans (min_le_right _ _)) j hj
  have hKd0 : 0 ≤ Kd := by linarith
  have hY0 : 0 ≤ ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) :=
    mul_nonneg hKd0 (by linarith)
  refine ⟨fun N om => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (Xc N om + Kmic N om),
    fun i => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (max (CX i) 0 + max (Cmic i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := mul_nonneg hc0 (add_nonneg (hXc0 N om) (hKmic0 N om))
    linarith
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).2
  · filter_upwards [hcellE, hmicE] with om hC hM
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hradN hrad1
    have hside : aux_prop_growth_holder_macro_campanato_side (N + j) =
        (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) := by
      unfold aux_prop_growth_holder_macro_campanato_side
      rw [zpow_neg, zpow_natCast]
    have hsidepos := aux_prop_growth_holder_macro_campanato_side_pos (N + j)
    have hrad0 : 0 < rad := hsidepos.trans_le (hside.trans_le hradN)
    have hA : 0 ≤ Xc N om * Kf := mul_nonneg (hXc0 N om) hKf
    have hB : 0 ≤ Kmic N om * Kf := mul_nonneg (hKmic0 N om) hKf
    have hu : MemLp ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) 2
        (volume.restrict (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))) := Lp.memLp _
    have H1 : ∀ l : ℕ, 0 ≤ l → l ≤ N + j → ∀ kk : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm l kk →
        aux_prop_growth_holder_macro_campanato_var
            (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk)
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (1 * aux_prop_growth_holder_macro_campanato_side l ^ alpha * (Xc N om * Kf)) ^ 2 *
            volume.real
              (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk) := by
      intro l _ hl kk hkk
      rw [one_mul]
      exact hC N F Kf hKf hFm hFb hmean v hsol l hl kk hkk
    have H2 : ∀ p ∈ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2), ∀ ρ : ℝ,
        aux_prop_growth_holder_macro_campanato_side (N + j) ≤ ρ →
        ρ ≤ aux_prop_growth_holder_macro_campanato_side (N + j) →
        aux_prop_growth_holder_macro_campanato_var
            (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Kmic N om * Kf) ^ 2 * ρ ^ (2 * alpha) *
            volume.real (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) := by
      intro p hp ρ hρ1 hρ2
      have hρ0 : 0 < ρ := hsidepos.trans_le hρ1
      have hρN : ρ ≤ (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) := hρ2.trans_eq hside
      have hρ1' : ρ ≤ 1 := hρ2.trans (aux_prop_growth_holder_macro_campanato_side_le_one (N + j))
      have h := hM N F Kf hKf hFm hFb hmean v hsol p hp ρ hρ0 hρN hρ1'
      rw [aux_prop_growth_holder_macro_campanato_target_eq
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        Set.inter_subset_right] at h
      exact h
    have H3 : aux_prop_growth_holder_macro_campanato_var
        (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Xc N om * Kf) ^ 2 := by
      have h0 := hC N F Kf hKf hFm hFb hmean v hsol 0 (Nat.zero_le _) (fun _ => 0)
        (by intro i; simp)
      have hcenter0 : aux_prop_growth_holder_macro_campanato_center
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          (fun _ : Fin d => (1 / 2 : ℝ)) := by
        funext i
        simp [aux_prop_growth_holder_macro_campanato_center,
          aux_prop_growth_holder_macro_campanato_side]
      have hcell0 : aux_prop_growth_holder_macro_campanato_cell
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
        unfold aux_prop_growth_holder_macro_campanato_cell
        rw [hcenter0]
        norm_num [aux_prop_growth_holder_macro_campanato_side]
      have hvol : volume.real (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) = 1 :=
        centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
      rw [hcell0, hvol, mul_one] at h0
      simpa [aux_prop_growth_holder_macro_campanato_side] using h0
    have hmain := hunit (fun _ => (1 / 2 : ℝ)) _ hu (N + j) 0 1 (Xc N om * Kf)
      (Kmic N om * Kf) (Xc N om * Kf) (aux_prop_growth_holder_macro_campanato_side (N + j))
      zero_le_one hA hB hA hsidepos le_rfl H1 H2 H3 x hx rad (hside.trans_le hradN) hrad1
    rw [aux_prop_growth_holder_macro_campanato_target_eq
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      Set.inter_subset_right]
    have harith := aux_cor_neumann_source_macro_arith Kd
      (((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) (Xc N om) (Kmic N om) Kf hKd0 hY0
      (hXc0 N om) (hKmic0 N om) hKf
    have hL0 : 0 ≤ Kd * (1 * (Xc N om * Kf) + Kmic N om * Kf +
        ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) * (Xc N om * Kf)) :=
      mul_nonneg hKd0 (add_nonneg (add_nonneg (by linarith) hB) (mul_nonneg hY0 hA))
    exact hmain.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hL0 harith 2) (Real.rpow_nonneg hrad0.le _)) measureReal_nonneg)

end Paper
