module

public import SubdiffusiveProcess.Paper.neumann_ht_rem_resolved
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.calib3_reference

@[expose] public section

/-! Comparison of the infrared-free and the top-block-removed coefficient on the unit Neumann cube,
and the global energy of a mean-zero Neumann solution of the latter.

`A^{HT_j}_N = A^0_N · e^{-G_j}` with `G_j = ∑_{i<j} ω(-i)` and `exp|HT_j| ≤ W_j` on `Q`, so
`A^0_N ≤ W_j A^{HT_j}_N` pointwise.  The Poincaré inequality of `in_poincare` is applied to the
infrared-free coefficient `A^0_N` (whose coarse-grained ellipticity has the moments of
`lane4_lambda_inv_moments`) and transported to `A^{HT_j}_N` through the energy comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

/-- `A^0_N = A^{HT_j}_N · e^{-HT_j}` pointwise. -/
theorem aux_neumann_ht_coeff_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j N : ℕ)
    (om : BilateralField d) (y : SpatialCoordinates d) :
    cutoffCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om N y =
      cutoffCoefficient M (calib3_HT d j) om N y * Real.exp (-(calib3_HT d j om y)) := by
  unfold cutoffCoefficient cutoffPotential
  simp only [Pi.zero_apply, ContinuousMap.zero_apply, zero_add]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Coefficient comparison on the unit cube.** -/
theorem aux_neumann_ht_coeff_compare {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j N : ℕ)
    (om : BilateralField d) (Wt : ℝ)
    (hWpt : ∀ x : SpatialCoordinates d, (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2) →
      Real.exp |calib3_HT d j om x| ≤ Wt) :
    ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y ≤
        Wt * (cutoffPositiveCoefficient M (calib3_HT d j) om N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y := by
  filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om N (fun _ : Fin d => (1 / 2 : ℝ))
      one_pos,
    aux_prop_growth_holder_micro_campanato_coeff_ae M (calib3_HT d j) om N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos,
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with y h0 hH hy
  rw [h0, hH, aux_neumann_ht_coeff_eq M j N om y]
  have hyb : ∀ i, -(1 / 2 : ℝ) ≤ y i ∧ y i ≤ 3 / 2 := by
    intro i
    have h1 : dist (y i) (1 / 2 : ℝ) ≤ dist y (fun _ : Fin d => (1 / 2 : ℝ)) :=
      dist_le_pi_dist y (fun _ : Fin d => (1 / 2 : ℝ)) i
    have h2 : dist y (fun _ : Fin d => (1 / 2 : ℝ)) < 1 / 2 := by
      have : y ∈ Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
        have h := hy
        rw [unitNeumannCube, centeredCube_coe_eq_ball] at h
        exact h
      exact this
    rw [Real.dist_eq] at h1
    have h3 := abs_lt.1 (lt_of_le_of_lt h1 h2)
    constructor <;> linarith [h3.1, h3.2]
  have hpos : 0 < cutoffCoefficient M (calib3_HT d j) om N y :=
    cutoffCoefficient_pos M (calib3_HT d j) om N y
  have h1 : Real.exp (-(calib3_HT d j om y)) ≤ Wt :=
    (Real.exp_le_exp.2 (neg_le_abs _)).trans (hWpt y hyb)
  rw [mul_comm Wt]
  exact mul_le_mul_of_nonneg_left h1 hpos.le

/-- **Global energy** of the mean-zero Neumann solution for the top-block-removed coefficient:
Poincaré for the comparable coefficient `a0` and the energy comparison `a0 ≤ W aH`. -/
theorem aux_neumann_ht_global_energy {d : ℕ} (hd : 2 ≤ d) (E : in_J d) (P : in_poincare d hd E)
    (a0 aH : PositiveCoefficient (centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos)) (W : ℝ)
    (hW : 0 ≤ W)
    (hab : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a0.val y ≤ W * aH.val y)
    (F : SpatialCoordinates d → ℝ)
    (hF : AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFb : ∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann aH F v) :
    sobolevCoefficientForm aH (v : SobolevData (unitNeumannCube d))
        (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * P.C ^ 2 * W *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a0 (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
  set lam : ℝ := E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a0 (fun _ => (1 / 2 : ℝ)) 1 1 1
    with hlamdef
  have hlam : 0 < lam := E.lam_pos _ _ _ _ _ _ _ _
  set En : ℝ := sobolevCoefficientForm aH (v : SobolevData (unitNeumannCube d))
    (v : SobolevData (unitNeumannCube d)) with hEn
  set En0 : ℝ := sobolevCoefficientForm a0 (v : SobolevData (unitNeumannCube d))
    (v : SobolevData (unitNeumannCube d)) with hEn0
  have hEn_nn : 0 ≤ En := sobolevCoefficientForm_nonneg aH _
  have hEn0_nn : 0 ≤ En0 := sobolevCoefficientForm_nonneg a0 _
  have hvw : (v : SobolevData (unitNeumannCube d)) ∈ weakSobolevGraph (unitNeumannCube d) :=
    (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
      weakSobolevGraph (unitNeumannCube d)) v.property
  have hid : En = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      F x * (v : SobolevData (unitNeumannCube d)).1 x :=
    hsol ⟨(v : SobolevData (unitNeumannCube d)), hvw⟩
  have hpair := aux_cor_neumann_source_pairing_ae F Kf hKf hF hFb
    (v : SobolevData (unitNeumannCube d)).1
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1 :=
    centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  have hpoin := P.poincare_meanZero (fun _ => (1 / 2 : ℝ)) one_pos a0 v
  have henergy0 : localGradientEnergy a0 (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) = En0 := by
    simpa only [En0] using! localGradientEnergy_domain_eq_sobolevCoefficientForm
      a0 (v : SobolevData (unitNeumannCube d))
  have henergyH : localGradientEnergy aH (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) = En := by
    simpa only [En] using! localGradientEnergy_domain_eq_sobolevCoefficientForm
      aH (v : SobolevData (unitNeumannCube d))
  have hnorm : normalizedEnergyNorm a0 (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) = Real.sqrt En0 := by
    unfold normalizedEnergyNorm
    rw [hvol, div_one, henergy0]
  rw [centeredCube_one_volume_real, Real.sqrt_one, div_one] at hpoin
  have hpoin' : ‖(v : SobolevData (unitNeumannCube d)).1‖ ≤
      P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En0 := by
    rw [← hnorm]; exact hpoin
  have hcmp : En0 ≤ W * En := by
    have h := localGradientEnergy_le_mul a0 aH W hab (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d)))
    rwa [henergy0, henergyH] at h
  have hsq0 : Real.sqrt En0 ≤ Real.sqrt W * Real.sqrt En := by
    rw [← Real.sqrt_mul hW]
    exact Real.sqrt_le_sqrt hcmp
  have hA0 : 0 ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt W) :=
    mul_nonneg hKf (mul_nonneg (mul_nonneg P.C_pos.le (Real.rpow_nonneg hlam.le _))
      (Real.sqrt_nonneg _))
  have hmain : En ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt W) * Real.sqrt En := by
    have hCl : 0 ≤ P.C * lam ^ (-(1 / 2) : ℝ) :=
      mul_nonneg P.C_pos.le (Real.rpow_nonneg hlam.le _)
    calc En ≤ Kf * ‖(v : SobolevData (unitNeumannCube d)).1‖ := by rw [hid]; exact hpair
      _ ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En0) :=
          mul_le_mul_of_nonneg_left hpoin' hKf
      _ ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * (Real.sqrt W * Real.sqrt En)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq0 hCl) hKf
      _ = Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt W) * Real.sqrt En := by ring
  have habs := aux_prop_neumann_growth_absorb En _ hEn_nn hmain
  have hsq : (lam ^ (-(1 / 2) : ℝ)) ^ 2 = lam⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one lam
  calc En ≤ (Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt W)) ^ 2 := habs
    _ = Kf ^ 2 * P.C ^ 2 * (lam ^ (-(1 / 2) : ℝ)) ^ 2 * (Real.sqrt W) ^ 2 := by ring
    _ = Kf ^ 2 * P.C ^ 2 * W * lam⁻¹ := by rw [hsq, Real.sq_sqrt hW]; ring

/-! Bounded-source Neumann energy growth for the top-block-removed coefficient on the unit cube:
`Γ(u)(B_r(x) ∩ Q) ≤ K_N ‖f‖_∞² r^t`, `K_N = K^{res}_N (1 + C² W_j (1 + λ_N^{-1}))`, where `K^{res}`
is `neumann_ht_rem_resolved`, `W_j` the moment-bounded weight, and `λ_N^{-1}` the (infrared-free)
coarse-grained ellipticity of `lane4_lambda_inv_moments`. -/

/-- **Model-level assembly of the energy growth for the top-block-removed coefficient.** -/
theorem aux_neumann_ht_energy_model (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j k : ℕ)
    (ps : Fin k → ℝ) (t : ℝ) (hps : ∀ i, 1 ≤ ps i)
    (Kres : ℕ → BilateralField d → ℝ) (Cres : Fin k → ℝ)
    (hKres0 : ∀ N om, 0 ≤ Kres N om)
    (hKresL : ∀ i N, MemLp (Kres N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure)
    (hKresB : ∀ i N, eLpNorm (Kres N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cres i))
    (hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
        (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy
          (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        Kres N om *
          (sobolevCoefficientForm
            (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
            (u : SobolevData (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d)) +
            Kf ^ 2) * r ^ t)
    (W : BilateralField d → ℝ) (hW1 : ∀ om, 1 ≤ W om)
    (hWpt : ∀ om (x : SpatialCoordinates d), (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2) →
      Real.exp |calib3_HT d j om x| ≤ W om)
    (CW : Fin k → ℝ) (hCW0 : ∀ i, 0 ≤ CW i)
    (hWL : ∀ i, MemLp W (ENNReal.ofReal (2 * (2 * ps i))) (chaosSampleLaw M).toMeasure)
    (hWB : ∀ i, eLpNorm W (ENNReal.ofReal (2 * (2 * ps i))) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CW i))
    (Lam0 : ℕ → BilateralField d → ℝ)
    (hLam0 : ∀ N om, Lam0 N om = (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹)
    (CL : Fin k → ℝ) (hCL0 : ∀ i, 0 ≤ CL i)
    (hLamL : ∀ i N, MemLp (Lam0 N) (ENNReal.ofReal (2 * (2 * ps i)))
      (chaosSampleLaw M).toMeasure)
    (hLamB : ∀ i N, eLpNorm (Lam0 N) (ENNReal.ofReal (2 * (2 * ps i)))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (CL i)) :
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ K N om) ∧
      (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
            localGradientEnergy
              (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
            K N om * Kf ^ 2 * rad ^ t := by
  have hW0 : ∀ om, 0 ≤ W om := fun om => le_trans zero_le_one (hW1 om)
  have hLam0nn : ∀ N om, 0 ≤ Lam0 N om := by
    intro N om
    rw [hLam0]
    exact (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le
  obtain ⟨Vl, hVldef⟩ : ∃ Vl : ℕ → BilateralField d → ℝ,
      Vl = fun N om => W om * (1 + Lam0 N om) := ⟨_, rfl⟩
  have hVl0 : ∀ N om, 0 ≤ Vl N om := by
    intro N om; rw [hVldef]
    exact mul_nonneg (hW0 om) (by linarith [hLam0nn N om])
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ,
      K = fun N om => Kres N om * (1 + P.C ^ 2 * Vl N om) := ⟨_, rfl⟩
  have hK0 : ∀ N om, 0 ≤ K N om := by
    intro N om; rw [hKdef]
    exact mul_nonneg (hKres0 N om) (by have := hVl0 N om; positivity)
  have hVmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (Vl N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (Vl N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max (CW i) (CL i) * (1 + max (CW i) (CL i))) := by
    intro i N
    have hq : 1 ≤ 2 * ps i := by linarith [hps i]
    have hCp0 : 0 ≤ max (CW i) (CL i) := le_trans (hCW0 i) (le_max_left _ _)
    have hq2 : 1 ≤ 2 * (2 * ps i) := by linarith [hps i]
    have h := aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * ps i)
      (max (CW i) (CL i)) hq hCp0 W (Lam0 N) (hWL i) (hLamL i N)
      ((hWB i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      ((hLamB i N).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
    rw [hVldef]
    exact h
  have hmom := fun (i : Fin k) (N : ℕ) =>
    aux_cor_neumann_source_K_moment (chaosSampleLaw M).toMeasure (ps i) (P.C ^ 2)
      (Cres i) (max (CW i) (CL i) * (1 + max (CW i) (CL i))) (hps i) (by positivity) (Kres N)
      (Vl N) (hKresL i N) (hVmom i N).1 (hKresB i N) (hVmom i N).2
  refine ⟨K, fun i => max (max (Cres i) (P.C ^ 2 * (max (CW i) (CL i) *
        (1 + max (CW i) (CL i))))) 0 *
      (1 + max (max (Cres i) (P.C ^ 2 * (max (CW i) (CL i) *
        (1 + max (CW i) (CL i))))) 0), hK0,
    fun i N => by rw [hKdef]; exact (hmom i N).1,
    fun i N => by rw [hKdef]; exact (hmom i N).2, ?_⟩
  filter_upwards [hae] with om hom
  intro N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
  have hloc := hom N F hFm Kf hKf hFb hmean v hsol x hx rad hrad hrad1
  have hab := aux_neumann_ht_coeff_compare M j (N + j) om (W om) (hWpt om)
  have hEn := aux_neumann_ht_global_energy hd E P
    (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
      (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
    (W om) (hW0 om) hab F hFm Kf hKf hFb v hsol
  have hlampos := E.lam_pos (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
      (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1
  have hmono := E.lam_mono (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
      (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 1 (1 / 8 : ℝ) 1 (by norm_num)
  have hinv : (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
        (fun _ => (1 / 2 : ℝ)) one_pos)
      (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ Lam0 N om := by
    rw [hLam0]; exact inv_anti₀ hlampos hmono
  have hEn' : sobolevCoefficientForm
      (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
      (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * 1 * P.C ^ 2 * (W om * (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
          (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹) := by
    calc _ ≤ Kf ^ 2 * P.C ^ 2 * W om * (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
            (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := hEn
      _ = _ := by ring
  have hlamle : W om * (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
        (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ Vl N om := by
    rw [hVldef]
    exact mul_le_mul_of_nonneg_left (by linarith) (hW0 om)
  have hloc' : localGradientEnergy
      (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
      (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
      Kres N om * (sobolevCoefficientForm
        (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
        (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
        Kf ^ 2 * 1) * rad ^ t := by
    rw [mul_one]; exact hloc
  have hfin := aux_prop_neumann_growth_combine _ (Kres N om) _ Kf 1 P.C _ (Vl N om)
    (rad ^ t) (hKres0 N om) zero_le_one (Real.rpow_nonneg hrad.le _) hlamle hloc' hEn'
  rw [hKdef]
  calc _ ≤ Kf ^ 2 * (Kres N om * (1 + P.C ^ 2 * Vl N om)) * 1 * rad ^ t := hfin
    _ = Kres N om * (1 + P.C ^ 2 * Vl N om) * Kf ^ 2 * rad ^ t := by ring


theorem neumann_ht_energy (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ) (htlo : (d : ℝ) - 1 < t) (hthi : t < (d : ℝ))
    (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
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
              ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d → 0 < rad →
                rad ≤ 1 →
                localGradientEnergy
                  (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                  (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                K N om * Kf ^ 2 * rad ^ t := by
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  have hps4 : ∀ i : Fin k, 1 ≤ 2 * (2 * ps i) := fun i => by linarith [hps i]
  obtain ⟨δres, hδres, hres⟩ :=
    neumann_ht_rem_resolved d hd E _P _X _W D t k (fun i => 2 * ps i) htlo hthi hps2
  obtain ⟨δlam, hδlam, hlam⟩ :=
    aux_lane4_lambda_inv_moments_adm d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  have hδi : ∀ i : Fin k, 0 < δlam (2 * (2 * ps i)) := fun i => hδlam _ (hps4 i)
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 4 * (1 + ∑ i, ps i) := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; linarith
  have hqi : ∀ i : Fin k, 2 * (2 * ps i) ≤ Q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hQdef]; linarith
  obtain ⟨cdw, hcdw, hWeight⟩ := aux_neumann_ht_weight d hd Q hQ1
  refine ⟨min δres (min cdw (1 / (1 + ∑ j : Fin k, 1 / δlam (2 * (2 * ps j))))),
    lt_min hδres (lt_min hcdw (aux_prop_neumann_growth_delta_pos _ hδi)), ?_⟩
  intro M Rm Sreg It hδ j hj
  have hδM : M.delta ≤ δres := hδ.trans (min_le_left _ _)
  have hδW : M.delta ≤ cdw := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδMi : ∀ i : Fin k, M.delta ≤ δlam (2 * (2 * ps i)) := fun i =>
    (hδ.trans ((min_le_right _ _).trans (min_le_right _ _))).trans
      (aux_prop_neumann_growth_delta_min _ hδi i)
  obtain ⟨Kres, Cres, hKres0, hKresL, hKresB, hae⟩ := hres M Rm Sreg It hδM j hj
  have hlamI := fun i : Fin k =>
    hlam M Rm 0 (InfraredAdmissible.zero M) (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl
      (2 * (2 * ps i)) (hps4 i) (hδMi i)
  choose Clam hLamMem hLamBd using hlamI
  obtain ⟨Lam0, hLam0⟩ : ∃ Lam0 : ℕ → BilateralField d → ℝ, ∀ N om, Lam0 N om =
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ :=
    ⟨fun N om => (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹,
      fun _ _ => rfl⟩
  have hLam0fun : ∀ N, Lam0 N = fun om => (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ :=
    fun N => funext (hLam0 N)
  obtain ⟨W, hWm, hW1, hWmem, hWpt⟩ := hWeight M hδW j hj
  have hWL : ∀ i : Fin k, MemLp W (ENNReal.ofReal (2 * (2 * ps i))) (chaosSampleLaw M).toMeasure :=
    fun i => hWmem.mono_exponent (ENNReal.ofReal_le_ofReal (hqi i))
  exact aux_neumann_ht_energy_model d hd E _P M j k ps t hps Kres Cres hKres0 hKresL hKresB hae
    W hW1 hWpt (fun i => (eLpNorm W (ENNReal.ofReal (2 * (2 * ps i)))
      (chaosSampleLaw M).toMeasure).toReal) (fun i => ENNReal.toReal_nonneg) hWL
    (fun i => le_of_eq (ENNReal.ofReal_toReal (hWL i).eLpNorm_lt_top.ne).symm) Lam0 hLam0
    (fun i => max (Clam i) 0) (fun i => le_max_right _ _)
    (fun i N => by rw [hLam0fun N]; exact hLamMem i (N + j))
    (fun i N => by
      rw [hLam0fun N]
      exact (hLamBd i (N + j)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

end Paper
