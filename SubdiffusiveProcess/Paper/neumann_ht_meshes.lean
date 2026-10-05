module

public import SubdiffusiveProcess.Paper.neumann_ht_onestep
public import SubdiffusiveProcess.Paper.calib3_reference
public import SubdiffusiveProcess.Paper.rem_resolved
public import SubdiffusiveProcess.Paper.lane4_reference_mesh_statistic
public import SubdiffusiveProcess.Main.InfraredAdmissible
public import SubdiffusiveProcess.Paper.rem_resolved_meshes

@[expose] public section

/-! Helpers for the mesh assembly of the top-block-removed coefficient: the weight
`W_j = ∑_{c ∈ {0,1}^d} exp ‖HT_j‖_{L^∞(closedCube c 1)}` dominating `exp |HT_j|` on
`[-1/2, 3/2]^d` with all finite moments, and the comparison of the literal references `b_k` of two
infrared potentials that differ by a bounded factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- **Comparison of the literal references** of two infrared potentials whose ratio
`exp (H1 - H2)` lies in `[Wt⁻¹, Wt]` on the reference ball. -/
theorem aux_neumann_ht_bref_compare {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (z : SpatialCoordinates d) (Wt : ℝ) (hWt : 1 ≤ Wt)
    (hW : ∀ x ∈ Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2),
      Wt⁻¹ ≤ Real.exp (H1 omega x - H2 omega x) ∧ Real.exp (H1 omega x - H2 omega x) ≤ Wt) :
    aux_rem_resolved_meshes_bref M H1 omega N k z ≤
        Wt * aux_rem_resolved_meshes_bref M H2 omega N k z ∧
      Wt⁻¹ * aux_rem_resolved_meshes_bref M H2 omega N k z ≤
        aux_rem_resolved_meshes_bref M H1 omega N k z := by
  have hWt0 : 0 < Wt := lt_of_lt_of_le one_pos hWt
  set B : Set (SpatialCoordinates d) := Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2) with hB
  have hBm : MeasurableSet B := measurableSet_ball
  have hvol : 0 < volume.real B := by
    have : volume B ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    exact ENNReal.toReal_pos this measure_ball_lt_top.ne
  obtain ⟨sH, hsH⟩ : ∃ sH : (BilateralField d → C(SpatialCoordinates d, ℝ)) →
      SpatialCoordinates d → ℝ, sH = fun H x =>
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp ((H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := ⟨_, rfl⟩
  have hcont : ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), Continuous (sH H) := by
    intro H
    rw [hsH]
    refine continuous_const.mul (Real.continuous_exp.comp ?_)
    exact ((H omega).continuous.add (continuous_finsetSum (Finset.range k) fun j _ =>
      (omega (-(j : ℤ))).continuous)).sub continuous_const
  have hint : ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), IntegrableOn (sH H) B := by
    intro H
    exact ((hcont H).continuousOn.integrableOn_compact (isCompact_closedBall z _)).mono_set
      Metric.ball_subset_closedBall
  have hrel : ∀ x, sH H1 x = sH H2 x * Real.exp (H1 omega x - H2 omega x) := by
    intro x
    rw [hsH]
    dsimp only
    rw [mul_assoc, ← Real.exp_add]
    congr 3
    ring
  have hpos2 : ∀ x, 0 ≤ sH H2 x := fun x => by
    rw [hsH]
    have := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
    have := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    positivity
  have hb : ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ),
      aux_rem_resolved_meshes_bref M H omega N k z = (volume.real B)⁻¹ * ∫ x in B, sH H x := by
    intro H
    rw [hsH]
    rfl
  rw [hb H1, hb H2]
  have hi0 : 0 ≤ (volume.real B)⁻¹ := inv_nonneg.mpr hvol.le
  constructor
  · have h1 : (∫ x in B, sH H1 x) ≤ ∫ x in B, Wt * sH H2 x := by
      refine setIntegral_mono_on (hint H1) ((hint H2).const_mul Wt) hBm ?_
      intro x hx
      rw [hrel x, mul_comm Wt]
      exact mul_le_mul_of_nonneg_left (hW x hx).2 (hpos2 x)
    rw [integral_const_mul] at h1
    calc (volume.real B)⁻¹ * ∫ x in B, sH H1 x ≤ (volume.real B)⁻¹ * (Wt * ∫ x in B, sH H2 x) :=
          mul_le_mul_of_nonneg_left h1 hi0
      _ = Wt * ((volume.real B)⁻¹ * ∫ x in B, sH H2 x) := by ring
  · have h1 : (∫ x in B, Wt⁻¹ * sH H2 x) ≤ ∫ x in B, sH H1 x := by
      refine setIntegral_mono_on ((hint H2).const_mul Wt⁻¹) (hint H1) hBm ?_
      intro x hx
      rw [hrel x, mul_comm Wt⁻¹]
      exact mul_le_mul_of_nonneg_left (hW x hx).1 (hpos2 x)
    rw [integral_const_mul] at h1
    calc Wt⁻¹ * ((volume.real B)⁻¹ * ∫ x in B, sH H2 x) =
          (volume.real B)⁻¹ * (Wt⁻¹ * ∫ x in B, sH H2 x) := by ring
      _ ≤ (volume.real B)⁻¹ * ∫ x in B, sH H1 x := mul_le_mul_of_nonneg_left h1 hi0

/-- The sum `b + b⁻¹` of the literal references compares with the same weight. -/
theorem aux_neumann_ht_bref_sum_le {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (z : SpatialCoordinates d) (Wt : ℝ) (hWt : 1 ≤ Wt)
    (hW : ∀ x ∈ Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2),
      Wt⁻¹ ≤ Real.exp (H1 omega x - H2 omega x) ∧ Real.exp (H1 omega x - H2 omega x) ≤ Wt) :
    aux_rem_resolved_meshes_bref M H1 omega N k z +
        (aux_rem_resolved_meshes_bref M H1 omega N k z)⁻¹ ≤
      Wt * (aux_rem_resolved_meshes_bref M H2 omega N k z +
        (aux_rem_resolved_meshes_bref M H2 omega N k z)⁻¹) := by
  obtain ⟨h1, h2⟩ := aux_neumann_ht_bref_compare M H1 H2 omega N k z Wt hWt hW
  have hWt0 : 0 < Wt := lt_of_lt_of_le one_pos hWt
  have hb2 : 0 < aux_rem_resolved_meshes_bref M H2 omega N k z :=
    aux_lane4_two_mesh_energy_bound_bpos M H2 omega N k z
  have hb1 : 0 < aux_rem_resolved_meshes_bref M H1 omega N k z :=
    aux_lane4_two_mesh_energy_bound_bpos M H1 omega N k z
  have h3 : (aux_rem_resolved_meshes_bref M H1 omega N k z)⁻¹ ≤
      Wt * (aux_rem_resolved_meshes_bref M H2 omega N k z)⁻¹ := by
    have hpos : 0 < Wt⁻¹ * aux_rem_resolved_meshes_bref M H2 omega N k z :=
      mul_pos (inv_pos.2 hWt0) hb2
    calc (aux_rem_resolved_meshes_bref M H1 omega N k z)⁻¹
        ≤ (Wt⁻¹ * aux_rem_resolved_meshes_bref M H2 omega N k z)⁻¹ := inv_anti₀ hpos h2
      _ = Wt * (aux_rem_resolved_meshes_bref M H2 omega N k z)⁻¹ := by
          rw [mul_inv, inv_inv]
  linarith

/-- **The weight of the top-block-removed potential.**  A measurable `W_j ≥ 1` with every finite
moment dominating `exp |HT_j|` on `[-1/2, 3/2]^d`; the smallness threshold does not depend on `j`. -/
theorem aux_neumann_ht_weight (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ cd : ℝ, 0 < cd ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ cd →
      ∀ j : ℕ, 0 < j →
        ∃ W : BilateralField d → ℝ, Measurable W ∧ (∀ om, 1 ≤ W om) ∧
          MemLp W (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ∧
          ∀ om (x : SpatialCoordinates d), (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2) →
            Real.exp |calib3_HT d j om x| ≤ W om := by
  obtain ⟨cd, hcd, href⟩ := calib3_reference d hd Q hQ
  refine ⟨cd, hcd, ?_⟩
  intro M hδ j hj
  set cv : (Fin d → Bool) → SpatialCoordinates d := fun c i => if c i then 1 else 0 with hcv
  have hall := fun c : Fin d → Bool => href M hδ j hj (cv c)
  refine ⟨fun om => ∑ c : Fin d → Bool,
      aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1 one_pos,
    Finset.measurable_sum _ fun c _ => (hall c).1, ?_, ?_, ?_⟩
  · intro om
    have hne : (Finset.univ : Finset (Fin d → Bool)).Nonempty := Finset.univ_nonempty
    obtain ⟨c0, hc0⟩ := hne
    have h1 : ∀ c : Fin d → Bool, 1 ≤ aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om)
        (cv c) 1 one_pos := fun c => by
      unfold aux_prop_growth_trunc_bank_refFactor
      exact Real.one_le_exp (norm_nonneg _)
    calc (1 : ℝ) ≤ aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c0) 1 one_pos :=
          h1 c0
      _ ≤ ∑ c : Fin d → Bool, aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1
            one_pos :=
          Finset.single_le_sum (f := fun c : Fin d → Bool =>
            aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1 one_pos)
            (fun c _ => le_trans zero_le_one (h1 c)) hc0
  · exact memLp_finsetSum (Finset.univ : Finset (Fin d → Bool))
      (fun c _ => (hall c).2.2)
  · intro om x hx
    set c : Fin d → Bool := fun i => decide (1 / 2 < x i) with hc
    have hxc : x ∈ (closedCube (cv c) 1 one_pos : Set (SpatialCoordinates d)) := by
      change x ∈ Metric.closedBall (cv c) (1 / 2)
      rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
      intro i
      rw [Real.dist_eq, abs_le]
      have := hx i
      by_cases h : 1 / 2 < x i
      · have hci : c i = true := by simp only [hc]; exact decide_eq_true h
        simp only [hcv, hci, ite_true]
        constructor <;> linarith [this.1, this.2]
      · have hci : c i = false := by simp only [hc]; exact decide_eq_false h
        simp only [hcv, hci]
        simp only [Bool.false_eq_true, ite_false]
        push Not at h
        constructor <;> linarith [this.1, this.2]
    calc Real.exp |calib3_HT d j om x|
        ≤ aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1 one_pos :=
          (hall c).2.1 om x hxc
      _ ≤ ∑ c : Fin d → Bool,
            aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1 one_pos :=
          Finset.single_le_sum (f := fun c : Fin d → Bool =>
            aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) (cv c) 1 one_pos)
            (fun c _ => by unfold aux_prop_growth_trunc_bank_refFactor; positivity)
            (Finset.mem_univ c)

/-! Mesh assembly for the top-block-removed coefficient `A^{HT_j}_{N+j}` on the unit Neumann cube:
the energy of a mean-zero Neumann solution on every cube of side `r ≥ 3^{-(N+j)}` is bounded by
`C_j U_N r^{t0-η} (E(Q) + V_N ‖f‖_∞²)`, where `U_N` is the folded-iteration statistic (a function of the
prefix lengths only) and `V_N = W_j (1 + V_N^0)` is the reference-mesh statistic of the
infrared-free coefficient multiplied by the moment-bounded weight `W_j`.  The threshold does not depend
on `j`; the constant `C_j` (through the root cap `3^{-(j+7)}/2`) and the moment bounds do. -/

/-- The weighted reference statistic: for the top-block-removed coefficient the literal references
`b_k` are bounded by `W (1 + V^0) R_k^{-η}`, from the same bound for the infrared-free coefficient. -/
theorem aux_neumann_ht_meshes_Vbound {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ)
    (om : BilateralField d) (Np : ℕ) (etas W V0 : ℝ) (hW1 : 1 ≤ W)
    (hWpt : ∀ x : SpatialCoordinates d, (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2) →
      Real.exp |calib3_HT d j om x| ≤ W)
    (hV0 : ∀ kk : ℕ, kk ≤ Np → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
      aux_rem_resolved_meshes_bref M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np kk z +
          (aux_rem_resolved_meshes_bref M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
            kk z)⁻¹ ≤ V0 * ((3 : ℝ) ^ (-((kk : ℤ))) / 2) ^ (-etas)) :
    ∀ kk : ℕ, kk ≤ Np → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
      aux_rem_resolved_meshes_bref M (calib3_HT d j) om Np kk z +
          (aux_rem_resolved_meshes_bref M (calib3_HT d j) om Np kk z)⁻¹ ≤
        (W * (1 + V0)) * ((3 : ℝ) ^ (-((kk : ℤ))) / 2) ^ (-etas) := by
  intro kk hkk z hz
  have hb := aux_neumann_ht_bref_sum_le M (calib3_HT d j) 0 om Np kk z W hW1
    (by
      intro x hx'
      have hxb : ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2 := by
        intro i
        have h1 : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
        have h2 : dist x z < (3 : ℝ) ^ (-((kk : ℤ))) / 2 := hx'
        have h3 : (3 : ℝ) ^ (-((kk : ℤ))) ≤ 1 :=
          zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
        have h4 : |x i - z i| < 1 / 2 := by
          rw [Real.dist_eq] at h1
          exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (by linarith))
        have h5 := abs_lt.1 h4
        have h6 := hz i
        constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]
      have hpt := hWpt x hxb
      have hy : Real.exp (calib3_HT d j om x - (0 : BilateralField d →
          C(SpatialCoordinates d, ℝ)) om x) = Real.exp (calib3_HT d j om x) := by
        simp
      rw [hy]
      constructor
      · have h1 : Real.exp (-|calib3_HT d j om x|) ≤ Real.exp (calib3_HT d j om x) :=
          Real.exp_le_exp.2 (neg_abs_le _)
        have h2 : W⁻¹ ≤ Real.exp (-|calib3_HT d j om x|) := by
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hpt
        exact h2.trans h1
      · exact (Real.exp_le_exp.2 (le_abs_self _)).trans hpt)
  have h2 := hV0 kk hkk z hz
  have hW0 : 0 ≤ W := le_trans zero_le_one hW1
  have hR' : 0 ≤ ((3 : ℝ) ^ (-((kk : ℤ))) / 2) ^ (-etas) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ W * (aux_rem_resolved_meshes_bref M 0 om Np kk z +
        (aux_rem_resolved_meshes_bref M 0 om Np kk z)⁻¹) := hb
    _ ≤ W * (V0 * ((3 : ℝ) ^ (-((kk : ℤ))) / 2) ^ (-etas)) :=
        mul_le_mul_of_nonneg_left h2 hW0
    _ ≤ (W * (1 + V0)) * ((3 : ℝ) ^ (-((kk : ℤ))) / 2) ^ (-etas) := by
        nlinarith [mul_nonneg hW0 hR']

theorem neumann_ht_meshes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t0 eta etas p q : ℝ)
    (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta)
    (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas)
    (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p)
    (hpq : p ≤ q)
    (hdq_eta : (d : ℝ) < q * eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
        (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (hdet : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ Cm Cp : ℝ, 0 < Cm ∧ 0 < Cp ∧
          ∃ U V : ℕ → BilateralField d → ℝ,
            (∀ N, Measurable (U N)) ∧ (∀ N, Measurable (V N)) ∧
            (∀ N omega, 0 ≤ U N omega) ∧ (∀ N omega, 0 ≤ V N omega) ∧
            (∀ N, MemLp (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, MemLp (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal Cp) ∧
            (∀ N, eLpNorm (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal Cp) ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
              ∀ f : SpatialCoordinates d → ℝ,
                AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              ∀ Kf : ℝ, 0 ≤ Kf →
                (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
                  |f y| ≤ Kf) →
                (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
              ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
                SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
              ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
                ∀ r : ℝ, (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) ≤ r →
                  aux_rem_resolved_meshes_energy
                      (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
                      {y | ∀ i : Fin d, |y i - x i| < r / 2} ≤
                    Cm * U N omega * r ^ (t0 - eta) *
                      (aux_rem_resolved_meshes_energy
                        (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
                        (unitNeumannCube d : Set (SpatialCoordinates d)) +
                        V N omega * Kf ^ 2) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0pos : 0 < t0 := by linarith
  -- the deterministic engine
  obtain ⟨Kt, Cstep, c, delta1, hKt, hCstep, hc, hdelta1, hone⟩ :=
    neumann_ht_onestep d hd 10 t0 (by norm_num) ht0_low ht0_high
  have hp2 : 1 ≤ 2 * p := by linarith
  have hq1 : 1 ≤ q := hp.trans hpq
  -- reference-mesh statistics of the infrared-free coefficient, at the doubled moment order
  obtain ⟨qref, hpqref, hqqref, hgapref, dref, Cmom, Crate, Cosc, CV, hdref, hCmom, hCrate,
    hCosc, hCV, hdref1, hbudget, href⟩ :=
    aux_lane4_reference_mesh_statistic_adm d 1 hd le_rfl (2 * p) q etas hp2 hq1 hetas_pos
  obtain ⟨cC, c1, c2, hcC1, -, -, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  have hKt1 : 1 ≤ Kt := by
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hα1 : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have haT : 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt < 1 := by
    have : 0 < (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := div_pos hα1 (by linarith)
    linarith
  have haThalf : 1 / 2 ≤ 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := by
    have h1 : (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt ≤ 1 - (t0 + 2 - (d : ℝ)) / 2 :=
      div_le_self hα1.le hKt1
    linarith
  have hr1 : 1 ≤ ((d : ℝ) + 1) * q := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hr0 : 0 < ((d : ℝ) + 1) * q := by linarith
  have hδfacts := aux_rem_resolved_meshes_delta_facts cC
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (((d : ℝ) + 1) * q) c hcC1 haT hr0 hc
  rcases hδfacts with ⟨hδm, hδall⟩
  have hK1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
      (Real.exp (c * (cC + 1)) * (1 + cC)) := by
    have h1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ Real.exp (c * (cC + 1)) * (1 + cC) :=
      one_le_mul_of_one_le_of_one_le h2 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h3
  -- the weight of the removed top block
  obtain ⟨cdw, hcdw, hWeight⟩ := aux_neumann_ht_weight d hd (2 * p) hp2
  refine ⟨min dref (min delta1 (min (min (1 / 2) (min (1 / cC)
      (min (((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) / cC) ^ 2)
        ((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) ^ 2 /
          (2 * (((d : ℝ) + 1) * q) * c * cC))))) cdw)),
    lt_min hdref (lt_min hdelta1 (lt_min hδm hcdw)), ?_⟩
  intro M E Poinc Ext Rm Sreg It hdet hδ j hj
  have hδref : M.delta ≤ dref := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ delta1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm' := hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδw : M.delta ≤ cdw :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδf := hδall M.delta hδpos hδm'
  rcases hδf with ⟨hdC, haTr, hrate⟩
  have hCeq : It.C = cC := (hconst E M Sreg It).1
  have hαT : (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) ∈ It.alphaRange := by
    rw [It.alphaRange_eq, hCeq]
    exact ⟨haThalf, haTr⟩
  have hδIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdC
  have hR := href M Rm 0 (InfraredAdmissible.zero M) hδref
  rcases hR with ⟨-, -, -, -, -, V0, hV0m, hV00, hV0mem, hV0norm, hV0ae⟩
  have hKsub : closure (unitNeumannCube d : Set (SpatialCoordinates d)) ⊆
      {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :=
    aux_rem_resolved_meshes_closure_subset d
  -- the weight
  obtain ⟨W, hWm, hW1, hWmem, hWpt⟩ := hWeight M hδw j hj
  -- the folded-iteration statistic
  let alpha : ℝ := (t0 + 2 - (d : ℝ)) / 2
  let relabel : ℕ → BilateralField d → BilateralField d :=
    fun N omega j =>
      ContinuousMap.compRightContinuousMap ℝ
        (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
          (by fun_prop)⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))
        (omega (j - (N : ℤ)))
  let Grid : ℕ → Type := fun n => Fin d → Fin (3 ^ (n + 1) + 1)
  let Cat : ℕ → Type :=
    fun n => (Fin d → Fin (3 ^ (n + 1) + 1)) × ((Fin (d + 1) → Fin (n + 1 + 1)) × Equiv.Perm (Fin d))
  let ygrid : (n : ℕ) → Grid n → SpatialCoordinates d :=
    fun n a i => (a i : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ)))
  let active : (n : ℕ) → Cat n → Fin (d + 1) → Set (Fin d) :=
    fun n pi i => {a : Fin d | (pi.2.2.symm a).val < i.val}
  let center : SpatialCoordinates d → Set (Fin d) → SpatialCoordinates d :=
    fun y I a => if a ∈ I then (if y a ≤ 1 / 2 then 0 else 1) else y a
  let k : (n : ℕ) → Cat n → Fin (d + 1) → ℕ := fun n pi i => (pi.2.1 i).val
  let allowance : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ :=
    fun N n pi i omega =>
      if k n pi i ≤ N then
        (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i))
            (1 - (1 - alpha) / Kt) (N - k n pi i + 1) (relabel N omega) : ℝ) +
          ((1 : ℕ) : ℝ) + (It.k : ℝ) + 5
      else 0
  have hBmom : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)),
      MemLp (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
          (Real.exp (c * (cC + 1)) * (1 + cC))) :=
    fun N n pi i => aux_rem_resolved_meshes_allowance_moment It cC hCeq hcC1 _ hαT hδIt c
      (((d : ℝ) + 1) * q) hc hr1 hrate 1
      ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i)) N (k n pi i)
  have hB0 : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)) (om : BilateralField d),
      0 ≤ allowance N n pi i om := by
    intro N n pi i om
    simp only [allowance]
    split_ifs <;> positivity
  have hU := aux_rem_resolved_meshes_regularity d 1 (chaosSampleLaw M).toMeasure p q eta hp hpq
    heta_pos hdq_eta Cstep c
    (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))
    hCstep hc.le hK1 (fun N n pi i om => allowance N n pi i om) hB0
    (fun N n pi i => (hBmom N n pi i).1) (fun N n pi i => (hBmom N n pi i).2)
  rcases hU with ⟨U, hUm, hU0, hUmem, hUnorm, hUae, hRb⟩
  -- the root cap and the constant
  set Rj : ℝ := (3 : ℝ) ^ (-((j + 7 : ℕ) : ℤ)) / 2 with hRjdef
  have hRjpos : 0 < Rj := by rw [hRjdef]; positivity
  have hRjlt : Rj < 1 / (100 * 10) := by
    have h1 : (3 : ℝ) ^ (-((j + 7 : ℕ) : ℤ)) ≤ (3 : ℝ) ^ (-(7 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      push_cast; omega
    have h2 : (3 : ℝ) ^ (-(7 : ℤ)) = 1 / 2187 := by norm_num
    have h3 : Rj ≤ 1 / 4374 := by
      rw [hRjdef]
      rw [h2] at h1
      linarith
    exact lt_of_le_of_lt h3 (by norm_num)
  have hRjmem : Rj ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-((j + 7 : ℕ) : ℤ), rfl⟩
  -- moment of the weighted reference statistic
  obtain ⟨CW, hCWdef⟩ : ∃ CW : ℝ, CW = (eLpNorm W (ENNReal.ofReal (2 * p))
    (chaosSampleLaw M).toMeasure).toReal := ⟨_, rfl⟩
  have hCW0 : 0 ≤ CW := by rw [hCWdef]; exact ENNReal.toReal_nonneg
  have hWb : eLpNorm W (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CW := by
    rw [hCWdef, ENNReal.ofReal_toReal hWmem.eLpNorm_lt_top.ne]
  set Cp1 : ℝ := max CW CV with hCp1def
  have hCp10 : 0 ≤ Cp1 := le_trans hCW0 (le_max_left _ _)
  have hVmom : ∀ N : ℕ, MemLp (fun om => W om * (1 + V0 (N + j) om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => W om * (1 + V0 (N + j) om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp1 * (1 + Cp1)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure p Cp1 hp hCp10 W (V0 (N + j))
      hWmem (hV0mem (N + j)) (hWb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      ((hV0norm (N + j)).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
  have hCp1' : 0 ≤ Cp1 * (1 + Cp1) := by positivity
  refine ⟨2 ^ d + (36 * (3 * (1 + 100 * 10)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rj ^ (-t0) + (d : ℝ) + 1),
    max 1 (max (aux_rem_resolved_meshes_Rbound d 1 eta q Cstep
      (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))).toReal
      (Cp1 * (1 + Cp1))),
    aux_lane4_two_mesh_energy_bound_Cpos d 10 Rj t0 eta (by norm_num) hRjpos,
    lt_of_lt_of_le one_pos (le_max_left _ _),
    fun N => U (N + j), fun N om => W om * (1 + V0 (N + j) om),
    fun N => hUm (N + j), fun N => hWm.mul (measurable_const.add (hV0m (N + j))),
    fun N om => hU0 (N + j) om,
    fun N om => mul_nonneg (by linarith [hW1 om]) (by linarith [hV00 (N + j) om]),
    fun N => hUmem (N + j), fun N => (hVmom N).1,
    fun N => (hUnorm (N + j)).trans (le_trans (le_of_eq (ENNReal.ofReal_toReal hRb).symm)
      (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _)))),
    fun N => (hVmom N).2.trans (ENNReal.ofReal_le_ofReal
      ((le_max_right _ _).trans (le_max_right _ _))), ?_⟩
  filter_upwards [hUae, hV0ae] with om hUlub hVlub
  intro N f hf Kf hKf hfb hf0 u hu x hx r hr
  have hsum : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
      (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
      (∑ l : Fin (d + 1), aux_rem_resolved_meshes_B
        (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
          (aux_rem_resolved_meshes_relabel (N + j) om)) (N + j) 1 It.k
        (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
        (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < l.val)) (dep l).val) =
      ∑ l : Fin (d + 1), allowance (N + j) n (g, (dep, σ)) l om := by
    intro n g dep σ
    apply Finset.sum_congr rfl
    intro l _
    simp only [aux_rem_resolved_meshes_B, allowance, k, center, ygrid, active, relabel, alpha,
      aux_rem_resolved_meshes_center_filter]
    rfl
  have hUcore : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
      (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
      (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ l : Fin (d + 1),
        aux_rem_resolved_meshes_B
          (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
            (aux_rem_resolved_meshes_relabel (N + j) om)) (N + j) 1 It.k
          (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
          (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < l.val)) (dep l).val)) ≤
        U (N + j) om := by
    intro n g dep σ
    rw [hsum n g dep σ]
    exact (hUlub (N + j)).1 ⟨n, (g, (dep, σ)), rfl⟩
  have hV := aux_neumann_ht_meshes_Vbound M j om (N + j) etas (W om) (V0 (N + j) om) (hW1 om)
    (hWpt om) (fun kk hkk z hz => (hVlub (N + j)).2 kk hkk z hz)
  exact aux_rem_resolved_meshes_energy_app d hd 10 Rj t0 eta etas (by norm_num) hRjpos hRjlt
    hRjmem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt 1 le_rfl Cstep c hCstep hc.le M
    (calib3_HT d j) om (N + j)
    (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u Kf
    (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
      (aux_rem_resolved_meshes_relabel (N + j) om)) It.k
    (hone M E Poinc Ext Sreg It hdet hδ1 om (N + j) N j rfl f hf Kf hKf hfb hf0 u hu)
    (U (N + j) om) hUcore (W om * (1 + V0 (N + j) om)) hV x hx r hr

end SubdiffusiveProcess.Paper
