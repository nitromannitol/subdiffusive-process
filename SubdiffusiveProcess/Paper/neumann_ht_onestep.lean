module

public import SubdiffusiveProcess.Paper.neumann_ht_finite_onestep
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.calib3_fedata
public import SubdiffusiveProcess.Paper.rem_resolved_meshes

@[expose] public section

/-! One-step residual for the top-block-removed coefficient `A^{HT_j}_{N+j}` on the unit Neumann
cube (`HT_j = -∑_{i<j} ω(-i)`), at every root of depth `k ≥ j + 7`.

On the unit cube `A^{HT_j}_{N+j}` is a constant multiple of the stationary coefficient `a_N` of the
`(N+j)`-relabelled field (`calib3_fedata`), i.e. the level of the stationary coefficient is `N`,
strictly below the top scale `N + j`.  Roots of depth `k ≥ j+1` satisfy the level relation
`N + j - k + 1 ≤ N` of `aux_neumann_ht_finite_onestep`; the cap `Rstar_j = 3^{-(j+7)}/2` of the
mesh assembly forces `k ≥ j + 7`.  The root reference of the folded estimate is exactly the literal
reference `b_{k-1}` of the coefficient `A^{HT_j}_{N+j}`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- The partial layer sums, read top-down: `S(m) = ∑_{i<m} ω(-i)`; a window of the relabelled sum
is a difference of two of them. -/
theorem aux_neumann_ht_window_sum {d : ℕ} (omega : BilateralField d) (Np n : ℕ) (hn : n ≤ Np)
    (x : SpatialCoordinates d) :
    (∑ i ∈ Finset.range (n + 1), (omega ((i : ℤ) - (Np : ℤ))) x) =
      (∑ i ∈ Finset.range (Np + 1), (omega (-(i : ℤ))) x) -
        ∑ i ∈ Finset.range (Np - n), (omega (-(i : ℤ))) x := by
  have hsplit : (∑ i ∈ Finset.range (Np + 1), (omega (-(i : ℤ))) x) =
      (∑ i ∈ Finset.range (Np - n), (omega (-(i : ℤ))) x) +
        ∑ i ∈ Finset.range (n + 1), (omega (-((Np - n + i : ℕ) : ℤ))) x := by
    rw [show Np + 1 = (Np - n) + (n + 1) by omega, Finset.sum_range_add]
  rw [hsplit, add_sub_cancel_left]
  rw [← Finset.sum_range_reflect (fun i : ℕ => (omega (-((Np - n + i : ℕ) : ℤ))) x) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  congr 2
  rw [show n + 1 - 1 - i = n - i by omega]
  push_cast [Nat.cast_sub hi', Nat.cast_sub hn]
  ring

/-- **Frame identity on the unit cube** (`calib3_fedata`, in the unit-cube/`zpow` spelling of the
mesh files): a.e. on `Q`, `A^{HT_j}_{N+j} = c_F · a_N(3^{N+j}·)` of the `(N+j)`-relabelled field. -/
theorem aux_neumann_ht_window {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    (Sreg : in_6_16 d M) (omega : BilateralField d) (j N : ℕ) :
    ∃ cF : ℝ, 0 < cF ∧ cF = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∧
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
          cF * (Sreg.cutoffOn N (aux_rem_resolved_meshes_relabel (N + j) omega)
            ((3 : ℝ) ^ ((N + j : ℕ) : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ ((N + j : ℕ) : ℤ)) (by positivity)).val
            (((3 : ℝ) ^ ((N + j : ℕ) : ℤ)) • y) := by
  refine ⟨(SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ *
      Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)),
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + j))) (Real.exp_pos _), rfl, ?_⟩
  have h : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
        ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ *
          Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))) *
          (Sreg.cutoffOn N (aux_aux_macro_energy_recurrence_relabel (N + j) omega)
            ((3 : ℝ) ^ (N + j) • (fun _ : Fin d => (1 / 2 : ℝ))) (3 ^ (N + j))
            (by positivity)).val ((3 : ℝ) ^ (N + j) • y) :=
    aux_calib3_fedata_identity Sreg omega j N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
      (by positivity)
  filter_upwards [h] with y hy
  rw [hy]
  congr 1

/-- **The root reference is the literal reference.**  For the roots of depth `k ≥ j+1` (so the root
scale `N + j - k + 1` lies below the level `N` of the stationary coefficient) the transfer
constant times the reference of `in_iteration` is the ball average `b_{k-1}` of
`s^{HT_j}_{N+j}(k-1, ·)`. -/
theorem aux_neumann_ht_ref_avg {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {E : in_J d} {Sreg : in_6_16 d M} (It : in_iteration d M E Sreg)
    (omega : BilateralField d) (j N k : ℕ) (hjk : j + 1 ≤ k) (hkN : k ≤ N + j)
    (hm2 : 2 ≤ N + j - k + 1) (c : SpatialCoordinates d) :
    ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))⁻¹ *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))) *
      It.ref N (N + j - k + 1 - 2) ((3 : ℝ) ^ ((N + j : ℕ) : ℤ) • c)
        (aux_rem_resolved_meshes_relabel (N + j) omega) =
      aux_rem_resolved_meshes_bref M (calib3_HT d j) omega (N + j) (k - 1) c := by
  have hk1 : 1 ≤ k := by omega
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((N + j : ℕ) : ℤ) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (N + j - k + 1) := by positivity
  have hmN : N + j - k + 1 ≤ N := by omega
  rw [It.ref_eq, show N + j - k + 1 - 2 + 2 = N + j - k + 1 by omega,
    Sreg.refAvg_eq _ _ _ _ hR, min_eq_left hmN,
    min_eq_left (show ((N + j - k + 1 : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN),
    aux_rem_resolved_meshes_cube_eq_smul_ball (N + j) k hk1 hkN c hR,
    aux_rem_resolved_meshes_setIntegral_smul _ measurableSet_ball h3,
    aux_rem_resolved_meshes_volume_smul _ h3]
  unfold aux_rem_resolved_meshes_bref
  have hvol : 0 < volume.real (Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)) := by
    have : volume (Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)) ≠ 0 :=
      (Metric.measure_ball_pos volume _ (by positivity)).ne'
    exact ENNReal.toReal_pos this measure_ball_lt_top.ne
  have h3d : (0 : ℝ) < ((3 : ℝ) ^ ((N + j : ℕ) : ℤ)) ^ d := pow_pos h3 d
  have hcast : (((k - 1 : ℕ) : ℤ)) = ((k : ℤ) - 1) := by omega
  refine aux_rem_resolved_meshes_avg_algebra _ _ _ _ _ h3d.ne' hvol.ne' ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hrel : ∀ i : ℕ, (aux_rem_resolved_meshes_relabel (N + j) omega (i : ℤ))
      (((3 : ℝ) ^ ((N + j : ℕ) : ℤ)) • x) = (omega ((i : ℤ) - ((N + j : ℕ) : ℤ))) x :=
    fun i => aux_rem_resolved_meshes_relabel_apply (N + j) omega (i : ℤ) x
  simp only [hrel]
  have hA := aux_neumann_ht_window_sum omega (N + j) N (by omega) x
  have hB := aux_neumann_ht_window_sum omega (N + j) (N + j - k + 1) (by omega) x
  rw [hA, hB, show N + j - N = j by omega, show N + j - (N + j - k + 1) = k - 1 by omega]
  have hApos : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) ≠ 0 :=
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + j)).ne'
  have hNk : N + j - (k - 1) = N + j - k + 1 := by omega
  rw [hNk]
  have hHT : (calib3_HT d j omega) x = -∑ i ∈ Finset.range j, (omega (-(i : ℤ))) x := by
    simp [calib3_HT]
  rw [hHT]
  have e1 : ((N : ℝ) - ((N + j - k + 1 : ℕ) : ℝ)) = ((k - 1 : ℕ) : ℝ) - (j : ℝ) := by
    push_cast [Nat.cast_sub (show k ≤ N + j by omega), Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  rw [e1]
  field_simp
  rw [show ∀ (a b m : ℝ), Real.exp a * m * Real.exp b = m * Real.exp (a + b) from
    fun a b m => by rw [Real.exp_add]; ring]
  congr 2
  ring


/-- **Good branch for the top-block-removed coefficient.**  The level-`Lam` finite-cutoff residual
(`aux_neumann_ht_finite_onestep`) applied to `A^{HT_j}_N`, `N = Lam + j`, `c_F · a_{Lam}(3^N ·)`,
for roots of depth `k ≥ j + 1`; the root reference `c_F · ref` is exactly the literal reference
`b_{k-1}`. -/
theorem aux_neumann_ht_good_finite (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_neumann_ht_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
    (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (hdet : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hδ : M.delta ≤ delta1)
    (omega : BilateralField d) (N Lam j : ℕ) (hN : N = Lam + j)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (n k : ℕ) (hjk : j + 1 ≤ k) (hkN : k ≤ N)
    (hR : (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar)
    (h8 : 8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2)
    (hI : ∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i))
    (hgood : n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1) :
    aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (calib3_HT d j) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
      7 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
        (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M (calib3_HT d j) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
  have hm2 : 2 ≤ N - k + 1 := by
    have := It.prefix_lower ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
      (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    rw [It.k_eq] at this
    omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨cF, hcF, hcFdef, hwin⟩ : ∃ cF : ℝ, 0 < cF ∧
      cF = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∧
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (calib3_HT d j) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
          cF * (Sreg.cutoffOn Lam (aux_rem_resolved_meshes_relabel N omega)
            ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) := by
    subst hN
    exact aux_neumann_ht_window Sreg omega j Lam
  have hlev : N - k + 1 ≤ Lam := by omega
  have hF := hfin M E Poinc Ext Sreg It hdet hδ omega N Lam cF hcF
    (cutoffPositiveCoefficient M (calib3_HT d j) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) hwin f hf Kf hKf hfb hf0 u hu y hy I n k
    hk1 hkN hlev hR h8 hI hgood
  have href : cF * It.ref Lam (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N omega) =
      aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I) := by
    subst hN
    rw [hcFdef]
    exact aux_neumann_ht_ref_avg It omega j Lam k hjk hkN hm2 _
  rw [href] at hF
  have hσ : 0 ≤ (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
    positivity
  have hK : 0 ≤ C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 :=
    mul_nonneg hC1 hσ
  have hbv : 0 < aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_two_mesh_energy_bound_bpos M (calib3_HT d j) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I)
  have hE3 : 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (calib3_HT d j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) := by
    have heq := aux_rem_resolved_meshes_energy_local
      (cutoffPositiveCoefficient M (calib3_HT d j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      measurableSet_ball
    have hn := localGradientEnergy_nonneg
      (cutoffPositiveCoefficient M (calib3_HT d j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      (s := Metric.ball (aux_rem_resolved_meshes_center y I)
        (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) measurableSet_ball
      (sobolevGradient (u : SobolevData (unitNeumannCube d)))
    calc
      0 ≤ localGradientEnergy
          (cutoffPositiveCoefficient M (calib3_HT d j) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
          (s := Metric.ball (aux_rem_resolved_meshes_center y I)
            (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) measurableSet_ball
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) := hn
      _ = _ := by exact heq.symm
  have hZ : 0 ≤ Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hB : 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (calib3_HT d j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
      (aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I))⁻¹ *
        (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) :=
    add_nonneg hE3 (mul_nonneg (inv_pos.mpr hbv).le hZ)
  refine hF.trans ?_
  have e : C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
      (aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (calib3_HT d j) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
          (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
          ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
      C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
        (aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (calib3_HT d j) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
          (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
  rw [e]
  nlinarith [mul_nonneg hK hB]

def aux_neumann_ht_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar t0 : ℝ) (Kt Cstep c delta1 : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
    (_ : in_poincare d hd E) (_ : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (_ : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
    M.delta ≤ delta1 →
    ∀ (omega : BilateralField d) (N Lam j : ℕ), N = Lam + j →
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ (3 : ℝ) ^ (-((j + 7 : ℕ) : ℤ)) / 2 →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (calib3_HT d j) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
        Cstep * Real.exp (c * (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
            (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
            (aux_rem_resolved_meshes_relabel N omega) : ℝ)) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (calib3_HT d j) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (calib3_HT d j) omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))

/-- **One step for the top-block-removed coefficient.**  The bad-prefix branch is paid by the
allowance, the good branch is `aux_neumann_ht_good_finite`; roots of depth `k ≥ j + 7`. -/
theorem aux_neumann_ht_onestep_of_finite (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (ht0 : 0 < t0) (Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : ∀ Rstar : ℝ, aux_neumann_ht_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1) :
    aux_neumann_ht_onestep d hd Lstar t0 Kt (max 1 (7 * C1))
      (t0 * Real.log 3 + 1) delta1 := by
  intro M E Poinc Ext Sreg It hdet hδ omega N Lam j hN f hf Kf hKf hfb hf0 u hu y hy I s k
    hs hs1 hs0 hk h8 hR hI
  set H : BilateralField d → C(SpatialCoordinates d, ℝ) := calib3_HT d j
    with hHdef
  obtain ⟨q0, rfl⟩ := hs
  dsimp only at hs1 hs0 h8 ⊢
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ t0 * Real.log 3 + 1 := by positivity
  -- the target depth
  have hjN : -(N : ℤ) ≤ q0 := by
    have h1 : (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ q0 := by linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h1
  have hjk7 : j + 7 ≤ k := by
    have h1 : (3 : ℝ) ^ (-(k : ℤ)) ≤ (3 : ℝ) ^ (-((j + 7 : ℕ) : ℤ)) := by linarith
    have h2 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h1
    push_cast at h2
    omega
  have hk1 : 1 ≤ k := by omega
  set n : ℕ := (q0 + (N : ℤ)).toNat with hn_def
  have hn : ((n : ℕ) : ℤ) = q0 + (N : ℤ) := Int.toNat_of_nonneg (by omega)
  have hjn : q0 = (n : ℤ) - (N : ℤ) := by omega
  set pl := It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    with hpl
  have hmono : ∀ {A A' : Set (SpatialCoordinates d)}, A ⊆ A' →
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A' :=
    fun h => aux_rem_resolved_strata_energy_mono
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      ⟨u.1, u.2.1⟩ h
  have hnn : ∀ A : Set (SpatialCoordinates d), 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A :=
    fun A => aux_rem_resolved_strata_energy_nonneg
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) ⟨u.1, u.2.1⟩ A
  have hRk : 0 < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_two_mesh_energy_bound_bpos M H omega N (k - 1) (aux_rem_resolved_meshes_center y I)
  have hsrc : 0 ≤ (aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hLR : aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ q0 / 2)) ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) :=
    hmono (Metric.ball_subset_ball (by nlinarith))
  have hσ : 0 ≤ (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
  have hexp1 : 1 ≤ Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc0 (Nat.cast_nonneg _))
  by_cases hgood : n + pl ≤ N - k + 1
  · -- good branch
    have hG := aux_neumann_ht_good_finite d hd Lstar ((3 : ℝ) ^ (-((j + 7 : ℕ) : ℤ)) / 2) t0 Kt C1
      delta1 hC1 (hfin _) M E Poinc Ext Sreg It hdet hδ omega N Lam j hN f hf Kf hKf hfb hf0 u hu y
      hy I n k (by omega) hk hR (by rw [← hjn]; exact h8) hI hgood
    rw [← hjn] at hG
    have h3L := hmono (Metric.ball_subset_ball (x := aux_rem_resolved_meshes_center y I)
      (show 3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) by nlinarith))
    refine hG.trans ?_
    have hC : 7 * C1 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) := by
      have := le_max_right 1 (7 * C1)
      have h1 : 0 ≤ max 1 (7 * C1) := le_trans zero_le_one (le_max_left _ _)
      nlinarith
    have hB : 0 ≤ aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
      have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      positivity
    calc 7 * (C1 * (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
        = (7 * C1) * (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
      _ ≤ (max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ))) *
            (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
          gcongr
      _ ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (1 - 1 + (k - 1))
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          rw [show 1 - 1 + (k - 1) = k - 1 by omega]
          have hK0 : 0 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
              (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
          apply mul_le_mul_of_nonneg_left _ hK0
          have e : (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
            (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by ring
          rw [e]
          linarith
      _ = _ := by rw [show 1 - 1 + (k - 1) = k - 1 by omega]
  · -- bad branch
    have hjk : 0 ≤ q0 + (k : ℤ) + (pl : ℤ) := by
      push Not at hgood
      have : (N : ℤ) - k + 1 < (n : ℤ) + pl := by
        have : N - k + 1 < n + pl := hgood
        omega
      omega
    have hfac := aux_rem_resolved_meshes_bad_factor t0 (t0 * Real.log 3 + 1) ht0 (by linarith) q0 k
      pl hjk
    have hE0 := hnn (Metric.ball (aux_rem_resolved_meshes_center y I)
      (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
    calc aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ q0 / 2))
        ≤ 1 * (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by linarith
      _ ≤ (max 1 (7 * C1) * (Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ q0 / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0)) *
          (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have := le_max_left 1 (7 * C1)
          nlinarith
      _ = _ := by ring

/-- **One step for the top-block-removed coefficient, constants before the model and `j`.** -/
theorem neumann_ht_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ)) :
    ∃ Kt Cstep c delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 1 ≤ Cstep ∧ 0 < c ∧
        0 < delta1 ∧ aux_neumann_ht_onestep d hd Lstar t0 Kt Cstep c delta1 := by
  obtain ⟨Kt, C1, delta1, hKt, hC1, hdelta1, hfin⟩ :=
    neumann_ht_finite_onestep d hd Lstar t0 hLstar ht0_low ht0_high
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t0 := by linarith
  refine ⟨Kt, max 1 (7 * C1), t0 * Real.log 3 + 1, delta1, hKt, le_max_left _ _, ?_, hdelta1,
    aux_neumann_ht_onestep_of_finite d hd Lstar t0 hLstar ht0 Kt C1 delta1 hC1 hfin⟩
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  positivity

end SubdiffusiveProcess.Paper
