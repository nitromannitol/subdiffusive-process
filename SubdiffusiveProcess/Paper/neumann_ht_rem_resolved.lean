module

public import SubdiffusiveProcess.Paper.neumann_ht_meshes
public import SubdiffusiveProcess.Paper.calib3_envelope
public import SubdiffusiveProcess.Paper.rem_resolved
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic

@[expose] public section

/-! Resolved-scale energy growth for the top-block-removed coefficient `A^{HT_j}_{N+j}` on the unit
Neumann cube: for a mean-zero bounded source the local energy on `B_r(x) ∩ Q`, `r ≤ 1`, is at most
`K_N (E(Q) + ‖f‖_∞²) r^t` with a random constant of every prescribed moment, uniformly in `N`.  The
smallness threshold is chosen before `j`; the mesh (`neumann_ht_meshes`) and the envelope
(`calib3_envelope`) carry `j` only in their prefactors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem aux_neumann_ht_rem_resolved_exponents (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (k : ℕ)
    (ps : Fin k → ℝ) (ht_low : (d : ℝ) - 1 < t) (ht_high : t < (d : ℝ))
    (_hps : ∀ i : Fin k, 1 ≤ ps i) :
    ∃ t1 t0 pmax : ℝ, t < t1 ∧ t1 < (d : ℝ) ∧ (d : ℝ) - 1 < t0 ∧ t0 < (d : ℝ) ∧
      0 < t0 - t1 ∧ t0 - t1 < t0 - ((d : ℝ) - 1) ∧ 0 < ((d : ℝ) + 2 - t0) / 2 ∧
      ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 ∧ 1 ≤ pmax ∧ (∀ i : Fin k, ps i ≤ pmax) ∧
      1 ≤ 2 * pmax * max 1 t ∧ pmax ≤ 2 * pmax * max 1 t ∧
      1 ≤ 2 * (2 * pmax * max 1 t) ∧
      2 * (2 * pmax * max 1 t) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) ∧
      (d : ℝ) < max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) ∧
      0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ∧
      0 < (d : ℝ) - t := by
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht_nn : 0 ≤ t := by linarith
  obtain ⟨t1, ht1⟩ : ∃ t1 : ℝ, t1 = t + ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, t0 = t + 2 * ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1]; linarith
  have ht0_low : (d : ℝ) - 1 < t0 := by rw [ht0]; linarith
  have ht0_high : t0 < (d : ℝ) := by rw [ht0]; linarith
  have heta_pos : 0 < t0 - t1 := by rw [ht0, ht1]; linarith
  have heta_lt : t0 - t1 < t0 - ((d : ℝ) - 1) := by rw [ht0, ht1]; linarith
  have hetas_pos : 0 < ((d : ℝ) + 2 - t0) / 2 := by linarith
  have hetas_lt : ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 := by linarith
  obtain ⟨pmax, hpmax_def⟩ : ∃ pmax : ℝ, pmax = 1 + ∑ i : Fin k, |ps i| := ⟨_, rfl⟩
  have hsum_nn : 0 ≤ ∑ i : Fin k, |ps i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hpmax : 1 ≤ pmax := by rw [hpmax_def]; linarith
  have hps_le : ∀ i : Fin k, ps i ≤ pmax := by
    intro i
    have h1 : ps i ≤ |ps i| := le_abs_self _
    have h2 : |ps i| ≤ ∑ j : Fin k, |ps j| :=
      Finset.single_le_sum (f := fun j => |ps j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hpmax_def]; linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hq1 : 1 ≤ 2 * pmax * max 1 t := by nlinarith
  have hpq : pmax ≤ 2 * pmax * max 1 t := by nlinarith
  have hqmesh_p : 1 ≤ 2 * (2 * pmax * max 1 t) := by linarith
  have hqmesh_q : 2 * (2 * pmax * max 1 t) ≤
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) := le_max_left _ _
  have hqmesh_eta : (d : ℝ) <
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
    have h1 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) = (d : ℝ) + 1 := by
      field_simp
    have h2 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heta_pos.le
    linarith
  have hrmax : 0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  exact ⟨t1, t0, pmax, htt1, ht1d, ht0_low, ht0_high, heta_pos, heta_lt, hetas_pos, hetas_lt,
    hpmax, hps_le, hq1, hpq, hqmesh_p, hqmesh_q, hqmesh_eta, hrmax, hdt⟩

theorem aux_neumann_ht_rem_resolved_micro_range (d : ℕ) (t : ℝ) (ht_high : t < (d : ℝ))
    (hdt : 0 < (d : ℝ) - t) :
    (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) ∧
      t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      positivity
    linarith
  refine ⟨hp1, ?_⟩
  have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
  have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
    rw [div_lt_iff₀ hp1pos]
    have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
      field_simp
    nlinarith
  linarith

/-- **The random constant and its moments.**  The three-term constant of the resolved-scale estimate
at level `N`, from the moments of the envelope and of the mesh statistic `W`, with the microscopic
absorption of `rem_resolved_microscopic` (the rate is below `min (t1 - t, d + 2 - t, d - t) log 3`). -/
theorem aux_neumann_ht_rem_resolved_K (d : ℕ) (hd : 2 ≤ d) (t t1 : ℝ) (ht : (d : ℝ) - 1 < t)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (ps : Fin k → ℝ) (pmax : ℝ) (hpmax : 1 ≤ pmax) (hps_le : ∀ i : Fin k, ps i ≤ pmax)
    (hpq : pmax ≤ 2 * pmax * max 1 t) (ht_nn : 0 ≤ t)
    (Cm Cmic Cp CD CE aRate : ℝ) (hCm : 0 ≤ Cm) (hCmic : 0 < Cmic) (hCp : 0 ≤ Cp)
    (hCD : 0 ≤ CD) (hCE : 0 ≤ CE) (haR0 : 0 ≤ aRate)
    (haR : aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3)
    (De Mx W : ℕ → Ω → ℝ) (hDMx0 : ∀ N om, 0 ≤ De N om ∧ 0 ≤ Mx N om)
    (hW0 : ∀ N om, 0 ≤ W N om)
    (hDL : ∀ N, MemLp (De N) (ENNReal.ofReal (2 * pmax * max 1 t)) P)
    (hML : ∀ N, MemLp (Mx N) (ENNReal.ofReal (2 * pmax * max 1 t)) P)
    (hWL : ∀ N, MemLp (W N) (ENNReal.ofReal (2 * pmax * max 1 t)) P)
    (hDb : ∀ N, eLpNorm (De N) (ENNReal.ofReal (2 * pmax * max 1 t)) P ≤
      ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ))))
    (hMb : ∀ N, eLpNorm (Mx N) (ENNReal.ofReal (2 * pmax * max 1 t)) P ≤
      ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ))))
    (hWb : ∀ N, eLpNorm (W N) (ENNReal.ofReal (2 * pmax * max 1 t)) P ≤
      ENNReal.ofReal (Cp * (1 + Cp))) :
    ∃ Cb : ℝ, ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * W N om +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * W N om) +
        (Cmic * 2 ^ t) * ((2 * Mx N om) * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) P ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * W N om +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * W N om) +
        (Cmic * 2 ^ t) * ((2 * Mx N om) * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal Cb := by
  have hSb : ∀ N' : ℕ,
      eLpNorm (fun om => 2 * Mx N' om + 2 * Mx N' om) (ENNReal.ofReal (2 * pmax * max 1 t)) P ≤
      ENNReal.ofReal (4 * CE * Real.exp (aRate * (N' : ℝ))) := by
    intro N'
    have h : (fun om => 2 * Mx N' om + 2 * Mx N' om) = fun om => 4 * Mx N' om := by
      funext om; ring
    rw [h, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ 4 (by norm_num)]
    calc ENNReal.ofReal 4 * eLpNorm (Mx N') (ENNReal.ofReal (2 * pmax * max 1 t)) P
        ≤ ENNReal.ofReal 4 * ENNReal.ofReal (CE * Real.exp (aRate * (N' : ℝ))) := by
          gcongr; exact hMb N'
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have hstat := aux_rem_resolved_microscopic_statistical_conjunct d hd t t1 ht
  obtain ⟨B, hB0, hBN⟩ := hstat Ω P pmax hpmax De (fun N' om => 2 * Mx N' om)
    (fun N' om => 2 * Mx N' om) W CD (4 * CE) (Cp * (1 + Cp)) aRate hCD (by positivity)
    (by positivity) haR0 haR
    (fun N' om => ⟨(hDMx0 N' om).1, by linarith [(hDMx0 N' om).2],
      by linarith [(hDMx0 N' om).2], hW0 N' om⟩)
    (fun N' => ⟨hDL N', (hML N').const_mul 2, (hML N').const_mul 2, hWL N'⟩) hDb hSb hWb
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  refine ⟨(Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
      (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B, ?_⟩
  intro i N'
  have hBNN := hBN N'
  beta_reduce at hBNN
  have hWm := hWL N'
  have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp P pmax t hpmax ht_nn (De N')
    (fun om => (hDMx0 N' om).1) (hDL N')).aestronglyMeasurable
  have hT1m : AEStronglyMeasurable (fun om =>
      (1 + De N' om) ^ t * ((3 : ℝ) ^ (-(N' : ℝ))) ^ (t1 - t) * W N' om) P :=
    (hDt.mul aestronglyMeasurable_const).mul hWm.aestronglyMeasurable
  have hT2m : AEStronglyMeasurable (fun om =>
      (2 * Mx N' om) * ((3 : ℝ) ^ (-(N' : ℝ))) ^ ((d : ℝ) + 2 - t)) P :=
    ((hML N').aestronglyMeasurable.const_mul 2).mul aestronglyMeasurable_const
  have hWb' : eLpNorm (W N') (ENNReal.ofReal pmax) P ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans (hWb N')
  exact aux_rem_resolved_three_term_moment P pmax _ _ _
    (Cp * (1 + Cp)) B hpmax hA1 hA2 hA3 (by positivity) hB0 _ _ _ hWm.aestronglyMeasurable hT1m hT2m hWb'
    hBNN.1 hBNN.2.1 (ps i) (hps_le i)

/-- **The model-level assembly** of the resolved-scale energy growth for the top-block-removed
coefficient: the mesh energy estimate (`neumann_ht_meshes`), the envelope (`calib3_envelope`) and the
matched-range microscopic estimate combine, for a fixed sample law, into one random constant. -/
theorem aux_neumann_ht_rem_resolved_model (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (k : ℕ) (ps : Fin k → ℝ)
    (t t1 t0 pmax Cm Cmic Cp CD CE aRate : ℝ)
    (ht_low : (d : ℝ) - 1 < t) (htt1 : t < t1) (ht_nn : 0 ≤ t) (hpmax : 1 ≤ pmax)
    (hps_le : ∀ i : Fin k, ps i ≤ pmax) (hq1 : 1 ≤ 2 * pmax * max 1 t)
    (hpq : pmax ≤ 2 * pmax * max 1 t)
    (hCm : 0 < Cm) (hCmic : 0 < Cmic) (hCp : 0 < Cp) (hCD : 0 ≤ CD) (hCE : 0 ≤ CE)
    (haR0 : 0 ≤ aRate)
    (haR : aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3)
    (U V : ℕ → BilateralField d → ℝ)
    (hU0 : ∀ N omega, 0 ≤ U N omega) (hV0 : ∀ N omega, 0 ≤ V N omega)
    (hULp : ∀ N, MemLp (U N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure)
    (hVLp : ∀ N, MemLp (V N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure)
    (hUb : ∀ N, eLpNorm (U N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp)
    (hVb : ∀ N, eLpNorm (V N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp)
    (hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
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
            Cm * U N omega * r ^ (t0 - (t0 - t1)) *
              (aux_rem_resolved_meshes_energy
                (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
                (unitNeumannCube d : Set (SpatialCoordinates d)) +
                V N omega * Kf ^ 2))
    (De Mx : ℕ → BilateralField d → ℝ)
    (hDMx0 : ∀ N om, 0 ≤ De N om ∧ 0 ≤ Mx N om)
    (heae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
      (∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M (calib3_HT d j) om N x ∧
          cutoffCoefficient M (calib3_HT d j) om N x ≤ Mx N om) ∧
      (∀ x y, x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) →
        y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M (calib3_HT d j) om N x) -
            Real.log (cutoffCoefficient M (calib3_HT d j) om N y)| ≤
          De N om * (3 : ℝ) ^ N * dist x y))
    (hDMLp : ∀ N, MemLp (De N) (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ∧
      MemLp (Mx N) (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure)
    (hDb : ∀ N, eLpNorm (De N) (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ))))
    (hMb : ∀ N, eLpNorm (Mx N) (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ))))
    (hmicL : ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ Kmac : ℝ, 0 ≤ Kmac →
        localGradientEnergy a (aux_rem_resolved_cube_meas x (Cmic * eps))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ Kmac * eps ^ t1 →
        ∀ r : ℝ, 0 < r → r ≤ eps →
          localGradientEnergy a (aux_rem_resolved_cube_meas x r)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            Cmic * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
              mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * r ^ t) :
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ N : ℕ,
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
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy
              (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            K N omega *
              (sobolevCoefficientForm
                (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                (u : SobolevData (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d)) +
                Kf ^ 2) * r ^ t := by
  have hW : ∀ N : ℕ,
      MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp.le
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  obtain ⟨Cb, hCb⟩ := aux_neumann_ht_rem_resolved_K d hd t t1 ht_low (chaosSampleLaw M).toMeasure
    k ps pmax hpmax hps_le hpq ht_nn Cm Cmic Cp CD CE aRate hCm.le
    hCmic hCp.le hCD hCE haR0 haR De Mx (fun N' om => U (N' - j) om * (1 + V (N' - j) om))
    hDMx0 (fun N' om => mul_nonneg (hU0 (N' - j) om) (by linarith [hV0 (N' - j) om]))
    (fun N' => (hDMLp N').1) (fun N' => (hDMLp N').2) (fun N' => (hW (N' - j)).1) hDb hMb
    (fun N' => (hW (N' - j)).2)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℕ → BilateralField d → ℝ, K' = fun N' om =>
      (Cm * 2 ^ t1) * (U (N' - j) om * (1 + V (N' - j) om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N' om) ^ t * ((3 : ℝ) ^ (-(N' : ℝ))) ^ (t1 - t) *
            (U (N' - j) om * (1 + V (N' - j) om))) +
        (Cmic * 2 ^ t) * ((2 * Mx N' om) * ((3 : ℝ) ^ (-(N' : ℝ))) ^ ((d : ℝ) + 2 - t))
      := ⟨_, rfl⟩
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  have hK'0 : ∀ N' om, 0 ≤ K' N' om := by
    intro N' om
    rw [hK'def]
    have h1 : 0 ≤ U (N' - j) om * (1 + V (N' - j) om) :=
      mul_nonneg (hU0 (N' - j) om) (by linarith [hV0 (N' - j) om])
    have h2 : 0 ≤ (1 + De N' om) ^ t := (Real.rpow_pos_of_pos (by linarith [(hDMx0 N' om).1]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N' : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N' : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 : 0 ≤ 2 * Mx N' om := by linarith [(hDMx0 N' om).2]
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  have hmom : ∀ (i : Fin k) (N' : ℕ),
      MemLp (K' N') (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (K' N') (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cb := by
    intro i N'
    rw [hK'def]
    exact hCb i N'
  refine ⟨fun N om => K' (N + j) om,
    fun _ => Cb,
    fun N om => hK'0 (N + j) om, fun i N => (hmom i (N + j)).1, fun i N => (hmom i (N + j)).2, ?_⟩
  filter_upwards [hae, heae] with om hω1 hω2
  intro N f hf Kf hKf hfb hmean u hsol x hx r hr hr1
  have hN : N + j - j = N := Nat.add_sub_cancel N j
  have hnormS : ∀ N' om, ‖Mx N' om + ((Mx N' om)⁻¹)⁻¹‖ = 2 * Mx N' om := by
    intro N' om
    rw [inv_inv, ← two_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hDMx0 N' om).2])]
  obtain ⟨hMxpos, hbnd, hlip⟩ := hω2 (N + j)
  have hfirst := aux_rem_resolved_sample d M (calib3_HT d j) om (N + j) t t1 t0 Cm Cmic
    (U N om) (V N om) (De (N + j) om) (Mx (N + j) om)⁻¹ (Mx (N + j) om)
    (le_of_lt htt1) hCm.le hCmic (hU0 N om) (hV0 N om) (hDMx0 (N + j) om).1 (inv_pos.2 hMxpos)
    (fun y hy => ⟨(hbnd y hy).1, (hbnd y hy).2⟩) hlip
    (hmicL ((3 : ℝ) ^ (-((N + j : ℕ) : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (Nat.cast_nonneg _))))
    (hω1 N)
  have h := hfirst f hf Kf hKf hfb hmean u hsol x hx r hr hr1
  rw [hnormS] at h
  rw [hK'def]
  simp only [hN]
  exact h

theorem neumann_ht_rem_resolved (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht_low : (d : ℝ) - 1 < t) (ht_high : t < (d : ℝ))
    (hps : ∀ i : Fin k, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N omega, 0 ≤ K N omega) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ N : ℕ,
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
              ∀ r : ℝ, 0 < r → r ≤ 1 →
                localGradientEnergy
                  (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                  (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                K N omega *
                  (sobolevCoefficientForm
                    (cutoffPositiveCoefficient M (calib3_HT d j) omega (N + j)
                      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (u : SobolevData (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d)) +
                    Kf ^ 2) * r ^ t := by
  obtain ⟨t1, t0, pmax, htt1, ht1d, ht0_low, ht0_high, heta_pos, heta_lt, hetas_pos, hetas_lt,
    hpmax, hps_le, hq1, hpq, hqmesh_p, hqmesh_q, hqmesh_eta, hrmax', hdt⟩ :=
    aux_neumann_ht_rem_resolved_exponents d hd t k ps ht_low ht_high hps
  have ht_nn : 0 ≤ t := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  -- the large-scale common package (top-block-removed mesh assembly)
  obtain ⟨delta0m, hdelta0m, hmesh⟩ := neumann_ht_meshes d hd t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)))
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  obtain ⟨hp1, htp⟩ := aux_neumann_ht_rem_resolved_micro_range d t ht_high hdt
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hstat := aux_rem_resolved_microscopic_statistical_conjunct d hd t t1 ht_low
  -- envelope of the top-block-removed coefficient on the closed unit cube
  obtain ⟨Cpe, Cde, cde, hCpe, hCde, hcde, hextM⟩ := calib3_envelope d hd (2 * pmax * max 1 t) hq1
  obtain ⟨rmax, hrmax_def⟩ : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  have hrmax : 0 < rmax := by rw [hrmax_def]; exact hrmax'
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  refine ⟨min (min delta0m (cde / (2 * (2 * pmax * max 1 t))))
    (min 1 (rmax / (2 * (Cde + Cpe)))), ?_, ?_⟩
  · refine lt_min (lt_min hdelta0m (div_pos hcde (by linarith))) (lt_min one_pos ?_)
    exact div_pos hrmax (by positivity)
  intro M _Rm Sreg _It hδ j hj
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * (2 * pmax * max 1 t)) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : M.delta ≤ rmax / (2 * (Cde + Cpe)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate := aux_rem_resolved_rate Cde Cpe rmax M.delta hCde hCpe hrmax hδpos hδ1 hδr
  rw [hrmax_def] at hrate
  -- instantiate the mesh and the envelope on the same sample law
  obtain ⟨Cm, Cp, hCm, hCp, U, V, hUm, hVm, hU0, hV0, hULp, hVLp, hUb, hVb, hae⟩ :=
    hmesh M E _P _X _Rm Sreg _It D hδm j hj
  obtain ⟨De, Mx, CD, CE, hCD, hCE, hDMx0, heae, hDMLp, hDb, hMb⟩ :=
    hextM M hδe j hj (fun _ => (1 / 2 : ℝ))
  exact aux_neumann_ht_rem_resolved_model d hd M j k ps t t1 t0 pmax Cm Cmic Cp CD CE
    (Cde * M.delta + Cpe * M.delta ^ 2) ht_low htt1 ht_nn hpmax hps_le hq1 hpq hCm hCmic hCp hCD
    hCE hrate.1 hrate.2 U V hU0 hV0 hULp hVLp hUb hVb hae De Mx hDMx0 heae hDMLp hDb hMb hmicL

end SubdiffusiveProcess.Paper
