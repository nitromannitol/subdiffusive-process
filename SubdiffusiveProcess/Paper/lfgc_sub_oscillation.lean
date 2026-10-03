module

public import SubdiffusiveProcess.Paper.lfgc_potential_lipschitz

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology
noncomputable section
namespace Paper

/-- A uniform cutoff score bound on padded-root descendants gives potential oscillation control. -/
theorem lfgc_sub_oscillation {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d) (G0 : ℝ)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (x y : SpatialCoordinates d) (hx : ∀ i, |x i - qcenter i| ≤ qside)
    (hy : ∀ i, |y i - qcenter i| ≤ qside) :
    |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤
      (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) := by
  refine lfgc_potential_lipschitz H omega N eta hEta hIR G0 x y ?_
  intro Z hZ J
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hZ
  set z' : SpatialCoordinates d := a • x + b • y with hz'
  have hZz : a • (((3 : ℝ) ^ N) • x) + b • (((3 : ℝ) ^ N) • y) = ((3 : ℝ) ^ N) • z' := by
    rw [hz', smul_add, smul_comm a, smul_comm b]
  rw [hZz]
  have hz'q : ∀ i, |z' i - qcenter i| ≤ 3 * qside / 2 := by
    intro i
    have hzi : z' i - qcenter i = a * (x i - qcenter i) + b * (y i - qcenter i) := by
      simp only [hz', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : qcenter i = a * qcenter i + b * qcenter i := by rw [← add_mul, hab, one_mul]
      linarith only [this]
    rw [hzi]
    calc |a * (x i - qcenter i) + b * (y i - qcenter i)|
        ≤ |a * (x i - qcenter i)| + |b * (y i - qcenter i)| := abs_add_le _ _
      _ = a * |x i - qcenter i| + b * |y i - qcenter i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * qside + b * qside :=
          add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = qside := by rw [← add_mul, hab, one_mul]
      _ ≤ 3 * qside / 2 := by linarith only [hqpos]
  obtain ⟨pword, hpw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter (3 * qside)
    (by positivity) z' hz'q (N - k + 1)
  have hside := (aux_in_deterministic_onestep_side_pad k N hkN qside hqside).1
  set c := descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword with hc
  have hmem : ((3 : ℝ) ^ N) • z' ∈ Metric.closedBall (((3 : ℝ) ^ N) • c) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
    intro i
    rw [Real.dist_eq]
    have h1 := (hpw i).1
    rw [hside] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
    calc (3 : ℝ) ^ N * |z' i - c i| ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left h1 hN.le
      _ = 1 / 2 := by field_simp
  obtain ⟨hfin, hle⟩ := hpad pword
  exact (aux_in_deterministic_onestep_gradsum_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt hPS
    _ hfin J _ hmem).trans hle

end Paper
