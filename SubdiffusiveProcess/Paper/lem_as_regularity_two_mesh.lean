module

public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_onestep
public import SubdiffusiveProcess.Analysis.NativeMeshAllowance

@[expose] public section

/-! The deterministic two-mesh estimate consumes the actual finite allowances
and the lower-cutoff reference envelope. The resulting constant is independent
of the final cutoff when those two supplied bounds are independent of it.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The reference depth loss is bounded by the inverse physical radius. -/
theorem aux_lem_as_regularity_two_mesh_depth (k : ℕ) :
    (3 : ℝ) ^ (k - 1) ≤ ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one, zpow_neg, zpow_natCast, inv_div, div_inv_eq_mul]
  have hh : (3 : ℝ) ^ (k - 1) ≤ (3 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hpow : 0 ≤ (3 : ℝ) ^ k := by positivity
  linarith only [hh, hpow]

/-- Coordinate bounds identify the closed unit cube used by the reference bank. -/
theorem aux_lem_as_regularity_two_mesh_closed {d : ℕ} (z : SpatialCoordinates d)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    z ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
  change dist z (fun _ : Fin d => (1 / 2 : ℝ)) ≤ 1 / 2
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith only [(hz i).1, (hz i).2]

/-- The exact boundary mesh yields resolved Neumann energy decay from the two uniform banks. -/
theorem lem_as_regularity_two_mesh (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t eta : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ))
    (heta : 0 < eta) (heta1 : eta < t - ((d : ℝ) - 1)) :
    ∃ Cgeo : ℝ, 0 < Cgeo ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
        (N : ℕ) (a : PositiveCoefficient (unitNeumannCube d))
        (u : meanZeroSobolevGraph (unitNeumannCube d)) (Kf : ℝ)
        (Z : ℕ → SpatialCoordinates d → ℝ) (Draw : ℕ → SpatialCoordinates d → ℝ≥0∞)
        (rate xi B V Cstep c : ℝ),
      0 ≤ xi → 0 ≤ B → 0 ≤ V → 1 ≤ Cstep → 0 ≤ c →
      c * (d + 1 : ℕ) * xi ≤ eta * Real.log 3 →
      (∀ (n : ℕ) (p : PrefixRootIndex d), p ∈ prefixRootCatalogue d 1 1 n →
        prefixRootLevel 1 p ≤ (N : ℤ) →
        (nativeScoreAllowance (fun j => Z j ((3 : ℝ) ^ N • prefixRootCentre 1 p))
          (fun j => Draw j ((3 : ℝ) ^ N • prefixRootCentre 1 p))
            ((N : ℤ) - prefixRootLevel 1 p).toNat rate : ℝ) ≤ xi * n + B) →
      (∀ k : ℕ, k ≤ N → ∀ z ∈
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        aux_in_deterministic_onestep_sref M H omega N k z +
          (aux_in_deterministic_onestep_sref M H omega N k z)⁻¹ ≤ V * (3 : ℝ) ^ k) →
      (∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ), 1 ≤ k → k ≤ N →
        s ∈ Set.range (fun j : ℤ => (3 : ℝ) ^ j / 2) →
        (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s → 8 * s < (3 : ℝ) ^ (-(k : ℤ)) / 2 →
        (∀ i, i ∉ I → 4 * 10 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ min (y i) (1 - y i)) →
        aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
          Cstep * Real.exp (c * (nativeScoreAllowance
            (fun j => Z j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I))
            (fun j => Draw j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)) (N - k + 1) rate : ℝ)) *
            (s / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t *
            (aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (10 * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
              (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1)
                (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
                  ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2))) →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
        aux_rem_resolved_meshes_energy a u (Metric.ball x rad) ≤
          Cgeo * (Cstep ^ (d + 1) * Real.exp (c * (d + 1 : ℕ) * B)) * (2 * rad) ^ (t - eta) *
            (aux_rem_resolved_meshes_energy a u Set.univ + V * Kf ^ 2) := by
  let Cgeo := (2 : ℝ) ^ d + (36 * (3 * (1 + 100 * 10)) ^ d) ^ t * 3 ^ eta * 2 ^ t *
    ((1 / 4374 : ℝ) ^ (-t) + (d : ℝ) + 1)
  refine ⟨Cgeo, aux_two_mesh_energy_bound_Cpos d 10 (1 / 4374) t eta (by norm_num) (by norm_num), ?_⟩
  intro M H omega N a u Kf Z Draw rate xi B V Cstep c hxi hB hV hCs hc hgap hroot href hone x hx rad hrad
  let b := fun (k : ℕ) (z : SpatialCoordinates d) => aux_in_deterministic_onestep_sref M H omega N (k - 1 : ℕ) z
  let budget := fun (y : SpatialCoordinates d) (I : Finset (Fin d)) (k : ℕ) =>
    nativeCutoffRootAllowance Z Draw N k rate (aux_rem_resolved_meshes_center y I)
  have hreference : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
      b k z + (b k z)⁻¹ ≤ V * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ (-1 : ℝ) := by
    intro k hk z hz
    exact (href (k - 1) (by omega) z (aux_lem_as_regularity_two_mesh_closed z hz)).trans
      (mul_le_mul_of_nonneg_left (aux_lem_as_regularity_two_mesh_depth k) hV)
  have hcore := aux_two_mesh_energy_bound_core d hd 10 (1 / 4374) t eta 1
    (by norm_num) (by norm_num) (by norm_num) ⟨-7, by norm_num⟩ ht1 ht2 heta heta1
    (by linarith only [ht2]) 1 le_rfl Cstep c hCs hc N Kf (aux_rem_resolved_meshes_energy a u)
    (fun S T hST => aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ hST)
    (fun S => aux_rem_resolved_strata_energy_nonneg a ⟨u.1, u.2.1⟩ S)
    b (fun k z => aux_in_deterministic_onestep_sref_pos M H omega N _ z)
    budget (fun y I k => nativeCutoffRootAllowance_nonneg Z Draw N k rate _) ?_
    (Cstep ^ (d + 1) * Real.exp (c * (d + 1 : ℕ) * B))
    (fun n g dep sigma => native_mesh_allowance_le Z Draw N rate xi B eta c Cstep hxi hB hc
      (le_trans zero_le_one hCs) hgap hroot n g dep sigma) V hreference x hx (2 * rad) ?_
  · simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hcore
  · intro y hy I s k hs hsmin hs0 hkN hsR hR hI
    have hk1 : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      subst k
      norm_num at hR
    have hh := hone y hy I s k hk1 hkN hs hsmin hs0 hsR hI
    change _ ≤ Cstep * Real.exp (c * budget y I k) * _ * (_ + (b k _)⁻¹ * _ * _)
    dsimp only [budget, nativeCutoffRootAllowance, b]
    rw [ite_eq_left hkN, Nat.cast_sub hk1, Nat.cast_one]
    exact hh
  · have hrpos : 0 < rad := lt_of_lt_of_le (zpow_pos (by norm_num) _) hrad
    linarith only [hrad, hrpos]

end SubdiffusiveProcess.Paper
