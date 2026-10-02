import SubdiffusiveProcess.Section10.EndpointPaths

open Filter Topology Set
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

def logScaleConstant (eta : ℝ) : ℝ :=
  1 + 1 / ((2 + eta) * Real.log 3 / 2)

/-- No monotonicity of the polynomial/geometric endpoints is required. -/
lemma endpoint_bracket (eta epsilon : ℝ) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (N : ℕ) : ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧ B = logScaleConstant eta ∧
      ∀ t : ℝ, 0 < t → t < delta → ∃ k : ℕ,
        N ≤ k ∧ endpoint eta epsilon k ≤ t ∧
        1 ≤ Real.log (1 / t) ∧ (k : ℝ) ≤ B * Real.log (1 / t) ∧
        t ≤ (3 : ℝ) ^ (2 + eta) * B ^ (1 + epsilon) *
          Real.log (1 / t) ^ (1 + epsilon) * (3 : ℝ) ^ (-((2 + eta) * k)) := by
  let a := 2 + eta
  let b := 1 + epsilon
  let c := a * Real.log 3 / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := div_pos (mul_pos ha (Real.log_pos (by norm_num))) (by norm_num)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (endpoint_eventually_le_exp eta epsilon heta)
  let K := max (max N J) 1
  have hK0 : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hKN : N ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKJ : J ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  let B := 1 + 1 / c
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min (endpoint eta epsilon K) (Real.exp (-1)), B,
    lt_min (endpoint_pos eta epsilon hK0) (Real.exp_pos _), hB, rfl, ?_⟩
  intro t ht htd
  have htK : t < endpoint eta epsilon K := htd.trans_le (min_le_left _ _)
  have htE : t < Real.exp (-1) := htd.trans_le (min_le_right _ _)
  have hL : 1 ≤ Real.log (1 / t) := by
    have := (Real.log_lt_log_iff ht (Real.exp_pos (-1))).mpr htE
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hex : ∃ k : ℕ, K ≤ k ∧ endpoint eta epsilon k ≤ t := by
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((endpoint_tendsto_zero eta epsilon heta).eventually (eventually_lt_nhds ht))
    exact ⟨max K M, le_max_left _ _, (hM _ (le_max_right _ _)).le⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkK : K < k := by
    have hne : k ≠ K := by intro heq; exact htK.not_ge (heq ▸ hk.2)
    exact lt_of_le_of_ne hk.1 (Ne.symm hne)
  have hjK : K ≤ k - 1 := by omega
  have hj : t < endpoint eta epsilon (k - 1) := by
    have h := Nat.find_min hex (show k - 1 < k by omega)
    exact lt_of_not_ge (fun hle => h ⟨hjK, hle⟩)
  have hjexp := hJ (k - 1) (hKJ.trans hjK)
  have hclog : c * ((k - 1 : ℕ) : ℝ) ≤ Real.log (1 / t) := by
    have := (Real.log_lt_log_iff ht (Real.exp_pos _)).mpr (hj.trans_le hjexp)
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    change Real.log t < -c * ((k - 1 : ℕ) : ℝ) at this
    linarith
  have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k = k - 1 + 1 by omega)
  have hkB : (k : ℝ) ≤ B * Real.log (1 / t) := by
    have hdiv : ((k - 1 : ℕ) : ℝ) ≤ Real.log (1 / t) / c :=
      (le_div_iff₀ hc).mpr (by rwa [mul_comm])
    calc (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := hkcast
      _ ≤ Real.log (1 / t) / c + Real.log (1 / t) := add_le_add hdiv hL
      _ = B * Real.log (1 / t) := by dsimp [B]; ring
  have hjpow : ((k - 1 : ℕ) : ℝ) ^ b ≤ (B * Real.log (1 / t)) ^ b :=
    Real.rpow_le_rpow (by positivity) ((by linarith [hkcast] :
      ((k - 1 : ℕ) : ℝ) ≤ B * Real.log (1 / t))) hb.le
  have hgeom : (3 : ℝ) ^ (-(a * ((k - 1 : ℕ) : ℝ))) =
      (3 : ℝ) ^ a * (3 : ℝ) ^ (-(a * (k : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hkcast]
    ring
  refine ⟨k, hKN.trans hk.1, hk.2, hL, hkB, ?_⟩
  have hL0 : 0 ≤ Real.log (1 / t) := le_trans (by norm_num) hL
  calc t ≤ endpoint eta epsilon (k - 1) := hj.le
    _ = ((k - 1 : ℕ) : ℝ) ^ b * (3 : ℝ) ^ (-(a * ((k - 1 : ℕ) : ℝ))) := rfl
    _ ≤ (B * Real.log (1 / t)) ^ b * (3 : ℝ) ^ (-(a * ((k - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hjpow (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ a * B ^ b * Real.log (1 / t) ^ b * (3 : ℝ) ^ (-(a * k)) := by
      rw [hgeom, Real.mul_rpow hB.le hL0]
      ring

lemma rpow_radius (eta : ℝ) (k : ℕ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 + eta) = (3 : ℝ) ^ (-((2 + eta) * k)) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

lemma root_lower_bound (a b B t R : ℝ) (ha : 0 < a) (hB : 0 < B)
    (ht : 0 < t) (hL : 0 < Real.log (1 / t)) (hR : 0 ≤ R)
    (h : t ≤ (3 : ℝ) ^ a * B ^ b * Real.log (1 / t) ^ b * R ^ a) :
    (t / Real.log (1 / t) ^ b) ^ (1 / a) ≤
      ((3 : ℝ) ^ a * B ^ b) ^ (1 / a) * R := by
  have hD : 0 < (3 : ℝ) ^ a * B ^ b :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hB _)
  have hLp : 0 < Real.log (1 / t) ^ b := Real.rpow_pos_of_pos hL _
  have hdiv : t / Real.log (1 / t) ^ b ≤ ((3 : ℝ) ^ a * B ^ b) * R ^ a := by
    apply (div_le_iff₀ hLp).mpr
    convert h using 1; ring
  calc (t / Real.log (1 / t) ^ b) ^ (1 / a)
      ≤ (((3 : ℝ) ^ a * B ^ b) * R ^ a) ^ (1 / a) :=
        Real.rpow_le_rpow (div_pos ht hLp).le hdiv (one_div_pos.mpr ha).le
    _ = ((3 : ℝ) ^ a * B ^ b) ^ (1 / a) * R := by
      rw [Real.mul_rpow hD.le (Real.rpow_nonneg hR _), ← Real.rpow_mul hR,
        mul_one_div_cancel ha.ne', Real.rpow_one]

end SubdiffusiveProcess.Section10.EndpointPaths
