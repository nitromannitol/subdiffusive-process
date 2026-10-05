module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScalingAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Assembly
public import SubdiffusiveProcess.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
@[expose] public section

/-!
# Conductance increments for the cutoff clock

Annealed ordering controls successive scales and the initial logarithmic
range. The reciprocal one-step estimate is summed in blocks of
`floor (delta⁻¹)` to control arbitrary pairs of scales in dimensions at least
three. Planar increments follow from the exact self-duality formula.
-/

set_option autoImplicit false
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
open _root_.SubdiffusiveProcess.Model (tauSq)
noncomputable section

theorem neg_log_mono {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Monotone (fun n => -Real.log (ahom M n)) := by
  intro n m hnm
  rcases lt_or_eq_of_le hnm with h | h
  · exact neg_le_neg (Real.log_le_log (ahom_pos M m)
      (_root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds.2 M m n h).1)
  · subst h; rfl

theorem neg_log_step {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) :
    -Real.log (ahom M (n+1)) - (-Real.log (ahom M n)) ≤
      2 * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
  obtain ⟨_, it⟩ :=
    _root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds.2 M (n+1) n (by omega)
  have h := Real.log_le_log (ahom_pos M n) it
  rw [Real.log_mul (Real.exp_pos _).ne' (ahom_pos M (n+1)).ne', Real.log_exp] at h
  norm_num at h
  linarith

theorem tau_bounds {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta^2 ∧
    _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ 1/4 := by
  have ht := tauSq_le_delta_sq M
  have hδ := M.shellPrefix.delta_pos
  have hh := M.shellPrefix.delta_le_half
  have hsmall : tauSq M.P ≤ M.delta^2 := by
    nlinarith [Real.log_two_lt_d9, sq_nonneg M.delta]
  exact ⟨hsmall, by nlinarith⟩

theorem planar_log_increment (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (n m : ℕ) :
    Real.log (ahom M n) - Real.log (ahom M m) =
      _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) - (n : ℝ)) := by
  rw [_root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M n,
      _root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M m,
      Real.log_exp, Real.log_exp]
  ring

theorem log_ratio_from_annealed {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {n m : ℕ} (hnm : n ≤ m) :
    Real.log (ahom M n) - Real.log (ahom M m) ≤
      2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m:ℝ)-(n:ℝ)) := by
  rcases Nat.eq_or_lt_of_le hnm with rfl | h
  · simp
  · have hb := (_root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds.2 M m n h).2
    have h1 := Real.log_le_log (ahom_pos M n) hb
    rw [Real.log_mul (Real.exp_pos _).ne' (ahom_pos M m).ne',
        Real.log_exp] at h1
    rw [Nat.cast_sub hnm] at h1
    linarith

/-- Summing the reciprocal one-step estimate from any starting scale. -/
theorem high_dimensional_log_increments (d : ℕ) (hd : 3 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ), n ≤ m →
      Real.log (ahom M n) - Real.log (ahom M m) ≤
        K * M.delta ^ 2 * |Real.log M.delta| +
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / d +
            K * M.delta ^ 3 * |Real.log M.delta|) * ((m : ℝ) - (n : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hstep⟩ :=
    Section5DualClosure.sharpOneStepLowerConclusion_of_dualCellMajorants hd
      (Section5DualCompetitor.dualCellMajorantInputsOfNeZero d hd)
  refine ⟨264 + 6 * C, by positivity, ?_⟩
  intro M n m hnm
  let J := sharpStartScale M.delta
  let H := sharpBlockLength M.delta
  let z := |Real.log M.delta|
  let t := 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / d
  let E := 3 * C * M.delta ^ 2 * z
  let F := fun k : ℕ => -Real.log (ahom M k) - t * (k : ℝ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have ht0 : 0 ≤ t :=
    div_nonneg (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) hd0.le
  have hz0 : 0 ≤ z := abs_nonneg _
  have hdelta := M.shellPrefix.delta_pos
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hH : 0 < H := sharpBlockLength_pos hdelta M.shellPrefix.delta_le_half
  have hHupper := delta_mul_sharpBlockLength_le_one hdelta
  have hHlower := half_le_delta_mul_sharpBlockLength hdelta M.shellPrefix.delta_le_half
  have hloghalf := half_le_abs_log_delta hdelta M.shellPrefix.delta_le_half
  have hstart := sourceStartScale_le_sharpStartScale hdelta M.shellPrefix.delta_le_half
  have hshort : ∀ k h : ℕ, J ≤ k → h ≤ H → F (k + h) - F k ≤ E := by
    intro k h hk hh
    have hhreal : (h : ℝ) ≤ H := by exact_mod_cast hh
    have hHinv : (H : ℝ) ≤ M.delta⁻¹ := Nat.floor_le (by positivity)
    have hraw := hstep M k h (hhreal.trans hHinv) (hstart.trans hk)
    have hrecip : Real.log (ahom M k) - Real.log (ahom M (k+h)) ≤
        t * (h : ℝ) + (C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 2 * z) := by
      apply reciprocal_log (ahom_pos M k) (ahom_pos M (k+h))
      convert hraw using 1
      dsimp [t, z]
      ring
    have herror := short_block_error hC.le hdelta.le (Nat.cast_nonneg h) hhreal
      hHupper hloghalf
    have heq : F (k+h) - F k =
        Real.log (ahom M k) - Real.log (ahom M (k+h)) - t*(h:ℝ) := by
      dsimp [F]
      push_cast
      ring
    rw [heq]
    change _ ≤ 3*C*M.delta^2*z
    linarith
  have htail : ∀ k l : ℕ, J ≤ k → k ≤ l →
      Real.log (ahom M k) - Real.log (ahom M l) ≤
        (2 * M.delta * ((l : ℝ) - (k : ℝ)) + 1) * E +
          t * ((l : ℝ) - (k : ℝ)) := by
    intro k l hk hkl
    have hfull : ∀ k q : ℕ, J ≤ k → F (k+q*H)-F k ≤ (q:ℝ)*E :=
      fun k q hk => block_telescope hshort hk q
    have hsum := block_remainder hfull hshort (n := k) (k := l-k) hk hH
    have hqH : (l-k)/H*H ≤ l-k := by
      have he := Nat.mod_add_div (l-k) H
      rw [Nat.mul_comm H] at he
      omega
    have hqHreal : (((l-k)/H : ℕ) : ℝ) * (H : ℝ) ≤ (l-k : ℕ) := by
      exact_mod_cast hqH
    have hcount := block_count hdelta.le (Nat.cast_nonneg ((l-k)/H)) hE0 hHlower hqHreal
    have heq : k+(l-k) = l := by omega
    rw [heq] at hsum
    rw [Nat.cast_sub hkl] at hcount
    have hsum' := hsum.trans hcount
    dsimp [F] at hsum'
    linarith
  have hearly : ∀ k l : ℕ, k ≤ l → l ≤ J →
      Real.log (ahom M k) - Real.log (ahom M l) ≤ 264*M.delta^2*z := by
    intro k l hkl hlJ
    have hraw := log_ratio_from_annealed M hkl
    have hgap : (l:ℝ)-(k:ℝ) ≤ (J:ℝ)+1 := by
      have hh : (l:ℝ) ≤ J := by exact_mod_cast hlJ
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      linarith
    exact hraw.trans (early_log_cost M.G4.tauSq_pos.le (tau_bounds M).1 hgap
      (sharpStartScale_add_one_le hdelta M.shellPrefix.delta_le_half) hz0
      (sub_nonneg.mpr (by exact_mod_cast hkl)))
  have hcost : Real.log (ahom M n)-Real.log (ahom M m) ≤
      264*M.delta^2*z + (2*M.delta*((m:ℝ)-(n:ℝ))+1)*E + t*((m:ℝ)-(n:ℝ)) := by
    have hgap0 : 0 ≤ (m:ℝ)-(n:ℝ) := sub_nonneg.mpr (by exact_mod_cast hnm)
    have hbase0 : 0 ≤ 264*M.delta^2*z := by positivity
    by_cases hJn : J ≤ n
    · have hh := htail n m hJn hnm
      linarith
    · by_cases hmJ : m ≤ J
      · have hh := hearly n m hnm hmJ
        have hx : 0 ≤ (2*M.delta*((m:ℝ)-(n:ℝ))+1)*E := by positivity
        have hy : 0 ≤ t*((m:ℝ)-(n:ℝ)) := mul_nonneg ht0 hgap0
        linarith
      · have hnJ : n ≤ J := by omega
        have hJm : J ≤ m := by omega
        have hfirst := hearly n J hnJ le_rfl
        have hsecond := htail J m le_rfl hJm
        have hnJreal : (n:ℝ) ≤ J := by exact_mod_cast hnJ
        have hcount : (2*M.delta*((m:ℝ)-(J:ℝ))+1)*E ≤
            (2*M.delta*((m:ℝ)-(n:ℝ))+1)*E := by
          apply mul_le_mul_of_nonneg_right _ hE0
          nlinarith
        have hdrift : t*((m:ℝ)-(J:ℝ)) ≤ t*((m:ℝ)-(n:ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) ht0
        linarith
  have hfinal := block_global_algebra hC.le hdelta.le hz0
    (sub_nonneg.mpr (show (n:ℝ) ≤ m by exact_mod_cast hnm)) hcost
  exact hfinal

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
