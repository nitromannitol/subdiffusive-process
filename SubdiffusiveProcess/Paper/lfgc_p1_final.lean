import SubdiffusiveProcess.Paper.lfgc_p1_cover

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Constants after the moment order. -/
theorem lfgc_p1_final {R p a' sigma lam v Cg Et : ℝ} (c1 buffer k0 : ℕ) (hR : 0 < R) (hp1 : 1 ≤ p)
    (ha'0 : 0 < a') (hs0 : 0 < sigma) (hlam : 0 < lam) (hv0 : 0 ≤ v) (hCg0 : 0 ≤ Cg)
    (hEt0 : 0 ≤ Et) (hps : 2 * R ≤ p * (sigma * Real.log 3 / 16))
    (hρ : ((3 : ℝ) ^ (-a') / (3 : ℝ) ^ (-(a' / 2))) ^ p ≤ Real.exp (-(2 + v + R * c1))) :
    ∃ (L0 Kn : ℕ) (Merr κ M' : ℝ), 0 < Merr ∧ Merr = κ * Real.exp (-(R * L0 / p)) ∧
      (2 + 2 * (buffer : ℝ)) * Et * (3 : ℝ) ^ (-(sigma / 16 * (L0 : ℝ))) ≤
        κ * Real.exp (-(R * L0 / p)) ∧
      k0 ≤ Kn ∧ 0 < M' ∧ M' < 1 ∧
      (∀ H : ℕ, Cg * (M' * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1))) *
          Real.exp (-(((v + R * c1 + 1) - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) *
          Paper.aux_prefix_error p Merr ((3 : ℝ) ^ (-a')) ((3 : ℝ) ^ (-(a' / 2)))
            (lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4) H ≤
        (1 / 3) * (Real.exp (-R * ((c1 * (H + 1) + L0 + buffer + 3 : ℕ) : ℝ)) / 2)) ∧
      (∀ H : ℕ, Kn ≤ H → Cg * 2 * Real.exp (-(((v + R * c1 + 1) - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) *
          Paper.aux_prefix_error p Merr ((3 : ℝ) ^ (-a')) ((3 : ℝ) ^ (-(a' / 2)))
            (lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4) H ≤
        (1 / 3) * (Real.exp (-R * ((c1 * (H + 1) + L0 + buffer + 3 : ℕ) : ℝ)) / 2)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < (3 : ℝ) ^ (-a') := by positivity
  have hr0 : 0 < (3 : ℝ) ^ (-(a' / 2)) := by positivity
  have hr1 : (3 : ℝ) ^ (-(a' / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqr : (3 : ℝ) ^ (-a') < (3 : ℝ) ^ (-(a' / 2)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hK'0 : 0 < lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4 := by
    have : 0 < 1 - (3 : ℝ) ^ (-(a' / 2)) := by linarith
    positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ((3 : ℝ) ^ (-a') * (lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4) / 2) *
      (Real.exp (-(R * ((c1 : ℝ) + buffer + 3))) / (24 * (Cg + 1))) ^ (1 / p) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨L0, hL0⟩ := p1_offset (E := (2 + 2 * (buffer : ℝ)) * Et) (by positivity) hκ0 hR hp1 hs0 hps
  obtain ⟨Merr, hMerr⟩ : ∃ Merr : ℝ, Merr = κ * Real.exp (-(R * L0 / p)) := ⟨_, rfl⟩
  have hMerr0 : 0 < Merr := by rw [hMerr]; positivity
  have hX : 24 * (Cg + 1) *
      (2 * Merr / ((3 : ℝ) ^ (-a') * (lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4))) ^ p ≤
      Real.exp (-(R * ((c1 : ℝ) + L0 + buffer + 3))) := by
    have hsplit := p1_merr_split (R := R) hq0 hK'0 hCg0 hp0 ((c1 : ℝ) + buffer + 3) L0
    have hid := p1_merr_identity (R := R) hq0 hK'0 hCg0 hp0 ((c1 : ℝ) + buffer + 3 + L0)
    rw [hsplit] at hid
    rw [show (c1 : ℝ) + L0 + buffer + 3 = (c1 : ℝ) + buffer + 3 + L0 by ring, hMerr, hκ]
    exact le_of_eq hid
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℕ, Kn = max k0 ⌈Real.log (24 * (Cg + 1)) +
      R * ((c1 : ℝ) + L0 + buffer + 3)⌉₊ := ⟨_, rfl⟩
  have hKb : Real.log (24 * (Cg + 1)) + R * ((c1 : ℝ) + L0 + buffer + 3) ≤ Kn := by
    have h1 := Nat.le_ceil (Real.log (24 * (Cg + 1)) + R * ((c1 : ℝ) + L0 + buffer + 3))
    have h2 : ⌈Real.log (24 * (Cg + 1)) + R * ((c1 : ℝ) + L0 + buffer + 3)⌉₊ ≤ Kn := by
      rw [hKn]; exact le_max_right _ _
    have h2' : (⌈Real.log (24 * (Cg + 1)) + R * ((c1 : ℝ) + L0 + buffer + 3)⌉₊ : ℝ) ≤ Kn := by
      exact_mod_cast h2
    linarith
  obtain ⟨E0, hE0⟩ : ∃ E0 : ℝ, E0 = Real.exp (-(R * ((c1 : ℝ) + L0 + buffer + 3))) := ⟨_, rfl⟩
  have hE0p : 0 < E0 := by rw [hE0]; exact Real.exp_pos _
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = min (1 / 2)
      (E0 / (12 * (Cg + 1) * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)))) := ⟨_, rfl⟩
  have hexpK : 0 < Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)) := Real.exp_pos _
  have hden : 0 < 12 * (Cg + 1) * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)) := by positivity
  have hM'0 : 0 < M' := by rw [hM']; exact lt_min (by norm_num) (div_pos hE0p hden)
  have hM'1 : M' < 1 := by rw [hM']; exact (min_le_left _ _).trans_lt (by norm_num)
  have hM'b : Cg * M' * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)) ≤
      Real.exp (-(R * ((c1 : ℝ) + L0 + buffer + 3))) / 12 := by
    rw [← hE0]
    have hle : M' ≤ E0 / (12 * (Cg + 1) * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1))) := by
      rw [hM']; exact min_le_right _ _
    calc Cg * M' * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1))
        ≤ Cg * (E0 / (12 * (Cg + 1) * Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)))) *
            Real.exp ((v + R * c1 + 1) * ((Kn : ℝ) - 1)) := by gcongr
      _ = E0 / 12 * (Cg / (Cg + 1)) := by field_simp
      _ ≤ E0 / 12 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = E0 / 12 := mul_one _
  obtain ⟨hbS, hbL⟩ := lfgc_p1_num (R := R) (v := v) (Cg := Cg) (A := v + R * c1 + 1) (M' := M')
    (Merr := Merr) (q := (3 : ℝ) ^ (-a')) (r := (3 : ℝ) ^ (-(a' / 2)))
    (K' := lam * (1 - (3 : ℝ) ^ (-(a' / 2))) / 4) (p := p) (c1 := c1) (L0 := L0) (b := buffer)
    (K := Kn) hR hv0 hCg0 rfl hq0 hqr hK'0 hp1 hρ hMerr0.le hX hM'0.le hM'b hKb
  exact ⟨L0, Kn, Merr, κ, M', hMerr0, hMerr, hL0, by rw [hKn]; exact le_max_left _ _, hM'0, hM'1,
    hbS, hbL⟩

end Paper
