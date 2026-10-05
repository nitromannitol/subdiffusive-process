module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleExtraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ConstantRepresentative

@[expose] public section

/-!
# S8 and S10 against the v4 Liouville hypothesis

The Liouville growth
hypothesis is stated of `t.large.scale.Holder.multifractal` from the `liminf` equation to
its intended analytic meaning:

```lean
(∀ ε > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
    sInf {r : ℝ | ∃ c : ℝ,
      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < ε) →
```

This is exactly the "frequently small" statement that
`LiouvilleExtraction.exists_radius_ge_and_lt` had to assume, so the
`IsCoboundedUnder` side condition disappears and **S8 becomes unconditional**
(`exists_scale_ge_and_lt_v4`).

S10 then follows.  Taking the base point `z = 0`, which lies on every triadic
grid, and the window `𝔠_n` (which is `translatedCube d n 0`), the oscillation
display of Theorem C reads

```
‖u-(u)_{𝔠_n}‖_{L̲²(𝔠_n)} ≤ C·3^{γn}·( 3^{-γm}‖u-(u)_{𝔠_m}‖_{L̲²(𝔠_m)} )
```

whose bracket S8 makes arbitrarily small at arbitrarily large `m`.  With `n`
fixed the left side is therefore `0`, so `u` is almost everywhere constant on
every `𝔠_n`; the constants agree because the cubes are nested and have positive
measure, and the cubes exhaust `ℝᵈ`.  That is
`t.large.scale.Holder.multifractal`, and it feeds `ConstantRepresentative` (S12) to
produce the frozen conclusion package.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### S8 against the v4 hypothesis -/

/-- **S8, unconditional under D-059.**  The v4 hypothesis is precisely the
frequently-small statement, so radii are available directly. -/
theorem exists_radius_ge_and_lt_v4 {gamma : ℝ} {u : Vec d → ℝ}
    (hfreq : ∀ ε > 0, ∃ᶠ R : ℝ in atTop,
      liouvilleFunctional (d := d) gamma u R < ε)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (R0 : ℝ) :
    ∃ R : ℝ, R0 ≤ R ∧ liouvilleFunctional (d := d) gamma u R < epsilon :=
  frequently_atTop.1 (hfreq epsilon hepsilon) R0

/-- **S8 assembled, unconditional.**  For every `ε > 0` and every `N` there is a
scale `m ≥ N` at which the scaled centered cube seminorm is below `ε`. -/
theorem exists_scale_ge_and_lt_v4 {gamma : ℝ} {u : Vec d → ℝ}
    (hgamma : 0 < gamma)
    (hfreq : ∀ ε > 0, ∃ᶠ R : ℝ in atTop,
      liouvilleFunctional (d := d) gamma u R < ε)
    (huInt : ∀ m : ℤ, IntegrableOn u (cube d m))
    (huSq : ∀ m : ℤ, IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hball : ∀ (R : ℝ) (c : ℝ),
      IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℤ) :
    ∃ m : ℤ, N ≤ m ∧
      (3 : ℝ) ^ (-gamma * (m : ℝ)) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u) < epsilon := by
  set K : ℝ := ((3 : ℝ) / 2) ^ gamma * Real.sqrt ((3 : ℝ) ^ d) with hK
  have hKpos : 0 < K := by
    refine mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos.2 ?_)
    positivity
  obtain ⟨R, hRge, hRlt⟩ :=
    exists_radius_ge_and_lt_v4 hfreq (div_pos hepsilon hKpos)
      (max ((3 : ℝ) ^ N) 1)
  have hR3N : (3 : ℝ) ^ N ≤ R := le_trans (le_max_left _ _) hRge
  have hRpos : 0 < R :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hRge)
  obtain ⟨m, hlower, hupper⟩ := exists_scale_le_and_lt hRpos
  refine ⟨m, le_of_scale_of_le hR3N hupper, ?_⟩
  have hscale : ((3 : ℝ) ^ m) ^ (-gamma) ≤
      ((3 : ℝ) / 2) ^ gamma * R ^ (-gamma) :=
    rpow_neg_scale_le hgamma hRpos hupper
  have htransfer :
      normalizedL2On (cube d m) (fun x ↦ u x - averageOn (cube d m) u) ≤
        Real.sqrt ((3 : ℝ) ^ d) *
          sInf {r : ℝ | ∃ c : ℝ,
            r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)} :=
    normalizedL2On_cube_le_sInf_ball hlower hupper (huInt m) (huSq m)
      (fun c ↦ hball R c)
  have hprod :
      ((3 : ℝ) ^ m) ^ (-gamma) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u) ≤
        K * liouvilleFunctional (d := d) gamma u R := by
    have h2 : (0 : ℝ) ≤
        normalizedL2On (cube d m) (fun x ↦ u x - averageOn (cube d m) u) :=
      normalizedL2On_nonneg _ _
    calc ((3 : ℝ) ^ m) ^ (-gamma) *
            normalizedL2On (cube d m)
              (fun x ↦ u x - averageOn (cube d m) u)
        ≤ (((3 : ℝ) / 2) ^ gamma * R ^ (-gamma)) *
            (Real.sqrt ((3 : ℝ) ^ d) *
              sInf {r : ℝ | ∃ c : ℝ,
                r = normalizedL2On (Metric.ball (0 : Vec d) R)
                  (fun x ↦ u x - c)}) :=
          mul_le_mul hscale htransfer h2 (by positivity)
      _ = K * liouvilleFunctional (d := d) gamma u R := by
          rw [hK, liouvilleFunctional]; ring
  rw [rpow_neg_mul_intCast]
  refine lt_of_le_of_lt hprod ?_
  rw [← lt_div_iff₀' hKpos]
  exact hRlt

/-! ### From a vanishing seminorm to almost-everywhere constancy -/

/-- A vanishing normalized seminorm on a window of positive finite volume forces
the function to vanish almost everywhere there. -/
theorem ae_eq_zero_of_normalizedL2On_eq_zero {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW : 0 < (volume W).toReal) (hf : IntegrableOn (fun x ↦ f x ^ 2) W)
    (h : normalizedL2On W f = 0) :
    f =ᵐ[volume.restrict W] 0 := by
  have hint : ∫ x in W, f x ^ 2 ∂volume = 0 := by
    have hsq : volumeAverage W (fun x ↦ f x ^ 2) = 0 :=
      (Real.sqrt_eq_zero (volumeAverage_sq_nonneg W f)).1 h
    unfold volumeAverage at hsq
    have hne : ((volume W).toReal)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.1 hsq).resolve_left hne
  have hae : (fun x ↦ f x ^ 2) =ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x)) hf).1 hint
  filter_upwards [hae] with x hx
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx

/-- A nonnegative quantity dominated by `B·ε` for every `ε > 0` is zero. -/
theorem eq_zero_of_le_const_mul_eps {A B : ℝ} (hAnn : 0 ≤ A) (hBnn : 0 ≤ B)
    (h : ∀ ε > 0, A ≤ B * ε) : A = 0 := by
  by_contra hne
  have hApos : 0 < A := lt_of_le_of_ne hAnn (Ne.symm hne)
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · have h1 := h 1 one_pos
    rw [← hB0, zero_mul] at h1
    linarith
  · have hle := h (A / (2 * B)) (by positivity)
    have hrw : B * (A / (2 * B)) = A / 2 := by field_simp
    rw [hrw] at hle
    linarith

/-- **S10, the local step.**  If the centered seminorm on `𝔠_n` is dominated by
`C·3^{γn}·ε` for every `ε > 0` -- which is what Theorem C's oscillation display
gives once S8 makes the outer factor arbitrarily small -- then it vanishes. -/
theorem normalizedL2On_cube_sub_average_eq_zero {gamma C : ℝ} {u : Vec d → ℝ}
    (hC : 0 ≤ C) (n : ℤ)
    (hdisp : ∀ ε > 0,
      normalizedL2On (cube d n) (fun x ↦ u x - averageOn (cube d n) u) ≤
        C * (3 : ℝ) ^ (gamma * (n : ℝ)) * ε) :
    normalizedL2On (cube d n) (fun x ↦ u x - averageOn (cube d n) u) = 0 :=
  eq_zero_of_le_const_mul_eps (normalizedL2On_nonneg _ _)
    (by positivity) hdisp

/-- **S10, the local conclusion.**  Hence `u` agrees almost everywhere with its
own average on `𝔠_n`. -/
theorem ae_eq_average_of_disp {gamma C : ℝ} {u : Vec d → ℝ}
    (hC : 0 ≤ C) (n : ℤ)
    (hint : IntegrableOn
      (fun x ↦ (u x - averageOn (cube d n) u) ^ 2) (cube d n))
    (hdisp : ∀ ε > 0,
      normalizedL2On (cube d n) (fun x ↦ u x - averageOn (cube d n) u) ≤
        C * (3 : ℝ) ^ (gamma * (n : ℝ)) * ε) :
    u =ᵐ[volume.restrict (cube d n)] fun _ ↦ averageOn (cube d n) u := by
  have hzero := ae_eq_zero_of_normalizedL2On_eq_zero
    (volume_cube_toReal_pos d n) hint
    (normalizedL2On_cube_sub_average_eq_zero hC n hdisp)
  filter_upwards [hzero] with x hx
  have : u x - averageOn (cube d n) u = 0 := hx
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
