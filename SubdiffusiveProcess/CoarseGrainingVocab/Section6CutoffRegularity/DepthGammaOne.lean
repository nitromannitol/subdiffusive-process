module

public import SubdiffusiveProcess.Assumptions.OGammaBridge

@[expose] public section

/-!
# From geometric depth tails to `O_{Γ_1}` control

The finite-cutoff good-scale proposition (paper label `e.cutoff.regularity.error.stopping.tail`,
displays `e.cutoff.regularity.error.stopping.tail` and
`e.cutoff.regularity.good.stopping.tail`) states the depth of a stopping
index in the expectation form `0 ≤ m - X ≤ 1 + O_{Γ_1}(A)`.  The proved
analytic estimates deliver instead a *tail* bound on the natural-valued
depth, of the geometric shape

`μ.real {ω | q < D ω} ≤ K * exp (-(r * (q - 1)_+))`,   `q ∈ ℕ`, `q > 0`.

This module converts that shape into the `SubdiffusiveProcess.OGammaLE` carrier for
the observable `(D - 1)_+`, with an explicit scale depending only on `K`
and `r`.  The two steps are separated: first the tail form
`Homogenization.IndependentSums.IsBigO ... (gammaSigma 1)`, then the
expectation form through `SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma`.

Both stopping clauses of the proposition consume this module, so the
integer-to-real bookkeeping is done once here rather than at each site.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The tail-form scale produced by a geometric depth tail with prefactor `K`
and rate `r`. -/
noncomputable def depthTailScale (K r : ℝ) : ℝ :=
  (1 + Real.log K + r) / r

/-- The expectation-form (`SubdiffusiveProcess.OGammaLE`) scale produced by a geometric depth
tail with prefactor `K` and rate `r`. -/
noncomputable def depthGammaOneScale (K r : ℝ) : ℝ :=
  4 * depthTailScale K r

theorem depthTailScale_pos {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r) :
    0 < depthTailScale K r := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  exact div_pos (by linarith) hr

theorem depthGammaOneScale_pos {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r) :
    0 < depthGammaOneScale K r :=
  mul_pos (by norm_num) (depthTailScale_pos hK hr)

theorem one_le_depthTailScale_mul_rate {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r) :
    r * depthTailScale K r = 1 + Real.log K + r := by
  unfold depthTailScale
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  field_simp

/-- The `(D - 1)_+` observable attached to a natural-valued depth. -/
noncomputable def depthObservable (D : Ω → ℕ) : Ω → ℝ :=
  fun omega => max ((D omega : ℝ) - 1) 0

omit [MeasurableSpace Ω] in
theorem depthObservable_nonneg (D : Ω → ℕ) (omega : Ω) :
    0 ≤ depthObservable D omega :=
  le_max_right _ _

theorem measurable_depthObservable {D : Ω → ℕ} (hD : Measurable D) :
    Measurable (depthObservable D) := by
  have hcast : Measurable fun omega : Ω => ((D omega : ℝ)) :=
    (measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp hD
  exact (hcast.sub measurable_const).max measurable_const

/-- **Tail form.**  A geometric tail on the natural-valued depth `D`, tested
only at positive natural thresholds, upgrades to the real-threshold
stretched-exponential bound at exponent `1`.

The prefactor `K` and the shortfall `r` in the exponent are absorbed into the
scale `depthTailScale K r`; the exponent slack is exactly the `t ≥ 1`
normalization of `IsBigO`. -/
theorem isBigO_gammaOne_depthObservable
    [IsFiniteMeasure μ] (D : Ω → ℕ) {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < D omega} ≤
        K * Real.exp (-(r * max ((q : ℝ) - 1) 0))) :
    IsBigO μ (gammaSigma 1) (depthObservable D) (depthTailScale K r) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hA : 0 < depthTailScale K r := depthTailScale_pos hK hr
  have hrA : r * depthTailScale K r = 1 + Real.log K + r :=
    one_le_depthTailScale_mul_rate hK hr
  rw [isBigO_gammaSigma_iff]
  intro t ht
  set A : ℝ := depthTailScale K r with hAdef
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hAt : 0 ≤ A * t := (mul_pos hA ht0).le
  -- the natural threshold just above `A * t`
  set q : ℕ := ⌊A * t⌋₊ + 1 with hqdef
  have hqpos : 0 < q := Nat.succ_pos _
  have hqle : (q : ℝ) ≤ A * t + 1 := by
    have := Nat.floor_le hAt
    push_cast [hqdef]
    linarith
  have hqsub : A * t - 1 ≤ (q : ℝ) - 1 := by
    have := Nat.lt_floor_add_one (A * t)
    push_cast [hqdef]
    linarith
  -- the real tail event sits inside the natural tail event
  have hsubset :
      absTailEvent (depthObservable D) (A * t) ⊆ {omega | q < D omega} := by
    intro omega homega
    have hlt : A * t < |depthObservable D omega| := homega
    have habs : |depthObservable D omega| = depthObservable D omega :=
      abs_of_nonneg (depthObservable_nonneg D omega)
    rw [habs] at hlt
    have hraw : A * t < (D omega : ℝ) - 1 := by
      unfold depthObservable at hlt
      rcases lt_max_iff.1 hlt with h | h
      · exact h
      · exact absurd h (not_lt.2 hAt)
    have : (q : ℝ) < (D omega : ℝ) := by linarith
    exact_mod_cast this
  -- transport the natural tail bound
  have hmono : μ.real (absTailEvent (depthObservable D) (A * t)) ≤
      μ.real {omega | q < D omega} :=
    measureReal_mono hsubset (measure_ne_top μ _)
  have hbase := htail q hqpos
  have hexp : K * Real.exp (-(r * max ((q : ℝ) - 1) 0)) ≤
      Real.exp (-(t ^ (1 : ℝ))) := by
    have hmax : A * t - 1 ≤ max ((q : ℝ) - 1) 0 :=
      hqsub.trans (le_max_left _ _)
    have hstep : -(r * max ((q : ℝ) - 1) 0) ≤ -(r * (A * t - 1)) := by
      have := mul_le_mul_of_nonneg_left hmax hr.le
      linarith
    have hK' : Real.exp (Real.log K) = K := Real.exp_log (by linarith)
    have hkey : Real.log K + -(r * (A * t - 1)) ≤ -(t ^ (1 : ℝ)) := by
      rw [Real.rpow_one]
      have hexpand : r * (A * t - 1) = (1 + Real.log K + r) * t - r := by
        rw [show r * (A * t - 1) = r * A * t - r by ring, hrA]
      rw [hexpand]
      nlinarith [mul_le_mul_of_nonneg_right ht (add_nonneg hlogK hr.le)]
    calc K * Real.exp (-(r * max ((q : ℝ) - 1) 0))
        ≤ K * Real.exp (-(r * (A * t - 1))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hstep) (by linarith)
      _ = Real.exp (Real.log K + -(r * (A * t - 1))) := by
          rw [Real.exp_add, hK']
      _ ≤ Real.exp (-(t ^ (1 : ℝ))) := Real.exp_le_exp.2 hkey
  exact hmono.trans (hbase.trans hexp)

/-- **Expectation form.**  The `SubdiffusiveProcess.OGammaLE` carrier for a stopping
depth with a geometric tail.  This is the shape consumed by the two stopping
clauses of `p.cutoff.regularity.good.scales`. -/
theorem ogammaLE_one_depthObservable
    [IsProbabilityMeasure μ] {D : Ω → ℕ} (hD : Measurable D)
    {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < D omega} ≤
        K * Real.exp (-(r * max ((q : ℝ) - 1) 0))) :
    SubdiffusiveProcess.OGammaLE μ 1 (depthGammaOneScale K r) (depthObservable D) := by
  have hbig := isBigO_gammaOne_depthObservable (μ := μ) D hK hr htail
  have hbridge :=
    SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (μ := μ)
      (σ := 1) (A := depthTailScale K r) (X := depthObservable D)
      zero_lt_one (depthTailScale_pos hK hr) (measurable_depthObservable hD) hbig
  have hscale : (4 : ℝ) ^ (1 : ℝ)⁻¹ * depthTailScale K r =
      depthGammaOneScale K r := by
    rw [inv_one, Real.rpow_one]
    rfl
  rwa [hscale] at hbridge

/-- The tail-form scale produced by an *unshifted* geometric depth tail,
whose exponent carries `q` rather than `(q - 1)_+`.

This is the sharp constant: unlike `depthTailScale`, it carries no additive
`1`, so it stays proportional to `r⁻¹` as the rate `r` grows.  In the
finite-cutoff application `r` is of order `s^6 ε² λ δ⁻² |log δ|⁻¹`, which is
large exactly in the small-`δ` regime, so the shifted scale would be useless
there. -/
noncomputable def depthTailScaleSharp (K r : ℝ) : ℝ :=
  (1 + Real.log K) / r

/-- The expectation-form scale attached to `depthTailScaleSharp`. -/
noncomputable def depthGammaOneScaleSharp (K r : ℝ) : ℝ :=
  4 * depthTailScaleSharp K r

theorem depthTailScaleSharp_pos {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r) :
    0 < depthTailScaleSharp K r := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  exact div_pos (by linarith) hr

theorem depthGammaOneScaleSharp_pos {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r) :
    0 < depthGammaOneScaleSharp K r :=
  mul_pos (by norm_num) (depthTailScaleSharp_pos hK hr)

theorem rate_mul_depthTailScaleSharp {K r : ℝ} (hr : 0 < r) :
    r * depthTailScaleSharp K r = 1 + Real.log K := by
  unfold depthTailScaleSharp
  field_simp

/-- **Sharp tail form.**  Same statement as `isBigO_gammaOne_depthObservable`,
but from the unshifted tail `μ.real {q < D} ≤ K exp (-(r q))`.  The resulting
scale is exactly `(1 + log K) / r`. -/
theorem isBigO_gammaOne_depthObservable_sharp
    [IsFiniteMeasure μ] (D : Ω → ℕ) {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < D omega} ≤ K * Real.exp (-(r * (q : ℝ)))) :
    IsBigO μ (gammaSigma 1) (depthObservable D) (depthTailScaleSharp K r) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hA : 0 < depthTailScaleSharp K r := depthTailScaleSharp_pos hK hr
  have hrA : r * depthTailScaleSharp K r = 1 + Real.log K :=
    rate_mul_depthTailScaleSharp hr
  rw [isBigO_gammaSigma_iff]
  intro t ht
  set A : ℝ := depthTailScaleSharp K r with hAdef
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hAt : 0 ≤ A * t := (mul_pos hA ht0).le
  set q : ℕ := ⌊A * t⌋₊ + 1 with hqdef
  have hqpos : 0 < q := Nat.succ_pos _
  have hqle : (q : ℝ) ≤ A * t + 1 := by
    have := Nat.floor_le hAt
    push_cast [hqdef]
    linarith
  have hqgt : A * t ≤ (q : ℝ) := by
    have := Nat.lt_floor_add_one (A * t)
    push_cast [hqdef]
    linarith
  have hsubset :
      absTailEvent (depthObservable D) (A * t) ⊆ {omega | q < D omega} := by
    intro omega homega
    have hlt : A * t < |depthObservable D omega| := homega
    rw [abs_of_nonneg (depthObservable_nonneg D omega)] at hlt
    have hraw : A * t < (D omega : ℝ) - 1 := by
      unfold depthObservable at hlt
      rcases lt_max_iff.1 hlt with h | h
      · exact h
      · exact absurd h (not_lt.2 hAt)
    have : (q : ℝ) < (D omega : ℝ) := by linarith
    exact_mod_cast this
  have hmono : μ.real (absTailEvent (depthObservable D) (A * t)) ≤
      μ.real {omega | q < D omega} :=
    measureReal_mono hsubset (measure_ne_top μ _)
  have hbase := htail q hqpos
  have hexp : K * Real.exp (-(r * (q : ℝ))) ≤ Real.exp (-(t ^ (1 : ℝ))) := by
    have hstep : -(r * (q : ℝ)) ≤ -(r * (A * t)) := by
      have := mul_le_mul_of_nonneg_left hqgt hr.le
      linarith
    have hK' : Real.exp (Real.log K) = K := Real.exp_log (by linarith)
    have hkey : Real.log K + -(r * (A * t)) ≤ -(t ^ (1 : ℝ)) := by
      rw [Real.rpow_one]
      have hexpand : r * (A * t) = (1 + Real.log K) * t := by
        rw [show r * (A * t) = r * A * t by ring, hrA]
      rw [hexpand]
      nlinarith [mul_le_mul_of_nonneg_right ht hlogK]
    calc K * Real.exp (-(r * (q : ℝ)))
        ≤ K * Real.exp (-(r * (A * t))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hstep) (by linarith)
      _ = Real.exp (Real.log K + -(r * (A * t))) := by
          rw [Real.exp_add, hK']
      _ ≤ Real.exp (-(t ^ (1 : ℝ))) := Real.exp_le_exp.2 hkey
  exact hmono.trans (hbase.trans hexp)

/-- **Sharp expectation form.**  The `SubdiffusiveProcess.OGammaLE` carrier at the sharp
scale `4 (1 + log K) / r`. -/
theorem ogammaLE_one_depthObservable_sharp
    [IsProbabilityMeasure μ] {D : Ω → ℕ} (hD : Measurable D)
    {K r : ℝ} (hK : 1 ≤ K) (hr : 0 < r)
    (htail : ∀ q : ℕ, 0 < q →
      μ.real {omega | q < D omega} ≤ K * Real.exp (-(r * (q : ℝ)))) :
    SubdiffusiveProcess.OGammaLE μ 1 (depthGammaOneScaleSharp K r) (depthObservable D) := by
  have hbig := isBigO_gammaOne_depthObservable_sharp (μ := μ) D hK hr htail
  have hbridge :=
    SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (μ := μ)
      (σ := 1) (A := depthTailScaleSharp K r) (X := depthObservable D)
      zero_lt_one (depthTailScaleSharp_pos hK hr)
      (measurable_depthObservable hD) hbig
  have hscale : (4 : ℝ) ^ (1 : ℝ)⁻¹ * depthTailScaleSharp K r =
      depthGammaOneScaleSharp K r := by
    rw [inv_one, Real.rpow_one]
    rfl
  rwa [hscale] at hbridge

/-- `SubdiffusiveProcess.OGammaLE` is monotone in its scale on nonnegative observables:
enlarging the scale weakens the constraint.  Proof a clause whose
printed constant is larger than the constant produced by the proof route uses
exactly this step. -/
theorem ogammaLE_mono_scale {sigma A B : ℝ} {X : Ω → ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hAB : A ≤ B) (hXm : Measurable X)
    (hX : SubdiffusiveProcess.OGammaLE μ sigma A X) :
    SubdiffusiveProcess.OGammaLE μ sigma B X := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hpoint : ∀ omega : Ω,
      Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma) ≤
        Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma) := by
    intro omega
    have hmax : 0 ≤ max (X omega) 0 := le_max_right _ _
    have hinv : B⁻¹ ≤ A⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hA hAB
    have hle : B⁻¹ * max (X omega) 0 ≤ A⁻¹ * max (X omega) 0 :=
      mul_le_mul_of_nonneg_right hinv hmax
    exact Real.exp_le_exp.2
      (Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hB.le) hmax) hle hsigma.le)
  have hmeas : Measurable
      (fun omega => Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma)) :=
    (((measurable_const.mul (hXm.max measurable_const)).pow_const sigma)).exp
  have hint : Integrable
      (fun omega => Real.exp ((B⁻¹ * max (X omega) 0) ^ sigma)) μ := by
    refine hX.1.mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hpoint omega
  exact ⟨hint, le_trans (integral_mono hint hX.1 hpoint) hX.2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
