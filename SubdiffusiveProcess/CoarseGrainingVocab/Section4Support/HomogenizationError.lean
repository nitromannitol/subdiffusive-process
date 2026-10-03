module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.InfinityOne

@[expose] public section

open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book

noncomputable section

/-!
# Section 4 support: localization of the paper homogenization error

This is the scalar `ENNReal` specialization of the one-cube comparison used in
the proof of `l.ellipticity.bound`.  The CoarseGraining theorem imported above
has the same geometric core but a different error carrier.

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Provider/ErrorComparison/OneCube.lean
-/

/-- Enlarging the root cube enlarges the descendant supremum in a fixed scale
response. -/
theorem paperMaxDescendantProbeAtScale_le_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k l : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ)
    (hR : R ∈ descendantsAtScale Q k) :
    paperMaxDescendantProbeAtScale R l a alpha ≤
      paperMaxDescendantProbeAtScale Q l a alpha := by
  unfold paperMaxDescendantProbeAtScale
  apply iSup_le
  intro S
  apply le_iSup_of_le
    (⟨S.1, mem_descendantsAtScale_trans hR S.2⟩ :
      {T : TriadicCube d // T ∈ descendantsAtScale Q l})
  exact le_rfl



theorem paperScaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k l : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ)
    (hR : R ∈ descendantsAtScale Q k) :
    paperScaleResponseAtScale R l .infinity a alpha ≤
      paperScaleResponseAtScale Q l .infinity a alpha := by
  unfold paperScaleResponseAtScale
  exact ENNReal.rpow_le_rpow
    (paperMaxDescendantProbeAtScale_le_of_mem_descendantsAtScale a alpha hR)
    (by norm_num)

/-- Paper display `e.bound.one.cube.by.mathcalE`: a descendant-cube error is
bounded by the root error with the exact geometric shift factor. -/
theorem paperHomogenizationErrorDefault_descendant_le
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) {s : ℝ}
    (hR : R ∈ descendantsAtScale Q k) :
    paperHomogenizationErrorDefault R R.scale s .infinity a alpha ≤
      ENNReal.ofReal (Real.rpow 3 (s * (Int.toNat (Q.scale - k) : ℝ))) *
        paperHomogenizationErrorDefault Q Q.scale s .infinity a alpha := by
  unfold paperHomogenizationErrorDefault paperHomogenizationError
    paperHomogenizationErrorFinite
  simp only [one_div, inv_one, ENNReal.rpow_one]
  let h : ℕ := Int.toNat (Q.scale - k)
  let factorR : ℝ := Real.rpow 3 (s * (h : ℝ))
  let factor : ℝ≥0∞ := ENNReal.ofReal factorR
  let fQ : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Ch02.geometricWeight s 1 n) *
      paperScaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a alpha
  let fR : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Ch02.geometricWeight s 1 n) *
      paperScaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a alpha
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hfactorR0 : 0 ≤ factorR := by
    dsimp [factorR]
    exact Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale : R.scale - (n : ℤ) =
        Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hresp :
        paperScaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a alpha ≤
          paperScaleResponseAtScale Q
            (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a alpha := by
      simpa [hscale] using
        paperScaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
          a alpha hR
    have hshift : ENNReal.ofReal (Ch02.geometricWeight s 1 n) =
        factor * ENNReal.ofReal (Ch02.geometricWeight s 1 (n + h)) := by
      rw [Ch02.geometricWeight_eq_old, Ch02.geometricWeight_eq_old,
        Homogenization.geometricWeight_one_shift (s := s) h n,
        ENNReal.ofReal_mul hfactorR0]
    calc
      fR n = factor *
          (ENNReal.ofReal (Ch02.geometricWeight s 1 (n + h)) *
            paperScaleResponseAtScale R (R.scale - (n : ℤ))
              .infinity a alpha) := by
        dsimp [fR]
        rw [hshift]
        ac_rfl
      _ ≤ factor *
          (ENNReal.ofReal (Ch02.geometricWeight s 1 (n + h)) *
            paperScaleResponseAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a alpha) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hresp)
      _ = factor * fQ (n + h) := by rfl
  have hsumLe : (∑' n, fR n) ≤ ∑' n, factor * fQ (n + h) :=
    ENNReal.tsum_le_tsum hterm
  have htailLe : (∑' n, fQ (n + h)) ≤ ∑' n, fQ n := by
    exact ENNReal.summable.tsum_le_tsum_of_inj
      (fun n : ℕ => n + h)
      (fun _ _ hab => Nat.add_right_cancel hab)
      (fun _ _ => zero_le)
      (fun _ => le_rfl)
      ENNReal.summable
  change (∑' n, fR n) ≤ factor * ∑' n, fQ n
  calc
    (∑' n, fR n) ≤ ∑' n, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n, fQ (n + h) := ENNReal.tsum_mul_left
    _ ≤ factor * ∑' n, fQ n := mul_le_mul' le_rfl htailLe

/-- Uniform version of the one-cube comparison over all scale-`k`
descendants. -/
theorem iSup_paperHomogenizationErrorDefault_descendantsAtScale_le
    {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (a : Ch02.TriadicCoeffFamily d) (alpha s : ℝ) :
    (⨆ R : {R : TriadicCube d // R ∈ descendantsAtScale Q k},
      paperHomogenizationErrorDefault R k s .infinity a alpha) ≤
        ENNReal.ofReal (Real.rpow 3 (s * (((Q.scale - k).toNat : ℕ) : ℝ))) *
          paperHomogenizationErrorDefault Q Q.scale s .infinity a alpha := by
  apply iSup_le
  intro R
  have hscale : R.1.scale = k :=
    descendant_scale_eq_of_mem_descendantsAtScale R.2
  have hbound := paperHomogenizationErrorDefault_descendant_le
    a alpha (s := s) R.2
  simpa only [hscale] using hbound

/-- Integer-cast form of the uniform one-cube comparison. -/
theorem iSup_paperHomogenizationErrorDefault_descendantsAtScale_le_rpow_sub
    {d : ℕ} (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (alpha s : ℝ) :
    (⨆ R : {R : TriadicCube d // R ∈ descendantsAtScale Q k},
      paperHomogenizationErrorDefault R k s .infinity a alpha) ≤
        ENNReal.ofReal (Real.rpow 3 (s * ((Q.scale - k : ℤ) : ℝ))) *
          paperHomogenizationErrorDefault Q Q.scale s .infinity a alpha := by
  have hcast : ((((Q.scale - k).toNat : ℕ) : ℝ)) =
      ((Q.scale - k : ℤ) : ℝ) := by
    have hz : (((Q.scale - k).toNat : ℕ) : ℤ) = Q.scale - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hk)
    exact_mod_cast hz
  simpa [hcast] using
    iSup_paperHomogenizationErrorDefault_descendantsAtScale_le
      Q (k := k) a alpha s

end

end SubdiffusiveProcess.CoarseGrainingVocab
