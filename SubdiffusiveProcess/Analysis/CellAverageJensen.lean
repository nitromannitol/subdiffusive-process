import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubcubeAveraging

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

namespace SubdiffusiveProcess



theorem averageOn_sub_averageOn_sq_le_double_setIntegral
    {d : ℕ} {Q P : Set (Homogenization.Vec d)} {f : Homogenization.Vec d → ℝ}
    (hQmeas : MeasurableSet Q) (hPmeas : MeasurableSet P)
    (hsub : P ⊆ Q) (hQtop : volume Q ≠ ⊤) (hPtop : volume P ≠ ⊤)
    (hQpos : 0 < (volume Q).toReal) (hPpos : 0 < (volume P).toReal)
    (hf : MemLp f 2 (volume.restrict Q)) :
    |SubdiffusiveProcess.CoarseGrainingVocab.averageOn P f -
        SubdiffusiveProcess.CoarseGrainingVocab.averageOn Q f| ^ 2 ≤
      ((volume P).toReal * (volume Q).toReal)⁻¹ *
        ∫ y in P, ∫ z in Q, |f y - f z| ^ 2 := by
  classical
  let p : ℝ := (volume P).toReal
  let q : ℝ := (volume Q).toReal
  let A : ℝ := averageOn P f
  let B : ℝ := averageOn Q f
  have hp : 0 < p := hPpos
  have hq : 0 < q := hQpos
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  letI : IsFiniteMeasure (volume.restrict P) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (lt_top_iff_ne_top.mpr hPtop)
  ⟩
  letI : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (lt_top_iff_ne_top.mpr hQtop)
  ⟩
  have hfQ : IntegrableOn f Q := hf.integrable (by norm_num)
  have hfQ2 : IntegrableOn (fun x => f x ^ 2) Q := hf.integrable_sq
  have hfP : IntegrableOn f P := hfQ.mono_set hsub
  have hfP2 : IntegrableOn (fun x => f x ^ 2) P := hfQ2.mono_set hsub
  have hPint : (∫ x in P, f x) = p * A := by
    dsimp [p, A]
    unfold averageOn volumeAverage
    field_simp
  have hQint : (∫ x in Q, f x) = q * B := by
    dsimp [q, B]
    unfold averageOn volumeAverage
    field_simp
  have hPint2 : (∫ x in P, f x ^ 2) =
      p * volumeAverage P (fun x => f x ^ 2) := by
    dsimp [p]
    unfold volumeAverage
    field_simp
  have hQint2 : (∫ x in Q, f x ^ 2) =
      q * volumeAverage Q (fun x => f x ^ 2) := by
    dsimp [q]
    unfold volumeAverage
    field_simp
  have hprod2 : Integrable
      (fun w : Homogenization.Vec d × Homogenization.Vec d =>
        (f w.1 - f w.2) ^ 2)
      ((volume.restrict P).prod (volume.restrict Q)) := by
    have hfst : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.1 ^ 2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfP2.comp_fst (volume.restrict Q)
    have hsnd : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.2 ^ 2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfQ2.comp_snd (volume.restrict P)
    have hcross : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.1 * f w.2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfP.mul_prod hfQ
    have heq : (fun w : Homogenization.Vec d × Homogenization.Vec d =>
        (f w.1 - f w.2) ^ 2) =
        (fun w => f w.1 ^ 2 - 2 * (f w.1 * f w.2) + f w.2 ^ 2) := by
      funext w
      ring
    rw [heq]
    exact (hfst.sub (hcross.const_mul 2)).add hsnd
  have hdouble :
      (∫ y in P, ∫ z in Q, |f y - f z| ^ 2) =
        ∫ w in P ×ˢ Q, (f w.1 - f w.2) ^ 2 ∂(volume.prod volume) := by
    symm
    rw [MeasureTheory.setIntegral_prod _]
    · simp only [sq_abs]
    · change Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d =>
          (f w.1 - f w.2) ^ 2)
        ((volume.prod volume).restrict (P ×ˢ Q))
      rw [← Measure.prod_restrict]
      exact hprod2
  have hprodI :
      ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) =
        (∫ x in P, f x ^ 2) * q + p * (∫ x in Q, f x ^ 2) -
          2 * ((∫ x in P, f x) * (∫ x in Q, f x)) := by
    have hfst : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.1 ^ 2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfP2.comp_fst (volume.restrict Q)
    have hsnd : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.2 ^ 2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfQ2.comp_snd (volume.restrict P)
    have hcross : Integrable
        (fun w : Homogenization.Vec d × Homogenization.Vec d => f w.1 * f w.2)
        ((volume.restrict P).prod (volume.restrict Q)) :=
      hfP.mul_prod hfQ
    have heq : (fun w : Homogenization.Vec d × Homogenization.Vec d =>
        (f w.1 - f w.2) ^ 2) =
        (fun w => (f w.1 ^ 2 - 2 * (f w.1 * f w.2)) + f w.2 ^ 2) := by
      funext w
      ring
    rw [heq]
    calc
      _ = (∫ w : Homogenization.Vec d × Homogenization.Vec d,
          f w.1 ^ 2 - 2 * (f w.1 * f w.2)
            ∂((volume.restrict P).prod (volume.restrict Q))) +
          ∫ w : Homogenization.Vec d × Homogenization.Vec d,
            f w.2 ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) :=
        integral_add (hfst.sub (hcross.const_mul 2)) hsnd
      _ = (∫ w : Homogenization.Vec d × Homogenization.Vec d,
          f w.1 ^ 2 ∂((volume.restrict P).prod (volume.restrict Q))) -
          2 * (∫ w : Homogenization.Vec d × Homogenization.Vec d,
            f w.1 * f w.2 ∂((volume.restrict P).prod (volume.restrict Q))) +
          ∫ w : Homogenization.Vec d × Homogenization.Vec d,
            f w.2 ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) := by
        rw [integral_sub hfst (hcross.const_mul 2), integral_const_mul]
      _ = _ := by
        have hfst' :
            (∫ w : Homogenization.Vec d × Homogenization.Vec d,
              f w.1 ^ 2 ∂((volume.restrict P).prod (volume.restrict Q))) =
              q * (∫ x in P, f x ^ 2) := by
          simpa [q, measureReal_def, smul_eq_mul] using
            (integral_fun_fst (μ := volume.restrict P) (ν := volume.restrict Q)
              (fun x : Homogenization.Vec d => f x ^ 2))
        have hsnd' :
            (∫ w : Homogenization.Vec d × Homogenization.Vec d,
              f w.2 ^ 2 ∂((volume.restrict P).prod (volume.restrict Q))) =
              p * (∫ x in Q, f x ^ 2) := by
          simpa [p, measureReal_def, smul_eq_mul] using
            (integral_fun_snd (μ := volume.restrict P) (ν := volume.restrict Q)
              (fun x : Homogenization.Vec d => f x ^ 2))
        have hcross' :
            (∫ w : Homogenization.Vec d × Homogenization.Vec d,
              f w.1 * f w.2 ∂((volume.restrict P).prod (volume.restrict Q))) =
              (∫ x in P, f x) * (∫ x in Q, f x) := by
          exact integral_prod_mul f f
        rw [hfst', hsnd', hcross']
        ring
  have hprodI' :
      ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) =
        p * q * (volumeAverage P (fun x => f x ^ 2) +
          volumeAverage Q (fun x => f x ^ 2) - 2 * A * B) := by
    rw [hprodI, hPint2, hQint2, hPint, hQint]
    ring
  have hvarP : 0 ≤ volumeAverage P (fun x => (f x - A) ^ 2) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volumeAverage_sq_nonneg P
      (fun x => f x - A)
  have hvarQ : 0 ≤ volumeAverage Q (fun x => (f x - B) ^ 2) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volumeAverage_sq_nonneg Q
      (fun x => f x - B)
  have hvarP' := SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volumeAverage_sub_const_sq
    hPmeas hPpos hPtop hfP hfP2 A
  have hvarQ' := SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volumeAverage_sub_const_sq
    hQmeas hQpos hQtop hfQ hfQ2 B
  have hA : volumeAverage P f = A := by rfl
  have hB : volumeAverage Q f = B := by rfl
  rw [hA] at hvarP'
  rw [hB] at hvarQ'
  have hnorm :
      (A - B) ^ 2 ≤ volumeAverage P (fun x => f x ^ 2) +
        volumeAverage Q (fun x => f x ^ 2) - 2 * A * B := by
    nlinarith [hvarP, hvarQ, hvarP', hvarQ', hA, hB]
  have hscaled :
      (p * q) * (A - B) ^ 2 ≤
        ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) := by
    rw [hprodI']
    exact mul_le_mul_of_nonneg_left hnorm (le_of_lt (mul_pos hp hq))
  have hfinalprod :
      (A - B) ^ 2 ≤ (p * q)⁻¹ *
        ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ (mul_pos hp hq)).2
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hdoubleprod :
      (∫ y in P, ∫ z in Q, |f y - f z| ^ 2) =
        ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) := by
    calc
      (∫ y in P, ∫ z in Q, |f y - f z| ^ 2) =
          ∫ w in P ×ˢ Q, (f w.1 - f w.2) ^ 2 ∂(volume.prod volume) := hdouble
      _ = ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) := by
        rw [← Measure.prod_restrict]
  have hfinalprod' := hfinalprod
  dsimp [A, B, p, q] at hfinalprod'
  calc
    |averageOn P f - averageOn Q f| ^ 2 =
        (averageOn P f - averageOn Q f) ^ 2 := by rw [sq_abs]
    _ ≤ ((volume P).toReal * (volume Q).toReal)⁻¹ *
        ∫ w : Homogenization.Vec d × Homogenization.Vec d,
          (f w.1 - f w.2) ^ 2 ∂((volume.restrict P).prod (volume.restrict Q)) :=
      hfinalprod'
    _ = ((volume P).toReal * (volume Q).toReal)⁻¹ *
        (∫ y in P, ∫ z in Q, |f y - f z| ^ 2) := by
      rw [hdoubleprod]

end SubdiffusiveProcess
