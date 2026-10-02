import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowBoundaryTouches
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.WindowGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalPoincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PhysicalRadiusRecurrence
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverNormalized




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The window datum energy is priced by the two printed datum budgets.**

`σ ∫_U ‖∇h‖²` is at most a dimension-only multiple of `|U|` times the four
printed budgets, on the boundary branch. -/
theorem exists_setIntegral_vecNormSq_grad_le_windowBudgets (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 / 4 →
      ∀ (L m n : ℕ), (n : ℤ) + 2 ≤ (m : ℤ) →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ cube d (m : ℤ) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x) s h.grad ≠ ∞ →
        BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x) (cube d (m : ℤ)) →
        tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z) *
            (∫ p in truncatedCube d (m : ℤ) (n : ℤ) x, vecNormSq (h.grad p)) ≤
          C * (volume (truncatedCube d (m : ℤ) (n : ℤ) x)).toReal *
            harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
  classical
  refine ⟨2 * ((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d + 1), by positivity, ?_⟩
  intro M s hs0 hs4 L m n hnm z x omega hx u h g hfrac htouch
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hUdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  have hsigma0 : 0 ≤ sigma :=
    Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _
  have hUmeas : MeasurableSet U :=
    Section6ExcessDecay.measurableSet_truncatedCube d _ _ _
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx (by omega)
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ∞ := (ENNReal.toReal_ne_zero.mp hUpos.ne').2
  have hU0' : 0 < volume U := pos_iff_ne_zero.mpr hU0
  have hUlow : ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d ≤ (volume U).toReal :=
    (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hx (by omega)).1
  set Uv : ℝ := (volume U).toReal with hUvdef
  set Fr : ℝ := (fractionalSeminormOn U s h.grad).toReal with hFrdef
  have hFr0 : 0 ≤ Fr := ENNReal.toReal_nonneg
  have hh2 : MemLp (fun q ↦ HilbertVec.ofVec (h.grad q)) 2
      (volume.restrict U) := memLp_hilbertGradient_truncatedCube h
  have hdiam : ∀ p ∈ U, ∀ q ∈ U, euclideanNorm (p - q) ≤ (d : ℝ) * (3 : ℝ) ^ (n : ℤ) :=
    euclideanDiameter_truncatedCube_le
  -- the fractional Poincare comparison on the window itself
  have hVraw := vectorNormalizedL2On_subwindow_le_mean_add_fractional
    (W' := U) (W := U) (s := s) (D := (d : ℝ) * (3 : ℝ) ^ (n : ℤ))
    (f := h.grad) Set.Subset.rfl hUmeas hU0' hUtop hUpos hs0 hdiam hh2 hfrac
  rw [div_self hUpos.ne', Real.sqrt_one, one_mul] at hVraw
  set MF : ℝ := ((d : ℝ) * (3 : ℝ) ^ (n : ℤ)) ^ (s + (d : ℝ) / 2) *
    s ^ (-(1 / 2 : ℝ)) * Uv ^ (-(1 / 2 : ℝ)) * Fr with hMFdef
  set A : ℝ := euclideanNorm (averageVecOn U h.grad) with hAdef
  have hV : vectorNormalizedL2On U h.grad ≤ MF + A := hVraw
  have hMF0 : 0 ≤ MF := by
    rw [hMFdef]
    have h1 : (0 : ℝ) ≤ ((d : ℝ) * (3 : ℝ) ^ (n : ℤ)) ^ (s + (d : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ s ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have h3 : (0 : ℝ) ≤ Uv ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hUpos.le _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) hFr0
  have hA0 : 0 ≤ A := euclideanNorm_nonneg _
  have hV0 : 0 ≤ vectorNormalizedL2On U h.grad :=
    Real.sqrt_nonneg _
  have hVsq : vectorNormalizedL2On U h.grad ^ 2 ≤ 2 * MF ^ 2 + 2 * A ^ 2 := by
    have hsq := pow_le_pow_left₀ hV0 hV 2
    nlinarith [sq_nonneg (MF - A)]
  -- the window integral as volume times the normalized square
  have hint : (∫ p in U, vecNormSq (h.grad p)) =
      Uv * vectorNormalizedL2On U h.grad ^ 2 := by
    rw [hUvdef, vectorNormalizedL2On]
    calc ∫ p in U, vecNormSq (h.grad p)
        = ∫ p in U, euclideanNorm (h.grad p) ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall fun p ↦
            (euclideanNorm_sq (h.grad p)).symm)
      _ = (volume U).toReal *
            normalizedL2On U (fun p ↦ euclideanNorm (h.grad p)) ^ 2 :=
          Section6HolderInterior.setIntegral_sq_eq_volume_mul_normalizedL2On_sq hUtop
  -- the two printed datum budgets
  set Bud2 : ℝ := sigma * vecNormSq (averageVecOn U h.grad) with hBud2def
  set Bud4 : ℝ := sigma * s ^ (-4 : ℝ) *
    ((3 : ℝ) ^ (2 * s * (n : ℝ))) * Fr ^ 2 with hBud4def
  have hA2 : A ^ 2 = vecNormSq (averageVecOn U h.grad) := by
    rw [hAdef, euclideanNorm_sq]
  -- the mean-fluctuation term against the fractional budget
  set Dn : ℝ := (d : ℝ) * (3 : ℝ) ^ (n : ℤ) with hDndef
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have hDpos : (0 : ℝ) < Dn := by rw [hDndef]; positivity
  set R : ℝ := (3 : ℝ) ^ (2 * s * (n : ℝ)) with hRdef
  have hR0 : (0 : ℝ) < R := Real.rpow_pos_of_pos (by norm_num) _
  set Z : ℝ := s ^ (-1 : ℝ) with hZdef
  set Z' : ℝ := s ^ (-4 : ℝ) with hZ'def
  have hZ0 : (0 : ℝ) < Z := Real.rpow_pos_of_pos hs0 _
  have hZ'0 : (0 : ℝ) < Z' := Real.rpow_pos_of_pos hs0 _
  set X : ℝ := Dn ^ (2 * s) with hXdef
  have hX0 : (0 : ℝ) < X := Real.rpow_pos_of_pos hDpos _
  set Y : ℝ := Dn ^ d * Uv⁻¹ with hYdef
  have hY0 : (0 : ℝ) ≤ Y := by rw [hYdef]; positivity
  have hMFsq_eq : MF ^ 2 = X * Y * Z * Fr ^ 2 := by
    have hpow : (Dn ^ (s + (d : ℝ) / 2)) ^ 2 =
        X * Dn ^ (d : ℝ) := by
      rw [hXdef, ← Real.rpow_natCast (Dn ^ (s + (d : ℝ) / 2)) 2,
        ← Real.rpow_mul hDpos.le, ← Real.rpow_add hDpos]
      congr 1
      push_cast
      ring
    have hnat : Dn ^ (d : ℝ) = Dn ^ d := Real.rpow_natCast Dn d
    have hsinv : (s ^ (-(1 / 2 : ℝ))) ^ 2 = Z := by
      rw [hZdef, ← Real.rpow_natCast (s ^ (-(1 / 2 : ℝ))) 2,
        ← Real.rpow_mul hs0.le]
      norm_num
    have hUinv : (Uv ^ (-(1 / 2 : ℝ))) ^ 2 = Uv⁻¹ := by
      rw [← Real.rpow_natCast (Uv ^ (-(1 / 2 : ℝ))) 2,
        ← Real.rpow_mul hUpos.le]
      norm_num
      exact Real.rpow_neg_one Uv
    rw [hMFdef, hYdef]
    calc (Dn ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            Uv ^ (-(1 / 2 : ℝ)) * Fr) ^ 2
        = (Dn ^ (s + (d : ℝ) / 2)) ^ 2 *
            (s ^ (-(1 / 2 : ℝ))) ^ 2 *
            (Uv ^ (-(1 / 2 : ℝ))) ^ 2 * Fr ^ 2 := by ring
      _ = (X * Dn ^ (d : ℝ)) * Z * Uv⁻¹ * Fr ^ 2 := by
          rw [hpow, hsinv, hUinv]
      _ = X * (Dn ^ d * Uv⁻¹) * Z * Fr ^ 2 := by rw [hnat]; ring
  have hXle : X ≤ (d : ℝ) * R := by
    have hsplit : X = (d : ℝ) ^ (2 * s) *
        ((3 : ℝ) ^ (n : ℤ)) ^ (2 * s) := by
      rw [hXdef, hDndef]
      exact Real.mul_rpow (by linarith) h3n.le
    have hthree : ((3 : ℝ) ^ (n : ℤ)) ^ (2 * s) = R := by
      have hz : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ (n : ℕ) := by
        rw [zpow_natCast]
      rw [hz, hRdef, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have hdle : (d : ℝ) ^ (2 * s) ≤ (d : ℝ) := by
      have h1 : (d : ℝ) ^ (2 * s) ≤ (d : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
      rwa [Real.rpow_one] at h1
    rw [hsplit, hthree]
    exact mul_le_mul_of_nonneg_right hdle hR0.le
  have hYle : Y ≤ (d : ℝ) ^ d * (9 : ℝ) ^ d := by
    have hlowpos : (0 : ℝ) < ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := by positivity
    have hinv : Uv⁻¹ ≤ (((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d)⁻¹ := by
      have hone := one_div_le_one_div_of_le hlowpos hUlow
      simpa only [one_div] using hone
    have hDpow : Dn ^ d = (d : ℝ) ^ d * ((3 : ℝ) ^ (n : ℤ)) ^ d := by
      rw [hDndef, mul_pow]
    have hlow_eq : ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d =
        ((3 : ℝ) ^ (n : ℤ)) ^ d / (9 : ℝ) ^ d := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), div_pow]
      norm_num
    calc Y = Dn ^ d * Uv⁻¹ := by rw [hYdef]
      _ ≤ Dn ^ d * (((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (d : ℝ) ^ d * ((3 : ℝ) ^ (n : ℤ)) ^ d *
            (((3 : ℝ) ^ (n : ℤ)) ^ d / (9 : ℝ) ^ d)⁻¹ := by
          rw [hDpow, hlow_eq]
      _ = (d : ℝ) ^ d * (9 : ℝ) ^ d := by
          have hne : ((3 : ℝ) ^ (n : ℤ)) ^ d ≠ 0 := by positivity
          field_simp
  have hZle : Z ≤ Z' := by
    rw [hZdef, hZ'def]
    exact Real.rpow_le_rpow_of_exponent_ge hs0 (by linarith) (by norm_num)
  have hMFsq : sigma * MF ^ 2 ≤ ((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d) * Bud4 := by
    have hchain : X * Y * Z * Fr ^ 2 ≤
        ((d : ℝ) * R) * ((d : ℝ) ^ d * (9 : ℝ) ^ d) * Z' * Fr ^ 2 := by
      have hdR : (0 : ℝ) ≤ (d : ℝ) * R :=
        mul_nonneg (Nat.cast_nonneg d) hR0.le
      have h1 : X * Y ≤ ((d : ℝ) * R) * ((d : ℝ) ^ d * (9 : ℝ) ^ d) :=
        mul_le_mul hXle hYle hY0 hdR
      have h2 : X * Y * Z ≤
          ((d : ℝ) * R) * ((d : ℝ) ^ d * (9 : ℝ) ^ d) * Z' :=
        mul_le_mul h1 hZle hZ0.le (mul_nonneg hdR (by positivity))
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have hstep := mul_le_mul_of_nonneg_left (hMFsq_eq ▸ hchain) hsigma0
    refine hstep.trans (le_of_eq ?_)
    rw [hBud4def, hZ'def, hRdef, hFrdef]
    ring
  -- assemble
  have hfinal : sigma * (∫ p in U, vecNormSq (h.grad p)) ≤
      (2 * ((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d + 1)) * Uv * (Bud2 + Bud4) := by
    rw [hint]
    have hstep : sigma * (Uv * vectorNormalizedL2On U h.grad ^ 2) ≤
        sigma * (Uv * (2 * MF ^ 2 + 2 * A ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hsigma0
      exact mul_le_mul_of_nonneg_left hVsq hUpos.le
    refine hstep.trans ?_
    have hexpand : sigma * (Uv * (2 * MF ^ 2 + 2 * A ^ 2)) =
        2 * Uv * (sigma * MF ^ 2) + 2 * Uv * (sigma * A ^ 2) := by ring
    rw [hexpand]
    have hB2 : sigma * A ^ 2 = Bud2 := by rw [hBud2def, hA2]
    have hBud40 : 0 ≤ Bud4 := by
      rw [hBud4def]
      exact mul_nonneg (mul_nonneg (mul_nonneg hsigma0 hZ'0.le) hR0.le) (sq_nonneg _)
    have hBud20 : 0 ≤ Bud2 := by
      rw [hBud2def]; exact mul_nonneg hsigma0 (vecNormSq_nonneg _)
    have h1 : 2 * Uv * (sigma * MF ^ 2) ≤
        2 * Uv * (((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d) * Bud4) :=
      mul_le_mul_of_nonneg_left hMFsq (by positivity)
    rw [hB2]
    have hextra : (0 : ℝ) ≤ 2 * Uv *
        (((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d) * Bud2 + Bud4) :=
      mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by positivity) hBud20) hBud40)
    have hid : (2 * ((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d + 1)) * Uv * (Bud2 + Bud4)
        = 2 * Uv * (((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d) * Bud4) + 2 * Uv * Bud2
          + 2 * Uv * (((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d) * Bud2 + Bud4) := by
      ring
    rw [hid]
    linarith [h1, hextra]
  refine hfinal.trans ?_
  -- the printed budgets
  have hbudEq : harmonicPhysicalFourBudgets M L m n z x omega s u h g =
      sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
          normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
        (if BoundaryTouches U (cube d (m : ℤ)) then Bud2 else 0) +
        (Real.rpow s (-12 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ (2 * s * (n : ℝ)) *
          (fractionalSeminormOn U s g).toReal ^ 2) +
        (if BoundaryTouches U (cube d (m : ℤ)) then Bud4 else 0) := rfl
  have hleg1 : (0 : ℝ) ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
      normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 :=
    mul_nonneg (mul_nonneg hsigma0 (by positivity)) (sq_nonneg _)
  have hleg3 : (0 : ℝ) ≤ Real.rpow s (-12 : ℝ) * sigma⁻¹ *
      (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s g).toReal ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma0)) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hbud : Bud2 + Bud4 ≤
      harmonicPhysicalFourBudgets M L m n z x omega s u h g := by
    rw [hbudEq, if_pos htouch, if_pos htouch]
    linarith
  have hCpos : (0 : ℝ) ≤ 2 * ((d : ℝ) ^ (d + 1) * (9 : ℝ) ^ d + 1) := by positivity
  exact mul_le_mul_of_nonneg_left hbud (mul_nonneg hCpos hUpos.le)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
