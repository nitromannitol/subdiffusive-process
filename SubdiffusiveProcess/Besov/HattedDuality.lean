import SubdiffusiveProcess.Besov.HattedNorm

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal ContDiff
noncomputable section
variable {d : ℕ} [NeZero d]

theorem hHatNorm_ne_top (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    hHatNorm Q F ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hHatNorm_le_sum_circ Q F hF)

theorem abs_pairing_le_hHatNorm_mul_smoothTestSize (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (φ : Vec d → Vec d) (hφ : ContDiff ℝ ∞ φ) :
    |∫ x, vecDot (F x) (φ x) ∂normalizedCubeMeasure Q| ≤
      (hHatNorm Q F).toReal * smoothTestSize Q φ := by
  have hN := hHatNorm_ne_top Q F hF
  have hD : 0 ≤ smoothTestSize Q φ := by
    unfold smoothTestSize smoothTestGradientSize smoothTestValueSize
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg
      (inv_nonneg.mpr (by unfold cubeScaleFactor; positivity)) (Real.sqrt_nonneg _))
  have hquot : ENNReal.ofReal |∫ x, vecDot (F x) (φ x) ∂normalizedCubeMeasure Q| /
      ENNReal.ofReal (smoothTestSize Q φ) ≤ hHatNorm Q F :=
    le_iSup_of_le ⟨φ, hφ⟩ le_rfl
  have hmul := (ENNReal.div_le_iff_le_mul (Or.inr hN)
    (Or.inl ENNReal.ofReal_ne_top)).mp hquot
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hN ENNReal.ofReal_ne_top) hmul
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal hD] using hr

theorem contDiff_single_field (i : Fin d) (ψ : Vec d → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun x => (Pi.single i (ψ x) : Vec d)) := by
  classical
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k = i
  · simpa [Pi.single_apply, hk] using hψ
  · simpa [Pi.single_apply, hk] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Vec d => (0 : ℝ)))

theorem fderiv_single_field (i j k : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (x : Vec d) :
    fderiv ℝ (fun y => (Pi.single i (ψ y) : Vec d)) x (Pi.single j 1) k =
      if k = i then fderiv ℝ ψ x (Pi.single j 1) else 0 := by
  classical
  have hs := contDiff_single_field i ψ hψ
  rw [fderiv_pi (fun l => ((contDiff_pi.mp hs l).differentiable (by simp)).differentiableAt)]
  simp only [ContinuousLinearMap.pi_apply]
  by_cases hk : k = i <;> simp [Pi.single_apply, hk]

theorem sqrt_sum_sq_le_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ ∑ i, a i := by
  calc
    Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt ((∑ i, a i) ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha i))
    _ = ∑ i, a i := Real.sqrt_sq (Finset.sum_nonneg fun i _ => ha i)

theorem smoothTestSize_single_le (Q : TriadicCube d) (i : Fin d)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    smoothTestSize Q (fun x => (Pi.single i (ψ x) : Vec d)) ≤
      (∑ j : Fin d, cubeLpNorm Q 2 (fun x => fderiv ℝ ψ x (Pi.single j 1))) +
        (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q 2 ψ := by
  classical
  have hs := contDiff_single_field i ψ hψ
  have hψmem : MemLp ψ 2 (normalizedCubeMeasure Q) := by
    simpa using smoothCoordinate_memLp Q _ hs i
  have hdermem : ∀ j : Fin d, MemLp (fun x => fderiv ℝ ψ x (Pi.single j 1)) 2
      (normalizedCubeMeasure Q) := by
    intro j
    simpa only [fderiv_single_field i j i ψ hψ, if_pos rfl] using smoothDerivative_memLp Q _ hs i j
  have hval : smoothTestValueSize Q (fun x => (Pi.single i (ψ x) : Vec d)) = cubeLpNorm Q 2 ψ := by
    unfold smoothTestValueSize
    have heq : (fun x => vecNormSq (Pi.single i (ψ x) : Vec d)) = fun x => ψ x ^ 2 := by
      funext x
      simp [vecNormSq, vecDot, Pi.single_apply, ← pow_two]
    rw [heq]
    rw [← cubeLpNorm_two_sq_eq_integral Q ψ hψmem]
    exact Real.sqrt_sq (cubeLpNorm_nonneg Q _ _)
  have hgrad : smoothTestGradientSize Q (fun x => (Pi.single i (ψ x) : Vec d)) ≤
      ∑ j : Fin d, cubeLpNorm Q 2 (fun x => fderiv ℝ ψ x (Pi.single j 1)) := by
    unfold smoothTestGradientSize
    have heq : (fun x => ∑ k : Fin d, ∑ j : Fin d,
        (fderiv ℝ (fun y => (Pi.single i (ψ y) : Vec d)) x (Pi.single j 1) k) ^ 2) =
        fun x => ∑ j : Fin d, (fderiv ℝ ψ x (Pi.single j 1)) ^ 2 := by
      funext x
      simp_rw [fderiv_single_field _ _ _ ψ hψ]
      simp
    rw [heq]
    rw [integral_finset_sum _ (fun j _ => (hdermem j).integrable_sq)]
    simp_rw [← cubeLpNorm_two_sq_eq_integral Q _ (hdermem _)]
    exact sqrt_sum_sq_le_sum _ (fun j => cubeLpNorm_nonneg Q _ _)
  unfold smoothTestSize
  rw [hval]
  exact add_le_add hgrad le_rfl

theorem abs_coordinate_pairing_smooth_le (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (i : Fin d) (ψ : Vec d → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    |∫ x, F x i * ψ x ∂normalizedCubeMeasure Q| ≤
      (hHatNorm Q F).toReal *
        ((∑ j : Fin d, cubeLpNorm Q 2 (fun x => fderiv ℝ ψ x (Pi.single j 1))) +
          (cubeScaleFactor Q)⁻¹ * cubeLpNorm Q 2 ψ) := by
  classical
  have h := abs_pairing_le_hHatNorm_mul_smoothTestSize Q F hF _
    (contDiff_single_field i ψ hψ)
  have heq : (fun x => vecDot (F x) ((Pi.single i (ψ x) : Vec d))) = fun x => F x i * ψ x := by
    funext x
    simp [vecDot, Pi.single_apply, mul_ite]
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (smoothTestSize_single_le Q i ψ hψ)
    ENNReal.toReal_nonneg)

end
end SubdiffusiveProcess.Besov
