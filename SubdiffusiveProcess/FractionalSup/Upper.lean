module

public import SubdiffusiveProcess.FractionalSup.SupBound

@[expose] public section

/-!
# The upper Stampacchia bound
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalSup

variable {d : ℕ}

open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

/-- **One Stampacchia step.** -/
theorem fractionalSup_step [NeZero d] (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {CS : ℝ} (hCS : 0 < CS)
    (hemb : ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (critExp d s))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ (critExp d s)) ^ (((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ)) ≤
          CS * cubeFractionalSqNorm hd z r hr s v)
    (hfin : ∀ Ψ : SobolevData (centeredCube z r hr), Ψ ∈ killedSobolevGraph (centeredCube z r hr) →
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => Ψ.1) < ⊤)
    (a : PositiveCoefficient (centeredCube z r hr)) {K : ℝ} (hK : 0 < K)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr s (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) {Kf : ℝ} (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (b u : weakSobolevGraph (centeredCube z r hr)) {M : ℝ}
    (hbM : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      b.val.1 x ≤ M)
    (hsol : SolvesDirichlet a F b u) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun x => (max (u.val.1 x - (M + k)) 0) ^ (critExp d s))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (max (u.val.1 x - (M + k)) 0) ^ (critExp d s) ≤
      (CS * K * Kf) ^ (critExp d s) *
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).real
          {x | M + k < u.val.1 x} ^ (critExp d s - 1) := by
  classical
  have hQconv := isOpenBoundedConvexDomain_centeredCube z hr
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp2 := critExp_gt_two hd s.2.1 s.2.2
  have hp1 : 1 < critExp d s := by linarith
  have : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [centeredCube_coe_eq_ball]; exact measure_ball_lt_top.ne
  obtain ⟨Ψ, hΨk, hΨ1, hΨ2⟩ := exists_killed_positivePart hQconv u b hsol.1 (M + k)
    (hbM.mono fun x hx => by linarith)
  have hWmeas : Measurable (fun x => u.val.1 x) := (Lp.stronglyMeasurable u.val.1).measurable
  have hf0 : 0 ≤ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => max (u.val.1 x - (M + k)) 0 := Filter.Eventually.of_forall fun x => le_max_right _ _
  have hΨf : (Ψ.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => max (u.val.1 x - (M + k)) 0 := hΨ1
  have hsem := hfin Ψ hΨk
  have hfp : MemLp (fun x => max (u.val.1 x - (M + k)) 0) (ENNReal.ofReal (critExp d s))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hemb Ψ.1 hsem).1.ae_eq hΨf
  have hfL1 : Integrable (fun x => max (u.val.1 x - (M + k)) 0)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hfp.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  have hEne := fractionalSup_energy_identity a F b u hsol Ψ hΨk (M + k) hΨ2
  have hEF : sobolevCoefficientForm a Ψ Ψ ≤ Kf * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      max (u.val.1 x - (M + k)) 0 := by
    rw [hEne]
    exact integral_mul_le_of_bound hFm hFb hf0 hfL1 hΨf
  obtain ⟨-, henergy⟩ := fractionalSup_energy_chain hd s z r hr hCS hemb hK hKf Ψ.1 hsem
    (hcoer ⟨Ψ, hΨk⟩) _ hf0 hΨf hEF
  have hA : MeasurableSet {x | M + k < u.val.1 x} := measurableSet_lt measurable_const hWmeas
  have hsupp : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      x ∉ {x | M + k < u.val.1 x} → max (u.val.1 x - (M + k)) 0 = 0 := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    simp only [mem_ofPred_eq, not_lt] at hx
    exact max_eq_right (by linarith)
  refine ⟨?_, levelset_step _ hp1 hf0 hfp hA hsupp (mul_nonneg (mul_nonneg hCS.le hK.le) hKf)
    henergy⟩
  have hint := hfp.integrable_norm_rpow (p := ENNReal.ofReal (critExp d s))
    (by simp; linarith) (by simp)
  refine hint.congr ?_
  filter_upwards [hf0] with x hx
  rw [ENNReal.toReal_ofReal (by linarith), Real.norm_eq_abs, abs_of_nonneg hx]

/-- **Upper Stampacchia bound.** -/
theorem fractionalSup_upper [NeZero d] (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {CS : ℝ} (hCS : 0 < CS)
    (hemb : ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (critExp d s))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ (critExp d s)) ^ (((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ)) ≤
          CS * cubeFractionalSqNorm hd z r hr s v)
    (hfin : ∀ Ψ : SobolevData (centeredCube z r hr), Ψ ∈ killedSobolevGraph (centeredCube z r hr) →
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => Ψ.1) < ⊤)
    (a : PositiveCoefficient (centeredCube z r hr)) {K : ℝ} (hK : 0 < K)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr s (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) {Kf : ℝ} (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (b u : weakSobolevGraph (centeredCube z r hr)) {M : ℝ}
    (hbM : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      b.val.1 x ≤ M)
    (hsol : SolvesDirichlet a F b u) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : (CS * K * Kf) * (r ^ d) ^ ((critExp d s - 2) / critExp d s) *
      (2 : ℝ) ^ ((critExp d s - 1) / (critExp d s - 2)) ≤ δ) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      u.val.1 x ≤ M + δ := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp2 := critExp_gt_two hd s.2.1 s.2.2
  set p := critExp d s with hp
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) with hμ
  have : IsFiniteMeasure μ := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [centeredCube_coe_eq_ball]; exact measure_ball_lt_top.ne
  have hWmeas : Measurable (fun x => u.val.1 x) := (Lp.stronglyMeasurable u.val.1).measurable
  set Λ : ℝ := CS * K * Kf with hΛ
  have hΛ0 : 0 ≤ Λ := mul_nonneg (mul_nonneg hCS.le hK.le) hKf
  set φ : ℝ → ℝ := fun k => μ.real {x | M + k < u.val.1 x} with hφ
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => measureReal_nonneg
  have hmono : ∀ k h, 0 ≤ k → k ≤ h → φ h ≤ φ k := by
    intro k h _ hkh
    apply measureReal_mono _ (measure_ne_top μ _)
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    linarith
  have hstep : ∀ k h, 0 ≤ k → k < h → (h - k) ^ p * φ h ≤ Λ ^ p * φ k ^ (p - 1) := by
    intro k h hk hkh
    obtain ⟨hint, hle⟩ := fractionalSup_step hd s z r hr hCS hemb hfin a hK hcoer F hKf hFm hFb b u
      hbM hsol hk
    have hmk := markov_level μ (by linarith : 0 < p) (v := fun x => u.val.1 x - M) hkh.le
      (by simpa only [sub_sub] using hint)
    have hset : {x | h < u.val.1 x - M} = {x | M + h < u.val.1 x} := by
      ext x; simp only [mem_ofPred_eq]; constructor <;> intro hx <;> linarith
    rw [hset] at hmk
    simp only [sub_sub] at hmk
    exact hmk.trans hle
  have hV : μ.real Set.univ = r ^ d := by
    rw [Measure.real, hμ, Measure.restrict_apply_univ, ← Measure.real,
      centeredCube_coe_eq_ball, Measure.real, Real.volume_pi_ball z (by positivity),
      ENNReal.toReal_ofReal (by positivity), Fintype.card_fin]
    congr 1; ring
  have hφ00 : φ 0 ≤ r ^ d := by
    rw [← hV]; exact measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
  have hδα : Λ ^ p * φ 0 ^ ((p - 1) - 1) * (2 : ℝ) ^ (p * (p - 1) / ((p - 1) - 1)) ≤ δ ^ p := by
    have hp0 : 0 < p := by linarith
    have hm1 : (p - 1) - 1 = p - 2 := by ring
    rw [hm1]
    have hV0 : 0 ≤ (r ^ d) := by positivity
    calc Λ ^ p * φ 0 ^ (p - 2) * (2 : ℝ) ^ (p * (p - 1) / (p - 2))
        ≤ Λ ^ p * (r ^ d) ^ (p - 2) * (2 : ℝ) ^ (p * (p - 1) / (p - 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hφ0 0) hφ00 (by linarith)) (Real.rpow_nonneg hΛ0 _)
      _ = (Λ * (r ^ d) ^ ((p - 2) / p) * (2 : ℝ) ^ ((p - 1) / (p - 2))) ^ p := by
          rw [Real.mul_rpow (mul_nonneg hΛ0 (Real.rpow_nonneg hV0 _)) (by positivity),
            Real.mul_rpow hΛ0 (Real.rpow_nonneg hV0 _), ← Real.rpow_mul hV0,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 3 <;> field_simp
      _ ≤ δ ^ p := Real.rpow_le_rpow (by positivity) hδ0 hp0.le
  have hzero := stampacchia_iteration (φ := φ) hφ0 hmono (A := Λ ^ p) (α := p) (β := p - 1)
    (Real.rpow_nonneg hΛ0 _) (by linarith) (by linarith) hstep hδ hδα
  have hμ0 : μ {x | M + δ < u.val.1 x} = 0 := by
    have : μ.real {x | M + δ < u.val.1 x} = 0 := hzero
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ _)] at this
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ0] with x hx
  simpa using hx

end SubdiffusiveProcess.FractionalSup
