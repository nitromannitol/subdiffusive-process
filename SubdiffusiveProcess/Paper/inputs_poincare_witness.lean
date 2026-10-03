module

public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.inputs_poincare_negative_finite
public import SubdiffusiveProcess.Paper.inputs_poincare_negative_endpoint
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.Paper.inputs_poincare_centered_representative
public import SubdiffusiveProcess.Paper.inputs_poincare_gradient
public import SubdiffusiveProcess.Paper.inputs_poincare_detach
public import SubdiffusiveProcess.Paper.inputs_poincare_mean_zero
public import SubdiffusiveProcess.Paper.inputs_poincare_killed
@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

lemma aux_inputs_poincare_witness_sup_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    0 ≤ sSup (Set.range f) := by
  by_cases hb : BddAbove (Set.range f)
  · exact (hf 0).trans (le_csSup hb ⟨0, rfl⟩)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma aux_inputs_poincare_witness_paper_nonneg {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s : ℝ) (hs : 0 ≤ s)
    (q : Homogenization.Book.Ch02.MultiscaleExponent) (F : Homogenization.Vec d → Homogenization.Vec d) :
    0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q s q F := by
  cases q with
  | finite q =>
    exact mul_nonneg (Real.rpow_nonneg hs _) (aux_inputs_poincare_witness_sup_nonneg _
      (fun N => Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite_nonneg Q s q N F))
  | infinity =>
    exact aux_inputs_poincare_witness_sup_nonneg _
      (fun j => Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm_nonneg Q s F j)

noncomputable def aux_inputs_poincare_witness_grad (d : ℕ) : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    SobolevData (centeredCube z r hr) → ℝ → ℝ≥0∞ → ℝ) :=
  fun z r hr u s q => |r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
    (Homogenization.originCube d 0) s (if q = ⊤ then .infinity else .finite q.toReal)
    (fun x i => u.2 i (fun j => z j + r * x j))|

lemma aux_inputs_poincare_witness_grad_eq (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : SobolevData (centeredCube z r hr)) (s : ℝ) (hs : 0 ≤ s) (q : ℝ≥0∞) :
    aux_inputs_poincare_witness_grad d z r hr u s q =
      r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s (if q = ⊤ then .infinity else .finite q.toReal)
        (fun x i => u.2 i (fun j => z j + r * x j)) := by
  exact abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _)
    (aux_inputs_poincare_witness_paper_nonneg _ _ hs _ _))

noncomputable def aux_inputs_poincare_witness_pos (d : ℕ) (hd : 2 ≤ d) : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    DomainL2 (centeredCube z r hr) → ℝ → ℝ) :=
  fun z r hr v s => r ^ (s - 1) * (iSup (fun j : ℕ =>
    Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
      (fun x => v (fun i => z i + r * x i))
      (inputs_poincare_positive_integrable d hd z r hr v) j)).toReal

noncomputable def aux_inputs_poincare_witness_css (s : ℝ) (q : ℝ≥0∞) : ℝ :=
  if 0 < s ∧ 1 ≤ q then SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s
    (if q = ⊤ then .infinity else .finite q.toReal)
  else SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 .infinity

lemma aux_inputs_poincare_witness_css_pos (s : ℝ) (q : ℝ≥0∞) :
    0 < aux_inputs_poincare_witness_css s q := by
  unfold aux_inputs_poincare_witness_css
  by_cases hv : 0 < s ∧ 1 ≤ q
  · rw [if_pos hv]
    by_cases htop : q = ⊤
    · simp [htop, SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor]
    · have hq : 1 ≤ q.toReal :=
        (ENNReal.toReal_le_toReal (by norm_num) htop).mpr hv.2
      simp only [htop, if_false, SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor]
      apply Real.rpow_pos_of_pos
      exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hv.1) (lt_of_lt_of_le zero_lt_one hq)))
  · rw [if_neg hv]
    norm_num [SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor]

theorem inputs_poincare_witness (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    (Nonempty (Paper.in_poincare d hd Jc)) := by
  classical
  obtain ⟨CD, hCD, hfinite, hDraw⟩ := inputs_poincare_detach d hd Jc
  obtain ⟨CM, hCM, hMraw⟩ := inputs_poincare_mean_zero d hd Jc
  obtain ⟨CK, hCK, hKraw⟩ := inputs_poincare_killed d hd Jc
  let C := CD + CM + CK
  have hC : 0 < C := by dsimp [C]; linarith
  have hCDle : CD ≤ C := by dsimp [C]; linarith
  have hCMle : CM ≤ C := by dsimp [C]; linarith
  have hCKle : CK ≤ C := by dsimp [C]; linarith
  let besovGradSeminorm := aux_inputs_poincare_witness_grad d
  let besovSeminorm := aux_inputs_poincare_witness_pos d hd
  let cssPow := aux_inputs_poincare_witness_css
  have hg_nonneg : ∀ z r hr u s q, 0 ≤ besovGradSeminorm z r hr u s q := by
    intro z r hr u s q; exact abs_nonneg _
  have hG : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ (q : ℝ≥0∞), 1 ≤ q →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      r ^ (-s) * besovGradSeminorm z r hr (u : SobolevData _) s q ≤
        cssPow s q * (Jc.lam z r hr a z r s q) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))) := by
    intro z r hr a s hs q hq u
    have hv : 0 < s ∧ 1 ≤ q := ⟨hs.1, hq⟩
    simp only [besovGradSeminorm, cssPow, aux_inputs_poincare_witness_grad_eq d z r hr _ s hs.1.le q,
      aux_inputs_poincare_witness_css, if_pos hv]
    exact inputs_poincare_gradient d hd Jc z r hr a s hs q hq u
  have hD : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      besovSeminorm z r hr (u : SobolevData (centeredCube z r hr)).1 s ≤
        C * besovGradSeminorm z r hr (u : SobolevData _) s 1) := by
    intro z r hr s hs u
    have h := hDraw z r hr s hs u
    change besovSeminorm z r hr _ s ≤ CD * _ at h
    dsimp only at h
    rw [← aux_inputs_poincare_witness_grad_eq d z r hr _ s hs.1.le 1] at h
    exact h.trans (mul_le_mul_of_nonneg_right hCDle (hg_nonneg z r hr _ s 1))
  have hM : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : meanZeroSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))) := by
    intro z r hr a u
    have he : 0 ≤ normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData _)) := Real.sqrt_nonneg _
    have hl : 0 ≤ (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_nonneg (Jc.lam_pos z r hr a z r 1 1).le _
    exact (hMraw z r hr a u).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCMle hr.le) hl) he)
  have hK : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : killedSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))) := by
    intro z r hr a u
    have he : 0 ≤ normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData _)) := Real.sqrt_nonneg _
    have hl : 0 ≤ (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_nonneg (Jc.lam_pos z r hr a z r 1 1).le _
    exact (hKraw z r hr a u).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCKle hr.le) hl) he)
  refine ⟨{
    besovGradSeminorm := besovGradSeminorm
    besovGradSeminorm_nonneg := hg_nonneg
    besovSeminorm := besovSeminorm
    besovSeminorm_nonneg := ?_
    cssPow := cssPow
    cssPow_pos := aux_inputs_poincare_witness_css_pos
    C := C
    C_pos := hC
    cssPow_eq := ?_
    besovGradSeminorm_eq := ?_
    negativeBesovVectorPartialNormFinite_bddAbove := inputs_poincare_negative_finite d hd
    negativeBesovVectorDepthSeminorm_bddAbove := inputs_poincare_negative_endpoint d hd
    positive_integrable := inputs_poincare_positive_integrable d hd
    besovSeminorm_eq := ?_
    besovSeminorm_finite := hfinite
    centered_representative := inputs_poincare_centered_representative d hd
    besov_grad_poincare := ?_
    detach := ?_
    poincare_meanZero := ?_
    poincare_killed := ?_
    besov_grad_poincare_all_radii := hG
    detach_all_radii := hD
    poincare_meanZero_all_radii := hM
    poincare_killed_all_radii := hK }⟩
  · intro z r hr v s
    exact mul_nonneg (Real.rpow_nonneg hr.le _) ENNReal.toReal_nonneg
  · intro s hs q hq
    exact if_pos ⟨hs.1, hq⟩
  · intro z r hr u s hs q hq
    exact aux_inputs_poincare_witness_grad_eq d z r hr u s hs.1.le q
  · intro z r hr v s hs
    rfl
  · intro z m hr a s hs q hq u
    have hp : ((3 : ℝ) ^ m) ^ (-s) = (3 : ℝ) ^ (-(s * (m : ℝ))) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
      congr 1
      ring
    simpa only [hp] using hG z ((3 : ℝ) ^ m) hr a s hs q hq u
  · intro z hr s hs u
    exact hD z 1 hr s hs u
  · intro z hr a u
    simpa using hM z 1 hr a u
  · intro z hr a u
    simpa using hK z 1 hr a u

end Paper

