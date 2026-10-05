module

public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import Homogenization.Sobolev.W1p.GlobalAffineLp

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

private noncomputable def aux_lem_19_smooth_density_one_step_dilation_kernel
    {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (xy : SpatialCoordinates d × SpatialCoordinates d) : ℝ :=
  (f xy.1 - f xy.2) /
    Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2)) (((d : ℝ) + 1) / 2)

private theorem aux_lem_19_smooth_density_one_step_dilation_kernel_sq
    {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (xy : SpatialCoordinates d × SpatialCoordinates d) :
    ENNReal.ofReal
        (aux_lem_19_smooth_density_one_step_dilation_kernel f xy ^ 2) =
      ENNReal.ofReal ((f xy.1 - f xy.2) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))) ^
          ((d : ℝ) + 1) := by
  rcases xy with ⟨x, y⟩
  by_cases hxy : x = y
  · subst y
    simp [aux_lem_19_smooth_density_one_step_dilation_kernel]
  · have hne : ∃ i : Fin d, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact hxy (funext hn)
    obtain ⟨i, hi⟩ := hne
    have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply Finset.sum_pos'
      · exact fun j _ => sq_nonneg _
      · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      Real.sqrt_pos.2 hsum
    simp only [aux_lem_19_smooth_density_one_step_dilation_kernel, div_pow]
    have hden : 0 <
        (Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
          (((d : ℝ) + 1) / 2)) ^ 2 :=
      sq_pos_of_pos (Real.rpow_pos_of_pos hpos _)
    rw [ENNReal.ofReal_div_of_pos hden]
    have hpow :
        (Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
          (((d : ℝ) + 1) / 2)) ^ 2 =
        Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ((d : ℝ) + 1) := by
      rw [pow_two]
      have hadd := Real.rpow_add hpos (((d : ℝ) + 1) / 2) (((d : ℝ) + 1) / 2)
      change
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (((d : ℝ) + 1) / 2) *
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (((d : ℝ) + 1) / 2) = _
      rw [← hadd]
      congr 1
      ring
    rw [hpow, ENNReal.ofReal_rpow_of_pos hpos]
    rfl

private noncomputable def aux_lem_19_smooth_density_one_step_dilation_e1
    {d : ℕ} : SpatialCoordinates (d + d) ≃ᵐ ((Fin d ⊕ Fin d) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin d ⊕ Fin d => ℝ) finSumFinEquiv.symm

private noncomputable def aux_lem_19_smooth_density_one_step_dilation_e2
    {d : ℕ} : ((Fin d ⊕ Fin d) → ℝ) ≃ᵐ
      ((SpatialCoordinates d) × (SpatialCoordinates d)) :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ)

private noncomputable def aux_lem_19_smooth_density_one_step_dilation_E
    {d : ℕ} : SpatialCoordinates (d + d) →
      (SpatialCoordinates d) × (SpatialCoordinates d) :=
  aux_lem_19_smooth_density_one_step_dilation_e2 ∘
    aux_lem_19_smooth_density_one_step_dilation_e1

private theorem aux_lem_19_smooth_density_one_step_dilation_E_measurePreserving
    {d : ℕ} : MeasurePreserving
      (aux_lem_19_smooth_density_one_step_dilation_E (d := d)) volume
      (volume.prod volume) := by
  have h1 : MeasurePreserving
      (aux_lem_19_smooth_density_one_step_dilation_e1 (d := d)) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin d ⊕ Fin d => ℝ) finSumFinEquiv.symm
  have h2 : MeasurePreserving
      (aux_lem_19_smooth_density_one_step_dilation_e2 (d := d)) volume
        (volume.prod volume) :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ)
  exact h2.comp h1

private theorem aux_lem_19_smooth_density_one_step_dilation_E_center_apply
    {d : ℕ} (z : SpatialCoordinates d) (x : SpatialCoordinates (d + d)) :
    (fun y : (SpatialCoordinates d) × (SpatialCoordinates d) => (z, z) + y)
        (aux_lem_19_smooth_density_one_step_dilation_E (d := d) x) =
      (z + (fun i : Fin d => x (finSumFinEquiv (Sum.inl i))),
       z + (fun i : Fin d => x (finSumFinEquiv (Sum.inr i)))) := by
  apply Prod.ext
  · funext i
    dsimp [aux_lem_19_smooth_density_one_step_dilation_E,
      aux_lem_19_smooth_density_one_step_dilation_e2,
      aux_lem_19_smooth_density_one_step_dilation_e1,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]
    congr 1
    exact (Equiv.piCongrLeft_apply (fun _ : Sum (Fin d) (Fin d) => ℝ) finSumFinEquiv.symm x (Sum.inl i)).trans (by
      have hrec {a b : Sum (Fin d) (Fin d)} (h : a = b) (v : ℝ) :
          (Eq.rec (motive := fun _ _ => ℝ) v h) = v := by cases h; rfl
      simpa only [Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using! hrec (finSumFinEquiv.symm.apply_symm_apply _) _)

  · funext i
    dsimp [aux_lem_19_smooth_density_one_step_dilation_E,
      aux_lem_19_smooth_density_one_step_dilation_e2,
      aux_lem_19_smooth_density_one_step_dilation_e1,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]
    congr 1
    exact (Equiv.piCongrLeft_apply (fun _ : Sum (Fin d) (Fin d) => ℝ) finSumFinEquiv.symm x (Sum.inr i)).trans (by
      have hrec {a b : Sum (Fin d) (Fin d)} (h : a = b) (v : ℝ) :
          (Eq.rec (motive := fun _ _ => ℝ) v h) = v := by cases h; rfl
      simpa only [Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] using! hrec (finSumFinEquiv.symm.apply_symm_apply _) _)

private theorem aux_lem_19_smooth_density_one_step_dilation_kernel_comp
    {d : ℕ} (f : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d)
    {lam : ℝ} (hlam : 0 < lam)
    (x y : SpatialCoordinates d) :
    aux_lem_19_smooth_density_one_step_dilation_kernel
        (fun q => f (z + lam • (q - z))) (x, y) =
      lam ^ (((d : ℝ) + 1) / 2) *
        aux_lem_19_smooth_density_one_step_dilation_kernel f
          (z + lam • (x - z), z + lam • (y - z)) := by
  by_cases hxy : x = y
  · subst y
    simp [aux_lem_19_smooth_density_one_step_dilation_kernel]
  · have hne : ∃ i : Fin d, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact hxy (funext hn)
    obtain ⟨i, hi⟩ := hne
    have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply Finset.sum_pos'
      · exact fun j _ => sq_nonneg _
      · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      Real.sqrt_pos.2 hsum
    have hden : 0 < Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
        (((d : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hpos _
    have hT : ∀ q : SpatialCoordinates d,
        z + lam • (q - z) = _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z z lam q := by
      intro q
      funext j
      simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, smul_eq_mul]
    have hs := _root_.SubdiffusiveProcess.EllipticRegularity.sqrt_sum_sq_cubeDilation
      z z hlam x y
    simp only [aux_lem_19_smooth_density_one_step_dilation_kernel]
    rw [show Real.sqrt (∑ j : Fin d,
        ((z + lam • (x - z)) j - (z + lam • (y - z)) j) ^ 2) =
          lam * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) by
      rw [hT x, hT y]
      exact hs]
    have hpow : Real.rpow (lam * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
        (((d : ℝ) + 1) / 2) =
        lam ^ (((d : ℝ) + 1) / 2) *
          Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
            (((d : ℝ) + 1) / 2) := by
      exact Real.mul_rpow (le_of_lt hlam) (Real.sqrt_nonneg _)
    rw [hpow]
    field_simp [hden.ne', hlam.ne']
private theorem aux_lem_19_smooth_density_one_step_dilation_seminorm_of_memLp
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr))
    (hf : MemLp (aux_lem_19_smooth_density_one_step_dilation_kernel
      (fun x => f x)) 2
      ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).prod
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))) :
    cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (fun _ : Fin 1 => f) < ⊤ := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  have : IsFiniteMeasure μ := by
    dsimp [μ, U]
    infer_instance
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hqint :
      (∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
        (fun x => f x) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) < ⊤ := by
    exact (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf.aestronglyMeasurable).mp hf
  have hqmeas : AEMeasurable
      (fun xy => ENNReal.ofReal
        (aux_lem_19_smooth_density_one_step_dilation_kernel
          (fun x => f x) xy ^ 2)) (μ.prod μ) := by
    have hfmeas : AEStronglyMeasurable (fun x => (f x : ℝ)) μ :=
      Lp.aestronglyMeasurable f
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          (f xy.1 - f xy.2)) (μ.prod μ) :=
      (hfmeas.comp_fst.sub hfmeas.comp_snd)
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    have hq : AEMeasurable
        (aux_lem_19_smooth_density_one_step_dilation_kernel
          (fun x => f x)) (μ.prod μ) := by
      exact hnum.aemeasurable.div hden.aemeasurable
    exact (hq.pow_const 2).ennreal_ofReal
  have hraw :
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 1)) < ⊤ := by
    have hqint' :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy ^ 2) ∂(μ.prod μ)) < ⊤ := by
      have heq :
          (∫⁻ xy, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (fun x => f x) xy ^ 2) ∂(μ.prod μ)) =
            ∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
              (fun x => f x) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
        apply lintegral_congr
        intro xy
        symm
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
        norm_num [Real.norm_eq_abs, sq_abs]
      rw [heq]
      exact hqint
    have hprod_eq :
        (∫⁻ x, ∫⁻ y,
          ENNReal.ofReal ((f x - f y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 1) ∂μ ∂μ) =
          ∫⁻ xy, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (fun x => f x) xy ^ 2) ∂(μ.prod μ) := by
      rw [lintegral_prod
        (fun xy => ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy ^ 2)) hqmeas]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      simpa using! (aux_lem_19_smooth_density_one_step_dilation_kernel_sq
        (fun x => f x) (x, y)).symm
    exact lt_of_eq_of_lt hprod_eq hqint'
  let a : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  have ha0 : a ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr halfFractionalOrder.2.1).ne', hvoltop⟩
  have hsemi : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
      (fun _ : Fin 1 => f) < ⊤ := by
    unfold cubeFractionalL2Seminorm
    have hpow : (a * (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 1))) ^ (1 / 2 : ℝ) < ⊤ := by
      apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      have hmul : a * (∫⁻ x in U, ∫⁻ y in U,
          ENNReal.ofReal ((f x - f y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 1)) < ⊤ := by
        dsimp [a]
        exact ENNReal.mul_lt_top
          (ENNReal.div_lt_top ENNReal.ofReal_ne_top
            hvolpos.ne') hraw
      exact hmul.ne
    simpa [U, a, halfFractionalOrder, Fin.sum_univ_succ] using! hpow
  exact hsemi

private theorem aux_lem_19_smooth_density_one_step_dilation_kernel_memLp_of_raw
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr))
    (hraw : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 1)) < ⊤) :
    MemLp (aux_lem_19_smooth_density_one_step_dilation_kernel (fun x => f x)) 2
      ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).prod
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  have : IsFiniteMeasure μ := by
    dsimp [μ, U]
    infer_instance
  have hqmeas : AEMeasurable
      (fun xy => ENNReal.ofReal
        (aux_lem_19_smooth_density_one_step_dilation_kernel
          (fun x => f x) xy ^ 2)) (μ.prod μ) := by
    have hfmeas : AEStronglyMeasurable (fun x => (f x : ℝ)) μ :=
      Lp.aestronglyMeasurable f
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          (f xy.1 - f xy.2)) (μ.prod μ) :=
      hfmeas.comp_fst.sub hfmeas.comp_snd
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    have hq : AEMeasurable
        (aux_lem_19_smooth_density_one_step_dilation_kernel (fun x => f x))
        (μ.prod μ) := hnum.aemeasurable.div hden.aemeasurable
    exact (hq.pow_const 2).ennreal_ofReal
  have hrawq :
      (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 1) ∂μ ∂μ) =
        ∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy ^ 2) ∂(μ.prod μ) := by
    rw [lintegral_prod
      (fun xy => ENNReal.ofReal
        (aux_lem_19_smooth_density_one_step_dilation_kernel
          (fun x => f x) xy ^ 2)) hqmeas]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    simpa using! (aux_lem_19_smooth_density_one_step_dilation_kernel_sq
      (fun x => f x) (x, y)).symm
  have hqint :
      (∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
        (fun x => f x) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ)) < ⊤ := by
    have hqraw :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy ^ 2) ∂(μ.prod μ)) < ⊤ := by
      exact hrawq ▸ hraw
    have heq :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy ^ 2) ∂(μ.prod μ)) =
          ∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => f x) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
      apply lintegral_congr
      intro xy
      symm
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
      norm_num [Real.norm_eq_abs, sq_abs]
    exact heq ▸ hqraw
  have hkernelmeas : AEStronglyMeasurable (aux_lem_19_smooth_density_one_step_dilation_kernel (fun x => f x)) (μ.prod μ) := by
    have hfmeas : AEStronglyMeasurable (fun x => (f x : ℝ)) μ :=
      Lp.aestronglyMeasurable f
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          (f xy.1 - f xy.2)) (μ.prod μ) :=
      hfmeas.comp_fst.sub hfmeas.comp_snd
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    exact (hnum.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  apply (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hkernelmeas).2
  exact hqint

private theorem aux_lem_19_smooth_density_one_step_dilation_inward_eLpNorm
    {n : ℕ} {g : SpatialCoordinates n → ℝ}
    (hg : MemLp g 2 volume) (c : SpatialCoordinates n)
    (lam : ℕ → ℝ) (hlam0 : ∀ k, 0 < lam k)
    (hlam1 : ∀ k, lam k ≤ 1)
    (hlim : Tendsto lam atTop (𝓝 1)) :
    Tendsto (fun k => eLpNorm
      (g ∘ (fun x : SpatialCoordinates n => c + lam k • (x - c)) - g)
      2 volume) atTop (𝓝 0) := by
  let eps : ℕ → ℝ := fun k => (lam k)⁻¹ - 1
  let D : ℕ → SpatialCoordinates n → SpatialCoordinates n :=
    fun k => globalAffineExpansion c (eps k)
  let A : ℕ → SpatialCoordinates n → SpatialCoordinates n :=
    fun k x => c + lam k • (x - c)
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    have hi : Tendsto ((fun x : ℝ => x⁻¹) ∘ lam) atTop (𝓝 (1 : ℝ)⁻¹) :=
      (tendsto_inv₀ (by norm_num)).comp hlim
    simpa [eps, Function.comp_def] using!
      hi.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hepsnonneg : ∀ k, 0 ≤ eps k := by
    intro k
    dsimp [eps]
    exact sub_nonneg.mpr ((one_le_inv₀ (hlam0 k)).2 (hlam1 k))
  have hDmap : ∀ k, Measure.map (D k) (volume : Measure (SpatialCoordinates n)) =
      ENNReal.ofReal (((1 + eps k) ^ n)⁻¹) • volume := by
    intro k
    exact map_globalAffineExpansion_volume c (hepsnonneg k)
  have hDpos : ∀ k, 0 < 1 + eps k := by
    intro k
    dsimp [eps]
    simpa [eps] using! inv_pos.mpr (hlam0 k)
  have hAD : ∀ k, A k ∘ D k = id := by
    intro k
    funext x
    ext i
    dsimp [A, D, eps, globalAffineExpansion]
    simp
    calc
      c i + lam k * ((lam k)⁻¹ * x i - ((lam k)⁻¹ - 1) * c i - c i) =
          c i + (lam k * (lam k)⁻¹) * (x i - c i) := by ring
      _ = x i := by rw [mul_inv_cancel₀ (hlam0 k).ne']; ring
  have hq : Tendsto (fun k => eLpNorm (g ∘ (D k) - g) 2 volume) atTop (𝓝 0) := by
    exact tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero
      (by norm_num) (by norm_num) hg c heps0 hepsnonneg
  have hDmeas : ∀ k, Measurable (D k) := by
    intro k
    exact ((measurable_const_smul (1 + eps k)).sub measurable_const)
  have hAmeas : ∀ k, Measurable (A k) := by
    intro k
    exact measurable_const.add ((measurable_const_smul (lam k)).comp
      (measurable_id.sub measurable_const))
  have hADmap : ∀ k, Measure.map (A k) (Measure.map (D k) volume) = volume := by
    intro k
    rw [Measure.map_map (hAmeas k) (hDmeas k)]
    convert Measure.map_id using 1
    rw [hAD k]
  have hAq : ∀ k, Measure.QuasiMeasurePreserving (A k)
      (Measure.map (D k) volume) volume := by
    intro k
    refine ⟨hAmeas k, ?_⟩
    rw [hADmap k]
  have hgD : ∀ k, AEStronglyMeasurable g (Measure.map (D k) volume) := by
    intro k
    rw [hDmap k]
    exact (hg.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable
  have htarget_meas : ∀ k, AEStronglyMeasurable (g ∘ A k - g)
      (Measure.map (D k) volume) := by
    intro k
    exact hg.aestronglyMeasurable.comp_quasiMeasurePreserving (hAq k) |>.sub (hgD k)
  have hq' : Tendsto (fun k => eLpNorm (g ∘ A k - g) (2 : ℝ≥0∞)
      (Measure.map (D k) volume)) atTop (𝓝 0) := by
    have hpoint : ∀ k, eLpNorm (g ∘ A k - g) (2 : ℝ≥0∞)
          (Measure.map (D k) volume) =
        eLpNorm (g ∘ D k - g) 2 volume := by
      intro k
      rw [eLpNorm_map_measure (htarget_meas k) (hDmeas k).aemeasurable]
      have hfun : (g ∘ A k - g) ∘ D k = -(g ∘ D k - g) := by
        funext x
        dsimp [Function.comp]
        rw [show A k (D k x) = x from congrFun (hAD k) x]
        ring
      rw [hfun, eLpNorm_neg]
    exact hq.congr (fun k => (hpoint k).symm)
  have hfactor : Tendsto (fun k =>
      (ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) ^ (1 / 2 : ℝ)) atTop (𝓝 1) := by
    have hscale : Tendsto (fun k => 1 + eps k) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using!
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add heps0)
    have he : Tendsto (fun k => (1 + eps k) ^ n) atTop (𝓝 (1 : ℝ)) :=
      by simpa only [one_pow] using! hscale.pow n
    have hi0 : Tendsto ((fun x : ℝ => x⁻¹) ∘ (fun k => (1 + eps k) ^ n))
        atTop (𝓝 (1 : ℝ)⁻¹) := (tendsto_inv₀ (by norm_num)).comp he
    have hi : Tendsto (fun k => ((1 + eps k) ^ n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa [Function.comp_def] using! hi0
    have ha : Tendsto (fun k => |((1 + eps k) ^ n)⁻¹|) atTop (𝓝 (1 : ℝ)) := by
      simpa only [abs_one] using! hi.abs
    have ho : Tendsto (fun k => ENNReal.ofReal |((1 + eps k) ^ n)⁻¹|) atTop (𝓝 1) :=
      by simpa only [Function.comp_def, ENNReal.ofReal_one] using!
        (ENNReal.continuous_ofReal.tendsto 1).comp ha
    have ho' : Tendsto (fun k => ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) atTop (𝓝 1) := by
      convert ho using 1
      funext k
      rw [abs_of_pos (inv_pos.mpr (pow_pos (hDpos k) n))]
    have hp := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 1 |>.comp ho'
    simpa [Function.comp_def] using! hp
  have htargetVolume : ∀ k, AEStronglyMeasurable (g ∘ A k - g) volume := by
    intro k
    have hm := htarget_meas k
    rw [hDmap k] at hm
    exact hm.mono_ac (Measure.absolutelyContinuous_smul ((ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (hDpos k) n))).ne'))
  have htarget_eq : ∀ k, eLpNorm (g ∘ A k - g) 2 volume =
      ((ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) ^ (1 / 2 : ℝ))⁻¹ *
        eLpNorm (g ∘ A k - g) 2 (Measure.map (D k) volume) := by
    intro k
    rw [hDmap k, eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (g ∘ A k - g) _ (htargetVolume k)]
    have hct : ENNReal.ofReal (((1 + eps k) ^ n)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hp0 : (ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) ^ (1 / 2 : ℝ) ≠ 0 := by
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by
        exact inv_pos.mpr (pow_pos (hDpos k) n))) hct).ne'
    have hpt : (ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hct
    rw [show (1 / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) by norm_num]
    rw [smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hp0 hpt, one_mul]
  let q : ℕ → ℝ≥0∞ := fun k =>
    (ENNReal.ofReal (((1 + eps k) ^ n)⁻¹)) ^ (1 / 2 : ℝ)
  have hbound : ∀ᶠ k in atTop, (q k)⁻¹ ≤ 2 := by
    filter_upwards [hfactor.eventually (eventually_gt_nhds
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1))] with k hk
    apply (ENNReal.inv_le_iff_inv_le).2
    exact (le_of_lt (by simpa [q] using! hk))
  have hupper : Tendsto (fun k => (2 : ℝ≥0∞) *
      eLpNorm (g ∘ A k - g) 2 (Measure.map (D k) volume)) atTop (𝓝 0) := by
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ≥0∞)) atTop (𝓝 2) := tendsto_const_nhds
    simpa using! ENNReal.Tendsto.mul htwo (Or.inl (by norm_num))
      hq' (Or.inr (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [] with k
    exact bot_le
  · filter_upwards [hbound] with k hk
    rw [htarget_eq k]
    exact mul_le_mul_of_nonneg_right hk (bot_le)

/-- Inward dilation step in the smooth-density construction.
Carried-input tick list:
- SOURCE: dimension `d ≥ 2`, arbitrary centre `z`, positive side `r`, and
  the half-fractional class `v`.
- SOURCE: the positive target error `η`.
- CONCLUDED HERE: an inward factor `λ ∈ (0,1)`, the dependent fractional
  class `u` representing the dilated datum on the original cube, and an
  admissible difference class with error below `η`.
The zero extensions, the difference quotient, and strong continuity of
dilation are the construction in the cited paper step; no smooth-density or
scaling result is assumed. -/
theorem lem_19_smooth_density_one_step_dilation
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    {η : ℝ} (hη : 0 < η) :
    ∃ (lam : Set.Ioo (0 : ℝ) 1)
      (u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
      (dilErr : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      ((u.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (v.val 0 : SpatialCoordinates d → ℝ) ∘
          (fun x : SpatialCoordinates d =>
            z + (lam : ℝ) • (x - z))) ∧
      dilErr.val 0 = v.val 0 - u.val 0 ∧
      cubeFractionalL2Norm hd z r hr halfFractionalOrder dilErr < η := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let lamSeq : ℕ → ℝ := fun k => 1 - ((k : ℝ) + 2)⁻¹
  have hlam0 : ∀ k, 0 < lamSeq k := by
    intro k
    dsimp [lamSeq]
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    have hi : 0 < ((k : ℝ) + 2)⁻¹ := inv_pos.mpr (by positivity)
    have hi' : ((k : ℝ) + 2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hk
    linarith
  have hlam1 : ∀ k, lamSeq k ≤ 1 := by
    intro k
    dsimp [lamSeq]
    linarith [inv_pos.mpr (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
  have hlam_lim : Tendsto lamSeq atTop (𝓝 1) := by
    have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop := by
      simpa [Nat.cast_add] using!
        (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hnat
    simpa [lamSeq] using! tendsto_const_nhds.sub hinv
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (centeredCube z r hr).isOpen.measurableSet
  have hμfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfμ : MemLp (fun x : SpatialCoordinates d => (v.val 0) x) 2 μ := by
    simpa [μ] using! (Lp.memLp (v.val 0))
  have hrawv : (∫⁻ x in U, ∫⁻ y in U,
      ENNReal.ofReal (((v.val 0) x - (v.val 0) y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 1)) < ⊤ := by
    have hs := scalar_halfFractional_kernel_lt_top hd z r hr v
    convert hs using 1
  let f : SpatialCoordinates d → ℝ := fun x => (v.val 0) x
  let qv : SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    aux_lem_19_smooth_density_one_step_dilation_kernel f
  have hqv : MemLp qv 2 (μ.prod μ) := by
    apply aux_lem_19_smooth_density_one_step_dilation_kernel_memLp_of_raw z r hr
      (v.val 0)
    simpa [U, μ, f] using! hrawv
  let Q : Set (SpatialCoordinates d × SpatialCoordinates d) := U ×ˢ U
  have hQmeas : MeasurableSet Q := hUmeas.prod hUmeas
  let F : SpatialCoordinates d → ℝ := U.indicator f
  let G : SpatialCoordinates d × SpatialCoordinates d → ℝ := Q.indicator qv
  have hF : MemLp F 2 volume := by
    apply (memLp_indicator_iff_restrict hUmeas).2
    simpa [F, μ] using! hfμ
  have hG : MemLp G 2 (volume.prod volume) := by
    apply (memLp_indicator_iff_restrict hQmeas).2
    simpa [G, Q, μ, Measure.prod_restrict] using! hqv
  let T : ℕ → SpatialCoordinates d → SpatialCoordinates d :=
    fun k x => z + lamSeq k • (x - z)
  let P : ℕ → (SpatialCoordinates d × SpatialCoordinates d) →
      (SpatialCoordinates d × SpatialCoordinates d) :=
    fun k xy => (T k xy.1, T k xy.2)
  have hTmeas : ∀ k, Measurable (T k) := by
    intro k
    exact measurable_const.add ((measurable_const_smul (lamSeq k)).comp
      (measurable_id.sub measurable_const))
  have hTmaps : ∀ k x, x ∈ U → T k x ∈ U := by
    intro k x hx
    change dist (T k x) z < r / 2
    have hx' : dist x z < r / 2 := by
      simpa [U, centeredCube] using! hx
    have heq : dist (T k x) z = lamSeq k * dist x z := by
      have hvec : T k x - z = lamSeq k • (x - z) := by
        funext i
        simp [T, smul_eq_mul]
      rw [dist_eq_norm, dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hlam0 k)]
    rw [heq]
    calc
      lamSeq k * dist x z ≤ 1 * dist x z :=
        mul_le_mul_of_nonneg_right (hlam1 k) (dist_nonneg)
      _ < r / 2 := by simpa using! hx'
  have hTmap : ∀ k, Measure.map (T k) (volume : Measure (SpatialCoordinates d)) =
      ENNReal.ofReal |((lamSeq k) ^ d)⁻¹| • volume := by
    intro k
    simpa [T, _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, smul_eq_mul] using!
      (_root_.SubdiffusiveProcess.EllipticRegularity.map_cubeDilation_volume z z (hlam0 k).ne')
  have hFcomp : ∀ k, MemLp (F ∘ T k) 2 μ := by
    intro k
    have hmaple : Measure.map (T k) μ ≤
        ENNReal.ofReal |((lamSeq k) ^ d)⁻¹| • volume := by
      calc
        Measure.map (T k) μ ≤ Measure.map (T k) volume :=
          Measure.map_mono Measure.restrict_le_self (hTmeas k)
        _ = _ := hTmap k
    have hFm : MemLp F 2 (Measure.map (T k) μ) := by
      apply MemLp.mono_measure hmaple
      exact hF.smul_measure ENNReal.ofReal_ne_top
    exact hFm.comp_of_map (hTmeas k).aemeasurable
  let cscale : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal |((lamSeq k) ^ d)⁻¹|
  have hPmeas : ∀ k, Measurable (P k) := by
    intro k
    simpa [P] using! (hTmeas k).prodMap (hTmeas k)
  have hPmap : ∀ k, Measure.map (P k) (volume.prod volume) =
      (cscale k * cscale k) • (volume.prod volume) := by
    intro k
    change Measure.map (Prod.map (T k) (T k)) (volume.prod volume) = _
    rw [← Measure.map_prod_map volume volume (hTmeas k) (hTmeas k),
      hTmap k, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hGcomp : ∀ k, MemLp (G ∘ P k) 2 (volume.prod volume) := by
    intro k
    have hGm : MemLp G 2 (Measure.map (P k) (volume.prod volume)) := by
      rw [hPmap k]
      apply hG.smul_measure
      simpa [cscale] using!
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    exact hGm.comp_of_map (hPmeas k).aemeasurable
  let H : SpatialCoordinates (d + d) →
      (SpatialCoordinates d × SpatialCoordinates d) := fun ξ =>
    (z + (fun i : Fin d => ξ (finSumFinEquiv (Sum.inl i))),
      z + (fun i : Fin d => ξ (finSumFinEquiv (Sum.inr i))))
  have hH_eq : H = (fun ξ => (z, z) +
      aux_lem_19_smooth_density_one_step_dilation_E (d := d) ξ) := by
    funext ξ
    exact (aux_lem_19_smooth_density_one_step_dilation_E_center_apply z ξ).symm
  have hH : MeasurePreserving H volume (volume.prod volume) := by
    rw [hH_eq]
    exact (measurePreserving_add_left (volume.prod volume) (z, z)).comp
      aux_lem_19_smooth_density_one_step_dilation_E_measurePreserving
  let gpair : SpatialCoordinates (d + d) → ℝ := G ∘ H
  have hgpair : MemLp gpair 2 volume := by
    exact hG.comp_measurePreserving hH
  have hpair_cont : Tendsto (fun k => eLpNorm
      (gpair ∘ (fun ξ : SpatialCoordinates (d + d) => lamSeq k • ξ) - gpair)
        2 volume) atTop (𝓝 0) := by
    simpa using! aux_lem_19_smooth_density_one_step_dilation_inward_eLpNorm
      hgpair 0 lamSeq hlam0 hlam1 hlam_lim
  have hP_H : ∀ k ξ, P k (H ξ) = H (lamSeq k • ξ) := by
    intro k ξ
    apply Prod.ext <;> funext i
    · simp [P, H, T, smul_eq_mul]
    · simp [P, H, T, smul_eq_mul]
  have hK_cont : Tendsto (fun k => eLpNorm
      (G ∘ P k - G) 2 (volume.prod volume)) atTop (𝓝 0) := by
    have hEq : ∀ k, eLpNorm (G ∘ P k - G) 2 (volume.prod volume) =
        eLpNorm (gpair ∘ (fun ξ : SpatialCoordinates (d + d) => lamSeq k • ξ) - gpair)
          2 volume := by
      intro k
      have hmeas : AEStronglyMeasurable (G ∘ P k - G) (Measure.map H volume) := by
        rw [hH.map_eq]
        exact (hGcomp k).aestronglyMeasurable.sub hG.aestronglyMeasurable
      rw [← hH.map_eq, eLpNorm_map_measure hmeas hH.measurable.aemeasurable]
      congr 1
      funext ξ
      dsimp [Function.comp]
      rw [hP_H k ξ]
      rfl
    exact hpair_cont.congr' (Filter.Eventually.of_forall fun k => (hEq k).symm)

  have hF_cont : Tendsto (fun k => eLpNorm (F ∘ T k - F) 2 volume)
      atTop (𝓝 0) := by
    simpa [T] using! aux_lem_19_smooth_density_one_step_dilation_inward_eLpNorm
      hF z lamSeq hlam0 hlam1 hlam_lim
  have hF_cont_restrict : Tendsto (fun k => eLpNorm (F ∘ T k - F) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF_cont
    · filter_upwards [] with k
      exact bot_le
    · filter_upwards [] with k
      exact eLpNorm_mono_measure _ (by simpa [μ] using! (Measure.restrict_le_self :
        volume.restrict U ≤ volume))

  let uFun : ℕ → DomainL2 (centeredCube z r hr) :=
    fun k => (hFcomp k).toLp (F ∘ T k)
  have hkernel_Fcomp : ∀ k, MemLp
      (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k)) 2
        (μ.prod μ) := by
    intro k
    have hGrestrict : MemLp (G ∘ P k) 2 (μ.prod μ) := by
      simpa [μ, Measure.prod_restrict] using!
        (hGcomp k).mono_measure (Measure.restrict_le_self :
          (volume.prod volume).restrict (U ×ˢ U) ≤ volume.prod volume)
    let c : ℝ := lamSeq k ^ (((d : ℝ) + 1) / 2)
    have hscalar : MemLp (fun xy => c * (G ∘ P k) xy) 2 (μ.prod μ) :=
      hGrestrict.const_mul c
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          F (T k xy.1) - F (T k xy.2)) (μ.prod μ) := by
      simpa [Function.comp_def] using!
        (hFcomp k).aestronglyMeasurable.comp_fst.sub
          (hFcomp k).aestronglyMeasurable.comp_snd
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    have hqmeas0 : AEMeasurable
        (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k))
        (μ.prod μ) := hnum.aemeasurable.div hden.aemeasurable
    have hqmeas : AEMeasurable
        (fun xy => ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k) xy ^ 2))
        (μ.prod μ) := by
      exact (hqmeas0.pow_const 2).ennreal_ofReal
    have htargetmeas : AEMeasurable
        (fun xy => ENNReal.ofReal ((c * (G ∘ P k) xy) ^ 2)) (μ.prod μ) := by
      exact (hscalar.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
    have hpoint : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k) (x, y) =
          c * (G ∘ P k) (x, y) := by
      filter_upwards [ae_restrict_mem hUmeas] with x hx
      filter_upwards [ae_restrict_mem hUmeas] with y hy
      have hxF : F (T k x) = f (T k x) := by
        simp only [F, Set.indicator_of_mem (hTmaps k x hx)]
      have hyF : F (T k y) = f (T k y) := by
        simp only [F, Set.indicator_of_mem (hTmaps k y hy)]
      have hGxy : G (P k (x, y)) = qv (T k x, T k y) := by
        change (U ×ˢ U).indicator qv (T k x, T k y) = qv (T k x, T k y)
        rw [Set.indicator_of_mem]
        exact ⟨hTmaps k x hx, hTmaps k y hy⟩
      change ((F (T k x) - F (T k y)) /
        Real.rpow (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2))
          (((d : ℝ) + 1) / 2)) = _
      rw [hxF, hyF]
      simpa [c, qv, Function.comp_def, hGxy] using!
        (aux_lem_19_smooth_density_one_step_dilation_kernel_comp
          f z (hlam0 k) x y)
    have hraw_eq :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k) xy ^ 2)
            ∂(μ.prod μ)) =
          ∫⁻ xy, ENNReal.ofReal ((c * (G ∘ P k) xy) ^ 2) ∂(μ.prod μ) := by
      calc
        _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k) (x, y) ^ 2)
              ∂μ ∂μ := lintegral_prod _ hqmeas
        _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((c * (G ∘ P k) (x, y)) ^ 2) ∂μ ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hpoint] with x hx
          apply lintegral_congr_ae
          filter_upwards [hx] with y hy
          exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hy
        _ = _ := (lintegral_prod _ htargetmeas).symm
    have htargetint :
        (∫⁻ xy, ENNReal.ofReal ((c * (G ∘ P k) xy) ^ 2) ∂(μ.prod μ)) < ⊤ := by
      have hqint :=
        (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hscalar.aestronglyMeasurable).mp
          hscalar
      have heq :
          (∫⁻ xy, ENNReal.ofReal ((c * (G ∘ P k) xy) ^ 2) ∂(μ.prod μ)) =
            ∫⁻ xy, ‖c * (G ∘ P k) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
        apply lintegral_congr
        intro xy
        symm
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
        congr 1
        rw [Real.norm_eq_abs, Real.rpow_two]
        exact sq_abs _
      exact heq ▸ hqint
    apply (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hqmeas0.aestronglyMeasurable).2
    have heq :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel (F ∘ T k) xy ^ 2)
            ∂(μ.prod μ)) =
          ∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
            (F ∘ T k) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
      apply lintegral_congr
      intro xy
      symm
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
      simp [Real.norm_eq_abs, sq_abs]
    exact heq ▸ (hraw_eq ▸ htargetint)

  have hkernel_u : ∀ k, MemLp
      (aux_lem_19_smooth_density_one_step_dilation_kernel (fun x => uFun k x)) 2
        (μ.prod μ) := by
    intro k
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          uFun k xy.1 - uFun k xy.2) (μ.prod μ) := by
      exact (Lp.aestronglyMeasurable (uFun k)).comp_fst.sub
        (Lp.aestronglyMeasurable (uFun k)).comp_snd
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    have hqmeas0 : AEMeasurable
        (aux_lem_19_smooth_density_one_step_dilation_kernel (fun x => uFun k x))
        (μ.prod μ) := hnum.aemeasurable.div hden.aemeasurable
    have hqmeas : AEMeasurable
        (fun xy => ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => uFun k x) xy ^ 2)) (μ.prod μ) := by
      exact (hqmeas0.pow_const 2).ennreal_ofReal
    have hpoint : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => uFun k x) (x, y) =
          aux_lem_19_smooth_density_one_step_dilation_kernel
            (F ∘ T k) (x, y) := by
      have hcoe := (hFcomp k).coeFn_toLp
      filter_upwards [hcoe] with x hx
      filter_upwards [hcoe] with y hy
      change ((uFun k x - uFun k y) /
        Real.rpow (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2))
          (((d : ℝ) + 1) / 2)) = _
      rw [hx, hy]
      rfl
    have hraw_eq :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => uFun k x) xy ^ 2) ∂(μ.prod μ)) =
          ∫⁻ xy, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (F ∘ T k) xy ^ 2) ∂(μ.prod μ) := by
      have hFmeas : AEMeasurable
          (fun xy => ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (F ∘ T k) xy ^ 2)) (μ.prod μ) := by
        have hn : AEStronglyMeasurable
            (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
              F (T k xy.1) - F (T k xy.2)) (μ.prod μ) := by
          exact (hFcomp k).aestronglyMeasurable.comp_fst.sub
            (hFcomp k).aestronglyMeasurable.comp_snd
        have hd' : Measurable
            (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
              Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
                (((d : ℝ) + 1) / 2)) := by
          apply (Real.continuous_rpow_const (by positivity)).measurable.comp
          apply Measurable.sqrt
          exact Finset.measurable_sum Finset.univ fun i _ =>
            (((measurable_pi_apply i).comp measurable_fst).sub
              ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
        exact ((hn.aemeasurable.div hd'.aemeasurable).pow_const 2).ennreal_ofReal
      calc
        _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (fun x => uFun k x) (x, y) ^ 2) ∂μ ∂μ := lintegral_prod _ hqmeas
        _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (F ∘ T k) (x, y) ^ 2) ∂μ ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hpoint] with x hx
          apply lintegral_congr_ae
          filter_upwards [hx] with y hy
          exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hy
        _ = _ := (lintegral_prod _ hFmeas).symm
    have hFraw :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (F ∘ T k) xy ^ 2) ∂(μ.prod μ)) < ⊤ := by
      have hqint :=
        (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hkernel_Fcomp k).aestronglyMeasurable).mp
          (hkernel_Fcomp k)
      have heq :
          (∫⁻ xy, ENNReal.ofReal
            (aux_lem_19_smooth_density_one_step_dilation_kernel
              (F ∘ T k) xy ^ 2) ∂(μ.prod μ)) =
            ∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
              (F ∘ T k) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
        apply lintegral_congr
        intro xy
        symm
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
        congr 1
        rw [Real.norm_eq_abs, Real.rpow_two]
        exact sq_abs _
      exact heq ▸ hqint
    apply (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hqmeas0.aestronglyMeasurable).2
    have heq :
        (∫⁻ xy, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => uFun k x) xy ^ 2) ∂(μ.prod μ)) =
          ∫⁻ xy, ‖aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => uFun k x) xy‖ₑ ^ (2 : ℝ) ∂(μ.prod μ) := by
      apply lintegral_congr
      intro xy
      symm
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
      congr 1
      rw [Real.norm_eq_abs, Real.rpow_two]
      exact sq_abs _
    exact heq ▸ (hraw_eq ▸ hFraw)

  have huSemi : ∀ k, cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
      (fun _ : Fin 1 => uFun k) < ⊤ := by
    intro k
    simpa [uFun] using!
      (aux_lem_19_smooth_density_one_step_dilation_seminorm_of_memLp
        hd z r hr (uFun k) (hkernel_u k))
  let uClass : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    fun k => ⟨fun _ : Fin 1 => uFun k, huSemi k⟩
  let errClass : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    fun k => ⟨fun _ : Fin 1 => v.val 0 - (uClass k).val 0,
      cubeFractionalL2Seminorm_sub_lt_top hd z r hr halfFractionalOrder
        (fun _ : Fin 1 => v.val 0) (uClass k).val v.property (huSemi k)⟩
  have hGmapmeas : ∀ k, AEStronglyMeasurable G
      (Measure.map (P k) (volume.prod volume)) := by
    intro k
    rw [hPmap k]
    exact hG.aestronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous
  have hcompnorm_eq : ∀ k, eLpNorm (G ∘ P k) 2 (volume.prod volume) =
      (cscale k * cscale k) ^ (1 / 2 : ℝ) * eLpNorm G 2 (volume.prod volume) := by
    intro k
    calc
      eLpNorm (G ∘ P k) 2 (volume.prod volume) =
          eLpNorm G 2 (Measure.map (P k) (volume.prod volume)) :=
        (eLpNorm_map_measure (hGmapmeas k) (hPmeas k).aemeasurable).symm
      _ = eLpNorm G 2 ((cscale k * cscale k) • (volume.prod volume)) := by
        rw [hPmap k]
      _ = (cscale k * cscale k) ^ (1 / 2 : ℝ) *
          eLpNorm G 2 (volume.prod volume) := by
        rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) G _ hG.aestronglyMeasurable]
        norm_num
  have hcscale : Tendsto cscale atTop (𝓝 1) := by
    have hp : Tendsto (fun k : ℕ => (lamSeq k) ^ d) atTop (𝓝 (1 : ℝ)) := by
      simpa only [one_pow] using! hlam_lim.pow d
    have hi0 : Tendsto ((fun x : ℝ => x⁻¹) ∘ (fun k : ℕ => (lamSeq k) ^ d))
        atTop (𝓝 (1 : ℝ)⁻¹) := (tendsto_inv₀ (by norm_num)).comp hp
    have hi : Tendsto (fun k : ℕ => ((lamSeq k) ^ d)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa [Function.comp_def] using! hi0
    have ha : Tendsto (fun k : ℕ => |((lamSeq k) ^ d)⁻¹|) atTop (𝓝 (1 : ℝ)) := by
      simpa only [abs_one] using! hi.abs
    simpa [cscale, Function.comp_def, ENNReal.ofReal_one] using!
      (ENNReal.continuous_ofReal.tendsto 1).comp ha
  have hcompnorm : Tendsto (fun k => eLpNorm (G ∘ P k) 2 (volume.prod volume))
      atTop (𝓝 (eLpNorm G 2 (volume.prod volume))) := by
    rw [show (fun k => eLpNorm (G ∘ P k) 2 (volume.prod volume)) =
        (fun k => (cscale k * cscale k) ^ (1 / 2 : ℝ) *
          eLpNorm G 2 (volume.prod volume)) by
      funext k
      exact hcompnorm_eq k]
    have hs : Tendsto (fun k => (cscale k * cscale k) ^ (1 / 2 : ℝ))
        atTop (𝓝 1) := by
      have hmul : Tendsto (fun k => cscale k * cscale k) atTop
          (𝓝 (1 : ℝ≥0∞)) := by
        simpa using! ENNReal.Tendsto.mul hcscale (Or.inl (by norm_num)) hcscale
          (Or.inl (by norm_num))
      have hp := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 1 |>.comp hmul
      simpa using! hp
    simpa using! ENNReal.Tendsto.mul hs (Or.inl (by norm_num))
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => eLpNorm G 2 (volume.prod volume))
        atTop (𝓝 (eLpNorm G 2 (volume.prod volume))))
      (Or.inr ENNReal.one_ne_top)
  let R : ℕ → (SpatialCoordinates d × SpatialCoordinates d) → ℝ :=
    fun k xy => G xy - (lamSeq k ^ (((d : ℝ) + 1) / 2)) * (G ∘ P k) xy
  have hRmem : ∀ k, MemLp (R k) 2 (volume.prod volume) := by
    intro k
    simpa [R] using! hG.sub ((hGcomp k).const_mul
      (lamSeq k ^ (((d : ℝ) + 1) / 2)))
  have hRnorm : Tendsto (fun k => eLpNorm (R k) 2 (volume.prod volume))
      atTop (𝓝 0) := by
    have hcoef : Tendsto (fun k => ‖(1 - lamSeq k ^ (((d : ℝ) + 1) / 2) : ℝ)‖ₑ)
        atTop (𝓝 0) := by
      have hc : Tendsto (fun k => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2) : ℝ))
          atTop (𝓝 0) := by
        have hp := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          ((Real.continuous_rpow_const (q := ((d : ℝ) + 1) / 2) (by positivity)).tendsto 1 |>.comp hlam_lim)
        simpa using! hp
      have ha := hc.abs
      have ha' : Tendsto (fun k => |1 - lamSeq k ^ (((d : ℝ) + 1) / 2)|)
          atTop (𝓝 (0 : ℝ)) := by simpa using! ha
      simpa [Real.norm_eq_abs, ← ofReal_norm] using!
        (ENNReal.continuous_ofReal.tendsto 0).comp ha'
    have hprod : Tendsto (fun k =>
        ‖(1 - lamSeq k ^ (((d : ℝ) + 1) / 2) : ℝ)‖ₑ *
          eLpNorm (G ∘ P k) 2 (volume.prod volume)) atTop (𝓝 0) := by
      have hp := ENNReal.Tendsto.mul hcoef (Or.inr hG.ne) hcompnorm
        (Or.inr (by norm_num : (0 : ℝ≥0∞) ≠ ⊤))
      simpa using! hp
    have hupper : Tendsto (fun k => eLpNorm (G ∘ P k - G) 2 (volume.prod volume) +
        ‖(1 - lamSeq k ^ (((d : ℝ) + 1) / 2) : ℝ)‖ₑ *
          eLpNorm (G ∘ P k) 2 (volume.prod volume)) atTop (𝓝 0) := by
      simpa using! hK_cont.add hprod
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [] with k
      exact bot_le
    · filter_upwards [] with k
      have hdecomp : R k = (G - G ∘ P k) +
          (fun xy => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) * (G ∘ P k) xy) := by
        funext xy
        dsimp [R]
        ring
      have hleft : AEStronglyMeasurable (G - G ∘ P k) (volume.prod volume) :=
        hG.aestronglyMeasurable.sub (hGcomp k).aestronglyMeasurable
      have hright : AEStronglyMeasurable
          (fun xy => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) * (G ∘ P k) xy)
          (volume.prod volume) :=
        (hGcomp k).aestronglyMeasurable.const_mul _
      have hle := eLpNorm_add_le (f := G - G ∘ P k) (g := fun xy => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) * (G ∘ P k) xy) (μ := volume.prod volume) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hswap : eLpNorm (G - G ∘ P k) 2 (volume.prod volume) =
          eLpNorm (G ∘ P k - G) 2 (volume.prod volume) := by
        have heq : G - G ∘ P k = -(G ∘ P k - G) := by
          funext xy
          simp only [Pi.sub_apply, Pi.neg_apply]
          ring
        rw [heq, eLpNorm_neg]
      rw [hswap] at hle
      calc
        eLpNorm (R k) 2 (volume.prod volume) =
            eLpNorm (G - G ∘ P k + fun xy =>
              (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) * (G ∘ P k) xy)
              2 (volume.prod volume) := by rw [hdecomp]
        _ ≤ eLpNorm (G ∘ P k - G) 2 (volume.prod volume) +
              eLpNorm (fun xy => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) *
                (G ∘ P k) xy) 2 (volume.prod volume) := hle
        _ = eLpNorm (G ∘ P k - G) 2 (volume.prod volume) +
            ‖(1 - lamSeq k ^ (((d : ℝ) + 1) / 2) : ℝ)‖ₑ *
              eLpNorm (G ∘ P k) 2 (volume.prod volume) := by
          have hsmul : (fun xy => (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) *
              (G ∘ P k) xy) =
              (1 - lamSeq k ^ (((d : ℝ) + 1) / 2)) • (G ∘ P k) := by
            rfl
          rw [hsmul, eLpNorm_const_smul]

  have hRraw_eq : ∀ k,
      (∫⁻ xy, ENNReal.ofReal ((R k xy) ^ 2) ∂(volume.prod volume)) =
        eLpNorm (R k) 2 (volume.prod volume) ^ (2 : ℝ) := by
    intro k
    calc
      (∫⁻ xy, ENNReal.ofReal ((R k xy) ^ 2) ∂(volume.prod volume)) =
          ∫⁻ xy, ‖R k xy‖ₑ ^ (2 : ℝ) ∂(volume.prod volume) := by
        apply lintegral_congr
        intro xy
        symm
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
        norm_num [Real.norm_eq_abs, sq_abs]
      _ = eLpNorm (R k) (2 : ℝ≥0) (volume.prod volume) ^ (2 : ℝ) := by
        symm
        exact eLpNorm_nnreal_pow_eq_lintegral (f := R k) (μ := volume.prod volume)
          (p := (2 : ℝ≥0)) (by norm_num) (hRmem k).aestronglyMeasurable

  have hμprod_le : μ.prod μ ≤ volume.prod volume := by
    simpa [μ, Measure.prod_restrict] using!
      (Measure.restrict_le_self :
        (volume.prod volume).restrict (U ×ˢ U) ≤ volume.prod volume)

  have hRraw_le : ∀ k,
      (∫⁻ xy, ENNReal.ofReal ((R k xy) ^ 2) ∂(μ.prod μ)) ≤
        eLpNorm (R k) 2 (volume.prod volume) ^ (2 : ℝ) := by
    intro k
    calc
      _ ≤ ∫⁻ xy, ENNReal.ofReal ((R k xy)^2) ∂(volume.prod volume) := lintegral_mono' hμprod_le (le_refl _)
      _ = _ := hRraw_eq k


  have hraw_err_eq : ∀ k,
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal ((((errClass k).val 0) x - ((errClass k).val 0) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 1)) =
        ∫⁻ xy, ENNReal.ofReal ((R k xy) ^ 2) ∂(μ.prod μ) := by
    intro k
    have herr : MemLp (fun x => ((errClass k).val 0) x) 2 μ := by
      simpa [μ] using! (Lp.memLp ((errClass k).val 0))
    have hnum : AEStronglyMeasurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          ((errClass k).val 0) xy.1 - ((errClass k).val 0) xy.2) (μ.prod μ) :=
      (herr.aestronglyMeasurable.comp_fst.sub herr.aestronglyMeasurable.comp_snd)
    have hden : Measurable
        (fun xy : SpatialCoordinates d × SpatialCoordinates d =>
          Real.rpow (Real.sqrt (∑ i : Fin d, (xy.1 i - xy.2 i) ^ 2))
            (((d : ℝ) + 1) / 2)) := by
      apply (Real.continuous_rpow_const (by positivity)).measurable.comp
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
    have hqmeas : AEMeasurable
        (fun xy => ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => ((errClass k).val 0) x) xy ^ 2)) (μ.prod μ) := by
      exact (hnum.aemeasurable.div hden.aemeasurable).pow_const 2 |>.ennreal_ofReal
    have hRmeas : AEMeasurable (fun xy => ENNReal.ofReal ((R k xy) ^ 2))
        (μ.prod μ) := by
      have hRrestrict : MemLp (R k) 2 (μ.prod μ) :=
        (hRmem k).mono_measure hμprod_le
      exact ((hRrestrict.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    have hpoint : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => ((errClass k).val 0) x) (x, y) = R k (x, y) := by
      have hcoe := (hFcomp k).coeFn_toLp
      have hsub := Lp.coeFn_sub (v.val 0) ((uClass k).val 0)
      filter_upwards [hsub, hcoe, ae_restrict_mem hUmeas] with x hsx hux hx
      filter_upwards [hsub, hcoe, ae_restrict_mem hUmeas] with y hsy huy hy
      have hxF : F (T k x) = f (T k x) := by
        simp only [F, Set.indicator_of_mem (hTmaps k x hx)]
      have hyF : F (T k y) = f (T k y) := by
        simp only [F, Set.indicator_of_mem (hTmaps k y hy)]
      have hGxy : G (x, y) = qv (x, y) := by
        change (U ×ˢ U).indicator qv (x, y) = qv (x, y)
        rw [Set.indicator_of_mem]
        exact ⟨hx, hy⟩
      have hGP : G (P k (x, y)) = qv (T k x, T k y) := by
        change (U ×ˢ U).indicator qv (T k x, T k y) = qv (T k x, T k y)
        rw [Set.indicator_of_mem]
        exact ⟨hTmaps k x hx, hTmaps k y hy⟩
      dsimp [aux_lem_19_smooth_density_one_step_dilation_kernel]
      rw [hsx, hsy]
      change ((f x - uFun k x) - (f y - uFun k y)) /
        Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
          (((d : ℝ) + 1) / 2) = R k (x, y)
      rw [hux, huy, Function.comp_apply, Function.comp_apply, hxF, hyF]
      calc
        ((f x - f (T k x)) - (f y - f (T k y))) /
            Real.rpow (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
              (((d : ℝ) + 1) / 2) =
            aux_lem_19_smooth_density_one_step_dilation_kernel f (x, y) -
              aux_lem_19_smooth_density_one_step_dilation_kernel
                (fun q => f (T k q)) (x, y) := by
                dsimp [aux_lem_19_smooth_density_one_step_dilation_kernel]
                ring
        _ = G (x, y) - lamSeq k ^ (((d : ℝ) + 1) / 2) * G (P k (x, y)) := by
          rw [hGxy, hGP]
          rw [aux_lem_19_smooth_density_one_step_dilation_kernel_comp
            f z (hlam0 k) x y]
        _ = R k (x, y) := by rfl
    calc
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          (aux_lem_19_smooth_density_one_step_dilation_kernel
            (fun x => ((errClass k).val 0) x) (x, y) ^ 2) ∂μ ∂μ := by
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro y
        simpa using! (aux_lem_19_smooth_density_one_step_dilation_kernel_sq
          (fun x => ((errClass k).val 0) x) (x, y)).symm
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((R k (x, y)) ^ 2) ∂μ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with x hx
        apply lintegral_congr_ae
        filter_upwards [hx] with y hy
        exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hy
      _ = _ := (lintegral_prod _ hRmeas).symm

  let a : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by
    dsimp [a]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨ENNReal.ofReal_pos.mpr halfFractionalOrder.2.1 |>.ne', hvoltop⟩
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact (ENNReal.div_lt_top ENNReal.ofReal_ne_top hvolpos.ne').ne
  have hsemi_formula : ∀ k,
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (errClass k).val =
        (a * (∫⁻ x in U, ∫⁻ y in U,
          ENNReal.ofReal ((((errClass k).val 0) x - ((errClass k).val 0) y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 1))) ^ (1 / 2 : ℝ) := by
    intro k
    unfold cubeFractionalL2Seminorm
    simp [a, U, halfFractionalOrder]
  let B : ℕ → ℝ≥0∞ := fun k =>
    (a * eLpNorm (R k) 2 (volume.prod volume) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hsemi_le : ∀ k,
      cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (errClass k).val ≤ B k := by
    intro k
    rw [hsemi_formula k, hraw_err_eq k]
    dsimp [B]
    exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (hRraw_le k) (bot_le : 0 ≤ a)) (by norm_num)
  have hRpow : Tendsto (fun k => eLpNorm (R k) 2 (volume.prod volume) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have hp := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
      |>.comp hRnorm
    simpa using! hp
  have hBa : Tendsto (fun k => a * eLpNorm (R k) 2 (volume.prod volume) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have hp := ENNReal.Tendsto.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
      (Or.inl ha0) hRpow (Or.inr ha_top)
    simpa using! hp
  have hB : Tendsto B atTop (𝓝 0) := by
    have hp := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hBa
    simpa [B] using! hp
  have hBtop : ∀ k, B k ≠ ⊤ := by
    intro k
    dsimp [B]
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top ha_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hRmem k).ne)
  have hBreal : Tendsto (fun k => (B k).toReal) atTop (𝓝 0) := by
    have hp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB
    simpa using! hp
  have hsemi_real : Tendsto
      (fun k => (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
        (errClass k).val).toReal) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBreal
    · filter_upwards [] with k
      exact ENNReal.toReal_nonneg
    · filter_upwards [] with k
      exact ENNReal.toReal_mono (hBtop k) (hsemi_le k)
  have hErrL2_eq : ∀ k,
      eLpNorm ((errClass k).val 0) 2 μ =
        eLpNorm (F ∘ T k - F) 2 μ := by
    intro k
    have hsub := Lp.coeFn_sub (v.val 0) ((uClass k).val 0)
    have hcoe := (hFcomp k).coeFn_toLp
    have hpoint : (fun x => ((errClass k).val 0) x) =ᵐ[μ]
        (F - F ∘ T k) := by
      filter_upwards [hsub, hcoe, ae_restrict_mem hUmeas] with x hs hu hx
      have hxF : F x = f x := by
        simp only [F, Set.indicator_of_mem hx]
      have hTxF : F (T k x) = f (T k x) := by
        simp only [F, Set.indicator_of_mem (hTmaps k x hx)]
      have hsubclass : (errClass k).val 0 x =
          ((v.val 0 - (uClass k).val 0) x) := by
        simp [errClass]
      rw [hsubclass, hs]
      simp only [Pi.sub_apply, Function.comp_apply]
      change (v.val 0 x - uFun k x) = F x - F (T k x)
      rw [hxF]
      rw [hu, Function.comp_apply, hTxF]
    have hfirst : eLpNorm ((errClass k).val 0) 2 μ =
        eLpNorm (F - F ∘ T k) 2 μ :=
      eLpNorm_congr_ae hpoint
    have hneg : F - F ∘ T k = -(F ∘ T k - F) := by
      funext x
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [hfirst, hneg, eLpNorm_neg]
  have hErrL2 : Tendsto
      (fun k => (eLpNorm ((errClass k).val 0) 2 μ).toReal) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hF_cont_restrict
    exact ht.congr' (Filter.Eventually.of_forall fun k =>
      congrArg ENNReal.toReal (hErrL2_eq k).symm)
  have hcube_eq : ∀ k, cubeFractionalL2Norm hd z r hr halfFractionalOrder
      (errClass k) =
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
          (errClass k).val).toReal +
          (r ^ (-(halfFractionalOrder : ℝ)) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
            (eLpNorm ((errClass k).val 0) 2 μ).toReal := by
    intro k
    unfold cubeFractionalL2Norm
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _), Lp.norm_def]
    ring
  have htotal : Tendsto (fun k =>
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
        (errClass k).val).toReal +
        (r ^ (-(halfFractionalOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
          (eLpNorm ((errClass k).val 0) 2 μ).toReal) atTop (𝓝 0) := by
    have hmul := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
      atTop (𝓝 (r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))))).mul
      hErrL2
    simpa using! hsemi_real.add hmul
  have hsmall : ∀ᶠ k in atTop, cubeFractionalL2Norm hd z r hr
      halfFractionalOrder (errClass k) < η := by
    exact htotal.congr' (Filter.Eventually.of_forall fun k =>
      (hcube_eq k).symm) |>.eventually (eventually_lt_nhds hη)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hsmall)
  have hNk : cubeFractionalL2Norm hd z r hr halfFractionalOrder
      (errClass N) < η := hN N le_rfl
  have hlam_lt1 : lamSeq N < 1 := by
    dsimp [lamSeq]
    linarith [inv_pos.mpr (by positivity : (0 : ℝ) < (N : ℝ) + 2)]
  have hDil : ∀ k, (uClass k).val 0 =ᵐ[μ]
      (v.val 0) ∘ T k := by
    intro k
    have hcoe := (hFcomp k).coeFn_toLp
    filter_upwards [hcoe, ae_restrict_mem hUmeas] with x hu hx
    have hTxF : F (T k x) = f (T k x) := by
      simp only [F, Set.indicator_of_mem (hTmaps k x hx)]
    change uFun k x = (v.val 0) (T k x)
    rw [hu, Function.comp_apply, hTxF]
  refine ⟨⟨lamSeq N, hlam0 N, hlam_lt1⟩, uClass N, errClass N, ?_, ?_, ?_⟩
  · simpa [μ, T, lamSeq] using! hDil N
  · simp [errClass]
  · exact hNk

end SubdiffusiveProcess.Paper
