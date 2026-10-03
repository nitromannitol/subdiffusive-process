module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The support of a square is the support of the function. -/
private theorem support_sq_eq_rows {f : Vec d → ℝ} :
    Function.support (fun x ↦ f x ^ 2) = Function.support f := by
  ext x
  simp [Function.mem_support]

/-- The differential of a square, evaluated on a coordinate direction. -/
private theorem fderiv_sq_apply_rows {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y ↦ f y ^ 2) x) (basisVec i) =
      2 * f x * (fderiv ℝ f x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ f x :=
    hf.differentiable (by simp) x
  have h := (hdiff.hasFDerivAt).pow 2
  rw [h.fderiv]
  simp [mul_comm, mul_assoc]



theorem massive_cutoff_mass_energy_le_of_zero_forcing
    {a : Vec d → ℝ} {mu lam Lam : ℝ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (w : H1Function W)
    (hw : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W w (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1)
    {K : ℝ} (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    mu * ∫ x in W, chi x ^ 2 * w.toFun x ^ 2 ∂volume +
        2⁻¹ * ∫ x in W, a x * chi x ^ 2 * vecNormSq (w.grad x) ∂volume ≤
      2 * ∫ x in W, a x * w.toFun x ^ 2 *
          vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  set gchi : Vec d → Vec d := fun x i ↦ (fderiv ℝ chi x) (basisVec i) with hgchi_def
  set eta : Vec d → ℝ := fun x ↦ chi x ^ 2 with heta_def
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta := hchi.pow 2
  have hetaC : HasCompactSupport eta := by
    apply HasCompactSupport.intro hchiC.isCompact
    intro x hx
    have : chi x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    simp [heta_def, this]
  have hetaS : tsupport eta ⊆ W := by
    refine le_trans (closure_mono ?_) hchiS
    exact le_of_eq (support_sq_eq_rows (f := chi))
  set phi : H10Function W :=
    w.mulContDiffHasCompactSupportToH10 hW heta hetaC hetaS with hphi_def
  have hphi_toFun : phi.toH1Function.toFun = fun x ↦ eta x * w.toFun x :=
    H1Function.mulContDiffHasCompactSupportToH10_toFun w hW heta hetaC hetaS
  set psi : H1Function W := w.mulContDiffHasCompactSupport heta hetaC with hpsi_def
  have hpsi_toFun : psi.toFun = fun x ↦ eta x * w.toFun x := by
    simp [hpsi_def]
  have hpsi_grad : psi.grad =
      fun x i ↦ eta x * w.grad x i + w.toFun x * (fderiv ℝ eta x) (basisVec i) := by
    simp [hpsi_def]
  have hgrad : phi.toH1Function.grad =ᵐ[volume.restrict W] psi.grad := by
    refine Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen ?_
    filter_upwards with x
    rw [hphi_toFun, hpsi_toFun]
  have heq := hw phi
  have hgchi_cont : Continuous gchi := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hint_min : IntegrableOn
      (fun x ↦ a x * w.toFun x ^ 2 * vecNormSq (gchi x)) W :=
    integrableOn_value_gradSq hWmeas hEll w hgchi_cont hK
  have hint_chi : IntegrableOn
      (fun x ↦ a x * chi x ^ 2 * vecNormSq (w.grad x)) W :=
    integrableOn_cutoff_energy hWmeas hEll w
      hchi.continuous.aestronglyMeasurable hchi_le
  have hint_energy : IntegrableOn
      (fun x ↦ vecDot (a x • w.grad x) (psi.grad x)) W :=
    integrableOn_energy_term hEll w.grad_memVectorL2 psi.grad_memVectorL2
  have hptwise : ∀ x,
      a x * chi x ^ 2 * vecNormSq (w.grad x) / 2 -
          2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x)) ≤
        vecDot (a x • w.grad x) (psi.grad x) := by
    intro x
    have hd : psi.grad x =
        fun i ↦ chi x ^ 2 * w.grad x i + w.toFun x * (2 * chi x * gchi x i) := by
      rw [hpsi_grad]
      funext i
      simp only [heta_def, hgchi_def, fderiv_sq_apply_rows hchi x i]
    have hexp : vecDot (a x • w.grad x) (psi.grad x) =
        a x * (chi x ^ 2 * vecNormSq (w.grad x) +
          2 * chi x * w.toFun x * vecDot (w.grad x) (gchi x)) := by
      rw [hd]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
      congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hyoung := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (chi x) (2 * w.toFun x) (w.grad x) (gchi x)
    have hyoung' : -(chi x ^ 2 * vecNormSq (w.grad x) / 2 +
          (2 * w.toFun x) ^ 2 * vecNormSq (gchi x) / 2) ≤
        chi x * (2 * w.toFun x) * vecDot (w.grad x) (gchi x) :=
      neg_le_of_abs_le hyoung
    have hGnn := vecNormSq_nonneg (w.grad x)
    have hgnn := vecNormSq_nonneg (gchi x)
    have hax := haNonneg x
    rw [hexp]
    nlinarith [mul_nonneg hax (mul_nonneg (sq_nonneg (chi x)) hGnn),
      mul_nonneg hax hgnn, hyoung']
  simp only [one_mul, zero_mul, integral_zero, hphi_toFun, heta_def] at heq
  have hmass : ∫ x in W, w.toFun x * (chi x ^ 2 * w.toFun x) ∂volume =
      ∫ x in W, chi x ^ 2 * w.toFun x ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  have henergy_eq : ∫ x in W, vecDot (a x • w.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, vecDot (a x • w.grad x) (psi.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have hminInt : Integrable
      (fun x ↦ a x * chi x ^ 2 * vecNormSq (w.grad x) / 2 -
        2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x)))
      (volume.restrict W) := (hint_chi.div_const 2).sub (hint_min.const_mul 2)
  have hmono : ∫ x in W, (a x * chi x ^ 2 * vecNormSq (w.grad x) / 2 -
        2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume ≤
      ∫ x in W, vecDot (a x • w.grad x) (psi.grad x) ∂volume :=
    integral_mono hminInt hint_energy (fun x ↦ hptwise x)
  have hminEq : ∫ x in W, (a x * chi x ^ 2 * vecNormSq (w.grad x) / 2 -
        2 * (a x * w.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume =
      (∫ x in W, a x * chi x ^ 2 * vecNormSq (w.grad x) ∂volume) / 2 -
        2 * ∫ x in W, a x * w.toFun x ^ 2 * vecNormSq (gchi x) ∂volume := by
    rw [integral_sub (hint_chi.div_const 2) (hint_min.const_mul 2),
      integral_div, integral_const_mul]
  rw [hmass, henergy_eq] at heq
  rw [hminEq] at hmono
  linarith


/-! ### The contraction between a set and a surrounding cutoff domain -/



theorem massive_local_l2_contraction_of_cutoff
    {a : Vec d → ℝ} {lam Lam t K : ℝ} {W S : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ W, a x ≤ Lam) (ht : 0 < t)
    (hSW : S ⊆ W) (hSmeas : MeasurableSet S)
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ S, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    (∫ x in S, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      4 * t * Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  set gchi : Vec d → Vec d := fun x i ↦ (fderiv ℝ chi x) (basisVec i) with hgchi_def
  have hK0 : (0 : ℝ) ≤ K := le_trans (vecNormSq_nonneg _) (hK 0)
  have hgchi_cont : Continuous gchi := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hmain := massive_cutoff_mass_energy_le_of_zero_forcing hW hEll haNonneg u hu
    hchi hchiC hchiS hchi_le hK
  -- integrability of the three densities on `W`
  have husq : IntegrableOn (fun x ↦ u.toFun x ^ 2) W := u.memL2.integrable_sq
  have hcutsq : IntegrableOn (fun x ↦ chi x ^ 2 * u.toFun x ^ 2) W := by
    refine Integrable.mono' husq
      ((hchi.continuous.aestronglyMeasurable.pow 2).mul
        husq.aestronglyMeasurable) ?_
    filter_upwards with x
    have h1 : chi x ^ 2 ≤ 1 := by
      have := hchi_le x
      nlinarith [abs_nonneg (chi x), sq_abs (chi x)]
    have h2 : (0 : ℝ) ≤ u.toFun x ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (chi x)]
  have hint_chi : IntegrableOn
      (fun x ↦ a x * chi x ^ 2 * vecNormSq (u.grad x)) W :=
    integrableOn_cutoff_energy hWmeas hEll u
      hchi.continuous.aestronglyMeasurable hchi_le
  have hint_min : IntegrableOn
      (fun x ↦ a x * u.toFun x ^ 2 * vecNormSq (gchi x)) W :=
    integrableOn_value_gradSq hWmeas hEll u hgchi_cont hK
  -- the right-hand side
  have hrhs : ∫ x in W, a x * u.toFun x ^ 2 * vecNormSq (gchi x) ∂volume ≤
      Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume := by
    have hmono : ∫ x in W, a x * u.toFun x ^ 2 * vecNormSq (gchi x) ∂volume ≤
        ∫ x in W, Lam * K * u.toFun x ^ 2 ∂volume := by
      refine setIntegral_mono_on hint_min (husq.const_mul _) hWmeas ?_
      intro x hx
      have h1 : a x * u.toFun x ^ 2 * vecNormSq (gchi x) ≤
          Lam * u.toFun x ^ 2 * vecNormSq (gchi x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (haLe x hx) (sq_nonneg _))
          (vecNormSq_nonneg _)
      have h2 : Lam * u.toFun x ^ 2 * vecNormSq (gchi x) ≤
          Lam * u.toFun x ^ 2 * K :=
        mul_le_mul_of_nonneg_left (hK x) (by positivity)
      calc a x * u.toFun x ^ 2 * vecNormSq (gchi x) ≤
            Lam * u.toFun x ^ 2 * vecNormSq (gchi x) := h1
        _ ≤ Lam * u.toFun x ^ 2 * K := h2
        _ = Lam * K * u.toFun x ^ 2 := by ring
    rwa [integral_const_mul] at hmono
  -- the two left-hand pieces
  have hleft1 : ∫ x in S, u.toFun x ^ 2 ∂volume ≤
      ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume := by
    have hcongr : ∫ x in S, u.toFun x ^ 2 ∂volume =
        ∫ x in S, chi x ^ 2 * u.toFun x ^ 2 ∂volume := by
      refine setIntegral_congr_fun hSmeas fun x hx ↦ ?_
      rw [hchi_one x hx]
      ring
    rw [hcongr]
    refine setIntegral_mono_set hcutsq ?_ (Filter.Eventually.of_forall hSW)
    filter_upwards with x
    positivity
  have hleft2 : ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      ∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
    have hcongr : ∫ x in S, a x * vecNormSq (u.grad x) ∂volume =
        ∫ x in S, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
      refine setIntegral_congr_fun hSmeas fun x hx ↦ ?_
      rw [hchi_one x hx]
      ring
    rw [hcongr]
    refine setIntegral_mono_set hint_chi ?_ (Filter.Eventually.of_forall hSW)
    filter_upwards with x
    have := haNonneg x
    have := vecNormSq_nonneg (u.grad x)
    positivity
  -- combine
  have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  have hstep : t⁻¹ * ∫ x in S, u.toFun x ^ 2 ∂volume +
      2⁻¹ * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      2 * (Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume) := by
    have h1 : t⁻¹ * ∫ x in S, u.toFun x ^ 2 ∂volume ≤
        t⁻¹ * ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume :=
      mul_le_mul_of_nonneg_left hleft1 htinv.le
    have h2 : 2⁻¹ * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
        2⁻¹ * ∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume :=
      mul_le_mul_of_nonneg_left hleft2 (by norm_num)
    linarith
  have hAnn : (0 : ℝ) ≤ ∫ x in S, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg hSmeas fun x _ ↦ sq_nonneg _
  have hfinal : ∫ x in S, u.toFun x ^ 2 ∂volume +
      t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      4 * t * (Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume) := by
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 * t)
    have hL : 2 * t * (t⁻¹ * ∫ x in S, u.toFun x ^ 2 ∂volume +
          2⁻¹ * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume) =
        2 * (∫ x in S, u.toFun x ^ 2 ∂volume) +
          t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume := by
      field_simp
    rw [hL] at hmul
    linarith
  calc (∫ x in S, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
        4 * t * (Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume) := hfinal
    _ = 4 * t * Lam * K * ∫ x in W, u.toFun x ^ 2 ∂volume := by ring


/-! ### The centred threefold enlargement of a triadic cube -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay in
/-- A cube sits inside its centred threefold enlargement. -/
theorem translatedCube_subset_succ (d : ℕ) (n : ℤ) (z : Vec d) :
    translatedCube d n z ⊆ translatedCube d (n + 1) z := by
  intro x hx
  rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := zpow_add_one₀ (by norm_num) n
  have := hx i
  rw [hsucc]
  constructor <;> nlinarith [this.1, this.2]

/-- The explicit squared-gradient bound of the cutoff adapted to a triadic cube
of side `3ⁿ` inside its centred threefold enlargement. -/
def translatedCubeCutoffGradBound (d : ℕ) (n : ℤ) : ℝ :=
  (d : ℝ) * (16 / ((1 / 2 : ℝ) * 3 ^ n)) ^ 2

theorem translatedCubeCutoffGradBound_eq (d : ℕ) (n : ℤ) :
    translatedCubeCutoffGradBound d n = 1024 * (d : ℝ) * ((3 : ℝ) ^ n)⁻¹ ^ 2 := by
  have h3 : ((3 : ℝ) ^ n) ≠ 0 := by positivity
  unfold translatedCubeCutoffGradBound
  field_simp
  ring

theorem translatedCubeCutoffGradBound_nonneg (d : ℕ) (n : ℤ) :
    0 ≤ translatedCubeCutoffGradBound d n := by
  unfold translatedCubeCutoffGradBound
  positivity

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay in
/-- **A smooth cutoff adapted to a triadic cube and its centred threefold
enlargement.**  It equals `1` on `z + □_n`, is supported in `z + □_{n+1}`,
takes values in `[-1,1]` and has squared gradient at most
`translatedCubeCutoffGradBound d n`. -/
theorem exists_smooth_translatedCube_cutoff (d : ℕ) (n : ℤ) (z : Vec d) :
    ∃ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ (∀ x, |chi x| ≤ 1) ∧
      (∀ x ∈ translatedCube d n z, chi x = 1) ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ translatedCube d (n + 1) z ∧
      ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        translatedCubeCutoffGradBound d n := by
  classical
  set r : ℝ := (1 / 2 : ℝ) * 3 ^ n with hr_def
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hr : 0 < r := by rw [hr_def]; positivity
  have hle : (fun i ↦ z i - r) ≤ (fun i ↦ z i + r) := by
    intro i
    dsimp only
    linarith
  obtain ⟨eta, hsmooth, hIcc, hone, hzero, _hderiv, hsq, _hvol⟩ :=
    exists_smoothBoxCutoff (fun i ↦ z i - r) (fun i ↦ z i + r) r hr hle
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := zpow_add_one₀ (by norm_num) n
  refine ⟨eta, hsmooth, fun x ↦ ?_, fun x hx ↦ ?_, ?_, ?_, fun x ↦ ?_⟩
  · exact abs_le.2 ⟨by linarith [(hIcc x).1], (hIcc x).2⟩
  · refine hone x ?_
    rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff] at hx
    refine Set.mem_Icc.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · have := (hx i).1
      simp only [Pi.sub_apply] at this
      simp only [hr_def]
      linarith
    · have := (hx i).2
      simp only [Pi.sub_apply] at this
      simp only [hr_def]
      linarith
  · refine HasCompactSupport.intro (K := Set.Icc (fun i ↦ z i - r - r)
      (fun i ↦ z i + r + r)) isCompact_Icc fun x hx ↦ hzero x hx
  · refine le_trans (closure_mono (Function.support_subset_iff'.2 fun x hx ↦ hzero x hx)) ?_
    rw [IsClosed.closure_eq isClosed_Icc]
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
    intro i
    have h1 := hx.1 i
    have h2 := hx.2 i
    simp only [hr_def] at h1 h2
    simp only [Pi.sub_apply]
    rw [hsucc]
    constructor <;> nlinarith
  · have hbound := hsq x
    have hcalc : vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) =
        ∑ i, ((fderiv ℝ eta x) (Pi.single i 1)) ^ 2 := by
      simp [vecNormSq, vecDot, basisVec, pow_two]
    rw [hcalc]
    exact le_trans hbound (le_of_eq (by rw [translatedCubeCutoffGradBound, hr_def]))

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay in


theorem localL2_resolvent_translatedCube_contraction
    {a : Vec d → ℝ} {lam Lam t : ℝ} {n : ℤ} {z : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ translatedCube d (n + 1) z, a x ≤ Lam) (ht : 0 < t)
    (u : H1Function (translatedCube d (n + 1) z))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) z) u (fun _ ↦ (0 : ℝ))) :
    (∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in translatedCube d n z, a x * vecNormSq (u.grad x) ∂volume ≤
      4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 *
        ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  obtain ⟨chi, hchi, hchi_le, hchi_one, hchiC, hchiS, hK⟩ :=
    exists_smooth_translatedCube_cutoff d n z
  have hbase := massive_local_l2_contraction_of_cutoff
    (isOpenBoundedConvexDomain_translatedCube d (n + 1) z) hEll haNonneg hLam
    haLe ht (translatedCube_subset_succ d n z)
    (isOpenBoundedConvexDomain_translatedCube d n z).isOpen.measurableSet u hu
    hchi hchiC hchiS hchi_le hchi_one hK
  refine hbase.trans (le_of_eq ?_)
  rw [translatedCubeCutoffGradBound_eq]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
