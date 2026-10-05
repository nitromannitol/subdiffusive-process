module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.EnergyStability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.L2Stability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence

@[expose] public section

/-! Stability of the weak Dirichlet problem with divergence-form datum under uniform perturbation of
the coefficient: two solutions with the same boundary datum and source differ by a zero-trace
function whose gradient energy is bounded by the coefficient defect. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- The energy identity for two divergence-form solutions with the same source. -/
theorem aux_lem_as_regularity_dirichlet_stability_energy_eq {W : Set (Vec d)}
    {a b : Vec d → ℝ} {u v : H1Function W} {w : H10Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn a W u g) (hv : IsDivFormWeakSolutionOn b W v g)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x)
    (hintv : IntegrableOn (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W)
    (hintu : IntegrableOn (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W)
    (hE : IntegrableOn (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W)
    (hD : IntegrableOn (fun x ↦ (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x)) W) :
    ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume =
      ∫ x in W, (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x) ∂volume := by
  have hvw := hv w
  have huw := hu w
  have hsub : ∫ x in W, (vecDot (b x • v.grad x) (w.toH1Function.grad x) -
      vecDot (a x • u.grad x) (w.toH1Function.grad x)) ∂volume = 0 := by
    rw [integral_sub hintv hintu, hvw, huw, sub_self]
  have h : ∫ x in W, (b x * vecNormSq (w.toH1Function.grad x) -
      (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x)) ∂volume = 0 := by
    rw [← hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    exact (energy_integrand_eq hgrad x).symm
  rw [integral_sub hE hD, sub_eq_zero] at h
  exact h

/-- Energy comparison with a window-local coefficient defect and a common source. -/
theorem aux_lem_as_regularity_dirichlet_stability_window {W : Set (Vec d)}
    {a b : Vec d → ℝ} {lam Lam lam' Lam' K : ℝ}
    {u v : H1Function W} {w : H10Function W} {g : Vec d → Vec d}
    (hW : MeasurableSet W) (hlam : 0 < lam) (hKnn : 0 ≤ K)
    (hElla : IsEllipticFieldOn lam' Lam' W (scalarCoeffField a))
    (hEllb : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (hb : ∀ x ∈ W, lam ≤ b x) (hK : ∀ x ∈ W, |a x - b x| ≤ K)
    (hu : IsDivFormWeakSolutionOn a W u g) (hv : IsDivFormWeakSolutionOn b W v g)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x) :
    ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume ≤
      (K / lam) ^ 2 * ∫ x in W, vecNormSq (u.grad x) ∂volume := by
  set Iw := ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume with hIwdef
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  have hIw : IntegrableOn (fun x ↦ vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hIu : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W :=
    integrableOn_vecNormSq_h1Grad u
  have hE : IntegrableOn
      (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_mul_vecNormSq_grad hEllb w.toH1Function
  have hD : IntegrableOn
      (fun x ↦ (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_defect hElla hEllb u w.toH1Function
  have hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hEllb v w.toH1Function
  have hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hElla u w.toH1Function
  have hleft : lam * Iw ≤
      ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [hIwdef, ← integral_const_mul]
    exact lower_bound_energy_on hW hb (hIw.const_mul lam) hE
  have hYoung : ∀ x ∈ W,
      (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x) ≤
        K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
          lam / 2 * vecNormSq (w.toH1Function.grad x) := by
    intro x hx
    refine (defect_le_at hKnn u.grad w.toH1Function.grad (hK x hx)).trans ?_
    have hy := young_pointwise (K := K) (A := euclideanNorm (u.grad x))
      (B := euclideanNorm (w.toH1Function.grad x)) hlam
    rwa [euclideanNorm_sq, euclideanNorm_sq] at hy
  have hRint : IntegrableOn
      (fun x ↦ K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
        lam / 2 * vecNormSq (w.toH1Function.grad x)) W :=
    (hIu.const_mul _).add (hIw.const_mul _)
  have hright : ∫ x in W, (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x) ∂volume ≤
      K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    have hmono := setIntegral_mono_on hD hRint hW hYoung
    rwa [integral_add (hIu.const_mul _) (hIw.const_mul _),
      integral_const_mul, integral_const_mul] at hmono
  have hid := aux_lem_as_regularity_dirichlet_stability_energy_eq hu hv hgrad hintv hintu hE hD
  have hchain : lam * Iw ≤ K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    rw [hid] at hleft; exact hleft.trans hright
  have hhalf : lam / 2 * Iw ≤ K ^ 2 / (2 * lam) * Iu := by linarith
  have key : lam ^ 2 * Iw ≤ K ^ 2 * Iu := by
    have h := mul_le_mul_of_nonneg_left hhalf (by linarith : (0 : ℝ) ≤ 2 * lam)
    calc lam ^ 2 * Iw = 2 * lam * (lam / 2 * Iw) := by ring
      _ ≤ 2 * lam * (K ^ 2 / (2 * lam) * Iu) := h
      _ = K ^ 2 * Iu := by field_simp
  rw [div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
  linarith [key]

/-- Two solutions with the same datum differ by a zero-trace function. -/
theorem aux_lem_as_regularity_dirichlet_stability_diff {Q : Homogenization.TriadicCube d}
    {a b : Vec d → ℝ} {u v h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionOn a Q u h g) (hv : IsDirichletSolutionOn b Q v h g) :
    ∃ w : H10Function (openCubeSet Q), (∀ x, v.toFun x = u.toFun x + w.toH1Function.toFun x) ∧
      ∀ x, v.grad x = u.grad x + w.toH1Function.grad x := by
  obtain ⟨w₁, hf1, hg1⟩ := hu.1
  obtain ⟨w₂, hf2, hg2⟩ := hv.1
  refine ⟨w₂ - w₁, fun x => ?_, fun x => ?_⟩
  · have : (w₂ - w₁).toH1Function.toFun x = w₂.toH1Function.toFun x - w₁.toH1Function.toFun x := by
      change w₂.toH1Function.toFun x + (-1 : ℝ) * w₁.toH1Function.toFun x = _
      ring
    rw [this, hf2 x, hf1 x]; ring
  · have : (w₂ - w₁).toH1Function.grad x = w₂.toH1Function.grad x - w₁.toH1Function.grad x := by
      change w₂.toH1Function.grad x + (-1 : ℝ) • w₁.toH1Function.grad x = _
      rw [neg_one_smul]; abel
    rw [this, hg2 x, hg1 x]; abel

/-- Uniform convergence of the coefficients gives `L²` convergence of the Dirichlet solutions. -/
theorem lem_as_regularity_dirichlet_stability [NeZero d]
    {Q : Homogenization.TriadicCube d}
    {a : Vec d → ℝ} {b : ℕ → Vec d → ℝ} {lam Lam lam' Lam' : ℝ}
    {u h : H1Function (openCubeSet Q)} {v : ℕ → H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hlam : 0 < lam) (hElla : IsEllipticFieldOn lam' Lam' (openCubeSet Q) (scalarCoeffField a))
    (hEllb : ∀ k, IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField (b k)))
    (hb : ∀ k, ∀ x ∈ openCubeSet Q, lam ≤ b k x)
    (hu : IsDirichletSolutionOn a Q u h g) (hv : ∀ k, IsDirichletSolutionOn (b k) Q (v k) h g)
    (hdefect : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ openCubeSet Q, |a x - b k x| ≤ ε) :
    Tendsto (fun k => ∫ x in openCubeSet Q, ((v k).toFun x - u.toFun x) ^ 2 ∂volume)
      atTop (𝓝 0) := by
  classical
  have hWm : MeasurableSet (openCubeSet Q) := (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
  choose w hwf hwg using fun k => aux_lem_as_regularity_dirichlet_stability_diff hu (hv k)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_poincare_integral_const
    (isOpenBoundedConvexDomain_openCubeSet Q) hWm
  set Iu := ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume with hIudef
  have hIunn : 0 ≤ Iu := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  have henergy : Tendsto (fun k ↦ ∫ x in openCubeSet Q,
      vecNormSq ((w k).toH1Function.grad x) ∂volume) atTop (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    set eta : ℝ := lam * Real.sqrt (ε / (Iu + 1)) with hetadef
    have hquot : 0 < ε / (Iu + 1) := div_pos hε (by linarith)
    have hetapos : 0 < eta := mul_pos hlam (Real.sqrt_pos.2 hquot)
    filter_upwards [hdefect eta hetapos] with k hk
    have hEnn : 0 ≤ ∫ x in openCubeSet Q, vecNormSq ((w k).toH1Function.grad x) ∂volume :=
      setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
    have hbound := aux_lem_as_regularity_dirichlet_stability_window (u := u) (v := v k) (w := w k)
      hWm hlam hetapos.le hElla (hEllb k) (hb k) hk hu.2 (hv k).2 (hwg k)
    have hratio : (eta / lam) ^ 2 = ε / (Iu + 1) := by
      have heq : eta / lam = Real.sqrt (ε / (Iu + 1)) := by
        rw [hetadef]; field_simp
      rw [heq, Real.sq_sqrt hquot.le]
    rw [hratio] at hbound
    have hlt : ε / (Iu + 1) * Iu < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < Iu + 1)]
      nlinarith
    have : ∫ x in openCubeSet Q, vecNormSq ((w k).toH1Function.grad x) ∂volume < ε :=
      lt_of_le_of_lt hbound hlt
    rwa [Real.norm_eq_abs, abs_of_nonneg hEnn]
  refine squeeze_zero (fun k ↦ setIntegral_nonneg hWm fun x _ ↦ sq_nonneg _) (fun k ↦ ?_)
    (by simpa using henergy.const_mul Cp)
  have := hCp (w k)
  have hcongr : ∫ x in openCubeSet Q, ((v k).toFun x - u.toFun x) ^ 2 ∂volume =
      ∫ x in openCubeSet Q, (w k).toH1Function.toFun x ^ 2 ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    show ((v k).toFun x - u.toFun x) ^ 2 = (w k).toH1Function.toFun x ^ 2
    rw [hwf k x]; ring
  rw [hcongr]
  exact this

end SubdiffusiveProcess.Paper
