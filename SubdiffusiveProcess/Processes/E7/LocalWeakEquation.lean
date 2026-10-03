module

public import SubdiffusiveProcess.Processes.E7.Galerkin

@[expose] public section

/-!
# Local `H¹` regularity of form-domain elements and the local weak equation

A form-domain element `u` (with its gradient `g`, a point of the closed graph) has weak gradient `g`
on every bounded open `W` (integration by parts against test functions), and is in `H¹(W)` because
the weights are bounded below and above on the bounded set `W`. The resolvent of the form solves
the weak massive equation tested against `H¹₀(W)`.
-/
open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- A positive continuous weight is bounded below by a positive constant on a bounded set. -/
theorem exists_lower_bound {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {W : Set (St d)} (hWb : Bornology.IsBounded W) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ W, m ≤ w x := by
  have hK : IsCompact (closure W) := hWb.isCompact_closure
  rcases (closure W).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x hx => absurd (subset_closure hx) (by simp [h])⟩
  · obtain ⟨x0, _, hmin⟩ := hK.exists_isMinOn h hw.continuousOn
    exact ⟨w x0, hpos x0, fun x hx => hmin (subset_closure hx)⟩

/-- Lebesgue measure on a bounded measurable set is dominated by a multiple of `wm w`. -/
theorem restrict_le_smul_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {W : Set (St d)} (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (volume : Measure (St d)).restrict W ≤ C • wm w := by
  obtain ⟨m, hm, hmw⟩ := exists_lower_bound hw hpos hWb
  have hm0 : ENNReal.ofReal m ≠ 0 := by simpa using hm
  refine ⟨(ENNReal.ofReal m)⁻¹, ENNReal.inv_ne_top.mpr hm0, ?_⟩
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply, smul_eq_mul, wm,
    withDensity_apply _ hs]
  calc volume (s ∩ W)
      = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * volume (s ∩ W)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ x in s, ENNReal.ofReal (w x) := by
        gcongr
        calc ENNReal.ofReal m * volume (s ∩ W)
            = ∫⁻ x in s ∩ W, ENNReal.ofReal m := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in s ∩ W, ENNReal.ofReal (w x) :=
            setLIntegral_mono' (hs.inter hW)
              (fun x hx => ENNReal.ofReal_le_ofReal (hmw x hx.2))
          _ ≤ ∫⁻ x in s, ENNReal.ofReal (w x) := lintegral_mono_set inter_subset_left

/-- `L²(w dx)` functions are `L²` on bounded measurable sets for Lebesgue measure. -/
theorem memLp_restrict_of_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {W : Set (St d)} (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) {u : St d → ℝ}
    (hu : MemLp u 2 (wm w)) : MemLp u 2 (volume.restrict W) := by
  obtain ⟨C, hC, hle⟩ := restrict_le_smul_wm hw hpos hW hWb
  exact hu.of_measure_le_smul hC hle

/-- A graph point has the pairing identity against a test function supported in `W`, as a
weak-derivative identity on `W`. -/
theorem hasWeakPartialDeriv_of_mem_gradGraph {c ρ : St d → ℝ} (hc : Continuous c)
    (hρ : Continuous ρ) (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (St d)}
    {u : Lp ℝ 2 (wm ρ)} {g : Fin d → Lp ℝ 2 (wm c)} (h : (u, g) ∈ gradGraph hc hρ)
    (i : Fin d) :
    HasWeakPartialDerivOn W i (fun x => u x) (fun x => g i x) := by
  intro φ hφ hφc hφW
  have hp := gradGraph_pairing hc hρ hcpos hρpos (ψ := φ) ⟨hφ, hφc⟩ i (u, g) h
  dsimp only at hp
  have hz1 : ∀ x ∉ W, u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have : fderiv ℝ φ x = 0 :=
      Function.notMem_support.mp fun hs => hx (hφW (support_fderiv_subset ℝ hs))
    simp [this]
  have hz2 : ∀ x ∉ W, g i x * φ x = 0 := by
    intro x hx
    have : φ x = 0 := Function.notMem_support.mp fun hs => hx (hφW (subset_tsupport _ hs))
    simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  have e1 : ∫ x, u x * (fderiv ℝ φ x) (basisVec i) = ∫ x, dpartial i φ x * u x :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [dpartial, basisVec]; ring)
  have e2 : ∫ x, g i x * φ x = ∫ x, φ x * g i x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e1, e2]
  linarith

/-- The `H¹(W)` function of a graph point over a bounded open set. -/
def h1OfGraph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u : Lp ℝ 2 (wm ρ)) (g : Fin d → Lp ℝ 2 (wm c))
    (h : (u, g) ∈ gradGraph hc hρ) : H1Function W where
  toFun := fun x => u x
  grad := fun x i => g i x
  memL2 := memLp_restrict_of_wm hρ hρpos hW.measurableSet hWb (Lp.memLp u)
  gradMemL2 := fun i => memLp_restrict_of_wm hc hcpos hW.measurableSet hWb (Lp.memLp (g i))
  hasWeakGradient := fun i => hasWeakPartialDeriv_of_mem_gradGraph hc hρ hcpos hρpos h i

/-- The `H¹(W)` function of a form-domain element (with its form gradient). -/
def h1OfDomain {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u : Lp ℝ 2 (wm ρ)) (hu : u ∈ gradDomain hc hρ) :
    H1Function W :=
  h1OfGraph hc hρ hcpos hρpos hW hWb u (gradOf hc hρ u)
    ((mem_gradGraph_iff hc hρ hcpos hρpos u _).2 ⟨hu, rfl⟩)

theorem h1OfDomain_toFun {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u : Lp ℝ 2 (wm ρ)) (hu : u ∈ gradDomain hc hρ) (x : Vec d) :
    (h1OfDomain hc hρ hcpos hρpos hW hWb u hu).toFun x = u x := rfl

theorem h1OfDomain_grad {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u : Lp ℝ 2 (wm ρ)) (hu : u ∈ gradDomain hc hρ) (x : Vec d)
    (i : Fin d) : (h1OfDomain hc hρ hcpos hρpos hW hWb u hu).grad x i = gradOf hc hρ u i x := rfl

/-- **A form-domain element satisfying the variational equation against `F` solves the weak
massive equation on every bounded open set**, tested against `H¹₀(W)`. -/
theorem weak_equation_of_form_eq {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ} {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {u F : Lp ℝ 2 (wm ρ)} (hu : u ∈ gradDomain hc hρ)
    (hEq : ∀ v ∈ gradDomain hc hρ, μ * inner ℝ u v + gradForm hc hρ u v = inner ℝ F v)
    (φ : H10Function W) :
    μ * ∫ x in W, ρ x * (h1OfDomain hc hρ hcpos hρpos hW hWb u hu).toFun x *
        φ.toH1Function.toFun x ∂volume +
      ∫ x in W, vecDot (c x • (h1OfDomain hc hρ hcpos hρpos hW hWb u hu).grad x)
        (φ.toH1Function.grad x) ∂volume =
    ∫ x in W, ρ x * F x * φ.toH1Function.toFun x ∂volume := by
  have hz := zextL_mem_gradDomain hc hρ hcpos hρpos hW hWb φ
  have heq := hEq _ hz
  rw [inner_zextL_eq hρ hρpos hW hWb u φ, inner_zextL_eq hρ hρpos hW hWb F φ] at heq
  have e2 : gradForm hc hρ u (zextL hρ hW hWb φ) =
      ∫ x in W, vecDot (c x • (h1OfDomain hc hρ hcpos hρpos hW hWb u hu).grad x)
        (φ.toH1Function.grad x) ∂volume := by
    unfold gradForm
    simp_rw [gradOf_zextL hc hρ hcpos hρpos hW hWb φ, inner_zextG_eq hc hcpos hW hWb]
    rw [← integral_finset_sum _ (fun i _ => integrableOn_zextG hc hcpos hW hWb _ φ i)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [vecDot, h1OfDomain_grad, mul_assoc]
  rw [e2] at heq
  exact heq

/-- **The resolvent of the gradient form solves the weak massive equation on every bounded open
set**, tested against `H¹₀(W)`. -/
theorem weak_equation_of_resolvent {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {μ : ℝ}
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) μ G)
    {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {f : St d → ℝ}
    (hf : MemLp f 2 (wm ρ)) (φ : H10Function W) :
    μ * ∫ x in W, ρ x * (h1OfDomain hc hρ hcpos hρpos hW hWb (G (hf.toLp f))
        (hG.mem_domain _)).toFun x * φ.toH1Function.toFun x ∂volume +
      ∫ x in W, vecDot (c x • (h1OfDomain hc hρ hcpos hρpos hW hWb (G (hf.toLp f))
        (hG.mem_domain _)).grad x) (φ.toH1Function.grad x) ∂volume =
    ∫ x in W, ρ x * f x * φ.toH1Function.toFun x ∂volume := by
  rw [weak_equation_of_form_eq hc hρ hcpos hρpos hW hWb (hG.mem_domain _) (F := hf.toLp f)
    (fun v hv => hG.eq _ hv) φ]
  have hae : ∀ᵐ x ∂(volume : Measure (St d)), (hf.toLp f) x = f x :=
    ae_volume_of_ae_wm hρ hρpos hf.coeFn_toLp
  refine setIntegral_congr_ae hW.measurableSet ?_
  filter_upwards [hae] with x hx _
  rw [hx]

end SubdiffusiveProcess.E7
