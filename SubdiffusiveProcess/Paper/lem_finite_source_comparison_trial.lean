module

public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_finite_stopping_gluing
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison_cells
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Sobolev.MeanZeroRepresentative
public import Mathlib.Tactic
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.TietzeExtension

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper


/- The Neumann branch needs the concrete global mean subtraction, not merely
  preservation of the cell energy.  This helper records both facts for a
  later gluing invocation. -/
theorem aux_lem_finite_source_comparison_trial_centered_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hvol : volume.real (Q : Set (SpatialCoordinates d)) ≠ 0)
    (a : PositiveCoefficient Q) (w : weakSobolevGraph Q) :
    ∃ v : meanZeroSobolevGraph Q,
      sobolevCoefficientForm a v.val v.val =
        sobolevCoefficientForm a w.val w.val ∧
      (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        v.val.1 x = w.val.1 x -
          (∫ y in (Q : Set (SpatialCoordinates d)), w.val.1 y) /
            volume.real (Q : Set (SpatialCoordinates d))) := by
  let v := meanZeroSobolevRepresentative hQ hvol w
  refine ⟨v, ?_, meanZeroSobolevRepresentative_coeFn hQ hvol w⟩
  have hg := meanZeroSobolevRepresentative_gradient hQ hvol w
  have hc : v.val.2 = w.val.2 := by
    have hh : sobolevGradient v.val = sobolevGradient w.val := by
      simpa only [subspaceGradient, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using hg
    exact congrArg (fun g : HilbertGradient Q =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Q)) g) hh
  simp only [sobolevCoefficientForm_apply, hc]

/- The missing Neumann sup step, isolated from the cell construction: if a
  continuous glued representative is uniformly close to a mean-zero source
  representative, subtracting its volume mean costs at most one further copy
  of that error. -/
theorem aux_lem_finite_source_comparison_trial_mean_subtraction_sup
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K)
    (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (hvol : 0 < volume.real (Q : Set (SpatialCoordinates d)))
    {U V : SpatialCoordinates d → ℝ} {δ : ℝ}
    (hU : ContinuousOn U K) (hV : ContinuousOn V K)
    (hclose : ∀ x ∈ K, |V x - U x| ≤ δ)
    (hzero : (∫ x in (Q : Set (SpatialCoordinates d)), U x) = 0) :
    ∀ x ∈ K,
      |V x - (∫ y in (Q : Set (SpatialCoordinates d)), V y) /
          volume.real (Q : Set (SpatialCoordinates d)) - U x| ≤ 2 * δ := by
  have hfin_lt : volume (Q : Set (SpatialCoordinates d)) < ⊤ := by
    simpa only [Measure.restrict_apply_univ] using
      (measure_lt_top (volume.restrict (Q : Set (SpatialCoordinates d))) univ)
  have hUi : IntegrableOn U (Q : Set (SpatialCoordinates d)) :=
    (hU.integrableOn_compact hK).mono_set hQK
  have hVi : IntegrableOn V (Q : Set (SpatialCoordinates d)) :=
    (hV.integrableOn_compact hK).mono_set hQK
  have hdiff :
      (∫ y in (Q : Set (SpatialCoordinates d)), V y - U y) =
        (∫ y in (Q : Set (SpatialCoordinates d)), V y) := by
    rw [integral_sub hVi hUi, hzero, sub_zero]
  have hmean :
      |(∫ y in (Q : Set (SpatialCoordinates d)), V y) /
          volume.real (Q : Set (SpatialCoordinates d))| ≤ δ := by
    rw [← hdiff]
    rw [abs_div, abs_of_pos hvol]
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := (Q : Set (SpatialCoordinates d))) hfin_lt
      (f := fun y => V y - U y) (C := δ) (fun y hy => by
        simpa only [Real.norm_eq_abs] using hclose y (hQK hy))
    rw [Real.norm_eq_abs] at hnorm
    rw [div_le_iff₀ hvol]
    simpa [mul_comm] using hnorm
  intro x hx
  calc
    |V x - (∫ y in (Q : Set (SpatialCoordinates d)), V y) /
          volume.real (Q : Set (SpatialCoordinates d)) - U x| ≤
        |V x - U x| +
          |(∫ y in (Q : Set (SpatialCoordinates d)), V y) /
            volume.real (Q : Set (SpatialCoordinates d))| := by
              rw [show V x - (∫ y in (Q : Set (SpatialCoordinates d)), V y) /
                    volume.real (Q : Set (SpatialCoordinates d)) - U x =
                  (V x - U x) -
                    (∫ y in (Q : Set (SpatialCoordinates d)), V y) /
                      volume.real (Q : Set (SpatialCoordinates d)) by ring]
              simpa only [sub_zero, zero_sub, abs_neg] using
                (abs_sub_le (V x - U x) 0
                  ((∫ y in (Q : Set (SpatialCoordinates d)), V y) /
                    volume.real (Q : Set (SpatialCoordinates d))))
    _ ≤ 2 * δ := by linarith [hclose x hx, hmean]

end SubdiffusiveProcess.Paper

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ContDiff

section FSTCellMax
namespace SubdiffusiveProcess.Paper

/-- Weak maximum principle for a target-harmonic cell replacement: a pointwise
upper bound on the boundary datum on the open cell bounds the harmonic function
almost everywhere.  This is GMC's zero-mass barrier comparison. -/
theorem aux_lem_finite_source_comparison_trial_ae_le_of_harmonic
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {h g : H1Function W} (hharm : IsWeaklyHarmonicOn a W h)
    (htr : HasZeroTraceDifferenceOn W h g) {M : ℝ}
    (hg : ∀ x ∈ W, g.toFun x ≤ M) :
    ∀ᵐ x ∂(volume.restrict W), h.toFun x ≤ M := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
  obtain ⟨w, hwf, hwg⟩ := htr
  let v0 : H1Function W := H1Function.const M - g
  have hv0 : (fun x => max (M - g.toFun x) 0) =ᵐ[volume.restrict W] v0.toFun := by
    filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
    have hx' : max (M - g.toFun x) 0 = M - g.toFun x :=
      max_eq_left (sub_nonneg.2 (hg x hx))
    rw [hx']
    simp [v0, H1Function.const]
  let v : H1Function W := lane2_H1ofAEEq v0 _ hv0
  have hvnn : ∀ x, 0 ≤ v.toFun x := fun x => le_max_right _ _
  have hgrad : ∀ x, (w.toH1Function - v).grad x = h.grad x := by
    intro x
    have hvg : v.grad = v0.grad := rfl
    rw [H1Function.sub_grad, hvg, hwg x]
    simp only [v0, H1Function.sub_grad]
    change w.toH1Function.grad x - ((fun _ => (0 : SpatialCoordinates d)) x - g.grad x) =
      g.grad x + w.toH1Function.grad x
    simp only [zero_sub, sub_neg_eq_add]
    exact add_comm _ _
  have hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn a W
      (w.toH1Function - v) := by
    intro ψ _
    have heq : (fun x => vecDot (a x • (w.toH1Function - v).grad x)
        (ψ.toH1Function.grad x)) =
        fun x => vecDot (a x • h.grad x) (ψ.toH1Function.grad x) := by
      funext x
      rw [hgrad x]
    rw [heq]
    exact (hharm ψ).le
  have hle := SubdiffusiveProcess.CoarseGrainingVocab.Section11.ae_barrier_le_of_isWeakSubSolutionOn
    hW hlam hameas hbounds hvnn hsub
  filter_upwards [hle, ae_restrict_mem hW.isOpen.measurableSet] with x hx hxW
  rw [hwf x]
  have hvx : v.toFun x = M - g.toFun x := max_eq_left (sub_nonneg.2 (hg x hxW))
  rw [hvx] at hx
  linarith

/-- Negation preserves weak harmonicity. -/
theorem aux_lem_finite_source_comparison_trial_harmonic_neg
    {d : ℕ} {W : Set (SpatialCoordinates d)} {a : SpatialCoordinates d → ℝ}
    {h : H1Function W} (hharm : IsWeaklyHarmonicOn a W h) :
    IsWeaklyHarmonicOn a W (-h) := by
  intro ψ
  have hx : (fun x => vecDot (a x • (-h).grad x) (ψ.toH1Function.grad x)) =
      fun x => -vecDot (a x • h.grad x) (ψ.toH1Function.grad x) := by
    funext x
    rw [H1Function.neg_grad]
    simp only [smul_neg, vecDot_neg_left]
  rw [hx, integral_neg, hharm ψ, neg_zero]

/-- Negation preserves the zero-trace difference. -/
theorem aux_lem_finite_source_comparison_trial_trace_neg
    {d : ℕ} {W : Set (SpatialCoordinates d)} {h g : H1Function W}
    (htr : HasZeroTraceDifferenceOn W h g) :
    HasZeroTraceDifferenceOn W (-h) (-g) := by
  obtain ⟨w, hwf, hwg⟩ := htr
  refine ⟨-w, fun x => ?_, fun x => ?_⟩
  · change (-h).toFun x = (-g).toFun x + ((-1 : ℝ) • w.toH1Function).toFun x
    rw [H1Function.neg_toFun, H1Function.neg_toFun, H1Function.smul_toFun]
    simp only
    rw [hwf x]
    ring
  · change (-h).grad x = (-g).grad x + ((-1 : ℝ) • w.toH1Function).grad x
    rw [H1Function.neg_grad, H1Function.neg_grad, H1Function.smul_grad]
    simp only
    rw [hwg x]
    funext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The lower weak maximum principle. -/
theorem aux_lem_finite_source_comparison_trial_le_ae_of_harmonic
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {h g : H1Function W} (hharm : IsWeaklyHarmonicOn a W h)
    (htr : HasZeroTraceDifferenceOn W h g) {m : ℝ}
    (hg : ∀ x ∈ W, m ≤ g.toFun x) :
    ∀ᵐ x ∂(volume.restrict W), m ≤ h.toFun x := by
  have hle := aux_lem_finite_source_comparison_trial_ae_le_of_harmonic hW hlam hameas
    hbounds (aux_lem_finite_source_comparison_trial_harmonic_neg hharm)
    (aux_lem_finite_source_comparison_trial_trace_neg htr) (M := -m)
    (fun x hx => by
      rw [H1Function.neg_toFun]
      simp only
      linarith [hg x hx])
  filter_upwards [hle] with x hx
  rw [H1Function.neg_toFun] at hx
  simp only at hx
  linarith

end SubdiffusiveProcess.Paper

end FSTCellMax

open Set Topology SubdiffusiveProcess
open scoped ContDiff

section FSTSmoothApprox
namespace SubdiffusiveProcess.Paper

/-- Globally smooth continuous functions form a point-separating subalgebra. -/
def aux_lem_finite_source_comparison_trial_smoothSubalgebra (d : ℕ) :
    Subalgebra ℝ C(SpatialCoordinates d, ℝ) where
  carrier := {f | ContDiff ℝ ∞ (f : SpatialCoordinates d → ℝ)}
  mul_mem' := fun {f g} (ha : ContDiff ℝ ∞ (f : SpatialCoordinates d → ℝ))
    (hb : ContDiff ℝ ∞ (g : SpatialCoordinates d → ℝ)) => by
      show ContDiff ℝ ∞ (fun x => f x * g x)
      exact ha.mul hb
  add_mem' := fun {f g} (ha : ContDiff ℝ ∞ (f : SpatialCoordinates d → ℝ))
    (hb : ContDiff ℝ ∞ (g : SpatialCoordinates d → ℝ)) => by
      show ContDiff ℝ ∞ (fun x => f x + g x)
      exact ha.add hb
  algebraMap_mem' := fun r => by
    show ContDiff ℝ ∞ (fun _ : SpatialCoordinates d => r)
    exact contDiff_const

theorem aux_lem_finite_source_comparison_trial_smoothSubalgebra_separatesPoints
    (d : ℕ) : (aux_lem_finite_source_comparison_trial_smoothSubalgebra d).SeparatesPoints := by
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z => z j, ⟨⟨fun z => z j, continuous_apply j⟩, ?_, rfl⟩, hj⟩
  show ContDiff ℝ ∞ (fun z : SpatialCoordinates d => z j)
  exact contDiff_apply ℝ ℝ j

/-- **Uniform smooth approximation on a compact set.**  A function continuous on
a compact set is uniformly within any `ε` of a globally smooth function there
(Tietze extension followed by Stone--Weierstrass). -/
theorem aux_lem_finite_source_comparison_trial_exists_smooth_near
    {d : ℕ} {K : Set (SpatialCoordinates d)} (hK : IsCompact K)
    {G : SpatialCoordinates d → ℝ} (hG : ContinuousOn G K) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ ∧ ∀ x ∈ K, |φ x - G x| < ε := by
  let fK : C(K, ℝ) := ⟨K.domRestrict G, hG.domRestrict⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed fK
  have hFK : ∀ x ∈ K, F x = G x := by
    intro x hx
    have := congrArg (fun f : C(K, ℝ) => f ⟨x, hx⟩) hF
    simpa only [fK, ContinuousMap.coe_mk, domRestrict_apply] using! this
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (aux_lem_finite_source_comparison_trial_smoothSubalgebra_separatesPoints d) F hK hε
  refine ⟨g, hgA, fun x hx => ?_⟩
  have := hg x hx
  rw [Real.norm_eq_abs, hFK x hx] at this
  exact this

end SubdiffusiveProcess.Paper

end FSTSmoothApprox

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ContDiff

section FSTCellContinuous
namespace SubdiffusiveProcess.Paper

/-- An almost-everywhere upper bound on an open set propagates to its closure
for a function continuous on the closure. -/
theorem aux_lem_finite_source_comparison_trial_le_on_closure_of_ae
    {d : ℕ} {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    {f : SpatialCoordinates d → ℝ} {M : ℝ} (hf : ContinuousOn f (closure W))
    (hae : ∀ᵐ x ∂(volume.restrict W), f x ≤ M) :
    ∀ x ∈ closure W, f x ≤ M :=
  le_on_closure (lane2_le_of_ae_le_of_continuousOn hW (hf.mono subset_closure) hae)
    hf continuousOn_const

/-- A real number bounded by `C/(n+1)` for every `n` vanishes. -/
theorem aux_lem_finite_source_comparison_trial_eq_zero_of_abs_le
    {t C : ℝ} (h : ∀ n : ℕ, |t| ≤ C * (1 / ((n : ℝ) + 1))) : t = 0 := by
  by_contra ht
  have hpos : 0 < |t| := abs_pos.mpr ht
  have hC : 0 < C := by
    have h0 := h 0
    by_contra hC
    push Not at hC
    have : C * (1 / ((0 : ℕ) + 1 : ℝ)) ≤ 0 := by
      simp only [Nat.cast_zero, zero_add, div_one, mul_one]
      exact hC
    linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hpos hC)
  have := h n
  have h2 : C * (1 / ((n : ℝ) + 1)) < |t| := by
    rw [lt_div_iff₀ hC] at hn
    linarith [mul_comm C (1 / ((n : ℝ) + 1))]
  linarith

/-- Differences of weakly harmonic functions are weakly harmonic. -/
theorem aux_lem_finite_source_comparison_trial_harmonic_sub
    {d : ℕ} {W : Opens (SpatialCoordinates d)} {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))), ‖a x‖ ≤ C)
    {u v : H1Function (W : Set (SpatialCoordinates d))}
    (hu : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (hv : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) v) :
    IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) (u - v) := by
  intro ψ
  have hiu := lane2_integrableOn_coeff_vecDot hameas habd u.gradMemL2
    ψ.toH1Function.gradMemL2
  have hiv := lane2_integrableOn_coeff_vecDot hameas habd v.gradMemL2
    ψ.toH1Function.gradMemL2
  have hsm : ∀ (w : H1Function (W : Set (SpatialCoordinates d))),
      (fun x => vecDot (a x • w.grad x) (ψ.toH1Function.grad x)) =
        fun x => a x * vecDot (w.grad x) (ψ.toH1Function.grad x) := by
    intro w
    funext x
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have heq : (fun x => vecDot (a x • (u - v).grad x) (ψ.toH1Function.grad x)) =
      fun x => a x * vecDot (u.grad x) (ψ.toH1Function.grad x) -
        a x * vecDot (v.grad x) (ψ.toH1Function.grad x) := by
    funext x
    rw [H1Function.sub_grad]
    simp only [vecDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 := hu ψ
  have h2 := hv ψ
  rw [hsm] at h1 h2
  rw [heq, integral_sub hiu hiv, h1, h2, sub_zero]

/-- Differences of zero-trace differences are zero-trace differences. -/
theorem aux_lem_finite_source_comparison_trial_trace_sub
    {d : ℕ} {W : Set (SpatialCoordinates d)} {u φ v ψ : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u φ) (hv : HasZeroTraceDifferenceOn W v ψ) :
    HasZeroTraceDifferenceOn W (u - v) (φ - ψ) := by
  obtain ⟨w₁, hw₁f, hw₁g⟩ := hu
  obtain ⟨w₂, hw₂f, hw₂g⟩ := hv
  refine ⟨w₁ - w₂, fun x => ?_, fun x => ?_⟩
  · change (u - v).toFun x = (φ - ψ).toFun x +
      (w₁.toH1Function + (-1 : ℝ) • w₂.toH1Function).toFun x
    rw [H1Function.sub_toFun, H1Function.sub_toFun, H1Function.add_toFun,
      H1Function.smul_toFun]
    simp only
    rw [hw₁f x, hw₂f x]
    ring
  · change (u - v).grad x = (φ - ψ).grad x +
      (w₁.toH1Function + (-1 : ℝ) • w₂.toH1Function).grad x
    rw [H1Function.sub_grad, H1Function.sub_grad, H1Function.add_grad,
      H1Function.smul_grad]
    simp only
    rw [hw₁g x, hw₂g x]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring



def aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity {d : ℕ}
    (a : SpatialCoordinates d → ℝ) (W : Set (SpatialCoordinates d)) : Prop :=
  ∀ φ u : H1Function W, ContDiff ℝ ∞ φ.toFun → IsWeaklyHarmonicOn a W u →
    HasZeroTraceDifferenceOn W u φ →
    ∃ v : SpatialCoordinates d → ℝ, ContinuousOn v (closure W) ∧
      v =ᵐ[volume.restrict W] u.toFun ∧ ∀ x ∈ frontier W, v x = φ.toFun x



theorem aux_lem_finite_source_comparison_trial_regular_of_continuous
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    {a : SpatialCoordinates d → ℝ} (ha : Continuous a) {lam Lam : ℝ} (hlam : 0 < lam)
    (habounds : ∀ x ∈ (centeredCube c s hs : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam) :
    aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity a
      (centeredCube c s hs : Set (SpatialCoordinates d)) :=
  fun φ u hφ hharm htr =>
    (lane2_cellDirichletBoundaryContinuity hd).continuous_up_to_boundary c s hs a
      lam Lam hlam ha habounds φ u hφ hharm htr

/-- **Continuity up to the cell boundary with a continuous datum.**  On an open
cube, let `a` be a measurable uniformly elliptic coefficient with smooth-datum
boundary regularity.  A weakly `a`-harmonic function whose trace is that of an
`H¹` datum continuous on the closed cube has a representative continuous on the
closed cube and equal to the datum on the frontier.  The datum is approximated
uniformly by smooth functions; each smooth-datum replacement is continuous up to
the boundary by `hreg`, and the weak maximum principle turns the uniform datum
error into a uniform error of the replacements. -/
theorem aux_lem_finite_source_comparison_trial_cell_continuous
    {d : ℕ} [NeZero d]
    (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (W0 : Opens (SpatialCoordinates d)) (hWc : W0 = centeredCube c s hs)
    {a : SpatialCoordinates d → ℝ} (ha : Measurable a) {lam Lam : ℝ} (hlam : 0 < lam)
    (habounds : ∀ x ∈ (W0 : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam)
    (hreg : aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity a
      (W0 : Set (SpatialCoordinates d)))
    {h g : H1Function (W0 : Set (SpatialCoordinates d))}
    (hharm : IsWeaklyHarmonicOn a (W0 : Set (SpatialCoordinates d)) h)
    (htr : HasZeroTraceDifferenceOn (W0 : Set (SpatialCoordinates d)) h g)
    {G : SpatialCoordinates d → ℝ}
    (hG : ContinuousOn G (closure (W0 : Set (SpatialCoordinates d))))
    (hgG : ∀ x ∈ (W0 : Set (SpatialCoordinates d)), g.toFun x = G x) :
    ∃ H : SpatialCoordinates d → ℝ,
      ContinuousOn H (closure (W0 : Set (SpatialCoordinates d))) ∧
      H =ᵐ[volume.restrict (W0 : Set (SpatialCoordinates d))] h.toFun ∧
      ∀ x ∈ frontier (W0 : Set (SpatialCoordinates d)), H x = G x := by
  classical
  have hWdef : (W0 : Set (SpatialCoordinates d)) = Metric.ball c (s / 2) := by
    rw [hWc]; rfl
  have hWconv : IsOpenBoundedConvexDomain (W0 : Set (SpatialCoordinates d)) := by
    rw [hWc]; exact lane2_isOpenBoundedConvexDomain_centeredCube c hs
  have hWopen : IsOpen (W0 : Set (SpatialCoordinates d)) := hWconv.isOpen
  have hWne : (W0 : Set (SpatialCoordinates d)).Nonempty := by
    rw [hWdef]; exact ⟨c, Metric.mem_ball_self (half_pos hs)⟩
  have hK : IsCompact (closure (W0 : Set (SpatialCoordinates d))) := by
    have : closure (W0 : Set (SpatialCoordinates d)) = Metric.closedBall c (s / 2) := by
      rw [hWdef]
      exact closure_ball c (ne_of_gt (half_pos hs))
    rw [this]
    exact isCompact_closedBall c (s / 2)
  have hameas : AEStronglyMeasurable a (volume.restrict (W0 : Set (SpatialCoordinates d))) :=
    ha.aestronglyMeasurable
  have hbounds : ∀ᵐ y ∂(volume.restrict (W0 : Set (SpatialCoordinates d))), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  have habd : ∀ᵐ y ∂(volume.restrict (W0 : Set (SpatialCoordinates d))), ‖a y‖ ≤ |Lam| := by
    filter_upwards [hbounds] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hlam hy.1)]
    exact hy.2.trans (le_abs_self Lam)
  have hEll := lane2_isEllipticFieldOn_scalar hWopen.measurableSet ha hlam habounds
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  -- smooth approximants of the datum
  have hφex : ∀ n : ℕ, ∃ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ ∧
      ∀ x ∈ closure (W0 : Set (SpatialCoordinates d)), |φ x - G x| < ε n :=
    fun n => aux_lem_finite_source_comparison_trial_exists_smooth_near hK hG (hεpos n)
  choose φ hφsmooth hφnear using hφex
  obtain ⟨φH, hφH⟩ : ∃ φH : ℕ → H1Function (W0 : Set (SpatialCoordinates d)), ∀ n, (φH n).toFun = φ n :=
    ⟨fun n => H1Function.ofContDiffOnIsOpenBoundedConvexDomain hWconv
      ((hφsmooth n).of_le (by exact_mod_cast le_top)), fun n => rfl⟩
  -- smooth-datum replacements
  have hrep : ∀ n : ℕ, ∃ hn : H1Function (W0 : Set (SpatialCoordinates d)), HasZeroTraceDifferenceOn (W0 : Set (SpatialCoordinates d)) hn (φH n) ∧
      IsWeaklyHarmonicOn a (W0 : Set (SpatialCoordinates d)) hn :=
    fun n => lane2_exists_weaklyHarmonic_of_zeroTrace hWconv hWne hEll (φH n)
  choose hn hntr hnharm using hrep
  have hcont : ∀ n : ℕ, ∃ Hn : SpatialCoordinates d → ℝ, ContinuousOn Hn (closure (W0 : Set (SpatialCoordinates d))) ∧
      Hn =ᵐ[volume.restrict (W0 : Set (SpatialCoordinates d))] (hn n).toFun ∧ ∀ x ∈ frontier (W0 : Set (SpatialCoordinates d)), Hn x = (φH n).toFun x :=
    fun n => hreg (φH n) (hn n) (by rw [hφH]; exact hφsmooth n) (hnharm n) (hntr n)
  choose Hn hHncont hHnae hHnfront using hcont
  -- maximum principle: uniform closeness to the given solution
  have hclose : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (W0 : Set (SpatialCoordinates d))), |Hn n x - h.toFun x| ≤ ε n := by
    intro n
    have hD := aux_lem_finite_source_comparison_trial_harmonic_sub
      (W := W0) hameas habd hharm (hnharm n)
    have hDt := aux_lem_finite_source_comparison_trial_trace_sub htr (hntr n)
    have hdat : ∀ x ∈ (W0 : Set (SpatialCoordinates d)), |(g - φH n).toFun x| ≤ ε n := by
      intro x hx
      rw [H1Function.sub_toFun]
      simp only
      rw [hφH n]
      rw [hgG x hx, abs_sub_comm]
      exact (hφnear n x (subset_closure hx)).le
    have hup := aux_lem_finite_source_comparison_trial_ae_le_of_harmonic hWconv hlam hameas
      hbounds hD hDt (M := ε n) (fun x hx => (abs_le.mp (hdat x hx)).2)
    have hlo := aux_lem_finite_source_comparison_trial_le_ae_of_harmonic hWconv hlam hameas
      hbounds hD hDt (m := -ε n) (fun x hx => (abs_le.mp (hdat x hx)).1)
    filter_upwards [hup, hlo, hHnae n] with x h1 h2 h3
    rw [H1Function.sub_toFun] at h1 h2
    simp only at h1 h2
    rw [h3, abs_sub_comm]
    exact abs_le.mpr ⟨h2, h1⟩
  -- uniform Cauchy property on the closed cube
  have hcauchy : ∀ n m : ℕ, ∀ x ∈ closure (W0 : Set (SpatialCoordinates d)), |Hn n x - Hn m x| ≤ ε n + ε m := by
    intro n m
    refine aux_lem_finite_source_comparison_trial_le_on_closure_of_ae hWopen
      (((hHncont n).sub (hHncont m)).abs) ?_
    filter_upwards [hclose n, hclose m] with x h1 h2
    calc |Hn n x - Hn m x| = |(Hn n x - h.toFun x) - (Hn m x - h.toFun x)| := by ring_nf
      _ ≤ |Hn n x - h.toFun x| + |Hn m x - h.toFun x| := abs_sub _ _
      _ ≤ ε n + ε m := add_le_add h1 h2
  have hεmono : ∀ n m : ℕ, n ≤ m → ε m ≤ ε n := by
    intro n m hnm
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- pointwise limit
  have hconv : ∀ x ∈ closure (W0 : Set (SpatialCoordinates d)), ∃ l, Tendsto (fun n => Hn n x) atTop (𝓝 l) := by
    intro x hx
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    calc |Hn n x - Hn N x| ≤ ε n + ε N := hcauchy n N x hx
      _ ≤ ε N + ε N := add_le_add (hεmono N n hn) le_rfl
      _ < δ := by
        have : ε N < δ / 2 := hN
        linarith
  let H : SpatialCoordinates d → ℝ := fun x => limUnder atTop (fun n => Hn n x)
  have hHlim : ∀ x ∈ closure (W0 : Set (SpatialCoordinates d)), Tendsto (fun n => Hn n x) atTop (𝓝 (H x)) :=
    fun x hx => tendsto_nhds_limUnder (hconv x hx)
  have hHbound : ∀ n : ℕ, ∀ x ∈ closure (W0 : Set (SpatialCoordinates d)), |H x - Hn n x| ≤ 2 * ε n := by
    intro n x hx
    have hlim : Tendsto (fun m => |Hn m x - Hn n x|) atTop (𝓝 |H x - Hn n x|) :=
      ((hHlim x hx).sub_const (Hn n x)).abs
    refine le_of_tendsto hlim ?_
    rw [eventually_atTop]
    refine ⟨n, fun m hm => ?_⟩
    calc |Hn m x - Hn n x| ≤ ε m + ε n := hcauchy m n x hx
      _ ≤ ε n + ε n := add_le_add (hεmono n m hm) le_rfl
      _ = 2 * ε n := by ring
  have hunif : TendstoUniformlyOn Hn H atTop (closure (W0 : Set (SpatialCoordinates d))) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have h2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
      have := hεlim.const_mul 2
      rwa [mul_zero] at this
    filter_upwards [(h2.eventually (gt_mem_nhds hδ))] with n hn x hx
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hHbound n x hx) hn
  have hHcont : ContinuousOn H (closure (W0 : Set (SpatialCoordinates d))) :=
    hunif.continuousOn (Frequently.of_forall fun n => hHncont n)
  refine ⟨H, hHcont, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂(volume.restrict (W0 : Set (SpatialCoordinates d))), ∀ n : ℕ, |Hn n x - h.toFun x| ≤ ε n :=
      ae_all_iff.mpr hclose
    filter_upwards [hall, ae_restrict_mem hWopen.measurableSet] with x hx hxW
    have hz : H x - h.toFun x = 0 := by
      apply aux_lem_finite_source_comparison_trial_eq_zero_of_abs_le (C := 3)
      intro n
      calc |H x - h.toFun x| = |(H x - Hn n x) + (Hn n x - h.toFun x)| := by ring_nf
        _ ≤ |H x - Hn n x| + |Hn n x - h.toFun x| := abs_add_le _ _
        _ ≤ 2 * ε n + ε n := add_le_add (hHbound n x (subset_closure hxW)) (hx n)
        _ = 3 * (1 / ((n : ℝ) + 1)) := by ring
    linarith
  · intro x hx
    have hxc : x ∈ closure (W0 : Set (SpatialCoordinates d)) := frontier_subset_closure hx
    have hz : H x - G x = 0 := by
      apply aux_lem_finite_source_comparison_trial_eq_zero_of_abs_le (C := 3)
      intro n
      have hf := hHnfront n x hx
      rw [hφH] at hf
      calc |H x - G x| = |(H x - Hn n x) + (φ n x - G x)| := by rw [hf]; ring_nf
        _ ≤ |H x - Hn n x| + |φ n x - G x| := abs_add_le _ _
        _ ≤ 2 * ε n + ε n := add_le_add (hHbound n x hxc) (hφnear n x hxc).le
        _ = 3 * (1 / ((n : ℝ) + 1)) := by ring
    linarith

end SubdiffusiveProcess.Paper

end FSTCellContinuous

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ContDiff

section FSTBridge
namespace SubdiffusiveProcess.Paper



theorem aux_lem_finite_source_comparison_trial_minimizer_bridge
    {d : ℕ} {Wc Q : Opens (SpatialCoordinates d)} (hle : Wc ≤ Q)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph Wc,
      ‖(v : SobolevData Wc).1‖ ≤
        K * ‖@subspaceGradient d Wc (killedSobolevGraph Wc) v‖)
    (aT : PositiveCoefficient Q) {A : SpatialCoordinates d → ℝ}
    (hA : (aT.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    (u : weakSobolevGraph Q) {U : SpatialCoordinates d → ℝ}
    (hU : ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) :
    ∃ g h : H1Function (Wc : Set (SpatialCoordinates d)),
      (∀ x, g.toFun x = U x) ∧
      IsWeaklyHarmonicOn A (Wc : Set (SpatialCoordinates d)) h ∧
      HasZeroTraceDifferenceOn (Wc : Set (SpatialCoordinates d)) h g ∧
      h.toFun =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))]
        (((@dirichletMinimizer d Wc (@killedResponseSpace d Wc hP)
          (positiveCoefficientRestrict hle aT)
          ⟨sobolevDataRestrict hle u.val,
            sobolevDataRestrict_mem_weak hle u.property⟩).val.1 :
              DomainL2 Wc) : SpatialCoordinates d → ℝ) := by
  classical
  let S := @killedResponseSpace d Wc hP
  let aTr := positiveCoefficientRestrict hle aT
  let b : weakSobolevGraph Wc :=
    ⟨sobolevDataRestrict hle u.val, sobolevDataRestrict_mem_weak hle u.property⟩
  let q := dirichletMinimizer S aTr b
  change ∃ g h : H1Function (Wc : Set (SpatialCoordinates d)),
      (∀ x, g.toFun x = U x) ∧
      IsWeaklyHarmonicOn A (Wc : Set (SpatialCoordinates d)) h ∧
      HasZeroTraceDifferenceOn (Wc : Set (SpatialCoordinates d)) h g ∧
      h.toFun =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))]
        ((q.val.1 : DomainL2 Wc) : SpatialCoordinates d → ℝ)
  have hWcQ : (Wc : Set (SpatialCoordinates d)) ⊆ Q := hle
  -- coefficient facts on the cell
  have hAcell : ((aTr.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))] A :=
    (positiveCoefficientRestrict_coeFn hle aT).trans
      (ae_restrict_of_ae_restrict_of_subset hWcQ hA)
  have hAmeas : AEStronglyMeasurable A (volume.restrict (Wc : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable aTr.val).congr hAcell
  obtain ⟨C, hC⟩ := lane2_coeff_ae_bound aTr
  have hAbd : ∀ᵐ x ∂(volume.restrict (Wc : Set (SpatialCoordinates d))), ‖A x‖ ≤ C := by
    filter_upwards [hC, hAcell] with x h1 h2
    rwa [h2] at h1
  -- the datum
  obtain ⟨g0, hg0val, hg0grad⟩ := exists_nativeH1Function_of_weakSobolevGraph b
  have hbU : ((b.val.1 : DomainL2 Wc) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))] U :=
    (domainLpRestrict_coeFn hle u.val.1).trans
      (ae_restrict_of_ae_restrict_of_subset hWcQ hU)
  have hg0U : U =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))] g0.toFun := by
    rw [hg0val]
    exact hbU.symm
  let g : H1Function (Wc : Set (SpatialCoordinates d)) := lane2_H1ofAEEq g0 U hg0U
  -- the killed correction
  have hdiffmem : q.val - b.val ∈ killedSobolevGraph Wc := by
    change q.val - b.val ∈ S.space
    exact dirichletMinimizer_mem_affine S aTr b
  obtain ⟨V, hVval, hVgrad⟩ :=
    exists_nativeH10Function_of_killedSobolevGraph
      (⟨q.val - b.val, hdiffmem⟩ : killedSobolevGraph Wc)
  let h : H1Function (Wc : Set (SpatialCoordinates d)) := g + V.toH1Function
  have hgrad_ae : ∀ i : Fin d, (fun x => h.grad x i)
      =ᵐ[volume.restrict (Wc : Set (SpatialCoordinates d))]
        fun x => ((q.val.2 i : DomainL2 Wc) : SpatialCoordinates d → ℝ) x := by
    intro i
    filter_upwards [Lp.coeFn_sub (q.val.2 i) (b.val.2 i)] with x hx
    change g0.grad x i + V.toH1Function.grad x i = _
    rw [hg0grad, hVgrad]
    change (b.val.2 i : DomainL2 Wc) x +
      (((q.val.2 i - b.val.2 i : DomainL2 Wc)) : SpatialCoordinates d → ℝ) x = _
    rw [hx]
    simp only [Pi.sub_apply]
    ring
  refine ⟨g, h, fun x => rfl, ?_, ⟨V, fun x => rfl, fun x => rfl⟩, ?_⟩
  · intro ψ
    let ψS : SobolevData Wc := sobolevDataOfH1 ψ.toH1Function
    have hψS : ψS ∈ killedSobolevGraph Wc := sobolevDataOfH1_mem_killed ψ
    have hEL := dirichletMinimizer_euler S aTr b (⟨ψS, hψS⟩ : S.space)
    change sobolevCoefficientForm aTr q.val ψS = 0 at hEL
    rw [sobolevCoefficientForm_apply] at hEL
    have hint : ∀ i : Fin d, IntegrableOn
        (fun x => A x * (h.grad x i * ψ.toH1Function.grad x i))
        (Wc : Set (SpatialCoordinates d)) volume := fun i =>
      lane2_integrableOn_coeff_mul hAmeas hAbd (h.gradMemL2 i)
        (ψ.toH1Function.gradMemL2 i)
    have hpt : (fun x => vecDot (A x • h.grad x) (ψ.toH1Function.grad x)) =
        fun x => ∑ i : Fin d, A x * (h.grad x i * ψ.toH1Function.grad x i) := by
      funext x
      simp only [vecDot, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hpt, integral_finsetSum _ (fun i _ => hint i)]
    rw [← hEL]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine integral_congr_ae ?_
    filter_upwards [hAcell, hgrad_ae i, sobolevDataOfH1_snd_coeFn ψ.toH1Function i]
      with x h1 h2 h3
    rw [h1, h2, h3]
  · filter_upwards [Lp.coeFn_sub q.val.1 b.val.1, hbU] with x hx hb
    change U x + V.toH1Function.toFun x = _
    rw [hVval]
    change U x + (((q.val.1 - b.val.1 : DomainL2 Wc)) : SpatialCoordinates d → ℝ) x = _
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hb]
    ring

end SubdiffusiveProcess.Paper

end FSTBridge

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ContDiff

section FSTCell
namespace SubdiffusiveProcess.Paper

/-- **One target replacement cell.**  On a cube cell of the source partition,
the target-coefficient Dirichlet minimizer with the restricted trace of the
source solution has a representative continuous on the closed cell, equal to
the source representative `U` on the cell frontier, and within the source
oscillation `η` of `U` on the whole closed cell (weak maximum principle). -/
theorem aux_lem_finite_source_comparison_trial_cell_replacement
    {d : ℕ} [NeZero d] {Q : Opens (SpatialCoordinates d)}
    (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (hle : centeredCube c s hs ≤ Q)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube c s hs),
      ‖(v : SobolevData (centeredCube c s hs)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube c s hs)
          (killedSobolevGraph (centeredCube c s hs)) v‖)
    (aT : PositiveCoefficient Q) {A : SpatialCoordinates d → ℝ} (hAm : Measurable A)
    (hA : (aT.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hAb : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ A x ∧ A x ≤ Lam)
    (hreg : aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity A
      (centeredCube c s hs : Set (SpatialCoordinates d)))
    (u : weakSobolevGraph Q) {U : SpatialCoordinates d → ℝ}
    (hU : ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (hUc : ContinuousOn U (closure (centeredCube c s hs : Set (SpatialCoordinates d))))
    {η : ℝ}
    (hosc : ∀ x ∈ closure (centeredCube c s hs : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube c s hs : Set (SpatialCoordinates d)), |U x - U y| ≤ η) :
    ∃ H : SpatialCoordinates d → ℝ,
      ContinuousOn H (closure (centeredCube c s hs : Set (SpatialCoordinates d))) ∧
      H =ᵐ[volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d))]
        (((@dirichletMinimizer d (centeredCube c s hs)
          (@killedResponseSpace d (centeredCube c s hs) hP)
          (positiveCoefficientRestrict hle aT)
          ⟨sobolevDataRestrict hle u.val,
            sobolevDataRestrict_mem_weak hle u.property⟩).val.1 :
              DomainL2 (centeredCube c s hs)) : SpatialCoordinates d → ℝ) ∧
      (∀ x ∈ frontier (centeredCube c s hs : Set (SpatialCoordinates d)), H x = U x) ∧
      (∀ x ∈ closure (centeredCube c s hs : Set (SpatialCoordinates d)),
        |H x - U x| ≤ η) := by
  obtain ⟨g, h, hgU, hharm, htr, hh⟩ :=
    aux_lem_finite_source_comparison_trial_minimizer_bridge hle hP aT hA u hU
  have hsub : (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆ Q := hle
  have habounds : ∀ x ∈ (centeredCube c s hs : Set (SpatialCoordinates d)),
      lam ≤ A x ∧ A x ≤ Lam := fun x hx => hAb x (hsub hx)
  obtain ⟨H, hHc, hHae, hHfront⟩ :=
    aux_lem_finite_source_comparison_trial_cell_continuous c s hs
      (centeredCube c s hs) rfl hAm hlam habounds hreg hharm htr hUc (fun x _ => hgU x)
  refine ⟨H, hHc, hHae.trans hh, hHfront, ?_⟩
  have hWconv : IsOpenBoundedConvexDomain (centeredCube c s hs : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube c hs
  have hWopen : IsOpen (centeredCube c s hs : Set (SpatialCoordinates d)) :=
    (centeredCube c s hs).isOpen
  have hameas : AEStronglyMeasurable A
      (volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d))) :=
    hAm.aestronglyMeasurable
  have hbounds : ∀ᵐ y ∂(volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d))),
      lam ≤ A y ∧ A y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  intro x0 hx0
  have hup := aux_lem_finite_source_comparison_trial_ae_le_of_harmonic hWconv hlam hameas
    hbounds hharm htr (M := U x0 + η) (fun y hy => by
      rw [hgU y]
      have := hosc y (subset_closure hy) x0 hx0
      linarith [le_abs_self (U y - U x0)])
  have hlo := aux_lem_finite_source_comparison_trial_le_ae_of_harmonic hWconv hlam hameas
    hbounds hharm htr (m := U x0 - η) (fun y hy => by
      rw [hgU y]
      have := hosc y (subset_closure hy) x0 hx0
      linarith [neg_abs_le (U y - U x0)])
  have hae : ∀ᵐ y ∂(volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d))),
      |H y - U x0| ≤ η := by
    filter_upwards [hup, hlo, hHae] with y h1 h2 h3
    rw [h3]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact aux_lem_finite_source_comparison_trial_le_on_closure_of_ae hWopen
    ((hHc.sub continuousOn_const).abs) hae x0 hx0

/-- A finite family of open cells covering an open set up to a null set has
closures covering the closure of that set. -/
theorem aux_lem_finite_source_comparison_trial_closure_subset_iUnion
    {d n : ℕ} {Q : Set (SpatialCoordinates d)} (hQ : IsOpen Q)
    (cell : Fin n → Set (SpatialCoordinates d))
    (hcover : (⋃ i, cell i) =ᵐ[volume] Q) :
    closure Q ⊆ ⋃ i, closure (cell i) := by
  have hclosed : IsClosed (⋃ i, closure (cell i)) :=
    isClosed_iUnion_of_finite fun i => isClosed_closure
  refine closure_minimal ?_ hclosed
  have hnull : volume (Q \ ⋃ i, cell i) = 0 := (ae_eq_set.mp hcover).2
  have hopen : IsOpen (Q \ ⋃ i, closure (cell i)) := hQ.sdiff hclosed
  have hnull' : volume (Q \ ⋃ i, closure (cell i)) = 0 := by
    refine measure_mono_null ?_ hnull
    intro x ⟨hxQ, hx⟩
    refine ⟨hxQ, fun hmem => hx ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    exact mem_iUnion.mpr ⟨i, subset_closure hi⟩
  have hempty := (hopen.measure_eq_zero_iff volume).mp hnull'
  intro x hx
  by_contra hnot
  have : x ∈ Q \ ⋃ i, closure (cell i) := ⟨hx, hnot⟩
  rw [hempty] at this
  exact this



theorem aux_lem_finite_source_comparison_trial_glue
    {d : ℕ} [NeZero d]
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
    (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i)
    (hle : ∀ i, centeredCube (centers i) (sides i) (hside i) ≤ centeredCube zQ rQ hrQ)
    (hdisj : Pairwise (fun i j =>
      Disjoint (centeredCube (centers i) (sides i) (hside i) : Set (SpatialCoordinates d))
        (centeredCube (centers j) (sides j) (hside j) : Set (SpatialCoordinates d))))
    (hcover : (⋃ i, (centeredCube (centers i) (sides i) (hside i) :
        Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)))
    (hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube (centers i) (sides i) (hside i)),
      ‖(v : SobolevData (centeredCube (centers i) (sides i) (hside i))).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube (centers i) (sides i) (hside i))
          (killedSobolevGraph (centeredCube (centers i) (sides i) (hside i))) v‖)
    (aT : PositiveCoefficient (centeredCube zQ rQ hrQ))
    {A : SpatialCoordinates d → ℝ} (hAm : Measurable A)
    (hA : (aT.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] A)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hAb : ∀ x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)),
      lam ≤ A x ∧ A x ≤ Lam)
    (hreg : ∀ i, aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity A
      (centeredCube (centers i) (sides i) (hside i) : Set (SpatialCoordinates d)))
    (b u : weakSobolevGraph (centeredCube zQ rQ hrQ))
    (hu : u.val - b.val ∈ killedSobolevGraph (centeredCube zQ rQ hrQ))
    {U : SpatialCoordinates d → ℝ}
    (hUc : ContinuousOn U (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))))
    (hU : ((u : SobolevData (centeredCube zQ rQ hrQ)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] U)
    {η : ℝ}
    (hosc : ∀ i, ∀ x ∈ closure (centeredCube (centers i) (sides i) (hside i) :
        Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (centers i) (sides i) (hside i) :
        Set (SpatialCoordinates d)), |U x - U y| ≤ η) :
    ∃ (v : weakSobolevGraph (centeredCube zQ rQ hrQ)) (V : SpatialCoordinates d → ℝ),
      v.val - b.val ∈ killedSobolevGraph (centeredCube zQ rQ hrQ) ∧
      ContinuousOn V (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) ∧
      ((v : SobolevData (centeredCube zQ rQ hrQ)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)),
        |V x - U x| ≤ η) ∧
      sobolevCoefficientForm aT v.val v.val =
        ∑ i : Fin ncell,
          @dirichletResponse d (centeredCube (centers i) (sides i) (hside i))
            (@killedResponseSpace d (centeredCube (centers i) (sides i) (hside i)) (hPcell i))
            (positiveCoefficientRestrict (hle i) aT)
            ⟨sobolevDataRestrict (hle i) u.val,
              sobolevDataRestrict_mem_weak (hle i) u.property⟩ := by
  classical
  let cell : Fin ncell → Opens (SpatialCoordinates d) := fun i =>
    centeredCube (centers i) (sides i) (hside i)
  have hQsub : ∀ i, closure (cell i : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
    fun i => closure_mono (hle i)
  -- the cellwise continuous replacements
  have hrep : ∀ i : Fin ncell, ∃ H : SpatialCoordinates d → ℝ,
      ContinuousOn H (closure (cell i : Set (SpatialCoordinates d))) ∧
      H =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
        (((@dirichletMinimizer d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
          (positiveCoefficientRestrict (hle i) aT)
          ⟨sobolevDataRestrict (hle i) u.val,
            sobolevDataRestrict_mem_weak (hle i) u.property⟩).val.1 :
              DomainL2 (cell i)) : SpatialCoordinates d → ℝ) ∧
      (∀ x ∈ frontier (cell i : Set (SpatialCoordinates d)), H x = U x) ∧
      (∀ x ∈ closure (cell i : Set (SpatialCoordinates d)), |H x - U x| ≤ η) := fun i =>
    aux_lem_finite_source_comparison_trial_cell_replacement (centers i) (sides i)
      (hside i) (hle i) (hPcell i) aT hAm hA hlam hAb (hreg i) u hU (hUc.mono (hQsub i))
      (hosc i)
  choose H hHc hHae hHfront hHosc using hrep
  obtain ⟨F, hFc, hFcell, -⟩ := lane2_exists_continuous_glue cell hdisj U H hHc hHfront
  have hcov : closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ⊆
      ⋃ i, closure (cell i : Set (SpatialCoordinates d)) :=
    aux_lem_finite_source_comparison_trial_closure_subset_iUnion
      (centeredCube zQ rQ hrQ).isOpen (fun i => (cell i : Set (SpatialCoordinates d))) hcover
  have hFH : ∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)), F x = H i x := by
    intro i
    refine Set.EqOn.of_subset_closure (fun x hx => hFcell i x hx)
      (hFc.mono (subset_iUnion (fun k => closure (cell k : Set (SpatialCoordinates d))) i))
      (hHc i) subset_closure le_rfl
  
  have hQconv : IsOpenBoundedConvexDomain
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube zQ hrQ
  have : IsFiniteMeasure (volume.restrict
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) :=
    hQconv.isFiniteMeasure_restrict_volume
  have hP := (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube zQ rQ hrQ) hQconv).1
  obtain ⟨v, hvb, hvcell, henergy, -⟩ :=
    lem_finite_stopping_gluing d zQ rQ hrQ hP ncell centers sides hside hle hdisj hcover
      hPcell aT b u hu
  have aux_i : ∀ i, ∀ᵐ x ∂(volume.restrict (cell i : Set (SpatialCoordinates d))),
      ((v : SobolevData (centeredCube zQ rQ hrQ)).1 : SpatialCoordinates d → ℝ) x = F x := by
    intro i
    have h1 : ((v : SobolevData (centeredCube zQ rQ hrQ)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
          (((@dirichletMinimizer d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aT)
            ⟨sobolevDataRestrict (hle i) u.val,
              sobolevDataRestrict_mem_weak (hle i) u.property⟩).val.1 :
                DomainL2 (cell i)) : SpatialCoordinates d → ℝ) := by
      have hfst := congrArg Prod.fst (hvcell i)
      have hc : ((domainLpRestrict (hle i) v.val.1 : DomainL2 (cell i)) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
          (((@dirichletMinimizer d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aT)
            ⟨sobolevDataRestrict (hle i) u.val,
              sobolevDataRestrict_mem_weak (hle i) u.property⟩).val.1 :
                DomainL2 (cell i)) : SpatialCoordinates d → ℝ) := by
        exact Filter.EventuallyEq.of_eq (congrArg (fun f : DomainL2 (cell i) =>
          (f : SpatialCoordinates d → ℝ)) hfst)
      exact (domainLpRestrict_coeFn (hle i) v.val.1).symm.trans hc
    filter_upwards [h1, (hHae i).symm, ae_restrict_mem (cell i).isOpen.measurableSet]
      with x hx1 hx2 hx3
    rw [hx1, hx2, hFcell i x hx3]
  refine ⟨v, F, hvb, hFc.mono hcov, ?_, ?_, henergy⟩
  · have key : ∀ᵐ x ∂(volume.restrict (⋃ i, (cell i : Set (SpatialCoordinates d)))),
        ((v : SobolevData (centeredCube zQ rQ hrQ)).1 : SpatialCoordinates d → ℝ) x = F x := by
      rw [ae_restrict_iUnion_iff]
      intro i
      exact aux_i i
    rwa [Measure.restrict_congr_set hcover] at key
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    rw [hFH i x hi]
    exact hHosc i x hi

end SubdiffusiveProcess.Paper

end FSTCell

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

section FSTRepaired
namespace SubdiffusiveProcess.Paper

/-- The target coefficient, continuous on the closed cube, has a globally
continuous representative with two-sided pointwise bounds on the open cube. -/
theorem aux_lem_finite_source_comparison_trial_coefficient
    {d : ℕ} (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (aT : PositiveCoefficient (centeredCube zQ rQ hrQ))
    (haT : ∃ A : SpatialCoordinates d → ℝ,
      ContinuousOn A (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) ∧
      ((aT.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] A)) :
    ∃ A : SpatialCoordinates d → ℝ, Continuous A ∧
      ((aT.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] A) ∧
      ∃ lam Lam : ℝ, 0 < lam ∧
        ∀ x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)),
          lam ≤ A x ∧ A x ≤ Lam := by
  obtain ⟨A0, hA0c, hA0⟩ := haT
  have hKc : IsCompact (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) := by
    rw [show (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) =
      Metric.ball zQ (rQ / 2) from rfl, closure_ball zQ (ne_of_gt (half_pos hrQ))]
    exact isCompact_closedBall zQ (rQ / 2)
  obtain ⟨Aext, hAext⟩ := ContinuousMap.exists_restrict_eq hKc.isClosed
    (⟨(closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).domRestrict A0,
      hA0c.domRestrict⟩ : C(closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), ℝ))
  have hAeq : ∀ x ∈ closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)),
      Aext x = A0 x := by
    intro x hx
    have := congrArg (fun f : C(closure (centeredCube zQ rQ hrQ :
      Set (SpatialCoordinates d)), ℝ) => f ⟨x, hx⟩) hAext
    simpa only [ContinuousMap.coe_mk, domRestrict_apply] using! this
  have hA : ((aT.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] Aext := by
    filter_upwards [hA0, ae_restrict_mem (centeredCube zQ rQ hrQ).isOpen.measurableSet]
      with x h1 h2
    rw [h1, hAeq x (subset_closure h2)]
  obtain ⟨c0, hc0, hac0⟩ := aT.property
  have hlow : ∀ x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), c0 ≤ Aext x := by
    have hae : ∀ᵐ x ∂(volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))),
        c0 - Aext x ≤ 0 := by
      filter_upwards [hac0, hA] with x h1 h2
      rw [← h2]
      linarith
    intro x hx
    have := lane2_le_of_ae_le_of_continuousOn (centeredCube zQ rQ hrQ).isOpen
      ((continuous_const.sub Aext.continuous).continuousOn) hae x hx
    have hh : c0 - Aext x ≤ 0 := by
      simpa only [Pi.sub_apply] using! this
    exact sub_nonpos.mp hh
  obtain ⟨Lam, hLam⟩ := hKc.exists_bound_of_continuousOn Aext.continuous.continuousOn
  refine ⟨Aext, Aext.continuous, hA, c0, Lam, hc0, fun x hx => ⟨hlow x hx, ?_⟩⟩
  have := hLam x (subset_closure hx)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this



theorem aux_lem_finite_source_comparison_trial_dirichlet_branch
    {d : ℕ} [NeZero d]
    {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (closedQ : Set (SpatialCoordinates d))
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (hQ : Q = centeredCube zQ rQ hrQ)
    (hclosedQ : closedQ = closure (Q : Set (SpatialCoordinates d)))
    (N : ℕ)
    (aTarget aSource : PositiveCoefficient Q)
    {A : SpatialCoordinates d → ℝ} (hAm : Measurable A)
    (hA : (aTarget.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hAb : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ A x ∧ A x ≤ Lam)
    (hreg : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s),
      (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆ Q →
        aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity A
          (centeredCube c s hs : Set (SpatialCoordinates d)))
    (err factor : ℝ)
    (hDir : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet aSource F b u →
        ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
          ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
          let cell := fun i => centeredCube (centers i) (sides i) (hside i)
          ∃ hle : ∀ i, cell i ≤ Q,
            (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
              (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
            Pairwise (fun i j =>
              Disjoint (cell i : Set (SpatialCoordinates d))
                (cell j : Set (SpatialCoordinates d))) ∧
            ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
              (Q : Set (SpatialCoordinates d))) ∧
            ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
              ∀ v : killedSobolevGraph (cell i),
                ‖(v : SobolevData (cell i)).1‖ ≤
                  K * ‖@subspaceGradient d (cell i)
                    (killedSobolevGraph (cell i)) v‖,
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U closedQ ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                  ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                    |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
            (∑ i : Fin ncell,
                @dirichletResponse d (cell i)
                  (@killedResponseSpace d (cell i) (hPcell i))
                  (positiveCoefficientRestrict (hle i) aTarget)
                  ⟨sobolevDataRestrict (hle i) u.val,
                    sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
                factor * sobolevCoefficientForm aSource u.val u.val +
                  err * (Kf + c2Norm closedQ phi) ^ 2)
    :
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet aSource F b u →
        ∃ (v : weakSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
          (v : SobolevData Q) - (b : SobolevData Q) ∈ killedSobolevGraph Q ∧
          ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
          ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
          ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ closedQ, |V x - U x| ≤ err * (Kf + c2Norm closedQ phi)) ∧
          sobolevCoefficientForm aTarget v.val v.val ≤
            factor * sobolevCoefficientForm aSource u.val u.val +
              err * (Kf + c2Norm closedQ phi) ^ 2) := by
  subst hQ
  subst hclosedQ
  have hzQ : zQ ∈ closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
    subset_closure (Metric.mem_ball_self (half_pos hrQ))
  intro F Kf hKf hF hFb phi hphi b u hb hsol
  obtain ⟨ncell, centers, sides, hside, hle, -, hdisj, hcover, hPcell, U, hUc, hUae,
    hosc, hsum⟩ := hDir F Kf hKf hF hFb phi hphi b u hb hsol
  beta_reduce at hle hdisj hcover hPcell hosc hsum
  obtain ⟨v, V, hvb, hVc, hvV, hVU, henergy⟩ :=
    aux_lem_finite_source_comparison_trial_glue zQ rQ hrQ ncell centers sides hside hle
      hdisj hcover hPcell aTarget hAm hA hlam hAb
      (fun i => hreg (centers i) (sides i) (hside i) (hle i)) b u hsol.1 hUc hUae hosc
  refine ⟨v, U, V, hvb, hUc, hVc, hUae, hvV, ?_, ?_⟩
  · intro x hx
    have h1 := hVU x hx
    have h0 := (abs_nonneg _).trans (hVU zQ hzQ)
    have h4 : err * (Kf + c2Norm (closure (centeredCube zQ rQ hrQ :
        Set (SpatialCoordinates d))) phi) =
        4 * (err / 4 * (Kf + c2Norm (closure (centeredCube zQ rQ hrQ :
          Set (SpatialCoordinates d))) phi)) := by ring
    linarith
  · rw [henergy]
    exact hsum



theorem aux_lem_finite_source_comparison_trial_neumann_branch
    {d : ℕ} [NeZero d]
    {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (closedQ : Set (SpatialCoordinates d))
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (hQ : Q = centeredCube zQ rQ hrQ)
    (hclosedQ : closedQ = closure (Q : Set (SpatialCoordinates d)))
    (N : ℕ)
    (aTarget aSource : PositiveCoefficient Q)
    {A : SpatialCoordinates d → ℝ} (hAm : Measurable A)
    (hA : (aTarget.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hAb : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ A x ∧ A x ≤ Lam)
    (hreg : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s),
      (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆ Q →
        aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity A
          (centeredCube c s hs : Set (SpatialCoordinates d)))
    (err factor : ℝ)
    (hNeu : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
      ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
        ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
          (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
          Pairwise (fun i j =>
            Disjoint (cell i : Set (SpatialCoordinates d))
              (cell j : Set (SpatialCoordinates d))) ∧
          ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
            (Q : Set (SpatialCoordinates d))) ∧
          ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
            ∀ v : killedSobolevGraph (cell i),
              ‖(v : SobolevData (cell i)).1‖ ≤
                K * ‖@subspaceGradient d (cell i)
                  (killedSobolevGraph (cell i)) v‖,
            ∃ U : SpatialCoordinates d → ℝ,
              ContinuousOn U closedQ ∧
              (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
              (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                  |U x - U y| ≤ (err / 4) * Kf) ∧
            (∑ i : Fin ncell,
              @dirichletResponse d (cell i)
                (@killedResponseSpace d (cell i) (hPcell i))
                (positiveCoefficientRestrict (hle i) aTarget)
                ⟨sobolevDataRestrict (hle i) u.val,
                  sobolevDataRestrict_mem_weak (hle i)
                    ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
              factor * sobolevCoefficientForm aSource u.val u.val + err * Kf ^ 2)
    :
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
      ∃ (v : meanZeroSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
        ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
        ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
        ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ closedQ, |V x - U x| ≤ err * Kf) ∧
        sobolevCoefficientForm aTarget v.val v.val ≤
          factor * sobolevCoefficientForm aSource u.val u.val + err * Kf ^ 2) := by
  subst hQ
  subst hclosedQ
  have hzQ : zQ ∈ closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
    subset_closure (Metric.mem_ball_self (half_pos hrQ))
  have hKc : IsCompact (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) := by
    rw [show (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) =
      Metric.ball zQ (rQ / 2) from rfl, closure_ball zQ (ne_of_gt (half_pos hrQ))]
    exact isCompact_closedBall zQ (rQ / 2)
  intro F Kf hKf hF hFb hFmean u hsol
  obtain ⟨ncell, centers, sides, hside, hle, -, hdisj, hcover, hPcell, U, hUc, hUae,
    hosc, hsum⟩ := hNeu F Kf hKf hF hFb hFmean u hsol
  beta_reduce at hle hdisj hcover hPcell hosc hsum
  have humem := (mem_meanZeroSobolevGraph_iff u.val).mp u.property
  let uw : weakSobolevGraph (centeredCube zQ rQ hrQ) := ⟨u.val, humem.1⟩
  have huw : uw.val - uw.val ∈ killedSobolevGraph (centeredCube zQ rQ hrQ) := by
    rw [sub_self]
    exact (killedSobolevGraph (centeredCube zQ rQ hrQ)).zero_mem
  obtain ⟨v, V, -, hVc, hvV, hVU, henergy⟩ :=
    aux_lem_finite_source_comparison_trial_glue zQ rQ hrQ ncell centers sides hside hle
      hdisj hcover hPcell aTarget hAm hA hlam hAb
      (fun i => hreg (centers i) (sides i) (hside i) (hle i)) uw uw huw hUc hUae hosc
  have hQb : Bornology.IsBounded (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
    Metric.isBounded_ball
  have hvolpos : 0 < volume.real (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) := by
    have hlt : volume (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) < ⊤ := by
      simpa only [Measure.restrict_apply_univ] using
        (measure_lt_top (volume.restrict
          (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) univ)
    have hpos : 0 < volume (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) :=
      Metric.measure_ball_pos volume zQ (half_pos hrQ)
    exact ENNReal.toReal_pos hpos.ne' hlt.ne
  obtain ⟨v', hv'energy, hv'ae⟩ :=
    aux_lem_finite_source_comparison_trial_centered_energy hQb hvolpos.ne' aTarget v
  let mV : ℝ := (∫ y in (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), V y) /
    volume.real (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))
  refine ⟨v', U, fun x => V x - mV, hUc, hVc.sub continuousOn_const, hUae, ?_, ?_, ?_⟩
  · have hint : (∫ y in (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), v.val.1 y) =
        ∫ y in (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), V y :=
      integral_congr_ae hvV
    filter_upwards [hv'ae, hvV] with x h1 h2
    rw [h1, h2, hint]
  · intro x hx
    have hzero : (∫ x in (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), U x) = 0 := by
      rw [← integral_congr_ae hUae]
      exact humem.2
    have hs := aux_lem_finite_source_comparison_trial_mean_subtraction_sup hKc subset_closure
      hvolpos hUc hVc hVU hzero x hx
    have h0 := (abs_nonneg _).trans (hVU zQ hzQ)
    have h4 : err * Kf = 4 * (err / 4 * Kf) := by ring
    change |V x - mV - U x| ≤ err * Kf
    linarith
  · rw [hv'energy, henergy]
    exact hsum

end SubdiffusiveProcess.Paper

end FSTRepaired

namespace SubdiffusiveProcess.Paper



theorem lem_finite_source_comparison_trial
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d)
    {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (closedQ : Set (SpatialCoordinates d))
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (hQ : Q = centeredCube zQ rQ hrQ)
    (hclosedQ : closedQ = closure (Q : Set (SpatialCoordinates d)))
    (N : ℕ)
    (aTarget aSource : PositiveCoefficient Q)
    (haTarget : ∃ A : SpatialCoordinates d → ℝ, ContinuousOn A closedQ ∧
      ((aTarget.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A))
    (err factor : ℝ)
    (hDir : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet aSource F b u →
        ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
          ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
          let cell := fun i => centeredCube (centers i) (sides i) (hside i)
          ∃ hle : ∀ i, cell i ≤ Q,
            (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
              (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
            Pairwise (fun i j =>
              Disjoint (cell i : Set (SpatialCoordinates d))
                (cell j : Set (SpatialCoordinates d))) ∧
            ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
              (Q : Set (SpatialCoordinates d))) ∧
            ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
              ∀ v : killedSobolevGraph (cell i),
                ‖(v : SobolevData (cell i)).1‖ ≤
                  K * ‖@subspaceGradient d (cell i)
                    (killedSobolevGraph (cell i)) v‖,
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U closedQ ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                  ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                    |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
            (∑ i : Fin ncell,
                @dirichletResponse d (cell i)
                  (@killedResponseSpace d (cell i) (hPcell i))
                  (positiveCoefficientRestrict (hle i) aTarget)
                  ⟨sobolevDataRestrict (hle i) u.val,
                    sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
                factor * sobolevCoefficientForm aSource u.val u.val +
                  err * (Kf + c2Norm closedQ phi) ^ 2)
    (hNeu : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
      ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
        ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
          (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
          Pairwise (fun i j =>
            Disjoint (cell i : Set (SpatialCoordinates d))
              (cell j : Set (SpatialCoordinates d))) ∧
          ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
            (Q : Set (SpatialCoordinates d))) ∧
          ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
            ∀ v : killedSobolevGraph (cell i),
              ‖(v : SobolevData (cell i)).1‖ ≤
                K * ‖@subspaceGradient d (cell i)
                  (killedSobolevGraph (cell i)) v‖,
            ∃ U : SpatialCoordinates d → ℝ,
              ContinuousOn U closedQ ∧
              (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
              (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                  |U x - U y| ≤ (err / 4) * Kf) ∧
            (∑ i : Fin ncell,
              @dirichletResponse d (cell i)
                (@killedResponseSpace d (cell i) (hPcell i))
                (positiveCoefficientRestrict (hle i) aTarget)
                ⟨sobolevDataRestrict (hle i) u.val,
                  sobolevDataRestrict_mem_weak (hle i)
                    ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
              factor * sobolevCoefficientForm aSource u.val u.val + err * Kf ^ 2) :
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet aSource F b u →
        ∃ (v : weakSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
          (v : SobolevData Q) - (b : SobolevData Q) ∈ killedSobolevGraph Q ∧
          ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
          ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
          ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ closedQ, |V x - U x| ≤ err * (Kf + c2Norm closedQ phi)) ∧
          sobolevCoefficientForm aTarget v.val v.val ≤
            factor * sobolevCoefficientForm aSource u.val u.val +
              err * (Kf + c2Norm closedQ phi) ^ 2) ∧
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
      ∃ (v : meanZeroSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
        ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
        ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
        ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ closedQ, |V x - U x| ≤ err * Kf) ∧
        sobolevCoefficientForm aTarget v.val v.val ≤
          factor * sobolevCoefficientForm aSource u.val u.val + err * Kf ^ 2) := by
  have : NeZero d := ⟨by omega⟩
  have haT := haTarget
  subst hQ
  subst hclosedQ
  obtain ⟨A, hAc, hA, lam, Lam, hlam, hAb⟩ :=
    aux_lem_finite_source_comparison_trial_coefficient zQ rQ hrQ aTarget haT
  have hreg : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s),
      (centeredCube c s hs : Set (SpatialCoordinates d)) ⊆
        (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) →
        aux_lem_finite_source_comparison_trial_SmoothDataCellRegularity A
          (centeredCube c s hs : Set (SpatialCoordinates d)) :=
    fun c s hs hsub => aux_lem_finite_source_comparison_trial_regular_of_continuous hd c s hs
      hAc hlam (fun x hx => hAb x (hsub hx))
  exact ⟨aux_lem_finite_source_comparison_trial_dirichlet_branch _ zQ rQ hrQ rfl rfl N
      aTarget aSource hAc.measurable hA hlam hAb hreg err factor hDir,
    aux_lem_finite_source_comparison_trial_neumann_branch _ zQ rQ hrQ rfl rfl N
      aTarget aSource hAc.measurable hA hlam hAb hreg err factor hNeu⟩

end SubdiffusiveProcess.Paper
