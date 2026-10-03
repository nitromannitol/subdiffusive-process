module

public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates

@[expose] public section

/-! # Weak maximum bounds for cellwise harmonic cutoff extensions -/

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

theorem ae_le_of_harmonic
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
  haveI : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
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
theorem isWeaklyHarmonicOn_neg
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
theorem hasZeroTraceDifferenceOn_neg
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
theorem le_ae_of_harmonic
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {h g : H1Function W} (hharm : IsWeaklyHarmonicOn a W h)
    (htr : HasZeroTraceDifferenceOn W h g) {m : ℝ}
    (hg : ∀ x ∈ W, m ≤ g.toFun x) :
    ∀ᵐ x ∂(volume.restrict W), m ≤ h.toFun x := by
  have hle := ae_le_of_harmonic hW hlam hameas
    hbounds (isWeaklyHarmonicOn_neg hharm)
    (hasZeroTraceDifferenceOn_neg htr) (M := -m)
    (fun x hx => by
      rw [H1Function.neg_toFun]
      simp only
      linarith [hg x hx])
  filter_upwards [hle] with x hx
  rw [H1Function.neg_toFun] at hx
  simp only at hx
  linarith


end SubdiffusiveProcess.Static
