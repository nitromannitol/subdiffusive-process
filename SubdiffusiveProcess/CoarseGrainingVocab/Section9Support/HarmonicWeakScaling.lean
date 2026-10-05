module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundedness
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation

@[expose] public section

/-!
# Dilation of the local weak-harmonicity predicate

The actual Sobolev witnesses and zero-trace tests are transported by positive
dilation. No regularity or pointwise measurability of the coefficient is
needed for this covariance of the weak equation.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped Pointwise ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private def castH10 {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H10Function U) : H10Function V := hUV ▸ u

private theorem castH10_grad {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H10Function U) (x : Vec d) :
    (castH10 hUV u).toH1Function.grad x = u.toH1Function.grad x := by
  cases hUV
  rfl

/-- Pullback of an almost-everywhere assertion under positive dilation. -/
theorem harmonic_ae_smul {d : ℕ} {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    {P : Vec d → Prop} (hP : ∀ᵐ x ∂volume.restrict (r • U), P x) :
    ∀ᵐ x ∂volume.restrict U, P (r • x) := by
  apply ae_of_ae_map (measurable_const_smul r).aemeasurable
  rw [map_smul_volume_restrict hr]
  exact Measure.ae_smul_measure hP _

/-- The weak equation is invariant under pullback by positive dilation. -/
theorem harmonic_isWeaklyHarmonic_unscale {d : ℕ} {U : Set (Vec d)}
    {r : ℝ} (hr : 0 < r) {a : Vec d → ℝ}
    (u : H1Function (r • U)) (hu : IsWeaklyHarmonicOn a (r • U) u) :
    IsWeaklyHarmonicOn (fun x => a (r • x)) U (u.unscale hr) := by
  intro phi
  have hdom : r⁻¹ • (r • U) = U := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  let psi : H10Function (r • U) := (castH10 hdom.symm phi).unscale (inv_pos.mpr hr)
  have hpsi (x : Vec d) : psi.toH1Function.grad (r • x) = r⁻¹ • phi.toH1Function.grad x := by
    simp only [psi, H10Function.unscale_toH1Function, H1Function.unscale_grad,
      castH10_grad, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  let f : Vec d → ℝ := fun y => a y * vecDot (u.grad y) (psi.toH1Function.grad y)
  have hf : (∫ y in r • U, f y) = 0 := by
    simpa only [f, vecDot_smul_left] using hu psi
  have hpoint (x : Vec d) :
      vecDot (a (r • x) • (u.unscale hr).grad x) (phi.toH1Function.grad x) =
        r ^ 2 * f (r • x) := by
    simp only [H1Function.unscale_grad, vecDot_smul_left, f, hpsi, vecDot_smul_right]
    field_simp
  simp_rw [hpoint]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume f U hr, hf,
    smul_zero, mul_zero]

/-- Positive dilation transports every local Sobolev witness in
`WeakHarmonic`, as well as its continuous representative. -/
theorem harmonic_weakHarmonic_unscale {d : ℕ} {U : Set (Vec d)}
    {r : ℝ} (hr : 0 < r) {a h : Vec d → ℝ}
    (hh : WeakHarmonic a (r • U) h) :
    WeakHarmonic (fun x => a (r • x)) U (fun x => h (r • x)) := by
  refine ⟨hh.1.comp (continuous_const_smul r).continuousOn (fun x hx => ⟨x, hx, rfl⟩), ?_⟩
  intro W hW hcompact hsub
  have hWr : IsOpen (r • W) := (Homeomorph.smulOfNeZero r hr.ne').isOpenMap W hW
  have hcompactr : IsCompact (closure (r • W)) := by
    rw [closure_smul₀]
    exact hcompact.image (continuous_const_smul r)
  have hsubr : closure (r • W) ⊆ r • U := by
    rw [closure_smul₀]
    exact smul_set_mono hsub
  obtain ⟨u, hueq, hu⟩ := hh.2 (r • W) hWr hcompactr hsubr
  refine ⟨u.unscale hr, ?_, ?_⟩
  · exact harmonic_ae_smul hr hueq
  · have hu' : IsWeaklyHarmonicOn a (r • W) u := by
      intro phi
      simpa only [vecDot_smul_left] using hu phi
    intro phi
    simpa only [vecDot_smul_left] using harmonic_isWeaklyHarmonic_unscale hr u hu' phi

/-- Centered cubes have the expected image under positive dilation. -/
theorem harmonic_smul_centeredAxisCube {d : ℕ} (z : Vec d) (L : ℝ)
    {r : ℝ} (hr : 0 < r) :
    r • centeredAxisCube z L = centeredAxisCube (r • z) (r * L) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centeredAxisCube.mpr
    intro i
    have hi := mem_centeredAxisCube.mp hy i
    change |r * y i - r * z i| < r * L / 2
    rw [← mul_sub, abs_mul, abs_of_pos hr]
    nlinarith
  · intro hx
    refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hr.ne' x⟩
    apply mem_centeredAxisCube.mpr
    intro i
    have hi := mem_centeredAxisCube.mp hx i
    change |r⁻¹ * x i - z i| < L / 2
    have heq : r⁻¹ * x i - z i = r⁻¹ * (x i - r * z i) := by field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hr)]
    change |x i - r * z i| < r * L / 2 at hi
    have hm := mul_lt_mul_of_pos_left hi (inv_pos.mpr hr)
    convert hm using 1
    field_simp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
