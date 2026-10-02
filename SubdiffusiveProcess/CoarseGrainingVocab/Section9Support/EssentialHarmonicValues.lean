import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicBoundedness

/-! # Affine value changes of bundled weak harmonic functions -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Scaling and translating values preserve the bundled weak equation. -/
theorem essential_harmonic_affine {d : ℕ} {U : Set (Vec d)} {a : Vec d → ℝ}
    [IsFiniteMeasure (volume.restrict U)]
    (u : H1Function U) (hu : IsWeaklyHarmonicOn a U u) (s t : ℝ) :
    IsWeaklyHarmonicOn a U ((s • u).addConst t) := by
  intro phi
  have hpoint (x : Vec d) :
      vecDot (a x • ((s • u).addConst t).grad x) (phi.toH1Function.grad x) =
        s * vecDot (a x • u.grad x) (phi.toH1Function.grad x) := by
    simp only [H1Function.grad_addConst, H1Function.smul_grad, smul_smul, vecDot_smul_left]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, hu phi, mul_zero]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
