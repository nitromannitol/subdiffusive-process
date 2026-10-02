import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

/-- Multiplying a scalar coefficient by a spatially constant factor preserves
its homogeneous weak equation. -/
theorem IsWeaklyHarmonicOn.const_mul {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} (c : ℝ)
    (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn (fun x ↦ c * a x) U u := by
  intro phi
  calc
    ∫ x in U, vecDot ((c * a x) • u.grad x)
        (phi.toH1Function.grad x) ∂volume =
        c * ∫ x in U, vecDot (a x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            simp only [mul_smul, vecDot_smul_left]
    _ = 0 := by rw [hu phi, mul_zero]

/-- A nonzero constant factor can be cancelled from a homogeneous weak
equation. -/
theorem IsWeaklyHarmonicOn.of_const_mul {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} {c : ℝ} (hc : c ≠ 0)
    (hu : IsWeaklyHarmonicOn (fun x ↦ c * a x) U u) :
    IsWeaklyHarmonicOn a U u := by
  have hscaled :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsWeaklyHarmonicOn.const_mul c⁻¹ hu
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hscaled

/-- Multiplication by a nonzero spatial constant leaves the class of
homogeneous weak solutions unchanged. -/
theorem isWeaklyHarmonicOn_const_mul_iff {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} {c : ℝ} (hc : c ≠ 0) :
    IsWeaklyHarmonicOn (fun x ↦ c * a x) U u ↔
      IsWeaklyHarmonicOn a U u :=
  ⟨fun hu ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsWeaklyHarmonicOn.of_const_mul hc hu,
    fun hu ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsWeaklyHarmonicOn.const_mul c hu⟩

/-- Scaling the coefficient and divergence datum by the same spatially
constant factor preserves the inhomogeneous weak equation. -/
theorem IsDivFormWeakSolutionOn.const_mul {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} {g : Vec d → Vec d} (c : ℝ)
    (hu : IsDivFormWeakSolutionOn a U u g) :
    IsDivFormWeakSolutionOn (fun x ↦ c * a x) U u (fun x ↦ c • g x) := by
  intro phi
  calc
    ∫ x in U, vecDot ((c * a x) • u.grad x)
        (phi.toH1Function.grad x) ∂volume =
        c * ∫ x in U, vecDot (a x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            simp only [mul_smul, vecDot_smul_left]
    _ = c * (-∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume) := by
      rw [hu phi]
    _ = -∫ x in U, vecDot (c • g x) (phi.toH1Function.grad x) ∂volume := by
      have hscale :
          ∫ x in U, vecDot (c • g x) (phi.toH1Function.grad x) ∂volume =
            c * ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [vecDot_smul_left]
      rw [hscale]
      ring

/-- A nonzero common factor can be cancelled from the coefficient and the
divergence datum. -/
theorem IsDivFormWeakSolutionOn.of_const_mul {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} {g : Vec d → Vec d} {c : ℝ}
    (hc : c ≠ 0)
    (hu : IsDivFormWeakSolutionOn (fun x ↦ c * a x) U u
      (fun x ↦ c • g x)) :
    IsDivFormWeakSolutionOn a U u g := by
  have hscaled :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDivFormWeakSolutionOn.const_mul c⁻¹ hu
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul,
    inv_smul_smul₀ hc] using hscaled

/-- Multiplication of the coefficient and divergence datum by the same
nonzero spatial constant preserves and reflects the weak equation. -/
theorem isDivFormWeakSolutionOn_const_mul_iff {d : ℕ} {a : Vec d → ℝ}
    {U : Set (Vec d)} {u : H1Function U} {g : Vec d → Vec d} {c : ℝ}
    (hc : c ≠ 0) :
    IsDivFormWeakSolutionOn (fun x ↦ c * a x) U u (fun x ↦ c • g x) ↔
      IsDivFormWeakSolutionOn a U u g :=
  ⟨fun hu ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDivFormWeakSolutionOn.of_const_mul hc hu,
    fun hu ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDivFormWeakSolutionOn.const_mul c hu⟩



theorem IsDirichletSolutionOn.const_mul {d : ℕ} {a : Vec d → ℝ}
    {Q : TriadicCube d} {u h : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (c : ℝ) (hu : IsDirichletSolutionOn a Q u h g) :
    IsDirichletSolutionOn (fun x ↦ c * a x) Q u h (fun x ↦ c • g x) :=
  ⟨hu.1,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDivFormWeakSolutionOn.const_mul c hu.2⟩

/-- For a nonzero constant, the complete Dirichlet predicates before and
after common rescaling are equivalent. -/
theorem isDirichletSolutionOn_const_mul_iff {d : ℕ} {a : Vec d → ℝ}
    {Q : TriadicCube d} {u h : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} {c : ℝ} (hc : c ≠ 0) :
    IsDirichletSolutionOn (fun x ↦ c * a x) Q u h (fun x ↦ c • g x) ↔
      IsDirichletSolutionOn a Q u h g := by
  constructor
  · intro hu
    exact ⟨hu.1,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDivFormWeakSolutionOn.of_const_mul hc hu.2⟩
  · exact fun hu ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.IsDirichletSolutionOn.const_mul c hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
