module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.KuhnDensity
public import Homogenization.Sobolev.H1.Algebra

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

/-! ## The energy of one competitor -/



def dirichletEnergyOn' (B : Vec d → ℝ) (U : Set (Vec d)) (p : Vec d)
    (Dw : Vec d → Vec d) : ℝ :=
  ∫ x in U, B x * vecNormSq (p + Dw x)

/-- The set of competitor energies whose infimum is the continuum minimum. -/
def dirichletEnergySet (B : Vec d → ℝ) (U : Set (Vec d)) (p : Vec d) : Set ℝ :=
  {E | ∃ w : H10Function U, E = dirichletEnergyOn' B U p w.toH1Function.grad}



def dirichletInfOn (B : Vec d → ℝ) (U : Set (Vec d)) (p : Vec d) : ℝ :=
  sInf (dirichletEnergySet B U p)

theorem dirichletEnergySet_nonempty (B : Vec d → ℝ) (U : Set (Vec d)) (p : Vec d) :
    (dirichletEnergySet B U p).Nonempty :=
  ⟨_, (0 : H10Function U), rfl⟩

theorem bddBelow_dirichletEnergySet {B : Vec d → ℝ} {U : Set (Vec d)} (p : Vec d)
    (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    BddBelow (dirichletEnergySet B U p) := by
  refine ⟨0, ?_⟩
  rintro E ⟨w, rfl⟩
  exact setIntegral_nonneg hU fun x _ => mul_nonneg (hB x) (vecNormSq_nonneg _)

/-- **The defining bound**: every admissible competitor dominates the infimum. -/
theorem dirichletInfOn_le {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) (w : H10Function U) :
    dirichletInfOn B U p ≤ dirichletEnergyOn' B U p w.toH1Function.grad :=
  csInf_le (bddBelow_dirichletEnergySet p hU hB) ⟨w, rfl⟩

theorem dirichletInfOn_nonneg {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) : 0 ≤ dirichletInfOn B U p := by
  refine le_csInf (dirichletEnergySet_nonempty B U p) ?_
  rintro E ⟨w, rfl⟩
  exact setIntegral_nonneg hU fun x _ => mul_nonneg (hB x) (vecNormSq_nonneg _)



theorem dirichletInfOn_le_affine {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (hU : MeasurableSet U) (hB : ∀ x, 0 ≤ B x) :
    dirichletInfOn B U p ≤ ∫ x in U, B x * vecNormSq p := by
  have h := dirichletInfOn_le (B := B) (U := U) (p := p) hU hB 0
  have hgrad : ((0 : H10Function U).toH1Function).grad = (0 : Vec d → Vec d) := rfl
  rw [dirichletEnergyOn', hgrad] at h
  simpa using h

/-! ## Integrability of the energy integrand -/

private theorem vecNormSq_add_eq_sum (p q : Vec d) :
    vecNormSq (p + q) = ∑ i, (p i + q i) ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

/-- **The energy integrand is integrable.**  A bounded measurable weight against
the square of an `L^2` gradient is integrable on a finite-measure domain.  This
is the side condition of every comparison of two energies. -/
theorem integrableOn_smul_vecNormSq_add_grad {B : Vec d → ℝ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] (hBmeas : Measurable B) {C : ℝ}
    (hBbd : ∀ x, ‖B x‖ ≤ C) (w : H1Function U) (p : Vec d) :
    IntegrableOn (fun x => B x * vecNormSq (p + w.grad x)) U volume := by
  have hmemLp : ∀ i : Fin d,
      MemLp (fun x => p i + w.grad x i) 2 (volume.restrict U) := fun i =>
    (memLp_const (p i)).add (w.gradMemL2 i)
  have hsq : Integrable (fun x => vecNormSq (p + w.grad x)) (volume.restrict U) := by
    have := integrable_finset_sum (μ := volume.restrict U) Finset.univ
      (f := fun (i : Fin d) (x : Vec d) => (p i + w.grad x i) ^ 2)
      fun i _ => (hmemLp i).integrable_sq
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (vecNormSq_add_eq_sum p (w.grad x)).symm
  exact hsq.bdd_mul hBmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hBbd)

/-! ## Comparison of two weights -/

/-- Monotonicity of the energy in the coefficient. -/
theorem dirichletEnergyOn'_mono {B B' : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    {Dw : Vec d → Vec d} (hU : MeasurableSet U)
    (hint : IntegrableOn (fun x => B x * vecNormSq (p + Dw x)) U volume)
    (hint' : IntegrableOn (fun x => B' x * vecNormSq (p + Dw x)) U volume)
    (hle : ∀ x ∈ U, B x ≤ B' x) :
    dirichletEnergyOn' B U p Dw ≤ dirichletEnergyOn' B' U p Dw :=
  setIntegral_mono_on hint hint' hU fun x hx =>
    mul_le_mul_of_nonneg_right (hle x hx) (vecNormSq_nonneg _)



theorem dirichletInfOn_le_kuhnEnvelope_energy {B : Vec d → ℝ} {U : Set (Vec d)}
    {p : Vec d} {S : Finset (KuhnCell d)} {s : ℤ} (hU : MeasurableSet U)
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x)
    (hcover : ∀ x ∈ U, ∃ T ∈ S, x ∈ T.carrier)
    (w : H10Function U)
    (hint : IntegrableOn (fun x => B x * vecNormSq (p + w.toH1Function.grad x)) U volume)
    (hint' : IntegrableOn
      (fun x => kuhnEnvelope S B x * vecNormSq (p + w.toH1Function.grad x)) U volume) :
    dirichletInfOn B U p ≤
      dirichletEnergyOn' (kuhnEnvelope S B) U p w.toH1Function.grad := by
  refine le_trans (dirichletInfOn_le hU hB0 w) ?_
  refine dirichletEnergyOn'_mono hU hint hint' fun x hx => ?_
  obtain ⟨T, hT, hxT⟩ := hcover x hx
  exact le_kuhnEnvelope hscale hB hT hxT

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
