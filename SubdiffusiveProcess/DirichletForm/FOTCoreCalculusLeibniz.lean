module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusProduct

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

theorem EnergyFamily.core_leibniz_formula {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hv : F.toClosedForm.MemCoreOn U v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal =
      (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂(Γ.measure u)) +
        2 * _root_.DirichletForm.signedIntegralOn (Γ.cross u v) B
          (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, Φ (uc x) ^ 2 ∂(Γ.measure v)) := by
  have hwU := core_mul_composition hu hv huae hvae hΦ hwae
  have hpc : Continuous (fun x => Φ (uc x)) := hΦ.continuous.comp huc
  have hdc : Continuous (fun x => deriv Φ (uc x)) := (hΦ.continuous_deriv le_rfl).comp huc
  have hac : Continuous (fun x => vc x * deriv Φ (uc x)) := hvc.mul hdc
  have hW := Γ.core_cross_mul_comp_measure h hu hv hwU huc hvc (hvc.mul hpc)
    huae hvae hwae Φ hΦ hwae
  have hA := Γ.core_cross_mul_comp_integral h hu hv hu huc hvc huc huae hvae huae
    Φ hΦ hwae hac hB
  have hD := Γ.core_cross_mul_comp_integral h hu hv hv huc hvc hvc huae hvae hvae
    Φ hΦ hwae hpc hB
  rw [Γ.cross_symm w hw u hu.1] at hA
  rw [Γ.cross_symm w hw v hv.1] at hD
  rw [Γ.cross_symm v hv.1 u hu.1] at hA
  have hselfA := Γ.signedIntegralOn_self h hu (hac.mul hac) B
  change signedIntegralOn (Γ.cross u u) B (fun x => (vc x * deriv Φ (uc x)) * (vc x * deriv Φ (uc x))) = _ at hselfA
  rw [hselfA] at hA
  have hselfD := Γ.signedIntegralOn_self h hv (hpc.mul hpc) B
  change signedIntegralOn (Γ.cross v v) B (fun x => Φ (uc x) * Φ (uc x)) = _ at hselfD
  rw [hselfD] at hD
  simp only [Pi.mul_apply] at hA hD
  have hpointA : (fun x => vc x * deriv Φ (uc x) * (vc x * deriv Φ (uc x))) =
      (fun x => vc x ^ 2 * deriv Φ (uc x) ^ 2) := by funext x; ring
  have hpointD : (fun x => Φ (uc x) * Φ (uc x)) = (fun x => Φ (uc x) ^ 2) := by
    funext x; ring
  have hpointC : (fun x => Φ (uc x) * (vc x * deriv Φ (uc x))) =
      (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) := by funext x; ring
  have hpointE : (fun x => vc x * deriv Φ (uc x) * Φ (uc x)) =
      (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) := by funext x; ring
  rw [hpointA, hpointC] at hA
  rw [hpointD, hpointE] at hD
  rw [← Γ.cross_self w hw B hB, hW, VectorMeasure.add_apply,
    signedDensity_apply _ (Γ.core_signedIntegrable h hu hw hac) hB,
    signedDensity_apply _ (Γ.core_signedIntegrable h hv hw hpc) hB, hA, hD]
  ring

end DirichletForm.FOTConstruction
