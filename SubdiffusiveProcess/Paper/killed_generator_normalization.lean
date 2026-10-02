import SubdiffusiveProcess.Paper.in_normalization
import SubdiffusiveProcess.Paper.in_killed_energy
import SubdiffusiveProcess.Paper.in_brownian_normalization
import SubdiffusiveProcess.Paper.in_energy_measure
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Sobolev.LocalEnergy
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import Mathlib.Analysis.Calculus.FDeriv.Mul
import SubdiffusiveProcess.Probability.BrownianProduct.PathLaw
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
import SubdiffusiveProcess.Lane3.LocalEnergyAux

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace Paper

private theorem aux_gradientEnergy_withDensity_finite_and_real
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (g : HilbertGradient Ω) :
    IsFiniteMeasure
        ((volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
          (fun x => ENNReal.ofReal (∑ i : Fin d, a.val x * (g i x) ^ 2))) ∧
      ∀ (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s),
        (((volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
          (fun x => ENNReal.ofReal (∑ i : Fin d, a.val x * (g i x) ^ 2))).real s) =
          localGradientEnergy a hs g := by
  simpa only using
    (gradientEnergy_withDensity_finite_and_real (a := a) (g := g))

private theorem aux_killed_energy_measure
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      ∃ Gamma : Measure (SpatialCoordinates d),
        Gamma =
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x *
                (∑ i : Fin d,
                  ((((u : SobolevData (centeredCube z r hr))).2 i) x) ^ 2))) ∧
        (∀ (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s),
          Gamma s = ENNReal.ofReal (localGradientEnergy
            (Lane4.cutoffPositiveCoefficient M H omega N z hr) hs
            (sobolevGradient (u : SobolevData (centeredCube z r hr))))) ∧
        Gamma Set.univ < ⊤ ∧
        (Gamma Set.univ).toReal =
          sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
            (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) := by
  intro u
  let Ω := centeredCube z r hr
  let a := Lane4.cutoffPositiveCoefficient M H omega N z hr
  let g := sobolevGradient (u : SobolevData Ω)
  let μa : Measure (SpatialCoordinates d) :=
    (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (∑ i : Fin d, a.val x * (g i x) ^ 2))
  let μraw : Measure (SpatialCoordinates d) :=
    (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x *
        (∑ i : Fin d, ((((u : SobolevData Ω)).2 i) x) ^ 2)))
  letI : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ closedCube z r hr)) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hcoef : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      cutoffCoefficient M H omega N x = a.val x := by
    filter_upwards [
      normalizedContinuousPositiveCoefficient_coeFn
        (Ω := Ω) (K := closedCube z r hr)
        (Lane4.cutoffCoefficientCM M H omega N z hr)
        (Lane4.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hΩ
    have hx' := hx hΩ
    simpa [a, Ω, Lane4.cutoffCoefficientCM] using hx'.symm
  have hμeq : μraw = μa := by
    apply withDensity_congr_ae
    filter_upwards [hcoef] with x hx
    rw [hx]
    congr 1
    rw [Finset.mul_sum]
    rfl
  have hμpair :=
    aux_gradientEnergy_withDensity_finite_and_real (d := d) (Ω := Ω) a g
  obtain ⟨hμfin, hμreal⟩ := hμpair
  have hμrawfin : IsFiniteMeasure μraw := by
    rw [hμeq]
    exact hμfin
  have hlocal (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s) :
      μraw s = ENNReal.ofReal (localGradientEnergy a hs g) := by
    rw [hμeq]
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top μa s) ENNReal.ofReal_ne_top).mp
    have hreal : (μa s).toReal = localGradientEnergy a hs g := by
      simpa [Measure.real, μa] using hμreal s hs
    rw [hreal]
    exact (ENNReal.toReal_ofReal (localGradientEnergy_nonneg a hs g)).symm
  have htotal : μraw Set.univ < ⊤ := by
    rw [hμeq]
    exact measure_lt_top μa Set.univ
  have htotal_real : (μraw Set.univ).toReal =
      sobolevCoefficientForm a (u : SobolevData Ω) (u : SobolevData Ω) := by
    rw [hμeq]
    change μa.real Set.univ = _
    rw [hμreal Set.univ MeasurableSet.univ]
    rw [Lane3.localGradientEnergy_univ]
    rfl
  refine ⟨μraw, ?_, ?_, htotal, ?_⟩
  · rfl
  · intro s hs
    simpa [μraw, μa, Ω, a, g] using hlocal s hs
  · simpa [Ω, a] using htotal_real



theorem killed_generator_normalization
    {d : Nat} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N x =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x) ∧
    (∀ (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d),
      (cutoffSpeedDensity M H omega N x)⁻¹ *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp (-(cutoffPotential H omega N x)) *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1))) ∧
    (∃ B : ProbabilityTheory.Kernel (SpatialCoordinates d) (DiffusionPath d), in_brownian_normalization B) ∧
    (∀ (u : killedSobolevGraph (centeredCube z r hr))
        (F : DomainL2 (centeredCube z r hr)),
      ∃ g : Lp ℝ 2
          ((cutoffSpeedMeasure M H omega N).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))),
          g x = F x / cutoffSpeedDensity M H omega N x) ∧
        ((∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, g x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂((cutoffSpeedMeasure M H omega N).restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))))) ↔
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, F x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))))) ∧
    (∀ (u : killedSobolevGraph (centeredCube z r hr))
        (g : Lp ℝ 2
          ((cutoffSpeedMeasure M H omega N).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)))),
      ∃ F : DomainL2 (centeredCube z r hr),
        (∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))),
          F x = cutoffSpeedDensity M H omega N x * g x) ∧
        ((∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, g x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂((cutoffSpeedMeasure M H omega N).restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))))) ↔
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, F x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))))) ∧
    (∀ u : weakSobolevGraph (centeredCube z r hr),
      ∃ Gamma : Measure (SpatialCoordinates d),
        Gamma =
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x *
                (∑ i : Fin d,
                  ((((u : SobolevData (centeredCube z r hr))).2 i) x) ^ 2))) ∧
        (∀ (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s),
          Gamma s = ENNReal.ofReal (localGradientEnergy
            (Lane4.cutoffPositiveCoefficient M H omega N z hr) hs
            (sobolevGradient (u : SobolevData (centeredCube z r hr))))) ∧
        Gamma Set.univ < ⊤ ∧
    (Gamma Set.univ).toReal =
          sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
            (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr))) := by
  have h_density : ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N x =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x := by
    intro x
    unfold cutoffSpeedDensity cutoffCoefficient
    rw [← mul_assoc, mul_inv_cancel₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne', one_mul]
  have h_generator : ∀ (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d),
      (cutoffSpeedDensity M H omega N x)⁻¹ *
          (∑ i : Fin d,
            (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp (-(cutoffPotential H omega N x)) *
          (∑ i : Fin d,
              (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) := by
    intro f x
    let a : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    let q : ℝ := (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
    have ha : a ≠ 0 := by
      dsimp [a]
      exact (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
    have hterm (i : Fin d) :
        (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
          (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1) =
          (a⁻¹ * Real.exp (-q)) *
            (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
              (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1) := by
      have hfun :
          (fun y => cutoffCoefficient M H omega N y *
            (fderiv ℝ f y) (Pi.single i 1)) =
            (a⁻¹ * Real.exp (-q)) •
              (fun y => Real.exp (cutoffPotential H omega N y) *
                (fderiv ℝ f y) (Pi.single i 1)) := by
        funext y
        simp only [cutoffCoefficient, a, q, Real.exp_sub, Pi.smul_apply, smul_eq_mul]
        have hq : ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
            (N : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
          push_cast
          ring
        rw [hq]
        simp only [Real.exp_neg]
        ring
      rw [hfun, fderiv_const_smul_of_field]
      rfl
    have hsum :
        (∑ i : Fin d,
          (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
            (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) =
          (a⁻¹ * Real.exp (-q)) *
            (∑ i : Fin d,
              (fderiv ℝ (fun y => Real.exp (cutoffPotential H omega N y) *
                (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)) := by
      simp_rw [hterm]
      rw [Finset.mul_sum]
    change (cutoffSpeedDensity M H omega N x)⁻¹ * _ = _
    rw [hsum]
    dsimp [a, q]
    simp only [cutoffSpeedDensity, Real.exp_sub]
    have hq : ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        (N : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
      push_cast
      ring
    rw [hq]
    simp only [Real.exp_neg]
    field_simp [ha, Real.exp_ne_zero]
  have h_brownian : ∃ B : ProbabilityTheory.Kernel (SpatialCoordinates d) (DiffusionPath d),
      in_brownian_normalization B := by
    have htranspose (k : Nat)
        (ν : Fin d → Fin k → Measure ℝ) [∀ i j, IsProbabilityMeasure (ν i j)] :
        (Measure.pi (fun i : Fin d => Measure.pi (fun j : Fin k => ν i j))).map
            (fun y i j => y j i) =
          Measure.pi (fun j : Fin k => Measure.pi (fun i : Fin d => ν i j)) := by
      let e : (Fin d × Fin k) ≃ (Fin k × Fin d) := Equiv.prodComm (Fin d) (Fin k)
      let R : (Fin d × Fin k → ℝ) ≃ᵐ (Fin k × Fin d → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin d => ℝ) e
      let cab : (Fin d × Fin k → ℝ) ≃ᵐ (Fin d → Fin k → ℝ) :=
        MeasurableEquiv.curry (Fin d) (Fin k) ℝ
      let cba : (Fin k × Fin d → ℝ) ≃ᵐ (Fin k → Fin d → ℝ) :=
        MeasurableEquiv.curry (Fin k) (Fin d) ℝ
      have hab :
          (Measure.pi (fun i : Fin d => Measure.pi (fun j : Fin k => ν i j))).map cab.symm =
            Measure.infinitePi (fun p : Fin d × Fin k => ν p.1 p.2) := by
        have hinner : (fun i : Fin d => Measure.pi (fun j : Fin k => ν i j)) =
            (fun i : Fin d => Measure.infinitePi (fun j : Fin k => ν i j)) := by
          funext i
          rw [Measure.infinitePi_eq_pi]
        rw [hinner, ← Measure.infinitePi_eq_pi]
        exact Measure.infinitePi_map_curry_symm ν
      have hba :
          (Measure.infinitePi (fun p : Fin d × Fin k => ν p.1 p.2)).map R =
            Measure.infinitePi (fun p : Fin k × Fin d => ν p.2 p.1) := by
        simpa [R, e] using
          (Measure.infinitePi_map_piCongrLeft
            (μ := fun p : Fin k × Fin d => ν p.2 p.1)
            (X := fun _ : Fin k × Fin d => ℝ) (Equiv.prodComm (Fin d) (Fin k)))
      have hcol :
          (Measure.infinitePi (fun p : Fin k × Fin d => ν p.2 p.1)).map cba =
            Measure.infinitePi (fun j : Fin k => Measure.infinitePi (fun i : Fin d => ν i j)) := by
        exact Measure.infinitePi_map_curry (fun j i => ν i j)
      calc
        (Measure.pi (fun i : Fin d => Measure.pi (fun j : Fin k => ν i j))).map
              (fun y i j => y j i) =
            (((Measure.pi (fun i : Fin d => Measure.pi (fun j : Fin k => ν i j))).map cab.symm).map R).map cba := by
              rw [Measure.map_map, Measure.map_map]
              · rfl
              all_goals fun_prop
        _ = ((Measure.infinitePi (fun p : Fin d × Fin k => ν p.1 p.2)).map R).map cba := by rw [hab]
        _ = (Measure.infinitePi (fun p : Fin k × Fin d => ν p.2 p.1)).map cba := by rw [hba]
        _ = Measure.infinitePi (fun j : Fin k => Measure.infinitePi (fun i : Fin d => ν i j)) := hcol
        _ = Measure.pi (fun j : Fin k => Measure.pi (fun i : Fin d => ν i j)) := by
          have hinnercol : (fun j : Fin k => Measure.infinitePi (fun i : Fin d => ν i j)) =
              (fun j : Fin k => Measure.pi (fun i : Fin d => ν i j)) := by
            funext j
            rw [Measure.infinitePi_eq_pi]
          rw [hinnercol]
          simpa using
            (Measure.infinitePi_eq_pi
              (fun j : Fin k => Measure.pi (fun i : Fin d => ν i j)))
    refine ⟨SubdiffusiveProcess.Probability.BrownianProduct.brownianPath d, ?_⟩
    refine ⟨inferInstance, ?_, ?_⟩
    · intro x
      rw [SubdiffusiveProcess.Probability.BrownianProduct.brownianPath_map_eval]
      have hzero : ∀ i : Fin d, ProbabilityTheory.gaussianReal (x i) (2 * (0 : ℝ≥0)) =
          Measure.dirac (x i) := by
        intro i
        rw [show (2 : ℝ≥0) * 0 = 0 by simp, ProbabilityTheory.gaussianReal_zero_var]
      rw [show (Measure.pi (fun i : Fin d =>
          ProbabilityTheory.gaussianReal (x i) (2 * (0 : ℝ≥0)))) =
          Measure.pi (fun i : Fin d => Measure.dirac (x i)) by
            congr 1; funext i; exact hzero i]
      rw [← Measure.infinitePi_eq_pi, Measure.infinitePi_dirac]
    · intro x k t ht
      have hinc :=
        SubdiffusiveProcess.Probability.BrownianProduct.brownianPath_map_coordinateIncrements x t ht
      let source : DiffusionPath d → (Fin d → Fin k → ℝ) :=
        fun path i j => (path (t j.succ)) i - (path (t j.castSucc)) i
      let target : DiffusionPath d → (Fin k → Fin d → ℝ) :=
        fun path i j => (path (t i.succ)) j - (path (t i.castSucc)) j
      let transpose : (Fin d → Fin k → ℝ) → (Fin k → Fin d → ℝ) :=
        fun y i j => y j i
      have hmap :
          Measure.map target (SubdiffusiveProcess.Probability.BrownianProduct.brownianPath d x) =
            (Measure.map source (SubdiffusiveProcess.Probability.BrownianProduct.brownianPath d x)).map transpose := by
        rw [Measure.map_map]
        · rfl
        · fun_prop
        · fun_prop
      rw [hmap, hinc]
      let gauss : Fin d → Fin k → Measure ℝ := fun i j =>
        ProbabilityTheory.gaussianReal 0 (2 * (t j.succ - t j.castSucc))
      exact htranspose k gauss
  have h_source_to_speed :
      ∀ (u : killedSobolevGraph (centeredCube z r hr))
        (F : DomainL2 (centeredCube z r hr)),
      ∃ g : Lp ℝ 2
          ((cutoffSpeedMeasure M H omega N).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))),
          g x = F x / cutoffSpeedDensity M H omega N x) ∧
        ((∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, g x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂((cutoffSpeedMeasure M H omega N).restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))))) ↔
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, F x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))) := by
    intro u F
    let Ω := centeredCube z r hr
    let μ₀ : Measure (SpatialCoordinates d) := volume.restrict (Ω : Set (SpatialCoordinates d))
    let ρ : SpatialCoordinates d → ℝ := cutoffSpeedDensity M H omega N
    let μ : Measure (SpatialCoordinates d) :=
      (cutoffSpeedMeasure M H omega N).restrict (Ω : Set (SpatialCoordinates d))
    have hρcont : Continuous ρ := by
      have hpot : Continuous (cutoffPotential H omega N) := by
        unfold cutoffPotential
        fun_prop
      dsimp [ρ, cutoffSpeedDensity]
      exact Real.continuous_exp.comp (hpot.sub continuous_const)
    have hρpos : ∀ x, 0 < ρ x := by
      intro x
      exact Real.exp_pos _
    have hρmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
      (hρcont.measurable.ennreal_ofReal)
    have hμ : μ = μ₀.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
      dsimp [μ, μ₀, cutoffSpeedMeasure]
      rw [restrict_withDensity Ω.isOpen.measurableSet]
      rfl
    have hlow : ∃ lo : ℝ, 0 < lo ∧
        ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), lo ≤ ρ x := by
      obtain ⟨lo, hlo, hlo'⟩ :=
        (closedCube z r hr).isCompact.exists_forall_le'
          hρcont.continuousOn (a := 0) (fun x _ => hρpos x)
      exact ⟨lo, hlo, hlo'⟩
    obtain ⟨lo, hlo, hlow⟩ := hlow
    obtain ⟨hi, hhi⟩ := bddAbove_def.mp
      ((closedCube z r hr).isCompact.bddAbove_image hρcont.continuousOn)
    have hupper : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), ρ x ≤ hi := by
      intro x hx
      exact hhi (ρ x) ⟨x, hx, rfl⟩
    have hμle : μ ≤ ENNReal.ofReal hi • μ₀ := by
      rw [hμ]
      refine (withDensity_mono ?_).trans_eq (withDensity_const _)
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal (hupper x (centeredCube_subset_closedCube z hr hx))
    have hμ₀le : μ₀ ≤ ENNReal.ofReal (lo⁻¹) • μ := by
      calc
        μ₀ = μ₀.withDensity (fun _ => 1) := by
          exact (withDensity_one (μ := μ₀)).symm
        _ ≤ μ₀.withDensity (fun x => ENNReal.ofReal (lo⁻¹) * ENNReal.ofReal (ρ x)) := by
          apply withDensity_mono
          filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
          have hxlo := hlow x (centeredCube_subset_closedCube z hr hx)
          have hreal : (1 : ℝ) ≤ lo⁻¹ * ρ x := by
            calc
              (1 : ℝ) = lo⁻¹ * lo := by field_simp
              _ ≤ lo⁻¹ * ρ x := mul_le_mul_of_nonneg_left hxlo (inv_nonneg.mpr hlo.le)
          have hscalar : (1 : ENNReal) ≤ ENNReal.ofReal (lo⁻¹ * ρ x) := by
            simpa using ENNReal.ofReal_le_ofReal hreal
          simpa only [ENNReal.ofReal_mul (inv_nonneg.mpr hlo.le)] using hscalar
        _ = ENNReal.ofReal (lo⁻¹) • μ₀.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
          rw [show (fun x => ENNReal.ofReal (lo⁻¹) * ENNReal.ofReal (ρ x)) =
              (ENNReal.ofReal (lo⁻¹)) • (fun x => ENNReal.ofReal (ρ x)) by rfl]
          exact withDensity_smul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (lo⁻¹) • μ := by rw [hμ]
    have hμac : μ ≪ μ₀ := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
    have hμ₀ac : μ₀ ≪ μ := by
      rw [hμ]
      apply withDensity_absolutelyContinuous' hρmeas.aemeasurable
      filter_upwards with x
      exact ENNReal.ofReal_ne_zero_iff.mpr (hρpos x)
    have hFmem₀ : MemLp (F : SpatialCoordinates d → ℝ) 2 μ₀ := Lp.memLp F
    have hFmem : MemLp (F : SpatialCoordinates d → ℝ) 2 μ :=
      MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hμle hFmem₀
    let q : SpatialCoordinates d → ℝ := fun x => F x / ρ x
    have hqmeas₀ : AEStronglyMeasurable q μ₀ := by
      have hiρ : AEStronglyMeasurable (fun x => (ρ x)⁻¹) μ₀ :=
        hρcont.measurable.aemeasurable.inv.aestronglyMeasurable
      simpa [q, div_eq_mul_inv] using hFmem₀.1.mul hiρ
    have hqmeas : AEStronglyMeasurable q μ := hqmeas₀.mono_ac hμac
    have hqbound : ∀ᵐ x ∂μ, ‖q x‖ ≤ lo⁻¹ * ‖F x‖ := by
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      have hxlo := hlow x (centeredCube_subset_closedCube z hr hx)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (hρpos x)]
      calc
        |F x| / ρ x ≤ |F x| / lo :=
          div_le_div_of_nonneg_left (abs_nonneg _) hlo hxlo
        _ = lo⁻¹ * |F x| := by field_simp
    have hqmem : MemLp q 2 μ := MemLp.of_le_mul hFmem hqmeas hqbound
    let g : Lp ℝ 2 μ := hqmem.toLp q
    have hgq : (g : SpatialCoordinates d → ℝ) =ᵐ[μ] q := hqmem.coeFn_toLp
    let ĝ : SpatialCoordinates d → ℝ := g
    have hpair (v : killedSobolevGraph Ω) :
        (∫ x, ĝ x *
          (((v : SobolevData Ω)).1) x ∂μ) =
        (∫ x, F x * (((v : SobolevData Ω)).1) x ∂μ₀) := by
      have hdens := integral_withDensity_eq_integral_toReal_smul (μ := μ₀)
        hρmeas (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
          (fun x => ĝ x * (((v : SobolevData Ω)).1) x)
      have hdens' : (∫ x, ĝ x * (((v : SobolevData Ω)).1) x ∂μ) =
          ∫ x, (ρ x) * (ĝ x * (((v : SobolevData Ω)).1) x) ∂μ₀ := by
        rw [hμ]
        simpa only [ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using hdens
      rw [hdens']
      have hgq₀ : (g : SpatialCoordinates d → ℝ) =ᵐ[μ₀] q := hμ₀ac.ae_eq hgq
      apply integral_congr_ae
      filter_upwards [hgq₀] with x hx
      change ρ x * (ĝ x * (((v : SobolevData Ω)).1) x) = _
      rw [show ĝ x = (g : SpatialCoordinates d → ℝ) x by rfl, hx]
      simp only [q]
      field_simp [ne_of_gt (hρpos x)]
    refine ⟨g, ?_, ?_⟩
    · simpa [μ, q, ρ] using hgq
    · constructor
      · intro h
        intro v
        have hv := h v
        have hvμ : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
            -(∫ x, ĝ x * (((v : SobolevData Ω)).1) x ∂μ) := by
          simpa [μ, Ω] using hv
        rw [hpair v] at hvμ
        simpa [μ₀, Ω] using hvμ
      · intro h
        intro v
        have hv := h v
        have hv' : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
            -(∫ x, F x * (((v : SobolevData Ω)).1) x ∂μ₀) := by
          simpa [μ₀, Ω] using hv
        rw [← hpair v] at hv'
        simpa [μ, Ω] using hv'
  have h_speed_to_source :
      ∀ (u : killedSobolevGraph (centeredCube z r hr))
        (g : Lp ℝ 2
          ((cutoffSpeedMeasure M H omega N).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)))),
      ∃ F : DomainL2 (centeredCube z r hr),
        (∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))),
          F x = cutoffSpeedDensity M H omega N x * g x) ∧
        ((∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, g x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂((cutoffSpeedMeasure M H omega N).restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))))) ↔
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
              -(∫ x, F x * (((v : SobolevData (centeredCube z r hr))).1) x
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))) := by
    intro u g₀
    let Ω := centeredCube z r hr
    let μ₀ : Measure (SpatialCoordinates d) := volume.restrict (Ω : Set (SpatialCoordinates d))
    let ρ : SpatialCoordinates d → ℝ := cutoffSpeedDensity M H omega N
    let μ : Measure (SpatialCoordinates d) :=
      (cutoffSpeedMeasure M H omega N).restrict (Ω : Set (SpatialCoordinates d))
    have hρcont : Continuous ρ := by
      have hpot : Continuous (cutoffPotential H omega N) := by
        unfold cutoffPotential
        fun_prop
      dsimp [ρ, cutoffSpeedDensity]
      exact Real.continuous_exp.comp (hpot.sub continuous_const)
    have hρpos : ∀ x, 0 < ρ x := by
      intro x
      exact Real.exp_pos _
    have hρmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
      hρcont.measurable.ennreal_ofReal
    have hμ : μ = μ₀.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
      dsimp [μ, μ₀, cutoffSpeedMeasure]
      rw [restrict_withDensity Ω.isOpen.measurableSet]
      rfl
    obtain ⟨lo, hlo, hlow⟩ : ∃ lo : ℝ, 0 < lo ∧
        ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), lo ≤ ρ x := by
      obtain ⟨lo, hlo, hlo'⟩ :=
        (closedCube z r hr).isCompact.exists_forall_le'
          hρcont.continuousOn (a := 0) (fun x _ => hρpos x)
      exact ⟨lo, hlo, hlo'⟩
    obtain ⟨hi, hhi⟩ := bddAbove_def.mp
      ((closedCube z r hr).isCompact.bddAbove_image hρcont.continuousOn)
    have hupper : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), ρ x ≤ hi := by
      intro x hx
      exact hhi (ρ x) ⟨x, hx, rfl⟩
    have hμle : μ ≤ ENNReal.ofReal hi • μ₀ := by
      rw [hμ]
      refine (withDensity_mono ?_).trans_eq (withDensity_const _)
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal (hupper x (centeredCube_subset_closedCube z hr hx))
    have hμ₀le : μ₀ ≤ ENNReal.ofReal (lo⁻¹) • μ := by
      calc
        μ₀ = μ₀.withDensity (fun _ => 1) := by
          exact (withDensity_one (μ := μ₀)).symm
        _ ≤ μ₀.withDensity (fun x => ENNReal.ofReal (lo⁻¹) * ENNReal.ofReal (ρ x)) := by
          apply withDensity_mono
          filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
          have hxlo := hlow x (centeredCube_subset_closedCube z hr hx)
          have hreal : (1 : ℝ) ≤ lo⁻¹ * ρ x := by
            calc
              (1 : ℝ) = lo⁻¹ * lo := by field_simp
              _ ≤ lo⁻¹ * ρ x := mul_le_mul_of_nonneg_left hxlo (inv_nonneg.mpr hlo.le)
          have hscalar : (1 : ENNReal) ≤ ENNReal.ofReal (lo⁻¹ * ρ x) := by
            simpa using ENNReal.ofReal_le_ofReal hreal
          simpa only [ENNReal.ofReal_mul (inv_nonneg.mpr hlo.le)] using hscalar
        _ = ENNReal.ofReal (lo⁻¹) • μ₀.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
          rw [show (fun x => ENNReal.ofReal (lo⁻¹) * ENNReal.ofReal (ρ x)) =
              (ENNReal.ofReal (lo⁻¹)) • (fun x => ENNReal.ofReal (ρ x)) by rfl]
          exact withDensity_smul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (lo⁻¹) • μ := by rw [hμ]
    have hμac : μ ≪ μ₀ := by
      rw [hμ]
      exact withDensity_absolutelyContinuous _ _
    have hμ₀ac : μ₀ ≪ μ := by
      rw [hμ]
      apply withDensity_absolutelyContinuous' hρmeas.aemeasurable
      filter_upwards with x
      exact ENNReal.ofReal_ne_zero_iff.mpr (hρpos x)
    let p : SpatialCoordinates d → ℝ := fun x => ρ x * g₀ x
    have hpmeas : AEStronglyMeasurable p μ := by
      have hρae : AEStronglyMeasurable ρ μ := hρcont.aestronglyMeasurable.mono_ac hμac
      simpa [p] using hρae.mul (Lp.memLp g₀).1
    have hpbound : ∀ᵐ x ∂μ, ‖p x‖ ≤ hi * ‖g₀ x‖ := by
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      have hxhi := hupper x (centeredCube_subset_closedCube z hr hx)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (hρpos x)]
      exact mul_le_mul_of_nonneg_right hxhi (abs_nonneg (g₀ x))
    have hpmeasLp : MemLp p 2 μ :=
      MemLp.of_le_mul (Lp.memLp g₀) hpmeas hpbound
    have hpmeasLp₀ : MemLp p 2 μ₀ :=
      MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hμ₀le hpmeasLp
    let F : DomainL2 Ω := hpmeasLp₀.toLp p
    have hFp : (F : SpatialCoordinates d → ℝ) =ᵐ[μ₀] p := hpmeasLp₀.coeFn_toLp
    let ĝ : SpatialCoordinates d → ℝ := g₀
    have hpair (v : killedSobolevGraph Ω) :
        (∫ x, ĝ x * (((v : SobolevData Ω)).1) x ∂μ) =
        (∫ x, F x *
          (((v : SobolevData Ω)).1) x ∂μ₀) := by
      have hdens := integral_withDensity_eq_integral_toReal_smul (μ := μ₀)
        hρmeas (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
          (fun x => ĝ x * (((v : SobolevData Ω)).1) x)
      have hdens' : (∫ x, ĝ x * (((v : SobolevData Ω)).1) x ∂μ) =
          ∫ x, (ρ x) * (ĝ x * (((v : SobolevData Ω)).1) x) ∂μ₀ := by
        rw [hμ]
        simpa only [ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using hdens
      rw [hdens']
      apply integral_congr_ae
      filter_upwards [hFp] with x hx
      change ρ x * (ĝ x * (((v : SobolevData Ω)).1) x) = _
      rw [show ĝ x = g₀ x by rfl, hx]
      simp only [p]
      ring
    refine ⟨F, ?_, ?_⟩
    · have hFpμ : (F : SpatialCoordinates d → ℝ) =ᵐ[μ] p := hμac.ae_eq hFp
      simpa [F, p, μ, ρ, Ω] using hFpμ
    · constructor
      · intro h
        intro v
        have hv := h v
        have hv' : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
            -(∫ x, ĝ x * (((v : SobolevData Ω)).1) x ∂μ) := by
          simpa [μ, Ω] using hv
        rw [hpair v] at hv'
        simpa [μ₀, Ω, F] using hv'
      · intro h
        intro v
        have hv := h v
        have hv' : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v =
            -(∫ x, (F : SpatialCoordinates d → ℝ) x *
              (((v : SobolevData Ω)).1) x ∂μ₀) := by
          simpa [μ₀, Ω] using hv
        rw [← hpair v] at hv'
        simpa [μ, Ω] using hv'
  have h_energy := aux_killed_energy_measure M H omega N z r hr
  exact ⟨h_density, h_generator, h_brownian, h_source_to_speed, h_speed_to_source, h_energy⟩

end Paper
