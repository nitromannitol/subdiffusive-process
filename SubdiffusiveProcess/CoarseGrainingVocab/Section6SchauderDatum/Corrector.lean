module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.MaxPrinciple
public import Homogenization.Sobolev.PotentialSolenoidalL2
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import Homogenization.Sobolev.Truncation.MatchedTrace
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.PDE.DirichletRHS
public import Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/ResidualCorrectorExistence.lean
-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/HarmonicReplacement.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/ResidualCorrectorExistence.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/HarmonicReplacement.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory
open Homogenization (Vec H1Function H10Function CoeffField MemH10 MemVectorL2 vecDot
  constantCoeffField scalarMatrix matVecMul IsEllipticFieldOn openCubeSet originCube
  IsOpenBoundedConvexDomain)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ### The identity coefficient field -/

/-- The identity coefficient field, as CoarseGraining's constant field at
`scalarMatrix 1`. -/
def unitCoeffField (d : ℕ) : CoeffField d := constantCoeffField (scalarMatrix (d := d) 1)

theorem matVecMul_unitCoeffField (x v : Vec d) :
    matVecMul (unitCoeffField d x) v = v := by
  show matVecMul (scalarMatrix (d := d) 1) v = v
  rw [Homogenization.matVecMul_scalarMatrix, one_smul]

theorem isEllipticFieldOn_unitCoeffField {V : Set (Vec d)} (hV : MeasurableSet V) :
    IsEllipticFieldOn 1 1 V (unitCoeffField d) :=
  Homogenization.isEllipticFieldOn_constantCoeffField hV
    (Homogenization.isEllipticMatrix_scalarMatrix one_pos)

/-! ### Splitting a forcing pairing -/

/-- The forcing pairing is additive in the force, in the form the affine shift
produces it (the combined field is given pointwise). -/
theorem integral_vecDot_add_left_split {U : Set (Vec d)} {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x + G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume) +
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume := by
  have hFint : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    Homogenization.integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    Homogenization.integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) +
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, Homogenization.vecDot_add_left]
  rw [hfun, integral_add hFint hGint]

/-! ### The Dirichlet problem on the window -/

/-- **The residual corrector exists.**

On any open bounded convex nonempty window `V` and for any `H¹(V)` datum `Φ`
there is a weakly harmonic `w` with `w - Φ ∈ H¹₀(V)`: the datum split's Dirichlet
problem for the residual corrector. -/
theorem exists_unitWeaklyHarmonicOn_of_datum [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (Φ : H1Function V) :
    ∃ w : H1Function V, IsUnitWeaklyHarmonicOn V w ∧
      MemH10 V (fun y => w.toFun y - Φ.toFun y) := by
  haveI : IsFiniteMeasure (Homogenization.volumeMeasureOn V) :=
    hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Φ.grad := Φ.grad_memVectorL2
  have hg : MemVectorL2 V (fun y => -Φ.grad y) := hgrad.neg
  have hrealize :
      Homogenization.PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    Homogenization.PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hV
  obtain ⟨rho, hrho⟩ :=
    Homogenization.exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := unitCoeffField d) (U := V) (g := fun y => -Φ.grad y) (lam := 1) (Lam := 1)
      hg hrealize hne (isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)
  have hrhomem : MemVectorL2 V rho.toH1Function.grad := rho.toH1Function.grad_memVectorL2
  refine ⟨Φ + rho.toH1Function, ?_, ⟨rho, ?_⟩⟩
  · intro φ
    have hsplit := integral_vecDot_add_left_split (U := V) hgrad hrhomem
      (H := (Φ + rho.toH1Function).grad)
      (fun x => by rw [Homogenization.H1Function.add_grad]) φ
    have hid := hrho φ
    have hcongr : ∫ x in V, vecDot (matVecMul (unitCoeffField d x)
          (rho.toH1Function.grad x)) (φ.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show vecDot (matVecMul (unitCoeffField d x) (rho.toH1Function.grad x))
            (φ.toH1Function.grad x) =
          vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x)
        rw [matVecMul_unitCoeffField])
    rw [hcongr] at hid
    have hneg : ∫ x in V, vecDot ((fun y => -Φ.grad y) x) (φ.toH1Function.grad x) ∂volume =
        -∫ x in V, vecDot (Φ.grad x) (φ.toH1Function.grad x) ∂volume := by
      have hfun : (fun x => vecDot ((fun y => -Φ.grad y) x) (φ.toH1Function.grad x)) =
          fun x => -vecDot (Φ.grad x) (φ.toH1Function.grad x) := by
        funext x
        show vecDot (-Φ.grad x) (φ.toH1Function.grad x) = _
        rw [Homogenization.vecDot_neg_left]
      rw [hfun, integral_neg]
    rw [hneg] at hid
    rw [hsplit, hid]
    ring
  · funext y
    show rho.toH1Function.toFun y = (Φ + rho.toH1Function).toFun y - Φ.toFun y
    rw [Homogenization.H1Function.add_toFun]
    show rho.toH1Function.toFun y = Φ.toFun y + rho.toH1Function.toFun y - Φ.toFun y
    ring

/-! ### The boundary bound from the datum -/

/-- A solution whose trace matches a datum globally bounded by `M` satisfies the
weak boundary bound at level `M`. -/
theorem hasBoundaryUpperBoundOn_of_datum_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {w Φ : H1Function V} {M : ℝ}
    (hdiff : MemH10 V (fun y => w.toFun y - Φ.toFun y)) (hΦ : ∀ y, Φ.toFun y ≤ M) :
    HasBoundaryUpperBoundOn V w M := by
  obtain ⟨ψ, hψ⟩ := Homogenization.memH10_max_sub_matched hV w Φ hdiff M
  obtain ⟨v, hvf, hvg⟩ := Homogenization.exists_h1_max_sub_const hV w M
  have hψf : ψ.toH1Function.toFun = fun y => max (w.toFun y - M) 0 := by
    rw [hψ]
    funext y
    rw [max_eq_right (by linarith only [hΦ y] : Φ.toFun y - M ≤ 0), sub_zero]
  refine ⟨ψ, hψf, ?_⟩
  have heq : ψ.toH1Function.toFun = v.toFun := by rw [hψf, hvf]
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hV.isOpen
    (u := ψ.toH1Function) (v := v)
    (Filter.Eventually.of_forall fun x => congrFun heq x)
  filter_upwards [hgrad, hvg] with y h1 h2
  rw [h1, h2]

/-! ### The globally clamped datum -/

private theorem clamp_bounds (t M : ℝ) (hM : 0 ≤ M) :
    t - max (t - M) 0 + max (-t - M) 0 ≤ M ∧
      -M ≤ t - max (t - M) 0 + max (-t - M) 0 := by
  rcases le_total t M with h1 | h1
  · rw [max_eq_right (by linarith only [h1] : t - M ≤ 0)]
    rcases le_total (-t - M) 0 with h2 | h2
    · rw [max_eq_right h2]
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
    · rw [max_eq_left h2]
      exact ⟨by linarith only [hM], by linarith only [hM]⟩
  · rw [max_eq_left (by linarith only [h1] : (0 : ℝ) ≤ t - M),
      max_eq_right (by linarith only [h1, hM] : -t - M ≤ 0)]
    exact ⟨by linarith only [hM], by linarith only [hM]⟩

private theorem clamp_eq (t M : ℝ) (h : |t| ≤ M) :
    t - max (t - M) 0 + max (-t - M) 0 = t := by
  rw [abs_le] at h
  rw [max_eq_right (by linarith only [h.2] : t - M ≤ 0),
    max_eq_right (by linarith only [h.1] : -t - M ≤ 0)]
  ring



theorem exists_h1_clamp {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (Φ : H1Function V) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Ψ : H1Function V, (∀ y, Ψ.toFun y ≤ M) ∧ (∀ y, -M ≤ Ψ.toFun y) ∧
      ∀ y, |Φ.toFun y| ≤ M → Ψ.toFun y = Φ.toFun y := by
  obtain ⟨v1, hv1f, _⟩ := Homogenization.exists_h1_max_sub_const hV Φ M
  obtain ⟨v2, hv2f, _⟩ := Homogenization.exists_h1_max_sub_const hV (-Φ) M
  have hval : ∀ y, (Φ - v1 + v2).toFun y =
      Φ.toFun y - max (Φ.toFun y - M) 0 + max (-Φ.toFun y - M) 0 := by
    intro y
    rw [Homogenization.H1Function.add_toFun, Homogenization.H1Function.sub_toFun]
    show Φ.toFun y - v1.toFun y + v2.toFun y = _
    rw [hv1f, hv2f, Homogenization.H1Function.neg_toFun]
  refine ⟨Φ - v1 + v2, fun y => ?_, fun y => ?_, fun y hy => ?_⟩
  · rw [hval y]
    exact (clamp_bounds (Φ.toFun y) M hM).1
  · rw [hval y]
    exact (clamp_bounds (Φ.toFun y) M hM).2
  · rw [hval y]
    exact clamp_eq (Φ.toFun y) M hy

/-! ### The packaged corrector -/

/-- **The residual corrector, packaged**: weakly harmonic, carrying the datum's
trace, and two-sidedly bounded on the boundary at the datum's level. -/
theorem exists_residualCorrector [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (Φ : H1Function V) {M : ℝ} (hupper : ∀ y, Φ.toFun y ≤ M)
    (hlower : ∀ y, -M ≤ Φ.toFun y) :
    ∃ w : H1Function V, IsUnitWeaklyHarmonicOn V w ∧
      MemH10 V (fun y => w.toFun y - Φ.toFun y) ∧
      HasBoundaryUpperBoundOn V w M ∧ HasBoundaryUpperBoundOn V (-w) M := by
  obtain ⟨w, hharm, hdiff⟩ := exists_unitWeaklyHarmonicOn_of_datum hV hne Φ
  refine ⟨w, hharm, hdiff, hasBoundaryUpperBoundOn_of_datum_le hV hdiff hupper, ?_⟩
  have hdiffneg : MemH10 V (fun y => (-w).toFun y - (-Φ).toFun y) := by
    have h := Homogenization.memH10_neg hdiff
    have hfun : (fun y => -(w.toFun y - Φ.toFun y)) =
        fun y => (-w).toFun y - (-Φ).toFun y := by
      funext y
      rw [Homogenization.H1Function.neg_toFun, Homogenization.H1Function.neg_toFun]
      ring
    rwa [hfun] at h
  refine hasBoundaryUpperBoundOn_of_datum_le hV hdiffneg fun y => ?_
  rw [Homogenization.H1Function.neg_toFun]
  show -Φ.toFun y ≤ M
  linarith only [hlower y]



theorem exists_residualCorrector_truncatedWindow [NeZero d] {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (Φ : H1Function (truncatedWindow x m k)) {M : ℝ}
    (hupper : ∀ y, Φ.toFun y ≤ M) (hlower : ∀ y, -M ≤ Φ.toFun y) :
    ∃ w : H1Function (truncatedWindow x m k),
      IsUnitWeaklyHarmonicOn (truncatedWindow x m k) w ∧
      MemH10 (truncatedWindow x m k) (fun y => w.toFun y - Φ.toFun y) ∧
      HasBoundaryUpperBoundOn (truncatedWindow x m k) w M ∧
      HasBoundaryUpperBoundOn (truncatedWindow x m k) (-w) M :=
  exists_residualCorrector (isOpenBoundedConvexDomain_truncatedWindow x m k)
    (truncatedWindow_nonempty k hx) Φ hupper hlower

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
