module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem prop_density_core_comparison
    (d : ℕ) (_hd : 2 ≤ d)
    (Hs : Type) [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
    (X : Type) [MeasurableSpace X]
    (C0 L : ℝ) (_hC0 : 1 ≤ C0) (_hL : 1 < L)
    (Cube Cellt : Type) [DecidableEq Cellt]
    (EE FF : Cube → DomainedEnergy Hs X)
    (cellsOf : Cube → Finset Cellt)
    (parentMass cellVol : Cellt → ℝ)
    (_hpm0 : ∀ q : Cellt, 0 ≤ parentMass q) (_hcv0 : ∀ q : Cellt, 0 ≤ cellVol q)
    (Fcell : Cube → Cellt → Hs → ℝ)
    (volQ : Cube → ℝ) (_hvolQ : ∀ c : Cube, 0 ≤ volQ c)
    (cconst : ℝ) (_hc : 0 < cconst)
    (Cg : ℝ) (hCg : 0 < Cg) (_hCgdep : Cg ≤ C0 ^ 3 * L ^ (d : ℕ))
    (a : ℝ) (ha : 0 < a)
    (hstopped : ∀ (c : Cube) (v : Hs), ∀ q ∈ cellsOf c,
      Fcell c q v ≤ Cg * a * (parentMass q + cconst * cellVol q))
    (hsum : ∀ (c : Cube) (v : Hs) (hv : v ∈ (EE c).dom),
      ∑ q ∈ cellsOf c, (parentMass q + cconst * cellVol q) ≤
        C0 * ((EE c).formAt v hv + cconst * volQ c))
    (hglue : ∀ (c : Cube) (v : Hs) (hv' : v ∈ (FF c).dom),
      (FF c).formAt v hv' ≤ ∑ q ∈ cellsOf c, Fcell c q v) :
    ∀ (c : Cube) (v : Hs) (hv : v ∈ (EE c).dom) (hv' : v ∈ (FF c).dom),
      (FF c).formAt v hv' ≤
        Cg * C0 * a * ((EE c).formAt v hv + cconst * volQ c) := by
  intro c v hv hv'
  have hCg0 : (0 : ℝ) ≤ Cg * a := by positivity
  have hstep : ∑ q ∈ cellsOf c, Fcell c q v ≤
      ∑ q ∈ cellsOf c, Cg * a * (parentMass q + cconst * cellVol q) :=
    Finset.sum_le_sum (fun q hq => hstopped c v q hq)
  have hpull : ∑ q ∈ cellsOf c, Cg * a * (parentMass q + cconst * cellVol q) =
      Cg * a * ∑ q ∈ cellsOf c, (parentMass q + cconst * cellVol q) := by
    rw [Finset.mul_sum]
  have hfin := hsum c v hv
  have : Cg * a * ∑ q ∈ cellsOf c, (parentMass q + cconst * cellVol q) ≤
      Cg * a * (C0 * ((EE c).formAt v hv + cconst * volQ c)) :=
    mul_le_mul_of_nonneg_left hfin hCg0
  calc (FF c).formAt v hv' ≤ ∑ q ∈ cellsOf c, Fcell c q v := hglue c v hv'
    _ ≤ Cg * a * ∑ q ∈ cellsOf c, (parentMass q + cconst * cellVol q) := by
        rw [← hpull]; exact hstep
    _ ≤ Cg * a * (C0 * ((EE c).formAt v hv + cconst * volQ c)) := this
    _ = Cg * C0 * a * ((EE c).formAt v hv + cconst * volQ c) := by ring

end SubdiffusiveProcess.Paper
