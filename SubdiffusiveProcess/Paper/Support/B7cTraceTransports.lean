module

public import SubdiffusiveProcess.Paper.Support.B7cGluingStatement

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

def aux_mfd_prop_gluing_bank
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (Cext beta : ℝ)
    (zz : SpatialCoordinates d) (rr : ℝ) (hrr : 0 < rr) : Prop :=
    let Uq := fun n => E.Lam zz rr hrr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (w n) (cutoff n) zz hrr)
      zz rr ((beta - 1 / 2) / 4) 2
    BddAbove (Set.range Uq) ∧ 0 ≤ sSup (Set.range Uq) ∧
    (∀ n, 0 ≤ Uq n ∧ Uq n ≤ sSup (Set.range Uq)) ∧
    ∀ n, ∀ e : H1Function (centeredCube zz rr hrr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube zz rr hrr : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta zz rr e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (w n) (cutoff n))
        (centeredCube zz rr hrr : Set (SpatialCoordinates d)) e ≤
      Cext * Uq n * rr ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta zz rr e.toFun ^ 2

theorem aux_mfd_prop_gluing_bank_congr
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (Cext beta : ℝ)
    (z0 z1 : SpatialCoordinates d) (r0 r1 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hz : z0 = z1) (hrad : r0 = r1)
    (h : aux_mfd_prop_gluing_bank M H w cutoff E Cext beta z0 r0 hr0) :
    aux_mfd_prop_gluing_bank M H w cutoff E Cext beta z1 r1 hr1 := by
  subst z0
  subst r0
  exact h

theorem aux_mfd_prop_gluing_finite_bound_congr {d : ℕ}
    (Q0 Q1 : Set (SpatialCoordinates d)) (hQ : Q0 = Q1)
    (A : ℕ → SpatialCoordinates d → ℝ) (z : SpatialCoordinates d) (r beta C : ℝ)
    (U : ℕ → ℝ)
    (h : ∀ n, ∀ e : H1Function Q0, ContinuousOn e.toFun (closure Q0) →
      IsCellBoundaryClass beta z r e.toFun → cellDirichletInfimum (A n) Q0 e ≤
        C * U n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2) :
    ∀ n, ∀ e : H1Function Q1, ContinuousOn e.toFun (closure Q1) →
      IsCellBoundaryClass beta z r e.toFun → cellDirichletInfimum (A n) Q1 e ≤
        C * U n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2 := by
  subst Q0
  exact h

theorem aux_mfd_prop_gluing_trace_transport {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (zq zQ : SpatialCoordinates d) (rq RQ : ℝ) (hrq : 0 < rq) (hRQ : 0 < RQ)
    (h3r : 0 < 3 * rq) (hz : zQ = zq) (hrad : RQ = 3 * rq)
    (S0 : ResponseSpace (centeredCube zQ RQ hRQ))
    (G0 : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (L0 : aux_limit_form_package_limit_side d hd zQ RQ hRQ S0 G0
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (w n) (cutoff n) zQ hRQ))
    (hS : S0.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (Ein : _root_.SubdiffusiveProcess.Paper.in_J d) (C beta alpha : ℝ) (b : SpatialCoordinates d → ℝ)
    (hp : ∀ (S1 : ResponseSpace (centeredCube zq (3 * rq) h3r))
      (G1 : DomainL2 (centeredCube zq (3 * rq) h3r) →L[ℝ] DomainL2 (centeredCube zq (3 * rq) h3r))
      (L1 : aux_limit_form_package_limit_side d hd zq (3 * rq) h3r S1 G1
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (w n) (cutoff n) zq h3r)),
      S1.space = killedSobolevGraph (centeredCube zq (3 * rq) h3r) →
      ∃ lam U Uc, aux_mfd_prop_gluing_trace_package d hd M H w cutoff
        zq rq hrq zq (3 * rq) h3r rfl rfl S1 G1 L1 Ein C beta alpha b lam U Uc) :
    ∃ lam U Uc, aux_mfd_prop_gluing_trace_package d hd M H w cutoff
      zq rq hrq zQ RQ hRQ hz hrad S0 G0 L0 Ein C beta alpha b lam U Uc := by
  subst zQ
  subst RQ
  exact hp S0 G0 L0 hS

end SubdiffusiveProcess.Paper
