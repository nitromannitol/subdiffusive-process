module

public import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- Eventual retained-grid bounds, with their own threshold. -/
def aux_lem_as_coarse_record_composition_ShallowPart {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho theta : ℝ) : Prop :=
  ∃ (Nsh : ℕ) (K : ℝ), 0 ≤ K ∧
    ∀ N, Nsh ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ))

/-- Eventual deep-grid bounds and their rate, with an independent threshold. -/
def aux_lem_as_coarse_record_composition_DeepPart {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho theta xi : ℝ) (m : ℕ) : Prop :=
  ∃ (Ndp : ℕ) (Kdeep : ℕ → ℝ), (∀ N, 0 ≤ Kdeep N) ∧
    (∀ N, Ndp ≤ N → Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ))) ∧
    (∀ N, Ndp ≤ N → ∀ k : ℕ, theta * N < (k : ℝ) → k + m ≤ N →
      ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)))

/-- Eventual scalar envelope and its subwavelength rate. -/
def aux_lem_as_coarse_record_composition_ScalarPart {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : ℝ) : Prop :=
  ∃ (Nsc : ℕ) (Ksub : ℝ) (lo hi : ℕ → ℝ),
    (∀ N, 0 < lo N) ∧ (∀ N, lo N ≤ hi N) ∧
    (∀ N, Nsc ≤ N → (3 : ℝ) ^ (-(s * (N : ℝ))) * (hi N + (lo N)⁻¹) ≤ Ksub) ∧
    (∀ N, Nsc ≤ N → ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo N ≤ cutoffCoefficient M H om N y ∧ cutoffCoefficient M H om N y ≤ hi N)

/-- Take the maximum of the three independent eventuality thresholds.  This is the exact
record required by the first-clause assembly, with the paper's single `theta` shared by the
retained and deep estimates. -/
theorem aux_lem_as_coarse_record_composition_inputs_of_parts {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s rho theta xi : ℝ) (m : ℕ)
    (hsh : aux_lem_as_coarse_record_composition_ShallowPart Jc M H om z r hr rho theta)
    (hdp : aux_lem_as_coarse_record_composition_DeepPart Jc M H om z r hr rho theta xi m)
    (hsc : aux_lem_as_coarse_record_composition_ScalarPart M H om z r hr s) :
    aux_lem_as_coarse_ms_Inputs Jc M H om z r hr s rho theta xi m := by
  obtain ⟨Nsh, K, hK, hsh⟩ := hsh
  obtain ⟨Ndp, Kdeep, hKd, hKdN, hdp⟩ := hdp
  obtain ⟨Nsc, Ksub, lo, hi, hlo, hle, hSN, hext⟩ := hsc
  refine ⟨max Nsh (max Ndp Nsc), K, Ksub, Kdeep, lo, hi, hK, hKd, hlo,
    hle, ?_, ?_, ?_, ?_, ?_⟩
  · intro N hN
    exact hKdN N ((le_max_left Ndp Nsc).trans ((le_max_right Nsh _).trans hN))
  · intro N hN
    exact hSN N ((le_max_right Ndp Nsc).trans ((le_max_right Nsh _).trans hN))
  · intro N hN
    exact hsh N ((le_max_left _ _).trans hN)
  · intro N hN
    exact hdp N ((le_max_left Ndp Nsc).trans ((le_max_right Nsh _).trans hN))
  · intro N hN
    exact hext N ((le_max_right Ndp Nsc).trans ((le_max_right Nsh _).trans hN))

/-- Direct interface for the first clause of `lem_as_coarse`: each infrared convention
provides three independently eventual inputs, and the assembled bound is uniform in
the convention, the cutoff, and both requested exponents. -/
theorem lem_as_coarse_record_composition {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hxi0 : 0 ≤ xi)
    (hxi : xi < (s - rho) * theta) (m : ℕ)
    (hsh : ∀ b : Bool, aux_lem_as_coarse_record_composition_ShallowPart Jc M
      (if b then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om z r hr rho theta)
    (hdp : ∀ b : Bool, aux_lem_as_coarse_record_composition_DeepPart Jc M
      (if b then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om z r hr rho theta xi m)
    (hsc : ∀ b : Bool, aux_lem_as_coarse_record_composition_ScalarPart M
      (if b then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om z r hr s) :
    ∃ K : ℝ, 0 < K ∧ ∀ withIR : Bool,
      let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
        if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ));
      ∀ (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) → ∀ N : ℕ,
        Jc.Lam z r hr (cutoffPositiveCoefficient M Hc om N z hr) z r s qe +
          (Jc.lam z r hr (cutoffPositiveCoefficient M Hc om N z hr) z r s qe)⁻¹ ≤ K := by
  apply lem_as_coarse_first_clause_assembly hd Jc M Hir om z r hr s hs rho theta xi
    hrhos htheta htheta1 hxi0 hxi m
  intro b
  exact aux_lem_as_coarse_record_composition_inputs_of_parts Jc M _ om z r hr s rho theta xi m (hsh b) (hdp b) (hsc b)


end SubdiffusiveProcess.Paper
