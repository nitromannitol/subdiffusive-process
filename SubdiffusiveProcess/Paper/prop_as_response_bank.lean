module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.neumann_load_pointwise
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.prop_as_dirichlet
public import SubdiffusiveProcess.Paper.prop_as_response_bank_cauchy
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.working_levels_ratio
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_completion
public import SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_tail
public import SubdiffusiveProcess.Paper.prop_as_response_bank_borel_cantelli

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The two Poincare witnesses required by the current response bank implementation. -/
theorem aux_source_response_bank_cube_poincare
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Q) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖) := by
  have : NeZero d := ⟨by omega⟩
  let Q := centeredCube z r hr
  have hQ : Homogenization.IsOpenBoundedConvexDomain
      (Q : Set (SpatialCoordinates d)) := by
    refine ⟨Q.isOpen, ?_, ?_⟩
    · simpa [Q] using
        (Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded z hr))
    · simpa [Q, centeredCube] using (convex_ball z (r / 2))
  exact exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Q hQ

/-- Smooth source data have a weak Sobolev representative on each cube. -/
theorem aux_source_response_bank_smooth_weak_witness
    {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] phi := by
  let Q := centeredCube z r hr
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (Q : Set (SpatialCoordinates d)) :=
    isOpenBoundedConvexDomain_centeredCube z hr
  let phiH : H1Function (Q : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hgeom
      (hphi.of_le (by simp))
  refine ⟨⟨sobolevDataOfH1 phiH, sobolevDataOfH1_mem_weak phiH⟩, ?_⟩
  simpa only [phiH, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain] using
    (sobolevDataOfH1_fst_coeFn phiH)

/-- Package the source-level inputs into exactly the four extra witnesses
    accepted by the current response-bank implementation. -/
theorem aux_source_response_bank_family_witnesses
    {d : ℕ} (hd : 2 ≤ d) {I : Type*}
    (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (phi : I → SpatialCoordinates d → ℝ)
    (hphi : ∀ i, ContDiff ℝ ∞ (phi i)) :
    ∃ (_hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖)
      (_hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖)
      (b : ∀ i, weakSobolevGraph
          (centeredCube (z i) (r i) (hr i))),
      ∀ i, ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
          SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube (z i) (r i) (hr i) :
              Set (SpatialCoordinates d))] phi i := by
  let hPP i := aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)
  let b i := Classical.choose
    (aux_source_response_bank_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
  refine ⟨(fun i => (hPP i).1), (fun i => (hPP i).2), b, ?_⟩
  intro i
  exact Classical.choose_spec
    (aux_source_response_bank_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))


/-- Assemble the completion, limit-relative tail, and Borel--Cantelli
interfaces for the eight response coordinates over a countable family. -/
theorem aux_response_bank_limit_assembly
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable I]
    (Z : I → Bool → Fin 4 → ℕ → Ω → ℝ)
    (hZ : ∀ i infrared branch N, Measurable (Z i infrared branch N))
    (hZnonneg : ∀ i infrared branch N (w : Ω), 0 ≤ Z i infrared branch N w)
    (hCauchy : ∀ i infrared branch, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {w | a < |Z i infrared branch M w - Z i infrared branch M' w|} ≤
          ENNReal.ofReal b)
    (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ i infrared branch, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
            P {w | Cgeom * eps * Z i infrared branch N w +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |Z i infrared branch N w - Z i infrared branch M w|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) :
    ∃ L : I → Bool → Fin 4 → Ω → ℝ,
      (∀ i infrared branch, Measurable (L i infrared branch)) ∧
      (∀ i infrared branch (w : Ω), 0 ≤ L i infrared branch w) ∧
      (∀ i infrared branch,
        TendstoInMeasure P (Z i infrared branch) atTop (L i infrared branch)) ∧
      (∀ i infrared branch eps, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ N : ℕ, Ne ≤ N →
            P {w | eps * L i infrared branch w +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |Z i infrared branch N w - L i infrared branch w|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
      (∀ i infrared branch eps, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ N : ℕ, Ne ≤ N →
            P {w | Cgeom * eps * L i infrared branch w +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |Z i infrared branch N w - L i infrared branch w|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
      (∀ᵐ w ∂P, ∀ i infrared branch,
        Tendsto (fun N => Z i infrared branch N w) atTop
          (nhds (L i infrared branch w))) := by
  let K := I × Bool × Fin 4
  let W : K → ℕ → Ω → ℝ := fun k N => Z k.1 k.2.1 k.2.2 N
  have hW : ∀ k N, Measurable (W k N) := by
    rintro ⟨i, infrared, branch⟩ N
    exact hZ i infrared branch N
  have hWnonneg : ∀ k N w, 0 ≤ W k N w := by
    rintro ⟨i, infrared, branch⟩ N w
    exact hZnonneg i infrared branch N w
  have hWCauchy : ∀ k : K, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {w | a < |W k M w - W k M' w|} ≤ ENNReal.ofReal b := by
    rintro ⟨i, infrared, branch⟩ a b ha hb
    exact hCauchy i infrared branch a b ha hb
  have hWpair : ∀ k : K, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
            P {w | Cgeom * eps * W k N w +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) < |W k N w - W k M w|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
    rintro ⟨i, infrared, branch⟩ eps heps
    simpa [W] using hpair i infrared branch eps heps
  obtain ⟨L, hL, hLnonneg, hconv⟩ :=
    prop_as_response_bank_limit_completion P W hW hWnonneg hWCauchy
  have htail : ∀ k : K, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          P {w | eps * L k w + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |W k N w - L k w|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
    intro k eps heps
    have heps' : 0 < eps / Cgeom := div_pos heps hCgeom
    obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ :=
      prop_as_response_bank_limit_tail P W L hW hL hWnonneg hLnonneg
        Cgeom hCgeom hWpair hconv k (eps / Cgeom) heps'
    refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
    intro N hN
    have := hbound N hN
    have hfactor : Cgeom * (eps / Cgeom) = eps := by field_simp
    simpa [hfactor] using this
  have hscaled : ∀ k : K, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          P {w | Cgeom * eps * L k w + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |W k N w - L k w|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
    intro k eps heps
    exact prop_as_response_bank_limit_tail P W L hW hL hWnonneg hLnonneg
      Cgeom hCgeom hWpair hconv k eps heps
  have hbc := prop_as_response_bank_borel_cantelli P W L hW hL htail
  refine ⟨fun i infrared branch => L (i, infrared, branch), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i infrared branch
    exact hL (i, infrared, branch)
  · intro i infrared branch w
    exact hLnonneg (i, infrared, branch) w
  · intro i infrared branch
    exact hconv (i, infrared, branch)
  · intro i infrared branch eps heps
    obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ := htail (i, infrared, branch) eps heps
    refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
    intro N hN
    simpa [W] using hbound N hN
  · intro i infrared branch eps heps
    obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ := hscaled (i, infrared, branch) eps heps
    refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
    intro N hN
    simpa [W] using hbound N hN
  · filter_upwards [hbc] with w hw
    intro i infrared branch
    exact hw (i, infrared, branch)

/-- The exact eight finite-cutoff response coordinates are measurable. -/
theorem aux_actual_response_bank_rsp_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    {I : Type*} (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (p : I → Fin d → ℝ) :
    let SD : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
          cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) a (b i)
        | 1 => inverseResponse (SD i) a
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) a
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) a (p i)
    ∀ i infrared branch N, Measurable (Rsp i infrared branch N) := by
  intro SD SN Rsp i infrared branch N
  have hm := aux_prop_as_response_bank_cauchy_measurable_branches
    model H HI.1 (z i) (r i) (hr i) (hP i) (hP0 i)
    (b i) (fD i) (fN i) (p i) infrared N
  dsimp only at hm
  have hbranch : branch.val = 0 ∨ branch.val = 1 ∨ branch.val = 2 ∨ branch.val = 3 := by
    omega
  rcases hbranch with h | h | h | h
  · simpa only [Rsp, SD, SN, h] using hm.1
  · simpa only [Rsp, SD, SN, h] using hm.2.1
  · simpa only [Rsp, SD, SN, h] using hm.2.2.1
  · simpa only [Rsp, SD, SN, h] using hm.2.2.2

theorem aux_actual_response_bank_rsp_nonneg
    {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {I : Type*} (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (p : I → Fin d → ℝ) :
    let SD : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
          cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) a (b i)
        | 1 => inverseResponse (SD i) a
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) a
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) a (p i)
    ∀ i infrared branch N omega, 0 ≤ Rsp i infrared branch N omega := by
  intro SD SN Rsp i infrared branch N omega
  rcases branch with ⟨_ | _ | _ | _ | k, hi⟩
  · exact dirichletResponse_nonneg _ _ _
  · exact inverseResponse_nonneg _ _ _
  · exact inverseResponse_nonneg _ _ _
  · exact inverseResponse_nonneg _ _ _
  · omega

/-- The relative-tail event has the same probability after each fixed
measure-preserving shift. No simultaneous event over all shifts is asserted. -/
theorem aux_response_bank_shift_tail_event
    {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Shift : T → Ω → Ω)
    (hShift : ∀ w, Measurable (Shift w))
    (hLaw : ∀ w, Measure.map (Shift w) P = P)
    (Z L : Ω → ℝ) (hZ : Measurable Z) (hL : Measurable L)
    (a b : ℝ) (w : T) :
    P {omega | a * L (Shift w omega) + b <
      |Z (Shift w omega) - L (Shift w omega)|} =
    P {omega | a * L omega + b < |Z omega - L omega|} := by
  let E : Set Ω := {omega | a * L omega + b < |Z omega - L omega|}
  have hE : MeasurableSet E := by
    have hAbs : Measurable (fun omega => |Z omega - L omega|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using! (hZ.sub hL).norm
    exact measurableSet_lt ((measurable_const.mul hL).add measurable_const) hAbs
  have hpre : {omega | a * L (Shift w omega) + b <
      |Z (Shift w omega) - L (Shift w omega)|} = (Shift w) ⁻¹' E := by
    rfl
  rw [hpre, ← Measure.map_apply (hShift w) hE, hLaw w]

/-- The reanchored whole-field translation in the response-bank statement. -/
def aux_responseBankShift {d : ℕ} (w : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j : ℤ =>
    (omega j).comp
      (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_measurable_responseBankShift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (w : SpatialCoordinates d) :
    Measurable (aux_responseBankShift w) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d)) := by
    fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply j)

/-- The exact eight response coordinates retain their relative-tail event
probabilities under each deterministic reanchored spatial shift. -/
theorem aux_response_bank_stationary_tail_transfer
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {I : Type*}
    (Z : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ)
    (L : I → Bool → Fin 4 → BilateralField d → ℝ)
    (hZ : ∀ i infrared branch N, Measurable (Z i infrared branch N))
    (hL : ∀ i infrared branch, Measurable (L i infrared branch))
    (a b : ℝ) (i : I) (N : ℕ) (infrared : Bool) (branch : Fin 4)
    (w : SpatialCoordinates d) :
    (chaosSampleLaw model).toMeasure
        {omega | a * L i infrared branch (aux_responseBankShift w omega) + b <
          |Z i infrared branch N (aux_responseBankShift w omega) -
            L i infrared branch (aux_responseBankShift w omega)|} =
    (chaosSampleLaw model).toMeasure
        {omega | a * L i infrared branch omega + b <
          |Z i infrared branch N omega - L i infrared branch omega|} := by
  exact aux_response_bank_shift_tail_event (chaosSampleLaw model).toMeasure
    aux_responseBankShift aux_measurable_responseBankShift
    (by
      intro w'
      simpa only [aux_responseBankShift] using!
        (prop_as_response_bank_shift_invariance d model w'))
    (Z i infrared branch N) (L i infrared branch)
    (hZ i infrared branch N) (hL i infrared branch) a b w

/-- A single unshifted tail estimate transfers to every deterministic shift
with precisely the same constants and cutoff. -/
theorem aux_response_bank_shifted_tail_of_unshifted
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {I : Type*}
    (Z : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ)
    (L : I → Bool → Fin 4 → BilateralField d → ℝ)
    (hZ : ∀ i infrared branch N, Measurable (Z i infrared branch N))
    (hL : ∀ i infrared branch, Measurable (L i infrared branch))
    (a b : ℝ) (rhs : ℝ≥0∞) (i : I) (N : ℕ)
    (hunshifted : ∀ infrared branch,
      (chaosSampleLaw model).toMeasure
        {omega | a * L i infrared branch omega + b <
          |Z i infrared branch N omega - L i infrared branch omega|} ≤ rhs) :
    ∀ w : SpatialCoordinates d, ∀ infrared branch,
      (chaosSampleLaw model).toMeasure
        {omega | a * L i infrared branch (aux_responseBankShift w omega) + b <
          |Z i infrared branch N (aux_responseBankShift w omega) -
            L i infrared branch (aux_responseBankShift w omega)|} ≤ rhs := by
  intro w infrared branch
  rw [aux_response_bank_stationary_tail_transfer d model Z L hZ hL a b i N
    infrared branch w]
  exact hunshifted infrared branch

/-- Merge two positive geometric-error envelopes at one slower rate. -/
theorem aux_response_bank_two_rate_uniform
    (Ce1 Ce2 ce1 ce2 : ℝ)
    (hCe1 : 0 < Ce1) (hCe2 : 0 < Ce2)
    (hce1 : 0 < ce1) (hce2 : 0 < ce2) :
    ∃ Ce ce : ℝ, 0 < Ce ∧ 0 < ce ∧
      ∀ N : ℕ,
        Ce1 * (3 : ℝ) ^ (-(ce1 * (N : ℝ))) ≤
          Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) ∧
        Ce2 * (3 : ℝ) ^ (-(ce2 * (N : ℝ))) ≤
          Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) := by
  refine ⟨Ce1 + Ce2, min ce1 ce2, add_pos hCe1 hCe2, lt_min hce1 hce2, ?_⟩
  intro N
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hbase : (1 : ℝ) ≤ 3 := by norm_num
  have hce_le1 : min ce1 ce2 ≤ ce1 := min_le_left _ _
  have hce_le2 : min ce1 ce2 ≤ ce2 := min_le_right _ _
  have hmul1 : (min ce1 ce2) * (N : ℝ) ≤ ce1 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hce_le1 hN
  have hmul2 : (min ce1 ce2) * (N : ℝ) ≤ ce2 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hce_le2 hN
  have hexp1 : -(ce1 * (N : ℝ)) ≤ -((min ce1 ce2) * (N : ℝ)) := by linarith
  have hexp2 : -(ce2 * (N : ℝ)) ≤ -((min ce1 ce2) * (N : ℝ)) := by linarith
  have hpow1 : (3 : ℝ) ^ (-(ce1 * (N : ℝ))) ≤
      (3 : ℝ) ^ (-((min ce1 ce2) * (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp1
  have hpow2 : (3 : ℝ) ^ (-(ce2 * (N : ℝ))) ≤
      (3 : ℝ) ^ (-((min ce1 ce2) * (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp2
  have hnn1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(ce1 * (N : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hnn2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(ce2 * (N : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hCe_nonneg : (0 : ℝ) ≤ Ce1 + Ce2 := by positivity
  constructor
  · calc Ce1 * (3 : ℝ) ^ (-(ce1 * (N : ℝ)))
        ≤ (Ce1 + Ce2) * (3 : ℝ) ^ (-(ce1 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn1
      _ ≤ (Ce1 + Ce2) * (3 : ℝ) ^ (-((min ce1 ce2) * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hpow1 hCe_nonneg
  · calc Ce2 * (3 : ℝ) ^ (-(ce2 * (N : ℝ)))
        ≤ (Ce1 + Ce2) * (3 : ℝ) ^ (-(ce2 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn2
      _ ≤ (Ce1 + Ce2) * (3 : ℝ) ^ (-((min ce1 ce2) * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hpow2 hCe_nonneg

/-- Uniformize finitely many geometric tails.  The common prefactor is the
sum of the individual prefactors, the common rate is the reciprocal of the
sum of reciprocal rates, and the common threshold is the sum of thresholds.
The event inclusion and measure monotonicity are proved here. -/
theorem aux_response_bank_finite_geometric_tail_uniform
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [Nonempty κ]
    (P : Measure Ω) (X : κ → ℕ → Ω → ℝ) (L : κ → Ω → ℝ) (a : ℝ)
    (hbranch : ∀ k : κ, ∃ C c : ℝ, ∃ N₀ : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ N : ℕ, N₀ ≤ N →
        P {w | a * L k w + C * (3 : ℝ) ^ (-(c * (N : ℝ))) <
          |X k N w - L k w|} ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (N : ℝ))))) :
    ∃ C c : ℝ, ∃ N₀ : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ k : κ, ∀ N : ℕ, N₀ ≤ N →
        P {w | a * L k w + C * (3 : ℝ) ^ (-(c * (N : ℝ))) <
          |X k N w - L k w|} ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (N : ℝ)))) := by
  classical
  choose C₀ c₀ N₀ hC₀ hc₀ htail using hbranch
  let C : ℝ := ∑ k : κ, C₀ k
  let R : ℝ := ∑ k : κ, (c₀ k)⁻¹
  let c : ℝ := R⁻¹
  let N : ℕ := ∑ k : κ, N₀ k
  have hκ : (Finset.univ : Finset κ).Nonempty := Finset.univ_nonempty
  have hCpos : 0 < C := by
    dsimp [C]
    exact Finset.sum_pos (fun k _ => hC₀ k) hκ
  have hRpos : 0 < R := by
    dsimp [R]
    apply Finset.sum_pos
    · intro k _
      exact inv_pos.mpr (hc₀ k)
    · exact hκ
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr hRpos
  have hCbound (k : κ) : C₀ k ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun j _ => le_of_lt (hC₀ j)) (Finset.mem_univ k)
  have hRbound (k : κ) : (c₀ k)⁻¹ ≤ R := by
    dsimp [R]
    exact Finset.single_le_sum
      (fun j _ => le_of_lt (inv_pos.mpr (hc₀ j))) (Finset.mem_univ k)
  have hcbound (k : κ) : c ≤ c₀ k := by
    dsimp [c]
    have hR_inv : R⁻¹ ≤ ((c₀ k)⁻¹)⁻¹ :=
      (inv_le_inv₀ hRpos (inv_pos.mpr (hc₀ k))).2 (hRbound k)
    simpa [inv_inv] using hR_inv
  have hNbound (k : κ) : N₀ k ≤ N := by
    dsimp [N]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨C, c, N, hCpos, hcpos, ?_⟩
  intro k n hn
  have hn₀ : N₀ k ≤ n := le_trans (hNbound k) hn
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow : (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) ≤
      (3 : ℝ) ^ (-(c * (n : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    have hnreal : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmul := mul_le_mul_of_nonneg_right (hcbound k) hnreal
    linarith
  have henv : C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) ≤
      C * (3 : ℝ) ^ (-(c * (n : ℝ))) := by
    calc
      C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) ≤
          C * (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right (hCbound k) hbase
      _ ≤ C * (3 : ℝ) ^ (-(c * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
  let A : Set Ω := {w | a * L k w + C * (3 : ℝ) ^ (-(c * (n : ℝ))) <
    |X k n w - L k w|}
  let B : Set Ω := {w | a * L k w + C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) <
    |X k n w - L k w|}
  have hsub : A ⊆ B := by
    intro w hw
    change a * L k w + C * (3 : ℝ) ^ (-(c * (n : ℝ))) <
      |X k n w - L k w| at hw
    change a * L k w + C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ))) <
      |X k n w - L k w|
    linarith
  have hmeas : P A ≤ P B := measure_mono hsub
  have hrhs : ENNReal.ofReal
      (C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ)))) ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (n : ℝ)))) :=
    ENNReal.ofReal_mono henv
  have htail' := htail k n hn₀
  calc
    P A ≤ P B := hmeas
    _ ≤ ENNReal.ofReal
        (C₀ k * (3 : ℝ) ^ (-(c₀ k * (n : ℝ)))) := by
          simpa [B] using htail'
    _ ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (n : ℝ)))) := hrhs

/-- Eight-coordinate form used by the response bank. -/
theorem aux_response_bank_eight_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Bool → Fin 4 → ℕ → Ω → ℝ)
    (L : Bool → Fin 4 → Ω → ℝ) (a : ℝ)
    (hbranch : ∀ infrared branch, ∃ C c : ℝ, ∃ N₀ : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ N : ℕ, N₀ ≤ N →
        P {w | a * L infrared branch w + C * (3 : ℝ) ^ (-(c * (N : ℝ))) <
          |Z infrared branch N w - L infrared branch w|} ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (N : ℝ))))) :
    ∃ C c : ℝ, ∃ N₀ : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ infrared : Bool, ∀ branch : Fin 4, ∀ N : ℕ, N₀ ≤ N →
        P {w | a * L infrared branch w + C * (3 : ℝ) ^ (-(c * (N : ℝ))) <
          |Z infrared branch N w - L infrared branch w|} ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (N : ℝ)))) := by
  let X : (Bool × Fin 4) → ℕ → Ω → ℝ := fun b N w => Z b.1 b.2 N w
  let L' : (Bool × Fin 4) → Ω → ℝ := fun b w => L b.1 b.2 w
  have hbranch' : ∀ b : Bool × Fin 4, ∃ C c : ℝ, ∃ N₀ : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ N : ℕ, N₀ ≤ N →
        P {w | a * L' b w + C * (3 : ℝ) ^ (-(c * (N : ℝ))) <
          |X b N w - L' b w|} ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(c * (N : ℝ)))) := by
    rintro ⟨infrared, branch⟩
    simpa [X, L'] using hbranch infrared branch
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ :=
    aux_response_bank_finite_geometric_tail_uniform P X L' a hbranch'
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro infrared branch N hN
  simpa [X, L'] using hbound (infrared, branch) N hN

/-- The first three actual response-bank clauses, conditional on the exact
per-branch Cauchy conclusion supplied by `prop_as_response_bank_cauchy`. -/
theorem aux_actual_response_bank_conditional_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    {I : Type*} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (p : I → Fin d → ℝ) :
    let SD : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
          cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) a (b i)
        | 1 => inverseResponse (SD i) a
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) a
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) a (p i)
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    (∀ i infrared branch, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {omega | a < |Rsp i infrared branch M omega -
          Rsp i infrared branch M' omega|} ≤ ENNReal.ofReal b) →
    ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
      (∀ i infrared branch, Measurable (Rlim i infrared branch)) ∧
      (∀ i infrared branch omega, 0 ≤ Rlim i infrared branch omega) ∧
      (∀ i infrared branch,
        TendstoInMeasure P (Rsp i infrared branch) atTop
          (Rlim i infrared branch)) := by
  intro SD SN Rsp P hCauchy
  have hZ := aux_actual_response_bank_rsp_measurable model H HI z r hr hP hP0 b fD fN p
  have hZnonneg := aux_actual_response_bank_rsp_nonneg model H z r hr hP hP0 b fD fN p
  obtain ⟨L, hLm, hLn, hLt⟩ :=
    prop_as_response_bank_limit_completion P
      (fun k : I × Bool × Fin 4 => Rsp k.1 k.2.1 k.2.2)
      (by rintro ⟨i, infrared, branch⟩ N; exact hZ i infrared branch N)
      (by rintro ⟨i, infrared, branch⟩ N omega;
          exact hZnonneg i infrared branch N omega)
      (by
        rintro ⟨i, infrared, branch⟩ a probability ha hb
        exact hCauchy i infrared branch a probability ha hb)
  exact ⟨fun i infrared branch => L (i, infrared, branch),
    (by intro i infrared branch; exact hLm (i, infrared, branch)),
    (by intro i infrared branch omega; exact hLn (i, infrared, branch) omega),
    (by intro i infrared branch; exact hLt (i, infrared, branch))⟩


/-- Convert the single-cube response Cauchy result to the exact
family-indexed Cauchy input needed above. The parameter `Rm` is explicit. -/
theorem aux_actual_response_bank_cauchy_family
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (_Pc : in_poincare d hd Jc) (_Xc : in_extension d hd Jc)
    (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    {I : Type*} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (phi : I → SpatialCoordinates d → ℝ)
    (hphi : ∀ i, ContDiff ℝ ∞ (phi i))
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (hb : ∀ i, ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d))] phi i)
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (KD KN : I → ℝ)
    (hKD : ∀ i, 0 ≤ KD i) (hKN : ∀ i, 0 ≤ KN i)
    (hfD : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i)
    (hfN : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i)
    (hfNmean : ∀ i, (∫ x in (centeredCube (z i) (r i) (hr i) :
      Set (SpatialCoordinates d)),
      (fN i : SpatialCoordinates d → ℝ) x) = 0)
    (p : I → Fin d → ℝ)
    (delta0 Cgeom : ℝ)
    (hresp : ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      let hP := (aux_prop_as_response_bank_cube_poincare hd z r hr).1
      let hP0 := (aux_prop_as_response_bank_cube_poincare hd z r hr).2
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a := cutoffPositiveCoefficient model Hused omega N z hr
          match branch.val with
          | 0 => dirichletResponse SD a b
          | 1 => inverseResponse SD a
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN a
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 a p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ infrared branch N, ∀ᵐ omega ∂P, 0 ≤ Rsp infrared branch N omega) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ infrared branch,
                  P {omega | |Rsp infrared branch N omega -
                    Rsp infrared branch M omega| >
                    Cgeom * eps * Rsp infrared branch N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (branch : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega | tolerance < |Rsp infrared branch M omega -
            Rsp infrared branch M' omega|} ≤
            ENNReal.ofReal probability))
    (hdelta : model.delta ≤ min 1 delta0) :
    let SD : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a := cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) a (b i)
        | 1 => inverseResponse (SD i) a
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) a
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) a (p i)
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∀ i infrared branch, ∀ a probability : ℝ,
      0 < a → 0 < probability →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {omega | a < |Rsp i infrared branch M omega -
          Rsp i infrared branch M' omega|} ≤ ENNReal.ofReal probability := by
  intro SD SN Rsp P i infrared branch a probability ha hp
  obtain ⟨_, _, hC⟩ := hresp model Rm Sreg It H HI hdelta (z i) (r i) (hr i)
    (htriadic i) (phi i) (hphi i) (b i) (hb i) (fD i) (fN i)
    (KD i) (KN i) (hKD i) (hKN i) (hfD i) (hfN i) (hfNmean i) (p i)
  simpa only [Rsp, SD, SN] using hC infrared branch a probability ha hp

/-- All five response-bank conclusions follow from the exact finite-level
Cauchy and pairwise relative-tail estimates. The finite estimates remain the
analytic obligation. -/
theorem aux_response_bank_full_conditional_assembly
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {I : Type*} [Countable I]
    (Z : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ)
    (hZ : ∀ i infrared branch N, Measurable (Z i infrared branch N))
    (hZnonneg : ∀ i infrared branch N omega, 0 ≤ Z i infrared branch N omega)
    (hCauchy : ∀ i infrared branch, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        (chaosSampleLaw model).toMeasure
          {omega | a < |Z i infrared branch M omega -
            Z i infrared branch M' omega|} ≤ ENNReal.ofReal b)
    (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ i infrared branch, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
            (chaosSampleLaw model).toMeasure
              {omega | Cgeom * eps * Z i infrared branch N omega +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i infrared branch N omega - Z i infrared branch M omega|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) :
    ∃ L : I → Bool → Fin 4 → BilateralField d → ℝ,
      (∀ i infrared branch, Measurable (L i infrared branch)) ∧
      (∀ i infrared branch omega, 0 ≤ L i infrared branch omega) ∧
      (∀ i infrared branch,
        TendstoInMeasure (chaosSampleLaw model).toMeasure
          (Z i infrared branch) atTop (L i infrared branch)) ∧
      (∀ i eps, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ N : ℕ, Ne ≤ N → ∀ infrared branch,
            (chaosSampleLaw model).toMeasure
              {omega | Cgeom * eps * L i infrared branch omega +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i infrared branch N omega - L i infrared branch omega|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
        ∀ i infrared branch,
          Tendsto (fun N => Z i infrared branch N omega) atTop
            (nhds (L i infrared branch omega))) ∧
      (∀ i eps, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N → ∀ infrared branch,
            (chaosSampleLaw model).toMeasure
              {omega | Cgeom * eps * L i infrared branch
                  (aux_responseBankShift w omega) +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i infrared branch N (aux_responseBankShift w omega) -
                  L i infrared branch (aux_responseBankShift w omega)|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) := by
  obtain ⟨L, hLm, hLn, hLt, _htail, hscaled, hbc⟩ :=
    aux_response_bank_limit_assembly (chaosSampleLaw model).toMeasure
      Z hZ hZnonneg hCauchy Cgeom hCgeom hpair
  refine ⟨L, hLm, hLn, hLt, ?_, hbc, ?_⟩
  · intro i eps heps
    obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ :=
      aux_response_bank_eight_tail_uniform
        (chaosSampleLaw model).toMeasure (Z i) (L i) (Cgeom * eps)
        (fun infrared branch => hscaled i infrared branch eps heps)
    exact ⟨Ce, ce, Ne, hCe, hce,
      fun N hN infrared branch => hbound infrared branch N hN⟩
  · intro i eps heps
    obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ :=
      aux_response_bank_eight_tail_uniform
        (chaosSampleLaw model).toMeasure (Z i) (L i) (Cgeom * eps)
        (fun infrared branch => hscaled i infrared branch eps heps)
    refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
    intro w N hN infrared branch
    rw [aux_response_bank_stationary_tail_transfer d model Z L hZ hLm
      (Cgeom * eps) (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))
      i N infrared branch w]
    exact hbound infrared branch N hN

/-- The fixed-`N`, large-`M` pair clause of the single-cube
`prop_as_response_bank_cauchy` body, reindexed over the countable family, in the
strict-threshold form consumed by `aux_response_bank_full_conditional_assembly`. -/
theorem aux_actual_response_bank_pair_family
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (_Pc : in_poincare d hd Jc) (_Xc : in_extension d hd Jc)
    (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    {I : Type*} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (phi : I → SpatialCoordinates d → ℝ)
    (hphi : ∀ i, ContDiff ℝ ∞ (phi i))
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (hb : ∀ i, ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d))] phi i)
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (KD KN : I → ℝ)
    (hKD : ∀ i, 0 ≤ KD i) (hKN : ∀ i, 0 ≤ KN i)
    (hfD : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i)
    (hfN : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i)
    (hfNmean : ∀ i, (∫ x in (centeredCube (z i) (r i) (hr i) :
      Set (SpatialCoordinates d)),
      (fN i : SpatialCoordinates d → ℝ) x) = 0)
    (p : I → Fin d → ℝ)
    (delta0 Cgeom : ℝ)
    (hresp : ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      let hP := (aux_prop_as_response_bank_cube_poincare hd z r hr).1
      let hP0 := (aux_prop_as_response_bank_cube_poincare hd z r hr).2
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a := cutoffPositiveCoefficient model Hused omega N z hr
          match branch.val with
          | 0 => dirichletResponse SD a b
          | 1 => inverseResponse SD a
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN a
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 a p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ infrared branch N, ∀ᵐ omega ∂P, 0 ≤ Rsp infrared branch N omega) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ infrared branch,
                  P {omega | |Rsp infrared branch N omega -
                    Rsp infrared branch M omega| >
                    Cgeom * eps * Rsp infrared branch N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (branch : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega | tolerance < |Rsp infrared branch M omega -
            Rsp infrared branch M' omega|} ≤
            ENNReal.ofReal probability))
    (hdelta : model.delta ≤ min 1 delta0) :
    let SD : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a := cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) a (b i)
        | 1 => inverseResponse (SD i) a
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) a
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) a (p i)
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∀ i infrared branch, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N → ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
          P {omega | Cgeom * eps * Rsp i infrared branch N omega +
              Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
            |Rsp i infrared branch N omega - Rsp i infrared branch M omega|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  intro SD SN Rsp P i infrared branch eps heps
  obtain ⟨_, hpr, _⟩ := hresp model Rm Sreg It H HI hdelta (z i) (r i) (hr i)
    (htriadic i) (phi i) (hphi i) (b i) (hb i) (fD i) (fN i)
    (KD i) (KN i) (hKD i) (hKN i) (hfD i) (hfN i) (hfNmean i) (p i)
  obtain ⟨Ce, ce, Ne, hCe, hce, hN⟩ := hpr eps heps
  refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
  intro N hNe
  obtain ⟨M0, hM0, hM⟩ := hN N hNe
  refine ⟨M0, hM0, ?_⟩
  intro M hM0M
  exact hM M hM0M infrared branch

/-- Family assembly of the six actual response-bank conclusions from the exact
single-cube body of `prop_as_response_bank_cauchy` at one `in_responses`
package `Rm`, via the two family adapters and
`aux_response_bank_full_conditional_assembly`. -/
theorem aux_actual_response_bank_family_of_cauchy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization model H)
    {I : Type*} [Countable I]
    (z : I → SpatialCoordinates d) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i))) u‖)
    (phi : I → SpatialCoordinates d → ℝ)
    (hphi : ∀ i, ContDiff ℝ ∞ (phi i))
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (hb : ∀ i, ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d))] phi i)
    (fD fN : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (KD KN : I → ℝ)
    (hKD : ∀ i, 0 ≤ KD i) (hKN : ∀ i, 0 ≤ KN i)
    (hfD : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i)
    (hfN : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
      |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i)
    (hfNmean : ∀ i, (∫ x in (centeredCube (z i) (r i) (hr i) :
      Set (SpatialCoordinates d)),
      (fN i : SpatialCoordinates d → ℝ) x) = 0)
    (p : I → Fin d → ℝ)
    (delta0 Cgeom : ℝ)
    (hresp : ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      let hP := (aux_prop_as_response_bank_cube_poincare hd z r hr).1
      let hP0 := (aux_prop_as_response_bank_cube_poincare hd z r hr).2
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a := cutoffPositiveCoefficient model Hused omega N z hr
          match branch.val with
          | 0 => dirichletResponse SD a b
          | 1 => inverseResponse SD a
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN a
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 a p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ infrared branch N, ∀ᵐ omega ∂P, 0 ≤ Rsp infrared branch N omega) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ infrared branch,
                  P {omega | |Rsp infrared branch N omega -
                    Rsp infrared branch M omega| >
                    Cgeom * eps * Rsp infrared branch N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (branch : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega | tolerance < |Rsp infrared branch M omega -
            Rsp infrared branch M' omega|} ≤
            ENNReal.ofReal probability))
    (hCgeom : 0 < Cgeom)
    (hdelta : model.delta ≤ min 1 delta0) :
    let SD : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => killedResponseSpace (hP i)
    let SN : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
      fun i => meanZeroResponseSpace (hP0 i)
    let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
      fun i infrared branch N omega =>
        let Hused := if infrared then H else
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
          cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
        match branch.val with
        | 0 => dirichletResponse (SD i) (a) (b i)
        | 1 => inverseResponse (SD i) (a)
            ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
        | 2 => inverseResponse (SN i) (a)
            ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
        | _ => affineInverseNeumannResponse (hP0 i) (a) (p i)
    let Shift : SpatialCoordinates d → BilateralField d → BilateralField d :=
      fun w omega => fun j : ℤ =>
        (omega j).comp
          (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
      (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
        Measurable (Rlim i infrared branch)) ∧
      (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
        ∀ omega : BilateralField d, 0 ≤ Rlim i infrared branch omega) ∧
      (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
        TendstoInMeasure P (Rsp i infrared branch) atTop
          (Rlim i infrared branch)) ∧
      (∀ i : I, ∀ eps : ℝ, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ N : ℕ, Ne ≤ N →
            ∀ infrared : Bool, ∀ branch : Fin 4,
              P {omega |
                  Cgeom * eps * Rlim i infrared branch omega +
                      Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |Rsp i infrared branch N omega -
                      Rlim i infrared branch omega|} ≤
                ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
      (∀ᵐ omega ∂P, ∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
        Tendsto (fun N : ℕ => Rsp i infrared branch N omega) atTop
          (nhds (Rlim i infrared branch omega))) ∧
      (∀ i : I, z i = 0 → r i = 1 → ∀ eps : ℝ, 0 < eps →
        ∃ Ce ce : ℝ, ∃ Ne : ℕ,
          0 < Ce ∧ 0 < ce ∧
          ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N →
            ∀ infrared : Bool, ∀ branch : Fin 4,
              P {omega |
                  Cgeom * eps * Rlim i infrared branch (Shift w omega) +
                      Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |Rsp i infrared branch N (Shift w omega) -
                      Rlim i infrared branch (Shift w omega)|} ≤
                ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) := by
  intro SD SN Rsp Shift P
  have hZ : ∀ i infrared branch N, Measurable (Rsp i infrared branch N) :=
    aux_actual_response_bank_rsp_measurable model H HI z r hr hP hP0 b fD fN p
  have hZn : ∀ i infrared branch N omega, 0 ≤ Rsp i infrared branch N omega :=
    aux_actual_response_bank_rsp_nonneg model H z r hr hP hP0 b fD fN p
  have hCauchy := aux_actual_response_bank_cauchy_family d hd Jc Pc Xc Sf model Rm Sreg It
    H HI z r hr htriadic hP hP0 phi hphi b hb fD fN KD KN hKD hKN hfD hfN hfNmean
    p delta0 Cgeom hresp hdelta
  have hpair := aux_actual_response_bank_pair_family d hd Jc Pc Xc Sf model Rm Sreg It
    H HI z r hr htriadic hP hP0 phi hphi b hb fD fN KD KN hKD hKN hfD hfN hfNmean
    p delta0 Cgeom hresp hdelta
  obtain ⟨L, hLm, hLn, hLt, htail, hae, hstat⟩ :=
    aux_response_bank_full_conditional_assembly d model Rsp hZ hZn hCauchy
      Cgeom hCgeom hpair
  exact ⟨L, hLm, hLn, hLt, htail, hae, fun i _ _ eps heps => hstat i eps heps⟩

/-! ## The universal constant of `p.coarse.grained.bound`, and the paper's response bank,
  are now `SubdiffusiveProcess.Paper.paper_responses_bank` (deduplicated): the former
  `aux_rbpf_C0`... `aux_rbpf_defect_exists` block moved there verbatim. -/

/-- The actual response defect selected from the attained finite-dimensional
maximum. Its value is uniquely determined by the `IsGreatest` property. -/
noncomputable def aux_rbpf_canonicalDefect {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ℕ → SpatialCoordinates d → BilateralField d → ℝ :=
  fun m y om => Classical.choose (aux_rbpf_defect_exists model m y om)

theorem aux_rbpf_canonicalDefect_nonneg {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ m y om, 0 ≤ aux_rbpf_canonicalDefect model m y om := by
  intro m y om
  exact (Classical.choose_spec (aux_rbpf_defect_exists model m y om)).1

theorem aux_rbpf_canonicalDefect_isGreatest {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
      IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.ResponseJ
            (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d))
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
            (fun x => Homogenization.scalarMatrix
              (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)))}
        (aux_rbpf_canonicalDefect model m y om) := by
  intro m y om
  exact (Classical.choose_spec (aux_rbpf_defect_exists model m y om)).2

theorem aux_rbpf_ahom_inputs {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    (∀ n m : ℕ, n < m →
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq model.P *
            ((m : ℝ) - n)) * SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) ∧
    (∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ 1) ∧
    (∀ m : ℕ,
      Real.exp (-((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) ≤
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) := by
  refine ⟨?_, SubdiffusiveProcess.CoarseGrainingVocab.ahom_le_one model, ?_⟩
  · intro n m hnm
    have h := (_root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds (d := d)).2 model m n hnm
    simpa only [Nat.cast_sub hnm.le] using h
  · intro m
    simpa [Nat.cast_add] using
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower model m)

/-- A common response moment bank for the four displayed branches. The construction uses the response Cauchy estimates, the killed and Dirichlet identifications, and continuous weighting. It passes to the limit after fixing the cutoff and applies Borel--Cantelli on the countable family, with the quantifier order shown in the statement. -/
theorem aux_prop_as_response_bank_conditional
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    : ∃ Cresp : ℝ, ∃ B : Finset ℝ, ∃ delta0 Cgeom : ℝ,
      0 < Cresp ∧
      B.Nonempty ∧
      (128 * (d : ℝ)) ∈ B ∧
      (∀ xi ∈ B, 1 ≤ xi) ∧
      0 < delta0 ∧ delta0 < 1 ∧ 0 < Cgeom ∧
      (∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (_hdelta : model.delta ≤ min 1 delta0),
        (∀ xi ∈ B,
            xi ≤ Cresp⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹) ∧
        (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
           (_HI : InfraredCharacterization model H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ)
        (hr : ∀ i : I, 0 < r i)
        (_htriadic : ∀ i : I, ∃ j : ℤ, r i = (3 : ℝ) ^ j),
      ∀ (hP : ∀ i : I, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖),
      ∀ (hP0 : ∀ i : I, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖),
      ∀ (phi : I → SpatialCoordinates d → ℝ),
        (∀ i : I, ContDiff ℝ ∞ (phi i)) →
      ∀ (b : ∀ i : I, weakSobolevGraph
          (centeredCube (z i) (r i) (hr i))),
        (∀ i : I,
          ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
            SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) :
                Set (SpatialCoordinates d))] phi i) →
      ∀ (fD fN : ∀ i : I, DomainL2 (centeredCube (z i) (r i) (hr i)))
        (KD KN : I → ℝ),
        (∀ i : I, 0 ≤ KD i) →
        (∀ i : I, 0 ≤ KN i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i) →
        (∀ i : I, (∫ x in (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d)),
          (fN i : SpatialCoordinates d → ℝ) x) = 0) →
      ∀ (p : I → (Fin d → ℝ)),
      let SD : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => killedResponseSpace (hP i)
      let SN : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => meanZeroResponseSpace (hP0 i)
      let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun i infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
            cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
          match branch.val with
          | 0 => dirichletResponse (SD i) (a) (b i)
          | 1 => inverseResponse (SD i) (a)
              ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
          | 2 => inverseResponse (SN i) (a)
              ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
          | _ => affineInverseNeumannResponse (hP0 i) (a) (p i)
      let Shift : SpatialCoordinates d → BilateralField d → BilateralField d :=
        fun w omega => fun j : ℤ =>
          (omega j).comp
            (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Measurable (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          ∀ omega : BilateralField d, 0 ≤ Rlim i infrared branch omega) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          TendstoInMeasure P (Rsp i infrared branch) atTop
            (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch omega +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N omega -
                        Rlim i infrared branch omega|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
        (∀ᵐ omega ∂P, ∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Tendsto (fun N : ℕ => Rsp i infrared branch N omega) atTop
            (nhds (Rlim i infrared branch omega))) ∧
        (∀ i : I, z i = 0 → r i = 1 → ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch (Shift w omega) +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N (Shift w omega) -
                        Rlim i infrared branch (Shift w omega)|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))))
      )) := by
  obtain ⟨delta0c, Cgeom, hdelta0c, hCgeom, hresp⟩ :=
    prop_as_response_bank_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  -- the finite bank: the single high order `128 d` (Remark ),
  -- chosen before the model; the disorder threshold makes it admissible both
  -- for the input constant `Cresp` and for the universal constant of the
  -- constructed paper package
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hxiB1 : (1 : ℝ) ≤ 128 * (d : ℝ) := by linarith
  have hC0 := (aux_rbpf_C0_spec d).1
  let Cresp := aux_rbpf_C0 d
  have hCresp : 0 < Cresp := hC0
  have hK1 : 0 < Cresp * (128 * (d : ℝ)) + 1 := by positivity
  refine ⟨Cresp, {128 * (d : ℝ)}, min (min delta0c (1 / 2))
      (1 / (Cresp * (128 * (d : ℝ)) + 1)), Cgeom,
    hCresp, Finset.singleton_nonempty _, Finset.mem_singleton_self _, ?_, ?_, ?_,
    hCgeom, ?_⟩
  · intro xi hxi
    rw [Finset.mem_singleton] at hxi
    rw [hxi]
    exact hxiB1
  · exact lt_min (lt_min hdelta0c (by norm_num)) (by positivity)
  · exact lt_of_le_of_lt (min_le_of_left_le (min_le_right _ _)) (by norm_num)
  · intro model Sreg It hdelta
    have hdpos : 0 < model.delta := model.shellPrefix.delta_pos
    have hd0 := hdelta.trans (min_le_right _ _)
    have hdc : model.delta ≤ min 1 delta0c :=
      le_min (hdelta.trans (min_le_left _ _))
        (hd0.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hhalf : model.delta ≤ 1 / 2 :=
      hd0.trans ((min_le_left _ _).trans (min_le_right _ _))
    refine ⟨?_, ?_⟩
    · intro xi hxi
      rw [Finset.mem_singleton] at hxi
      rw [hxi]
      exact aux_rbpf_order_admissible Cresp (128 * (d : ℝ)) model.delta hCresp hxiB1
        hdpos hhalf (hd0.trans (min_le_right _ _))
    · intro H HI I _ z r hr htriadic
        hP hP0 phi hphi b hb fD fN KD KN hKD hKN hfD hfN hfNmean p
      have : NeZero d := ⟨by omega⟩
      obtain ⟨ahom_ordering, ahom_le_one, ahom_lower⟩ := aux_rbpf_ahom_inputs model
      let defect := aux_rbpf_canonicalDefect model
      have hdefect_nonneg := aux_rbpf_canonicalDefect_nonneg model
      have hdefect_isGreatest := aux_rbpf_canonicalDefect_isGreatest model
      exact aux_actual_response_bank_family_of_cauchy d hd Jc Pc Xc Sf model
        (aux_rbpf_paperResponses hd model ahom_ordering ahom_le_one ahom_lower
          defect hdefect_nonneg hdefect_isGreatest)
        Sreg It H HI z r hr htriadic hP hP0 phi hphi b hb fD fN KD KN hKD hKN hfD hfN
        hfNmean p delta0c Cgeom hresp hCgeom hdc

/-- Source-facing response bank: construct the cube witnesses and the actual
response moment bank before invoking the conditional analytic assembly. -/

theorem prop_as_response_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    : ∃ Cresp : ℝ, ∃ B : Finset ℝ, ∃ delta0 Cgeom : ℝ,
      0 < Cresp ∧
      B.Nonempty ∧
      (128 * (d : ℝ)) ∈ B ∧
      (∀ xi ∈ B, 1 ≤ xi) ∧
      0 < delta0 ∧ delta0 < 1 ∧ 0 < Cgeom ∧
      (∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (_hdelta : model.delta ≤ min 1 delta0),
        (∀ xi ∈ B,
            xi ≤ Cresp⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹) ∧
        (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
           (_HI : InfraredCharacterization model H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ)
        (hr : ∀ i : I, 0 < r i)
        (_htriadic : ∀ i : I, ∃ j : ℤ, r i = (3 : ℝ) ^ j),
      ∀ (phi : I → SpatialCoordinates d → ℝ)
        (hphi : ∀ i : I, ContDiff ℝ ∞ (phi i)),
      ∀ (fD fN : ∀ i : I, DomainL2 (centeredCube (z i) (r i) (hr i)))
        (KD KN : I → ℝ),
        (∀ i : I, 0 ≤ KD i) →
        (∀ i : I, 0 ≤ KN i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i) →
        (∀ i : I, (∫ x in (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d)),
          (fN i : SpatialCoordinates d → ℝ) x) = 0) →
      ∀ (p : I → (Fin d → ℝ)),
      let hP : ∀ i : I, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).1
      let hP0 : ∀ i : I, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).2
      let b : ∀ i : I, weakSobolevGraph
          (centeredCube (z i) (r i) (hr i)) :=
        fun i => Classical.choose
          (aux_source_response_bank_smooth_weak_witness
            (z i) (r i) (hr i) (phi i) (hphi i))
      let SD : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => killedResponseSpace (hP i)
      let SN : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => meanZeroResponseSpace (hP0 i)
      let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun i infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
            cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
          match branch.val with
          | 0 => dirichletResponse (SD i) (a) (b i)
          | 1 => inverseResponse (SD i) (a)
              ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
          | 2 => inverseResponse (SN i) (a)
              ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
          | _ => affineInverseNeumannResponse (hP0 i) (a) (p i)
      let Shift : SpatialCoordinates d → BilateralField d → BilateralField d :=
        fun w omega => fun j : ℤ =>
          (omega j).comp
            (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Measurable (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          ∀ omega : BilateralField d, 0 ≤ Rlim i infrared branch omega) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          TendstoInMeasure P (Rsp i infrared branch) atTop
            (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch omega +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N omega -
                        Rlim i infrared branch omega|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
        (∀ᵐ omega ∂P, ∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Tendsto (fun N : ℕ => Rsp i infrared branch N omega) atTop
            (nhds (Rlim i infrared branch omega))) ∧
        (∀ i : I, z i = 0 → r i = 1 → ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch (Shift w omega) +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N (Shift w omega) -
                        Rlim i infrared branch (Shift w omega)|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))))
      )) := by

  obtain ⟨Cresp, B, delta0, Cgeom, hCresp, hBnonempty, hB128,
    hBord, hdelta0, hdelta1, hCgeom, hmain⟩ :=
    aux_prop_as_response_bank_conditional d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨Cresp, B, delta0, Cgeom, hCresp, hBnonempty, hB128,
    hBord, hdelta0, hdelta1, hCgeom, ?_⟩
  intro model Sreg It hdelta
  obtain ⟨horders, hrest⟩ := hmain model Sreg It hdelta
  refine ⟨horders, ?_⟩
  intro H HI I _ z r hr htriadic phi hphi fD fN KD KN hKD hKN hfD hfN hfNmean p
  let hP := fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).1
  let hP0 := fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).2
  let b := fun i => Classical.choose
    (aux_source_response_bank_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
  have hb : ∀ i, ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
      phi i := by
    intro i
    exact Classical.choose_spec
      (aux_source_response_bank_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
  exact hrest H HI I z r hr htriadic hP hP0 phi hphi b hb
    fD fN KD KN hKD hKN hfD hfN hfNmean p

end SubdiffusiveProcess.Paper
