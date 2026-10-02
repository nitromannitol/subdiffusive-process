import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.cell_catalogue
import SubdiffusiveProcess.Paper.good_event
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.finite_interval_packing
import SubdiffusiveProcess.Paper.paper_responses_bank
import SubdiffusiveProcess.Paper.finite_response_ramp
import SubdiffusiveProcess.Paper.lem_rare_tests
import SubdiffusiveProcess.Paper.lem_finite_trace_tests
import SubdiffusiveProcess.Paper.lem_local_normalizations
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.lfsgs_trace_moments
import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
import SubdiffusiveProcess.FiniteStopping.BilateralSamples
import SubdiffusiveProcess.FiniteStopping.CellRegularity
import SubdiffusiveProcess.FiniteStopping.ZeroDisorderScores
import SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists

/-! This module establishes hRegWitness of arbitrary Rm for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- hRegWitness of lfgc in the finite stopping construction. -/
theorem aux_lfsgs_hRegWitness_of_arbitrary_Rm_hRegWitness_of_lfgc
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I)
    (Extension : Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) (hH1four : 4 ≤ H1)
    (hlfgc :
          let L : ℝ := (3 : ℝ) ^ H1
          let mgrid := subdivisionHalfWidth H1
          ∃ sigma eps cell lam lamDet cdet : ℝ,
          ∃ en nc ns : ℕ, ∃ self padRoot : Fin en, ∃ chosen : Fin nc,
          ∃ selfShift : Fin ns,
          ∃ (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
            (cmpShift : Fin nc → SpatialCoordinates d)
            (shift : Fin ns → SpatialCoordinates d)
            (cmpRoot : Fin nc → Fin en × Fin ns)
            (cmpWord : (c : Fin nc) →
              Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
            (buffer k0 : ℕ),
            sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
            0 < cell ∧ 0 < lam ∧ lam < lamDet ∧ lamDet < 1 ∧ 0 < cdet ∧
            enDepth self = 0 ∧ shift selfShift = 0 ∧ 0 < buffer ∧
            (∀ c : Fin nc,
              cmpShift c = descendantCenter 1
                (((3 : ℝ) ^ enDepth (cmpRoot c).1) • shift (cmpRoot c).2)
                ((3 : ℝ) ^ enDepth (cmpRoot c).1)
                (enDepth (cmpRoot c).1 + cmpDepth c) (cmpWord c)) ∧
            (∀ x : SpatialCoordinates d,
              x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) →
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                ∃ (U : Fin en × Fin ns) (D : ℕ) (w : Fin D → OddGridIndex d 1),
                  Metric.ball x (rho / 2) ⊆
                    Metric.ball (descendantCenter 1
                      (((3 : ℝ) ^ enDepth U.1) • shift U.2)
                      ((3 : ℝ) ^ enDepth U.1) D w)
                      (descendantSide 1 D ((3 : ℝ) ^ enDepth U.1) / 2) ∧
                  descendantSide 1 D ((3 : ℝ) ^ enDepth U.1) ≤ 9 * rho) ∧
            cell_catalogue d (Fin en) (Fin nc)
              (fun k z => Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2))
              (fun k z e => Metric.ball z
                (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth e) / 2))
              (fun k z c => Metric.ball
                (z + (3 : ℝ) ^ (-(k : ℤ)) • cmpShift c)
                (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (-(cmpDepth c : ℤ))) / 2))
              self (fun _ _ => chosen) ∧
          ∃ delta0 Cfin Aext pad : ℝ,
            0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧ ∃ hpad : 1 < pad, pad < L ∧
      pad ≤ 3 ∧ pad ≤ (3 : ℝ) ^ enDepth padRoot ∧
            ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
              (response : Paper.in_responses d model)
              (hresponse : response.C ≤ Cresp)
              (regularity : Paper.in_6_16 d model)
              (iteration : Paper.in_iteration d model I regularity)
              (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization model H → model.delta ≤ delta0 →
            ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
                eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
            ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
              (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
              (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
                primitive_scores d model sigma eps (eta N omega)
                  (fun m z => F N m z omega) (fun m z => Praw N m z omega)
                  (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
                  (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) →
            ∃ Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d),
            let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
            ∃ Carrier : Set (BilateralField d), MeasurableSet Carrier ∧ P Carrierᶜ = 0 ∧
            (∀ (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d),
              omega ∈ Carrier →
              let N := m + k
              let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
              let rootSide : Fin en × Fin ns → ℝ :=
                fun U => r * (3 : ℝ) ^ enDepth U.1
              let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
                fun U => z + rootSide U • shift U.2
              let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
                fun U D => by
                  classical
                  exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
                    ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
                    ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                      (descendantCenter 1 (rootCentre U) (rootSide U) D))
              let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
                fun U D _ =>
                  Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
                    (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
              let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
                if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
              let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
              omega ∈ Good m k z ↔
                (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
                  0 ≤ (N : ℤ) - j →
                    Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
                (∀ t : Fin ns,
                  F N (m + enDepth padRoot)
                    ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
                  Praw N (m + enDepth padRoot)
                    ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
                ∀ infrared : Bool,
                  let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
                  let kappa := fun J : ℕ =>
                    Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
                  let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
                    if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
                    else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
                  let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
                    kappa ((N : ℤ) - j).toNat / kappa N *
                      Real.exp (Hused om w + retained j w om)
                  let rEn := rootSide
                  let zEn := rootCentre
                  let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
                    intro U; dsimp [rEn, rootSide, r]; positivity
                  let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
                    cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
                  let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
                    reference ((k : ℤ) - enDepth U.1) (zEn U) om
                  let zCmp := fun c : Fin nc => z + r • cmpShift c
                  let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
                  let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
                  let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
                    cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
                  let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
                    reference ((k : ℤ) + cmpDepth c) (zCmp c) om
                  good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
                    centres pre Zphys Dphys
                    (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
                    (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
                    (fun e om i j =>
                      (Homogenization.Book.Ch02.sigmaCoarse
                        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                        ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                          (Homogenization.originCube d 0))) i j / refEn e om)
                    (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
                      (zCmp c) (rCmp c) (refCmp c om) sigma 2)
                    (fun c om => reference (k : ℤ) z om / refCmp c om)
                    chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega) ∧
            (∀ (m k : ℕ) (z : SpatialCoordinates d),
              MeasurableSet (Good m k z) ∧ ∃ W : ℕ+ → Set (BilateralField d),
                (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
                  ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))] (W h)) ∧
                (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
                (Good m k z)ᶜ ⊆ ⋃ h : ℕ+, W h) ∧
            (∀ (omega : BilateralField d), omega ∈ Carrier →
              ∀ (m k : ℕ) (z : SpatialCoordinates d),
              omega ∈ Good m k z → ∀ infrared : Bool,
              let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
              let hr : 0 < r := by positivity
              let hLr : 0 < L * r := mul_pos (pow_pos (by norm_num) H1) hr
              let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
              let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
              let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
              let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
              let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
              let N := m + k
              let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
              let s : ℝ := (kappa m / kappa (m + k)) *
                Real.exp ((Hused omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
              (4 ≤ H1 → ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d mgrid),
                z = oddGridCenter zP (L * r) mgrid idx →
                (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
                  (centeredCube zP (L * r) hLr : Set (SpatialCoordinates d)) →
                let Parent : Opens (SpatialCoordinates d) := centeredCube zP (L * r) hLr
                let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model Hused omega N zP hLr
                ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
                  Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
                  ∀ u : weakSobolevGraph Parent,
                    (∀ psi : killedSobolevGraph Parent,
                      @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
                        ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
                    ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
                      ContinuousOn U closedQ ∧
                      ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                      @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
                      @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
                        Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
                          Real.sqrt (@sobolevCoefficientForm d Parent aP
                            (u : SobolevData Parent) (u : SobolevData Parent)) +
                        Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf) ∧
              (let aQ : PositiveCoefficient Q := cutoffPositiveCoefficient model Hused omega N z hr
               ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
                   ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
                 ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
                   ContinuousOn G closedQ → @IsHolderOn d beta (frontier (Q : Set (SpatialCoordinates d))) G →
                   ((fun x => (b : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) → ∀ c : ℝ,
                   @dirichletResponse d Q (@killedResponseSpace d Q hP) aQ b ≤
                     Aext * r ^ ((d : ℝ) - 2) * s *
                       (@cAlphaNorm d beta
                         (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
                         (fun x => G (T x) - c)) ^ (2 : ℕ))))    :
    ∃ Cfin pad delta0 sigma eps : ℝ, 0 < Cfin ∧ ∃ hpad : (1 : ℝ) < pad, pad ≤ 3 ∧ 0 < delta0 ∧
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d model)
        (Sreg : Paper.in_6_16 d model) (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H),
        model.delta ≤ delta0 → Rm.C ≤ Cresp →
        ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
          ∃ Wt : ℕ+ → Set (BilateralField d),
            (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
              ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))] (Wt h)) ∧
            (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wt h) ≤
              ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
              ¬ SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k z omega →
                omega ∈ ⋃ h : ℕ+, Wt h) := by
  classical
  obtain ⟨sigma, eps, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _,
      hsigma, heps, _, _, _, _, _, _, _, _, _, _, _,
      delta0, Cfin, _, pad,
      hdelta0, hCfin, _,
      hpad,
      hpadL, hpad3, _, hinner⟩ := hlfgc
  refine ⟨Cfin, pad, min delta0 1, sigma, eps, hCfin, hpad, hpad3, lt_min hdelta0 one_pos,
    hsigma, heps, ?_⟩
  intro model Rm Sreg It H hH hdeltamin hCresp' N k z hkN
  have hd1 : min delta0 1 ≤ delta0 := min_le_left _ _
  obtain ⟨eta0, F0, Praw0, Rraw0, Draw0, Z0, rawGood0, hEta0, hprim0⟩ :=
    Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists model sigma eps hsigma heps
  obtain ⟨Good, Carrier, hCarrierMeas, hCarrierNull, hGoodIff, hGoodMeasW, hClause⟩ :=
    hinner model Rm hCresp' Sreg It H hH (hdeltamin.trans hd1) eta0 hEta0
      F0 Praw0 Rraw0 Draw0 Z0 rawGood0 hprim0
  obtain ⟨_, W, hWmeas, hWdecay, hWcover⟩ := hGoodMeasW (N - k) k z
  refine ⟨W, hWmeas, hWdecay, ?_⟩
  have hcarr : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, omega ∈ Carrier := by
    rw [ae_iff]; simpa only using hCarrierNull
  filter_upwards [hcarr] with omega homega hnReg
  by_contra hnotin
  have hgmem : omega ∈ Good (N - k) k z := by
    by_contra hcon
    exact hnotin (hWcover hcon)
  apply hnReg
  have hgoodclause := (hClause omega homega (N - k) k z hgmem true).1 hH1four
  have hmk : N - k + k = N := Nat.sub_add_cancel hkN
  simp only [hmk, if_true] at hgoodclause
  exact hgoodclause

/-- hRegWitness direct in the finite stopping construction. -/
theorem aux_lfsgs_hRegWitness_of_arbitrary_Rm_hRegWitness_direct
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I)
    (Extension : Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) (hH1four : 4 ≤ H1) :
    ∃ Cfin pad delta0 sigma eps : ℝ, 0 < Cfin ∧ ∃ hpad : (1 : ℝ) < pad, pad ≤ 3 ∧ 0 < delta0 ∧
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d model)
        (Sreg : Paper.in_6_16 d model) (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H),
        model.delta ≤ delta0 → Rm.C ≤ Cresp →
        ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
          ∃ Wt : ℕ+ → Set (BilateralField d),
            (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
              ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))] (Wt h)) ∧
            (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wt h) ≤
              ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
              ¬ SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k z omega →
                omega ∈ ⋃ h : ℕ+, Wt h) :=
  Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_hRegWitness_of_lfgc d hd I Poincare Extension Sobolev
    MeyersMorrey Cp Step D Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 hH1four
    (Paper.lem_finite_good_cell d hd I Poincare Extension Sobolev MeyersMorrey Cp Step D Dbase
      Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1)

/-- canonicalDefect in the finite stopping construction. -/
noncomputable def aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ℕ → SpatialCoordinates d → BilateralField d → ℝ :=
  fun m y om => Classical.choose (Paper.aux_rbpf_defect_exists model m y om)

/-- canonicalDefect nonneg in the finite stopping construction. -/
theorem aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_nonneg [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ m y om, 0 ≤ Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect model m y om := by
  intro m y om
  exact (Classical.choose_spec (Paper.aux_rbpf_defect_exists model m y om)).1

/-- canonicalDefect isGreatest in the finite stopping construction. -/
theorem aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_isGreatest [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
      IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.ResponseJ
            (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d))
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) • e)
            (fun x => Homogenization.scalarMatrix
              (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
                ((m : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)))}
        (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect model m y om) := by
  intro m y om
  exact (Classical.choose_spec (Paper.aux_rbpf_defect_exists model m y om)).2

/-- hRegWitness of arbitrary Rm in the finite stopping construction. -/
theorem lfsgs_hRegWitness_of_arbitrary_Rm
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I)
    (Extension : Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) (hH1four : 4 ≤ H1) :
    ∃ Cfin pad delta0 sigma eps : ℝ, 0 < Cfin ∧ ∃ hpad : (1 : ℝ) < pad, pad ≤ 3 ∧ 0 < delta0 ∧
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d model)
        (Sreg : Paper.in_6_16 d model) (It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H),
        model.delta ≤ delta0 →
        ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
          ∃ Wt : ℕ+ → Set (BilateralField d),
            (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
              ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))] (Wt h)) ∧
            (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wt h) ≤
              ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
              ¬ SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k z omega →
                omega ∈ ⋃ h : ℕ+, Wt h) := by
  obtain ⟨C0, hC0pos, hbank⟩ := Paper.paper_responses_bank d hd
  obtain ⟨Cfin, pad, delta0, sigma, eps, hCfin, hpad, hpadle3, hdelta0, hsigma, heps, hwit⟩ :=
    Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_hRegWitness_direct d hd I Poincare Extension Sobolev
      MeyersMorrey Cp Step D Dbase C0 hC0pos alpha beta rate hbeta hba halpha hrate H1 hH1 hH1four
  refine ⟨Cfin, pad, delta0, sigma, eps, hCfin, hpad, hpadle3, hdelta0, hsigma, heps, ?_⟩
  intro model Rm Sreg It H hH hdelta N k z hkN
  obtain ⟨Rm', hRmC, -, -⟩ :=
    hbank model Rm.ahom_ordering Rm.ahom_le_one Rm.ahom_lower
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect model)
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_nonneg model)
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_isGreatest model)
  have hRmCresp : Rm'.C ≤ C0 := le_of_eq hRmC
  exact hwit model Rm' Sreg It H hH hdelta hRmCresp N k z hkN

end Paper
