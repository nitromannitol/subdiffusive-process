import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Paper.inputs_baseline_witness
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace Paper

/-- Band approximation for the actual primitive scores. The baseline moment
bank is derived internally, so its moment-constant function is not a public input
and the positive decay rates precede every moment order. -/
theorem mfd_lem_band : ∀
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I)
    (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d)
    (weight : Fin 4 → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (Klip : ℝ≥0)
    (Phi : (Fin T → (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)) → ℝ) → ℝ)
    (hPhiLip : LipschitzWith Klip Phi) (hPhi0 : Phi 0 = 0)
    (hPhiNonneg : ∀ x, 0 ≤ Phi x),
    ∃ a c : ℝ, ∃ width : ℕ,
      0 < a ∧ 0 < c ∧ 0 < width ∧
      ∀ p : ℝ, 1 ≤ p →
        ∃ q delta0 Cp : ℝ,
          max (2 * p) (32 * (d : ℝ) / min s sigma) ≤ q ∧ 1 ≤ q ∧
          0 < delta0 ∧ 0 < Cp ∧
          ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
            ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
            ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
            ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
              InfraredCharacterization M H →
            ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
                  omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
            ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
              (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
              (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
                primitive_scores d M s eps (eta N omega)
                  (fun m y => F N m y omega) (fun m y => Praw N m y omega)
                  (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
                  (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
            ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n))
              (unitA : ∀ (n : ℤ) (z : SpatialCoordinates d),
                PositiveCoefficient (centeredCube z ((3 : ℝ) ^ (-n)) (sidePos n))),
              (∀ n z, (unitA n z).val =ᵐ[volume.restrict
                (centeredCube z ((3 : ℝ) ^ (-n)) (sidePos n) : Set (SpatialCoordinates d))]
                  (fun _ => (1 : ℝ))) →
            let kappa : ℕ → ℝ := fun J =>
              Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
            let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
              fun n z omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) z
                else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) z
            let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
              fun N n z omega => kappa ((N : ℤ) - n).toNat / kappa N *
                Real.exp (H omega z + retained n z omega)
            let eramp : ℝ → ℝ → ENNReal → ℝ := fun lo hi x =>
              (min (1 : ENNReal) ((x - ENNReal.ofReal lo) /
                ENNReal.ofReal (hi - lo))).toReal
            12 * q ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ ∧
            ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d), n ≤ (N : ℤ) →
              (∀ i : Fin T, n + offset i ≤ (N : ℤ)) →
              let coords : BilateralField d →
                  Fin T → (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)) → ℝ :=
                fun omega i =>
                  let m := n + offset i
                  let w := z + ((3 : ℝ) ^ (-n)) • shift i
                  let r := (3 : ℝ) ^ (-m)
                  let aN := Lane4.cutoffPositiveCoefficient M H omega N w (sidePos m)
                  let ref := reference N m w omega
                  Sum.elim
                    (fun j => if j = 0 then
                      I.lam w r (sidePos m) aN w r sigma 2 / ref -
                        I.lam w r (sidePos m) (unitA m w) w r sigma 2
                    else if j = 1 then
                      I.Lam w r (sidePos m) aN w r sigma 2 / ref -
                        I.Lam w r (sidePos m) (unitA m w) w r sigma 2
                    else ref / I.lam w r (sidePos m) aN w r sigma 2 -
                      (I.lam w r (sidePos m) (unitA m w) w r sigma 2)⁻¹)
                    (Sum.elim
                      (fun ij =>
                        (if ij.1 then (Homogenization.Book.Ch02.sigmaCoarse
                          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                          ((I.chart w r (sidePos m) aN w r).coeffOn
                            (Homogenization.originCube d 0))) ij.2.1 ij.2.2 / ref
                        else ref * (Homogenization.Book.Ch02.sigmaStarInvCoarse
                          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                          ((I.chart w r (sidePos m) aN w r).coeffOn
                            (Homogenization.originCube d 0))) ij.2.1 ij.2.2) -
                        (if ij.2.1 = ij.2.2 then 1 else 0))
                      (fun j => if j = 0 then I.err w r (sidePos m) aN w r ref s 2
                        else reference N n z omega / ref - 1))
              let X : BilateralField d → ℝ := fun omega =>
                let m := ((N : ℤ) - n).toNat
                let w := (3 : ℝ) ^ N • z
                weight 0 * (Draw N m w omega).toReal +
                weight 1 * eramp (eps / 2) eps (F N m w omega) +
                weight 2 * eramp 6 12 (Praw N m w omega) +
                weight 3 * eramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m w omega) +
                Phi (coords omega)
              ∀ h : ℕ, 1 ≤ h →
                ∃ Xband : BilateralField d → ℝ,
                  AEStronglyMeasurable[MeasurableSpace.comap
                    (fun omega : BilateralField d =>
                      fun j : Set.Icc (-n - (width * (h + 1) : ℕ))
                        (-n + (width * (h + 1) : ℕ)) => omega (j : ℤ))
                    inferInstance] Xband (chaosSampleLaw M).toMeasure ∧
                  eLpNorm (fun omega => X omega - Xband omega)
                    (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                    ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ))))
 :=
by
  classical
  intro d hd _ _ _ I hPoincare hExtension hPerturbation hSobolev D Cresp hCresp
    s sigma eps hs hsigma heps T offset shift weight hweight Klip Phi hPhiLip hPhi0 hPhiNonneg
  obtain ⟨CD0, deltaD, hpositive, hbaseline⟩ :=
    (inputs_baseline_witness d hd) s eps hs heps
  obtain ⟨a, c, width, ha, hc, hwidth, hband⟩ :=
    lem_band d hd I hPoincare hExtension hPerturbation hSobolev D Cresp hCresp
      s sigma eps hs hsigma heps T offset shift weight hweight Klip Phi hPhiLip hPhi0
      hPhiNonneg CD0 (fun q hq => (hpositive q hq).1)
  refine ⟨a, c, width, ha, hc, hwidth, ?_⟩
  intro p hp
  obtain ⟨q, delta0, Cp, hq, hqone, hdelta0, hCp, hmodel⟩ := hband p hp
  refine ⟨q, min delta0 (min 1 (deltaD q)), Cp, hq, hqone,
    lt_min hdelta0 (lt_min zero_lt_one (hpositive q hqone).2), hCp, ?_⟩
  intro M hsmall Rm hRm Sreg It H hIR eta hEta F Praw Rraw Draw Z rawGood hprim
    sidePos unitA hunitA
  have hsmallOld : M.delta ≤ delta0 :=
    hsmall.trans (min_le_left delta0 (min 1 (deltaD q)))
  have hsmallBaseline : M.delta ≤ min 1 (deltaD q) :=
    hsmall.trans (min_le_right delta0 (min 1 (deltaD q)))
  have hDraw := hbaseline q hqone M hsmallBaseline eta hEta F Praw Rraw Draw Z rawGood hprim
  exact hmodel M hsmallOld Rm hRm Sreg It H hIR eta hEta F Praw Rraw Draw Z rawGood hprim
    hDraw sidePos unitA hunitA

end Paper
