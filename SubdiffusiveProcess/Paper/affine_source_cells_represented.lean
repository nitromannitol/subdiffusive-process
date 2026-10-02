import SubdiffusiveProcess.Paper.affine_source_cells_env
import SubdiffusiveProcess.Paper.represented_infrared_subsequence
import SubdiffusiveProcess.Paper.conv_represented_estimates_subseq
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Varying-environment affine estimates with the needed infrared subsequence
constructed internally. The conclusion concerns the original limit forms and
original measurable array limits, and does not depend on the further subsequence. -/
theorem affine_source_cells_represented
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    ∀ (alpha gamma zeta rho s sigma cell : ℝ)
    (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta)
    (hrho : 0 < rho)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (cbuf k0 : ℕ),
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 →
      (0 < H1 ∧ (1 : ℝ) < (3 : ℝ) ^ H1 ∧ Nat.floor (gamma * (H1 : ℝ)) + 6 < H1) ∧
      ∃ epshom : ℝ, ∃ (_hepshom : 0 < epshom),
      ∃ Cbound eps0 lam0 delta0 : ℝ,
        (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (hMH : InfraredCharacterization M H)
          (Rm : Paper.in_responses d M)
          (Sreg : Paper.in_6_16 d M)
          (_It : Paper.in_iteration d M I Sreg)
          (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (field : Ω → BilateralField d)
          (hfieldMeas : Measurable field)
          (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
          (env : ℕ → Ω → BilateralField d) (hEnvMeas : ∀ n, Measurable (env n))
          (hEnvLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
          (hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega))),
          M.delta ≤ delta0 →
          ∀ (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
            (S : ResponseSpace (centeredCube Qcentre Qside hQside))
            (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
            (phi : ℕ → ℕ) (hphi : StrictMono phi)
            (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
            (root0 : RootIndex)
            (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
            (hrCat : ∀ j, 0 < rCat j)
            (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
            (DCat : ∀ j,
              Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
            [hDCatc : ∀ j, Countable (DCat j)]
            (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
            (TCat : RootIndex → Type) [hTCatc : ∀ j, Countable (TCat j)]
            (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
            (thetaH1Cat : ∀ j, TCat j →
              Homogenization.H1Function
                (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
            (usrc : ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
            (srcRep : ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
            (ucell : ∀ j, TCat j → ℕ → Ω →
              Homogenization.H1Function
                (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
            (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
            (Index : Type) [Countable Index]
            (resp : Index → ℕ → Ω → ℝ)
            (respLim : Index → Ω → ℝ)
            (constants : Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
            (coercivityKey extensionKey lambdaKey : RootIndex → Index)
            (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
            (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
            (Grid : Type) [Countable Grid]
            (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
            (gridKey : Grid → Index)
            (hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
            (hRep : conv_represented_estimates d hd M H Ω P phi env
                RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat
                thetaH1Cat usrc srcRep ucell Cext beta alpha etaCat t
                orders I Index resp respLim constants Gcat
                coercivityKey extensionKey lambdaKey sourceResponseKey
                sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
                cellHolderKey Grid origin gridRoot gridKey)
            (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
              DomainL2 (centeredCube Qcentre Qside hQside))
            (hGE : ∀ᵐ omega ∂P,
              Tendsto (fun n => volumeResponseOperator S
                (Lane4.cutoffPositiveCoefficient M H (env n omega) (phi n) Qcentre hQside))
                atTop (𝓝 (GE omega)))
            (hside : ∀ᵐ omega ∂P,
              ∃ (Ef : _root_.DirichletForm
                  (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
                (Gam : DirichletForm.EnergyMeasure Ef.toClosedForm),
                (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GE omega) u) ∧
                ∃ C, DirichletForm.IsCoreOn Ef.toClosedForm
                  (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C)
            (eRef : ℕ → ℝ)
            (heRefPos : ∀ k : ℕ, 0 < eRef k)
            (heRefLim : ∀ k : ℕ,
              Tendsto (fun n : ℕ =>
                (let kappa : ℕ → ℝ := fun J =>
                   Real.exp (((J : ℝ) + 1) *
                     SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                     SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                 kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
                atTop (𝓝 (eRef k)))
            (J : ℕ) (gridChoice : Fin J → Grid)
            (hGridChoice : ∀ j, gridRoot (gridChoice j) = root0)
            (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
            (cellCentre : Cells → SpatialCoordinates d)
            (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
            (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Fin d → ℝ),
                eta N omega i y =
                  omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
            (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop)
            (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hepsSmall : eps ≤ eps0)
            (hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ N : ℕ,
                primitive_scores d M s eps (eta N omega)
                  (fun m y => F N m y omega)
                  (fun m y => Praw N m y omega)
                  (fun m y => Rraw N m y omega)
                  (fun m y => Draw N m y omega)
                  (fun m y => Z N m y omega)
                  (fun m y => rawGood N m y omega)))
            (lambdaCut lambdaLim lambdaDet cdet : ℝ)
            (hThresholds :
              0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
              lambdaLim < lambdaDet ∧ lambdaDet < 1)
            (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
            (hlamSmall : lambdaDet ≤ lam0)
            (hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (c : Cells) (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
                (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
                gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U + (D : ℤ) ≤ (N : ℤ) →
                ∀ j ∈ Finset.Icc (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U -
                    (cbuf : ℤ))
                  (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U + (D : ℤ)),
                  Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • gcat_obsCentre (Nat.floor (gamma * (H1 : ℝ)) + 4)
                      (cellLevel c) (cellCentre c) U D code) omega ≠ ⊤))
            (ZLim DLim : Cells → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
              ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
            (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
            (AELim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d →
              Matrix (Fin d) (Fin d) ℝ)
            (errLim ratioLim : Cells → Unit → BilateralField d → ℝ)
            (hArrMeas : ∀ c : Cells,
              (∀ U D code, Measurable (ZLim c U D code) ∧ Measurable (DLim c U D code)) ∧
              (∀ U, Measurable (loLim c U) ∧ Measurable (hiLim c U) ∧
                ∀ i j, Measurable (fun omega => AELim c U omega i j)) ∧
              Measurable (errLim c ()) ∧ Measurable (ratioLim c ()))
            (hArr : aux_affine_source_cells_env_arrays I M H s sigma
              (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf Z Draw phi cellLevel cellCentre
              ZLim DLim loLim hiLim AELim errLim ratioLim),
          aux_affine_source_cells_env_Concl Qcentre Qside hQside P field GE gamma zeta rho
            H1 k0 lambdaLim cell epshom cdet Grid origin J gridChoice cellLevel cellCentre ZLim DLim
            loLim hiLim errLim ratioLim := by
  intro alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs hsSmall
    hsigma_eq hsigma hcell cbuf k0
  obtain ⟨H0, hH0⟩ := affine_source_cells_env d hd I _X _Sob _Step _MeyersMorrey Pin D Cp
    beta hbeta hbeta1 alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta
    hrho hneg hs hsSmall hsigma_eq hsigma hcell cbuf k0
  refine ⟨H0, fun H1 hH1 => ?_⟩
  obtain ⟨hgeom, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hM⟩ := hH0 H1 hH1
  refine ⟨hgeom, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, ?_⟩
  intro M H hMH Rm Sreg _It Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv hdelta Qcentre Qside hQside S hS phi
    hphi RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat thetaH1Cat usrc srcRep
    ucell Cext etaCat t orders Index _ resp respLim constants Gcat coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue hRep GE hGE hside eRef heRefPos
    heRefLim J gridChoice hGridChoice Cells _ cellLevel cellCentre eta hEta F Praw Rraw Draw Z
    rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hFiniteScoreGuard ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArr
  obtain ⟨psi, hpsi, hIR⟩ := represented_infrared_subsequence M H hMH P field
    ⟨hfieldMeas, hfieldLaw⟩ PUnit Cells (fun _ => env)
    (fun _ n => ⟨hEnvMeas n, hEnvLaw n⟩) (hEnvConv.mono fun omega h _ => h) cellCentre
  have hRepSub := conv_represented_estimates_subseq d hd M H Ω P phi env
    RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    usrc srcRep ucell Cext beta alpha etaCat t orders I Index resp respLim constants Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep psi hpsi
  have hArrSub : aux_affine_source_cells_env_arrays I M H s sigma
      (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf Z Draw (fun n => phi (psi n))
      cellLevel cellCentre ZLim DLim loLim hiLim AELim errLim ratioLim := by
    intro c
    obtain ⟨hZ, hD, hlo, hhi, hA, herr, hrat⟩ := hArr c
    exact ⟨fun U D code => (hZ U D code).comp hpsi.tendsto_atTop,
      fun U D code => (hD U D code).comp hpsi.tendsto_atTop,
      fun U => (hlo U).comp hpsi.tendsto_atTop,
      fun U => (hhi U).comp hpsi.tendsto_atTop,
      fun U i j => (hA U i j).comp hpsi.tendsto_atTop,
      herr.comp hpsi.tendsto_atTop, hrat.comp hpsi.tendsto_atTop⟩
  exact hM M H hMH Rm Sreg _It Ω P field hfieldMeas hfieldLaw
    (fun n => env (psi n)) (fun n => hEnvMeas (psi n)) (fun n => hEnvLaw (psi n))
    (hEnvConv.mono fun omega h => h.comp hpsi.tendsto_atTop) hdelta
    Qcentre Qside hQside S hS (fun n => phi (psi n)) (hphi.comp hpsi)
    RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    (fun j f n => usrc j f (psi n)) (fun j f n => srcRep j f (psi n))
    (fun j t n => ucell j t (psi n)) Cext etaCat t orders Index
    (fun i n => resp i (psi n)) respLim (fun i n => constants i (psi n)) Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRootCatalogue
    hRepSub GE (hGE.mono fun omega h => h.comp hpsi.tendsto_atTop) hside eRef heRefPos
    (fun k => (heRefLim k).comp hpsi.tendsto_atTop) J gridChoice hGridChoice
    Cells cellLevel cellCentre (hIR.mono fun omega h => h PUnit.unit)
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    hFiniteScoreGuard ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArrSub

end Paper
