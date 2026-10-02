import SubdiffusiveProcess.Paper.affine_source_cells_represented
import SubdiffusiveProcess.Paper.conv_represented_estimates_subcatalogue
import SubdiffusiveProcess.Paper.conv_represented_estimates_subseq
import Mathlib.Tactic

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem affine_source_cells_root_represented
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
          ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
            (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
            (NE psi phi : ℕ → ℕ) (hpsi : StrictMono psi) (hphi : phi = fun n => NE (psi n))
            (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
            (responseE : ℕ → Ω → ℝ) (eventE : Set Ω) (root : ℕ)
            (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
            [hDcat : ∀ i, Countable (Dcat i)]
            (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
            (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
            (traceH1 : ∀ i, ℕ → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (usrcE : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
            (srcRepE : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
            (ucellE : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (Cext etaCat t : ℝ)
            (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
            (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
            (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
            (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
            (hRepE : conv_represented_estimates d hd M H Ω P NE env
              ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
              usrcE srcRepE ucellE Cext beta alpha etaCat t {1} I
              ℕ (fun i n omega => catalogResponse i (NE n) (env n omega)) responseE
              (fun i n omega => catalogConstant i (NE n) (env n omega)) eventE
              coercivityKey extensionKey lambdaKey
              sourceResponseKey sourceGrowthKey sourceHolderKey
              cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)
            (hgrid : ∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
              ∃ g : ℕ, gridRoot g = j ∧ origin g = o)
            (jQ : ℕ)
            (GE : Ω → DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
              DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
            (hGE : ∀ᵐ omega ∂P,
              Tendsto (fun n => volumeResponseOperator (Sspace jQ)
                (Lane4.cutoffPositiveCoefficient M H (env (psi n) omega) (phi n) (z jQ) (hr jQ)))
                atTop (𝓝 (GE omega)))
            (hside : ∀ᵐ omega ∂P,
              ∃ (Ef : _root_.DirichletForm
                  (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
                (Gam : DirichletForm.EnergyMeasure Ef.toClosedForm),
                (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GE omega) u) ∧
                ∃ C, DirichletForm.IsCoreOn Ef.toClosedForm
                  (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C)
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
            (Mm : ℕ)
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
          ∃ (Grid : Type) (origin' : Grid → SpatialCoordinates d)
            (gridChoice : Fin (Fintype.card (Fin d → Fin Mm)) → Grid),
            (∀ sg : Fin d → Fin Mm,
              origin' (gridChoice ((Fintype.equivFin (Fin d → Fin Mm)) sg)) =
                fun i => ((sg i).val : ℝ) / (Mm : ℝ) + 1 / 2) ∧
            aux_affine_source_cells_env_Concl (z jQ) (r jQ) (hr jQ) P field GE gamma zeta
              rho H1 k0 lambdaLim cell epshom cdet Grid origin' (Fintype.card (Fin d → Fin Mm))
              gridChoice cellLevel cellCentre ZLim DLim loLim hiLim errLim ratioLim := by
  intro alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs hsSmall
    hsigma_eq hsigma hcell cbuf k0
  obtain ⟨H0, hH0⟩ := affine_source_cells_represented d hd I _X _Sob _Step _MeyersMorrey Pin D Cp
    beta hbeta hbeta1 alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs
    hsSmall hsigma_eq hsigma hcell cbuf k0
  refine ⟨H0, fun H1 hH1 => ?_⟩
  obtain ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hM⟩ := hH0 H1 hH1
  refine ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, ?_⟩
  intro M H hMH Rm Sreg _It Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv hdelta z r hr Sspace NE psi phi hpsi hphi
    catalogResponse catalogConstant responseE eventE root Dcat _ fcat trace traceH1 usrcE srcRepE ucellE
    Cext etaCat t coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hRepE hgrid jQ GE hGE hside
    eRef heRefPos heRefLim Mm Cells _ cellLevel cellCentre eta hEta F Praw Rraw Draw Z rawGood eps heps
    hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    hFiniteScoreGuard ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArr
  subst hphi
  classical
  have hR1 := conv_represented_estimates_subcatalogue (hrepresented := hRepE) (jTarget := jQ) ..
  have hR2 := conv_represented_estimates_subseq (hrep := hR1) (psi := psi) (hpsi := hpsi) ..
  have hNE : StrictMono NE ∧ (Sspace jQ).space =
      killedSobolevGraph (centeredCube (z jQ) (r jQ) (hr jQ)) := by
    have h := hRepE
    unfold conv_represented_estimates at h
    obtain ⟨-, -, -, -, -, hN, -, -, -, -, -, -, -, -, -, -, hS17, -⟩ := h
    exact ⟨hN, hS17 jQ⟩
  have hex : ∀ sg : Fin d → Fin Mm, ∃ g : ℕ, gridRoot g = jQ ∧
      origin g = (fun i => ((sg i).val : ℝ) / (Mm : ℝ) + 1 / 2) := fun sg =>
    hgrid jQ _ (fun i => ⟨((sg i).val : ℚ) / (Mm : ℚ) + 1 / 2, by push_cast; ring⟩)
  choose gsel hgsel1 hgsel2 using hex
  let gc : Fin (Fintype.card (Fin d → Fin Mm)) → {g : ℕ //
      (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))} :=
    fun i => ⟨gsel ((Fintype.equivFin (Fin d → Fin Mm)).symm i), by rw [hgsel1]⟩
  have hcore := hM M H hMH Rm Sreg _It Ω P field hfieldMeas hfieldLaw
    (fun n => env (psi n)) (fun n => hEnvMeas (psi n)) (fun n => hEnvLaw (psi n))
    (hEnvConv.mono fun omega h => h.comp hpsi.tendsto_atTop) hdelta (z jQ) (r jQ) (hr jQ)
    (Sspace jQ) hNE.2 _ (hNE.1.comp hpsi) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by exact ⟨rfl, rfl⟩) hR2 GE hGE hside eRef heRefPos heRefLim
    (Fintype.card (Fin d → Fin Mm)) gc (by intro i; exact Subtype.ext (hgsel1 _)) Cells cellLevel cellCentre
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet
    cdet hThresholds hcdet hcdetSmall hlamSmall hFiniteScoreGuard ZLim DLim loLim hiLim AELim errLim
    ratioLim hArrMeas hArr
  refine ⟨_, fun g => origin g.1, gc, ?_, hcore⟩
  intro sg
  simp only [gc, Equiv.symm_apply_apply, hgsel2]

end Paper
end
