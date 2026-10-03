module

public import SubdiffusiveProcess.Paper.density_source_harmonic_grid

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

/-- The conclusion of `density_source_harmonic_grid` after its constants, folded into a definition (verbatim body): destructuring
the folded form is cheap. -/
def aux_density_grid_packed_body
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (Pin : Paper.in_poincare d hd I)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (alpha beta etaGrid t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hbetaLtAlpha : beta < alpha)
    (hetaGrid : 0 < etaGrid) (H1 : ℕ) (hH1 : 0 < H1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (Cbound eps lambdaLim cdet Ce delta0 : ℝ) : Prop :=
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (hfield_meas : Measurable field)
        (hfield_law : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : Fin 2 → ℕ → Ω → BilateralField d)
        (henv_meas : ∀ (a : Fin 2) (n : ℕ), Measurable (env a n))
        (henv_law : ∀ (a : Fin 2) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (hEnvConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
      , ∀ (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside),
      ∀ (Bank : Type) [Countable Bank] (level : Bank → ℕ) (indexInt : Bank → Fin d → ℤ),
      let fullCentre := fun q i => Qcentre i + (3 : ℝ) ^ (-(level q : ℤ)) * indexInt q i
      let fullRadius := fun q => (3 : ℝ) ^ (-(level q : ℤ))
      let fullCube := fun q => centeredCube (fullCentre q) (fullRadius q) (zpow_pos (by norm_num) _)
      ∀ (hsub : ∀ q, (fullCube q : Set (SpatialCoordinates d)) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (Cells : Type) [Countable Cells] (first : Cells) (embed : Cells → Bank),
      let k := fun b => level (embed b)
      let kIdx := fun b => indexInt (embed b)
      let z := fun b i => Qcentre i + (3 : ℝ) ^ (-(k b : ℤ)) * kIdx b i
      ∀ (hgH : ∀ b, 1 ≤ k b)
        (hRootsQ : ∀ (b : Cells) (U : Fin 3 × (Fin d → Fin 3)),
          closure (centeredCube (gcat_rootCentre 1 (k b) (z b) U) (gcat_rootSide 1 (k b) U)
            (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))),
      ∀ (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
        (hdisorder : M.delta ≤ delta0)
        (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
        (root0 : RootIndex)
        (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
        (hrCat : ∀ j, 0 < rCat j)
        (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
        (DCat : ∀ j, Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
        [hDCat : ∀ j, Countable (DCat j)]
        (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
        (TCat : RootIndex → Type) [hTCat : ∀ j, Countable (TCat j)]
        (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
        (thetaH1Cat : ∀ j, TCat j →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (usrc : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
        (srcRep : Fin 2 → ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : Fin 2 → ∀ j, TCat j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
        (Cext : ℝ) (etaCat : ℝ) (orders : Finset ℝ)
        (hetaCatGrid : etaCat ≤ etaGrid)
        (Index : Type) [Countable Index]
        (resp : Fin 2 → Index → ℕ → Ω → ℝ) (respLim : Fin 2 → Index → Ω → ℝ)
        (constants : Fin 2 → Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
        (coercivityKey extensionKey lambdaKey : RootIndex → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
        (gridKey : Grid → Index)
        (hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
        (hRepEstimates : ∀ a : Fin 2,
          conv_represented_estimates d hd M H Ω P (phi a) (env a) RootIndex root0
            zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
            (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t orders I
            Index (resp a) (respLim a) (constants a) Gcat
            coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
            sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
            Grid origin gridRoot gridKey)
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (hBounds : ∀ a : Fin 2, ∀ᵐ omega ∂P,
          in_represented_bounds_seq d hd Qcentre Qside hQside S
            (fun n => Lane4.cutoffPositiveCoefficient M H (env a n omega)
              (phi a n) Qcentre hQside) (G a omega)),
      ∃ (Form : Fin 2 → Ω → _root_.DirichletForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (Gamma : ∀ (a : Fin 2) omega, DirichletForm.EnergyMeasure (Form a omega).toClosedForm),
      (∀ a omega, ∃ C, DirichletForm.IsCoreOn (Form a omega).toClosedForm
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C) ∧
      (∀ᵐ omega ∂P, ∀ a u, (Form a omega).energy u = limitFormEnergy (G a omega) u) ∧
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ (a : Fin 2) (j : ℕ), 0 < eRef a j) ∧
      ( ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a (psi n) - j) / kappa (phi a (psi n))) atTop
            (𝓝 (eRef a j))) ∧
      ∃ (ZL DL : Fin 2 → Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loL hiL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AEL : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errL ratL : Fin 2 → Cells → Unit → BilateralField d → ℝ),
      (∀ (active : List (Fin d → Fin (3 ^ H1)) → Prop)
        (index : List (Fin d → Fin (3 ^ H1)) → Cells),
        (∀ w, active w → k (index w) = H1 * w.length) →
        let Good := fun w => {omega | active w → ∀ a : Fin 2, omega ∈
          gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet (ZL a (index w)) (DL a (index w))
            (loL a (index w)) (hiL a (index w)) (errL a (index w)) (ratL a (index w))}
        ∃ B : BilateralField d → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
              (Set.ncard {i : Fin J | omega ∉ Good ((List.ofFn pi).take (i.val + 1))} : ℝ) ≤
                theta * (J : ℝ) + B omega ) ∧
      (let ref := fun b omega => eRef 0 (k b) * Real.exp
        (H (field omega) (z b) + ∑ j ∈ Finset.range (k b), (field omega) (-(j : ℤ)) (z b))
       let Good := fun b => field ⁻¹' gcat_good 1 lambdaLim (1 / 4) (1 / 4) cdet
         (ZL 0 b) (DL 0 b) (loL 0 b) (hiL 0 b) (errL 0 b) (ratL 0 b)
       ∃ K : Ω → ℝ, (∀ omega, 0 ≤ K omega) ∧ ∀ᵐ omega ∂P,
         (∀ b, omega ∈ Good b → (ref b omega)⁻¹ ≤ K omega * ((3 : ℝ) ^ (-(k b : ℤ))) ^ (-etaCat)) ∧
         ∀ fsup c : ℝ, 0 < c → ∃ r0 : ℝ, 0 < r0 ∧ ∀ b,
           (3 : ℝ) ^ (-(k b : ℤ)) ≤ r0 → omega ∈ Good b →
           (ref b omega)⁻¹ * ((3 : ℝ) ^ (-(k b : ℤ))) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
             c * ((3 : ℝ) ^ (-(k b : ℤ))) ^ d) ∧
      (let Q := centeredCube Qcentre Qside hQside
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))
      let Good : Cells → Fin 2 → Set Ω := fun b a => field ⁻¹' gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
        (ZL a b) (DL a b) (loL a b) (hiL a b) (errL a b) (ratL a b)
      let sRef : Cells → Fin 2 → Ω → ℝ := fun b a omega => eRef a (k b) *
        Real.exp (H (field omega) (z b) + ∑ j ∈ Finset.range (k b), (field omega) (-(j : ℤ)) (z b))
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (fL2 : DomainL2 Q), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] f) →
        let u := G 0 omega fL2
        let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
          Lane4.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
          ∃ tau : ℕ → ℕ, StrictMono tau ∧
            Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd Qcentre Qside hQside S
              (fun n => cutoffPositiveCoefficient M H (env 1 (tau n) omega) (phi 1 (tau n)) Qcentre hQside)) ∧
            aux_prop_conc_mesh_cutoff_family_AllCellBounds Qcentre Qside hQside
              (fun n => cutoffCoefficient M H (env 1 (tau n) omega) (phi 1 (tau n))) t alpha ∧
            let coeff := fun (q : Bank) (n : ℕ) => cutoffPositiveCoefficient M H
              (env 1 (tau n) omega) (phi 1 (tau n)) (fullCentre q)
              (show 0 < fullRadius q from zpow_pos (by norm_num) _)
            ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
            ∃ (uN : ∀ q, ℕ → weakSobolevGraph (fullCube q))
              (VN : Bank → ℕ → SpatialCoordinates d → ℝ)
              (Vcell : Bank → SpatialCoordinates d → ℝ) (cost : Bank → ℝ),
              (∀ q,
                (∀ n, ContinuousOn (VN q n) (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                  ((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                    (fullCube q : Set (SpatialCoordinates d))] VN q n ∧
                  (∀ x ∈ frontier (fullCube q : Set (SpatialCoordinates d)), VN q n x = U x) ∧
                  ∀ x ∈ closure (fullCube q : Set (SpatialCoordinates d)),
                    |VN q n x - U x| ≤ Osc * fullRadius q ^ alpha) ∧
                ContinuousOn (Vcell q) (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                TendstoUniformlyOn (VN q) (Vcell q) atTop (closure (fullCube q : Set (SpatialCoordinates d))) ∧
                Tendsto (fun n => sobolevCoefficientForm (coeff q n) (uN q n).val (uN q n).val)
                  atTop (𝓝 (cost q)) ∧
                0 ≤ cost q ∧ cost q ≤ A0 * fullRadius q ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)) ∧
              ∀ b : Cells, omega ∈ Good b 0 ∧ omega ∈ Good b 1 →
                ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                let r : ℝ := (3 : ℝ) ^ (-(k b : ℤ))
                z b = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall (z b) (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                cost (embed b) ≤ (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Ctotal) ^ 2) *
                  (eRef 1 (k b) / eRef 0 (k b)) *
                  ((((Gamma 0 omega).measure u) (Metric.ball zP (L * r / 2))).toReal +
                    (sRef b 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2))

/-- `density_source_harmonic_grid`, with the conclusion after the constants folded into `aux_density_grid_packed_body`. -/
theorem density_grid_packed
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (Pin : Paper.in_poincare d hd I)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (alpha beta etaGrid t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hbetaLtAlpha : beta < alpha)
    (hetaGrid : 0 < etaGrid) (H1 : ℕ) (hH1 : 0 < H1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ Cbound eps lambdaLim cdet Ce delta0 : ℝ,
      (1 ≤ Cbound ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧ lambdaLim ∈ Set.Ioo (0 : ℝ) 1 ∧
        0 < cdet ∧ 0 < Ce ∧ 0 < delta0) ∧
      aux_density_grid_packed_body d hd I _X _Sob Interp _Step Pin _MeyersMorrey D Cp Dbase alpha beta etaGrid t ht htd halpha hbeta hbetaLtAlpha hetaGrid H1 hH1 theta htheta0 htheta1 Cbound eps lambdaLim cdet Ce delta0 := by
  obtain ⟨Cbound, eps, lambdaLim, cdet, Ce, delta0, h1, h2, h3, h4, h5, h6, hB⟩ :=
    density_source_harmonic_grid d hd I _X _Sob Interp _Step Pin _MeyersMorrey D Cp Dbase alpha beta etaGrid t ht htd halpha hbeta hbetaLtAlpha hetaGrid H1 hH1 theta htheta0 htheta1
  exact ⟨Cbound, eps, lambdaLim, cdet, Ce, delta0, ⟨h1, h2, h3, h4, h5, h6⟩, hB⟩

end Paper
