module

public import SubdiffusiveProcess.Paper.density_represented_harmonic_bank
public import SubdiffusiveProcess.Paper.density_source_energy_limit
public import SubdiffusiveProcess.Paper.goodext_source_upper_goodcells
public import SubdiffusiveProcess.Paper.density_full_grid
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- The actual same-array good-cell caps and represented harmonic construction
produce one bank of actual energy limits. Its good-cell costs satisfy the local
source bound for every supplied normalized Holder estimate, while all contained
cells retain the crude cost and maximum-principle bounds. -/
theorem density_good_harmonic_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta etaGrid : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hba : beta ≤ alpha) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (hetaGrid : 0 < etaGrid) :
    ∃ Ce delta0 : ℝ, 0 < Ce ∧ 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)) (hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (N : ℕ → ℕ) (hN : StrictMono N)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
        (field : Omega → BilateralField d)
        (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
        (hConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega)))
        (eRef : ℕ → ℝ) (heRef : ∀ k, 0 < eRef k)
        (hRefLim : ∀ k : ℕ,
          let kappa : ℕ → ℝ := fun L => Real.exp (((L : ℝ) + 1) *
            _root_.SubdiffusiveProcess.Model.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M L
          Tendsto (fun n => kappa (N n - k) / kappa (N n)) atTop (𝓝 (eRef k)))
        (lambdaLim cdet : ℝ)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal),
      ∀ (Bank : Type) [Countable Bank] (level : Bank → ℕ) (idx : Bank → Fin d → ℤ),
      let centre := fun q i => z i + (3 : ℝ) ^ (-(level q : ℤ)) * idx q i
      let radius := fun q => (3 : ℝ) ^ (-(level q : ℤ))
      let cube := fun q => centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _)
      ∀ (hsub : ∀ q, (cube q : Set (SpatialCoordinates d)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Cells : Type) [Countable Cells] (embed : Cells → Bank),
      let ref := fun b : Cells => fun omega => eRef (level (embed b)) * Real.exp
        (H (field omega) (centre (embed b)) +
          ∑ j ∈ Finset.range (level (embed b)), (field omega) (-(j : ℤ)) (centre (embed b)))
      ∀ (ZL DL : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loL hiL : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AEL : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errL ratL : Cells → Unit → BilateralField d → ℝ)
        (hMeas : ∀ b U, Measurable (hiL b U))
        (hArr : ∀ b, aux_affine_source_cells_env_cellArrays I M H (1 / 64) ((beta - 1 / 2) / 4)
          1 0 Z Draw N (level (embed b)) (centre (embed b))
          (ZL b) (DL b) (loL b) (hiL b) (AEL b) (errL b) (ratL b)),
      let Good := fun b => field ⁻¹' gcat_good 1 lambdaLim (1 / 4) (1 / 4) cdet
        (ZL b) (DL b) (loL b) (hiL b) (errL b) (ratL b)
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᵐ om ∂P,
      let coeff := fun (q : Bank) (n : ℕ) => cutoffPositiveCoefficient M H (env n om) (N n)
        (centre q) (show 0 < radius q from zpow_pos (by norm_num) _)
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (psi (seq n)) om) (N (psi (seq n))) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (psi (seq n)) om) (N (psi (seq n)))) t alpha ∧
        ∀ g : SpatialCoordinates d → ℝ,
          ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g →
    ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
      ∃ (uN : ∀ q, ℕ → weakSobolevGraph (cube q))
        (VN : Bank → ℕ → SpatialCoordinates d → ℝ)
        (rho : ℕ → ℕ) (Vcell : Bank → SpatialCoordinates d → ℝ) (cost : Bank → ℝ),
      StrictMono rho ∧ (∀ q,
        (∀ n, ContinuousOn (VN q n)
            (closure (cube q : Set (SpatialCoordinates d))) ∧
          ((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (cube q : Set (SpatialCoordinates d))] VN q n ∧
          (∀ x ∈ frontier (cube q : Set (SpatialCoordinates d)),
            VN q n x = g x) ∧
          ∀ x ∈ closure (cube q : Set (SpatialCoordinates d)),
            |VN q n x - g x| ≤ Osc * radius q ^ alpha) ∧
        ContinuousOn (Vcell q)
          (closure (cube q : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (VN q) (Vcell q) atTop
          (closure (cube q : Set (SpatialCoordinates d))) ∧
        Tendsto (fun n => sobolevCoefficientForm
          (coeff q (psi (seq (rho n)))) (uN q n).val (uN q n).val) atTop (𝓝 (cost q)) ∧
        0 ≤ cost q ∧ cost q ≤ A0 * radius q ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid) ) ∧
      ∀ b : Cells, om ∈ Good b → 0 < ref b om ∧
        ∀ (Cnorm se nu fsup : ℝ), 0 ≤ Cnorm → 0 < se → 0 ≤ nu → 0 ≤ fsup →
        ∀ cq : ℝ,
        IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => g (centre (embed b) + radius (embed b) • x) - cq) →
        cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => g (centre (embed b) + radius (embed b) • x) - cq) ≤
            Cnorm * radius (embed b) ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
              Cnorm * radius (embed b) ^ (2 : ℝ) * se⁻¹ * fsup →
        cost (embed b) ≤ (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Cnorm) ^ 2) *
          (ref b om / se) * (nu + se⁻¹ * radius (embed b) ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  have hHarmonic0 := density_represented_harmonic_bank d hd I Pin X W Cp Sob Interp
    t alpha beta etaGrid ht htd ha ha1 hba hb hetaGrid
  obtain ⟨delta0, hd0, hHarmonic⟩ := hHarmonic0
  obtain ⟨Ce, hCe, hCost⟩ := density_source_energy_limit d hd I X Sob beta hb
  refine ⟨Ce, delta0, hCe, hd0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N hN Omega _ P _ env hEnv field hfield hConv
    eRef heRef hRefLim lambdaLim cdet Z Draw Bank _ level idx centre radius cube hsub Cells _ embed ref
    ZL DL loL hiL AEL errL ratL hMeas hArr Good
  have hThree : (0 : ℝ) < 3 := by norm_num
  have hRadius : ∀ q, 0 < radius q := fun q => zpow_pos hThree _
  have hUpper0 := goodext_source_upper_goodcells d I M H hIR Omega P N hN env
    beta Cells (fun b => level (embed b)) (fun b => centre (embed b))
    field hfield hEnv hConv eRef heRef hRefLim (1 / 64) ((beta - 1 / 2) / 4) rfl
    1 0 1 lambdaLim (1 / 4) (1 / 4) cdet (by norm_num)
    Z Draw ZL DL loL hiL AEL errL ratL hMeas hArr
  obtain ⟨psi, hpsi, hUpper⟩ := hUpper0
  have hBank := hHarmonic M Rm Sreg It H hIR hdelta z r hr S hS 1 (fun _ => z)
    (fun n => N (psi n)) (hN.comp hpsi) Omega P (fun n => env (psi n))
    (fun n => (hEnv (psi n)).measurable) (fun n => (hEnv (psi n)).map_eq)
    Bank level (fun _ => 0) idx hsub
  refine ⟨psi, hpsi, ?_⟩
  filter_upwards [hUpper, hBank] with om hu hbAll
  intro coeff
  obtain ⟨seq, hseq, hA, hCells, hgAll⟩ := hbAll
  refine ⟨seq, hseq, hA, hCells, ?_⟩
  intro g hgc hgh
  obtain ⟨A0, Osc, hA0, hOsc, datum, VN, rho, Vcell, cost, hrho, hbank⟩ := hgAll g hgc hgh
  let uN := fun q n => dirichletMinimizer
    (killedResponseSpace (centeredCube_killedPoincare (centre q) (hRadius q)))
    (coeff q (psi (seq (rho n)))) (datum q)
  refine ⟨A0, Osc, hA0, hOsc, uN, VN, rho, Vcell, cost, hrho, ?_, ?_⟩
  · exact hbank

  · intro b hgood
    have href : 0 < ref b om := (hu b).1
    refine ⟨href, ?_⟩
    intro Cnorm se nu fsup hCnorm hse hnu hfsup cq hHolder hNorm
    have hSide : radius (embed b) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    have hLam : ∀ᶠ n in atTop,
        I.Lam (centre (embed b)) (radius (embed b)) (hRadius (embed b))
          (coeff (embed b) (psi (seq (rho n))))
          (centre (embed b)) (radius (embed b)) ((beta - 1 / 2) / 4) 2 ≤ 8 * ref b om := by
      have h := (hseq.comp hrho).tendsto_atTop.eventually ((hu b).2.2.2 hgood)
      norm_num only [show (2 : ℝ) * (1 / 4)⁻¹ = 8 by norm_num] at h
      exact h
    exact hCost (centre (embed b)) (radius (embed b)) (hRadius (embed b)) hSide
      alpha Cnorm se (ref b om) nu fsup 8 hba hCnorm hse href.le hnu hfsup (by norm_num)
      g cq hHolder hNorm (centeredCube_killedPoincare (centre (embed b)) (hRadius (embed b)))
      (fun n => coeff (embed b) (psi (seq (rho n)))) hLam (datum (embed b)) (VN (embed b))
      (fun n => ((hbank (embed b)).1 n).1)
      (fun n => ((hbank (embed b)).1 n).2.1)
      (fun n => ((hbank (embed b)).1 n).2.2.1)
      (cost (embed b)) (hbank (embed b)).2.2.2.1
end SubdiffusiveProcess.Paper
