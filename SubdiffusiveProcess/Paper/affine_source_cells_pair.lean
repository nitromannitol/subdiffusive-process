import SubdiffusiveProcess.Paper.affine_source_cells_root_mass
import SubdiffusiveProcess.Paper.gcat_prefix_reference_pair
import SubdiffusiveProcess.Paper.gcat_good_measurable

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Both actual represented candidates satisfy the mass-cell affine estimate on the SAME
literal good event. All original-space array and reference limits are produced on one common
refinement, retained in the result, and used in the estimate. The event is measurable. -/
theorem affine_source_cells_pair
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    ∀ (alpha gamma zeta s sigma cell : ℝ)
    (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta)
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
      ∃ Cbound eps0 lam0 : ℝ,
        (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧
        ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 → eps ≤ eps0 →
        ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (hMH : InfraredCharacterization M H)
          (Rm : Paper.in_responses d M) (hRm : Rm.C ≤ Cresp)
          (Sreg : Paper.in_6_16 d M)
          (_It : Paper.in_iteration d M I Sreg)
          (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (field : Ω → BilateralField d)
          (hfieldMeas : Measurable field)
          (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
          (env : Fin 2 → ℕ → Ω → BilateralField d)
          (hEnvMeas : ∀ a n, Measurable (env a n))
          (hEnvLaw : ∀ a n, Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
          (hEnvConv : ∀ a, ∀ᵐ omega ∂P,
            Tendsto (fun n => env a n omega) atTop (𝓝 (field omega))),
          M.delta ≤ delta0 →
          ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
            (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
            (N : Fin 2 → ℕ → ℕ)
            (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
            (response : Fin 2 → ℕ → Ω → ℝ) (event : Fin 2 → Set Ω) (root : ℕ)
            (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
            [hDcat : ∀ i, Countable (Dcat i)]
            (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
            (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
            (traceH1 : ∀ i, ℕ → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (usrc : Fin 2 → ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
            (srcRep : Fin 2 → ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
            (ucell : Fin 2 → ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
            (Cext etaCat t : ℝ)
            (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
            (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
            (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
            (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
            (hRep : ∀ a, conv_represented_estimates d hd M H Ω P (N a) (env a)
              ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
              (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t {1} I
              ℕ (fun i n omega => catalogResponse i (N a n) (env a n omega)) (response a)
              (fun i n omega => catalogConstant i (N a n) (env a n omega)) (event a)
              coercivityKey extensionKey lambdaKey
              sourceResponseKey sourceGrowthKey sourceHolderKey
              cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)
            (hgrid : ∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
              ∃ g : ℕ, gridRoot g = j ∧ origin g = o)
            (GE : Fin 2 → ∀ j, Ω → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
              DomainL2 (centeredCube (z j) (r j) (hr j)))
            (hGE : ∀ a j, ∀ᵐ omega ∂P,
              Tendsto (fun n => volumeResponseOperator (Sspace j)
                (Lane4.cutoffPositiveCoefficient M H (env a n omega) (N a n) (z j) (hr j)))
                atTop (𝓝 (GE a j omega)))
            (hBounds : ∀ a j, ∀ᵐ omega ∂P, in_represented_bounds_seq d hd
              (z j) (r j) (hr j) (Sspace j)
              (fun n => Lane4.cutoffPositiveCoefficient M H (env a n omega) (N a n) (z j) (hr j))
              (GE a j omega))
            (g : aux_thm_prop_selection_geometry d)
            (hgH1 : g.H1 = H1) (hggamma : g.gamma = gamma) (hgzeta : g.zeta = zeta)
            (hwidth : 81 ≤ g.width)
            (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
            (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Fin d → ℝ),
                eta N omega i y =
                  omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
            (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop)
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
            (hlamSmall : lambdaDet ≤ lam0),
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ a k, 0 < eRef a k) ∧
      (∀ a (k : ℕ), Tendsto (fun n =>
        (let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((N a (psi n) : ℤ) - (k : ℤ)).toNat) / kappa (N a (psi n))))
        atTop (𝓝 (eRef a k))) ∧
      ∃ (ZLim DLim : Fin 2 → (ℕ × ℕ) → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → (ℕ × ℕ) → Unit → BilateralField d → ℝ),
      (∀ a c,
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U) ∧
          ∀ i j, Measurable (fun omega => AELim a c U omega i j)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ()) ∧
        aux_affine_source_cells_env_cellArrays I M H s sigma (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf Z Draw
          (fun n => N a (psi n)) (H1 * c.2) (z c.1)
          (ZLim a c) (DLim a c) (loLim a c) (hiLim a c) (AELim a c)
          (errLim a c) (ratioLim a c)) ∧
      (let Good : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
        {omega | aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
        ∀ a : Fin 2, omega ∈ gcat_good k0 lambdaLim cell epshom cdet
          (ZLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (DLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (loLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (hiLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (errLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (ratioLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))}
      (∀ n zc, MeasurableSet (Good n zc)) ∧
      ∀ᵐ omega ∂P, ∀ a : Fin 2, ∀ jQ : ℕ,
      ∀ (E' : _root_.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GE a jQ omega) u) →
      (∃ C, DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ hu : GE a jQ omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
      ∃ baseMesh : ℝ, 0 < baseMesh ∧
        ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
        ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        field omega ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
        aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
        closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
        let mu := Gam'.measure (GE a jQ omega f) + ENNReal.ofReal c •
          volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
        (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
          ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
            (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
          (⇑(GE a jQ omega f) =ᵐ[volume.restrict
            (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
          aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
            E'.toClosedForm Gam' (GE a jQ omega f) U c
            (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
              (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
                Set (SpatialCoordinates d))) := by
  intro alpha gamma zeta s sigma cell hba halpha hgamma hgamma1 hzeta hneg hs hsSmall
    hsigma_eq hsigma hcell cbuf k0
  obtain ⟨H0, hH0⟩ := affine_source_cells_root_mass d hd I _X _Sob _Step _MeyersMorrey Pin D Cp
    beta hbeta hbeta1 alpha gamma zeta s sigma cell hba halpha hgamma hgamma1 hzeta hneg hs
    hsSmall hsigma_eq hsigma hcell cbuf k0
  refine ⟨H0, fun H1 hH1 => ?_⟩
  obtain ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, deltaAff, hC, he0, hl0, hdAff, hAffine⟩ :=
    hH0 H1 hH1
  refine ⟨hfacts, epshom, hepshom, Cbound, eps0, lam0, hC, he0, hl0, ?_⟩
  intro eps heps hepsSmall
  obtain ⟨deltaPrefix, hdPrefix, hPrefix⟩ := gcat_prefix_reference_pair d hd I Pin _X
    _MeyersMorrey _Sob D Cresp hCresp s sigma eps hs hsigma heps
    (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf
  refine ⟨min deltaAff deltaPrefix, lt_min hdAff hdPrefix, ?_⟩
  intro M H hMH Rm hRm Sreg It Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw
    hEnvConv hdelta z r hr Sspace N catalogResponse catalogConstant response event root
    Dcat _ fcat trace traceH1 usrc srcRep ucell Cext etaCat t coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
    origin gridRoot gridKey hRep hgrid GE hGE hBounds g hgH1 hggamma hgzeta hwidth
    eta hEta F Praw Rraw Draw Z rawGood hPrimitive lambdaCut lambdaLim lambdaDet cdet
    hThresholds hcdet hcdetSmall hlamSmall
  classical
  have hN : ∀ a, StrictMono (N a) := by
    intro a
    have h := hRep a
    rcases h with ⟨_, _, _, _, _, hN, _⟩
    exact hN
  obtain ⟨psi, hpsi, eRef, heRef, heRefLim, ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim, hArr⟩ :=
    hPrefix M (hdelta.trans (min_le_right _ _)) Rm hRm Sreg It H hMH eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive (ℕ × ℕ) (fun c => H1 * c.2) (fun c => z c.1) N hN
  refine ⟨psi, hpsi, eRef, heRef, heRefLim, ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim,
    hArr, ?_⟩
  dsimp only
  let Good : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
    {omega | aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
        ∀ a : Fin 2, omega ∈ gcat_good k0 lambdaLim cell epshom cdet
      (ZLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
      (DLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
      (loLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
      (hiLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
      (errLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
      (ratioLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))}
  constructor
  · intro n zc
    change MeasurableSet (Good n zc)
    simp only [Good, setOf_forall]
    apply MeasurableSet.iInter
    intro _havailable
    apply MeasurableSet.iInter
    intro a
    have h := hArr a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n)
    exact gcat_good_measurable k0 lambdaLim cell epshom cdet _ _ _ _ _ _
      (fun U D code => (h.1 U D code).1) (fun U D code => (h.1 U D code).2)
      (fun U => (h.2.1 U).1) (fun U => (h.2.1 U).2.1) h.2.2.1
      (fun c => by cases c; exact h.2.2.2.1)
  · rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro jQ
    exact hAffine M H hMH Rm Sreg It Ω P field hfieldMeas hfieldLaw (env a)
      (hEnvMeas a) (hEnvLaw a) (hEnvConv a) (hdelta.trans (min_le_left _ _))
      z r hr Sspace (N a) psi (fun n => N a (psi n)) hpsi rfl catalogResponse catalogConstant
      (response a) (event a) root Dcat fcat trace traceH1 (usrc a) (srcRep a) (ucell a)
      Cext etaCat t coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey
      (hRep a) hgrid jQ (GE a jQ) (hGE a jQ) (hBounds a jQ) g hgH1 hggamma hgzeta hwidth
      (eRef a) (heRef a) (heRefLim a) eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall
      hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
      (ZLim a) (DLim a) (loLim a) (hiLim a) (AELim a) (errLim a) (ratioLim a)
      (fun c => ⟨(hArr a c).1, (hArr a c).2.1, (hArr a c).2.2.1, (hArr a c).2.2.2.1⟩)
      (fun c => (hArr a c).2.2.2.2) (fun n zc => field ⁻¹' Good n zc)
      (fun n zc havailable omega h => h havailable a)

end Paper
