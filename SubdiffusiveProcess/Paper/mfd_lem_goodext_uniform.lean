module

public import SubdiffusiveProcess.Paper.lem_goodext
public import SubdiffusiveProcess.Paper.represented_estimates_actual_model
public import SubdiffusiveProcess.Paper.goodext_controlled_response_recovery
public import SubdiffusiveProcess.Paper.candidate_source_compact_bank
public import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
public import SubdiffusiveProcess.Paper.goodext_represented_cell_growth_bank
public import SubdiffusiveProcess.Geometry.BoundaryPartitions
public import SubdiffusiveProcess.Sobolev.HarmonicSmoothGrowth

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

theorem aux_mfd_lem_goodext_root_controls_with_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (N : ℕ → ℕ)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (_hEnv : ∀ n, Measurable (env n))
        (_hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
        (Jbank : Type) [Countable Jbank]
        (Xbank : Jbank → ℕ → Omega → ℝ) (Bbank : Jbank → ℝ≥0)
        (_hExtraMem : ∀ j n, MemLp (Xbank j n) 1 P)
        (_hExtraNorm : ∀ j n, eLpNorm (Xbank j n) 1 P ≤ Bbank j),
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        (∀ q : TriadicGridLabel d,
          ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (triadicGridCell z r hr q),
            ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (triadicGridCell z r hr q : Set (SpatialCoordinates d))] phi) →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
              ContinuousOn V (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) ∧
              ((dirichletMinimizer
                (killedResponseSpace (centeredCube_killedPoincare (triadicGridCenter z r q)
                  (triadicGridSide_pos hr q)))
                (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
                  (triadicGridCenter z r q) (triadicGridSide_pos hr q)) b).val.1 :
                    SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (triadicGridCell z r hr q : Set (SpatialCoordinates d))] V ∧
              IsHolderOn alpha (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) V ∧
              cAlphaNorm alpha (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) V ≤ C) ∧
        ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |Xbank j (seq n) om| ≤ B := by
  classical
  obtain ⟨deltaGrowth, hdeltaGrowth, hGrowthAll⟩ :=
    goodext_represented_cell_growth_bank d hd I Pin X W Cp Sob t alpha
      ht htd ha ha1
  obtain ⟨deltaControls, hdeltaControls, hControlsAll⟩ :=
    goodext_represented_controls_with_bank d hd I Pin X W Cp Sob Interp t alpha
      ht htd ha ha1
  refine ⟨min deltaControls deltaGrowth,
    lt_min hdeltaControls hdeltaGrowth, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N Omega _ P _ env hEnv hLaw Jbank _ Xbank Bbank hExtraMem hExtraNorm
  have hdeltaControls' : M.delta ≤ deltaControls :=
    hdelta.trans (min_le_left _ _)
  have hdeltaGrowth' : M.delta ≤ deltaGrowth :=
    hdelta.trans (min_le_right _ _)
  let rootLabelCountable : Countable (TriadicGridLabel d) := by
    unfold TriadicGridLabel
    infer_instance
  let rootCenter : TriadicGridLabel d → SpatialCoordinates d :=
    fun q => triadicGridCenter z r q
  let rootSide : TriadicGridLabel d → ℝ :=
    fun q => triadicGridSide r q
  have hrootSide : ∀ q, 0 < rootSide q := by
    intro q
    dsimp only [rootSide]
    exact triadicGridSide_pos hr q
  obtain ⟨growthBank, growthBounds, hgrowthMem, hgrowthNorm, hgrowthAll⟩ :=
    hGrowthAll M Rm Sreg It H hIR hdeltaGrowth'
      (TriadicGridLabel d) rootCenter rootSide hrootSide N Omega P env hEnv hLaw
  let bank : (TriadicGridLabel d ⊕ Jbank) → ℕ → Omega → ℝ :=
    Sum.elim growthBank Xbank
  let bounds : (TriadicGridLabel d ⊕ Jbank) → ℝ≥0 :=
    Sum.elim growthBounds Bbank
  have hmem : ∀ j n, MemLp (bank j n) 1 P := by
    intro j n
    cases j with
    | inl q => exact hgrowthMem q n
    | inr q => exact hExtraMem q n
  have hnorm : ∀ j n, eLpNorm (bank j n) 1 P ≤ bounds j := by
    intro j n
    cases j with
    | inl q => exact hgrowthNorm q n
    | inr q => exact hExtraNorm q n
  have hControls :=
    hControlsAll M Rm Sreg It H hIR hdeltaControls' z r hr S hS N
      Omega P env hEnv hLaw (TriadicGridLabel d ⊕ Jbank) bank bounds hmem hnorm
  filter_upwards [hControls, hgrowthAll] with om hControlsOm hgrowthOm
  obtain ⟨seq, hseq, hAmbient, hAllCell, hCaps⟩ := hControlsOm
  refine ⟨seq, hseq, hAmbient, hAllCell, ?_, fun j => hCaps (Sum.inr j)⟩
  intro q phi hphi b hb
  obtain ⟨Kgrowth, hKgrowth, hGrowthCapRaw⟩ := hCaps (Sum.inl q)
  have hGrowthCap : ∀ n, |growthBank q (seq n) om| ≤ Kgrowth := by
    intro n
    exact hGrowthCapRaw n
  have hGrowthUniform : ∀ n (psi : SpatialCoordinates d → ℝ) (Cpsi : ℝ),
      ContDiff ℝ 2 psi → c2Norm (closedCube (triadicGridCenter z r q)
        (triadicGridSide r q) (triadicGridSide_pos hr q)) psi ≤ Cpsi →
      ∀ b' u' : weakSobolevGraph
          (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
            (triadicGridSide_pos hr q)),
        ((b'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
            (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))] psi) →
        SolvesDirichlet
          (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
            (triadicGridCenter z r q) (triadicGridSide_pos hr q))
          (fun _ => 0) b' u' →
        ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
          ((u'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
              (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))] V) ∧
          IsHolderOn alpha (closure (centeredCube (triadicGridCenter z r q)
            (triadicGridSide r q) (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube (triadicGridCenter z r q)
            (triadicGridSide r q) (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))) V ≤
            Kgrowth * Cpsi := by
    intro n psi Cpsi hpsi hCpsi b' u' hb' hu'
    have hpsi2 : ContDiff ℝ 2 psi := hpsi
    obtain ⟨V, hVcont, hVae, hVholder, hVnorm⟩ :=
      hgrowthOm q (seq n) psi Cpsi hpsi2 hCpsi b' u' hb' hu'
    have hCpsi0 : 0 ≤ Cpsi :=
      (aux_prop_growth_c2Norm_nonneg _ _).trans hCpsi
    have hbankBound : growthBank q (seq n) om ≤ Kgrowth :=
      (le_abs_self _).trans (hGrowthCap n)
    refine ⟨V, hVcont, hVae, hVholder, ?_⟩
    exact hVnorm.trans (mul_le_mul_of_nonneg_right hbankBound hCpsi0)
  exact smooth_minimizer_regularity_of_growth
    (triadicGridCenter z r q) (triadicGridSide r q) (triadicGridSide_pos hr q)
    (centeredCube_killedPoincare (triadicGridCenter z r q) (triadicGridSide_pos hr q))
    (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
      (triadicGridCenter z r q) (triadicGridSide_pos hr q))
    alpha Kgrowth hKgrowth hGrowthUniform phi hphi b hb

theorem aux_mfd_lem_goodext_tolerance_uniform_on_coupling
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (_Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (etaGrid : ℝ) (hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (moment : ℝ) (_hmoment : 1 ≤ moment)
    :
    ∃ Cbound eps0 lam0 delta0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (epshom : ℝ), 0 < epshom → epshom ≤ 1 →
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (_hfield_meas : Measurable field)
        (_hfield_law : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : Fin 2 → ℕ → Ω → BilateralField d)
        (_henv_meas : ∀ (a : Fin 2) (n : ℕ), Measurable (env a n))
        (_henv_law : ∀ (a : Fin 2) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (_hEnvConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (_hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (_hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre :
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (_hepsSmall : eps ≤ eps0)
        (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (_hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
        (_hlamSmall : lambdaDet ≤ lam0)
        (_hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (phi : Fin 2 → ℕ → ℕ)
        (_hphi : ∀ (a : Fin 2), StrictMono (phi a))
        (prefixZLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (prefixDLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (ellLoLim ellHiLim : Fin 2 → (Enl × Shift) → Ω → ℝ)
        (AE_Lim : Fin 2 → (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cmp → Ω → ℝ)
        (_hPrefixZLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixZ (phi a n) U D code (env a n omega)) atTop
            (prefixZLim a U D code))
        (_hPrefixDLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixD (phi a n) U D code (env a n omega)) atTop
            (prefixDLim a U D code))
        (_hEllLoLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellLoN (phi a n) U (env a n omega)) atTop
            (ellLoLim a U))
        (_hEllHiLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellHiN (phi a n) U (env a n omega)) atTop
            (ellHiLim a U))
        (_hAELim : ∀ (a : Fin 2) (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure P
            (fun n omega => AEN (phi a n) U (env a n omega) i j) atTop
            (fun omega => AE_Lim a U omega i j))
        (_hErrLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => errN (phi a n) c (env a n omega)) atTop
            (errLim a c))
        (_hRatioLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => ratioN (phi a n) c (env a n omega)) atTop
            (ratioLim a c))
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (_hQtri : ∃ m : ℤ, Qside = (3 : ℝ) ^ m)
        (_hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (_hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (_hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (sRef : Fin 2 → Ω → ℝ)
        (sCmp : Fin 2 → Cmp → Ω → ℝ)
        (_hsRef : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            0 < sRef a omega ∧
            Tendsto (fun n => sN (phi a n) (k : ℤ) z (env a n omega)) atTop
              (𝓝 (sRef a omega)))
        (_hsCmp : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P, ∀ c : Cmp,
            0 < sCmp a c omega ∧
            Tendsto (fun n => sN (phi a n) (cmpLevel c) (cmpCentre c) (env a n omega))
              atTop (𝓝 (sCmp a c omega)))
        (eRef : Fin 2 → ℕ → ℝ)
        (_heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (_heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (_hsRef_eq : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            sRef a omega = eRef a k *
              Real.exp (H (field omega) z +
                ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set Ω := fun a =>
        {omega |
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
              prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
          (∀ U : Enl × Shift,
            cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
          errLim a chosen omega ≤ epshom * cdet ∧
          (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂P,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))
  := by
  have halpha' : alpha ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [halpha.1], halpha.2⟩
  obtain ⟨Cbase, hCGE⟩ := candidate_good_estimates.{0} d hd I _X _Sob Pin
    _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha' hbeta hs hsSmall
    hsigma_eq hsigma hcell
  let tGrowth : ℝ := (d : ℝ) - 1 / 2
  have htGrowthLower : (d : ℝ) - 1 < tGrowth := by
    dsimp [tGrowth]
    linarith only [show (0 : ℝ) < 1 / 2 by norm_num]
  have htGrowthUpper : tGrowth < (d : ℝ) := by
    dsimp [tGrowth]
    linarith only [show (0 : ℝ) < 1 / 2 by norm_num]
  obtain ⟨Ctrace, deltaTrace, hCtrace, hdeltaTrace, hSharpTrace⟩ :=
    goodext_represented_local_trace d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) tGrowth alpha beta
      htGrowthLower htGrowthUpper (by linarith only [halpha.1]) halpha.2 hbeta
  obtain ⟨deltaRep, hdeltaRep, hGlobalSource⟩ :=
    candidate_good_estimates_trace_support d hd I Pin _X _MeyersMorrey Cp _Sob alpha
      ⟨by linarith only [halpha.1], halpha.2⟩
  obtain ⟨deltaRoot, hdeltaRoot, hRootTraceControls⟩ :=
    aux_mfd_lem_goodext_root_controls_with_bank d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) tGrowth alpha
      htGrowthLower htGrowthUpper (by linarith only [halpha.1]) halpha.2
  let etaCat : ℝ := min etaGrid (alpha - 1 / 2)
  have hetaCat : 0 < etaCat := lt_min hetaGrid (by linarith only [hbeta.1, hbetaLtAlpha])
  have hetaCatGrid : etaCat ≤ etaGrid := min_le_left _ _
  have hCatExponent : 1 + etaCat < 2 * alpha := by
    have hsmall : etaCat ≤ alpha - 1 / 2 := min_le_right _ _
    linarith only [hsmall, hbeta.1, hbetaLtAlpha]
  obtain ⟨deltaGrid, hdeltaGrid, hNativeGrid⟩ :=
    (lem_extension d hd I _X _Sob).2 etaCat 1 hetaCat le_rfl beta hbeta
  obtain ⟨eps0, lam0, deltaCGE, heps0, hlam0, hdeltaCGE, hCGEatOne⟩ :=
    hCGE.2 1 (by norm_num) (by norm_num)
  have hsigmaPos : 0 < sigma := hsigma.1
  let discount : ℝ := Homogenization.Book.Ch02.geometricDiscount sigma 2 /
    Homogenization.Book.Ch02.geometricDiscount 1 1
  have hdiscount : 0 < discount := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  let Kp : ℝ := Real.sqrt (Pin.C ^ 2 * 18 / (discount * cell * (3 : ℝ) ^ d))
  have hKp : 0 ≤ Kp := Real.sqrt_nonneg _
  have hCbase : 0 < Cbase := lt_of_lt_of_le zero_lt_one hCGE.1
  let Dtrace : ℝ := (Real.sqrt d) ^ (alpha - beta)
  let CeTrace : ℝ := 2 * Ctrace * cell⁻¹
  have hDtrace : 0 ≤ Dtrace := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hCeTrace : 0 ≤ CeTrace :=
    mul_nonneg (mul_nonneg (by norm_num) hCtrace.le) (inv_nonneg.mpr hcell.1.le)
  obtain ⟨Cbound, hCbound, hCbaseBound, hCminBound, hBudget⟩ :=
    exists_triadic_trace_energy_budget Cbase Kp CeTrace Dtrace Cbase
      hCbase.le hKp hCeTrace hDtrace
  let delta0 : ℝ := min (min 1 (min (min deltaCGE (min deltaTrace deltaRep)) deltaRoot)) deltaGrid
  have hdelta0 : 0 < delta0 :=
    lt_min (lt_min zero_lt_one (lt_min (lt_min hdeltaCGE (lt_min hdeltaTrace hdeltaRep)) hdeltaRoot)) hdeltaGrid
  refine ⟨Cbound, eps0, lam0, delta0, hCbound, heps0, hlam0, hdelta0, ?_⟩
  intro epshom hepshom hepshom_le cbuf k0 M Rm Sreg It H hMH Ω instΩ P instP field hfield_meas hfield_law env henv_meas henv_law hEnvConv k z qside hqside qcenter hqcenter Enl Shift Cmp instEnl instShift instCmp selfE selfShift
    qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre
    rootPos hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen
    observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive lambdaCut
    lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD
    hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim
    prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim
    hRatioLim Qcentre Qside hQside hQtri hRootsQ S hS GN hGN G hGE Form hE Gamma sRef sCmp hsRef hsCmp eRef heRef_pos
    heRef_lim hsRef_eq
  have hdisorderOld0 : M.delta ≤ min 1 (min (min deltaCGE (min deltaTrace deltaRep)) deltaRoot) :=
    hdisorder.trans (min_le_left _ _)
  have hdisorderGrid : M.delta ≤ deltaGrid := hdisorder.trans (min_le_right _ _)
  have hdisorderOne : M.delta ≤ 1 := hdisorderOld0.trans (min_le_left _ _)
  have hdisorderRoot : M.delta ≤ deltaRoot :=
    hdisorderOld0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisorderOld : M.delta ≤ min deltaCGE (min deltaTrace deltaRep) :=
    hdisorderOld0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdisorderTrace : M.delta ≤ deltaTrace :=
    hdisorderOld.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdisorderRep : M.delta ≤ deltaRep :=
    hdisorderOld.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdisorderCGE : M.delta ≤ deltaCGE := hdisorderOld.trans (min_le_left _ _)
  have htauOne : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ 1 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [h]
    have hdeltaSq : M.delta ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ M.shellPrefix.delta_pos.le zero_le_one).mpr hdisorderOne
    have hTau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 :=
      (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M).trans
        (mul_le_of_le_one_left (sq_nonneg _) hlog)
    simpa only [one_pow] using hTau.trans hdeltaSq
  have hCboundPos : 0 < Cbound := lt_of_lt_of_le zero_lt_one hCbound
  have hcdetCGE : cdet ≤ Cbase⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hCbase).2
    calc
      cdet * Cbase = Cbase * cdet := by ring
      _ ≤ Cbound * cdet := mul_le_mul_of_nonneg_right hCminBound hcdet.le
      _ ≤ Cbound * Cbound⁻¹ := mul_le_mul_of_nonneg_left hcdetSmall hCboundPos.le
      _ = 1 := mul_inv_cancel₀ hCboundPos.ne'
  have hEnvConv0 : ∀ᵐ om ∂P, ∀ a : PUnit,
      Tendsto (fun n => env 0 n om) atTop (𝓝 (field om)) :=
    hEnvConv.mono (fun om h a => h 0)
  have hCGEEvent := hCGEatOne cbuf k0 M Rm Sreg It H hMH Ω P field
    hfield_meas hfield_law (fun (_ : PUnit) => env 0)
    (fun (_ : PUnit) => henv_meas 0) (fun (_ : PUnit) => henv_law 0) hEnvConv0
    k z qside hqside qcenter hqcenter Enl Shift Cmp selfE selfShift qRoot hqRoot
    factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide
    rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre hcmpCentre
    cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre hObservationCentre
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetCGE hlamSmall hdisorderCGE prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
    sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN
    (phi 0) (hphi 0) (prefixZLim 0) (prefixDLim 0) (ellLoLim 0) (ellHiLim 0)
    (AE_Lim 0) (errLim 0) (ratioLim 0) (hPrefixZLim 0) (hPrefixDLim 0)
    (hEllLoLim 0) (hEllHiLim 0) (hAELim 0) (hErrLim 0) (hRatioLim 0)
    Qcentre Qside hQside hRootsQ S hS GN hGN (G 0) (hGE 0) (Form 0) (hE 0)
    (Gamma 0) (sRef 0) (sCmp 0) (hsRef 0) (hsCmp 0)
  have hGE0event : ∀ᵐ omega ∂P,
      Tendsto (fun n => GN (phi 0 n) (env 0 n omega)) atTop (𝓝 (G 0 omega)) := hGE 0
  have hGE1event : ∀ᵐ omega ∂P,
      Tendsto (fun n => GN (phi 1 n) (env 1 n omega)) atTop (𝓝 (G 1 omega)) := hGE 1
  obtain ⟨Krep1, Crep1, hCrep1, hKrepMem1, hKrepNorm1, _, hRepSource1⟩ :=
    hGlobalSource M Rm Sreg It H hMH hdisorderRep Qcentre Qside hQside
  let CrepNN : ℝ≥0 := ⟨Crep1, hCrep1⟩
  have hCrepNN : (CrepNN : ℝ≥0∞) = ENNReal.ofReal Crep1 :=
    (ENNReal.ofReal_eq_coe_nnreal hCrep1).symm
  have hPadLevel : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
    rw [hrootLevel, hpad]
    norm_num
  have hPadCentre : rootCentre (padE, selfShift) = z := by
    rw [hrootCentre, hshift, smul_zero, add_zero, hqcenter]
  have hPadSide : rootSide (padE, selfShift) = (3 : ℝ) ^ (-((k : ℤ) - 1)) := by
    rw [hrootSide, hPadLevel]
  have hPadObservation : observationCentre (padE, selfShift) k0
      (Sum.inr (padE, selfShift)) = z := by
    rw [hObservationCentre]
    exact hPadCentre
  have hPadPrefix : ∀ N xi,
      prefixD N (padE, selfShift) k0 (Sum.inr (padE, selfShift)) xi =
        if (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ)) ((k : ℤ) - 1 + (k0 : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z) xi).toReal else 0
        else 0 := by
    intro N xi
    rw [hPrefixD, hPadLevel, hPadObservation]
  have hFinitePad : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) →
        Draw N ((N : ℤ) - ((k : ℤ) - 1)).toNat (((3 : ℝ) ^ N) • z) xi ≠ ⊤ := by
    filter_upwards [hFiniteScoreGuard] with xi hxi
    intro N hN
    have h := hxi N (padE, selfShift) k0 (Sum.inr (padE, selfShift))
    rw [hPadLevel, hPadObservation] at h
    exact h hN ((k : ℤ) - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hNormPad : TendstoInMeasure P
      (fun n om => I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
        (cutoffPositiveCoefficient M H (env 0 n om) (phi 0 n) z (by positivity))
        z ((3 : ℝ) ^ (-((k : ℤ) - 1))) sigma 2 /
          sN (phi 0 n) ((k : ℤ) - 1) z (env 0 n om)) atTop (ellLoLim 0 (padE, selfShift)) := by
    have hEq : (fun n om => ellLoN (phi 0 n) (padE, selfShift) (env 0 n om)) =
        (fun n om => I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
          (cutoffPositiveCoefficient M H (env 0 n om) (phi 0 n) z (by positivity))
          z ((3 : ℝ) ^ (-((k : ℤ) - 1))) sigma 2 /
            sN (phi 0 n) ((k : ℤ) - 1) z (env 0 n om)) := by
      funext n om
      rw [hEllLoN, aux_lem_goodext_lower_coefficient_congr I M H
        (env 0 n om) (phi 0 n) _ _ _ _ _ (by positivity) hPadCentre hPadSide sigma,
        hPadLevel, hPadCentre]
    rw [← hEq]
    exact hEllLoLim 0 (padE, selfShift)
  obtain ⟨rhoPad, hRhoPad, hLowerPad⟩ := goodext_represented_padded_lower
    I M Rm H k k0 cbuf z s eps sigma cell (lambdaLim * (k0 : ℝ)) hs hcell.1
    eta hEta F Praw Rraw Draw Z rawGood hPrimitive
    (fun N xi => prefixD N (padE, selfShift) k0 (Sum.inr (padE, selfShift)) xi)
    hPadPrefix hFinitePad sN hsN P (phi 0) (hphi 0) (env 0) (henv_meas 0) (henv_law 0)
    (prefixDLim 0 (padE, selfShift) k0 (Sum.inr (padE, selfShift)))
    (ellLoLim 0 (padE, selfShift))
    (hPrefixDLim 0 (padE, selfShift) k0 (Sum.inr (padE, selfShift))) hNormPad
  have hFormBank (a : Fin 2) := goodext_represented_source_representative
    (chaosSampleLaw M).toMeasure P (env a) (henv_meas a) (henv_law a) (phi a)
    Qcentre Qside hQside alpha ⟨hbeta.1.trans hbetaLtAlpha, halpha.2⟩ S hS
    (fun n xi => cutoffPositiveCoefficient M H xi n Qcentre hQside) GN hGN
    (G a) (hGE a) Krep1 CrepNN hKrepMem1
    (fun n => (hKrepNorm1 n).trans_eq hCrepNN.symm) hRepSource1
  have hSourceControlEvent := hRootTraceControls M Rm Sreg It H hMH hdisorderRoot
    Qcentre Qside hQside S hS (fun n => phi 0 (rhoPad n)) Ω P
    (fun n => env 0 (rhoPad n)) (fun n => henv_meas 0 (rhoPad n))
    (fun n => henv_law 0 (rhoPad n))
    PUnit (fun _ n om => Krep1 (phi 0 (rhoPad n)) (env 0 (rhoPad n) om))
    (fun _ => CrepNN)
    (fun _ n => (hKrepMem1 _).comp_measurePreserving
      ⟨henv_meas 0 (rhoPad n), henv_law 0 (rhoPad n)⟩)
    (by
      intro j n
      change eLpNorm (Krep1 (phi 0 (rhoPad n)) ∘ env 0 (rhoPad n)) 1 P ≤ CrepNN
      rw [eLpNorm_comp_measurePreserving (hKrepMem1 _).aestronglyMeasurable
        (⟨henv_meas 0 (rhoPad n), henv_law 0 (rhoPad n)⟩ :
          MeasurePreserving (env 0 (rhoPad n)) P (chaosSampleLaw M).toMeasure)]
      exact (hKrepNorm1 _).trans_eq hCrepNN.symm)
  obtain ⟨KgridNative, CgridNative, hKgridMem, hKgridNorm, hGridNative⟩ :=
    hNativeGrid M Rm H hMH hdisorderGrid Qcentre Qside hQside 1 (fun _ => Qcentre)
  let Bgrid : ℝ≥0 := CgridNative.toNNReal
  have hGridNorm : ∀ n, eLpNorm (KgridNative n) 1 (chaosSampleLaw M).toMeasure ≤ Bgrid := by
    intro n
    have h : eLpNorm (KgridNative n) 1 (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal CgridNative := by
      simpa only [ENNReal.ofReal_one] using hKgridNorm n
    exact h.trans_eq (show ENNReal.ofReal CgridNative = (Bgrid : ℝ≥0∞) from rfl)
  have hContinuousFormEvent (a : Fin 2) : ∀ᵐ om ∂P,
      ∀ fL2 : DomainL2 (centeredCube Qcentre Qside hQside),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
          (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] fc) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
          (G a om fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U ∧
          ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0 := by
    filter_upwards [hFormBank a] with om hBank
    intro fL2 hfL2
    obtain ⟨fc, hfc, _, _, hfcAE⟩ := hfL2
    obtain ⟨U, hUc, hUrep, hUzero, _⟩ := hBank fc hfc fL2 hfcAE
    exact ⟨U, hUc, hUrep, hUzero⟩
  have hRootTraceEvent := hRootTraceControls M Rm Sreg It H hMH hdisorderRoot
    Qcentre Qside hQside S hS (phi 1) Ω P (env 1) (henv_meas 1) (henv_law 1)
    PUnit (fun _ n om => KgridNative (phi 1 n) (env 1 n om)) (fun _ => Bgrid)
    (fun _ n => by
      have hm : MemLp (KgridNative (phi 1 n)) 1 (chaosSampleLaw M).toMeasure := by
        simpa only [ENNReal.ofReal_one] using hKgridMem (phi 1 n)
      exact hm.comp_measurePreserving
          (⟨henv_meas 1 n, henv_law 1 n⟩ :
            MeasurePreserving (env 1 n) P (chaosSampleLaw M).toMeasure))
    (by
      intro j n
      change eLpNorm (KgridNative (phi 1 n) ∘ env 1 n) 1 P ≤ Bgrid
      have hm : MemLp (KgridNative (phi 1 n)) 1 (chaosSampleLaw M).toMeasure := by
        simpa only [ENNReal.ofReal_one] using hKgridMem (phi 1 n)
      rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
        (⟨henv_meas 1 n, henv_law 1 n⟩ :
          MeasurePreserving (env 1 n) P (chaosSampleLaw M).toMeasure)]
      exact hGridNorm (phi 1 n))
  have hLevelSelf : rootLevel qRoot = (k : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]
    simp only [Nat.cast_zero, sub_zero]
  have hSideSelf : rootSide qRoot = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hrootSide, hLevelSelf]
  have hCentreSelf : rootCentre qRoot = z := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero, hqcenter]
  have hNorm1 : TendstoInMeasure P
      (fun n om => I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H (env 1 n om) (phi 1 n) z (by positivity))
        z ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 /
          sN (phi 1 n) (k : ℤ) z (env 1 n om)) atTop (ellHiLim 1 qRoot) := by
    have hEq : (fun n om => ellHiN (phi 1 n) qRoot (env 1 n om)) =
        (fun n om => I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
          (cutoffPositiveCoefficient M H (env 1 n om) (phi 1 n) z (by positivity))
          z ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 /
            sN (phi 1 n) (k : ℤ) z (env 1 n om)) := by
      funext n om
      rw [hEllHiN, aux_goodext_represented_local_trace_coefficient_congr I M H
        (env 1 n om) (phi 1 n) _ _ _ _ _ (by positivity) sigma ((beta - 1 / 2) / 4)
        hCentreSelf hSideSelf hsigma_eq, hLevelSelf, hCentreSelf]
    rw [← hEq]
    exact hEllHiLim 1 qRoot
  have hSharpEvent := hSharpTrace M Rm Sreg It H hMH hdisorderTrace
    Qcentre Qside hQside S hS k z (phi 1) (hphi 1) Ω P (env 1)
    (henv_meas 1) (henv_law 1) GN hGN (G 1) (hGE 1) (Form 1) (hE 1) (Gamma 1)
    (hContinuousFormEvent 1) (fun n om => sN (phi 1 n) (k : ℤ) z (env 1 n om))
    (sRef 1) (ellHiLim 1 qRoot) (hsRef 1) hNorm1 cell⁻¹ (inv_pos.mpr hcell.1)
  have hSourceRawEnv := ae_all_iff.mpr (fun n =>
    ae_of_ae_map (henv_meas 0 n).aemeasurable
      (by rw [henv_law 0 n]; exact hRepSource1))
  have hGridRawEnv := ae_all_iff.mpr (fun n =>
    ae_of_ae_map (henv_meas 1 n).aemeasurable
      (by rw [henv_law 1 n]; exact hGridNative))
  filter_upwards [hCGEEvent, hGE0event, hGE1event, hSharpEvent,
      hRootTraceEvent, hContinuousFormEvent 0, hContinuousFormEvent 1,
      hSourceControlEvent, hSourceRawEnv, hGridRawEnv, hLowerPad,
      hsRef 0, hsRef 1, hsRef_eq 0, hsRef_eq 1] with
    omega hCGE0 hGE0 hGE1 hSharp1 hRootTrace1 hContinuousForm0 hContinuousForm1
      hSourceControl hSourceRaw hGridRaw hLowerPad hs0 hs1 hsEq0 hsEq1
  obtain ⟨seqSource, hSeqSource, ⟨ASource⟩, hSourceCells, _hSourceReg, hSourceCaps⟩ := hSourceControl
  obtain ⟨Ksource, hKsource, hSourceCap⟩ := hSourceCaps PUnit.unit
  let baseSource : ℕ → ℕ := rhoPad ∘ seqSource
  have hBaseSource : StrictMono baseSource := hRhoPad.comp hSeqSource
  have hGamma0 := goodext_controlled_response_recovery hd Qcentre Qside hQside S hS
    (fun n => cutoffPositiveCoefficient M H (env 0 (baseSource n) omega) (phi 0 (baseSource n)) Qcentre hQside)
    ASource (fun n => cutoffCoefficient M H (env 0 (baseSource n) omega) (phi 0 (baseSource n)))
    (fun n => cutoffCoefficient_continuous M H (env 0 (baseSource n) omega) (phi 0 (baseSource n)))
    (fun n => by
      obtain ⟨lam, Lam, hlam, hb⟩ := cutoffCoefficient_closedCube_bounds M H (env 0 (baseSource n) omega)
        (phi 0 (baseSource n)) Qcentre hQside
      exact ⟨lam, Lam, hlam, fun x hx => hb x (Metric.ball_subset_closedBall hx)⟩)
    (fun n => (cutoffPositiveCoefficient_representative M H (env 0 (baseSource n) omega)
      (phi 0 (baseSource n)) Qcentre hQside).2.2.2)
    tGrowth alpha halpha'.1 hSourceCells
    (fun n => GN (phi 0 (baseSource n)) (env 0 (baseSource n) omega)) (G 0 omega)
    (fun n f => hGN _ _ f) (hGE0.comp hBaseSource.tendsto_atTop)
    (Form 0 omega) (hE 0 omega) hContinuousForm0 (Gamma 0 omega)
  have hG0dom : ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      G 0 omega f ∈ (Form 0 omega).domain := by
    apply aux_lem_goodext_limit_range_mem_domain
      S
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env 0 n omega) (phi 0 n)
        Qcentre hQside)
      (fun n => GN (phi 0 n) (env 0 n omega)) (G 0 omega) (Form 0 omega)
    · intro n f
      exact hGN (phi 0 n) (env 0 n omega) f
    · exact hGE0
    · exact hE 0 omega
  have hG1dom : ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      G 1 omega f ∈ (Form 1 omega).domain := by
    apply aux_lem_goodext_limit_range_mem_domain
      S
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env 1 n omega) (phi 1 n)
        Qcentre hQside)
      (fun n => GN (phi 1 n) (env 1 n omega)) (G 1 omega) (Form 1 omega)
    · intro n f
      exact hGN (phi 1 n) (env 1 n omega) f
    · exact hGE1
    · exact hE 1 omega
  have hSourceTraceClass := aux_lem_goodext_source_trace_class
    Qcentre Qside hQside alpha beta hbetaLtAlpha
  show
      (let Q := centeredCube Qcentre Qside hQside
       let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
       let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
       let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
       let Good : Fin 2 → Set Ω := fun a =>
         {omega |
           (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
             ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
               prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
               prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
             cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
           errLim a chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
       let L : ℝ := (3 : ℝ) ^ H1
       let unitClosed : Set (SpatialCoordinates d) :=
         closedCube (0 : SpatialCoordinates d) 1 one_pos
       let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
           fun r' z' b =>
             {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ (Form 1 omega).domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
               e = ((Gamma 1 omega).measure v
                 (Metric.ball z' (r' / 2))).toReal}
         let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
           fun r' z' b => sInf (responseSet r' z' b)
         (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
           ∀ (fL2 : DomainL2 Q),
             ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
               (Q : Set (SpatialCoordinates d))] f) →
           let u := G 0 omega fL2
           let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
           ∃ U : SpatialCoordinates d → ℝ,
             ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
             ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
               (Q : Set (SpatialCoordinates d))] U) ∧
             (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
             _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
             ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
               ∀ (zP : SpatialCoordinates d)
                 (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                 z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                 Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                 Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                 let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                 let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                 ∃ cq : ℝ,
                   _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                   _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                     Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                       Real.sqrt nuP +
                     Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                   (responseSet r z U).Nonempty ∧
                   IsGLB (responseSet r z U) (responseF r z U) ∧
                   responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                     (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
             (∃ K : ℝ, 0 ≤ K ∧
               ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                 Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                   (responseSet r' z' U).Nonempty ∧
                   IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                   responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid))))
  intro Q r q Ctotal Good L unitClosed responseSet responseF f hf fL2 hfL2
  let fsup : ℝ := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
  have hfsup : 0 ≤ fsup := by
    apply Real.sSup_nonneg
    rintro v ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hfbdd : BddAbove {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|} := by
    obtain ⟨B, hB⟩ :=
      (centeredCube_isBounded Qcentre hQside).isCompact_closure.exists_bound_of_continuousOn
        hf.continuous.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs] using hB x hx
  have hfbound : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |f x| ≤ fsup :=
    ae_restrict_of_forall_mem Q.isOpen.measurableSet
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure hx, rfl⟩)
  obtain ⟨U, ns, UN, hns, hUc, hUr, hUb, hUh, hUniform, hUN⟩ :=
    candidate_source_compact_bank Qcentre Qside hQside alpha
      ⟨hbeta.1.trans hbetaLtAlpha, halpha.2⟩ S hS
      (fun n => cutoffPositiveCoefficient M H (env 0 (baseSource n) omega) (phi 0 (baseSource n)) Qcentre hQside)
      (fun n => GN (phi 0 (baseSource n)) (env 0 (baseSource n) omega)) (fun n f => hGN _ _ f)
      (G 0 omega) (hGE0.comp hBaseSource.tendsto_atTop) f fL2 hfL2
      (Ksource * fsup) (mul_nonneg hKsource hfsup)
      (by
        intro n u hsolve
        obtain ⟨V, hVc, hVr, hVb, hVh, hVnorm⟩ :=
          hSourceRaw (baseSource n) (phi 0 (baseSource n)) f fsup hf hfsup hfbound u hsolve
        refine ⟨V, hVc, hVr, hVb, hVh, hVnorm.trans ?_⟩
        exact mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hSourceCap n)) hfsup)
  refine ⟨U, hUc, hUr, hUb, hUh, ?_, ?_⟩
  · intro hGood zP idx hzP hPadParent hParentQ
    have hr : 0 < r := by dsimp only [r]; positivity
    have h3qQ : Metric.ball z (3 * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) :=
      Metric.ball_subset_closedBall.trans (hPadParent.trans hParentQ)
    have hqQ : q ⊆ (Q : Set (SpatialCoordinates d)) :=
      (Metric.ball_subset_ball (by linarith only [hr.le] : r / 2 ≤ 3 * r / 2)).trans h3qQ
    have hGoodCGE := hCGE0 ⟨hGood.1.1, hGood.1.2.1, ?_, hGood.1.2.2.2⟩
    swap
    · exact hGood.1.2.2.1.trans (mul_le_mul_of_nonneg_right hepshom_le hcdet.le)
    obtain ⟨Ucge, hcgeC, hcgeRep, hcge0, hcgeHolder, ⟨cq, hcgeNorm⟩, hcgeHarm⟩ :=
      hGoodCGE.1 f hf fL2 hfL2
    have hSourceBound := goodext_source_bound_transport Q z r alpha _ (sRef 0 omega) fsup cq hr
      U Ucge (G 0 omega fL2) hcgeC hcgeRep hUc hUr hUh h3qQ hcgeNorm
    have hPadPower : (3 : ℝ) ^ (-((k : ℤ) - 1)) = 3 * r := by
      change (3 : ℝ) ^ (-((k : ℤ) - 1)) = 3 * (3 : ℝ) ^ (-(k : ℤ))
      rw [show -((k : ℤ) - 1) = (1 : ℤ) + -(k : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    let rr : ℕ → ℕ := baseSource ∘ ns
    have hrr : StrictMono rr := hBaseSource.comp hns
    have hSourcePos (n : ℕ) : 0 < sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega) := by
      rw [hsN]
      split_ifs
      · exact aux_in_deterministic_onestep_sref_pos M H _ _ _ _
      · norm_num
    have hPadLowerRaw := (hSeqSource.comp hns).tendsto_atTop.eventually
      (hLowerPad (hGood.1.2.1 (padE, selfShift)).1
        (hGood.1.1 (padE, selfShift) k0 le_rfl (Sum.inr (padE, selfShift))).2)
    have hPadLower : ∀ᶠ n in atTop,
        (cell / (2 * Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P + 2 * (lambdaLim * (k0 : ℝ))))) *
          sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega) ≤
        I.lam z (3 * r) (by positivity)
          (cutoffPositiveCoefficient M H (env 0 (rr n) omega) (phi 0 (rr n)) z (by positivity))
          z (3 * r) sigma 2 := by
      filter_upwards [hPadLowerRaw] with n hn
      simp only [Function.comp_apply] at hn
      rw [aux_lem_goodext_lower_coefficient_congr I M H
        (env 0 (rhoPad (seqSource (ns n))) omega) (phi 0 (rhoPad (seqSource (ns n)))) z z
        ((3 : ℝ) ^ (-((k : ℤ) - 1))) (3 * r) (by positivity)
        (show 0 < 3 * r by positivity) rfl hPadPower sigma] at hn
      exact hn
    let tauBudget : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P + 2 * (lambdaLim * (k0 : ℝ))
    let nu := (Gamma 0 omega).measure (G 0 omega fL2)
    have hParentOsc := goodext_padded_oscillation hd I Pin M H Qcentre Qside hQside S
      (fun n => env 0 (rr n) omega) (fun n => phi 0 (rr n)) GN hGN fL2 U UN
      (fun n => (hUN n).2) hUniform (G 0 omega) hUr z r hr h3qQ sigma cell tauBudget hsigma.1
      (by rw [hsigma_eq]; linarith only [hbeta.2]) hcell.1
      (fun n => sN (phi 0 (rr n)) (k : ℤ) z (env 0 (rr n) omega)) (sRef 0 omega)
      hSourcePos hs0.1 (hs0.2.comp hrr.tendsto_atTop) hPadLower (Form 0 omega) (Gamma 0 omega)
      (hG0dom fL2)
      (fun chi hc hcompact => (hGamma0 fL2 chi hc hcompact).comp hns.tendsto_atTop)
      zP (L * r) hPadParent
    have htime : lambdaLim * (k0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by
      have hll : lambdaLim ≤ 1 := hThresholds.2.2.1.le.trans hThresholds.2.2.2.le
      have h := mul_le_mul_of_nonneg_right hll (Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0)
      linarith only [h, (Nat.cast_nonneg cbuf : (0 : ℝ) ≤ cbuf)]
    have hCostBudget := hBudget ((k0 : ℝ) + (cbuf : ℝ))
      (_root_.SubdiffusiveProcess.Model.tauSq M.P) (lambdaLim * (k0 : ℝ))
      (by positivity) htauOne htime
    have hUqBoundary : ContinuousOn U (frontier q) :=
      hUc.mono (frontier_subset_closure.trans (closure_mono hqQ))
    have hTraceExtension : IsHolderOn beta (frontier q) U →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ (Form 1 omega).domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ frontier q, V x = U x) ∧
          ((Gamma 1 omega).measure v q).toReal ≤
            CeTrace * (sRef 1 omega) * r ^ ((d : ℝ) - 2) *
              (r ^ beta * holderSeminorm beta (frontier q) U) ^ 2 := by
      intro hBetaTrace
      obtain ⟨v, V, hv, hVc, hVrep, hVtrace, hVe⟩ :=
        hSharp1 (hGood.2.2.1 qRoot).2 h3qQ U hUqBoundary hBetaTrace
      refine ⟨v, V, hv, hVc, hVrep, hVtrace, hVe.trans_eq ?_⟩
      dsimp only [CeTrace]
      ring
    have hRatioRef : sRef 1 omega / sRef 0 omega = eRef 1 k / eRef 0 k := by
      rw [hsEq1, hsEq0]
      exact aux_lem_goodext_sRef_ratio_eRef_ratio _ _ _
        (heRef_pos 0 k).ne' (Real.exp_pos _).ne'
    exact goodext_good_cell_final (Gamma 1 omega)
      (closure (Q : Set (SpatialCoordinates d))) z r alpha beta (sRef 0 omega) (sRef 1 omega)
      (nu (Metric.ball zP (L * r / 2))).toReal fsup _ (eRef 0 k) (eRef 1 k)
      Cbase Kp tauBudget ((k0 : ℝ) + (cbuf : ℝ)) CeTrace Ctotal hr hbetaLtAlpha.le
      (by linarith only [hbeta.1]) hs0.1 hs1.1.le ENNReal.toReal_nonneg hfsup hCbase hKp
      hCeTrace hCostBudget U hUqBoundary hSourceBound hParentOsc hTraceExtension hRatioRef
  · obtain ⟨ellRoot, hQScale⟩ := hQtri
    obtain ⟨seqRoot, hSeqRoot, ⟨ARoot⟩, hRootCells, hRootReg, hRootCaps⟩ := hRootTrace1
    obtain ⟨Kgrid, hKgrid, hGridCap⟩ := hRootCaps PUnit.unit
    have hKgridCap : ∀ (n j : ℕ) (idx : Fin d → ℤ), j ≤ phi 1 (seqRoot n) →
        let wc : SpatialCoordinates d := fun a => Qcentre a + (3 : ℝ) ^ (-(j : ℤ)) * idx a
        let rc : ℝ := (3 : ℝ) ^ (-(j : ℤ))
        ∀ hc : 0 < rc, (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
        I.Lam wc rc hc (cutoffPositiveCoefficient M H (env 1 (seqRoot n) omega) (phi 1 (seqRoot n)) wc hc)
            wc rc ((beta - 1 / 2) / 4) 2 +
          (I.lam wc rc hc (cutoffPositiveCoefficient M H (env 1 (seqRoot n) omega) (phi 1 (seqRoot n)) wc hc)
            wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ Kgrid * rc ^ (-etaCat) := by
      intro n j idx hj wc rc hc hsub
      have hNative := hGridRaw (seqRoot n) (phi 1 (seqRoot n)) j 0 idx hj hsub
      have hSigma : ((beta - 1 / 2) / 4) ∈ Ioc (0 : ℝ) 1 := by
        constructor <;> linarith only [hbeta.1, hbeta.2]
      have hLocal := goodext_cutoff_ellipticity_locality I M H (env 1 (seqRoot n) omega)
        (phi 1 (seqRoot n)) Qcentre Qside hQside wc rc hc hsub
        ((beta - 1 / 2) / 4) hSigma
      rw [hLocal.1, hLocal.2] at hNative
      exact hNative.trans (mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (hGridCap n)) (Real.rpow_nonneg (by positivity) _))
    exact goodext_arbitrary_cell_response hd I _X _Sob M H Qcentre Qside hQside S hS
      (fun n => env 1 (seqRoot n) omega) (fun n => phi 1 (seqRoot n)) ((hphi 1).comp hSeqRoot)
      tGrowth alpha beta etaCat etaGrid (by linarith only [halpha.1]) hbeta hbetaLtAlpha.le
      hCatExponent hetaCatGrid ARoot hRootCells hRootReg GN hGN (G 1 omega)
      (hGE1.comp hSeqRoot.tendsto_atTop) (Form 1 omega) (hE 1 omega) hContinuousForm1
      (Gamma 1 omega) ellRoot hQScale Kgrid hKgrid
      hKgridCap U hUc hUh hUb


theorem mfd_lem_goodext_uniform
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (etaGrid : ℝ) (hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (hH1 : 0 < H1)
    (moment : ℝ) (hmoment : 1 ≤ moment)
    :
    ∃ Cbound : ℝ, 1 ≤ Cbound ∧
      ∀ (epshom : ℝ), 0 < epshom → epshom ≤ 1 →
      ∃ eps0 lam0 delta0 : ℝ, 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (_hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (_hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre :
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (_hepsSmall : eps ≤ eps0)
        (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (_hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
        (_hlamSmall : lambdaDet ≤ lam0)
        (_hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (phi : Fin 2 → ℕ → ℕ)
        (_hphi : ∀ (a : Fin 2), StrictMono (phi a))
        (prefixZLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixDLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (ellLoLim ellHiLim : Fin 2 → (Enl × Shift) → BilateralField d → ℝ)
        (AE_Lim : Fin 2 → (Enl × Shift) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cmp → BilateralField d → ℝ)
        (_hPrefixZLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => prefixZ (phi a n) U D code omega) atTop
            (prefixZLim a U D code))
        (_hPrefixDLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => prefixD (phi a n) U D code omega) atTop
            (prefixDLim a U D code))
        (_hEllLoLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ellLoN (phi a n) U omega) atTop
            (ellLoLim a U))
        (_hEllHiLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ellHiN (phi a n) U omega) atTop
            (ellHiLim a U))
        (_hAELim : ∀ (a : Fin 2) (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => AEN (phi a n) U omega i j) atTop
            (fun omega => AE_Lim a U omega i j))
        (_hErrLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => errN (phi a n) c omega) atTop
            (errLim a c))
        (_hRatioLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ratioN (phi a n) c omega) atTop
            (ratioLim a c))
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (_hQrat : ∀ i : Fin d, ∃ q : ℚ, Qcentre i = (q : ℝ))
        (_hQtri : ∃ m : ℤ, Qside = (3 : ℝ) ^ m)
        (_hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (_hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            Tendsto (fun n => GN (phi a n) omega) atTop (𝓝 (G a omega)))
        (Form : Fin 2 → BilateralField d → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (_hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (sRef : Fin 2 → BilateralField d → ℝ)
        (sCmp : Fin 2 → Cmp → BilateralField d → ℝ)
        (_hsRef : ∀ (a : Fin 2),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            0 < sRef a omega ∧
            Tendsto (fun n => sN (phi a n) (k : ℤ) z omega) atTop
              (𝓝 (sRef a omega)))
        (_hsCmp : ∀ (a : Fin 2),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ c : Cmp,
            0 < sCmp a c omega ∧
            Tendsto (fun n => sN (phi a n) (cmpLevel c) (cmpCentre c) omega)
              atTop (𝓝 (sCmp a c omega)))
        (eRef : Fin 2 → ℕ → ℝ)
        (_heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (_heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (_hsRef_eq : ∀ (a : Fin 2),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            sRef a omega = eRef a k *
              Real.exp (H omega z +
                ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set (BilateralField d) := fun a =>
        {omega |
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
              prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
          (∀ U : Enl × Shift,
            cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
          errLim a chosen omega ≤ epshom * cdet ∧
          (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))
  :=
 by
  obtain ⟨Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0, hApply⟩ :=
    aux_mfd_lem_goodext_tolerance_uniform_on_coupling d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
      alpha beta s sigma cell halpha hbeta hbetaLtAlpha hs hsSmall
      hsigma_eq hsigma hcell etaGrid hetaGrid H1 hH1 moment hmoment
  refine ⟨Cbound, hC, ?_⟩
  intro epshom hepshom hepshom_le
  refine ⟨eps0, lam0, delta0, he0, hl0, hd0, ?_⟩
  have hApplyTolerance := hApply epshom hepshom hepshom_le
  intros cbuf k0 M Rm Sreg It H hMH k z qside hqside qcenter hqcenter Enl Shift Cmp
    instEnl instShift instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
    shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos
    hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
    cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
    sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi
    prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim
    hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside
    hQrat hQtri hRootsQ S hS GN hGN G hGE Form hE Gamma sRef sCmp hsRef hsCmp eRef
    heRef_pos heRef_lim hsRef_eq
  exact hApplyTolerance cbuf k0 M Rm Sreg It H hMH (BilateralField d)
    (chaosSampleLaw M).toMeasure id measurable_id Measure.map_id
    (fun _ _ => id) (fun _ _ => measurable_id) (fun _ _ => Measure.map_id)
    (Eventually.of_forall (fun _ _ => tendsto_const_nhds))
    k z qside hqside qcenter hqcenter Enl Shift Cmp selfE selfShift qRoot hqRoot
    factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide
    rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre hcmpCentre
    cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre hObservationCentre
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN
    hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim prefixDLim
    ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim
    hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside hQtri hRootsQ
    S hS GN hGN G hGE Form hE Gamma sRef sCmp hsRef hsCmp eRef heRef_pos heRef_lim hsRef_eq


def aux_mfd_lem_goodext_comparison_on_pair
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (_Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell epshom : ℝ)
    (_halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (_hbetaLtAlpha : beta < alpha)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (_hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (_hepshom : 0 < epshom)
    (etaGrid : ℝ) (_hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (moment : ℝ) (_hmoment : 1 ≤ moment)
    (Cbound eps0 lam0 delta0 : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (env : Fin 2 → ℕ → Ω → BilateralField d)
    (phi : Fin 2 → ℕ → ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (_S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (G : Fin 2 → Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside)) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (_hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (_hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre :
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (_hepsSmall : eps ≤ eps0)
        (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (_hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
        (_hlamSmall : lambdaDet ≤ lam0)
        (_hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (prefixZLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (prefixDLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (ellLoLim ellHiLim : Fin 2 → (Enl × Shift) → Ω → ℝ)
        (AE_Lim : Fin 2 → (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cmp → Ω → ℝ)
        (_hPrefixZLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixZ (phi a n) U D code (env a n omega)) atTop
            (prefixZLim a U D code))
        (_hPrefixDLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixD (phi a n) U D code (env a n omega)) atTop
            (prefixDLim a U D code))
        (_hEllLoLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellLoN (phi a n) U (env a n omega)) atTop
            (ellLoLim a U))
        (_hEllHiLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellHiN (phi a n) U (env a n omega)) atTop
            (ellHiLim a U))
        (_hAELim : ∀ (a : Fin 2) (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure P
            (fun n omega => AEN (phi a n) U (env a n omega) i j) atTop
            (fun omega => AE_Lim a U omega i j))
        (_hErrLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => errN (phi a n) c (env a n omega)) atTop
            (errLim a c))
        (_hRatioLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => ratioN (phi a n) c (env a n omega)) atTop
            (ratioLim a c))
        (_hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (_hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (sRef : Fin 2 → Ω → ℝ)
        (sCmp : Fin 2 → Cmp → Ω → ℝ)
        (_hsRef : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            0 < sRef a omega ∧
            Tendsto (fun n => sN (phi a n) (k : ℤ) z (env a n omega)) atTop
              (𝓝 (sRef a omega)))
        (_hsCmp : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P, ∀ c : Cmp,
            0 < sCmp a c omega ∧
            Tendsto (fun n => sN (phi a n) (cmpLevel c) (cmpCentre c) (env a n omega))
              atTop (𝓝 (sCmp a c omega)))
        (eRef : Fin 2 → ℕ → ℝ)
        (_heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (_heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (_hsRef_eq : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            sRef a omega = eRef a k *
              Real.exp (H (field omega) z +
                ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set Ω := fun a =>
        {omega |
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
              prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
          (∀ U : Enl × Shift,
            cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
          errLim a chosen omega ≤ epshom * cdet ∧
          (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂P,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))


/-- The uniform record-free estimate on every equal-law coupling. -/
def aux_mfd_lem_goodext_uniform_estimate
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (_Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell epshom : ℝ)
    (_halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (_hbetaLtAlpha : beta < alpha)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (_hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (_hepshom : 0 < epshom)
    (etaGrid : ℝ) (_hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (moment : ℝ) (_hmoment : 1 ≤ moment)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (_hfield_meas : Measurable field)
        (_hfield_law : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : Fin 2 → ℕ → Ω → BilateralField d)
        (_henv_meas : ∀ (a : Fin 2) (n : ℕ), Measurable (env a n))
        (_henv_law : ∀ (a : Fin 2) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (_hEnvConv : ∀ᵐ omega ∂P, ∀ a : Fin 2,
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (_hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (_hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre :
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (_hepsSmall : eps ≤ eps0)
        (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (_hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
        (_hlamSmall : lambdaDet ≤ lam0)
        (_hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (phi : Fin 2 → ℕ → ℕ)
        (_hphi : ∀ (a : Fin 2), StrictMono (phi a))
        (prefixZLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (prefixDLim : Fin 2 → ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            Ω → ℝ)
        (ellLoLim ellHiLim : Fin 2 → (Enl × Shift) → Ω → ℝ)
        (AE_Lim : Fin 2 → (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cmp → Ω → ℝ)
        (_hPrefixZLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixZ (phi a n) U D code (env a n omega)) atTop
            (prefixZLim a U D code))
        (_hPrefixDLim : ∀ (a : Fin 2) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixD (phi a n) U D code (env a n omega)) atTop
            (prefixDLim a U D code))
        (_hEllLoLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellLoN (phi a n) U (env a n omega)) atTop
            (ellLoLim a U))
        (_hEllHiLim : ∀ (a : Fin 2) (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellHiN (phi a n) U (env a n omega)) atTop
            (ellHiLim a U))
        (_hAELim : ∀ (a : Fin 2) (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure P
            (fun n omega => AEN (phi a n) U (env a n omega) i j) atTop
            (fun omega => AE_Lim a U omega i j))
        (_hErrLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => errN (phi a n) c (env a n omega)) atTop
            (errLim a c))
        (_hRatioLim : ∀ (a : Fin 2) (c : Cmp),
          TendstoInMeasure P
            (fun n omega => ratioN (phi a n) c (env a n omega)) atTop
            (ratioLim a c))
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (_hQtri : ∃ m : ℤ, Qside = (3 : ℝ) ^ m)
        (_hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (_hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Fin 2 → Ω →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (_hGE : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            Tendsto (fun n => GN (phi a n) (env a n omega)) atTop (𝓝 (G a omega)))
        (Form : Fin 2 → Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (_hE : ∀ (a : Fin 2) omega u,
          (Form a omega).energy u = limitFormEnergy (G a omega) u)
        (Gamma : ∀ (a : Fin 2) omega,
          _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Form a omega))
        (sRef : Fin 2 → Ω → ℝ)
        (sCmp : Fin 2 → Cmp → Ω → ℝ)
        (_hsRef : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            0 < sRef a omega ∧
            Tendsto (fun n => sN (phi a n) (k : ℤ) z (env a n omega)) atTop
              (𝓝 (sRef a omega)))
        (_hsCmp : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P, ∀ c : Cmp,
            0 < sCmp a c omega ∧
            Tendsto (fun n => sN (phi a n) (cmpLevel c) (cmpCentre c) (env a n omega))
              atTop (𝓝 (sCmp a c omega)))
        (eRef : Fin 2 → ℕ → ℝ)
        (_heRef_pos : ∀ (a : Fin 2) (j : ℕ), 0 < eRef a j)
        (_heRef_lim : ∀ (a : Fin 2) (j : ℕ),
          let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
          Tendsto (fun n : ℕ => kappa (phi a n - j) / kappa (phi a n)) atTop
            (𝓝 (eRef a j)))
        (_hsRef_eq : ∀ (a : Fin 2),
          ∀ᵐ omega ∂P,
            sRef a omega = eRef a k *
              Real.exp (H (field omega) z +
                ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)),
      let Q := centeredCube Qcentre Qside hQside
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let _q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let Good : Fin 2 → Set Ω := fun a =>
        {omega |
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZLim a U D code omega < lambdaLim * (D : ℝ) ∧
              prefixDLim a U D code omega < lambdaLim * (D : ℝ)) ∧
          (∀ U : Enl × Shift,
            cell ≤ ellLoLim a U omega ∧ ellHiLim a U omega ≤ cell⁻¹) ∧
          errLim a chosen omega ≤ epshom * cdet ∧
          (∀ c : Cmp, ratioLim a c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
      let L : ℝ := (3 : ℝ) ^ H1
      let unitClosed : Set (SpatialCoordinates d) :=
        closedCube (0 : SpatialCoordinates d) 1 one_pos
      ∀ᵐ omega ∂P,
        let responseSet : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → Set ℝ :=
          fun r' z' b =>
            {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
              v ∈ (Form 1 omega).domain ∧
              ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
              ((v : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
              (∀ x ∈ frontier (Metric.ball z' (r' / 2)), V x = b x) ∧
              e = ((Gamma 1 omega).measure v
                (Metric.ball z' (r' / 2))).toReal}
        let responseF : ℝ → SpatialCoordinates d → (SpatialCoordinates d → ℝ) → ℝ :=
          fun r' z' b => sInf (responseSet r' z' b)
        (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          ∀ (fL2 : DomainL2 Q),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] f) →
          let u := G 0 omega fL2
          let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
            ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (Q : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U ∧
            ((omega ∈ Good 0 ∧ omega ∈ Good 1) →
              ∀ (zP : SpatialCoordinates d)
                (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
                Metric.closedBall z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) →
                Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
                let nuP : ℝ := ((Gamma 0 omega).measure u parentCell).toReal
                ∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha unitClosed (fun x => U (z + r • x) - cq) ∧
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) ≤
                    Ctotal * r ^ ((2 - (d : ℝ)) / 2) * (sRef 0 omega) ^ (-(1 : ℝ) / 2) *
                      Real.sqrt nuP +
                      Ctotal * r ^ (2 : ℝ) * (sRef 0 omega)⁻¹ * fsup ∧
                  (responseSet r z U).Nonempty ∧
                  IsGLB (responseSet r z U) (responseF r z U) ∧
                  responseF r z U ≤ Ctotal * (eRef 1 k / eRef 0 k) *
                    (nuP + (sRef 0 omega)⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
            (∃ K : ℝ, 0 ≤ K ∧
              ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
                Metric.ball z' (r' / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
                  (responseSet r' z' U).Nonempty ∧
                  IsGLB (responseSet r' z' U) (responseF r' z' U) ∧
                  responseF r' z' U ≤ K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid)))


/-- Specializes the uniform proved estimate to a fixed native represented
operator pair. This adapter carries no additional analytic assumption. -/
theorem aux_mfd_lem_goodext_pair_of_coupling
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom)
    (etaGrid : ℝ) (hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (hH1 : 0 < H1)
    (moment : ℝ) (hmoment : 1 ≤ moment)
    (Cbound eps0 lam0 deltaBase deltaResult : ℝ)
    (hApply : aux_mfd_lem_goodext_uniform_estimate d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
      alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall
      hsigma_eq hsigma hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment Cbound eps0 lam0 deltaBase)
    (hDelta : deltaResult ≤ deltaBase)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (hfield : Measurable field)
    (hfieldlaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
    (env : Fin 2 → ℕ → Ω → BilateralField d)
    (henv_meas : ∀ a n, Measurable (env a n))
    (henv_law : ∀ a n, Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
    (hEnvConv : ∀ᵐ omega ∂P, ∀ a, Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
    (phi : Fin 2 → ℕ → ℕ) (hphi : ∀ a, StrictMono (phi a))
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hQtri : ∃ m : ℤ, Qside = (3 : ℝ) ^ m)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (GN : ℕ → BilateralField d → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (hGN : ∀ N xi f, GN N xi f = (responseSolution S
      (cutoffPositiveCoefficient M H xi N Qcentre hQside)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (G : Fin 2 → Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (hGpair : ∀ a, ∀ᵐ om ∂P,
      Tendsto (fun n => GN (phi a n) (env a n om)) atTop (𝓝 (G a om))) :
    aux_mfd_lem_goodext_comparison_on_pair d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
      alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall
      hsigma_eq hsigma hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment
      Cbound eps0 lam0 deltaResult M H Ω P field env phi Qcentre Qside hQside S G := by
  unfold aux_mfd_lem_goodext_comparison_on_pair
  intros cbuf k0 Rm Sreg It k z qside hqside qcenter hqcenter Enl Shift Cmp
    instEnl instShift instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
    shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos
    hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
    cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
    sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN
    prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim
    hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim hRootsQ Form hE Gamma sRef sCmp hsRef hsCmp eRef
    heRef_pos heRef_lim hsRef_eq
  exact hApply cbuf k0 M Rm Sreg It H hIR Ω P field hfield hfieldlaw env henv_meas henv_law hEnvConv
    k z qside hqside qcenter hqcenter Enl Shift Cmp selfE selfShift qRoot hqRoot
    factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide
    rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre hcmpCentre
    cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre hObservationCentre
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall (hdisorder.trans hDelta)
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN
    hEllHiN AEN hAEN errN ratioN hErrN hRatioN
    phi hphi prefixZLim prefixDLim
    ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim
    hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside hQtri hRootsQ S hS GN hGN G hGpair Form hE Gamma sRef sCmp hsRef hsCmp eRef heRef_pos heRef_lim hsRef_eq


theorem aux_mfd_lem_goodext_tolerance_uniform_represented_exists
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hbetaLtAlpha : beta < alpha)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (etaGrid : ℝ) (hetaGrid : 0 < etaGrid)
    (H1 : ℕ) (hH1 : 0 < H1)
    (moment : ℝ) (hmoment : 1 ≤ moment)
    : ∃ Cbound : ℝ, 1 ≤ Cbound ∧
      ∀ (epshom : ℝ) (hepshom : 0 < epshom), epshom ≤ 1 →
      ∃ eps0 lam0 delta0 etaCat t : ℝ,
      0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧ 0 < etaCat ∧
      etaCat ≤ etaGrid ∧ 1 + etaCat < 2 * alpha ∧ (d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i))),
      (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i))) →
      (∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m) →
      conv_represented_root_family d Z R hR →
      ∀ (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
          (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i)))
          (GE GF : (i : ℕ) → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i))),
          conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha etaCat I beta t ∧
          aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
          ∀ i : ℕ,
            aux_mfd_lem_goodext_comparison_on_pair d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
              alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall hsigma_eq hsigma
              hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment
              Cbound eps0 lam0 delta0 M H Ωh Ph field (fun _ => env)
              (Fin.cases (fun n => NE (seq n)) (fun _ n => NF (seq n)))
              (Z i) (R i) (hR i) (Sspace i) (Fin.cases (GE i) (fun _ => GF i)) := by
  classical
  let etaCat : ℝ := min etaGrid (alpha - 1 / 2)
  let t : ℝ := (d : ℝ) - 1 / 2
  have heta : 0 < etaCat := lt_min hetaGrid (by linarith only [hbeta.1, hbetaLtAlpha])
  have hetale : etaCat ≤ etaGrid := min_le_left _ _
  have hAeta : 1 + etaCat < 2 * alpha := by
    have hsmall : etaCat ≤ alpha - 1 / 2 := min_le_right _ _
    linarith only [hsmall, hbeta.1, hbetaLtAlpha]
  have ht : (d : ℝ) - 1 < t := by dsimp [t]; linarith only []
  have htd : t < (d : ℝ) := by dsimp [t]; linarith only []
  obtain ⟨_hChart, _hCatalogue, hEveryChart⟩ :=
    represented_estimates_actual_model d hd alpha etaCat beta t ht htd
      (by linarith only [halpha.1]) halpha.2 heta hAeta hbeta.1 hbetaLtAlpha
  obtain ⟨deltaB1, hdeltaB1, hModel⟩ := hEveryChart I
  obtain ⟨Cbound, eps0, lam0, deltaG, hC, he0, hl0, hdG, hApply⟩ :=
    aux_mfd_lem_goodext_tolerance_uniform_on_coupling d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
      alpha beta s sigma cell halpha hbeta hbetaLtAlpha hs hsSmall
      hsigma_eq hsigma hcell etaGrid hetaGrid H1 hH1 moment hmoment
  let delta0 := min deltaG deltaB1
  refine ⟨Cbound, hC, ?_⟩
  intro epshom hepshom hepshom_le
  refine ⟨eps0, lam0, delta0, etaCat, t, he0, hl0,
    lt_min hdG hdeltaB1, heta, hetale, hAeta, ht, htd, ?_⟩
  have hApplyTolerance := hApply epshom hepshom hepshom_le
  intro M hM H hIR Z R hR Sspace hSspace hrat hfam NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hbounds⟩ :=
    (hModel M (hM.trans (min_le_right _ _))).2 H hIR Z R hR Sspace hSspace hrat hfam NE NF hNE hNF
  let := mΩh
  let := hPh
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hbounds, ?_⟩
  have hInterface := hjoint.1
  rcases hInterface with ⟨_hp, hfield, hfieldlaw, _hIR, hNES, hNFS, henv, henvConv,
    _hSpaces, hactual, hconv⟩
  intro i
  choose GN hGN using fun N (xi : BilateralField d) =>
    (existsUnique_volumeResponseOperator (Sspace i)
      (cutoffPositiveCoefficient M H xi N (Z i) (hR i))).exists
  let phiPair : Fin 2 → ℕ → ℕ :=
    Fin.cases (fun n => NE (seq n)) (fun _ n => NF (seq n))
  let GPair : Fin 2 → Ωh → DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
      DomainL2 (centeredCube (Z i) (R i) (hR i)) := Fin.cases (GE i) (fun _ => GF i)
  have hGpair : ∀ a : Fin 2, ∀ᵐ om ∂Ph,
      Tendsto (fun n => GN (phiPair a n) (env n om)) atTop (𝓝 (GPair a om)) := by
    intro a
    filter_upwards [hactual, hconv] with om ha hc
    fin_cases a
    · apply (hc i).1.congr
      intro n
      apply ContinuousLinearMap.ext
      intro f
      exact (ha i n f).1.trans (hGN _ _ f).symm
    · apply (hc i).2.congr
      intro n
      apply ContinuousLinearMap.ext
      intro f
      exact (ha i n f).2.trans (hGN _ _ f).symm
  exact aux_mfd_lem_goodext_pair_of_coupling d hd I _X _Sob _Step Pin _MeyersMorrey D Cp Interp
      alpha beta s sigma cell epshom halpha hbeta hbetaLtAlpha hs hsSmall
      hsigma_eq hsigma hcell hepshom etaGrid hetaGrid H1 hH1 moment hmoment
    Cbound eps0 lam0 deltaG delta0 hApplyTolerance (min_le_left _ _) M H hIR
    Ωh Ph field hfield hfieldlaw (fun _ => env)
    (fun _ n => (henv n).1.measurable) (fun _ n => (henv n).1.map_eq)
    (henvConv.mono (fun om h a => h.1)) phiPair
    (by intro a; fin_cases a; exact hNES; exact hNFS)
    (Z i) (R i) (hR i) (hrat i).2 (Sspace i) (hSspace i) GN hGN GPair hGpair


end
end SubdiffusiveProcess.Paper
