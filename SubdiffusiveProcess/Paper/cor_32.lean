module

public import SubdiffusiveProcess.ResponseMoments.AffineRadiusTransport
public import SubdiffusiveProcess.Paper.Support.Cor32AssemblySupport
public import SubdiffusiveProcess.Paper.Support.Cor32MatrixPassage
public import SubdiffusiveProcess.Paper.Support.Cor32ChainTransfer
public import SubdiffusiveProcess.Paper.Support.Cor32Geometry
public import SubdiffusiveProcess.Paper.prop_allchain
public import SubdiffusiveProcess.Paper.gcat_good_measurable
public import SubdiffusiveProcess.Paper.prop_conc

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper


theorem cor_32
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Dd : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (s sigma epsRaw : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hepsRaw : epsRaw ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf k0 : ℕ) (hk0 : 1 ≤ k0)
    (lambdaLim cell epshom cdet : ℝ) (hlam : 0 < lambdaLim)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hepshom : 0 < epshom) (hcdet : 0 < cdet)
    (Ccamp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) (Interp : CubeFractionalInterpolationInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    let c0 : ℝ := ((d : ℝ) / cell ^ 2)⁻¹
    ∃ delta0 epsPrime : ℝ, 0 < delta0 ∧ 0 < epsPrime ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
          primitive_scores d model s epsRaw (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (_hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (_hm : C0⁻¹ ≤ m) (_hmM : m ≤ M) (_hM : M ≤ C0)
        (_horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (rootCenter : SpatialCoordinates d)
        (idx : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ)
        (_hidx : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          z (idx n w) =
              descendantCenter (subdivisionHalfWidth H1) rootCenter 1 n w ∧
            r (idx n w) = descendantSide (subdivisionHalfWidth H1) n 1)
        (paddedIdx : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ)
        (_hpaddedIdx : ∀ n w,
          z (paddedIdx n w) = descendantCenter (subdivisionHalfWidth H1) rootCenter 1 n w ∧
          r (paddedIdx n w) = 3 * descendantSide (subdivisionHalfWidth H1) n 1),
      let nodeCenter : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
          SpatialCoordinates d :=
        fun n w => descendantCenter (subdivisionHalfWidth H1) rootCenter 1 n w
      let nodeSide : ℕ → ℝ := fun n => descendantSide (subdivisionHalfWidth H1) n 1
      let q : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
          Opens (SpatialCoordinates d) :=
        fun n w => centeredCube (nodeCenter n w) (nodeSide n)
          (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)
      ∀ (phi : Fin 2 → ℕ → ℕ), (∀ a, StrictMono (phi a)) →
      ∀ (ZLim DLim : Fin 2 → aux_cor_32_Cells d H1 → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → aux_cor_32_Cells d H1 → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → aux_cor_32_Cells d H1 → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → aux_cor_32_Cells d H1 → Unit → BilateralField d → ℝ),
      (∀ (a : Fin 2) (c : aux_cor_32_Cells d H1),
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U) ∧
          ∀ i j, Measurable (fun omega => AELim a c U omega i j)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ())) →
      (∀ a : Fin 2, aux_affine_source_cells_env_arrays I model H s sigma gH cbuf Z Draw (phi a)
        (fun c : aux_cor_32_Cells d H1 => H1 * c.1)
        (fun c => nodeCenter c.1 c.2) (ZLim a) (DLim a) (loLim a) (hiLim a)
        (AELim a) (errLim a) (ratioLim a)) →
      ∀ (eRef : Fin 2 → ℕ → ℝ), (∀ a k, 0 < eRef a k) →
      let AE := fun (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω) =>
        aux_cor_32_reference H (eRef 0) (H1 * n) (nodeCenter n w) (field omega) •
          AELim 0 ⟨n, w⟩ ((0 : Fin 3), fun _ => (1 : Fin 3)) (field omega)
      let AF := fun (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω) =>
        aux_cor_32_reference H (eRef 1) (H1 * n) (nodeCenter n w) (field omega) •
          AELim 1 ⟨n, w⟩ ((0 : Fin 3), fun _ => (1 : Fin 3)) (field omega)
      ∀ (hPnode : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (q n w),
            ‖(u : SobolevData (q n w)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (q n w)) u‖),
      ∀ (_hsymAE : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
          (AE n w omega).transpose = AE n w omega)
        (_hsymAF : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
          (AF n w omega).transpose = AF n w omega)
        (_hAE : ∀ᵐ omega ∂P, ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (pvec : Fin d → ℝ),
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos))
                (hPnode n w)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NE j) (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)) pvec /
                (volume (q n w : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE n w omega).mulVec pvec)))
        (_hAF : ∀ᵐ omega ∂P, ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (pvec : Fin d → ℝ),
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos))
                (hPnode n w)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NF j) (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)) pvec /
                (volume (q n w : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF n w omega).mulVec pvec))),
      let ck : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ :=
        (fun n w =>
          ∫ omega, Matrix.trace (AF n w omega) /
            Matrix.trace (AE n w omega) ∂P)
      let Bk : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
          Matrix (Fin d) (Fin d) ℝ :=
        fun n w omega =>
          (Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)
      let BaseGood := fun (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) =>
        {omega : Ω |
          (∀ a : Fin 2, field omega ∈ gcat_good k0 lambdaLim cell epshom cdet
            (ZLim a ⟨n, w⟩) (DLim a ⟨n, w⟩) (loLim a ⟨n, w⟩) (hiLim a ⟨n, w⟩)
            (errLim a ⟨n, w⟩) (ratioLim a ⟨n, w⟩)) ∧
          0 < Matrix.trace (AE n w omega) ∧
          ∀ xi : Fin d → ℝ,
            c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi) ≤
              xi ⬝ᵥ (AE n w omega).mulVec xi}
      let ExtraGood : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w =>
          {omega | omega ∈ BaseGood n w ∧
            (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤
              epsPrime * (M - m)}
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          MeasurableSet (ExtraGood n w)) ∧
      (∃ Bnew : Ω → ℝ,
        Measurable Bnew ∧ (∀ omega, 0 ≤ Bnew omega) ∧
          (∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
            ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
              Nat.card {j : Fin J //
                ¬ omega ∈ ExtraGood (j.val + 1)
                  (fun t : Fin (j.val + 1) =>
                    pi ⟨t.val, by omega⟩)} ≤
                theta * (J : ℝ) + Bnew omega) ∧
          ∀ (n : ℕ)
            (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
            omega ∈ ExtraGood n w →
            ∀ xi : Fin d → ℝ,
              |(volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AF n w omega).mulVec xi) -
                ck n w * (volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)| ≤
                eps * (M - m) *
                  (volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)) :=
 by
  classical
  intro c0
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hc0 : 0 < c0 := inv_pos.mpr (div_pos hdpos (sq_pos_of_pos hcell.1))
  obtain ⟨aexp, haexp, hConcentration⟩ :=
    aux_prop_conc_thin_core d hd I Xc Sf W Pc Ccamp Interp hES
  let rate : ℝ := 2 * (2 * Real.log 2 + 1 + (48 / theta) *
    (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2))
  let p : ℝ := max 1 (rate / (aexp * Real.log 3))
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 0 < aexp * Real.log 3 := mul_pos haexp (Real.log_pos (by norm_num))
  have hpRate : rate ≤ p * aexp * Real.log 3 := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 (rate / (aexp * Real.log 3))) hb.le
    rw [div_mul_cancel₀ _ hb.ne'] at h
    simpa only [p, mul_assoc] using h
  obtain ⟨dc, Cp, hdc, hCp, hConc⟩ := hConcentration C0 hC0 p hp
  obtain ⟨de, epsPrime, hde, hep, hExtra⟩ :=
    aux_cor_32_of_base_and_concentration d hd H1 hH1 eps heps theta htheta htheta1
      C0 hC0 c0 hc0 p hp Cp hCp aexp haexp hpRate
  have hth4 : 0 < theta / 4 := by positivity
  have hth41 : theta / 4 < 1 := by linarith
  obtain ⟨db, hdb, hAll⟩ := prop_allchain d hd I Pc Xc W Sf Dd Cresp hCresp Dbase
    s sigma epsRaw hs hsigma hepsRaw gH cbuf k0 hk0 lambdaLim cell epshom cdet hlam hcell
    hepshom hcdet H1 (by omega) (theta / 4) 1 hth4 hth41 zero_lt_one
  refine ⟨min db (min dc de), epsPrime, lt_min hdb (lt_min hdc hde), hep, ?_⟩
  intro model hdelta Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrimitive
    Ω _ P field z r hr Sspace GN GE GF NE NF hJoint m M hm hmM hM horder rootCenter idx hidx
    paddedIdx hpaddedIdx nodeCenter nodeSide q phi hphi ZLim DLim loLim hiLim AELim errLim ratioLim
    hMeas hArrays eRef heRef AE AF hPnode hsymAE hsymAF hAE hAF ck Bk BaseGood ExtraGood
  have hdeltaB := hdelta.trans (min_le_left _ _)
  have hdeltaC := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaE := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have : IsProbabilityMeasure P := hJoint.1
  have hf : Measurable field := hJoint.2.1
  have hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure := hJoint.2.2.1
  have hMatrixMeas : ∀ (a : Fin 2) (n : ℕ)
      (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
      Measurable (fun omega : Ω =>
        (aux_cor_32_reference H (eRef a) (H1 * n) (nodeCenter n w) (field omega) •
          AELim a ⟨n, w⟩ (0, fun _ => 1) (field omega)) i j) := by
    intro a n w i j
    exact ((aux_cor_32_reference_measurable H hH.1 (eRef a) _ _).comp hf).mul
      ((((hMeas a ⟨n, w⟩).2.1 (0, fun _ => 1)).2.2 i j).comp hf)
  have hBaseMeas : ∀ n w, MeasurableSet (BaseGood n w) := by
    intro n w
    have hg : MeasurableSet {omega : Ω | ∀ a : Fin 2, field omega ∈
        gcat_good k0 lambdaLim cell epshom cdet (ZLim a ⟨n, w⟩) (DLim a ⟨n, w⟩)
          (loLim a ⟨n, w⟩) (hiLim a ⟨n, w⟩) (errLim a ⟨n, w⟩) (ratioLim a ⟨n, w⟩)} := by
      simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro a
      exact (gcat_good_measurable k0 lambdaLim cell epshom cdet _ _ _ _ _ _
        (fun U D code => ((hMeas a ⟨n, w⟩).1 U D code).1)
        (fun U D code => ((hMeas a ⟨n, w⟩).1 U D code).2)
        (fun U => ((hMeas a ⟨n, w⟩).2.1 U).1)
        (fun U => ((hMeas a ⟨n, w⟩).2.1 U).2.1)
        (hMeas a ⟨n, w⟩).2.2.1 (fun u => by cases u; exact (hMeas a ⟨n, w⟩).2.2.2)).preimage hf
    exact hg.inter (_root_.SubdiffusiveProcess.ResponseMoments.measurableSet_trace_coercivity (AE n w) (hMatrixMeas 0 n w) c0)
  have hGuard : ∀ n w, ∀ᵐ omega ∂P,
      field omega ∈ gcat_good k0 lambdaLim cell epshom cdet (ZLim 0 ⟨n, w⟩) (DLim 0 ⟨n, w⟩)
        (loLim 0 ⟨n, w⟩) (hiLim 0 ⟨n, w⟩) (errLim 0 ⟨n, w⟩) (ratioLim 0 ⟨n, w⟩) →
      0 < Matrix.trace (AE n w omega) ∧ ∀ x : Fin d → ℝ,
        c0 * Matrix.trace (AE n w omega) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE n w omega).mulVec x := by
    intro n w
    have h := aux_cor_32_chart_guard I model H s sigma hsigma gH cbuf Z Draw (phi 0)
      (H1 * n) (nodeCenter n w) (ZLim 0 ⟨n, w⟩) (DLim 0 ⟨n, w⟩)
      (loLim 0 ⟨n, w⟩) (hiLim 0 ⟨n, w⟩) (AELim 0 ⟨n, w⟩) (errLim 0 ⟨n, w⟩) (ratioLim 0 ⟨n, w⟩)
      (hArrays 0 ⟨n, w⟩) (eRef 0) (heRef 0) k0 lambdaLim cell epshom cdet hcell.1
    rw [← hlaw] at h
    exact ae_of_ae_map hf.aemeasurable h
  let Good := fun (a : Fin 2) n w => {omega : Ω | field omega ∈
    gcat_good k0 lambdaLim cell epshom cdet (ZLim a ⟨n, w⟩) (DLim a ⟨n, w⟩)
      (loLim a ⟨n, w⟩) (hiLim a ⟨n, w⟩) (errLim a ⟨n, w⟩) (ratioLim a ⟨n, w⟩)}
  have hEach : ∀ a : Fin 2, ∃ B : Ω → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J → ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
        (Nat.card {j : Fin J // omega ∉ Good a (j.val + 1)
          (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤ (theta / 4) * J + B omega := by
    intro a
    have hAllA := hAll model hdeltaB Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood
      hPrimitive (aux_cor_32_Cells d H1) (fun c => H1 * c.1) (fun c => nodeCenter c.1 c.2)
      (phi a) (hphi a) (ZLim a) (DLim a) (loLim a) (hiLim a) (AELim a) (errLim a) (ratioLim a)
      (fun c => ⟨(hMeas a c).1, fun U => ⟨((hMeas a c).2.1 U).1, ((hMeas a c).2.1 U).2.1⟩,
        (hMeas a c).2.2⟩) (hArrays a)
    rw [← two_mul_subdivisionHalfWidth_add_one H1] at hAllA
    obtain ⟨_, B, hBm, hB0, hBae, _⟩ := hAllA (fun _ => True) (fun w => ⟨w.length, w.get⟩)
      (fun _ _ => rfl)
    exact aux_cor_32_transfer_chain P (chaosSampleLaw model).toMeasure field hf hlaw
      (fun n w => gcat_good k0 lambdaLim cell epshom cdet (ZLim a ⟨n, w⟩) (DLim a ⟨n, w⟩)
        (loLim a ⟨n, w⟩) (hiLim a ⟨n, w⟩) (errLim a ⟨n, w⟩) (ratioLim a ⟨n, w⟩))
      (theta / 4) B hBm hB0 (by simpa only [true_and, mem_ofPred_eq] using! hBae)
  have hBaseChain := aux_cor_32_guarded_pair_chain P (Good 0) (Good 1)
    (fun n w omega => 0 < Matrix.trace (AE n w omega) ∧ ∀ x : Fin d → ℝ,
      c0 * Matrix.trace (AE n w omega) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE n w omega).mulVec x)
    hGuard theta (hEach 0) (hEach 1)
  have hBaseEq : BaseGood = fun n w => {omega | omega ∈ Good 0 n w ∧ omega ∈ Good 1 n w ∧
      0 < Matrix.trace (AE n w omega) ∧ ∀ x : Fin d → ℝ,
        c0 * Matrix.trace (AE n w omega) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE n w omega).mulVec x} := by
    funext n w
    ext omega
    simp only [BaseGood, Good, Fin.forall_fin_two, mem_ofPred_eq]
    tauto
  rw [← hBaseEq] at hBaseChain
  have hCube : ∀ n w, q n w = centeredCube (nodeCenter n w)
      ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _) := by
    intro n w
    apply Opens.ext
    change Metric.ball (nodeCenter n w)
      (descendantSide (subdivisionHalfWidth H1) n 1 / 2) =
      Metric.ball (nodeCenter n w) ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) / 2)
    rw [aux_cor_32_side_eq]
  have hPpow : ∀ n w, ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (centeredCube (nodeCenter n w)
        ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
        ‖(u : SobolevData (centeredCube (nodeCenter n w)
          ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube (nodeCenter n w)
            ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖ := by
    intro n w
    exact (congrArg (fun U : Opens (SpatialCoordinates d) =>
      ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
        ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖)
      (hCube n w)).mp (hPnode n w)
  have hNodeConc := fun n w => hConc model hdeltaC Rm Sreg It H Ω P field z r hr Sspace GN GE GF
    NE NF m M (nodeCenter n w) (H1 * n) (idx n w) (paddedIdx n w)
    (hPpow n w) (AE n w) (AF n w)
    ⟨hJoint, ⟨hm, hmM, hM⟩, horder,
      ⟨(hidx n w).1, by simpa only [aux_cor_32_side_eq] using (hidx n w).2⟩,
      ⟨(hpaddedIdx n w).1, by simpa only [aux_cor_32_side_eq] using (hpaddedIdx n w).2⟩,
      hsymAE n w, hsymAF n w,
      (by
        filter_upwards [hAE] with omega h
        intro pvec
        apply Filter.Tendsto.congr ?_ (h n w pvec)
        intro j
        unfold aux_prop_conc_setup_resp
        exact _root_.SubdiffusiveProcess.ResponseMoments.normalized_affine_response_congr_radius model H (field omega)
          (NE j) (nodeCenter n w) (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)
          (Real.rpow_pos_of_pos zero_lt_three _) (aux_cor_32_side_eq H1 n)
          (hPnode n w) (hPpow n w) pvec),
      (by
        filter_upwards [hAF] with omega h
        intro pvec
        apply Filter.Tendsto.congr ?_ (h n w pvec)
        intro j
        unfold aux_prop_conc_setup_resp
        exact _root_.SubdiffusiveProcess.ResponseMoments.normalized_affine_response_congr_radius model H (field omega)
          (NF j) (nodeCenter n w) (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)
          (Real.rpow_pos_of_pos zero_lt_three _) (aux_cor_32_side_eq H1 n)
          (hPnode n w) (hPpow n w) pvec)⟩
  exact hExtra model hdeltaE H Ω P field z r hr Sspace GN GE GF NE NF hJoint m M hm hmM hM horder
    rootCenter idx hidx hPnode AE AF hsymAE hsymAF hAE hAF (hMatrixMeas 0) (hMatrixMeas 1)
    BaseGood hBaseMeas (fun _ _ _ h => h.2) hBaseChain
    (fun n w => (hNodeConc n w).2.1)
    (fun n w => (hNodeConc n w).2.2.1)
    (fun n w => (hNodeConc n w).2.2.2)

end SubdiffusiveProcess.Paper
