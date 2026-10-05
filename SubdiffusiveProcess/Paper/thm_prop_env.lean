module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_uniqueness_actual
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.conv_represented_affine_counted_actual_e
public import SubdiffusiveProcess.Paper.prop_conc
public import SubdiffusiveProcess.Paper.thm_prop_env_concentration
public import SubdiffusiveProcess.Paper.thm_prop_env_comparison
public import SubdiffusiveProcess.Paper.thm_prop_env_affine
public import SubdiffusiveProcess.Paper.thm_prop_env_endpoints
public import SubdiffusiveProcess.Paper.thm_prop_env_select
public import SubdiffusiveProcess.Paper.thm_prop_env_core
public import SubdiffusiveProcess.Paper.thm_prop_env_prepared
public import SubdiffusiveProcess.Paper.thm_prop_env_orig_limits
public import SubdiffusiveProcess.Paper.thm_prop_env_transfer
public import SubdiffusiveProcess.Paper.thm_prop_env_catalogue
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
public import SubdiffusiveProcess.Paper.thm_prop_env_measure
public import SubdiffusiveProcess.Paper.thm_prop_env_energy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

/-- **Proportionality of the two subsequential limits, for the ACTUAL model, on the ORIGINAL space.**
The represented (Skorokhod) package, its bounds, catalogue, affine data and the relative concentration
are all constructed inside the proof: no `hJoint`/`hBounds`/`hCat`/`hEnum`/`hResp`/`hNonzero`, no affine or
relative supplier.  Hypotheses are those of `conv_represented_thm_c1_uniqueness_actual` for the a.s.
operator-norm limits `GE0`, `GF0` of the two cutoff sequences on the original space, plus the standing inputs of
`conv_represented_affine_counted_actual` (`Step`, `D`, `Dbase`), `prop_conc` (`Interp`, `hES`) and
`thm_prop` (`BD BDQ EM hcontract`).  Conclusion = the conclusion of `thm_prop` (`F = cE`, deterministic `c` in
`[C0^-1, C0]`) for the limit forms on the original space, for the whole family of rational triadic cubes.
The deterministic endpoints are the essential endpoints of the random ones (not the paper's `lem_endpoints`). -/
theorem thm_prop_env
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization model H),
        model.delta ≤ delta0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ (GE0 GF0 : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i))),
        (∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NE n) (Z i) (hR i))) atTop
            (𝓝 (GE0 i β))) →
        (∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β (NF n) (Z i) (hR i))) atTop
            (𝓝 (GF0 i β))) →
        ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧
          ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i : ℕ,
            limitFormDomain (GE0 i β) = limitFormDomain (GF0 i β) ∧
            ∀ u : DomainL2 (centeredCube (Z i) (R i) (hR i)),
              u ∈ limitFormDomain (GE0 i β) →
              (limitFormEnergy (GF0 i β) u).toReal =
                c * (limitFormEnergy (GE0 i β) u).toReal := by
  classical
  obtain ⟨alpha, gamma, zeta, hba, ha1, hgam, hz0, hneg, g, eps, epshom, lambdaLim, cdet, hgg,
    hgz, hgw, hLl, hep, heh, hl, hc, deltaA, hdA, hAff⟩ :=
    conv_represented_affine_counted_actual_e d hd Interp I Pin X W Cp Sob Step D Dbase
  obtain ⟨aexp, haexp, hconcAll⟩ := aux_prop_conc_thin_core d hd I X Sob W Pin Cp Interp hES
  obtain ⟨deltaC0, C0, hdC0, hC01, hC0spec⟩ :=
    thm_prop_env_comparison d hd I X Sob Step W Pin D Cp alpha hba ha1
  obtain ⟨p, hp2, hpRate⟩ := aux_thm_prop_env_pconst g.H1 d aexp haexp
  have hcoreConc : aux_thm_prop_env_conc_core d hd I C0 p aexp :=
    hconcAll C0 hC01 p (by linarith)
  obtain ⟨deltaOC, Cp', hdOC, hCp', hOrigConc⟩ :=
    thm_prop_env_concentration d hd I C0 p aexp g.H1 hcoreConc
  have hc0 : 0 < ((1 / 2 : ℝ) ^ 2) / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  obtain ⟨deltaEnv, hdEnv, hcoreEnv⟩ := thm_prop_env_core d hd C0 hC01 g
    (((1 / 2 : ℝ) ^ 2) / (d : ℝ)) hc0 p (by linarith) Cp' hCp' aexp haexp hpRate
  obtain ⟨deltaCo, hdCo, hcoerc⟩ := aux_thm_prop_coercivity_pair d hd I Pin Sob
  refine ⟨min deltaA (min deltaC0 (min deltaOC (min deltaEnv deltaCo))), C0,
    lt_min hdA (lt_min hdC0 (lt_min hdOC (lt_min hdEnv hdCo))), hC01, ?_⟩
  intro model Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF GE0 GF0 hlimE hlimF
  have hδA : model.delta ≤ deltaA := hδ.trans (min_le_left _ _)
  have hδC0 : model.delta ≤ deltaC0 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδOC : model.delta ≤ deltaOC :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδEnv : model.delta ≤ deltaEnv :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hδCo : model.delta ≤ deltaCo :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hBounds, hForms,
    hKB⟩ := hAff model Rm Sreg It H hH hδA Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  have : IsProbabilityMeasure Ph := hPh
  have hKB' : aux_thm_prop_env_Kblock d hd I model H Ωh Ph field env Z R hR Sspace GE GF seq NE NF
      alpha gamma zeta g eps epshom lambdaLim cdet := hKB
  have hid := aux_thm_prop_env_identification d model H Z R hR Sspace NE NF seq seq hseq hseq GE0 GF0
    hlimE hlimF hH Ωh Ph field env GNE GNF GE GF hjoint.1
  have hsnG := aux_thm_prop_env_hsn d model H Ωh Ph field env env Z R hR Sspace GNE GNF GE GF
    (fun n => NE (seq n)) (fun n => NF (seq n)) hjoint.1
  obtain ⟨hprob, hfm, hfmap, hIR, hNEs, hNFs, hMP, henvc, hSpin, hGNd, hGNc⟩ := hjoint.1
  have hfield : MeasurePreserving field Ph (chaosSampleLaw model).toMeasure := ⟨hfm, hfmap⟩
  have hpos : ∀ᵐ ω ∂Ph, ∃ u : DomainL2 (centeredCube (Z 0) (R 0) (hR 0)),
      u ∈ limitFormDomain (GE 0 ω) ∧ 0 < (limitFormEnergy (GE 0 ω) u).toReal := by
    filter_upwards [hForms] with ω h
    obtain ⟨LE, LF, -⟩ := h
    exact aux_thm_c1_cube_positive_energy (Z 0) (R 0) (hR 0) (GE 0 ω) (LE 0).form.toClosedForm
      (LE 0).energy_eq
  choose e hcover hcatE hK1 using hKB'
  have hlocal : ∀ K : ℕ, ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧ ∀ᵐ ω ∂Ph, ∀ j : ℕ,
      limitFormDomain (GE (e K j) ω) = limitFormDomain (GF (e K j) ω) ∧
      ∀ u : DomainL2 (centeredCube (Z (e K j)) (R (e K j)) (hR (e K j))),
        u ∈ limitFormDomain (GE (e K j) ω) →
          (limitFormEnergy (GF (e K j) ω) u).toReal =
            c * (limitFormEnergy (GE (e K j) ω) u).toReal := by
    intro K
    have : NeZero d := inferInstance
    have hcatK := hcatE K
    have hK1' := hK1 K
    let NE' : ℕ → ℕ := fun n => NE (seq n)
    let NF' : ℕ → ℕ := fun n => NF (seq n)
    have hjointK := aux_thm_prop_env_joint_reindex d model H Ωh Ph field env env Z R hR Sspace GNE GNF
      GE GF NE' NF' (e K) ⟨hprob, hfm, hfmap, hIR, hNEs, hNFs, hMP, henvc, hSpin, hGNd, hGNc⟩
    have hcatI := aux_thm_prop_env_catalogue_of_grids d hd model H Ωh Ph env env (Z ∘ e K)
      (R ∘ e K) (fun j => hR (e K j)) (fun j => Sspace (e K j)) NE' NF' alpha (1 / 128) I
      (127 / 128) ((d : ℝ) - 1 / 2) hcatK
    have hBK : aux_conv_represented_env_interface_bounds d hd model H Ωh Ph env env (Z ∘ e K)
        (R ∘ e K) (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GE (e K j))
        (fun j => GF (e K j)) NE' NF' :=
      hBounds.mono fun om h i => h (e K i)
    have hcompK := hC0spec model hδC0 Rm Sreg It H Ωh Ph field env (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GNE (e K j)) (fun j => GNF (e K j))
      (fun j => GE (e K j)) (fun j => GF (e K j)) NE' NF' hjointK hcatK hBK
    have hsnK := aux_thm_prop_env_hsn d model H Ωh Ph field env env (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GNE (e K j)) (fun j => GNF (e K j))
      (fun j => GE (e K j)) (fun j => GF (e K j)) NE' NF' hjointK
    have hsideK : ∀ᵐ om ∂Ph, ∀ j,
        Nonempty (aux_limit_form_package_limit_side d hd (Z (e K j)) (R (e K j)) (hR (e K j))
          (Sspace (e K j)) (GE (e K j) om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE' n) (Z (e K j))
            (hR (e K j)))) ∧
        Nonempty (aux_limit_form_package_limit_side d hd (Z (e K j)) (R (e K j)) (hR (e K j))
          (Sspace (e K j)) (GF (e K j) om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF' n) (Z (e K j))
            (hR (e K j)))) := by
      filter_upwards [hForms] with om h j
      obtain ⟨LE, LF, -⟩ := h
      exact ⟨⟨LE (e K j)⟩, ⟨LF (e K j)⟩⟩
    have hnzK := aux_thm_prop_env_nonzero d hd Ωh Ph (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GE (e K j))
      (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE' n) (Z (e K i))
        (hR (e K i)))
      (hsideK.mono fun om h i => (h i).1)
    have hsourceEK := aux_thm_prop_env_source d Ωh Ph (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j))
      (fun j => GE (e K j)) (hsnK.mono fun om h i => (h i).1)
    have hsourceFK := aux_thm_prop_env_source d Ωh Ph (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j))
      (fun j => GF (e K j)) (hsnK.mono fun om h i => (h i).2)
    have hJ0 := aux_thm_prop_env_orig_joint d model H hIR (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => hS (e K j)) NE NF hNE hNF
      (fun j => GE0 (e K j)) (fun j => GF0 (e K j)) (hlimE.mono fun β h j => h (e K j))
      (hlimF.mono fun β h j => h (e K j))
    have hcoerc0 := hcoerc model hδCo Rm H (BilateralField d) (chaosSampleLaw model).toMeasure
      (fun β => β) (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j)) (fun j => Sspace (e K j))
      (fun i N β => volumeResponseOperator (Sspace (e K i))
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N (Z (e K i)) (hR (e K i))))
      (fun j => GE0 (e K j)) (fun j => GF0 (e K j)) NE NF hJ0
    have hcoerK : ∀ᵐ om ∂Ph, ∀ i,
        aux_thm_prop_coercive_candidate (centeredCube (Z (e K i)) (R (e K i)) (hR (e K i)))
          (GE (e K i) om) ∧
        aux_thm_prop_coercive_candidate (centeredCube (Z (e K i)) (R (e K i)) (hR (e K i)))
          (GF (e K i) om) := by
      filter_upwards [hfield.quasiMeasurePreserving.ae hcoerc0, hid] with om h hidω i
      rw [(hidω (e K i)).1, (hidω (e K i)).2]
      exact h i
    have hdataB := conv_represented_joint_grids_buffered d hd model H Ωh Ph field env env Z R hR
      Sspace GNE GNF GE GF NE' NF' alpha (1 / 128) I (127 / 128) ((d : ℝ) - 1 / 2) hjoint
    have hplanesG := aux_thm_prop_env_planes d hd model H Ωh Ph field env Z R hR Sspace NE' NF'
      alpha (1 / 128) GNE GNF GE GF hdataB hBounds
    have hplanesK := hplanesG.mono fun om h j => h (e K j)
    obtain ⟨AE, AF, hAEsym, hAFsym, hAEmeas, hAFmeas, hconvAE, hprepAll⟩ :=
      thm_prop_env_prepared d hd BD BDQ EM hcontract model H hIR.1 Ωh Ph env
        (fun n => (hMP n).1.measurable) (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j))
        (fun j => Sspace (e K j)) (fun j => GE (e K j)) (fun j => GF (e K j)) NE' NF' alpha
        (1 / 128) hcatI (fun j => hS (e K j)) hsideK hplanesK
    have hposAF := aux_thm_prop_env_trace_positive d hd model H Ωh Ph env (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) NE' NF' alpha (1 / 128) hcatI
      (aux_thm_prop_env_hP (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j))) AE AF hconvAE
    have hK1c := hK1 K
    obtain ⟨eta, F, Praw, Rraw, Draw, Zs, rawGood, hEta, hScores, psi, hpsi, eRef, heRefpos,
      hkappa, ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim, harr, hGoodBlock⟩ := hK1 K
    have hNcut : ∀ a : Fin 2, StrictMono (![NE', NF'] a) := by
      intro a; fin_cases a
      · exact hNE.comp hseq
      · exact hNF.comp hseq
    obtain ⟨psi2, A, hpsi2, hAsym, hAmeas, hAin, hAae⟩ := thm_prop_env_orig_limits I model H
      hIR.1 (1 / 64) (((127 / 128 : ℝ) - 1 / 2) / 4) (⌊gamma * (g.H1 : ℝ)⌋₊ + 4) 4 Zs Draw g.H1
      (Z ∘ e K) ![NE', NF'] hNcut psi hpsi eRef hkappa ZLim DLim loLim hiLim AELim errLim ratioLim
      (fun a c => (harr a c).2.2.2.2) (fun a c i j => ((harr a c).2.1 (0, fun _ => 1)).2.2 i j)
      (fun c => aux_thm_prop_env_hPcube ((Z ∘ e K) c.1)
        ((3 : ℝ) ^ (-((g.H1 * c.2 : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))
    let nOf : ℕ → ℕ := fun j =>
      if h : ∃ n, R (e K j) = aux_thm_prop_mass_side g.H1 n then h.choose else 0
    have hnOf : ∀ j, (∃ n, R (e K j) = aux_thm_prop_mass_side g.H1 n) →
        R (e K j) = aux_thm_prop_mass_side g.H1 (nOf j) := by
      intro j hj
      simp only [nOf, dite_eq_left hj]
      exact hj.choose_spec
    let AE0 : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun j β => A 0 (j, nOf j) β
    let AF0 : ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun j β => A 1 (j, nOf j) β
    let NE0 : ℕ → ℕ := fun m => NE' (psi (psi2 m))
    let NF0 : ℕ → ℕ := fun m => NF' (psi (psi2 m))
    have hAEconv : ∀ j, (∃ n, (R ∘ e K) j = aux_thm_prop_mass_side g.H1 n) →
        ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
          aux_thm_prop_affine_converges model H β ((Z ∘ e K) j) ((R ∘ e K) j) (hR (e K j)) NE0
            (aux_thm_prop_env_hPcube ((Z ∘ e K) j) ((R ∘ e K) j) (hR (e K j))) (AE0 j β) := by
      intro j hj
      have hm := hnOf j hj
      have hrk : R (e K j) = (3 : ℝ) ^ (-((g.H1 * nOf j : ℕ) : ℝ)) :=
        hm.trans (aux_thm_prop_mass_side_rpow _ _)
      filter_upwards [hAae] with β hβ
      unfold aux_thm_prop_affine_converges
      intro p
      refine (hβ 0 (j, nOf j) p).congr (fun m => ?_)
      exact aux_thm_prop_env_setup_resp_eq model H ((Z ∘ e K) j) (g.H1 * nOf j) (R (e K j))
        (hR (e K j)) hrk _ _ _ β p
    have hAFconv : ∀ j, (∃ n, (R ∘ e K) j = aux_thm_prop_mass_side g.H1 n) →
        ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
          aux_thm_prop_affine_converges model H β ((Z ∘ e K) j) ((R ∘ e K) j) (hR (e K j)) NF0
            (aux_thm_prop_env_hPcube ((Z ∘ e K) j) ((R ∘ e K) j) (hR (e K j))) (AF0 j β) := by
      intro j hj
      have hm := hnOf j hj
      have hrk : R (e K j) = (3 : ℝ) ^ (-((g.H1 * nOf j : ℕ) : ℝ)) :=
        hm.trans (aux_thm_prop_mass_side_rpow _ _)
      filter_upwards [hAae] with β hβ
      unfold aux_thm_prop_affine_converges
      intro p
      refine (hβ 1 (j, nOf j) p).congr (fun m => ?_)
      exact aux_thm_prop_env_setup_resp_eq model H ((Z ∘ e K) j) (g.H1 * nOf j) (R (e K j))
        (hR (e K j)) hrk _ _ _ β p
    have hpsiSM : StrictMono (fun m => seq (psi (psi2 m))) := hseq.comp (hpsi.comp hpsi2)
    have hJ0' := aux_thm_prop_env_orig_joint d model H hIR (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => hS (e K j)) NE0 NF0
      (hNE.comp hpsiSM) (hNF.comp hpsiSM)
      (fun j => GE0 (e K j)) (fun j => GF0 (e K j))
      (hlimE.mono fun β h j => (h (e K j)).comp hpsiSM.tendsto_atTop)
      (hlimF.mono fun β h j => (h (e K j)).comp hpsiSM.tendsto_atTop)
    have hMP' : ∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw model).toMeasure :=
      fun n => (hMP n).1
    have hconvenv : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)) :=
      henvc.mono fun om h => h.1
    have hEid : ∀ j, (∃ n, (R ∘ e K) j = aux_thm_prop_mass_side g.H1 n) →
        ∀ᵐ om ∂Ph, AE j om = AE0 j (field om) := by
      intro j hj
      have hm := hnOf j hj
      have hrk : R (e K j) = (3 : ℝ) ^ (-((g.H1 * nOf j : ℕ) : ℝ)) :=
        hm.trans (aux_thm_prop_mass_side_rpow _ _)
      refine thm_prop_env_measure model H hIR.1 ((Z ∘ e K) j) (R (e K j))
        (hR (e K j)) (aux_thm_prop_env_hP (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j)) j) NE' psi hpsi
        (AE0 j) (fun β => hAsym 0 (j, nOf j) β) (fun i k => hAmeas 0 (j, nOf j) i k)
        (fun p => ?_) Ωh Ph field env hMP' hfield hconvenv (AE j) (hAEsym j)
        (hconvAE.mono fun om h p => (h j).1 p)
      have hin := hAin 0 (j, nOf j) p
      refine hin.congr_left (fun n => Filter.Eventually.of_forall fun β => ?_)
      exact aux_thm_prop_env_setup_resp_eq model H ((Z ∘ e K) j) (g.H1 * nOf j) (R (e K j))
        (hR (e K j)) hrk _ _ _ _ p
    have hFid : ∀ j, (∃ n, (R ∘ e K) j = aux_thm_prop_mass_side g.H1 n) →
        ∀ᵐ om ∂Ph, AF j om = AF0 j (field om) := by
      intro j hj
      have hm := hnOf j hj
      have hrk : R (e K j) = (3 : ℝ) ^ (-((g.H1 * nOf j : ℕ) : ℝ)) :=
        hm.trans (aux_thm_prop_mass_side_rpow _ _)
      refine thm_prop_env_measure model H hIR.1 ((Z ∘ e K) j) (R (e K j))
        (hR (e K j)) (aux_thm_prop_env_hP (Z ∘ e K) (R ∘ e K) (fun j => hR (e K j)) j) NF' psi hpsi
        (AF0 j) (fun β => hAsym 1 (j, nOf j) β) (fun i k => hAmeas 1 (j, nOf j) i k)
        (fun p => ?_) Ωh Ph field env hMP' hfield hconvenv (AF j) (hAFsym j)
        (hconvAE.mono fun om h p => (h j).2 p)
      have hin := hAin 1 (j, nOf j) p
      refine hin.congr_left (fun n => Filter.Eventually.of_forall fun β => ?_)
      exact aux_thm_prop_env_setup_resp_eq model H ((Z ∘ e K) j) (g.H1 * nOf j) (R (e K j))
        (hR (e K j)) hrk _ _ _ _ p
    have hprep := fun (m M : ℝ) => hprepAll
      (aux_thm_prop_env_ck (chaosSampleLaw model).toMeasure (Z ∘ e K) (R ∘ e K) AE0 AF0 g.H1) m M
    choose prepared hpAE hpAF hpck using hprep
    have haff := fun (m M : ℝ) => thm_prop_env_affine d hd I model H hIR Ωh Ph field
      env Z R hR Sspace GE GF seq NE NF hseq alpha gamma zeta (e K) g eps epshom lambdaLim cdet
      hK1c hfield hMP' hconvenv AE AF hconvAE hposAF m M (prepared m M) (hpAE m M)
    have hconcK : ∀ m M : ℝ, C0⁻¹ ≤ m → m ≤ M → M ≤ C0 →
        (∀ᵐ om ∂Ph, ∀ i, limitFormDomain (GE (e K i) om) = limitFormDomain (GF (e K i) om) ∧
          ∀ u ∈ limitFormDomain (GE (e K i) om),
            m * (limitFormEnergy (GE (e K i) om) u).toReal ≤
              (limitFormEnergy (GF (e K i) om) u).toReal ∧
            (limitFormEnergy (GF (e K i) om) u).toReal ≤
              M * (limitFormEnergy (GE (e K i) om) u).toReal) →
        aux_thm_prop_cell_matrix_moments Ph field (Z ∘ e K) (R ∘ e K) (prepared m M).AE
          (prepared m M).AF (prepared m M).ck g.H1 p (Cp' * model.delta * (M - m)) aexp := by
      intro m M hm hmM hM hord
      have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC01
      have hm0 : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
      have hM0 : 0 < M := lt_of_lt_of_le hm0 hmM
      have horder0 := thm_prop_env_transfer d model H hIR (Z ∘ e K) (R ∘ e K)
        (fun j => hR (e K j)) (fun j => Sspace (e K j)) NE NF (fun j => GE0 (e K j))
        (fun j => GF0 (e K j)) (hlimE.mono fun β h j => h (e K j))
        (hlimF.mono fun β h j => h (e K j)) Ωh Ph field hfield (fun j => GE (e K j))
        (fun j => GF (e K j)) (hid.mono fun om h i => h (e K i)) hsnK m M hm0 hM0 hord
      have hmom0 := hOrigConc model hδOC Rm Sreg It H hIR (Z ∘ e K) (R ∘ e K)
        (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GE0 (e K j))
        (fun j => GF0 (e K j)) NE0 NF0 hJ0' AE0 AF0 (fun j β => hAsym 0 (j, nOf j) β)
        (fun j β => hAsym 1 (j, nOf j) β) hAEconv hAFconv m M hm hmM hM horder0
      have hmomh := aux_thm_prop_env_hconc_of_orig Ph field (chaosSampleLaw model).toMeasure hfield
        (Z ∘ e K) (R ∘ e K) g.H1 AE AF AE0 AF0 hEid hFid
        (fun j i k => hAmeas 0 (j, nOf j) i k) (fun j i k => hAmeas 1 (j, nOf j) i k) _ p _ aexp
        (by linarith) hmom0
      rw [hpAE m M, hpAF m M, hpck m M]
      exact hmomh
    exact hcoreEnv model hδEnv Ωh Ph field hfm hfmap (Z ∘ e K) (R ∘ e K)
      (fun j => hR (e K j)) (fun j => Sspace (e K j)) (fun j => GE (e K j)) (fun j => GF (e K j))
      (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE' n) (Z (e K i))
        (hR (e K i)))
      (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF' n) (Z (e K i))
        (hR (e K i)))
      hcompK hnzK hsnK hsideK hcoerK hsourceEK hsourceFK prepared (fun m M => (haff m M).some)
      hconcK
  obtain ⟨c, hc1, hc2, hcprop⟩ := aux_thm_prop_env_glue Ph C0 hC01 Z R hR GE GF e hcover hpos hlocal
  have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC01)) hc1
  have hop : ∀ᵐ ω ∂Ph, ∀ i, GE i ω = c • GF i ω := by
    filter_upwards [hcprop, hsnG] with ω h hs i
    obtain ⟨⟨hsE, hpE⟩, ⟨hsF, hpF⟩⟩ := hs i
    exact aux_thm_prop_env_op_eq_of_prop (GE i ω) (GF i ω)
      (fun x y => by rw [real_inner_comm, hsE]) hpE
      (fun x y => by rw [real_inner_comm, hsF]) hpF c hcpos (h i).1 (h i).2
  have hop0 := aux_thm_prop_env_operator_transfer d model H hH Z R hR Sspace NE NF seq hseq GE0 GF0
    hlimE hlimF Ωh Ph field env GNE GNF GE GF ⟨hprob, hfm, hfmap, hIR, hNEs, hNFs, hMP, henvc, hSpin,
      hGNd, hGNc⟩ c hop
  refine ⟨c, hc1, hc2, ?_⟩
  filter_upwards [hop0] with β hβ i
  exact aux_thm_prop_env_prop_of_smul (GE0 i β) (GF0 i β) c hcpos (hβ i)
    (fun G u => aux_thm_prop_env_limitFormEnergy_smul G c hcpos u)

end Part0

end SubdiffusiveProcess.Paper
end
