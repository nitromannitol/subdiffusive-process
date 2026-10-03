module

public import SubdiffusiveProcess.Paper.affine_source_cells_counted
public import SubdiffusiveProcess.Paper.mass_grid_geometry_fixed
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Choose the geometry, score margins, response bound and primitive scores, and apply the
counted affine theorem to the actual shared represented catalogue. -/
theorem affine_source_cells_catalogue
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd) (Step : Paper.cutoff_good_scale_input d)
    (W : Lane4.SmallPerturbationInput d) (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (beta alpha gamma zeta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) (hzeta : 0 < zeta)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0) :
    ∃ (g : aux_thm_prop_selection_geometry d) (eps epshom lambdaLim cdet : ℝ),
      g.gamma = gamma ∧ g.zeta = zeta ∧ g.width = 81 ∧
      2 * (4 * (d : ℝ)) ^ ((1 / 4 : ℝ) / 3) ≤
        ((3 : ℝ) ^ g.H1) ^ ((1 / 4 : ℝ) / 3 - (1 / 4 : ℝ) / 8) ∧
      eps ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < epshom ∧ lambdaLim ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < cdet ∧
      ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (Rm : Paper.in_responses d M) (Sreg : Paper.in_6_16 d M)
        (_It : Paper.in_iteration d M I Sreg), M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d), Measurable field →
        Measure.map field P = (chaosSampleLaw M).toMeasure →
      ∀ (env : Fin 2 → ℕ → Ω → BilateralField d),
        (∀ a n, Measurable (env a n)) →
        (∀ a n, Measure.map (env a n) P = (chaosSampleLaw M).toMeasure) →
        (∀ a, ∀ᵐ omega ∂P, Tendsto (fun n => env a n omega) atTop (𝓝 (field omega))) →
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (N : Fin 2 → ℕ → ℕ) (etaCat t : ℝ)
        (GE : Fin 2 → ∀ j, Ω → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
          DomainL2 (centeredCube (z j) (r j) (hr j))),
      conv_represented_catalogue_grids d hd M H Ω P (env 0) (env 1)
        z r hr Sspace (N 0) (N 1) alpha etaCat I beta t →
      (∀ a j, ∀ᵐ omega ∂P,
        Tendsto (fun n => volumeResponseOperator (Sspace j)
          (Lane4.cutoffPositiveCoefficient M H (env a n omega) (N a n) (z j) (hr j)))
          atTop (𝓝 (GE a j omega))) →
      (∀ a j, ∀ᵐ omega ∂P, in_represented_bounds_seq d hd
        (z j) (r j) (hr j) (Sspace j)
        (fun n => Lane4.cutoffPositiveCoefficient M H (env a n omega) (N a n) (z j) (hr j))
        (GE a j omega)) →
      ∃ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Fin d → ℝ),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
        primitive_scores d M (1 / 64) eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) ∧
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
        aux_affine_source_cells_env_cellArrays I M H (1 / 64) ((beta - 1 / 2) / 4) (Nat.floor (gamma * (g.H1 : ℝ)) + 4) 4 Z Draw
          (fun n => N a (psi n)) (g.H1 * c.2) (z c.1)
          (ZLim a c) (DLim a c) (loLim a c) (hiLim a c) (AELim a c)
          (errLim a c) (ratioLim a c)) ∧
      (let Good : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
        {omega | aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
        ∀ a : Fin 2, omega ∈ gcat_good 1 lambdaLim (1 / 2) epshom cdet
          (ZLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (DLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (loLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (hiLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (errLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (ratioLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))}
      (∀ n zc, MeasurableSet (Good n zc)) ∧
      (∀ z0 : SpatialCoordinates d,
        ∃ B : Ω → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂P, ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (Lane3.subdivisionHalfWidth g.H1)),
            (Nat.card {j : Fin J // field omega ∉ Good (j.val + 1)
              (Lane3.descendantCenter (Lane3.subdivisionHalfWidth g.H1) z0 1 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
              ((1 / 32 : ℝ) / 2) * (J : ℝ) + B omega) ∧
      aux_thm_prop_mass_good_counts P z r hr g (fun n zc => field ⁻¹' Good n zc) ∧
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
  obtain ⟨Cresp, hCresp, hUniform⟩ := aux_thm_prop_uniform_response_input d hd
  have hs : (1 / 64 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have hsigma : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith
  obtain ⟨H0, hH0⟩ := affine_source_cells_counted d hd I X Sob Step W Pin D Cp Dbase Cresp hCresp
    beta hbeta hbeta1 alpha gamma zeta (1 / 64) ((beta - 1 / 2) / 4) (1 / 2)
    hba halpha hgamma.1 hgamma.2 hzeta hneg hs (by norm_num) rfl hsigma (by norm_num)
    4 1 le_rfl
  have hCd : 1 ≤ 4 * (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨HD, hHD⟩ := aux_thm_prop_Llarge (4 * (d : ℝ)) (1 / 4) hCd (by norm_num)
  obtain ⟨g, hH0g, hggamma, hgzeta, hgwidth⟩ := mass_grid_geometry_fixed d 81 gamma zeta
    (by norm_num) hgamma hzeta (max H0 HD)
  obtain ⟨_hfacts, epshom, hepshom, Cbound, eps0, lam0, hC, he0, hl0, hApply⟩ := hH0 g.H1 ((le_max_left _ _).trans hH0g)
  let eps := min (1 / 2 : ℝ) (eps0 / 2)
  have heps : eps ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by norm_num) (by positivity), (min_le_left _ _).trans_lt (by norm_num)⟩
  have hepsSmall : eps ≤ eps0 := (min_le_right _ _).trans (by linarith)
  let lambdaDet := min (1 / 2 : ℝ) (lam0 / 2)
  let lambdaLim := lambdaDet / 2
  let lambdaCut := lambdaLim / 2
  have hld : 0 < lambdaDet := lt_min (by norm_num) (by positivity)
  have hld1 : lambdaDet < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hThresholds : 0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
      lambdaLim < lambdaDet ∧ lambdaDet < 1 := by
    dsimp only [lambdaCut, lambdaLim]
    constructor; · positivity
    constructor; · linarith
    exact ⟨by linarith, hld1⟩
  have hll : lambdaLim ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp only [lambdaLim]; constructor <;> linarith
  have hlam : lambdaDet ≤ lam0 := (min_le_right _ _).trans (by linarith)
  let cdet := Cbound⁻¹ / 2
  have hC0 : 0 < Cbound := zero_lt_one.trans_le hC
  have hcdet : 0 < cdet := by positivity
  have hcSmall : cdet ≤ Cbound⁻¹ := by
    have : 0 < Cbound⁻¹ := inv_pos.mpr hC0
    dsimp only [cdet]; linarith
  obtain ⟨delta0, hdelta0, hModel⟩ := hApply eps heps hepsSmall lambdaCut lambdaLim lambdaDet cdet
    hThresholds hcdet hcSmall hlam
  refine ⟨g, eps, epshom, lambdaLim, cdet, hggamma, hgzeta, hgwidth,
    hHD _ ((le_max_right _ _).trans hH0g),
    heps, hepshom, hll, hcdet, delta0, hdelta0, ?_⟩
  intro M H hMH Rm Sreg It hdelta Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw
    hEnvConv z r hr Sspace N etaCat t GE hCat hGE hBounds
  classical
  obtain ⟨Rgood, hRgood, _hPhysical⟩ := hUniform M Rm
  obtain ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hPrimitive⟩ :=
    aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists M (1 / 64) eps
      (by norm_num) heps
  refine ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, hEta, hPrimitive, ?_⟩
  obtain ⟨cR, cC, respE, respF, eventE, eventF, root, _hunit, Dcat, hDcat,
    fcat, trace, traceH1, usrcE, usrcF, srcE, srcF, ucellE, ucellF,
    Cext, beta', t', I', cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK,
    origin, gridRoot, gridKey, hAnchor, hgrid, _hbuf, hrep⟩ := hCat
  rcases hAnchor with ⟨hI, hBeta, hT⟩
  subst I'
  subst beta'
  subst t'
  letI : ∀ i, Countable (Dcat i) := hDcat
  exact hModel M H hMH Rgood hRgood.le Sreg It Ω P field hfieldMeas hfieldLaw env hEnvMeas
    hEnvLaw hEnvConv hdelta z r hr Sspace N cR cC ![respE, respF] ![eventE, eventF] root
    Dcat fcat trace traceH1 ![usrcE, usrcF] ![srcE, srcF] ![ucellE, ucellF]
    Cext etaCat t cK eK lK sRK sGK sHK cRK cGK cHK origin gridRoot gridKey
    (by intro a; fin_cases a
        · exact hrep.1
        · exact hrep.2)
    hgrid GE hGE hBounds g rfl hggamma hgzeta (by rw [hgwidth])
    eta hEta F Praw Rraw Draw Z rawGood hPrimitive

end Paper
