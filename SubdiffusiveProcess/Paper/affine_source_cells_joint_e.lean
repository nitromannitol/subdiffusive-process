module

public import SubdiffusiveProcess.Paper.affine_source_cells_catalogue
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
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

/-- The actual expanding joint representation supplies the counted affine estimates on
bounded determining subfamilies covering every prescribed finite initial family. -/
theorem affine_source_cells_joint_e
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
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Rm : Paper.in_responses d M) (Sreg : Paper.in_6_16 d M)
        (_It : Paper.in_iteration d M I Sreg), M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
        (Zc : ℕ → SpatialCoordinates d) (Rc : ℕ → ℝ) (hRc : ∀ i, 0 < Rc i)
        (Sc : (i : ℕ) → ResponseSpace (centeredCube (Zc i) (Rc i) (hRc i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (Zc i) (Rc i) (hRc i)) →L[ℝ]
            DomainL2 (centeredCube (Zc i) (Rc i) (hRc i)))
        (E F : (i : ℕ) → Ω →
          DomainL2 (centeredCube (Zc i) (Rc i) (hRc i)) →L[ℝ]
            DomainL2 (centeredCube (Zc i) (Rc i) (hRc i)))
        (NE NF : ℕ → ℕ) (etaCat t : ℝ),
      conv_represented_joint_grids d hd M H Ω P field envE envF Zc Rc hRc Sc
        GNE GNF E F NE NF alpha etaCat I beta t →
      aux_conv_represented_env_interface_bounds d hd M H Ω P envE envF Zc Rc hRc Sc E F NE NF →
      ∀ K : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ K, ∃ j, e j = i) ∧
      conv_represented_catalogue_grids d hd M H Ω P envE envF (Zc ∘ e) (Rc ∘ e)
        (fun j => hRc (e j)) (fun j => Sc (e j)) NE NF alpha etaCat I beta t ∧
      (let z := Zc ∘ e
       let r := Rc ∘ e
       let hr := fun j => hRc (e j)
       let N : Fin 2 → ℕ → ℕ := ![NE, NF]
       let GE : Fin 2 → ∀ j, Ω → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
          DomainL2 (centeredCube (z j) (r j) (hr j)) :=
         (fun a j => (![E, F] a) (e j))
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
                Set (SpatialCoordinates d)))) := by
  obtain ⟨g, eps, epshom, lambdaLim, cdet, hg, hz, hw, hLlarge, hep, heh, hl, hc,
    delta0, hd0, happly⟩ := affine_source_cells_catalogue d hd I X Sob Step W Pin D Cp Dbase
      beta alpha gamma zeta hbeta hbeta1 hba halpha hgamma hzeta hneg
  refine ⟨g, eps, epshom, lambdaLim, cdet, hg, hz, hw, hLlarge, hep, heh, hl, hc,
    delta0, hd0, ?_⟩
  intro M H Rm Sreg It hdelta Ω _ P _ field envE envF Zc Rc hRc Sc GNE GNF E F
    NE NF etaCat t hJoint hBounds K
  obtain ⟨e, he, hCat⟩ := hJoint.2 K
  rcases hJoint.1 with ⟨_hprob, hfieldMeas, hfieldLaw, hH, hNE, hNF,
    henv, henvConv, _hSc, hGN, hlim⟩
  refine ⟨e, he, hCat, ?_⟩
  dsimp only
  have hEnvMeas (a : Fin 2) (n : ℕ) : Measurable ((![envE, envF] a) n) := by
    fin_cases a
    · exact (henv n).1.measurable
    · exact (henv n).2.measurable
  have hEnvLaw (a : Fin 2) (n : ℕ) :
      Measure.map ((![envE, envF] a) n) P = (chaosSampleLaw M).toMeasure := by
    fin_cases a
    · exact (henv n).1.map_eq
    · exact (henv n).2.map_eq
  have hEnvConv (a : Fin 2) : ∀ᵐ omega ∂P,
      Tendsto (fun n => (![envE, envF] a) n omega) atTop (𝓝 (field omega)) := by
    fin_cases a
    · exact henvConv.mono fun _ h => h.1
    · exact henvConv.mono fun _ h => h.2
  have hGE (a : Fin 2) (j : ℕ) : ∀ᵐ omega ∂P,
      Tendsto (fun n => volumeResponseOperator (Sc (e j))
        (Lane4.cutoffPositiveCoefficient M H ((![envE, envF] a) n omega)
          ((![NE, NF] a) n) (Zc (e j)) (hRc (e j))))
        atTop (𝓝 ((![E, F] a) (e j) omega)) := by
    fin_cases a
    · filter_upwards [hGN, hlim] with omega hG hL
      apply (hL (e j)).1.congr
      intro n
      apply ContinuousLinearMap.ext
      intro f
      rw [volumeResponseOperator_apply]
      exact (hG (e j) n f).1
    · filter_upwards [hGN, hlim] with omega hG hL
      apply (hL (e j)).2.congr
      intro n
      apply ContinuousLinearMap.ext
      intro f
      rw [volumeResponseOperator_apply]
      exact (hG (e j) n f).2
  have hB (a : Fin 2) (j : ℕ) : ∀ᵐ omega ∂P, in_represented_bounds_seq d hd
      (Zc (e j)) (Rc (e j)) (hRc (e j)) (Sc (e j))
      (fun n => Lane4.cutoffPositiveCoefficient M H ((![envE, envF] a) n omega)
        ((![NE, NF] a) n) (Zc (e j)) (hRc (e j))) ((![E, F] a) (e j) omega) := by
    fin_cases a
    · exact hBounds.mono fun _ h => (h (e j)).1
    · exact hBounds.mono fun _ h => (h (e j)).2
  exact happly M H hH Rm Sreg It hdelta Ω P field hfieldMeas hfieldLaw ![envE, envF]
    hEnvMeas hEnvLaw hEnvConv (Zc ∘ e) (Rc ∘ e) (fun j => hRc (e j)) (fun j => Sc (e j))
    ![NE, NF] etaCat t (fun a j => (![E, F] a) (e j)) hCat hGE hB

end Paper
