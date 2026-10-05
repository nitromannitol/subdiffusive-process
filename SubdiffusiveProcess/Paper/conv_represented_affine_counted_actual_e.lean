module

public import SubdiffusiveProcess.Paper.affine_source_cells_joint_e
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual model produces joint regular form families together with the paired affine
and shifted-grid counting estimates, after all geometric and analytic choices are made.
No catalogue, represented-bound, primitive-score, affine or counting supplier is assumed. -/
theorem conv_represented_affine_counted_actual_e
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Step : cutoff_good_scale_input d)
    (D : deterministic_good_scale_input d) (Dbase : sum_errors_baseline_input d) :
    ∃ alpha gamma zeta : ℝ,
      (127 / 128 : ℝ) < alpha ∧ alpha < 1 ∧ gamma ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < zeta ∧
      affineExponent (d : ℝ) alpha (127 / 128) gamma zeta < 0 ∧
    ∃ (g : aux_thm_prop_selection_geometry d) (eps epshom lambdaLim cdet : ℝ),
      g.gamma = gamma ∧ g.zeta = zeta ∧ g.width = 81 ∧
      2 * (4 * (d : ℝ)) ^ ((1 / 4 : ℝ) / 3) ≤
        ((3 : ℝ) ^ g.H1) ^ ((1 / 4 : ℝ) / 3 - (1 / 4 : ℝ) / 8) ∧
      eps ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < epshom ∧ lambdaLim ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < cdet ∧
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ delta0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
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
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha (1 / 128) I (127 / 128) ((d : ℝ) - 1 / 2) ∧
          aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
          (∀ᵐ omega ∂Ph,
      ∃ (LE : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
          (GE i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE (seq n)) (Z i) (hR i)))
        (LF : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
          (GF i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NF (seq n)) (Z i) (hR i))),
        (∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LE i).form.toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LF i).form.toClosedForm) ∧
        ∀ i j (hji : (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) ⊆
            (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))),
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (Z i) (R i) (hR i))),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (LE i).form.toClosedForm
              (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LE j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LE j).form.domain, zeroExtensionLp hji u ∈ (LE i).form.domain ∧
              (LE i).form.energy (zeroExtensionLp hji u) = (LE j).form.energy u) ∧
            (∀ u ∈ (LE j).form.domain, ∀ v ∈ (LE j).form.domain,
              (LE i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LE j).form.form u v)) ∧
          (∃ D : Submodule ℝ (DomainL2 (centeredCube (Z i) (R i) (hR i))),
            _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain (LF i).form.toClosedForm
              (centeredCube (Z j) (R j) (hR j) : Set (SpatialCoordinates d)) D ∧
            (∀ w, w ∈ D ↔ ∃ u, u ∈ (LF j).form.domain ∧ zeroExtensionLp hji u = w) ∧
            (∀ u ∈ (LF j).form.domain, zeroExtensionLp hji u ∈ (LF i).form.domain ∧
              (LF i).form.energy (zeroExtensionLp hji u) = (LF j).form.energy u) ∧
            (∀ u ∈ (LF j).form.domain, ∀ v ∈ (LF j).form.domain,
              (LF i).form.form (zeroExtensionLp hji u) (zeroExtensionLp hji v) =
                (LF j).form.form u v))) ∧
      ∀ K : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ K, ∃ j, e j = i) ∧
      conv_represented_catalogue_grids d hd M H Ωh Ph env env (Z ∘ e) (R ∘ e)
        (fun j => hR (e j)) (fun j => Sspace (e j)) (fun n => NE (seq n)) (fun n => NF (seq n))
        alpha (1 / 128) I (127 / 128) ((d : ℝ) - 1 / 2) ∧
      (let z := Z ∘ e
       let r := R ∘ e
       let hr := fun j => hR (e j)
       let N : Fin 2 → ℕ → ℕ := ![(fun n => NE (seq n)), (fun n => NF (seq n))]
       let GE : Fin 2 → ∀ j, Ωh → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
          DomainL2 (centeredCube (z j) (r j) (hr j)) :=
         (fun a j => (![GE, GF] a) (e j))
      ∃ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
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
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((N a (psi n) : ℤ) - (k : ℤ)).toNat) / kappa (N a (psi n))))
        atTop (𝓝 (eRef a k))) ∧
      ∃ (ZLim DLim : Fin 2 → (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → (ℕ × ℕ) → Unit → BilateralField d → ℝ),
      (∀ a c,
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U) ∧
          ∀ i j, Measurable (fun omega => AELim a c U omega i j)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ()) ∧
        aux_affine_source_cells_env_cellArrays I M H (1 / 64) (((127 / 128 : ℝ) - 1 / 2) / 4) (Nat.floor (gamma * (g.H1 : ℝ)) + 4) 4 Z Draw
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
        ∃ B : Ωh → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂Ph, ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (_root_.SubdiffusiveProcess.ResponseMoments.subdivisionHalfWidth g.H1)),
            (Nat.card {j : Fin J // field omega ∉ Good (j.val + 1)
              (_root_.SubdiffusiveProcess.ResponseMoments.descendantCenter (_root_.SubdiffusiveProcess.ResponseMoments.subdivisionHalfWidth g.H1) z0 1 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
              ((1 / 32 : ℝ) / 2) * (J : ℝ) + B omega) ∧
      aux_thm_prop_mass_good_counts Ph z r hr g (fun n zc => field ⁻¹' Good n zc) ∧
      ∀ᵐ omega ∂Ph, ∀ a : Fin 2, ∀ jQ : ℕ,
      ∀ (E' : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GE a jQ omega) u) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ _hu : GE a jQ omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
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
  obtain ⟨alpha, gamma, zeta, hba, ha1, hg0, hg1, hz0, hneg⟩ :=
    aux_lem_affine_moreover_exists d hd (127 / 128) (by norm_num) (by norm_num)
  obtain ⟨g, eps, epshom, lambdaLim, cdet, hg, hz, hw, hLlarge, hep, heh, hl, hc,
    deltaAff, hdAff, hAff⟩ := affine_source_cells_joint_e d hd I X Sob Step W Pin D Cp Dbase
      (127 / 128) alpha gamma zeta (by norm_num) (by norm_num) hba ha1 ⟨hg0, hg1⟩ hz0 hneg
  obtain ⟨deltaCat, hdCat, hCat⟩ := conv_represented_thm_c1_family_grids_actual
    d hd hInterp I Pin X W Cp Sob alpha (1 / 128) (127 / 128) ((d : ℝ) - 1 / 2)
    (by linarith) (by linarith) (by linarith) ha1 (by norm_num) (by linarith)
    (by norm_num) hba
  refine ⟨alpha, gamma, zeta, hba, ha1, ⟨hg0, hg1⟩, hz0, hneg,
    g, eps, epshom, lambdaLim, cdet, hg, hz, hw, hLlarge, hep, heh, hl, hc,
    min deltaAff deltaCat, lt_min hdAff hdCat, ?_⟩
  intro M Rm Sreg It H hH hDelta Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hBounds, hForms⟩ :=
    hCat M Rm Sreg It H hH (hDelta.trans (min_le_right _ _)) Z R hR Sspace hS hrat hcomp
      NE NF hNE hNF
  have : IsProbabilityMeasure Ph := hPh
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hBounds, hForms, ?_⟩
  exact hAff M H Rm Sreg It (hDelta.trans (min_le_left _ _)) Ωh Ph field env env Z R hR
    Sspace GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) (1 / 128)
    ((d : ℝ) - 1 / 2) hjoint hBounds

end SubdiffusiveProcess.Paper
