module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.density_source_harmonic_grid
public import SubdiffusiveProcess.Paper.density_bank_partition
public import SubdiffusiveProcess.Paper.density_cutoff_partition_gluing
public import SubdiffusiveProcess.Paper.density_based_counts
public import SubdiffusiveProcess.Paper.density_represented_source_continuity
public import SubdiffusiveProcess.Paper.density_grid_packed
public import SubdiffusiveProcess.Paper.density_cont_packed
public import SubdiffusiveProcess.Paper.conv_represented_estimates_subcatalogue
public import SubdiffusiveProcess.Paper.conv_represented_estimates_event
public import SubdiffusiveProcess.Paper.conv_represented_estimates_change_input
public import SubdiffusiveProcess.Paper.density_glue_sequence
public import SubdiffusiveProcess.Paper.density_bank_mesh
public import SubdiffusiveProcess.Paper.inputs_Interp_witness
public import SubdiffusiveProcess.Paper.inputs_baseline_witness
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_goodext
public import SubdiffusiveProcess.Paper.lem_skeleton
public import SubdiffusiveProcess.Paper.parameter_chain
public import SubdiffusiveProcess.Paper.prop_allchain
public import SubdiffusiveProcess.Paper.prop_density_core_comparison
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.reference_coefficients
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- A closed form whose energy is the limit-form energy of `G`: elements of its domain are in the finite-energy
domain of `G`, and the two energies agree as reals. -/
theorem aux_prop_density_core_approximation_form_energy {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) (v : DomainL2 Q) (hv : v ∈ E.domain) :
    v ∈ limitFormDomain G ∧ (limitFormEnergy G v).toReal = E.form v v := by
  have h1 : E.energy v = ↑(E.form v v) := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem E hv
  have h2 : limitFormEnergy G v = ↑(E.form v v) := (hE v).symm.trans h1
  constructor
  · show limitFormEnergy G v < ⊤
    rw [h2]
    exact EReal.coe_lt_top _
  · rw [h2, EReal.toReal_coe]

/-- Total mass of the energy measure plus a floor of volume, on the cube. -/
theorem aux_prop_density_core_approximation_mass_bound {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hvol : volume (Q : Set (SpatialCoordinates d)) < ⊤)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (u : DomainL2 Q) (hu : u ∈ E.domain)
    (c : ℝ) (hc : 0 ≤ c) :
    (Gam.measure u + ENNReal.ofReal c • volume.restrict (Q : Set (SpatialCoordinates d))).real
        (Q : Set (SpatialCoordinates d)) ≤
      E.form u u + c * (volume (Q : Set (SpatialCoordinates d))).toReal := by
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hvol_ne : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤ := ne_of_lt hvol
  have hrestrict : (volume.restrict (Q : Set (SpatialCoordinates d))) (Q : Set (SpatialCoordinates d)) = volume (Q : Set (SpatialCoordinates d)) := by
    rw [Measure.restrict_apply hQmeas, Set.inter_self]
  have hGam_ne : Gam.measure u (Q : Set (SpatialCoordinates d)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt (Gam.measure_univ_lt_top u hu)) (measure_mono (subset_univ _))
  have hsmul_ne : ENNReal.ofReal c * volume (Q : Set (SpatialCoordinates d)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol_ne
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hrestrict]
  rw [ENNReal.toReal_add hGam_ne hsmul_ne, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  have h1 : (Gam.measure u (Q : Set (SpatialCoordinates d))).toReal ≤ E.form u u := by
    rw [← Gam.measure_univ u hu]
    exact ENNReal.toReal_mono (ne_of_lt (Gam.measure_univ_lt_top u hu)) (measure_mono (subset_univ _))
  linarith

/-- For a symmetric positive killed inverse, the image `G f` lies in the domain of any closed form whose energy is
the limit-form energy of `G`, with energy `⟪f, G f⟫`. -/
theorem aux_prop_density_core_approximation_source_domain {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hp : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) (f : DomainL2 Q) :
    G f ∈ E.domain ∧ E.form (G f) (G f) = inner ℝ f (G f) := by
  have h1 : limitFormEnergy G (G f) = ↑(inner ℝ f (G f)) := by
    unfold limitFormEnergy
    exact iSup_quadraticDual_apply_image G hs hp f
  have h2 : E.energy (G f) = ↑(inner ℝ f (G f)) := by rw [hE, h1]
  have h3 : E.energy (G f) < ⊤ := by rw [h2]; exact EReal.coe_lt_top _
  have hmem : G f ∈ E.domain := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.mem_domain_of_energy_lt_top E h3
  refine ⟨hmem, ?_⟩
  have h4 : E.energy (G f) = ↑(E.form (G f) (G f)) := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem E hmem
  have h5 : (↑(E.form (G f) (G f)) : EReal) = ↑(inner ℝ f (G f)) := by rw [← h4, h2]
  exact EReal.coe_eq_coe_iff.mp h5

/-- Uniqueness of limits along a subsequence: the ratio limit `e'` along `psi` equals the full-sequence limit `e`. -/
theorem aux_prop_density_core_approximation_ratio_eq (kappa : ℕ → ℝ) (Ncut : ℕ → ℕ) (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (k : ℕ) (e e' : ℝ)
    (h1 : Tendsto (fun j => kappa (Ncut j - k) / kappa (Ncut j)) atTop (nhds e))
    (h2 : Tendsto (fun n => kappa (Ncut (psi n) - k) / kappa (Ncut (psi n))) atTop (nhds e')) :
    e' = e := by
  exact tendsto_nhds_unique h2 (h1.comp hpsi.tendsto_atTop)

/-- Final scalar bookkeeping of the finite-horizon comparison. -/
theorem aux_prop_density_core_approximation_energy_arith (Cloc a LD Cstar M Eu cv F eps : ℝ)
    (hCstar : Cstar = Cloc * LD) (hpos : 0 ≤ Cloc * a * LD)
    (hM : M ≤ Eu + cv) (hF : F ≤ Cloc * a * LD * M + eps) :
    F ≤ Cstar * a * (Eu + cv) + eps := by
  have h1 : Cloc * a * LD * M ≤ Cloc * a * LD * (Eu + cv) :=
    mul_le_mul_of_nonneg_left hM hpos
  have h2 : Cloc * a * LD * (Eu + cv) = Cstar * a * (Eu + cv) := by
    rw [hCstar]; ring
  linarith

/-- Shape conversion of the source-continuity statement to the form used by the partition gluing: the
smooth-source hypothesis is unpacked, the Hölder conjunct is dropped. -/
theorem aux_prop_density_core_approximation_hcont_convert {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (Hol : (SpatialCoordinates d → ℝ) → Prop)
    (h : ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f →
      ∀ fL2 : DomainL2 Q,
        (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          (G fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧ Hol U) :
    ∀ f : DomainL2 Q,
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (Q : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0 := by
  rintro f ⟨fc, hfc, -, -, hae⟩
  obtain ⟨U, hUc, hUae, hUfr, -⟩ := h fc hfc f hae
  exact ⟨U, hUc, hUae, hUfr⟩


/-- Sample-level step of `prop_density_core_approximation` at one cube and one sample: from the pointwise data of the
density chain (simultaneous harmonic bank `hbank`, source absorption `habs`, branch counts `hCount`) and the two limit forms,
the finite-horizon approximation of the source with the cost bound `Cstar * a * (E(u) + cFloor |Q|)`. -/
theorem aux_prop_density_core_approximation_sample {d : ℕ} (hd : 2 ≤ d) [NeZero d] (hd1 : 1 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc)
    (S : ResponseSpace (centeredCube zc rc hrc))
    (hS : S.space = killedSobolevGraph (centeredCube zc rc hrc))
    (envE envF : ℕ → BilateralField d) (NE NF : ℕ → ℕ)
    (GNfun : ℕ → BilateralField d →
      DomainL2 (centeredCube zc rc hrc) →L[ℝ] DomainL2 (centeredCube zc rc hrc))
    (hGNfun : ∀ N xi f, GNfun N xi f = (responseSolution S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H xi N zc hrc)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (G0 G1 : DomainL2 (centeredCube zc rc hrc) →L[ℝ] DomainL2 (centeredCube zc rc hrc))
    (hg0 : Tendsto (fun n => GNfun (NE n) (envE n)) atTop (𝓝 G0))
    (hg1 : Tendsto (fun n => GNfun (NF n) (envF n)) atTop (𝓝 G1))
    (Form0 Form1 : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))))
    (Gamma0 : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Form0.toClosedForm)
    (Gamma1 : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Form1.toClosedForm)
    (hform0 : ∀ u, Form0.toClosedForm.energy u = limitFormEnergy G0 u)
    (hform1 : ∀ u, Form1.toClosedForm.energy u = limitFormEnergy G1 u)
    (alpha eta t : ℝ) (halpha0 : 0 < alpha)
    (hcF : ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube zc rc hrc)),
        ((fL2 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] f) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d))) ∧
          ((G1 fL2 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (centeredCube zc rc hrc : Set (SpatialCoordinates d)), U x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d))) U)
    (ell : ℤ) (hell : rc = (3 : ℝ) ^ ell) (H1 : ℕ) (hH1 : 0 < H1) (theta : ℝ)
    (hCellsSub : ∀ b : aux_goodext_admissible_grid_cells zc rc hrc,
      (centeredCube (aux_goodext_admissible_grid_centre zc b.val)
        ((3 : ℝ) ^ (-(b.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          (centeredCube zc rc hrc : Set (SpatialCoordinates d)))
    (index : ℕ × (Fin d → ℤ) → List (OddGridIndex d (subdivisionHalfWidth H1)) →
        aux_goodext_admissible_grid_cells zc rc hrc)
    (hIndex : ∀ (b : ℕ × (Fin d → ℤ)) (w : List (OddGridIndex d (subdivisionHalfWidth H1))),
      aux_density_based_tree_active H1 b.1 zc rc hrc
        (fun i => zc i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ)) w →
      (index b w).val.1 = H1 * (b.1 + w.length) ∧
      aux_goodext_admissible_grid_centre zc (index b w).val =
        descendantCenter (subdivisionHalfWidth H1)
          (fun i => zc i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ))
          ((3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ))) w.length w.get)
    (hPad : ∀ (b : ℕ × (Fin d → ℤ)) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
      (descendantCell (subdivisionHalfWidth H1)
        (fun i => zc i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ))
        (zpow_pos (by norm_num : (0 : ℝ) < 3) (-((H1 * b.1 : ℕ) : ℤ))) n (fun i => w i.castSucc) :
          Set (SpatialCoordinates d)) ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
      aux_density_based_tree_active H1 b.1 zc rc hrc
        (fun i => zc i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ)) (List.ofFn w))
    (Good0 Good1 Good : aux_goodext_admissible_grid_cells zc rc hrc → Prop)
    (hG0 : ∀ b, Good b → Good0 b) (hG1 : ∀ b, Good b → Good1 b)
    (B : ℕ × (Fin d → ℤ) → ℝ)
    (hCount : ∀ (b : ℕ × (Fin d → ℤ)) (J : ℕ) (w : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
      (Set.ncard {i : Fin J | ¬ (aux_density_based_tree_active H1 b.1 zc rc hrc
        (fun i => zc i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ))
        ((List.ofFn w).take (i.val + 1)) → Good (index b ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤
          theta * J + B b)
    (ref : aux_density_full_grid_cells zc rc hrc → ℝ) (hRef : ∀ q, 0 < ref q)
    (ratio : ℕ → ℝ)
    (habs : ∀ (fsup c : ℝ), 0 < c → ∃ r0 : ℝ, 0 < r0 ∧ ∀ b : aux_goodext_admissible_grid_cells zc rc hrc,
      (3 : ℝ) ^ (-(b.val.1 : ℤ)) ≤ r0 → Good0 b →
        (ref ⟨b.val, hCellsSub b⟩)⁻¹ * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
          c * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ d)
    (C0 : ℝ)
    (hbank : ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube zc rc hrc)),
        ((fL2 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] f) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d))) ∧
          ((G0 fL2 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (centeredCube zc rc hrc : Set (SpatialCoordinates d)), U x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d))) U ∧
          ∃ tau : ℕ → ℕ, StrictMono tau ∧
            Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zc rc hrc S
              (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF (tau n)) (NF (tau n)) zc hrc)) ∧
            aux_prop_conc_mesh_cutoff_family_AllCellBounds zc rc hrc
              (fun n => cutoffCoefficient model H (envF (tau n)) (NF (tau n))) t alpha ∧
            ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
              ∃ (uN : ∀ q : aux_density_full_grid_cells zc rc hrc, ℕ → weakSobolevGraph
                    (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                      ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _)))
                (VN : aux_density_full_grid_cells zc rc hrc → ℕ → SpatialCoordinates d → ℝ)
                (Vcell : aux_density_full_grid_cells zc rc hrc → SpatialCoordinates d → ℝ)
                (cost : aux_density_full_grid_cells zc rc hrc → ℝ),
                (∀ q : aux_density_full_grid_cells zc rc hrc,
                  (∀ n, ContinuousOn (VN q n) (closure (centeredCube
                      (aux_goodext_admissible_grid_centre zc q.val)
                      ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
                    (((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                        ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))]
                      VN q n) ∧
                    (∀ x ∈ frontier (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                      ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)),
                      VN q n x = U x) ∧
                    ∀ x ∈ closure (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                      ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)),
                      |VN q n x - U x| ≤ Osc * ((3 : ℝ) ^ (-(q.val.1 : ℤ))) ^ alpha) ∧
                  ContinuousOn (Vcell q) (closure (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                    ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
                  TendstoUniformlyOn (VN q) (Vcell q) atTop
                    (closure (centeredCube (aux_goodext_admissible_grid_centre zc q.val)
                      ((3 : ℝ) ^ (-(q.val.1 : ℤ))) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
                  Tendsto (fun n => sobolevCoefficientForm
                      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF (tau n)) (NF (tau n))
                        (aux_goodext_admissible_grid_centre zc q.val) (zpow_pos (by norm_num) _))
                      (uN q n).val (uN q n).val) atTop (𝓝 (cost q)) ∧
                  0 ≤ cost q ∧
                  cost q ≤ A0 * ((3 : ℝ) ^ (-(q.val.1 : ℤ))) ^ ((d : ℝ) - 2 + 2 * alpha - eta)) ∧
                ∀ b : aux_goodext_admissible_grid_cells zc rc hrc, Good0 b ∧ Good1 b →
                  ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
                    aux_goodext_admissible_grid_centre zc b.val =
                      oddGridCenter zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b.val.1 : ℤ)))
                        (subdivisionHalfWidth H1) idx →
                    Metric.closedBall (aux_goodext_admissible_grid_centre zc b.val)
                      (3 * (3 : ℝ) ^ (-(b.val.1 : ℤ)) / 2) ⊆
                        Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b.val.1 : ℤ)) / 2) →
                    Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b.val.1 : ℤ)) / 2) ⊆
                      (centeredCube zc rc hrc : Set (SpatialCoordinates d)) →
                    cost ⟨b.val, hCellsSub b⟩ ≤ C0 * ratio b.val.1 *
                      ((((Gamma0.measure (G0 fL2))
                          (Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b.val.1 : ℤ)) / 2))).toReal) +
                        (ref ⟨b.val, hCellsSub b⟩)⁻¹ * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ ((d : ℝ) + 2) *
                          (sSup {v : ℝ | ∃ x ∈ closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)),
                            v = |f x|}) ^ 2))
    (D eta0 a Cstar : ℝ) (hD0 : 0 < D) (heta0 : 0 < eta0) (heta03' : eta0 ≤ 3)
    (hDimEarly : (d : ℝ) / D ≤ eta0 / 8) (htheta8 : theta ≤ eta0 / 8)
    (hsExp : (d : ℝ) - eta0 / 8 < (d : ℝ) - 2 + 2 * alpha - eta) (hC0 : 0 < C0) (ha : 0 < a)
    (hCstar : Cstar = C0 * ((3 : ℝ) ^ H1) ^ D)
    (Sset : ℕ → Prop) (hden : eta0 ≤ upperDensity Sset)
    (hratio : ∀ n, Sset n → ratio (H1 * n) ≤ a)
    (hLarge6d : 2 * (6 * (d : ℝ)) ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8)) :
    ∀ f : DomainL2 (centeredCube zc rc hrc),
      (∃ fSmooth : SpatialCoordinates d → ℝ,
        ContDiff ℝ ∞ fSmooth ∧ HasCompactSupport fSmooth ∧
        tsupport fSmooth ⊆ (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ∧
        ((f : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] fSmooth)) →
      ∀ cFloor : ℝ, 0 < cFloor →
        ∃ uRep : SpatialCoordinates d → ℝ, ∃ v : ℕ → DomainL2 (centeredCube zc rc hrc),
          ∃ vRep : ℕ → SpatialCoordinates d → ℝ,
          ContinuousOn uRep (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d))) ∧
          ((G0 f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] uRep) ∧
          (∀ J, v J ∈ limitFormDomain G1) ∧
          (∀ J, ContinuousOn (vRep J) (closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)))) ∧
          (∀ J, (v J : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))] (vRep J)) ∧
          (∀ eps : ℝ, 0 < eps → ∃ J0 : ℕ, ∀ J ≥ J0,
            (∀ x ∈ (centeredCube zc rc hrc : Set (SpatialCoordinates d)), |vRep J x - uRep x| ≤ eps) ∧
            (limitFormEnergy G1 (v J)).toReal ≤ Cstar * a *
              ((limitFormEnergy G0 (G0 f)).toReal +
                cFloor * (volume (centeredCube zc rc hrc : Set (SpatialCoordinates d))).toReal) + eps) := by
  intro f hf cFloor hc
  have hvol : volume (centeredCube zc rc hrc : Set (SpatialCoordinates d)) < ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  obtain ⟨fSm, hfSmooth, hfSupp, hfTsupp, hfAE⟩ := hf
  obtain ⟨U, hUc, hUae, hUfront, hUholder, tau, htau, ⟨A⟩, hcell, A0, Osc, hA0, hOsc, uN, VN, Vcell,
    cost, hBankProps, hLocalB⟩ := hbank fSm hfSmooth f hfAE
  obtain ⟨hsym, hposop⟩ := aux_goodext_controlled_response_recovery_sym_pos S
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n) (NE n) zc hrc)
    (fun n => GNfun (NE n) (envE n)) G0 (fun n f => hGNfun _ _ f) hg0
  obtain ⟨huDom, -⟩ := aux_prop_density_core_approximation_source_domain G0 hsym hposop Form0.toClosedForm hform0 f
  obtain ⟨-, hEuReal⟩ := aux_prop_density_core_approximation_form_energy G0 Form0.toClosedForm hform0 (G0 f) huDom
  have hfinν : IsFiniteMeasure (Gamma0.measure (G0 f)) :=
    ⟨Gamma0.measure_univ_lt_top _ huDom⟩
  obtain ⟨r0, hr0pos, hr0⟩ := habs (sSup {v : ℝ | ∃ x ∈ closure (centeredCube zc rc hrc :
    Set (SpatialCoordinates d)), v = |fSm x|}) cFloor hc
  obtain ⟨v, V, hv, hVc, hVr, hVfin⟩ := density_glue_sequence hd model H
    (fun n => envF (tau n)) (fun n => NF (tau n)) zc rc hrc S hS A
    t alpha halpha0 hcell (fun n => GNfun (NF (tau n)) (envF (tau n))) G1
    (fun n f => hGNfun _ _ f) (hg1.comp htau.tendsto_atTop) Form1.toClosedForm hform1
    (aux_prop_density_core_approximation_hcont_convert G1 _ hcF) Gamma1 U hUfront Osc hOsc uN VN Vcell cost
    (fun q => ⟨(hBankProps q).1, (hBankProps q).2.2.1, (hBankProps q).2.2.2.1⟩)
    ((C0 * a * ((3 : ℝ) ^ H1) ^ D) *
      ((Gamma0.measure (G0 f) + ENNReal.ofReal cFloor •
        volume.restrict (centeredCube zc rc hrc : Set (SpatialCoordinates d))).real
          (centeredCube zc rc hrc : Set (SpatialCoordinates d))))
    (fun mesh hmesh eps heps => density_bank_mesh hd1 zc rc hrc ell hell H1 hH1 theta
      (fun b => ⟨b.val, hCellsSub b⟩) (fun b => rfl) index hIndex hPad Good B hCount ref cost ratio
      (Gamma0.measure (G0 f)) C0 A0 ((d : ℝ) - 2 + 2 * alpha - eta)
      (sSup {v : ℝ | ∃ x ∈ closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)), v = |fSm x|})
      cFloor r0 hr0pos hRef
      (fun b hg hle => hr0 b hle (hG0 b hg))
      (fun b hg zP idx hcentre hcl hbl => hLocalB b ⟨hG0 b hg, hG1 b hg⟩ zP idx hcentre hcl hbl)
      (fun q => (hBankProps q).2.2.2.2.2)
      D eta0 a hc hD0 heta0 heta03' hDimEarly htheta8 hsExp hC0.le ha hA0 Sset hden hratio
      hLarge6d mesh hmesh eps heps)
  refine ⟨U, v, V, hUc, hUae, fun J => (aux_prop_density_core_approximation_form_energy G1 Form1.toClosedForm hform1 (v J)
    (hv J)).1, hVc, hVr, ?_⟩
  intro eps heps
  obtain ⟨J0, hJ0⟩ := hVfin eps heps
  refine ⟨J0, fun J hJ => ⟨fun x hx => (hJ0 J hJ).1 x (subset_closure hx), ?_⟩⟩
  have h1 := (hJ0 J hJ).2
  have hFeq := (aux_prop_density_core_approximation_form_energy G1 Form1.toClosedForm hform1 (v J) (hv J)).2
  rw [hFeq, hEuReal]
  exact aux_prop_density_core_approximation_energy_arith C0 a (((3 : ℝ) ^ H1) ^ D) Cstar _ _ _ _ eps hCstar
    (by positivity) (aux_prop_density_core_approximation_mass_bound hvol Form0.toClosedForm Gamma0 (G0 f) huDom cFloor hc.le) h1



/-- The elementary inequalities among the standing parameters used by the proof. -/
theorem aux_prop_density_core_approximation_arith (d : ℕ) (hdpos : 0 < d)
    (eta0 D theta alpha eta Cd : ℝ) (H1 : ℕ)
    (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3) (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta8 : theta ≤ eta0 / 8) (halpha1 : alpha < 1) (heta : 0 < eta)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8) (hCd : 6 * (d : ℝ) ≤ Cd)
    (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8)) :
    2 * (6 * (d : ℝ)) ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8) ∧ theta < 1 ∧
      0 < alpha ∧ eta0 ≤ 3 ∧ (d : ℝ) - eta0 / 8 < (d : ℝ) - 2 + 2 * alpha - eta ∧ 0 < D ∧
      (d : ℝ) / D ≤ eta0 / 8 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (div_pos (by linarith) heta0) hD
  have h6 : (6 * (d : ℝ)) ^ (eta0 / 3) ≤ Cd ^ (eta0 / 3) :=
    Real.rpow_le_rpow (by linarith) hCd (by linarith)
  have h8 := (div_le_iff₀ heta0).1 hD
  refine ⟨le_trans (by linarith) hLlarge, by linarith, by linarith, by linarith, by linarith, hD0, ?_⟩
  rw [div_le_iff₀ hD0]
  linarith [mul_comm D eta0]


/-- The two deterministic constants of the proof are positive. -/
theorem aux_prop_density_core_approximation_consts (d : ℕ) (hdpos : 0 < d) (alpha beta Cbound Ce : ℝ)
    (hCb : 1 ≤ Cbound) (hCe : 0 < Ce) :
    ∃ Ctotal Cloc : ℝ,
      Ctotal = Cbound * (3 : ℝ) ^ (Cbound * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ))) ∧
      Cloc = 2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) * Ctotal) ^ 2 ∧ 0 < Ctotal ∧ 0 < Cloc := by
  have hCtotalpos : 0 < Cbound * (3 : ℝ) ^ (Cbound * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ))) :=
    mul_pos (lt_of_lt_of_le one_pos hCb) (Real.rpow_pos_of_pos (by norm_num) _)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  refine ⟨_, _, rfl, rfl, hCtotalpos, ?_⟩
  positivity

/-- Fine proof step for `mfd:prop-density`.

Scope and inputs:
- The parameter chain, common extracted candidates, reference ratios, and
  the deterministic constant order are retained exactly from the parent.
- `lem_extension` and `conv_represented_estimates` supply the crude
  source/coefficient absorption used below the base mesh; `cor_energy_measures`
  supplies the represented-to-limit energy-measure passage.
- `lem_goodext`, `prop_allchain`, `prop_growth`, and
  `prop_density_core_comparison` supply the local stopped-cell cost, branch
  counting, residual growth, and finite summation inputs.
- `lem_skeleton` concludes the finite-horizon glued functions, their
  continuous representatives, and the maximum-principle approximation.
- `prop_killed_inverse` supplies the closed killed candidate form used in
  the limiting passage; no closedness, density, or comparison assertion is a
  hypothesis here.
- CONCLUDED HERE: the smooth-source finite-horizon approximation with the
  unreduced `cFloor * |Q|` term.  The parent alone removes `cFloor` and passes
  from this core to the full domain.
- This child is the arbitrary-killed-cube finite-horizon supplier consumed
  by both `prop_density` and `lem_boundary`.
- The sample-level step is `aux_prop_density_core_approximation_sample`.
 -/
theorem prop_density_core_approximation
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (_heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (_hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8)),
    ∃ delta0 Cstar : ℝ, 0 < delta0 ∧ 0 < Cstar ∧
      ∀ [MeasurableSpace (ContinuousMap (SpatialCoordinates d) ℝ)]
        [BorelSpace (ContinuousMap (SpatialCoordinates d) ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → ContinuousMap (SpatialCoordinates d) ℝ)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr Sspace GE GF NE NF →
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂P, ∀ i : ℕ,
          ∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
            (∃ fSmooth : SpatialCoordinates d → ℝ,
              ContDiff ℝ ∞ fSmooth ∧
              HasCompactSupport fSmooth ∧
              tsupport fSmooth ⊆
                (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
              ((f : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict
                  (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
                fSmooth)) →
            ∀ cFloor : ℝ, 0 < cFloor →
              ∃ uRep : SpatialCoordinates d → ℝ,
                ∃ v : ℕ → DomainL2 (centeredCube (z i) (r i) (hr i)),
                ∃ vRep : ℕ → SpatialCoordinates d → ℝ,
                  ContinuousOn uRep
                    (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
                  ((GE i omega f : SpatialCoordinates d → ℝ) =ᵐ[
                      volume.restrict
                        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
                    uRep) ∧
                  (∀ J, v J ∈ limitFormDomain (GF i omega)) ∧
                  (∀ J, ContinuousOn (vRep J)
                    (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))) ∧
                  (∀ J, (v J : SpatialCoordinates d → ℝ) =ᵐ[
                      volume.restrict
                        (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
                    (vRep J)) ∧
                  (∀ eps : ℝ, 0 < eps →
                    ∃ J0 : ℕ, ∀ J ≥ J0,
                      (∀ x ∈ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
                        |vRep J x - uRep x| ≤ eps) ∧
                      (limitFormEnergy (GF i omega) (v J)).toReal ≤
                        Cstar * a *
                          ((limitFormEnergy (GE i omega) (GE i omega f)).toReal +
                            cFloor *
                              (volume (centeredCube (z i) (r i) (hr i) :
                                Set (SpatialCoordinates d))).toReal) + eps) := by
  intro L hLlarge
  have hArith := aux_prop_density_core_approximation_arith d (Nat.lt_of_lt_of_le (by norm_num) hd)
    eta0 D theta alpha eta Cd H1 heta0 heta03 hD htheta8 halpha1 heta hexp hCd hLlarge
  have hLarge6d := hArith.1
  have hthetaLt := hArith.2.1
  have halpha0 := hArith.2.2.1
  have heta03' := hArith.2.2.2.1
  have hsExp := hArith.2.2.2.2.1
  have hD0 := hArith.2.2.2.2.2.1
  have hDimEarly := hArith.2.2.2.2.2.2
  let mC : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  have bC : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨Cbound, epsG, lambdaLim, cdet, Ce, delta1, ⟨hCb, hepsG, hlamG, hcdet, hCe, hdelta1⟩, hGrid⟩ :=
    density_grid_packed d hd I _X _Sob (inputs_Interp_witness d hd) _Step Pin _MeyersMorrey
      Ddet Cp (inputs_baseline_witness d hd) alpha beta eta t ht htd ⟨halpha.le, halpha1⟩
      ⟨hbeta, hbetaAlpha.trans halpha1⟩ hbetaAlpha heta H1 hH1 theta htheta hthetaLt
  obtain ⟨delta2, hdelta2, hCont⟩ :=
    density_cont_packed d hd I Pin _X _MeyersMorrey Cp _Sob alpha ⟨halpha, halpha1⟩
  obtain ⟨Ctotal, Cloc, hCtotal, hCloc, hCtotalpos, hClocpos⟩ :=
    aux_prop_density_core_approximation_consts d (Nat.lt_of_lt_of_le (by norm_num) hd) alpha beta Cbound Ce hCb hCe
  refine ⟨min delta1 delta2, Cloc * ((3 : ℝ) ^ H1) ^ D, lt_min hdelta1 hdelta2,
    mul_pos hClocpos (Real.rpow_pos_of_pos (pow_pos (by norm_num) _) _), ?_⟩
  intro mC' bC' model hmodel Rm Sreg It H Ω mΩ P hPprob field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF hHyp hBoundsAll
    eE eF hpos kappa hEk hFk Sset a ha hden hratio
  obtain rfl : mC' = borel _ := bC'.measurable_eq
  obtain ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv, hcat⟩ := hHyp
  obtain ⟨root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF,
    Cext, I', coercivityKey, extensionKey, lambdaKey, sourceResponseKey, sourceGrowthKey,
    sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey,
    hCatE, hCatF⟩ := hcat
  let : ∀ i, Countable (Dcat i) := hDcat
  have hCatE1 := conv_represented_estimates_change_input d hd model H Ω P NE envE ℕ root z r hr
    Sspace Dcat fcat (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE Cext beta alpha eta t {1} I'
    ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
    (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey I hCatE
  have hCatF1 := conv_represented_estimates_change_input d hd model H Ω P NF envF ℕ root z r hr
    Sspace Dcat fcat (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF Cext beta alpha eta t {1} I'
    ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
    (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey I hCatF
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, hEmeas, hEnull, -, -⟩, -, -, htri, -⟩ := id hCatE1
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, hFmeas, hFnull, -, -⟩, -⟩ := id hCatF1
  have hnullG : P (eventE ∩ eventF)ᶜ = 0 := by
    rw [Set.compl_inter]; exact measure_union_null hEnull hFnull
  have hmeasG : MeasurableSet (eventE ∩ eventF) := hEmeas.inter hFmeas
  refine ae_all_iff.2 (fun i => ?_)
  have hCatE2 := conv_represented_estimates_subcatalogue d hd model H Cext beta alpha eta t {1} Ω P
    NE envE ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE I ℕ
    (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
    (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey hCatE1 i
  have hCatF2 := conv_represented_estimates_subcatalogue d hd model H Cext beta alpha eta t {1} Ω P
    NF envF ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF I ℕ
    (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
    (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey hCatF1 i
  have hCatE3 := conv_represented_estimates_event (G' := eventE ∩ eventF)
    (hsub := Set.inter_subset_left) (hmeas := hmeasG) (hnull := hnullG) (hrepresented := hCatE2) ..
  have hCatF3 := conv_represented_estimates_event (G' := eventE ∩ eventF)
    (hsub := Set.inter_subset_right) (hmeas := hmeasG) (hnull := hnullG) (hrepresented := hCatF2) ..
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hCellsCount, hCellsNE, hCellsSub, hCellsPad⟩ := goodext_admissible_grid d hd1 (z i) (r i) (hr i)
  obtain ⟨hBankCount, hBankNE, -, -⟩ := density_full_grid hd1 (z i) (r i) (hr i)
  have : Countable (aux_density_full_grid_cells (z i) (r i) (hr i)) := hBankCount
  have : Countable (aux_goodext_admissible_grid_cells (z i) (r i) (hr i)) := hCellsCount
  obtain ⟨first⟩ := hCellsNE
  have hEnvConv' : ∀ᵐ omega ∂P, ∀ a : Fin 2,
      Tendsto (fun n => (![envE, envF] a) n omega) atTop (𝓝 (field omega)) :=
    hEnvTend.mono fun omega h => Fin.forall_fin_two.2 h
  obtain ⟨GNfun, hGNfun⟩ : ∃ GNf : ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)),
      ∀ N xi f, GNf N xi f = (responseSolution (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H xi N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 :=
    ⟨fun N xi => volumeResponseOperator (Sspace i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H xi N (z i) (hr i)),
     fun N xi f => volumeResponseOperator_apply _ _ f⟩
  have hGEa : ∀ a : Fin 2, ∀ᵐ omega ∂P, Tendsto (fun n => GNfun ((![NE, NF] a) n)
      ((![envE, envF] a) n omega)) atTop (𝓝 ((![GE i, GF i] a) omega)) := by
    rw [Fin.forall_fin_two]
    constructor
    · filter_upwards [hGNdef, hGconv] with omega h1 h2
      refine (h2 i).1.congr (fun n => ?_)
      exact (ContinuousLinearMap.ext fun f => ((h1 i n f).1).trans (hGNfun _ _ f).symm)
    · filter_upwards [hGNdef, hGconv] with omega h1 h2
      refine (h2 i).2.congr (fun n => ?_)
      exact (ContinuousLinearMap.ext fun f => ((h1 i n f).2).trans (hGNfun _ _ f).symm)
  have hBoundsI : ∀ a : Fin 2, ∀ᵐ omega ∂P, in_represented_bounds_seq d hd (z i) (r i) (hr i)
      (Sspace i) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H ((![envE, envF] a) n omega)
        ((![NE, NF] a) n) (z i) (hr i)) ((![GE i, GF i] a) omega) := by
    rw [Fin.forall_fin_two]
    exact ⟨hBoundsAll.mono fun omega h => (h i).1, hBoundsAll.mono fun omega h => (h i).2⟩
  have hGridI := hGrid model Rm Sreg It H hInfra Ω P field hMeasF hMap (![envE, envF])
    (Fin.forall_fin_two.2 ⟨fun n => (hMP n).1.measurable, fun n => (hMP n).2.measurable⟩)
    (Fin.forall_fin_two.2 ⟨fun n => (hMP n).1.map_eq, fun n => (hMP n).2.map_eq⟩) hEnvConv'
    (z i) (r i) (hr i) (aux_density_full_grid_cells (z i) (r i) (hr i)) (fun q => q.val.1)
    (fun q => q.val.2) (fun q => q.property) (aux_goodext_admissible_grid_cells (z i) (r i) (hr i))
    first (fun b => ⟨b.val, hCellsSub b⟩) (fun b => b.property.1) (fun b U => b.property.2 U)
    (![NE, NF]) (Fin.forall_fin_two.2 ⟨hNEmono, hNFmono⟩) (hmodel.trans (min_le_left _ _))
    {j : ℕ // (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))}
    ⟨i, subset_rfl⟩ (fun j => z j.val) (fun j => r j.val) (fun j => hr j.val)
    (fun j => Sspace j.val) (fun j => Dcat j.val) (fun j => fcat j.val) (fun _ => ℕ)
    (fun j => trace j.val) (fun j => traceH1 j.val)
    (![fun j => usrcE j.val, fun j => usrcF j.val])
    (![fun j => srcRepE j.val, fun j => srcRepF j.val])
    (![fun j => ucellE j.val, fun j => ucellF j.val]) Cext eta {1} le_rfl ℕ
    (![fun i n omega => catalogResponse i (NE n) (envE n omega),
       fun i n omega => catalogResponse i (NF n) (envF n omega)])
    (![responseE, responseF])
    (![fun i n omega => catalogConstant i (NE n) (envE n omega),
       fun i n omega => catalogConstant i (NF n) (envF n omega)])
    (eventE ∩ eventF) (fun j => coercivityKey j.val) (fun j => extensionKey j.val)
    (fun j => lambdaKey j.val) (fun j => sourceResponseKey j.val) (fun j => sourceGrowthKey j.val)
    (fun j => sourceHolderKey j.val) (fun j => cellResponseKey j.val)
    (fun j => cellGrowthKey j.val) (fun j => cellHolderKey j.val)
    {g : ℕ // (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))}
    (fun g => origin g.val) (fun g => ⟨gridRoot g.val, g.property⟩) (fun g => gridKey g.val)
    ⟨rfl, rfl⟩ (Fin.forall_fin_two.2 ⟨hCatE3, hCatF3⟩) (Sspace i) (hSdef i) GNfun hGNfun
    (![GE i, GF i]) hGEa hBoundsI
  obtain ⟨Form, Gamma, hCore, hForm, psi, hpsi, eRef, heRef, hRefLim, ZL, DL, loL, hiL, AEL, errL,
    ratL, hChain, hAbs, hBank⟩ := hGridI
  have hcounts := density_based_counts hd1 H1 hH1 (z i) (r i) (hr i)
    (chaosSampleLaw model).toMeasure P field ⟨hMeasF, hMap⟩
    (fun b => {xi | ∀ a : Fin 2, xi ∈ gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
      (ZL a b) (DL a b) (loL a b) (hiL a b) (errL a b) (ratL a b)})
    theta htheta.le (fun active index hidx => hChain active index hidx)
  obtain ⟨index, B, hBnn, hIndex, hPad, hCountAE⟩ := hcounts
  obtain ⟨K, hK0, hAbsAE⟩ := hAbs
  have hcontF := hCont model Rm Sreg It H hInfra (hmodel.trans (min_le_right _ _)) (z i) (r i)
    (hr i) (Sspace i) (hSdef i) Ω P envF (fun n => (hMP n).2) NF GNfun hGNfun (GF i) (hGEa 1)
  clear hCatE hCatF hCatE1 hCatF1 hCatE2 hCatF2 hGrid hCont
  obtain ⟨ell, hell⟩ := htri i
  have hkap0 : ∀ k, eRef 0 k = eE k := fun k =>
    aux_prop_density_core_approximation_ratio_eq kappa NE psi hpsi k (eE k) (eRef 0 k) (hEk k) (hRefLim 0 k)
  have hkap1 : ∀ k, eRef 1 k = eF k := fun k =>
    aux_prop_density_core_approximation_ratio_eq kappa NF psi hpsi k (eF k) (eRef 1 k) (hFk k) (hRefLim 1 k)
  have hvol : volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) < ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  filter_upwards [hCountAE, hAbsAE, hBank, hForm, hcontF, hGEa 0, hGEa 1] with omega hcount habs
    hbank hform hcF hg0 hg1
  exact aux_prop_density_core_approximation_sample hd hd1 model H (z i) (r i) (hr i) (Sspace i) (hSdef i)
    (fun n => envE n omega) (fun n => envF n omega) NE NF GNfun hGNfun (GE i omega) (GF i omega)
    hg0 hg1 (Form 0 omega) (Form 1 omega) (Gamma 0 omega) (Gamma 1 omega) (hform 0) (hform 1)
    alpha eta t halpha0 hcF ell hell H1 hH1 theta hCellsSub index hIndex hPad
    (fun b => omega ∈ field ⁻¹' gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
      (ZL 0 b) (DL 0 b) (loL 0 b) (hiL 0 b) (errL 0 b) (ratL 0 b))
    (fun b => omega ∈ field ⁻¹' gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
      (ZL 1 b) (DL 1 b) (loL 1 b) (hiL 1 b) (errL 1 b) (ratL 1 b))
    (fun b => ∀ a : Fin 2, field omega ∈ gcat_good 1 lambdaLim (1 / 4 : ℝ) (1 / 4 : ℝ) cdet
      (ZL a b) (DL a b) (loL a b) (hiL a b) (errL a b) (ratL a b))
    (fun b hg => hg 0) (fun b hg => hg 1) (fun b => B b omega) hcount
    (fun q => eRef 0 q.val.1 * Real.exp (H (field omega) (aux_goodext_admissible_grid_centre (z i) q.val) +
      ∑ j ∈ Finset.range q.val.1, (field omega) (-(j : ℤ)) (aux_goodext_admissible_grid_centre (z i) q.val)))
    (fun q => mul_pos (heRef 0 _) (Real.exp_pos _)) (fun n => eRef 1 n / eRef 0 n) habs.2
    (2 * (Ce * 8) * ((Real.sqrt d) ^ (alpha - beta) *
      (Cbound * (3 : ℝ) ^ (Cbound * (((1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ))))) ^ 2)
    hbank D eta0 a (Cloc * ((3 : ℝ) ^ H1) ^ D) hD0 heta0 heta03' hDimEarly htheta8 hsExp
    (by rw [← hCtotal, ← hCloc]; exact hClocpos) ha (by rw [hCloc, hCtotal]) Sset hden
    (fun n hn => by simp only [hkap0, hkap1]; exact hratio n hn) hLarge6d

end
end SubdiffusiveProcess.Paper
