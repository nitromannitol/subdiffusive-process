module

public import SubdiffusiveProcess.Paper.goodext_parent_oscillation_of_l2
public import SubdiffusiveProcess.Paper.goodext_controlled_response_recovery

@[expose] public section

/-! Energy-to-oscillation (coarse Poincaré) bound for the limiting response `G f` on any cube
whose closure lies in an open parent, measured by an arbitrary energy measure of the limiting
form.  Inputs are the controlled finite-cutoff sequence and an eventual coarse lower bound on the
cube; no pointwise or uniform convergence and no local good-cell estimate is assumed. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace Paper

/-- Coarse Poincaré for the limiting response on a cube inside an open parent, with the
parent energy measured by an arbitrary energy measure of the limiting closed form. -/
theorem affine_comparison_poincare
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
    (S : ResponseSpace (centeredCube zQ rQ hrQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ rQ hrQ))
    (a : ℕ → PositiveCoefficient (centeredCube zQ rQ hrQ))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd zQ rQ hrQ S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds zQ rQ hrQ c t alpha)
    (GN : ℕ → DomainL2 (centeredCube zQ rQ hrQ) →L[ℝ] DomainL2 (centeredCube zQ rQ hrQ))
    (G : DomainL2 (centeredCube zQ rQ hrQ) →L[ℝ] DomainL2 (centeredCube zQ rQ hrQ))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube zQ rQ hrQ),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E)
    (f : DomainL2 (centeredCube zQ rQ hrQ)) (U : SpatialCoordinates d → ℝ)
    (hU : (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))] U)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hq : centeredCube z r hr ≤ centeredCube zQ rQ hrQ)
    (acmp : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hab : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] (acmp n).val)
    (sigma cell : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1) (hcell0 : 0 < cell)
    (sN : ℕ → ℝ) (s : ℝ) (hsN : ∀ n, 0 < sN n) (hs : 0 < s)
    (hsLim : Tendsto sN atTop (𝓝 s))
    (hlow : ∀ᶠ n in atTop, cell * sN n ≤ I.lam z r hr (acmp n) z r sigma 2)
    (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
    (hpad : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ parentCell) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        ((Gamma.measure (G f)) parentCell).toReal := by
  obtain ⟨hsym, hpos⟩ := aux_goodext_controlled_response_recovery_sym_pos S a GN G hGN hConv
  have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
    iSup_quadraticDual_apply_image G hsym hpos f
  have hdom : G f ∈ E.domain := by
    apply DirichletForm.ClosedForm.mem_domain_of_energy_lt_top
    rw [hE, hval]
    exact EReal.coe_lt_top _
  letI hfin : IsFiniteMeasure (Gamma.measure (G f)) :=
    ⟨Gamma.measure_univ_lt_top _ hdom⟩
  let un : ℕ → weakSobolevGraph (centeredCube zQ rQ hrQ) := fun n =>
    ⟨(responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val,
      S.le_weak (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).property⟩
  have hconv : Tendsto (fun n => (un n).val.1) atTop (𝓝 (G f)) := by
    have happ : Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hConv
    refine happ.congr (fun n => ?_)
    rw [hGN]
  have hrec := goodext_controlled_response_recovery hd zQ rQ hrQ S hS a A c hc hell hrep
    t alpha ha hcell GN G hGN hConv E hE hcont Gamma f
  exact goodext_parent_oscillation_of_l2 hd I Pin z r hr (centeredCube zQ rQ hrQ) hq a acmp hab
    un (fun n => ((un n).val.1 : SpatialCoordinates d → ℝ)) U (fun n => EventuallyEq.rfl)
    (G f) hconv hU sigma cell hsigma hsigma1 hcell0 sN s hsN hs hsLim hlow
    (Gamma.measure (G f)) parentCell hparent hpad hrec

end Paper
