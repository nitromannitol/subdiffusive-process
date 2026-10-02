import SubdiffusiveProcess.Paper.goodext_local_cell_trace_of_eventual_cap
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

/-! Actual cutoff coefficients instantiate the local trace construction on a
concentric three-cell grid. All uniform controls remain explicit hypotheses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- An eventual central cutoff cap supplies the same ambient witness with the sharper central-cell cost. -/
theorem goodext_cutoff_local_trace_eventual
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (N : ℕ → ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
      (fun n => cutoffPositiveCoefficient M H (env n) (N n) z hr))
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H (env n) (N n)) t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (cutoffPositiveCoefficient M H (env n) (N n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0) (h3r0 : 0 < 3 * r0)
    (hPsub : (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hReg : ∀ (j : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ),
      ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0),
        (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))] phi →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer
            (killedResponseSpace (centeredCube_killedPoincare
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0))
            (cutoffPositiveCoefficient M H (env n) (N n)
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0) b).val.1 :
                SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                  (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0 : Set (SpatialCoordinates d))) V ≤ K)
    (hr01 : r0 ≤ 1) (Lam : OddGridIndex d (triadicHalf 1) → ℝ)
    (hLam0 : ∀ j, 0 ≤ Lam j)
    (hLam : ∀ n j, I.Lam (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 hr0
      (cutoffPositiveCoefficient M H (env n) (N n)
        (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hr0)
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) r0 ((beta - 1 / 2) / 4) 2 ≤ Lam j)
    (Lcentral : ℝ) (hLcentral : 0 ≤ Lcentral)
    (hCentral : ∀ᶠ n in atTop, I.Lam z0 r0 hr0
      (cutoffPositiveCoefficient M H (env n) (N n) z0 hr0)
      z0 r0 ((beta - 1 / 2) / 4) 2 ≤ Lcentral)
    (b : SpatialCoordinates d → ℝ)
    (hbc : ContinuousOn b (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hbh : IsHolderOn beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b),
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), V x = b x) ∧
      (Gamma.measure v (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal ≤
        C * Lcentral * r0 ^ ((d : ℝ) - 2) *
          (r0 ^ beta * holderSeminorm beta (frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) b) ^ 2 := by
  obtain ⟨C, hC, hTrace⟩ := goodext_local_cell_trace_of_eventual_cap d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro M H env N z r hr S hS A t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    z0 r0 hr0 h3r0 hPsub hReg hr01 Lam hLam0 hLam Lcentral hLcentral hCentral b hbc hbh
  have hchild : (3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1) = r0 := by
    rw [show triadicHalf 1 = 1 from rfl]
    norm_num
  let side : ℝ := (3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)
  have hside : 0 < side := div_pos h3r0 (by positivity)
  let aCell := fun n (j : OddGridIndex d (triadicHalf 1)) =>
    cutoffPositiveCoefficient M H (env n) (N n)
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hside
  let hP := fun j : OddGridIndex d (triadicHalf 1) =>
    centeredCube_killedPoincare (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hside
  have hrep (n : ℕ) := (cutoffPositiveCoefficient_representative M H (env n) (N n) z hr).2.2.2
  have hell (n : ℕ) : ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H (env n) (N n) x ∧ cutoffCoefficient M H (env n) (N n) x ≤ Lam := by
    obtain ⟨lo, hi, hlo, hbounds⟩ := cutoffCoefficient_closedCube_bounds M H (env n) (N n) z hr
    exact ⟨lo, hi, hlo, fun x hx => hbounds x (centeredCube_subset_closedCube z hr hx)⟩
  apply hTrace z r hr S hS _ A _ (fun n => cutoffCoefficient_continuous M H (env n) (N n))
    hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    z0 r0 hr0 h3r0 hPsub aCell ?_ hP ?_ hr01 Lam hLam0 ?_ Lcentral hLcentral ?_ b hbc hbh
  · intro n j
    have hsub := (oddGridCell_subset z0 h3r0 (triadicHalf 1) j).trans hPsub
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hrep n),
      (cutoffPositiveCoefficient_representative M H (env n) (N n)
        (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hside).2.2.2] with x hx hy
    exact hx.trans hy.symm
  · let Reg : (rr : ℝ) → 0 < rr → Prop := fun rr hrr =>
      ∀ (j : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ),
      ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr),
        (b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr : Set (SpatialCoordinates d))] phi →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer
            (killedResponseSpace (centeredCube_killedPoincare
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hrr))
            (cutoffPositiveCoefficient M H (env n) (N n)
              (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hrr) b).val.1 :
                SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                  (centeredCube (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube
            (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr : Set (SpatialCoordinates d))) V ≤ K
    have transport : ∀ (rr : ℝ) (hrr : 0 < rr), rr = r0 → Reg rr hrr := by
      intro rr hrr heq
      subst rr
      exact hReg
    simpa only [Reg, aCell, hP, oddGridCell] using transport side hside hchild
  · let Cap : (rr : ℝ) → 0 < rr → Prop := fun rr hrr =>
      ∀ n j, I.Lam (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr hrr
      (cutoffPositiveCoefficient M H (env n) (N n)
        (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) hrr)
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) j) rr ((beta - 1 / 2) / 4) 2 ≤ Lam j
    have transport : ∀ (rr : ℝ) (hrr : 0 < rr), rr = r0 → Cap rr hrr := by
      intro rr hrr heq
      subst rr
      exact hLam
    simpa only [Cap, aCell] using transport side hside hchild
  · let Cap : SpatialCoordinates d → (rr : ℝ) → 0 < rr → Prop := fun zz rr hrr =>
      ∀ᶠ n in atTop, I.Lam zz rr hrr
        (cutoffPositiveCoefficient M H (env n) (N n) zz hrr)
        zz rr ((beta - 1 / 2) / 4) 2 ≤ Lcentral
    have transport : ∀ zz (rr : ℝ) (hrr : 0 < rr), zz = z0 → rr = r0 → Cap zz rr hrr := by
      intro zz rr hrr hzz heq
      subst zz
      subst rr
      exact hCentral
    have hcenter : oddGridCenter z0 (3 * r0) (triadicHalf 1) (fun _ => 1) = z0 := by
      change oddGridCenter z0 (3 * r0) 1 (fun _ => (1 : Fin 3)) = z0
      funext i
      simp only [oddGridCenter, Fin.val_one, Nat.cast_one, sub_self, zero_mul, add_zero]
    simpa only [Cap, aCell] using transport _ side hside hcenter hchild
end Paper
