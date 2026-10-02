import SubdiffusiveProcess.Paper.goodext_local_cell_trace_from_controls
import SubdiffusiveProcess.Paper.goodext_coefficient_grid_trace
import SubdiffusiveProcess.Sobolev.CentralGridTrace

/-!
# Controlled local-cell trace

This module derives the central-cell trace witness from supplied continuous
coefficient-grid controls and makes no additional existence claim.
-/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- An eventual uniform cap at the central grid cell suffices for the prescribed local trace cost. -/
theorem goodext_local_cell_trace_of_eventual_cap
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
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
    [NeZero d]
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0) (h3r0 : 0 < 3 * r0)
    (hPsub : (centeredCube z0 (3 * r0) h3r0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (aCell : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
      PositiveCoefficient (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k))
    (hab : ∀ n k, (a n).val =ᵐ[volume.restrict
      (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] (aCell n k).val)
    (hP : ∀ k : OddGridIndex d (triadicHalf 1), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k), ‖u.val.1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k)) u‖)
    (hReg : ∀ (k : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (hP k)) (aCell n k) b).val.1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ≤ C)
    (hr01 : r0 ≤ 1)
    (Lam : OddGridIndex d (triadicHalf 1) → ℝ)
    (hLam0 : ∀ k, 0 ≤ Lam k)
    (hLam : ∀ n k, I.Lam
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) k) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) (div_pos h3r0 (by positivity))
      (aCell n k) (oddGridCenter z0 (3 * r0) (triadicHalf 1) k) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) ((beta - 1 / 2) / 4) 2 ≤ Lam k)
    (Lcentral : ℝ) (hLcentral : 0 ≤ Lcentral)
    (hCentral : ∀ᶠ n in atTop, I.Lam
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) (fun _ => 1)) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) (div_pos h3r0 (by positivity))
      (aCell n (fun _ => 1)) (oddGridCenter z0 (3 * r0) (triadicHalf 1) (fun _ => 1)) ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) ((beta - 1 / 2) / 4) 2 ≤ Lcentral)

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
  obtain ⟨C, hC, hLocal⟩ :=
    Paper.goodext_local_cell_trace_from_controls d hd I X Sob beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr S hS a A c hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    instNeZero z0 r0 hr0 h3r0 hPsub aCell hab hP hReg hr01 Lam hLam0 hLam
    Lcentral hLcentral hCentral b hbc hbh
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hCentral
  let sigma : ℕ → ℕ := fun n => N + n
  have hSigma : StrictMono sigma := by
    intro i j hij
    dsimp [sigma]
    exact Nat.add_lt_add_left hij N
  have hTail (n : ℕ) : N ≤ sigma n := by
    dsimp [sigma]
    exact Nat.le_add_right N n
  let a' : ℕ → PositiveCoefficient (centeredCube z r hr) := fun n => a (sigma n)
  let c' : ℕ → SpatialCoordinates d → ℝ := fun n => c (sigma n)
  let GN' : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr) :=
    fun n => GN (sigma n)
  let aCell' : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
      PositiveCoefficient (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k) :=
    fun n k => aCell (sigma n) k
  let Lam' : OddGridIndex d (triadicHalf 1) → ℝ :=
    fun k => if k = (fun _ => 1) then Lcentral else Lam k
  let A' := Paper.aux_prop_conc_controlled_forms_controls_reindex A sigma
  have hc' : ∀ n, Continuous (c' n) := fun n => hc (sigma n)
  have hell' : ∀ n, ∃ lam Lam0 : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ c' n x ∧ c' n x ≤ Lam0 :=
    fun n => hell (sigma n)
  have hrep' : ∀ n, (a' n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] c' n :=
    fun n => hrep (sigma n)
  have hcell' : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c' t alpha := by
    intro J hJ theta htheta thetaH hthetaH k
    rcases hcell J hJ theta htheta thetaH hthetaH k with
      ⟨Ecell, Grcell, Hocell, hEcell, hGrcell, hHocell, hbounds⟩
    refine ⟨Ecell, Grcell, Hocell, hEcell, hGrcell, hHocell, ?_⟩
    intro n w hw htrace hwcont
    exact hbounds (sigma n) w hw htrace hwcont
  have hGN' : ∀ n f, GN' n f =
      (responseSolution S (a' n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
    intro n f
    exact hGN (sigma n) f
  have hConv' : Tendsto GN' atTop (𝓝 G) := hConv.comp hSigma.tendsto_atTop
  have hab' : ∀ n k, (a' n).val =ᵐ[volume.restrict
      (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))]
        (aCell' n k).val := fun n k => hab (sigma n) k
  have hReg' :
      ∀ (k : OddGridIndex d (triadicHalf 1)) (phi : SpatialCoordinates d → ℝ),
        ContDiff ℝ ∞ phi →
        ∀ (b0 : weakSobolevGraph (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k)),
          ((b0.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] phi) →
          ∃ Creg : ℝ, 0 ≤ Creg ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
            ContinuousOn V (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) ∧
            ((dirichletMinimizer (killedResponseSpace (hP k)) (aCell' n k) b0).val.1 :
              SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))] V ∧
            IsHolderOn alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ∧
            cAlphaNorm alpha (closure (oddGridCell z0 (3 * r0) h3r0 (triadicHalf 1) k : Set (SpatialCoordinates d))) V ≤ Creg := by
    intro k phi hphi b0 hb0
    obtain ⟨Creg, hCreg, hRegSeq⟩ := hReg k phi hphi b0 hb0
    refine ⟨Creg, hCreg, ?_⟩
    intro n
    simpa only [aCell', sigma] using hRegSeq (sigma n)
  have hLam0' : ∀ k, 0 ≤ Lam' k := by
    intro k
    by_cases hk : k = (fun _ => 1)
    · simp only [Lam', if_pos hk]
      exact hLcentral
    · simp only [Lam', if_neg hk]
      exact hLam0 k
  have hLam' : ∀ n k, I.Lam
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) k)
      ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) (div_pos h3r0 (by positivity))
      (aCell' n k)
      (oddGridCenter z0 (3 * r0) (triadicHalf 1) k)
      ((3 * r0) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) ((beta - 1 / 2) / 4) 2 ≤ Lam' k := by
    intro n k
    by_cases hk : k = (fun _ => 1)
    · subst k
      have h := hN (sigma n) (hTail n)
      simpa only [Lam', aCell', sigma, if_pos rfl] using h
    · have h := hLam (sigma n) k
      simpa only [Lam', aCell', sigma, if_neg hk] using h
  obtain ⟨v, V, hv, hVcont, hVae, hVtrace, hcost⟩ :=
    hLocal z r hr S hS a' A' c' hc' hell' hrep' t alpha ha hcell' GN' G hGN' hConv'
      E hE hcont Gamma z0 r0 hr0 h3r0 hPsub aCell' hab' hP hReg' hr01 Lam' hLam0' hLam'
      b hbc hbh
  refine ⟨v, V, hv, hVcont, hVae, hVtrace, ?_⟩
  simpa only [Lam', if_pos rfl] using hcost
end Paper
