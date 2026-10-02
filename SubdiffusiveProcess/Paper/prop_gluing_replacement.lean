import SubdiffusiveProcess.Paper.prop_gluing
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Paper.lem_truncation
import SubdiffusiveProcess.Paper.prop_killed_consistency
import SubdiffusiveProcess.Paper.prop_locality
import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.obl_FOT
import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
import SubdiffusiveProcess.Paper.prop_gluing_replacement_energy
import SubdiffusiveProcess.Paper.prop_gluing_replacement_patch
import SubdiffusiveProcess.Paper.prop_gluing_replacement_localization

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem prop_gluing_replacement
    (hd : 2 ≤ d)
    (hQcube : ∃ z : SpatialCoordinates d, ∃ R : ℝ, 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : DirichletForm.EnergyMeasure E)
    (beta : ℝ) (hbeta : 1 / 2 < beta)
    (alpha : ℝ) (hba : beta < alpha)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hcellQ : ∀ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (henlarge : ∀ i : Fin m,
      Metric.ball (cent i) (3 * rad i / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcent : ∀ (i : Fin m) (j : Fin d), ∃ s : ℚ, cent i j = (s : ℝ))
    (htri : ∀ i : Fin m, ∃ k : ℤ, rad i = (3 : ℝ) ^ k)
    (Dq : Fin m → Submodule ℝ (DomainL2 Q))
    (hDq : ∀ i : Fin m, DirichletForm.IsKilledDomain E
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (Dq i))
    (V : DomainL2 Q) (hV : V ∈ E.domain)
    (Vc : SpatialCoordinates d → ℝ)
    (hVcont : ContinuousOn Vc (closure (Q : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Vc)
    (hVholder : ∀ i : Fin m, Lane4.IsHolderOn alpha
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) Vc)
    (Lam : Fin m → ℝ)
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : (i : Fin m) → ℕ →
      PositiveCoefficient (centeredCube (cent i) (rad i) (hrad i)))
    (haC : ∀ i n,
      ((aC i n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))] a n)
    (haCont : ∀ i n, ContinuousOn (a n)
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (haEll : ∀ i n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        lo ≤ a n x ∧ a n x ≤ hi)
    (ext : (i : Fin m) → ℕ → H1Function
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
    (hextcont : ∀ i n, ContinuousOn (ext i n).toFun
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (hextb : ∀ i n, ∀ x ∈ frontier
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
      (ext i n).toFun x = Vc x)
    (hLam : ∀ i, Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (ext i n)) atTop (𝓝 (Lam i)))
    (Ui : Fin m → SpatialCoordinates d → ℝ)
    (UiL2 : Fin m → DomainL2 Q)
    (hUiDomain : ∀ i : Fin m, UiL2 i ∈ E.domain)
    (hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Ui i)
    (hUicont : ∀ i : Fin m, ContinuousOn (Ui i)
      (closure (Q : Set (SpatialCoordinates d))))
    (hUibdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), Ui i x = Vc x)
    (hUiOrth : ∀ i : Fin m, ∀ φ : DomainL2 Q, φ ∈ Dq i →
      E.form (UiL2 i) φ = 0)
    (hUiFace : ∀ i : Fin m, Γ.measure (UiL2 i)
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) = 0)
    (hUiEnergy : ∀ i : Fin m, (Γ.measure (UiL2 i)
      (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))).toReal = Lam i)
    (hZeroTrace : ∀ i : Fin m, ∀ (w : DomainL2 Q), w ∈ E.domain →
      ∀ (wc : SpatialCoordinates d → ℝ),
      ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc) →
      (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), wc x = 0) →
      ∀ (wq : DomainL2 Q),
      ((wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          Set.indicator (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) wc) →
      wq ∈ Dq i ∧ E.form wq wq = (Γ.measure w
        (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal)
    (V' : DomainL2 Q) (V'c : SpatialCoordinates d → ℝ)
    (hV'rep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c)
    (hV'out : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) → V'c x = Vc x)
    (hV'in : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), V'c x = Ui i x) :
    V' ∈ E.domain ∧
      ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))) ∧
      E.form V' V' = E.form V V
        - ∑ i : Fin m,
            ((Γ.measure V (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d))).toReal - Lam i) ∧
      E.form V' V' ≤ E.form V V ∧
      (∀ i : Fin m, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) →
        Γ.measure V' B = Γ.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (Q : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) →
        Γ.measure V' B = Γ.measure V B) := by
  have hpatch : V' ∈ E.domain ∧
      ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))) :=
    prop_gluing_replacement_patch hd hQcube E Γ alpha halpha halpha1 m cent rad
      hrad hcellQ henlarge hdisj hcent htri Dq hDq V hV Vc hVcont hVrep hVholder
      Ui UiL2 hUiDomain hUiRep hUicont hUibdry hZeroTrace V' V'c hV'rep hV'out hV'in
  have hloc :
      (∀ i : Fin m, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) →
        Γ.measure V' B = Γ.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (Q : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) →
        Γ.measure V' B = Γ.measure V B) :=
    prop_gluing_replacement_localization E Γ m cent rad hrad hcellQ hdisj Dq hDq
      V hV Vc hVcont hVrep Ui UiL2 hUiDomain hUiRep hUicont hUibdry hUiFace
      hZeroTrace V' V'c hV'rep hV'out hV'in hpatch
  have henergy :
      E.form V' V' = E.form V V - ∑ i : Fin m,
        ((Γ.measure V (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal - Lam i) ∧
      E.form V' V' ≤ E.form V V :=
    (prop_gluing_replacement_energy E Γ m cent rad hrad hcellQ hdisj Dq hDq
      V hV Vc hVcont hVrep Ui UiL2 hUiDomain hUiRep hUicont hUibdry hUiOrth Lam
      hUiEnergy hZeroTrace V' V'c hV'rep hV'out hV'in hpatch hloc).2
  exact ⟨hpatch.1, hpatch.2, henergy.1, henergy.2, hloc.1, hloc.2⟩


end Paper
