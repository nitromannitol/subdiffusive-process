module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section



theorem common_trace_class
    (d : ℕ) (hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d)) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ), ∃ hrQ : 0 < rQ,
      Q = centeredCube zQ rQ hrQ) :
    let q := centeredCube z r hr
    ∀ (hcollarGeom : closure (q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
      (E F : DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E)
      (GammaF : DirichletForm.EnergyMeasure F)
      (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
      (hdom : E.domain = F.domain)
      (horder : ∀ u ∈ E.domain,
        m * (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal ≤
          (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal ∧
        (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal ≤
          M * (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal)
      (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
      (b : SpatialCoordinates d → ℝ)
      (hb : Lane4.IsHolderOn beta (frontier (q : Set (SpatialCoordinates d))) b)
      (uE : DomainL2 Q) (UE : SpatialCoordinates d → ℝ)
      (huE : uE ∈ E.domain)
      (hUE : ContinuousOn UE (closure (Q : Set (SpatialCoordinates d))))
      (hrep : (uE : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] UE)
      (htrace : ∀ x ∈ frontier (q : Set (SpatialCoordinates d)), UE x = b x)
      (hminE : ∀ (u : DomainL2 Q), u ∈ E.domain →
        ∀ (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) →
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) →
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x) →
        GammaE.measure uE (q : Set (SpatialCoordinates d)) ≤
          GammaE.measure u (q : Set (SpatialCoordinates d)))
      (LambdaE LambdaF : ℝ)
      (hLE : IsGLB {x : ℝ | ∃ (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ),
        u ∈ E.domain ∧ ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x) ∧
        x = (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal} LambdaE)
      (hLF : IsGLB {x : ℝ | ∃ (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ),
        u ∈ F.domain ∧ ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x) ∧
        x = (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal} LambdaF),
      uE ∈ F.domain ∧
      ({u : DomainL2 Q | u ∈ E.domain ∧ ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x)} =
       {u : DomainL2 Q | u ∈ F.domain ∧ ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x)}) ∧
      (∃ (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ),
        u ∈ E.domain ∧ u ∈ F.domain ∧
        ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
        ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), U x = b x)) ∧
      (m * LambdaE ≤ LambdaF ∧ LambdaF ≤ M * LambdaE) := by
  intro q hcollarGeom E F GammaE GammaF m M hm hmM hdom horder beta hbeta hbeta1 b hb
    uE UE huE hUE hrep htrace hminE LambdaE LambdaF hLE hLF
  have hMF : uE ∈ F.domain := hdom ▸ huE
  have hElow : ∀ x ∈ {t : ℝ | ∃ (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ),
      u ∈ E.domain ∧ ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
      ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U) ∧
      (∀ y ∈ frontier (q : Set (SpatialCoordinates d)), U y = b y) ∧
      t = (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal}, LambdaE ≤ x :=
    mem_lowerBounds.mp ((le_isGLB_iff hLE).mp le_rfl)
  have hFlow : ∀ x ∈ {t : ℝ | ∃ (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ),
      u ∈ F.domain ∧ ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
      ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U) ∧
      (∀ y ∈ frontier (q : Set (SpatialCoordinates d)), U y = b y) ∧
      t = (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal}, LambdaF ≤ x :=
    mem_lowerBounds.mp ((le_isGLB_iff hLF).mp le_rfl)
  refine ⟨hMF, ?_, ?_, ?_, ?_⟩
  · ext u
    simp only [Set.mem_setOf_eq, hdom]
  · exact ⟨uE, UE, huE, hMF, hUE, hrep, htrace⟩
  · exact (le_isGLB_iff hLF).mpr (by
      rw [mem_lowerBounds]
      intro x hx
      obtain ⟨u, U, huF, hU, hrepU, htrU, rfl⟩ := hx
      have huE' : u ∈ E.domain := hdom.symm ▸ huF
      calc m * LambdaE ≤
            m * (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal :=
            mul_le_mul_of_nonneg_left
              (hElow _ ⟨u, U, huE', hU, hrepU, htrU, rfl⟩) (le_of_lt hm)
        _ ≤ (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal :=
            (horder u huE').1)
  · rw [mul_comm M LambdaE, ← div_le_iff₀ (lt_of_lt_of_le hm hmM)]
    exact (le_isGLB_iff hLE).mpr (by
      rw [mem_lowerBounds]
      intro x hx
      obtain ⟨u, U, huE', hU, hrepU, htrU, rfl⟩ := hx
      have huF : u ∈ F.domain := hdom ▸ huE'
      rw [div_le_iff₀ (lt_of_lt_of_le hm hmM)]
      calc LambdaF ≤ (GammaF.measure u (q : Set (SpatialCoordinates d))).toReal :=
            hFlow _ ⟨u, U, huF, hU, hrepU, htrU, rfl⟩
        _ ≤ M * (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal :=
            (horder u huE').2
        _ = (GammaE.measure u (q : Set (SpatialCoordinates d))).toReal * M :=
            mul_comm _ _)


end
end Paper
