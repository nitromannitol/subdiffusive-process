import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

/-!
# Coefficient locality of good-cube harmonic estimates

Weak harmonicity on a domain depends only on the coefficient there. The same
holds for harmonic contraction on a family whose outer cubes lie in that
domain. A predicate constant on observation fibres is exactly the pullback
of a predicate on the observations; this identifies the raw failure event
before taking a restricted-measurable hull.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Weak harmonicity is invariant under coefficient equality on its domain. -/
theorem goodCube_weakHarmonic_congr_coeff {d : ℕ} {a b h : Vec d → ℝ}
    {U : Set (Vec d)} (hab : Set.EqOn a b U) :
    WeakHarmonic a U h ↔ WeakHarmonic b U h := by
  constructor
  · rintro ⟨hcont, henergy⟩
    refine ⟨hcont, fun W hW hc hsub => ?_⟩
    obtain ⟨u, hu, hE⟩ := henergy W hW hc hsub
    refine ⟨u, hu, fun phi => ?_⟩
    have hae : ∀ᵐ x ∂volume.restrict W,
        a x * vecDot (u.grad x) (phi.toH1Function.grad x)
          = b x * vecDot (u.grad x) (phi.toH1Function.grad x) := by
      filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
      rw [hab (hsub (subset_closure hx))]
    rw [← integral_congr_ae hae]
    exact hE phi
  · rintro ⟨hcont, henergy⟩
    refine ⟨hcont, fun W hW hc hsub => ?_⟩
    obtain ⟨u, hu, hE⟩ := henergy W hW hc hsub
    refine ⟨u, hu, fun phi => ?_⟩
    have hae : ∀ᵐ x ∂volume.restrict W,
        b x * vecDot (u.grad x) (phi.toH1Function.grad x)
          = a x * vecDot (u.grad x) (phi.toH1Function.grad x) := by
      filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
      rw [Set.EqOn.symm hab (hsub (subset_closure hx))]
    rw [← integral_congr_ae hae]
    exact hE phi

/-- Harmonic contraction only depends on the coefficient on a set containing
all outer cubes in the family. -/
theorem goodCube_localHarmonicOscillation_congr_coeff {d : ℕ}
    {a b : Vec d → ℝ} {S : Set (Vec d)} {eps0 : ℝ}
    {Pfam : Set (Cube d × Cube d)}
    (hab : Set.EqOn a b S) (hin : ∀ p ∈ Pfam, cubeSet p.2 ⊆ S) :
    LocalHarmonicOscillation a eps0 Pfam ↔ LocalHarmonicOscillation b eps0 Pfam := by
  constructor
  · rintro ⟨hcontr⟩
    refine ⟨fun p hp h hwh => ?_⟩
    have hwhb : WeakHarmonic a (cubeSet p.2) h :=
      (goodCube_weakHarmonic_congr_coeff (hab.mono (hin p hp))).mpr hwh
    exact hcontr p hp h hwhb
  · rintro ⟨hcontr⟩
    refine ⟨fun p hp h hwh => ?_⟩
    have hwha : WeakHarmonic b (cubeSet p.2) h :=
      (goodCube_weakHarmonic_congr_coeff (hab.mono (hin p hp))).mp hwh
    exact hcontr p hp h hwha

/-- The failure of a predicate constant on observation fibres is exactly a
pullback from the observation space. -/
theorem goodCube_exists_restricted_failure {Ω V : Type*} (observe : Ω → V)
    (P : Ω → Prop) (hlocal : ∀ ω ω', observe ω = observe ω' → (P ω ↔ P ω')) :
    ∃ bad : Set V, observe ⁻¹' bad = {ω | ¬ P ω} := by
  refine ⟨observe '' {ω | ¬ P ω}, ?_⟩
  ext ω
  constructor
  · intro h
    obtain ⟨ω', hω', hobs⟩ := h
    intro hP
    exact hω' ((hlocal ω' ω hobs).mpr hP)
  · intro h
    exact ⟨ω, h, rfl⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
