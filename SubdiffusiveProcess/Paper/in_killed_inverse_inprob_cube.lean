module

public import SubdiffusiveProcess.Paper.in_killed_inverse_inprob
public import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy

@[expose] public section

/-!
# `in_killed_inverse_inprob_cube`: the cube-by-cube form of `in_killed_inverse_inprob`

For every rational-centred cube of triadic side, the killed inverse of the cutoff-`N` coefficient (for the
canonical killed response space) converges in probability, in operator norm, to a measurable random operator.
Derived from the enumerated form by choosing an enumeration of the rational triadic cubes; the uniqueness
hypothesis `hUniq` is inherited unchanged.
-/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Cube-by-cube convergence in probability of the killed inverses** (rational triadic cubes; the canonical
killed response space), from the uniqueness hypothesis `hUniq`. -/
theorem in_killed_inverse_inprob_cube
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (hUniq : ∃ δU : ℝ, 0 < δU ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δU →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ (GE0 GF0 : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i))),
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (NE n) (Z i) (hR i))) atTop
            (𝓝 (GE0 i β))) →
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (NF n) (Z i) (hR i))) atTop
            (𝓝 (GF0 i β))) →
        ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i, GE0 i β = GF0 i β) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∀ c : Fin d, ∃ q : ℚ, z c = (q : ℝ)) → (∃ m : ℤ, r = (3 : ℝ) ^ m) →
      ∀ (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
        ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖),
      ∃ G : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        Measurable G ∧
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
          (chaosSampleLaw M).toMeasure {β | eps ≤
            ‖volumeResponseOperator (killedResponseSpace hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N z hr) - G β‖} ≤
            ENNReal.ofReal rho := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, hmain⟩ := in_killed_inverse_inprob d hd hInterp E Pin X W Cp Sob hUniq
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hz hr3 hP
  let S : Set ((Fin d → ℝ) × ℝ) := {p | (∀ c : Fin d, ∃ q : ℚ, p.1 c = (q : ℝ)) ∧
    ∃ m : ℤ, p.2 = (3 : ℝ) ^ m}
  have hScount : S.Countable := by
    have hrange : (Set.range (fun p : (Fin d → ℚ) × ℤ =>
        ((fun c => ((p.1 c : ℚ) : ℝ), (3 : ℝ) ^ p.2) : (Fin d → ℝ) × ℝ))).Countable :=
      Set.countable_range _
    refine hrange.mono ?_
    rintro ⟨w, s⟩ ⟨hw, m, hm⟩
    choose q hq using hw
    exact ⟨(q, m), by simp only [Prod.mk.injEq]; exact ⟨funext fun c => (hq c).symm, hm.symm⟩⟩
  have hSne : S.Nonempty := ⟨(z, r), hz, hr3⟩
  obtain ⟨f, hf⟩ := hScount.exists_eq_range hSne
  have hfS : ∀ i, f i ∈ S := fun i => by rw [hf]; exact ⟨i, rfl⟩
  let Z : ℕ → SpatialCoordinates d := fun i => (f i).1
  let R : ℕ → ℝ := fun i => (f i).2
  have hR : ∀ i, 0 < R i := fun i => by
    obtain ⟨m, hm⟩ := (hfS i).2
    show 0 < (f i).2
    rw [hm]; exact zpow_pos (by norm_num) m
  let Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)) :=
    fun i => killedResponseSpace (centeredCube_killedPoincare (Z i) (hR i))
  have hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m :=
    fun i => hfS i
  have hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
      (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r' := by
    intro z' r' h1 h2
    have hmem : (z', r') ∈ Set.range f := by rw [← hf]; exact ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, by simp only [Z]; rw [hi], by simp only [R]; rw [hi]⟩
  obtain ⟨G, hGmeas, hGprob⟩ := hmain M Rm Sreg It H hH hδ Z R hR Sspace (fun i => rfl) hrat hcomp
  obtain ⟨i0, hi0⟩ : (z, r) ∈ Set.range f := by rw [← hf]; exact ⟨hz, hr3⟩
  have hzi : Z i0 = z := by simp only [Z]; rw [hi0]
  have hri : R i0 = r := by simp only [R]; rw [hi0]
  subst hzi
  subst hri
  exact ⟨G i0, hGmeas i0, hGprob i0⟩

end SubdiffusiveProcess.Paper
