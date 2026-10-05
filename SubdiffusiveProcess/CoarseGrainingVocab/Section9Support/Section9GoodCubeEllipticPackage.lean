module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassReduction

@[expose] public section

/-!
# The elliptic form of the residual good-cube package

`GoodCubeAnalyticPackage` (`Section9GoodCubeCalibration`) lists seven residual
displays.  Two of them — the parent/middle-quarter mass ratio and the
descendant mass ratio — are now *derived*: `Section9GoodCubeMassReduction`
proves them from a two-sided ellipticity ratio on the parent cube together
with the fixed family's volume ratios, which is exactly the manuscript's own
route (with the mass constant chosen after the family).

This file records the resulting **six-input** residual: the five remaining
analytic/probabilistic displays and the ellipticity property.
-/

set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The five residual displays of the good-cube anchor that are **not**
mass ratios. -/
structure GoodCubeEllipticDisplays (d : ℕ) (c C p0 eps1 B : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)) :
    Prop where
  tail : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
    M.P.toMeasure (coefficientLocalBadEvent M n B (bad M n) z) ≤ ENNReal.ofReal
      (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))))
  exit_lower : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
        ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)) ≤
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x)
  exit_upper : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
        meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)))
  descendant : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M _ _ _ law _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        (∀ x ∈ cubeSet B',
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
            meanExit law (cubeSet Bq) x) ∧
        (∀ x ∈ cubeSet Bq,
          meanExit law (cubeSet Bq) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2)))
  sobolev : GoodCubeReferenceDisplay d c eps1 B Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
        lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
          ENNReal.ofReal C *
            weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
            ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
              energy (aCutoff M n omega) (cubeSet Q) f.toH1Function))

/-- **The residual good-cube package in elliptic form.**

Six inputs: the five displays above and the two-sided ellipticity ratio of the
coefficient on the parent cube.  The two mass displays of
`GoodCubeAnalyticPackage` are no longer assumed. -/
def GoodCubeEllipticPackage (d : ℕ) : Prop :=
  ∃ (p0 B C0 K : ℝ) (_hp0 : 2 < p0) (_hB : 0 < B) (_hC0 : 0 < C0) (_hK : 0 < K)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)),
    ∀ (j1 j2 : ℕ), 2 ≤ j1 → 1 ≤ j2 →
      ∀ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
            Pfam0 Qfam0 Afam0 →
        (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
            (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)) →
        ∃ c0 : ℝ, 0 < c0 ∧
          (∀ eps1 : ℝ, 0 < eps1 → GoodCubeParentEllipticity d c0 eps1 B K bad) ∧
          ∀ c C eps1 : ℝ, 0 < c → c ≤ c0 → C0 ≤ C → 0 < eps1 →
            GoodCubeEllipticDisplays d c C p0 eps1 B Pfam0 Qfam0 Afam0 bad

/-- **The six-input package implies the seven-input package.**  The two mass
displays are supplied by `exists_mass_constant_of_parentEllipticity`, whose
mass constant is produced after the family. -/
theorem goodCubeAnalyticPackage_of_ellipticPackage {d : ℕ}
    (h : GoodCubeEllipticPackage d) : GoodCubeAnalyticPackage d := by
  obtain ⟨p0, B, C0, K, hp0, hB, hC0, hK, bad, h⟩ := h
  refine ⟨p0, B, C0, hp0, hB, hC0, bad, ?_⟩
  intro j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hgeom0 hinside hgeom
  obtain ⟨c0, hc0, hell, hdisp⟩ := h j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0
    hgeom0 hinside hgeom
  obtain ⟨cm, hcm, hcmc0, hmass⟩ :=
    exists_mass_constant_of_parentEllipticity c0 B K hK hc0 hgeom0 hinside hell
  refine ⟨cm, hcm, ?_⟩
  intro c C eps1 hc hccm hC heps1
  obtain ⟨hmq, hmd⟩ := hmass c eps1 hc hccm heps1
  obtain ⟨htail, hxl, hxu, hdesc, hsob⟩ := hdisp c C eps1 hc (hccm.trans hcmc0) hC heps1
  exact ⟨htail, hxl, hxu, hdesc, hmq, hmd, hsob⟩


/-! ## The ellipticity conjunct is a structural condition on `bad` -/

/-- The explicit failure of a two-sided ellipticity ratio `K` on the reference
observation box.  This is a subset of the manuscript's `G(U)ᶜ`, not a new
event: it is one component of the regularity part of `G(U)`. -/
def badEllipticity (d : ℕ) (n : ℕ) (B K : ℝ) :
    Set (nativeBox n B (0 : Lattice d) → ℝ) :=
  {f | ¬ ∃ lam : ℝ, 0 < lam ∧ ∀ x : nativeBox n B (0 : Lattice d),
    lam ≤ f x ∧ f x ≤ K * lam}

theorem goodCubeCentre_zero {d : ℕ} (n : ℕ) :
    goodCubeCentre n (0 : Lattice d) = 0 := by
  funext i
  simp [goodCubeCentre]

/-- **The ellipticity input of `GoodCubeEllipticPackage` is free.**  If the raw
bad predicate contains the ellipticity failure — which the layer-zero tail must
control in any case — then the good event carries the ratio bound on the parent
cube, with no further assumption. -/
theorem goodCubeParentEllipticity_of_bad_superset {d : ℕ} {B K c eps1 : ℝ}
    (hB : 1 ≤ B)
    {bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)}
    (hsub : ∀ (M : GMCModel d) (n : ℕ), badEllipticity d n B K ⊆ bad M n) :
    GoodCubeParentEllipticity d c eps1 B K bad := by
  intro M _ n z omega hom
  have h0 : omega ∉ coefficientLocalBadEvent M n B (bad M n) z :=
    Set.mem_iInter.mp hom 0
  have hnb : SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.restrictedCoefficientObservation
      (fun w : PotentialSample d => aCutoff M n w) (nativeBox n B (0 : Lattice d))
      (translatePotentialSequence (goodCubeCentre n z) omega) ∉ bad M n := h0
  have hne : SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.restrictedCoefficientObservation
      (fun w : PotentialSample d => aCutoff M n w) (nativeBox n B (0 : Lattice d))
      (translatePotentialSequence (goodCubeCentre n z) omega) ∉
      badEllipticity d n B K := fun h => hnb (hsub M n h)
  obtain ⟨lam, hlam, hbd⟩ := not_not.mp hne
  refine ⟨lam, hlam, ?_⟩
  intro y hy
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hmemy : ∀ i, |y i - goodCubeCentre n z i| < (3 : ℝ) ^ n / 2 :=
    mem_centeredAxisCube.mp hy
  have hx : (y - goodCubeCentre n z) ∈ nativeBox n B (0 : Lattice d) := by
    rw [nativeBox, goodCubeCentre_zero]
    refine mem_centeredAxisCube.mpr fun i => ?_
    have h1 := hmemy i
    have h2 : (3 : ℝ) ^ n / 2 ≤ B * (3 : ℝ) ^ n / 2 := by nlinarith
    have h3 : (y - goodCubeCentre n z) i - (0 : Vec d) i = y i - goodCubeCentre n z i := by
      simp
    rw [h3]
    linarith
  have hval := hbd ⟨y - goodCubeCentre n z, hx⟩
  have hrw : SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.restrictedCoefficientObservation
      (fun w : PotentialSample d => aCutoff M n w) (nativeBox n B (0 : Lattice d))
      (translatePotentialSequence (goodCubeCentre n z) omega)
      ⟨y - goodCubeCentre n z, hx⟩ = aCutoff M n omega y := by
    show aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega)
      (y - goodCubeCentre n z) = aCutoff M n omega y
    rw [SubdiffusiveProcess.CoarseGrainingVocab.aCutoff_translatePotentialSequence, sub_add_cancel]
  rwa [hrw] at hval

/-- **The residual, with the ellipticity conjunct absorbed into `bad`.**
Five displays and one containment: the raw bad predicate must contain the
ellipticity failure.  This is the shape in which the residual is a pure list  §13 estimates. -/
def GoodCubeDisplayPackage (d : ℕ) : Prop :=
  ∃ (p0 B C0 K : ℝ) (_hp0 : 2 < p0) (_hB : 1 ≤ B) (_hC0 : 0 < C0) (_hK : 0 < K)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)),
    (∀ (M : GMCModel d) (n : ℕ), badEllipticity d n B K ⊆ bad M n) ∧
    ∀ (j1 j2 : ℕ), 2 ≤ j1 → 1 ≤ j2 →
      ∀ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
            Pfam0 Qfam0 Afam0 →
        (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
            (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)) →
        ∃ c0 : ℝ, 0 < c0 ∧
          ∀ c C eps1 : ℝ, 0 < c → c ≤ c0 → C0 ≤ C → 0 < eps1 →
            GoodCubeEllipticDisplays d c C p0 eps1 B Pfam0 Qfam0 Afam0 bad

/-- The five-display package implies the six-input elliptic package. -/
theorem goodCubeEllipticPackage_of_displayPackage {d : ℕ}
    (h : GoodCubeDisplayPackage d) : GoodCubeEllipticPackage d := by
  obtain ⟨p0, B, C0, K, hp0, hB, hC0, hK, bad, hsub, h⟩ := h
  refine ⟨p0, B, C0, K, hp0, lt_of_lt_of_le zero_lt_one hB, hC0, hK, bad, ?_⟩
  intro j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  obtain ⟨c0, hc0, hdisp⟩ := h j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  exact ⟨c0, hc0, fun _ _ => goodCubeParentEllipticity_of_bad_superset hB hsub, hdisp⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
