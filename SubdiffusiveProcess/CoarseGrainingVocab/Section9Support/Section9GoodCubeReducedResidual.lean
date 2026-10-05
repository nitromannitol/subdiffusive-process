module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-!
# Historical good-cube residual after the exit-upper transfer

This pre-v4 contract is retained for its existing conditional consumers.
New analytic work targets `GoodCubeSelectedReducedPackage` in
`Section9GoodCubeReducedV4` and its exact v4 assembly in
`Section9GoodCubeSelectedAssembly`; that path requires estimates for one
selected template and obtains killed densities from `LocalDiffusionData`.

§13 at

the residual good-cube estimates left `GoodCubeResidualPackage d` with six displays.  Two of them —
`exit_upper`  and the **upper** half of `descendant`
 — are not independent estimates: `Section9GoodCubeExitTransfer`
derives both from the residual's own `sobolev` display through the sealed
local resolvent exit bound, once the law carries a continuous killed
density on the cube.  `GoodCubeReducedDisplays` is the residual with those two
half-displays deleted and the killed density added as a structural clause, and
`goodCubeAnalyticPackage_of_reduced` proves that it still implies the coupled good-cube estimates's
`GoodCubeAnalyticPackage`, hence (through that collection's calibration) the
installed version 2 block.

Two bookkeeping points.

* The Sobolev display is carried at a **fixed** constant `A0`, not at the
  running `C`.  It has to be: the local resolvent exit bound returns the mean
  exit bound with constant `C_E · A^{C_E}`, so a Sobolev constant that grows
  with `C` would never be absorbed.  The package's exported `C0` is
  `max 2 (max A0 (C_E · A0^{C_E}))`, which is a constraint of this historical
  all-family interface. The source  chooses its mass constant
  after the geometry; the selected v4 residual preserves that freedom.

* The raw bad predicate is not pinned to `goodCubeBad`, only required to
  contain it.  the residual good-cube estimates's `GoodCubeResidualPackage` pins it, and that
  over-commits on the two mass displays; see the docstring of
  `GoodCubeReducedPackage` and P378-F2.

* The weighted mass of every family cube must be finite and nonzero for the
  normalisation of the Sobolev display; on the good event this is free, by the
  two-sided ellipticity of P373-F2
  (`exists_parentEllipticity_scale_of_not_goodCubeBad`), whose ratio is allowed
  to depend on the scale.  This is the one place where the non-uniform
  ellipticity of P373-F1 is enough.
-/

set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ahom ahom_pos)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## The weighted mass of a family cube on the good event -/

/-- The native box of unit box factor is the parent cube of the local family. -/
theorem nativeBox_one_eq_cubeSet (n : ℕ) (z : Lattice d) :
    nativeBox n 1 z = cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n) := by
  rw [nativeBox, one_mul]
  rfl

/-- **The weighted mass of a family cube is finite and nonzero on the good
event.**  Both bounds come from the scale-dependent two-sided ellipticity of
P373-F2, which is all that the concrete layer-zero event supplies. -/
theorem weightedMeasure_pos_lt_top_of_not_goodCubeBad (M : GMCModel d) (n : ℕ)
    (z : Lattice d) (omega : PotentialSample d)
    (hom : omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z)
    {Q : Cube d} (hQ : 0 < Q.2)
    (hsub : cubeSet Q ⊆ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) :
    weightedMeasure (aCutoff M n omega) (cubeSet Q) ≠ 0 ∧
      weightedMeasure (aCutoff M n omega) (cubeSet Q) ≠ ⊤ := by
  obtain ⟨lam, hlam, hbd⟩ :=
    exists_parentEllipticity_scale_of_not_goodCubeBad M n z omega hom
  set Lam : ℝ :=
    Real.exp (2 * (logLipschitzThreshold M n * (3 : ℝ) ^ n)) * lam with hLam
  have hbox := nativeBox_one_eq_cubeSet (d := d) n z
  have hbd' : ∀ y ∈ cubeSet Q, lam ≤ aCutoff M n omega y ∧ aCutoff M n omega y ≤ Lam := by
    intro y hy
    exact hbd y (hbox ▸ hsub hy)
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) := volume_cubeSet hQ.le
  constructor
  · have hlow := le_weightedMeasure_of_le (aCutoff M n omega) (measurableSet_cubeSet Q)
      (fun x hx => (hbd' x hx).1)
    rw [hvol, ← ENNReal.ofReal_mul hlam.le] at hlow
    have hpos : (0 : ℝ) < lam * Q.2 ^ d := by positivity
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hlow)
  · have hup := weightedMeasure_le_of_le (aCutoff M n omega) (measurableSet_cubeSet Q)
      (fun x hx => (hbd' x hx).2)
    rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hup
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup

/-! ## The reduced displays -/

/-- The residual of the good-cube anchor after the exit-upper transfer:
`exit_upper` and the upper half of `descendant` are gone, and the continuous
killed density  is a clause.  The raw bad
predicate is a parameter, not `goodCubeBad`; see `GoodCubeReducedPackage`. -/
structure GoodCubeReducedDisplays (d : ℕ) (c A0 p0 eps1 : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
    (bad : (M : GMCModel d) → (n : ℕ) →
      Set (nativeBox n 1 (0 : Lattice d) → ℝ)) : Prop where
  /-- The weighted Sobolev display at the intrinsic clock, at the fixed
  constant `A0`. -/
  sobolev : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ Q ∈ Qfam, GoodCubeSobolevDisplay (aCutoff M n omega) p0 A0
        (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) Q)
  /-- The continuous killed transition density on every family cube
  (P363-F3). -/
  killed : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega law _ Qfam _ =>
      ∀ Q ∈ Qfam, HasContinuousKilledDensity (aCutoff M n omega) law (cubeSet Q))
  /-- The parent mean-exit lower bound on the middle quarter. -/
  exit_lower : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
        ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)) ≤
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x)
  /-- The **lower** half of the descendant exit estimate. -/
  descendant_lower : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M _ _ _ law _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ∀ x ∈ cubeSet B',
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
            meanExit law (cubeSet Bq) x)
  /-- The middle-quarter mass display. -/
  mass_quarter : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n z omega _ _ _ _ =>
      ENNReal.ofReal c *
          weightedMeasure (aCutoff M n omega)
            (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
        weightedMeasure (aCutoff M n omega)
          (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n)))
  /-- The descendant mass display. -/
  mass_descendant : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 bad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
          weightedMeasure (aCutoff M n omega) (cubeSet B'))

/-- **The reduced residual of the good-cube anchor.**  Four analytic displays
(`sobolev`, `exit_lower`, `descendant_lower`, and the two mass displays), the
structural killed-density clause, and the layer-zero tail of the bad predicate
they all speak about.

The predicate is **not** pinned to `goodCubeBad`; it is only required to
*contain* it, so that P373-F2's two-sided ellipticity — and with it the
finiteness and non-vanishing of every family cube's weighted mass — is still
available.  Pinning it, as `GoodCubeResidualPackage` does, over-commits: the
concrete layer-zero event constrains only the log-Lipschitz constant
`logLipschitzThreshold M n` of `log a_n` on the native box, so on it the mass
ratio `|V|_a / |U|_a` is only bounded below by `4^{-d}e^{-Θ_n 3^n}`, and
`Θ_n 3^n → ∞`; a coefficient with the admissible linear ramp
`log a_n(x) = Θ_n x_1` lies in that event and makes the ratio smaller than any
fixed `c` once `n` is large.  The manuscript agrees:  puts "the
finitely many mass ratios" inside `G(U)`, i.e. inside the bad predicate, and
the tail of that component is the weighted-volume estimate.  So
the two mass displays are carried here together with the freedom to enlarge the
event that carries them.  See P378-F2 in the collection report. -/
def GoodCubeReducedPackage (d : ℕ) : Prop :=
  ∃ (p0 A0 C1 c1 : ℝ) (_hp0 : 2 < p0) (_hA0 : 1 ≤ A0) (_hC1 : 2 ≤ C1) (_hc1 : 0 < c1)
    (bad : (M : GMCModel d) → (n : ℕ) →
      Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
    (∀ (M : GMCModel d) (n : ℕ), goodCubeBad M n ⊆ bad M n) ∧
    (∀ M : GMCModel d, M.delta ≤ c1 → ∀ (n : ℕ) (z : Lattice d),
      M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤ ENNReal.ofReal
        (C1 * Real.exp (-(c1 * (c1 / (M.delta ^ 2 * Real.log M.delta ^ 2)))))) ∧
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
        ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ c1 ∧
          ∀ c eps1 : ℝ, 0 < c → c ≤ c0 → 0 < eps1 →
            GoodCubeReducedDisplays d c A0 p0 eps1 Pfam0 Qfam0 Afam0 bad

/-! ## Structural helpers -/

/-- The good event excludes the layer-zero event. -/
theorem not_mem_layerZero_of_goodCubeEvent {n : ℕ} {B eps1 : ℝ}
    {E0 : Lattice d → Set (PotentialSample d)} {z : Lattice d}
    {omega : PotentialSample d}
    (hom : omega ∈ goodCubeEvent (goodCubeEventField n B eps1 E0) z) :
    omega ∉ E0 z :=
  Set.mem_iInter.mp hom 0

/-- The parent cube is the transported image of the reference family's own
top cube. -/
theorem parent_mem_transported_family {Qfam0 : Set (Cube d)}
    (hself : ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)) ∈ Qfam0) (n : ℕ) (z : Lattice d) :
    (goodCubeCentre n z, (3 : ℝ) ^ n) ∈ goodCubeReferenceFamily Qfam0 n z := by
  refine ⟨((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)), hself, ?_⟩
  simp [goodCubeReferenceTransport]

/-! ## The reduction -/

/-- **The reduced residual implies the seven-display analytic package**, hence
(through the coupled good-cube estimates's calibration) the installed version 2 block.  The two deleted
half-displays are recovered from the `sobolev` display and the killed density
through the sealed local resolvent exit bound. -/
theorem goodCubeAnalyticPackage_of_reduced (hd : 2 ≤ d)
    (h : GoodCubeReducedPackage d) : GoodCubeAnalyticPackage d := by
  obtain ⟨p0, A0, C1, c1, hp0, hA0, hC1, hc1, bad, hsub, htail, h⟩ := h
  obtain ⟨CE, hCE, hexit⟩ := exists_goodCube_exit_upper_constant hp0
  have hC0pos : 0 < max C1 (max A0 (CE * A0 ^ CE)) :=
    lt_of_lt_of_le (lt_of_lt_of_le two_pos hC1) (le_max_left _ _)
  refine ⟨p0, 1, max C1 (max A0 (CE * A0 ^ CE)), hp0, one_pos, hC0pos, bad, ?_⟩
  intro j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  obtain ⟨c0, hc0, hc0c1, hdisp⟩ := h j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  refine ⟨c0, hc0, ?_⟩
  intro c C eps1 hc hcc0 hCC0 heps1
  obtain ⟨hsob, hker, hxl, hdl, hmq, hmd⟩ := hdisp c eps1 hc hcc0 heps1
  have hC1C : C1 ≤ C := le_trans (le_max_left _ _) hCC0
  have hA0C : A0 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC0
  have hCEC : CE * A0 ^ CE ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC0
  have hcc1 : c ≤ c1 := hcc0.trans hc0c1
  -- the layer-zero tail, transported from `(c1, C1)` to `(c, C)`
  have htailC : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
      M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤ ENNReal.ofReal
        (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))) := by
    intro M hdelta n z
    refine (htail M (hdelta.trans hcc1) n z).trans (ENNReal.ofReal_le_ofReal ?_)
    have hD : (0 : ℝ) ≤ M.delta ^ 2 * Real.log M.delta ^ 2 := by positivity
    have hmono : c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) ≤
        c1 * (c1 / (M.delta ^ 2 * Real.log M.delta ^ 2)) := by
      rcases eq_or_lt_of_le hD with hD0 | hD0
      · rw [← hD0]; simp
      · gcongr
    have hexp : Real.exp (-(c1 * (c1 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) ≤
        Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul hC1C hexp (Real.exp_pos _).le
      (le_trans (le_trans zero_le_two hC1) hC1C)
  -- the exit-upper bound on an arbitrary cube of the transported family
  have hup : ∀ (M : GMCModel d), M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
      ∀ omega ∈ goodCubeEvent
        (goodCubeEventField n 1 eps1 (coefficientLocalBadEvent M n 1 (bad M n))) z,
      ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusion (aCutoff M n omega) (aCutoff M n omega) law →
        ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z, ∀ x ∈ cubeSet Q,
          meanExit law (cubeSet Q) x ≤
            ENNReal.ofReal (C *
              SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2) := by
    intro M hdelta n z omega hom law hdiff Q hQfam x hx
    have hom0 : omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z := fun hmem =>
      not_mem_layerZero_of_goodCubeEvent hom
        (Set.preimage_mono (Set.preimage_mono (hsub M n)) hmem)
    have hQ2 : 0 < Q.2 := side_pos_transported hg0.side_pos n z Q hQfam
    have hclock : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_pos (ahom_pos M) hQ2
    obtain ⟨hm0, hmt⟩ := weightedMeasure_pos_lt_top_of_not_goodCubeBad M n z omega hom0
      hQ2 (cubeSet_transported_subset hin n z Q hQfam)
    refine (hexit d hd (aCutoff M n omega) law hdiff
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) A0 hA0 Q hQ2 hclock
      hm0 hmt (hsob M hdelta n z omega hom law hdiff Q hQfam)
      (hker M hdelta n z omega hom law hdiff Q hQfam) x hx).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hCEC hclock.le
  refine ⟨htailC, hxl, ?_, ?_, hmq, hmd, ?_⟩
  · -- exit_upper on the parent cube
    intro M hdelta n z omega hom law hdiff x hx
    exact hup M hdelta n z omega hom law hdiff _
      (parent_mem_transported_family hg0.self_mem n z) x hx
  · -- descendant: lower half from the residual, upper half from the transfer
    intro M hdelta n z omega hom law hdiff B' hB' Bq hBq hcomp
    exact ⟨hdl M hdelta n z omega hom law hdiff B' hB' Bq hBq hcomp,
      hup M hdelta n z omega hom law hdiff Bq hBq⟩
  · -- sobolev, at the running constant
    intro M hdelta n z omega hom law hdiff Q hQfam f
    refine (hsob M hdelta n z omega hom law hdiff Q hQfam f).trans ?_
    gcongr

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
