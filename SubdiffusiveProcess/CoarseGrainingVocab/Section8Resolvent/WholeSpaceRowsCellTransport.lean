/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicLift
public import Homogenization.Sobolev.H1.Translation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The weak massive equation under a translation -/

/-- **Translation transport of the weak massive equation.**

If `u` solves `mu rho u - div (c grad u) = rho f` weakly on `z + U`, then the
pullback `H1Function.untranslate z u = u (. + z)` solves the same equation on
`U` for the translated data `c (. + z)`, `rho (. + z)`, `f (. + z)`.

The test function is transported the other way, by `H10Function.translate`, and
the three integrals are moved by `setIntegral_comp_addRight_translateSet`. -/
theorem isMassiveWeakSolutionOn_untranslate {c rho f : Vec d → ℝ} {mu : ℝ}
    {U : Set (Vec d)} (z : Vec d) (u : H1Function (translateSet z U))
    (hu : IsMassiveWeakSolutionOn c rho mu (translateSet z U) u f) :
    IsMassiveWeakSolutionOn (fun x => c (x + z)) (fun x => rho (x + z)) mu U
      (H1Function.untranslate z u) (fun x => f (x + z)) := by
  intro φ
  have h := hu (φ.translate z)
  have hmass : ∫ x in U, rho (x + z) * u.toFun (x + z) * φ.toH1Function.toFun x ∂volume =
      ∫ x in translateSet z U,
        rho x * u.toFun x * φ.toH1Function.toFun (x - z) ∂volume := by
    have := setIntegral_comp_addRight_translateSet (d := d) z U
      (fun x => rho x * u.toFun x * φ.toH1Function.toFun (x - z))
    simpa using this
  have henergy : ∫ x in U, vecDot (c (x + z) • u.grad (x + z))
        (φ.toH1Function.grad x) ∂volume =
      ∫ x in translateSet z U,
        vecDot (c x • u.grad x) (φ.toH1Function.grad (x - z)) ∂volume := by
    have := setIntegral_comp_addRight_translateSet (d := d) z U
      (fun x => vecDot (c x • u.grad x) (φ.toH1Function.grad (x - z)))
    simpa using this
  have hforce : ∫ x in U, rho (x + z) * f (x + z) * φ.toH1Function.toFun x ∂volume =
      ∫ x in translateSet z U,
        rho x * f x * φ.toH1Function.toFun (x - z) ∂volume := by
    have := setIntegral_comp_addRight_translateSet (d := d) z U
      (fun x => rho x * f x * φ.toH1Function.toFun (x - z))
    simpa using this
  show mu * ∫ x in U, rho (x + z) * (H1Function.untranslate z u).toFun x *
        φ.toH1Function.toFun x ∂volume +
      ∫ x in U, vecDot (c (x + z) • (H1Function.untranslate z u).grad x)
        (φ.toH1Function.grad x) ∂volume =
    ∫ x in U, rho (x + z) * f (x + z) * φ.toH1Function.toFun x ∂volume
  simp only [H1Function.untranslate_toFun, H1Function.untranslate_grad]
  rw [hmass, henergy, hforce]
  exact h

/-! ## The coarse energy bound under a translation -/

/-- **Translation transport of `CoarseEnergyBoundOn`.**

Both sides are plain volume set integrals, so the change of variables
`x -> x + z` moves the bound from the pair `(W, V)` to `(z + W, z + V)` with
the constant unchanged. -/
theorem coarseEnergyBoundOn_translateSet {a : Vec d → ℝ} {W V : Set (Vec d)}
    {wf : Vec d → ℝ} {G : Vec d → Vec d} {t Gam : ℝ} (z : Vec d)
    (h : CoarseEnergyBoundOn (fun x => a (x + z)) W V (fun x => wf (x + z))
      (fun x => G (x + z)) t Gam) :
    CoarseEnergyBoundOn a (translateSet z W) (translateSet z V) wf G t Gam := by
  have henergy : ∫ x in V, a (x + z) * vecNormSq (G (x + z)) ∂volume =
      ∫ x in translateSet z V, a x * vecNormSq (G x) ∂volume := by
    have := setIntegral_comp_addRight_translateSet (d := d) z V
      (fun x => a x * vecNormSq (G x))
    simpa using this
  have hmass : ∫ x in W, wf (x + z) ^ 2 ∂volume =
      ∫ x in translateSet z W, wf x ^ 2 ∂volume := by
    have := setIntegral_comp_addRight_translateSet (d := d) z W
      (fun x => wf x ^ 2)
    simpa using this
  have h' : t * ∫ x in V, a (x + z) * vecNormSq (G (x + z)) ∂volume ≤
      Gam * ∫ x in W, wf (x + z) ^ 2 ∂volume := h
  rw [henergy, hmass] at h'
  exact h'

/-! ## The coarse energy bound on a half-grid cell -/

/-- **The mesoscopic coarse energy bound on a translated cell.**

The half-grid form of `exists_mesoscopic_coarseEnergyBoundOn` (P-222): the
solution lives on the cell `z + Q`, the coefficient is `a`, and the constant is
built from the **translated** coefficient family `afam`, i.e. from a family
whose cube representative is `a (. + z)`.  That is precisely the family whose
coarse ellipticities `WholeSpaceRowsOffGridEllipticity.lambdaSq_translated_inv_le`
and `LambdaSq_translated_le` transfer back to any triadic cube containing the
cell, and hence the family for which
`WholeSpaceRowsExponentBridge.thetaRatio_translated_le` controls
`caccioppoliWithRHSPrefactor`.

The intermediate set is the translate of an admissible Caccioppoli core, which
is what `WholeSpaceRowsHalfGridCells.exists_mesoscopic_cell_datum` produces at
every point of the contraction cube. -/
theorem exists_mesoscopic_coarseEnergyBoundOn_translated (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc Gam0 : ℝ, 0 < Ccacc ∧ 0 ≤ Gam0 ∧
      ∀ (Q : TriadicCube d) (afam : CoeffFamily d) (a : Vec d → ℝ)
        (s T : ℝ) (x z : Vec d)
        (u : H1Function (translateSet z (openCubeSet Q))),
        (∀ y, (afam.coeffOn Q).toCoeffField y =
          scalarCoeffField (fun p => a (p + z)) y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹
          (translateSet z (openCubeSet Q)) u (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        (cubeScaleFactor Q) ^ 2 ≤ Ch02.lambdaS Q t afam * T →
        Ch02.lambdaS Q t afam * T ≤ 9 * (cubeScaleFactor Q) ^ 2 →
        CoarseEnergyBoundOn a (translateSet z (openCubeSet Q))
          (translateSet z (caccioppoliCoreSet Q x)) u.toFun u.grad T
          (caccioppoliWithRHSPrefactor Ccacc Q afam s t * Gam0) := by
  classical
  obtain ⟨Ccacc, Gam0, hCcacc, hGam0, hbound⟩ :=
    exists_mesoscopic_coarseEnergyBoundOn d ht ht2
  refine ⟨Ccacc, Gam0, hCcacc, hGam0, ?_⟩
  intro Q afam a s T x z u hA hu hs hs1 hst hT hpatch hlo hhi
  have hu' : IsMassiveWeakSolutionOn (fun y => a (y + z)) (fun _ ↦ (1 : ℝ)) T⁻¹
      (openCubeSet Q) (H1Function.untranslate z u) (fun _ ↦ (0 : ℝ)) :=
    isMassiveWeakSolutionOn_untranslate z u hu
  have hbase := hbound Q afam (fun y => a (y + z)) s T x
    (H1Function.untranslate z u) hA hu' hs hs1 hst hT hpatch hlo hhi
  exact coarseEnergyBoundOn_translateSet z hbase


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
