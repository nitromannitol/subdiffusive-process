
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellUniform
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCrossIntegrability

@[expose] public section

/-!
# The two mesoscopic legs, for the frozen carrier's own fields

`wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells`
(`WholeSpaceRowsCoarseCellRow.lean`) consumes the two mesoscopic legs stated
**for the carrier's fields** `u.toFun`, `u.grad`, while the per-cell analytic
theorems (/for the energy, for the price) are stated for an
`H¹` function *on the cell*.  The carrier only promises a local `H¹` solution on
each open bounded convex domain, so the transfer is the same one
`wholeSpaceSolution_translatedCube_mass_contraction_of_local` performs for the
contraction itself: assume the leg for **every** local solution on the cell and
move it onto the carrier by the congruences of `WholeSpaceRowsCoarseCellRow`
§3b.

* §1 monotonicity of the two predicates in their constants, and the uniform
  Caccioppoli prefactor of `WholeSpaceRowsCellUniform.lean` applied cell by
  cell;
* §2 the energy leg `henergycell`, discharged for the carrier;
* §3 the price leg `hpricecell`, discharged for the carrier, with the constants
  made uniform over the index box.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. Monotonicity in the constants -/

/-- The coarse energy bound only weakens when its constant grows. -/
theorem coarseEnergyBoundOn_mono {a : Vec d → ℝ} {W V : Set (Vec d)}
    {w : Vec d → ℝ} {G : Vec d → Vec d} {T Gam Gam' : ℝ}
    (hWmeas : MeasurableSet W) (hmono : Gam ≤ Gam')
    (h : CoarseEnergyBoundOn a W V w G T Gam) :
    CoarseEnergyBoundOn a W V w G T Gam' := by
  have hnn : (0 : ℝ) ≤ ∫ x in W, w x ^ 2 ∂volume :=
    setIntegral_nonneg hWmeas fun x _ ↦ sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right hmono hnn)

/-- The mesoscopic cross price only weakens when its three constants grow. -/
theorem mesoscopicCrossPriceEnergyOn_mono {a chi : Vec d → ℝ} {W V : Set (Vec d)}
    {w : Vec d → ℝ} {G : Vec d → Vec d} {t P R Sc P' R' Sc' : ℝ}
    (hWmeas : MeasurableSet W) (hVmeas : MeasurableSet V)
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (hSc0 : 0 ≤ Sc)
    (hP : P ≤ P') (hR : 0 ≤ R) (hR' : R ≤ R') (hSc : Sc ≤ Sc')
    (hP0 : 0 ≤ P')
    (h : MesoscopicCrossPriceEnergyOn a W V w G chi t P R Sc) :
    MesoscopicCrossPriceEnergyOn a W V w G chi t P' R' Sc' := by
  intro beta hbeta hbeta1
  set M : ℝ := ∫ x in W, w x ^ 2 ∂volume with hMdef
  set E : ℝ := ∫ x in V, a x * vecNormSq (G x) ∂volume with hEdef
  have hM : (0 : ℝ) ≤ M := setIntegral_nonneg hWmeas fun x _ ↦ sq_nonneg _
  have hE : (0 : ℝ) ≤ E :=
    setIntegral_nonneg hVmeas fun x _ ↦
      mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  have htinv : (0 : ℝ) ≤ t⁻¹ * M := mul_nonneg (inv_pos.mpr ht).le hM
  have hbracket : E + Sc * (t⁻¹ * M) ≤ E + Sc' * (t⁻¹ * M) := by
    have := mul_le_mul_of_nonneg_right hSc htinv
    linarith
  have hbracket0 : (0 : ℝ) ≤ E + Sc * (t⁻¹ * M) :=
    add_nonneg hE (mul_nonneg hSc0 htinv)
  have hbeta0 : (0 : ℝ) ≤ beta⁻¹ := (inv_pos.mpr hbeta).le
  have hR0' : (0 : ℝ) ≤ R' := le_trans hR hR'
  have hfirst : beta * P * (E + Sc * (t⁻¹ * M)) ≤
      beta * P' * (E + Sc' * (t⁻¹ * M)) :=
    calc beta * P * (E + Sc * (t⁻¹ * M))
        ≤ beta * P' * (E + Sc * (t⁻¹ * M)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hP hbeta.le) hbracket0
      _ ≤ beta * P' * (E + Sc' * (t⁻¹ * M)) :=
          mul_le_mul_of_nonneg_left hbracket (mul_nonneg hbeta.le hP0)
  have hsqrt : Real.sqrt (E + Sc * (t⁻¹ * M)) ≤
      Real.sqrt (E + Sc' * (t⁻¹ * M)) := Real.sqrt_le_sqrt hbracket
  have hsecond : beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * M)) * Real.sqrt M ≤
      beta⁻¹ * R' * Real.sqrt (E + Sc' * (t⁻¹ * M)) * Real.sqrt M := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg M)
    calc beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * M))
        ≤ beta⁻¹ * R' * Real.sqrt (E + Sc * (t⁻¹ * M)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR' hbeta0) (Real.sqrt_nonneg _)
      _ ≤ beta⁻¹ * R' * Real.sqrt (E + Sc' * (t⁻¹ * M)) :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hbeta0 hR0')
  exact (h beta hbeta hbeta1).trans (by linarith)

/-- **The uniform Caccioppoli prefactor, cell by cell.**

`caccioppoliWithRHSPrefactor_le_of_thetaRatio_le` composed with
`coarseEnergyBoundOn_mono`: the constant per-cell energy bound produces
may be replaced by the cell-independent one of `WholeSpaceRowsCellUniform`. -/
theorem coarseEnergyBoundOn_mesoCell_uniformPrefactor [NeZero d]
    {a : Vec d → ℝ} {k : ℤ} {m : Fin d → ℤ} {afam : CoeffFamily d}
    {sExp tExp Ccacc Gam0 B T : ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hCcacc : 0 ≤ Ccacc) (hs : 0 < sExp) (ht : 0 < tExp)
    (hst : sExp + tExp < 1) (hGam0 : 0 ≤ Gam0)
    (hTheta : Ch02.ThetaRatio (originCube d k) sExp tExp afam ≤ B)
    (h : CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) w G T
      (caccioppoliWithRHSPrefactor Ccacc (originCube d k) afam sExp tExp *
        Gam0)) :
    CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) w G T
      (coarseCaccioppoliUniformPrefactor Ccacc sExp tExp B * Gam0) :=
  coarseEnergyBoundOn_mono (measurableSet_mesoCell k m)
    (mul_le_mul_of_nonneg_right
      (caccioppoliWithRHSPrefactor_le_of_thetaRatio_le (originCube d k) afam
        hCcacc hs ht hst hTheta) hGam0) h

/-! ## 2. The energy leg for the carrier -/

/-- A mesoscopic cell is an open bounded convex domain. -/
theorem isOpenBoundedConvexDomain_mesoCell (d : ℕ) (k : ℤ) (m : Fin d → ℤ) :
    IsOpenBoundedConvexDomain (mesoCell d k m) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet
    (mesoCentre d k m)

/-- **The energy leg on one mesoscopic cell, for the carrier's own fields.**

The datum must vanish on the cell, which makes the local equation there
homogeneous; the leg is then assumed for every local solution on the cell — the
form /produce it in — and moved onto the carrier by
`coarseEnergyBoundOn_congr`. -/
theorem coarseEnergyBoundOn_mesoCell_wholeSpaceSolution
    {a f : Vec d → ℝ} {T Gam : ℝ} {k : ℤ} {m : Fin d → ℤ}
    (u : WholeSpaceDivergenceResolventSolution a T f)
    (hf0 : ∀ x ∈ mesoCell d k m, f x = 0)
    (hlocal : ∀ v : H1Function (mesoCell d k m),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (mesoCell d k m) v
        (fun _ ↦ (0 : ℝ)) →
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) v.toFun v.grad
        T Gam) :
    CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
      T Gam := by
  classical
  have hdom := isOpenBoundedConvexDomain_mesoCell d k m
  obtain ⟨v, hval, hgrad, hsol⟩ := u.locally_weak_solution (mesoCell d k m) hdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹
      (mesoCell d k m) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun (measurableSet_mesoCell k m) fun x hx ↦ ?_
    simp [hf0 x hx]
  exact coarseEnergyBoundOn_congr (measurableSet_mesoCell k m)
    (mesoCore_subset_mesoCell k m) (fun x hx ↦ hval x hx) hgrad
    (hlocal v hsol0)

/-- **`henergycell`, discharged for the carrier over the whole index box.**

This is verbatim the `henergycell` hypothesis of
`wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells`. -/
theorem coarseEnergyBoundOn_mesoIndexBox_wholeSpaceSolution
    {a f : Vec d → ℝ} {T Gam : ℝ} {k n : ℤ} {c : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a T f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) c, f x = 0)
    (hlocal : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      ∀ v : H1Function (mesoCell d k m),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (mesoCell d k m) v
        (fun _ ↦ (0 : ℝ)) →
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) v.toFun v.grad
        T Gam) :
    ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
        T Gam := by
  intro m hm
  exact coarseEnergyBoundOn_mesoCell_wholeSpaceSolution u
    (fun x hx ↦ hf0 x (mesoCell_subset_translatedCube hm hx)) (hlocal m hm)

/-! ## 3. The price leg for the carrier -/

/-- Every price cell of the index box sits inside the contraction cube.  This is
the containment already used inside
`wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells`, isolated
here because the price leg needs it on its own. -/
theorem openCubeSet_priceCell_subset_translatedCube {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3) {m : Fin d → ℤ}
    (hm : m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n)) :
    openCubeSet (priceCell d k m) ⊆ translatedCube d (n + 1) c := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hrho1 : (0 : ℝ) < 4 / 5 * (3 : ℝ) ^ n := by positivity
  refine (openCubeSet_priceCell_subset k m).trans ?_
  exact (cubeSet_priceCell_subset_ball hrho1 (price_slack_bound hkn) hm).trans
    (ball_subset_translatedCube_succ d n c)

/-- **The price leg on one triadic cell, for the carrier's own fields.**

The exact analogue of `coarseEnergyBoundOn_mesoCell_wholeSpaceSolution` for the
price: the datum vanishes on the cell, the leg is assumed for every local
solution there — the form `mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum`
produces it in — and moved onto the carrier by
`mesoscopicCrossPriceEnergyOn_congr`. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_wholeSpaceSolution
    {a f chi : Vec d → ℝ} {T P R Sc : ℝ} {Q : TriadicCube d}
    (u : WholeSpaceDivergenceResolventSolution a T f)
    (hf0 : ∀ x ∈ openCubeSet Q, f x = 0)
    (hlocal : ∀ v : H1Function (openCubeSet Q),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) v
        (fun _ ↦ (0 : ℝ)) →
      MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) v.toFun
        v.grad chi T P R Sc) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun
      u.grad chi T P R Sc := by
  classical
  have hdom : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨v, hval, hgrad, hsol⟩ := u.locally_weak_solution (openCubeSet Q) hdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹
      (openCubeSet Q) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun (measurableSet_openCubeSet Q) fun x hx ↦ ?_
    simp [hf0 x hx]
  exact mesoscopicCrossPriceEnergyOn_congr (measurableSet_openCubeSet Q)
    (subset_refl _) (fun x hx ↦ hval x hx) hgrad (hlocal v hsol0)

/-- **`hpricecell`, discharged for the carrier over the whole index box.**

This is verbatim the `hpricecell` hypothesis of
`wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells`. -/
theorem mesoscopicCrossPriceEnergyOn_priceIndexBox_wholeSpaceSolution
    {a f chi : Vec d → ℝ} {T P R Sc : ℝ} {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3)
    (u : WholeSpaceDivergenceResolventSolution a T f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) c, f x = 0)
    (hlocal : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      ∀ v : H1Function (openCubeSet (priceCell d k m)),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹
        (openCubeSet (priceCell d k m)) v (fun _ ↦ (0 : ℝ)) →
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) v.toFun v.grad chi T P R Sc) :
    ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) u.toFun u.grad chi T P R Sc := by
  intro m hm
  exact mesoscopicCrossPriceEnergyOn_openCubeSet_wholeSpaceSolution u
    (fun x hx ↦ hf0 x (openCubeSet_priceCell_subset_translatedCube hkn hm hx))
    (hlocal m hm)

/-- **One price constant for the whole index box.**

The per-cell price produced by
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum` carries constants
that depend on the cell through its coarse ellipticities and through the sup
norm of the cutoff field there; the consumer needs a single triple.  By
`mesoscopicCrossPriceEnergyOn_mono` any uniform upper bound on the three will
do. -/
theorem mesoscopicCrossPriceEnergyOn_priceIndexBox_uniform
    {a chi : Vec d → ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d}
    {T P R Sc : ℝ} {k : ℤ} {c : Vec d} {rho : ℝ}
    {Pf Rf Scf : (Fin d → ℤ) → ℝ}
    (haNonneg : ∀ x, 0 ≤ a x) (hT : 0 < T) (hP0 : 0 ≤ P)
    (hcell : ∀ m ∈ priceIndexBox d k c rho,
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) w G chi T (Pf m) (Rf m) (Scf m))
    (hPf : ∀ m ∈ priceIndexBox d k c rho, Pf m ≤ P)
    (hRf0 : ∀ m ∈ priceIndexBox d k c rho, 0 ≤ Rf m)
    (hRf : ∀ m ∈ priceIndexBox d k c rho, Rf m ≤ R)
    (hScf0 : ∀ m ∈ priceIndexBox d k c rho, 0 ≤ Scf m)
    (hScf : ∀ m ∈ priceIndexBox d k c rho, Scf m ≤ Sc) :
    ∀ m ∈ priceIndexBox d k c rho,
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) w G chi T P R Sc := by
  intro m hm
  exact mesoscopicCrossPriceEnergyOn_mono
    (measurableSet_openCubeSet _) (measurableSet_openCubeSet _) haNonneg hT
    (hScf0 m hm) (hPf m hm) (hRf0 m hm) (hRf m hm) (hScf m hm) hP0 (hcell m hm)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
