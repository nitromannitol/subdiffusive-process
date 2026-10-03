module

public import SubdiffusiveProcess.Analysis.InteriorComparisonCollapse
public import SubdiffusiveProcess.Analysis.InteriorComparisonErrorTransport
public import SubdiffusiveProcess.Analysis.InteriorComparisonLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.ForceOverlapSlot
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.ForceBesovSlot

@[expose] public section




namespace SubdiffusiveProcess.InteriorComparisonEngine

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube Mat
open Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.InteriorComparisonCollapse
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- The loop of `aux_icc_loop` on the translated cube `y + 𝔠_{n-2}` in its
physical form, with `IsWeaklyHarmonicOn (fun _ => 1)`. -/
theorem aux_icc_loop_translated (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (s : ℝ) (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (n : ℕ) (y : Vec d)
        (a : Vec d → ℝ) (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
        (a0 : ℝ), 0 < a0 →
      let Q := originCube d ((n : ℤ) - 2)
      let s1 : FractionalOrder := ⟨s / 3, by positivity, by linarith⟩
      let smid : FractionalOrder := ⟨s / 2, by positivity, by linarith⟩
      let s2 : FractionalOrder := ⟨s, hs0, by linarith⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2 FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (dataY.toTriadicCoeffFamily.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ),
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ E S D : ℝ,
        Ch02.HomogenizationErrorOnCube Q (s / 6) Ch02.MultiscaleExponent.infinity
          (Ch02.MultiscaleExponent.finite 2) dataY.toTriadicCoeffFamily
          (scalarMatrix (d := d) a0) ≤ E →
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (dataY.toTriadicCoeffFamily.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤
            ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
      ∀ (ubar : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (translatedCube d ((n : ℤ) - 2) y) ubar →
        MemH10 (translatedCube d ((n : ℤ) - 2) y)
          (fun p ↦ ubar.toFun p - uPhysical p) →
        normalizedL2On (translatedCube d ((n : ℤ) - 2) y)
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n a0 smid s1 s2 E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ := aux_icc_loop d hd
  refine ⟨C, hCtop, ?_⟩
  intro s hs0 hs4 n y a dataY a0 ha0
  dsimp only
  intro g hg u0 hu0 uPhysical hu0Physical E S D hE hS hD
  have hDset : translatedCube d ((n : ℤ) - 2) y =
      translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))) := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hDset]
  intro ubar hharm ht
  exact hloop s hs0 hs4 n y a dataY a0 ha0 g hg u0 hu0 uPhysical ubar
    (isUnitWeaklyHarmonicOn_iff.mpr hharm) ht hu0Physical E S D hE hS hD

/-- **The deterministic interior comparison at the original powers.**  Given
the manuscript prices of the physical weighted local energy on the comparison
cube (`hS`), every unit-harmonic replacement obeys the interior estimate on the
smaller observation window, with a constant depending only on `d`, `Cerr` and
the energy constant `K`. -/
theorem aux_icc_interior_comparison (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cerr K : ℝ) (hCerr : 0 < Cerr) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : ℝ), 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ (m n : ℕ), n + 5 ≤ m → ∀ (z x y : Vec d),
      x ∈ truncatedCube d m ((n : ℤ) - 3) z →
      ∀ (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
        (dataY : ScalarTriadicCoeffData (fun q => a (q + y))) (a0 : ℝ), 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two g) →
      translatedCube d ((n : ℤ) - 2) y ⊆ truncatedCube d m ((n : ℤ) - 1) x →
      truncatedCube d m ((n : ℤ) - 4) x ⊆ translatedCube d ((n : ℤ) - 2) y →
      ∀ uD : H1Function (translatedCube d ((n : ℤ) - 2) y),
        (∀ q, uD.toFun q = u.toFun q) →
      (∀ u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2))),
        (∀ p, u0.grad p = u.grad (p + y)) →
        ∀ s1 smid : FractionalOrder, s1.1 < smid.1 →
        weightedLocalSymmetricEnergyLp (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            (dataY.toTriadicCoeffFamily.coeffOn (originCube d ((n : ℤ) - 2)))
            u0 s1 smid FiniteLpExponent.two ≤
          ENNReal.ofReal (dirichletWeightedEnergyFactor s1.1 smid.1 *
            Real.sqrt (K *
              (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On (truncatedCube d m n x)
                    (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) ^ 2 +
                s ^ (-12 : ℝ) * a0⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
                  (fractionalSeminormOn (truncatedCube d m n x) s g).toReal ^ 2)))) →
      ∀ (v : H1Function (translatedCube d ((n : ℤ) - 2) y)),
        IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (translatedCube d ((n : ℤ) - 2) y) v →
        HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD →
        normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
            (fun q => u.toFun q - v.toFun q) ≤
          C * s ^ (-3 / 2 : ℝ) *
              (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
                (s / 8) Ch02.MultiscaleExponent.infinity
                (Ch02.MultiscaleExponent.finite 2) data.toTriadicCoeffFamily a0).toReal *
              normalizedL2On (truncatedCube d m n x)
                (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
            C * s ^ (-15 / 2 : ℝ) * a0⁻¹ * (3 : ℝ) ^ ((1 + s) * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal := by
  classical
  obtain ⟨Cloop, hCloopTop, hloop⟩ := aux_icc_loop_translated d hd
  obtain ⟨Cd, hCd, hforce⟩ := exists_interiorForceOverlap_le_windowSeminorm d
  obtain ⟨Cb, hCb, hbesov⟩ := exists_interiorForceBesov_le_windowSeminorm d
  have hCX0 := aux_icc_constX_nonneg d Cloop K
  have hCF0 := aux_icc_constF_nonneg d Cloop (Kslot := K) hCd.le hCerr.le hCb.le
  refine ⟨(9 : ℝ) ^ d * (aux_icc_constX d Cloop K +
    aux_icc_constF d Cloop K Cd Cerr Cb + 1), by positivity, ?_⟩
  intro s hs0 hs4 m n hnm z x y hx a data dataY a0 ha0 herr u g hweak hgex hloc hcov
    uD hfval hS v hharm htrace
  have hslt : s < 1 := by linarith
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  set Er : ℝ := (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
    (s / 8) Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
    data.toTriadicCoeffFamily a0).toReal with hErdef
  set Wq : ℝ := normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
    (fun q ↦ u.toFun q - averageOn (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun)
    with hWqdef
  set Gq : ℝ := (fractionalSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x) s g).toReal
    with hGqdef
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hWq0 : 0 ≤ Wq := Section6Iteration.normalizedL2On_nonneg _ _
  have hGq0 : 0 ≤ Gq := ENNReal.toReal_nonneg
  have hP1 : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) * Er * Wq :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hEr0) hWq0
  have hP2 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) * a0⁻¹ *
      (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr ha0.le)) (Real.rpow_nonneg (by norm_num) _)) hGq0
  -- the anchored error: finite, and below `Cerr`
  have hErrNeTop : paperHomogenizationError (originCube d ((n : ℤ) + 2))
      ((n : ℤ) + 2) (s / 8) Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 2) data.toTriadicCoeffFamily a0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  have hErC : Er ≤ Cerr := ENNReal.toReal_le_of_le_ofReal hCerr.le herr
  have herrEr : paperHomogenizationError (originCube d ((n : ℤ) + 2))
      ((n : ℤ) + 2) (s / 8) Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 2) data.toTriadicCoeffFamily a0 ≤
        ENNReal.ofReal Er := by
    rw [hErdef, ENNReal.ofReal_toReal hErrNeTop]
  -- the source and the three slots
  obtain ⟨sOrder, hsval, hgWsp⟩ := hgex
  have hsO : sOrder = (⟨s, hs0, hslt⟩ : FractionalOrder) := Subtype.ext hsval
  rw [hsO] at hgWsp
  have hsubOpen : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hloc hp).2
  obtain ⟨g0, hg0, hg0eq, u0, v0, hu0forced, _hv0, _huv0, hu0val, hu0grad⟩ :=
    aux_icc_localSourceComparisonDatum m ((n : ℤ) - 2) y
      (⟨s, hs0, hslt⟩ : FractionalOrder) dataY u g hweak hgWsp hsubOpen a0 ha0
  have hSb := hS u0 hu0grad
    (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
    (by dsimp only; linarith)
  have hDforce := hforce (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc
    g g0 hgWsp hg0 hg0eq
  have hcontain : translateSet (y - z)
      (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
        cubeSet (originCube d ((n : ℤ) + 2)) :=
    closedOffGridCube_subset_originAnchorParent hx hloc
  have hEtrans := aux_icc_errorTransport n s Er a0 a z y data dataY hs0
    (by linarith) hEr0 ha0 herrEr hcontain
  have hEtrans' : Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
      Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
      dataY.toTriadicCoeffFamily (scalarMatrix (d := d) a0) ≤
        Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) := by
    rw [show s / 8 * (4 : ℝ) = s / 2 by ring]
    exact hEtrans
  have hH10 : MemH10 (translatedCube d ((n : ℤ) - 2) y)
      (fun p ↦ v.toFun p - u.toFun p) :=
    memH10_sub_physical_of_hasZeroTraceDifferenceOn htrace hfval
  have hL := hloop s hs0 hs4 n y a dataY a0 ha0 g0 hg0 u0 hu0forced u.toFun hu0val
    _ _ _ hEtrans' hSb hDforce v hharm hH10
  have hBv := hbesov (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc g hgWsp
    (s / 2) (by dsimp only; linarith)
  have hC := aux_icc_loopBound_le Cloop hK hCd hCb n hs0 hs4
    ha0 hEr0 hErC hWq0 hGq0 (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s, hs0, hslt⟩ : FractionalOrder) rfl rfl rfl (originCube d ((n : ℤ) - 2))
    (fun p ↦ g (p + y)) hBv
  have hshrink := aux_icc_windowShrink hnm hxDomain (uD := uD) (v := v)
    (u := u.toFun) hfval hcov
  set CX := aux_icc_constX d Cloop K with hCXdef
  set CF := aux_icc_constF d Cloop K Cd Cerr Cb with hCFdef
  have hg0fun : g0 = fun p ↦ g (p + y) := funext hg0eq
  rw [hg0fun] at hL
  have hmain := hshrink.trans (mul_le_mul_of_nonneg_left (hL.trans hC) (by positivity))
  refine hmain.trans ?_
  have hb1 : (9 : ℝ) ^ d * CX ≤ (9 : ℝ) ^ d * (CX + CF + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hCF0]) (by positivity)
  have hb2 : (9 : ℝ) ^ d * CF ≤ (9 : ℝ) ^ d * (CX + CF + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hCX0]) (by positivity)
  calc (9 : ℝ) ^ d * (CX * s ^ (-3 / 2 : ℝ) * Er * Wq +
        CF * s ^ (-15 / 2 : ℝ) * a0⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq)
      = ((9 : ℝ) ^ d * CX) * (s ^ (-3 / 2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * CF) *
          (s ^ (-15 / 2 : ℝ) * a0⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) := by
        ring
    _ ≤ ((9 : ℝ) ^ d * (CX + CF + 1)) * (s ^ (-3 / 2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * (CX + CF + 1)) *
          (s ^ (-15 / 2 : ℝ) * a0⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) :=
        add_le_add (mul_le_mul_of_nonneg_right hb1 hP1)
          (mul_le_mul_of_nonneg_right hb2 hP2)
    _ = (9 : ℝ) ^ d * (CX + CF + 1) * s ^ (-3 / 2 : ℝ) * Er * Wq +
        (9 : ℝ) ^ d * (CX + CF + 1) * s ^ (-15 / 2 : ℝ) * a0⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by ring

end

end SubdiffusiveProcess.InteriorComparisonEngine
