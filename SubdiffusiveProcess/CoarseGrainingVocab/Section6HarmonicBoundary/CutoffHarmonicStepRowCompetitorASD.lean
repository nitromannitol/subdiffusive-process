
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowCompetitorASD
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicCoarseAffineAtScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicLeaves

@[expose] public section

/-!
# The step-row competitor and its ASD price, at a finite cutoff

Cutoff companions of
`Section6HarmonicBoundary.exists_stepRowCompetitorLift_atScale` and
`Section6HarmonicBoundary.exists_stepRowCompetitorASD_atScale`: the binders
`n + 2 ≤ L` and `m ≤ L` are deleted and the good event is `𝒢^{(L)}_{n+2,z}`.
The changed leaves are the cutoff tile ellipticity caps and the cutoff coarse
affine datum price; the corrector construction, the mean-defect algebra and the
scale arithmetic are deterministic and are quoted unchanged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The competitor of the boundary ASD row, at a free cover scale.**

On the good event, the coarse affine Dirichlet lift of the projected
boundary datum, corrected by the forced zero-trace corrector, is a solution of
the *same* forced equation whose difference with the datum is an exact `H¹₀`
function, and whose coefficient energy is priced by

* the datum's affine mean, with **no** power of the Besov order,
* the datum's positive Besov seminorm, with `(s/2)^{-3}`,
* the force's positive Besov seminorm, with `(s/2)^{-3} σ⁻¹`,

all carrying the single cover-depth loss `3^{(s/4)(n+2-k)}`.  No pointwise cap
on `aCutoff` occurs. -/
theorem exists_stepRowCompetitorLift_atScale (d : ℕ) [NeZero d] :
    ∃ Cv : ℝ, 0 < Cv ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ),
        s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L n : ℕ), 
      ∀ (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d),
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      let Q := originCube d k
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let depth := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
      ∀ (h0 : H1Function (openCubeSet Q)) (g0 : Vec d → Vec d),
        ForceBesovRegularity Q s h0.grad →
        ForceBesovRegularity Q s g0 →
        ∃ r : H10Function (openCubeSet Q),
          IsForcedEquation Q A (h0 + r.toH1Function) g0 ∧
            localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q)
                (h0 + r.toH1Function) ≤
              Cv * Real.rpow (3 : ℝ) (s / 4 * depth) *
                (sigma * (vecNormSq (cubeAverageVec Q h0.grad) +
                    Real.rpow (s / 2) (-3 : ℝ) *
                      scaleNormalizedPositiveBesovVectorSeminormTwo Q s h0.grad ^ 2) +
                  sigma⁻¹ * (Real.rpow (s / 2) (-3 : ℝ) *
                      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g0 ^ 2)) := by
  obtain ⟨Cdat, hCdat, hlift⟩ :=
    exists_coarseAffineDirichletLift_goodEvent_atScale_energy_le d
  obtain ⟨Ct, hCt, hcaps⟩ := exists_localTileEllipticityCaps_atScale d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set K0 : ℝ := 2 * (d : ℝ) * (192 * (d : ℝ) * Ct ^ 2 + 1) with hK0def
  have hK0 : 0 < K0 := by rw [hK0def]; positivity
  set Kc : ℝ := ((d : ℝ) * stepRowCorrectorConst d) ^ 2 with hKcdef
  have hKc : 0 ≤ Kc := by rw [hKcdef]; positivity
  refine ⟨2 * Cdat + 2 * Kc * K0 + 1, by positivity, ?_⟩
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  set Q : TriadicCube d := originCube d k with hQdef
  set A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample y omega)
    with hAdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set depth : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hdepthdef
  intro h0 g0 hh0reg hg0reg
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  have hdepth0 : (0 : ℝ) ≤ depth := by rw [hdepthdef]; positivity
  set B : ℝ := tileEllipticityConst d Ct s depth with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact tileEllipticityConst_pos d Ct s depth
  have hBle : B ≤ K0 * Real.rpow (3 : ℝ) (s / 4 * depth) := by
    rw [hBdef, hK0def]
    exact tileEllipticityConst_le d hs0 hdepth0
  obtain ⟨_hupper6, hlower6, _hLam1, _h4, _h5, _h6⟩ :=
    hcaps M s hs L n k omega y z hcontain hgood
  -- the coarse affine zero-force lift
  obtain ⟨w, hwh, hwE⟩ := hlift M s hs L n k omega y z hcontain hgood h0 hh0reg
  -- the forced zero-trace corrector
  have hgL2 : MemVectorL2 (cubeSet Q) g0 :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg0reg
  set rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q A) g0 :=
    zeroTraceDirichletCorrectorData_publicCoeffField Q A hgL2 with hrhodef
  have hr0forced : IsForcedEquation Q A
      (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := A) rho).toH1Function
      g0 :=
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution
      (Q := Q) (a := A) rho).weakSolution
  obtain ⟨r, hforced, hEsplit⟩ :=
    exists_forcedCompetitor_of_corrector h0 _ hr0forced w hwh
  refine ⟨r, hforced, ?_⟩
  -- the corrector's energy, priced by the force
  have hg0reg' : ForceBesovRegularity Q (2 * (s / 2)) g0 := by
    simpa only [show 2 * (s / 2) = s by ring] using hg0reg
  have hcorr := localizedCoeffEnergyValue_corrector_le rho
    (t := s / 2) (by linarith only [hs0]) (by linarith only [hs.2, hs0]) hg0reg'
  rw [show 2 * (s / 2) = s by ring] at hcorr
  -- the coarse lower ellipticity cap at the half order
  have hcapHalf : sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ B :=
    Section6HolderInterior.lambdaSq_cap_mono Q A (by linarith only [hs0])
      (by linarith only [hs0]) hsigma.le hlower6
  have hinvCap : (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ B * sigma⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hcapHalf (inv_nonneg.mpr hsigma.le)
    rwa [mul_comm sigma _, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at h
  -- abbreviations
  set R : ℝ := Real.rpow (3 : ℝ) (s / 4 * depth) with hRdef
  have hR : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  set P3 : ℝ := Real.rpow (s / 2) (-3 : ℝ) with hP3def
  have hP3 : 0 ≤ P3 := by
    rw [hP3def]; exact Real.rpow_nonneg (by linarith only [hs0]) _
  set Sg : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q s g0 ^ 2 with hSgdef
  have hSg : 0 ≤ Sg := by rw [hSgdef]; exact sq_nonneg _
  set Dh : ℝ := vecNormSq (cubeAverageVec Q h0.grad) +
    P3 * scaleNormalizedPositiveBesovVectorSeminormTwo Q s h0.grad ^ 2 with hDhdef
  have hDh : 0 ≤ Dh := by
    rw [hDhdef]
    exact add_nonneg (vecNormSq_nonneg _) (mul_nonneg hP3 (sq_nonneg _))
  have hcorr2 : localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q)
      (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := A) rho).toH1Function ≤
      Kc * K0 * (R * (sigma⁻¹ * (P3 * Sg))) := by
    refine hcorr.trans ?_
    have hstep : (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ K0 * R * sigma⁻¹ :=
      hinvCap.trans (mul_le_mul_of_nonneg_right hBle (inv_nonneg.mpr hsigma.le))
    have hmul : Kc * P3 * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ * Sg ≤
        Kc * P3 * (K0 * R * sigma⁻¹) * Sg := by
      refine mul_le_mul_of_nonneg_right ?_ hSg
      exact mul_le_mul_of_nonneg_left hstep (mul_nonneg hKc hP3)
    calc Kc * P3 * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ * Sg
        ≤ Kc * P3 * (K0 * R * sigma⁻¹) * Sg := hmul
      _ = Kc * K0 * (R * (sigma⁻¹ * (P3 * Sg))) := by ring
  have hX : 0 ≤ R * (sigma * Dh) := by positivity
  have hY : 0 ≤ R * (sigma⁻¹ * (P3 * Sg)) := by positivity
  have hfin := hEsplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left hcorr2 (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hwE (by norm_num : (0 : ℝ) ≤ 2)))
  refine hfin.trans ?_
  have hKcK0 : 0 ≤ Kc * K0 := mul_nonneg hKc hK0.le
  have hC1 : 2 * Cdat ≤ 2 * Cdat + 2 * Kc * K0 + 1 := by
    nlinarith only [hKcK0]
  have hC2 : 2 * (Kc * K0) ≤ 2 * Cdat + 2 * Kc * K0 + 1 := by
    nlinarith only [hCdat]
  calc 2 * (Kc * K0 * (R * (sigma⁻¹ * (P3 * Sg)))) +
        2 * (Cdat * R * sigma * Dh)
      = 2 * Cdat * (R * (sigma * Dh)) +
          2 * (Kc * K0) * (R * (sigma⁻¹ * (P3 * Sg))) := by ring
    _ ≤ (2 * Cdat + 2 * Kc * K0 + 1) * (R * (sigma * Dh)) +
          (2 * Cdat + 2 * Kc * K0 + 1) * (R * (sigma⁻¹ * (P3 * Sg))) :=
        add_le_add (mul_le_mul_of_nonneg_right hC1 hX)
          (mul_le_mul_of_nonneg_right hC2 hY)
    _ = (2 * Cdat + 2 * Kc * K0 + 1) * R * (sigma * Dh + sigma⁻¹ * (P3 * Sg)) := by
        ring

omit [NeZero d] in

/-- **The competitor-centred boundary ASD row at a free cover scale.**

Report §20.2: the manuscript's ASD row is re-centred at the *competitor* mean
`(v)_Q` rather than at the datum mean `(h)_Q`.  The datum then enters only
through the competitor's own coefficient energy `Hv`, whose mean half is free of
any power of the Besov order; the price of the change of centre is the residual
mean `((u-v)_Q)^2`, which the boundary tile family pays.

No pointwise cap on `aCutoff` occurs: every coefficient is a coarse good-event
quantity. -/
theorem exists_stepRowCompetitorASD_atScale (d : ℕ) [NeZero d] :
    ∃ K Cv Cosc : ℝ, 0 < K ∧ 0 < Cv ∧ 0 < Cosc ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ k : ℤ, k ≤ (n : ℤ) - 2 →
      ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ cube d (m : ℤ) →
        translatedCube d k (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) ⊆
          truncatedCube d (m : ℤ) (n : ℤ) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample c omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let D := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)
        ∃ (g0 : Vec d → Vec d) (u0 h0 : H1Function (openCubeSet Q))
          (r : H10Function (openCubeSet Q)) (Hv : ℝ),
          (∀ y, g0 y = g (y + c)) ∧
          (∀ y, u0.toFun y = u.toFun (y + c)) ∧
          (∀ y, u0.grad y = u.grad (y + c)) ∧
          (∀ y, h0.toFun y = h.toFun (y + c)) ∧
          (∀ y, h0.grad y = h.grad (y + c)) ∧
          0 ≤ Hv ∧
          Hv = localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q)
              (h0 + r.toH1Function) ∧
          Hv ≤ Cv * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) *
              (sigma * (vecNormSq (cubeAverageVec Q h0.grad) +
                  Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      h0.grad ^ 2) +
                sigma⁻¹ * (Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      (fun y ↦ -g0 y) ^ 2)) ∧
          normalizedL2SqOnSet (openCubeSet Q)
              (fun y ↦ (h0 + r.toH1Function).toFun y -
                volumeAverage (openCubeSet Q) (h0 + r.toH1Function).toFun) ≤
            Cosc * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) * sigma⁻¹ *
              cubeScaleFactor Q ^ 2 * Hv ∧
          normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
              (fun p ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
                vecNormSq (u.grad p)) ≤
            K * (Real.rpow (3 : ℝ) (7 / 4 * sOrder.1 * D) *
                  (sigma * Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) *
                    (normalizedL2SqOnSet (openCubeSet Q)
                        (fun y ↦ u0.toFun y - c0) +
                      volumeAverage (openCubeSet Q)
                        (fun y ↦ u0.toFun y - (h0 + r.toH1Function).toFun y) ^ 2)) +
                Real.rpow (3 : ℝ) (2 * sOrder.1 * D) * Hv) := by
  obtain ⟨C1, hC1, hslot⟩ :=
    exists_boundaryCaccioppoliEnergy_of_competitorEnergy_centered d
  obtain ⟨Ct, hCt, hcaps⟩ := exists_localTileEllipticityCaps_atScale d
  obtain ⟨Cvl, hCvl, hlift⟩ := exists_stepRowCompetitorLift_atScale d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set Pref : ℝ := (4 * max 1 C1) ^ (8 : ℕ) * 8 with hPrefdef
  have hPref : 0 < Pref := by rw [hPrefdef]; positivity
  set K0 : ℝ := 2 * (d : ℝ) * (192 * (d : ℝ) * Ct ^ 2 + 1) with hK0def
  have hK0 : 0 < K0 := by rw [hK0def]; positivity
  set CP : ℝ := coarseL2PoincareConst d with hCPdef
  have hCP : 0 ≤ CP := by rw [hCPdef]; exact coarseL2PoincareConst_nonneg d
  refine ⟨(81 : ℝ) ^ d * (4 * Pref * K0 ^ (7 : ℕ) +
      4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) + 2 * (18 : ℝ) ^ d), Cvl,
    CP ^ 2 * K0 + 1, by positivity, hCvl, by positivity, ?_⟩
  intro M sOrder hs L m n hnm k hk z x q omega hx hq hparent hgood
    u h g c0 hdir hg hh
  dsimp only
  set c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k with hcdef
  set Q : TriadicCube d := originCube d k with hQdef
  set A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
    with hAdef
  set sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set D : ℝ := ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ) with hDdef
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hkm : k ≤ (m : ℤ) := by omega
  have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  -- the translated datum
  obtain ⟨g0, u0, h0, hg0, hu0, hgLocal, hu0grad, hueq, hh0, hh0grad,
      hhLocal, hgReg, htrace⟩ :=
    exists_projectedBoundaryDirectDatum M L omega m k q sOrder u h g
      hdir hg hh hkm
  have hhReg : ForceBesovRegularity Q sOrder.1 h0.grad := by
    have heq : h0.grad = fun y ↦ h.grad (y + c) := funext hh0grad
    rw [heq]
    exact forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le
      (by simpa [hQdef, hcdef] using hhLocal) le_rfl
  -- geometry of the projected parent
  have hcmem : c ∈ translatedCube d k c := by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k
  have hcU : c ∈ truncatedCube d (m : ℤ) (n : ℤ) x := hparent hcmem
  have hcontain := translateSet_cubeSet_originCube_subset_anchor_of_mem_nextWindow
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k) (x := x) (y := c) (z := z)
    hk hx hcU
  -- the competitor
  obtain ⟨r, hforced, hEbound⟩ :=
    hlift M sOrder.1 hs L n k omega c z hcontain hgood h0 (fun y ↦ -g0 y)
      hhReg hgReg
  set v : H1Function (openCubeSet Q) := h0 + r.toH1Function with hvdef
  set Hv : ℝ := localizedCoeffEnergyValue (openCubeSet Q) (A.coeffOn Q) v
    with hHvdef
  have hHv0 : 0 ≤ Hv := by
    rw [hHvdef,
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Q := Q) (a := A) Set.Subset.rfl v, volumeAverage_openCubeSet_eq_cubeAverage]
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro y hy
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q A) v.grad y hy
  -- the coarse ellipticity package
  obtain ⟨_hupper6, hlower6, hLam1, _h4, _h5, _h6⟩ :=
    hcaps M sOrder.1 hs L n k omega c z hcontain hgood
  set B : ℝ := tileEllipticityConst d Ct sOrder.1 D with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact tileEllipticityConst_pos d Ct sOrder.1 D
  have hBle : B ≤ K0 * (3 : ℝ) ^ (sOrder.1 / 4 * D) := by
    rw [hBdef, hK0def]
    exact tileEllipticityConst_le d hs0 hD0
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma hLam1 hlower6
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC1 hs0 hs.2 hhalf.2.2
  rw [← hPrefdef] at hpref
  -- the competitor's own parent oscillation
  have hKs : 0 ≤ B * sigma⁻¹ := mul_nonneg hBpos.le (inv_nonneg.mpr hsigma.le)
  have hosc := normalizedL2SqOnSet_centred_le_of_lambdaSCap M L
    (translatePotentialSample c omega) Q v (t := sOrder.1 / 2)
    (by linarith only [hs0]) (by linarith only [hs.2, hs0]) hhalf.1 hKs
    (le_of_eq hHvdef.symm)
  have hoscBound : normalizedL2SqOnSet (openCubeSet Q)
      (fun y ↦ v.toFun y - volumeAverage (openCubeSet Q) v.toFun) ≤
      (CP ^ 2 * K0 + 1) * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) * sigma⁻¹ *
        cubeScaleFactor Q ^ 2 * Hv := by
    refine hosc.trans ?_
    have hnn : 0 ≤ sigma⁻¹ * cubeScaleFactor Q ^ 2 * Hv :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr hsigma.le) (sq_nonneg _)) hHv0
    have hX : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) :=
      Real.rpow_nonneg (by norm_num) _
    have hb : CP ^ 2 * B ≤
        (CP ^ 2 * K0 + 1) * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) := by
      have h1 : CP ^ 2 * B ≤ CP ^ 2 * (K0 * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D)) :=
        mul_le_mul_of_nonneg_left hBle (by positivity)
      nlinarith only [h1, hX]
    calc CP ^ 2 * (B * sigma⁻¹) * cubeScaleFactor Q ^ 2 * Hv
        = (CP ^ 2 * B) * (sigma⁻¹ * cubeScaleFactor Q ^ 2 * Hv) := by ring
      _ ≤ ((CP ^ 2 * K0 + 1) * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D)) *
            (sigma⁻¹ * cubeScaleFactor Q ^ 2 * Hv) :=
          mul_le_mul_of_nonneg_right hb hnn
      _ = (CP ^ 2 * K0 + 1) * Real.rpow (3 : ℝ) (sOrder.1 / 4 * D) * sigma⁻¹ *
            cubeScaleFactor Q ^ 2 * Hv := by ring
  refine ⟨g0, u0, h0, r, Hv, hg0, hu0, hu0grad, hh0, hh0grad, hHv0, rfl,
    hEbound, hoscBound, ?_⟩
  rw [← hvdef]
  -- the localized zero trace of `u0 - v`
  have hrtrace : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale (q - c) (k - 1)) r.toH1Function.toFun :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_of_memH10 ⟨r, rfl⟩
  have htraceUV : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale (q - c) (k - 1)) (fun y ↦ u0.toFun y - v.toFun y) := by
    refine Section6SchauderDatum.localizedZeroTraceFunctionOn_congr ?_
      (Homogenization.localizedZeroTraceFunctionOn_sub htrace hrtrace)
    intro y
    show u0.toFun y - h0.toFun y - r.toH1Function.toFun y = _
    rw [hvdef]
    show _ = u0.toFun y - (h0.toFun y + r.toH1Function.toFun y)
    ring
  -- the localization centre
  have hqtrunc : q ∈ truncatedCube d (m : ℤ) (k - 1) q :=
    Section6ExcessDecay.mem_truncatedCube_self (k - 1) hq
  have hqtranslated : q ∈ translatedCube d k c :=
    Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre q
      hkm (by omega) hqtrunc
  have hxmem : q - c ∈ openCubeSet Q :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hqtranslated
  -- the competitor-slot ASD row, centred at the competitor mean
  set cv : ℝ := volumeAverage (openCubeSet Q) v.toFun with hcvdef
  have hcore := hslot (Q := Q) (a := A) (s := 1 / 2) (t := sOrder.1 / 2)
    (x := q - c) (g := fun y ↦ -g0 y) u0 v cv Hv hueq hforced htraceUV
    (by norm_num) (by norm_num) (by linarith only [hs0])
    (by linarith only [hs.2, hs0]) (by linarith only [hs.2, hs0]) hxmem le_rfl
  -- the cell readout
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0grad
  -- abbreviations
  set P1 : ℝ := caccioppoliWithRHSPrefactor C1 Q A (1 / 2) (sOrder.1 / 2) with hP1def
  set lam : ℝ := Ch02.lambdaS Q (sOrder.1 / 2) A with hlamdef
  set Z : ℝ := Real.rpow (3 : ℝ) (-2 * ((k : ℤ) : ℝ)) with hZdef
  set SF : ℝ := cubeScaleFactor Q with hSFdef
  set R2 : ℝ := Real.rpow (3 : ℝ) (2 * sOrder.1 * D) with hR2def
  set N : ℝ := normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u0.toFun y - cv)
    with hNdef
  set Oscv : ℝ := normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ v.toFun y - cv)
    with hOscvdef
  have hzr : ((3 : ℝ) ^ (-(2 * Q.scale))) = Z := by
    have hsc : (-(2 * Q.scale) : ℤ) = -(2 * k) := rfl
    rw [hsc, hZdef, ← Real.rpow_intCast (3 : ℝ) (-(2 * k))]
    congr 1
    push_cast
    ring
  rw [hzr] at hcore
  -- nonnegativity
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact Real.rpow_nonneg (by norm_num) _
  have hNnn : 0 ≤ N := by
    rw [hNdef]; exact normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q)
  have hOscnn : 0 ≤ Oscv := by
    rw [hOscvdef]; exact normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q)
  have hlamnn : 0 ≤ lam := by
    rw [hlamdef, Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
  have hP1nn : 0 ≤ P1 := by
    rw [hP1def]
    exact caccioppoliWithRHSPrefactor_nonneg hC1.le (by norm_num)
      (by linarith only [hs0]) (by linarith only [hs.2, hs0])
  have hR2pos : 0 < R2 := by
    rw [hR2def]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hR2one : 1 ≤ R2 := by
    rw [hR2def]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  -- the prefactor times the coarse ellipticity
  have hprodA : P1 * lam ≤ Pref * B ^ (7 : ℕ) * sigma := by
    have hh := mul_le_mul hpref hhalf.2.1 hlamnn
      (by positivity : (0 : ℝ) ≤ Pref * (B ^ (2 : ℕ)) ^ (3 : ℕ))
    calc P1 * lam ≤ Pref * (B ^ (2 : ℕ)) ^ (3 : ℕ) * (B * sigma) := hh
      _ = Pref * B ^ (7 : ℕ) * sigma := by ring
  have hleg1 : P1 * (lam * Z * N) ≤ Pref * B ^ (7 : ℕ) * (sigma * Z * N) := by
    calc P1 * (lam * Z * N) = (P1 * lam) * (Z * N) := by ring
      _ ≤ (Pref * B ^ (7 : ℕ) * sigma) * (Z * N) :=
          mul_le_mul_of_nonneg_right hprodA (mul_nonneg hZ0 hNnn)
      _ = Pref * B ^ (7 : ℕ) * (sigma * Z * N) := by ring
  have hZSF : Z * SF ^ 2 = 1 := by
    rw [hZdef, hSFdef, hQdef]
    exact rpow_three_neg_two_mul_cubeScaleFactor_sq k
  have hleg2 : P1 * (lam * Z * Oscv) ≤ Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv := by
    have hstep : P1 * (lam * Z * Oscv) ≤
        (Pref * B ^ (7 : ℕ) * sigma) *
          (Z * (CP ^ 2 * (B * sigma⁻¹) * SF ^ 2 * Hv)) := by
      calc P1 * (lam * Z * Oscv) = (P1 * lam) * (Z * Oscv) := by ring
        _ ≤ (Pref * B ^ (7 : ℕ) * sigma) *
              (Z * (CP ^ 2 * (B * sigma⁻¹) * SF ^ 2 * Hv)) := by
            refine mul_le_mul hprodA (mul_le_mul_of_nonneg_left hosc hZ0)
              (mul_nonneg hZ0 hOscnn) ?_
            have : (0 : ℝ) ≤ Pref * B ^ (7 : ℕ) :=
              mul_nonneg hPref.le (by positivity)
            exact mul_nonneg this hsigma.le
    refine hstep.trans (le_of_eq ?_)
    calc (Pref * B ^ (7 : ℕ) * sigma) *
          (Z * (CP ^ 2 * (B * sigma⁻¹) * SF ^ 2 * Hv))
        = (Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv) * ((sigma * sigma⁻¹) * (Z * SF ^ 2)) := by
          ring
      _ = Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv := by
          rw [mul_inv_cancel₀ hsigma.ne', hZSF]; ring
  -- the powers of the tile ellipticity constant
  set R7 : ℝ := Real.rpow (3 : ℝ) (7 / 4 * sOrder.1 * D) with hR7def
  have hR7pos : 0 < R7 := by
    rw [hR7def]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hB7 : B ^ (7 : ℕ) ≤ K0 ^ (7 : ℕ) * R7 := by
    have hh := pow_le_rpow_three_exact hBpos.le hBle 7
    have heq : ((7 : ℕ) : ℝ) * (sOrder.1 / 4 * D) = 7 / 4 * sOrder.1 * D := by
      push_cast; ring
    rw [heq] at hh
    rw [hR7def]
    exact hh
  have hB8 : B ^ (8 : ℕ) ≤ K0 ^ (8 : ℕ) * R2 := by
    rw [hR2def]; exact pow_eight_le_rpow_three hBpos.le hBle
  have hSZN : 0 ≤ sigma * Z * N := mul_nonneg (mul_nonneg hsigma.le hZ0) hNnn
  -- the residual-mean recentring
  have hVpos : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hVtop : volume (openCubeSet Q) ≠ ⊤ := (volume_openCubeSet_lt_top Q).ne
  have hu0int : IntegrableOn u0.toFun (openCubeSet Q) :=
    u0.memL2.integrable (by norm_num)
  have hu0int2 : IntegrableOn (fun y ↦ u0.toFun y ^ 2) (openCubeSet Q) :=
    u0.memL2.integrable_sq
  set N0 : ℝ := normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u0.toFun y - c0)
    with hN0def
  set Res : ℝ := volumeAverage (openCubeSet Q) (fun y ↦ u0.toFun y - v.toFun y)
    with hResdef
  have hNsplit : N ≤ N0 + Res ^ 2 := by
    have hbase := normalizedL2SqOnSet_sub_const_le_add_sq_meanDefect
      (W := openCubeSet Q) (f := u0.toFun) cv c0 hVpos hVtop hu0int hu0int2
    have hmean : averageOn (openCubeSet Q) u0.toFun - cv = Res := by
      rw [hResdef, hcvdef]
      exact (volumeAverage_sub_eq_solutionAverage_sub_datumAverage Q u0 v).symm
    rw [hNdef, hN0def, ← hmean]
    exact hbase
  set S : ℝ := sigma * Z * (N0 + Res ^ 2) with hSdef
  have hN0nn : 0 ≤ N0 := by
    rw [hN0def]
    exact normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q)
  have hSnn : 0 ≤ S :=
    mul_nonneg (mul_nonneg hsigma.le hZ0) (add_nonneg hN0nn (sq_nonneg _))
  have hmono : sigma * Z * N ≤ S := by
    rw [hSdef]
    exact mul_le_mul_of_nonneg_left hNsplit (mul_nonneg hsigma.le hZ0)
  set Ktot : ℝ := 4 * Pref * K0 ^ (7 : ℕ) + 4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) +
    2 * (18 : ℝ) ^ d with hKtotdef
  have hRS : 0 ≤ R7 * S := mul_nonneg hR7pos.le hSnn
  have hRH : 0 ≤ R2 * Hv := mul_nonneg hR2pos.le hHv0
  have hc1 : (0 : ℝ) ≤ 4 * Pref * K0 ^ (7 : ℕ) := by positivity
  have hc2 : (0 : ℝ) ≤ 4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) := by positivity
  have hc3 : (0 : ℝ) ≤ 2 * (18 : ℝ) ^ d := by positivity
  have hstep1 : 4 * (P1 * (lam * Z * N)) + 4 * (P1 * (lam * Z * Oscv)) +
      2 * ((18 : ℝ) ^ d * Hv) ≤
      4 * (Pref * B ^ (7 : ℕ) * (sigma * Z * N)) +
        4 * (Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv) + 2 * ((18 : ℝ) ^ d * Hv) := by
    linarith only [hleg1, hleg2]
  have hstep2 : 4 * (Pref * B ^ (7 : ℕ) * (sigma * Z * N)) +
      4 * (Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv) + 2 * ((18 : ℝ) ^ d * Hv) ≤
      4 * Pref * K0 ^ (7 : ℕ) * (R7 * (sigma * Z * N)) +
        4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R2 * Hv) +
        2 * (18 : ℝ) ^ d * (R2 * Hv) := by
    have e1 : Pref * B ^ (7 : ℕ) * (sigma * Z * N) ≤
        Pref * (K0 ^ (7 : ℕ) * R7) * (sigma * Z * N) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB7 hPref.le) hSZN
    have e2 : Pref * CP ^ 2 * B ^ (8 : ℕ) * Hv ≤
        Pref * CP ^ 2 * (K0 ^ (8 : ℕ) * R2) * Hv :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB8 (by positivity)) hHv0
    have e3 : (18 : ℝ) ^ d * Hv ≤ (18 : ℝ) ^ d * (R2 * Hv) := by
      have : Hv ≤ R2 * Hv := by nlinarith only [hR2one, hHv0]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith only [e1, e2, e3]
  have hstep3 : 4 * Pref * K0 ^ (7 : ℕ) * (R7 * (sigma * Z * N)) +
      4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R2 * Hv) +
      2 * (18 : ℝ) ^ d * (R2 * Hv) ≤
      4 * Pref * K0 ^ (7 : ℕ) * (R7 * S) +
        4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R2 * Hv) +
        2 * (18 : ℝ) ^ d * (R2 * Hv) := by
    have e : R7 * (sigma * Z * N) ≤ R7 * S :=
      mul_le_mul_of_nonneg_left hmono hR7pos.le
    nlinarith only [e, hc1]
  have hstep4 : 4 * Pref * K0 ^ (7 : ℕ) * (R7 * S) +
      4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R2 * Hv) +
      2 * (18 : ℝ) ^ d * (R2 * Hv) ≤ Ktot * (R7 * S + R2 * Hv) := by
    have p1 : 0 ≤ 4 * Pref * K0 ^ (7 : ℕ) * (R2 * Hv) := mul_nonneg hc1 hRH
    have p2 : 0 ≤ 4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R7 * S) := mul_nonneg hc2 hRS
    have p3 : 0 ≤ 2 * (18 : ℝ) ^ d * (R7 * S) := mul_nonneg hc3 hRS
    have hexp : Ktot * (R7 * S + R2 * Hv) =
        (4 * Pref * K0 ^ (7 : ℕ) * (R7 * S) +
            4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R2 * Hv) +
            2 * (18 : ℝ) ^ d * (R2 * Hv)) +
          (4 * Pref * K0 ^ (7 : ℕ) * (R2 * Hv) +
            4 * Pref * CP ^ 2 * K0 ^ (8 : ℕ) * (R7 * S) +
            2 * (18 : ℝ) ^ d * (R7 * S)) := by
      rw [hKtotdef]; ring
    rw [hexp]
    linarith only [p1, p2, p3]
  have hcore2 : localizedCoeffEnergyValue (caccioppoliCoreSet Q (q - c))
      (A.coeffOn Q) u0 ≤ Ktot * (R7 * S + R2 * Hv) :=
    hcore.trans (hstep1.trans (hstep2.trans (hstep3.trans hstep4)))
  refine hread.trans ?_
  have h81 : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  refine (mul_le_mul_of_nonneg_left hcore2 h81).trans (le_of_eq ?_)
  rw [hKtotdef, hSdef, hR7def, hR2def]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
