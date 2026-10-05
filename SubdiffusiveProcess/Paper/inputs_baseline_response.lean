module

public import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseGamma
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_inputs_baseline_response_J_eq_ofReal_realSup
    {d : ℕ} [NeZero d] (M : GMCModel d) (n : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    aux_psf_Jval M n omega x =
      ENNReal.ofReal (sSup {t : ℝ | ∃ e : Vec d,
        Homogenization.vecNormSq e = 1 ∧
          t = section6Response M n n omega x e}) := by
  let S : Set ℝ := {t : ℝ | ∃ e : Vec d,
    Homogenization.vecNormSq e = 1 ∧ t = section6Response M n n omega x e}
  have hb : BddAbove S := by
    simpa only [S] using
      bddAbove_section6Response_unitSphere M n n omega x
  have hne : S.Nonempty := by
    let e : Vec d := (Classical.arbitrary (ScalarProbeUnitSphere d)).1
    have he : Homogenization.vecNormSq e = 1 :=
      (Classical.arbitrary (ScalarProbeUnitSphere d)).2
    exact ⟨section6Response M n n omega x e, e, he, rfl⟩
  have hsup_nonneg : 0 ≤ sSup S := by
    let e : Vec d := (Classical.arbitrary (ScalarProbeUnitSphere d)).1
    have he : Homogenization.vecNormSq e = 1 :=
      (Classical.arbitrary (ScalarProbeUnitSphere d)).2
    have hresp : 0 ≤ section6Response M n n omega x e := by
      unfold section6Response paperScalarProbe J
      exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
    exact hresp.trans (le_csSup hb ⟨e, he, rfl⟩)
  unfold aux_psf_Jval
  apply le_antisymm
  · refine sSup_le ?_
    rintro v ⟨e, he, rfl⟩
    exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨e, he, rfl⟩)
  · have htop :
      sSup {v : ENNReal | ∃ e : Vec d,
        Homogenization.vecNormSq e = 1 ∧
          v = ENNReal.ofReal (section6Response M n n omega x e)} ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      refine sSup_le ?_
      rintro v ⟨e, he, rfl⟩
      exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨e, he, rfl⟩)
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    apply csSup_le hne
    rintro t ⟨e, he, rfl⟩
    have hv : ENNReal.ofReal (section6Response M n n omega x e) ≤
        sSup {v : ENNReal | ∃ e : Vec d,
          Homogenization.vecNormSq e = 1 ∧
            v = ENNReal.ofReal (section6Response M n n omega x e)} :=
      le_sSup ⟨e, he, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hv

private theorem aux_inputs_baseline_response_term_le_window
    {d : ℕ} [NeZero d] (M : GMCModel d) {s : ℝ} (hs : 0 < s) (k : ℕ)
    (z : Vec d) (omega : PotentialSample d) :
    (let term : PotentialSample d → ENNReal := fun omega =>
      sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧
        ∃ x : Vec d, OnTriadicGrid l (x - z) ∧
          x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d,
              Homogenization.vecNormSq e = 1 ∧
                u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
              (1 / 2 : ℝ)};
      (term omega).toReal ≤
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.translatedCutoffParameterizedAccumulatedResponseSup
          M k s k z omega) := by
  dsimp only
  let Jset := fun (l : ℕ) (x : Vec d) =>
    {t : ℝ | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      t = section6Response M l l omega x e}
  let Aset : Set ℝ := {r | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ x : Vec d, OnTriadicGrid l (x - z) ∧
      x - z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup (Jset l x)) 1)}
  have hA_bdd : BddAbove Aset := by
    refine ⟨1, ?_⟩
    rintro r ⟨j, l, hjk, hlj, x, hxgrid, hxann, rfl⟩
    have hexp : -(s / 2) * ((k : ℝ) - (l : ℝ)) ≤ 0 := by
      have hlk : (l : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by omega : l ≤ k)
      have hprod : 0 ≤ (s / 2) * ((k : ℝ) - (l : ℝ)) :=
        mul_nonneg (by linarith) (sub_nonneg.mpr hlk)
      linarith
    have hw : (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
    have hroot : Real.sqrt (min (sSup (Jset l x)) 1) ≤ 1 := by
      calc
        Real.sqrt (min (sSup (Jset l x)) 1) ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt (min_le_right _ _)
        _ = 1 := Real.sqrt_one
    calc
      _ ≤ 1 * 1 := mul_le_mul hw hroot (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hA_nonneg : 0 ≤ sSup Aset := by
    by_cases hne : Aset.Nonempty
    · rcases hne with ⟨r, ⟨j, l, hjk, hlj, x, hgrid, hann, rfl⟩⟩
      have hmem :
          (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup (Jset l x)) 1) ∈ Aset := by
        exact ⟨j, l, hjk, hlj, x, hgrid, hann, rfl⟩
      exact (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.sqrt_nonneg _)).trans (le_csSup hA_bdd hmem)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
  let Eset : Set ENNReal := {v : ENNReal | ∃ j l : ℕ,
      j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) *
          ((k : ℝ) - (l : ℝ)))) *
          (min (sSup {u : ENNReal | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
            (1 / 2 : ℝ)}
  have hE_le : sSup Eset ≤ ENNReal.ofReal (sSup Aset) := by
    refine sSup_le ?_
    rintro v ⟨j, l, hjk, hlk, hlj, x, hxgrid, hxann, rfl⟩
    have hJ := aux_inputs_baseline_response_J_eq_ofReal_realSup M l omega x
    have hR0 : 0 ≤ sSup (Jset l x) := by
      have hb : BddAbove (Jset l x) := by
        simpa only [Jset] using
          bddAbove_section6Response_unitSphere M l l omega x
      let e : Vec d := (Classical.arbitrary (ScalarProbeUnitSphere d)).1
      have he : Homogenization.vecNormSq e = 1 :=
        (Classical.arbitrary (ScalarProbeUnitSphere d)).2
      have hresp : 0 ≤ section6Response M l l omega x e := by
        unfold section6Response paperScalarProbe J
        exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
      exact hresp.trans (le_csSup hb ⟨e, he, rfl⟩)
    have hmin : 0 ≤ min (sSup (Jset l x)) 1 := le_min hR0 zero_le_one
    have hweight0 : 0 ≤ (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hval :
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (sSup {u : ENNReal | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
            (1 / 2 : ℝ) =
          ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) *
            ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup (Jset l x)) 1)) := by
      change ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) *
          ((k : ℝ) - (l : ℝ)))) *
          (min (aux_psf_Jval M l omega x) 1) ^ (1 / 2 : ℝ) = _
      rw [hJ]
      have hminENN :
          min (ENNReal.ofReal (sSup (Jset l x))) 1 =
            ENNReal.ofReal (min (sSup (Jset l x)) 1) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_min]
      rw [hminENN]
      rw [ENNReal.ofReal_rpow_of_nonneg hmin (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      rw [Real.sqrt_eq_rpow]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    rw [hval]
    have hmem : (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup (Jset l x)) 1) ∈ Aset := by
      exact ⟨j, l, hjk, hlj, x, hxgrid, hxann, rfl⟩
    have hreal : _ ≤ sSup Aset := le_csSup hA_bdd hmem
    have hreal0 : 0 ≤ sSup Aset := hA_nonneg
    exact ENNReal.ofReal_le_ofReal hreal
  have hterm_le :
      (sSup Eset).toReal ≤ sSup Aset := by
    have htop : sSup Eset ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) hE_le
    have hrealTop : ENNReal.ofReal (sSup Aset) ≠ ∞ := ENNReal.ofReal_ne_top
    have h := (ENNReal.toReal_le_toReal htop hrealTop).2 hE_le
    simpa [ENNReal.toReal_ofReal hA_nonneg] using h
  let Wset : Set ℝ := {r | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ x : Vec d, OnTriadicGrid l (x - z) ∧
      x - z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          Homogenization.vecNormSq e = 1 ∧
            t = section6Response M l (min l k) omega x e}) 1)}
  have hAeq : Aset = Wset := by
    ext r
    constructor
    · rintro ⟨j, l, hjk, hlj, x, hxgrid, hxann, rfl⟩
      have hlk : l ≤ k := by omega
      refine ⟨j, l, hjk, hlj, x, hxgrid, hxann, ?_⟩
      simp [Jset, Nat.min_eq_left hlk]
    · rintro ⟨j, l, hjk, hlj, x, hxgrid, hxann, rfl⟩
      have hlk : l ≤ k := by omega
      refine ⟨j, l, hjk, hlj, x, hxgrid, hxann, ?_⟩
      simp [Jset, Nat.min_eq_left hlk]
  change (sSup Eset).toReal ≤ sSup Wset
  rw [← hAeq]
  exact hterm_le

private theorem aux_inputs_baseline_response_weight_sum
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) ≤ 24 / s := by
  have hsHalf : 0 < s / 2 := by positivity
  have hsHalf1 : s / 2 ≤ 1 := by linarith
  have hshift :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.sum_cutoffParameterizedResponseWeight_le
      hsHalf hsHalf1 (k + 2)
  have hshift' :
      ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) ≤ 4 / (s / 2) := by
    rw [show k + 2 - 1 = k + 1 by omega] at hshift
    calc
      ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) =
        ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 2 / 2) * ((k + 2 : ℕ) - j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            ring
      _ ≤ 4 / (s / 2) := hshift
  have hsum :
      (∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ)))) ≤
        3 * (∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j ≤ k := by
      have : j < k + 1 := Finset.mem_range.mp hj
      omega
    have hshift0 :
        0 ≤ (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hfactor : (3 : ℝ) ^ (s / 2) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (x := (3 : ℝ)) (y := s / 2) (z := 1) (by norm_num) (by linarith)
      simpa using h
    have hexp : -(s / 4) * ((k : ℝ) - (j : ℝ)) =
        -(s / 4) * ((k + 2 : ℕ) - j : ℝ) + s / 2 := by
      have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      push_cast
      ring
    calc
      (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) =
          (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) *
            (3 : ℝ) ^ (s / 2) := by
        rw [hexp, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ 3 * (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) := by
        calc
          _ ≤ (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ)) * 3 :=
            mul_le_mul_of_nonneg_left hfactor hshift0
          _ = _ := by ring
  calc
    _ ≤ 3 * (∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k + 2 : ℕ) - j : ℝ))) := hsum
    _ ≤ 3 * (4 / (s / 2)) := by
      gcongr
    _ = 24 / s := by field_simp [hs.ne']; ring

/-- The response term of the literal four-term accumulated-error score. -/
theorem inputs_baseline_response (d : ℕ) (_hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          let term : PotentialSample d → ENNReal := fun omega =>
            sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)}
          (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
          MemLp (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  rcases SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_budget
      (d := d) with ⟨K, Cg, hK, hCg, hrows⟩
  let delta0 : ℝ := min 1 (s / (2 * K))
  let tri : ℝ := Homogenization.IndependentSums.gammaTriangleConst 2
  let indep : ℝ := Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2
  let MeanCoeff : ℝ := 2 * (8 / s) *
    Homogenization.IndependentSums.gammaMomentConst 2
  let FluctCoeff : ℝ := 2 * (8 / s) * tri *
    (tri * (8 / s) + tri * (SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.responseScoreRange d : ℝ) *
      (indep * (1 + Homogenization.IndependentSums.gammaMomentConst 2)))
  let D : ℝ := (MeanCoeff + FluctCoeff) * Real.exp 1 *
    Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaSqConst d Cg s)
  let C : ℝ := Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt q * D
  rcases hs with ⟨hsPos, hsOne⟩
  have htri : 0 < tri := by
    dsimp [tri]
    exact Homogenization.IndependentSums.gammaTriangleConst_pos
  have hindep : 0 < indep := by
    dsimp [indep]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.gammaSigmaIndependentSumConst_two_pos
  have hrange : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.responseScoreRange d : ℝ) := by
    exact_mod_cast SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.responseScoreRange_pos d
  have hgm : 0 < Homogenization.IndependentSums.gammaMomentConst 2 :=
    Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num)
  have hMeanCoeff : 0 < MeanCoeff := by
    dsimp [MeanCoeff]
    exact mul_pos (mul_pos (by norm_num) (div_pos (by norm_num) hsPos)) hgm
  have hFluctCoeff : 0 < FluctCoeff := by
    dsimp [FluctCoeff]
    apply mul_pos
    · exact mul_pos (mul_pos (by norm_num) (div_pos (by norm_num) hsPos)) htri
    · apply add_pos
      · exact mul_pos htri (div_pos (by norm_num) hsPos)
      · exact mul_pos (mul_pos htri hrange)
          (mul_pos hindep (add_pos zero_lt_one hgm))
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min zero_lt_one (div_pos hsPos (by positivity))
  have hCsq : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaSqConst d Cg s :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaSqConst_pos
      d hCg hsPos
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (add_pos hMeanCoeff hFluctCoeff) (Real.exp_pos 1))
      (Real.sqrt_pos.mpr hCsq)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hgm
      (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hq))) hD
  refine ⟨C, delta0, hC, hdelta0, ?_⟩
  intro M hMsmall k z
  let term : PotentialSample d → ENNReal := fun omega =>
    sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
        (min (sSup {u : ENNReal | ∃ e : Vec d,
          Homogenization.vecNormSq e = 1 ∧ u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
          (1 / 2 : ℝ)}
  let Y : PotentialSample d → ℝ := fun omega => (term omega).toReal
  have hdelta_le : M.delta ≤ delta0 := le_trans hMsmall (min_le_right _ _)
  have hδpos := M.shellPrefix.delta_pos
  have hδhalf := M.shellPrefix.delta_le_half
  have hδone : M.delta ≤ 1 := le_trans hδhalf (by norm_num)
  have hδlog : M.delta * |Real.log M.delta| ≤ 1 := by
    have hlog := Real.abs_log_mul_self_lt M.delta hδpos hδone
    have heq : M.delta * |Real.log M.delta| =
        |Real.log M.delta * M.delta| := by
      rw [abs_mul, abs_of_pos hδpos]
      ring
    rw [heq]
    exact le_of_lt hlog
  have hKδ : K * M.delta ≤ s / 2 := by
    calc
      K * M.delta ≤ K * (s / (2 * K)) :=
        mul_le_mul_of_nonneg_left (le_trans hdelta_le (min_le_right _ _)) hK.le
      _ = s / 2 := by field_simp [hK.ne']
  have hbudget : K * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    calc
      K * M.delta ^ 2 * |Real.log M.delta| =
          (K * M.delta) * (M.delta * |Real.log M.delta|) := by ring
      _ ≤ (s / 2) * 1 :=
        mul_le_mul hKδ hδlog (by positivity) (by positivity)
      _ ≤ s := by linarith
  let gammaScale :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaScale M Cg s
  let A : ℝ := Real.exp 1 * gammaScale
  have hgammaScale : 0 < gammaScale := by
    dsimp [gammaScale]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaScale_pos
      M hCg hsPos
  have hA : 0 < A := by dsimp [A]; positivity
  have hrow : ∀ j : ℕ,
      Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 2)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseRow M k s j) A := by
    intro j
    exact hrows M s hsPos hsOne hbudget k j
  let Fluct : PotentialSample d → ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowFluctuation
      M k s z k k
  let FluctScale : ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowFluctuationScale
      d s A k k
  let Mean : ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowMeanBound
      s A k k
  let Scale : ℝ := FluctScale + Mean
  have hFluct : Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) Fluct FluctScale := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.isBigO_cutoffParameterizedAccumulatedResponseWindowFluctuation
      M k hsPos hsOne z (n := k) (m := k) le_rfl hA hrow
  have hFluctScale : FluctScale = FluctCoeff * A := by
    dsimp [FluctScale, FluctCoeff,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowFluctuationScale]
    have hk : k + 1 - k = 1 := by omega
    rw [hk]
    simp [tri, indep, Homogenization.Book.Ch04.gammaTriangleConst]
    ring
  have hMean : Mean = MeanCoeff * A := by
    dsimp [Mean, MeanCoeff,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowMeanBound]
    have hk : k + 1 - k = 1 := by omega
    rw [hk]
    norm_num
    ring
  have hMeanPos : 0 < Mean := by rw [hMean]; exact mul_pos hMeanCoeff hA
  have hScalePos : 0 < Scale := by
    dsimp [Scale]
    exact add_pos (by rw [hFluctScale]; exact mul_pos hFluctCoeff hA) hMeanPos
  have hwindow :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ae_sum_translatedCutoffParameterizedAccumulatedResponseSup_le_mean_add_fluctuation
      M k hsPos hsOne z (n := k) (m := k) le_rfl hA hrow
  have hYle : ∀ᵐ omega ∂M.P.toMeasure,
      Y omega ≤ Mean + Fluct omega := by
    filter_upwards [hwindow] with omega hω
    have hsum : (∑ i ∈ Finset.Icc k k,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.translatedCutoffParameterizedAccumulatedResponseSup
          M k s i z omega) =
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.translatedCutoffParameterizedAccumulatedResponseSup
          M k s k z omega := by
      simp
    have hsup := hω
    rw [hsum] at hsup
    calc
      Y omega ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.translatedCutoffParameterizedAccumulatedResponseSup
          M k s k z omega := by
        dsimp [Y, term]
        exact aux_inputs_baseline_response_term_le_window M hsPos k z omega
      _ ≤ Mean + Fluct omega := by simpa [Mean, Fluct] using hsup
  have hshift := SubdiffusiveProcess.CoarseGrainingVocab.isBigO_gammaTwo_sub_const
    (X := Fluct) (A := FluctScale) (b := -Mean) hFluct
  have hYleAbs : ∀ᵐ omega ∂M.P.toMeasure,
      Y omega ≤ |Fluct omega - (-Mean)| := by
    filter_upwards [hYle] with omega hω
    have hnonneg : 0 ≤ Fluct omega - (-Mean) := by
      have hy : 0 ≤ Y omega := ENNReal.toReal_nonneg
      linarith [hω]
    calc
      Y omega ≤ Mean + Fluct omega := hω
      _ = Fluct omega - (-Mean) := by ring
      _ = |Fluct omega - (-Mean)| := (abs_of_nonneg hnonneg).symm
  have hYupper' := Homogenization.Book.Ch04.isBigOWith_of_ae_le hshift hYleAbs
  have hYupper : Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) Y Scale := by
    simpa [Scale, abs_of_nonpos (neg_nonpos.mpr hMeanPos.le)] using hYupper'
  have hYbigO : Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) Y Scale := by
    have hYeq : (fun omega => |Y omega|) = Y := by
      funext omega
      exact abs_of_nonneg ENNReal.toReal_nonneg
    simpa [Homogenization.IndependentSums.IsBigO, hYeq] using hYupper
  have hYmeas : AEMeasurable Y M.P.toMeasure := by
    have htermMeas := aux_lem_prefix_limit_actual_Dsc_first_meas M s k z
    exact (ENNReal.measurable_toReal.comp htermMeas).aemeasurable
  have hLp := SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
    hScalePos hq hYmeas hYbigO
  have hδsqrt : M.delta * Real.sqrt |Real.log M.delta| ≤ Real.sqrt M.delta := by
    have hsq : (M.delta * Real.sqrt |Real.log M.delta|) ^ 2 ≤ (Real.sqrt M.delta) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (abs_nonneg (Real.log M.delta)), Real.sq_sqrt hδpos.le]
      have hmul : M.delta * (M.delta * |Real.log M.delta|) ≤ M.delta := by
        calc
          M.delta * (M.delta * |Real.log M.delta|) ≤ M.delta * 1 :=
            mul_le_mul_of_nonneg_left hδlog hδpos.le
          _ = M.delta := by ring
      nlinarith [hmul]
    have hleft : 0 ≤ M.delta * Real.sqrt |Real.log M.delta| :=
      mul_nonneg hδpos.le (Real.sqrt_nonneg _)
    nlinarith [hsq, hleft, Real.sqrt_nonneg M.delta]
  have hScaleEq : Scale = (MeanCoeff + FluctCoeff) * A := by
    dsimp [Scale]
    rw [hFluctScale, hMean]
    ring
  have hAeq : A = Real.exp 1 *
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaSqConst d Cg s) *
        (M.delta * Real.sqrt |Real.log M.delta|) := by
    dsimp [A, gammaScale,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaScale]
    ring
  have hfinalReal :
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt q * Scale ≤
        C * Real.sqrt M.delta := by
    rw [hScaleEq, hAeq]
    calc
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt q *
          ((MeanCoeff + FluctCoeff) *
            (Real.exp 1 * Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffParameterizedResponseGammaSqConst d Cg s) *
              (M.delta * Real.sqrt |Real.log M.delta|))) =
          C * (M.delta * Real.sqrt |Real.log M.delta|) := by
            dsimp [C, D]
            ring
      _ ≤ C * Real.sqrt M.delta :=
        mul_le_mul_of_nonneg_left hδsqrt hC.le
  have hLpBound : eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (C * Real.sqrt M.delta) :=
    hLp.trans (ENNReal.ofReal_le_ofReal hfinalReal)
  have hYmem : MemLp Y (ENNReal.ofReal q) M.P.toMeasure := by
    exact lt_of_le_of_lt hLp (by simp)
  have htermFinite : ∀ omega, term omega ≠ ∞ := by
    intro omega
    have hterm_le_one : term omega ≤ 1 := by
      dsimp [term]
      refine sSup_le ?_
      rintro v ⟨j, l, hjk, hlk, hlj, x, hxgrid, hxann, rfl⟩
      have hexp : -(s / 2) * ((k : ℝ) - (l : ℝ)) ≤ 0 := by
        have hlk' : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
        have hprod : 0 ≤ (s / 2) * ((k : ℝ) - (l : ℝ)) :=
          mul_nonneg (by linarith) (sub_nonneg.mpr hlk')
        linarith
      have hw : (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
      have hwenn : ENNReal.ofReal ((3 : ℝ) ^
          (-(s / 2) * ((k : ℝ) - (l : ℝ)))) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hw
      have hrpow : (min (sSup {u : ENNReal | ∃ e : Vec d,
          Homogenization.vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
              (1 / 2 : ℝ) ≤ 1 :=
        ENNReal.rpow_le_one (min_le_right _ _) (by norm_num)
      calc
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d,
              Homogenization.vecNormSq e = 1 ∧
                u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^
              (1 / 2 : ℝ) ≤ 1 * 1 := by
          exact mul_le_mul hwenn hrpow (by simp) (by simp)
        _ = 1 := by simp
    exact ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) hterm_le_one
  change (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
    MemLp Y (ENNReal.ofReal q) M.P.toMeasure ∧
      eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ))
  refine ⟨Filter.Eventually.of_forall htermFinite, ?_, ?_⟩
  · simpa [Y] using hYmem
  · simpa [Y, Real.sqrt_eq_rpow] using hLpBound

end SubdiffusiveProcess.Paper

