import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic

/-! This module establishes ps D zero for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

/-- ps section6Response nonpos in the finite stopping construction. -/
theorem ps_section6Response_nonpos [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P = 0) (hahom : ahom M n = 1)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (z e : Vec d) (he : vecNormSq e = 1) :
    section6Response M n n omega z e ≤ 0 := by
  have ha1 : ∀ x, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x = 1 := by
    intro x
    unfold SubdiffusiveProcess.Frozen.Assumptions.aCutoff
    have hzero : ∀ k, (translatePotentialSample z omega k) x = 0 := by
      intro k
      rw [translatePotentialSample, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]
      exact hz k (x + z)
    rw [Finset.sum_eq_zero (fun k hk => by rw [hzero k, htau, sub_zero]), Real.exp_zero]
  let U : Book.Ch02.Domain d := Book.Ch02.cubeDomain (originCube d n)
  let ha : ScalarCoeffOnData U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega)) :=
    SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData M n (translatePotentialSample z omega) U
  have hmax := SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn_le_half_scalar_ratio U ha
    (alpha := 1) one_pos (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n (translatePotentialSample z omega) x)
  have hle : ENNReal.ofReal (section6Response M n n omega z e)
      ≤ SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn U ha.toCoeffOn 1 := by
    have hsec : section6Response M n n omega z e =
        paperScalarProbe (originCube d n) (aCutoffFamily M n (translatePotentialSample z omega)) 1 e := by
      unfold section6Response
      rw [hahom]
    rw [hsec]
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn paperScalarProbe
    simp only [Real.sqrt_one, inv_one, one_smul]
    exact le_iSup (fun e' : {e' // vecNormSq e' = 1} => ENNReal.ofReal (J U ha.toCoeffOn e'.1 e'.1)) ⟨e, he⟩
  have hrhs : SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn U ha.toCoeffOn 1 = 0 := by
    have havg : Book.Ch02.average U
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x / 1
          + 1 / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x - 2) = 0 := by
      have hfun : (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x / 1
          + 1 / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x - 2)
          = (fun _ => (0:ℝ)) := by
        funext x
        rw [ha1 x]
        norm_num
      rw [hfun]
      unfold Book.Ch02.average
      simp only [integral_zero, mul_zero]
    have hR : ENNReal.ofReal (1 / 2 * Book.Ch02.average U
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x / 1
          + 1 / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega) x - 2)) = 0 := by
      rw [havg, mul_zero, ENNReal.ofReal_zero]
    have hle0 : SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn U ha.toCoeffOn 1 ≤ 0 :=
      le_trans hmax (le_of_eq hR)
    exact le_antisymm hle0 (zero_le _)
  have hfin : ENNReal.ofReal (section6Response M n n omega z e) ≤ 0 := by
    rw [hrhs] at hle; exact hle
  have h0 : ENNReal.ofReal (section6Response M n n omega z e) = 0 := le_antisymm hfin (zero_le _)
  rwa [ENNReal.ofReal_eq_zero] at h0

/-- ps F zero in the finite stopping construction. -/
theorem ps_F_zero (s : ℝ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (m : ℕ) (z : Vec d) :
    sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
              w = ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (omega i) x))|}} = 0 := by
  have hgd : ∀ (i : ℕ) (x : Vec d), shellGradient (omega i) x = 0 := by
    intro i x
    have h1 : HasFDerivAt (fun _ : Vec d => (0 : ℝ)) (0 : Vec d →L[ℝ] ℝ) x :=
      hasFDerivAt_const 0 x
    have h2 : HasFDerivAt (fun _ : Vec d => (0 : ℝ)) ((omega i).deriv x) x := by
      have h0 : (⇑((omega i).val.1) : Vec d → ℝ) = fun _ => (0 : ℝ) := by
        funext y
        exact hz i y
      have hthis := (omega i).hasFDerivAt (x := x)
      rw [h0] at hthis
      exact hthis
    have huniq : (omega i).deriv x = 0 := h2.unique h1
    funext k
    simp only [shellGradient, huniq, ContinuousLinearMap.zero_apply, Pi.zero_apply]
  have hnorm0 : Homogenization.euclideanNorm (0 : Vec d) = 0 := by
    simp only [euclideanNorm, vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
  have hinner : ∀ (i : ℕ) (x : Vec d),
      ENNReal.ofReal |(|(omega i).val.1 x| + (3 : ℝ) ^ (i : ℝ) *
        Homogenization.euclideanNorm (shellGradient (omega i) x))| = 0 := by
    intro i x
    rw [hz i x, hgd i x, hnorm0]
    simp only [abs_zero, Real.rpow_natCast, mul_zero, add_zero, ENNReal.ofReal_zero]
  have hsup0 : ∀ (j i : ℕ),
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
        w = ENNReal.ofReal |(|(omega i).val.1 x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (omega i) x))|} = 0 := by
    intro j i
    refine le_antisymm ?_ (zero_le _)
    apply sSup_le
    intro w hw
    obtain ⟨x, _, rfl⟩ := hw
    rw [hinner i x]
  have hsum : ∀ j : ℕ,
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
          w = ENNReal.ofReal |(|(omega i).val.1 x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (omega i) x))|} = 0 := by
    intro j
    apply Finset.sum_eq_zero
    intro i _
    exact hsup0 j i
  refine le_antisymm ?_ (zero_le _)
  apply sSup_le
  intro v hv
  obtain ⟨j, rfl⟩ := hv
  rw [hsum j, mul_zero]

/-- ps P two in the finite stopping construction. -/
theorem ps_P_two (s : ℝ) (hs : 0 < s)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (m : ℕ) (z : Vec d) :
    sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                  ENNReal.ofReal (Real.exp |omega i x|)) +
                sSup {u : ENNReal | ∃ K : ℕ,
                  u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}} = 2 := by
  have hA1 : ∀ (i : ℕ) (x : Vec d), ENNReal.ofReal (Real.exp |omega i x|) = 1 := by
    intro i x
    rw [hz i x, abs_zero, Real.exp_zero, ENNReal.ofReal_one]
  have hA2 : ∀ (i : ℕ) (x : Vec d),
      ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|)) = 1 := by
    intro i x
    rw [hz i x, hz i z, sub_self, abs_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  have hcube0 : ∀ k : ℤ, (0 : Vec d) ∈ openCubeSet (originCube d k) := by
    intro k
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hpos : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
    simp only [Pi.zero_apply]
    constructor <;> nlinarith only [hs, hz, hA1, hA2, hpos, hpos]
  have hW : ∀ j : ℕ, sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
      w = (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |omega i x|)) +
          sSup {u : ENNReal | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
              ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}} = 2 := by
    intro j
    have hU : ∀ x : Vec d, sSup {u : ENNReal | ∃ K : ℕ,
        u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
          ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))} = 1 := by
      intro x
      apply le_antisymm
      · apply sSup_le
        rintro u ⟨K, rfl⟩
        rw [Finset.prod_eq_one (fun i _ => hA2 i x)]
      · apply le_sSup
        exact ⟨0, by rw [Finset.prod_eq_one (fun i _ => hA2 i x)]⟩
    apply le_antisymm
    · apply sSup_le
      rintro w ⟨x, hx, rfl⟩
      rw [hU x, Finset.prod_eq_one (fun i _ => hA1 i x)]
      norm_num
    · have hmem : z ∈ translatedCube d (m + 1 + j) z := by
        refine ⟨0, ?_, ?_⟩
        · rw [cube]; exact hcube0 _
        · simp only [add_zero]
      apply le_sSup
      refine ⟨z, hmem, ?_⟩
      rw [hU z, Finset.prod_eq_one (fun i _ => hA1 i z)]
      norm_num
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨j, rfl⟩
    rw [hW j]
    have hb : ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j:ℝ) / 8))) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have h8 : (0:ℝ) ≤ s * (j:ℝ) / 8 :=
        div_nonneg (mul_nonneg (le_of_lt hs) hj) (by norm_num)
      linarith only [hs, hz, hA1, hA2, hcube0, hW, hj, h8]
    exact mul_le_of_le_one_left (show (0 : ENNReal) ≤ 2 from by norm_num) hb
  · apply le_sSup
    refine ⟨0, ?_⟩
    rw [hW 0, show -(s * ((0:ℕ):ℝ) / 8) = 0 by norm_num, Real.rpow_zero,
      ENNReal.ofReal_one, one_mul]

/-- ps R zero in the finite stopping construction. -/
theorem ps_R_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hJ : ∀ (n : ℕ) (x e : Vec d), vecNormSq e = 1 → section6Response M n n omega x e ≤ 0)
    (m : ℕ) (z : Vec d) :
    sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
          sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M n n omega x e)}} = 0 := by
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨j, n, hj, hn, x, hg, hc, rfl⟩
    have hinner : sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
        u = ENNReal.ofReal (section6Response M n n omega x e)} = 0 := by
      apply le_antisymm
      · apply sSup_le
        rintro u ⟨e, he, rfl⟩
        exact (ENNReal.ofReal_eq_zero.mpr (hJ n x e he)).le
      · exact zero_le _
    rw [hinner, mul_zero]
  · exact zero_le _

/-- psD Jsup zero in the finite stopping construction. -/
theorem psD_Jsup_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hJ : ∀ (n : ℕ) (x e : Vec d), vecNormSq e = 1 → section6Response M n n omega x e ≤ 0)
    (l : ℕ) (x : Vec d) :
    sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
      u = ENNReal.ofReal (section6Response M l l omega x e)} = 0 := by
  apply le_antisymm
  · apply sSup_le
    rintro u ⟨e, he, rfl⟩
    exact le_of_eq (ENNReal.ofReal_eq_zero.mpr (hJ l x e he))
  · exact zero_le _

/-- psD shellBlock zero in the finite stopping construction. -/
theorem psD_shellBlock_zero (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (m j : ℕ) (x : Vec d) :
    shellBlock m j omega x = 0 := by
  unfold shellBlock
  apply Finset.sum_eq_zero
  intro i hi
  exact hz i x

/-- psD deriv zero in the finite stopping construction. -/
theorem psD_deriv_zero (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (j : ℕ) (x : Vec d) :
    (omega j).deriv x = 0 := by
  have hfun : (fun y : Vec d => omega j y) = (fun _ : Vec d => (0 : ℝ)) := by
    funext y; exact hz j y
  have h1 : HasFDerivAt (fun y : Vec d => omega j y) ((omega j).deriv x) x :=
    (omega j).hasFDerivAt x
  have h0 : HasFDerivAt (fun y : Vec d => omega j y) (0 : Vec d →L[ℝ] ℝ) x := by
    rw [hfun]
    exact hasFDerivAt_const (0 : ℝ) x
  exact HasFDerivAt.unique h1 h0

/-- psD shellGradient zero in the finite stopping construction. -/
theorem psD_shellGradient_zero (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (j : ℕ) (x : Vec d) :
    shellGradient (omega j) x = 0 := by
  unfold shellGradient
  funext i
  rw [SubdiffusiveProcess.FiniteStopping.psD_deriv_zero omega hz j x]
  exact ContinuousLinearMap.zero_apply (Pi.single i 1)

/-- ps D zero in the finite stopping construction. -/
theorem ps_D_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hJ : ∀ (n : ℕ) (x e : Vec d), vecNormSq e = 1 → section6Response M n n omega x e ≤ 0)
    (hz : ∀ (i : ℕ) (x : Vec d), omega i x = 0) (k : ℕ) (z : Vec d) :
    sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)} +
        sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              w = ENNReal.ofReal |shellBlock k j omega x|}} +
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |omega 0 x|} +
        ∑' j : ℕ, (if k ≤ j then
          ENNReal.ofReal ((3 : ℝ) ^ k) *
            sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
          else 0) = 0 := by
  have hterm1 : (sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)}) = 0 := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨j, l, hjk, hlk, hlj, x, hgrid, hcube, rfl⟩
      rw [SubdiffusiveProcess.FiniteStopping.psD_Jsup_zero M omega hJ l x,
          min_eq_left (zero_le_one : (0 : ENNReal) ≤ 1),
          ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      apply le_of_eq
      exact mul_zero _
    · exact zero_le _
  have hterm2 : (sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |shellBlock k j omega x|}}) = 0 := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨j, hjk, rfl⟩
      have hsup : sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          w = ENNReal.ofReal |shellBlock k j omega x|} = 0 := by
        apply le_antisymm
        · apply sSup_le
          rintro w ⟨x, hx, rfl⟩
          apply le_of_eq
          simp only [SubdiffusiveProcess.FiniteStopping.psD_shellBlock_zero omega hz k j x, abs_zero, ENNReal.ofReal_zero]
        · exact zero_le _
      rw [hsup]
      apply le_of_eq
      exact mul_zero _
    · exact zero_le _
  have hterm3 : ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        w = ENNReal.ofReal |omega 0 x|} = 0 := by
    have hsup : sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        w = ENNReal.ofReal |omega 0 x|} = 0 := by
      apply le_antisymm
      · apply sSup_le
        rintro w ⟨x, hx, rfl⟩
        apply le_of_eq
        simp only [hz 0 x, abs_zero, ENNReal.ofReal_zero]
      · exact zero_le _
    rw [hsup]
    exact mul_zero _
  have hterm4 : (∑' j : ℕ, (if k ≤ j then
      ENNReal.ofReal ((3 : ℝ) ^ k) *
        sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
      else 0)) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro j
    by_cases hkj : k ≤ j
    · rw [if_pos hkj]
      have hsup : sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|} = 0 := by
        apply le_antisymm
        · apply sSup_le
          rintro w ⟨x, hx, rfl⟩
          apply le_of_eq
          simp only [SubdiffusiveProcess.FiniteStopping.psD_shellGradient_zero omega hz j x, Homogenization.euclideanNorm_zero,
            abs_zero, ENNReal.ofReal_zero]
        · exact zero_le _
      rw [hsup]
      exact mul_zero _
    · exact if_neg hkj
  rw [hterm1, hterm2, hterm3, hterm4]
  simp only [add_zero]

end SubdiffusiveProcess.FiniteStopping
