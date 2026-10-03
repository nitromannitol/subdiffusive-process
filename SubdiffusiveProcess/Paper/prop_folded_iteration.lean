module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.Dilation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.VecDotForm
public import SubdiffusiveProcess.Lane2.LocalRepresentative
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.HolderSobolevBridge
public import SubdiffusiveProcess.Lane4.NormalizedEnergyComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorPrefactorPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedDatumPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FullWspTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.CoarsePoincareEnergyLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CoefficientEnergyBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TopWindowEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.PlanarStreamFunction
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_iteration_input
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.lem_repair
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_localization
public import SubdiffusiveProcess.Paper.lem_repair_err_good_scale_transport
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_carrier_bridge
public import SubdiffusiveProcess.Paper.rem_repair

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section InteriorOneStep

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
attribute [local instance] Classical.propDecidable

/-- Datum-free interior one-step excess decay for an ARBITRARY coefficient, from the interior
harmonic-approximation clause of `lane4_deterministic_good_scale_input` (paper 356–370, item (v)).
This is GMC's `excess_decay_interior_of_interiorHarmonic` with the aCutoff anchor replaced by that
clause and the good-event cap replaced by the error bound `err ≤ Cerr·ε`; the powers are the
source powers `s^{-3/2}`, `s^{-15/2}`. -/
theorem aux_prop_folded_iteration_interior_excess_decay (d : ℕ) (hd : 2 ≤ d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∀ Cerr : ℝ, 0 < Cerr → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 → ∀ k : ℕ, 0 < k →
      ∀ m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal (Cerr * epsilon) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
              excess n (truncatedCube d m n x) u.toFun +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
              (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
                Homogenization.Book.Ch02.MultiscaleExponent.infinity
                (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                data.toTriadicCoeffFamily a0).toReal *
              Real.sqrt (vecNormSq ell.slope) +
            C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (a0)⁻¹ * (3 : ℝ) ^ (s * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal := by
  haveI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  intro Cerr hCerr
  obtain ⟨CA, hCApos, hA⟩ := D.2.1 Cerr hCerr
  set CB : ℝ := Cerr with hCBdef
  have hCBpos : 0 < CB := hCerr
  refine ⟨anchorInteriorConst d CA CB,
    anchorInteriorConst_pos d hCApos.le hCBpos.le, ?_⟩
  have hC0 : (0 : ℝ) ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_nonneg d hCApos.le hCBpos.le
  have hCcontr : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
      ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_contraction_le d hCApos.le hCBpos.le
  have hCrem : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
      (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
      ≤ anchorInteriorConst d CA CB := anchorInteriorConst_remainder_le d
  have hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ anchorInteriorConst d CA CB :=
    anchorInteriorConst_crude_le d hCApos.le hCBpos.le
  set C : ℝ := anchorInteriorConst d CA CB with hCdef
  intro s hs0 hs4 epsilon heps0 heps1 k hk m n hkn hnm x hx z hz hxz hnbt a data a0 ha0 herr
    u g hweak hgfrac ell hell
  set errE : ENNReal := paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
    (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) data.toTriadicCoeffFamily a0
    with herrEdef
  have hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m :=
    Section6HolderInterior.translatedCube_subset_cube_of_not_boundaryTouches
      hx (by omega) hnbt
  have hdne : d ≠ 0 := by omega
  have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hErr : 0 ≤ errE.toReal := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (a0)⁻¹ := inv_nonneg.2 ha0.le
  have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
  have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
  have hss : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs15 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon :=
    mul_nonneg (mul_nonneg hpow2 hss) heps0
  have hT2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      s ^ (-3 / 2 : ℝ) * errE.toReal * Real.sqrt (vecNormSq ell.slope) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr) hSl
  have hT3 : (0 : ℝ) ≤ C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      (a0)⁻¹ * (3 : ℝ) ^ (s * n) *
      (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
  by_cases hk6 : 6 ≤ k
  · obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
    have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
      hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
    have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
      Section6Schauder.isOpen_translatedCube d _ y
    have herr1 : errE ≤ ENNReal.ofReal Cerr := by
      refine le_trans herr (ENNReal.ofReal_le_ofReal ?_)
      calc Cerr * epsilon ≤ Cerr * 1 := mul_le_mul_of_nonneg_left heps1 hCerr.le
        _ = Cerr := mul_one _
    obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
      hA s hs0 hs4 m n hnm z hz x hxz hnbt a data a0 ha0 herr1 u g hweak hgfrac y hy hy1 hy2
        (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨v', K, hv'ae, hv'mem, hK0, hint, hgradv, hholK, hschauder⟩ :=
      Section6Schauder.exists_gradientHolder_of_weaklyHarmonic (d := d) (m := (m : ℤ))
        (n := (n : ℤ)) (x := x) (y := y) hdne hx (by omega) hgate hy1 hvharm
    have hv'4 : MemLp v' 2 (volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)) :=
      hv'mem.restrict _
    have hone := excess_oneStep_of_schauder (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k)
      (Kh := 0) hk6 hx (by omega) hu_n hv'4 hK0
      (Section6Schauder.schauderInteriorConst_nonneg d) hint hgradv hholK hschauder
    have hDeq : normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun p => u.toFun p - v' p)
        = normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
          (fun q => u.toFun q - v.toFun q) := by
      refine normalizedL2On_congr_ae ?_
      have hres : v' =ᵐ[volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)] v.toFun :=
        hv'ae.filter_mono (ae_mono (Measure.restrict_mono hy1 le_rfl))
      filter_upwards [hres] with p hp
      rw [hp]
    rw [hDeq, mul_zero, add_zero] at hone
    have hD := hHA v hvharm hvzt
    have hcapz : errE.toReal ≤ CB * epsilon :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCerr.le heps0) herr
    have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
      hx (by omega) hu_n hell
    set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun with hEdef
    set Err := errE.toReal with hErrdef
    set Sl := Real.sqrt (vecNormSq ell.slope) with hSldef
    set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal with hFgdef
    set Tinv := (a0)⁻¹ with hTinvdef
    set Dd := normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
      (fun q => u.toFun q - v.toFun q) with hDdef
    set N := normalizedL2On (truncatedCube d m n x)
      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) with hNdef
    have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k :=
      oneStepRemainderConst_nonneg d (Section6Schauder.schauderInteriorConst_nonneg d) k
    have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := hpow2
    have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        positivity
      simpa using h0
    have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d :=
      mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d))
        (Section6Schauder.schauderInteriorConst_nonneg d)
    have hCrm0 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1 := by
      linarith only [h81]
    have hKrb : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k
        ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      have hleft : 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        exact mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
      have hright : (3 : ℝ) ^ ((k : ℤ)) *
            Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
          ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
          rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
          norm_num
        have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) =
            ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
          sqrt_pow_eq_rpow_half ht0.le d
        have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
            ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
          refine Real.sqrt_le_sqrt ?_
          rw [← htz]
          exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
            (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
        have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
          three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
        rw [hsplit, htz]
        exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
      rw [oneStepRemainderConst]
      linarith only [hleft, hright]
    have hbudget : ∀ c : ℝ, 0 ≤ c →
        c ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d →
        oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA * c
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      intro c hc0 hcle
      have h1 : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA * c
          ≤ ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * CA * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKrb hCApos.le) hc0
      have h2 : ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * CA * c
          = ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
      have h3 : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c
          ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
            (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
        mul_le_mul_of_nonneg_left hcle (mul_nonneg hCrm0 hCApos.le)
      have h4 : ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
        mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
      linarith only [h1, h2.le, h2.ge, h4]
    have hCH0 : (0 : ℝ) ≤ fractionalHolderConst d := fractionalHolderConst_nonneg d
    have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hbCB := hbudget CB hCBpos.le (by linarith only [hCH0, hsd0])
    have hbOne := hbudget 1 zero_le_one (by linarith only [hCH0, hsd0, hCBpos])
    have hbSqrt := hbudget (Real.sqrt (d : ℝ) / 2) (by linarith only [hsd0])
      (by linarith only [hCH0, hCBpos])
    have hb3 : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA
        ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by simpa using hbOne
    have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
    have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
        = (3 : ℝ) ^ (s * (n : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    have hCAErr : (0 : ℝ) ≤ CA * s ^ (-3 / 2 : ℝ) * Err :=
      mul_nonneg (mul_nonneg hCApos.le hss) hErr
    have hNterm : CA * s ^ (-3 / 2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
        ≤ CA * s ^ (-3 / 2 : ℝ) * Err * E +
          CA * s ^ (-3 / 2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
      have hstep := mul_le_mul_of_nonneg_left hstep6 hCAErr
      linarith only [hstep]
    have hDs : (3 : ℝ) ^ (-(n : ℤ)) * Dd
        ≤ CA * s ^ (-3 / 2 : ℝ) * Err * E
          + CA * s ^ (-3 / 2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
          + CA * s ^ (-3 / 2 : ℝ) * Err * 0
          + CA * s ^ (-15 / 2 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg
          + 0 := by
      have hbase := mul_le_mul_of_nonneg_left hD h3n.le
      have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
            (CA * s ^ (-3 / 2 : ℝ) * Err * N +
              CA * s ^ (-15 / 2 : ℝ) * Tinv *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg)
          = CA * s ^ (-3 / 2 : ℝ) * Err *
              ((3 : ℝ) ^ (-(n : ℤ)) * N) +
            CA * s ^ (-15 / 2 : ℝ) * Tinv *
              ((3 : ℝ) ^ (-(n : ℤ)) *
                (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg := by
        ring
      rw [hexp, hfront] at hbase
      linarith only [hbase, hNterm]
    have hKcle : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        rw [three_zpow_rpow_half_eq]
        push_cast
        ring_nf
      rw [hpe]
      exact mul_le_mul_of_nonneg_right hCcontr hpow1
    have hcombined := excessDecayCombine hEn hErr hSl hFg hTail
      (show (0 : ℝ) ≤ 0 by norm_num) heps0 hss hs15 hpow3 hKr0 hCApos.le
      hone hDs hcapz hKcle hbCB hbSqrt hb3
      (show oneStepRemainderConst d
          (Section6Schauder.schauderInteriorConst d) k * 0 ≤ 0 by
        rw [mul_zero])
    simpa only [add_zero] using hcombined
  have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
    (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu_n
  rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
  have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
      calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 243 := by norm_num
    have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
      refine Real.sqrt_le_sqrt ?_
      calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
            pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
              (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
        _ = (3 : ℝ) ^ (7 * d) := by
            rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
    have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
      linarith
    have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
      rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
    have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
        ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
      mul_le_mul hA1 hA2 hsq1 (by norm_num)
    have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
        = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
      rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
    have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      rw [← hA4]
      refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
    linarith only [hleft, hmid, hright]
  have hstep : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
      ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
          excess (n : ℤ) (truncatedCube d m n x) u.toFun := by
    have h1 : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) * excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
      le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)
    have h2 : C * (3 : ℝ) ^ (-(k : ℝ) / 2) ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP]) hC0
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hEn)
  exact le_trans (le_trans hstep (le_add_of_nonneg_right hT2))
    (le_add_of_nonneg_right hT3)

end InteriorOneStep

section IterationCore

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
attribute [local instance] Classical.propDecidable

/-- Steps (2)–(3) of the folded proof, deterministic part: on the origin-centred windows
`U_j = truncatedCube d m j 0` of the root `□_m`, the arbitrary-coefficient interior one-step
(`aux_prop_folded_iteration_interior_excess_decay`) feeds the proved iteration lemma
(`Section6Holder.truncatedCube_iteration`) at every non-bad scale.  At a non-bad scale `j` the
discounted error of the coefficient at `□_{j+2}` against the scale's reference `a0 j` is at most
`Cerr·η`, where `η` satisfies the contraction threshold `CH(3^{-h/2}+3^{(1+d/2)h}s^{-3/2}η) ≤ θ^h`.
The error and source terms enter the exponent and the defect sum exactly as in the paper. -/
theorem aux_prop_folded_iteration_iteration_core (d : ℕ) (hd : 2 ≤ d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∀ Cerr : ℝ, 0 < Cerr → ∃ CH CI : ℝ, 0 < CH ∧ 0 < CI ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ h : ℕ, 0 < h → ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5 →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * s ^ (-3 / 2 : ℝ) * eta) ≤
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h →
      ∀ m n top : ℕ, n < top → top + 5 ≤ m →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + 0)),
      ∀ a0 : ℕ → ℝ, (∀ j, 0 < a0 j) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc (n : ℤ) (top : ℤ) →
      (∀ j : ℕ, n ≤ j → j ≤ top → (j : ℤ) ∉ bad →
        h ≤ j ∧
          paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (s / 8)
              Homogenization.Book.Ch02.MultiscaleExponent.infinity
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
              data.toTriadicCoeffFamily (a0 j) ≤ ENNReal.ofReal (Cerr * eta)) →
      let epsJ : ℤ → ℝ := fun j =>
        if j ∈ bad then 0 else
          CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * s ^ (-3 / 2 : ℝ) *
            (paperHomogenizationError (originCube d ((j.toNat : ℤ) + 2)) ((j.toNat : ℤ) + 2)
              (s / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
              data.toTriadicCoeffFamily (a0 j.toNat)).toReal
      let defJ : ℤ → ℝ := fun j =>
        if j ∈ bad then 0 else
          CH * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
            (a0 j.toNat)⁻¹ * (3 : ℝ) ^ (s * (j.toNat : ℕ)) *
            (fractionalSeminormOn (truncatedCube d m (j.toNat : ℕ) 0) s g).toReal
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (truncatedCube d m n 0)
            (fun x ↦ u.toFun x - averageOn (truncatedCube d m n 0) u.toFun) ≤
        Real.exp (CI * (h + 1) * (bad.card + 1) +
            CI * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsJ j) *
          ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On (truncatedCube d m top 0)
                (fun x ↦ u.toFun x - averageOn (truncatedCube d m top 0) u.toFun) +
            ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), defJ j) := by
  intro Cerr hCerr
  obtain ⟨CH, hCH, hstep⟩ := aux_prop_folded_iteration_interior_excess_decay d hd D Cerr hCerr
  obtain ⟨CI, hCI, hiter⟩ := Section6Holder.truncatedCube_iteration d
  refine ⟨CH, CI, hCH, hCI, ?_⟩
  intro s hs0 hs4 h hh hth35 eta heta0 heta1 hthr m n top hntop htopm a data a0 ha0 u g hweak
    hgfrac bad hbad hgood epsJ defJ
  have htheta : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hthetah : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) :=
    ⟨pow_pos htheta.1 h, hth35⟩
  have hz : (0 : Vec d) ∈ cube d m := zero_mem_cube d m
  have hnonneg : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), 0 ≤ epsJ j ∧ 0 ≤ defJ j := by
    intro j _
    constructor
    · change 0 ≤ (if j ∈ bad then (0 : ℝ) else _)
      split_ifs
      · exact le_rfl
      · have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) := Real.rpow_nonneg (by norm_num) _
        have h2 : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
        exact mul_nonneg (mul_nonneg (mul_nonneg hCH.le h1) h2) ENNReal.toReal_nonneg
    · change 0 ≤ (if j ∈ bad then (0 : ℝ) else _)
      split_ifs
      · exact le_rfl
      · have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) := Real.rpow_nonneg (by norm_num) _
        have h2 : (0 : ℝ) ≤ s ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
        have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * (j.toNat : ℕ)) := Real.rpow_nonneg (by norm_num) _
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCH.le h2) h1)
          (inv_nonneg.2 (ha0 _).le)) h3) ENNReal.toReal_nonneg
  have hrec : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), j ∉ bad →
      ∀ ell : Affine d,
        ell ∈ affineMinimizers (truncatedCube d m j 0) u.toFun →
        excess (j - h) (truncatedCube d m (j - h) 0) u.toFun ≤
          ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h * excess j (truncatedCube d m j 0) u.toFun +
            epsJ j * Real.sqrt (vecNormSq ell.slope) + defJ j := by
    intro j hj hjbad ell hell
    obtain ⟨hnj, hjtop⟩ := Finset.mem_Icc.1 hj
    have hj0 : (0 : ℤ) ≤ j := le_trans (by exact_mod_cast Nat.zero_le n) hnj
    obtain ⟨jn, rfl⟩ : ∃ jn : ℕ, j = (jn : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj0).symm⟩
    have hnjn : n ≤ jn := by exact_mod_cast hnj
    have hjntop : jn ≤ top := by exact_mod_cast hjtop
    obtain ⟨hhj, herr⟩ := hgood jn hnjn hjntop hjbad
    have hint : ¬ BoundaryTouches (truncatedCube d m jn 0) (cube d m) :=
      not_boundaryTouches_of_interior (m := (m : ℤ)) (n := (jn : ℤ))
        (zero_mem_cube d ((m : ℤ) - 1)) (by omega)
    have hxz : (0 : Vec d) ∈ truncatedCube d m ((jn : ℤ) - 3) 0 := mem_truncatedCube_self _ hz
    have hone := hstep s hs0 hs4 eta heta0 heta1 h hh m jn hhj (by omega) 0 hz 0 hz hxz hint
      a data (a0 jn) (ha0 jn) herr u g hweak hgfrac ell hell
    have hEj : 0 ≤ excess (jn : ℤ) (truncatedCube d m jn 0) u.toFun := excess_nonneg _ _ _
    have hcoef := mul_le_mul_of_nonneg_right hthr hEj
    have heps : epsJ (jn : ℤ) = CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * s ^ (-3 / 2 : ℝ) *
        (paperHomogenizationError (originCube d ((jn : ℤ) + 2)) ((jn : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (a0 jn)).toReal := by
      change (if (jn : ℤ) ∈ bad then (0 : ℝ) else _) = _
      rw [if_neg hjbad, Int.toNat_natCast]
    have hdef : defJ (jn : ℤ) = CH * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (a0 jn)⁻¹ * (3 : ℝ) ^ (s * (jn : ℕ)) *
        (fractionalSeminormOn (truncatedCube d m (jn : ℕ) 0) s g).toReal := by
      change (if (jn : ℤ) ∈ bad then (0 : ℝ) else _) = _
      rw [if_neg hjbad, Int.toNat_natCast]
    rw [heps, hdef]
    have hcast : ((jn : ℤ) - (h : ℤ)) = ((jn : ℕ) : ℤ) - ((h : ℕ) : ℤ) := rfl
    calc excess ((jn : ℤ) - (h : ℤ)) (truncatedCube d m ((jn : ℤ) - (h : ℤ)) 0) u.toFun
        ≤ _ := hone
      _ ≤ _ := by linarith only [hcoef]
  exact (hiter h hh _ htheta hthetah m n top hntop (by omega) 0 hz u bad hbad epsJ defJ
    hnonneg hrec).1

end IterationCore

section PaperErrorDilation

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch02 in
/-- Probe-level dilation: the paper's scalar probe of a coefficient family `B` on `3^k R` equals
that of `A` on `R` as soon as the two coefficient fields are a.e. dilates of each other on `3^k R`
(no condition on the carried ellipticity constants). -/
theorem aux_prop_folded_iteration_probe_dilate {d : ℕ} (k : ℤ)
    (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d) (R : Homogenization.TriadicCube d)
    (h : (B.coeffOn (dilateCube k R)).toCoeffField
        =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
        dilateCoeffField k (A.coeffOn R).toCoeffField)
    (alpha : ℝ) :
    paperScalarProbeMax (dilateCube k R) B alpha = paperScalarProbeMax R A alpha := by
  have hdil := CoeffOn.dilate_isCubeDilation k (A.coeffOn R)
  have hae : CoeffOn.AEEq (B.coeffOn (dilateCube k R)) (CoeffOn.dilate k (A.coeffOn R)) := by
    change (B.coeffOn (dilateCube k R)).toCoeffField
      =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
      (CoeffOn.dilate k (A.coeffOn R)).toCoeffField
    exact h.trans hdil.coeff_ae_eq.symm
  unfold paperScalarProbeMax paperScalarProbe
  apply iSup_congr
  intro e
  congr 1
  exact (responseJ_eq_ofAEEq hae _ _).trans (responseJ_dilate hdil _ _)

open Homogenization.Book.Ch02 in
/-- Scale-level dilation of the paper response aggregation. -/
theorem aux_prop_folded_iteration_scale_dilate {d : ℕ} (k : ℤ)
    (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d) (Q : Homogenization.TriadicCube d)
    (n : ℤ)
    (h : ∀ R : Homogenization.TriadicCube d, R ∈ Homogenization.descendantsAtScale Q n →
      (B.coeffOn (dilateCube k R)).toCoeffField
        =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
        dilateCoeffField k (A.coeffOn R).toCoeffField)
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ) :
    paperScaleResponseAtScale (dilateCube k Q) (n + k) p B alpha =
      paperScaleResponseAtScale Q n p A alpha := by
  classical
  have himg := descendantsAtScale_dilateCube k n Q
  have hinj : Set.InjOn (dilateCube k : Homogenization.TriadicCube d → _)
      (Homogenization.descendantsAtScale Q n : Set _) :=
    (dilateCube_injective k).injOn
  cases p with
  | finite p =>
      simp only [paperScaleResponseAtScale]
      rw [himg, Finset.card_image_of_injOn hinj, Finset.sum_image hinj]
      congr 2
      apply Finset.sum_congr rfl
      intro R hR
      rw [aux_prop_folded_iteration_probe_dilate k A B R (h R hR) alpha]
  | infinity =>
      simp only [paperScaleResponseAtScale, paperMaxDescendantProbeAtScale]
      congr 1
      rw [himg]
      apply le_antisymm
      · refine iSup_le ?_
        rintro ⟨R, hR⟩
        obtain ⟨R0, hR0, rfl⟩ := Finset.mem_image.1 hR
        refine le_iSup_of_le ⟨R0, hR0⟩ ?_
        rw [aux_prop_folded_iteration_probe_dilate k A B R0 (h R0 hR0) alpha]
      · refine iSup_le ?_
        rintro ⟨R0, hR0⟩
        refine le_iSup_of_le ⟨dilateCube k R0, Finset.mem_image_of_mem _ hR0⟩ ?_
        rw [aux_prop_folded_iteration_probe_dilate k A B R0 (h R0 hR0) alpha]

open Homogenization.Book.Ch02 in
/-- Dilation covariance of the paper homogenization error `ℰ_{s,p,q}`: the error of `B` on
`3^k Q` at scale `n+k` equals that of `A` on `Q` at scale `n` whenever, on every descendant `R` of
`Q`, the coefficient field of `B` on `3^k R` is a.e. the dilate of that of `A` on `R`. -/
theorem aux_prop_folded_iteration_paper_error_dilate {d : ℕ} (k : ℤ)
    (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d) (Q : Homogenization.TriadicCube d)
    (n : ℤ) (s : ℝ)
    (h : ∀ (j : ℤ) (R : Homogenization.TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q j →
      (B.coeffOn (dilateCube k R)).toCoeffField
        =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
        dilateCoeffField k (A.coeffOn R).toCoeffField)
    (p q : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ) :
    paperHomogenizationError (dilateCube k Q) (n + k) s p q B alpha =
      paperHomogenizationError Q n s p q A alpha := by
  have hsc : ∀ l : ℕ, paperScaleResponseAtScale (dilateCube k Q) (n + k - (l : ℤ)) p B alpha =
      paperScaleResponseAtScale Q (n - (l : ℤ)) p A alpha := by
    intro l
    rw [show n + k - (l : ℤ) = (n - (l : ℤ)) + k by ring]
    exact aux_prop_folded_iteration_scale_dilate k A B Q (n - (l : ℤ)) (h (n - (l : ℤ))) p alpha
  cases q with
  | finite q =>
      simp only [paperHomogenizationError, paperHomogenizationErrorFinite]
      congr 1
      exact tsum_congr fun l => by rw [hsc l]
  | infinity =>
      simp only [paperHomogenizationError, paperHomogenizationErrorInfinity]
      exact iSup_congr fun l => by rw [hsc l]

open Homogenization.Book.Ch02 in


theorem aux_prop_folded_iteration_err_physical {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (m j : ℕ) (hR : (0 : ℝ) < 3 ^ m) (hjm : j + 2 ≤ m)
    (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR))
    (a' : SpatialCoordinates d → ℝ)
    (ha' : ∀ᵐ y ∂volume.restrict
        (Homogenization.openCubeSet (Homogenization.originCube d ((j : ℤ) + 2))),
      a' y = (a.val : SpatialCoordinates d → ℝ) (fun i => z i + y i))
    (data : ScalarTriadicCoeffData (fun y => a' (y + 0)))
    (a0 : ℝ) (ha0 : 0 < a0) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.err z ((3 : ℝ) ^ m) hR a z ((3 : ℝ) ^ (j + 2)) a0 s 2 =
      (paperHomogenizationError
        (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0).toReal ∧
    paperHomogenizationError
        (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≠ ⊤ := by
  have hr' : (0 : ℝ) < (3 : ℝ) ^ (j + 2) := by positivity
  have hsub : (centeredCube z ((3 : ℝ) ^ (j + 2)) hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
    change Metric.ball z ((3 : ℝ) ^ (j + 2) / 2) ⊆ Metric.ball z ((3 : ℝ) ^ m / 2)
    refine Metric.ball_subset_ball ?_
    have : (3 : ℝ) ^ (j + 2) ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hjm
    linarith
  have e := E.err_eq z _ hR a z _ hr' hsub s hs 2 (by norm_num) a0 ha0
  have efin := E.err_finite z _ hR a z _ hr' hsub s hs 2 (by norm_num) a0 ha0
  simp only [if_neg (show (2 : ℝ≥0∞) ≠ ⊤ by simp)] at e efin
  set k : ℤ := (j : ℤ) + 2 with hkdef
  set A : TriadicCoeffFamily d := E.chart z ((3 : ℝ) ^ m) hR a z ((3 : ℝ) ^ (j + 2)) with hAdef
  have hfac : triadicDilationFactor k = (3 : ℝ) ^ (j + 2) := by
    rw [triadicDilationFactor, hkdef]
    rw [show ((j : ℤ) + 2) = ((j + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hQk : Homogenization.originCube d k = dilateCube k (Homogenization.originCube d 0) := by
    simp [dilateCube, Homogenization.originCube]
  have hcoef : ∀ (jj : ℤ) (R : Homogenization.TriadicCube d),
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) jj →
      (data.toTriadicCoeffFamily.coeffOn (dilateCube k R)).toCoeffField
        =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
        dilateCoeffField k (A.coeffOn R).toCoeffField := by
    intro jj R hRmem
    have hk0 : jj ≤ (Homogenization.originCube d 0).scale :=
      Homogenization.descendant_scale_le_of_mem_descendantsAtScale hRmem
    have hRsub : Homogenization.openCubeSet R ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
        (by simpa [Homogenization.originCube] using hk0) hRmem
    have hchart := E.chart_eq z _ hR a z _ hr' hsub R hRsub
    have hpull := eventuallyEq_comp_undilate_of_ae_eq k (Q := R)
      (f := (A.coeffOn R).toCoeffField)
      (g := fun x => Homogenization.scalarMatrix
        ((a.val : SpatialCoordinates d → ℝ) (fun i => z i + (3 : ℝ) ^ (j + 2) * x i)))
      hchart
    have hdsub : Homogenization.openCubeSet (dilateCube k R) ⊆
        Homogenization.openCubeSet (Homogenization.originCube d k) := by
      rw [hQk, openCubeSet_dilateCube, openCubeSet_dilateCube]
      exact Set.smul_set_mono hRsub
    have ha'R : ∀ᵐ y ∂Homogenization.volumeMeasureOn
        (Homogenization.openCubeSet (dilateCube k R)),
        a' y = (a.val : SpatialCoordinates d → ℝ) (fun i => z i + y i) :=
      ae_restrict_of_ae_restrict_of_subset hdsub ha'
    filter_upwards [hpull, ha'R] with y hy hya
    change SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (fun y => a' (y + 0)) y =
      (A.coeffOn R).toCoeffField (undilateVec k y)
    rw [hy]
    have hund : ∀ i, (3 : ℝ) ^ (j + 2) * (undilateVec k y) i = y i := by
      intro i
      simp only [undilateVec, Pi.smul_apply, smul_eq_mul, hfac]
      field_simp
    simp only [hund, add_zero]
    change Homogenization.scalarMatrix (a' y) = _
    rw [hya]
  have hdil := aux_prop_folded_iteration_paper_error_dilate k A data.toTriadicCoeffFamily
    (Homogenization.originCube d 0) 0 s hcoef
    Homogenization.Book.Ch02.MultiscaleExponent.infinity
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) a0
  rw [zero_add, ← hQk] at hdil
  have hP : paperHomogenizationError (Homogenization.originCube d k) k s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 =
    paperHomogenizationErrorFinite (Homogenization.originCube d 0) 0 s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity (2 : ℝ≥0∞).toReal A a0 := by
    rw [hdil]
    simp only [paperHomogenizationError, ENNReal.toReal_ofNat]
  refine ⟨?_, ?_⟩
  · rw [e, hP]
  · rw [hP]
    exact efin.ne

end PaperErrorDilation

section GoodScaleError

open SubdiffusiveProcess.CoarseGrainingVocab

/-- Per-scale input of the one-step for the folded coefficient: at a good scale `j+2` of the
(tightened) good events, the physical-scale paper error on `□_{j+2}` of any global representative
`a'` of the translated folded coefficient, against the ORIGINAL reference `It.ref L j z om`, is at
most `Cg·ε`.  Chain: `lem_repair_err_fold_localization` (folded ≤ `C_d`·unfolded),
`lem_repair_err_good_scale_transport` (`C_d`·unfolded ≤ `Cg·min(ε,…)`), and the unit-chart /
physical identification `aux_prop_folded_iteration_err_physical`. -/
theorem aux_prop_folded_iteration_good_scale_error (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cg : ℝ, 0 < Cg ∧
      ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
      64 * M.delta ^ 2 ≤ It.s0 →
      It.s0⁻¹ * M.delta ^ 2 ≤ It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) →
      It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) ≤ 1 →
      ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (om : BilateralField d) (I P : Finset (Fin d)), I.Nonempty →
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
      ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m →
        It.good (j + 2) z (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) It.s0 om →
      ∀ (a' : SpatialCoordinates d → ℝ),
        (∀ᵐ y ∂volume.restrict
            (Homogenization.openCubeSet (Homogenization.originCube d ((j : ℤ) + 2))),
          a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i)) →
      ∀ data : ScalarTriadicCoeffData (fun y => a' (y + 0)),
        paperHomogenizationError
            (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (It.ref L j z om) ≤
          ENNReal.ofReal (Cg * (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))) := by
  obtain ⟨Cg, hCg, hT⟩ := lem_repair_err_good_scale_transport d hd
  refine ⟨Cg, hCg, ?_⟩
  intro E M Sreg It alpha halpha hdel h64 heps1 heps2 L m z hR om I P hI foldedCoef hfold j hjL
    hjm hgood a' ha' data
  have hloc := lem_repair_err_fold_localization d hd E M Sreg It alpha halpha hdel h64 heps1
    heps2 L m z hR om I P hI foldedCoef hfold j hjL hjm hgood
  have htr := hT E M Sreg It alpha halpha hdel h64 heps1 heps2 L m j z hR om hjL hjm hgood
  have hs0 : It.s0 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [It.s0_eq]; constructor <;> norm_num
  obtain ⟨hEq, hfin⟩ := aux_prop_folded_iteration_err_physical E z m j hR hjm foldedCoef a' ha'
    data (It.ref L j z om) (It.ref_pos L j z om) It.s0 hs0
  rw [It.s0_eq] at hEq hfin
  rw [← ENNReal.ofReal_toReal hfin, ← hEq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmin : Cg * min (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
      (M.delta ^ 2 + (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) ^ 8 +
        It.score (j + 2) z It.s0 om) ≤ Cg * (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hCg.le
  rw [It.s0_eq] at hloc htr hmin
  exact hloc.trans (htr.trans hmin)

end GoodScaleError

section FoldedRepresentative

open SubdiffusiveProcess.CoarseGrainingVocab



theorem aux_prop_folded_iteration_folded_representative (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (L m : ℕ)
    (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m) (om : BilateralField d)
    (I P : Finset (Fin d))
    (foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR))
    (hfold : (foldedCoef.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
      fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) :
    ∃ a' : SpatialCoordinates d → ℝ, Continuous a' ∧ (∀ y, 0 < a' y) ∧
      (∀ᵐ y ∂volume.restrict
          (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))),
        a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i)) ∧
      Nonempty (ScalarTriadicCoeffData (fun y => a' (y + 0))) := by
  set W : Set (SpatialCoordinates d) :=
    (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) with hWdef
  set F : SpatialCoordinates d → ℝ := fun x =>
    Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
      (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) with hFdef
  have hFc : Continuous F := by
    refine Real.continuous_exp.comp (Continuous.sub ?_ continuous_const)
    exact continuous_finset_sum _ fun j _ => (om (j : ℤ)).continuous
  have hshift : Continuous (fun y : SpatialCoordinates d => fun i => z i + y i) :=
    continuous_pi fun i => continuous_const.add (continuous_apply i)
  set a' : SpatialCoordinates d → ℝ :=
    fun y => F (coordinateFold z I P (fun i => z i + y i)) with ha'def
  have ha'c : Continuous a' := hFc.comp ((coordinateFold_continuous z I P).comp hshift)
  have ha'pos : ∀ y, 0 < a' y := fun y => Real.exp_pos _
  refine ⟨a', ha'c, ha'pos, ?_, ?_⟩
  · have hWm : MeasurableSet W := (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
    -- the cutoff coefficient is the explicit exponential a.e. on the root
    have h2 := Sreg.cutoffOn_eq L om z ((3 : ℝ) ^ m) hR
    rw [ae_restrict_iff' hWm] at h2
    set N : Set (SpatialCoordinates d) :=
      {x | x ∈ W ∧ (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val x ≠ F x} with hNdef
    have hN : volume N = 0 := by
      rw [ae_iff] at h2
      refine measure_mono_null ?_ h2
      intro x hx
      simp only [Set.mem_setOf_eq]
      exact fun h => hx.2 (h hx.1)
    have hfoldN : volume (coordinateFold z I P ⁻¹' N) = 0 :=
      (aux_lem_repair_err_fold_carrier_bridge_fold_qmp z I P).preimage_null hN
    have hmaps : ∀ x ∈ W, coordinateFold z I P x ∈ W := by
      intro x hx
      change dist (coordinateFold z I P x) z < (3 : ℝ) ^ m / 2
      rw [coordinateFold_dist_center]
      exact hx
    have h4 : ∀ᵐ x ∂volume, x ∈ W →
        (foldedCoef.val : SpatialCoordinates d → ℝ) x = F (coordinateFold z I P x) := by
      have h1 := hfold
      rw [Filter.EventuallyEq, ae_restrict_iff' hWm] at h1
      have h3 : ∀ᵐ x ∂volume, x ∉ coordinateFold z I P ⁻¹' N :=
        measure_eq_zero_iff_ae_notMem.1 hfoldN
      filter_upwards [h1, h3] with x hx1 hx3 hxW
      rw [hx1 hxW]
      by_contra hne
      exact hx3 ⟨hmaps x hxW, hne⟩
    have h5 : ∀ᵐ (y : SpatialCoordinates d) ∂volume, (fun i => z i + y i) ∈ W →
        (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i) =
          F (coordinateFold z I P (fun i => z i + y i)) := by
      have hmp := (measurePreserving_add_left (volume : Measure (SpatialCoordinates d)) z)
      have := hmp.quasiMeasurePreserving.ae h4
      simpa [Pi.add_def] using this
    have hOm : MeasurableSet
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) :=
      Homogenization.measurableSet_openCubeSet _
    rw [ae_restrict_iff' hOm]
    filter_upwards [h5] with y hy hyQ
    have hyW : (fun i => z i + y i) ∈ W := by
      have hy0 : y ∈ (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (m : ℤ))
          (by positivity) : Set (SpatialCoordinates d)) := by
        rw [SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube]
        exact hyQ
      change dist y 0 < (3 : ℝ) ^ (m : ℤ) / 2 at hy0
      change dist (fun i => z i + y i) z < (3 : ℝ) ^ m / 2
      have hdist : dist (fun i => z i + y i) z = dist y 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        funext i
        simp
      rw [hdist]
      simpa [zpow_natCast] using hy0
    exact (hy hyW).symm
  · refine ⟨{ onCube := fun Q => ?_ }⟩
    exact Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
        (ha'c.comp (continuous_id.add continuous_const))
        (fun y => ha'pos (y + 0)) (Homogenization.Book.Ch02.cubeDomain Q))

end FoldedRepresentative

section WeakTransfer

open SubdiffusiveProcess.CoarseGrainingVocab



theorem aux_prop_folded_iteration_inner_eq {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hgrad : HilbertGradient Ω) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : ∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => g x i)
    (φ : Homogenization.H10Function (Ω : Set (SpatialCoordinates d))) :
    inner ℝ hgrad (sobolevGradient (sobolevDataOfH1 φ.toH1Function)) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        Homogenization.vecDot (g x) (φ.toH1Function.grad x) := by
  rw [PiLp.inner_apply]
  have hterm : ∀ i : Fin d,
      inner ℝ (hgrad i) ((sobolevGradient (sobolevDataOfH1 φ.toH1Function)) i) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), g x i * φ.toH1Function.grad x i := by
    intro i
    change inner ℝ (hgrad i) ((sobolevDataOfH1 φ.toH1Function).2 i) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg i, sobolevDataOfH1_snd_coeFn φ.toH1Function i] with x hx1 hx2
    rw [RCLike.inner_apply, conj_trivial, hx1, hx2]
    ring
  simp only [hterm]
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Homogenization.vecDot]
  · intro i _
    have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hgrad i)
      ((sobolevDataOfH1 φ.toH1Function).2 i)
    refine hint.congr ?_
    filter_upwards [hg i, sobolevDataOfH1_snd_coeFn φ.toH1Function i] with x hx1 hx2
    rw [RCLike.inner_apply, conj_trivial, hx1, hx2]
    ring

/-- A set-level version of GMC's `isDivFormWeakSolutionOn_untranslate`, stated for any set equal
to a translate (so that it applies to the MFD root `centeredCube z (3^m)`). -/
theorem aux_prop_folded_iteration_untranslate {d : ℕ} (V U : Set (Vec d)) (z : Vec d)
    (hV : V = Homogenization.translateSet z U) {a : Vec d → ℝ}
    (u : Homogenization.H1Function V) {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn a V u g) :
    ∃ u' : Homogenization.H1Function U,
      (∀ y, u'.toFun y = u.toFun (y + z)) ∧ (∀ y, u'.grad y = u.grad (y + z)) ∧
      IsDivFormWeakSolutionOn (fun x => a (x + z)) U u' (fun x => g (x + z)) := by
  subst hV
  exact ⟨Homogenization.H1Function.untranslate z u, fun y => by simp, fun y => by simp,
    Section6HarmonicApproximation.isDivFormWeakSolutionOn_untranslate z h⟩



theorem aux_prop_folded_iteration_weak_transfer {d : ℕ} (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m)
    (foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR))
    (a' : SpatialCoordinates d → ℝ)
    (ha' : ∀ᵐ y ∂volume.restrict
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))),
      a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i))
    (g : SpatialCoordinates d → Fin d → ℝ)
    (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR))
    (hg : ∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
        Set (SpatialCoordinates d))] fun x => g x i)
    (hweak : ∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
      sobolevCoefficientForm foldedCoef
          (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
          (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
        -inner ℝ hgrad
          (subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) :
    ∃ u' : Homogenization.H1Function
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))),
      (∀ y, u'.toFun y = (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)).1 (y + z)) ∧
      (∀ y i, u'.grad y i =
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)).2 i (y + z)) ∧
      IsDivFormWeakSolutionOn a' (cube d (m : ℤ)) u' (fun y => g (y + z)) := by
  obtain ⟨v, hv1, hv2⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hsd : sobolevDataOfH1 v = (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) := by
    refine Prod.ext ?_ ?_
    · refine Lp.ext ((sobolevDataOfH1_fst_coeFn v).trans ?_)
      exact Filter.EventuallyEq.of_eq (by rw [show v.toFun = _ from hv1])
    · funext i
      refine Lp.ext ((sobolevDataOfH1_snd_coeFn v i).trans ?_)
      exact Filter.EventuallyEq.of_eq (by rw [hv2])
  have hwv : IsDivFormWeakSolutionOn (foldedCoef.val : SpatialCoordinates d → ℝ)
      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) v g := by
    refine isDivFormWeakSolutionOn_of_weak_equation foldedCoef v g ?_ ?_
    · intro w i
      have h := integrable_weighted_coordinates foldedCoef.val
        (sobolevGradient (sobolevDataOfH1 v)) (sobolevGradient (sobolevDataOfH1 w)) i
      refine h.congr ?_
      filter_upwards [sobolevDataOfH1_snd_coeFn v i, sobolevDataOfH1_snd_coeFn w i]
        with x hx1 hx2
      change foldedCoef.val x * ((sobolevDataOfH1 v).2 i x * (sobolevDataOfH1 w).2 i x) = _
      rw [hx1, hx2]
    · intro φ
      have h := hweak ⟨sobolevDataOfH1 φ.toH1Function, sobolevDataOfH1_mem_killed φ⟩
      rw [hsd]
      rw [h]
      congr 1
      exact aux_prop_folded_iteration_inner_eq hgrad g hg φ
  have hVeq : (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) = Homogenization.translateSet z
      (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) := by
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem,
      ← SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d)
        (m : ℤ) (by positivity)]
    change dist x z < (3 : ℝ) ^ m / 2 ↔ dist (x - z) 0 < (3 : ℝ) ^ (m : ℤ) / 2
    rw [dist_eq_norm, dist_eq_norm, sub_zero, zpow_natCast]
  obtain ⟨u', hu'1, hu'2, hu'w⟩ :=
    aux_prop_folded_iteration_untranslate _ _ z hVeq v hwv
  refine ⟨u', fun y => by rw [hu'1, hv1], fun y i => by rw [hu'2, hv2], ?_⟩
  refine lane2_isDivFormWeakSolutionOn_congr_coefficient ?_ hu'w
  filter_upwards [ha'] with y hy
  rw [hy]
  congr 1
  funext i
  simp [add_comm]

end WeakTransfer

section EnergyLegs

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- A scalar divergence-form weak solution on an origin cube is a public forced solution for
the scalar triadic family of the same coefficient, with the source sign flipped. -/
theorem aux_prop_folded_iteration_forced_of_divForm {d : ℕ} {Q : Homogenization.TriadicCube d}
    {a : Vec d → ℝ} (data : ScalarTriadicCoeffData a)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn a (openCubeSet Q) u g) :
    Ch03.IsForcedEquation Q data.toTriadicCoeffFamily u (fun x => -g x) := by
  intro phi
  have hflux : ∀ x, matVecMul ((data.toTriadicCoeffFamily.coeffOn Q).toCoeffField x)
      (u.grad x) = a x • u.grad x := fun x => matVecMul_scalarMatrix _ _
  have hneg : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  simp only [Ch02.cubeDomain_coe]
  calc ∫ x in openCubeSet Q, vecDot (matVecMul
          ((data.toTriadicCoeffFamily.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume
      = ∫ x in openCubeSet Q, vecDot (a x • u.grad x) (phi.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Eventually.of_forall fun x => by
          exact congrArg (fun w => vecDot w (phi.toH1Function.grad x)) (hflux x))
    _ = -∫ x in openCubeSet Q, vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in openCubeSet Q, vecDot ((fun x => -g x) x) (phi.toH1Function.grad x) ∂volume := by
        rw [hneg, integral_neg]

/-- The Euclidean fractional carrier of a source gives the Besov regularity of its negative
(the forced-equation sign), as consumed by the coarse Caccioppoli estimate. -/
theorem aux_prop_folded_iteration_forceBesov_neg {d : ℕ} [NeZero d] {Q : Homogenization.TriadicCube d}
    {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp Q s FiniteLpExponent.two f) :
    Ch03.ForceBesovRegularity Q s.1 (fun x => -f x) := by
  let F0 : CubeEuclideanWspField Q s FiniteLpExponent.two :=
    { toField := f, euclideanMemLp := hf.1, euclideanMemWsp := hf.2 }
  let F := negCubeEuclideanWspField F0
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa [F, F0] using hsob.toForceBesovRegularity s.2.1 s.2.2.le

end EnergyLegs
section EnergyGeometry

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- Interior windows of the origin chart are origin cubes. -/
theorem aux_prop_folded_iteration_window_eq {d : ℕ} (m j : ℕ) (hj : j + 5 ≤ m) :
    truncatedCube d (m : ℤ) (j : ℤ) 0 = openCubeSet (originCube d (j : ℤ)) := by
  rw [Section6HolderInterior.truncatedCube_eq_translateSet_of_interior
    (Section6ExcessDecay.zero_mem_cube d ((m : ℤ) - 1)) (by omega), translateSet_zero]

theorem aux_prop_folded_iteration_originCube_subset {d : ℕ} {k l : ℤ} (hkl : k ≤ l) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d l) :=
  openCubeSet_originCube_subset_of_scale_le hkl

theorem aux_prop_folded_iteration_openCubeAtScale_zero {d : ℕ} (k : ℤ) :
    Ch03.openCubeAtScale (0 : Vec d) k = openCubeSet (originCube d k) := by
  have h := openCubeAtScale_cubeCenter (originCube d k)
  rw [cubeCenter_originCube] at h
  exact h

/-- The Caccioppoli core of `□_{k+2}` about the origin is `□_k`. -/
theorem aux_prop_folded_iteration_core_eq {d : ℕ} (k : ℤ) :
    Ch03.caccioppoliCoreSet (originCube d (k + 2)) (0 : Vec d) = openCubeSet (originCube d k) := by
  unfold Ch03.caccioppoliCoreSet
  have hs : (originCube d (k + 2)).scale - 2 = k := by
    change k + 2 - 2 = k
    ring
  rw [hs, aux_prop_folded_iteration_openCubeAtScale_zero]
  exact Set.inter_eq_right.mpr (aux_prop_folded_iteration_originCube_subset (by omega))

/-- The Caccioppoli patch of `□_{k+2}` about the origin lies in `□_{k+2}`. -/
theorem aux_prop_folded_iteration_patch {d : ℕ} (k : ℤ) :
    Ch03.openCubeAtScale (0 : Vec d) ((originCube d (k + 2)).scale - 1) ⊆
      openCubeSet (originCube d (k + 2)) := by
  have hs : (originCube d (k + 2)).scale - 1 = k + 1 := by
    change k + 2 - 1 = k + 1
    ring
  rw [hs, aux_prop_folded_iteration_openCubeAtScale_zero]
  exact aux_prop_folded_iteration_originCube_subset (by omega)

theorem aux_prop_folded_iteration_volumeAverage_nonneg {d : ℕ} (W : Set (Vec d))
    (f : Vec d → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ volumeAverage W f := by
  unfold volumeAverage
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun x => hf x)

/-- The localized scalar energy on the Caccioppoli core is the square of the normalized
weighted gradient on `□_k`. -/
theorem aux_prop_folded_iteration_core_energy {d : ℕ} (k : ℤ) {a : Vec d → ℝ}
    (ha : ∀ y, 0 ≤ a y) (data : ScalarTriadicCoeffData a)
    (u : H1Function (openCubeSet (originCube d (k + 2)))) :
    Ch03.localizedCoeffEnergyValue (Ch03.caccioppoliCoreSet (originCube d (k + 2)) 0)
        (data.toTriadicCoeffFamily.coeffOn (originCube d (k + 2))) u =
      vectorNormalizedL2On (openCubeSet (originCube d k))
        (fun y => Real.sqrt (a y) • u.grad y) ^ 2 := by
  rw [Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage _ a u.grad ha,
    Real.sq_sqrt (aux_prop_folded_iteration_volumeAverage_nonneg _ _
      fun x => mul_nonneg (ha x) (vecNormSq_nonneg _)),
    aux_prop_folded_iteration_core_eq]
  unfold Ch03.localizedCoeffEnergyValue Ch03.normalizedSetAverage
  congr 1
  funext x
  change vecDot (u.grad x) (matVecMul (symmPart (scalarMatrix (a x))) (u.grad x)) = _
  rw [Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix]
  simp [vecDot, vecNormSq, Finset.mul_sum, mul_left_comm]

/-- `normalizedL2SqOnSet` is the square of `normalizedL2On`. -/
theorem aux_prop_folded_iteration_l2sq_eq {d : ℕ} (V : Set (Vec d)) (f : Vec d → ℝ) :
    Ch03.normalizedL2SqOnSet V f = normalizedL2On V f ^ 2 := by
  unfold Ch03.normalizedL2SqOnSet Ch03.normalizedSetAverage normalizedL2On
  rw [Real.sq_sqrt (aux_prop_folded_iteration_volumeAverage_nonneg _ _ fun x => sq_nonneg _)]

end EnergyGeometry
section EnergySource

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

theorem aux_prop_folded_iteration_openCube_volume_ne_zero {d : ℕ}
    (Q : Homogenization.TriadicCube d) : volume (openCubeSet Q) ≠ 0 := by
  intro h0
  have h := volume_openCubeSet_toReal Q
  rw [h0, ENNReal.toReal_zero] at h
  exact (cubeVolume_pos Q).ne' h.symm

/-- The Caccioppoli source seminorm on an origin cube is controlled by the fractional
Gagliardo seminorm of the source on the same cube. -/
theorem aux_prop_folded_iteration_source_bound {d : ℕ} [NeZero d] (k : ℤ)
    (sOrder : FractionalOrder) (g : Vec d → Vec d)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder FiniteLpExponent.two g) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) sOrder.1
        (fun x => -g x) ≤
      caccioppoliExactDatumConstant d * (3 : ℝ) ^ (sOrder.1 * (k : ℝ)) *
        (sOrder.1 ^ (-(1 / 2 : ℝ)) *
          (fractionalSeminormOn (openCubeSet (originCube d k)) sOrder.1 g).toReal) := by
  have h0 := aux_prop_folded_iteration_openCube_volume_ne_zero (originCube d k)
  have htop : volume (openCubeSet (originCube d k)) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d k)).ne
  have hfin : fractionalSeminormOn (openCubeSet (originCube d k)) sOrder.1 g ≠ ⊤ := by
    rw [Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have h := Section6HarmonicApproximation.projectedForceSeminorm_le_window (originCube d k) 0
    (openCubeSet (originCube d k)) sOrder g g (by simpa using hg) (fun x => by simp)
    (by rw [translateSet_zero]) (by rwa [translateSet_zero]) (by rwa [translateSet_zero])
    h0 htop hfin
  rw [translateSet_zero, div_self (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩), Real.sqrt_one,
    one_mul] at h
  have hw : cubeBesovScaleWeight (-sOrder.1) (originCube d k) =
      (3 : ℝ) ^ (sOrder.1 * (k : ℝ)) := by
    unfold cubeBesovScaleWeight cubeScaleFactor
    rw [neg_neg, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), mul_comm]
    rfl
  rw [hw] at h
  exact h

end EnergySource
section CaccioppoliLeg

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- Real arithmetic of the Caccioppoli leg: square-root extraction with the two ellipticity
caps and the source bound. -/
theorem aux_prop_folded_iteration_cacc_arith {W X Y lam sig pref P0 B T Cb Bes : ℝ}
    (hW : 0 ≤ W) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hlam : 0 < lam) (hsig : 0 < sig)
    (hpref0 : 0 ≤ pref) (hpref : pref ≤ P0) (hlamU : lam ≤ B * sig)
    (hlamL : lam⁻¹ ≤ B * sig⁻¹) (hT : 0 ≤ T) (hBes0 : 0 ≤ Bes) (hBes : Bes ≤ Cb * Y)
    (hB : 0 ≤ B) (hCb : 0 ≤ Cb)
    (h : W ^ 2 ≤ pref * (lam * X ^ 2 + T * lam⁻¹ * Bes ^ 2)) :
    W ≤ Real.sqrt P0 * (Real.sqrt B + Real.sqrt (T * B) * Cb) *
      (Real.sqrt sig * X + (Real.sqrt sig)⁻¹ * Y) := by
  have hP0 : 0 ≤ P0 := hpref0.trans hpref
  have hsq : Real.sqrt sig ^ 2 = sig := Real.sq_sqrt hsig.le
  have hsqi : (Real.sqrt sig)⁻¹ ^ 2 = sig⁻¹ := by rw [inv_pow, hsq]
  have hs0 : 0 < Real.sqrt sig := Real.sqrt_pos.2 hsig
  have hinner1 : lam * X ^ 2 ≤ B * sig * X ^ 2 :=
    mul_le_mul_of_nonneg_right hlamU (sq_nonneg X)
  have hBes2 : Bes ^ 2 ≤ (Cb * Y) ^ 2 := pow_le_pow_left₀ hBes0 hBes 2
  have hinner2 : T * lam⁻¹ * Bes ^ 2 ≤ T * (B * sig⁻¹) * (Cb * Y) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlamL hT) hBes2 (sq_nonneg _)
      (mul_nonneg hT (mul_nonneg hB (inv_nonneg.2 hsig.le)))
  have hin0 : 0 ≤ lam * X ^ 2 + T * lam⁻¹ * Bes ^ 2 :=
    add_nonneg (mul_nonneg hlam.le (sq_nonneg X))
      (mul_nonneg (mul_nonneg hT (inv_nonneg.2 hlam.le)) (sq_nonneg _))
  have hstep : W ^ 2 ≤ P0 * (B * sig * X ^ 2 + T * (B * sig⁻¹) * (Cb * Y) ^ 2) :=
    h.trans (mul_le_mul hpref (add_le_add hinner1 hinner2) hin0 hP0)
  set a1 : ℝ := Real.sqrt B * (Real.sqrt sig * X) with ha1
  set b1 : ℝ := Real.sqrt (T * B) * Cb * ((Real.sqrt sig)⁻¹ * Y) with hb1
  have ha10 : 0 ≤ a1 := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hs0.le hX)
  have hb10 : 0 ≤ b1 := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCb)
    (mul_nonneg (inv_nonneg.2 hs0.le) hY)
  have ha1sq : a1 ^ 2 = B * sig * X ^ 2 := by
    rw [ha1, mul_pow, mul_pow, Real.sq_sqrt hB, hsq]
    ring
  have hb1sq : b1 ^ 2 = T * (B * sig⁻¹) * (Cb * Y) ^ 2 := by
    rw [hb1, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hT hB), hsqi]
    ring
  have hsum : a1 ^ 2 + b1 ^ 2 ≤ (a1 + b1) ^ 2 := by
    nlinarith only [mul_nonneg ha10 hb10]
  have hR : Real.sqrt P0 * (Real.sqrt B + Real.sqrt (T * B) * Cb) *
      (Real.sqrt sig * X + (Real.sqrt sig)⁻¹ * Y) ≥ Real.sqrt P0 * (a1 + b1) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have e : (Real.sqrt B + Real.sqrt (T * B) * Cb) *
        (Real.sqrt sig * X + (Real.sqrt sig)⁻¹ * Y) =
        a1 + b1 + (Real.sqrt B * ((Real.sqrt sig)⁻¹ * Y) +
          Real.sqrt (T * B) * Cb * (Real.sqrt sig * X)) := by
      rw [ha1, hb1]
      ring
    rw [e]
    have : 0 ≤ Real.sqrt B * ((Real.sqrt sig)⁻¹ * Y) +
        Real.sqrt (T * B) * Cb * (Real.sqrt sig * X) :=
      add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (inv_nonneg.2 hs0.le) hY))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCb) (mul_nonneg hs0.le hX))
    linarith
  have hWsq : W ^ 2 ≤ (Real.sqrt P0 * (a1 + b1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hP0]
    calc W ^ 2 ≤ P0 * (a1 ^ 2 + b1 ^ 2) := by rw [ha1sq, hb1sq]; exact hstep
      _ ≤ P0 * (a1 + b1) ^ 2 := mul_le_mul_of_nonneg_left hsum hP0
  have hR0 : 0 ≤ Real.sqrt P0 * (a1 + b1) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg ha10 hb10)
  exact ((pow_le_pow_iff_left₀ hW hR0 two_ne_zero).1 hWsq).trans hR

end CaccioppoliLeg
section CaccioppoliLegMain

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- Step (4), energy side at a good scale: the coarse-grained Caccioppoli inequality on
`□_{k+2}` (GMC's interior form at `(s,t)=(1/2,1/16)`, source order `2t = 1/8 < 1/2`) with the
ellipticity caps supplied by a bound `E₀` on the `(1/32, ∞, 2)` error against the scalar `σ`
(`localBoundaryEllipticityCaps_of_errorCap` at `s = 3/16`), read on the physical origin chart. -/
theorem aux_prop_folded_iteration_caccioppoli_leg (d : ℕ) [NeZero d] (E0 : ℝ) :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∀ (a : Vec d → ℝ), (∀ y, 0 ≤ a y) → ∀ (data : ScalarTriadicCoeffData a)
        (m k : ℕ), k + 2 + 5 ≤ m →
        ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d (m : ℤ)) u g →
        ∀ sOrder : FractionalOrder, sOrder.1 = 1 / 8 →
        Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d (m : ℤ)) sOrder
          FiniteLpExponent.two g →
        ∀ sigma : ℝ, 0 < sigma →
        Ch02.HomogenizationErrorOnCube (originCube d ((k : ℤ) + 2)) (1 / 32)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (scalarMatrix sigma) ≤ E0 →
        vectorNormalizedL2On (openCubeSet (originCube d (k : ℤ)))
            (fun y => Real.sqrt (a y) • u.grad y) ≤
          Cc * (Real.sqrt sigma *
              ((3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) *
                normalizedL2On (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0)
                  (fun x ↦ u.toFun x -
                    averageOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) u.toFun)) +
            (Real.sqrt sigma)⁻¹ *
              ((3 : ℝ) ^ ((1 / 8 : ℝ) * ((k + 2 : ℕ) : ℝ)) *
                (fractionalSeminormOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) (1 / 8)
                  g).toReal)) := by
  obtain ⟨C, hC, hcac⟩ := Section6HarmonicApproximation.exists_interior_caccioppoli_quarter_subConst d
  set B : ℝ := 2 * (d : ℝ) * (E0 ^ 2 + 1) with hBdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hB : 0 < B := mul_pos (mul_pos two_pos hd0) (by positivity)
  set P0 : ℝ := (4 * max 1 C) ^ 8 * 8 * (B ^ 2) ^ 3 with hP0def
  set T : ℝ := Real.rpow (1 / 16 : ℝ) (-11 : ℝ) with hTdef
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  set Cb : ℝ := caccioppoliExactDatumConstant d * (1 / 8 : ℝ) ^ (-(1 / 2 : ℝ)) with hCbdef
  have hCb : 0 ≤ Cb := mul_nonneg (caccioppoliExactDatumConstant_pos d).le
    (Real.rpow_nonneg (by norm_num) _)
  refine ⟨Real.sqrt P0 * (Real.sqrt B + Real.sqrt (T * B) * Cb) + 1, by positivity, ?_⟩
  intro a ha data m k hkm u g hweak sOrder hs hg sigma hsigma herr
  set F := data.toTriadicCoeffFamily with hFdef
  set Q : Homogenization.TriadicCube d := originCube d ((k : ℤ) + 2) with hQdef
  have hQsub : openCubeSet Q ⊆ openCubeSet (originCube d (m : ℤ)) :=
    aux_prop_folded_iteration_originCube_subset (by omega)
  set uQ : H1Function (openCubeSet Q) := u.restrict (isOpen_openCubeSet Q) hQsub with huQ
  have heqQ : IsDivFormWeakSolutionOn a (openCubeSet Q) uQ g :=
    Section6HarmonicApproximation.isDivFormWeakSolutionOn_restrict
      (isOpen_openCubeSet _) (isOpen_openCubeSet Q) hQsub hweak
  have hforced := aux_prop_folded_iteration_forced_of_divForm data heqQ
  have hgQ : Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder FiniteLpExponent.two g := by
    have h := Section6HarmonicApproximation.memCubeEuclideanFullWsp_translate_of_subset Q
      (originCube d (m : ℤ)) 0 sOrder FiniteLpExponent.two g
      (by rw [translateSet_zero]; exact hQsub) hg
    simpa using h
  have hgReg := aux_prop_folded_iteration_forceBesov_neg hgQ
  have hcaps := Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap Q F
    (s := 3 / 16) (E₀ := E0) (by norm_num) (by norm_num) hsigma
    (by rw [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num]; exact herr)
  obtain ⟨-, -, -, hlinv, hlam, htheta⟩ := hcaps
  rw [show (3 / 16 : ℝ) / 3 = 1 / 16 by norm_num] at hlinv hlam htheta
  have hpref := Section6HarmonicApproximation.caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := F) hC (s := 1 / 8) (by norm_num) (by norm_num) (Theta₀ := B ^ 2)
    (by rw [show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num]; exact htheta)
  rw [show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num] at hpref
  set c := averageOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) u.toFun with hcdef
  have hmain := hcac (Q := Q) (A := F) (s := 1 / 2) (t := 1 / 16) (x := 0)
    (g := fun x => -g x) uQ c hforced (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (aux_prop_folded_iteration_patch _)
    (by rw [show 2 * (1 / 16 : ℝ) = sOrder.1 by rw [hs]; norm_num]; exact hgReg)
  rw [aux_prop_folded_iteration_core_energy (k : ℤ) ha data uQ,
    aux_prop_folded_iteration_l2sq_eq] at hmain
  have hwin : truncatedCube d (m : ℤ) ((k + 2 : ℕ) : ℤ) 0 = openCubeSet Q := by
    rw [aux_prop_folded_iteration_window_eq m (k + 2) hkm]
    push_cast
    rfl
  -- the source seminorm
  have hsrc := aux_prop_folded_iteration_source_bound ((k : ℤ) + 2) sOrder g hgQ
  rw [hs] at hsrc
  set lam := Ch02.lambdaS Q (1 / 16) F with hlamdef
  have hlampos : 0 < lam := by
    rw [hlamdef, Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_pos Q F (by norm_num) (by norm_num)
  set X : ℝ := (3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) *
    normalizedL2On (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) (fun x ↦ u.toFun x - c) with hXdef
  set Y : ℝ := (3 : ℝ) ^ ((1 / 8 : ℝ) * ((k + 2 : ℕ) : ℝ)) *
    (fractionalSeminormOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) (1 / 8) g).toReal with hYdef
  have hX0 : 0 ≤ X := mul_nonneg (zpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hY0 : 0 ≤ Y := mul_nonneg (Real.rpow_nonneg (by norm_num) _) ENNReal.toReal_nonneg
  have hscale : Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
      normalizedL2On (openCubeSet Q) (fun y => uQ.toFun y - c) ^ 2 = X ^ 2 := by
    rw [hXdef, hwin, mul_pow]
    congr 1
    change (3 : ℝ) ^ (-2 * (((k : ℤ) + 2 : ℤ) : ℝ)) = _
    rw [← zpow_natCast, ← zpow_mul, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hBes : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * (1 / 16))
      (fun x => -g x) ≤ Cb * Y := by
    rw [show 2 * (1 / 16 : ℝ) = 1 / 8 by norm_num]
    refine hsrc.trans (le_of_eq ?_)
    rw [hYdef, hCbdef, hwin]
    push_cast
    ring
  have hBes0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * (1 / 16))
      (fun x => -g x) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (by rw [show 2 * (1 / 16 : ℝ) = sOrder.1 by rw [hs]; norm_num]; exact hgReg)
  have hTheta0 : 0 ≤ Ch02.ThetaRatio Q (1 / 2) (1 / 16) F := by
    unfold Ch02.ThetaRatio
    refine div_nonneg ?_ hlampos.le
    rw [Ch02.LambdaS]
    exact Ch02.LambdaSq_finite_nonneg Q F (by norm_num) (by norm_num)
  have hpref0 : 0 ≤ Ch03.caccioppoliWithRHSPrefactor C Q F (1 / 2) (1 / 16) := by
    unfold Ch03.caccioppoliWithRHSPrefactor
    have h1 : 0 ≤ Real.rpow (C / (1 - 1 / 2 - 1 / 16)) (2 + 4 * (1 / 2) / (1 - 1 / 2 - 1 / 16)) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ Real.rpow (1 / 2 : ℝ) (-(2 * (1 / 2) / (1 - 1 / 2 - 1 / 16))) :=
      Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 2) (1 / 16) F)
        ((1 - 1 / 16) / (1 - 1 / 2 - 1 / 16)) := Real.rpow_nonneg hTheta0 _
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hmain' : vectorNormalizedL2On (openCubeSet (originCube d (k : ℤ)))
      (fun y => Real.sqrt (a y) • u.grad y) ^ 2 ≤
      Ch03.caccioppoliWithRHSPrefactor C Q F (1 / 2) (1 / 16) *
        (lam * X ^ 2 + T * lam⁻¹ *
          Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * (1 / 16))
            (fun x => -g x) ^ 2) := by
    have hlaminv : Real.rpow lam (-1) = lam⁻¹ := Real.rpow_neg_one lam
    rw [hlaminv, ← hTdef] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [← hscale]
    ring
  have hW0 : 0 ≤ vectorNormalizedL2On (openCubeSet (originCube d (k : ℤ)))
      (fun y => Real.sqrt (a y) • u.grad y) := Real.sqrt_nonneg _
  have hfin := aux_prop_folded_iteration_cacc_arith hW0 hX0 hY0 hlampos hsigma hpref0 hpref
    hlam (by simpa [Real.rpow_neg_one] using hlinv) hT hBes0 hBes hB.le hCb hmain'
  refine hfin.trans ?_
  have hR0 : 0 ≤ Real.sqrt sigma * X + (Real.sqrt sigma)⁻¹ * Y :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hX0)
      (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hY0)
  have := mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
      Real.sqrt P0 * (Real.sqrt B + Real.sqrt (T * B) * Cb) ≤
        Real.sqrt P0 * (Real.sqrt B + Real.sqrt (T * B) * Cb) + 1) hR0
  exact this

end CaccioppoliLegMain
section PoincareLeg

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- Step (4), oscillation side at the top good scale: fractional Poincaré followed by GMC's
proved coarse-grained Poincaré inequality (`λ_{1/2,2}`) on `□_{k+2}`, with the lower
ellipticity cap supplied by a bound `E₀` on the `(1/32, ∞, 2)` error against `σ`. -/
theorem aux_prop_folded_iteration_poincare_leg (d : ℕ) [NeZero d] (hd : 2 ≤ d) (E0 : ℝ) :
    ∃ CP : ℝ, 0 < CP ∧
      ∀ (a : Vec d → ℝ), (∀ y, 0 ≤ a y) → ∀ (data : ScalarTriadicCoeffData a)
        (m k : ℕ), k + 2 + 5 ≤ m →
        ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)))),
        ∀ sigma : ℝ, 0 < sigma →
        Ch02.HomogenizationErrorOnCube (originCube d ((k : ℤ) + 2)) (1 / 32)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (scalarMatrix sigma) ≤ E0 →
        (3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) *
            normalizedL2On (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0)
              (fun x ↦ u.toFun x - averageOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) u.toFun) ≤
          CP * (Real.sqrt sigma)⁻¹ *
            vectorNormalizedL2On (openCubeSet (originCube d ((k : ℤ) + 2)))
              (fun y => Real.sqrt (a y) • u.grad y) := by
  set B : ℝ := 2 * (d : ℝ) * (E0 ^ 2 + 1) with hBdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hB : 0 < B := mul_pos (mul_pos two_pos hd0) (by positivity)
  set Cfp := Section6HolderInterior.interiorFractionalPoincareConst d with hCfp
  have hCfp0 : 0 ≤ Cfp := Section6HolderInterior.interiorFractionalPoincareConst_nonneg d
  set pr := Section6HolderBoundary.coarsePoincareNormalizationPrice with hpr
  have hpr0 : 0 < pr := Section6HolderBoundary.coarsePoincareNormalizationPrice_pos
  set gf := paperPoincareGeometricFactor (1 / 2 : ℝ) (Ch02.MultiscaleExponent.finite 2) with hgf
  have hgf0 : 0 ≤ gf := by
    rw [hgf]
    unfold paperPoincareGeometricFactor
    exact Real.rpow_nonneg (Ch02.book_geometricDiscount_pos (by norm_num)).le _
  refine ⟨Cfp * (pr * gf) * Real.sqrt B + 1, by positivity, ?_⟩
  intro a ha data m k hkm u sigma hsigma herr
  set F := data.toTriadicCoeffFamily with hFdef
  set Q : Homogenization.TriadicCube d := originCube d ((k : ℤ) + 2) with hQdef
  have hQsub : openCubeSet Q ⊆ openCubeSet (originCube d (m : ℤ)) :=
    aux_prop_folded_iteration_originCube_subset (by omega)
  set uQ : H1Function (openCubeSet Q) := u.restrict (isOpen_openCubeSet Q) hQsub with huQ
  have hsym : ∀ R : Homogenization.TriadicCube d, (F.coeffOn R).IsSymmetric :=
    fun R => (data.onCube R).isSymmetric
  have hfp := Section6HolderInterior.normalizedL2On_fluctuation_le_scaleNormalized Q uQ
  have hcp := Section6HolderBoundary.scaleNormalizedNegativeBesov_le_coarsePoincareEnergy hd F
    hsym ((k : ℤ) + 2) uQ
  have hen : coefficientEnergyNorm Q F uQ.grad =
      vectorNormalizedL2On (openCubeSet Q) (fun y => Real.sqrt (a y) • u.grad y) :=
    Section6HolderInterior.sqrt_integral_scalarEnergy_eq_vectorNormalizedL2On Q a ha uQ.grad
  have hcaps := Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap Q F
    (s := 3 / 16) (E₀ := E0) (by norm_num) (by norm_num) hsigma
    (by rw [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num]; exact herr)
  obtain ⟨-, hlow, -⟩ := hcaps
  rw [show (3 / 16 : ℝ) / 6 = 1 / 32 by norm_num] at hlow
  have hmono : Ch02.lambdaSq Q (1 / 32) (Ch02.MultiscaleExponent.finite 2) F ≤
      Ch02.lambdaSq Q (1 / 2) (Ch02.MultiscaleExponent.finite 2) F :=
    Ch02.lambdaSq_finite_mono Q F (by norm_num) (by norm_num) (by norm_num)
  have hlpos : 0 < Ch02.lambdaSq Q (1 / 32) (Ch02.MultiscaleExponent.finite 2) F :=
    Ch02.lambdaSq_finite_pos Q F (by norm_num) (by norm_num)
  have hcap : sigma * (Ch02.lambdaSq Q (1 / 2) (Ch02.MultiscaleExponent.finite 2) F)⁻¹ ≤ B :=
    (mul_le_mul_of_nonneg_left (inv_anti₀ hlpos hmono) hsigma.le).trans hlow
  have hl0 : 0 ≤ Ch02.lambdaSq Q (1 / 2) (Ch02.MultiscaleExponent.finite 2) F :=
    (hlpos.trans_le hmono).le
  have hrp := Section6HarmonicApproximation.rpow_neg_half_le_of_lower_ratio_cap hl0 hsigma
    hB.le hcap
  have hrp' : Real.rpow (lambda Q (1 / 2) (Ch02.MultiscaleExponent.finite 2) F) (-1 / 2) ≤
      Real.sqrt B * (Real.sqrt sigma)⁻¹ := by
    rw [← Real.sqrt_inv]
    convert hrp using 2
    norm_num
  have hwin : truncatedCube d (m : ℤ) ((k + 2 : ℕ) : ℤ) 0 = openCubeSet Q := by
    rw [aux_prop_folded_iteration_window_eq m (k + 2) hkm]
    push_cast
    rfl
  have hw1 : cubeBesovScaleWeight (1 : ℝ) Q = (3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) := by
    unfold cubeBesovScaleWeight cubeScaleFactor
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
    congr 1
    change ((((k : ℤ) + 2 : ℤ)) : ℝ) * (-1) = _
    push_cast
    ring
  rw [hw1] at hfp
  have hW0 : 0 ≤ vectorNormalizedL2On (openCubeSet Q) (fun y => Real.sqrt (a y) • u.grad y) :=
    Real.sqrt_nonneg _
  have hs0 : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hsigma
  rw [hwin]
  change (3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) *
      normalizedL2On (openCubeSet Q) (fun y => uQ.toFun y -
        volumeAverage (openCubeSet Q) uQ.toFun) ≤ _
  refine hfp.trans ?_
  rw [hen] at hcp
  have hstep : Cfp * Ch03.scaleNormalizedNegativeBesovVectorNorm Q (1 / 2)
      (Ch02.MultiscaleExponent.finite 2) uQ.grad ≤
      Cfp * (pr * (gf * (Real.sqrt B * (Real.sqrt sigma)⁻¹) *
        vectorNormalizedL2On (openCubeSet Q) (fun y => Real.sqrt (a y) • u.grad y))) := by
    refine mul_le_mul_of_nonneg_left (hcp.trans ?_) hCfp0
    refine mul_le_mul_of_nonneg_left ?_ hpr0.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrp' hgf0) hW0
  refine hstep.trans ?_
  set W := vectorNormalizedL2On (openCubeSet Q) (fun y => Real.sqrt (a y) • u.grad y) with hWdef
  have hX0 : 0 ≤ (Real.sqrt sigma)⁻¹ * W := mul_nonneg (inv_nonneg.2 hs0.le) hW0
  have hmono := mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
      Cfp * (pr * gf) * Real.sqrt B ≤ Cfp * (pr * gf) * Real.sqrt B + 1) hX0
  calc Cfp * (pr * (gf * (Real.sqrt B * (Real.sqrt sigma)⁻¹) * W))
      = Cfp * (pr * gf) * Real.sqrt B * ((Real.sqrt sigma)⁻¹ * W) := by ring
    _ ≤ (Cfp * (pr * gf) * Real.sqrt B + 1) * ((Real.sqrt sigma)⁻¹ * W) := hmono
    _ = _ := by ring

end PoincareLeg
section EnergyBridge

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

/-- The paper's `(1/32, ∞, 2)` error bound on `□_{k+2}` bounds the Chapter-2 error that feeds
the ellipticity caps. -/
theorem aux_prop_folded_iteration_error_cap {d : ℕ} [NeZero d] {a : Vec d → ℝ}
    (data : ScalarTriadicCoeffData a) (k : ℤ) (sigma E : ℝ) (hsigma : 0 < sigma) (hE : 0 ≤ E)
    (h : paperHomogenizationError (originCube d (k + 2)) (k + 2) (1 / 32)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily sigma ≤ ENNReal.ofReal E) :
    Ch02.HomogenizationErrorOnCube (originCube d (k + 2)) (1 / 32)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily (scalarMatrix sigma) ≤ E := by
  have hb := Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    (originCube d (k + 2)) data.toTriadicCoeffFamily (fun R => (data.onCube R).isSymmetric)
    (s := 1 / 32) (by norm_num) hsigma
  exact (ENNReal.ofReal_le_ofReal_iff hE).1 (hb.trans h)



theorem aux_prop_folded_iteration_energy_bridge {d : ℕ} (m n : ℕ) (hnm : n ≤ m)
    (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
    (foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR))
    (a' : SpatialCoordinates d → ℝ) (ha'0 : ∀ y, 0 ≤ a' y)
    (ha' : ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d (m : ℤ))),
      a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i))
    (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
    (u' : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hu'2 : ∀ y i, u'.grad y i = u.2 i (y + z)) (hRn : (0 : ℝ) < 3 ^ n) :
    normalizedEnergyNorm foldedCoef (centeredCube z ((3 : ℝ) ^ n) hRn).isOpen.measurableSet
        (sobolevGradient u) =
      vectorNormalizedL2On (openCubeSet (originCube d (n : ℤ)))
        (fun y => Real.sqrt (a' y) • u'.grad y) := by
  set s : Set (SpatialCoordinates d) :=
    (centeredCube z ((3 : ℝ) ^ n) hRn : Set (SpatialCoordinates d)) with hsdef
  set V : Set (Vec d) := openCubeSet (originCube d (n : ℤ)) with hVdef
  have hsV : s = translateSet z V := by
    rw [hsdef, centeredCube_eq_translateSet_cube n z hRn]
    rfl
  have hsΩ : s ⊆ (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
    change Metric.ball z ((3 : ℝ) ^ n / 2) ⊆ Metric.ball z ((3 : ℝ) ^ m / 2)
    refine Metric.ball_subset_ball ?_
    have : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hnm
    linarith
  have hsmeas : MeasurableSet s := (centeredCube z ((3 : ℝ) ^ n) hRn).isOpen.measurableSet
  have hVsub : V ⊆ openCubeSet (originCube d (m : ℤ)) :=
    aux_prop_folded_iteration_originCube_subset (by exact_mod_cast hnm)
  -- the MFD energy as one set integral
  set G : SpatialCoordinates d → ℝ := fun x =>
    ∑ i : Fin d, (foldedCoef.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2 with hGdef
  have hint : ∀ i : Fin d, Integrable
      (fun x => (foldedCoef.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2)
      ((volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
        Set (SpatialCoordinates d))).restrict s) := by
    intro i
    have h := integrable_weighted_coordinates foldedCoef.val (sobolevGradient u)
      (sobolevGradient u) i
    refine (h.restrict (s := s)).congr (Eventually.of_forall fun x => ?_)
    change (foldedCoef.val : SpatialCoordinates d → ℝ) x * (u.2 i x * u.2 i x) = _
    ring
  have hloc : localGradientEnergy foldedCoef hsmeas (sobolevGradient u) = ∫ x in s, G x := by
    rw [localGradientEnergy_eq_integral]
    change ∑ i : Fin d, ∫ x in s, (foldedCoef.val : SpatialCoordinates d → ℝ) x * (u.2 i x) ^ 2
        ∂volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) = _
    rw [← integral_finset_sum _ (fun i _ => hint i)]
    rw [Measure.restrict_restrict hsmeas, Set.inter_eq_left.mpr hsΩ]
  have htr : ∫ x in s, G x = ∫ y in V, G (y + z) := by
    rw [hsV, setIntegral_comp_addRight_translateSet]
  have hcongr : ∫ y in V, G (y + z) = ∫ y in V, a' y * vecNormSq (u'.grad y) := by
    refine setIntegral_congr_ae (measurableSet_openCubeSet _) ?_
    have ha'V : ∀ᵐ y ∂volume.restrict V,
        a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i) :=
      ae_restrict_of_ae_restrict_of_subset hVsub ha'
    rw [ae_restrict_iff' (measurableSet_openCubeSet _)] at ha'V
    filter_upwards [ha'V] with y hy hyV
    rw [hy hyV, hGdef]
    have hzy : (fun i => z i + y i) = y + z := by
      funext i
      simp [add_comm]
    rw [hzy]
    simp only [vecNormSq, vecDot, hu'2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hvolV : (volume V).toReal = volume.real s := by
    rw [hVdef, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale, hsdef,
      centeredCube_volume_real]
    change ((3 : ℝ) ^ (n : ℤ)) ^ d = _
    rw [zpow_natCast]
  rw [Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage _ a' _ ha'0]
  unfold normalizedEnergyNorm volumeAverage
  rw [hloc, htr, hcongr, hvolV, div_eq_inv_mul]

end EnergyBridge
section GoodScaleErrorMin

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The per-scale folded error bound in `min` form for a fixed constant `Cg`, packaged as a
proposition. -/
def aux_prop_folded_iteration_gse_prop (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cg : ℝ) : Prop :=
      ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
      64 * M.delta ^ 2 ≤ It.s0 →
      It.s0⁻¹ * M.delta ^ 2 ≤ It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) →
      It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) ≤ 1 →
      ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (om : BilateralField d) (I P : Finset (Fin d)), I.Nonempty →
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
      ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m →
        It.good (j + 2) z (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) It.s0 om →
      ∀ (a' : SpatialCoordinates d → ℝ),
        (∀ᵐ y ∂volume.restrict
            (Homogenization.openCubeSet (Homogenization.originCube d ((j : ℤ) + 2))),
          a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i)) →
      ∀ data : ScalarTriadicCoeffData (fun y => a' (y + 0)),
        paperHomogenizationError
            (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (It.ref L j z om) ≤
          ENNReal.ofReal (Cg * min (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
            (M.delta ^ 2 + (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) ^ 8 +
              It.score (j + 2) z It.s0 om))

/-- `aux_prop_folded_iteration_good_scale_error` with the full `min` form of
`lem_repair_err_good_scale_transport` retained (its second slot feeds the error sum). -/
theorem aux_prop_folded_iteration_good_scale_error_min (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cg : ℝ, 0 < Cg ∧ aux_prop_folded_iteration_gse_prop d Cg := by
  obtain ⟨Cg, hCg, hT⟩ := lem_repair_err_good_scale_transport d hd
  refine ⟨Cg, hCg, ?_⟩
  intro E M Sreg It alpha halpha hdel h64 heps1 heps2 L m z hR om I P hI foldedCoef hfold j hjL
    hjm hgood a' ha' data
  have hloc := lem_repair_err_fold_localization d hd E M Sreg It alpha halpha hdel h64 heps1
    heps2 L m z hR om I P hI foldedCoef hfold j hjL hjm hgood
  have htr := hT E M Sreg It alpha halpha hdel h64 heps1 heps2 L m j z hR om hjL hjm hgood
  have hs0 : It.s0 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [It.s0_eq]; constructor <;> norm_num
  obtain ⟨hEq, hfin⟩ := aux_prop_folded_iteration_err_physical E z m j hR hjm foldedCoef a' ha'
    data (It.ref L j z om) (It.ref_pos L j z om) It.s0 hs0
  rw [show (1 / 32 : ℝ) = It.s0 from It.s0_eq.symm]
  rw [← ENNReal.ofReal_toReal hfin, ← hEq]
  exact ENNReal.ofReal_le_ofReal (hloc.trans htr)

end GoodScaleErrorMin
section CarrierConstants

/-- The dimensional constants `It.C`, `It.C1`, `It.C2` of `mfd:in-iteration` are closed
`d`-only terms (`C_eq`, `C1_eq`, `C2_eq` and `in_6_16.C_eq_dimensional`), so they can be named
before any model, carrier or datum. -/
theorem aux_prop_folded_iteration_carrier_constants (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ cC c1 c2 : ℝ, 1 ≤ cC ∧ 2 ≤ c1 ∧ c1 ≤ c2 ∧
      ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
        (It : in_iteration d M E Sreg), It.C = cC ∧ It.C1 = c1 ∧ It.C2 = c2 := by
  haveI inst : NeZero d := ⟨by omega⟩
  let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
      d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
  let c1 := Classical.choose H
  let c2 := Classical.choose (Classical.choose_spec H)
  let cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
  let c0 := max (max 46 c1) (max (1024 * c2 ^ 2) cmin)
  let hH := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  let h1 : (1 : ℝ) ≤ c1 := le_trans (by norm_num) hH.1
  let h2 : (1 : ℝ) ≤ c2 := le_trans h1 hH.2.1
  let Ct := Classical.choose
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_uncutGammaOneTail d 21 h1 h2)
  let Ce := Classical.choose
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d)
  let SC : ℝ := ((d : ℝ) + 1) ^ 2 *
    max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d))
  refine ⟨max SC (max c0 (max Ct Ce)), c1, c2, ?_, hH.1, hH.2.1,
    fun E M Sreg It => ⟨?_, It.C1_eq inst, It.C2_eq inst⟩⟩
  · have hSC : (1 : ℝ) ≤ SC := by
      have ha : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
        have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
        nlinarith
      exact one_le_mul_of_one_le_of_one_le ha (le_max_left _ _)
    exact hSC.trans (le_max_left _ _)
  · have h := It.C_eq inst
    have hS := Sreg.C_eq_dimensional
    simp only at h
    rw [h, hS]

end CarrierConstants
section Counting

/-- Reindexing a sum over an integer interval with natural endpoints. -/
theorem aux_prop_folded_iteration_sum_Icc_cast (F : ℤ → ℝ) (a b : ℕ) :
    ∑ j ∈ Finset.Icc (a : ℤ) (b : ℤ), F j = ∑ j ∈ Finset.Icc a b, F (j : ℤ) := by
  refine (Finset.sum_nbij' (fun j : ℕ => (j : ℤ)) (fun j : ℤ => j.toNat) ?_ ?_ ?_ ?_ ?_).symm
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _
    simp
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact Int.toNat_of_nonneg (by omega)
  · intro j _
    rfl

/-- Two good scales in the working range `[n, m-7]`, the nearest ones to both ends, whose
distances to `n` and to `m-7` are bounded by the number of bad scales in `[n,m]`. -/
theorem aux_prop_folded_iteration_good_pair (good : ℕ → Prop) (n m : ℕ) (hnm : n + 26 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 1 / 2)
    (hcount : ((@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
      (Finset.Icc n m)).card : ℝ) < 1 + lam * ((m : ℝ) - n)) :
    ∃ k k' : ℕ, n ≤ k ∧ k < k' ∧ k' + 7 ≤ m ∧ good (k + 2) ∧ good (k' + 2) ∧
      k - n ≤ (@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
        (Finset.Icc n m)).card ∧
      m - 7 - k' ≤ (@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
        (Finset.Icc n m)).card := by
  classical
  set NB := @Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _) (Finset.Icc n m)
    with hNB
  set Bd := (Finset.Icc n (m - 7)).filter (fun j => ¬ good (j + 2)) with hBd
  set G := (Finset.Icc n (m - 7)).filter (fun j => good (j + 2)) with hG
  have hBdNB : Bd.card ≤ NB.card := by
    have hsub : Bd.image (· + 2) ⊆ NB := by
      intro i hi
      simp only [Finset.mem_image, hBd, Finset.mem_filter, Finset.mem_Icc] at hi
      obtain ⟨j, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
      simp only [hNB, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, h3⟩
    calc Bd.card = (Bd.image (· + 2)).card :=
          (Finset.card_image_of_injective _ (add_left_injective 2)).symm
      _ ≤ NB.card := Finset.card_le_card hsub
  have hsplit : G.card + Bd.card = m - 7 + 1 - n := by
    rw [hG, hBd, Finset.card_filter_add_card_filter_not, Nat.card_Icc]
  have hmn : (n : ℝ) + 26 ≤ m := by exact_mod_cast hnm
  have hNBreal : (NB.card : ℝ) * 2 < 2 + ((m : ℝ) - n) := by
    have hl : lam * ((m : ℝ) - n) ≤ ((m : ℝ) - n) / 2 :=
      mul_le_mul_of_nonneg_right hlam (by linarith) |>.trans_eq (by ring)
    linarith
  have hNBnat : NB.card * 2 < 2 + (m - n) := by
    have : ((NB.card * 2 : ℕ) : ℝ) < ((2 + (m - n) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : n ≤ m)]
      linarith
    exact_mod_cast this
  have hGcard : 1 < G.card := by omega
  have hGne : G.Nonempty := Finset.card_pos.1 (by omega)
  set k0 := G.min' hGne with hk0
  set k1 := G.max' hGne with hk1
  have hkmem : k0 ∈ Finset.Icc n (m - 7) ∧ good (k0 + 2) :=
    Finset.mem_filter.mp (Finset.min'_mem G hGne)
  have hk'mem : k1 ∈ Finset.Icc n (m - 7) ∧ good (k1 + 2) :=
    Finset.mem_filter.mp (Finset.max'_mem G hGne)
  rw [Finset.mem_Icc] at hkmem hk'mem
  have hlt : k0 < k1 := Finset.min'_lt_max'_of_card G hGcard
  refine ⟨k0, k1, hkmem.1.1, hlt, by omega, hkmem.2, hk'mem.2, ?_, ?_⟩
  · have hsub : Finset.Ico n k0 ⊆ Bd := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [hBd, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hj.1, by omega⟩, fun hgj => ?_⟩
      have hjG : j ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, by omega⟩, hgj⟩
      exact absurd (Finset.min'_le G j hjG) (by omega)
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  · have hsub : Finset.Ioc k1 (m - 7) ⊆ Bd := by
      intro j hj
      simp only [Finset.mem_Ioc] at hj
      simp only [hBd, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hj.2⟩, fun hgj => ?_⟩
      have hjG : j ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hj.2⟩, hgj⟩
      exact absurd (Finset.le_max' G j hjG) (by omega)
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    omega

/-- The iteration's bad set on `[k+2, k'+2]`: the scales below the step `h` and the scales
whose working cube is not good; at most `h` plus the bad count on `[n, m]`. -/
theorem aux_prop_folded_iteration_bad_card (good : ℕ → Prop) (n m k k' h : ℕ) (hnk : n ≤ k)
    (hk'm : k' + 7 ≤ m) :
    (@Finset.filter ℕ (fun j => j < h ∨ ¬ good (j + 2)) (Classical.decPred _)
        (Finset.Icc (k + 2) (k' + 2))).card ≤
      h + (@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
        (Finset.Icc n m)).card := by
  classical
  have hor := @Finset.filter_or ℕ (fun j => j < h) (fun j => ¬ good (j + 2)) _ _ _
    (Finset.Icc (k + 2) (k' + 2))
  calc (@Finset.filter ℕ (fun j => j < h ∨ ¬ good (j + 2)) (Classical.decPred _)
          (Finset.Icc (k + 2) (k' + 2))).card
      = ((Finset.Icc (k + 2) (k' + 2)).filter (fun j => j < h) ∪
          (Finset.Icc (k + 2) (k' + 2)).filter (fun j => ¬ good (j + 2))).card := by
        rw [← hor]
        congr 1
        exact Finset.filter_congr_decidable _ _ _
    _ ≤ ((Finset.Icc (k + 2) (k' + 2)).filter (fun j => j < h)).card +
          ((Finset.Icc (k + 2) (k' + 2)).filter (fun j => ¬ good (j + 2))).card :=
        Finset.card_union_le _ _
    _ ≤ h + (@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
          (Finset.Icc n m)).card := by
        refine add_le_add ?_ ?_
        · calc ((Finset.Icc (k + 2) (k' + 2)).filter (fun j => j < h)).card
              ≤ (Finset.range h).card := Finset.card_le_card (fun j hj => by
                  simp only [Finset.mem_filter] at hj
                  exact Finset.mem_range.2 hj.2)
            _ = h := Finset.card_range h
        · have hsub : ((Finset.Icc (k + 2) (k' + 2)).filter
              (fun j => ¬ good (j + 2))).image (· + 2) ⊆
              @Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _) (Finset.Icc n m) := by
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hi
            obtain ⟨j, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
            simp only [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, by omega⟩, h3⟩
          calc ((Finset.Icc (k + 2) (k' + 2)).filter (fun j => ¬ good (j + 2))).card
              = (((Finset.Icc (k + 2) (k' + 2)).filter
                  (fun j => ¬ good (j + 2))).image (· + 2)).card :=
                (Finset.card_image_of_injective _ (add_left_injective 2)).symm
            _ ≤ _ := Finset.card_le_card hsub

attribute [local instance] Classical.propDecidable in
/-- The accumulated one-step error over the iteration range, from the per-scale bound at
non-bad scales. -/
theorem aux_prop_folded_iteration_eps_sum (lo hi n m : ℕ) (hlo : n ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi + 2 ≤ m)
    (bad : Finset ℤ) (e score : ℕ → ℝ) (cE Cg base : ℝ) (hcE : 0 ≤ cE) (hCg : 0 ≤ Cg)
    (hbase : 0 ≤ base) (hscore : ∀ i, 0 ≤ score i)
    (hgood : ∀ j : ℕ, lo ≤ j → j ≤ hi → (j : ℤ) ∉ bad → e j ≤ Cg * (base + score (j + 2))) :
    ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat) ≤
      cE * Cg * (base * ((m : ℝ) - n) + ∑ i ∈ Finset.Icc n m, score i) := by
  classical
  rw [aux_prop_folded_iteration_sum_Icc_cast]
  have hterm : ∀ j ∈ Finset.Icc lo hi,
      (if (j : ℤ) ∈ bad then 0 else cE * e ((j : ℤ).toNat)) ≤
        cE * Cg * base + cE * Cg * score (j + 2) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    split_ifs with hb
    · have : 0 ≤ cE * Cg * score (j + 2) := mul_nonneg (mul_nonneg hcE hCg) (hscore _)
      have : 0 ≤ cE * Cg * base := mul_nonneg (mul_nonneg hcE hCg) hbase
      linarith
    · rw [Int.toNat_natCast]
      have := mul_le_mul_of_nonneg_left (hgood j hj.1 hj.2 hb) hcE
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : ((hi + 1 - lo : ℕ) : ℝ) ≤ (m : ℝ) - n := by
    have h1 : hi + 1 - lo ≤ m - n := by omega
    have h2 : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub (by omega)
    rw [← h2]
    exact_mod_cast h1
  have hsc : ∑ j ∈ Finset.Icc lo hi, score (j + 2) ≤ ∑ i ∈ Finset.Icc n m, score i := by
    rw [← Finset.sum_image (f := score) (g := (· + 2)) (fun a _ b _ h => by simp only at h; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hscore i)
    intro i hi'
    simp only [Finset.mem_image, Finset.mem_Icc] at hi' ⊢
    obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hi'
    omega
  have hce : 0 ≤ cE * Cg := mul_nonneg hcE hCg
  have e1 : ((hi + 1 - lo : ℕ) : ℝ) * (cE * Cg * base) ≤ cE * Cg * (base * ((m : ℝ) - n)) := by
    have := mul_le_mul_of_nonneg_right hcard (mul_nonneg hce hbase)
    linarith
  have e2 := mul_le_mul_of_nonneg_left hsc hce
  linarith

end Counting
section Parameters

theorem aux_prop_folded_iteration_sqrt_log_ge_one {delta : ℝ} (hdel0 : 0 < delta)
    (hdel1 : delta ≤ 1 / 46) : 1 ≤ Real.sqrt |Real.log delta| := by
  have h1 : Real.log delta ≤ Real.log (1 / 46) := Real.log_le_log hdel0 hdel1
  have h2 : Real.log (1 / 46) < -1 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub, neg_lt_neg_iff,
      Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog : 1 ≤ |Real.log delta| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt hlog

theorem aux_prop_folded_iteration_eps_lower {delta K C c2 x : ℝ} (hdel0 : 0 < delta)
    (hdel1 : delta ≤ 1) (hKpos : 0 < K) (hc2 : 0 < c2) (hKc2 : 1024 * c2 ^ 2 * K ≤ C)
    (hx : C * delta / K ≤ x) : (1 / 32 : ℝ)⁻¹ * delta ^ 2 ≤ c2⁻¹ * Real.sqrt x := by
  have hd3 : delta ^ 3 ≤ 1 := pow_le_one₀ hdel0.le hdel1
  have h2 : 1024 * c2 ^ 2 * K * delta ^ 3 ≤ C :=
    (mul_le_of_le_one_right (by positivity) hd3).trans hKc2
  have h4 : (32 * delta ^ 2 * c2) ^ 2 ≤ x := by
    refine le_trans ?_ hx
    rw [le_div_iff₀ hKpos]
    calc (32 * delta ^ 2 * c2) ^ 2 * K = (1024 * c2 ^ 2 * K * delta ^ 3) * delta := by ring
      _ ≤ C * delta := mul_le_mul_of_nonneg_right h2 hdel0.le
  have hsqrt : 32 * delta ^ 2 * c2 ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le h4
  rw [show (1 / 32 : ℝ)⁻¹ = 32 by norm_num, le_inv_mul_iff₀ hc2]
  calc c2 * (32 * delta ^ 2) = 32 * delta ^ 2 * c2 := by ring
    _ ≤ Real.sqrt x := hsqrt

theorem aux_prop_folded_iteration_eps_le_eta {K c2 x eta : ℝ} (hK : 0 < K) (hc2 : 1 ≤ c2)
    (hx : x ≤ 1 / (2 * K)) (heta0 : 0 < eta) (hKeta : 1 / (2 * eta ^ 2) ≤ K) :
    c2⁻¹ * Real.sqrt x ≤ eta := by
  have hs1 : c2⁻¹ * Real.sqrt x ≤ Real.sqrt x :=
    mul_le_of_le_one_left (Real.sqrt_nonneg _) (inv_le_one_of_one_le₀ hc2)
  refine hs1.trans ?_
  rw [Real.sqrt_le_left heta0.le]
  refine hx.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have he2 : 0 < 2 * eta ^ 2 := by positivity
  have h1 : 1 = 1 / (2 * eta ^ 2) * (2 * eta ^ 2) := by field_simp
  calc (1 : ℝ) = 1 / (2 * eta ^ 2) * (2 * eta ^ 2) := h1
    _ ≤ K * (2 * eta ^ 2) := mul_le_mul_of_nonneg_right hKeta he2.le
    _ = eta ^ 2 * (2 * K) := by ring

theorem aux_prop_folded_iteration_eps8_le {c1 c2 x : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h18 : c1 * c2 ^ (-8 : ℝ) ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (c2⁻¹ * Real.sqrt x) ^ 8 ≤ c1⁻¹ * x := by
  rw [mul_pow, show Real.sqrt x ^ 8 = x ^ 4 by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt hx0]]
  have hc28 : c2⁻¹ ^ 8 ≤ c1⁻¹ := by
    have h := h18
    rw [Real.rpow_neg hc2.le, show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at h
    rw [inv_pow, inv_le_inv₀ (by positivity) hc1]
    have hp : 0 < c2 ^ 8 := by positivity
    rw [mul_inv_le_iff₀ hp] at h
    linarith
  have hx4 : x ^ 4 ≤ x := pow_le_of_le_one hx0 hx1 (by norm_num)
  exact mul_le_mul hc28 hx4 (by positivity) (by positivity)

/-- Parameter bookkeeping at the tightened exponent `αT = 1-(1-α)/K`: the carrier's admissible
range, the small-disorder side conditions of the good-scale error, the contraction tolerance
`ε' ≤ η`, and `δ² + ε'^8 ≤ 2λ'`. All constants are the closed carrier constants. -/
theorem aux_prop_folded_iteration_parameters {delta alpha K C cC c1 c2 eta : ℝ}
    (hdel0 : 0 < delta) (hdel : delta ≤ C⁻¹) (hK1 : 1 ≤ K) (hC46 : 46 ≤ C) (hcC1 : 1 ≤ cC)
    (hKcC : K * cC ≤ C) (hKc2 : 1024 * c2 ^ 2 * K ≤ C) (hKc1 : K * c1 ≤ C)
    (hc1 : 2 ≤ c1) (hc12 : c1 ≤ c2) (h18 : c1 * c2 ^ (-8 : ℝ) ≤ 1)
    (heta0 : 0 < eta) (hKeta : 1 / (2 * eta ^ 2) ≤ K)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) (1 - C * delta * Real.sqrt |Real.log delta|)) :
    let aT : ℝ := 1 - (1 - alpha) / K
    let eps : ℝ := c2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)
    let lam : ℝ := c1⁻¹ * (1 - aT)
    aT ∈ Set.Icc (1 / 2 : ℝ) (1 - cC * delta * Real.sqrt |Real.log delta|) ∧
      delta ≤ cC⁻¹ ∧ 64 * delta ^ 2 ≤ 1 / 32 ∧ (1 / 32 : ℝ)⁻¹ * delta ^ 2 ≤ eps ∧
      eps ≤ eta ∧ 0 ≤ eps ∧ 0 ≤ lam ∧ lam ≤ 1 / 2 ∧ delta ^ 2 + eps ^ 8 ≤ 2 * lam ∧
      lam = (1 - alpha) / (K * c1) := by
  intro aT eps lam
  obtain ⟨ha1, ha2⟩ := halpha
  have hCpos : 0 < C := by linarith
  have hKpos : 0 < K := by linarith
  have hc1pos : 0 < c1 := by linarith
  have hc2pos : 0 < c2 := by linarith
  have hdel1 : delta ≤ 1 / 46 :=
    hdel.trans ((inv_anti₀ (by norm_num) hC46).trans_eq (by norm_num))
  have hsq1 := aux_prop_folded_iteration_sqrt_log_ge_one hdel0 hdel1
  have hCd0 : 0 ≤ C * delta := by positivity
  have hCd : C * delta ≤ 1 - alpha := by
    have : C * delta ≤ C * delta * Real.sqrt |Real.log delta| :=
      le_mul_of_one_le_right hCd0 hsq1
    linarith
  have h1a : 0 ≤ 1 - alpha := hCd0.trans hCd
  have h1ah : 1 - alpha ≤ 1 / 2 := by linarith
  set x : ℝ := 1 - aT with hxdef
  have hx1 : x = (1 - alpha) / K := by simp only [x, aT]; ring
  have hx0 : 0 ≤ x := by rw [hx1]; exact div_nonneg h1a hKpos.le
  have hxhalf : x ≤ 1 / (2 * K) := by
    rw [hx1, div_le_div_iff₀ hKpos (by positivity)]
    have := mul_le_mul_of_nonneg_right h1ah hKpos.le
    linarith
  have hxlow : C * delta / K ≤ x := by
    rw [hx1]; exact div_le_div_of_nonneg_right hCd hKpos.le
  have hxle1 : x ≤ 1 := by
    refine hxhalf.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hepsdef : eps = c2⁻¹ * Real.sqrt x := by
    simp only [eps, x, Real.sqrt_eq_rpow]
  have hlam : lam = c1⁻¹ * x := rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (1 - alpha) / K ≤ 1 - alpha := div_le_self h1a hK1
    simp only [aT]; linarith
  · have hcK : cC * K ≤ C := by linarith
    have hpos : 0 ≤ delta * Real.sqrt |Real.log delta| := by positivity
    have hcC : cC * delta * Real.sqrt |Real.log delta| ≤ (1 - alpha) / K := by
      rw [le_div_iff₀ hKpos]
      calc cC * delta * Real.sqrt |Real.log delta| * K
          = (cC * K) * (delta * Real.sqrt |Real.log delta|) := by ring
        _ ≤ C * (delta * Real.sqrt |Real.log delta|) := mul_le_mul_of_nonneg_right hcK hpos
        _ = C * delta * Real.sqrt |Real.log delta| := by ring
        _ ≤ 1 - alpha := by linarith
    simp only [aT]; linarith
  · have hcC : cC ≤ C := le_trans (le_mul_of_one_le_left (by linarith) hK1) hKcC
    exact hdel.trans (inv_anti₀ (by linarith) hcC)
  · have : delta ^ 2 ≤ (1 / 46) ^ 2 := pow_le_pow_left₀ hdel0.le hdel1 2
    linarith
  · rw [hepsdef]
    exact aux_prop_folded_iteration_eps_lower hdel0 (by linarith) hKpos hc2pos hKc2 hxlow
  · rw [hepsdef]
    exact aux_prop_folded_iteration_eps_le_eta hKpos (by linarith) hxhalf heta0 hKeta
  · rw [hepsdef]; positivity
  · rw [hlam]; positivity
  · rw [hlam]
    have : c1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hxh : x ≤ 1 / 2 := by rw [hx1]; exact (div_le_self h1a hK1).trans h1ah
    calc c1⁻¹ * x ≤ 1 * x := mul_le_mul_of_nonneg_right this hx0
      _ ≤ 1 / 2 := by rw [one_mul]; exact hxh
  · have hd2 : delta ^ 2 ≤ c1⁻¹ * x := by
      have h1 : c1 * delta ≤ x := by
        refine le_trans ?_ hxlow
        rw [le_div_iff₀ hKpos]
        calc c1 * delta * K = (K * c1) * delta := by ring
          _ ≤ C * delta := mul_le_mul_of_nonneg_right hKc1 hdel0.le
      rw [le_inv_mul_iff₀ hc1pos]
      have hd : delta ^ 2 ≤ delta := by
        have := pow_le_one₀ hdel0.le (by linarith : delta ≤ 1) (n := 1)
        nlinarith
      calc c1 * delta ^ 2 ≤ c1 * delta := mul_le_mul_of_nonneg_left hd hc1pos.le
        _ ≤ x := h1
    have he8 : eps ^ 8 ≤ c1⁻¹ * x := by
      rw [hepsdef]; exact aux_prop_folded_iteration_eps8_le hc1pos hc2pos h18 hx0 hxle1
    rw [hlam]; linarith
  · rw [hlam, hx1]
    field_simp

end Parameters
section RealArithmetic

/-- The contraction step: `θ^h < 3/5` and `2·CH·3^{-h/2} ≤ θ^h` for `θ = 3^{-1/4}`. -/
theorem aux_prop_folded_iteration_step_choice (CH : ℝ) :
    ∃ h : ℕ, 0 < h ∧ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5 ∧
      2 * CH * (3 : ℝ) ^ (-(h : ℝ) / 2) ≤ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * CH) (by norm_num : (1 : ℝ) < 3)
  refine ⟨4 * N + 2, by omega, ?_, ?_⟩
  · have hθ : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (4 * N + 2) = (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hθ]
    have h1 : (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
    refine h1.trans_lt ?_
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_lt_comm₀ (by positivity)
      (by norm_num), Real.lt_sqrt (by norm_num)]
    norm_num
  · have hθ : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (4 * N + 2) = (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hθ]
    have hsplit : (3 : ℝ) ^ (-(((4 * N + 2 : ℕ) : ℝ)) / 2) =
        (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) * ((3 : ℝ) ^ (N : ℝ))⁻¹ * (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hsplit]
    have hA : 0 < (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) := by positivity
    have hB : 2 * CH * ((3 : ℝ) ^ (N : ℝ))⁻¹ ≤ 1 := by
      rw [Real.rpow_natCast]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact hN.le
    have hC : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hB0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    calc 2 * CH * ((3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) * ((3 : ℝ) ^ (N : ℝ))⁻¹ *
          (3 : ℝ) ^ (-(1 / 2 : ℝ)))
        = (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) * ((2 * CH * ((3 : ℝ) ^ (N : ℝ))⁻¹) *
          (3 : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ (3 : ℝ) ^ (-((N : ℝ) + 1 / 2)) * (1 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hA.le
          by_cases h0 : 0 ≤ 2 * CH * ((3 : ℝ) ^ (N : ℝ))⁻¹
          · exact mul_le_mul hB hC hB0 zero_le_one
          · push_neg at h0
            nlinarith
      _ = _ := by ring

/-- With `η = min 1 (θ^h / (2·CH·A))` the one-step contraction threshold holds. -/
theorem aux_prop_folded_iteration_eta_choice {CH A th r : ℝ} (hCH : 0 < CH) (hA : 0 < A)
    (hth : 0 < th) (hr : 2 * CH * r ≤ th) :
    let eta := min 1 (th / (2 * CH * A))
    0 < eta ∧ eta ≤ 1 ∧ CH * (r + A * eta) ≤ th := by
  intro eta
  have hq : 0 < th / (2 * CH * A) := by positivity
  refine ⟨lt_min one_pos hq, min_le_left _ _, ?_⟩
  have h1 : CH * A * eta ≤ th / 2 := by
    have : eta ≤ th / (2 * CH * A) := min_le_right _ _
    calc CH * A * eta ≤ CH * A * (th / (2 * CH * A)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = th / 2 := by field_simp
  have h2 : CH * r ≤ th / 2 := by linarith
  calc CH * (r + A * eta) = CH * r + CH * A * eta := by ring
    _ ≤ th / 2 + th / 2 := add_le_add h2 h1
    _ = th := by ring

/-- The normalized-energy volume factor `√((3^k)^d / (3^n)^d)` as an exponential. -/
theorem aux_prop_folded_iteration_vol_factor (d n k : ℕ) (B : ℝ)
    (hB : (k : ℝ) - n ≤ B) :
    Real.sqrt (((3 : ℝ) ^ k) ^ d / ((3 : ℝ) ^ n) ^ d) ≤
      Real.exp ((d : ℝ) / 2 * Real.log 3 * B) := by
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : ((3 : ℝ) ^ k) ^ d / ((3 : ℝ) ^ n) ^ d =
      Real.exp ((d : ℝ) * Real.log 3 * ((k : ℝ) - n)) := by
    rw [← pow_mul, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast (3 : ℝ) (n * d),
      ← Real.rpow_sub (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  rw [h1]
  have h2 : Real.exp ((d : ℝ) * Real.log 3 * ((k : ℝ) - n)) =
      Real.exp ((d : ℝ) / 2 * Real.log 3 * ((k : ℝ) - n)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h2, Real.sqrt_sq (Real.exp_pos _).le]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hB (by positivity))

end RealArithmetic


section ChainArithmetic

/-- The ratio bookkeeping of step (4): with `ρ⁻¹R ≤ σ_k ≤ ρR`, `ρ⁻¹R ≤ σ_{k'}`, the translated
chain collapses to one factor `Pk·Pt·e^A·ρ²` in front of the root energy plus the root source. -/
theorem aux_prop_folded_iteration_chain_arith {En Ek Wt Em T R sk skt eA ρ Pk Pt Cc CP S1 S2 : ℝ}
    (hR : 0 < R) (hρ : 1 ≤ ρ) (heA : 1 ≤ eA) (hPt : 1 ≤ Pt) (hPk : 0 ≤ Pk)
    (hCc : 0 ≤ Cc) (hCP : 0 ≤ CP) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hT : 0 ≤ T) (hEm : 0 ≤ Em)
    (hWt : 0 ≤ Wt)
    (hsk1 : ρ⁻¹ * R ≤ sk) (hsk2 : sk ≤ ρ * R) (hskt1 : ρ⁻¹ * R ≤ skt)
    (hEn : En ≤ Pk * Ek)
    (hEk : Ek ≤ Cc * (Real.sqrt sk * eA * (CP * (Real.sqrt skt)⁻¹ * Wt + S1 * (ρ * R⁻¹ * T)) +
        (Real.sqrt sk)⁻¹ * (S2 * T)))
    (hWt' : Wt ≤ Pt * Em) :
    En ≤ Pk * Pt * eA * ρ ^ 2 * (Cc * (CP + S1 + S2)) * (Em + (Real.sqrt R)⁻¹ * T) := by
  set r := Real.sqrt ρ with hr
  set a := Real.sqrt R with ha
  have hρ0 : 0 < ρ := by linarith
  have hr1 : 1 ≤ r := by
    rw [hr, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hρ
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := Real.sqrt_pos.2 hR
  have hrr : r * r = ρ := Real.mul_self_sqrt hρ0.le
  have haa : a * a = R := Real.mul_self_sqrt hR.le
  have hlow : ∀ x, ρ⁻¹ * R ≤ x → (Real.sqrt x)⁻¹ ≤ r * a⁻¹ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    have h1 : a * r⁻¹ ≤ Real.sqrt x := by
      rw [show a * r⁻¹ = Real.sqrt (ρ⁻¹ * R) by
        rw [Real.sqrt_mul (inv_nonneg.2 hρ0.le), Real.sqrt_inv]; ring]
      exact Real.sqrt_le_sqrt hx
    calc (Real.sqrt x)⁻¹ ≤ (a * r⁻¹)⁻¹ := inv_anti₀ (by positivity) h1
      _ = r * a⁻¹ := by rw [mul_inv, inv_inv]; ring
  have b1 : Real.sqrt sk ≤ r * a := by
    rw [hr, ha, ← Real.sqrt_mul hρ0.le]
    exact Real.sqrt_le_sqrt hsk2
  have b2 := hlow skt hskt1
  have b3 := hlow sk hsk1
  have hsk0 : 0 ≤ Real.sqrt sk := Real.sqrt_nonneg _
  have hskt0 : 0 ≤ (Real.sqrt skt)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hRinv : R⁻¹ = a⁻¹ * a⁻¹ := by rw [← haa, mul_inv]
  have hmid : Real.sqrt sk * eA * (CP * (Real.sqrt skt)⁻¹ * Wt + S1 * (ρ * R⁻¹ * T)) +
        (Real.sqrt sk)⁻¹ * (S2 * T) ≤
      (r * a) * eA * (CP * (r * a⁻¹) * (Pt * Em) + S1 * (ρ * R⁻¹ * T)) +
        (r * a⁻¹) * (S2 * T) := by
    have hin : CP * (Real.sqrt skt)⁻¹ * Wt + S1 * (ρ * R⁻¹ * T) ≤
        CP * (r * a⁻¹) * (Pt * Em) + S1 * (ρ * R⁻¹ * T) := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left b2 hCP) hWt' hWt
        (mul_nonneg hCP (by positivity))
      linarith
    have hin0 : 0 ≤ CP * (Real.sqrt skt)⁻¹ * Wt + S1 * (ρ * R⁻¹ * T) :=
      add_nonneg (mul_nonneg (mul_nonneg hCP hskt0) hWt)
        (mul_nonneg hS1 (mul_nonneg (mul_nonneg hρ0.le (inv_nonneg.2 hR.le)) hT))
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right b3 (mul_nonneg hS2 hT))
    refine mul_le_mul (mul_le_mul_of_nonneg_right b1 (by linarith)) hin hin0
      (mul_nonneg (by positivity) (by linarith))
  have heq : (r * a) * eA * (CP * (r * a⁻¹) * (Pt * Em) + S1 * (ρ * R⁻¹ * T)) +
        (r * a⁻¹) * (S2 * T) =
      eA * (r * r) * Pt * CP * Em + eA * (r * r * r) * S1 * (a⁻¹ * T) + r * S2 * (a⁻¹ * T) := by
    have ha1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    calc (r * a) * eA * (CP * (r * a⁻¹) * (Pt * Em) + S1 * (ρ * R⁻¹ * T)) +
          (r * a⁻¹) * (S2 * T)
        = eA * (r * r) * Pt * CP * Em * (a * a⁻¹) +
            eA * (r * r * r) * S1 * (a⁻¹ * T) * (a * a⁻¹) + r * S2 * (a⁻¹ * T) := by
          rw [hRinv, ← hrr]; ring
      _ = _ := by rw [ha1]; ring
  have hrle : r ≤ ρ := by
    have : r ≤ r * r := le_mul_of_one_le_left hr0.le hr1
    rwa [hrr] at this
  have h2 : ρ ≤ ρ ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hρ0.le hρ
  have hr2 : r * r ≤ ρ ^ 2 := by rw [hrr]; exact h2
  have hr3 : r * r * r ≤ ρ ^ 2 := by
    rw [hrr, sq]; exact mul_le_mul_of_nonneg_left hrle hρ0.le
  have hr1' : r ≤ ρ ^ 2 * eA * Pt := by
    have : r ≤ ρ := hrle
    have h3 : ρ ^ 2 ≤ ρ ^ 2 * eA * Pt := by
      have : 1 ≤ eA * Pt := one_le_mul_of_one_le_of_one_le heA hPt
      calc ρ ^ 2 = ρ ^ 2 * 1 := by ring
        _ ≤ ρ ^ 2 * (eA * Pt) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = ρ ^ 2 * eA * Pt := by ring
    linarith
  have hX0 : 0 ≤ a⁻¹ * T := mul_nonneg (inv_nonneg.2 ha0.le) hT
  have hfin : eA * (r * r) * Pt * CP * Em + eA * (r * r * r) * S1 * (a⁻¹ * T) +
        r * S2 * (a⁻¹ * T) ≤
      Pt * eA * ρ ^ 2 * ((CP + S1 + S2) * (Em + a⁻¹ * T)) := by
    have e1 : eA * (r * r) * Pt * CP * Em ≤ eA * ρ ^ 2 * Pt * CP * Em := by
      have hPCE : 0 ≤ Pt * CP * Em := mul_nonneg (mul_nonneg (by linarith) hCP) hEm
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr2 (by linarith : (0 : ℝ) ≤ eA)) hPCE
      calc eA * (r * r) * Pt * CP * Em = eA * (r * r) * (Pt * CP * Em) := by ring
        _ ≤ eA * ρ ^ 2 * (Pt * CP * Em) := this
        _ = eA * ρ ^ 2 * Pt * CP * Em := by ring
    have e2 : eA * (r * r * r) * S1 * (a⁻¹ * T) ≤ eA * ρ ^ 2 * Pt * S1 * (a⁻¹ * T) := by
      have h3 : eA * (r * r * r) ≤ eA * ρ ^ 2 * Pt := by
        have := mul_le_mul_of_nonneg_left hr3 (by linarith : (0 : ℝ) ≤ eA)
        have h4 : eA * ρ ^ 2 ≤ eA * ρ ^ 2 * Pt := le_mul_of_one_le_right (by positivity) hPt
        linarith
      have := mul_le_mul_of_nonneg_right h3 (mul_nonneg hS1 hX0)
      linarith
    have e3 : r * S2 * (a⁻¹ * T) ≤ eA * ρ ^ 2 * Pt * S2 * (a⁻¹ * T) := by
      have := mul_le_mul_of_nonneg_right hr1' (mul_nonneg hS2 hX0)
      linarith
    have e4 : eA * ρ ^ 2 * Pt * CP * Em + eA * ρ ^ 2 * Pt * S1 * (a⁻¹ * T) +
        eA * ρ ^ 2 * Pt * S2 * (a⁻¹ * T) ≤
        Pt * eA * ρ ^ 2 * ((CP + S1 + S2) * (Em + a⁻¹ * T)) := by
      have hP : 0 ≤ Pt * eA * ρ ^ 2 := by positivity
      have hrest : CP * Em + S1 * (a⁻¹ * T) + S2 * (a⁻¹ * T) ≤
          (CP + S1 + S2) * (Em + a⁻¹ * T) := by
        have hx : (CP + S1 + S2) * (Em + a⁻¹ * T) = CP * Em + S1 * (a⁻¹ * T) +
            S2 * (a⁻¹ * T) + (CP * (a⁻¹ * T) + S1 * Em + S2 * Em) := by ring
        have h1 := mul_nonneg hCP hX0
        have h2' := mul_nonneg hS1 hEm
        have h3' := mul_nonneg hS2 hEm
        rw [hx]
        linarith
      have := mul_le_mul_of_nonneg_left hrest hP
      linarith
    linarith
  calc En ≤ Pk * Ek := hEn
    _ ≤ Pk * (Cc * ((r * a) * eA * (CP * (r * a⁻¹) * (Pt * Em) + S1 * (ρ * R⁻¹ * T)) +
          (r * a⁻¹) * (S2 * T))) :=
        mul_le_mul_of_nonneg_left (hEk.trans (mul_le_mul_of_nonneg_left hmid hCc)) hPk
    _ ≤ Pk * (Cc * (Pt * eA * ρ ^ 2 * ((CP + S1 + S2) * (Em + a⁻¹ * T)))) := by
        rw [heq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin hCc) hPk
    _ = Pk * Pt * eA * ρ ^ 2 * (Cc * (CP + S1 + S2)) * (Em + a⁻¹ * T) := by ring

/-- Exponent absorption: the accumulated factors cost at most `exp(Γ·λ'(m-n))` times a
dimensional constant, and `K ≥ Γ` turns this into `3^{(1-α)(m-n)}`. -/
theorem aux_prop_folded_iteration_exponent {Pk Pt eA ρ Lam a0 a1 cC dd K c1 N w : ℝ}
    (hdd : 0 ≤ dd) (hc1 : 2 ≤ c1) (hK : dd * Real.log 3 + a1 + 2 * cC ≤ K) (hKpos : 0 < K)
    (hcC : 0 ≤ cC) (ha1 : 0 ≤ a1) (hw : 0 ≤ w) (hN : 0 ≤ N)
    (hLam : Lam = w * N / (K * c1)) (hLam0 : 0 ≤ Lam)
    (hPt0 : 0 ≤ Pt) (heA0 : 0 ≤ eA)
    (hPk : Pk ≤ Real.exp (dd / 2 * Real.log 3 * (1 + Lam)))
    (hPt : Pt ≤ Real.exp (dd / 2 * Real.log 3 * (6 + Lam)))
    (heA : eA ≤ Real.exp (a0 + a1 * Lam)) (hρ : ρ = cC * Real.exp (cC * Lam)) :
    Pk * Pt * eA * ρ ^ 2 ≤
      Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 * (3 : ℝ) ^ (w * N) := by
  have hL : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hρ2 : ρ ^ 2 = cC ^ 2 * Real.exp (2 * cC * Lam) := by
    rw [hρ, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hprod : Pk * Pt * eA ≤ Real.exp (dd / 2 * Real.log 3 * (1 + Lam)) *
      Real.exp (dd / 2 * Real.log 3 * (6 + Lam)) * Real.exp (a0 + a1 * Lam) :=
    mul_le_mul (mul_le_mul hPk hPt hPt0 (Real.exp_pos _).le) heA heA0 (by positivity)
  have hGam : (dd * Real.log 3 + a1 + 2 * cC) * Lam ≤ w * N * Real.log 3 := by
    have hG0 : 0 ≤ dd * Real.log 3 + a1 + 2 * cC := by positivity
    calc (dd * Real.log 3 + a1 + 2 * cC) * Lam ≤ K * Lam := mul_le_mul_of_nonneg_right hK hLam0
      _ = w * N / c1 := by rw [hLam]; field_simp
      _ ≤ w * N := div_le_self (mul_nonneg hw hN) (by linarith)
      _ ≤ w * N * Real.log 3 := le_mul_of_one_le_right (mul_nonneg hw hN) hL.le
  have h3 : (3 : ℝ) ^ (w * N) = Real.exp (w * N * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  calc Pk * Pt * eA * ρ ^ 2
      ≤ Real.exp (dd / 2 * Real.log 3 * (1 + Lam)) *
          Real.exp (dd / 2 * Real.log 3 * (6 + Lam)) * Real.exp (a0 + a1 * Lam) * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
    _ = Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 *
          Real.exp ((dd * Real.log 3 + a1 + 2 * cC) * Lam) := by
        rw [hρ2, ← Real.exp_add, ← Real.exp_add]
        rw [show Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 *
            Real.exp ((dd * Real.log 3 + a1 + 2 * cC) * Lam) =
            cC ^ 2 * (Real.exp (7 * dd / 2 * Real.log 3 + a0) *
              Real.exp ((dd * Real.log 3 + a1 + 2 * cC) * Lam)) by ring,
          ← Real.exp_add]
        rw [show Real.exp (dd / 2 * Real.log 3 * (1 + Lam) + dd / 2 * Real.log 3 * (6 + Lam) +
              (a0 + a1 * Lam)) * (cC ^ 2 * Real.exp (2 * cC * Lam)) =
            cC ^ 2 * (Real.exp (dd / 2 * Real.log 3 * (1 + Lam) +
              dd / 2 * Real.log 3 * (6 + Lam) + (a0 + a1 * Lam)) *
              Real.exp (2 * cC * Lam)) by ring, ← Real.exp_add]
        congr 2
        ring
    _ ≤ Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 * (3 : ℝ) ^ (w * N) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hGam) (by positivity)

end ChainArithmetic
section FinalArithmetic

/-- The final collapse: ratio bookkeeping, exponent absorption into `3^{(1-α)(m-n)}` via
`K ≥ Γ`, and the dimensional prefactor `C`. -/
theorem aux_prop_folded_iteration_final_arith
    {En Wk Wt Em T R sk skt eA ρ Pk Pt Cc CP S1 S2 Lam a0 a1 cC dd K c1 N w C : ℝ}
    (hR : 0 < R) (hcC : 1 ≤ cC) (heA : 1 ≤ eA) (hPt : 1 ≤ Pt) (hPk : 0 ≤ Pk)
    (hCc : 0 ≤ Cc) (hCP : 0 ≤ CP) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hT : 0 ≤ T) (hEm : 0 ≤ Em)
    (hWt : 0 ≤ Wt)
    (hsk1 : ρ⁻¹ * R ≤ sk) (hsk2 : sk ≤ ρ * R) (hskt1 : ρ⁻¹ * R ≤ skt)
    (hEn : En ≤ Pk * Wk)
    (hWk : Wk ≤ Cc * (Real.sqrt sk * eA * (CP * (Real.sqrt skt)⁻¹ * Wt + S1 * (ρ * R⁻¹ * T)) +
        (Real.sqrt sk)⁻¹ * (S2 * T)))
    (hWt' : Wt ≤ Pt * Em)
    (hdd : 0 ≤ dd) (hc1 : 2 ≤ c1) (hK : dd * Real.log 3 + a1 + 2 * cC ≤ K) (hKpos : 0 < K)
    (ha1 : 0 ≤ a1) (hw : 0 ≤ w) (hN : 0 ≤ N) (hLam : Lam = w * N / (K * c1))
    (hLam0 : 0 ≤ Lam)
    (hPkb : Pk ≤ Real.exp (dd / 2 * Real.log 3 * (1 + Lam)))
    (hPtb : Pt ≤ Real.exp (dd / 2 * Real.log 3 * (6 + Lam)))
    (heAb : eA ≤ Real.exp (a0 + a1 * Lam)) (hρ : ρ = cC * Real.exp (cC * Lam))
    (hC : Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 * (Cc * (CP + S1 + S2)) ≤ C) :
    En ≤ C * (3 : ℝ) ^ (w * N) * (Em + (Real.sqrt R)⁻¹ * T) := by
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]
    exact one_le_mul_of_one_le_of_one_le hcC (Real.one_le_exp (by positivity))
  have hch := aux_prop_folded_iteration_chain_arith hR hρ1 heA hPt hPk hCc hCP hS1 hS2 hT hEm
    hWt hsk1 hsk2 hskt1 hEn hWk hWt'
  have hex := aux_prop_folded_iteration_exponent hdd hc1 hK hKpos (by linarith) ha1 hw hN hLam
    hLam0 (by linarith) (by linarith) hPkb hPtb heAb hρ
  have hY0 : 0 ≤ Em + (Real.sqrt R)⁻¹ * T :=
    add_nonneg hEm (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hT)
  have hQ0 : 0 ≤ Cc * (CP + S1 + S2) := mul_nonneg hCc (by linarith)
  have h3 : 0 ≤ (3 : ℝ) ^ (w * N) := by positivity
  calc En ≤ Pk * Pt * eA * ρ ^ 2 * (Cc * (CP + S1 + S2)) * (Em + (Real.sqrt R)⁻¹ * T) := hch
    _ ≤ Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 * (3 : ℝ) ^ (w * N) *
          (Cc * (CP + S1 + S2)) * (Em + (Real.sqrt R)⁻¹ * T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hex hQ0) hY0
    _ = (Real.exp (7 * dd / 2 * Real.log 3 + a0) * cC ^ 2 * (Cc * (CP + S1 + S2))) *
          (3 : ℝ) ^ (w * N) * (Em + (Real.sqrt R)⁻¹ * T) := by ring
    _ ≤ C * (3 : ℝ) ^ (w * N) * (Em + (Real.sqrt R)⁻¹ * T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC h3) hY0

/-- Ratio bounds in inverse form. -/
theorem aux_prop_folded_iteration_ratio {c x r R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (h : c⁻¹ * Real.exp (-x) ≤ r / R ∧ r / R ≤ c * Real.exp x) :
    (c * Real.exp x)⁻¹ * R ≤ r ∧ r ≤ c * Real.exp x * R ∧ r⁻¹ ≤ c * Real.exp x * R⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  have he : 0 < Real.exp x := Real.exp_pos x
  have hinv : (c * Real.exp x)⁻¹ = c⁻¹ * Real.exp (-x) := by
    rw [mul_inv, Real.exp_neg]
  have hlow : (c * Real.exp x)⁻¹ * R ≤ r := by
    rw [hinv]
    have := mul_le_mul_of_nonneg_right h1 hR.le
    rwa [div_mul_cancel₀ _ hR.ne'] at this
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hlow
  refine ⟨hlow, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h2 hR.le
    rwa [div_mul_cancel₀ _ hR.ne'] at this
  · have h' : (c * Real.exp x)⁻¹ ≤ r / R := by rw [hinv]; exact h1
    have := inv_anti₀ (by positivity) h'
    rw [inv_inv, inv_div] at this
    calc r⁻¹ = R / r * R⁻¹ := by field_simp
      _ ≤ c * Real.exp x * R⁻¹ := mul_le_mul_of_nonneg_right this (inv_nonneg.2 hR.le)

end FinalArithmetic


section TranslatedChain

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
attribute [local instance] Classical.propDecidable

theorem aux_prop_folded_iteration_halfHolder_nonneg {d : ℕ} (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin d → ℝ) : 0 ≤ halfHolderSeminorm S g := by
  refine Real.sSup_nonneg (fun v hv => ?_)
  obtain ⟨x, _, y, _, _, rfl⟩ := hv
  positivity

/-- The composed translated-chain estimate (Caccioppoli → iteration → Poincaré, with the B5
source bounds) for fixed constants `CH CI Cc CP`, packaged as a proposition. -/
def aux_prop_folded_iteration_chain_prop (d : ℕ) (Cg CH CI Cc CP : ℝ) : Prop :=
      ∀ h : ℕ, 0 < h → ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5 →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * eta) ≤
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h →
      ∀ (m k k' : ℕ), k < k' → k' + 7 ≤ m →
      ∀ (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (g : SpatialCoordinates d → Fin d → ℝ),
        MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g →
      ∀ (a' : Vec d → ℝ), (∀ y, 0 < a' y) →
      ∀ data : ScalarTriadicCoeffData (fun y => a' (y + 0)),
      ∀ u' : H1Function (openCubeSet (originCube d (m : ℤ))),
        IsDivFormWeakSolutionOn a' (cube d (m : ℤ)) u' (fun y => g (y + z)) →
      ∀ a0 : ℕ → ℝ, (∀ j, 0 < a0 j) →
      ∀ Amax : ℝ, (∀ j : ℕ, k + 2 ≤ j → j ≤ k' + 2 → (a0 j)⁻¹ ≤ Amax) →
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ) →
      (∀ j : ℕ, k + 2 ≤ j → j ≤ k' + 2 → (j : ℤ) ∉ bad →
        h ≤ j ∧
          paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
              Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
              data.toTriadicCoeffFamily (a0 j) ≤ ENNReal.ofReal (Cg * eta)) →
      paperHomogenizationError (originCube d ((k : ℤ) + 2)) ((k : ℤ) + 2) (1 / 32)
          Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (a0 k) ≤ ENNReal.ofReal Cg →
      paperHomogenizationError (originCube d ((k' : ℤ) + 2)) ((k' : ℤ) + 2) (1 / 32)
          Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (a0 k') ≤ ENNReal.ofReal Cg →
      let epsJ : ℤ → ℝ := fun j =>
        if j ∈ bad then 0 else
          CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) *
            (paperHomogenizationError (originCube d ((j.toNat : ℤ) + 2)) ((j.toNat : ℤ) + 2)
              (1 / 4 / 8) Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
              data.toTriadicCoeffFamily (a0 j.toNat)).toReal
      let T : ℝ := (3 : ℝ) ^ ((m : ℝ) / 2) *
        halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g
      vectorNormalizedL2On (openCubeSet (originCube d (k : ℤ)))
          (fun y => Real.sqrt (a' y) • u'.grad y) ≤
        Cc * (Real.sqrt (a0 k) *
            Real.exp (CI * (h + 1) * (bad.card + 1) +
              CI * ∑ j ∈ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ), epsJ j) *
            (CP * (Real.sqrt (a0 k'))⁻¹ *
                vectorNormalizedL2On (openCubeSet (originCube d ((k' : ℤ) + 2)))
                  (fun y => Real.sqrt (a' y) • u'.grad y) +
              (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
                  (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) *
                Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4) * (Amax * T)) +
          (Real.sqrt (a0 k))⁻¹ *
            (Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) * T))

/-- Steps (2)–(4) on the origin chart: at the target good scale `k` the Caccioppoli leg, then
the iteration core from `k+2` up to the top good scale `k'+2`, then the Poincaré leg there; the
source enters through B5's summed defect and window display. -/
theorem aux_prop_folded_iteration_translated_chain (d : ℕ) (hd : 2 ≤ d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (Cg : ℝ) (hCg : 0 < Cg) :
    ∃ CH CI Cc CP : ℝ, 0 < CH ∧ 0 < CI ∧ 0 < Cc ∧ 0 < CP ∧
      aux_prop_folded_iteration_chain_prop d Cg CH CI Cc CP := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨CH, CI, hCH, hCI, hcore⟩ := aux_prop_folded_iteration_iteration_core d hd D Cg hCg
  obtain ⟨Cc, hCc, hcac⟩ := aux_prop_folded_iteration_caccioppoli_leg d Cg
  obtain ⟨CP, hCP, hpoi⟩ := aux_prop_folded_iteration_poincare_leg d hd Cg
  refine ⟨CH, CI, Cc, CP, hCH, hCI, hCc, hCP, ?_⟩
  intro h hh hth eta heta0 heta1 hthr m k k' hkk' hk'm z hR g hgH a' ha'pos data u' hweak a0
    ha0 Amax hAmax bad hbad hgood hcapk hcapk' epsJ T
  have ha'0 : ∀ y, 0 ≤ (fun y => a' (y + 0)) y := fun y => (ha'pos _).le
  have hfun : (fun y => a' (y + 0)) = a' := by funext y; rw [add_zero]
  have hweak0 : IsDivFormWeakSolutionOn (fun y => a' (y + 0)) (cube d (m : ℤ)) u'
      (fun y => g (y + z)) := by rw [hfun]; exact hweak
  -- sources (B5)
  obtain ⟨s8, hs8, hg8⟩ := folded_source_memCubeEuclideanFullWsp hd m z hR g hgH (1 / 8)
    (by norm_num) (by norm_num)
  have hg4 := folded_source_memCubeEuclideanFullWsp hd m z hR g hgH (1 / 4)
    (by norm_num) (by norm_num)
  have hCH0 : 0 ≤ Section6ExcessDecay.fractionalHolderConst d :=
    Section6ExcessDecay.fractionalHolderConst_nonneg d
  have hHg0 := aux_prop_folded_iteration_halfHolder_nonneg
    (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g
  have hT0 : 0 ≤ T := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hHg0
  -- caps
  have hEk := aux_prop_folded_iteration_error_cap data (k : ℤ) (a0 k) Cg (ha0 k) hCg.le hcapk
  have hEk' := aux_prop_folded_iteration_error_cap data (k' : ℤ) (a0 k') Cg (ha0 k') hCg.le
    hcapk'
  -- Caccioppoli leg at k
  have hC := hcac (fun y => a' (y + 0)) ha'0 data m k (by omega) u' (fun y => g (y + z)) hweak0
    s8 hs8 hg8 (a0 k) (ha0 k) hEk
  simp only [add_zero] at hC
  -- iteration core from k+2 to k'+2
  have hgood' : ∀ j : ℕ, k + 2 ≤ j → j ≤ k' + 2 → (j : ℤ) ∉ bad →
      h ≤ j ∧ paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 4 / 8)
          Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (a0 j) ≤ ENNReal.ofReal (Cg * eta) := by
    intro j h1 h2 h3
    rw [show (1 / 4 / 8 : ℝ) = 1 / 32 by norm_num]
    exact hgood j h1 h2 h3
  have hit := hcore (1 / 4) (by norm_num) le_rfl h hh hth eta heta0 heta1 hthr m (k + 2) (k' + 2)
    (by omega) (by omega) a' data a0 ha0 u' (fun y => g (y + z)) hweak hg4 bad hbad hgood'
  dsimp only at hit
  -- Poincaré leg at k'
  have hP := hpoi (fun y => a' (y + 0)) ha'0 data m k' hk'm u' (a0 k') (ha0 k') hEk'
  simp only [add_zero] at hP
  -- the summed defect (B5)
  have hdef := folded_source_defect_sum_le hd m z hR g hgH (1 / 4) (by norm_num) le_rfl
    (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h))
    (mul_nonneg (mul_nonneg hCH.le (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _))
    (k + 2) (k' + 2) (by omega) (by omega) a0 ha0 Amax hAmax
    (fun j => if j ∈ bad then 0 else
      CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (a0 j.toNat)⁻¹ * (3 : ℝ) ^ ((1 / 4 : ℝ) * (j.toNat : ℕ)) *
        (fractionalSeminormOn (truncatedCube d m (j.toNat : ℕ) 0) (1 / 4)
          (fun y => g (y + z))).toReal)
    (fun j _ => by
      by_cases hb : j ∈ bad
      · left; simp only [if_pos hb]
      · right; simp only [if_neg hb])
  -- the window at k+2 (B5)
  have hwin := folded_source_window_le_nat hd m z hR g hgH (1 / 8) (by norm_num) (by norm_num)
    (k + 2)
  have hdecay : (3 : ℝ) ^ (-(((m : ℝ) - ((k + 2 : ℕ) : ℝ)) / 2)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : ((k + 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : k + 2 ≤ m)
    linarith
  have hY : (3 : ℝ) ^ ((1 / 8 : ℝ) * ((k + 2 : ℕ) : ℝ)) *
      (fractionalSeminormOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) (1 / 8)
        (fun y => g (y + z))).toReal ≤
      Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) * T := by
    refine hwin.trans ?_
    have hc0 : 0 ≤ Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) :=
      mul_nonneg hCH0 (Real.sqrt_nonneg _)
    calc Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) *
          (3 : ℝ) ^ (-(((m : ℝ) - ((k + 2 : ℕ) : ℝ)) / 2)) * T
        ≤ Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) * 1 * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hc0) hT0
      _ = _ := by ring
  -- assembly
  set X : ℝ := (3 : ℝ) ^ (-((k + 2 : ℕ) : ℤ)) *
    normalizedL2On (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0)
      (fun x ↦ u'.toFun x - averageOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) u'.toFun)
    with hXdef
  set Y : ℝ := (3 : ℝ) ^ ((1 / 8 : ℝ) * ((k + 2 : ℕ) : ℝ)) *
      (fractionalSeminormOn (truncatedCube d m ((k + 2 : ℕ) : ℤ) 0) (1 / 8)
        (fun y => g (y + z))).toReal with hYdef
  set eA : ℝ := Real.exp (CI * (h + 1) * (bad.card + 1) +
      CI * ∑ j ∈ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ), epsJ j) with heA
  set Xtop : ℝ := (3 : ℝ) ^ (-((k' + 2 : ℕ) : ℤ)) *
    normalizedL2On (truncatedCube d m ((k' + 2 : ℕ) : ℤ) 0)
      (fun x ↦ u'.toFun x - averageOn (truncatedCube d m ((k' + 2 : ℕ) : ℤ) 0) u'.toFun)
    with hXtop
  set Sdef := ∑ j ∈ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ),
    (fun j => if j ∈ bad then (0 : ℝ) else
      CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (a0 j.toNat)⁻¹ * (3 : ℝ) ^ ((1 / 4 : ℝ) * (j.toNat : ℕ)) *
        (fractionalSeminormOn (truncatedCube d m (j.toNat : ℕ) 0) (1 / 4)
          (fun y => g (y + z))).toReal) j with hSdef
  have hit' : X ≤ eA * (Xtop + Sdef) := hit
  have heA0 : 0 ≤ eA := (Real.exp_pos _).le
  have hsk := Real.sqrt_nonneg (a0 k)
  have hS : Sdef ≤ (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) *
      Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4) * (Amax * T) := by
    refine hdef.trans (le_of_eq ?_)
    simp only [T]
    ring
  -- combine
  have hX2 : X ≤ eA * (CP * (Real.sqrt (a0 k'))⁻¹ *
        vectorNormalizedL2On (openCubeSet (originCube d ((k' : ℤ) + 2)))
          (fun y => Real.sqrt (a' y) • u'.grad y) +
      (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4) * (Amax * T)) :=
    hit'.trans (mul_le_mul_of_nonneg_left (add_le_add hP hS) heA0)
  refine hC.trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCc.le
  · calc Real.sqrt (a0 k) * X
        ≤ Real.sqrt (a0 k) * (eA * _) := mul_le_mul_of_nonneg_left hX2 hsk
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_left hY (inv_nonneg.2 hsk)

end TranslatedChain


section RootedHelpers

theorem aux_prop_folded_iteration_eta_exists (d : ℕ) (CH : ℝ) (h : ℕ) (hCH : 0 < CH)
    (hstep : 2 * CH * (3 : ℝ) ^ (-(h : ℝ) / 2) ≤ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧
      CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * eta) ≤
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h := by
  have hA : 0 < (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) := by positivity
  have hth : 0 < ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h := by positivity
  obtain ⟨h1, h2, h3⟩ := aux_prop_folded_iteration_eta_choice hCH hA hth hstep
  exact ⟨_, h1, h2, h3⟩

theorem aux_prop_folded_iteration_choose_KC (Gam Keta Kd2 cC c1 c2 Cfin : ℝ) :
    ∃ K C : ℝ, 1 ≤ K ∧ Gam ≤ K ∧ Keta ≤ K ∧ Kd2 ≤ K ∧ 46 ≤ C ∧ K * cC ≤ C ∧
      1024 * c2 ^ 2 * K ≤ C ∧ K * c1 ≤ C ∧ Cfin ≤ C := by
  refine ⟨max (max Kd2 Keta) (max Gam 1),
    max 46 (max (max (max Kd2 Keta) (max Gam 1) * cC)
      (max (1024 * c2 ^ 2 * max (max Kd2 Keta) (max Gam 1))
        (max (max (max Kd2 Keta) (max Gam 1) * c1) Cfin))),
    le_trans (le_max_right _ _) (le_max_right _ _),
    le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_left _ _),
    le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem aux_prop_folded_iteration_final_shape {En C x Em R T1 T2 : ℝ}
    (h : En ≤ C * x * (Em + (Real.sqrt R)⁻¹ * (T1 * T2))) :
    En ≤ C * x * (Em + Real.sqrt R⁻¹ * T1 * T2) := by
  rw [Real.sqrt_inv]
  calc En ≤ C * x * (Em + (Real.sqrt R)⁻¹ * (T1 * T2)) := h
    _ = C * x * (Em + (Real.sqrt R)⁻¹ * T1 * T2) := by ring

attribute [local instance] Classical.propDecidable in
/-- The iteration exponent `CI(h+1)(|bad|+1) + CI·Σ ε_j` is at most `a₀ + a₁·λ'(m-n)`, from the
bad count, the per-scale error bound at non-bad scales, `δ²+ε'^8 ≤ 2λ'` and the score sum. -/
theorem aux_prop_folded_iteration_eA_bound (lo hi n m h : ℕ) (hlo : n ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi + 2 ≤ m) (bad : Finset ℤ) (e score : ℕ → ℝ) (cE Cg CI base lam nb : ℝ)
    (hcE : 0 ≤ cE) (hCg : 0 ≤ Cg) (hCI : 0 ≤ CI) (hbase0 : 0 ≤ base)
    (hscore : ∀ i, 0 ≤ score i) (he0 : ∀ j, 0 ≤ e j)
    (hgood : ∀ j : ℕ, lo ≤ j → j ≤ hi → (j : ℤ) ∉ bad → e j ≤ Cg * (base + score (j + 2)))
    (hbase : base ≤ 2 * lam)
    (hsc : ∑ i ∈ Finset.Icc n m, score i ≤ lam * ((m : ℝ) - n))
    (hbad : (bad.card : ℝ) ≤ h + nb) (hnb : nb < 1 + lam * ((m : ℝ) - n)) :
    1 ≤ Real.exp (CI * (h + 1) * (bad.card + 1) +
        CI * ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat)) ∧
      Real.exp (CI * (h + 1) * (bad.card + 1) +
        CI * ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat)) ≤
      Real.exp (CI * (h + 1) * (h + 2) + (CI * (h + 1) + 3 * (cE * Cg) * CI) *
        (lam * ((m : ℝ) - n))) := by
  have hN0 : (0 : ℝ) ≤ (m : ℝ) - n := by
    have : (n : ℝ) ≤ m := by exact_mod_cast (by omega : n ≤ m)
    linarith only [this]
  have hsum := aux_prop_folded_iteration_eps_sum lo hi n m hlo hlohi hhi bad e score cE Cg base
    hcE hCg hbase0 hscore hgood
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat) :=
    Finset.sum_nonneg (fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg hcE (he0 _))
  have hce : 0 ≤ cE * Cg := mul_nonneg hcE hCg
  have hS : ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat) ≤
      3 * (cE * Cg) * (lam * ((m : ℝ) - n)) := by
    refine hsum.trans ?_
    have hb := mul_le_mul_of_nonneg_right hbase hN0
    calc cE * Cg * (base * ((m : ℝ) - n) + ∑ i ∈ Finset.Icc n m, score i)
        ≤ cE * Cg * (2 * lam * ((m : ℝ) - n) + lam * ((m : ℝ) - n)) :=
          mul_le_mul_of_nonneg_left (add_le_add hb hsc) hce
      _ = 3 * (cE * Cg) * (lam * ((m : ℝ) - n)) := by ring
  have hh0 : (0 : ℝ) ≤ CI * (h + 1) := mul_nonneg hCI (by positivity)
  refine ⟨Real.one_le_exp (add_nonneg (mul_nonneg hh0 (by positivity)) (mul_nonneg hCI hS0)),
    Real.exp_le_exp.2 ?_⟩
  have hb : (bad.card : ℝ) + 1 ≤ h + 2 + lam * ((m : ℝ) - n) := by
    linarith only [hbad, hnb]
  have h1 := mul_le_mul_of_nonneg_left hb hh0
  have h2 := mul_le_mul_of_nonneg_left hS hCI
  calc CI * (h + 1) * (bad.card + 1) +
        CI * ∑ j ∈ Finset.Icc (lo : ℤ) (hi : ℤ), (if j ∈ bad then 0 else cE * e j.toNat)
      ≤ CI * (h + 1) * (h + 2 + lam * ((m : ℝ) - n)) +
        CI * (3 * (cE * Cg) * (lam * ((m : ℝ) - n))) := add_le_add h1 h2
    _ = _ := by ring

end RootedHelpers

section Rooted

open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
attribute [local instance] Classical.propDecidable

/-- The whole estimate for fixed dimensional constants: parameters at `αT`, the good-scale pair,
the translated chain, the energy bridges, the reference ratios and the final collapse. -/
theorem aux_prop_folded_iteration_rooted (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Cg CH CI Cc CP cC c1 c2 eta K C : ℝ) (h : ℕ)
    (hCg : 0 < Cg) (hCH : 0 < CH) (hCI : 0 < CI) (hCc : 0 < Cc) (hCP : 0 < CP)
    (hcC : 1 ≤ cC) (hc1 : 2 ≤ c1) (hc12 : c1 ≤ c2)
    (hGSE : aux_prop_folded_iteration_gse_prop d Cg)
    (hchain : aux_prop_folded_iteration_chain_prop d Cg CH CI Cc CP)
    (hconst : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg), It.C = cC ∧ It.C1 = c1 ∧ It.C2 = c2)
    (hh : 0 < h) (hth : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hthr : CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * eta) ≤
      ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h)
    (hK1 : 1 ≤ K)
    (hKGam : (d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Cg) * CI) + 2 * cC ≤ K)
    (hKeta : 1 / (2 * eta ^ 2) ≤ K)
    (hC46 : 46 ≤ C) (hKcC : K * cC ≤ C) (hKc2 : 1024 * c2 ^ 2 * K ≤ C) (hKc1 : K * c1 ≤ C)
    (hCfin : Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * cC ^ 2 *
        (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (1 / 4) +
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))) ≤ C) :
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), I.Nonempty → m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (It.ref L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro M Sreg It hdel alpha halpha aT L m n z hR om I P hI hmL hnm hpre foldedCoef hfold g hgrad
    u hgH hg hweak
  obtain ⟨hCeq, hC1eq, hC2eq⟩ := hconst M Sreg It
  have hdel0 : 0 < M.delta := M.shellPrefix.delta_pos
  have h18 : c1 * c2 ^ (-8 : ℝ) ≤ 1 := by rw [← hC1eq, ← hC2eq]; exact It.C1_C2_le_one
  obtain ⟨haT, hdelC, h64, hs0eps, hepseta, heps0, hlam0, hlamhalf, hbase, hlameq⟩ :=
    aux_prop_folded_iteration_parameters (delta := M.delta) (alpha := alpha) (K := K) (C := C)
      (cC := cC) (c1 := c1) (c2 := c2) (eta := eta) hdel0 hdel hK1 hC46 hcC hKcC hKc2 hKc1
      hc1 hc12 h18 heta0 hKeta halpha
  have hαT : aT ∈ It.alphaRange := by rw [It.alphaRange_eq, hCeq]; exact haT
  have hdelIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdelC
  have h64It : 64 * M.delta ^ 2 ≤ It.s0 := by rw [It.s0_eq]; exact h64
  have hsIt : It.s0⁻¹ * M.delta ^ 2 ≤ It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) := by
    rw [It.s0_eq, hC2eq]; exact hs0eps
  have hepseta' : It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) ≤ eta := by rw [hC2eq]; exact hepseta
  have hepsIt1 : It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) ≤ 1 := hepseta'.trans heta1
  have hlamhalf' : It.C1⁻¹ * (1 - aT) ≤ 1 / 2 := by rw [hC1eq]; exact hlamhalf
  have hbase' : M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8 ≤
      2 * (It.C1⁻¹ * (1 - aT)) := by rw [hC2eq, hC1eq]; exact hbase
  have hlam0' : 0 ≤ It.C1⁻¹ * (1 - aT) := by rw [hC1eq]; exact hlam0
  have heps0' : 0 ≤ It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) := by rw [hC2eq]; exact heps0
  have hlameq' : It.C1⁻¹ * (1 - aT) = (1 - alpha) / (K * c1) := by rw [hC1eq]; exact hlameq
  obtain ⟨hscore, hcount⟩ := It.good_scale_sums z aT hαT hdelIt (It.C1⁻¹ * (1 - aT))
    (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) rfl rfl n m om hpre
  have hpl := It.prefix_lower z aT m om
  rw [It.k_eq] at hpl
  have h26 : n + 26 ≤ m := by omega
  have hcount' : ((@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card : ℝ) <
      1 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    convert hcount using 3
    ext j
    simp
  obtain ⟨k, k', hnk, hkk', hk'm, hgk, hgk', hdk, hdk'⟩ :=
    aux_prop_folded_iteration_good_pair
      (fun j => It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om) n m h26
      (It.C1⁻¹ * (1 - aT)) hlamhalf' hcount'
  obtain ⟨a', -, ha'pos, ha'm, ⟨data⟩⟩ :=
    aux_prop_folded_iteration_folded_representative d Sreg L m z hR om I P foldedCoef hfold
  obtain ⟨u', -, hu'2, hu'w⟩ :=
    aux_prop_folded_iteration_weak_transfer m z hR foldedCoef a' ha'm g hgrad u hg hweak
  -- per-scale error at good scales
  have hsc : ∀ j : ℕ, j + 2 ≤ m → It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤
        ENNReal.ofReal (Cg * min (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ))
          (M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8 +
            It.score (j + 2) z It.s0 om)) := by
    intro j hjm hgj
    exact hGSE E M Sreg It aT hαT hdelIt h64It hsIt hepsIt1 L m z hR om I P hI foldedCoef hfold j
      (by omega) hjm hgj a' (ae_restrict_of_ae_restrict_of_subset
        (aux_prop_folded_iteration_originCube_subset (by omega)) ha'm) data
  have hsc_eta : ∀ j : ℕ, j + 2 ≤ m →
      It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤ ENNReal.ofReal (Cg * eta) :=
    fun j hjm hgj => (hsc j hjm hgj).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hepseta') hCg.le))
  have hsc_one : ∀ j : ℕ, j + 2 ≤ m →
      It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤ ENNReal.ofReal Cg :=
    fun j hjm hgj => (hsc_eta j hjm hgj).trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right hCg.le heta1))
  -- the iteration's bad set
  obtain ⟨bad, hbaddef⟩ : ∃ bad : Finset ℤ, bad = ((Finset.Icc (k + 2) (k' + 2)).filter
      (fun j => j < h ∨ ¬ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)).image
      (fun j : ℕ => (j : ℤ)) := ⟨_, rfl⟩
  have hbadsub : bad ⊆ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ) := by
    intro j hj
    rw [hbaddef] at hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨i, ⟨⟨h1, h2⟩, _⟩, rfl⟩ := hj
    simp only [Finset.mem_Icc]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hnotbad : ∀ j : ℕ, k + 2 ≤ j → j ≤ k' + 2 → (j : ℤ) ∉ bad →
      h ≤ j ∧ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om := by
    intro j h1 h2 hj
    by_contra hcon
    apply hj
    rw [hbaddef]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨j, ⟨⟨h1, h2⟩, ?_⟩, rfl⟩
    by_contra hc2
    push_neg at hc2
    exact hcon hc2
  have hbadcard : (bad.card : ℝ) ≤ h + (@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card := by
    have h1 := aux_prop_folded_iteration_bad_card
      (fun j => It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om) n m k k' h hnk hk'm
    have h2 : bad.card ≤ (@Finset.filter ℕ
        (fun j => j < h ∨ ¬ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
        (Classical.decPred _) (Finset.Icc (k + 2) (k' + 2))).card := by
      rw [hbaddef]
      refine Finset.card_image_le.trans (le_of_eq ?_)
      congr 1
      ext j
      simp
    exact_mod_cast h2.trans h1
  -- reference ratios
  have hR0 : 0 < It.ref L (m - 2) z om := It.ref_pos L (m - 2) z om
  have hrat : ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
      (It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)))⁻¹ *
          It.ref L (m - 2) z om ≤ It.ref L j z om ∧
        It.ref L j z om ≤ It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) *
          It.ref L (m - 2) z om ∧
        (It.ref L j z om)⁻¹ ≤ It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) *
          (It.ref L (m - 2) z om)⁻¹ := fun j hnj hj5 =>
    aux_prop_folded_iteration_ratio It.C_pos hR0
      (It.ref_ratio L z aT hαT hdelIt _ rfl n m j om hpre hmL hnj hj5)
  -- the translated chain
  have hW := hchain h hh hth eta heta0.le heta1 hthr m k k' hkk' hk'm z hR g hgH a' ha'pos data
    u' hu'w (fun j => It.ref L j z om) (fun j => It.ref_pos L j z om)
    (It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) * (It.ref L (m - 2) z om)⁻¹)
    (fun j h1 h2 => (hrat j (by omega) (by omega)).2.2) bad hbadsub
    (fun j h1 h2 hj => ⟨(hnotbad j h1 h2 hj).1,
      hsc_eta j (by omega) (hnotbad j h1 h2 hj).2⟩)
    (hsc_one k (by omega) hgk) (hsc_one k' (by omega) hgk')
  dsimp only at hW
  -- energies on the root chart
  have hRn : (0 : ℝ) < 3 ^ n := by positivity
  have hRk : (0 : ℝ) < 3 ^ k := by positivity
  have hRt : (0 : ℝ) < 3 ^ (k' + 2) := by positivity
  have hsubc : ∀ (a b : ℕ), a ≤ b → ∀ (ha : (0 : ℝ) < 3 ^ a) (hb : (0 : ℝ) < 3 ^ b),
      (centeredCube z ((3 : ℝ) ^ a) ha : Set (SpatialCoordinates d)) ⊆
        centeredCube z ((3 : ℝ) ^ b) hb := by
    intro a b hab ha hb
    change Metric.ball z ((3 : ℝ) ^ a / 2) ⊆ Metric.ball z ((3 : ℝ) ^ b / 2)
    refine Metric.ball_subset_ball ?_
    have : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hab
    linarith only [this]
  have hEk := aux_prop_folded_iteration_energy_bridge m k (by omega) z hR foldedCoef a'
    (fun y => (ha'pos y).le) ha'm (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) u' hu'2 hRk
  have hEt := aux_prop_folded_iteration_energy_bridge m (k' + 2) (by omega) z hR foldedCoef a'
    (fun y => (ha'pos y).le) ha'm (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) u' hu'2 hRt
  have hcast : ((k' + 2 : ℕ) : ℤ) = (k' : ℤ) + 2 := by push_cast; ring
  rw [hcast] at hEt
  have hEn := normalizedEnergyNorm_le_sqrt_volume_ratio foldedCoef
    (centeredCube z ((3 : ℝ) ^ n) hRn).isOpen.measurableSet
    (centeredCube z ((3 : ℝ) ^ k) hRk).isOpen.measurableSet (hsubc n k hnk hRn hRk)
    (by rw [centeredCube_volume_real]; positivity) (by rw [centeredCube_volume_real]; positivity)
    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)))
  rw [centeredCube_volume_real, centeredCube_volume_real, hEk] at hEn
  have hEtm := normalizedEnergyNorm_le_sqrt_volume_ratio foldedCoef
    (centeredCube z ((3 : ℝ) ^ (k' + 2)) hRt).isOpen.measurableSet
    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet (hsubc (k' + 2) m (by omega) hRt hR)
    (by rw [centeredCube_volume_real]; positivity) (by rw [centeredCube_volume_real]; positivity)
    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)))
  rw [centeredCube_volume_real, centeredCube_volume_real, hEt] at hEtm
  -- counting in reals
  obtain ⟨nb, hnb⟩ : ∃ nb : ℕ, nb = (@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card := ⟨_, rfl⟩
  rw [← hnb] at hdk hdk' hcount' hbadcard
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast (by omega : n ≤ m)
  have hN0 : (0 : ℝ) ≤ (m : ℝ) - n := by linarith only [hnm']
  have hLam0 : 0 ≤ It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := mul_nonneg hlam0' hN0
  have hkn : (k : ℝ) - n ≤ 1 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    have h1 : ((k - n : ℕ) : ℝ) ≤ (nb : ℝ) := by exact_mod_cast hdk
    rw [Nat.cast_sub hnk] at h1
    linarith only [h1, hcount']
  have hmt : (m : ℝ) - ((k' + 2 : ℕ) : ℝ) ≤ 6 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    have h1 : ((m - 7 - k' : ℕ) : ℝ) ≤ (nb : ℝ) := by exact_mod_cast hdk'
    have h2 : ((m - 7 - k' : ℕ) : ℝ) = (m : ℝ) - 7 - k' := by
      rw [Nat.cast_sub (by omega : k' ≤ m - 7), Nat.cast_sub (by omega : 7 ≤ m)]
      push_cast
      ring
    rw [h2] at h1
    push_cast
    linarith only [h1, hcount']
  have hPkb := aux_prop_folded_iteration_vol_factor d n k _ hkn
  have hPtb := aux_prop_folded_iteration_vol_factor d (k' + 2) m _ hmt
  have hPt1 : 1 ≤ Real.sqrt (((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (k' + 2)) ^ d) := by
    rw [Real.one_le_sqrt, one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) d
  -- the error sum and the iteration exponent
  have hcE0 : 0 ≤ CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hCH.le (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨heA1, heAb⟩ := aux_prop_folded_iteration_eA_bound (k + 2) (k' + 2) n m h (by omega)
    (by omega) (by omega) bad
    (fun j => (paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
      (1 / 4 / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily (It.ref L j z om)).toReal)
    (fun i => It.score i z It.s0 om)
    (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)) Cg CI
    (M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8) (It.C1⁻¹ * (1 - aT)) nb
    hcE0 hCg.le hCI.le (by positivity) (fun i => It.score_nonneg i z It.s0 om)
    (fun j => ENNReal.toReal_nonneg)
    (fun j h1 h2 hj => by
      have hgj := (hnotbad j h1 h2 hj).2
      have h3 := hsc j (by omega) hgj
      rw [show (1 / 4 / 8 : ℝ) = 1 / 32 by norm_num]
      exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg hCg.le (add_nonneg (by positivity) (It.score_nonneg _ _ _ _)))
        (h3.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hCg.le))))
    hbase' hscore hbadcard hcount'
  -- final collapse
  have hrk := hrat k hnk (by omega)
  have hrk' := hrat k' (by omega) (by omega)
  have hw : 0 ≤ 1 - alpha := by
    have : 0 ≤ C * M.delta * Real.sqrt |Real.log M.delta| :=
      mul_nonneg (mul_nonneg (by linarith only [hC46]) hdel0.le) (Real.sqrt_nonneg _)
    linarith only [halpha.2, this]
  have hT0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) *
      halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g :=
    mul_nonneg (by positivity) (aux_prop_folded_iteration_halfHolder_nonneg _ _)
  have hfin := aux_prop_folded_iteration_final_arith (dd := (d : ℝ)) (c1 := c1) (C := C)
    (K := K) (w := 1 - alpha) (N := (m : ℝ) - n) (cC := cC)
    (Lam := It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n))
    hR0 hcC (by exact heA1) hPt1 (Real.sqrt_nonneg _)
    hCc.le hCP.le
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCH.le
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)))
      (Section6ExcessDecay.fractionalHolderConst_nonneg d)) (Real.sqrt_nonneg _))
    (mul_nonneg (Section6ExcessDecay.fractionalHolderConst_nonneg d) (Real.sqrt_nonneg _))
    hT0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hrk.1 hrk.2.1 hrk'.1 hEn hW hEtm
    (Nat.cast_nonneg d) hc1 hKGam (lt_of_lt_of_le one_pos hK1) (by positivity) hw hN0
    (by rw [hlameq']; ring) hLam0 hPkb hPtb
    (by exact heAb)
    (by rw [hCeq, mul_assoc cC]) hCfin
  exact aux_prop_folded_iteration_final_shape hfin

end Rooted



theorem prop_folded_iteration :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (Poinc : in_poincare d hd E)
    (Ext : in_extension d hd E)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
  ∃ C K : ℝ, 0 < C ∧
    1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ K ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), I.Nonempty → m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (It.ref L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro d hd _ _ E Poinc Ext D
  obtain ⟨Cg, hCg, hGSE⟩ := aux_prop_folded_iteration_good_scale_error_min d hd
  obtain ⟨CH, CI, Cc, CP, hCH, hCI, hCc, hCP, hchain⟩ :=
    aux_prop_folded_iteration_translated_chain d hd D Cg hCg
  obtain ⟨cC, c1, c2, hcC, hc1, hc12, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  obtain ⟨h, hh, hth, hstep⟩ := aux_prop_folded_iteration_step_choice CH
  obtain ⟨eta, heta0, heta1, hthr⟩ := aux_prop_folded_iteration_eta_exists d CH h hCH hstep
  obtain ⟨K, C, hK1, hKGam, hKeta, hKd2, hC46, hKcC, hKc2, hKc1, hCfin⟩ :=
    aux_prop_folded_iteration_choose_KC
      ((d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Cg) * CI) + 2 * cC)
      (1 / (2 * eta ^ 2))
      (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1))
      cC c1 c2
      (Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * cC ^ 2 *
        (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (1 / 4) +
          SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))))
  exact ⟨C, K, lt_of_lt_of_le (by norm_num) hC46, hKd2,
    aux_prop_folded_iteration_rooted d E Cg CH CI Cc CP cC c1 c2 eta K C h hCg hCH hCI hCc hCP
      hcC hc1 hc12 hGSE hchain (hconst E) hh hth heta0 heta1 hthr hK1 hKGam hKeta hC46 hKcC
      hKc2 hKc1 hCfin⟩

end Paper
