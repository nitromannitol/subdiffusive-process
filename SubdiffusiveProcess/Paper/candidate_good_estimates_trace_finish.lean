module

public import SubdiffusiveProcess.Sobolev.CampanatoBudget
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.candidate_good_event
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_passage
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.WeakGraphMaxPrinciple
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.lem_prefix_limit
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

public import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_support
public import SubdiffusiveProcess.Paper.candidate_good_estimates_constants_support
public import SubdiffusiveProcess.Paper.candidate_source_compact_bank
public import SubdiffusiveProcess.Paper.candidate_represented_source_bank
public import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

universe uCge

section CgeTraceFinishContext
variable (d : ℕ)
variable (hd : 2 ≤ d)
variable [NeZero d]
variable (I : in_J d)
variable (alpha beta s cell : ℝ)
variable (halpha : alpha ∈ Ioo 0 1)
variable (hcell : cell ∈ Ioo 0 1)
def aux_candidate_good_estimates_trace_finish_cellDet (cell : ℝ) : ℝ :=
  cell / 2
variable (deltaGS Cbound Ccamp : ℝ)
variable (hCbound : 1 ≤ Cbound)
variable (hCcamp0 : 0 ≤ Ccamp)
variable (hCcampB : Ccamp ≤ Cbound)
variable (hCcampHolder : 2 * aux_in_deterministic_regularity_holderConst d alpha * Ccamp ≤ Cbound)
variable (deltaGrowth epshom epsCap lamCap deltaCap : ℝ)
variable (hNum : 0 < 1 - alpha)
def aux_candidate_good_estimates_trace_finish_T (alpha : ℝ) (Cbound : ℝ) : ℝ :=
  (1 - alpha) / (4 * Cbound)
variable (hTpos : 0 < (aux_candidate_good_estimates_trace_finish_T alpha Cbound))
def aux_candidate_good_estimates_trace_finish_eps0 (alpha : ℝ) (Cbound : ℝ) (epsCap : ℝ) : ℝ :=
  min epsCap (min 1 (aux_candidate_good_estimates_trace_finish_T alpha Cbound))
def aux_candidate_good_estimates_trace_finish_lam0 (alpha : ℝ) (Cbound : ℝ) (lamCap : ℝ) : ℝ :=
  min lamCap (aux_candidate_good_estimates_trace_finish_T alpha Cbound)
def aux_candidate_good_estimates_trace_finish_deltaDet (alpha : ℝ) (Cbound : ℝ) (deltaCap : ℝ) : ℝ :=
  min deltaCap √(aux_candidate_good_estimates_trace_finish_T alpha Cbound)
def aux_candidate_good_estimates_trace_finish_delta0 (alpha : ℝ) (deltaGS : ℝ) (Cbound : ℝ) (deltaGrowth : ℝ) (deltaCap : ℝ) : ℝ :=
  min (aux_candidate_good_estimates_trace_finish_deltaDet alpha Cbound deltaCap) (min deltaGrowth deltaGS)
variable (cbuf k0 : ℕ)
variable (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
variable (H : BilateralField d → C(SpatialCoordinates d, ℝ))
variable (Ω : Type)
variable [_instΩ : MeasurableSpace Ω]
variable (P : Measure Ω)
variable (env : PUnit.{uCge} → ℕ → Ω → BilateralField d)
variable (k : ℕ)
variable (z : SpatialCoordinates d)
variable (qside : ℝ)
variable (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
variable (qcenter : SpatialCoordinates d)
variable (hqcenter : qcenter = z)
variable (Enl Shift Cmp : Type)
variable [_instCmp : Fintype Cmp]
variable (rootLevel : Enl × Shift → ℤ)
variable (cmpLevel : Cmp → ℤ)
variable (chosen : Cmp)
variable (observationCentre :
          (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → SpatialCoordinates d)
variable (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
variable (eps : ℝ)
variable (heps : eps ∈ Ioo 0 1)
variable (hepsSmall : eps ≤ (aux_candidate_good_estimates_trace_finish_eps0 alpha Cbound epsCap))
variable (lambdaLim lambdaDet cdet : ℝ)
variable (hLamPos : 0 < lambdaDet)
variable (hlamSmall : lambdaDet ≤ (aux_candidate_good_estimates_trace_finish_lam0 alpha Cbound lamCap))
variable (hdisorder : M.delta ≤ (aux_candidate_good_estimates_trace_finish_delta0 alpha deltaGS Cbound deltaGrowth deltaCap))
variable (prefixZ prefixD :
          (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ)
variable (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
variable (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
variable (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
variable (phi : ℕ → ℕ)
variable (hphi : StrictMono phi)
variable (prefixZLim prefixDLim : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ)
variable (ellLoLim ellHiLim : Enl × Shift → Ω → ℝ)
variable (errLim ratioLim : Cmp → Ω → ℝ)
variable (Qcentre : SpatialCoordinates d)
variable (Qside : ℝ)
variable (hQside : 0 < Qside)
variable (S : ResponseSpace (centeredCube Qcentre Qside hQside))
variable (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
variable (GN :
          ℕ →
            BilateralField d →
              ↥(DomainL2 (centeredCube Qcentre Qside hQside)) →L[ℝ] ↥(DomainL2 (centeredCube Qcentre Qside hQside)))
variable (hGN :
          ∀ (N : ℕ) (omega : BilateralField d) (f : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
            (GN N omega) f =
              (responseSolution S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                    ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
variable (GE : Ω → ↥(DomainL2 (centeredCube Qcentre Qside hQside)) →L[ℝ] ↥(DomainL2 (centeredCube Qcentre Qside hQside)))
variable (sE : Ω → ℝ)
variable (hsE :
          ∀ᵐ (omega : Ω) ∂P,
            0 < sE omega ∧ Tendsto (fun n => sN (phi n) (↑k) z (env PUnit.unit n omega)) atTop (𝓝 (sE omega)))
variable (hDeltaPos : 0 < M.delta)
variable (hEps0Cap : (aux_candidate_good_estimates_trace_finish_eps0 alpha Cbound epsCap) ≤ epsCap)
variable (hqpos : 0 < qside)
def aux_candidate_good_estimates_trace_finish_lambdaA (lambdaLim : ℝ) (lambdaDet : ℝ) : ℝ :=
  (lambdaLim + lambdaDet) / 2
def aux_candidate_good_estimates_trace_finish_Q (d : ℕ) [NeZero d] (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside) : Opens (SpatialCoordinates d) :=
  centeredCube Qcentre Qside hQside
def aux_candidate_good_estimates_trace_finish_Good (d : ℕ) [NeZero d] (cell : ℝ) (epshom : ℝ) (k0 : ℕ) (Ω : Type) [_instΩ : MeasurableSpace Ω] (Enl : Type) (Shift : Type) (Cmp : Type) [_instCmp : Fintype Cmp] (chosen : Cmp) (lambdaLim : ℝ) (cdet : ℝ) (prefixZLim : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ) (prefixDLim : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ) (ellLoLim : Enl × Shift → Ω → ℝ) (ellHiLim : Enl × Shift → Ω → ℝ) (errLim : Cmp → Ω → ℝ) (ratioLim : Cmp → Ω → ℝ) : Set Ω :=
  {omega |
            (∀ (U : Enl × Shift) (D : ℕ),
                k0 ≤ D →
                  ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                    prefixZLim U D code omega < lambdaLim * ↑D ∧ prefixDLim U D code omega < lambdaLim * ↑D) ∧
              (∀ (U : Enl × Shift), cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
                errLim chosen omega ≤ epshom * cdet ∧ ∀ (c : Cmp), ratioLim c omega ∈ Ioo (1 / 2) 2}
variable (hGoodLimit :
            ∀ᵐ (omega : Ω) ∂P,
              omega ∈ (aux_candidate_good_estimates_trace_finish_Good d cell epshom k0 Ω Enl Shift Cmp chosen lambdaLim cdet prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim) →
                (∀ (U : Enl × Shift) (D : ℕ),
                    k0 ≤ D →
                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                        prefixZLim U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧ prefixDLim U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) ∧
                  (∀ (U : Enl × Shift), cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
                    errLim chosen omega ≤ epshom * cdet ∧ ∀ (c : Cmp), ratioLim c omega ∈ Ioo (1 / 2) 2)
def aux_candidate_good_estimates_trace_finish_prefixZSeq (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Enl : Type) (Shift : Type) (prefixZ : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (phi : ℕ → ℕ) : ℕ → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ :=
  fun n U D code omega => prefixZ (phi n) U D code (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_prefixDSeq (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Enl : Type) (Shift : Type) (prefixD : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (phi : ℕ → ℕ) : ℕ → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ :=
  fun n U D code omega => prefixD (phi n) U D code (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_lowN (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Enl : Type) (Shift : Type) (ellLoN : ℕ → Enl × Shift → BilateralField d → ℝ) (phi : ℕ → ℕ) : Enl × Shift → ℕ → Ω → ℝ :=
  fun U n omega => ellLoN (phi n) U (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_highN (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Enl : Type) (Shift : Type) (ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ) (phi : ℕ → ℕ) : Enl × Shift → ℕ → Ω → ℝ :=
  fun U n omega => ellHiN (phi n) U (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_errorN (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Cmp : Type) [_instCmp : Fintype Cmp] (chosen : Cmp) (errN : ℕ → Cmp → BilateralField d → ℝ) (phi : ℕ → ℕ) : ℕ → Ω → ℝ :=
  fun n omega => errN (phi n) chosen (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_ratioSeq (d : ℕ) [NeZero d] (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Cmp : Type) [_instCmp : Fintype Cmp] (ratioN : ℕ → Cmp → BilateralField d → ℝ) (phi : ℕ → ℕ) : Cmp → ℕ → Ω → ℝ :=
  fun c n omega => ratioN (phi n) c (env PUnit.unit n omega)
def aux_candidate_good_estimates_trace_finish_FinEvent (d : ℕ) [NeZero d] (cell : ℝ) (epshom : ℝ) (k0 : ℕ) (Ω : Type) [_instΩ : MeasurableSpace Ω] (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (Enl : Type) (Shift : Type) (Cmp : Type) [_instCmp : Fintype Cmp] (chosen : Cmp) (lambdaLim : ℝ) (lambdaDet : ℝ) (cdet : ℝ) (prefixZ : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (prefixD : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (ellLoN : ℕ → Enl × Shift → BilateralField d → ℝ) (ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ) (errN : ℕ → Cmp → BilateralField d → ℝ) (ratioN : ℕ → Cmp → BilateralField d → ℝ) (phi : ℕ → ℕ) : ℕ → ℕ → Ω → Prop :=
  fun horizon n omega =>
            (∀ (U : Enl × Shift) (D : ℕ),
                k0 ≤ D →
                  D ≤ horizon →
                    ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                      (aux_candidate_good_estimates_trace_finish_prefixZSeq d Ω env Enl Shift prefixZ phi) n U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧ (aux_candidate_good_estimates_trace_finish_prefixDSeq d Ω env Enl Shift prefixD phi) n U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) ∧
              (∀ (U : Enl × Shift), cell / 2 < (aux_candidate_good_estimates_trace_finish_lowN d Ω env Enl Shift ellLoN phi) U n omega ∧ (aux_candidate_good_estimates_trace_finish_highN d Ω env Enl Shift ellHiN phi) U n omega < 2 * cell⁻¹) ∧
                (aux_candidate_good_estimates_trace_finish_errorN d Ω env Cmp chosen errN phi) n omega < 2 * epshom * cdet ∧ ∀ (c : Cmp), (aux_candidate_good_estimates_trace_finish_ratioSeq d Ω env Cmp ratioN phi) c n omega ∈ Ioo (1 / 2) 2
variable (nu : ℕ → ℕ → ℕ)
def aux_candidate_good_estimates_trace_finish_Budget (d : ℕ) [NeZero d] (I : in_J d) (s : ℝ) (Cbound : ℝ) (cbuf : ℕ) (k0 : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (Enl : Type) (Shift : Type) (rootLevel : Enl × Shift → ℤ) (observationCentre : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → SpatialCoordinates d) (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ) (eps : ℝ) (lambdaDet : ℝ) (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ) : ℕ → ℕ → BilateralField d → Prop :=
  fun horizon N omega =>
              (∀ (Uroot : Enl × Shift),
                  ∀ D ≤ horizon,
                    rootLevel Uroot + ↑D ≤ ↑N →
                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                        ↑{j ∈ Finset.Icc (rootLevel Uroot - ↑cbuf) (rootLevel Uroot + ↑D) |
                                j < rootLevel Uroot + ↑k0 ∨
                                  1 ≤ Z N (↑N - j).toNat ((3 : ℝ) ^ N • observationCentre Uroot D code) omega}.card ≤
                          ↑k0 + ↑cbuf + lambdaDet * ↑D) ∧
                ∀ (Uroot : Enl × Shift),
                  ∀ D ≤ horizon,
                    rootLevel Uroot + ↑D ≤ ↑N →
                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                        (∑ j ∈ Finset.Icc (rootLevel Uroot - ↑cbuf) (rootLevel Uroot + ↑D),
                            if
                                rootLevel Uroot + ↑k0 ≤ j ∧
                                  Z N (↑N - j).toNat ((3 : ℝ) ^ N • observationCentre Uroot D code) omega < 1 then
                              let w : SpatialCoordinates d := observationCentre Uroot D code;
                              let rj : ℝ := 3 ^ (-j);
                              I.err w rj (by positivity) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity)) w rj (sN N j w omega) s 2
                            else 0) ≤
                          Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * ↑D + Cbound * (↑k0 + ↑cbuf)
variable (hBudgetAll :
                ∀ᵐ (omega : Ω) ∂P,
                  ∀ (horizon n : ℕ),
                    k + k0 ≤ phi (nu horizon n) →
                      (∀ (U : Enl × Shift) (D : ℕ),
                          k0 ≤ D →
                            D ≤ horizon →
                              ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                prefixZ (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
                                    (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧
                                  prefixD (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
                                    (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) →
                        (aux_candidate_good_estimates_trace_finish_Budget d I s Cbound cbuf k0 M H Enl Shift rootLevel observationCentre Z eps lambdaDet sN) horizon (phi (nu horizon n)) (env PUnit.unit (nu horizon n) omega))
def aux_candidate_good_estimates_trace_finish_CmpBound (Cmp : Type) [_instCmp : Fintype Cmp] (cmpLevel : Cmp → ℤ) : ℕ :=
  ∑ c, (cmpLevel c).toNat
variable (hCmpBound : ∀ (c : Cmp), cmpLevel c ≤ ↑(aux_candidate_good_estimates_trace_finish_CmpBound Cmp cmpLevel))
def aux_candidate_good_estimates_trace_finish_Nmin (k0 : ℕ) (k : ℕ) (Cmp : Type) [_instCmp : Fintype Cmp] (cmpLevel : Cmp → ℤ) : ℕ :=
  max (k + k0) (aux_candidate_good_estimates_trace_finish_CmpBound Cmp cmpLevel)
variable (shiftIndex : (horizon : ℕ) → ℕ)
def aux_candidate_good_estimates_trace_finish_nuShift (nu : ℕ → ℕ → ℕ) (shiftIndex : (horizon : ℕ) → ℕ) : ℕ → ℕ → ℕ :=
  fun horizon n => nu horizon (n + shiftIndex horizon)
variable (hnuShift : ∀ (horizon : ℕ), StrictMono ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon))
variable (hNlarge : ∀ (horizon n : ℕ), (aux_candidate_good_estimates_trace_finish_Nmin k0 k Cmp cmpLevel) ≤ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon n))
variable (hFiniteAllShift :
                      ∀ᵐ (omega : Ω) ∂P,
                        omega ∈ (aux_candidate_good_estimates_trace_finish_Good d cell epshom k0 Ω Enl Shift Cmp chosen lambdaLim cdet prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim) → ∀ (horizon : ℕ), ∀ᶠ (n : ℕ) in atTop, (aux_candidate_good_estimates_trace_finish_FinEvent d cell epshom k0 Ω env Enl Shift Cmp chosen lambdaLim lambdaDet cdet prefixZ prefixD ellLoN ellHiN errN ratioN phi) horizon ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon n) omega)
def aux_candidate_good_estimates_trace_finish_campAllContract (d : ℕ) [NeZero d] (I : in_J d) (alpha : ℝ) (s : ℝ) (cell : ℝ) (Cbound : ℝ) (Ccamp : ℝ) (epshom : ℝ) (cbuf : ℕ) (k0 : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (Ω : Type) [_instΩ : MeasurableSpace Ω] (P : Measure Ω) (env : PUnit.{uCge} → ℕ → Ω → BilateralField d) (k : ℕ) (qside : ℝ) (qcenter : SpatialCoordinates d) (Enl : Type) (Shift : Type) (Cmp : Type) [_instCmp : Fintype Cmp] (rootLevel : Enl × Shift → ℤ) (chosen : Cmp) (observationCentre : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → SpatialCoordinates d) (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ) (eps : ℝ) (lambdaLim : ℝ) (lambdaDet : ℝ) (cdet : ℝ) (prefixZ : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (prefixD : (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ) (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ) (ellLoN : ℕ → Enl × Shift → BilateralField d → ℝ) (ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ) (errN : ℕ → Cmp → BilateralField d → ℝ) (ratioN : ℕ → Cmp → BilateralField d → ℝ) (phi : ℕ → ℕ) (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside) (hqpos : 0 < qside) (nu : ℕ → ℕ → ℕ) (shiftIndex : (horizon : ℕ) → ℕ) : Prop :=
  ∀ᵐ (a : Ω) ∂P,
                        ∀ (i i_1 horizon : ℕ),
                          ((∀ (U : Enl × Shift) (D : ℕ),
                                k0 ≤ D →
                                  D ≤ horizon →
                                    rootLevel U + ↑D ≤ ↑(phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) →
                                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                        prefixZ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) U D code (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) <
                                            (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧
                                          prefixD (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) U D code (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) <
                                            (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) ∧
                              (∀ (U : Enl × Shift),
                                  (aux_candidate_good_estimates_trace_finish_cellDet cell) ≤ ellLoN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) U (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) ∧
                                    ellHiN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) U (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) ≤ (aux_candidate_good_estimates_trace_finish_cellDet cell)⁻¹) ∧
                                errN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) chosen (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) ≤
                                    2 * epshom * cdet ∧
                                  ∀ (c : Cmp),
                                    ratioN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) c (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) ∈ Icc (1 / 2) 2) →
                            ((∀ (Uroot : Enl × Shift),
                                  ∀ D ≤ horizon,
                                    rootLevel Uroot + ↑D ≤ ↑(phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) →
                                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                        ↑{j ∈ Finset.Icc (rootLevel Uroot - ↑cbuf) (rootLevel Uroot + ↑D) |
                                                j < rootLevel Uroot + ↑k0 ∨
                                                  1 ≤
                                                    Z (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) (↑(phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) - j).toNat
                                                      ((3 : ℝ) ^ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) • observationCentre Uroot D code)
                                                      (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a)}.card ≤
                                          ↑k0 + ↑cbuf + lambdaDet * ↑D) ∧
                                ∀ (Uroot : Enl × Shift),
                                  ∀ D ≤ horizon,
                                    rootLevel Uroot + ↑D ≤ ↑(phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) →
                                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                        (∑ j ∈ Finset.Icc (rootLevel Uroot - ↑cbuf) (rootLevel Uroot + ↑D),
                                            if
                                                rootLevel Uroot + ↑k0 ≤ j ∧
                                                  Z (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) (↑(phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) - j).toNat
                                                      ((3 : ℝ) ^ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) • observationCentre Uroot D code)
                                                      (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) <
                                                    1 then
                                              have w : SpatialCoordinates d := observationCentre Uroot D code;
                                              let rj : ℝ := 3 ^ (-j);
                                              I.err w rj (by positivity)
                                                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a)
                                                  (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) w (by positivity))
                                                w rj (sN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) j w (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a)) s
                                                2
                                            else 0) ≤
                                          Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * ↑D + Cbound * (↑k0 + ↑cbuf)) →
                              ∀ (f : SpatialCoordinates d → ℝ),
                                MemLp f (ENNReal.ofReal (↑d / (1 - alpha)))
                                    (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
                                  ∀ (fL2 : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
                                    ↑↑fL2 =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] f →
                                      have fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
                                        (eLpNorm f (ENNReal.ofReal (↑d / (1 - alpha))) (volume.restrict W)).toReal /
                                          volume.real W ^ (1 / (↑d / (1 - alpha)));
                                      ∀ (u : ↥(weakSobolevGraph (centeredCube Qcentre Qside hQside))),
                                        (∀ (psi : ↥(killedSobolevGraph (centeredCube Qcentre Qside hQside))),
                                            ((sobolevCoefficientForm
                                                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
                                                      (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a) (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) Qcentre
                                                      hQside))
                                                  ↑u)
                                                ↑psi =
                                              (sobolevVolumeLoad fL2) ↑psi) →
                                          ∀ (U : SpatialCoordinates d → ℝ),
                                            ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
                                              ((u.val.1 : SpatialCoordinates d → ℝ)) =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] U →
                                                ∀ D ≤ horizon,
                                                  ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
                                                    have B : Set (SpatialCoordinates d) :=
                                                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                                                        (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d));
                                                    (normalizedL2On B fun y =>
                                                        U y -
                                                          (volume.real B)⁻¹ * ∫ (t : SpatialCoordinates d) in B, U t) ≤
                                                      Ccamp * 3 ^ (Ccamp * (↑k0 + ↑cbuf)) *
                                                            3 ^ (Ccamp * (lambdaDet + M.delta ^ 2 + eps ^ 8) * ↑D) *
                                                          (3 : ℝ) ^ (-(D : ℤ)) *
                                                        ((normalizedL2On (Metric.ball qcenter (3 * qside / 2)) fun y =>
                                                            U y -
                                                              (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                                                                ∫ (t : SpatialCoordinates d) in
                                                                  Metric.ball qcenter (3 * qside / 2), U t) +
                                                          qside ^ 2 *
                                                              (sN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1)) (↑k) qcenter
                                                                  (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i i_1) a))⁻¹ *
                                                            fNorm (Metric.ball qcenter (3 * qside / 2)))
variable (hCampAll : aux_candidate_good_estimates_trace_finish_campAllContract d I alpha s cell Cbound Ccamp epshom cbuf k0 M H Ω P env k qside qcenter Enl Shift Cmp rootLevel chosen observationCentre Z eps lambdaLim lambdaDet cdet prefixZ prefixD sN ellLoN ellHiN errN ratioN phi Qcentre Qside hQside hqpos nu shiftIndex)
variable (hBankAll :
                      ∀ᵐ (a : Ω) ∂P,
                        ∀ (i : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
                          ContDiff ℝ ∞ f →
                            0 ≤ Kf →
                              (∀ᵐ (x : SpatialCoordinates d) ∂volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                                  |f x| ≤ Kf) →
                                ∀ (fL2 : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
                                  ↑↑fL2 =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] f →
                                    ∃ U ns UN,
                                      StrictMono ns ∧
                                        ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                                          ↑↑((GE a) fL2) =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))]
                                              U ∧
                                            (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
                                              _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) U ∧
                                                TendstoUniformlyOn UN U atTop
                                                    (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                                                  ∀ (n : ℕ),
                                                    Continuous (UN n) ∧
                                                      ↑↑((GN ((fun n => phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i n)) (ns n))
                                                                ((fun n omega => env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i n) omega)
                                                                  (ns n) a))
                                                              fL2) =ᶠ[ae
                                                          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))]
                                                        UN n)
variable (hgeom :
                      Metric.ball qcenter (3 * qside / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
                        closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
                          (∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos, qcenter + qside • x ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                            qcenter ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
variable (hQopen : IsOpen ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)))
variable (hQcompact : IsCompact (closure ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d))))
include d hd I alpha beta s cell halpha hcell deltaGS Cbound Ccamp hCbound hCcamp0 hCcampB hCcampHolder deltaGrowth epshom epsCap lamCap deltaCap hNum hTpos cbuf k0 M H Ω P env k z qside hqside qcenter hqcenter Enl Shift Cmp rootLevel cmpLevel chosen observationCentre Z eps heps hepsSmall lambdaLim lambdaDet cdet hLamPos hlamSmall hdisorder prefixZ prefixD sN ellLoN ellHiN errN ratioN phi hphi prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim Qcentre Qside hQside S hS GN hGN GE sE hsE hDeltaPos hEps0Cap hqpos hGoodLimit nu hBudgetAll hCmpBound shiftIndex hnuShift hNlarge hFiniteAllShift hCampAll hBankAll hgeom hQopen hQcompact
omit d hd I alpha beta s cell halpha hcell deltaGS Cbound Ccamp hCbound hCcamp0 hCcampB hCcampHolder deltaGrowth epshom epsCap lamCap deltaCap hNum hTpos cbuf k0 M H Ω P env k z qside hqside qcenter hqcenter Enl Shift Cmp rootLevel cmpLevel chosen observationCentre Z eps heps hepsSmall lambdaLim lambdaDet cdet hLamPos hlamSmall hdisorder prefixZ prefixD sN ellLoN ellHiN errN ratioN phi hphi prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim Qcentre Qside hQside S hS GN hGN GE sE hsE hDeltaPos hEps0Cap hqpos hGoodLimit nu hBudgetAll hCmpBound shiftIndex hnuShift hNlarge hFiniteAllShift hCampAll hBankAll hgeom hQopen hQcompact [NeZero d] _instΩ _instCmp in
/-- The finite horizon Campanato data pass to the candidate trace estimate. -/
theorem candidate_good_estimates_trace_finish
    (d : ℕ)
    (hd : 2 ≤ d)
    [_instNeZero : NeZero d]
    (I : in_J d)
    (alpha beta s cell : ℝ)
    (halpha : alpha ∈ Ioo 0 1)
    (_hcell : cell ∈ Ioo 0 1)
    (deltaGS Cbound Ccamp : ℝ)
    (hCbound : 1 ≤ Cbound)
    (hCcamp0 : 0 ≤ Ccamp)
    (hCcampB : Ccamp ≤ Cbound)
    (hCcampHolder : 2 * aux_in_deterministic_regularity_holderConst d alpha * Ccamp ≤ Cbound)
    (deltaGrowth epshom epsCap lamCap deltaCap : ℝ)
    (_hNum : 0 < 1 - alpha)
    (_hTpos : 0 < (aux_candidate_good_estimates_trace_finish_T alpha Cbound))
    (cbuf k0 : ℕ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type)
    [_instΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (env : PUnit.{uCge} → ℕ → Ω → BilateralField d)
    (k : ℕ)
    (z : SpatialCoordinates d)
    (qside : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (hqcenter : qcenter = z)
    (Enl Shift Cmp : Type)
    [_instCmp : Fintype Cmp]
    (rootLevel : Enl × Shift → ℤ)
    (cmpLevel : Cmp → ℤ)
    (chosen : Cmp)
    (observationCentre :
          (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → SpatialCoordinates d)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (eps : ℝ)
    (heps : eps ∈ Ioo 0 1)
    (hepsSmall : eps ≤ (aux_candidate_good_estimates_trace_finish_eps0 alpha Cbound epsCap))
    (lambdaLim lambdaDet cdet : ℝ)
    (hLamPos : 0 < lambdaDet)
    (hlamSmall : lambdaDet ≤ (aux_candidate_good_estimates_trace_finish_lam0 alpha Cbound lamCap))
    (hdisorder : M.delta ≤ (aux_candidate_good_estimates_trace_finish_delta0 alpha deltaGS Cbound deltaGrowth deltaCap))
    (prefixZ prefixD :
          (N : ℕ) → (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → BilateralField d → ℝ)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
    (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
    (phi : ℕ → ℕ)
    (_hphi : StrictMono phi)
    (prefixZLim prefixDLim : (U : Enl × Shift) → (D : ℕ) → (Fin D → OddGridIndex d 1) ⊕ Enl × Shift → Ω → ℝ)
    (ellLoLim ellHiLim : Enl × Shift → Ω → ℝ)
    (errLim ratioLim : Cmp → Ω → ℝ)
    (Qcentre : SpatialCoordinates d)
    (Qside : ℝ)
    (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (GN :
          ℕ →
            BilateralField d →
              ↥(DomainL2 (centeredCube Qcentre Qside hQside)) →L[ℝ] ↥(DomainL2 (centeredCube Qcentre Qside hQside)))
    (hGN :
          ∀ (N : ℕ) (omega : BilateralField d) (f : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
            (GN N omega) f =
              (responseSolution S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                    ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (GE : Ω → ↥(DomainL2 (centeredCube Qcentre Qside hQside)) →L[ℝ] ↥(DomainL2 (centeredCube Qcentre Qside hQside)))
    (sE : Ω → ℝ)
    (hsE :
          ∀ᵐ (omega : Ω) ∂P,
            0 < sE omega ∧ Tendsto (fun n => sN (phi n) (↑k) z (env PUnit.unit n omega)) atTop (𝓝 (sE omega)))
    (hDeltaPos : 0 < M.delta)
    (_hEps0Cap : (aux_candidate_good_estimates_trace_finish_eps0 alpha Cbound epsCap) ≤ epsCap)
    (hqpos : 0 < qside)
    (hGoodLimit :
            ∀ᵐ (omega : Ω) ∂P,
              omega ∈ (aux_candidate_good_estimates_trace_finish_Good d cell epshom k0 Ω Enl Shift Cmp chosen lambdaLim cdet prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim) →
                (∀ (U : Enl × Shift) (D : ℕ),
                    k0 ≤ D →
                      ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                        prefixZLim U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧ prefixDLim U D code omega < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) ∧
                  (∀ (U : Enl × Shift), cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
                    errLim chosen omega ≤ epshom * cdet ∧ ∀ (c : Cmp), ratioLim c omega ∈ Ioo (1 / 2) 2)
    (nu : ℕ → ℕ → ℕ)
    (hBudgetAll :
                ∀ᵐ (omega : Ω) ∂P,
                  ∀ (horizon n : ℕ),
                    k + k0 ≤ phi (nu horizon n) →
                      (∀ (U : Enl × Shift) (D : ℕ),
                          k0 ≤ D →
                            D ≤ horizon →
                              ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                prefixZ (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
                                    (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D ∧
                                  prefixD (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
                                    (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * ↑D) →
                        (aux_candidate_good_estimates_trace_finish_Budget d I s Cbound cbuf k0 M H Enl Shift rootLevel observationCentre Z eps lambdaDet sN) horizon (phi (nu horizon n)) (env PUnit.unit (nu horizon n) omega))
    (hCmpBound : ∀ (c : Cmp), cmpLevel c ≤ ↑(aux_candidate_good_estimates_trace_finish_CmpBound Cmp cmpLevel))
    (shiftIndex : (horizon : ℕ) → ℕ)
    (hnuShift : ∀ (horizon : ℕ), StrictMono ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon))
    (hNlarge : ∀ (horizon n : ℕ), (aux_candidate_good_estimates_trace_finish_Nmin k0 k Cmp cmpLevel) ≤ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon n))
    (hFiniteAllShift :
                      ∀ᵐ (omega : Ω) ∂P,
                        omega ∈ (aux_candidate_good_estimates_trace_finish_Good d cell epshom k0 Ω Enl Shift Cmp chosen lambdaLim cdet prefixZLim prefixDLim ellLoLim ellHiLim errLim ratioLim) → ∀ (horizon : ℕ), ∀ᶠ (n : ℕ) in atTop, (aux_candidate_good_estimates_trace_finish_FinEvent d cell epshom k0 Ω env Enl Shift Cmp chosen lambdaLim lambdaDet cdet prefixZ prefixD ellLoN ellHiN errN ratioN phi) horizon ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) horizon n) omega)
    (hCampAll : aux_candidate_good_estimates_trace_finish_campAllContract d I alpha s cell Cbound Ccamp epshom cbuf k0 M H Ω P env k qside qcenter Enl Shift Cmp rootLevel chosen observationCentre Z eps lambdaLim lambdaDet cdet prefixZ prefixD sN ellLoN ellHiN errN ratioN phi Qcentre Qside hQside hqpos nu shiftIndex)
    (hBankAll :
                      ∀ᵐ (a : Ω) ∂P,
                        ∀ (i : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
                          ContDiff ℝ ∞ f →
                            0 ≤ Kf →
                              (∀ᵐ (x : SpatialCoordinates d) ∂volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                                  |f x| ≤ Kf) →
                                ∀ (fL2 : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
                                  ↑↑fL2 =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] f →
                                    ∃ U ns UN,
                                      StrictMono ns ∧
                                        ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                                          ↑↑((GE a) fL2) =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))]
                                              U ∧
                                            (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
                                              _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) U ∧
                                                TendstoUniformlyOn UN U atTop
                                                    (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                                                  ∀ (n : ℕ),
                                                    Continuous (UN n) ∧
                                                      ↑↑((GN ((fun n => phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i n)) (ns n))
                                                                ((fun n omega => env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) i n) omega)
                                                                  (ns n) a))
                                                              fL2) =ᶠ[ae
                                                          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))]
                                                        UN n)
    (hgeom :
                      Metric.ball qcenter (3 * qside / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
                        closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
                          (∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos, qcenter + qside • x ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                            qcenter ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hQopen : IsOpen ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)))
    (hQcompact : IsCompact (closure ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)))) :
  ∀ᵐ (omega : Ω) ∂P,
                      omega ∈
                          {omega |
                            (∀ (U : Enl × Shift) (D : ℕ),
                                k0 ≤ D →
                                  ∀ (code : (Fin D → OddGridIndex d 1) ⊕ Enl × Shift),
                                    prefixZLim U D code omega < lambdaLim * ↑D ∧
                                      prefixDLim U D code omega < lambdaLim * ↑D) ∧
                              (∀ (U : Enl × Shift), cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
                                errLim chosen omega ≤ epshom * cdet ∧ ∀ (c : Cmp), ratioLim c omega ∈ Ioo (1 / 2) 2} →
                        ∀ (f : SpatialCoordinates d → ℝ),
                          ContDiff ℝ ∞ f →
                            ∀ (fL2 : ↥(DomainL2 (centeredCube Qcentre Qside hQside))),
                              ↑↑fL2 =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] f →
                                ∃ U,
                                  ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                                    ↑↑((GE omega) fL2) =ᶠ[ae (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))] U ∧
                                      (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
                                        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2))) U ∧
                                          ∃ cq,
                                            (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) fun x =>
                                                U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - cq) ≤
                                              Cbound * 3 ^ (Cbound * (↑k0 + ↑cbuf)) *
                                                ((normalizedL2On (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2)) fun x =>
                                                    U x -
                                                      (volume.real (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2)))⁻¹ *
                                                        ∫ (y : SpatialCoordinates d) in
                                                          Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), U y) +
                                                  ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 * (sE omega)⁻¹ *
                                                    sSup
                                                      {v |
                                                        ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
                                                          v = |f x|}) := by
  filter_upwards [hGoodLimit, hFiniteAllShift, hBudgetAll, hCampAll, hBankAll, hsE]
    with omega hGoodLim hFinAll hBudAll hCampAllω hBankAllω hSE
  intro hGood f hf fL2 hfL2
  let fsup := sSup {v : ℝ | ∃ x ∈ closure ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)), v = |f x|}
  have hfsup : 0 ≤ fsup := Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _)
  have hfbdd : BddAbove {v : ℝ | ∃ x ∈ closure ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)), v = |f x|} := by
    obtain ⟨B, hB⟩ := (centeredCube_isBounded Qcentre hQside).isCompact_closure.exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs] using hB x hx
  have hfbound : ∀ᵐ x ∂volume.restrict ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)), |f x| ≤ fsup :=
    ae_restrict_of_forall_mem hQopen.measurableSet
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure hx, rfl⟩)
  have hpsource : 0 < (d : ℝ) / (1 - alpha) :=
    div_pos (by exact_mod_cast (show 0 < d by omega)) (by linarith only [halpha.2])
  have hQfinite : volume (aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside : Set (SpatialCoordinates d)) < (∞ : ℝ≥0∞) :=
    measure_lt_top_of_subset subset_closure hQcompact.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside : Set (SpatialCoordinates d))) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hQfinite⟩
  have hfMem : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable fsup
      (hfbound.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)
  choose Uh ns VN hns hUhcont hUhrep hUhzero hUhHolder hUni hVNcont hVNrep
    using fun horizon => hBankAllω horizon f fsup hf hfsup hfbound fL2 hfL2
  let U := Uh 0
  have hUae : ∀ h, U =ᵐ[volume.restrict ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d))] Uh h := by
    intro h
    exact (hUhrep 0).symm.trans (hUhrep h)
  let aN : ℕ → ℕ → ℝ := fun h n =>
    sN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) (k : ℤ) z (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega)
  have hA : ∀ h, Tendsto (aN h) atTop (𝓝 (sE omega)) := by
    intro h
    exact hSE.2.comp ((hnuShift h).comp (hns h)).tendsto_atTop
  let uN : ℕ → ℕ → Ω → weakSobolevGraph (aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) := fun h n omega =>
    ⟨(responseSolution S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
        (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) Qcentre hQside)
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val,
      killedSobolevGraph_le_weakSobolevGraph (hS ▸ (responseSolution S
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
          (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) Qcentre hQside)
        ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).property)⟩
  have hsolve : ∀ h n omega, ∀ psi : killedSobolevGraph (aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside),
      sobolevCoefficientForm
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
          (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) Qcentre hQside)
        (uN h n omega).val psi.val = sobolevVolumeLoad fL2 psi.val := by
    intro h n omega psi
    exact responseSolution_spec S _ ((sobolevVolumeLoad fL2).comp S.space.subtypeL)
      ⟨psi.val, hS.symm ▸ psi.property⟩
  have hUNrep : ∀ h n, ((uN h n omega).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d))] (VN h n) := by
    intro h n
    have he := hVNrep h n
    have hgn := hGN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) fL2
    change ((responseSolution S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
        (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) Qcentre hQside)
      ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val.1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d))] (VN h n)
    rw [← hgn]
    simpa only [id, aux_candidate_good_estimates_trace_finish_Q] using he
  have hcellDetInv : (aux_candidate_good_estimates_trace_finish_cellDet cell)⁻¹ = 2 * cell⁻¹ := by
    change (cell * (2 : ℝ)⁻¹)⁻¹ = 2 * cell⁻¹
    rw [_root_.mul_inv_rev, inv_inv]
  have hCampFinite : ∀ (h D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)), ∀ᶠ n in atTop,
        let W : Set (SpatialCoordinates d) :=
          Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
        normalizedL2On W (fun y => VN h n y - (volume.real W)⁻¹ * ∫ y in W, VN h n y) ≤
          Ccamp * (3 : ℝ) ^ (Ccamp * ((k0 : ℝ) + (cbuf : ℝ))) *
            (3 : ℝ) ^ (Ccamp * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
            (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
              (fun y => VN h n y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                ∫ y in Metric.ball qcenter (3 * qside / 2), VN h n y) +
              qside ^ 2 * (aN h n)⁻¹ *
                ((eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
                  (volume.restrict (Metric.ball qcenter (3 * qside / 2)))).toReal /
                  volume.real (Metric.ball qcenter (3 * qside / 2)) ^
                    (1 / ((d : ℝ) / (1 - alpha))))) := by
    intro h D hDh x hx
    filter_upwards [(hns h).tendsto_atTop.eventually (hFinAll hGood h)] with n hfin
    have Nbig : (aux_candidate_good_estimates_trace_finish_Nmin k0 k Cmp cmpLevel) ≤ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) := hNlarge h (ns h n)
    have hkn : k + k0 ≤ phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) :=
      (Nat.le_max_left _ _).trans Nbig
    have hcmp : ∀ c : Cmp, cmpLevel c ≤ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) : ℤ) := by
      intro c
      exact (hCmpBound c).trans (by exact_mod_cast ((Nat.le_max_right _ _).trans Nbig))
    have hprefix : ∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ h →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          prefixZ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
              (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) ∧
          prefixD (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
              (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) := by
      intro U D hD hDh code
      simpa only [aux_candidate_good_estimates_trace_finish_FinEvent, aux_candidate_good_estimates_trace_finish_prefixZSeq, aux_candidate_good_estimates_trace_finish_prefixDSeq, aux_candidate_good_estimates_trace_finish_lowN, aux_candidate_good_estimates_trace_finish_highN, aux_candidate_good_estimates_trace_finish_errorN, aux_candidate_good_estimates_trace_finish_ratioSeq] using
        hfin.1 U D hD hDh code
    have hprefixBudget : ∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ h →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          prefixZ (phi (nu h (ns h n + shiftIndex h))) U D code
              (env PUnit.unit (nu h (ns h n + shiftIndex h)) omega) <
                (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) ∧
          prefixD (phi (nu h (ns h n + shiftIndex h))) U D code
              (env PUnit.unit (nu h (ns h n + shiftIndex h)) omega) <
                (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) := by
      intro U D hD hDh code
      change prefixZ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
          (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) ∧
        prefixD (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
          (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ)
      exact hprefix U D hD hDh code
    have hbudget := hBudAll h (ns h n + shiftIndex h) hkn hprefixBudget
    have hfiniteInput :
        (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ h →
          rootLevel U + (D : ℤ) ≤ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) : ℤ) →
          ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
            prefixZ (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
                (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ) ∧
            prefixD (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U D code
                (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) < (aux_candidate_good_estimates_trace_finish_lambdaA lambdaLim lambdaDet) * (D : ℝ)) ∧
        (∀ U : Enl × Shift,
          (aux_candidate_good_estimates_trace_finish_cellDet cell) ≤ ellLoN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U
              (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) ∧
          ellHiN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) U (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) ≤
              (aux_candidate_good_estimates_trace_finish_cellDet cell)⁻¹) ∧
        errN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) chosen (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) ≤
            2 * epshom * cdet ∧
        (∀ c : Cmp, ratioN (phi ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n))) c
          (env PUnit.unit ((aux_candidate_good_estimates_trace_finish_nuShift nu shiftIndex) h (ns h n)) omega) ∈ Set.Icc (1 / 2 : ℝ) 2) := by
      rcases hfin with ⟨_, hcellGood, herr, hratio⟩
      refine ⟨?_, ?_, herr.le, ?_⟩
      · intro U D hD hDh hlevel code
        exact hprefix U D hD hDh code
      · intro U
        exact ⟨by simpa only [aux_candidate_good_estimates_trace_finish_cellDet, aux_candidate_good_estimates_trace_finish_lowN] using! (hcellGood U).1.le,
          by rw [hcellDetInv]; exact (hcellGood U).2.le⟩
      · intro c
        exact ⟨(hratio c).1.le, (hratio c).2.le⟩
    have hcamp := hCampAllω h (ns h n) h hfiniteInput hbudget
    have hwindow := hcamp f hfMem fL2 hfL2 (uN h n omega) (hsolve h n omega)
      (VN h n) (hVNcont h n).continuousOn (hUNrep h n) D hDh x hx
    simpa only [aux_candidate_good_estimates_trace_finish_nuShift, aN, aux_candidate_good_estimates_trace_finish_cellDet, hqside, hqcenter, Real.rpow_neg_natCast] using hwindow
  let psource : ℝ := (d : ℝ) / (1 - alpha)
  let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
    (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
      volume.real W ^ (1 / psource)
  have hFle : fNorm (Metric.ball qcenter (3 * qside / 2)) ≤ fsup := by
    have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball qcenter (3 * qside / 2)), |f x| ≤ fsup :=
      ae_restrict_of_forall_mem measurableSet_ball (fun x hx =>
        le_csSup hfbdd ⟨x, subset_closure (hgeom.1 hx), rfl⟩)
    have htop : volume (Metric.ball qcenter (3 * qside / 2)) ≠ ⊤ :=
      Metric.isBounded_ball.measure_lt_top.ne
    let : IsFiniteMeasure (volume.restrict (Metric.ball qcenter (3 * qside / 2))) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact htop.lt_top⟩
    have hn := SubdiffusiveProcess.normalized_eLpNorm_le_of_ae_bound
      (volume.restrict (Metric.ball qcenter (3 * qside / 2))) psource hpsource f fsup hfsup hbound
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf.continuous.aestronglyMeasurable] at hn
    have hvol : ((volume.restrict (Metric.ball qcenter (3 * qside / 2))) Set.univ).toReal =
        volume.real (Metric.ball qcenter (3 * qside / 2)) := by
      rw [Measure.restrict_apply_univ]
      rfl
    simpa only [fNorm, psource, hvol] using hn
  obtain ⟨hHolder, hCa⟩ := aux_candidate_good_estimates_trace_support_campanato_limit_bank alpha halpha
    ((aux_candidate_good_estimates_trace_finish_Q d Qcentre Qside hQside) : Set (SpatialCoordinates d)) hQopen hQcompact qcenter qside hqpos hgeom.1 hgeom.2.1
    hgeom.2.2.1 hgeom.2.2.2 U Uh VN ((hUhcont 0).mono subset_closure) hUhcont
    (fun h n => (hVNcont h n).continuousOn) hUae hUni aN (sE omega) hSE.1 hA
    Ccamp Cbound ((k0 : ℝ) + (cbuf : ℝ)) (lambdaDet + M.delta ^ 2 + eps ^ 8)
    (fNorm (Metric.ball qcenter (3 * qside / 2))) fsup hCcamp0 hCcampB hCcampHolder
    (by positivity) (by positivity)
    (campanato_budget_of_small_caps alpha Cbound eps lambdaDet M.delta
      (lt_of_lt_of_le zero_lt_one hCbound) halpha.2 heps.1.le heps.2.le hDeltaPos.le
      (hepsSmall.trans ((min_le_right epsCap (min 1 (aux_candidate_good_estimates_trace_finish_T alpha Cbound))).trans (min_le_right 1 (aux_candidate_good_estimates_trace_finish_T alpha Cbound))))
      (hlamSmall.trans (min_le_right lamCap (aux_candidate_good_estimates_trace_finish_T alpha Cbound)))
      (hdisorder.trans ((min_le_left (aux_candidate_good_estimates_trace_finish_deltaDet alpha Cbound deltaCap) (min deltaGrowth deltaGS)).trans
        (min_le_right deltaCap (Real.sqrt (aux_candidate_good_estimates_trace_finish_T alpha Cbound))))))
    hfsup hFle (by simpa only [fNorm, psource, Real.rpow_neg_natCast] using hCampFinite)
  have hcenterBall : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by
    change Metric.ball qcenter (qside / 2) = Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2)
    rw [hqcenter, hqside]
  refine ⟨U, hUhcont 0, hUhrep 0, hUhzero 0, ?_, ?_⟩
  · simpa only [hcenterBall] using hHolder
  · refine ⟨U z, ?_⟩
    simpa only [hqcenter, hqside, fsup, psource, fNorm, aux_candidate_good_estimates_trace_finish_Q, Real.rpow_neg_natCast] using hCa
end CgeTraceFinishContext
end SubdiffusiveProcess.Paper
end
