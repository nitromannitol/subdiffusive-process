import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor

/-! # Uniform stochastic energy price for harmonic cutoff cells -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A measurable physical Dirichlet energy envelope with any prescribed moment,
uniform over the cutoff, domain scale, and real centre. All response-moment and
fractional-order premises of the source energy theorem are discharged. -/
theorem exists_uniform_cutoffDirichletEnergy_moment_bound
    (d : ℕ) [NeZero d] (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 Cenergy Cmoment : ℝ, 0 < delta0 ∧ 0 < Cenergy ∧ 0 < Cmoment ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ L N : ℕ, L ≤ N → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
          eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal Cmoment ∧
          ∀ᵐ omega ∂M.P.toMeasure,
            ∀ {u : H1Function (openCubeSet (originCube d 0))}
              (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
              (F : CubeVectorH1Function (originCube d 0))
              (hu : IsScalarDirichletSolutionOn
                (scalarCoeffField (rescaledCutoffCoefficient M L N (translatePotentialSample z omega)))
                (originCube d 0) u h.toH1 f)
              (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
                ∫ x in openCubeSet (originCube d 0), f x * psi.toFun x =
                  -∫ x in openCubeSet (originCube d 0), vecDot (F.toField x) (psi.grad x)),
              dirichletForcedSolutionEnergyNorm (originCube d (N : ℤ)) (aCutoffFamily M L
                  (translatePotentialSample z omega))
                (cutoffPhysicalDirichletForcedCubeSolution M L N
                  (translatePotentialSample z omega) F hu hF) ≤
                K omega * Real.sqrt (ahom M L) * (centeredCubeScale (N : ℤ))⁻¹ *
                  sourceDirichletEnergyDatumPrice Cenergy ⟨1 / 16, by norm_num⟩ F h := by
  let s : FractionalOrder := ⟨1 / 16, by norm_num⟩
  let s2 : FractionalOrder := ⟨1 / 8, by norm_num⟩
  let xi := max q (128 * (d : ℝ))
  have hqxi : q ≤ xi := le_max_left _ _
  have hxi : 1 ≤ xi := hq.trans hqxi
  have hdim : 4 * (d : ℝ) * ((1 / 16 : ℝ) / 2)⁻¹ ≤ xi := by
    calc
      _ = 128 * (d : ℝ) := by norm_num; ring
      _ ≤ xi := le_max_right q (128 * (d : ℝ))
  obtain ⟨deltaR, R, hdeltaR, hR, hresponse⟩ :=
    exists_dirichletFullResponse_paper_moment_bound (s := (1 / 16 : ℝ))
      (xi := xi) (by norm_num) (by norm_num) hxi hdim
  obtain ⟨deltaY, Cmoment, hdeltaY, hCmoment, henvelope⟩ :=
    exists_dirichletEllipticityEnvelope_moment_bound (s := (1 / 16 : ℝ))
      (xi := xi) (by norm_num) (by norm_num) hxi hdim
  obtain ⟨Cenergy, hCenergy, henergy⟩ := exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice d
  refine ⟨min deltaR deltaY, Cenergy, Cmoment, lt_min hdeltaR hdeltaY,
    hCenergy, hCmoment, ?_⟩
  intro M hM L N hLN z
  have hMR := hM.trans (min_le_left deltaR deltaY)
  have hMY := hM.trans (min_le_right deltaR deltaY)
  have hresp := (hresponse M hMR L N hLN).2
  have hevent := henergy M L N s s2 (by norm_num [s, s2])
    (zero_lt_one.trans_le hxi) hresp
  let K0 := dirichletEllipticityEnvelope M L N (1 / 16)
  have hK0 : Measurable K0 := by
    unfold K0 dirichletEllipticityEnvelope
    exact measurable_const.add ((measurable_dirichletFullResponseTwo M L N _).const_mul 2)
  have hnorm0 : eLpNorm K0 (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal Cmoment := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal hqxi) hK0.aestronglyMeasurable).trans ?_
    exact henvelope M hMY L N hLN
  have hmp := Section6Covariance.measurePreserving_translatePotentialSample M z
  let K := K0 ∘ translatePotentialSample z
  refine ⟨K, hK0.comp hmp.measurable, fun omega =>
    one_le_dirichletEllipticityEnvelope M L N _ _, ?_, ?_⟩
  · change eLpNorm (K0 ∘ translatePotentialSample z) _ _ ≤ _
    rw [eLpNorm_comp_measurePreserving hK0.aestronglyMeasurable hmp]
    exact hnorm0
  · exact hmp.quasiMeasurePreserving.ae hevent

end SubdiffusiveProcess.Static
