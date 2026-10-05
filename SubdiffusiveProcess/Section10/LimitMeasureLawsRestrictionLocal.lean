module

public import SubdiffusiveProcess.Section10.LimitMeasureLawsLocality
public import SubdiffusiveProcess.MultiplicativeChaos.VagueMeasurable
public import Mathlib.Probability.Kernel.Condexp

@[expose] public section

/-!
# Local representatives of masses of the same chaos limit

The existing countable supported Urysohn tests determine open masses. The
existing conditional kernel supplies a measure-valued version of the actual
restriction; its diagonal-law identity fixes every locally measurable scalar
representative. No new vague topology or Riesz representation is introduced.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology
open scoped CompactlySupported ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The existing supported positive test family determines the mass of an
open set for every Borel measure, including infinite mass. -/
theorem open_mass_eq_iSup_positive_tests {d : ℕ}
    (mu : Measure (SpatialCoordinates d)) (O : Set (SpatialCoordinates d)) (hO : IsOpen O)
    (f : ℕ → C_c(SpatialCoordinates d, ℝ))
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (hK : ∀ n x, x ∈ openPiece O n → f n x = 1)
    (hs : ∀ n, tsupport (f n : SpatialCoordinates d → ℝ) ⊆ O) :
    mu O = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂mu := by
  refine le_antisymm ?_ ?_
  · rw [← iUnion_openPiece hO, (monotone_openPiece O).measure_iUnion]
    refine iSup_le fun n => le_iSup_of_le n ?_
    calc
      mu (openPiece O n) = ∫⁻ x, (openPiece O n).indicator (fun _ => (1 : ℝ≥0∞)) x ∂mu := by
        rw [lintegral_indicator (isClosed_openPiece O n).measurableSet]
        simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f n x) ∂mu := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ openPiece O n
        · simp only [Set.indicator_of_mem hx, hK n x hx, ENNReal.ofReal_one, le_refl]
        · simp only [Set.indicator_of_notMem hx]
          exact bot_le
  · refine iSup_le fun n => ?_
    calc
      (∫⁻ x, ENNReal.ofReal (f n x) ∂mu) ≤
          ∫⁻ x, O.indicator (fun _ => (1 : ℝ≥0∞)) x ∂mu := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ O
        · simp only [Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_one.mpr (hf n x).2
        · have hz : f n x = 0 := by
            by_contra hn
            exact hx (hs n (subset_closure hn))
          simp only [Set.indicator_of_notMem hx, hz, ENNReal.ofReal_zero, le_refl]
      _ = mu O := by
        rw [lintegral_indicator hO.measurableSet]
        simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]

/-- Open mass evaluations of the same actual limit have local scalar
representatives. Unbounded open regions are included by the existing countable
compact exhaustion; no continuity of Borel restriction is used. -/
theorem same_limit_open_mass_local {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w))
    (U O : Set (SpatialCoordinates d)) (hU : IsOpen U) (hO : IsOpen O) :
    ∃ g : BilateralField d → ℝ≥0∞,
      @Measurable (BilateralField d) ℝ≥0∞ (fineSpatialSigma U) (borel ℝ≥0∞) g ∧
      g =ᵐ[(chaosSampleLaw M).toMeasure] fun w => (mu0 w).restrict U O := by
  classical
  let W := O ∩ U
  have hW : IsOpen W := hO.inter hU
  choose f hf hK hs using fun n => exists_urysohn_openPiece hW n
  let g : BilateralField d → ℝ≥0∞ := fun w => ⨆ n, localPositiveTestLimit M W (f n) w
  refine ⟨g, Measurable.iSup (fun n =>
    (measurable_local_positive_test_limit M W hW.measurableSet (f n)).mono
      (fine_spatial_sigma_mono Set.inter_subset_right) le_rfl), ?_⟩
  have heq : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ n,
      localPositiveTestLimit M W (f n) w =
        ∫⁻ x, ENNReal.ofReal (f n x) ∂(mu0 w).restrict W := by
    rw [ae_all_iff]
    intro n
    exact same_chaos_limit_positive_test_local M mu0 hl hc W hW.measurableSet
      (f n) (fun x => (hf n x).1) ((subset_closure).trans (hs n))
  filter_upwards [heq] with w hw
  calc
    g w = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂(mu0 w).restrict W := iSup_congr hw
    _ = (mu0 w).restrict W W :=
      (open_mass_eq_iSup_positive_tests _ W hW f hf hK hs).symm
    _ = (mu0 w).restrict U O := by
      rw [Measure.restrict_apply_self, Measure.restrict_apply hO.measurableSet]

/-- A conditional kernel fixes a scalar map with an AE locally measurable
representative. This standard-axiom helper uses the supplied measure and its
existing conditional kernel, with no integrability or moment assumption. -/
theorem conditional_kernel_local_lintegral_ae
    {Omega : Type*} (m : MeasurableSpace Omega)
    [m0 : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P]
    (hm : m ≤ m0)
    (f g : Omega → ℝ≥0∞) (hg : @Measurable Omega ℝ≥0∞ m _ g)
    (hfg : f =ᵐ[P] g) :
    (fun w => ∫⁻ v, f v ∂condExpKernel P m w) =ᵐ[P] f := by
  have hgm : Measurable g := hg.mono hm le_rfl
  have hpair : @Measurable Omega (Omega × Omega) m0 (m.prod m0)
      (fun w => (id w, id w)) := (measurable_id'' hm).prodMk measurable_id
  have hdiag : @MeasurableSet (Omega × Omega) (m.prod m0) {p | g p.2 = g p.1} :=
    measurableSet_eq_fun (hgm.comp measurable_snd) (hg.comp measurable_fst)
  have hd : ∀ᵐ p ∂(P.trim hm) ⊗ₘ condExpKernel P m, g p.2 = g p.1 := by
    let : MeasurableSpace (Omega × Omega) := m.prod m0
    rw [compProd_trim_condExpKernel hm]
    exact (ae_map_iff hpair.aemeasurable hdiag).mpr (ae_of_all _ (fun _ => rfl))
  have he : ∀ᵐ w ∂P.trim hm, f =ᵐ[condExpKernel P m w] g := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hfg
  filter_upwards [ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hd),
    ae_of_ae_trim hm he, hfg] with w hdw hew hfgw
  calc
    (∫⁻ v, f v ∂condExpKernel P m w) = ∫⁻ _v, g w ∂condExpKernel P m w :=
      lintegral_congr_ae (hew.trans hdw)
    _ = g w := by simp only [lintegral_const, measure_univ, mul_one]
    _ = f w := hfgw.symm

end SubdiffusiveProcess.Section10
