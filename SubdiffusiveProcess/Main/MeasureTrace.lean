import SubdiffusiveProcess.Analysis.GlobalTriadicCongruence
import SubdiffusiveProcess.Geometry.CubeSupportInterior
import SubdiffusiveProcess.Analysis.GlobalTriadicNormBound
import SubdiffusiveProcess.Analysis.ScalarHalfFractionalKernel
import SubdiffusiveProcess.Analysis.GlobalTriadicSubtraction
import SubdiffusiveProcess.Analysis.GlobalTriadicLimitIdentification
import SubdiffusiveProcess.Sobolev.MeasureTraceSmoothDensity
import SubdiffusiveProcess.Sobolev.MeasureTraceUniqueness

open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess

theorem exists_unique_measureTrace :
  ∀ {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
      (hr : 0 < Homogenization.cubeScaleFactor Q) (t : ℝ),
    (d : ℝ) - 1 < t →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ν : Measure (SpatialCoordinates d)) (K : ℝ),
        ν Set.univ < (⊤ : ℝ≥0∞) →
        ν (closure (Homogenization.openCubeSet Q))ᶜ = 0 →
        0 ≤ K →
        (∀ x ∈ closure (Homogenization.openCubeSet Q),
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            ν (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t)) →
        ∃! T : CubeFractionalL2 (k := 1) hd
            (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
            halfFractionalOrder → Lp ℝ 2 ν,
          MeasureTraceCharacterization hd Q hr ν K C T
 := by
  classical
  intro d hd Q hr t ht
  let traceAverage {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
      (f : SpatialCoordinates d → ℝ) (n : ℕ) (x : SpatialCoordinates d) : ℝ :=
    ∑ k : OddGridIndex d (triadicHalf n),
      (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) f) x

  have exists_traceCandidate
      {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
      (hr : 0 < cubeScaleFactor Q)
      (t : ℝ) (ht : (d : ℝ) - 1 < t) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : Measure (SpatialCoordinates d)) (K : ℝ),
        ν univ < ⊤ → ν (closure (openCubeSet Q))ᶜ = 0 → 0 ≤ K →
        (∀ x ∈ closure (openCubeSet Q), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t)) →
        ∃ T : CubeFractionalL2 (k := 1) hd (cubeCenter Q) (cubeScaleFactor Q) hr
            halfFractionalOrder → Lp ℝ 2 ν,
          ∀ u : CubeFractionalL2 (k := 1) hd (cubeCenter Q) (cubeScaleFactor Q) hr
              halfFractionalOrder,
            Tendsto (fun n => eLpNorm
              (fun x => traceAverage (cubeCenter Q) hr (u.val 0) n x - (T u) x) 2 ν)
              atTop (nhds 0) ∧
            ‖T u‖ ^ 2 ≤ C * (K + (ν (closure (openCubeSet Q))).toReal) *
              (cubeFractionalL2Norm hd (cubeCenter Q) (cubeScaleFactor Q) hr
                halfFractionalOrder u) ^ 2 := by
    classical
    let z := cubeCenter Q
    let r := cubeScaleFactor Q
    let A := CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder
    have hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        closure (openCubeSet Q) := by
      rw [centeredCube_eq_openCubeSet Q hr]
      exact subset_closure
    obtain ⟨C, hC, hbound⟩ :=
      globalTriadicAverages_L2_limit_norm_bound hd Q z hr hroot t ht
    refine ⟨C, hC, ?_⟩
    intro ν K hν hsupp hK hgrowth
    letI : IsFiniteMeasure ν := ⟨hν⟩
    have hf (u : A) : MemLp (u.val 0) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      Lp.memLp (u.val 0)
    have hE (u : A) : ∀ n, MemLp (traceAverage z hr (u.val 0) n) 2 ν :=
      (globalTriadicAverages_memLp_and_increment_bound hd Q z hr hroot K t hK ht
        0 ν inferInstance hsupp hgrowth (u.val 0) (hf u)).1
    have hlim (u : A) : ∃ g : SpatialCoordinates d → ℝ, MemLp g 2 ν ∧
        Tendsto (fun n => eLpNorm
          (fun x => traceAverage z hr (u.val 0) n x - g x) 2 ν) atTop (nhds 0) := by
      have hsum := globalTriadicAverages_summable_increment_eLpNorm_of_finite_kernel
        hd Q z hr hroot K t hK ht ν inferInstance hsupp hgrowth (u.val 0) (hf u)
        (scalar_halfFractional_kernel_lt_top hd z r hr u).ne
      exact globalTriadicAverages_exists_L2_limit_of_summable_increments
        z hr ν (u.val 0) (hE u) hsum
    choose g hg hgt using hlim
    let T : A → Lp ℝ 2 ν := fun u => (hg u).toLp (g u)
    refine ⟨T, ?_⟩
    intro u
    constructor
    · have heq : (fun n => eLpNorm
            (fun x => traceAverage z hr (u.val 0) n x - (T u) x) 2 ν) =
          (fun n => eLpNorm
            (fun x => traceAverage z hr (u.val 0) n x - g u x) 2 ν) := by
        funext n
        apply eLpNorm_congr_ae
        filter_upwards [(hg u).coeFn_toLp] with x hx
        simp only [T, hx]
      rw [heq]
      exact hgt u
    · rw [show ‖T u‖ = (eLpNorm (g u) 2 ν).toReal from Lp.norm_toLp _ _]
      exact hbound K hK ν inferInstance hsupp hgrowth u (hf u)
        (scalar_halfFractional_kernel_lt_top hd z r hr u).ne (hE u) (g u) (hg u) (hgt u)
  obtain ⟨C, hC, hCandidate⟩ := exists_traceCandidate hd Q hr t ht
  refine ⟨C, hC, ?_⟩
  intro ν K hν hsupp hK hgrowth
  letI : IsFiniteMeasure ν := ⟨hν⟩
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let z := cubeCenter Q
  let r := cubeScaleFactor Q
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let A := CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder
  obtain ⟨T, hT⟩ := hCandidate ν K hν hsupp hK hgrowth
  let E (u : A) := traceAverage z hr (u.val 0)
  have hroot : U ⊆ closure (openCubeSet Q) := by
    change (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ _
    rw [centeredCube_eq_openCubeSet Q hr]
    exact subset_closure
  have hf (u : A) : MemLp (u.val 0) 2 (volume.restrict U) := Lp.memLp _
  have hE (u : A) : ∀ n, MemLp (E u n) 2 ν :=
    (globalTriadicAverages_memLp_and_increment_bound hd Q z hr hroot K t hK ht
      0 ν inferInstance hsupp hgrowth (u.val 0) (hf u)).1
  let V (u : A) (n : ℕ) : Lp ℝ 2 ν := (hE u n).toLp (E u n)
  have hlp (u : A) : Tendsto (V u) atTop (nhds (T u)) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (E u) (hE u)
      (T u : SpatialCoordinates d → ℝ) (Lp.memLp (T u))).mpr (hT u).1
    simpa only [Lp.toLp_coeFn, V] using h
  have hsub (u v w : A) (hw : w.val 0 = u.val 0 - v.val 0) :
      T w = T u - T v := by
    have hfg : (w.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U]
        (fun x => u.val 0 x - v.val 0 x) := by
      rw [hw]
      exact Lp.coeFn_sub _ _
    have heq (n : ℕ) : E w n = fun x => E u n x - E v n x := by
      calc
        E w n = traceAverage z hr (fun x => u.val 0 x - v.val 0 x) n :=
          globalTriadicAverages_congr_ae z hr n (w.val 0) _ hfg
        _ = fun x => E u n x - E v n x :=
          globalTriadicAverages_sub z hr n (u.val 0) (v.val 0)
            ((hf u).integrable (by norm_num)) ((hf v).integrable (by norm_num))
    have heqlp (n : ℕ) : V w n = V u n - V v n := by
      calc
        V w n = ((hE u n).sub (hE v n)).toLp (E u n - E v n) :=
          (hE w n).toLp_congr _ (Filter.Eventually.of_forall (congrFun (heq n)))
        _ = V u n - V v n := (hE u n).toLp_sub (hE v n)
    apply tendsto_nhds_unique (hlp w)
    have hseq : V w = fun n => V u n - V v n := funext heqlp
    rw [hseq]
    exact (hlp u).sub (hlp v)
  have hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0 :=
    (growth_cube_boundary_noAtoms hd Q ν inferInstance K t hK ht hsupp hgrowth).1
  have hsuppU : ν (closure U)ᶜ = 0 := by
    dsimp only [U]
    rw [centeredCube_eq_openCubeSet Q hr]
    exact hsupp
  have hUae : ∀ᵐ x ∂ν, x ∈ U :=
    ae_mem_centeredCube_of_support_closure_of_hyperplanes_null z hr ν hsuppU hplanes
  have hchar : MeasureTraceCharacterization hd Q hr ν K C T := by
    refine ⟨?_, ?_, ?_⟩
    · intro u v
      refine ⟨⟨fun i => u.val i - v.val i,
        cubeFractionalL2Seminorm_sub_lt_top hd z r hr halfFractionalOrder
          u.val v.val u.property v.property⟩, rfl⟩
    · intro u v w hw
      rw [← hsub u v w hw]
      exact (hT w).2
    · intro f hfcont v hvf hfν
      have heq (n : ℕ) : traceAverage z hr f n = E v n :=
        (globalTriadicAverages_congr_ae z hr n (v.val 0) f hvf).symm
      have hEf : ∀ n, MemLp (traceAverage z hr f n) 2 ν := by
        intro n
        rw [heq n]
        exact hE v n
      have hlim : Tendsto (fun n => eLpNorm
          (fun x => traceAverage z hr f n x - (T v) x) 2 ν) atTop (nhds 0) := by
        simpa only [heq] using (hT v).1
      have hae : (T v : SpatialCoordinates d → ℝ) =ᵐ[ν] U.indicator f :=
        globalTriadicAverages_L2_limit_eq_ae_indicator_of_continuousOn
          hd z hr ν hplanes f hfcont.continuous.continuousOn
          (T v) hEf (Lp.memLp (T v)) hlim
      apply Lp.ext
      filter_upwards [hae, hUae, hfν.coeFn_toLp] with x hx hxU hxf
      rw [hx, Set.indicator_of_mem hxU, hxf]
  refine ⟨T, hchar, ?_⟩
  intro T' hT'
  exact measureTrace_unique_of_smoothDensity hd Q hr ν K C T' T hT' hchar
    (fun u => measureTrace_hdense_of_finiteMeasure_supported hd Q hr ν hsupp u)

end SubdiffusiveProcess
