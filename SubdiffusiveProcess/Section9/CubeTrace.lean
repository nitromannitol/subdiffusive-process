import SubdiffusiveProcess.Main.MeasureTrace

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Section9

def CubeTraceCharacterization {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder → Lp ℝ 2 ν) : Prop :=
  (∀ u v : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder,
    ∃ w : CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder,
      w.val 0 = u.val 0 - v.val 0) ∧
  (∀ (u v w : CubeFractionalL2 (k := 1) hd z
      r hr halfFractionalOrder),
    w.val 0 = u.val 0 - v.val 0 →
    ‖T u - T v‖ ^ 2 ≤
      C * (K + (ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
        (cubeFractionalL2Norm hd z
          r hr halfFractionalOrder w) ^ 2) ∧
  ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
    ∀ (v : CubeFractionalL2 (k := 1) hd z
        r hr halfFractionalOrder),
      (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z
            r hr : Set (SpatialCoordinates d))] f →
      ∀ hf : MemLp f 2 ν, T v = hf.toLp f


/-- Completed half-order trace on an arbitrary centred cube contained in a growth root. -/
theorem exists_cubeTrace_of_growth {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closure (openCubeSet Q))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : Measure (SpatialCoordinates d)) (K : ℝ),
      ν Set.univ < ⊤ → ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
      0 ≤ K →
      (∀ x ∈ closure (openCubeSet Q), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t)) →
      ∃ T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 ν,
        CubeTraceCharacterization hd z hr ν K C T := by
  classical
  let traceAverage (f : SpatialCoordinates d → ℝ) (n : ℕ) (x : SpatialCoordinates d) : ℝ :=
    ∑ k : OddGridIndex d (triadicHalf n),
      (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) f) x
  obtain ⟨C, hC, hbound⟩ := globalTriadicAverages_L2_limit_norm_bound hd Q z hr hroot t ht
  refine ⟨C, hC, ?_⟩
  intro ν K hν hsuppU hK hgrowth
  letI : IsFiniteMeasure ν := ⟨hν⟩
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let A := CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder
  have hsupp : ν (closure (openCubeSet Q))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (closure_minimal hroot isClosed_closure)) hsuppU
  have hmass : ν (closure (openCubeSet Q)) = ν (closure U) :=
    (measure_of_measure_compl_eq_zero hsupp).trans (measure_of_measure_compl_eq_zero hsuppU).symm
  have hf (u : A) : MemLp (u.val 0) 2 (volume.restrict U) := Lp.memLp _
  have hE (u : A) : ∀ n, MemLp (traceAverage (u.val 0) n) 2 ν :=
    (globalTriadicAverages_memLp_and_increment_bound hd Q z hr hroot K t hK ht
      0 ν inferInstance hsupp hgrowth (u.val 0) (hf u)).1
  have hlim (u : A) : ∃ g : SpatialCoordinates d → ℝ, MemLp g 2 ν ∧
      Tendsto (fun n => eLpNorm
        (fun x => traceAverage (u.val 0) n x - g x) 2 ν) atTop (nhds 0) := by
    have hsum := globalTriadicAverages_summable_increment_eLpNorm_of_finite_kernel
      hd Q z hr hroot K t hK ht ν inferInstance hsupp hgrowth (u.val 0) (hf u)
      (scalar_halfFractional_kernel_lt_top hd z r hr u).ne
    exact globalTriadicAverages_exists_L2_limit_of_summable_increments
      z hr ν (u.val 0) (hE u) hsum
  choose g hg hgt using hlim
  let T : A → Lp ℝ 2 ν := fun u => (hg u).toLp (g u)
  have hT : ∀ u : A,
      Tendsto (fun n => eLpNorm
        (fun x => traceAverage (u.val 0) n x - (T u) x) 2 ν) atTop (nhds 0) ∧
      ‖T u‖ ^ 2 ≤ C * (K + (ν (closure U)).toReal) *
        (cubeFractionalL2Norm hd z r hr halfFractionalOrder u) ^ 2 := by
    intro u
    constructor
    · have heq : (fun n => eLpNorm
          (fun x => traceAverage (u.val 0) n x - (T u) x) 2 ν) =
          (fun n => eLpNorm (fun x => traceAverage (u.val 0) n x - g u x) 2 ν) := by
        funext n
        apply eLpNorm_congr_ae
        filter_upwards [(hg u).coeFn_toLp] with x hx
        simp only [T, hx]
      rw [heq]
      exact hgt u
    · rw [show ‖T u‖ = (eLpNorm (g u) 2 ν).toReal from Lp.norm_toLp _ _]
      have hb := hbound K hK ν inferInstance hsupp hgrowth u (hf u)
        (scalar_halfFractional_kernel_lt_top hd z r hr u).ne (hE u) (g u) (hg u) (hgt u)
      rwa [hmass] at hb
  let E (u : A) := traceAverage (u.val 0)
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
        E w n = traceAverage (fun x => u.val 0 x - v.val 0 x) n :=
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
  have hUae : ∀ᵐ x ∂ν, x ∈ U :=
    ae_mem_centeredCube_of_support_closure_of_hyperplanes_null z hr ν hsuppU hplanes
  have hchar : CubeTraceCharacterization hd z hr ν K C T := by
    refine ⟨?_, ?_, ?_⟩
    · intro u v
      refine ⟨⟨fun i => u.val i - v.val i,
        cubeFractionalL2Seminorm_sub_lt_top hd z r hr halfFractionalOrder
          u.val v.val u.property v.property⟩, rfl⟩
    · intro u v w hw
      rw [← hsub u v w hw]
      exact (hT w).2
    · intro f hfcont v hvf hfν
      have heq (n : ℕ) : traceAverage f n = E v n :=
        (globalTriadicAverages_congr_ae z hr n (v.val 0) f hvf).symm
      have hEf : ∀ n, MemLp (traceAverage f n) 2 ν := by
        intro n
        rw [heq n]
        exact hE v n
      have hlim : Tendsto (fun n => eLpNorm
          (fun x => traceAverage f n x - (T v) x) 2 ν) atTop (nhds 0) := by
        simpa only [heq] using (hT v).1
      have hae : (T v : SpatialCoordinates d → ℝ) =ᵐ[ν] U.indicator f :=
        globalTriadicAverages_L2_limit_eq_ae_indicator_of_continuousOn
          hd z hr ν hplanes f hfcont.continuous.continuousOn
          (T v) hEf (Lp.memLp (T v)) hlim
      apply Lp.ext
      filter_upwards [hae, hUae, hfν.coeFn_toLp] with x hx hxU hxf
      rw [hx, Set.indicator_of_mem hxU, hxf]
  exact ⟨T, hchar⟩

end SubdiffusiveProcess.Section9
