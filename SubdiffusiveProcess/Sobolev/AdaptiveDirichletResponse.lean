module

public import SubdiffusiveProcess.Sobolev.RootFoldConvolution
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.H1.Algebra.Membership
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
public import SubdiffusiveProcess.Sobolev.PartitionEnergy


@[expose] public section

/-! # Adaptive partition inequality for the Dirichlet response

The native zero-trace approximants give the local killed-graph carrier.
GMC's finite-family gluing theorem then joins the actual cell minimizers,
and the partition energy identity gives the primal subadditivity inequality.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess

/-- The value and gradient of a native zero-trace function lie in the killed graph. -/
theorem killed_of_nativeH10_local {d : ℕ} {U : Opens (SpatialCoordinates d)}
    (v : Homogenization.H10Function (U : Set (SpatialCoordinates d))) :
    let q : SobolevData U :=
      ((v.toH1Function.memL2).toLp v.toFun,
        fun i => (v.toH1Function.gradMemL2 i).toLp (fun x => v.grad x i))
    q ∈ killedSobolevGraph U := by
  let q : SobolevData U :=
    ((v.toH1Function.memL2).toLp v.toFun,
      fun i => (v.toH1Function.gradMemL2 i).toLp (fun x => v.grad x i))
  have hscalar : Tendsto (fun n => testL2 (extendTest (le_refl U) ⟨v.approx n,
      (v.approx_smooth n), (v.approx_hasCompactSupport n),
      (v.approx_support_subset n)⟩)) atTop
      (𝓝 q.1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have he : ∀ n, edist
        (testL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
          (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩)) q.1 =
        eLpNorm (fun x => v.approx n x - v.toFun x) 2
          (volume.restrict (U : Set (SpatialCoordinates d))) := by
      intro n
      rw [Lp.edist_def]
      refine (eLpNorm_congr_ae ?_).symm
      filter_upwards [testL2_coeFn (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩),
        Lp.coeFn_sub (testL2 (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩)) q.1,
        v.toH1Function.memL2.coeFn_toLp] with x hx hsub hq
      calc
        v.approx n x - v.toFun x =
            (testL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
              (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩) :
              SpatialCoordinates d → ℝ) x - q.1 x := by
                rw [hx, hq]
                rfl
        _ = ((testL2 (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩) - q.1) :
              SpatialCoordinates d → ℝ) x := by
                simp only [Pi.sub_apply]
    have hn : Tendsto (fun n =>
        ‖testL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
          (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩) - q.1‖)
        atTop (𝓝 0) := by
      have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
        v.tendsto_approx
      apply ht.congr'
      exact Filter.Eventually.of_forall (fun n => by
        have hh := congrArg ENNReal.toReal (he n)
        rw [edist_dist, dist_eq_norm] at hh
        simpa using hh.symm)
    exact hn
  have hgrad : ∀ i : Fin d, Tendsto (fun n =>
      testPartialL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
        (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩) i) atTop
        (𝓝 (q.2 i)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have he : ∀ n, edist
        (testPartialL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
          (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩) i) (q.2 i) =
        eLpNorm (fun x => (fderiv ℝ (v.approx n) x) (Homogenization.basisVec i) -
          v.grad x i) 2 (volume.restrict (U : Set (SpatialCoordinates d))) := by
      intro n
      rw [Lp.edist_def]
      refine (eLpNorm_congr_ae ?_).symm
      filter_upwards [testPartialL2_coeFn (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩) i,
        Lp.coeFn_sub (testPartialL2 (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩) i) (q.2 i),
        v.toH1Function.gradMemL2 i |>.coeFn_toLp] with x hx hsub hq
      calc
        (fderiv ℝ (v.approx n) x) (Homogenization.basisVec i) - v.grad x i =
            (testPartialL2 (extendTest (le_refl U) ⟨v.approx n,
              (v.approx_smooth n), (v.approx_hasCompactSupport n),
              (v.approx_support_subset n)⟩) i :
              SpatialCoordinates d → ℝ) x - q.2 i x := by
                rw [hx, hq]
                rfl
        _ = ((testPartialL2 (extendTest (le_refl U) ⟨v.approx n,
          (v.approx_smooth n), (v.approx_hasCompactSupport n),
          (v.approx_support_subset n)⟩) i - q.2 i) :
              SpatialCoordinates d → ℝ) x := by
                simp only [Pi.sub_apply]
    have hn : Tendsto (fun n =>
        ‖testPartialL2 (extendTest (le_refl U) ⟨v.approx n, (v.approx_smooth n),
          (v.approx_hasCompactSupport n), (v.approx_support_subset n)⟩) i - q.2 i‖)
        atTop (𝓝 0) := by
      have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
        (v.tendsto_approx_grad i)
      apply ht.congr'
      exact Filter.Eventually.of_forall (fun n => by
        have hh := congrArg ENNReal.toReal (he n)
        rw [edist_dist, dist_eq_norm] at hh
        simpa using hh.symm)
    exact hn
  dsimp [q]
  change (v.toH1Function.memL2.toLp v.toFun,
      fun i => (v.toH1Function.gradMemL2 i).toLp (fun x => v.grad x i)) ∈
    closure ((LinearMap.range (smoothSobolevDataLinear (Ω := U))) :
      Set (SobolevData U))
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => smoothSobolevData (extendTest (le_refl U) ⟨v.approx n,
    (v.approx_smooth n), (v.approx_hasCompactSupport n),
    (v.approx_support_subset n)⟩), ?_, ?_⟩
  · intro n
    exact ⟨⟨v.approx n, (v.approx_smooth n), (v.approx_hasCompactSupport n),
      (v.approx_support_subset n)⟩, rfl⟩
  · simpa only [smoothSobolevData, q, nhds_prod_eq] using
      hscalar.prodMk (tendsto_pi_nhds.2 hgrad)

end SubdiffusiveProcess

namespace SubdiffusiveProcess

/-- Gluing the actual cell minimizers bounds the root affine Dirichlet response. -/
theorem triadicAdaptive_affineDirichletResponse_le_sum
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ)
    (hD0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hD : ∀ n (k : OddGridIndex d (triadicHalf n)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf n) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf n) k)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (oddGridCell z r hr (triadicHalf n) k)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (p : Fin d → ℝ) :
    affineDirichletResponse (centeredCube_isBounded z hr) hD0 a p ≤
      ∑ t ∈ triadicAdaptiveLabels I J,
        affineDirichletResponse (triadicAdaptiveCell_isBounded z hr J t)
          (triadicAdaptiveCell_killedPoincare z hr hD J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
  classical
  let Ω := centeredCube z r hr
  let S := triadicAdaptiveLabels I J
  let q : TriadicAdaptiveIndex d J → Opens (SpatialCoordinates d) :=
    triadicAdaptiveCell z r hr J
  let hq : ∀ t, q t ≤ Ω := fun t => triadicAdaptiveCell_subset_root z hr J t
  let hΩ := centeredCube_isBounded z hr
  have hqmeas : ∀ t, MeasurableSet (q t : Set (SpatialCoordinates d)) :=
    fun t => (q t).isOpen.measurableSet
  have hmin' : ∀ t, ∃ u : killedSobolevGraph (q t),
      t ∈ S →
        (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          (positiveCoefficientRestrict (hq t) a).val x *
            (p i + (u : SobolevData (q t)).2 i x) ^ 2) =
          affineDirichletResponse (triadicAdaptiveCell_isBounded z hr J t)
            (triadicAdaptiveCell_killedPoincare z hr hD J t)
            (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨u, hu⟩ := (affineDirichletResponse_isLeast
          (triadicAdaptiveCell_isBounded z hr J t)
          (triadicAdaptiveCell_killedPoincare z hr hD J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p).1
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose u hu using hmin'
  have hnative : ∀ t, ∃ v : Homogenization.H10Function (q t : Set (SpatialCoordinates d)),
      (v : SpatialCoordinates d → ℝ) = (fun x => (u t).val.1 x) ∧
      v.toH1Function.grad = (fun x i => (u t).val.2 i x) := by
    intro t
    exact exists_nativeH10Function_of_killedSobolevGraph (u t)
  choose v hvval hvgrad using hnative
  obtain ⟨W, hW⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_h10Function_grad_eq_sum_indicator
      (U := (Ω : Set (SpatialCoordinates d)))
      Ω.isOpen S hqmeas hq v
  have hsum (t : TriadicAdaptiveIndex d J) (ht : t ∈ S)
      {x : SpatialCoordinates d} (hx : x ∈ (q t : Set (SpatialCoordinates d))) :
      ∑ s ∈ S, Set.indicator (q s : Set (SpatialCoordinates d))
          (fun y => (v s).toH1Function.grad y) x = (v t).toH1Function.grad x := by
    refine (Finset.sum_eq_single t ?_ (fun h => absurd ht h)).trans
      (Set.indicator_of_mem hx _)
    intro s hs hst
    refine Set.indicator_of_notMem (fun hmem => ?_) _
    have hdisj := (triadicAdaptiveCells_pairwiseDisjoint z hr I J) ht hs hst.symm
    exact Set.disjoint_left.mp hdisj hx hmem
  have hrootcoe (i : Fin d) :
      ((W.toH1Function.gradMemL2 i).toLp (fun x => W.toH1Function.grad x i) :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          fun x => W.toH1Function.grad x i :=
    (W.toH1Function.gradMemL2 i).coeFn_toLp
  let Q : killedSobolevGraph Ω :=
    ⟨((W.toH1Function.memL2).toLp W.toFun,
      fun i => (W.toH1Function.gradMemL2 i).toLp
        (fun x => W.toH1Function.grad x i)), by
      simpa using (killed_of_nativeH10_local W)⟩
  have hcellgrad (t : TriadicAdaptiveIndex d J) (ht : t ∈ S) (i : Fin d) :
      ∀ᵐ x ∂volume.restrict (q t : Set (SpatialCoordinates d)),
        (Q : SobolevData Ω).2 i x = (u t : SobolevData (q t)).2 i x := by
    have hroot := ae_restrict_of_ae_restrict_of_subset (hq t) (hrootcoe i)
    filter_upwards [hroot, ae_restrict_mem (hqmeas t)] with x hxroot hxmem
    rw [hxroot, hW x, hsum t ht hxmem]
    exact congrArg (fun f => f x i) (hvgrad t)
  let g : HilbertGradient Ω :=
    sobolevGradient (affineSobolevData hΩ p 0 + (Q : SobolevData Ω))
  have hgaff (i : Fin d) :
      (g i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => p i + (Q : SobolevData Ω).2 i x := by
    filter_upwards [domainConstantL2_coeFn (Ω := Ω) (p i),
      Lp.coeFn_add (domainConstantL2 (Ω := Ω) (p i)) ((Q : SobolevData Ω).2 i)]
      with x hx hpq
    change (domainConstantL2 (Ω := Ω) (p i) + (Q : SobolevData Ω).2 i) x = _
    rw [hpq]
    simpa only [Pi.add_apply] using congrArg
      (fun y => y + (Q : SobolevData Ω).2 i x) hx
  have hglocal (t : TriadicAdaptiveIndex d J) (ht : t ∈ S) (i : Fin d) :
      ∀ᵐ x ∂volume.restrict (q t : Set (SpatialCoordinates d)),
        (domainGradientRestrict (hq t) g i) x =
          p i + (u t : SobolevData (q t)).2 i x := by
    have hga := ae_restrict_of_ae_restrict_of_subset (hq t) (hgaff i)
    have hgr := domainGradientRestrict_coeFn (hq t) g i
    filter_upwards [hga, hgr, hcellgrad t ht i] with x hga hgr hcell
    rw [hgr, hga, hcell]
  have hlocalform (t : TriadicAdaptiveIndex d J) (ht : t ∈ S) :
      (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          (positiveCoefficientRestrict (hq t) a).val x *
            (p i + (u t : SobolevData (q t)).2 i x) ^ 2) =
        weightedGradientForm (positiveCoefficientRestrict (hq t) a).val
          (domainGradientRestrict (hq t) g) (domainGradientRestrict (hq t) g) := by
    rw [weightedGradientForm_apply]
    apply (Finset.sum_congr rfl)
    intro i hi
    apply integral_congr_ae
    filter_upwards [positiveCoefficientRestrict_coeFn (hq t) a,
      hglocal t ht i] with x ha hg
    rw [ha, hg, pow_two]
  have hrootform :
      weightedGradientForm a.val g g =
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + (Q : SobolevData Ω).2 i x) ^ 2 := by
    rw [weightedGradientForm_apply]
    apply (Finset.sum_congr rfl)
    intro i hi
    apply integral_congr_ae
    filter_upwards [hgaff i] with x hg
    rw [hg, pow_two]
  have hsumenergy :
      (∑ t ∈ S,
        (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          (positiveCoefficientRestrict (hq t) a).val x *
            (p i + (u t : SobolevData (q t)).2 i x) ^ 2)) =
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + (Q : SobolevData Ω).2 i x) ^ 2 := by
    calc
      _ = ∑ t ∈ S,
          weightedGradientForm (positiveCoefficientRestrict (hq t) a).val
            (domainGradientRestrict (hq t) g) (domainGradientRestrict (hq t) g) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hlocalform t ht
      _ = weightedGradientForm a.val g g := by
        simpa [S, q, hq] using weightedGradientForm_triadicAdaptiveCells z hr hI J a g g
      _ = _ := hrootform
  have hrootleast := affineDirichletResponse_isLeast
    (centeredCube_isBounded z hr) hD0 a p
  have hrootle := hrootleast.2 (Set.mem_range_self Q)
  calc
    affineDirichletResponse (centeredCube_isBounded z hr) hD0 a p ≤
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * (p i + (Q : SobolevData Ω).2 i x) ^ 2 := hrootle
    _ = ∑ t ∈ S,
        (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          (positiveCoefficientRestrict (hq t) a).val x *
            (p i + (u t : SobolevData (q t)).2 i x) ^ 2) := hsumenergy.symm
    _ = ∑ t ∈ S,
        affineDirichletResponse (triadicAdaptiveCell_isBounded z hr J t)
          (triadicAdaptiveCell_killedPoincare z hr hD J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hu t ht
    _ = _ := by rfl

end SubdiffusiveProcess
