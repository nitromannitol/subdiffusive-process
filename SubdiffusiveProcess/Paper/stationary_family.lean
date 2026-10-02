import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PointwiseRangeDependence
import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionIndependence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

theorem aux_stationary_family_scaled_layer
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (hν : ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x : SpatialCoordinates d => x + z,
          continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
      ν.toMeasure ν.toMeasure) :
    ∀ (j : ℤ) (z : SpatialCoordinates d), MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x : SpatialCoordinates d => x + z,
          continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
      (scaledLayerLaw d ν j).toMeasure (scaledLayerLaw d ν j).toMeasure := by
  intro j z
  let trans : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => x + z, continuous_id.add continuous_const⟩
  let scaled : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ (-j) • x, continuous_const.smul continuous_id⟩
  let shifted : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => x + ((3 : ℝ) ^ (-j) • z), continuous_id.add continuous_const⟩
  let T : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ trans
  let S : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ scaled
  let U : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ shifted
  have hcomp : T ∘ S = S ∘ U := by
    funext f
    ext x
    dsimp [T, S, U, trans, scaled, shifted]
    rw [smul_add]
  have hT : Measurable T := T.continuous.measurable
  have hS : Measurable S := S.continuous.measurable
  have hU : Measurable U := U.continuous.measurable
  change MeasurePreserving T
    (Measure.map S ν.toMeasure) (Measure.map S ν.toMeasure)
  refine ⟨hT, ?_⟩
  rw [Measure.map_map hT hS, hcomp, ← Measure.map_map hS hU]
  change Measure.map S
    (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp shifted) ν.toMeasure) =
    Measure.map S ν.toMeasure
  rw [(hν ((3 : ℝ) ^ (-j) • z)).map_eq]

theorem aux_stationary_family_product_stationary
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (hlayer : ∀ (j : ℤ) (z : SpatialCoordinates d), MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x : SpatialCoordinates d => x + z,
          continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
      (scaledLayerLaw d ν j).toMeasure (scaledLayerLaw d ν j).toMeasure) :
    ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun omega : BilateralField d => fun j : ℤ =>
        (omega j).comp (⟨fun x : SpatialCoordinates d => x + z,
          continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
      (commonScaleLaw d ν).toMeasure (commonScaleLaw d ν).toMeasure := by
  intro z
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let trans : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => x + z, continuous_id.add continuous_const⟩
  let T : BilateralField d → BilateralField d := fun omega j =>
    (omega j).comp trans
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro j
    exact (ContinuousMap.compRightContinuousMap ℝ trans).continuous.measurable.comp
      (measurable_pi_apply j)
  change MeasurePreserving T (Measure.infinitePi laws) (Measure.infinitePi laws)
  refine ⟨hT, ?_⟩
  rw [Measure.infinitePi_map_pi (μ := laws)
    (f := fun j : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp trans)
    (fun _ => (ContinuousMap.compRightContinuousMap ℝ trans).continuous.measurable)]
  congr 1
  funext j
  exact (hlayer j z).map_eq

theorem aux_stationary_family_relabelled_coordinate
    (d N : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (i : Fin (N + 1)) :
    IdentDistrib
      (fun omega : BilateralField d => omega (-(i : ℤ)))
      (fun omega : BilateralField d =>
        ContinuousMap.compRightContinuousMap ℝ
          (⟨fun y : SpatialCoordinates d => (3 : ℝ) ^ N • y,
            continuous_const.smul continuous_id⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
          (omega ((N : ℤ) - (i : ℤ))))
      (commonScaleLaw d ν).toMeasure (commonScaleLaw d ν).toMeasure := by
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let dilationMap : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun y => (3 : ℝ) ^ N • y, continuous_const.smul continuous_id⟩
  let dilate : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ dilationMap
  let k : ℤ := (N : ℤ) - (i : ℤ)
  let hleft : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun omega => omega (-(i : ℤ))
  let hright : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun omega => dilate (omega k)
  have hleft_meas : Measurable hleft := measurable_pi_apply _
  have hright_meas : Measurable hright := by
    exact (dilate.continuous.measurable.comp (measurable_pi_apply k))
  have hleft_map :
      Measure.map hleft (commonScaleLaw d ν).toMeasure = laws (-(i : ℤ)) := by
    change Measure.map (fun omega : BilateralField d => omega (-(i : ℤ)))
        (Measure.infinitePi laws) = laws (-(i : ℤ))
    exact measurePreserving_eval_infinitePi laws (-(i : ℤ)) |>.map_eq
  have hright_map :
      Measure.map hright (commonScaleLaw d ν).toMeasure = laws (-(i : ℤ)) := by
    change Measure.map hright (Measure.infinitePi laws) = laws (-(i : ℤ))
    calc
      Measure.map hright (Measure.infinitePi laws) =
            Measure.map dilate (Measure.map (fun omega : BilateralField d => omega k)
            (Measure.infinitePi laws)) := by
              change Measure.map (dilate ∘ (fun omega : BilateralField d => omega k))
                  (Measure.infinitePi laws) = _
              rw [Measure.map_map dilate.continuous.measurable
                (measurable_pi_apply k)]
      _ = Measure.map dilate (laws k) := by
            rw [measurePreserving_eval_infinitePi laws k |>.map_eq]
      _ = Measure.map (dilate ∘ layerScaling d k) ν.toMeasure := by
            change Measure.map dilate (Measure.map (layerScaling d k) ν.toMeasure) = _
            rw [Measure.map_map dilate.continuous.measurable
              (layerScaling d k).continuous.measurable]
      _ = Measure.map (layerScaling d (-(i : ℤ))) ν.toMeasure := by
            congr 1
            funext f
            ext y
            dsimp [dilate, dilationMap, layerScaling, k]
            rw [smul_smul, ← zpow_natCast]
            rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            congr 2
            ring_nf
      _ = laws (-(i : ℤ)) := by rfl
  exact
    { aemeasurable_fst := hleft_meas.aemeasurable
      aemeasurable_snd := hright_meas.aemeasurable
      map_eq := hleft_map.trans hright_map.symm }

theorem aux_stationary_family_finite_eval_indep
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (x : I → SpatialCoordinates d) (y : J → SpatialCoordinates d)
    (hxy : ∀ i j, Real.sqrt (d : ℝ) <
      Homogenization.euclideanNorm (x i - y j)) :
    IndepFun (fun f : C(SpatialCoordinates d, ℝ) => fun i : I => f (x i))
      (fun f : C(SpatialCoordinates d, ℝ) => fun j : J => f (y j))
      (chaosRootFieldLaw model).toMeasure := by
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw model
  let margin : I × J → ℝ := fun ij =>
    (Homogenization.euclideanNorm (x ij.1 - y ij.2) - Real.sqrt (d : ℝ)) /
      (2 * (d : ℝ) + 2)
  have hmargin_pos : ∀ ij : I × J, 0 < margin ij := by
    intro ij
    dsimp [margin]
    exact div_pos (sub_pos.mpr (hxy ij.1 ij.2)) (by positivity)
  let vals : Finset ℝ := Finset.univ.image margin
  have hvals_nonempty : vals.Nonempty := by
    exact Finset.univ_nonempty.image margin
  have hvals_pos : ∀ v ∈ vals, 0 < v := by
    intro v hv
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hv
    exact hmargin_pos ij
  let eps : ℝ := vals.min' hvals_nonempty
  have heps_pos : 0 < eps := by
    exact hvals_pos _ (Finset.min'_mem vals hvals_nonempty)
  let U : Set (SpatialCoordinates d) := ⋃ i : I, Metric.ball (x i) eps
  let V : Set (SpatialCoordinates d) := ⋃ j : J, Metric.ball (y j) eps
  have hUopen : IsOpen U := by
    exact isOpen_iUnion (fun i => Metric.isOpen_ball)
  have hVopen : IsOpen V := by
    exact isOpen_iUnion (fun j => Metric.isOpen_ball)
  have hU : MeasurableSet U := hUopen.measurableSet
  have hV : MeasurableSet V := hVopen.measurableSet
  letI : NeZero d := ⟨by
    have hd' := model.shellPrefix.dimension
    omega⟩
  have hsep : SubdiffusiveProcess.CoarseGrainingVocab.PotentialRangeSeparated U V := by
    intro u v hu hv
    obtain ⟨i, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨j, hv⟩ := Set.mem_iUnion.mp hv
    have heps_le : eps ≤ margin (i, j) := by
      exact Finset.min'_le vals _
        (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have hden : 0 < 2 * (d : ℝ) + 2 := by positivity
    have hmargin : Real.sqrt (d : ℝ) + 2 * (d : ℝ) * eps ≤
        Homogenization.euclideanNorm (x i - y j) := by
      have hdim : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hmul : eps * (2 * (d : ℝ) + 2) ≤
          Homogenization.euclideanNorm (x i - y j) - Real.sqrt (d : ℝ) :=
        (le_div_iff₀ hden).mp heps_le
      nlinarith
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.potentialRangeSeparated_ball
      hmargin hu hv
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → I → ℝ :=
    fun g i => g (x i)
  let Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → J → ℝ :=
    fun g j => g (y j)
  have hXlocal : @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (I → ℝ)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
      (MeasurableSpace.pi) X := by
    letI : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U
    apply measurable_pi_lambda
    intro i
    have hi : x i ∈ U := by
      exact Set.mem_iUnion.mpr ⟨i, Metric.mem_ball_self heps_pos⟩
    simpa only [X] using
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
        hUopen hi)
  have hYlocal : @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (J → ℝ)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V)
      (MeasurableSpace.pi) Y := by
    letI : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V
    apply measurable_pi_lambda
    intro j
    have hj : y j ∈ V := by
      exact Set.mem_iUnion.mpr ⟨j, Metric.mem_ball_self heps_pos⟩
    simpa only [Y] using
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
        hVopen hj)
  have hlocal := model.G1.range_dependence U V hU hV hsep
  have hpot : IndepFun X Y
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure := by
    apply (IndepFun_iff_Indep X Y _).2
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hlocal hXlocal.comap_le) hYlocal.comap_le
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let Xc : C(SpatialCoordinates d, ℝ) → I → ℝ :=
    fun f i => f (x i)
  let Yc : C(SpatialCoordinates d, ℝ) → J → ℝ :=
    fun f j => f (y j)
  have hforget : Measurable forget := by
    exact forget.continuous.measurable
  have hXc : Measurable Xc := by
    apply measurable_pi_lambda
    intro i
    exact (continuous_eval_const (x i)).measurable
  have hYc : Measurable Yc := by
    apply measurable_pi_lambda
    intro j
    exact (continuous_eval_const (y j)).measurable
  have hpot' : Indep
      (MeasurableSpace.comap (Xc ∘ forget) MeasurableSpace.pi)
      (MeasurableSpace.comap (Yc ∘ forget) MeasurableSpace.pi)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure := by
    exact (IndepFun_iff_Indep X Y _).mp hpot
  have hν : Measure.map forget
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure = ν.toMeasure := by
    rfl
  have hcont : Indep
      (MeasurableSpace.comap Xc MeasurableSpace.pi)
      (MeasurableSpace.comap Yc MeasurableSpace.pi)
      ν.toMeasure := by
    rw [← hν]
    apply (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map
      hforget.aemeasurable (by exact hXc.comap_le) (by exact hYc.comap_le)).1
    simpa only [MeasurableSpace.comap_comp] using hpot'
  exact (IndepFun_iff_Indep Xc Yc _).2 hcont

theorem aux_stationary_family_scaled_restrict_indep
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (j : ℤ) (hj : j ≤ 0)
    (B C : Set (SpatialCoordinates d))
    (hsep : ∀ x ∈ B, ∀ y ∈ C,
      Real.sqrt (d : ℝ) < Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2)) :
    IndepFun (fun f : C(SpatialCoordinates d, ℝ) => fun x : B => f x)
      (fun f : C(SpatialCoordinates d, ℝ) => fun y : C => f y)
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure := by
  letI : NeZero d := ⟨by
    have hd' := model.shellPrefix.dimension
    omega⟩
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw model
  let c : ℝ := (3 : ℝ) ^ (-j)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact zpow_pos (by norm_num) _
  have hc_one : 1 ≤ c := by
    dsimp [c]
    apply one_le_zpow₀ (by norm_num)
    omega
  have heuc (u v : SpatialCoordinates d) :
      Homogenization.euclideanNorm (u - v) =
        Real.sqrt (∑ k : Fin d, (u k - v k) ^ 2) := by
    simp [Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, pow_two]
  have hscaled (x y : SpatialCoordinates d) (hx : x ∈ B) (hy : y ∈ C) :
      Real.sqrt (d : ℝ) <
        Homogenization.euclideanNorm (c • x - c • y) := by
    have hxy := hsep x hx y hy
    rw [show c • x - c • y = c • (x - y) by ext k; simp; ring,
      Homogenization.euclideanNorm_smul, abs_of_nonneg hc_pos.le]
    have hnorm : 0 ≤ Homogenization.euclideanNorm (x - y) :=
      Homogenization.euclideanNorm_nonneg _
    have hxy' : Real.sqrt (d : ℝ) <
        Homogenization.euclideanNorm (x - y) := by
      rw [heuc]
      exact hxy
    nlinarith
  apply ProbabilityTheory.IndepFun.process_indepFun_process
  · intro x
    exact (continuous_eval_const (x : SpatialCoordinates d)).measurable
  · intro y
    exact (continuous_eval_const (y : SpatialCoordinates d)).measurable
  intro I J
  classical
  by_cases hI : I.Nonempty
  · by_cases hJ : J.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hI
      obtain ⟨j₀, hj₀⟩ := hJ
      letI : Nonempty I := ⟨⟨i₀, hi₀⟩⟩
      letI : Nonempty J := ⟨⟨j₀, hj₀⟩⟩
      let xr : I → SpatialCoordinates d := fun i => c • (i : B)
      let yr : J → SpatialCoordinates d := fun j => c • (j : C)
      have hroot := aux_stationary_family_finite_eval_indep d model xr yr (by
        intro i k
        exact hscaled (i : B) (k : C) (i : B).property (k : C).property)
      let S : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
        layerScaling d j
      let X : C(SpatialCoordinates d, ℝ) → (i : I) → ℝ :=
        fun f i => f (i : B)
      let Y : C(SpatialCoordinates d, ℝ) → (k : J) → ℝ :=
        fun f k => f (k : C)
      let Xr : C(SpatialCoordinates d, ℝ) → (i : I) → ℝ :=
        fun f i => f (xr i)
      let Yr : C(SpatialCoordinates d, ℝ) → (k : J) → ℝ :=
        fun f k => f (yr k)
      have hX : Measurable X := by
        apply measurable_pi_lambda
        intro i
        simpa only [X] using
          (continuous_eval_const (F := C(SpatialCoordinates d, ℝ))
            (α := SpatialCoordinates d) (X := ℝ) (i : B)).measurable
      have hY : Measurable Y := by
        apply measurable_pi_lambda
        intro k
        simpa only [Y] using
          (continuous_eval_const (F := C(SpatialCoordinates d, ℝ))
            (α := SpatialCoordinates d) (X := ℝ) (k : C)).measurable
      have hS : Measurable S := by
        exact (layerScaling d j).continuous.measurable
      have hXeq : Xr = X ∘ S := by
        funext f i
        dsimp [Xr, X, S, xr, c, layerScaling]
      have hYeq : Yr = Y ∘ S := by
        funext f k
        dsimp [Yr, Y, S, yr, c, layerScaling]
      have hroot' : Indep
          (MeasurableSpace.comap Xr MeasurableSpace.pi)
          (MeasurableSpace.comap Yr MeasurableSpace.pi) ν.toMeasure :=
        (IndepFun_iff_Indep Xr Yr _).mp hroot
      have hcomap : Indep
          (MeasurableSpace.comap S (MeasurableSpace.comap X MeasurableSpace.pi))
          (MeasurableSpace.comap S (MeasurableSpace.comap Y MeasurableSpace.pi))
          ν.toMeasure := by
        simpa only [MeasurableSpace.comap_comp, hXeq, hYeq] using hroot'
      have htarget : IndepFun X Y (Measure.map S ν.toMeasure) := by
        apply (IndepFun_iff_Indep X Y _).2
        exact (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map
          hS.aemeasurable hX.comap_le hY.comap_le).1 hcomap
      change IndepFun X Y (Measure.map (layerScaling d j) ν.toMeasure)
      exact htarget
    · letI : IsEmpty J := ⟨fun k => hJ ⟨k.1, k.2⟩⟩
      have hconst : (fun f : C(SpatialCoordinates d, ℝ) =>
          fun k : J => f (k : C)) =
          fun _ => (default : J → ℝ) := by
        funext f
        funext k
        exact isEmptyElim k
      rw [hconst]
      exact indepFun_const_right _ _
  · letI : IsEmpty I := ⟨fun i => hI ⟨i.1, i.2⟩⟩
    have hconst : (fun f : C(SpatialCoordinates d, ℝ) =>
        fun i : I => f (i : B)) =
        fun _ => (default : I → ℝ) := by
      funext f
      funext i
      exact isEmptyElim i
    rw [hconst]
    exact indepFun_const_left _ _

theorem aux_stationary_family_finite_layer_restrict_indep
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (B C : Set (SpatialCoordinates d))
    (hsep : ∀ x ∈ B, ∀ y ∈ C,
      Real.sqrt (d : ℝ) < Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2)) :
    IndepFun
      (fun omega : BilateralField d => fun x : B =>
        ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) x))
      (fun omega : BilateralField d => fun y : C =>
        ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) y))
      (chaosSampleLaw model).toMeasure := by
  classical
  let P := (chaosSampleLaw model).toMeasure
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun k => (scaledLayerLaw d (chaosRootFieldLaw model) k).toMeasure
  let coord : Fin (N + 1) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun i omega => omega (-(i : ℤ))
  let rb : C(SpatialCoordinates d, ℝ) → (B → ℝ) :=
    fun f x => f x
  let rc : C(SpatialCoordinates d, ℝ) → (C → ℝ) :=
    fun f y => f y
  have hrb : Measurable rb := by
    apply measurable_pi_lambda
    intro x
    exact (continuous_eval_const (x : SpatialCoordinates d)).measurable
  have hrc : Measurable rc := by
    apply measurable_pi_lambda
    intro y
    exact (continuous_eval_const (y : SpatialCoordinates d)).measurable
  have hneg : Function.Injective (fun i : Fin (N + 1) => -(i : ℤ)) := by
    intro i k hik
    apply Fin.ext
    have hcast : (i : ℤ) = (k : ℤ) := Int.neg_inj.mp hik
    exact Int.ofNat_inj.mp hcast
  have hbase : iIndepFun
      (fun k : ℤ => fun omega : BilateralField d => omega k)
      (Measure.infinitePi laws) :=
    iIndepFun_infinitePi (P := laws)
      (X := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f)
      (fun _ => measurable_id)
  have hcoord : iIndepFun coord P := by
    simpa only [coord, P, chaosSampleLaw, commonScaleLaw, laws] using
      hbase.precomp hneg
  let kappa : Fin (N + 1) → MeasurableSpace (BilateralField d) :=
    fun i => MeasurableSpace.comap (coord i) inferInstance
  let a : Fin (N + 1) → MeasurableSpace (BilateralField d) :=
    fun i => MeasurableSpace.comap (rb ∘ coord i) MeasurableSpace.pi
  let b : Fin (N + 1) → MeasurableSpace (BilateralField d) :=
    fun i => MeasurableSpace.comap (rc ∘ coord i) MeasurableSpace.pi
  have hkappa : iIndep kappa P := by
    exact hcoord.iIndep
  have hle : ∀ i, kappa i ≤
      (inferInstance : MeasurableSpace (BilateralField d)) := by
    intro i
    dsimp [kappa]
    exact (measurable_pi_apply (-(i : ℤ))).comap_le
  have ha : ∀ i, a i ≤ kappa i := by
    intro i
    dsimp [a, kappa]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hrb.comap_le
  have hb : ∀ i, b i ≤ kappa i := by
    intro i
    dsimp [b, kappa]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hrc.comap_le
  have hrow : ∀ i, Indep (a i) (b i) P := by
    intro i
    have hi : -(i : ℤ) ≤ 0 := by omega
    have hlayer := aux_stationary_family_scaled_restrict_indep d model
      (-(i : ℤ)) hi B C hsep
    have hcoord_map : Measure.map (coord i) P = laws (-(i : ℤ)) := by
      change Measure.map (fun omega : BilateralField d => omega (-(i : ℤ)))
          (Measure.infinitePi laws) = laws (-(i : ℤ))
      exact measurePreserving_eval_infinitePi laws (-(i : ℤ)) |>.map_eq
    have hlayer' : Indep (MeasurableSpace.comap rb MeasurableSpace.pi)
        (MeasurableSpace.comap rc MeasurableSpace.pi)
        (Measure.map (coord i) P) := by
      rw [hcoord_map]
      exact (IndepFun_iff_Indep rb rc _).mp hlayer
    have hcoord_meas : Measurable (coord i) := by
      exact measurable_pi_apply _
    have hpull := (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map
      (f := coord i) hcoord_meas.aemeasurable hrb.comap_le hrc.comap_le).2 hlayer'
    simpa only [a, b, MeasurableSpace.comap_comp] using hpull
  have hagg : Indep (⨆ i, a i) (⨆ i, b i) P :=
    SubdiffusiveProcess.CoarseGrainingVocab.indep_iSup_of_indep_of_iIndep
      hkappa hle ha hb hrow
  let prodB : BilateralField d → (B → ℝ) := fun omega x =>
    ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) x)
  let prodC : BilateralField d → (C → ℝ) := fun omega y =>
    ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) y)
  have hprodB : @Measurable (BilateralField d) (B → ℝ)
      (⨆ i, a i) MeasurableSpace.pi prodB := by
    letI : MeasurableSpace (BilateralField d) := ⨆ i, a i
    apply measurable_pi_lambda
    intro x
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.exp
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    let k : Fin (N + 1) := ⟨i, hiN⟩
    have hcoordx : @Measurable (BilateralField d) ℝ (a k) inferInstance
        (fun omega => omega (-(i : ℤ)) x) := by
      have hfun : @Measurable (BilateralField d) (B → ℝ) (a k)
          MeasurableSpace.pi (rb ∘ coord k) :=
        Measurable.of_comap_le le_rfl
      exact (measurable_pi_apply x).comp hfun
    exact hcoordx.mono (le_iSup a k) le_rfl
  have hprodC : @Measurable (BilateralField d) (C → ℝ)
      (⨆ i, b i) MeasurableSpace.pi prodC := by
    letI : MeasurableSpace (BilateralField d) := ⨆ i, b i
    apply measurable_pi_lambda
    intro y
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.exp
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    let k : Fin (N + 1) := ⟨i, hiN⟩
    have hcoordy : @Measurable (BilateralField d) ℝ (b k) inferInstance
        (fun omega => omega (-(i : ℤ)) y) := by
      have hfun : @Measurable (BilateralField d) (C → ℝ) (b k)
          MeasurableSpace.pi (rc ∘ coord k) :=
        Measurable.of_comap_le le_rfl
      exact (measurable_pi_apply y).comp hfun
    exact hcoordy.mono (le_iSup b k) le_rfl
  apply (IndepFun_iff_Indep prodB prodC P).2
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hagg hprodB.comap_le) hprodC.comap_le



theorem stationary_family (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    let P := (chaosSampleLaw model).toMeasure
    let kappa : ℕ → ℝ := fun N =>
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
    let A0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ := fun N omega x =>
      (kappa N)⁻¹ * Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)
    let a : ℕ → BilateralField d → SpatialCoordinates d → ℝ := fun N omega x =>
      Real.exp (∑ j ∈ Finset.range (N + 1),
        (omega (j : ℤ) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
    (∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x =
        A0 N omega x) ∧
    (∀ N : ℕ, IdentDistrib (fun omega => A0 N omega)
      (fun omega x => (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        a N omega ((3 : ℝ) ^ N • x)) P P) ∧
    (∀ (N : ℕ) (z : SpatialCoordinates d),
      IdentDistrib (fun omega => A0 N omega)
        (fun omega x => A0 N omega (x + z)) P P) ∧
    (∀ (N : ℕ) (B C : Set (SpatialCoordinates d)),
      (∀ x ∈ B, ∀ y ∈ C,
        Real.sqrt (d : ℝ) < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) →
      IndepFun (fun omega => fun x : B => A0 N omega x)
        (fun omega => fun y : C => A0 N omega y) P) := by
  dsimp
  constructor
  · intro N omega x
    unfold cutoffCoefficient cutoffPotential
    simp only [ContinuousMap.zero_apply, inv_mul_eq_div]
    rw [Real.exp_sub]
    simp
    ring
  · constructor
    · intro N
      let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
        chaosRootFieldLaw model
      let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
        fun j => (scaledLayerLaw d ν j).toMeasure
      let dilate : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
        ContinuousMap.compRightContinuousMap ℝ
          (⟨fun y : SpatialCoordinates d => (3 : ℝ) ^ N • y,
            continuous_const.smul continuous_id⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
      let X : (i : Fin (N + 1)) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
        fun i omega => omega (-(i : ℤ))
      let Y : (i : Fin (N + 1)) → BilateralField d → C(SpatialCoordinates d, ℝ) :=
        fun i omega => dilate (omega ((N : ℤ) - (i : ℤ)))
      have hXY : ∀ i : Fin (N + 1), IdentDistrib (X i) (Y i)
          (commonScaleLaw d ν).toMeasure (commonScaleLaw d ν).toMeasure := by
        intro i
        simpa only [X, Y, dilate, ν, chaosRootFieldLaw] using
          (aux_stationary_family_relabelled_coordinate d N ν i)
      have hbase : iIndepFun
          (fun j : ℤ => fun omega : BilateralField d => omega j)
          (Measure.infinitePi laws) :=
        iIndepFun_infinitePi (P := laws)
          (X := fun _ : ℤ => fun x : C(SpatialCoordinates d, ℝ) => x)
          (fun _ => measurable_id)
      have hneg : Function.Injective (fun i : Fin (N + 1) => -(i : ℤ)) := by
        intro i k hik
        apply Fin.ext
        have hcast : (i : ℤ) = (k : ℤ) := Int.neg_inj.mp hik
        exact Int.ofNat_inj.mp hcast
      have hshift : Function.Injective (fun i : Fin (N + 1) =>
          (N : ℤ) - (i : ℤ)) := by
        intro i k hik
        apply Fin.ext
        have hcast : (i : ℤ) = (k : ℤ) := by linarith
        exact Int.ofNat_inj.mp hcast
      have hXind : iIndepFun X (Measure.infinitePi laws) := by
        simpa only [X] using hbase.precomp hneg
      have hYbase : iIndepFun
          (fun i : Fin (N + 1) => fun omega : BilateralField d =>
            omega ((N : ℤ) - (i : ℤ))) (Measure.infinitePi laws) := by
        simpa only using hbase.precomp hshift
      have hYind : iIndepFun Y (Measure.infinitePi laws) := by
        have hcomp := hYbase.comp
          (fun _ : Fin (N + 1) => dilate)
          (fun _ => dilate.continuous.measurable)
        simpa only [Y, Function.comp_apply] using hcomp
      have hfamily : IdentDistrib
          (fun omega => fun i : Fin (N + 1) => X i omega)
          (fun omega => fun i : Fin (N + 1) => Y i omega)
          (Measure.infinitePi laws) (Measure.infinitePi laws) :=
        IdentDistrib.pi hXY hXind hYind
      have hU : Measurable
          (fun q : (i : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) =>
            fun x : SpatialCoordinates d =>
              (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
                Real.exp (∑ i : Fin (N + 1), q i x)) := by
        apply measurable_pi_lambda
        intro x
        apply Measurable.mul
        · exact measurable_const
        · apply Measurable.exp
          apply Finset.measurable_sum
          intro i hi
          exact (continuous_eval_const x).measurable.comp (measurable_pi_apply i)
      have hpost := hfamily.comp hU
      have hsum (omega : BilateralField d) (x : SpatialCoordinates d) :
          (∑ i : Fin (N + 1), omega ((N : ℤ) - (i : ℤ)) ((3 : ℝ) ^ N • x)) =
            ∑ j ∈ Finset.range (N + 1), omega (j : ℤ) ((3 : ℝ) ^ N • x) := by
        have hfin :
            (∑ i : Fin (N + 1), omega ((N : ℤ) - (i : ℤ)) ((3 : ℝ) ^ N • x)) =
              ∑ j ∈ Finset.range (N + 1),
                omega ((N : ℤ) - (j : ℤ)) ((3 : ℝ) ^ N • x) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro j hj
          rw [dif_pos (Finset.mem_range.mp hj)]
        rw [hfin, ← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        have hjlt : j < N + 1 := Finset.mem_range.mp hj
        have hjN : j ≤ N := by omega
        have hj' : N + 1 - 1 - j = N - j := by omega
        rw [hj', Int.ofNat_sub hjN]
        congr 2
        ring
      have hleft :
          (fun omega => (fun q : (i : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) =>
            fun x : SpatialCoordinates d =>
              (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
                Real.exp (∑ i : Fin (N + 1), q i x))
            (fun i => X i omega)) =
            (fun omega => fun x =>
              (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
                Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) := by
        funext omega x
        dsimp [X]
        have hsumneg :
            (∑ i : Fin (N + 1), omega (-(i : ℤ)) x) =
              ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro j hj
          rw [dif_pos (Finset.mem_range.mp hj)]
        rw [hsumneg]
      have hright :
          (fun omega => (fun q : (i : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) =>
            fun x : SpatialCoordinates d =>
              (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
                Real.exp (∑ i : Fin (N + 1), q i x))
            (fun i => Y i omega)) =
            (fun omega => fun x =>
              (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
                Real.exp (∑ j ∈ Finset.range (N + 1),
                  (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
                    SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))) := by
        funext omega x
        dsimp [Y, dilate]
        rw [hsum]
        rw [Finset.sum_sub_distrib]
        simp
        rw [Real.exp_sub]
        ring
      have htarget : IdentDistrib
          (fun omega => fun x =>
            (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
              Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x))
          (fun omega => fun x =>
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
              Real.exp (∑ j ∈ Finset.range (N + 1),
                (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
                  SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)))
          (Measure.infinitePi laws) (Measure.infinitePi laws) := by
        refine
          { aemeasurable_fst := hpost.aemeasurable_fst.congr
                (Filter.Eventually.of_forall (fun omega => congrFun hleft omega))
            aemeasurable_snd := hpost.aemeasurable_snd.congr
                (Filter.Eventually.of_forall (fun omega => congrFun hright omega))
            map_eq := ?_ }
        rw [← hleft, ← hright]
        exact hpost.map_eq
      simpa only [ν, chaosRootFieldLaw, chaosSampleLaw] using htarget
    · constructor
      · intro N z
        let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
          chaosRootFieldLaw model
        have hν : ∀ z : SpatialCoordinates d, MeasurePreserving
            (fun f : C(SpatialCoordinates d, ℝ) =>
              f.comp (⟨fun x : SpatialCoordinates d => x + z,
                continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d)))
            ν.toMeasure ν.toMeasure := by
          intro z
          simpa only [ν, chaosRootFieldLaw] using
            (gmc_zero_field_law_stationary model z)
        have hscaled := aux_stationary_family_scaled_layer d ν hν
        have hprod := aux_stationary_family_product_stationary d ν hscaled z
        let kappa : ℕ → ℝ := fun N =>
          Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
        let A0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N omega x =>
            (kappa N)⁻¹ * Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)
        change IdentDistrib (fun omega => A0 N omega)
          (fun omega x => A0 N omega (x + z))
          (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure
        have hA0 : Measurable (fun omega : BilateralField d => A0 N omega) := by
          apply measurable_pi_lambda
          intro x
          dsimp [A0]
          apply Measurable.mul
          · exact measurable_const
          · apply Measurable.exp
            apply Finset.measurable_sum
            intro j hj
            exact (continuous_eval_const x).measurable.comp
              (measurable_pi_apply (-(j : ℤ)))
        have hT : Measurable (fun omega : BilateralField d => fun j : ℤ =>
            (omega j).comp (⟨fun x : SpatialCoordinates d => x + z,
              continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))) :=
          hprod.measurable
        have hcomp : (fun omega : BilateralField d => A0 N omega) ∘
            (fun omega : BilateralField d => fun j : ℤ =>
              (omega j).comp (⟨fun x : SpatialCoordinates d => x + z,
                continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))) =
            (fun omega : BilateralField d => fun x => A0 N omega (x + z)) := by
          funext omega
          funext x
          rfl
        refine
          { aemeasurable_fst := hA0.aemeasurable
            aemeasurable_snd := ?_
            map_eq := ?_ }
        · rw [← hcomp]
          exact hA0.comp_aemeasurable hT.aemeasurable
        · rw [← hcomp]
          change Measure.map (fun omega => A0 N omega)
              (commonScaleLaw d ν).toMeasure =
            Measure.map ((fun omega => A0 N omega) ∘
              (fun omega : BilateralField d => fun j : ℤ =>
                (omega j).comp (⟨fun x : SpatialCoordinates d => x + z,
                  continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))))
              (commonScaleLaw d ν).toMeasure
          rw [← Measure.map_map hA0 hT, hprod.map_eq]
      · intro N B C hsep
        let kappa : ℕ → ℝ := fun N =>
          Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
        let A0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N omega x =>
            (kappa N)⁻¹ * Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)
        let prodB : BilateralField d → (B → ℝ) := fun omega x =>
          ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) x)
        let prodC : BilateralField d → (C → ℝ) := fun omega y =>
          ∏ i ∈ Finset.range (N + 1), Real.exp (omega (-(i : ℤ)) y)
        have hprod := aux_stationary_family_finite_layer_restrict_indep
          d model N B C hsep
        let φ : (B → ℝ) → (B → ℝ) := fun f x => (kappa N)⁻¹ * f x
        let ψ : (C → ℝ) → (C → ℝ) := fun f y => (kappa N)⁻¹ * f y
        have hφ : Measurable φ := by
          apply measurable_pi_lambda
          intro x
          exact measurable_const.mul (measurable_pi_apply x)
        have hψ : Measurable ψ := by
          apply measurable_pi_lambda
          intro y
          exact measurable_const.mul (measurable_pi_apply y)
        have hscaled := hprod.comp hφ hψ
        have hleft : (φ ∘ prodB) =
            (fun omega => fun x : B => A0 N omega x) := by
          funext omega x
          dsimp [φ, prodB, A0]
          rw [← Real.exp_sum]
        have hright : (ψ ∘ prodC) =
            (fun omega => fun y : C => A0 N omega y) := by
          funext omega y
          dsimp [ψ, prodC, A0]
          rw [← Real.exp_sum]
        rw [hleft, hright] at hscaled
        exact hscaled

end
end Paper
