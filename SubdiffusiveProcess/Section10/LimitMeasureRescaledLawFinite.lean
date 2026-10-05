module

public import SubdiffusiveProcess.MacroAllCube.ResidualLaw
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Assumptions.Cutoff
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section




open MeasureTheory ProbabilityTheory SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

def nativeFieldFamily (w : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ℕ → C(SpatialCoordinates d, ℝ) := fun i => (w i).1.1

theorem measurable_nativeFieldFamily : Measurable (nativeFieldFamily (d := d)) := by
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  exact Measurable.of_eval fun i => forget.continuous.measurable.comp
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate i)

/-- The actual natural-index family and the natural projection of the
bilateral field have the same entire family law. -/
theorem nativeFieldFamily_law (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Measure.map nativeFieldFamily M.P.toMeasure =
      Measure.map (fun w : BilateralField d => fun i : ℕ => w (i : ℤ))
        (chaosSampleLaw M).toMeasure := by
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  have hn : iIndepFun (fun i : ℕ => fun w : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      forget (w i)) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun _ => forget) (fun _ => forget.continuous.measurable)
  have hnmap := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => forget.continuous.measurable.comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate i))).mp hn
  simp only [Function.comp_def] at hnmap
  have hnm (i : ℕ) :
      Measure.map (fun w : _root_.SubdiffusiveProcess.Model.PotentialSample d => forget (w i))
        M.P.toMeasure = (scaledLayerLaw d (chaosRootFieldLaw M) (i : ℤ)).toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure (gmc_marginal_field_law_eq_scaledLayerLaw M i)
    change Measure.map forget (Measure.map (fun w => w i) M.P.toMeasure) =
      (scaledLayerLaw d (chaosRootFieldLaw M) (i : ℤ)).toMeasure at h
    rw [Measure.map_map forget.continuous.measurable
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate i)] at h
    exact h
  have hb : iIndepFun (fun j : ℤ => fun w : BilateralField d => w j)
      (chaosSampleLaw M).toMeasure :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hbmap := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i : ℕ => measurable_pi_apply (i : ℤ))).mp
    (hb.precomp (by intro i j hij; exact_mod_cast hij))
  have hbm (i : ℕ) : Measure.map (fun w : BilateralField d => w (i : ℤ))
      (chaosSampleLaw M).toMeasure =
        (scaledLayerLaw d (chaosRootFieldLaw M) (i : ℤ)).toMeasure :=
    Measure.infinitePi_map_eval _ _
  change Measure.map (fun w i => forget (w i)) M.P.toMeasure = _
  rw [hnmap, hbmap]
  congr 1
  funext i
  rw [hnm, hbm]

/-- Literal cutoff-dependent relabelling and spatial scaling of the original
bilateral layers, with the same common-scale law. -/
def relabelledNativeFamily (N : ℕ) (w : BilateralField d) :
    ℕ → C(SpatialCoordinates d, ℝ) :=
  fun i => MacroAllCube.residualShift ((3 : ℝ) ^ (-(N : ℤ))) N w (i : ℤ)

theorem measurable_relabelledNativeFamily (N : ℕ) :
    Measurable (relabelledNativeFamily (d := d) N) :=
  Measurable.of_eval fun i =>
    (MacroAllCube.dilateField d ((3 : ℝ) ^ (-(N : ℤ)))).continuous.measurable.comp
      (measurable_pi_apply ((i : ℤ) - (N : ℤ)))

theorem relabelledNativeFamily_law (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measure.map (relabelledNativeFamily N) (chaosSampleLaw M).toMeasure =
      Measure.map nativeFieldFamily M.P.toMeasure := by
  have hroot (nu : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
      MacroAllCube.residualRootLaw nu 1 = nu := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (MacroAllCube.dilateField d 1) nu.toMeasure = nu.toMeasure
    have hid : (MacroAllCube.dilateField d 1 : C(SpatialCoordinates d, ℝ) →
        C(SpatialCoordinates d, ℝ)) = id := by
      funext f
      ext x
      simp [MacroAllCube.dilateField, MacroAllCube.spatialDilation]
    rw [hid, Measure.map_id]
  have hscale : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  have hp := MacroAllCube.measurePreserving_residualShift (chaosRootFieldLaw M)
    ((3 : ℝ) ^ (-(N : ℤ))) N
  rw [hscale, hroot] at hp
  have hproj : Measurable (fun w : BilateralField d => fun i : ℕ => w (i : ℤ)) :=
    Measurable.of_eval fun i => measurable_pi_apply (i : ℤ)
  calc Measure.map (relabelledNativeFamily N) (chaosSampleLaw M).toMeasure
      = Measure.map (fun w : BilateralField d => fun i : ℕ => w (i : ℤ))
          (Measure.map (MacroAllCube.residualShift ((3 : ℝ) ^ (-(N : ℤ))) N)
            (chaosSampleLaw M).toMeasure) := by
        rw [Measure.map_map hproj hp.measurable]
        rfl
    _ = Measure.map (fun w : BilateralField d => fun i : ℕ => w (i : ℤ))
          (chaosSampleLaw M).toMeasure :=
        congrArg (Measure.map (fun w : BilateralField d => fun i : ℕ => w (i : ℤ))) hp.map_eq
    _ = Measure.map nativeFieldFamily M.P.toMeasure := (nativeFieldFamily_law M).symm

/-- A continuous-family expression for the literal rescaled cutoff. -/
def rescaledFieldMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (f : ℕ → C(SpatialCoordinates d, ℝ)) : Measure (SpatialCoordinates d) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp
    (∑ i ∈ Finset.range (N + 1), (f i ((3 : ℝ) ^ N • x) - _root_.SubdiffusiveProcess.Model.tauSq M.P))))

/-- The actual natural-environment measure `a_N(3^N x) dx`. -/
def rescaledCutoffMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (w : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Measure (SpatialCoordinates d) :=
  volume.withDensity (fun x => ENNReal.ofReal
    (_root_.SubdiffusiveProcess.Model.aCutoff M N w ((3 : ℝ) ^ N • x)))

theorem measurable_rescaledFieldMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measurable (rescaledFieldMeasure M N) := by
  apply Measure.measurable_measure.mpr
  intro U hU
  have hj : Measurable (fun fx : (ℕ → C(SpatialCoordinates d, ℝ)) × SpatialCoordinates d =>
      ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range (N + 1),
        (fx.1 i ((3 : ℝ) ^ N • fx.2) - _root_.SubdiffusiveProcess.Model.tauSq M.P)))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i _
    apply Measurable.sub_const
    exact continuous_eval.measurable.comp
      (((measurable_pi_apply (i : ℕ) : Measurable (fun fx : ℕ → C(SpatialCoordinates d, ℝ) => fx i)).comp measurable_fst).prodMk
        ((measurable_const : Measurable (fun _ : (ℕ → C(SpatialCoordinates d, ℝ)) × SpatialCoordinates d => (3 : ℝ) ^ N)).smul measurable_snd))
  simpa only [rescaledFieldMeasure, withDensity_apply _ hU] using
    hj.lintegral_prod_right (ν := volume.restrict U)

theorem measurable_rescaledCutoffMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measurable (rescaledCutoffMeasure M N) :=
  (measurable_rescaledFieldMeasure M N).comp measurable_nativeFieldFamily

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem rescaledCutoffMeasure_locallyFinite (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) (w : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    IsLocallyFiniteMeasure (rescaledCutoffMeasure M N w) :=
  by
    apply IsLocallyFiniteMeasure.withDensity_ofReal
    simpa only [Function.comp_apply] using! ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M N w).comp
      ((continuous_const : Continuous (fun _ : SpatialCoordinates d => (3 : ℝ) ^ N)).smul continuous_id))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Pointwise cancellation of the spatial dilation, followed by reflection
of the exact finite layer range. -/
theorem rescaledFieldMeasure_relabelled (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) (w : BilateralField d) :
    rescaledFieldMeasure M N (relabelledNativeFamily N w) = chaosCutoff M N w := by
  have hdensity (x : SpatialCoordinates d) :
      Real.exp (∑ i ∈ Finset.range (N + 1),
        ((relabelledNativeFamily N w) i ((3 : ℝ) ^ N • x) - _root_.SubdiffusiveProcess.Model.tauSq M.P))
        = fineDensity M N w x := by
    have he (i : ℕ) : (relabelledNativeFamily N w) i ((3 : ℝ) ^ N • x) =
        w ((i : ℤ) - (N : ℤ)) x := by
      change w _ (((3 : ℝ) ^ (-(N : ℤ))) • ((3 : ℝ) ^ N • x)) = _
      rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
    simp_rw [he]
    have hs : (∑ i ∈ Finset.range (N + 1),
        (w ((i : ℤ) - (N : ℤ)) x - _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
        ∑ i ∈ Finset.range (N + 1),
          (w (-(i : ℤ)) x - _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [← Finset.sum_range_reflect
        (fun i => w ((i : ℤ) - (N : ℤ)) x - _root_.SubdiffusiveProcess.Model.tauSq M.P) (N + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hile : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [Nat.add_sub_cancel, Int.natCast_sub hile,
        show (N : ℤ) - (i : ℤ) - (N : ℤ) = -(i : ℤ) by ring]
    rw [hs]
    simp [fineDensity, finePotential, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  simp only [rescaledFieldMeasure, chaosCutoff, hdensity, Function.comp_def]

/-- Equality of the full finite measure-valued laws, on the actual natural
and bilateral probability carriers. No replacement field law is used. -/
theorem rescaledCutoffMeasure_law (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measure.map (rescaledCutoffMeasure M N) M.P.toMeasure =
      Measure.map (chaosCutoff M N) (chaosSampleLaw M).toMeasure := by
  have hcomp : rescaledCutoffMeasure M N = rescaledFieldMeasure M N ∘ nativeFieldFamily := rfl
  rw [hcomp, ← Measure.map_map (measurable_rescaledFieldMeasure M N)
    measurable_nativeFieldFamily, ← relabelledNativeFamily_law M N,
    Measure.map_map (measurable_rescaledFieldMeasure M N) (measurable_relabelledNativeFamily N)]
  congr 1
  funext w
  exact rescaledFieldMeasure_relabelled M N w

end SubdiffusiveProcess.Section10
