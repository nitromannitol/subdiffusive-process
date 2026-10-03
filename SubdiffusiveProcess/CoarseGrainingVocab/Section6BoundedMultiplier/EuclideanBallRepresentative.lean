module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastBallRescaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SlopeStabilityEndpoints

@[expose] public section

/-!
# Canonical representative from shrinking Euclidean-ball averages

The representative is defined globally, without choosing or gluing local
Schauder representatives.  A local continuous representative identifies with
this canonical limit at every point of its open carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Filter MeasureTheory Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The deterministic positive radii used by the canonical representative. -/
def euclideanBallRepresentativeRadius (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

theorem euclideanBallRepresentativeRadius_pos (n : ℕ) :
    0 < euclideanBallRepresentativeRadius n := by
  unfold euclideanBallRepresentativeRadius
  positivity

theorem tendsto_euclideanBallRepresentativeRadius :
    Tendsto euclideanBallRepresentativeRadius atTop (𝓝 0) := by
  simpa only [euclideanBallRepresentativeRadius, one_div] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The raw shrinking-ball averages at a point. -/
def euclideanBallAverageSequence (f : Vec d → ℝ) (x : Vec d) (n : ℕ) : ℝ :=
  averageOn (euclideanBall x (euclideanBallRepresentativeRadius n)) f

/-- The canonical global representative. -/
def euclideanBallAverageRepresentative (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  limUnder atTop (euclideanBallAverageSequence f x)

/-- Pull a unit-ball scalar representative back to its physical ball with the
inverse value normalization used by `ballToUnitH1`. -/
def physicalBallRepresentative (x : Vec d) (rho : ℝ)
    (uRep : Vec d → ℝ) (y : Vec d) : ℝ :=
  rho * uRep (rho⁻¹ • (y - x))

theorem continuousOn_physicalBallRepresentative
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho) {uRep : Vec d → ℝ}
    (hcont : ContinuousOn uRep (smallContrastBall d (1 / 2))) :
    ContinuousOn (physicalBallRepresentative x rho uRep)
      (euclideanBall x (rho / 2)) := by
  have haffine : Continuous (fun y : Vec d ↦ rho⁻¹ • (y - x)) :=
    (continuous_const_smul rho⁻¹).comp (continuous_id.sub continuous_const)
  have hmap : Set.MapsTo (fun y : Vec d ↦ rho⁻¹ • (y - x))
      (euclideanBall x (rho / 2)) (smallContrastBall d (1 / 2)) := by
    intro y hy
    simp only [smallContrastBall, euclideanBall, Set.mem_setOf_eq,
      euclideanSqDist, sub_zero]
    simp only [euclideanBall, Set.mem_setOf_eq, euclideanSqDist] at hy
    rw [vecNormSq_smul]
    have hr2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
    field_simp [hrho.ne']
    nlinarith
  exact continuousOn_const.mul (hcont.comp haffine.continuousOn hmap)

/-- The pulled-back local representative agrees almost everywhere with the
physical Sobolev representative on the inner half-ball. -/
theorem physicalBallRepresentative_ae_eq
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    {u : H1Function (euclideanBall x rho)} {uRep : Vec d → ℝ}
    (hrep : uRep =ᵐ[volume.restrict (smallContrastUnitBall d)]
      (ballToUnitH1 x hrho u).toFun) :
    physicalBallRepresentative x rho uRep =ᵐ[
      volume.restrict (euclideanBall x (rho / 2))] u.toFun := by
  have hglobal : ∀ᵐ y ∂volume, y ∈ smallContrastUnitBall d →
      uRep y = (ballToUnitH1 x hrho u).toFun y :=
    (ae_restrict_iff'
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet).1 hrep
  let T : Vec d → Vec d := fun y ↦ rho⁻¹ • (y - x)
  have hsub : Measure.QuasiMeasurePreserving (fun y : Vec d ↦ y - x)
      volume volume := by
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure (Vec d)) (-x)).quasiMeasurePreserving
  have hsmul : Measure.QuasiMeasurePreserving (rho⁻¹ • · : Vec d → Vec d)
      volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hrho.ne')
  have hT : Measure.QuasiMeasurePreserving T volume volume := by
    simpa [T, Function.comp_def] using hsmul.comp hsub
  have hcomp := hT.ae hglobal
  refine (ae_restrict_iff'
    (isOpen_euclideanBall x (rho / 2)).measurableSet).2 ?_
  filter_upwards [hcomp] with y hy hyBall
  have hyOuter : y ∈ euclideanBall x rho :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith) hyBall
  have hTy : T y ∈ smallContrastUnitBall d := by
    change rho⁻¹ • (y - x) ∈ euclideanBall 0 1
    have haff : rho • (rho⁻¹ • (y - x)) + x = y := by
      ext i
      simp [hrho.ne']
    exact (affine_mem_euclideanBall_iff_of_pos x _ hrho).1 (by simpa [haff] using hyOuter)
  have heq := hy hTy
  change rho * uRep (T y) = u.toFun y
  rw [heq, ballToUnitH1_toFun]
  dsimp [T]
  have haff : rho • (rho⁻¹ • (y - x)) + x = y := by
    ext i
    simp [hrho.ne']
  rw [haff]
  field_simp [hrho.ne']

/-- Pulling a unit-ball Hölder bound back to the physical ball costs the
expected factor `rho^(1-alpha)`. -/
theorem euclideanHolderBoundOn_physicalBallRepresentative
    {x : Vec d} {rho alpha K : ℝ} (hrho : 0 < rho)
    {uRep : Vec d → ℝ}
    (hholder : EuclideanHolderBoundOn (smallContrastBall d (1 / 2))
      alpha K uRep) :
    EuclideanHolderBoundOn (euclideanBall x (rho / 2)) alpha
      (K * rho ^ (1 - alpha))
      (physicalBallRepresentative x rho uRep) := by
  intro y hy w hw
  have hy' : rho⁻¹ • (y - x) ∈ smallContrastBall d (1 / 2) := by
    simp only [smallContrastBall, euclideanBall, Set.mem_setOf_eq,
      euclideanSqDist, sub_zero] at hy ⊢
    rw [vecNormSq_smul]
    have hr2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
    field_simp [hrho.ne']
    nlinarith
  have hw' : rho⁻¹ • (w - x) ∈ smallContrastBall d (1 / 2) := by
    simp only [smallContrastBall, euclideanBall, Set.mem_setOf_eq,
      euclideanSqDist, sub_zero] at hw ⊢
    rw [vecNormSq_smul]
    have hr2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
    field_simp [hrho.ne']
    nlinarith
  have hbase := hholder _ hy' _ hw'
  unfold physicalBallRepresentative
  rw [← mul_sub, abs_mul, abs_of_pos hrho]
  have hdiff : rho⁻¹ • (y - x) - rho⁻¹ • (w - x) =
      rho⁻¹ • (y - w) := by
    ext i
    simp
    ring
  calc
    rho * |uRep (rho⁻¹ • (y - x)) - uRep (rho⁻¹ • (w - x))| ≤
        rho * (K * euclideanNorm
          (rho⁻¹ • (y - x) - rho⁻¹ • (w - x)) ^ alpha) :=
      mul_le_mul_of_nonneg_left hbase hrho.le
    _ = K * rho ^ (1 - alpha) * euclideanNorm (y - w) ^ alpha := by
      rw [hdiff, euclideanNorm_smul, abs_of_pos (inv_pos.mpr hrho),
        Real.mul_rpow (inv_nonneg.mpr hrho.le) (euclideanNorm_nonneg _),
        Real.inv_rpow hrho.le, ← Real.rpow_neg hrho.le]
      have hpow : rho * rho ^ (-alpha) = rho ^ (1 - alpha) := by
        nth_rewrite 1 [← Real.rpow_one rho]
        rw [← Real.rpow_add hrho]
        congr 1
      rw [show rho * (K * (rho ^ (-alpha) *
          euclideanNorm (y - w) ^ alpha)) =
          K * (rho * rho ^ (-alpha)) * euclideanNorm (y - w) ^ alpha by ring,
        hpow]

/-- An almost-everywhere pointwise bound on a ball controls the difference
between the ball average and the reference value. -/
theorem abs_averageOn_euclideanBall_sub_le_of_ae_eq
    [NeZero d] {W V : Set (Vec d)} {u : H1Function W}
    {g : Vec d → ℝ} {x : Vec d} {r C : ℝ} (hr : 0 < r)
    (hballV : euclideanBall x r ⊆ V) (hVW : V ⊆ W)
    (hlocal : g =ᵐ[volume.restrict V] u.toFun)
    (hC : 0 ≤ C) (hbound : ∀ y ∈ euclideanBall x r, |g y - g x| ≤ C) :
    |averageOn (euclideanBall x r) u.toFun - g x| ≤ C := by
  let S := euclideanBall x r
  letI : IsFiniteMeasure (volume.restrict S) :=
    Homogenization.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall x r
  have hSW : S ⊆ W := hballV.trans hVW
  have huS : MemLp u.toFun 2 (volume.restrict S) :=
    u.memL2.mono_measure (Measure.restrict_mono hSW le_rfl)
  have hcenter : MemLp (fun _ : Vec d ↦ g x) 2 (volume.restrict S) :=
    memLp_const (g x)
  have hdiff : MemLp (fun y ↦ u.toFun y - g x) 2 (volume.restrict S) :=
    huS.sub hcenter
  have hlocalS : g =ᵐ[volume.restrict S] u.toFun :=
    hlocal.filter_mono (ae_mono (Measure.restrict_mono hballV le_rfl))
  have haeBound : ∀ᵐ y ∂(volume.restrict S), |u.toFun y - g x| ≤ C := by
    filter_upwards [hlocalS,
      ae_restrict_mem (isOpen_euclideanBall x r).measurableSet] with y hy hyS
    rw [← hy]
    exact hbound y hyS
  have hvolne := Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hr
  have hvolpos : 0 < (volume S).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hvolne)
  have hvoltop := Homogenization.Book.Ch01.volume_euclideanBall_ne_top x r
  have hJ := SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.abs_volumeAverage_le_normalizedL2On
    (isOpen_euclideanBall x r).measurableSet hvolpos
    (hdiff.integrable one_le_two) hdiff.integrable_sq
  have hL2 := SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.normalizedL2On_le_of_ae_abs_le
    hvolpos hvoltop hC hdiff haeBound
  have havg : averageOn S u.toFun - g x =
      volumeAverage S (fun y ↦ u.toFun y - g x) := by
    unfold averageOn
    change volumeAverage S u.toFun - g x =
      volumeAverage S (u.toFun - fun _ ↦ g x)
    rw [volumeAverage_sub (huS.integrable one_le_two) (hcenter.integrable one_le_two),
      volumeAverage_const hvolne]
  rw [havg]
  exact hJ.trans hL2

/-- A local continuous representative is the limit of the canonical shrinking
Euclidean-ball averages at every point of its open carrier. -/
theorem tendsto_euclideanBallAverageSequence_of_localRepresentative
    [NeZero d] {W V : Set (Vec d)} {u : H1Function W}
    {g : Vec d → ℝ} (hV : IsOpen V) (hVW : V ⊆ W)
    (hlocal : g =ᵐ[volume.restrict V] u.toFun)
    (hcont : ContinuousOn g V) {x : Vec d} (hx : x ∈ V) :
    Tendsto (euclideanBallAverageSequence u.toFun x) atTop (𝓝 (g x)) := by
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon ↦ ?_
  have hgx : ContinuousAt g x := hcont.continuousAt (hV.mem_nhds hx)
  obtain ⟨delta, hdelta, hgdelta⟩ :=
    (Metric.continuousAt_iff.1 hgx) (epsilon / 2) (by linarith)
  obtain ⟨eta, heta, hetaV⟩ := Metric.isOpen_iff.1 hV x hx
  have hradius := tendsto_euclideanBallRepresentativeRadius
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hradius (min delta eta) (lt_min hdelta heta)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hrpos := euclideanBallRepresentativeRadius_pos n
  have hrlt : euclideanBallRepresentativeRadius n < min delta eta := by
    have hn' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos hrpos] at hn'
    exact hn'
  have hballV : euclideanBall x (euclideanBallRepresentativeRadius n) ⊆ V := by
    intro y hy
    apply hetaV
    have hyr : dist y x < euclideanBallRepresentativeRadius n :=
      euclideanBall_subset_metricBall hrpos hy
    exact hyr.trans (hrlt.trans_le (min_le_right _ _))
  have hbound : ∀ y ∈ euclideanBall x (euclideanBallRepresentativeRadius n),
      |g y - g x| ≤ epsilon / 2 := by
    intro y hy
    have hydist : dist y x < delta := by
      have hyr : dist y x < euclideanBallRepresentativeRadius n :=
        euclideanBall_subset_metricBall hrpos hy
      exact hyr.trans (hrlt.trans_le (min_le_left _ _))
    exact le_of_lt (hgdelta hydist)
  have havg := abs_averageOn_euclideanBall_sub_le_of_ae_eq hrpos hballV hVW
    hlocal (by linarith : 0 ≤ epsilon / 2) hbound
  simpa only [Real.dist_eq, euclideanBallAverageSequence] using
    (havg.trans_lt (by linarith : epsilon / 2 < epsilon))

/-- Every local continuous representative agrees pointwise with the canonical
global ball-average representative. -/
theorem euclideanBallAverageRepresentative_eq_local
    [NeZero d] {W V : Set (Vec d)} {u : H1Function W}
    {g : Vec d → ℝ} (hV : IsOpen V) (hVW : V ⊆ W)
    (hlocal : g =ᵐ[volume.restrict V] u.toFun)
    (hcont : ContinuousOn g V) {x : Vec d} (hx : x ∈ V) :
    euclideanBallAverageRepresentative u.toFun x = g x := by
  exact Tendsto.limUnder_eq
    (tendsto_euclideanBallAverageSequence_of_localRepresentative
      hV hVW hlocal hcont hx)

/-- A local Schauder representative on a rescaled ball identifies pointwise
with the canonical global representative on the physical inner half-ball. -/
theorem euclideanBallAverageRepresentative_eq_physicalBallRepresentative
    [NeZero d] {W : Set (Vec d)}
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W) {u : H1Function W}
    {uRep : Vec d → ℝ}
    (hcont : ContinuousOn uRep (smallContrastBall d (1 / 2)))
    (hrep : uRep =ᵐ[volume.restrict (smallContrastUnitBall d)]
      (ballToUnitH1 x hrho
        (u.restrict (isOpen_euclideanBall x rho) hball)).toFun) :
    ∀ y ∈ euclideanBall x (rho / 2),
      euclideanBallAverageRepresentative u.toFun y =
        physicalBallRepresentative x rho uRep y := by
  let v := u.restrict (isOpen_euclideanBall x rho) hball
  have hae : physicalBallRepresentative x rho uRep =ᵐ[
      volume.restrict (euclideanBall x (rho / 2))] u.toFun := by
    simpa [v] using! physicalBallRepresentative_ae_eq hrho (u := v) hrep
  have hcontPhysical :=
    continuousOn_physicalBallRepresentative (x := x) hrho hcont
  intro y hy
  exact euclideanBallAverageRepresentative_eq_local
    (isOpen_euclideanBall x (rho / 2))
    ((euclideanBall_subset_euclideanBall (by positivity) (by linarith)).trans hball)
    hae hcontPhysical hy

/-- A countable open cover by local continuous representatives identifies the
canonical representative with the Sobolev function almost everywhere. -/
theorem euclideanBallAverageRepresentative_ae_eq_of_countableCover
    [NeZero d] {ι : Type*} [Countable ι]
    {W : Set (Vec d)} (hW : MeasurableSet W) {u : H1Function W}
    (V : ι → Set (Vec d)) (g : ι → Vec d → ℝ)
    (hVopen : ∀ n, IsOpen (V n)) (hVW : ∀ n, V n ⊆ W)
    (hcover : W ⊆ ⋃ n, V n)
    (hlocal : ∀ n, g n =ᵐ[volume.restrict (V n)] u.toFun)
    (hcont : ∀ n, ContinuousOn (g n) (V n)) :
    euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict W] u.toFun := by
  have hn : ∀ n, ∀ᵐ x ∂volume, x ∈ V n →
      euclideanBallAverageRepresentative u.toFun x = u.toFun x := by
    intro n
    have hloc : ∀ᵐ x ∂volume, x ∈ V n → g n x = u.toFun x :=
      (ae_restrict_iff' (hVopen n).measurableSet).1 (hlocal n)
    filter_upwards [hloc] with x hx
    intro hxV
    rw [euclideanBallAverageRepresentative_eq_local
      (hVopen n) (hVW n) (hlocal n) (hcont n) hxV]
    exact hx hxV
  refine (ae_restrict_iff' hW).2 ?_
  filter_upwards [ae_all_iff.2 hn] with x hxall hxW
  have hxUnion := hcover hxW
  simp only [Set.mem_iUnion] at hxUnion
  obtain ⟨n, hxn⟩ := hxUnion
  exact hxall n hxn

/-- The same countable local data make the canonical representative
continuous on the whole covered window. -/
theorem continuousOn_euclideanBallAverageRepresentative_of_countableCover
    [NeZero d] {ι : Type*} [Countable ι]
    {W : Set (Vec d)} {u : H1Function W}
    (V : ι → Set (Vec d)) (g : ι → Vec d → ℝ)
    (hVopen : ∀ n, IsOpen (V n)) (hVW : ∀ n, V n ⊆ W)
    (hcover : W ⊆ ⋃ n, V n)
    (hlocal : ∀ n, g n =ᵐ[volume.restrict (V n)] u.toFun)
    (hcont : ∀ n, ContinuousOn (g n) (V n)) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) W := by
  intro x hxW
  have hxUnion := hcover hxW
  simp only [Set.mem_iUnion] at hxUnion
  obtain ⟨n, hxn⟩ := hxUnion
  have heq : euclideanBallAverageRepresentative u.toFun =ᶠ[𝓝 x] g n :=
    Filter.mem_of_superset ((hVopen n).mem_nhds hxn) fun y hy ↦
      euclideanBallAverageRepresentative_eq_local
        (hVopen n) (hVW n) (hlocal n) (hcont n) hy
  exact ((hcont n).continuousAt ((hVopen n).mem_nhds hxn)).congr_of_eventuallyEq
    heq |>.continuousWithinAt

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
