module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.GMCLocalLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousGlobalRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout

@[expose] public section

/-!
# Continuous representatives of compact-data massive local limits

The compatible centered-cube solutions produced by the monotone exhaustion
are replaced by one global canonical shrinking-ball-average representative.
Local almost-everywhere agreement makes the defining average sequences
eventually equal on each cube, so the local Schauder representatives glue
without any choice on overlaps.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- Locally almost-everywhere equal functions have eventually equal
shrinking-ball averages at every interior point. -/
theorem eventuallyEq_euclideanBallAverageSequence_of_ae_eq_on_open
    {W : Set (Vec d)} (hW : IsOpen W) {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict W] g) {x : Vec d} (hx : x ∈ W) :
    euclideanBallAverageSequence f x =ᶠ[atTop]
      euclideanBallAverageSequence g x := by
  obtain ⟨eta, heta, hballW⟩ := Metric.isOpen_iff.1 hW x hx
  have hradius : ∀ᶠ n : ℕ in atTop,
      euclideanBallRepresentativeRadius n < eta :=
    tendsto_euclideanBallRepresentativeRadius.eventually (Iio_mem_nhds heta)
  filter_upwards [hradius] with n hn
  have hsub : euclideanBall x (euclideanBallRepresentativeRadius n) ⊆ W :=
    (euclideanBall_subset_metricBall (euclideanBallRepresentativeRadius_pos n)).trans
      ((Metric.ball_subset_ball hn.le).trans hballW)
  have hfgBall : f =ᵐ[
      volume.restrict (euclideanBall x (euclideanBallRepresentativeRadius n))] g :=
    hfg.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact averageOn_eq_of_ae_eq hfgBall

private theorem exists_mem_centeredCube (x : Vec d) :
    ∃ n : ℕ, x ∈ cube d (n : ℤ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * ‖x‖)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hpow : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> nlinarith [neg_le_of_abs_le hxi, le_of_abs_le hxi]

/-- A bounded pointwise function with compatible massive weak solutions on
all centered cubes has a global continuous canonical representative for the
GMC coefficient. -/
theorem continuous_and_ae_eq_localMassiveLimitRepresentative
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    {mu U : ℝ} (f : C_c(Vec d, ℝ)) {u : Vec d → ℝ}
    (huBound : ∀ x, |u x| ≤ U)
    (huLocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
          (cube d (k : ℤ)) uLocal f) :
    Continuous (euclideanBallAverageRepresentative u) ∧
      euclideanBallAverageRepresentative u =ᵐ[volume] u := by
  choose uLocal huLocalAE huLocalSolution using huLocal
  let v : ℕ → Vec d → ℝ := fun k ↦
    euclideanBallAverageRepresentative (uLocal k).toFun
  have huLocalBound : ∀ k, ∀ᵐ x ∂(volume.restrict (cube d (k : ℤ))),
      |(uLocal k).toFun x| ≤ U := by
    intro k
    filter_upwards [huLocalAE k] with x hx
    rw [hx]
    exact huBound x
  have hv : ∀ k,
      ContinuousOn (v k) (cube d (k : ℤ)) ∧
        v k =ᵐ[volume.restrict (cube d (k : ℤ))] (uLocal k).toFun := by
    intro k
    exact continuousOn_and_ae_eq_massiveWeakSolutionRepresentative_of_two_le
      M.shellPrefix.dimension
      (continuous_coefficientAt M L omega).continuousOn
      (fun x _hx ↦ coefficientAt_pos M L omega x) f
      (B.rho_measurable k) (B.rho_bounded k) (huLocalBound k)
      (huLocalSolution k)
  have hcanonical : ∀ k, Set.EqOn (euclideanBallAverageRepresentative u)
      (v k) (cube d (k : ℤ)) := by
    intro k x hx
    have hseq : euclideanBallAverageSequence u x =ᶠ[atTop]
        euclideanBallAverageSequence (uLocal k).toFun x :=
      eventuallyEq_euclideanBallAverageSequence_of_ae_eq_on_open
        (isOpen_openCubeSet (originCube d (k : ℤ))) (huLocalAE k).symm hx
    have htendstoLocal : Tendsto
        (euclideanBallAverageSequence (uLocal k).toFun x) atTop (𝓝 (v k x)) :=
      tendsto_euclideanBallAverageSequence_of_localRepresentative
        (isOpen_openCubeSet (originCube d (k : ℤ))) Set.Subset.rfl
        (hv k).2 (hv k).1 hx
    have htendsto : Tendsto (euclideanBallAverageSequence u x) atTop
        (𝓝 (v k x)) :=
      (tendsto_congr' hseq).2 htendstoLocal
    exact htendsto.limUnder_eq
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨k, hx⟩ := exists_mem_centeredCube x
    exact ((hv k).1.congr fun y hy ↦ hcanonical k hy).continuousAt
      ((isOpen_openCubeSet (originCube d (k : ℤ))).mem_nhds hx)
  · have hk : ∀ k : ℕ, ∀ᵐ x ∂volume,
        x ∈ cube d (k : ℤ) → euclideanBallAverageRepresentative u x = u x := by
      intro k
      have hvAEGlobal : ∀ᵐ x ∂volume,
          x ∈ cube d (k : ℤ) → v k x = (uLocal k).toFun x :=
        (ae_restrict_iff'
          (isOpen_openCubeSet (originCube d (k : ℤ))).measurableSet).1 (hv k).2
      have huAEGlobal : ∀ᵐ x ∂volume,
          x ∈ cube d (k : ℤ) → (uLocal k).toFun x = u x :=
        (ae_restrict_iff'
          (isOpen_openCubeSet (originCube d (k : ℤ))).measurableSet).1
          (huLocalAE k)
      filter_upwards [hvAEGlobal, huAEGlobal] with x hxv hxu
      intro hx
      rw [hcanonical k hx, hxv hx, hxu hx]
    filter_upwards [ae_all_iff.2 hk] with x hx
    obtain ⟨k, hxk⟩ := exists_mem_centeredCube x
    exact hx k hxk

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
