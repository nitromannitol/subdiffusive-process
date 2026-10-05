module

public import SubdiffusiveProcess.Sobolev.HarmonicUniformComparison
public import SubdiffusiveProcess.Sobolev.SmoothBoundaryApproximation
public import SubdiffusiveProcess.Sobolev.NativeHarmonicData
public import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
public import Mathlib.Topology.TietzeExtension

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess

/-- A harmonic extension of globally continuous native data on a cube is continuous up to its boundary. -/
theorem continuous_boundary_representative_of_native_cube_datum
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (A : SpatialCoordinates d → ℝ) (hA : Continuous A)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hbounds : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lam ≤ A x ∧ A x ≤ Lam)
    (beta u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hbeta : Continuous beta.toFun)
    (hu : IsWeaklyHarmonicOn A (centeredCube z r hr : Set (SpatialCoordinates d)) u)
    (hut : HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) u beta) :
    ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      u.toFun =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = beta.toFun x := by
  classical
  let W : Set (SpatialCoordinates d) := centeredCube z r hr
  have hW : IsOpenBoundedConvexDomain W := lane2_isOpenBoundedConvexDomain_centeredCube z hr
  have hWne : W.Nonempty := ⟨z, Metric.mem_ball_self (half_pos hr)⟩
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heps : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have happrox (n : ℕ) : ∃ phi : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ phi ∧ ∀ x, |phi x - beta.toFun x| < eps n := by
    obtain ⟨phi, hphi, hbound, _⟩ := hbeta.exists_contDiff_approx (⊤ : ℕ∞)
      (ε := fun _ => eps n) continuous_const (fun _ => by dsimp [eps]; positivity)
    exact ⟨phi, hphi, fun x => by simpa only [Real.dist_eq] using hbound x⟩
  choose phi hphi hphiBound using happrox
  let datum : ℕ → H1Function W := fun n =>
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW ((hphi n).of_le (by norm_num))
  have hdatum : ∀ n, (datum n).toFun = phi n := fun _ => rfl
  have hEll := lane2_isEllipticFieldOn_scalar hW.isOpen.measurableSet hA.measurable hlam hbounds
  have hex : ∀ n, ∃ v : H1Function W, HasZeroTraceDifferenceOn W v (datum n) ∧
      IsWeaklyHarmonicOn A W v := fun n =>
    lane2_exists_weaklyHarmonic_of_zeroTrace hW hWne hEll (datum n)
  choose v hvt hvharm using hex
  have hrep : ∀ n, ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure W) ∧ V =ᵐ[volume.restrict W] (v n).toFun ∧
      ∀ x ∈ frontier W, V x = phi n x := by
    intro n
    exact (lane2_cellDirichletBoundaryContinuity hd).continuous_up_to_boundary
      z r hr A lam Lam hlam hA hbounds (datum n) (v n)
      (by rw [hdatum]; exact hphi n) (hvharm n) (hvt n)
  choose Vn hVn hVnae hVntrace using hrep
  have herror : ∀ n, ∀ᵐ x ∂volume.restrict W, |u.toFun x - Vn n x| ≤ eps n := by
    intro n
    have hcomparison := ae_abs_sub_le_of_harmonic_datum_bound hW A hA.measurable
      lam Lam hlam hbounds u (v n) beta (datum n) hu (hvharm n) hut (hvt n)
      (eps n) (fun x => by
        rw [hdatum, abs_sub_comm]
        exact (hphiBound n x).le)
    filter_upwards [hcomparison, hVnae n] with x hx hrep
    rwa [← hrep] at hx
  have hpair : ∀ n m x, x ∈ closure W → |Vn n x - Vn m x| ≤ eps n + eps m := by
    intro n m
    apply le_on_closure_of_continuousOn_of_ae_le hW.isOpen
      (fun x => |Vn n x - Vn m x|) ((hVn n).sub (hVn m)).abs (eps n + eps m)
    filter_upwards [herror n, herror m] with x hn hm
    calc
      |Vn n x - Vn m x| ≤ |Vn n x - u.toFun x| + |u.toFun x - Vn m x| :=
        abs_sub_le _ _ _
      _ ≤ eps n + eps m := by rw [abs_sub_comm (Vn n x)]; exact add_le_add hn hm
  have hcauchy : UniformCauchySeqOn Vn atTop (closure W) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro delta hdelta
    obtain ⟨N, hN⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds (half_pos hdelta)))
    refine ⟨N, fun n hn m hm x hx => ?_⟩
    rw [Real.dist_eq]
    exact (hpair n m x hx).trans_lt (by linarith [hN n hn, hN m hm])
  have hlimit : ∀ x : closure W, ∃ l : ℝ,
      Tendsto (fun n => Vn n x) atTop (𝓝 l) := fun x =>
    cauchySeq_tendsto_of_complete (hcauchy.cauchySeq x.property)
  choose limit hlimit using hlimit
  let V : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ closure W then limit ⟨x, hx⟩ else 0
  have hlim : ∀ x ∈ closure W, Tendsto (fun n => Vn n x) atTop (𝓝 (V x)) := by
    intro x hx
    dsimp only [V]
    rw [dite_eq_left hx]
    exact hlimit ⟨x, hx⟩
  have huniform : TendstoUniformlyOn Vn V atTop (closure W) :=
    hcauchy.tendstoUniformlyOn_of_tendsto hlim
  refine ⟨V, huniform.continuousOn (Eventually.of_forall hVn).frequently, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr herror, self_mem_ae_restrict hW.isOpen.measurableSet]
      with x hx hxW
    have htoU : Tendsto (fun n => Vn n x) atTop (𝓝 (u.toFun x)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun n => dist_nonneg) (fun n => by
        rw [Real.dist_eq, abs_sub_comm]
        exact hx n) heps
    exact tendsto_nhds_unique htoU (hlim x (subset_closure hxW))
  · intro x hx
    have hphiLim : Tendsto (fun n => phi n x) atTop (𝓝 (beta.toFun x)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun n => dist_nonneg) (fun n => by
        rw [Real.dist_eq]
        exact (hphiBound n x).le) heps
    have htraceLim : Tendsto (fun n => Vn n x) atTop (𝓝 (beta.toFun x)) :=
      hphiLim.congr (fun n => (hVntrace n x hx).symm)
    exact tendsto_nhds_unique (hlim x (frontier_subset_closure hx)) htraceLim


end SubdiffusiveProcess
