module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryDivergenceKernel
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryKernelStream

@[expose] public section

/-!
# Two-scale stationary antisymmetric stream

The explicit divergence kernel between two product mollifiers is fed to the
stationary kernel-stream construction.  The small smoothing scale is also
proved to be an approximate identity directly in stationary `L²`.

The remaining analytic input for convergence to the original solenoidal field
is the large-scale decorrelation of the projected one-step forcing.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


variable {d : ℕ}

namespace Stationary

/-- Stationary mollification is linear in the spatial kernel for a fixed
strongly continuous orbit. -/
theorem mollifyL2_kernel_sub_of_continuous
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [AddAction (Vec d) Omega]
    [MeasurableConstVAdd (Vec d) Omega]
    [VAddInvariantMeasure (Vec d) Omega mu]
    {kappa eta : Vec d → ℝ}
    (hkappa : Continuous kappa) (hkappaCompact : HasCompactSupport kappa)
    (heta : Continuous eta) (hetaCompact : HasCompactSupport eta)
    (F : VectorL2 d mu)
    (hF : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    mollifyL2 (mu := mu) (fun x => kappa x - eta x) F =
      mollifyL2 (mu := mu) kappa F - mollifyL2 (mu := mu) eta F := by
  rw [mollifyL2, mollifyL2, mollifyL2]
  simp_rw [sub_smul]
  exact integral_sub
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hkappaCompact F hF)
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) heta hetaCompact F hF)

end Stationary



theorem toLp_streamVectorPack_representativeMollify_eq_mollifyL2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R)) :
    let X := stationaryVectorRepresentative M R
    let psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun i =>
      representativeMollify kappa (representativeCoord X i)
    let hpsiM : ∀ i, StronglyMeasurable (psi i) := fun i =>
      stronglyMeasurable_representativeMollify hkappa
        (stronglyMeasurable_representativeCoord
          (stronglyMeasurable_stationaryVectorRepresentative M R) i)
    let hpsi : ∀ i, MemLp (psi i) 2 M.P.toMeasure := fun i =>
      memLp_two_representativeMollify M hkappa
        (hkappa.integrable_of_hasCompactSupport hcompact)
        (stronglyMeasurable_representativeCoord
          (stronglyMeasurable_stationaryVectorRepresentative M R) i)
        (memLp_representativeCoord M
          (stronglyMeasurable_stationaryVectorRepresentative M R)
          (memLp_two_stationaryVectorRepresentative M R) i)
    let hpack := memLp_two_streamVectorPack M hpsiM hpsi
    letI := potentialSequenceVAddInvariant M
    hpack.toLp (streamVectorPack psi) =
      Stationary.mollifyL2 (mu := M.P.toMeasure) kappa R := by
  let := potentialSequenceVAddInvariant M
  let X := stationaryVectorRepresentative M R
  let psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun i =>
    representativeMollify kappa (representativeCoord X i)
  let hpsiM : ∀ i, StronglyMeasurable (psi i) := fun i =>
    stronglyMeasurable_representativeMollify hkappa
      (stronglyMeasurable_representativeCoord
        (stronglyMeasurable_stationaryVectorRepresentative M R) i)
  let hpsi : ∀ i, MemLp (psi i) 2 M.P.toMeasure := fun i =>
    memLp_two_representativeMollify M hkappa
      (hkappa.integrable_of_hasCompactSupport hcompact)
      (stronglyMeasurable_representativeCoord
        (stronglyMeasurable_stationaryVectorRepresentative M R) i)
      (memLp_representativeCoord M
        (stronglyMeasurable_stationaryVectorRepresentative M R)
        (memLp_two_stationaryVectorRepresentative M R) i)
  let hpack := memLp_two_streamVectorPack M hpsiM hpsi
  apply Stationary.vectorL2_eq_of_coord_eq
  intro i
  rw [vectorL2Coord_toLp_representative M
    (stronglyMeasurable_streamVectorPack hpsiM) hpack i]
  change (hpsi i).toLp (psi i) =
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i
      (Stationary.mollifyL2 (mu := M.P.toMeasure) kappa R)
  rw [Stationary.vectorL2Coord_mollifyL2_of_continuous
    hkappa hcompact R hR i]
  have hcoord : Stationary.vectorL2Coord (mu := M.P.toMeasure) i R =
      (memLp_representativeCoord M
        (stronglyMeasurable_stationaryVectorRepresentative M R)
        (memLp_two_stationaryVectorRepresentative M R) i).toLp
        (representativeCoord X i) := by
    simpa only [X, toLp_stationaryVectorRepresentative] using!
      (vectorL2Coord_toLp_representative M
        (stronglyMeasurable_stationaryVectorRepresentative M R)
        (memLp_two_stationaryVectorRepresentative M R) i)
  have horbit : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.comp hR
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i R
  have hrep := toLp_representativeMollify_eq_mollifyL2 M hkappa hcompact
    (stronglyMeasurable_representativeCoord
      (stronglyMeasurable_stationaryVectorRepresentative M R) i)
    (memLp_representativeCoord M
      (stronglyMeasurable_stationaryVectorRepresentative M R)
      (memLp_two_stationaryVectorRepresentative M R) i)
    (by rw [← hcoord]; exact horbit)
  rw [hcoord]
  simpa only [psi, hpsi, X] using! hrep

/-- The explicit kernel family connecting product mollifiers at radii `r` and
`s`. -/
def twoScaleStationaryStreamKernel {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) : Fin d → Vec d → ℝ :=
  fun m x => streamDivKernel
    (streamScaledBump hr) (streamScaledBump hs) (r + s) x m

theorem contDiff_twoScaleStationaryStreamKernel {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (twoScaleStationaryStreamKernel (d := d) hr hs m) :=
  contDiff_twoScaleStreamKernel hr hs m

theorem hasCompactSupport_twoScaleStationaryStreamKernel {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (m : Fin d) :
    HasCompactSupport (twoScaleStationaryStreamKernel (d := d) hr hs m) :=
  hasCompactSupport_twoScaleStreamKernel hr hs m

theorem kernelDeriv_sum_twoScaleStationaryStreamKernel {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (x : Vec d) :
    ∑ m : Fin d, Stationary.kernelDeriv
        (twoScaleStationaryStreamKernel (d := d) hr hs m) m x =
      streamProductDensity d hr x - streamProductDensity d hs x := by
  simpa only [Stationary.kernelDeriv, streamCoordDeriv,
    twoScaleStationaryStreamKernel] using!
      streamCoordDeriv_sum_twoScaleStreamKernel (d := d) hr hs x

/-- The concrete antisymmetric stream whose divergence is the realization of
the difference between small- and large-scale product smoothings. -/
theorem exists_twoScaleStationaryKernelStream
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R))
    (hsol : letI := potentialSequenceVAddInvariant M
      R ∈ Stationary.stationarySolenoidalSubspace
        (mu := M.P.toMeasure) (d := d)) :
    ∃ S : _root_.SubdiffusiveProcess.Model.PotentialSample d → Fin d → HilbertVec d,
      ∃ D : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d,
        StronglyMeasurable S ∧ MemLp S 2 M.P.toMeasure ∧
        (∀ᵐ omega ∂M.P.toMeasure, ∀ i m : Fin d,
          ContDiff ℝ (⊤ : ℕ∞) (stationaryStreamRealization S omega i m)) ∧
        (∀ omega, ∀ i m : Fin d,
          stationaryStreamRealization S omega m i =
            -stationaryStreamRealization S omega i m) ∧
        (∀ᵐ omega ∂M.P.toMeasure, ∀ x : Vec d,
          streamDivergence (stationaryStreamRealization S omega) x =
            (realize D omega x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 M.P.toMeasure ∧
        (∀ᵐ omega ∂M.P.toMeasure,
          D omega = streamVectorPack (fun i => representativeMollify
            (fun x => streamProductDensity d hr x -
              streamProductDensity d hs x)
            (representativeCoord (stationaryVectorRepresentative M R) i))
            omega) := by
  refine exists_stationaryKernelStream M
    (contDiff_twoScaleStationaryStreamKernel hr hs)
    (hasCompactSupport_twoScaleStationaryStreamKernel hr hs)
    ((continuous_streamProductDensity d hr).sub
      (continuous_streamProductDensity d hs))
    ((integrable_streamProductDensity d hr).sub
      (integrable_streamProductDensity d hs)) ?_ R hR hsol
  intro x
  exact (kernelDeriv_sum_twoScaleStationaryStreamKernel hr hs x).symm

/-- Product mollifiers form an approximate identity for every strongly
continuous stationary `L²` orbit. -/
theorem exists_streamProduct_radius_norm_mollifyL2_sub_lt
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      letI := potentialSequenceVAddInvariant M
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hr) R - R‖ < epsilon := by
  let := potentialSequenceVAddInvariant M
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  have heta_lt : eta < epsilon := by
    dsimp only [eta]
    linarith
  have hcont : ContinuousAt
      (fun z : Vec d => Stationary.koopman
        (mu := M.P.toMeasure) z R) 0 := hR.continuousAt
  have hnhds : ∀ᶠ z : Vec d in nhds 0,
      ‖Stationary.koopman (mu := M.P.toMeasure) z R - R‖ < eta := by
    have hnorm : ContinuousAt
        (fun z : Vec d =>
          ‖Stationary.koopman (mu := M.P.toMeasure) z R - R‖) 0 :=
      (hcont.sub (continuousAt_const : ContinuousAt
        (fun _ : Vec d => R) 0)).norm
    exact hnorm.eventually_lt continuousAt_const (by
      simpa only [Stationary.koopman_zero, sub_self, norm_zero] using! heta)
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.1 hnhds
  refine ⟨r, hr, lt_of_le_of_lt
    (Stationary.norm_mollifyL2_sub_le_of_continuous
      (mu := M.P.toMeasure) (epsilon := eta)
      (Stationary.L2Mollifier.ofStreamProduct d hr) R hR ?_) heta_lt⟩
  intro y hy
  apply le_of_lt (hrball (y := -y) ?_)
  rw [dist_zero_right, norm_neg]
  change y ∈ Metric.ball (0 : Vec d) r at hy
  simpa only [Metric.mem_ball, dist_zero_right] using! hy

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
