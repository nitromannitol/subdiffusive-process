import SubdiffusiveProcess.Paper.lim_cor_paths
import SubdiffusiveProcess.Paper.physical_rescaling
import SubdiffusiveProcess.Section10.LegacyPhysicalAttachment
import SubdiffusiveProcess.Section10.LegacyPathsSupNorm
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.Main.DiffusionPath

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper



theorem lim_paths
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 → ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
      ∀ p : ℝ, 0 < p → ∃ cp : ℝ, 0 < cp ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (phi : ℕ → ℕ) (hphi : StrictMono phi)
        (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d)
        (hxs : Tendsto xs atTop (𝓝 x))
        (Plim : ProbabilityMeasure (DiffusionPath d))
        (hPlim : ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
          Tendsto (fun n => ∫ omega, (∫ w, G w ∂(KN (phi n) (omega, xs n)))
              ∂(chaosSampleLaw M).toMeasure) atTop
            (𝓝 (∫ w, G w ∂(Plim : Measure (DiffusionPath d))))),
        -- running maximum `M_t = sup_{0 ≤ s ≤ t} |Z_s - Z_0|`
        let Mt : ℝ≥0 → DiffusionPath d → ℝ := fun t w =>
          ⨆ s : Set.Icc (0 : ℝ≥0) t, ‖w s - w 0‖
        (∀ beta : ℝ, 0 < beta → beta < eta →
          ∀ᵐ w ∂(Plim : Measure (DiffusionPath d)),
            (∀ᶠ (t : ℝ≥0) in 𝓝[>] 0, (1 / 6 : ℝ) * (t : ℝ) ^ (1 / (2 + beta)) ≤ Mt t w) ∧
            Tendsto (fun t : ℝ≥0 => Mt t w / Real.sqrt t) (𝓝[>] 0) atTop) ∧
        (∀ᵐ w ∂(Plim : Measure (DiffusionPath d)), ∀ gamma : ℝ, 0 ≤ gamma →
          (fun t : ℝ≥0 => ‖w t - w 0‖) =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma) →
          gamma ≤ 1 / (2 + eta)) ∧
        (∀ epsilon : ℝ, 0 < epsilon → ∀ᵐ w ∂(Plim : Measure (DiffusionPath d)),
          ∀ᶠ k : ℕ in atTop,
            ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ≤
              ENNReal.ofReal ((k : ℝ) ^ (1 + epsilon) * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
        ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
          ENNReal.ofReal (cp * (t : ℝ) ^ (p / (2 + eta))) ≤
            ∫⁻ w, ENNReal.ofReal ((Mt t w) ^ p) ∂(Plim : Measure (DiffusionPath d)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hmodels⟩ := lim_cor_paths hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hM
  obtain ⟨eta, Cdecay, heta, hCdecay, hplanar, hdecay, hsmall, hmoments⟩ := hmodels M hM
  refine ⟨Cdecay, eta, hCdecay, heta, hplanar, hdecay, ?_⟩
  intro p hp
  obtain ⟨cp, hcp, hmoment⟩ := hmoments p hp
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  refine ⟨cp * (d : ℝ) ^ (-p), mul_pos hcp (Real.rpow_pos_of_pos hdpos _), ?_⟩
  intro H hH PN KN hKN hin L hL hLloc phi hphi xs x hxs Plim hPlim
  obtain ⟨X, hX, hphysical, hphysicalLimit⟩ :=
    SubdiffusiveProcess.Section10.LegacyPhysicalAttachment.exists_annealed_limit
      aux_physical_rescaling_kernel_conjugacy_massive_unscale
      M H hH PN KN hKN hin phi xs Plim hPlim
  have hsource : aux_lim_cor_paths_IsAnnealedLimit M X true phi xs Plim := hphysicalLimit
  obtain ⟨cepsilon, hcepsilon, hsmallPhysical, _⟩ := hsmall 1 one_pos
  have hae := hsmallPhysical X hX hphysical true phi hphi xs x hxs Plim hsource
  have hexit : ∀ᵐ w ∂(Plim : Measure (DiffusionPath d)),
      ∀ᶠ k : ℕ in atTop,
        SubdiffusiveProcess.Section10.EndpointPaths.smallExit k w ≤
          ENNReal.ofReal (SubdiffusiveProcess.Section10.EndpointPaths.endpoint eta 1 k) := by
    filter_upwards [hae] with w hw
    exact hw.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro beta hbeta hbetaeta
    filter_upwards [hexit] with w hw
    exact SubdiffusiveProcess.Section10.LegacyPathsSupNorm.legacy_power_and_sqrt
      (by omega) eta heta w hw beta hbeta hbetaeta
  · filter_upwards [hexit] with w hw
    exact SubdiffusiveProcess.Section10.LegacyPathsSupNorm.holder_exponent_le eta heta w hw
  · intro epsilon hepsilon
    obtain ⟨c, hc, hsmallPhysical, _⟩ := hsmall epsilon hepsilon
    filter_upwards [hsmallPhysical X hX hphysical true phi hphi xs x hxs Plim hsource]
      with w hw
    exact hw.2.2.2
  · intro t ht ht1
    exact SubdiffusiveProcess.Section10.LegacyPathsSupNorm.moment_lower (by omega)
      (Plim : Measure (DiffusionPath d)) p cp t eta hp t
      (hmoment X hX hphysical true phi hphi xs x hxs Plim hsource t ht ht1)

end Paper
