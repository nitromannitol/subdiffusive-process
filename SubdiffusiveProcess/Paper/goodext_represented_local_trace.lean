import SubdiffusiveProcess.Paper.goodext_cutoff_local_trace_eventual
import SubdiffusiveProcess.Paper.goodext_represented_local_trace_controls
import SubdiffusiveProcess.Analysis.NormalizedCoefficientLimits

/-! A normalized coefficient limit and equal-law cutoff controls give the sharp
local trace estimate. The stated limiting form and energy measure are retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Equal center, side and order coordinates identify the literal cutoff upper coefficient. -/
theorem aux_goodext_represented_local_trace_coefficient_congr
    {d : ℕ} (I : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (xi : BilateralField d) (N : ℕ)
    (z1 z2 : SpatialCoordinates d) (r1 r2 : ℝ) (h1 : 0 < r1) (h2 : 0 < r2)
    (s1 s2 : ℝ) (hz : z1 = z2) (hr : r1 = r2) (hs : s1 = s2) :
    I.Lam z1 r1 h1 (cutoffPositiveCoefficient M H xi N z1 h1) z1 r1 s1 2 =
      I.Lam z2 r2 h2 (cutoffPositiveCoefficient M H xi N z2 h2) z2 r2 s2 2 := by
  cases hz
  cases hr
  cases hs
  rfl

/-- The normalized upper-coefficient limit bounds the response of every actual Hölder trace on a padded local cell. -/
theorem goodext_represented_local_trace
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (S : ResponseSpace (centeredCube z r hr))
      (hS : S.space = killedSobolevGraph (centeredCube z r hr))
      (k : ℕ) (z0 : SpatialCoordinates d) (N : ℕ → ℕ) (hN : StrictMono N)
      (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
      (env : ℕ → Omega → BilateralField d)
      (hEnv : ∀ n, Measurable (env n))
      (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
      (GN : ℕ → BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
        DomainL2 (centeredCube z r hr))
      (hGN : ∀ n xi f, GN n xi f =
        (responseSolution S (cutoffPositiveCoefficient M H xi n z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
      (G : Omega → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (hG : ∀ᵐ om ∂P, Tendsto (fun n => GN (N n) (env n om)) atTop (𝓝 (G om)))
      (E : Omega → DirichletForm.ClosedForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
      (hE : ∀ om u, (E om).energy u = limitFormEnergy (G om) u)
      (Gamma : ∀ om, DirichletForm.EnergyMeasure (E om))
      (hcont : ∀ᵐ om ∂P, ∀ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
      (scale : ℕ → Omega → ℝ) (s L : Omega → ℝ)
      (hs : ∀ᵐ om ∂P, 0 < s om ∧ Tendsto (fun n => scale n om) atTop (𝓝 (s om)))
      (hNorm : TendstoInMeasure P
        (fun n om => I.Lam z0 ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
          (cutoffPositiveCoefficient M H (env n om) (N n) z0 (by positivity))
          z0 ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 / scale n om) atTop L)
      (cap : ℝ) (hcap : 0 < cap),
    ∀ᵐ om ∂P, L om ≤ cap →
      Metric.ball z0 (3 * ((3 : ℝ) ^ (-(k : ℤ))) / 2) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ b : SpatialCoordinates d → ℝ,
        ContinuousOn b (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) →
        IsHolderOn beta (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) b →
        ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
          v ∈ (E om).domain ∧
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2)), V x = b x) ∧
          ((Gamma om).measure v (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))).toReal ≤
            C * (2 * cap * s om) * ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) *
              (((3 : ℝ) ^ (-(k : ℤ))) ^ beta * holderSeminorm beta
                (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) b) ^ 2 := by
  obtain ⟨C, hC, hTrace⟩ := goodext_cutoff_local_trace_eventual d hd I X Sob beta hb
  obtain ⟨delta0, hdelta0, hControls⟩ := goodext_represented_local_trace_controls
    d hd I Pin X W Cp Sob Interp t alpha beta ht htd ha ha1 hb
  refine ⟨C, delta0, hC, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS k z0 N hN Omega _ P _ env hEnv hLaw
    GN hGN G hG E hE Gamma hcont scale s L hs hNorm cap hcap
  obtain ⟨rho, hrho, hNormAE⟩ := hNorm.exists_seq_tendsto_ae
  have hc := hControls M Rm Sreg It H hIR hdelta z r hr S hS k
    (OddGridIndex d (triadicHalf 1))
    (fun j => oddGridCenter z0 (3 * ((3 : ℝ) ^ (-(k : ℤ)))) (triadicHalf 1) j)
    (fun n => N (rho n)) (hN.comp hrho) Omega P
    (fun n => env (rho n)) (fun n => hEnv (rho n)) (fun n => hLaw (rho n))
  filter_upwards [hc, hNormAE, hs, hG, hcont] with om hc hn hs hg hcont
  intro hL hPsub b hbc hbh
  obtain ⟨seq, hseq, ⟨A⟩, hcell, hCells⟩ := hc
  choose Lam hLam0 hLam hReg using hCells
  have hCentral : ∀ᶠ n in atTop,
      I.Lam z0 ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H (env (rho (seq n)) om) (N (rho (seq n))) z0 (by positivity))
        z0 ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 ≤ 2 * cap * s om :=
    eventually_upper_coefficient_of_normalized_tendsto _ _ (L om) (s om) cap hs.1 hcap
      (hs.2.comp (hrho.comp hseq).tendsto_atTop) (hn.comp hseq.tendsto_atTop) hL
  exact hTrace M H (fun n => env (rho (seq n)) om) (fun n => N (rho (seq n)))
    z r hr S hS A t alpha ha hcell
    (fun n => GN (N (rho (seq n))) (env (rho (seq n)) om)) (G om)
    (fun n f => hGN _ _ f) (hg.comp (hrho.comp hseq).tendsto_atTop)
    (E om) (hE om) hcont (Gamma om) z0 ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
    (by positivity) hPsub hReg
    (zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega))
    Lam hLam0 (fun n j => hLam j n) (2 * cap * s om) (mul_nonneg (mul_nonneg (by norm_num) hcap.le) hs.1.le)
    hCentral b hbc hbh
end Paper
