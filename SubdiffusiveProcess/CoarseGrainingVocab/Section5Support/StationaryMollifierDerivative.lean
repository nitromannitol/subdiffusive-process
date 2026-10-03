module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollification
public import Mathlib.Analysis.Convolution

@[expose] public section

/-!
# Derivatives of stationary Hilbert-space mollifications

The translated stationary mollifier is an ordinary Hilbert-valued
convolution of its smooth kernel with the strongly continuous Koopman orbit.
Mathlib's convolution derivative theorem therefore puts the derivative on
the kernel.  This mirrors
`Algsuperdiff/Section3/Provider/Corrector/MollifiedPrimitive.lean`, but works
directly in stationary `L²` and needs no samplewise realization layer.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]
variable [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
variable [ContinuousVAdd (Vec d) Omega]
variable [IsLocallyFiniteMeasure mu] [mu.InnerRegularCompactLTTop]

/-- The strongly continuous Hilbert-valued Koopman orbit. -/
def koopmanOrbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Lp E 2 mu) : Vec d → Lp E 2 mu :=
  fun z => koopman (mu := mu) z X

theorem continuous_koopmanOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Lp E 2 mu) : Continuous (koopmanOrbit (mu := mu) (d := d) X) :=
  continuous_koopman_orbit (d := d) X

theorem locallyIntegrable_koopmanOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Lp E 2 mu) : LocallyIntegrable
      (koopmanOrbit (mu := mu) (d := d) X) volume :=
  (continuous_koopmanOrbit (mu := mu) (d := d) X).locallyIntegrable

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Local integrability of a particular strongly continuous Koopman orbit,
without topologizing the sample carrier. -/
theorem locallyIntegrable_koopmanOrbit_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Lp E 2 mu)
    (hX : Continuous (koopmanOrbit (mu := mu) (d := d) X)) :
    LocallyIntegrable (koopmanOrbit (mu := mu) (d := d) X) volume :=
  hX.locallyIntegrable

/-- Translating a stationary mollification is precisely convolution of the
kernel with the Koopman orbit. -/
theorem koopman_mollifyL2_eq_convolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) (z : Vec d) :
    koopman (mu := mu) z (mollifyL2 (mu := mu) kappa X) =
      convolution kappa (koopmanOrbit (mu := mu) X)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
  rw [mollifyL2, convolution_def]
  have hint := integrable_mollifyL2_integrand
    (mu := mu) hkappa hcompact X
  change (koopman (mu := mu) z).toContinuousLinearMap
      (∫ y : Vec d, kappa y • koopman (mu := mu) (-y) X) = _
  rw [← (koopman (mu := mu) z).toContinuousLinearMap.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul]
  change kappa y • koopman (mu := mu) z (koopman (mu := mu) (-y) X) =
    kappa y • koopman (mu := mu) (z - y) X
  rw [koopman_koopman]
  congr 2
  abel_nf

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Convolution representation from continuity of the particular orbit. -/
theorem koopman_mollifyL2_eq_convolution_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu)
    (hX : Continuous (koopmanOrbit (mu := mu) (d := d) X)) (z : Vec d) :
    koopman (mu := mu) z (mollifyL2 (mu := mu) kappa X) =
      convolution kappa (koopmanOrbit (mu := mu) X)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
  rw [mollifyL2, convolution_def]
  have hint := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa hcompact X hX
  change (koopman (mu := mu) z).toContinuousLinearMap
      (∫ y : Vec d, kappa y • koopman (mu := mu) (-y) X) = _
  rw [← (koopman (mu := mu) z).toContinuousLinearMap.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul]
  change kappa y • koopman (mu := mu) z (koopman (mu := mu) (-y) X) =
    kappa y • koopman (mu := mu) (z - y) X
  rw [koopman_koopman]
  congr 2
  abel_nf

/-- The `i`th partial derivative of a smooth scalar kernel. -/
def kernelDeriv (kappa : Vec d → ℝ) (i : Fin d) : Vec d → ℝ :=
  fun y => fderiv ℝ kappa y (basisVec i)

theorem continuous_kernelDeriv {kappa : Vec d → ℝ}
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i : Fin d) :
    Continuous (kernelDeriv kappa i) :=
  (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
    (hkappa.continuous_fderiv (by simp))

theorem hasCompactSupport_kernelDeriv {kappa : Vec d → ℝ}
    (hcompact : HasCompactSupport kappa) (i : Fin d) :
    HasCompactSupport (kernelDeriv kappa i) :=
  (hcompact.fderiv ℝ).comp_left
    (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) rfl

theorem contDiff_kernelDeriv {kappa : Vec d → ℝ}
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelDeriv kappa i) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ kappa) := by
    simpa using! hkappa.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact hd.clm_apply contDiff_const

/-- Directional differentiation of a convolution falls on its compactly
supported smooth kernel. -/
theorem fderiv_convolution_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {u : Vec d → E} (hu : LocallyIntegrable u volume)
    (x : Vec d) (i : Fin d) :
    fderiv ℝ
        (convolution kappa u (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        x (basisVec i) =
      convolution (kernelDeriv kappa i) u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hflip : convolution kappa u L volume = convolution u kappa L.flip volume :=
    (convolution_flip (L := L) (f := kappa) (g := u) (μ := volume)).symm
  have hderiv : HasFDerivAt (convolution u kappa L.flip volume)
      ((convolution u (fderiv ℝ kappa) (L.flip.precompR (Vec d)) volume) x) x :=
    hcompact.hasFDerivAt_convolution_right L.flip hu
      (hkappa.of_le (by simp)) x
  have hfd : fderiv ℝ (convolution kappa u L volume) x =
      (convolution u (fderiv ℝ kappa)
        (L.flip.precompR (Vec d)) volume) x := by
    rw [hflip]
    exact hderiv.fderiv
  rw [hfd]
  rw [convolution_precompR_apply (L := L.flip) hu (hcompact.fderiv ℝ)
    (hkappa.continuous_fderiv (by simp)) x (basisVec i)]
  exact congrFun
    (convolution_flip (L := L) (f := kernelDeriv kappa i)
      (g := u) (μ := volume)) x

/-- Every smooth stationary mollification has the expected strong coordinate
generator, with the derivative placed on the kernel. -/
theorem hasDerivAt_koopman_mollifyL2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Lp E 2 mu) (i : Fin d) :
    HasDerivAt
      (fun t : ℝ => koopman (mu := mu)
        (t • (Pi.single i 1 : Vec d))
        (mollifyL2 (mu := mu) kappa X))
      (mollifyL2 (mu := mu) (kernelDeriv kappa i) X) 0 := by
  let C : Vec d → Lp E 2 mu :=
    convolution kappa (koopmanOrbit (mu := mu) (d := d) X)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hloc := locallyIntegrable_koopmanOrbit (mu := mu) (d := d) X
  have hCdiff : DifferentiableAt ℝ C 0 := by
    exact (hcompact.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (hkappa.of_le (by simp)) hloc 0)
      |>.differentiableAt
  have hline : HasDerivAt
      (fun t : ℝ => t • (Pi.single i 1 : Vec d))
      (basisVec i) 0 := by
    simpa [basisVec] using!
      (hasDerivAt_id (x := (0 : ℝ))).smul_const
        (Pi.single i 1 : Vec d)
  have hdir : HasDerivAt (fun t : ℝ => C
      (t • (Pi.single i 1 : Vec d)))
      (fderiv ℝ C 0 (basisVec i)) 0 :=
    by
      have hout : HasFDerivAt C (fderiv ℝ C 0)
          ((0 : ℝ) • (Pi.single i 1 : Vec d)) := by
        simpa using! hCdiff.hasFDerivAt
      simpa only [zero_smul] using! hout.comp_hasDerivAt 0 hline
  have hderivValue : fderiv ℝ C 0 (basisVec i) =
      mollifyL2 (mu := mu) (kernelDeriv kappa i) X := by
    rw [fderiv_convolution_apply hcompact hkappa hloc]
    rw [mollifyL2, convolution_def]
    congr 1
    funext y
    change kernelDeriv kappa i y •
      koopman (mu := mu) (0 - y) X = _
    rw [zero_sub]
  rw [hderivValue] at hdir
  convert hdir using 1
  funext t
  exact koopman_mollifyL2_eq_convolution hkappa.continuous hcompact X
    (t • (Pi.single i 1 : Vec d))

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Derivative of a mollified field from strong continuity of its particular
Koopman orbit. -/
theorem hasDerivAt_koopman_mollifyL2_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Lp E 2 mu)
    (hX : Continuous (koopmanOrbit (mu := mu) (d := d) X)) (i : Fin d) :
    HasDerivAt
      (fun t : ℝ => koopman (mu := mu)
        (t • (Pi.single i 1 : Vec d))
        (mollifyL2 (mu := mu) kappa X))
      (mollifyL2 (mu := mu) (kernelDeriv kappa i) X) 0 := by
  let C : Vec d → Lp E 2 mu :=
    convolution kappa (koopmanOrbit (mu := mu) (d := d) X)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hloc := locallyIntegrable_koopmanOrbit_of_continuous
    (mu := mu) X hX
  have hCdiff : DifferentiableAt ℝ C 0 := by
    exact (hcompact.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (hkappa.of_le (by simp)) hloc 0)
      |>.differentiableAt
  have hline : HasDerivAt
      (fun t : ℝ => t • (Pi.single i 1 : Vec d))
      (basisVec i) 0 := by
    simpa [basisVec] using!
      (hasDerivAt_id (x := (0 : ℝ))).smul_const
        (Pi.single i 1 : Vec d)
  have hdir : HasDerivAt (fun t : ℝ => C
      (t • (Pi.single i 1 : Vec d)))
      (fderiv ℝ C 0 (basisVec i)) 0 := by
    have hout : HasFDerivAt C (fderiv ℝ C 0)
        ((0 : ℝ) • (Pi.single i 1 : Vec d)) := by
      simpa using! hCdiff.hasFDerivAt
    simpa only [zero_smul] using! hout.comp_hasDerivAt 0 hline
  have hderivValue : fderiv ℝ C 0 (basisVec i) =
      mollifyL2 (mu := mu) (kernelDeriv kappa i) X := by
    rw [fderiv_convolution_apply hcompact hkappa hloc]
    rw [mollifyL2, convolution_def]
    congr 1
    funext y
    change kernelDeriv kappa i y •
      koopman (mu := mu) (0 - y) X = _
    rw [zero_sub]
  rw [hderivValue] at hdir
  convert hdir using 1
  funext t
  exact koopman_mollifyL2_eq_convolution_of_continuous
    hkappa.continuous hcompact X hX
    (t • (Pi.single i 1 : Vec d))

/-- Integration by parts for a strong horizontal gradient after stationary
mollification: differentiating the kernel is the same as mollifying the
corresponding gradient coordinate. -/
theorem mollifyL2_kernelDeriv_eq_mollifyL2_coord
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i : Fin d) :
    mollifyL2 (mu := mu) (kernelDeriv kappa i) phi =
      mollifyL2 (mu := mu) kappa (vectorL2Coord (mu := mu) i F) := by
  have hleft := hasDerivAt_koopman_mollifyL2
    (mu := mu) hcompact hkappa phi i
  have hright := hphi.mollifyL2 hkappa.continuous hcompact i
  rw [vectorL2Coord_mollifyL2 (mu := mu) hkappa.continuous hcompact] at hright
  exact hleft.unique hright

/-- Equality of the two mixed partial derivatives of a smooth scalar kernel. -/
theorem kernelDeriv_kernelDeriv_comm
    {kappa : Vec d → ℝ} (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (i j : Fin d) :
    kernelDeriv (kernelDeriv kappa i) j =
      kernelDeriv (kernelDeriv kappa j) i := by
  funext y
  have hdiff : DifferentiableAt ℝ (fderiv ℝ kappa) y :=
    ((show ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ kappa) by
      simpa using! hkappa.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
      |>.differentiable (by simp)).differentiableAt
  have hi : DifferentiableAt ℝ (fun _ : Vec d => basisVec i) y :=
    differentiableAt_const _
  have hj : DifferentiableAt ℝ (fun _ : Vec d => basisVec j) y :=
    differentiableAt_const _
  have hkappaAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kappa y :=
    hkappa.contDiffAt
  have hsymm := (hkappaAt.isSymmSndFDerivAt
    (show minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
      simp only [minSmoothness]
      rw [if_pos (by infer_instance)]
      change (((2 : ℕ∞) : WithTop ℕ∞) ≤
        (((⊤ : ℕ∞) : WithTop ℕ∞)))
      exact WithTop.coe_le_coe.mpr le_top)).eq
    (basisVec j) (basisVec i)
  have hij : fderiv ℝ (kernelDeriv kappa i) y (basisVec j) =
      fderiv ℝ (fderiv ℝ kappa) y (basisVec j) (basisVec i) := by
    change fderiv ℝ (fun z => fderiv ℝ kappa z (basisVec i)) y
      (basisVec j) = _
    rw [fderiv_clm_apply hdiff hi]
    simp
  have hji : fderiv ℝ (kernelDeriv kappa j) y (basisVec i) =
      fderiv ℝ (fderiv ℝ kappa) y (basisVec i) (basisVec j) := by
    change fderiv ℝ (fun z => fderiv ℝ kappa z (basisVec j)) y
      (basisVec i) = _
    rw [fderiv_clm_apply hdiff hj]
    simp
  rw [kernelDeriv, kernelDeriv, hij, hji]
  exact hsymm

/-- The mollified curl of every genuine strong horizontal gradient vanishes. -/
theorem mollifyL2_kernelDeriv_coord_comm_of_hasHorizontalGradient
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d) :
    mollifyL2 (mu := mu) (kernelDeriv kappa i)
        (vectorL2Coord (mu := mu) j F) =
      mollifyL2 (mu := mu) (kernelDeriv kappa j)
        (vectorL2Coord (mu := mu) i F) := by
  rw [← mollifyL2_kernelDeriv_eq_mollifyL2_coord hphi
      (hasCompactSupport_kernelDeriv hcompact i)
      (contDiff_kernelDeriv hkappa i) j,
    ← mollifyL2_kernelDeriv_eq_mollifyL2_coord hphi
      (hasCompactSupport_kernelDeriv hcompact j)
      (contDiff_kernelDeriv hkappa j) i,
    kernelDeriv_kernelDeriv_comm hkappa i j]

/-- The bounded mollified-curl operator on stationary vector `L²`. -/
def mollifiedCurlCLM
    (kappa : Vec d → ℝ) (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d) :
    VectorL2 d mu →L[ℝ] ScalarL2 mu :=
  ((mollifyL2CLM (mu := mu) (kernelDeriv kappa i)
      (continuous_kernelDeriv hkappa i)
      (hasCompactSupport_kernelDeriv hcompact i)).comp
    (vectorL2Coord (mu := mu) j)) -
  ((mollifyL2CLM (mu := mu) (kernelDeriv kappa j)
      (continuous_kernelDeriv hkappa j)
      (hasCompactSupport_kernelDeriv hcompact j)).comp
    (vectorL2Coord (mu := mu) i))

@[simp] theorem mollifiedCurlCLM_apply
    (kappa : Vec d → ℝ) (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d)
    (F : VectorL2 d mu) :
    mollifiedCurlCLM (mu := mu) kappa hcompact hkappa i j F =
      mollifyL2 (mu := mu) (kernelDeriv kappa i)
          (vectorL2Coord (mu := mu) j F) -
        mollifyL2 (mu := mu) (kernelDeriv kappa j)
          (vectorL2Coord (mu := mu) i F) := rfl

/-- The mollified curl vanishes on the full closed stationary-potential
subspace. -/
theorem mollifyL2_kernelDeriv_coord_comm_of_mem_stationaryPotentialSubspace
    {F : VectorL2 d mu}
    (hF : F ∈ stationaryPotentialSubspace (mu := mu) (d := d))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d) :
    mollifyL2 (mu := mu) (kernelDeriv kappa i)
        (vectorL2Coord (mu := mu) j F) =
      mollifyL2 (mu := mu) (kernelDeriv kappa j)
        (vectorL2Coord (mu := mu) i F) := by
  let T := mollifiedCurlCLM (mu := mu) kappa hcompact hkappa i j
  let S := horizontalGradientRange (mu := mu) (d := d)
  have hsub : S ≤ LinearMap.ker T.toLinearMap := by
    intro G hG
    obtain ⟨phi, hphi⟩ := hG
    rw [LinearMap.mem_ker]
    change mollifiedCurlCLM (mu := mu) kappa hcompact hkappa i j G = 0
    rw [mollifiedCurlCLM_apply]
    rw [mollifyL2_kernelDeriv_coord_comm_of_hasHorizontalGradient
      hphi hcompact hkappa i j, sub_self]
  have hkerClosed : IsClosed ((LinearMap.ker T.toLinearMap : Submodule ℝ (VectorL2 d mu)) :
      Set (VectorL2 d mu)) := ContinuousLinearMap.isClosed_ker T
  have hmem : F ∈ LinearMap.ker T.toLinearMap :=
    (Submodule.topologicalClosure_minimal S hsub hkerClosed) hF
  rw [LinearMap.mem_ker] at hmem
  change mollifiedCurlCLM (mu := mu) kappa hcompact hkappa i j F = 0 at hmem
  rw [mollifiedCurlCLM_apply] at hmem
  exact sub_eq_zero.mp hmem

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary
