import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryPotentialCutoff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Antisymmetric streams and zero-normal solenoidal fields

This is the deterministic stream layer used in the Neumann half of the
Section 5 stationary exhaustion.  It mirrors
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`: the row
divergence of a smooth compactly supported antisymmetric tensor is orthogonal
to every `H1Function` gradient, hence belongs to
`IsSolenoidalZeroNormalTraceOn`.

No probabilistic or stationary input is used here.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The `m`th coordinate derivative of a scalar field. -/
def streamCoordDeriv (f : Vec d → ℝ) (m : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ f x (basisVec m)

theorem streamCoordDeriv_neg (f : Vec d → ℝ) (m : Fin d) :
    streamCoordDeriv (-f) m = -streamCoordDeriv f m := by
  funext x
  simp [streamCoordDeriv, fderiv_neg]

theorem contDiff_streamCoordDeriv {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (streamCoordDeriv f m) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
    have h := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    simpa using h
  exact hd.clm_apply contDiff_const

theorem hasCompactSupport_streamCoordDeriv {f : Vec d → ℝ}
    (hf : HasCompactSupport f) (m : Fin d) :
    HasCompactSupport (streamCoordDeriv f m) :=
  hf.fderiv_apply ℝ (basisVec m)

theorem tsupport_streamCoordDeriv_subset (f : Vec d → ℝ) (m : Fin d) :
    tsupport (streamCoordDeriv f m) ⊆ tsupport f := by
  refine le_trans (closure_mono ?_) (tsupport_fderiv_subset ℝ (f := f))
  intro x hx
  simp only [Function.mem_support, streamCoordDeriv, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro hzero
  exact hx (by simp [hzero])

theorem streamCoordDeriv_streamCoordDeriv_eq {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m i : Fin d) (x : Vec d) :
    streamCoordDeriv (streamCoordDeriv f m) i x =
      fderiv ℝ (fderiv ℝ f) x (basisVec i) (basisVec m) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
    have h := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    simpa using h
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hd.differentiable (by simp)).differentiableAt
  have hkey :
      fderiv ℝ (fun y => (fderiv ℝ f y) (basisVec m)) x =
        (fderiv ℝ f x).comp
            (fderiv ℝ (fun _ : Vec d => basisVec m) x) +
          (fderiv ℝ (fderiv ℝ f) x).flip (basisVec m) :=
    fderiv_clm_apply hdiff (differentiableAt_const _)
  have hrewrite : streamCoordDeriv (streamCoordDeriv f m) i x =
      fderiv ℝ (fun y => (fderiv ℝ f y) (basisVec m)) x (basisVec i) := rfl
  rw [hrewrite, hkey]
  simp

theorem streamCoordDeriv_comm {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m i : Fin d) (x : Vec d) :
    streamCoordDeriv (streamCoordDeriv f m) i x =
      streamCoordDeriv (streamCoordDeriv f i) m x := by
  have hle : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField,
      show ((2 : WithTop ℕ∞)) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]
    exact WithTop.coe_le_coe.2 le_top
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt hle
  rw [streamCoordDeriv_streamCoordDeriv_eq hf,
    streamCoordDeriv_streamCoordDeriv_eq hf]
  exact hsymm.eq _ _

/-- Row divergence of a matrix-valued stream. -/
def streamDivergence (T : Fin d → Fin d → (Vec d → ℝ))
    (x : Vec d) : Vec d :=
  fun i => ∑ m : Fin d, streamCoordDeriv (T i m) m x

theorem streamDivergence_apply
    (T : Fin d → Fin d → (Vec d → ℝ)) (x : Vec d) (i : Fin d) :
    streamDivergence T x i =
      ∑ m : Fin d, streamCoordDeriv (T i m) m x := rfl

private theorem memScalarL2_of_continuous_of_hasCompactSupport
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemScalarL2 U f :=
  (hf.memLp_of_hasCompactSupport (μ := volume) (p := 2) hfc).restrict U

private theorem integrableOn_mul_of_memScalarL2
    {U : Set (Vec d)} {u f : Vec d → ℝ} (hu : MemScalarL2 U u)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => u x * f x) U := by
  have h := hu.integrable_mul
    (memScalarL2_of_continuous_of_hasCompactSupport (U := U) hf hfc)
  simpa [IntegrableOn, Pi.mul_apply] using h

private theorem setIntegral_grad_mul_streamCoordDeriv_eq
    {U : Set (Vec d)} {T : Fin d → Fin d → (Vec d → ℝ)}
    (phi : H1Function U)
    (hsmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (T i m))
    (hsupp : ∀ i m, HasCompactSupport (T i m))
    (hsub : ∀ i m, tsupport (T i m) ⊆ U) (i m : Fin d) :
    ∫ x in U, phi.grad x i * streamCoordDeriv (T i m) m x =
      -∫ x in U, phi.toFun x *
        streamCoordDeriv (streamCoordDeriv (T i m) m) i x := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (streamCoordDeriv (T i m) m) :=
    contDiff_streamCoordDeriv (hsmooth i m) m
  have hc : HasCompactSupport (streamCoordDeriv (T i m) m) :=
    hasCompactSupport_streamCoordDeriv (hsupp i m) m
  have hsu : tsupport (streamCoordDeriv (T i m) m) ⊆ U :=
    le_trans (tsupport_streamCoordDeriv_subset (T i m) m) (hsub i m)
  have hweak := phi.hasWeakGradient i
    (streamCoordDeriv (T i m) m) hs hc hsu
  have hweak' :
      ∫ x in U, phi.toFun x *
          streamCoordDeriv (streamCoordDeriv (T i m) m) i x =
        -∫ x in U, phi.grad x i * streamCoordDeriv (T i m) m x := by
    simpa [streamCoordDeriv] using hweak
  linarith [hweak']

/-- The row divergence of a smooth, compactly supported antisymmetric tensor
has zero normal trace in the weak `L2` sense. -/
theorem isSolenoidalZeroNormalTraceOn_streamDivergence
    {U : Set (Vec d)} {T : Fin d → Fin d → (Vec d → ℝ)}
    (hsmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (T i m))
    (hsupp : ∀ i m, HasCompactSupport (T i m))
    (hsub : ∀ i m, tsupport (T i m) ⊆ U)
    (hanti : ∀ i m, T m i = -T i m) :
    IsSolenoidalZeroNormalTraceOn U (streamDivergence T) := by
  intro phi
  classical
  set b : Fin d → Fin d → ℝ := fun i m =>
    ∫ x in U, phi.toFun x *
      streamCoordDeriv (streamCoordDeriv (T i m) m) i x with hbdef
  have hbanti : ∀ i m, b m i = -b i m := by
    intro i m
    have hpt : ∀ x : Vec d,
        streamCoordDeriv (streamCoordDeriv (T m i) i) m x =
          -streamCoordDeriv (streamCoordDeriv (T i m) m) i x := by
      intro x
      have h1 : streamCoordDeriv (T m i) i =
          -streamCoordDeriv (T i m) i := by
        rw [hanti i m, streamCoordDeriv_neg]
      rw [h1, streamCoordDeriv_neg]
      simp only [Pi.neg_apply, neg_inj]
      exact streamCoordDeriv_comm (hsmooth i m) i m x
    have hfun :
        (fun x => phi.toFun x *
          streamCoordDeriv (streamCoordDeriv (T m i) i) m x) =
        fun x => -(phi.toFun x *
          streamCoordDeriv (streamCoordDeriv (T i m) m) i x) := by
      funext x
      rw [hpt x]
      ring
    simp only [hbdef]
    rw [hfun, integral_neg]
  have hsum : ∑ i : Fin d, ∑ m : Fin d, b i m = 0 := by
    have hswap : ∑ i : Fin d, ∑ m : Fin d, b i m =
        ∑ i : Fin d, ∑ m : Fin d, b m i := Finset.sum_comm
    have hneg : ∑ i : Fin d, ∑ m : Fin d, b m i =
        -∑ i : Fin d, ∑ m : Fin d, b i m := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => hbanti i m
    have h := hswap.trans hneg
    linarith
  have hint : ∀ i m : Fin d,
      IntegrableOn (fun x => phi.grad x i *
        streamCoordDeriv (T i m) m x) U := by
    intro i m
    exact integrableOn_mul_of_memScalarL2 (phi.grad_memL2 i)
      ((contDiff_streamCoordDeriv (hsmooth i m) m).continuous)
      (hasCompactSupport_streamCoordDeriv (hsupp i m) m)
  have hexpand : ∀ x : Vec d,
      vecDot (streamDivergence T x) (phi.grad x) =
        ∑ i : Fin d, ∑ m : Fin d,
          phi.grad x i * streamCoordDeriv (T i m) m x := by
    intro x
    simp only [vecDot, streamDivergence_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun m _ => by ring
  calc
    ∫ x in U, vecDot (streamDivergence T x) (phi.grad x) =
        ∫ x in U, ∑ i : Fin d, ∑ m : Fin d,
          phi.grad x i * streamCoordDeriv (T i m) m x := by
      exact integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : Fin d, ∑ m : Fin d,
        ∫ x in U, phi.grad x i * streamCoordDeriv (T i m) m x := by
      rw [integral_finset_sum _
        (fun i _ => integrable_finset_sum _ fun m _ => hint i m)]
      exact Finset.sum_congr rfl fun i _ =>
        integral_finset_sum _ fun m _ => hint i m
    _ = ∑ i : Fin d, ∑ m : Fin d, -b i m := by
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun m _ => ?_
      exact setIntegral_grad_mul_streamCoordDeriv_eq
        phi hsmooth hsupp hsub i m
    _ = -∑ i : Fin d, ∑ m : Fin d, b i m := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
    _ = 0 := by rw [hsum, neg_zero]

/-- Tensor cutoff `eta * (S - c)`. -/
def cutoffStream (eta : Vec d → ℝ)
    (S : Fin d → Fin d → (Vec d → ℝ))
    (c : Fin d → Fin d → ℝ) (i m : Fin d) (x : Vec d) : ℝ :=
  eta x * (S i m x - c i m)

theorem streamCoordDeriv_mul {f g : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (m : Fin d) :
    streamCoordDeriv (fun y => f y * g y) m x =
      streamCoordDeriv f m x * g x + f x * streamCoordDeriv g m x := by
  simp only [streamCoordDeriv, fderiv_fun_mul hf hg,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  ring

theorem streamCoordDeriv_sub_const (f : Vec d → ℝ) (a : ℝ)
    (m : Fin d) (x : Vec d) :
    streamCoordDeriv (fun y => f y - a) m x =
      streamCoordDeriv f m x := by
  simp only [streamCoordDeriv]
  rw [fderiv_sub_const]

theorem streamDivergence_cutoffStream_apply
    {eta : Vec d → ℝ} {S : Fin d → Fin d → (Vec d → ℝ)}
    {c : Fin d → Fin d → ℝ} {x : Vec d}
    (heta : DifferentiableAt ℝ eta x)
    (hS : ∀ i m, DifferentiableAt ℝ (S i m) x) (i : Fin d) :
    streamDivergence (cutoffStream eta S c) x i =
      eta x * streamDivergence S x i +
        ∑ m : Fin d, streamCoordDeriv eta m x *
          (S i m x - c i m) := by
  classical
  have hterm : ∀ m : Fin d,
      streamCoordDeriv (cutoffStream eta S c i m) m x =
        eta x * streamCoordDeriv (S i m) m x +
          streamCoordDeriv eta m x * (S i m x - c i m) := by
    intro m
    have hsub : DifferentiableAt ℝ (fun y => S i m y - c i m) x :=
      (hS i m).sub_const _
    have h := streamCoordDeriv_mul (f := eta)
      (g := fun y => S i m y - c i m) heta hsub m
    rw [streamCoordDeriv_sub_const] at h
    simpa [cutoffStream] using h.trans (by ring)
  simp only [streamDivergence_apply]
  rw [Finset.sum_congr rfl fun m _ => hterm m,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The row divergence of a cutoff antisymmetric stream is an admissible
zero-normal solenoidal competitor. -/
theorem isSolenoidalZeroNormalTraceOn_cutoffStream
    {U : Set (Vec d)} {eta : Vec d → ℝ}
    {S : Fin d → Fin d → (Vec d → ℝ)}
    {c : Fin d → Fin d → ℝ}
    (hetas : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hS : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (S i m))
    (hSanti : ∀ i m, S m i = -S i m)
    (hcanti : ∀ i m, c m i = -c i m) :
    IsSolenoidalZeroNormalTraceOn U
      (streamDivergence (cutoffStream eta S c)) := by
  refine isSolenoidalZeroNormalTraceOn_streamDivergence ?_ ?_ ?_ ?_
  · intro i m
    exact hetas.mul ((hS i m).sub contDiff_const)
  · intro i m
    exact hetac.mul_right
  · intro i m
    exact le_trans (tsupport_mul_subset_left (f := eta)
      (g := fun x => S i m x - c i m)) hetasub
  · intro i m
    funext x
    have hS' : S m i x = -S i m x := by rw [hSanti i m]; rfl
    have hc' : c m i = -c i m := hcanti i m
    simp only [cutoffStream, Pi.neg_apply, hS', hc']
    ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
