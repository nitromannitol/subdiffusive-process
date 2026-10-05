module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMollifiedDivergence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySolenoidalCutoff

@[expose] public section

/-!
# Kernel construction of an approximate stationary stream

For a family of smooth compactly supported kernels `g_m`, this module builds

`S_im = A_(g_m) X_i - A_(g_i) X_m`.

It is antisymmetric by construction.  Its realized row divergence is exactly
the realization of the smoothing by `sum_m partial_m g_m`, minus the mollified
horizontal divergence. The construction is topology-free.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


variable {d : ℕ}

/-- Pack scalar coordinates into the Hilbert Euclidean carrier. -/
def streamVectorPack (psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : HilbertVec d :=
  HilbertVec.ofVec fun i => psi i omega

/-- The representative-level antisymmetric kernel stream. -/
def stationaryKernelStream (g : Fin d → Vec d → ℝ)
    (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Fin d → HilbertVec d :=
  fun m => streamVectorPack (fun i omega' =>
    representativeMollify (g m) (representativeCoord X i) omega' -
      representativeMollify (g i) (representativeCoord X m) omega') omega

theorem stationaryStreamRealization_kernelStream_eq
    (g : Fin d → Vec d → ℝ) (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (i m : Fin d) :
    stationaryStreamRealization (stationaryKernelStream g X) omega i m =
      fun x =>
        realize (representativeMollify (g m) (representativeCoord X i))
            omega x -
          realize (representativeMollify (g i) (representativeCoord X m))
            omega x := rfl

theorem stationaryKernelStream_antisymmetric
    (g : Fin d → Vec d → ℝ) (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (i m : Fin d) :
    stationaryStreamRealization (stationaryKernelStream g X) omega m i =
      -stationaryStreamRealization (stationaryKernelStream g X) omega i m := by
  funext x
  show _ = -(_ - _)
  rw [neg_sub]
  rfl

theorem contDiff_stationaryKernelStream
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hloc : ∀ i : Fin d,
      LocallyIntegrable (realize (representativeCoord X i) omega) volume)
    (i m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (stationaryStreamRealization (stationaryKernelStream g X) omega i m) := by
  rw [stationaryStreamRealization_kernelStream_eq]
  rw [realize_representativeMollify, realize_representativeMollify]
  exact (hgc m).contDiff_convolution_left _ (hgs m) (hloc i) |>.sub
    ((hgc i).contDiff_convolution_left _ (hgs i) (hloc m))

/-- The representative mollified horizontal divergence. -/
def representativeMollifiedDivergence (kappa : Vec d → ℝ)
    (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑ m : Fin d,
    representativeMollify (Stationary.kernelDeriv kappa m)
      (representativeCoord X m) omega

/-- The exact Omega-level row divergence of the kernel stream. -/
def stationaryKernelStreamDiv (g : Fin d → Vec d → ℝ)
    (nu : Vec d → ℝ) (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : HilbertVec d :=
  streamVectorPack (fun i omega' =>
    representativeMollify nu (representativeCoord X i) omega' -
      representativeMollifiedDivergence (g i) X omega') omega

private theorem fderiv_stationaryKernelStream_entry
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hloc : ∀ i : Fin d,
      LocallyIntegrable (realize (representativeCoord X i) omega) volume)
    (i m : Fin d) (x : Vec d) :
    streamCoordDeriv
        (stationaryStreamRealization (stationaryKernelStream g X) omega i m)
        m x =
      realize (representativeMollify (Stationary.kernelDeriv (g m) m)
          (representativeCoord X i)) omega x -
        realize (representativeMollify (Stationary.kernelDeriv (g i) m)
          (representativeCoord X m)) omega x := by
  have hA : DifferentiableAt ℝ
      (realize (representativeMollify (g m) (representativeCoord X i)) omega) x :=
    by
      rw [realize_representativeMollify]
      exact (((hgc m).contDiff_convolution_left _ (hgs m) (hloc i)).differentiable
        (by simp)).differentiableAt
  have hB : DifferentiableAt ℝ
      (realize (representativeMollify (g i) (representativeCoord X m)) omega) x :=
    by
      rw [realize_representativeMollify]
      exact (((hgc i).contDiff_convolution_left _ (hgs i) (hloc m)).differentiable
        (by simp)).differentiableAt
  show fderiv ℝ
      (stationaryStreamRealization (stationaryKernelStream g X) omega i m)
      x (basisVec m) = _
  rw [stationaryStreamRealization_kernelStream_eq,
    fderiv_fun_sub hA hB, sub_apply]
  rw [fderiv_realize_representativeMollify_apply
      (hgc m) (hgs m) (hloc i) x m,
    fderiv_realize_representativeMollify_apply
      (hgc i) (hgs i) (hloc m) x m]

/-- Exact samplewise divergence identity for the kernel stream. -/
theorem streamDivergence_stationaryKernelStream
    {g : Fin d → Vec d → ℝ} {nu : Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    (hnu : ∀ y, nu y =
      ∑ m : Fin d, Stationary.kernelDeriv (g m) m y)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hloc : ∀ i : Fin d,
      LocallyIntegrable (realize (representativeCoord X i) omega) volume)
    (x : Vec d) :
    streamDivergence
        (stationaryStreamRealization (stationaryKernelStream g X) omega) x =
      (realize (stationaryKernelStreamDiv g nu X) omega x).toVec := by
  classical
  funext i
  rw [streamDivergence_apply]
  simp_rw [fderiv_stationaryKernelStream_entry hgs hgc hloc i]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ m : Fin d,
        realize (representativeMollify
          (Stationary.kernelDeriv (g m) m)
          (representativeCoord X i)) omega x) =
        realize (representativeMollify nu (representativeCoord X i))
          omega x := by
    simp only [realize_apply, representativeMollify]
    have hint : ∀ m : Fin d, Integrable
        (fun y : Vec d => Stationary.kernelDeriv (g m) m y •
          representativeCoord X i ((-y) +ᵥ (x +ᵥ omega))) volume := by
      intro m
      have hlocal : LocallyIntegrable
          (realize (representativeCoord X i) omega) volume := hloc i
      have hconv :=
        (Stationary.hasCompactSupport_kernelDeriv (hgc m) m)
          |>.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
            (Stationary.continuous_kernelDeriv (hgs m) m) hlocal x
      simpa only [realize_apply, vadd_vadd, neg_add_rev, neg_neg,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using! hconv
    have hsum := integral_finsetSum Finset.univ (fun m _ => hint m)
    rw [← hsum]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    change (∑ m : Fin d, Stationary.kernelDeriv (g m) m y •
      representativeCoord X i ((-y) +ᵥ (x +ᵥ omega))) =
      nu y • representativeCoord X i ((-y) +ᵥ (x +ᵥ omega))
    rw [hnu y, Finset.sum_smul]
  rw [hfirst]
  rfl

theorem stronglyMeasurable_streamVectorPack
    {psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ}
    (hpsi : ∀ i, StronglyMeasurable (psi i)) :
    StronglyMeasurable (streamVectorPack psi) := by
  have hvec : Measurable fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (fun i => psi i omega : Vec d) :=
    Measurable.of_eval fun i => (hpsi i).measurable
  exact ((HilbertVec.continuousLinearEquivVec d).symm.continuous)
    |>.comp_stronglyMeasurable hvec.stronglyMeasurable

theorem memLp_two_streamVectorPack
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ}
    (hpsiM : ∀ i, StronglyMeasurable (psi i))
    (hpsi : ∀ i, MemLp (psi i) 2 M.P.toMeasure) :
    MemLp (streamVectorPack psi) 2 M.P.toMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_streamVectorPack hpsiM).aestronglyMeasurable).2 ?_
  have hsum : Integrable (fun omega =>
      ∑ i : Fin d, psi i omega ^ 2) M.P.toMeasure :=
    integrable_finsetSum _ fun i _ =>
      ((memLp_two_iff_integrable_sq_norm
        (hpsiM i).aestronglyMeasurable).1 (hpsi i)).congr
          (Filter.Eventually.of_forall fun omega => by
            change ‖psi i omega‖ ^ 2 = psi i omega ^ 2
            rw [Real.norm_eq_abs, sq_abs])
  refine hsum.congr (Filter.Eventually.of_forall fun omega => ?_)
  change (∑ i : Fin d, psi i omega ^ 2) =
    ‖streamVectorPack psi omega‖ ^ 2
  rw [HilbertVec.norm_sq_eq_sum_sq]
  rfl

theorem stronglyMeasurable_stationaryKernelStream
    {g : Fin d → Vec d → ℝ} (hg : ∀ m, Continuous (g m))
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hX : StronglyMeasurable X) :
    StronglyMeasurable (stationaryKernelStream g X) := by
  have hcoord : ∀ m i : Fin d, StronglyMeasurable fun omega =>
      representativeMollify (g m) (representativeCoord X i) omega -
        representativeMollify (g i) (representativeCoord X m) omega := by
    intro m i
    exact (stronglyMeasurable_representativeMollify (hg m)
      (stronglyMeasurable_representativeCoord hX i)).sub
        (stronglyMeasurable_representativeMollify (hg i)
          (stronglyMeasurable_representativeCoord hX m))
  exact (Measurable.of_eval fun m =>
    (stronglyMeasurable_streamVectorPack (fun i => hcoord m i)).measurable)
      |>.stronglyMeasurable

theorem memLp_two_stationaryKernelStream
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {g : Fin d → Vec d → ℝ} (hg : ∀ m, Continuous (g m))
    (hgi : ∀ m, Integrable (g m) volume)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    MemLp (stationaryKernelStream g X) 2 M.P.toMeasure := by
  have hcol : ∀ m : Fin d,
      MemLp (fun omega => stationaryKernelStream g X omega m)
        2 M.P.toMeasure := by
    intro m
    apply memLp_two_streamVectorPack M
    · intro i
      exact (stronglyMeasurable_representativeMollify (hg m)
        (stronglyMeasurable_representativeCoord hXm i)).sub
          (stronglyMeasurable_representativeMollify (hg i)
            (stronglyMeasurable_representativeCoord hXm m))
    · intro i
      exact (memLp_two_representativeMollify M (hg m) (hgi m)
        (stronglyMeasurable_representativeCoord hXm i)
        (memLp_representativeCoord M hXm hX i)).sub
          (memLp_two_representativeMollify M (hg i) (hgi i)
            (stronglyMeasurable_representativeCoord hXm m)
            (memLp_representativeCoord M hXm hX m))
  have hdom : MemLp (fun omega =>
      ∑ m : Fin d, ‖stationaryKernelStream g X omega m‖)
      2 M.P.toMeasure := memLp_finsetSum _ fun m _ => (hcol m).norm
  refine MemLp.mono' hdom
    (stronglyMeasurable_stationaryKernelStream hg hXm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun omega => ?_
  have hnonneg : 0 ≤ ∑ m : Fin d,
      ‖stationaryKernelStream g X omega m‖ :=
    Finset.sum_nonneg fun m _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun m => ?_
  exact Finset.single_le_sum (fun k _ => norm_nonneg _)
    (Finset.mem_univ m)

theorem stronglyMeasurable_representativeMollifiedDivergence
    {kappa : Vec d → ℝ} (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (representativeMollifiedDivergence kappa X) := by
  exact Finset.stronglyMeasurable_fun_sum _ fun m _ =>
    stronglyMeasurable_representativeMollify
      (Stationary.continuous_kernelDeriv hkappa m)
      (stronglyMeasurable_representativeCoord hXm m)

theorem memLp_two_representativeMollifiedDivergence
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    MemLp (representativeMollifiedDivergence kappa X)
      2 M.P.toMeasure := by
  exact memLp_finsetSum _ fun m _ =>
    memLp_two_representativeMollify M
      (Stationary.continuous_kernelDeriv hkappa m)
      ((Stationary.continuous_kernelDeriv hkappa m)
        |>.integrable_of_hasCompactSupport
          (Stationary.hasCompactSupport_kernelDeriv hcompact m))
      (stronglyMeasurable_representativeCoord hXm m)
      (memLp_representativeCoord M hXm hX m)

/-- Solenoidality kills the cross-divergence term in the representative
kernel stream.  The proof compares each representative convolution with the
existing Hilbert-space mollifier and then uses the stationary Hodge
identity `mollifiedDivergenceL2_eq_zero_of_mem_solenoidal`. -/
theorem ae_representativeMollifiedDivergence_eq_zero_of_solenoidal
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R))
    (hsol : letI := potentialSequenceVAddInvariant M
      R ∈ Stationary.stationarySolenoidalSubspace
        (mu := M.P.toMeasure) (d := d)) :
    ∀ᵐ omega ∂M.P.toMeasure,
      representativeMollifiedDivergence kappa
        (stationaryVectorRepresentative M R) omega = 0 := by
  let := potentialSequenceVAddInvariant M
  classical
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := stationaryVectorRepresentative M R
  let f : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun m =>
    representativeMollify (Stationary.kernelDeriv kappa m)
      (representativeCoord X m)
  let T : Fin d → Stationary.ScalarL2 M.P.toMeasure := fun m =>
    Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa m)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) m R)
  have hXm : StronglyMeasurable X :=
    stronglyMeasurable_stationaryVectorRepresentative M R
  have hXL : MemLp X 2 M.P.toMeasure :=
    memLp_two_stationaryVectorRepresentative M R
  have hfm : ∀ m : Fin d, StronglyMeasurable (f m) := by
    intro m
    exact stronglyMeasurable_representativeMollify
      (Stationary.continuous_kernelDeriv hkappa m)
      (stronglyMeasurable_representativeCoord hXm m)
  have hf : ∀ m : Fin d, MemLp (f m) 2 M.P.toMeasure := by
    intro m
    exact memLp_two_representativeMollify M
      (Stationary.continuous_kernelDeriv hkappa m)
      ((Stationary.continuous_kernelDeriv hkappa m)
        |>.integrable_of_hasCompactSupport
          (Stationary.hasCompactSupport_kernelDeriv hcompact m))
      (stronglyMeasurable_representativeCoord hXm m)
      (memLp_representativeCoord M hXm hXL m)
  have hcoordOrbit : ∀ m : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) m R)) := by
    intro m
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) m).continuous.comp hR
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z m R
  have hcoordClass : ∀ m : Fin d,
      Stationary.vectorL2Coord (mu := M.P.toMeasure) m R =
        (memLp_representativeCoord M hXm hXL m).toLp
          (representativeCoord X m) := by
    intro m
    have h := vectorL2Coord_toLp_representative M hXm hXL m
    simpa only [X, toLp_stationaryVectorRepresentative] using! h
  have hclass : ∀ m : Fin d, (hf m).toLp (f m) = T m := by
    intro m
    have hbase := toLp_representativeMollify_eq_mollifyL2 M
      (Stationary.continuous_kernelDeriv hkappa m)
      (Stationary.hasCompactSupport_kernelDeriv hcompact m)
      (stronglyMeasurable_representativeCoord hXm m)
      (memLp_representativeCoord M hXm hXL m)
      (by
        simpa only [← hcoordClass m] using! hcoordOrbit m)
    simpa only [f, T, ← hcoordClass m] using! hbase
  have htermAE : ∀ m : Fin d,
      (T m : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) =ᵐ[M.P.toMeasure] f m := by
    intro m
    rw [← hclass m]
    exact (hf m).coeFn_toLp
  have hsumAE : ∀ s : Finset (Fin d),
      ((∑ m ∈ s, T m : Stationary.ScalarL2 M.P.toMeasure) :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) =ᵐ[M.P.toMeasure]
        fun omega => ∑ m ∈ s, f m omega := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using! (Lp.coeFn_zero ℝ 2 M.P.toMeasure)
    | @insert m s hms ih =>
      filter_upwards [Lp.coeFn_add (T m) (∑ i ∈ s, T i),
        htermAE m, ih] with omega hadd hm hs
      rw [Finset.sum_insert hms, hadd]
      change (T m : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega +
        ((∑ i ∈ s, T i : Stationary.ScalarL2 M.P.toMeasure) :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega = ∑ i ∈ insert m s, f i omega
      rw [hm, hs, Finset.sum_insert hms]
  have hz : mollifiedDivergenceL2 M kappa R = 0 :=
    mollifiedDivergenceL2_eq_zero_of_mem_solenoidal
      M hcompact hkappa R hR hsol
  have hzeroAE :
      (mollifiedDivergenceL2 M kappa R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) =ᵐ[M.P.toMeasure]
        fun _ => 0 := by
    rw [hz]
    simpa using! (Lp.coeFn_zero ℝ 2 M.P.toMeasure)
  filter_upwards [hsumAE Finset.univ, hzeroAE] with omega hsum hzero
  have hsum' : (∑ m : Fin d, f m omega) = 0 := by
    exact hsum.symm.trans hzero
  simpa only [representativeMollifiedDivergence, X, f] using! hsum'

theorem stronglyMeasurable_stationaryKernelStreamDiv
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    {nu : Vec d → ℝ} (hnu : Continuous nu)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (stationaryKernelStreamDiv g nu X) := by
  apply stronglyMeasurable_streamVectorPack
  intro i
  exact (stronglyMeasurable_representativeMollify hnu
    (stronglyMeasurable_representativeCoord hXm i)).sub
      (stronglyMeasurable_representativeMollifiedDivergence
        (hgs i) hXm)

theorem memLp_two_stationaryKernelStreamDiv
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    {nu : Vec d → ℝ} (hnu : Continuous nu)
    (hnui : Integrable nu volume)
    {X : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    MemLp (stationaryKernelStreamDiv g nu X) 2 M.P.toMeasure := by
  apply memLp_two_streamVectorPack M
  · intro i
    exact (stronglyMeasurable_representativeMollify hnu
      (stronglyMeasurable_representativeCoord hXm i)).sub
        (stronglyMeasurable_representativeMollifiedDivergence
          (hgs i) hXm)
  · intro i
    exact (memLp_two_representativeMollify M hnu hnui
      (stronglyMeasurable_representativeCoord hXm i)
      (memLp_representativeCoord M hXm hX i)).sub
        (memLp_two_representativeMollifiedDivergence M
          (hgc i) (hgs i) hXm hX)

/-- For a solenoidal stationary field the exact stream divergence is almost
surely just the prescribed kernel smoothing; the cross term vanishes. -/
theorem ae_stationaryKernelStreamDiv_eq_representativeMollify
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    (nu : Vec d → ℝ)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R))
    (hsol : letI := potentialSequenceVAddInvariant M
      R ∈ Stationary.stationarySolenoidalSubspace
        (mu := M.P.toMeasure) (d := d)) :
    ∀ᵐ omega ∂M.P.toMeasure,
      stationaryKernelStreamDiv g nu
          (stationaryVectorRepresentative M R) omega =
        streamVectorPack (fun i => representativeMollify nu
          (representativeCoord (stationaryVectorRepresentative M R) i))
          omega := by
  have hzero : ∀ i : Fin d, ∀ᵐ omega ∂M.P.toMeasure,
      representativeMollifiedDivergence (g i)
        (stationaryVectorRepresentative M R) omega = 0 :=
    fun i => ae_representativeMollifiedDivergence_eq_zero_of_solenoidal
      M (hgc i) (hgs i) R hR hsol
  have hzeroAll : ∀ᵐ omega ∂M.P.toMeasure, ∀ i : Fin d,
      representativeMollifiedDivergence (g i)
        (stationaryVectorRepresentative M R) omega = 0 :=
    ae_all_iff.2 hzero
  filter_upwards [hzeroAll] with omega homega
  apply HilbertVec.ext
  intro i
  change representativeMollify nu
      (representativeCoord (stationaryVectorRepresentative M R) i) omega -
      representativeMollifiedDivergence (g i)
        (stationaryVectorRepresentative M R) omega =
    representativeMollify nu
      (representativeCoord (stationaryVectorRepresentative M R) i) omega
  rw [homega i, sub_zero]

/-- Carrier package for the approximate antisymmetric stream.  The
construction is explicit; no stream existence is assumed. -/
theorem exists_stationaryKernelStream
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {g : Fin d → Vec d → ℝ}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    {nu : Vec d → ℝ} (hnuc : Continuous nu)
    (hnui : Integrable nu volume)
    (hnu : ∀ y, nu y =
      ∑ m : Fin d, Stationary.kernelDeriv (g m) m y)
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
          D omega = streamVectorPack (fun i => representativeMollify nu
            (representativeCoord (stationaryVectorRepresentative M R) i))
            omega) := by
  let X := stationaryVectorRepresentative M R
  have hXm : StronglyMeasurable X :=
    stronglyMeasurable_stationaryVectorRepresentative M R
  have hXL : MemLp X 2 M.P.toMeasure :=
    memLp_two_stationaryVectorRepresentative M R
  have hloc : ∀ᵐ omega ∂M.P.toMeasure, ∀ i : Fin d,
      LocallyIntegrable (realize (representativeCoord X i) omega) volume := by
    exact ae_all_iff.2 fun i => ae_locallyIntegrable_realize M
      (stronglyMeasurable_representativeCoord hXm i)
      (memLp_representativeCoord M hXm hXL i)
  refine ⟨stationaryKernelStream g X, stationaryKernelStreamDiv g nu X,
    stronglyMeasurable_stationaryKernelStream
      (fun m => (hgs m).continuous) hXm,
    memLp_two_stationaryKernelStream M
      (fun m => (hgs m).continuous)
      (fun m => (hgs m).continuous.integrable_of_hasCompactSupport (hgc m))
      hXm hXL, ?_, ?_, ?_,
    stronglyMeasurable_stationaryKernelStreamDiv hgs hnuc hXm,
    memLp_two_stationaryKernelStreamDiv M hgs hgc hnuc hnui hXm hXL,
    ae_stationaryKernelStreamDiv_eq_representativeMollify
      M hgs hgc nu R hR hsol⟩
  · filter_upwards [hloc] with omega homega i m
    exact contDiff_stationaryKernelStream hgs hgc homega i m
  · intro omega i m
    exact stationaryKernelStream_antisymmetric g X omega i m
  · filter_upwards [hloc] with omega homega x
    exact streamDivergence_stationaryKernelStream hgs hgc hnu homega x

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
