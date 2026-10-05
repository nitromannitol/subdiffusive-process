module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMarginalIdentification
public import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
public import MarkovProcess.Trajectory.Equivariance

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess
open scoped ZeroAtInfty NNReal Pointwise ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.LegacyPhysicalTransport

def MassiveUnscale (d : ℕ) : Prop :=
  ∀ {U : Set (SpatialCoordinates d)}
    {a α r μ lam : ℝ} {c rho C R : SpatialCoordinates d → ℝ}
    {u : H1Function (a • U)} {f0 f : SpatialCoordinates d → ℝ}
    (ha : 0 < a) (_hα : α ≠ 0) (_hr : r ≠ 0)
    (_hμ : μ = r * a ^ 2 * lam)
    (_hC : ∀ x, C x = α * r * c (a • x))
    (_hR : ∀ x, R x = α * rho (a • x))
    (_hf : ∀ x, f0 (a • x) = f x)
  (_hu : IsMassiveWeakSolutionOn c rho lam (a • U) u f0),
    IsMassiveWeakSolutionOn C R μ U
      ((r * a ^ 2)⁻¹ • u.unscale ha) f

variable {d : ℕ}

theorem datum_weak (hscale : MassiveUnscale d) (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (D : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D) :
    IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega)
      (transportedDatum D (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)) := by
  let a : ℝ := (3 : ℝ) ^ m
  let r : ℝ := (ahom M (activeScale L m))⁻¹
  let alpha : ℝ := (localFactor M L m z omega)⁻¹
  have ha : 0 < a := pow_pos (by norm_num) _
  have hr : 0 < r := inv_pos.mpr (ahom_pos M _)
  have halpha : 0 < alpha := inv_pos.mpr (localFactor_pos M L m z omega)
  have hclock : (rawClock M L m : ℝ) = r * a ^ 2 := by
    dsimp [rawClock, a, r]
    change (3 : ℝ) ^ (2 * m) / ahom M (activeScale L m) = _
    rw [← pow_mul, Nat.mul_comm m 2]
    ring
  intro mu f W hW
  let e := physicalCoordinates (d := d) m z
  let f0 := pullback e.symm f
  have hscaled : IsOpenBoundedConvexDomain (a • W) := by
    have hb : IsBoundedDomain (a • W) := by
      obtain ⟨K, hK, hbound⟩ := hW.isBoundedDomain
      refine ⟨a * K, mul_pos ha hK, ?_⟩
      rintro x ⟨y, hy, rfl⟩ i
      change |a * y i| ≤ a * K
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (hbound y hy i) ha.le
    exact ⟨(Homeomorph.smulOfNeZero a ha.ne').isOpen_image.mpr hW.isOpen,
      hb, hW.convex.smul a⟩
  obtain ⟨u, hu, hweak⟩ := hD
    (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0
    (translateSet z (a • W)) (hscaled.translateSet z)
  let v := H1Function.untranslate z u
  have hv := isMassiveWeakSolutionOn_untranslate z u hweak
  have hmass := hscale
    (U := W) (a := a) (α := alpha) (r := r) (μ := (mu : ℝ))
    (lam := (mu : ℝ) / (rawClock M L m : ℝ))
    (c := fun y => coefficientAt M L omega (y + z))
    (rho := fun y => coefficientAt M L omega (y + z))
    (C := localCoefficient M L m z omega) (R := localSpeed M L m z omega)
    (u := v) (f0 := fun y => f0 (y + z)) (f := fun y => f y)
    ha halpha.ne' hr.ne'
    (by rw [← hclock]; field_simp [(show 0 < (rawClock M L m : ℝ) from rawClock_pos M L m).ne'])
    (fun x => by dsimp [localCoefficient, localSpeed, alpha, r, a]; rw [add_comm]; ring)
    (fun x => by dsimp [localSpeed, alpha, a]; rw [add_comm])
    (fun x => by change f (e.symm (a • x + z)) = f x
                 rw [show a • x + z = e x by dsimp [e, physicalCoordinates, a]; simp [add_comm]]
                 rw [e.symm_apply_apply]) hv
  refine ⟨(r * a ^ 2)⁻¹ • v.unscale ha, ?_, hmass⟩
  intro x hx
  simp only [H1Function.smul_toFun, H1Function.unscale_toFun]
  change (r * a ^ 2)⁻¹ * u.toFun (a • x + z) = _
  rw [hu (a • x + z) ⟨a • x, ⟨x, hx, rfl⟩, rfl⟩]
  change (r * a ^ 2)⁻¹ * D.solution
      (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0 (a • x + z) =
    (rawClock M L m : ℝ)⁻¹ * D.solution
      (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0 (e x)
  rw [← hclock]
  congr 1
  dsimp [e, physicalCoordinates, a]
  simp [add_comm]

theorem laplace_dilation {F G : ℝ → ℝ} (c : ℝ) (hc : 0 < c)
    (h : ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        c⁻¹ * ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * s)) * G s) :
    ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * G (c * s) := by
  intro mu hmu
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi
    (fun s : ℝ => Real.exp (-((mu / c) * s)) * G s) 0 hc
  calc
    (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        c⁻¹ * ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * s)) * G s := h mu hmu
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * (c * s))) * G (c * s) := by
      simpa only [Function.comp_apply, mul_zero, zero_mul, smul_eq_mul] using hchange.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      rw [show (mu / c) * (c * s) = mu * s by
        rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']]

theorem datum_conjugacy
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (D.fellerKernelSemigroup hdense)
      ((transportedDatum D e c hc).fellerKernelSemigroup
        (transportedDatum_dense D hdense e c hc)) e.symm c := by
  let E := transportedDatum D e c hc
  let he := transportedDatum_dense D hdense e c hc
  let P := D.fellerKernelSemigroup hdense
  let Q := E.fellerKernelSemigroup he
  have hPF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have hQF := E.isFellerKernelSemigroup_fellerKernelSemigroup he
  intro t x
  simp only [Homeomorph.symm_symm]
  change Q t x = (((P (c * t)) (e x)).map e.symm)
  have : IsFiniteMeasure (Q t x) :=
    ⟨lt_of_le_of_lt (Q.isSubMarkovKernel t x) (by norm_num)⟩
  have : IsFiniteMeasure ((P (c * t)) (e x)) :=
    ⟨lt_of_le_of_lt (P.isSubMarkovKernel _ _) (by norm_num)⟩
  have : IsFiniteMeasure (((P (c * t)) (e x)).map e.symm) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
  let f : C₀(Vec d, ℝ) :=
    ⟨⟨fun y => g y, g.continuous⟩, zero_at_infty g⟩
  let f0 := pullback e.symm f
  let F : ℝ → ℝ := fun s => kernelIntegral (Q (Real.toNNReal s)) f x
  let G : ℝ → ℝ := fun s => kernelIntegral (P (Real.toNNReal s)) f0 (e x)
  have hFc : Continuous F := E7.continuous_kernelIntegral_of_feller Q hQF f x
  have hGc : Continuous G := E7.continuous_kernelIntegral_of_feller P hPF f0 (e x)
  have hlap : ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * G ((c : ℝ) * s) := by
    apply laplace_dilation (c : ℝ) hc
    intro mu hmu
    have hsol := E.solution_eq_laplace he ⟨mu, hmu⟩ f x
    change (c : ℝ)⁻¹ * D.solution (dividedShift c hc ⟨mu, hmu⟩) f0 (e x) = _ at hsol
    rw [D.solution_eq_laplace hdense] at hsol
    simpa only [F, G, dividedShift, neg_mul] using hsol.symm
  have hFb : ∀ s, |F s| ≤ max ‖f‖ ‖f0‖ :=
    fun s => (E7.abs_kernelIntegral_le Q _ f x).trans (le_max_left _ _)
  have hGb : ∀ s, |G ((c : ℝ) * s)| ≤ max ‖f‖ ‖f0‖ :=
    fun s => (E7.abs_kernelIntegral_le P _ f0 (e x)).trans (le_max_right _ _)
  have htime := eq_of_forall_integral_exp_neg_mul_eq hFc
    (hGc.comp (continuous_const.mul continuous_id)) hFb hGb hlap (t : ℝ) t.coe_nonneg
  have hn : Real.toNNReal ((c : ℝ) * (t : ℝ)) = c * t := by
    change Real.toNNReal ((c * t : ℝ≥0) : ℝ) = c * t
    exact Real.toNNReal_coe
  have hint : kernelIntegral (Q t) f x = kernelIntegral (P (c * t)) f0 (e x) := by
    change kernelIntegral (Q (Real.toNNReal (t : ℝ))) f x =
      kernelIntegral (P (Real.toNNReal ((c : ℝ) * (t : ℝ)))) f0 (e x) at htime
    rw [Real.toNNReal_coe, hn] at htime
    exact htime
  have hmap : (∫ y, g y ∂(((P (c * t)) (e x)).map e.symm)) =
      ∫ y, g (e.symm y) ∂((P (c * t)) (e x)) :=
    integral_map e.symm.measurable.aemeasurable
      (show AEStronglyMeasurable (fun y : Vec d => g y)
        (((P (c * t)) (e x)).map e.symm) from
        (show Continuous (fun y : Vec d => g y) from g.continuous).aestronglyMeasurable)
  rw [hmap]
  exact hint

theorem ordered_marginal
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (μ : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    (hμ : ∀ I : Finset NNReal,
      μ.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    μ.map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      SubMarkovKernelSemigroup.finiteTimeKernel P times x := by
  classical
  let I : Finset NNReal :=
    Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card :=
    phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : NNReal) = times i :=
    fun _ ↦ rfl
  have hsel : Measurable (fun w : I → SpatialCoordinates d =>
      w ∘ (phi : Fin n → I)) := by
    exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  have hcomp : ContinuousPath.finiteEvaluation (α := SpatialCoordinates d)
      (fun i ↦ times i) =
      (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation I := by
    funext path i
    rfl
  have hrestrict :
      (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) ∘
          SubMarkovKernelSemigroup.orderedPathToFiniteSet I =
        FiniteOrderedTimes.restrictPath emb := by
    rfl
  have htimes : (SubMarkovKernelSemigroup.finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show SubMarkovKernelSemigroup.finiteSetTimes I
        ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  have hset : SubMarkovKernelSemigroup.finiteSetKernel P I x =
      (SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
    rw [← Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)]
    exact congrArg (fun K : Kernel (SpatialCoordinates d) (I → SpatialCoordinates d) => K x)
      (SubMarkovKernelSemigroup.finiteSetKernel_eq_map P I)
  calc
    μ.map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
        (μ.map (ContinuousPath.finsetEvaluation I)).map
          (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hcomp, ← Measure.map_map hsel hfinset]
    _ = (SubMarkovKernelSemigroup.finiteSetKernel P I x).map
          (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hμ I]
    _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I)).map
            (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hset]
    _ = (SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (FiniteOrderedTimes.restrictPath emb) := by
      rw [Measure.map_map hsel
        (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I), hrestrict]
    _ = SubMarkovKernelSemigroup.finiteTimeKernel P
        ((SubMarkovKernelSemigroup.finiteSetTimes I).restrict emb) x := by
      rw [← Kernel.map_apply _ (FiniteOrderedTimes.measurable_restrictPath emb)]
      exact congrArg (fun K : Kernel (SpatialCoordinates d) (Fin n → SpatialCoordinates d) => K x)
        (hP.finiteTimeKernel_map_restrictPath P
          (SubMarkovKernelSemigroup.finiteSetTimes I) emb)
    _ = SubMarkovKernelSemigroup.finiteTimeKernel P times x := by rw [htimes]

variable [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

theorem rescaled_fdd
    (P P' : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (DiffusionPath d)) (_hK : IsMarkovKernel K)
    (hKmarg : ∀ I x, (K x).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (hconj : SubMarkovKernelSemigroup.IsRescaledConjugate P P' e c) :
    ∀ I x, ((K (e.symm x)).map (ContinuousPath.rescale e c)).map
        (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P' I x := by
  classical
  let : IsMarkovKernel K := _hK
  intro I x
  let hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)
  let hfinite : Measurable (ContinuousPath.finiteEvaluation
      (α := Vec d) (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation I ∘ ContinuousPath.rescale e c =
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) ∘ ContinuousPath.finiteEvaluation
          (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i) := by
    funext path t
    show e (path (c * (t : NNReal))) = e (path (c * SubMarkovKernelSemigroup.finiteSetTimes I
      ((I.orderIsoOfFin rfl).symm t)))
    rw [SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply]
  have hordered := ordered_marginal P hP (K (e.symm x)) (e.symm x)
    (fun J => hKmarg J (e.symm x)) ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc)
  have hfinite' := congrArg (fun Q : Kernel (Vec d) (I → Vec d) => Q x)
    (hconj.finiteSetKernel_eq hc hP I)
  rw [Kernel.map_apply _ hmapPath, Kernel.comap_apply] at hfinite'
  calc
    ((K (e.symm x)).map (ContinuousPath.rescale e c)).map (ContinuousPath.finsetEvaluation I) =
        (K (e.symm x)).map (ContinuousPath.finsetEvaluation I ∘ ContinuousPath.rescale e c) :=
      Measure.map_map (ContinuousPath.measurable_finsetEvaluation I) (ContinuousPath.measurable_rescale e c)
    _ = ((K (e.symm x)).map (ContinuousPath.finiteEvaluation
        (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i))).map
          ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
            SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
      rw [hcomp, ← Measure.map_map hmapPath hfinite]
    _ = _ := by rw [hordered]; exact hfinite'.symm

end SubdiffusiveProcess.Section10.LegacyPhysicalTransport
