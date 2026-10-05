module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Sobolev.NativeH1
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Homogenization.Sobolev.Foundations.PoincareMeanZero
public import SubdiffusiveProcess.Paper.neumann_boundary_identity_face_trace

@[expose] public section

open MeasureTheory TopologicalSpace Set Filter
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open BoxIntegral
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem test_smooth_identity
    (n : ℕ) (φ : SpatialCoordinates (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (p : SpatialCoordinates (n + 1)) :
    ∑ i : Fin (n + 1), p i *
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (fderiv ℝ φ x) (Pi.single i 1) =
      ∑ i : Fin (n + 1), p i *
        ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            φ (Fin.insertNth i 1 y)) -
          (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            φ (Fin.insertNth i 0 y))) := by
  let I : Box (Fin (n + 1)) :=
    ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num⟩
  have hQ : (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) = Box.Ioo I := by
    rw [unitNeumannCube, centeredCube_eq_pi]
    ext x
    change _ ↔ x ∈ Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)
    simp
    norm_num
  have hQface : ∀ i : Fin (n + 1),
      (unitNeumannCube n : Set (SpatialCoordinates n)) = Box.Ioo (I.face i) := by
    intro i
    rw [unitNeumannCube, centeredCube_eq_pi]
    ext x
    change _ ↔ x ∈ Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)
    simp
    norm_num
  have hle : I.lower ≤ I.upper := fun i => (I.lower_lt_upper i).le
  have hdiv :
      (∫ x in Box.Icc I, ∑ i : Fin (n + 1),
        (p i • fderiv ℝ φ x) (Pi.single i 1)) =
        ∑ i : Fin (n + 1),
          ((∫ x in Box.Icc (I.face i),
              p i * φ (Fin.insertNth i (I.upper i) x)) -
            (∫ x in Box.Icc (I.face i),
              p i * φ (Fin.insertNth i (I.lower i) x))) := by
    refine integral_divergence_of_hasFDerivAt_off_countable' I.lower I.upper hle
      (fun i x => p i * φ x) (fun i x => p i • fderiv ℝ φ x) ∅ countable_empty ?_ ?_ ?_
    · intro i
      exact (continuous_const.mul hφ.continuous).continuousOn
    · intro x hx i
      simpa [smul_eq_mul] using
        ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.const_mul (p i))
    · have hc : Continuous (fun x => ∑ i : Fin (n + 1),
          (p i • fderiv ℝ φ x) (Pi.single i 1)) := by
        fun_prop
      exact hc.continuousOn.integrableOn_compact (Box.isCompact_Icc I)
  have hcoord : ∀ i : Fin (n + 1),
      IntegrableOn (fun x => p i * (fderiv ℝ φ x) (Pi.single i 1)) (Box.Icc I) := by
    intro i
    have hc : Continuous (fun x => (fderiv ℝ φ x) (Pi.single i 1)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (continuous_const.mul hc).continuousOn.integrableOn_compact
      (Box.isCompact_Icc I)
  have hsum :
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          ∑ i : Fin (n + 1), p i * (fderiv ℝ φ x) (Pi.single i 1)) =
        ∑ i : Fin (n + 1), p i *
          ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
            (fderiv ℝ φ x) (Pi.single i 1) := by
    have hsub : (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) ⊆ Box.Icc I := by
      rw [hQ]
      exact Box.Ioo_subset_Icc I
    rw [integral_finsetSum Finset.univ (fun i hi => (hcoord i).mono_set hsub)]
    simp_rw [integral_const_mul]
  have hset :
      (∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          ∑ i : Fin (n + 1), p i * (fderiv ℝ φ x) (Pi.single i 1)) =
        (∫ x in Box.Icc I, ∑ i : Fin (n + 1),
          (p i • fderiv ℝ φ x) (Pi.single i 1)) := by
    rw [hQ]
    rw [setIntegral_congr_set (Box.Ioo_ae_eq_Icc I)]
    congr 1
  have hfront : ∀ i : Fin (n + 1),
      (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          φ (Fin.insertNth i 1 y)) =
        ∫ y in Box.Icc (I.face i), φ (Fin.insertNth i (I.upper i) y) := by
    intro i
    rw [hQface i]
    rw [setIntegral_congr_set (Box.Ioo_ae_eq_Icc (I.face i))]
  have hback : ∀ i : Fin (n + 1),
      (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          φ (Fin.insertNth i 0 y)) =
        ∫ y in Box.Icc (I.face i), φ (Fin.insertNth i (I.lower i) y) := by
    intro i
    rw [hQface i]
    rw [setIntegral_congr_set (Box.Ioo_ae_eq_Icc (I.face i))]
  rw [← hsum, hset, hdiv]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_const_mul, ← hfront i, ← hback i]
  ring

theorem aux_neumann_boundary_identity_weak_ftc_smooth
    (n : ℕ) (p : SpatialCoordinates (n + 1))
    (Tr : (i : Fin (n + 1)) → (side : Bool) →
      weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] DomainL2 (unitNeumannCube n))
    (hTr : ∀ (φ : SpatialCoordinates (n + 1) → ℝ),
      ContDiff ℝ 1 φ →
        ∀ (v : weakSobolevGraph (unitNeumannCube (n + 1))),
          ((v : SobolevData (unitNeumannCube (n + 1))).1 :
            SpatialCoordinates (n + 1) → ℝ) =ᵐ[
              volume.restrict (unitNeumannCube (n + 1) :
                Set (SpatialCoordinates (n + 1)))] φ →
            ∀ (i : Fin (n + 1)) (side : Bool),
              ((Tr i side v : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) =ᵐ[
                  volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))]
                (fun y => φ (Fin.insertNth i (if side then 1 else 0) y)))
    (ψ : ℕ → Homogenization.H1Function
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))))
    (w : ℕ → weakSobolevGraph (unitNeumannCube (n + 1)))
    (hw_spec : ∀ k : ℕ,
      ((w k : SobolevData (unitNeumannCube (n + 1))).1 :
        SpatialCoordinates (n + 1) → ℝ) =ᵐ[
          volume.restrict (unitNeumannCube (n + 1) :
            Set (SpatialCoordinates (n + 1)))] (ψ k).toFun ∧
      ∀ i : Fin (n + 1),
        ((w k : SobolevData (unitNeumannCube (n + 1))).2 i :
          SpatialCoordinates (n + 1) → ℝ) =ᵐ[
            volume.restrict (unitNeumannCube (n + 1) :
              Set (SpatialCoordinates (n + 1)))] fun x => (ψ k).grad x i)
    (hψC : ∀ k : ℕ, ContDiff ℝ 1 (ψ k).toFun)
    (hψgradf : ∀ k : ℕ, (ψ k).grad = fun x j =>
      (fderiv ℝ (ψ k).toFun x) (Pi.single j 1)) :
    ∀ k : ℕ,
      (∑ i : Fin (n + 1), p i * ∫ x in
          (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
            (sobolevGradient (w k : SobolevData (unitNeumannCube (n + 1))) i) x) =
        ∑ i : Fin (n + 1), p i *
          ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
              ((Tr i true (w k) : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) y) -
            (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
              ((Tr i false (w k) : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) y)) := by
  have hsg : ∀ (z : SobolevData (unitNeumannCube (n + 1))) (i : Fin (n + 1)),
      (sobolevGradient z).ofLp i = z.2 i := by
    intro z i
    simp [sobolevGradient]
  intro k
  have hbase := test_smooth_identity n (ψ k).toFun (hψC k) p
  have hwgradf : ∀ (i : Fin (n + 1)),
      ((w k : SobolevData (unitNeumannCube (n + 1))).2 i :
        SpatialCoordinates (n + 1) → ℝ) =ᵐ[
          volume.restrict (unitNeumannCube (n + 1) :
            Set (SpatialCoordinates (n + 1)))]
        fun x => (fderiv ℝ (ψ k).toFun x) (Pi.single i 1) := by
    intro i
    filter_upwards [(hw_spec k).2 i] with x hx
    exact hx.trans (congrFun (congrFun (hψgradf k) x) i)
  have htrue : ∀ i : Fin (n + 1),
      (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i true (w k) : DomainL2 (unitNeumannCube n)) :
            SpatialCoordinates n → ℝ) y) =
        ∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          (ψ k).toFun (Fin.insertNth i 1 y) := by
    intro i
    apply integral_congr_ae
    simpa using (hTr (ψ k).toFun (hψC k) (w k) (hw_spec k).1 i true)
  have hfalse : ∀ i : Fin (n + 1),
      (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i false (w k) : DomainL2 (unitNeumannCube n)) :
            SpatialCoordinates n → ℝ) y) =
        ∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          (ψ k).toFun (Fin.insertNth i 0 y) := by
    intro i
    apply integral_congr_ae
    simpa using (hTr (ψ k).toFun (hψC k) (w k) (hw_spec k).1 i false)
  rw [show (∑ i : Fin (n + 1), p i * ∫ x in
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        (sobolevGradient (w k : SobolevData (unitNeumannCube (n + 1))) i) x) =
      ∑ i : Fin (n + 1), p i * ∫ x in
        (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (fderiv ℝ (ψ k).toFun x) (Pi.single i 1) by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        apply integral_congr_ae
        have hco :
            ((sobolevGradient (w k : SobolevData (unitNeumannCube (n + 1)))).ofLp i :
              SpatialCoordinates (n + 1) → ℝ) =ᵐ[
                volume.restrict (unitNeumannCube (n + 1) :
                  Set (SpatialCoordinates (n + 1)))]
              fun x => (fderiv ℝ (ψ k).toFun x) (Pi.single i 1) := by
          rw [hsg]
          exact hwgradf i
        exact hco]
  calc
    _ = ∑ i : Fin (n + 1), p i *
        ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            (ψ k).toFun (Fin.insertNth i 1 y)) -
          (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            (ψ k).toFun (Fin.insertNth i 0 y))) := hbase
    _ = _ := by
      simp only [htrue, hfalse]

/-- Proof-step fine child: extension of the coordinate FTC from smooth
functions to the weak Sobolev graph using the bounded face traces. The face-trace
characterization is the only supplied analytic interface. -/
theorem aux_neumann_boundary_identity_weak_ftc_proof
    (n : ℕ) (_hn : 1 ≤ n)
    (Tr : (i : Fin (n + 1)) → (side : Bool) →
      weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] DomainL2 (unitNeumannCube n))
    (hTr : ∀ (φ : SpatialCoordinates (n + 1) → ℝ),
      ContDiff ℝ 1 φ →
        ∀ (v : weakSobolevGraph (unitNeumannCube (n + 1))),
          ((v : SobolevData (unitNeumannCube (n + 1))).1 :
            SpatialCoordinates (n + 1) → ℝ) =ᵐ[
              volume.restrict (unitNeumannCube (n + 1) :
                Set (SpatialCoordinates (n + 1)))] φ →
            ∀ (i : Fin (n + 1)) (side : Bool),
              ((Tr i side v : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) =ᵐ[
                  volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))]
                (fun y => φ (Fin.insertNth i (if side then 1 else 0) y)))
    (v : weakSobolevGraph (unitNeumannCube (n + 1)))
    (p : SpatialCoordinates (n + 1)) :
    ∃ w : ℕ → weakSobolevGraph (unitNeumannCube (n + 1)),
      Tendsto w atTop (nhds v) ∧
      ∀ k : ℕ,
        (∑ i : Fin (n + 1), p i * ∫ x in
            (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
              (sobolevGradient (w k : SobolevData (unitNeumannCube (n + 1))) i) x) =
          ∑ i : Fin (n + 1), p i *
            ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
                ((Tr i true (w k) : DomainL2 (unitNeumannCube n)) :
                  SpatialCoordinates n → ℝ) y) -
              (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
                ((Tr i false (w k) : DomainL2 (unitNeumannCube n)) :
                  SpatialCoordinates n → ℝ) y)) := by
  obtain ⟨u, hu, hgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  have hQconv :
      Homogenization.IsOpenBoundedConvexDomain
        (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) := by
    change Homogenization.IsOpenBoundedConvexDomain
      (Metric.ball (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) (1 / 2))
    exact Homogenization.isOpenBoundedConvexDomain_ball _ (by norm_num)
  have huv : u.toScalarL2 = (v : SobolevData (unitNeumannCube (n + 1))).1 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [u.coeFn_toScalarL2] with x hx
    exact hx.trans (congrFun hu x)
  have huvgrad : ∀ i : Fin (n + 1),
      u.gradCoordToScalarL2 i = (v : SobolevData (unitNeumannCube (n + 1))).2 i := by
    intro i
    apply MeasureTheory.Lp.ext
    filter_upwards [u.coeFn_gradCoordToScalarL2 i] with x hx
    exact hx.trans (congrFun (congrFun hgrad x) i)
  let x0 : SpatialCoordinates (n + 1) := fun _ => (1 / 2 : ℝ)
  have hball : Metric.closedBall x0 (1 / 4) ⊆
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) := by
    rw [show (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) =
      Metric.ball x0 (1 / 2) by rfl]
    exact Metric.closedBall_subset_ball (by norm_num)
  let ψ : ℕ → Homogenization.H1Function
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) :=
    Homogenization.H1Function.convexApproxSmoothH1 hQconv u x0 (r := (1 / 4 : ℝ))
      (by norm_num)
  have hψval : Tendsto (fun k => (ψ k).toScalarL2) atTop
      (nhds u.toScalarL2) := by
    simpa [ψ] using
      (Homogenization.H1Function.tendsto_convexApproxSmoothH1_toScalarL2
        hQconv u hball (by norm_num))
  have hψgrad : ∀ i : Fin (n + 1),
      Tendsto (fun k => (ψ k).gradCoordToScalarL2 i) atTop
        (nhds (u.gradCoordToScalarL2 i)) := by
    intro i
    simpa [ψ] using
      (Homogenization.H1Function.tendsto_convexApproxSmoothH1_gradCoordToScalarL2
        hQconv u hball (by norm_num) i)
  let w : ℕ → weakSobolevGraph (unitNeumannCube (n + 1)) := fun k =>
    Classical.choose (exists_weakSobolevGraph_of_nativeH1 (ψ k))
  have hw_spec : ∀ k : ℕ,
      ((w k : SobolevData (unitNeumannCube (n + 1))).1 : SpatialCoordinates (n + 1) → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))]
            (ψ k).toFun ∧
      ∀ i : Fin (n + 1),
        ((w k : SobolevData (unitNeumannCube (n + 1))).2 i : SpatialCoordinates (n + 1) → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))]
            fun x => (ψ k).grad x i := by
    intro k
    exact Classical.choose_spec (exists_weakSobolevGraph_of_nativeH1 (ψ k))
  have hwval : ∀ k : ℕ,
      (w k : SobolevData (unitNeumannCube (n + 1))).1 = (ψ k).toScalarL2 := by
    intro k
    apply MeasureTheory.Lp.ext
    filter_upwards [(hw_spec k).1, (ψ k).coeFn_toScalarL2] with x hx hy
    exact hx.trans hy.symm
  have hwgrad : ∀ (k : ℕ) (i : Fin (n + 1)),
      (w k : SobolevData (unitNeumannCube (n + 1))).2 i =
        (ψ k).gradCoordToScalarL2 i := by
    intro k i
    apply MeasureTheory.Lp.ext
    filter_upwards [(hw_spec k).2 i, (ψ k).coeFn_gradCoordToScalarL2 i] with x hx hy
    exact hx.trans hy.symm
  have hwscalar : Tendsto
      (fun k => (w k : SobolevData (unitNeumannCube (n + 1))).1) atTop
        (nhds (v : SobolevData (unitNeumannCube (n + 1))).1) := by
    have h := hψval
    rw [← show (fun k => (w k : SobolevData (unitNeumannCube (n + 1))).1) =
        (fun k => (ψ k).toScalarL2) by funext k; exact hwval k] at h
    rw [huv] at h
    exact h
  have hwgradient : Tendsto
      (fun k => (w k : SobolevData (unitNeumannCube (n + 1))).2) atTop
        (nhds (v : SobolevData (unitNeumannCube (n + 1))).2) := by
    apply tendsto_pi_nhds.2
    intro i
    have h := hψgrad i
    rw [← show (fun k => (w k : SobolevData (unitNeumannCube (n + 1))).2 i) =
        (fun k => (ψ k).gradCoordToScalarL2 i) by funext k; exact hwgrad k i] at h
    rw [huvgrad i] at h
    exact h
  have hwdata : Tendsto
      (fun k => (w k : SobolevData (unitNeumannCube (n + 1)))) atTop
        (nhds (v : SobolevData (unitNeumannCube (n + 1)))) := by
    exact hwscalar.prodMk_nhds hwgradient
  have hw : Tendsto w atTop (nhds v) := by
    rw [tendsto_subtype_rng]
    exact hwdata
  have hψC : ∀ k : ℕ, ContDiff ℝ 1 (ψ k).toFun := by
    intro k
    rw [show (ψ k).toFun =
        Homogenization.convexApproxSmoothRepresentative
          (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))
          Homogenization.unitConvexApproxKernel u.toFun x0 (1 / 4 : ℝ)
          (Homogenization.unitConvexApproxScale k) by
      simpa [ψ] using
        (Homogenization.H1Function.convexApproxSmoothH1_toFun
          hQconv u x0 (r := (1 / 4 : ℝ)) (by norm_num) k)]
    exact (Homogenization.contDiff_convexApproxSmoothRepresentative
      hQconv.isOpen.measurableSet
      (Homogenization.isConvexApproxKernel_unitConvexApproxKernel (d := n + 1))
      (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 (by norm_num)
      (Homogenization.W1pFunction.unitConvexApproxScale_pos k)).of_le (by simp)
  have hψgradf : ∀ k : ℕ,
      (ψ k).grad = fun x j =>
        (fderiv ℝ (ψ k).toFun x) (Pi.single j 1) := by
    intro k
    funext x j
    have hgrad' := Homogenization.H1Function.convexApproxSmoothH1_grad
      hQconv u x0 (r := (1 / 4 : ℝ)) (by norm_num) k
    have hfun' := Homogenization.H1Function.convexApproxSmoothH1_toFun
      hQconv u x0 (r := (1 / 4 : ℝ)) (by norm_num) k
    simpa [ψ, hfun'] using! congrFun (congrFun hgrad' x) j
  have hwgradf : ∀ (k : ℕ) (i : Fin (n + 1)),
      ((w k : SobolevData (unitNeumannCube (n + 1))).2 i : SpatialCoordinates (n + 1) → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))]
          fun x => (fderiv ℝ (ψ k).toFun x) (Pi.single i 1) := by
    intro k i
    filter_upwards [(hw_spec k).2 i] with x hx
    exact hx.trans (congrFun (congrFun (hψgradf k) x) i)
  have hsmooth := aux_neumann_boundary_identity_weak_ftc_smooth
    n p Tr hTr ψ w hw_spec hψC hψgradf
  exact ⟨w, hw, hsmooth⟩

theorem aux_neumann_boundary_identity_weak_ftc_limit
    (n : ℕ) (p : SpatialCoordinates (n + 1))
    (Tr : (i : Fin (n + 1)) → (side : Bool) →
      weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] DomainL2 (unitNeumannCube n))
    (v : weakSobolevGraph (unitNeumannCube (n + 1)))
    (w : ℕ → weakSobolevGraph (unitNeumannCube (n + 1)))
    (hw : Tendsto w atTop (nhds v))
    (hsmooth : ∀ k : ℕ,
      (∑ i : Fin (n + 1), p i * ∫ x in
          (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
            (sobolevGradient (w k : SobolevData (unitNeumannCube (n + 1))) i) x) =
        ∑ i : Fin (n + 1), p i *
          ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
              ((Tr i true (w k) : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) y) -
            (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
              ((Tr i false (w k) : DomainL2 (unitNeumannCube n)) :
                SpatialCoordinates n → ℝ) y))) :
    (∑ i : Fin (n + 1), p i * ∫ x in
        (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (sobolevGradient (v : SobolevData (unitNeumannCube (n + 1))) i) x) =
      ∑ i : Fin (n + 1), p i *
        ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            ((Tr i true v : DomainL2 (unitNeumannCube n)) :
              SpatialCoordinates n → ℝ) y) -
          (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            ((Tr i false v : DomainL2 (unitNeumannCube n)) :
              SpatialCoordinates n → ℝ) y)) := by
  let L : weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] ℝ :=
    (affineNeumannLoad p).comp
      ((sobolevGradient (Ω := unitNeumannCube (n + 1))).comp
        (weakSobolevGraph (unitNeumannCube (n + 1))).subtypeL)
  let C : DomainL2 (unitNeumannCube n) →L[ℝ] ℝ :=
    innerSL ℝ (domainConstantL2 (Ω := unitNeumannCube n) 1)
  let B : weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] ℝ :=
    ∑ i : Fin (n + 1), p i •
      (C.comp (Tr i true) - C.comp (Tr i false))
  have hL_apply (z : weakSobolevGraph (unitNeumannCube (n + 1))) :
      L z = ∑ i : Fin (n + 1), p i *
        ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (sobolevGradient (z : SobolevData (unitNeumannCube (n + 1))) i) x := by
    simp [L, affineNeumannLoad_apply, integral_const_mul]
  have hB_apply (z : weakSobolevGraph (unitNeumannCube (n + 1))) :
      B z = ∑ i : Fin (n + 1), p i *
        ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            ((Tr i true z : DomainL2 (unitNeumannCube n)) :
              SpatialCoordinates n → ℝ) y) -
          (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
            ((Tr i false z : DomainL2 (unitNeumannCube n)) :
              SpatialCoordinates n → ℝ) y)) := by
    simp [B, C, inner_domainConstantL2]
  have hLlim : Tendsto (fun k => L (w k)) atTop (nhds (L v)) :=
    (L.continuous.tendsto v).comp hw
  have hBlim : Tendsto (fun k => B (w k)) atTop (nhds (B v)) :=
    (B.continuous.tendsto v).comp hw
  have hLB : ∀ k : ℕ, L (w k) = B (w k) := by
    intro k
    rw [hL_apply, hB_apply]
    exact hsmooth k
  have hBtoL : Tendsto (fun k => B (w k)) atTop (nhds (L v)) := by
    apply hLlim.congr'
    filter_upwards [] with k
    exact hLB k
  have hLv : L v = B v := tendsto_nhds_unique hBtoL hBlim
  rw [hL_apply v, hB_apply v] at hLv
  exact hLv

theorem neumann_boundary_identity_weak_ftc
    (n : ℕ) (hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    let μface : Measure (SpatialCoordinates n) :=
      volume.restrict (Qface : Set (SpatialCoordinates n))
    ∀ (Tr : (i : Fin (n + 1)) → (side : Bool) →
        weakSobolevGraph Q →L[ℝ] DomainL2 Qface),
      (∀ (φ : SpatialCoordinates (n + 1) → ℝ),
        ContDiff ℝ 1 φ →
          ∀ (v : weakSobolevGraph Q),
            ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
              volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ →
              ∀ (i : Fin (n + 1)) (side : Bool),
                ((Tr i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[μface]
                  (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))) →
      ∀ (v : weakSobolevGraph Q) (p : SpatialCoordinates (n + 1)),
        (∑ i : Fin (n + 1),
            p i * ∫ x in (Q : Set (SpatialCoordinates (n + 1))),
              (sobolevGradient (v : SobolevData Q) i) x) =
          ∑ i : Fin (n + 1),
            p i *
              ((∫ y in (Qface : Set (SpatialCoordinates n)),
                  ((Tr i true v : DomainL2 Qface) : SpatialCoordinates n → ℝ) y) -
                (∫ y in (Qface : Set (SpatialCoordinates n)),
                  ((Tr i false v : DomainL2 Qface) : SpatialCoordinates n → ℝ) y)) := by
  dsimp
  intro Tr hTr v p
  obtain ⟨w, hw, hsmooth⟩ :=
    aux_neumann_boundary_identity_weak_ftc_proof n hn Tr hTr v p
  exact aux_neumann_boundary_identity_weak_ftc_limit
    n p Tr v w hw hsmooth

end SubdiffusiveProcess.Paper
