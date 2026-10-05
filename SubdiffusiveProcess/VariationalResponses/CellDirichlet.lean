module

public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover

@[expose] public section

/-!
# The cell Dirichlet problem on a centred cube

GMC's existence theorem for the scalar-forcing weak Dirichlet problem is stated
for a triadic cube, but its proof only uses that the carrier is an open bounded
convex domain.  This file states it for such a domain and instantiates it at the
centred cubes the mesh is built from, which are not triadic.
-/

open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A centred cube is an open bounded convex domain. -/
theorem lane2_isOpenBoundedConvexDomain_centeredCube (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  refine ⟨(centeredCube z r hr).isOpen, ?_, ?_⟩
  · refine Bornology.IsBounded.isBoundedDomain ?_
    show Bornology.IsBounded (Metric.ball z (r / 2))
    exact Metric.isBounded_ball
  · show Convex ℝ (Metric.ball z (r / 2))
    exact convex_ball z (r / 2)

/-- A continuous uniformly elliptic scalar coefficient gives an elliptic
coefficient field. -/
theorem lane2_isEllipticFieldOn_scalar {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a : SpatialCoordinates d → ℝ} (ha : Measurable a)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField a) := by
  classical
  refine ⟨?_, fun x hx =>
    (isEllipticMatrix_scalarMatrix
      (lt_of_lt_of_le hlam (hb x hx).1)).mono hlam (hb x hx).1 (hb x hx).2⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst hij
    have he : (fun x => if x ∈ W then scalarCoeffField a x i i else 0)
        = fun x => if x ∈ W then a x else 0 := by
      funext x
      by_cases hx : x ∈ W <;> simp [hx, scalarCoeffField, scalarMatrix]
    rw [he]
    exact Measurable.ite hW ha measurable_const
  · have he : (fun x => if x ∈ W then scalarCoeffField a x i j else 0)
        = fun _ => (0 : ℝ) := by
      funext x
      by_cases hx : x ∈ W <;> simp [hx, scalarCoeffField, scalarMatrix, hij]
    rw [he]
    exact measurable_const

/-- **Existence for the cell Dirichlet problem on an open bounded convex
domain.**  GMC's `exists_isScalarDirichletSolutionOn` is stated for a triadic
cube, but its proof uses the cube only through
`IsOpenBoundedConvexDomain`; this is the same argument for a general such
domain, with zero forcing and a scalar coefficient. -/
theorem lane2_exists_weaklyHarmonic_of_zeroTrace [NeZero d]
    {W : Set (SpatialCoordinates d)} (hWgeom : IsOpenBoundedConvexDomain W)
    (hne : W.Nonempty) {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (hD : H1Function W) :
    ∃ u : H1Function W, HasZeroTraceDifferenceOn W u hD ∧
      IsWeaklyHarmonicOn a W u := by
  have : IsFiniteMeasure (volumeMeasureOn W) :=
    hWgeom.isFiniteMeasure_restrict_volume
  have hDatumFlux : MemVectorL2 W
      (fun x => matVecMul (scalarCoeffField a x) (hD.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hD.grad_memVectorL2
  have hG : MemVectorL2 W
      (fun x => -matVecMul (scalarCoeffField a x) (hD.grad x)) := hDatumFlux.neg
  have hRealize :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hWgeom
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := scalarCoeffField a) (U := W)
      (g := fun x => -matVecMul (scalarCoeffField a x) (hD.grad x))
      (lam := lam) (Lam := Lam) hG hRealize hne hEll
  refine ⟨hD + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, fun φ => ?_⟩
  have hDatumInt := integrableOn_vecDot_of_memVectorL2 hDatumFlux
    φ.toH1Function.grad_memVectorL2
  have hCorrFlux : MemVectorL2 W
      (fun x => matVecMul (scalarCoeffField a x) (w.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      w.toH1Function.grad_memVectorL2
  have hCorrInt := integrableOn_vecDot_of_memVectorL2 hCorrFlux
    φ.toH1Function.grad_memVectorL2
  have hconv : (fun x => vecDot (a x • (hD + w.toH1Function).grad x)
      (φ.toH1Function.grad x))
      = fun x => vecDot (matVecMul (scalarCoeffField a x)
        ((hD + w.toH1Function).grad x)) (φ.toH1Function.grad x) := by
    funext x
    rw [scalarCoeffField, matVecMul_scalarMatrix]
  have hsplit : (fun x => vecDot (matVecMul (scalarCoeffField a x)
        ((hD + w.toH1Function).grad x)) (φ.toH1Function.grad x))
      = fun x => vecDot (matVecMul (scalarCoeffField a x) (hD.grad x))
          (φ.toH1Function.grad x)
        + vecDot (matVecMul (scalarCoeffField a x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x) := by
    funext x
    simp [H1Function.add_grad, matVecMul_add, vecDot_add_left]
  have hneg : (fun x => vecDot (-matVecMul (scalarCoeffField a x) (hD.grad x))
        (φ.toH1Function.grad x))
      = fun x => -vecDot (matVecMul (scalarCoeffField a x) (hD.grad x))
        (φ.toH1Function.grad x) := by
    funext x
    rw [vecDot_neg_left]
  have hwφ := hw φ
  rw [hneg, integral_neg] at hwφ
  show (∫ x in W, vecDot (a x • (hD + w.toH1Function).grad x)
    (φ.toH1Function.grad x) ∂volume) = 0
  rw [hconv, hsplit, integral_add hDatumInt hCorrInt, hwφ]
  ring

/-! ## Zero extension preserves the killed space -/

/-- **The zero extension of a killed datum is killed.**  On smooth compactly
supported data the zero extension is the extension of the test function, and the
killed space is the closure of those. -/
theorem lane2_zeroExtensionSobolevData_mem_killed
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U) {u : SobolevData V}
    (hu : u ∈ killedSobolevGraph V) :
    zeroExtensionSobolevData hV u ∈ killedSobolevGraph U := by
  have hm : Set.MapsTo (zeroExtensionSobolevData hV)
      (Set.range (smoothSobolevData (Ω := V)))
      (killedSobolevGraph U : Set (SobolevData U)) := by
    rintro w ⟨ψ, rfl⟩
    rw [lane2_zeroExtensionSobolevData_smooth]
    exact smoothSobolevData_mem_killed _
  apply hm.closure_left (lane2_continuous_zeroExtensionSobolevData hV)
    (isClosed_killedSobolevGraph (Ω := U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hu

/-! ## Gluing killed cell data -/

/-- The coefficient function of a finite sum in `L²`. -/
theorem lane2_Lp_coeFn_sum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} (f : ι → Lp ℝ 2 μ) (s : Finset ι) :
    (↑(∑ j ∈ s, f j) : α → ℝ)
      =ᵐ[μ] fun x => ∑ j ∈ s, ((f j : Lp ℝ 2 μ) : α → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using! Lp.coeFn_zero ℝ 2 μ
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ j ∈ s, f j), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]



/-- **The glued datum.**  Over finitely many pairwise disjoint subdomains, a
datum on the parent plus the zero extensions of killed data on the pieces is
killed on the parent, and on each piece it is the parent datum plus that
piece's datum.  This is what replaces the face-term cancellation: the cellwise
corrections `u_q - φ` are KILLED on their cells, and zero extension of a killed
datum is killed, so no trace matching across faces is needed to see that the
glued object lies in `H¹₀`. -/
theorem lane2_exists_glued_killed {Q : Opens (SpatialCoordinates d)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cell : ι → Opens (SpatialCoordinates d))
    (hle : ∀ k, cell k ≤ Q)
    (hdisj : Pairwise (fun k l : ι =>
      Disjoint (cell k : Set (SpatialCoordinates d))
        (cell l : Set (SpatialCoordinates d))))
    (φS : SobolevData Q) (hφS : φS ∈ killedSobolevGraph Q)
    (wk : ∀ k : ι, SobolevData (cell k))
    (hwk : ∀ k : ι, wk k ∈ killedSobolevGraph (cell k)) :
    ∃ W : SobolevData Q, W ∈ killedSobolevGraph Q ∧
      ∀ k : ι, ((W.1 : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (cell k : Set (SpatialCoordinates d))]
          fun x => ((φS.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x
            + (((wk k).1 : DomainL2 (cell k)) : SpatialCoordinates d → ℝ) x := by
  classical
  refine ⟨φS + ∑ k : ι, zeroExtensionSobolevData (hle k) (wk k), ?_, ?_⟩
  · exact Submodule.add_mem _ hφS (Submodule.sum_mem _ (fun k _ =>
      lane2_zeroExtensionSobolevData_mem_killed (hle k) (hwk k)))
  · intro k
    have hfst : ((φS + ∑ j : ι, zeroExtensionSobolevData (hle j) (wk j)).1 :
        DomainL2 Q)
        = φS.1 + ∑ j : ι, (zeroExtensionLp (hle j) ((wk j).1)) := by
      rw [Prod.fst_add]
      congr 1
      exact map_sum (AddMonoidHom.fst (DomainL2 Q) (Fin d → DomainL2 Q))
        (fun j : ι => zeroExtensionSobolevData (hle j) (wk j)) Finset.univ
    have hall : ∀ᵐ x ∂(volume.restrict (cell k : Set (SpatialCoordinates d))),
        ∀ j : ι, ((zeroExtensionLp (hle j) ((wk j).1) : DomainL2 Q) :
          SpatialCoordinates d → ℝ) x
          = (cell j : Set (SpatialCoordinates d)).indicator
            (((wk j).1 : DomainL2 (cell j)) : SpatialCoordinates d → ℝ) x :=
      ae_all_iff.2 (fun j =>
        ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) (hle k)
          (zeroExtensionLp_coeFn (hle j) ((wk j).1)))
    have hsum := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d))) (hle k)
      (Lp.coeFn_add φS.1 (∑ j : ι, zeroExtensionLp (hle j) ((wk j).1)))
    have hfin := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d))) (hle k)
      (lane2_Lp_coeFn_sum (fun j : ι => zeroExtensionLp (hle j) ((wk j).1))
        Finset.univ)
    filter_upwards [hall, hsum, hfin,
      ae_restrict_mem (cell k).isOpen.measurableSet] with x h1 h2 h3 hx
    rw [hfst]
    rw [h2, Pi.add_apply, h3]
    congr 1
    rw [Finset.sum_eq_single k]
    · rw [h1 k, Set.indicator_of_mem hx]
    · intro j _ hjk
      rw [h1 j, Set.indicator_of_notMem]
      exact fun hxj => (Set.disjoint_left.mp (hdisj (Ne.symm hjk)) hx) hxj
    · intro hk
      exact absurd (Finset.mem_univ k) hk

/-! ## The cellwise minimality -/

theorem lane2_integrableOn_coeff_vecDot {W : Opens (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C)
    {p q : SpatialCoordinates d → SpatialCoordinates d}
    (hp : ∀ i : Fin d, MemLp (fun x => p x i) 2
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (hq : ∀ i : Fin d, MemLp (fun x => q x i) 2
      (volume.restrict (W : Set (SpatialCoordinates d)))) :
    IntegrableOn (fun x => a x * vecDot (p x) (q x))
      (W : Set (SpatialCoordinates d)) volume := by
  have he : (fun x => a x * vecDot (p x) (q x))
      = fun x => ∑ i : Fin d, a x * (p x i * q x i) := by
    funext x
    rw [vecDot, Finset.mul_sum]
  rw [he]
  exact integrable_finsetSum _ (fun i _ =>
    lane2_integrableOn_coeff_mul hameas habd (hp i) (hq i))

/-- The energy of a sum expands with the cross term. -/
theorem lane2_energy_add {W : Opens (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C)
    (f g : H1Function (W : Set (SpatialCoordinates d))) :
    energy a (W : Set (SpatialCoordinates d)) (f + g)
      = energy a (W : Set (SpatialCoordinates d)) f
      + 2 * (∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (f.grad x) (g.grad x))
      + energy a (W : Set (SpatialCoordinates d)) g := by
  have hff := lane2_integrableOn_coeff_vecDot hameas habd
    (fun i => f.gradMemL2 i) (fun i => f.gradMemL2 i)
  have hfg := lane2_integrableOn_coeff_vecDot hameas habd
    (fun i => f.gradMemL2 i) (fun i => g.gradMemL2 i)
  have hgg := lane2_integrableOn_coeff_vecDot hameas habd
    (fun i => g.gradMemL2 i) (fun i => g.gradMemL2 i)
  have e1 : (∫ x in (W : Set (SpatialCoordinates d)),
      a x * vecDot ((f + g).grad x) ((f + g).grad x))
      = ∫ x in (W : Set (SpatialCoordinates d)),
        ((a x * vecDot (f.grad x) (f.grad x)
          + (a x * vecDot (f.grad x) (g.grad x)
            + a x * vecDot (f.grad x) (g.grad x)))
          + a x * vecDot (g.grad x) (g.grad x)) := by
    refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
    funext x
    rw [H1Function.add_grad]
    simp only [Pi.add_apply, vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have s3 : (∫ x in (W : Set (SpatialCoordinates d)),
      (a x * vecDot (f.grad x) (g.grad x)
        + a x * vecDot (f.grad x) (g.grad x)))
      = (∫ x in (W : Set (SpatialCoordinates d)),
          a x * vecDot (f.grad x) (g.grad x))
        + ∫ x in (W : Set (SpatialCoordinates d)),
          a x * vecDot (f.grad x) (g.grad x) := integral_add hfg hfg
  have s2 : (∫ x in (W : Set (SpatialCoordinates d)),
      (a x * vecDot (f.grad x) (f.grad x)
        + (a x * vecDot (f.grad x) (g.grad x)
          + a x * vecDot (f.grad x) (g.grad x))))
      = (∫ x in (W : Set (SpatialCoordinates d)),
          a x * vecDot (f.grad x) (f.grad x))
        + ∫ x in (W : Set (SpatialCoordinates d)),
          (a x * vecDot (f.grad x) (g.grad x)
            + a x * vecDot (f.grad x) (g.grad x)) :=
    integral_add hff (hfg.add hfg)
  have s1 : (∫ x in (W : Set (SpatialCoordinates d)),
      ((a x * vecDot (f.grad x) (f.grad x)
        + (a x * vecDot (f.grad x) (g.grad x)
          + a x * vecDot (f.grad x) (g.grad x)))
        + a x * vecDot (g.grad x) (g.grad x)))
      = (∫ x in (W : Set (SpatialCoordinates d)),
          (a x * vecDot (f.grad x) (f.grad x)
            + (a x * vecDot (f.grad x) (g.grad x)
              + a x * vecDot (f.grad x) (g.grad x))))
        + ∫ x in (W : Set (SpatialCoordinates d)),
          a x * vecDot (g.grad x) (g.grad x) :=
    integral_add (hff.add (hfg.add hfg)) hgg
  show (∫ x in (W : Set (SpatialCoordinates d)),
    a x * vecDot ((f + g).grad x) ((f + g).grad x)) = _
  rw [e1, s1, s2, s3]
  show ((∫ x in (W : Set (SpatialCoordinates d)),
      a x * vecDot (f.grad x) (f.grad x))
    + ((∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (f.grad x) (g.grad x))
      + ∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (f.grad x) (g.grad x)))
    + (∫ x in (W : Set (SpatialCoordinates d)),
      a x * vecDot (g.grad x) (g.grad x))
    = (∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (f.grad x) (f.grad x))
      + 2 * (∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (f.grad x) (g.grad x))
      + (∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (g.grad x) (g.grad x))
  ring

/-- **The harmonic extension minimises the energy in its trace class.** -/
theorem lane2_energy_isLeast {W : Opens (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C)
    (hanneg : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      0 ≤ a x)
    {u φ : H1Function (W : Set (SpatialCoordinates d))}
    (hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φ) :
    energy a (W : Set (SpatialCoordinates d)) u
      = sInf {e : ℝ | ∃ v : H1Function (W : Set (SpatialCoordinates d)),
        HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) v φ ∧
          e = energy a (W : Set (SpatialCoordinates d)) v} := by
  classical
  have hleast : IsLeast {e : ℝ | ∃ v : H1Function (W : Set (SpatialCoordinates d)),
      HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) v φ ∧
        e = energy a (W : Set (SpatialCoordinates d)) v}
      (energy a (W : Set (SpatialCoordinates d)) u) := by
    refine ⟨⟨u, htrace, rfl⟩, ?_⟩
    rintro e ⟨v, ⟨wv, hwv1, hwv2⟩, rfl⟩
    obtain ⟨wu, hwu1, hwu2⟩ := htrace
    set h : H10Function (W : Set (SpatialCoordinates d)) := wv - wu with hh
    have hsubgrad : ∀ x : SpatialCoordinates d,
        h.toH1Function.grad x = fun i => wv.toH1Function.grad x i
          - wu.toH1Function.grad x i := by
      intro x
      funext i
      show (wv.toH1Function + ((-1 : ℝ) • wu.toH1Function)).grad x i = _
      rw [H1Function.add_grad]
      simp
      ring
    have hsubfun : ∀ x : SpatialCoordinates d,
        h.toH1Function.toFun x
          = wv.toH1Function.toFun x - wu.toH1Function.toFun x := by
      intro x
      show (wv.toH1Function + ((-1 : ℝ) • wu.toH1Function)).toFun x = _
      rw [H1Function.add_toFun]
      simp
      ring
    have hvsum : v = u + h.toH1Function := by
      refine H1Function.ext ?_ ?_
      · funext x
        show v.toFun x = u.toFun x + h.toH1Function.toFun x
        rw [hsubfun x, hwv1 x, hwu1 x]
        ring
      · funext x
        funext i
        show v.grad x i = u.grad x i + h.toH1Function.grad x i
        rw [hsubgrad x]
        have h1 := congrFun (hwv2 x) i
        have h2 := congrFun (hwu2 x) i
        simp only [Pi.add_apply] at h1 h2
        rw [h1, h2]
        ring
    rw [hvsum, lane2_energy_add hameas habd u h.toH1Function]
    have hcross : (∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (u.grad x) (h.toH1Function.grad x)) = 0 := by
      have hharmh := hharm h
      rw [← hharmh]
      refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
      funext x
      rw [Homogenization.vecDot_smul_left]
    have hnn : 0 ≤ energy a (W : Set (SpatialCoordinates d)) h.toH1Function := by
      show 0 ≤ ∫ x in (W : Set (SpatialCoordinates d)),
        a x * vecDot (h.toH1Function.grad x) (h.toH1Function.grad x)
      refine setIntegral_nonneg_ae W.isOpen.measurableSet ?_
      filter_upwards [(ae_restrict_iff' W.isOpen.measurableSet).mp hanneg]
        with x hx
      intro hxW
      exact mul_nonneg (hx hxW) (vecNormSq_nonneg _)
    linarith [hcross, hnn]
  exact (IsLeast.csInf_eq hleast).symm

/-! ## Gradients follow the function, and energies add over the cells -/

/-- Two `H¹` functions agreeing almost everywhere have the same gradient almost
everywhere: weak derivatives see only the a.e. class, and are a.e. unique. -/
theorem lane2_grad_ae_eq_of_ae_eq {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u v : H1Function W)
    (h : u.toFun =ᵐ[volume.restrict W] v.toFun) (i : Fin d) :
    (fun x => u.grad x i) =ᵐ[volume.restrict W] fun x => v.grad x i := by
  have hfin : volume W ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hWb.isCompact_closure.measure_lt_top)
  have : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  have hui : IntegrableOn (fun x => u.grad x i) W volume :=
    (u.gradMemL2 i).integrable (by norm_num)
  have hvi : IntegrableOn (fun x => v.grad x i) W volume :=
    (v.gradMemL2 i).integrable (by norm_num)
  have hu : LocallyIntegrableOn (fun x => u.grad x i) W volume :=
    hui.locallyIntegrableOn
  have hv : LocallyIntegrableOn (fun x => v.grad x i) W volume :=
    hvi.locallyIntegrableOn
  exact HasWeakPartialDerivOn.ae_eq hW hu hv
    (_root_.SubdiffusiveProcess.EllipticRegularity.hasWeakPartialDerivOn_congr_ae h (Filter.EventuallyEq.refl _ _)
      (u.hasWeakPartialDerivOn i))
    (v.hasWeakPartialDerivOn i)

/-- **Energy adds over the cells.**  The cells are finitely many, pairwise
disjoint, and fill the parent up to a null set, so the energy integral splits;
on each cell the integrand is that of the cell datum. -/
theorem lane2_energy_sum_cells {Q : Opens (SpatialCoordinates d)}
    {ι : Type*} [Fintype ι] (cell : ι → Opens (SpatialCoordinates d))
    (hle : ∀ k, cell k ≤ Q)
    (hdisj : Pairwise (Function.onFun Disjoint
      (fun k : ι => (cell k : Set (SpatialCoordinates d)))))
    (hcover : (⋃ k : ι, (cell k : Set (SpatialCoordinates d)))
      =ᵐ[volume] (Q : Set (SpatialCoordinates d)))
    {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C)
    (W : H1Function (Q : Set (SpatialCoordinates d)))
    (uc : ∀ k : ι, H1Function (cell k : Set (SpatialCoordinates d)))
    (hagree : ∀ (k : ι) (i : Fin d),
      (fun x => W.grad x i)
        =ᵐ[volume.restrict (cell k : Set (SpatialCoordinates d))]
          fun x => (uc k).grad x i) :
    energy a (Q : Set (SpatialCoordinates d)) W
      = ∑ k : ι, energy a (cell k : Set (SpatialCoordinates d)) (uc k) := by
  classical
  have hint : ∀ k : ι, IntegrableOn
      (fun x => a x * vecDot (W.grad x) (W.grad x))
      (cell k : Set (SpatialCoordinates d)) volume := by
    intro k
    refine lane2_integrableOn_coeff_vecDot (W := cell k)
      (hameas.mono_measure (Measure.restrict_mono (hle k) le_rfl))
      (ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) (hle k) habd)
      (fun i => ?_) (fun i => ?_) <;>
      exact ((W.gradMemL2 i).mono_measure (Measure.restrict_mono (hle k) le_rfl))
  have hsplit : (∫ x in (Q : Set (SpatialCoordinates d)),
      a x * vecDot (W.grad x) (W.grad x))
      = ∑ k : ι, ∫ x in (cell k : Set (SpatialCoordinates d)),
        a x * vecDot (W.grad x) (W.grad x) := by
    rw [← setIntegral_congr_set hcover]
    exact integral_iUnion_fintype
      (fun k => (cell k).isOpen.measurableSet) hdisj hint
  show (∫ x in (Q : Set (SpatialCoordinates d)),
    a x * vecDot (W.grad x) (W.grad x)) = _
  rw [hsplit]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show _ = ∫ x in (cell k : Set (SpatialCoordinates d)),
    a x * vecDot ((uc k).grad x) ((uc k).grad x)
  refine integral_congr_ae ?_
  have hall : ∀ᵐ x ∂(volume.restrict (cell k : Set (SpatialCoordinates d))),
      ∀ i : Fin d, W.grad x i = (uc k).grad x i :=
    ae_all_iff.2 (fun i => hagree k i)
  filter_upwards [hall] with x hx
  congr 1
  simp only [vecDot]
  exact Finset.sum_congr rfl (fun i _ => by rw [hx i])

/-! ## The continuous glue -/

/-- **Gluing continuous cell representatives.**  Finitely many disjoint open
cells, each carrying a function continuous up to its closure with boundary
values `φ`, glue to one function continuous on the union of the closed cells.
A point of `closure (cell k)` lies in no other open cell, so the definition is
unambiguous, and on the frontier both descriptions give `φ`. -/
theorem lane2_exists_continuous_glue {ι : Type*} [Fintype ι]
    (cell : ι → Opens (SpatialCoordinates d))
    (hdisj : Pairwise (fun k l : ι =>
      Disjoint (cell k : Set (SpatialCoordinates d))
        (cell l : Set (SpatialCoordinates d))))
    (φ : SpatialCoordinates d → ℝ)
    (v : ι → SpatialCoordinates d → ℝ)
    (hv : ∀ k, ContinuousOn (v k)
      (closure (cell k : Set (SpatialCoordinates d))))
    (hvb : ∀ k, ∀ x ∈ frontier (cell k : Set (SpatialCoordinates d)),
      v k x = φ x) :
    ∃ F : SpatialCoordinates d → ℝ,
      ContinuousOn F (⋃ k : ι, closure (cell k : Set (SpatialCoordinates d))) ∧
      (∀ (k : ι), ∀ x ∈ (cell k : Set (SpatialCoordinates d)), F x = v k x) ∧
      (∀ x : SpatialCoordinates d,
        (∀ k : ι, x ∉ (cell k : Set (SpatialCoordinates d))) → F x = φ x) := by
  classical
  set F : SpatialCoordinates d → ℝ := fun x =>
    if h : ∃ k : ι, x ∈ (cell k : Set (SpatialCoordinates d))
      then v h.choose x else φ x with hF
  have huniq : ∀ (k j : ι), ∀ x : SpatialCoordinates d,
      x ∈ (cell k : Set (SpatialCoordinates d)) →
      x ∈ (cell j : Set (SpatialCoordinates d)) → j = k := by
    intro k j x hk hj
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hne) hj) hk
  have hcell : ∀ (k : ι), ∀ x ∈ (cell k : Set (SpatialCoordinates d)),
      F x = v k x := by
    intro k x hx
    have hex : ∃ j : ι, x ∈ (cell j : Set (SpatialCoordinates d)) := ⟨k, hx⟩
    rw [hF]
    simp only [dite_eq_left hex]
    rw [huniq k hex.choose x hx hex.choose_spec]
  have hout : ∀ x : SpatialCoordinates d,
      (∀ k : ι, x ∉ (cell k : Set (SpatialCoordinates d))) → F x = φ x := by
    intro x hx
    have hex : ¬ ∃ j : ι, x ∈ (cell j : Set (SpatialCoordinates d)) := by
      rintro ⟨j, hj⟩
      exact hx j hj
    rw [hF]
    simp only [dite_eq_right hex]
  refine ⟨F, ?_, hcell, hout⟩
  refine LocallyFinite.continuousOn_iUnion
    (locallyFinite_of_finite _) (fun k => isClosed_closure) (fun k => ?_)
  refine (hv k).congr (fun x hx => ?_)
  by_cases hin : ∃ j : ι, x ∈ (cell j : Set (SpatialCoordinates d))
  · obtain ⟨j, hj⟩ := hin
    have hjk : j = k := by
      by_contra hne
      have hopen : IsOpen (cell j : Set (SpatialCoordinates d)) :=
        (cell j).isOpen
      obtain ⟨y, hy1, hy2⟩ :=
        mem_closure_iff.mp hx _ hopen hj
      exact (Set.disjoint_left.mp (hdisj hne) hy1) hy2
    subst hjk
    exact hcell j x hj
  · push Not at hin
    have hfront : x ∈ frontier (cell k : Set (SpatialCoordinates d)) := by
      refine ⟨hx, ?_⟩
      rw [(cell k).isOpen.interior_eq]
      exact hin k
    rw [hout x hin, hvb k x hfront]

/-- Re-basing an `H¹` function on an almost-everywhere equal value function. -/
def lane2_H1ofAEEq {W : Set (SpatialCoordinates d)} (u : H1Function W)
    (v : SpatialCoordinates d → ℝ)
    (hv : v =ᵐ[volume.restrict W] u.toFun) : H1Function W where
  toFun := v
  grad := u.grad
  memL2 := u.memL2.ae_eq hv.symm
  gradMemL2 := u.gradMemL2
  hasWeakGradient := by
    intro i
    exact _root_.SubdiffusiveProcess.EllipticRegularity.hasWeakPartialDerivOn_congr_ae hv.symm
      (Filter.EventuallyEq.refl _ _) (u.hasWeakPartialDerivOn i)

/-- **Re-basing an `H¹₀` function.**  The value function may be replaced by any
almost-everywhere equal one, keeping the same approximants and gradient.  This
is what lets the glued datum CARRY its continuous representative, which the
mesh interpolant's continuity clause asserts of the function itself. -/
def lane2_H10ofAEEq {W : Set (SpatialCoordinates d)} (u : H10Function W)
    (v : SpatialCoordinates d → ℝ)
    (hv : v =ᵐ[volume.restrict W] u.toH1Function.toFun) : H10Function W where
  toH1Function := lane2_H1ofAEEq u.toH1Function v hv
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    refine u.tendsto_approx.congr (fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hv] with x hx
    show u.approx n x - u.toH1Function.toFun x = u.approx n x - v x
    rw [hx]
  tendsto_approx_grad := u.tendsto_approx_grad

/-- A smooth compactly supported `H¹` datum is killed: its Sobolev data are
those of the corresponding test function. -/
theorem lane2_sobolevDataOfH1_mem_killed_of_test
    {Q : Opens (SpatialCoordinates d)}
    (hQb : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (φ : H1Function (Q : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun)
    (hφsupp : HasCompactSupport φ.toFun)
    (hφQ : tsupport φ.toFun ⊆ (Q : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 φ ∈ killedSobolevGraph Q := by
  classical
  set ψ : 𝓓(Q, ℝ) := ⟨φ.toFun, hφ, hφsupp, hφQ⟩ with hψ
  have heq : sobolevDataOfH1 φ = smoothSobolevData ψ := by
    refine Prod.ext ?_ ?_
    · refine Lp.ext ?_
      refine (MemLp.coeFn_toLp φ.memL2).trans ?_
      exact (testL2_coeFn ψ).symm
    · funext i
      refine Lp.ext ?_
      refine (MemLp.coeFn_toLp (φ.gradMemL2 i)).trans ?_
      refine Filter.EventuallyEq.trans ?_ (testPartialL2_coeFn ψ i).symm
      exact lane2_grad_ae_eq_fderiv Q.isOpen hQb φ hφ i
  rw [heq]
  exact smoothSobolevData_mem_killed ψ

/-- Re-basing an `H¹` function on almost-everywhere equal value AND gradient.
The mesh interpolant's cellwise clauses are POINTWISE identities, so the
correction it exhibits must carry the glued datum's own value and gradient, not
merely a.e. equal ones. -/
def lane2_H1ofAEEq2 {W : Set (SpatialCoordinates d)} (u : H1Function W)
    (v : SpatialCoordinates d → ℝ) (g : SpatialCoordinates d → Homogenization.Vec d)
    (hv : v =ᵐ[volume.restrict W] u.toFun)
    (hg : ∀ i : Fin d,
      (fun x => g x i) =ᵐ[volume.restrict W] fun x => u.grad x i) :
    H1Function W where
  toFun := v
  grad := g
  memL2 := u.memL2.ae_eq hv.symm
  gradMemL2 := fun i => (u.gradMemL2 i).ae_eq (hg i).symm
  hasWeakGradient := by
    intro i
    exact _root_.SubdiffusiveProcess.EllipticRegularity.hasWeakPartialDerivOn_congr_ae hv.symm (hg i).symm
      (u.hasWeakPartialDerivOn i)

/-- Re-basing an `H¹₀` function on almost-everywhere equal value and
gradient. -/
def lane2_H10ofAEEq2 {W : Set (SpatialCoordinates d)} (u : H10Function W)
    (v : SpatialCoordinates d → ℝ) (g : SpatialCoordinates d → Homogenization.Vec d)
    (hv : v =ᵐ[volume.restrict W] u.toH1Function.toFun)
    (hg : ∀ i : Fin d,
      (fun x => g x i) =ᵐ[volume.restrict W] fun x => u.toH1Function.grad x i) :
    H10Function W where
  toH1Function := lane2_H1ofAEEq2 u.toH1Function v g hv hg
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    refine u.tendsto_approx.congr (fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hv] with x hx
    show u.approx n x - u.toH1Function.toFun x = u.approx n x - v x
    rw [hx]
  tendsto_approx_grad := by
    intro i
    refine (u.tendsto_approx_grad i).congr (fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hg i] with x hx
    show (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i
      = (fderiv ℝ (u.approx n) x) (basisVec i) - g x i
    rw [hx]

/-- The full gradient, not just its components, is almost everywhere
determined by the function. -/
theorem lane2_grad_ae_eq_of_ae_eq' {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (u v : H1Function W)
    (h : u.toFun =ᵐ[volume.restrict W] v.toFun) :
    u.grad =ᵐ[volume.restrict W] v.grad := by
  have hall : ∀ᵐ x ∂(volume.restrict W), ∀ i : Fin d, u.grad x i = v.grad x i := by
    rw [ae_all_iff]
    exact fun i => lane2_grad_ae_eq_of_ae_eq hW hWb u v h i
  filter_upwards [hall] with x hx
  exact funext hx

/-- Weak harmonicity depends on the gradient only through its class. -/
theorem lane2_isWeaklyHarmonicOn_congr_ae {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a : SpatialCoordinates d → ℝ} {u v : H1Function W}
    (h : u.grad =ᵐ[volume.restrict W] v.grad)
    (hu : IsWeaklyHarmonicOn a W u) : IsWeaklyHarmonicOn a W v := by
  intro χ
  refine Eq.trans ?_ (hu χ)
  refine setIntegral_congr_ae hW ?_
  filter_upwards [(ae_restrict_iff' hW).mp h] with x hx
  intro hxW
  rw [hx hxW]

/-- The energy depends on the gradient only through its class. -/
theorem lane2_energy_congr_ae {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a : SpatialCoordinates d → ℝ} {u v : H1Function W}
    (h : u.grad =ᵐ[volume.restrict W] v.grad) :
    energy a W u = energy a W v := by
  refine setIntegral_congr_ae hW ?_
  filter_upwards [(ae_restrict_iff' hW).mp h] with x hx
  intro hxW
  rw [hx hxW]

/-- A continuous function bounded almost everywhere on an open set is bounded
everywhere on it. -/
theorem lane2_le_of_ae_le_of_continuousOn {W : Set (SpatialCoordinates d)}
    (hW : IsOpen W) {f : SpatialCoordinates d → ℝ} {M : ℝ}
    (hf : ContinuousOn f W)
    (hae : ∀ᵐ x ∂(volume.restrict W), f x ≤ M) :
    ∀ x ∈ W, f x ≤ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0W, hx0⟩ := hcon
  obtain ⟨V, hVopen, hV⟩ := (continuousOn_iff'.mp hf) (Set.Ioi M) isOpen_Ioi
  have hset : {x | x ∈ W ∧ M < f x} = V ∩ W := by
    rw [← hV]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, mem_ofPred_eq]
    tauto
  have hopen : IsOpen {x | x ∈ W ∧ M < f x} := by
    rw [hset]; exact hVopen.inter hW
  have hne : {x | x ∈ W ∧ M < f x}.Nonempty := ⟨x0, hx0W, hx0⟩
  have hpos : 0 < volume {x | x ∈ W ∧ M < f x} := hopen.measure_pos volume hne
  have hnull : volume {x | x ∈ W ∧ M < f x} = 0 := by
    have h1 : ∀ᵐ x ∂volume, x ∈ W → f x ≤ M := (ae_restrict_iff' hW.measurableSet).mp hae
    have h2 : {x | x ∈ W ∧ M < f x} ⊆ {x | ¬ (x ∈ W → f x ≤ M)} := by
      rintro y ⟨hy, hy2⟩ hcontra
      exact absurd (hcontra hy) (not_le.mpr hy2)
    exact measure_mono_null h2 h1
  exact absurd hnull (ne_of_gt hpos)

end SubdiffusiveProcess
