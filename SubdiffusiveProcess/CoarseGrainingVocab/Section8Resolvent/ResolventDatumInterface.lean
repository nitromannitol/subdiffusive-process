import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumUniqueness
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ### A `C₀` datum is square integrable on every cube -/

/-- Every function vanishing at infinity is square integrable on a bounded
open convex domain. -/
theorem memL2On_of_zeroAtInfty {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (f : C₀(Vec d, ℝ)) : MemL2On W (fun x ↦ f x) := by
  haveI : IsFiniteMeasure (volume.restrict W) :=
    hW.isBoundedDomain.isFiniteMeasure_restrict_volume
  refine MemLp.of_bound (f.continuous.aestronglyMeasurable.restrict) ‖f‖ ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  simpa only [Real.norm_eq_abs] using
    (BoundedContinuousFunction.norm_coe_le_norm
      (ZeroAtInftyContinuousMap.toBCF f) x)

/-! ### The PDE obligations -/



structure MassiveC0Resolvent (c rho : Vec d → ℝ) where
  /-- The solution operator on data vanishing at infinity. -/
  sol : PositiveShift → C₀(Vec d, ℝ) → C₀(Vec d, ℝ)
  /-- The weak massive equation on every cube of the centred exhaustion. -/
  sol_local : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (k : ℕ),
    ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = sol mu f x) ∧
        IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) v (fun x ↦ f x)

namespace MassiveC0Resolvent

variable {c rho : Vec d → ℝ}

/-- Changing the forcing to an equal function keeps the weak equation. -/
theorem _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn.congr_forcing
    {W : Set (Vec d)} {mu : ℝ} {u : H1Function W} {f g : Vec d → ℝ} (h : f = g)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W u g := h ▸ hu

/-- **Changing the shift.**  A solution at shift `ν` solves the equation at any
other shift `μ` with the forcing corrected by `(μ − ν) u`. -/
theorem _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn.shiftMu
    {W : Set (Vec d)} {mu nu rhoMax : ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c rho nu W u f) :
    IsMassiveWeakSolutionOn c rho mu W u (fun x ↦ f x + (mu - nu) * u.toFun x) := by
  intro φ
  have hEq := hu φ
  have hmassU := integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 φ.toH1Function.memL2
  have hmassF := integrableOn_mass_term hrhoMeas hrhoBdd hf φ.toH1Function.memL2
  have hsplit :
      (∫ x in W, rho x * (f x + (mu - nu) * u.toFun x) *
          φ.toH1Function.toFun x ∂volume) =
        (∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume) +
          (mu - nu) * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul, ← integral_add hmassF (hmassU.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  rw [hsplit]
  linarith [hEq]

/-- **Uniqueness in the shape used below.**  A `C₀` function solving the
homogeneous massive equation on every centred cube vanishes. -/
theorem eq_zero_of_local (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 < mu)
    (h : C₀(Vec d, ℝ))
    (hloc : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = h x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ))) :
    h = 0 := by
  have hzero : ∀ x, h x = 0 := by
    refine eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
      h.continuous (zero_at_infty h) ?_
    intro k
    obtain ⟨v, hv, hvsol⟩ := hloc k
    exact ⟨v, Filter.Eventually.of_forall fun x ↦ hv x, hvsol⟩
  exact ZeroAtInftyContinuousMap.ext fun x ↦ by simpa using hzero x

/-- The local equations in the almost-everywhere shape used by the whole-space
maximum principle. -/
theorem sol_local_ae (R : MassiveC0Resolvent c rho) (mu : PositiveShift)
    (f : C₀(Vec d, ℝ)) (k : ℕ) :
    ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] (fun x ↦ R.sol mu f x) ∧
        IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) v
          (fun x ↦ f x) := by
  obtain ⟨v, hv, hvsol⟩ := R.sol_local mu f k
  exact ⟨v, Filter.Eventually.of_forall fun x ↦ hv x, hvsol⟩

/-- **Positivity of the whole-space resolvent**, derived from the maximum
principle rather than assumed. -/
theorem sol_nonneg (R : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) (x : Vec d) :
    0 ≤ R.sol mu f x := by
  refine forall_nonneg_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.2
    (R.sol mu f).continuous (zero_at_infty (R.sol mu f))
    (fun k ↦ memL2On_of_zeroAtInfty
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)) f)
    (R.sol_local_ae mu f) hf x

/-- **The sup-norm contraction** `μ ‖R_μ f‖_∞ ≤ ‖f‖_∞`, derived from the
maximum principle rather than assumed. -/
theorem norm_sol_le (R : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    ‖R.sol mu f‖ ≤ ((mu : ℝ))⁻¹ * ‖f‖ := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
  have hk0 : 0 ≤ ((mu : ℝ))⁻¹ * ‖f‖ :=
    mul_nonneg (inv_nonneg.2 hmu.le) (norm_nonneg _)
  have hbound : ∀ x, |f x| ≤ (mu : ℝ) * (((mu : ℝ))⁻¹ * ‖f‖) := by
    intro x
    have hpoint : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF f) x
    have : (mu : ℝ) * (((mu : ℝ))⁻¹ * ‖f‖) = ‖f‖ := by
      field_simp
    rw [this]
    exact hpoint
  have habs := forall_abs_le_of_localMassiveWeakSolution_of_tendsto_cocompact B
    hmu (R.sol mu f).continuous (zero_at_infty (R.sol mu f))
    (fun k ↦ memL2On_of_zeroAtInfty
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)) f)
    (R.sol_local_ae mu f) hk0 hbound
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hk0).2 fun x ↦ ?_
  simpa only [ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using habs x

/-- Additivity of the solution operator. -/
theorem sol_add (R : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu : PositiveShift) (f g : C₀(Vec d, ℝ)) :
    R.sol mu (f + g) = R.sol mu f + R.sol mu g := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
  have hkey : R.sol mu (f + g) - R.sol mu f - R.sol mu g = 0 := by
    refine eq_zero_of_local B hmu _ fun k ↦ ?_
    obtain ⟨v1, hv1, hv1sol⟩ := R.sol_local mu (f + g) k
    obtain ⟨v2, hv2, hv2sol⟩ := R.sol_local mu f k
    obtain ⟨v3, hv3, hv3sol⟩ := R.sol_local mu g k
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    have hs1 := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) (memL2On_of_zeroAtInfty hW (f + g))
      (memL2On_of_zeroAtInfty hW f) hv1sol hv2sol
    have hs2 := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k)
      (((memL2On_of_zeroAtInfty hW (f + g)).sub (memL2On_of_zeroAtInfty hW f)))
      (memL2On_of_zeroAtInfty hW g) hs1 hv3sol
    refine ⟨v1 - v2 - v3, fun x ↦ ?_,
      IsMassiveWeakSolutionOn.congr_forcing ?_ hs2⟩
    · simp only [H1Function.sub_toFun, hv1, hv2, hv3]
      rfl
    · funext x
      simp
  have := sub_eq_zero.mp (by simpa [sub_sub] using hkey)
  simpa using this

/-- Homogeneity of the solution operator. -/
theorem sol_smul (R : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu : PositiveShift) (r : ℝ) (f : C₀(Vec d, ℝ)) :
    R.sol mu (r • f) = r • R.sol mu f := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
  have hkey : R.sol mu (r • f) - r • R.sol mu f = 0 := by
    refine eq_zero_of_local B hmu _ fun k ↦ ?_
    obtain ⟨v1, hv1, hv1sol⟩ := R.sol_local mu (r • f) k
    obtain ⟨v2, hv2, hv2sol⟩ := R.sol_local mu f k
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    have hsmul := IsMassiveWeakSolutionOn.const_smul (u := v2) r hv2sol
    have hs := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) (memL2On_of_zeroAtInfty hW (r • f))
      ((memL2On_of_zeroAtInfty hW f).const_mul r) hv1sol hsmul
    refine ⟨v1 - r • v2, fun x ↦ ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hs⟩
    · have hL : (v1 - r • v2).toFun x = v1.toFun x - r * v2.toFun x := by
        simp [H1Function.sub_toFun, H1Function.smul_toFun]
      rw [hL, hv1, hv2]
      simp
    · funext x
      simp
  exact sub_eq_zero.mp hkey

/-- **The resolvent identity** `R_μ − R_ν = (ν − μ) R_μ R_ν`. -/
theorem sol_sub_sol (R : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu nu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    R.sol mu f - R.sol nu f =
      ((nu : ℝ) - (mu : ℝ)) • R.sol mu (R.sol nu f) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
  have hkey :
      (R.sol mu f - R.sol nu f) -
        ((nu : ℝ) - (mu : ℝ)) • R.sol mu (R.sol nu f) = 0 := by
    refine eq_zero_of_local B hmu _ fun k ↦ ?_
    obtain ⟨a, ha, hasol⟩ := R.sol_local mu f k
    obtain ⟨b, hb, hbsol⟩ := R.sol_local nu f k
    obtain ⟨e, he, hesol⟩ := R.sol_local mu (R.sol nu f) k
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    -- move the `ν` equation to the shift `μ`
    have hbmu := IsMassiveWeakSolutionOn.shiftMu (mu := (mu : ℝ))
      (B.rho_measurable k) (B.rho_bounded k) (memL2On_of_zeroAtInfty hW f) hbsol
    have hbL2 : MemL2On (cube d (k : ℤ))
        (fun x ↦ f x + ((mu : ℝ) - (nu : ℝ)) * b.toFun x) :=
      (memL2On_of_zeroAtInfty hW f).add (b.memL2.const_mul _)
    have hs1 := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) (memL2On_of_zeroAtInfty hW f) hbL2 hasol hbmu
    -- the composite term
    have hsmul := IsMassiveWeakSolutionOn.const_smul
      (u := e) ((nu : ℝ) - (mu : ℝ)) hesol
    have heL2 : MemL2On (cube d (k : ℤ))
        (fun x ↦ ((nu : ℝ) - (mu : ℝ)) * (R.sol nu f) x) :=
      (memL2On_of_zeroAtInfty hW (R.sol nu f)).const_mul _
    have hs2 := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k)
      ((memL2On_of_zeroAtInfty hW f).sub hbL2) heL2 hs1 hsmul
    refine ⟨(a - b) - ((nu : ℝ) - (mu : ℝ)) • e, fun x ↦ ?_,
      IsMassiveWeakSolutionOn.congr_forcing ?_ hs2⟩
    · have hL : ((a - b) - ((nu : ℝ) - (mu : ℝ)) • e).toFun x =
          (a.toFun x - b.toFun x) - ((nu : ℝ) - (mu : ℝ)) * e.toFun x := by
        simp [H1Function.sub_toFun, H1Function.smul_toFun]
      rw [hL, ha, hb, he]
      simp
    · funext x
      show (f x - (f x + ((mu : ℝ) - (nu : ℝ)) * b.toFun x)) -
        ((nu : ℝ) - (mu : ℝ)) * (R.sol nu f) x = 0
      rw [hb]
      ring
  exact sub_eq_zero.mp hkey

/-- **The whole-space solution operator is canonical.**  Any two whole-space
massive solution operators for the same pair agree; the operator is not a
choice. -/
theorem sol_eq (R R' : MassiveC0Resolvent c rho) (B : MassiveCubeBounds c rho)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    R.sol mu f = R'.sol mu f := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
  have hkey : R.sol mu f - R'.sol mu f = 0 := by
    refine eq_zero_of_local B hmu _ fun k ↦ ?_
    obtain ⟨v, hv, hvsol⟩ := R.sol_local mu f k
    obtain ⟨v', hv', hv'sol⟩ := R'.sol_local mu f k
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    have hs := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) (memL2On_of_zeroAtInfty hW f)
      (memL2On_of_zeroAtInfty hW f) hvsol hv'sol
    refine ⟨v - v', fun x ↦ ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hs⟩
    · simp only [H1Function.sub_toFun, hv, hv']
      rfl
    · funext x
      simp
  exact sub_eq_zero.mp hkey

/-- **The packaged `C₀` resolvent datum.** -/
def toC0ResolventDatum (R : MassiveC0Resolvent c rho)
    (B : MassiveCubeBounds c rho) : C0ResolventDatum (Vec d) where
  solution := R.sol
  solution_add := R.sol_add B
  solution_smul := R.sol_smul B
  solution_nonneg := fun mu f hf x ↦ R.sol_nonneg B mu f hf x
  norm_solution_le := R.norm_sol_le B
  solution_sub_solution := R.sol_sub_sol B

@[simp]
theorem toC0ResolventDatum_solution (R : MassiveC0Resolvent c rho)
    (B : MassiveCubeBounds c rho) (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    (R.toC0ResolventDatum B).solution mu f = R.sol mu f := rfl

/-- **The weak elliptic characterization.**  On every bounded open convex
domain the value function `R_μ f` is the value function of an `H¹` solution of
the massive equation. -/
theorem isWeakEllipticResolvent (R : MassiveC0Resolvent c rho)
    (B : MassiveCubeBounds c rho) :
    IsWeakEllipticResolvent c rho (R.toC0ResolventDatum B) := by
  intro mu f W hW
  obtain ⟨k, hk⟩ := exists_nat_cube_superset hW.isBoundedDomain.isBounded
  obtain ⟨v, hv, hvsol⟩ := R.sol_local mu f k
  refine ⟨v.restrict hW.isOpen hk, fun x _ ↦ hv x, ?_⟩
  exact IsMassiveWeakSolutionOn.restrict hW.isOpen
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen hk hvsol

/-- **Dense range** from the usual strong convergence `μ R_μ f → f`. -/
theorem denseRange_operator (R : MassiveC0Resolvent c rho)
    (B : MassiveCubeBounds c rho)
    (hstrong : ∀ f : C₀(Vec d, ℝ),
      Tendsto (fun mu : PositiveShift ↦ (mu : ℝ) • R.sol mu f) atTop (nhds f))
    (mu : PositiveShift) :
    DenseRange ((R.toC0ResolventDatum B).operator mu) := by
  refine C0ResolventDatum.denseRange_of_tendsto_smul_solution
    (D := R.toC0ResolventDatum B) (S := Set.univ) dense_univ ?_ mu
  intro f _
  simpa using hstrong f

end MassiveC0Resolvent

/-! ### The obligation as a single proposition -/



def HasC0MassiveSolutions (c rho : Vec d → ℝ) : Prop :=
  ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), ∃ g : C₀(Vec d, ℝ),
    ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g x) ∧
        IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) v (fun x ↦ f x)

/-- The whole-space solution operator produced by the obligation. -/
noncomputable def MassiveC0Resolvent.ofHasC0MassiveSolutions
    {c rho : Vec d → ℝ} (h : HasC0MassiveSolutions c rho) :
    MassiveC0Resolvent c rho where
  sol := fun mu f ↦ (h mu f).choose
  sol_local := fun mu f k ↦ (h mu f).choose_spec k

/-- **The dense-range obligation.**  The normalised resolvent converges
strongly as the shift grows.  By `MassiveC0Resolvent.sol_eq` this does not
depend on which solution operator is used. -/
def HasStrongMassiveResolventLimit (c rho : Vec d → ℝ) : Prop :=
  ∀ (R : MassiveC0Resolvent c rho) (f : C₀(Vec d, ℝ)),
    Tendsto (fun mu : PositiveShift ↦ (mu : ℝ) • R.sol mu f) atTop (nhds f)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
