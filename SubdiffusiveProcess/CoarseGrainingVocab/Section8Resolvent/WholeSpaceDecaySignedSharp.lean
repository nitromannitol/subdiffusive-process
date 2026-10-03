module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayEnergy

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}



theorem exists_signedMassiveCubeLimit_with_l2_and_local [NeZero d]
    {c : Vec d → ℝ} (B : MassiveCubeBounds c (fun _ ↦ (1 : ℝ)))
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution c
          (fun _ ↦ (1 : ℝ)) mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Tendsto (fun n ↦ v n x) atTop (nhds (u x))) ∧
        MemLp u 2 volume ∧
        (mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn c (fun _ ↦ 1)
              mu (cube d (k : ℤ)) uLocal f := by
  let fPlus : C_c(Vec d, ℝ) := f.nnrealPart.toReal
  let fMinus : C_c(Vec d, ℝ) := (-f).nnrealPart.toReal
  have hfPlus : ∀ x, 0 ≤ fPlus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  have hfMinus : ∀ x, 0 ≤ fMinus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  obtain ⟨uCubePlus, vPlus, uPlus, hcontrolledPlus, hvEqPlus,
      _hvMonoPlus, _hvBoundsPlus, hvLimPlus⟩ :=
    exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport
      B hmu fPlus hfPlus
  obtain ⟨uCubeMinus, vMinus, uMinus, hcontrolledMinus, hvEqMinus,
      _hvMonoMinus, _hvBoundsMinus, hvLimMinus⟩ :=
    exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport
      B hmu fMinus hfMinus
  let uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)) :=
    fun n ↦ uCubePlus n - uCubeMinus n
  let v : ℕ → Vec d → ℝ := fun n ↦ vPlus n - vMinus n
  let u : Vec d → ℝ := uPlus - uMinus
  have hfDecomp : fPlus - fMinus = f := by
    simpa only [fPlus, fMinus] using
      (CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f)
  have hfDecompFun : (fPlus : Vec d → ℝ) - fMinus = f := by
    funext x
    exact congrArg (fun q : C_c(Vec d, ℝ) ↦ q x) hfDecomp
  have hfMem : MemLp (fun x : Vec d ↦ f x) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hcontrolled : ∀ n,
      IsControlledMassiveCubeSolution c
        (fun _ ↦ (1 : ℝ)) mu f n (uCube n) := by
    intro n
    let W := cube d (n : ℤ)
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hfLocal : MemL2On W f := hfMem.restrict W
    have hfPlusLocal : MemL2On W fPlus :=
      (fPlus.continuous.memLp_of_hasCompactSupport
        fPlus.hasCompactSupport).restrict W
    have hfMinusLocal : MemL2On W fMinus :=
      (fMinus.continuous.memLp_of_hasCompactSupport
        fMinus.hasCompactSupport).restrict W
    have hsolution : IsMassiveWeakSolutionOn c
        (fun _ ↦ (1 : ℝ)) mu W (uCube n).toH1Function f := by
      have hsub := (hcontrolledPlus n).1.sub (B.ell n)
        (B.rho_measurable n) (B.rho_bounded n)
        hfPlusLocal hfMinusLocal (hcontrolledMinus n).1
      simpa only [uCube, hfDecompFun] using! hsub
    refine ⟨hsolution, ?_, ?_, ?_⟩
    · exact massive_l2_contraction hW.isOpen.measurableSet hmu
        (B.rhoMin_pos n) (B.lam_pos n) (B.coeff_lower n)
        (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n)
        hfLocal hsolution
    · exact massive_energy_bound hW.isOpen.measurableSet hmu
        (B.rhoMin_pos n) (B.rho_measurable n) (B.rho_lower n)
        (B.rho_bounded n) hfLocal hsolution
    · have hk : 0 ≤ ‖compactSupportToC0 f‖ / mu :=
        div_nonneg (norm_nonneg _) hmu.le
      apply ae_abs_le_of_isMassiveWeakSolutionOn hW hmu hk
        (B.rhoMin_pos n) (B.lam_pos n) (B.coeff_lower n)
        (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n)
        hfLocal
      · intro x _hx
        have hpoint : |f x| ≤ ‖compactSupportToC0 f‖ := by
          simpa only [Real.norm_eq_abs, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ZeroAtInftyContinuousMap.toBCF_apply, compactSupportToC0_apply] using
            BoundedContinuousFunction.norm_coe_le_norm
              (ZeroAtInftyContinuousMap.toBCF (compactSupportToC0 f)) x
        convert hpoint using 1
        field_simp [hmu.ne']
      · exact hsolution
  have hvEq : ∀ n, v n =ᵐ[volume] (uCube n).zeroExtension := by
    intro n
    filter_upwards [hvEqPlus n, hvEqMinus n] with x hxPlus hxMinus
    rw [show v n x = vPlus n x - vMinus n x from rfl, hxPlus, hxMinus]
    by_cases hx : x ∈ cube d (n : ℤ)
    · rw [(uCubePlus n).zeroExtension_apply_of_mem hx,
        (uCubeMinus n).zeroExtension_apply_of_mem hx,
        (uCube n).zeroExtension_apply_of_mem hx]
      change (uCubePlus n).toH1Function.toFun x -
          (uCubeMinus n).toH1Function.toFun x =
        ((uCubePlus n).toH1Function -
          (uCubeMinus n).toH1Function).toFun x
      rw [H1Function.sub_toFun]
    · rw [(uCubePlus n).zeroExtension_apply_of_not_mem hx,
        (uCubeMinus n).zeroExtension_apply_of_not_mem hx,
        (uCube n).zeroExtension_apply_of_not_mem hx]
      exact sub_self 0
  have hvLim : ∀ x, Tendsto (fun n ↦ v n x) atTop (nhds (u x)) := by
    intro x
    exact (hvLimPlus x).sub (hvLimMinus x)
  have hL2 := memLp_two_and_massive_l2_contraction_of_pointwise_cube_limit
    hmu f uCube v u hcontrolled hvEq hvLim
  have hlocal := exists_localMassiveWeakSolutions_of_pointwise_cube_limit
    B hmu f uCube v u hcontrolled hvEq hvLim
  exact ⟨uCube, v, u, hcontrolled, hvEq, hvLim, hL2.1, hL2.2, hlocal⟩



theorem exists_localNormalizedMassiveWeakSolution_of_compactSupport_with_sharp_l2
    [NeZero d] {c : Vec d → ℝ}
    (B : MassiveCubeBounds c (fun _ ↦ (1 : ℝ)))
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn c (fun _ ↦ 1)
            mu (cube d (k : ℤ)) uLocal (fun x ↦ mu * f x) := by
  obtain ⟨_uCube, _v, u, _hcontrolled, _hvEq, _hvLim, huMem,
      huEnergy, huLocal⟩ :=
    exists_signedMassiveCubeLimit_with_l2_and_local
      B hmu (mu • f)
  have hforcingIntegral :
      ∫ x, (mu • f) x ^ 2 ∂volume = mu ^ 2 * ∫ x, f x ^ 2 ∂volume := by
    calc
      ∫ x, (mu • f) x ^ 2 ∂volume =
          ∫ x, mu ^ 2 * f x ^ 2 ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change (mu * f x) ^ 2 = mu ^ 2 * f x ^ 2
          ring
      _ = mu ^ 2 * ∫ x, f x ^ 2 ∂volume :=
        integral_const_mul (mu ^ 2) (fun x ↦ f x ^ 2)
  refine ⟨u, huMem, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hmu)).1
    calc
      mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤
          ∫ x, (mu • f) x ^ 2 ∂volume := huEnergy
      _ = mu ^ 2 * ∫ x, f x ^ 2 ∂volume := hforcingIntegral
  · intro k
    obtain ⟨uLocal, huAE, huSolution⟩ := huLocal k
    exact ⟨uLocal, huAE, by
      simpa only [Pi.smul_apply, smul_eq_mul] using! huSolution⟩



theorem exists_localNormalizedMassiveWeakSolution_with_sharp_l2_and_energy
    [NeZero d] {c : Vec d → ℝ}
    (B : MassiveCubeBounds c (fun _ ↦ (1 : ℝ)))
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c (fun _ ↦ 1)
          mu (cube d (k : ℤ)) uLocal (fun x ↦ mu * f x) ∧
        2 * mu * (∫ x in cube d (k : ℤ),
          c x * vecNormSq (uLocal.grad x) ∂volume) ≤
          mu ^ 2 * ∫ x, f x ^ 2 ∂volume := by
  obtain ⟨uCube, v, u, hcontrolled, hvEq, hvLim, huMem,
      huEnergy, _huLocal⟩ :=
    exists_signedMassiveCubeLimit_with_l2_and_local B hmu (mu • f)
  have hforcingIntegral :
      ∫ x, (mu • f) x ^ 2 ∂volume = mu ^ 2 * ∫ x, f x ^ 2 ∂volume := by
    calc
      ∫ x, (mu • f) x ^ 2 ∂volume =
          ∫ x, mu ^ 2 * f x ^ 2 ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change (mu * f x) ^ 2 = mu ^ 2 * f x ^ 2
          ring
      _ = mu ^ 2 * ∫ x, f x ^ 2 ∂volume :=
        integral_const_mul (mu ^ 2) (fun x ↦ f x ^ 2)
  have hlocal :=
    exists_localMassiveWeakSolutions_with_energy_of_pointwise_cube_limit
      B hmu (mu • f) uCube v u hcontrolled hvEq hvLim
  refine ⟨u, huMem, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hmu)).1
    calc
      mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤
          ∫ x, (mu • f) x ^ 2 ∂volume := huEnergy
      _ = mu ^ 2 * ∫ x, f x ^ 2 ∂volume := hforcingIntegral
  · intro k
    obtain ⟨uLocal, huAE, huSolution, huLocalEnergy⟩ := hlocal k
    refine ⟨uLocal, huAE, ?_, ?_⟩
    · simpa only [Pi.smul_apply, smul_eq_mul] using! huSolution
    · simpa only [hforcingIntegral] using! huLocalEnergy

/-- GMC divergence-form specialization of the generic sharp normalized
compact-data construction. -/
theorem exists_localDivergenceNormalizedMassiveWeakSolution_of_compactSupport_with_sharp_l2
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega) (fun _ ↦ 1)
            mu (cube d (k : ℤ)) uLocal (fun x ↦ mu * f x) :=
  exists_localNormalizedMassiveWeakSolution_of_compactSupport_with_sharp_l2
    (divergenceMassiveCubeBounds M L omega) hmu f

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
