import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecaySignedSharp
import SubdiffusiveProcess.Frozen.Section8.WholeSpaceDivergenceResolventSolution




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped CompactlySupported

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



noncomputable def wholeSpaceDecayH1FunctionOfAE {W : Set (Vec d)}
    (v : H1Function W) (u : Vec d → ℝ)
    (hvu : v.toFun =ᵐ[volume.restrict W] u) : H1Function W where
  toFun := u
  grad := v.grad
  memL2 := MemLp.ae_eq hvu v.memL2
  gradMemL2 := v.gradMemL2
  hasWeakGradient := by
    intro i phi hphi hcompact hsupport
    have hv := v.hasWeakGradient i phi hphi hcompact hsupport
    calc
      ∫ x in W, u x * (fderiv ℝ phi x) (basisVec i) ∂volume =
          ∫ x in W, v.toFun x * (fderiv ℝ phi x) (basisVec i) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hvu] with x hx
        rw [hx]
      _ = -∫ x in W, v.grad x i * phi x ∂volume := hv

@[simp] theorem wholeSpaceDecayH1FunctionOfAE_toFun {W : Set (Vec d)}
    (v : H1Function W) (u : Vec d → ℝ)
    (hvu : v.toFun =ᵐ[volume.restrict W] u) :
    (wholeSpaceDecayH1FunctionOfAE v u hvu).toFun = u :=
  rfl

@[simp] theorem wholeSpaceDecayH1FunctionOfAE_grad {W : Set (Vec d)}
    (v : H1Function W) (u : Vec d → ℝ)
    (hvu : v.toFun =ᵐ[volume.restrict W] u) :
    (wholeSpaceDecayH1FunctionOfAE v u hvu).grad = v.grad :=
  rfl

private theorem exists_nat_domain_subset_cube {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) :
    ∃ n : ℕ, W ⊆ cube d (n : ℤ) := by
  let R : ℝ := Classical.choose hW.isBoundedDomain
  have hRpos : 0 < R := (Classical.choose_spec hW.isBoundedDomain).1
  have hbound : ∀ x ∈ W, ∀ i, |x i| ≤ R :=
    (Classical.choose_spec hW.isBoundedDomain).2
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, fun x hx ↦ ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hi := abs_le.mp (hbound x hx i)
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> linarith only [hn, hRpos, hi.1, hi.2]

private theorem exists_nat_mem_cube (x : Vec d) :
    ∃ n : ℕ, x ∈ cube d (n : ℤ) := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (2 * ‖x‖) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hibounds := abs_le.mp hi
  rw [zpow_natCast]
  constructor <;> linarith only [hn, hibounds.1, hibounds.2]

/-- The first centered cube in the exhaustion containing a point. -/
noncomputable def wholeSpaceDecayCubeIndex (x : Vec d) : ℕ :=
  Nat.find (exists_nat_mem_cube x)

theorem mem_cube_wholeSpaceDecayCubeIndex (x : Vec d) :
    x ∈ cube d (wholeSpaceDecayCubeIndex x : ℤ) :=
  Nat.find_spec (exists_nat_mem_cube x)



theorem exists_globalGradient_of_forall_cube_local_solution [NeZero d]
    {a : Vec d → ℝ} {mu : ℝ} {f u : Vec d → ℝ}
    (hlocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
        (cube d (k : ℤ)) uLocal f) :
    ∃ grad : Vec d → Vec d,
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
          (cube d (k : ℤ)) uLocal f := by
  choose w hwValue hwSolution using hlocal
  let grad : Vec d → Vec d := fun x ↦
    (w (wholeSpaceDecayCubeIndex x)).grad x
  have hpair : ∀ k n : ℕ,
      (w k).grad =ᵐ[volume.restrict
        (cube d (k : ℤ) ∩ cube d (n : ℤ))] (w n).grad := by
    intro k n
    rcases le_total k n with hkn | hnk
    · have hsubset : cube d (k : ℤ) ⊆ cube d (n : ℤ) :=
        Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hkn)
      let wn : H1Function (cube d (k : ℤ)) :=
        (w n).restrict
          (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen
          hsubset
      have hmeasure : volume.restrict (cube d (k : ℤ)) ≤
          volume.restrict (cube d (n : ℤ)) :=
        Measure.restrict_mono hsubset le_rfl
      have hwnValue : wn.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u :=
        (hwValue n).filter_mono (ae_mono hmeasure)
      have hvalue : (w k).toFun =ᵐ[volume.restrict (cube d (k : ℤ))]
          wn.toFun := (hwValue k).trans hwnValue.symm
      have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
        (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen
        hvalue
      change (w k).grad =ᵐ[volume.restrict (cube d (k : ℤ))] (w n).grad at hgrad
      rw [inter_eq_left.mpr hsubset]
      exact hgrad
    · have hsubset : cube d (n : ℤ) ⊆ cube d (k : ℤ) :=
        Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hnk)
      let wk : H1Function (cube d (n : ℤ)) :=
        (w k).restrict
          (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen
          hsubset
      have hmeasure : volume.restrict (cube d (n : ℤ)) ≤
          volume.restrict (cube d (k : ℤ)) :=
        Measure.restrict_mono hsubset le_rfl
      have hwkValue : wk.toFun =ᵐ[volume.restrict (cube d (n : ℤ))] u :=
        (hwValue k).filter_mono (ae_mono hmeasure)
      have hvalue : wk.toFun =ᵐ[volume.restrict (cube d (n : ℤ))]
          (w n).toFun := hwkValue.trans (hwValue n).symm
      have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
        (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen
        hvalue
      change (w k).grad =ᵐ[volume.restrict (cube d (n : ℤ))] (w n).grad at hgrad
      rw [inter_eq_right.mpr hsubset]
      exact hgrad
  refine ⟨grad, fun k ↦ ⟨w k, hwValue k, ?_, hwSolution k⟩⟩
  have hpairGlobal : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ cube d (k : ℤ) ∩ cube d (n : ℤ) →
        (w k).grad x = (w n).grad x := by
    intro n
    exact (ae_restrict_iff'
      ((Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen.measurableSet.inter
        (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet)).1
      (hpair k n)
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      x ∈ cube d (k : ℤ) ∩ cube d (n : ℤ) →
        (w k).grad x = (w n).grad x :=
    ae_all_iff.mpr hpairGlobal
  apply (ae_restrict_iff'
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen.measurableSet).2
  filter_upwards [hall] with x hx
  intro hxk
  exact hx (wholeSpaceDecayCubeIndex x)
    ⟨hxk, mem_cube_wholeSpaceDecayCubeIndex x⟩



theorem exists_globalGradient_with_integrable_energy_of_cube_locals [NeZero d]
    {a : Vec d → ℝ} {mu C : ℝ} {f u : Vec d → ℝ}
    (B : MassiveCubeBounds a (fun _ ↦ (1 : ℝ)))
    (hlocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
        (cube d (k : ℤ)) uLocal f ∧
      (∫ x in cube d (k : ℤ),
        a x * vecNormSq (uLocal.grad x) ∂volume) ≤ C) :
    ∃ grad : Vec d → Vec d,
      Integrable (fun x ↦ a x * vecNormSq (grad x)) volume ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
          (cube d (k : ℤ)) uLocal f ∧
        (∫ x in cube d (k : ℤ),
          a x * vecNormSq (uLocal.grad x) ∂volume) ≤ C := by
  have hlocalSolution : ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
          (cube d (k : ℤ)) uLocal f := by
    intro k
    obtain ⟨uLocal, huValue, huSolution, _huEnergy⟩ := hlocal k
    exact ⟨uLocal, huValue, huSolution⟩
  obtain ⟨grad, hgradLocal⟩ :=
    exists_globalGradient_of_forall_cube_local_solution hlocalSolution
  have hlocalFull : ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
          (cube d (k : ℤ)) uLocal f ∧
        (∫ x in cube d (k : ℤ),
          a x * vecNormSq (uLocal.grad x) ∂volume) ≤ C := by
    intro k
    obtain ⟨uLocal, huValue, huGrad, huSolution⟩ := hgradLocal k
    obtain ⟨wLocal, hwValue, _hwSolution, hwEnergy⟩ := hlocal k
    have huWGrad : uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))]
        wLocal.grad :=
      Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
        (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
          (k : ℤ)).isOpen
        (huValue.trans hwValue.symm)
    refine ⟨uLocal, huValue, huGrad, huSolution, ?_⟩
    calc
      (∫ x in cube d (k : ℤ),
          a x * vecNormSq (uLocal.grad x) ∂volume) =
          ∫ x in cube d (k : ℤ),
            a x * vecNormSq (wLocal.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [huWGrad] with x hx
        rw [hx]
      _ ≤ C := hwEnergy
  let energy : Vec d → ℝ := fun x ↦ a x * vecNormSq (grad x)
  have henergyNonneg : ∀ x, 0 ≤ energy x := by
    intro x
    let k := wholeSpaceDecayCubeIndex x
    have ha : 0 ≤ a x :=
      (B.lam_pos k).le.trans
        (B.coeff_lower k x (mem_cube_wholeSpaceDecayCubeIndex x))
    exact mul_nonneg ha (vecNormSq_nonneg _)
  have hlocalIntegrable : ∀ k : ℕ,
      IntegrableOn energy (cube d (k : ℤ)) volume := by
    intro k
    obtain ⟨uLocal, _huValue, huGrad, _huSolution, _huEnergy⟩ := hlocalFull k
    have huInt := integrableOn_scalarCoeffEnergy (B.ell k) uLocal
    apply huInt.congr
    filter_upwards [huGrad] with x hx
    simp only [energy, hx]
  have hlocalIntegral : ∀ k : ℕ,
      (∫ x in cube d (k : ℤ), energy x ∂volume) ≤ C := by
    intro k
    obtain ⟨uLocal, _huValue, huGrad, _huSolution, huEnergy⟩ := hlocalFull k
    calc
      (∫ x in cube d (k : ℤ), energy x ∂volume) =
          ∫ x in cube d (k : ℤ),
            a x * vecNormSq (uLocal.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [huGrad] with x hx
        simp only [energy, hx]
      _ ≤ C := huEnergy
  have hcubeUnion : (⋃ k : ℕ, cube d (k : ℤ)) = Set.univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.2
      ⟨wholeSpaceDecayCubeIndex x, mem_cube_wholeSpaceDecayCubeIndex x⟩
  have henergyMeas : AEStronglyMeasurable energy volume := by
    have hmeas : AEStronglyMeasurable energy
        (volume.restrict (⋃ k : ℕ, cube d (k : ℤ))) :=
      AEStronglyMeasurable.iUnion fun k ↦ (hlocalIntegrable k).1
    simpa only [hcubeUnion, Measure.restrict_univ] using hmeas
  have hdirected : Directed (· ⊆ ·) (fun k : ℕ ↦ cube d (k : ℤ)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact Section6ExcessDecay.cube_subset_cube_of_le
        (by exact_mod_cast Nat.le_max_left i j)
    · exact Section6ExcessDecay.cube_subset_cube_of_le
        (by exact_mod_cast Nat.le_max_right i j)
  have hlocalLIntegral : ∀ k : ℕ,
      (∫⁻ x in cube d (k : ℤ), ‖energy x‖ₑ ∂volume) ≤
        ENNReal.ofReal C := by
    intro k
    have hInt := hlocalIntegrable k
    rw [← ofReal_integral_norm_eq_lintegral_enorm hInt]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ x in cube d (k : ℤ), ‖energy x‖ ∂volume) =
          ∫ x in cube d (k : ℤ), energy x ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change ‖energy x‖ = energy x
          rw [Real.norm_eq_abs, abs_of_nonneg (henergyNonneg x)]
      _ ≤ C := hlocalIntegral k
  have hfinite : HasFiniteIntegral energy volume := by
    change (∫⁻ x, ‖energy x‖ₑ ∂volume) < ⊤
    calc
      (∫⁻ x, ‖energy x‖ₑ ∂volume) =
          ∫⁻ x in ⋃ k : ℕ, cube d (k : ℤ), ‖energy x‖ₑ ∂volume := by
        rw [hcubeUnion, Measure.restrict_univ]
      _ = ⨆ k : ℕ,
          ∫⁻ x in cube d (k : ℤ), ‖energy x‖ₑ ∂volume :=
        setLIntegral_iUnion_of_directed _ hdirected
      _ ≤ ENNReal.ofReal C := iSup_le hlocalLIntegral
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨grad, ⟨henergyMeas, hfinite⟩, hlocalFull⟩



theorem exists_localDivergenceNormalizedMassiveWeakSolution_with_globalGradient
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, ∃ grad : Vec d → Vec d,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn (coefficientAt M L omega) (fun _ ↦ (1 : ℝ))
          mu (cube d (k : ℤ)) uLocal (fun x ↦ mu * f x) := by
  obtain ⟨u, huMem, huL2, huLocal⟩ :=
    exists_localDivergenceNormalizedMassiveWeakSolution_of_compactSupport_with_sharp_l2
      M L omega hmu f
  obtain ⟨grad, hgrad⟩ :=
    exists_globalGradient_of_forall_cube_local_solution huLocal
  exact ⟨u, grad, huMem, huL2, hgrad⟩



theorem exists_exact_localMassiveWeakSolutionOn_of_forall_cube [NeZero d]
    {a : Vec d → ℝ} {mu : ℝ} {f u : Vec d → ℝ}
    {grad : Vec d → Vec d}
    (hlocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
      uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu
        (cube d (k : ℤ)) uLocal f) :
    ∀ W : Set (Vec d), IsOpenBoundedConvexDomain W →
      ∃ uW : H1Function W,
        (∀ x ∈ W, uW.toFun x = u x) ∧
        uW.grad =ᵐ[volume.restrict W] grad ∧
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W uW f := by
  intro W hW
  obtain ⟨k, hWcube⟩ := exists_nat_domain_subset_cube hW
  obtain ⟨uLocal, huValue, huGrad, huSolution⟩ := hlocal k
  let v : H1Function W := uLocal.restrict hW.isOpen hWcube
  have hmeasure : volume.restrict W ≤ volume.restrict (cube d (k : ℤ)) :=
    Measure.restrict_mono hWcube le_rfl
  have hvValue : v.toFun =ᵐ[volume.restrict W] u :=
    huValue.filter_mono (ae_mono hmeasure)
  have hvGrad : v.grad =ᵐ[volume.restrict W] grad :=
    huGrad.filter_mono (ae_mono hmeasure)
  let uW : H1Function W := wholeSpaceDecayH1FunctionOfAE v u hvValue
  have hvSolution : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W v f :=
    huSolution.restrict hW.isOpen
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen
      hWcube
  have huWSolution :
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W uW f :=
    hvSolution.congr hvValue (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact ⟨uW, fun _ _ ↦ rfl, hvGrad, huWSolution⟩



noncomputable def wholeSpaceDivergenceResolventSolutionOfCubeLocals [NeZero d]
    (a : Vec d → ℝ) (t : ℝ) (f u : Vec d → ℝ)
    (grad : Vec d → Vec d)
    (hu : MemLp u 2 volume)
    (henergy : Integrable (fun x ↦ a x * vecNormSq (grad x)) volume)
    (hlocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
      uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
        (cube d (k : ℤ)) uLocal (fun x ↦ t⁻¹ * f x)) :
    WholeSpaceDivergenceResolventSolution a t f where
  toFun := u
  grad := grad
  memL2_toFun := hu
  integrable_energy := henergy
  locally_weak_solution :=
    exists_exact_localMassiveWeakSolutionOn_of_forall_cube hlocal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
