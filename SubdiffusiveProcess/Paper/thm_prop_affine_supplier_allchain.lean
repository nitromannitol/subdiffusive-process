module

public import SubdiffusiveProcess.Paper.prop_allchain

@[expose] public section

/-! Uniform-threshold form of `prop_allchain` (helper for the affine supplier of `thm_prop`).
The rate `A` is produced from `(d, H1, θ, b*)` alone, and the disorder threshold is an explicit
parameter `deltaW` of the witness supplier (instead of being produced after `fail`), so the chain
estimates for a whole countable family of failure events (all shifted mass grids and root cells)
hold below ONE threshold.  The proof is the proof of `SubdiffusiveProcess.Paper.prop_allchain` with the supplier
threshold made an input. -/

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem thm_prop_affine_supplier_allchain
    (d : ℕ) (_hd : 2 ≤ d) (H1 : ℕ) (hH1 : 0 < H1)
    (theta bstar : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < 1) (hbstar : 0 < bstar)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ A : ℝ, 0 < A ∧
    ∀ (fail : (M : _root_.SubdiffusiveProcess.Model.GMCModel d) →
        List (Fin d → Fin (3 ^ H1)) → Set (BilateralField d)),
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (word : List (Fin d → Fin (3 ^ H1))),
      MeasurableSet (fail M word)) →
    ∀ (deltaW : ℝ), 0 < deltaW →
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ deltaW →
        ∀ (word : List (Fin d → Fin (3 ^ H1))), 1 ≤ word.length →
          ∃ W : PNat → Set (BilateralField d),
            (∀ h : PNat,
              MeasurableSet[
                MeasurableSpace.comap
                  (fun omega : BilateralField d =>
                    fun j : Set.Icc
                        (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                        (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ)) =>
                      omega (-(j : ℤ)))
                  (inferInstance : MeasurableSpace
                    ((j : Set.Icc
                        (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                        (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]
                (W h)) ∧
            (∀ h : PNat,
              (chaosSampleLaw M).toMeasure (W h) ≤
                ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              omega ∈ fail M word → omega ∈ ⋃ h : PNat, W h)) →
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ deltaW →
      let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let badCount : (J : ℕ) → (Fin J → (Fin d → Fin (3 ^ H1))) → BilateralField d → ℕ :=
        fun J pi omega =>
          Set.ncard {i : Fin J |
            omega ∈ fail M ((List.ofFn pi).take (i.val + 1))}
      (∀ (J : ℕ), 1 ≤ J →
        P {omega |
            ∃ pi : Fin J → (Fin d → Fin (3 ^ H1)),
              theta * (J : ℝ) ≤ (badCount J pi omega : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ))))) ∧
      ∃ B : BilateralField d → ℝ, Measurable B ∧
        (∀ omega, 0 ≤ B omega) ∧
        (∀ᵐ omega ∂P, ∀ (J : ℕ) (pi : Fin J → (Fin d → Fin (3 ^ H1))), 1 ≤ J →
          badCount J pi omega ≤ theta * (J : ℝ) + B omega) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {omega | t < B omega} ≤
            ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ *
              Real.exp (-(bstar * t / (1 - theta))))) := by
  let L : ℕ := 3 ^ H1
  let Child := Fin d → Fin L
  let N : ℕ := Fintype.card Child
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hChild : Nonempty Child := by
    refine ⟨fun _ => ⟨0, hLpos⟩⟩
  have hNpos : 0 < N := by
    dsimp [N]
    exact Fintype.card_pos_iff.mpr hChild
  let c : ℝ := (N : ℝ)
  have hcpos : 0 < c := by
    dsimp [c]
    exact_mod_cast hNpos
  have hlogc : 0 ≤ Real.log c := by
    apply Real.log_nonneg
    dsimp [c]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let K : ℝ := bstar + Real.log c + Real.log 2 + 1
  have hK : 0 < K := by
    dsimp [K]
    nlinarith
  let A : ℝ := 2 * Real.log 2 + 1 + (24 / theta) * K
  have hA : 0 < A := by
    dsimp [A]
    have h24 : 0 < (24 : ℝ) / theta := div_pos (by norm_num) hθ0
    nlinarith
  have hAterm : A * theta / 24 =
      (2 * Real.log 2 + 1) * theta / 24 + K := by
    dsimp [A]
    field_simp [ne_of_gt hθ0]
  have hAhalf : -A / 2 ≤ -Real.log 2 := by
    dsimp [A]
    have h24 : 0 < (24 : ℝ) / theta := div_pos (by norm_num) hθ0
    nlinarith
  have hexphalf : Real.exp (-A / 2) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-A / 2) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr hAhalf
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hlograte : -Real.log 2 ≤ Real.log (1 - Real.exp (-A / 2)) := by
    have hsub : (1 / 2 : ℝ) ≤ 1 - Real.exp (-A / 2) := by
      linarith
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hsub
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hrate : bstar + Real.log c ≤
      A * theta / 24 + Real.log (1 - Real.exp (-A / 2)) := by
    rw [hAterm]
    dsimp [K]
    nlinarith
  refine ⟨A, hA, ?_⟩
  intro fail hfail deltaW hdeltaW hWall M hM
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let badCount : (J : ℕ) → (Fin J → Child) → BilateralField d → ℕ :=
    fun J pi omega =>
      Set.ncard {i : Fin J |
        omega ∈ fail M ((List.ofFn pi).take (i.val + 1))}
  change
    (∀ (J : ℕ), 1 ≤ J →
      P {omega |
          ∃ pi : Fin J → Child,
            theta * (J : ℝ) ≤ (badCount J pi omega : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ))))) ∧
      ∃ B : BilateralField d → ℝ, Measurable B ∧
        (∀ omega, 0 ≤ B omega) ∧
        (∀ᵐ omega ∂P, ∀ (J : ℕ) (pi : Fin J → Child), 1 ≤ J →
          badCount J pi omega ≤ theta * (J : ℝ) + B omega) ∧
        (∀ t : ℝ, 0 ≤ t →
          P {omega | t < B omega} ≤
            ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ *
              Real.exp (-(bstar * t / (1 - theta)))))
  let e : Child ≃ Fin N := Fintype.equivFin Child
  let badCountN : (J : ℕ) → (Fin J → Fin N) → BilateralField d → ℕ :=
    fun J pi omega => badCount J (fun i => e.symm (pi i)) omega
  have hleN : ∀ (K : ℕ) (pi : Fin K → Fin N) (omega),
      badCountN K pi omega ≤ K := by
    intro K pi omega
    dsimp [badCountN, badCount]
    simpa using
      (Set.ncard_le_card
        {i : Fin K |
          omega ∈ fail M ((List.ofFn (fun i => e.symm (pi i))).take (i.val + 1))})
  have hmeasN : ∀ (K : ℕ) (pi : Fin K → Fin N),
      Measurable (badCountN K pi) := by
    intro K pi
    apply measurable_ncard.comp
    apply measurable_set_iff.mpr
    intro i
    change Measurable (fun omega =>
      omega ∈ fail M ((List.ofFn (fun i => e.symm (pi i))).take (i.val + 1)))
    exact measurableSet_setOfPred.mp
      (hfail M ((List.ofFn (fun i => e.symm (pi i))).take (i.val + 1)))
  have hdevAll : ∀ (K : ℕ), 1 ≤ K →
      P {omega | ∃ b : Fin K → Child,
          theta * (K : ℝ) ≤
            (badCount K b omega : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(bstar * (K : ℝ)))) := by
    intro J hJ
    let g : ℤ → BilateralField d → C(SpatialCoordinates d, ℝ) :=
      fun j omega => omega j
    have hg_meas : ∀ j : ℤ, Measurable (g j) := by
      intro j
      exact measurable_pi_apply j
    have hg_indep : ProbabilityTheory.iIndepFun g P := by
      change ProbabilityTheory.iIndepFun
        (fun j (omega : ℤ → C(SpatialCoordinates d, ℝ)) => omega j)
        (Measure.infinitePi
          (fun j : ℤ =>
            (SubdiffusiveProcess.scaledLayerLaw d
              (SubdiffusiveProcess.chaosRootFieldLaw M) j :
              Measure C(SpatialCoordinates d, ℝ)))
          )
      exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
    let ns : (Fin J → Child) → Fin J → ℤ := fun _ i =>
      ((H1 * (i.val + 1) : ℕ) : ℤ)
    have hns : ∀ b : Fin J → Child, Function.Injective (ns b) := by
      intro b i k hik
      have hnat : H1 * (i.val + 1) = H1 * (k.val + 1) := by
        dsimp [ns] at hik
        exact_mod_cast hik
      have hsum : i.val + 1 = k.val + 1 := Nat.mul_left_cancel hH1 hnat
      exact Fin.ext (by omega)
    let Wword : List Child → PNat → Set (BilateralField d) := fun word =>
      if hword : 1 ≤ word.length then
        Classical.choose (hWall M hM word hword)
      else fun _ => ∅
    have hWspec : ∀ (word : List Child), 1 ≤ word.length →
        (∀ h : PNat,
          MeasurableSet[
            MeasurableSpace.comap
              (fun omega : BilateralField d =>
                fun j : Set.Icc
                    (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                    (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ)) =>
                  omega (-(j : ℤ)))
              (inferInstance : MeasurableSpace
                ((j : Set.Icc
                    (((H1 * word.length : ℕ) : ℤ) - (h : ℤ))
                    (((H1 * word.length : ℕ) : ℤ) + 2 * (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))]
            (Wword word h)) ∧
        (∀ h : PNat,
          P (Wword word h) ≤
            ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
        (∀ᵐ omega ∂P, omega ∈ fail M word →
          omega ∈ ⋃ h : PNat, Wword word h) := by
      intro word hword
      dsimp [Wword]
      rw [dite_eq_left hword]
      exact Classical.choose_spec (hWall M hM word hword)
    let W : (Fin J → Child) → Fin J → PNat → Set (BilateralField d) :=
      fun b i h => Wword ((List.ofFn b).take (i.val + 1)) h
    let failure : (Fin J → Child) → Fin J → Set (BilateralField d) :=
      fun b i =>
        fail M ((List.ofFn b).take (i.val + 1)) ∩
          ⋃ h : PNat, W b i h
    have hWmeas : ∀ (b : Fin J → Child) (i : Fin J) (h : PNat),
        @MeasurableSet (BilateralField d)
          (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc
            (ns b i - (h : ℤ)) (ns b i + 2 * (h : ℤ))),
            MeasurableSpace.comap (g (-j))
              (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)))
          (W b i h) := by
      intro b i h
      have htake : i.val + 1 ≤ (List.ofFn b).length := by
        simp
      have hword : 1 ≤ ((List.ofFn b).take (i.val + 1)).length := by
        rw [List.length_take_of_le htake]
        omega
      have hs := ((hWspec ((List.ofFn b).take (i.val + 1))
        hword).1 h)
      have hns_eq :
          ns b i = ((H1 * ((List.ofFn b).take (i.val + 1)).length : ℕ) : ℤ) := by
        dsimp [ns]
        rw [List.length_take_of_le htake]
        norm_num
      rw [hns_eq]
      dsimp [W]
      rw [← aux_prop_allchain_band]
      exact hs
    have hWprob : ∀ (b : Fin J → Child) (i : Fin J) (h : PNat),
        P (W b i h) ≤ ENNReal.ofReal (Real.exp (-A * (h : ℝ))) := by
      intro b i h
      have htake : i.val + 1 ≤ (List.ofFn b).length := by
        simp
      have hword : 1 ≤ ((List.ofFn b).take (i.val + 1)).length := by
        rw [List.length_take_of_le htake]
        omega
      dsimp [W]
      simpa [neg_mul] using (hWspec ((List.ofFn b).take (i.val + 1)) hword).2.1 h
    have hfailure : ∀ (b : Fin J → Child) (i : Fin J),
        failure b i ⊆ ⋃ h : PNat, W b i h := by
      intro b i omega hω
      exact hω.2
    have hbranch := SubdiffusiveProcess.union_bound_finitely_many_bad_branches
      (β := Fin J → Child) J A theta hA hθ0 hθ1
      (BilateralField d) C(SpatialCoordinates d, ℝ) P g hg_meas hg_indep ns hns
      failure W hWmeas hWprob hfailure
    have hae : ∀ᵐ omega ∂P, ∀ (b : Fin J → Child) (i : Fin J),
        omega ∈ fail M ((List.ofFn b).take (i.val + 1)) →
          omega ∈ ⋃ h : PNat, W b i h := by
      apply ae_all_iff.mpr
      intro b
      apply ae_all_iff.mpr
      intro i
      have htake : i.val + 1 ≤ (List.ofFn b).length := by
        simp
      have hword : 1 ≤ ((List.ofFn b).take (i.val + 1)).length := by
        rw [List.length_take_of_le htake]
        omega
      exact (hWspec ((List.ofFn b).take (i.val + 1)) hword).2.2
    have horigmod :
        {omega | ∃ b : Fin J → Child,
            theta * (J : ℝ) ≤
              (Set.ncard {i : Fin J |
                omega ∈ fail M ((List.ofFn b).take (i.val + 1))} : ℝ)} ≤ᵐ[P]
        {omega | ∃ b : Fin J → Child,
            theta * (J : ℝ) ≤
              (Set.ncard {i : Fin J | omega ∈ failure b i} : ℝ)} := by
      filter_upwards [hae] with omega hω
      rintro ⟨b, hb⟩
      refine ⟨b, hb.trans ?_⟩
      have hn :
          Set.ncard {i : Fin J |
            omega ∈ fail M ((List.ofFn b).take (i.val + 1))} ≤
          Set.ncard {i : Fin J | omega ∈ failure b i} := by
        apply Set.ncard_mono
        intro i hi
        exact ⟨hi, hω b i hi⟩
      exact_mod_cast hn
    have hchild :
        P {omega | ∃ b : Fin J → Child,
            theta * (J : ℝ) ≤
              (Set.ncard {i : Fin J |
                omega ∈ fail M ((List.ofFn b).take (i.val + 1))} : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ)))) := by
      calc
        P {omega | ∃ b : Fin J → Child,
            theta * (J : ℝ) ≤
              (Set.ncard {i : Fin J |
                omega ∈ fail M ((List.ofFn b).take (i.val + 1))} : ℝ)} ≤
            P {omega | ∃ b : Fin J → Child,
              theta * (J : ℝ) ≤
                (Set.ncard {i : Fin J | omega ∈ failure b i} : ℝ)} :=
          measure_mono_ae horigmod
        _ ≤ (Fintype.card (Fin J → Child) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              (-((A * theta / 24) + Real.log (1 - Real.exp (-A / 2))) *
                (J : ℝ))) := hbranch
        _ ≤ ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ)))) := by
          have hcard :
              (Fintype.card (Fin J → Child) : ℝ) =
                Real.exp (Real.log c * (J : ℝ)) := by
            calc
              (Fintype.card (Fin J → Child) : ℝ) = c ^ J := by
                simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
                rfl
              _ = (Real.exp (Real.log c)) ^ J := by
                rw [Real.exp_log hcpos]
              _ = Real.exp (Real.log c * (J : ℝ)) := by
                rw [← Real.exp_nat_mul]
                congr 1
                ring
          have hprod :
              (Fintype.card (Fin J → Child) : ℝ) *
                  Real.exp
                    (-((A * theta / 24) +
                      Real.log (1 - Real.exp (-A / 2))) * (J : ℝ)) ≤
                Real.exp (-(bstar * (J : ℝ))) := by
            rw [hcard, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hJ0 : 0 ≤ (J : ℝ) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hrate hJ0]
          rw [show (Fintype.card (Fin J → Child) : ℝ≥0∞) =
              ENNReal.ofReal (Fintype.card (Fin J → Child) : ℝ) by
                exact
                  (ENNReal.ofReal_natCast (Fintype.card (Fin J → Child))).symm]
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hprod
    simpa [badCount] using hchild
  have hdevNAll : ∀ (K : ℕ), 1 ≤ K →
      P {omega | ∃ pi : Fin K → Fin N,
          theta * (K : ℝ) ≤ badCountN K pi omega} ≤
        ENNReal.ofReal (Real.exp (-(bstar * (K : ℝ)))) := by
    intro K hK'
    have hchildN :
        {omega | ∃ b : Fin K → Child,
            theta * (K : ℝ) ≤ badCount K b omega} =
        {omega | ∃ pi : Fin K → Fin N,
            theta * (K : ℝ) ≤ badCountN K pi omega} := by
      ext omega
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨fun i => e (b i), ?_⟩
        simpa [badCountN] using hb
      · rintro ⟨pi, hpi⟩
        refine ⟨fun i => e.symm (pi i), ?_⟩
        simpa [badCountN] using hpi
    rw [← hchildN]
    exact hdevAll K hK'
  constructor
  · exact hdevAll
  · obtain ⟨B, hBmeas, hBnonneg, hBae, hBtail⟩ :=
      _root_.SubdiffusiveProcess.ResponseMoments.all_chain_estimate
        (BilateralField d) P N hNpos theta bstar hθ0 hθ1 hbstar
        badCountN hleN hmeasN hdevNAll
    refine ⟨B, hBmeas, hBnonneg, ?_, hBtail⟩
    filter_upwards [hBae] with omega hω K pi hK'
    simpa [badCountN] using hω K (fun i => e (pi i)) hK'

end SubdiffusiveProcess.Paper

