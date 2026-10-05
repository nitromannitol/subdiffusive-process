module

public import SubdiffusiveProcess.Paper.lem_prefix_limit
public import SubdiffusiveProcess.Paper.prefix_physical_tail
public import SubdiffusiveProcess.Analysis.GuardedPrefixSums
public import SubdiffusiveProcess.Probability.PrefixMeshBounds
public import SubdiffusiveProcess.Probability.BufferedPrefixRate

@[expose] public section

/-! Limiting original-field prefixes retain exponential tails. This composes
the specified prefix-limit and physical-tail suppliers, including the buffer
and both the bad-scale and accumulated-error scores. It does not assert a
uniform finite-cutoff transfer on a growing mesh.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A guarded physical prefix equals the translated prefix used by the limit supplier. -/
theorem aux_lem_as_regularity_limit_prefix_sum
    {d : ℕ} (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (N buffer D : ℕ) (level : ℤ) (w : SpatialCoordinates d)
    (useD : Bool) (omega : BilateralField d) :
    (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer),
      if level + j ≤ (N : ℤ) then
        if useD then (Draw N ((N : ℤ) - (level + j)).toNat
          ((3 : ℝ) ^ N • w) omega).toReal
        else Z N ((N : ℤ) - (level + j)).toNat ((3 : ℝ) ^ N • w) omega
      else 0) =
      aux_prefix_physical_tail_sum N level.toNat buffer D (-level).toNat w Z Draw
        useD omega := by
  let f : ℤ → ℝ := fun j => if j ≤ (N : ℤ) then
    if useD then (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega).toReal
    else Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega
    else 0
  have hz j (hj : (N : ℤ) < j) : f j = 0 := ite_eq_right (not_le_of_gt hj)
  have heq : (level.toNat : ℤ) - ((-level).toNat : ℤ) = level := by omega
  change (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), f (level + j)) = _
  rw [sum_Icc_translate]
  rw [← sum_Icc_min_of_eq_zero_above _ _ (N : ℤ) f hz]
  simp only [aux_prefix_physical_tail_sum, heq, sub_eq_add_neg, add_assoc]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f]
  simp only [sub_eq_add_neg, show (0 ≤ (N : ℤ) + -j) ↔ j ≤ (N : ℤ) by omega]

/-- Physical exponential prefix bounds pass to one jointly extracted limiting score bank. -/
theorem lem_as_regularity_limit_prefix
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pc : in_poincare d hd I) (Xc : in_extension d hd I)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (Dinput : lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s eps lam A : ℝ) (buffer : ℕ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) (hA : 0 < A) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      ∀ eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d,
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : SpatialCoordinates d),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        primitive_scores d M s eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (Pos : Type) [Countable Pos] (level : Pos → ℤ)
        (centre : Pos → SpatialCoordinates d),
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ Vlim : Pos → ℤ → Bool → BilateralField d → ℝ,
        (∀ pos j useD, AEStronglyMeasurable (Vlim pos j useD)
          (chaosSampleLaw M).toMeasure) ∧
        (∀ pos j useD,
          Tendsto (fun n => eLpNorm (fun omega =>
            (if level pos + j ≤ (psi n : ℤ) then
              if useD then (Draw (psi n) ((psi n : ℤ) - (level pos + j)).toNat
                ((3 : ℝ) ^ (psi n) • centre pos) omega).toReal
              else Z (psi n) ((psi n : ℤ) - (level pos + j)).toNat
                ((3 : ℝ) ^ (psi n) • centre pos) omega
            else 0) - Vlim pos j useD omega) 1 (chaosSampleLaw M).toMeasure)
            atTop (𝓝 0)) ∧
        (∀ pos (D : ℕ), 1 ≤ D → ∀ useD,
          (chaosSampleLaw M).toMeasure {omega | lam * (D : ℝ) / 2 <
            ∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer),
              Vlim pos j useD omega} ≤ ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) ∧
        (∀ (k : ℕ → ℕ) (g b : ℕ) (Ccount xi : ℝ), 0 ≤ Ccount → 0 < xi →
          (g : ℝ) * Real.log 3 < A * xi →
          (∀ n : ℕ, (k n : ℝ) ≤
            Ccount * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((g : ℝ) * n)) →
          ∀ entry : ∀ n : ℕ, Fin (k n) → Pos,
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B0 : ℝ, 0 < B0 ∧
            ∀ (n : ℕ) (i : Fin (k n)) (D : ℕ), xi * (n : ℝ) + B0 ≤ (D : ℝ) →
              ∀ useD, (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer),
                Vlim (entry n i) j useD omega) ≤ lam * (D : ℝ) / 2) := by
  obtain ⟨q, dl, K, hq, hmom, hdim, hdl, hK, hlimit⟩ :=
    lem_prefix_limit d hd I Pc Xc W Sf Dinput Cresp hCresp s s eps hs hs heps
      0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) ∅ (by
        intro p hp
        exact (Finset.notMem_empty p hp).elim)
  have hrate : 0 < A * ((buffer : ℝ) + 1) + Real.log 2 := by
    have hb : 0 < (buffer : ℝ) + 1 := by positivity
    exact add_pos_of_pos_of_nonneg (mul_pos hA hb) (Real.log_nonneg (by norm_num))
  obtain ⟨dt, hdt, htail⟩ := prefix_physical_tail d s eps lam
    (A * ((buffer : ℝ) + 1) + Real.log 2) buffer hs heps hlam hrate
  refine ⟨min dl dt, lt_min hdl hdt, ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim
    Pos hPos level centre
  have hL := (hlimit M (hM.trans (min_le_left _ _)) Rm hRm Sreg It H hH
    eta hEta F Praw Rraw Draw Z rawGood hPrim (fun n => by positivity)).2.2
  obtain ⟨psi, hpsi, V, hVm, hVmom, hVNmom, hconv, hprefix⟩ :=
    hL Pos level centre id strictMono_id
  let test : Bool → Fin 5 := fun useD => if useD then 3 else 4
  let Vlim : Pos → ℤ → Bool → BilateralField d → ℝ :=
    fun pos j useD => V pos j (Sum.inl (test useD))
  have htailLim : ∀ pos (D : ℕ), 1 ≤ D → ∀ useD,
      (chaosSampleLaw M).toMeasure {omega | lam * (D : ℝ) / 2 <
        ∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), Vlim pos j useD omega} ≤
        ENNReal.ofReal (Real.exp (-(A * (D : ℝ)))) := by
    intro pos D hD useD
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
    have hp := (hprefix pos 0 (D + buffer) buffer (Sum.inl (test useD))).2.2
      A (lam * (D : ℝ) / 4) (lam * (D : ℝ) / 2) hA
      (by nlinarith only [mul_pos hlam hDpos])
    have ht N := (htail M (hM.trans (min_le_right _ _)) eta hEta F Praw Rraw Draw Z rawGood
      hPrim N (level pos).toNat D hD (-(level pos)).toNat (centre pos) useD).1
    have hbound : ∀ N,
        (chaosSampleLaw M).toMeasure {omega | lam * (D : ℝ) / 4 <
          aux_prefix_physical_tail_sum N (level pos).toNat buffer D
            (-(level pos)).toNat (centre pos) Z Draw useD omega} ≤
        ENNReal.ofReal (Real.exp (-(A * ((D : ℝ) + buffer)))) := fun N =>
      (ht N).trans (ENNReal.ofReal_le_ofReal
        (buffered_prefix_tail_le A hA buffer D hD))
    have hp' := hp (by
      intro N
      convert hbound N using 1
      · congr 1
        ext omega
        have heq := aux_lem_as_regularity_limit_prefix_sum Z Draw N buffer D
          (level pos) (centre pos) useD omega
        simp only [Function.id_def, zero_sub, zero_add, Nat.cast_add, mem_ofPred_eq]
        cases useD <;>
          exact iff_of_eq (congrArg (fun v : ℝ => lam * (D : ℝ) / 4 < v) heq)
      · rw [Nat.cast_add])
    refine (show (chaosSampleLaw M).toMeasure {omega | lam * (D : ℝ) / 2 <
        ∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), Vlim pos j useD omega} ≤
        ENNReal.ofReal (Real.exp (-(A * ((D : ℝ) + buffer)))) from ?_).trans ?_
    · simpa only [Vlim, zero_sub, zero_add, Nat.cast_add] using hp'
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hA.le (Nat.cast_nonneg (α := ℝ) buffer)]
  refine ⟨psi, hpsi, Vlim, fun pos j useD => hVm pos j (Sum.inl (test useD)),
    ?_, htailLim, ?_⟩
  · intro pos j useD
    have hc := hconv 1 (Finset.mem_insert_self 1 ∅) pos j (Sum.inl (test useD))
    cases useD <;>
      simpa only [Vlim, test, Bool.false_eq_true, ↓reduceIte, Sum.elim_inl,
        Function.id_def, ENNReal.ofReal_one] using! hc
  · intro k g b Ccount xi hCcount hxi hrate hcard entry
    have hmesh := ae_prefix_bound_on_mesh (chaosSampleLaw M).toMeasure k g b Ccount
      1 A xi (lam / 2) hCcount zero_le_one hA hxi hrate hcard entry
      (fun pos tag m omega => ∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((m : ℤ) + buffer),
        Vlim pos j tag omega) (fun pos m hm tag => by
          simpa only [div_mul_eq_mul_div, one_mul, neg_mul] using htailLim pos m hm tag)
    simpa only [div_mul_eq_mul_div] using hmesh

end SubdiffusiveProcess.Paper
