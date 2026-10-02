import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingGain




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## The length-free chain sum -/

/-- The total weight of all admissible chains from `c`, with no length bound. -/
def chainSumAll (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (gb : ℕ) (c : CrossCell d) :
    ℝ≥0∞ :=
  ∑' L : List (CrossCell d),
    if L.IsChain (cellReach Cbox Cdep J) ∧
        (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb then
      (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0

theorem chainSumAll_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ)
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob cprob q ≤ 2 * crossBranch d J)
    (gb : ℕ) (c : CrossCell d) :
    chainSumAll Cbox Cdep J Cprob cprob q gb c ≤
      2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
        (4 * crossBranch d J) ^ gb := by
  classical
  rw [chainSumAll, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set n : ℕ := s.sup List.length with hn
  have hterm : ∀ L ∈ s,
      (if L.IsChain (cellReach Cbox Cdep J) ∧
          (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb then
        (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) ≤
      (if AdmissibleChain Cbox Cdep J n gb c L then
        (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) := by
    intro L hL
    by_cases hc : L.IsChain (cellReach Cbox Cdep J) ∧
        (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb
    · rw [if_pos hc, if_pos ⟨Finset.le_sup hL, hc.1, hc.2.1, hc.2.2⟩]
    · rw [if_neg hc]
      exact zero_le _
  calc (∑ L ∈ s, if L.IsChain (cellReach Cbox Cdep J) ∧
        (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb then
        (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0)
      ≤ ∑ L ∈ s, (if AdmissibleChain Cbox Cdep J n gb c L then
          (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑' L : List (CrossCell d), (if AdmissibleChain Cbox Cdep J n gb c L then
          (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) :=
        ENNReal.sum_le_tsum s
    _ ≤ 2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
          (4 * crossBranch d J) ^ gb := chainSum_le Cbox Cdep J Cprob cprob q hpi n gb c

/-! ## The start of a certificate -/

theorem tsum_start_le (Cbox Cdep : ℕ) (Cprob cprob q : ℝ) (z : Lattice d) (l : ℕ)
    (K : ℝ≥0∞) :
    (∑' c : CrossCell d,
      (if 3 * latticeDist z (cellCenter Cdep c) ≤ l + 3 * cellRadius Cbox Cdep c then
        cellWeight d Cdep Cprob cprob q c *
          (K * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞))
      else 0)) ≤
      (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
        (1 + crossScaleSum d Cbox Cdep Cprob cprob q) := by
  classical
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  -- the good-vertex starts
  have hgood : (∑' v : Lattice d,
      (if 3 * latticeDist z (cellCenter Cdep (Sum.inr v)) ≤
          l + 3 * cellRadius Cbox Cdep (Sum.inr v) then
        cellWeight d Cdep Cprob cprob q (Sum.inr v) *
          (K * (((cellRadius Cbox Cdep (Sum.inr v) + 1) ^ d : ℕ) : ℝ≥0∞))
      else 0)) ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K := by
    have hcongr : ∀ v : Lattice d,
        (if 3 * latticeDist z (cellCenter Cdep (Sum.inr v)) ≤
            l + 3 * cellRadius Cbox Cdep (Sum.inr v) then
          cellWeight d Cdep Cprob cprob q (Sum.inr v) *
            (K * (((cellRadius Cbox Cdep (Sum.inr v) + 1) ^ d : ℕ) : ℝ≥0∞))
        else 0) ≤ (if latticeDist z (id v) ≤ l then K else 0) := by
      intro v
      by_cases h : 3 * latticeDist z v ≤ l + 3 * 0
      · rw [if_pos (by simpa [cellCenter, cellRadius] using h),
          if_pos (by simp only [id]; omega)]
        simp [cellWeight, cellRadius]
      · rw [if_neg (by simpa [cellCenter, cellRadius] using h)]
        exact zero_le _
    refine (ENNReal.tsum_le_tsum hcongr).trans ?_
    refine (tsum_ite_ball_le z l K id Function.injective_id).trans ?_
    refine mul_le_mul' ?_ le_rfl
    have hnat : (2 * l + 1) ^ d ≤ 2 ^ d * (l + 1) ^ d := by
      have hbase : 2 * l + 1 ≤ 2 * (l + 1) := by omega
      calc (2 * l + 1) ^ d ≤ (2 * (l + 1)) ^ d := Nat.pow_le_pow_left hbase d
        _ = 2 ^ d * (l + 1) ^ d := by rw [mul_pow]
    exact_mod_cast hnat
  -- the event-cell starts
  have hevent : (∑' p : ℕ × Lattice d,
      (if 3 * latticeDist z (cellCenter Cdep (Sum.inl p)) ≤
          l + 3 * cellRadius Cbox Cdep (Sum.inl p) then
        cellWeight d Cdep Cprob cprob q (Sum.inl p) *
          (K * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞))
      else 0)) ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
        crossScaleSum d Cbox Cdep Cprob cprob q := by
    have hinner : ∀ j : ℕ,
        (∑' a : Lattice d,
          (if 3 * latticeDist z (cellCenter Cdep (Sum.inl (j, a))) ≤
              l + 3 * cellRadius Cbox Cdep (Sum.inl (j, a)) then
            cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
              (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
          else 0)) ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
            (((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) *
              cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))) := by
      intro j
      set rho : ℕ := (Cbox + Cdep) * 3 ^ j with hrho
      set wj : ℝ≥0∞ := cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))
        with hwj
      set W : ℝ≥0∞ := wj * (K * (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) with hW
      have hcongr : ∀ a : Lattice d,
          (if 3 * latticeDist z (cellCenter Cdep (Sum.inl (j, a))) ≤
              l + 3 * cellRadius Cbox Cdep (Sum.inl (j, a)) then
            cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
              (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
          else 0) ≤
          (if latticeDist z (crossGrid Cdep j a) ≤ l + rho then W else 0) := by
        intro a
        by_cases h : 3 * latticeDist z (crossGrid Cdep j a) ≤ l + 3 * rho
        · rw [if_pos (by simpa [cellCenter, cellRadius, hrho] using h),
            if_pos (by omega)]
          rw [hW, hwj]
          rfl
        · rw [if_neg (by simpa [cellCenter, cellRadius, hrho] using h)]
          exact zero_le _
      refine (ENNReal.tsum_le_tsum hcongr).trans ?_
      refine (tsum_ite_ball_le z (l + rho) W (crossGrid Cdep j)
        (crossGrid_injective Cdep j)).trans ?_
      have hcount : (((2 * (l + rho) + 1) ^ d : ℕ) : ℝ≥0∞) ≤
          (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * (((rho + 1) ^ d : ℕ) : ℝ≥0∞) := by
        have hbase : 2 * (l + rho) + 1 ≤ 2 * (l + 1) * (rho + 1) := by nlinarith
        have hnat : (2 * (l + rho) + 1) ^ d ≤ 2 ^ d * (l + 1) ^ d * (rho + 1) ^ d := by
          calc (2 * (l + rho) + 1) ^ d ≤ (2 * (l + 1) * (rho + 1)) ^ d :=
                Nat.pow_le_pow_left hbase d
            _ = 2 ^ d * (l + 1) ^ d * (rho + 1) ^ d := by rw [mul_pow, mul_pow]
        exact_mod_cast hnat
      have hsq : ((((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * ((((rho + 1) ^ d : ℕ) : ℝ≥0∞)) =
          (((rho + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_mul, ← pow_add]
        congr 2
        ring
      calc (((2 * (l + rho) + 1) ^ d : ℕ) : ℝ≥0∞) * W
          ≤ ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
              (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * W := mul_le_mul' hcount le_rfl
        _ = (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
              (((((rho + 1) ^ d : ℕ) : ℝ≥0∞) * (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * wj) := by
            rw [hW]; ring
        _ = (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
              ((((rho + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) * wj) := by rw [hsq]
    calc (∑' p : ℕ × Lattice d, _)
        = ∑' (j : ℕ) (a : Lattice d),
            (if 3 * latticeDist z (cellCenter Cdep (Sum.inl (j, a))) ≤
                l + 3 * cellRadius Cbox Cdep (Sum.inl (j, a)) then
              cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
                (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
            else 0) := ENNReal.tsum_prod'
      _ ≤ ∑' j : ℕ, (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
            (((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) *
              cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))) :=
          ENNReal.tsum_le_tsum hinner
      _ = (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
            crossScaleSum d Cbox Cdep Cprob cprob q := by
          rw [ENNReal.tsum_mul_left, crossScaleSum]
  calc (∑' p : ℕ × Lattice d, _) + (∑' v : Lattice d, _)
      ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
          crossScaleSum d Cbox Cdep Cprob cprob q +
        (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K := add_le_add hevent hgood
    _ = (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
          (1 + crossScaleSum d Cbox Cdep Cprob cprob q) := by ring

/-! ## The total weight of all certificates -/

theorem tsum_crossChain_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (z : Lattice d)
    (l gb : ℕ)
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob cprob q ≤ 2 * crossBranch d J) :
    (∑' L : List (CrossCell d),
      (if CrossChain Cbox Cdep J z l L ∧ goodCellCount L ≤ gb then
        (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0)) ≤
      (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * (2 * (4 * crossBranch d J) ^ gb) *
        (1 + crossScaleSum d Cbox Cdep Cprob cprob q) := by
  classical
  set w : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob cprob q with hw
  set K : ℝ≥0∞ := 2 * (4 * crossBranch d J) ^ gb with hK
  have hnil : (if CrossChain Cbox Cdep J z l ([] : List (CrossCell d)) ∧
      goodCellCount ([] : List (CrossCell d)) ≤ gb then
        (([] : List (CrossCell d)).map w).prod else 0) = 0 := by
    rw [if_neg]
    rintro ⟨⟨hne, -⟩, -⟩
    exact hne rfl
  have hcons : ∀ c₀ : CrossCell d,
      (∑' L' : List (CrossCell d),
        (if CrossChain Cbox Cdep J z l (c₀ :: L') ∧
            goodCellCount (c₀ :: L') ≤ gb then ((c₀ :: L').map w).prod else 0)) ≤
      (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
          l + 3 * cellRadius Cbox Cdep c₀ then
        w c₀ * (K * (((cellRadius Cbox Cdep c₀ + 1) ^ d : ℕ) : ℝ≥0∞)) else 0) := by
    intro c₀
    have hterm : ∀ L' : List (CrossCell d),
        (if CrossChain Cbox Cdep J z l (c₀ :: L') ∧
            goodCellCount (c₀ :: L') ≤ gb then ((c₀ :: L').map w).prod else 0) ≤
        (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
            l + 3 * cellRadius Cbox Cdep c₀ then w c₀ else 0) *
          (if L'.IsChain (cellReach Cbox Cdep J) ∧
              (∀ c' ∈ L'.head?, cellReach Cbox Cdep J c₀ c') ∧
              goodCellCount L' ≤ gb then (L'.map w).prod else 0) := by
      intro L'
      by_cases hc : CrossChain Cbox Cdep J z l (c₀ :: L') ∧
          goodCellCount (c₀ :: L') ≤ gb
      · have hstart : 3 * latticeDist z (cellCenter Cdep c₀) ≤
            l + 3 * cellRadius Cbox Cdep c₀ := hc.1.2.2.1 c₀ (by simp)
        obtain ⟨hhead, htail⟩ := List.isChain_cons.mp hc.1.2.1
        have hgc' : goodCellCount L' ≤ gb := by
          have hgc := hc.2
          rw [goodCellCount_cons] at hgc
          omega
        rw [if_pos hc, if_pos hstart, if_pos ⟨htail, hhead, hgc'⟩,
          List.map_cons, List.prod_cons]
      · rw [if_neg hc]
        exact zero_le _
    calc (∑' L' : List (CrossCell d),
          (if CrossChain Cbox Cdep J z l (c₀ :: L') ∧
              goodCellCount (c₀ :: L') ≤ gb then ((c₀ :: L').map w).prod else 0))
        ≤ ∑' L' : List (CrossCell d),
            (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
              l + 3 * cellRadius Cbox Cdep c₀ then w c₀ else 0) *
              (if L'.IsChain (cellReach Cbox Cdep J) ∧
                (∀ c' ∈ L'.head?, cellReach Cbox Cdep J c₀ c') ∧
                goodCellCount L' ≤ gb then (L'.map w).prod else 0) :=
          ENNReal.tsum_le_tsum hterm
      _ = (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
              l + 3 * cellRadius Cbox Cdep c₀ then w c₀ else 0) *
            chainSumAll Cbox Cdep J Cprob cprob q gb c₀ := ENNReal.tsum_mul_left
      _ ≤ (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
              l + 3 * cellRadius Cbox Cdep c₀ then w c₀ else 0) *
            (2 * (((cellRadius Cbox Cdep c₀ + 1) ^ d : ℕ) : ℝ≥0∞) *
              (4 * crossBranch d J) ^ gb) :=
          mul_le_mul' le_rfl (chainSumAll_le Cbox Cdep J Cprob cprob q hpi gb c₀)
      _ = (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
              l + 3 * cellRadius Cbox Cdep c₀ then
            w c₀ * (K * (((cellRadius Cbox Cdep c₀ + 1) ^ d : ℕ) : ℝ≥0∞)) else 0) := by
          by_cases hs : 3 * latticeDist z (cellCenter Cdep c₀) ≤
              l + 3 * cellRadius Cbox Cdep c₀
          · rw [if_pos hs, if_pos hs, hK]; ring
          · rw [if_neg hs, if_neg hs, zero_mul]
  calc (∑' L : List (CrossCell d),
        (if CrossChain Cbox Cdep J z l L ∧ goodCellCount L ≤ gb then
          (L.map w).prod else 0))
      = (if CrossChain Cbox Cdep J z l ([] : List (CrossCell d)) ∧
          goodCellCount ([] : List (CrossCell d)) ≤ gb then
            (([] : List (CrossCell d)).map w).prod else 0) +
        ∑' p : CrossCell d × List (CrossCell d),
          (if CrossChain Cbox Cdep J z l (p.1 :: p.2) ∧
            goodCellCount (p.1 :: p.2) ≤ gb then ((p.1 :: p.2).map w).prod else 0) :=
        tsum_list_eq _
    _ = ∑' (c₀ : CrossCell d) (L' : List (CrossCell d)),
          (if CrossChain Cbox Cdep J z l (c₀ :: L') ∧
            goodCellCount (c₀ :: L') ≤ gb then ((c₀ :: L').map w).prod else 0) := by
        rw [hnil, zero_add, ENNReal.tsum_prod']
    _ ≤ ∑' c₀ : CrossCell d,
          (if 3 * latticeDist z (cellCenter Cdep c₀) ≤
            l + 3 * cellRadius Cbox Cdep c₀ then
            w c₀ * (K * (((cellRadius Cbox Cdep c₀ + 1) ^ d : ℕ) : ℝ≥0∞))
          else 0) := ENNReal.tsum_le_tsum hcons
    _ ≤ (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * K *
          (1 + crossScaleSum d Cbox Cdep Cprob cprob q) :=
        tsum_start_le Cbox Cdep Cprob cprob q z l K

/-! ## The crossing-density failure probability -/

/-- The event that some `J`-step crossing of the annulus at scale `l` carries
fewer than `N` annulus-good vertices. -/
def crossFailEvent (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (z : Lattice d)
    (l N : ℕ) : Set Ω := {ω | ¬ CrossingGoodCount E Cbox J ω z l N}

/-- **`[ASD, Lemma B.1(2)]` for the concrete field, at one scale.** -/
theorem measure_crossFailEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcq : 0 ≤ cprob * q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d J)
    (z : Lattice d) (l N : ℕ) (hCbox : 12 * Cbox ≤ l) (hCbox1 : 1 ≤ Cbox) :
    mu (crossFailEvent E Cbox J z l N) ≤
      ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ d) * q *
        (((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) /
          (6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ))))) *
        ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d J) ^ (N + 2)) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) := by
  classical
  set gb : ℕ := N + 2 with hgb
  set Ac : ℝ := 6 * ((Cbox + Cdep : ℕ) : ℝ) + 3 * (J : ℝ) with hAc
  have hAcpos : 0 < Ac := by
    have h1 : (1 : ℝ) ≤ ((Cbox + Cdep : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have h2 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
    rw [hAc]; linarith
  set beta : ℝ := cprob / 2 / 2 ^ d with hbeta
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-beta * q * (((l : ℝ) -
    3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac))) with hG
  set S : Set (List (CrossCell d)) :=
    {L | CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧ goodCellCount L ≤ gb} with hS
  set w : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob cprob q with hw
  set wh : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob (cprob / 2) q with hwh
  -- the failure event is covered by the certificates
  have hsub : crossFailEvent E Cbox J z l N ⊆ ⋃ L ∈ S, chainEvent E Cdep L := by
    intro ω hω
    obtain ⟨L, hcc, hnd, hev, hgc⟩ :=
      exists_crossChain_of_not_crossingGoodCount (Cdep := Cdep) E Cbox J ω z l N
        hCbox hω
    exact Set.mem_biUnion (show L ∈ S from ⟨hcc, hnd, hgc⟩) hev
  -- each certificate's weight carries the gain
  have hgain : ∀ L : List (CrossCell d), L ∈ S →
      (L.map w).prod ≤ G * (L.map wh).prod := by
    intro L hL
    rw [prod_map_cellWeight_eq d Cdep Cprob cprob q L, prod_map_crossGain d cprob q L]
    refine mul_le_mul' ?_ le_rfl
    rw [hG]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hkey := le_sum_cellTau hL.1 hL.2.2
    have hbq : 0 ≤ beta * q := by
      rw [hbeta]
      have h2 : (0 : ℝ) < 2 ^ d := by positivity
      have : cprob / 2 / 2 ^ d * q = cprob * q / 2 / 2 ^ d := by ring
      rw [this]
      positivity
    have hdiv : ((l : ℝ) - 3 * (J : ℝ) * ((N : ℝ) + 2)) / Ac ≤ (L.map cellTau).sum := by
      rw [div_le_iff₀ hAcpos]
      have hgbR : ((gb : ℕ) : ℝ) = (N : ℝ) + 2 := by rw [hgb]; push_cast; ring
      rw [hgbR] at hkey
      nlinarith [hkey]
    nlinarith [hdiv, hbq]
  -- assemble
  calc mu (crossFailEvent E Cbox J z l N)
      ≤ mu (⋃ L ∈ S, chainEvent E Cdep L) := measure_mono hsub
    _ ≤ ∑' L : S, mu (chainEvent E Cdep (L : List (CrossCell d))) :=
        measure_biUnion_le mu S.to_countable _
    _ ≤ ∑' L : S, G * ((L : List (CrossCell d)).map wh).prod := by
        refine ENNReal.tsum_le_tsum fun L => ?_
        exact le_trans (measure_chainEvent_le mu Cdep hsc hr hprob
          (L : List (CrossCell d)) L.2.2.1) (hgain _ L.2)
    _ = G * ∑' L : S, ((L : List (CrossCell d)).map wh).prod := ENNReal.tsum_mul_left
    _ ≤ G * ∑' L : List (CrossCell d),
          (if CrossChain Cbox Cdep J z l L ∧ goodCellCount L ≤ gb then
            (L.map wh).prod else 0) := by
        refine mul_le_mul' le_rfl ?_
        rw [tsum_subtype S (fun L => (L.map wh).prod)]
        refine ENNReal.tsum_le_tsum fun L => ?_
        by_cases hLS : L ∈ S
        · rw [Set.indicator_of_mem hLS, if_pos ⟨hLS.1, hLS.2.2⟩]
        · rw [Set.indicator_of_notMem hLS]
          exact zero_le _
    _ ≤ G * ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
          (2 * (4 * crossBranch d J) ^ gb) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) :=
        mul_le_mul' le_rfl (tsum_crossChain_le Cbox Cdep J Cprob (cprob / 2) q z l gb hpi)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
