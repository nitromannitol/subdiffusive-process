module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerConclusion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Frozen.Section3.SpecialTwoDExactFormula

@[expose] public section

/-!
# Conditional spine for strict decay of the homogenized coefficient

The planar branch is discharged by the proved exact formula.  In dimensions
at least three, the sole remaining boundary is the quantitative output of the
paper's sparse-simplex construction: a strict one-cell contraction transported
to a real-exponent bound at every cutoff scale.

The decomposition follows
`Algsuperdiff/Section3/Provider/Diffusivity/RecurrenceIntegration/`: keep the
analytic block gain separate from the deterministic conversion to a power-law
rate, then cap the rate only at the final source-facing assembly.
-/

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The literal quantitative output of Steps 1--6 : a strict one-cell contraction `q < 1`, a
positive integer sparse spacing `R`, and the sparse natural-power estimate.

Unlike `HighDimensionalSparseDecayConclusion`, this carrier contains no
real-exponent conversion.  Its proof is precisely the still-missing simplex
rigidity, finite-element approximation, sparse-layer induction, and
thermodynamic passage. -/
def HighDimensionalSparseNaturalPowerConclusion {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : Prop :=
  ∃ q : ℝ, ∃ R : ℕ, 0 < q ∧ q < 1 ∧ 0 < R ∧
    ∀ m : ℕ, ahom M m ≤ q ^ (m / R + 1)

/-- The sparse-index payload of Steps 1--4.  The  bounds `ahom M m` through the sparse layer count
`N = floor(m / R)` alone, so its genuine output is the family indexed by the
sparse layers themselves.  This is strictly weaker than
`HighDimensionalSparseNaturalPowerConclusion`: the two are separated only by
the proved cutoff monotonicity. -/
def HighDimensionalSparseLayerConclusion {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : Prop :=
  ∃ q : ℝ, ∃ R : ℕ, 0 < q ∧ q < 1 ∧ 0 < R ∧
    ∀ N : ℕ, ahom M (N * R) ≤ q ^ (N + 1)

/-- Recover the natural-power payload at every cutoff from its restriction to
the sparse layers.  The only input beyond the sparse family is the proved
monotonicity of `ahom` in the cutoff index. -/
theorem high_dimensional_sparse_natural_power_of_sparse_layer {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (hLayer : HighDimensionalSparseLayerConclusion M) :
    HighDimensionalSparseNaturalPowerConclusion M := by
  rcases hLayer with ⟨q, R, hq, hq1, hR, hsparse⟩
  exact ⟨q, R, hq, hq1, hR,
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_pow_div_of_sparse_index M
      hsparse⟩

/-- The exact quantitative payload left by Steps 1--4 of the proof, after converting the sparse natural power to a
real exponent.  The witnesses may depend on the model law, as permitted by
the source statement. -/
def HighDimensionalSparseDecayConclusion {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : Prop :=
  ∃ q R : ℝ, 0 < q ∧ q < 1 ∧ 0 < R ∧
    ∀ m : ℕ, ahom M m ≤ Real.rpow q ((m + 1 : ℝ) / R)

/-- Convert the manuscript's sparse natural power
`q^(floor(m/R)+1)` to the real-exponent payload used by the final rate
assembly.  This is the arithmetic. -/
theorem high_dimensional_sparse_decay_of_natural_power {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (hSparse : HighDimensionalSparseNaturalPowerConclusion M) :
    HighDimensionalSparseDecayConclusion M := by
  rcases hSparse with ⟨q, R, hq, hq1, hR, hdecay⟩
  refine ⟨q, (R : ℝ), hq, hq1, by exact_mod_cast hR, ?_⟩
  intro m
  have hnat : m + 1 ≤ R * (m / R + 1) := by
    have hmod := Nat.mod_lt m hR
    have hdecomp := Nat.div_add_mod m R
    calc
      m + 1 = R * (m / R) + m % R + 1 := by omega
      _ ≤ R * (m / R) + R := by omega
      _ = R * (m / R + 1) := by ring
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hexponent :
      (m + 1 : ℝ) / (R : ℝ) ≤ ((m / R + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hRreal]
    exact_mod_cast (show m + 1 ≤ (m / R + 1) * R by
      simpa [Nat.mul_comm] using hnat)
  calc
    ahom M m ≤ q ^ (m / R + 1) := hdecay m
    _ = Real.rpow q ((m / R + 1 : ℕ) : ℝ) := by
      exact (Real.rpow_natCast q (m / R + 1)).symm
    _ ≤ Real.rpow q ((m + 1 : ℝ) / (R : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1.le hexponent

private theorem rpow_sparse_eq_base_three {q R : ℝ}
    (hq : 0 < q) (hR : 0 < R) (m : ℕ) :
    Real.rpow q ((m + 1 : ℝ) / R) =
      Real.rpow 3
        (-(-Real.log q / (R * Real.log 3)) * (m + 1 : ℝ)) := by
  change q ^ ((m + 1 : ℝ) / R) =
    (3 : ℝ) ^ (-(-Real.log q / (R * Real.log 3)) * (m + 1 : ℝ))
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- The high-dimensional sparse contraction gives the printed strict-decay
rate, including the harmless cap by `tauSq / (d * log 3)`. -/
theorem high_dimensional_strict_decay_of_sparse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hd : 3 ≤ d)
    (hSparse : HighDimensionalSparseDecayConclusion M) :
    ∃ eta : ℝ, 0 < eta ∧
      eta ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) := by
  rcases hSparse with ⟨q, R, hq, hq1, hR, hdecay⟩
  let eta0 : ℝ := -Real.log q / (R * Real.log 3)
  let etaTau : ℝ :=
    _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3)
  let eta : ℝ := min eta0 etaTau
  have hlogq : Real.log q < 0 := Real.log_neg hq hq1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have heta0 : 0 < eta0 := by
    dsimp [eta0]
    exact div_pos (neg_pos.mpr hlogq) (mul_pos hR hlog3)
  have hetaTau : 0 < etaTau := by
    dsimp [etaTau]
    exact div_pos M.G4.tauSq_pos (mul_pos hdreal hlog3)
  have heta : 0 < eta := lt_min heta0 hetaTau
  refine ⟨eta, heta, min_le_right _ _, ?_⟩
  intro m
  have hbase : (1 : ℝ) < 3 := by norm_num
  have hmono :
      Real.rpow 3 (-eta0 * (m + 1 : ℝ)) ≤
        Real.rpow 3 (-eta * (m + 1 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase.le
    have hm : (0 : ℝ) ≤ (m + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hm
  calc
    ahom M m ≤ Real.rpow q ((m + 1 : ℝ) / R) := hdecay m
    _ = Real.rpow 3 (-eta0 * (m + 1 : ℝ)) :=
      rpow_sparse_eq_base_three hq hR m
    _ ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) := hmono

/-- Conditional provider spine for the frozen strict-decay proposition.  Its
only open premise is the sparse-simplex payload in dimensions at least three;
the planar branch and all exponent arithmetic are proved here. -/
theorem homogenized_coefficient_strict_decay_of_sparse {d : ℕ}
    (hSparse : ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      3 ≤ d → HighDimensionalSparseDecayConclusion M)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
      (3 ≤ d → eta ≤
        _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) := by
  by_cases hd2 : d = 2
  · subst d
    let eta : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3
    have heta : 0 < eta := by
      dsimp [eta]
      exact div_pos M.G4.tauSq_pos (Real.log_pos (by norm_num))
    refine ⟨eta, heta, by rintro _; rfl, ?_, ?_⟩
    · omega
    · intro m
      rw [SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula M m]
      change Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
        (3 : ℝ) ^ (-eta * (m + 1 : ℝ))
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      apply le_of_eq
      congr 1
      have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      dsimp [eta]
      field_simp
  · have hd : 3 ≤ d := by
      have hdim := M.shellPrefix.dimension
      omega
    rcases high_dimensional_strict_decay_of_sparse M hd (hSparse M hd) with
      ⟨eta, heta, hetaUpper, hdecay⟩
    exact ⟨eta, heta, by omega, fun _ => hetaUpper, hdecay⟩

/-- Source-shaped conditional provider whose only high-dimensional premise is
the natural sparse-power estimate actually produced. -/
theorem homogenized_coefficient_strict_decay_of_sparse_natural {d : ℕ}
    (hSparse : ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      3 ≤ d → HighDimensionalSparseNaturalPowerConclusion M)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
      (3 ≤ d → eta ≤
        _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) := by
  apply homogenized_coefficient_strict_decay_of_sparse
  intro M hd
  exact high_dimensional_sparse_decay_of_natural_power M (hSparse M hd)

/-- Conditional provider spine whose only high-dimensional premise is the
sparse-layer family produced by Steps 1--3 of the proof.  Everything else in
the strict-decay proposition -- the planar branch, cutoff monotonicity, the
`floor(m/R)` arithmetic, and the exponent cap -- is proved. -/
theorem homogenized_coefficient_strict_decay_of_sparse_layer {d : ℕ}
    (hSparse : ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      3 ≤ d → HighDimensionalSparseLayerConclusion M)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
      (3 ≤ d → eta ≤
        _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) := by
  apply homogenized_coefficient_strict_decay_of_sparse_natural
  intro M hd
  exact high_dimensional_sparse_natural_power_of_sparse_layer M (hSparse M hd)

/-- **The sparse-layer payload of Steps 1--4**,
unconditionally.  Step 2 selects the spacing `R` with `q_R < 1` uniformly in the
order; Step 3 runs the sparse induction; Step 4 compares the full cutoff with
the sparse product on the cube `cu_{NR}` and reads off `ahom`. -/
theorem high_dimensional_sparse_layer {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    HighDimensionalSparseLayerConclusion M :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_sparse_layer_bound M

/-- **`p.homogenized.coefficient.strict.decay`**
unconditional: the planar branch is the proved
exact formula and the high-dimensional branch is the sparse-simplex
construction. -/
theorem homogenized_coefficient_strict_decay {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
      (3 ≤ d → eta ≤
        _root_.SubdiffusiveProcess.Model.tauSq M.P / ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ)) :=
  homogenized_coefficient_strict_decay_of_sparse_layer
    (fun M _ => high_dimensional_sparse_layer M) M

end

end SubdiffusiveProcess.Providers.Section5
