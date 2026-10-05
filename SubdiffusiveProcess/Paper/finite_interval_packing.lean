module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Probability.FiniteBranchUnion
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_branch
public import SubdiffusiveProcess.Paper.in_source_independence
public import SubdiffusiveProcess.Paper.finite_interval_packing_witness_union
public import SubdiffusiveProcess.Paper.finite_interval_packing_prefix_entropy
public import SubdiffusiveProcess.Paper.finite_interval_packing_branch_entropy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_finite_interval_packing_depth_bound
    (H1 N : ℕ) (hH1 : 0 < H1) (jroot : ℤ) (n : ℕ)
    (h : (H1 : ℤ) * (n : ℤ) - jroot < (N : ℤ)) :
    n < N / H1 + jroot.natAbs + 2 := by
  have hj : jroot ≤ (jroot.natAbs : ℤ) := Int.le_natAbs
  have hmul : (H1 : ℤ) * (n : ℤ) < (N : ℤ) + (jroot.natAbs : ℤ) := by
    linarith
  have hmul' : H1 * n < N + jroot.natAbs := by
    exact_mod_cast hmul
  by_contra hn
  have hn' : N / H1 + jroot.natAbs + 2 ≤ n := by omega
  have hmod : N % H1 < H1 := Nat.mod_lt N hH1
  have hdecomp : N = H1 * (N / H1) + N % H1 :=
    (Nat.div_add_mod N H1).symm
  have hmulabs : jroot.natAbs ≤ H1 * jroot.natAbs := by
    simpa using Nat.mul_le_mul_right jroot.natAbs hH1
  have hbig : N + jroot.natAbs < H1 * (N / H1 + jroot.natAbs + 2) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact (not_lt_of_ge (Nat.mul_le_mul_left H1 hn')) (hmul'.trans hbig)

lemma aux_finite_interval_packing_two_witnesses
    {Ω X β : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype β]
    (J : ℕ) (B theta : ℝ) (hB : 4 < B) (htheta : 0 < theta) (htheta1 : theta < 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℤ → Ω → X) (hg : ∀ j : ℤ, Measurable (g j))
    (hgi : iIndepFun g P)
    (n : β → Fin J → ℤ) (hn : ∀ b : β, Function.Injective (n b))
    (W₁ W₂ : β → Fin J → ℕ+ → Set Ω)
    (hW₁ : ∀ (b : β) (i : Fin J) (h : ℕ+),
      MeasurableSet[
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (n b i - (h : ℤ))
          (n b i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))]
        (W₁ b i h))
    (hW₂ : ∀ (b : β) (i : Fin J) (h : ℕ+),
      MeasurableSet[
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (n b i - (h : ℤ))
          (n b i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))]
        (W₂ b i h))
    (hP₁ : ∀ (b : β) (i : Fin J) (h : ℕ+),
      P (W₁ b i h) ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ))))
    (hP₂ : ∀ (b : β) (i : Fin J) (h : ℕ+),
      P (W₂ b i h) ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) :
    P {ω | ∃ b : β, theta * (J : ℝ) ≤
      (Set.ncard {i : Fin J | ∃ h : ℕ+,
        ω ∈ W₁ b i h ∨ ω ∈ W₂ b i h} : ℝ)} ≤
      (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (-((B / 2 * theta / 24) + Real.log (1 - Real.exp (-(B / 4)))) * (J : ℝ))) := by
  let W : β → Fin J → ℕ+ → Set Ω := fun b i h => W₁ b i h ∪ W₂ b i h
  let failure : β → Fin J → Set Ω := fun b i => ⋃ h : ℕ+, W b i h
  have hW : ∀ (b : β) (i : Fin J) (h : ℕ+),
      MeasurableSet[
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (n b i - (h : ℤ))
          (n b i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))]
        (W b i h) := by
    intro b i h
    exact (hW₁ b i h).union (hW₂ b i h)
  have hP : ∀ (b : β) (i : Fin J) (h : ℕ+),
      P (W b i h) ≤ ENNReal.ofReal (Real.exp (-(B / 2) * (h : ℝ))) := by
    intro b i h
    have hbh : 1 ≤ B * (h : ℝ) / 2 := by
      have hh : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h.property
      nlinarith
    have hexp : 2 ≤ Real.exp (B * (h : ℝ) / 2) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      exact htwo.trans (Real.exp_le_exp.mpr hbh)
    have hmul : 2 * Real.exp (-B * (h : ℝ)) ≤
        Real.exp (-(B / 2) * (h : ℝ)) := by
      calc
        2 * Real.exp (-B * (h : ℝ)) ≤
            Real.exp (B * (h : ℝ) / 2) * Real.exp (-B * (h : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
        _ = Real.exp (-(B / 2) * (h : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring
    calc
      P (W b i h) ≤ P (W₁ b i h) + P (W₂ b i h) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ))) +
          ENNReal.ofReal (Real.exp (-B * (h : ℝ))) :=
        add_le_add (hP₁ b i h) (hP₂ b i h)
      _ = ENNReal.ofReal (2 * Real.exp (-B * (h : ℝ))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (Real.exp (-(B / 2) * (h : ℝ))) :=
        ENNReal.ofReal_le_ofReal hmul
  have hsub : ∀ (b : β) (i : Fin J),
      failure b i ⊆ ⋃ h : ℕ+, W b i h := by
    intro b i
    exact Subset.rfl
  have hmain := SubdiffusiveProcess.union_bound_finitely_many_bad_branches
    J (B / 2) theta (by linarith) htheta htheta1 Ω X P g hg hgi n hn failure W hW hP hsub
  have heq : -(B / 2) / 2 = -(B / 4) := by ring
  rw [heq] at hmain
  have hmain' : P {ω | ∃ b : β, theta * (J : ℝ) ≤
      (Set.ncard {i : Fin J | ∃ h : ℕ+,
        ω ∈ W₁ b i h ∨ ω ∈ W₂ b i h} : ℝ)} ≤
      (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (-((B / 2 * theta / 24) + Real.log (1 - Real.exp (-(B / 4)))) * (J : ℝ))) := by
    simpa [failure, W, Set.mem_iUnion, exists_or] using hmain
  exact hmain'

lemma aux_finite_interval_packing_word_card (d H1 K : ℕ) :
    (Fintype.card (Fin K → OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) =
      Real.exp ((H1 : ℝ) * (d : ℝ) * (K : ℝ) * Real.log 3) := by
  simp [OddGridIndex, two_mul_subdivisionHalfWidth_add_one]
  rw [show (H1 : ℝ) * (d : ℝ) * (K : ℝ) * Real.log 3 =
      (K : ℝ) * ((H1 : ℝ) * ((d : ℝ) * Real.log 3)) by ring]
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  ring

lemma aux_finite_interval_packing_exp_order (d H1 K : ℕ) :
    (H1 : ℝ) * (d : ℝ) * (K : ℝ) * Real.log 3 =
      ((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ) := by
  ring

lemma aux_finite_interval_packing_sigma
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (k : ℤ) (h : ℕ+) :
    (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (k - (h : ℤ))
      (k + 2 * (h : ℤ))),
      MeasurableSpace.comap
        (fun omega : BilateralField d => omega (-j))
        (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ))) =
      MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) →
            C(SpatialCoordinates d, ℝ))) := by
  have hs : MeasurableSpace.comap
      ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace
        ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) →
          C(SpatialCoordinates d, ℝ))) =
      ⨆ i ∈ Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ)),
        MeasurableSpace.comap (fun omega : BilateralField d => omega i)
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
    simpa only using! SubdiffusiveProcess.comap_restrict_eq_iSup
      (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      (Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ)))
  rw [hs]
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hj' : -j ∈ Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ)) := by
      simp only [Finset.mem_Icc] at hj
      simp only [Set.mem_Icc]
      omega
    exact le_iSup_of_le (-j) (le_iSup_of_le hj' le_rfl)
  · refine iSup_le fun i => iSup_le fun hi => ?_
    have hi' : -i ∈ Finset.Icc (k - (h : ℤ)) (k + 2 * (h : ℤ)) := by
      simp only [Set.mem_Icc] at hi
      simp only [Finset.mem_Icc]
      omega
    have hle :
        MeasurableSpace.comap (fun x : BilateralField d => x i)
            (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) ≤
          MeasurableSpace.comap (fun omega : BilateralField d => omega (-(-i)))
            (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
      have hle0 :
          MeasurableSpace.comap (fun x : BilateralField d => x i)
              (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) ≤
            MeasurableSpace.comap (fun x : BilateralField d => x i)
              (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := le_rfl
      simpa only [neg_neg] using hle0
    exact le_iSup_of_le (-i) (le_iSup_of_le hi' hle)

lemma aux_finite_interval_packing_exp_two
    (B : ℝ) (hB : 4 < B) (h : ℕ+) :
    2 * Real.exp (-B * (h : ℝ)) ≤ Real.exp (-(B / 2) * (h : ℝ)) := by
  have hh : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h.property
  have hBnonneg : 0 ≤ B := by linarith
  have hmul : (4 : ℝ) ≤ B * (h : ℝ) := by
    calc
      (4 : ℝ) = 4 * 1 := by norm_num
      _ ≤ B * 1 := by gcongr
      _ ≤ B * (h : ℝ) := by gcongr
  have hBhalf : 1 ≤ B * (h : ℝ) / 2 := by nlinarith only [hmul]
  have he : 2 ≤ Real.exp (B * (h : ℝ) / 2) := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact he1.trans (Real.exp_le_exp.mpr hBhalf)
  calc
    2 * Real.exp (-B * (h : ℝ)) ≤
        Real.exp (B * (h : ℝ) / 2) * Real.exp (-B * (h : ℝ)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (-(B / 2) * (h : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma aux_finite_interval_packing_nat_div_real
    (N H1 K : ℕ) (hH1 : 0 < H1) (hK : N / H1 + 1 ≤ K) :
    (N : ℝ) / (H1 : ℝ) ≤ (K : ℝ) := by
  have hnat : N < H1 * (N / H1 + 1) := by
    have hdecomp : N = H1 * (N / H1) + N % H1 :=
      (Nat.div_add_mod N H1).symm
    have hmod : N % H1 < H1 := Nat.mod_lt N hH1
    calc
      N = H1 * (N / H1) + N % H1 := hdecomp
      _ < H1 * (N / H1) + H1 := Nat.add_lt_add_left hmod _
      _ = H1 * (N / H1 + 1) := by rw [Nat.mul_add]; simp
  have hdiv : (N : ℝ) / (H1 : ℝ) < ((N / H1 : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < H1)).2
    have hnatR : (N : ℝ) < (H1 : ℝ) * ((N / H1 : ℕ) + 1) := by
      exact_mod_cast hnat
    nlinarith
  have hKcast : ((N / H1 : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by
    exact_mod_cast hK
  exact (le_of_lt hdiv).trans hKcast

lemma aux_finite_interval_packing_add_two (x y : ℕ) : x + 1 ≤ x + y + 2 := by
  omega

lemma aux_finite_interval_packing_measure_union_three
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B C : Set Ω) :
    P (A ∪ (B ∪ C)) ≤ P A + (P B + P C) := by
  have hinner : P (B ∪ C) ≤ P B + P C := measure_union_le _ _
  exact (measure_union_le _ _).trans (add_le_add_right hinner (P A))

lemma aux_finite_interval_packing_three_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B C : Set Ω) (r : ℝ) (hr : 4 < r) (h : ℕ+)
    (hA : P A ≤ ENNReal.ofReal (Real.exp (-r * (h : ℝ))))
    (hB : P B ≤ ENNReal.ofReal (Real.exp (-r * (h : ℝ))))
    (hC : P C ≤ ENNReal.ofReal (Real.exp (-r * (h : ℝ)))) :
    P (A ∪ (B ∪ C)) ≤ ENNReal.ofReal (Real.exp (-(r / 2) * (h : ℝ))) := by
  have hh : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h.property
  have hthree : (3 : ℝ) ≤ Real.exp (r * (h : ℝ) / 2) := by
    have hthree0 : (3 : ℝ) ≤ Real.exp 2 := by
      nlinarith [Real.add_one_le_exp (2 : ℝ)]
    apply hthree0.trans
    apply Real.exp_le_exp.mpr
    have hrhalf : (2 : ℝ) < r / 2 := by linarith only [hr]
    have hrhalf0 : 0 ≤ r / 2 := by linarith only [hr]
    have hmul : r / 2 ≤ r / 2 * (h : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left hh hrhalf0)
    calc
      (2 : ℝ) ≤ r / 2 := hrhalf.le
      _ ≤ r / 2 * (h : ℝ) := hmul
      _ = r * (h : ℝ) / 2 := by ring
  have hexp : 3 * Real.exp (-r * (h : ℝ)) ≤
      Real.exp (-(r / 2) * (h : ℝ)) := by
    calc
      3 * Real.exp (-r * (h : ℝ)) ≤
          Real.exp (r * (h : ℝ) / 2) * Real.exp (-r * (h : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
      _ = Real.exp (-(r / 2) * (h : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    P (A ∪ (B ∪ C)) ≤ P A + (P B + P C) :=
      aux_finite_interval_packing_measure_union_three P A B C
    _ ≤ ENNReal.ofReal (Real.exp (-r * (h : ℝ))) +
        (ENNReal.ofReal (Real.exp (-r * (h : ℝ))) +
          ENNReal.ofReal (Real.exp (-r * (h : ℝ)))) := by
      exact add_le_add hA (add_le_add hB hC)
    _ = ENNReal.ofReal (3 * Real.exp (-r * (h : ℝ))) := by
      calc
        _ = ENNReal.ofReal
            (Real.exp (-r * (h : ℝ)) +
              (Real.exp (-r * (h : ℝ)) + Real.exp (-r * (h : ℝ)))) := by
          rw [ENNReal.ofReal_add (Real.exp_pos _).le
            (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
          rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        _ = ENNReal.ofReal (3 * Real.exp (-r * (h : ℝ))) := by
          congr 1
          ring
    _ ≤ ENNReal.ofReal (Real.exp (-(r / 2) * (h : ℝ))) :=
      ENNReal.ofReal_le_ofReal hexp

lemma aux_finite_interval_packing_decay
    (e q ceta Ceta : ℝ) (N K H1 : ℕ)
    (hH1 : 0 < H1) (hK : (N : ℝ) / (H1 : ℝ) ≤ (K : ℝ))
    (hgap : 0 < q - e)
    (hceta : ceta = (q - e) / (2 * (H1 : ℝ) * Real.log 3))
    (hCeta : Ceta = Real.exp (q - e)) :
    Real.exp ((e - q) * (K : ℝ)) ≤
      Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ)) := by
  have hhalf : (q - e) * (N : ℝ) / (2 * (H1 : ℝ)) ≤
      (q - e) * (K : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hK hgap.le
    calc
      (q - e) * (N : ℝ) / (2 * (H1 : ℝ)) ≤
          (q - e) * (N : ℝ) / (H1 : ℝ) := by
            gcongr
            nlinarith [hH1]
      _ ≤ (q - e) * (K : ℝ) := by
        simpa [mul_div_assoc] using hmul
  have hexp : (e - q) * (K : ℝ) ≤
      (q - e) + (-ceta * (N : ℝ)) * Real.log 3 := by
    have hcancel : (-ceta * (N : ℝ)) * Real.log 3 =
        -(q - e) * (N : ℝ) / (2 * (H1 : ℝ)) := by
      rw [hceta]
      field_simp
    rw [hcancel]
    calc
      (e - q) * (K : ℝ) = -(q - e) * (K : ℝ) := by ring
      _ ≤ -(q - e) * (N : ℝ) / (2 * (H1 : ℝ)) := by
        convert neg_le_neg hhalf using 1 <;> ring
      _ ≤ (q - e) + (-(q - e) * (N : ℝ) / (2 * (H1 : ℝ))) := by
        linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [hCeta, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using hexp



theorem finite_interval_packing
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (a b theta alpha beta : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (htheta : 0 < theta) (hthetab : theta < b - a)
    (_hbeta : 1 / 2 < beta) (_hba : beta < alpha) (_halpha : alpha < 1)
    (H1 : ℕ) (hH1 : 0 < H1)
    (Cfin Aext pad B : ℝ) (_hCfin : 0 < Cfin) (_hAext : 0 < Aext)
    (hpad : 1 < pad) (_hpadL : pad < (3 : ℝ) ^ H1)
    (hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization model H)
    (zroot : SpatialCoordinates d) (jroot : ℤ) :
    let rootSide : ℝ := (3 : ℝ) ^ jroot
    let L : ℝ := (3 : ℝ) ^ H1
    let mgrid := subdivisionHalfWidth H1
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∀ (Reg : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
      (_hReg : ∀ N k z omega, Reg N k z omega ↔
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let hr : 0 < r := by positivity
        let hLr : 0 < L * r := mul_pos (pow_pos (by norm_num) H1) hr
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
        let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
        let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
        let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
        let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let s : ℝ := (kappa (N - k) / kappa N) *
          Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d mgrid),
          z = oddGridCenter zP (L * r) mgrid idx →
          (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
            (centeredCube zP (L * r) hLr : Set (SpatialCoordinates d)) →
          let Parent : Opens (SpatialCoordinates d) := centeredCube zP (L * r) hLr
          let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model H omega N zP hLr
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
            ∀ u : weakSobolevGraph Parent,
              (∀ psi : killedSobolevGraph Parent,
                @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
                  ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
              ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
                ContinuousOn U closedQ ∧
                ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
                @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
                  Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
                    Real.sqrt (@sobolevCoefficientForm d Parent aP
                      (u : SobolevData Parent) (u : SobolevData Parent)) +
                  Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf)
      (_hRegWitness : ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
        ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂P, ¬Reg N k z omega → omega ∈ ⋃ h : ℕ+, W h)),
    ∀ (eta : ℝ) (_heta : 0 < eta) (m0 : ℕ)
      (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
      (_hTraceClose : ∀ N M k z omega, TraceClose N M k z omega ↔
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let hr : 0 < r := by positivity
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
        let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
        let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let sN : ℝ := (kappa (N - k) / kappa N) *
          Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        let sM : ℝ := (kappa (M - k) / kappa M) *
          Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        let aN : PositiveCoefficient Q := cutoffPositiveCoefficient model H omega N z hr
        let aM : PositiveCoefficient Q := cutoffPositiveCoefficient model H omega M z hr
        ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
            ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
          ∀ (u : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
            ContinuousOn G closedQ → IsCellBoundaryClass alpha z r G →
            ((fun x => (u : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) →
            |@dirichletResponse d Q (@killedResponseSpace d Q hP) aN u /
                (r ^ ((d : ℝ) - 2) * sN) -
              @dirichletResponse d Q (@killedResponseSpace d Q hP) aM u /
                (r ^ ((d : ℝ) - 2) * sM)| ≤
              eta * (cellBoundaryQuotientNorm alpha z r G) ^ (2 : ℕ))
      (_hTraceWitness : ∀ (N M k : ℕ) (z : SpatialCoordinates d),
        k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
        ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂P, ¬TraceClose N M k z omega → omega ∈ ⋃ h : ℕ+, W h)),
    ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          P Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ w : ℕ → OddGridIndex d mgrid,
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - jroot
              let z : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter mgrid zroot rootSide n (fun i : Fin n => w i)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(Reg N (k n).toNat (z n) omega ∧
                  Reg M (k n).toNat (z n) omega ∧
                  TraceClose N M (k n).toNat (z n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
  dsimp only
  intro Reg hReg hRegWitness eta heta m0 TraceClose hTraceClose hTraceWitness
  classical
  clear hReg hTraceClose _hH H _hCfin _hAext hpad _hpadL eta heta
    alpha beta _hbeta _hba _halpha
  let jabs : ℕ := jroot.natAbs
  let qmargin : ℝ := 1 - b
  have hqmargin : 0 < qmargin := by
    dsimp [qmargin]
    linarith
  obtain ⟨Ncut, hNcut⟩ : ∃ Ncut : ℕ, (m0 : ℝ) / qmargin < Ncut :=
    exists_nat_gt ((m0 : ℝ) / qmargin)
  have hNcut' : (m0 : ℝ) < qmargin * (Ncut : ℝ) := by
    have := (div_lt_iff₀ hqmargin).mp hNcut
    nlinarith
  let N0 : ℕ := max Ncut (max 1 (H1 * (jabs + 2)))
  let q : ℝ := (B / 2 * (theta / 2) / 24) +
    Real.log (1 - Real.exp (-(B / 4)))
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hBtheta : 1000 * (H1 : ℝ) * ((d : ℝ) + 1) *
      (Real.log 3 + 1) < B * theta := by
    exact (div_lt_iff₀ htheta).mp hB
  have hB4 : 4 < B := by
    have htheta1 : theta < 1 := by
      have : b - a < 1 := by linarith
      linarith
    have hprod : 3000 ≤ 1000 * (H1 : ℝ) * ((d : ℝ) + 1) *
        (Real.log 3 + 1) := by
      have hH1' : (1 : ℝ) ≤ H1 := by
        exact_mod_cast (show 1 ≤ H1 by omega)
      have hd' : (3 : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast (show 3 ≤ d + 1 by omega)
      have hl' : (1 : ℝ) ≤ Real.log 3 + 1 := by linarith
      calc
        (3000 : ℝ) = 1000 * 1 * 3 * 1 := by norm_num
        _ ≤ 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) := by
          gcongr
    have hfour : 4 * theta < B * theta := by linarith [hBtheta, hprod]
    nlinarith
  have hloglower : -1 ≤ Real.log (1 - Real.exp (-(B / 4))) := by
    have hexp : Real.exp (-(B / 4)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hinside : 0 < 1 - Real.exp (-(B / 4)) := sub_pos.mpr hexp
    have harg : Real.exp (-1 : ℝ) ≤ 1 - Real.exp (-(B / 4)) := by
      have hsum : (2 : ℝ) ≤ Real.exp 1 := by
        have ht := Real.add_one_le_exp (1 : ℝ)
        norm_num at ht ⊢
        exact ht
      have he : Real.exp (-(B / 4)) ≤ Real.exp (-1 : ℝ) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hmul : Real.exp 1 * Real.exp (-1 : ℝ) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hhalf : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
        nlinarith [Real.exp_pos (-1 : ℝ), hmul]
      nlinarith [hhalf]
    have hposarg : Real.exp (-1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      exact Real.exp_pos _
    have hlog := Real.strictMonoOn_log.monotoneOn hposarg
      (show 1 - Real.exp (-(B / 4)) ∈ Set.Ioi (0 : ℝ) by exact hinside) harg
    simpa [Real.log_exp] using hlog
  have hqentropy : (H1 : ℝ) * (d : ℝ) * Real.log 3 < q := by
    have hbase : (H1 : ℝ) * (d : ℝ) * Real.log 3 ≤
        (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) := by
      calc
        (H1 : ℝ) * (d : ℝ) * Real.log 3 ≤
            (H1 : ℝ) * ((d : ℝ) + 1) * Real.log 3 := by
              have hdle : (d : ℝ) ≤ (d : ℝ) + 1 := by linarith
              gcongr
        _ ≤ (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) := by
              have : Real.log 3 ≤ Real.log 3 + 1 := by linarith
              have hH1nonneg : (0 : ℝ) ≤ H1 := by positivity
              have hd1nonneg : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
              gcongr
    have hA : 3 ≤ (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) := by
      calc
        (3 : ℝ) = 1 * 3 * 1 := by norm_num
        _ ≤ (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) := by
          have hH1' : (1 : ℝ) ≤ H1 := by
            exact_mod_cast (show 1 ≤ H1 by omega)
          have hd' : (3 : ℝ) ≤ (d : ℝ) + 1 := by
            exact_mod_cast (show 3 ≤ d + 1 by omega)
          have hl' : (1 : ℝ) ≤ Real.log 3 + 1 := by linarith
          have hl'' : Real.log 3 ≤ Real.log 3 + 1 := by linarith
          gcongr
    dsimp [q]
    have hAplus :
        (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) + 1 < B * theta / 96 := by
      linarith only [hBtheta, hA]
    have hXlt : (H1 : ℝ) * (d : ℝ) * Real.log 3 < B * theta / 96 - 1 := by
      linarith only [hbase, hAplus]
    linarith only [hXlt, hloglower]
  let ceta : ℝ := (q - (H1 : ℝ) * (d : ℝ) * Real.log 3) /
    (2 * (H1 : ℝ) * Real.log 3)
  let Ceta : ℝ := Real.exp (q - (H1 : ℝ) * (d : ℝ) * Real.log 3)
  have hceta : 0 < ceta := by
    dsimp [ceta]
    have hnum : 0 < q - (H1 : ℝ) * (d : ℝ) * Real.log 3 := by
      linarith only [hqentropy]
    have hden : 0 < 2 * (H1 : ℝ) * Real.log 3 := by positivity
    exact div_pos hnum hden
  have hCeta : 0 < Ceta := by
    dsimp [Ceta]
    positivity
  refine ⟨Ceta, ceta, N0, hCeta, hceta, ?_⟩
  intro N M hN0 hNM
  have hN1 : 1 ≤ N := by
    have h : 1 ≤ N0 := le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans h hN0
  have hNpos : 0 < (N : ℝ) := by positivity
  have hNcutN : Ncut ≤ N := le_trans (le_max_left _ _) hN0
  have hsize : H1 * (jabs + 2) ≤ N := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN0)
  have hwindow : ∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) →
      (k : ℝ) ≤ b * (N : ℝ) →
      0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat := by
    intro k hka hkb
    have hapos : 0 < a * (N : ℝ) := mul_pos ha hNpos
    have hbNlt : b * (N : ℝ) < (N : ℝ) := by
      have h := mul_lt_mul_of_pos_right hb hNpos
      simpa [mul_one] using h
    have hkposreal : 0 < (k : ℝ) := lt_of_lt_of_le hapos hka
    have hk0 : 0 ≤ k := by exact_mod_cast hkposreal.le
    have hklt : (k : ℝ) < (N : ℝ) := lt_of_le_of_lt hkb hbNlt
    have hkN : k.toNat ≤ N := by
      have hklt' : k < (N : ℤ) := by exact_mod_cast hklt
      omega
    have hkcast : (k.toNat : ℝ) = k := by
      have h := Int.toNat_of_nonneg hk0
      exact_mod_cast h
    have hsubcast : ((N - k.toNat : ℕ) : ℝ) = (N : ℝ) - k := by
      rw [Nat.cast_sub hkN]
      norm_num [hkcast]
    have hcut : (m0 : ℝ) ≤ (N : ℝ) - k := by
      have hqN : (m0 : ℝ) < qmargin * (N : ℝ) := by
        have hNcutreal : (Ncut : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNcutN
        have hmul : qmargin * (Ncut : ℝ) ≤ qmargin * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hNcutreal hqmargin.le
        exact lt_of_lt_of_le hNcut' hmul
      dsimp [qmargin] at hqN ⊢
      linarith only [hqN, hkb]
    have hcutN : m0 ≤ N - k.toNat := by
      have hcut' : (m0 : ℝ) ≤ ((N - k.toNat : ℕ) : ℝ) := by
        rw [hsubcast]
        exact hcut
      exact_mod_cast hcut'
    have hcutM : m0 ≤ M - k.toNat := by
      exact le_trans hcutN (Nat.sub_le_sub_right hNM _)
    exact ⟨hk0, hcutN, hcutM⟩
  constructor
  · exact hwindow
  let K : ℕ := N / H1 + jabs + 2
  have hKreal : (N : ℝ) / (H1 : ℝ) ≤ (K : ℝ) := by
    apply aux_finite_interval_packing_nat_div_real N H1 K hH1
    change N / H1 + 1 ≤ N / H1 + jabs + 2
    exact aux_finite_interval_packing_add_two (N / H1) jabs
  let β := Fin K → OddGridIndex d (subdivisionHalfWidth H1)
  have hcardβ : (Fintype.card β : ℝ≥0∞) =
      ENNReal.ofReal (Fintype.card β : ℝ) := by
    exact (ENNReal.ofReal_natCast (Fintype.card β)).symm
  let kval : Fin K → ℕ := fun i =>
    ((H1 : ℤ) * (i.val : ℤ) - jroot).toNat
  let kint : Fin K → ℤ := fun i => (H1 : ℤ) * (i.val : ℤ) - jroot
  let zval : β → Fin K → SpatialCoordinates d := fun w i =>
    descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ jroot) i.val
      (fun j : Fin i.val => w ⟨j.val, j.isLt.trans i.isLt⟩)
  let relevant : Fin K → Prop := fun i =>
    a * (N : ℝ) ≤ (kint i : ℝ) ∧ (kint i : ℝ) ≤ b * (N : ℝ)
  have hKle : K ≤ 2 * (N / H1) := by
    have hdiv : jabs + 2 ≤ N / H1 := by
      apply (Nat.le_div_iff_mul_le hH1).2
      simpa [Nat.mul_comm] using hsize
    dsimp [K]
    omega
  have hKlower : N / H1 ≤ K := by
    dsimp [K]
    omega
  have hthetaK : theta / 2 * (K : ℝ) ≤ theta * (N : ℝ) / (H1 : ℝ) := by
    have hKle' : (K : ℝ) ≤ 2 * (N / H1 : ℕ) := by exact_mod_cast hKle
    have hdivcast : ((N / H1 : ℕ) : ℝ) ≤ (N : ℝ) / (H1 : ℝ) := by
      exact Nat.cast_div_le
    calc
      theta / 2 * (K : ℝ) ≤ theta / 2 * (2 * (N / H1 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hKle' (by positivity)
      _ = theta * ((N / H1 : ℕ) : ℝ) := by ring
      _ ≤ theta * (N : ℝ) / (H1 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hdivcast htheta.le
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hdata : ∀ i : Fin K, relevant i →
      kval i ≤ N ∧ m0 ≤ N - kval i ∧ m0 ≤ M - kval i := by
    intro i hi
    have hw := hwindow (kint i) hi.1 hi.2
    have hk0 : 0 ≤ kint i := hw.1
    have hklt : (kint i : ℝ) < (N : ℝ) := by
      have hbNlt : b * (N : ℝ) < (N : ℝ) := by
        have h := mul_lt_mul_of_pos_right hb hNpos
        simpa [mul_one] using h
      exact lt_of_le_of_lt hi.2 hbNlt
    have hkcastZ : (kval i : ℤ) = kint i := by
      dsimp [kval]
      exact Int.toNat_of_nonneg hk0
    have hklt' : kint i < (N : ℤ) := by exact_mod_cast hklt
    have hkn : kval i ≤ N := by omega
    exact ⟨hkn, hw.2.1, hw.2.2⟩
  have hvalid (i : Fin K) (hi : relevant i) : kval i ≤ N := (hdata i hi).1
  have hcutNvalid (i : Fin K) (hi : relevant i) : m0 ≤ N - kval i := (hdata i hi).2.1
  have hcutMvalid (i : Fin K) (hi : relevant i) : m0 ≤ M - kval i := (hdata i hi).2.2
  let WNpos : β → (i : Fin K) → relevant i → ℕ+ → Set (BilateralField d) :=
    fun w i hi => Classical.choose (hRegWitness N (kval i) (zval w i) (hvalid i hi))
  let WMpos : β → (i : Fin K) → relevant i → ℕ+ → Set (BilateralField d) :=
    fun w i hi => Classical.choose (hRegWitness M (kval i) (zval w i)
      ((hvalid i hi).trans hNM))
  let WTpos : β → (i : Fin K) → relevant i → ℕ+ → Set (BilateralField d) :=
    fun w i hi => Classical.choose (hTraceWitness N M (kval i) (zval w i)
      (hvalid i hi) ((hvalid i hi).trans hNM) (hcutNvalid i hi) (hcutMvalid i hi))
  have hWNspec (w : β) (i : Fin K) (hi : relevant i) :=
    Classical.choose_spec (hRegWitness N (kval i) (zval w i) (hvalid i hi))
  have hWMspec (w : β) (i : Fin K) (hi : relevant i) :=
    Classical.choose_spec (hRegWitness M (kval i) (zval w i)
      ((hvalid i hi).trans hNM))
  have hWTspec (w : β) (i : Fin K) (hi : relevant i) :=
    Classical.choose_spec (hTraceWitness N M (kval i) (zval w i)
      (hvalid i hi) ((hvalid i hi).trans hNM) (hcutNvalid i hi) (hcutMvalid i hi))
  let g : ℤ → BilateralField d → C(SpatialCoordinates d, ℝ) := fun j omega => omega j
  have hg : ∀ j : ℤ, Measurable (g j) := by
    intro j
    dsimp [g]
    exact measurable_pi_apply j
  have hgi : iIndepFun g (chaosSampleLaw model).toMeasure := by
    change iIndepFun (fun j : ℤ => fun omega : BilateralField d => omega j)
      (Measure.infinitePi
        (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) j :
          Measure C(SpatialCoordinates d, ℝ))))
    exact iIndepFun_infinitePi (fun _ => measurable_id)
  have hnidx : ∀ w : β, Function.Injective (fun i : Fin K => kint i) := by
    intro w i j hij
    apply Fin.ext
    have hmul : (H1 : ℤ) * (i.val : ℤ) = (H1 : ℤ) * (j.val : ℤ) := by
      change (H1 : ℤ) * (i.val : ℤ) - jroot =
        (H1 : ℤ) * (j.val : ℤ) - jroot at hij
      exact sub_left_injective hij
    have hH1z : (H1 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH1)
    have hc : (i.val : ℤ) = (j.val : ℤ) := mul_left_cancel₀ hH1z hmul
    exact_mod_cast hc
  let WU : β → Fin K → ℕ+ → Set (BilateralField d) := fun w i h =>
    if hi : relevant i then WNpos w i hi h ∪ (WMpos w i hi h ∪ WTpos w i hi h) else ∅
  have hUmeas : ∀ (w : β) (i : Fin K) (h : ℕ+),
      MeasurableSet[
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (kint i - (h : ℤ))
          (kint i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j))
            (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)))]
        (WU w i h) := by
    intro w i h
    by_cases hi : relevant i
    · dsimp [WU]
      rw [dite_eq_left hi]
      have hk0 : 0 ≤ kint i := (hwindow (kint i) hi.1 hi.2).1
      have hkcastZ : (kval i : ℤ) = kint i := by
        dsimp [kval]
        exact Int.toNat_of_nonneg hk0
      change MeasurableSet[
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (kint i - (h : ℤ))
          (kint i + 2 * (h : ℤ))),
          MeasurableSpace.comap (fun omega : BilateralField d => omega (-j))
            (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)))]
        (WNpos w i hi h ∪ (WMpos w i hi h ∪ WTpos w i hi h))
      rw [aux_finite_interval_packing_sigma (kint i) h]
      rw [← hkcastZ]
      change @MeasurableSet (BilateralField d)
        (MeasurableSpace.comap
          ((Set.Icc (-(kval i : ℤ) - 2 * (h : ℤ))
            (-(kval i : ℤ) + (h : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((j : Set.Icc (-(kval i : ℤ) - 2 * (h : ℤ))
              (-(kval i : ℤ) + (h : ℤ))) → C(SpatialCoordinates d, ℝ))))
        (WNpos w i hi h ∪ (WMpos w i hi h ∪ WTpos w i hi h))
      exact ((hWNspec w i hi).1 h).union ((hWMspec w i hi).1 h |>.union ((hWTspec w i hi).1 h))
    · dsimp [WU]
      simp only [dite_eq_right hi, MeasurableSet.empty]
  have hUprob : ∀ (w : β) (i : Fin K) (h : ℕ+),
      (chaosSampleLaw model).toMeasure (WU w i h) ≤
        ENNReal.ofReal (Real.exp (-(B / 2) * (h : ℝ))) := by
    intro w i h
    by_cases hi : relevant i
    · dsimp [WU]
      rw [dite_eq_left hi]
      exact aux_finite_interval_packing_three_rate
        (chaosSampleLaw model).toMeasure (WNpos w i hi h)
          (WMpos w i hi h) (WTpos w i hi h) B hB4 h
          ((hWNspec w i hi).2.1 h) ((hWMspec w i hi).2.1 h)
          ((hWTspec w i hi).2.1 h)
    · simp [WU, hi]
  let failure : β → Fin K → Set (BilateralField d) := fun w i => ⋃ h : ℕ+, WU w i h
  have hfailure : ∀ (w : β) (i : Fin K),
      failure w i ⊆ ⋃ h : ℕ+, WU w i h := by intro w i; exact Subset.rfl
  have hEprob := SubdiffusiveProcess.union_bound_finitely_many_bad_branches
    (J := K) (A := B / 2) (θ := theta / 2) (by linarith [hB4])
    (by positivity) (by nlinarith [htheta, hthetab, hab, hb])
    (BilateralField d) (C(SpatialCoordinates d, ℝ)) (chaosSampleLaw model).toMeasure
    g hg hgi (fun _ i => kint i) hnidx failure WU hUmeas hUprob hfailure
  have hcoverAE : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
      ∀ w : β, ∀ i : Fin K, ∀ hi : relevant i,
        (¬Reg N (kval i) (zval w i) omega → omega ∈ ⋃ h : ℕ+, WNpos w i hi h) ∧
        (¬Reg M (kval i) (zval w i) omega → omega ∈ ⋃ h : ℕ+, WMpos w i hi h) ∧
        (¬TraceClose N M (kval i) (zval w i) omega →
          omega ∈ ⋃ h : ℕ+, WTpos w i hi h) := by
    apply ae_all_iff.mpr
    intro w
    apply ae_all_iff.mpr
    intro i
    by_cases hi : relevant i
    · filter_upwards [(hWNspec w i hi).2.2, (hWMspec w i hi).2.2,
        (hWTspec w i hi).2.2] with omega hN hM hT
      exact fun _ => ⟨hN, hM, hT⟩
    · exact Filter.Eventually.of_forall (fun omega hi' => (hi hi').elim)
  let Good : BilateralField d → Prop := fun omega =>
    ∀ w : β, ∀ i : Fin K, ∀ hi : relevant i,
      (¬Reg N (kval i) (zval w i) omega → omega ∈ ⋃ h : ℕ+, WNpos w i hi h) ∧
      (¬Reg M (kval i) (zval w i) omega → omega ∈ ⋃ h : ℕ+, WMpos w i hi h) ∧
      (¬TraceClose N M (kval i) (zval w i) omega →
        omega ∈ ⋃ h : ℕ+, WTpos w i hi h)
  let Null : Set (BilateralField d) := {omega | ¬Good omega}
  have hNull : (chaosSampleLaw model).toMeasure Null = 0 := by
    apply ae_iff.mp
    simpa [Null, Good] using hcoverAE
  let E : Set (BilateralField d) := {omega | ∃ w : β,
    theta / 2 * (K : ℝ) ≤
      (Set.ncard {i : Fin K | omega ∈ failure w i} : ℝ)}
  have hEprob' : (chaosSampleLaw model).toMeasure E ≤
      (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-q * (K : ℝ))) := by
    change (chaosSampleLaw model).toMeasure
      {omega | ∃ w : β, theta / 2 * (K : ℝ) ≤
        (Set.ncard {i : Fin K | omega ∈ failure w i} : ℝ)} ≤ _
    convert hEprob using 1 ; dsimp [q] ; ring
  have hgap : 0 < q - (H1 : ℝ) * (d : ℝ) * Real.log 3 := by
    apply sub_pos.mpr
    simpa using hqentropy
  have hcardreal : (Fintype.card β : ℝ) =
      Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ)) := by
    change (Fintype.card (Fin K → OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) = _
    calc
      (Fintype.card (Fin K → OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) =
          Real.exp ((H1 : ℝ) * (d : ℝ) * (K : ℝ) * Real.log 3) :=
        aux_finite_interval_packing_word_card d H1 K
      _ = Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ)) :=
        congrArg Real.exp (aux_finite_interval_packing_exp_order d H1 K)
  have hcardenn : (Fintype.card β : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ))) := by
    calc
      (Fintype.card β : ℝ≥0∞) = ENNReal.ofReal (Fintype.card β : ℝ) := hcardβ
      _ = ENNReal.ofReal (Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ))) :=
        congrArg ENNReal.ofReal hcardreal
  have hprod : (Fintype.card β : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-q * (K : ℝ))) =
      ENNReal.ofReal (Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3 - q) * (K : ℝ))) := by
    rw [hcardenn]
    rw [← ENNReal.ofReal_mul
      (by positivity : 0 ≤ Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3) * (K : ℝ)))]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hcetaEq : ceta =
      (q - (H1 : ℝ) * (d : ℝ) * Real.log 3) /
        (2 * (H1 : ℝ) * Real.log 3) := by
    dsimp [ceta]
  have hCetaEq : Ceta =
      Real.exp (q - (H1 : ℝ) * (d : ℝ) * Real.log 3) := by
    dsimp [Ceta]
  have hnum : ENNReal.ofReal
      (Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3 - q) * (K : ℝ))) ≤
      ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    exact aux_finite_interval_packing_decay
      ((H1 : ℝ) * (d : ℝ) * Real.log 3) q ceta Ceta N K H1
      hH1 hKreal hgap hcetaEq hCetaEq
  let Bad : Set (BilateralField d) := toMeasurable
    (chaosSampleLaw model).toMeasure (E ∪ Null)
  have hBadprob : (chaosSampleLaw model).toMeasure Bad ≤
      ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) := by
    calc
      (chaosSampleLaw model).toMeasure Bad =
          (chaosSampleLaw model).toMeasure (E ∪ Null) := by
            dsimp [Bad]
            exact measure_toMeasurable _
      _ ≤ (chaosSampleLaw model).toMeasure E +
          (chaosSampleLaw model).toMeasure Null := measure_union_le _ _
      _ = (chaosSampleLaw model).toMeasure E := by rw [hNull, add_zero]
      _ ≤ (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-q * (K : ℝ))) := hEprob'
      _ = ENNReal.ofReal (Real.exp (((H1 : ℝ) * (d : ℝ) * Real.log 3 - q) * (K : ℝ))) := hprod
      _ ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) := hnum
  refine ⟨Bad, measurableSet_toMeasurable _ _, hBadprob, ?_⟩
  have hsubset : E ∪ Null ⊆ Bad := subset_toMeasurable _ _
  intro omega hnot w
  have hGood : Good omega := by
    by_contra hbad
    exact hnot (hsubset (Or.inr hbad))
  dsimp [Good] at hGood
  let kN : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - jroot
  let zN : ℕ → SpatialCoordinates d := fun n =>
    descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ jroot) n
      (fun i => w i)
  let bw : β := fun i => w i.val
  let T : Set ℕ := {n | a * (N : ℝ) ≤ (kN n : ℝ) ∧
      (kN n : ℝ) ≤ b * (N : ℝ) ∧
      ¬(Reg N (kN n).toNat (zN n) omega ∧
        Reg M (kN n).toNat (zN n) omega ∧
        TraceClose N M (kN n).toNat (zN n) omega)}
  change (Nat.card {n : ℕ // n ∈ T} : ℝ) ≤ theta * (N : ℝ) / (H1 : ℝ)
  let S : Set (Fin K) := {i | omega ∈ failure bw i}
  have hnotE : omega ∉ E := by
    intro hE
    exact hnot (hsubset (Or.inl hE))
  have hSlt : (Set.ncard S : ℝ) < theta / 2 * (K : ℝ) := by
    apply lt_of_not_ge
    intro hge
    apply hnotE
    exact ⟨bw, by simpa [E, S] using hge⟩
  have hdepth : ∀ n : ℕ, n ∈ T → n < K := by
    intro n hn
    apply aux_finite_interval_packing_depth_bound H1 N hH1 jroot n
    have hbNlt : b * (N : ℝ) < (N : ℝ) := by
      have h := mul_lt_mul_of_pos_right hb hNpos
      simpa [mul_one] using h
    have hklt : (kN n : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt hn.2.1 hbNlt
    exact_mod_cast hklt
  have hmem : ∀ n : ℕ, ∀ hn : n ∈ T,
      (⟨n, hdepth n hn⟩ : Fin K) ∈ S := by
    intro n hn
    let i : Fin K := ⟨n, hdepth n hn⟩
    have hrel : relevant i := by
      dsimp [relevant, kint, i]
      exact ⟨hn.1, hn.2.1⟩
    have hk0 : 0 ≤ kN n := (hwindow (kN n) hn.1 hn.2.1).1
    have hkcast : (kval i : ℤ) = kN n := by
      dsimp [kval, kN, i]
      exact Int.toNat_of_nonneg hk0
    have hfail : ¬(Reg N (kval i) (zval bw i) omega ∧
        Reg M (kval i) (zval bw i) omega ∧
        TraceClose N M (kval i) (zval bw i) omega) := by
      simpa [T, zN, zval, i, hkcast] using hn.2.2
    have hcover : omega ∈ failure bw i := by
      have hg := hGood bw i hrel
      have hu : omega ∈
          (⋃ h : ℕ+, WNpos bw i hrel h) ∪
            ((⋃ h : ℕ+, WMpos bw i hrel h) ∪ (⋃ h : ℕ+, WTpos bw i hrel h)) := by
        by_cases hN : Reg N (kval i) (zval bw i) omega
        · by_cases hM : Reg M (kval i) (zval bw i) omega
          · by_cases hT : TraceClose N M (kval i) (zval bw i) omega
            · exact (hfail ⟨hN, hM, hT⟩).elim
            · exact Or.inr (Or.inr (hg.2.2 hT))
          · exact Or.inr (Or.inl (hg.2.1 hM))
        · exact Or.inl (hg.1 hN)
      rw [show failure bw i = ⋃ h : ℕ+, WU bw i h by rfl]
      rcases hu with hu | hu
      · rcases Set.mem_iUnion.1 hu with ⟨h, hh⟩
        exact Set.mem_iUnion.2 ⟨h, by simpa [WU, hrel] using Or.inl hh⟩
      · rcases hu with hu | hu
        · rcases Set.mem_iUnion.1 hu with ⟨h, hh⟩
          exact Set.mem_iUnion.2 ⟨h, by simpa [WU, hrel] using Or.inr (Or.inl hh)⟩
        · rcases Set.mem_iUnion.1 hu with ⟨h, hh⟩
          exact Set.mem_iUnion.2 ⟨h, by simpa [WU, hrel] using Or.inr (Or.inr hh)⟩
    exact hcover
  let f : {n // n ∈ T} → {i // i ∈ S} := fun n =>
    ⟨⟨n.1, hdepth n.1 n.2⟩, hmem n.1 n.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : {i // i ∈ S} => z.val.val) hxy
  have hcardNat : Nat.card {n // n ∈ T} ≤ Nat.card {i // i ∈ S} :=
    Nat.card_le_card_of_injective f hf
  have hcardReal : (Nat.card {n // n ∈ T} : ℝ) ≤ (Set.ncard S : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_coe_set_eq] using hcardNat)
  have hcardT : (Nat.card {n // n ∈ T} : ℝ) < theta / 2 * (K : ℝ) :=
    hcardReal.trans_lt hSlt
  exact (le_of_lt hcardT).trans hthetaK

end SubdiffusiveProcess.Paper
