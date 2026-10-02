import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalPathConstruction
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalSeed




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set Finset
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The coordinatewise `ℓ∞` geodesic -/

/-- The coordinatewise `ℓ∞` geodesic from `v` to `w`: at time `t` every
coordinate has moved `t` steps towards its target, and then stops. -/
def latticeSeg (v w : Lattice d) (t : ℕ) : Lattice d :=
  fun i => if v i ≤ w i then min (v i + (t : ℤ)) (w i) else max (v i - (t : ℤ)) (w i)

@[simp]
theorem latticeSeg_zero (v w : Lattice d) : latticeSeg v w 0 = v := by
  funext i
  simp only [latticeSeg]
  split_ifs <;> omega

/-- The geodesic has arrived at `w` after `latticeDist v w` steps. -/
theorem latticeSeg_of_dist_le (v w : Lattice d) {t : ℕ} (ht : latticeDist v w ≤ t) :
    latticeSeg v w t = w := by
  funext i
  have h := latticeDist_le_iff.mp ht i
  have hz : |(v i - w i : ℤ)| ≤ (t : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  rw [abs_le] at hz
  simp only [latticeSeg]
  split_ifs <;> omega

/-- Consecutive geodesic sites are `*`-adjacent. -/
theorem latticeDist_latticeSeg_succ (v w : Lattice d) (t : ℕ) :
    latticeDist (latticeSeg v w t) (latticeSeg v w (t + 1)) ≤ 1 := by
  rw [latticeDist_le_iff]
  intro i
  simp only [latticeSeg]
  push_cast
  split_ifs <;> omega

/-- Every geodesic site is coordinatewise between the endpoints. -/
theorem latticeSeg_between (v w : Lattice d) (t : ℕ) (i : Fin d) :
    min (v i) (w i) ≤ latticeSeg v w t i ∧ latticeSeg v w t i ≤ max (v i) (w i) := by
  simp only [latticeSeg]
  split_ifs <;> omega

/-- The geodesic stays in every `ℓ∞` ball containing both endpoints. -/
theorem latticeDist_latticeSeg_le {z v w : Lattice d} {L : ℕ}
    (hv : latticeDist z v ≤ L) (hw : latticeDist z w ≤ L) (t : ℕ) :
    latticeDist z (latticeSeg v w t) ≤ L := by
  rw [latticeDist_le_iff]
  intro i
  have hvi := latticeDist_le_iff.mp hv i
  have hwi := latticeDist_le_iff.mp hw i
  have hbet := latticeSeg_between v w t i
  have hvz : |(z i - v i : ℤ)| ≤ (L : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hvi
  have hwz : |(z i - w i : ℤ)| ≤ (L : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hwi
  rw [abs_le] at hvz hwz
  have : |(z i - latticeSeg v w t i : ℤ)| ≤ (L : ℤ) := by
    rw [abs_le]
    constructor <;> [skip; skip] <;> omega
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-! ## The ball/ball-radius dictionary -/

/-- A real-radius ball membership at a natural radius is the integer bound. -/
theorem latticeDist_le_of_inLatticeBallReal {z v : Lattice d} {L : ℕ}
    (h : InLatticeBallReal z v (L : ℝ)) : latticeDist z v ≤ L := by
  rw [latticeDist_le_iff]
  intro i
  have hi := h i
  have : ((|(v i - z i : ℤ)| : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by exact_mod_cast hi
  have hint : |(v i - z i : ℤ)| ≤ (L : ℤ) := by exact_mod_cast this
  rw [abs_le] at hint
  omega

/-! ## A fully good ball has no chemical-distance failure -/

/-- **Two-vertex links.**  Adjacent good sites form a good path of budget `2`. -/
theorem isShortGoodPath_link {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {a b : Lattice d} (hab : latticeDist a b ≤ 1)
    (ha : IsPercolationGoodSite E Cbox ω a) (hb : IsPercolationGoodSite E Cbox ω b) :
    IsShortGoodPath E Cbox ω 2 a b := by
  refine ⟨[a, b], rfl, rfl, by norm_num, ?_, ?_⟩
  · rw [isJStepListPath_iff_isChain]
    simpa using hab
  · intro u hu
    rcases List.mem_cons.mp hu with h | h
    · exact h ▸ ha
    · rw [List.mem_singleton] at h
      exact h ▸ hb

/-- **The geodesic is a short good path.**  If every site of the geodesic from
`v` to `w` is good, then `v` and `w` are joined by a good `1`-step path of at
most `2 * latticeDist v w` vertices (and at least one vertex). -/
theorem isShortGoodPath_of_latticeSeg_good {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {v w : Lattice d} {bound : ℝ}
    (hgood : ∀ t : ℕ, IsPercolationGoodSite E Cbox ω (latticeSeg v w t))
    (h1 : (1 : ℝ) ≤ bound) (h2 : 2 * (latticeDist v w : ℝ) ≤ bound) :
    IsShortGoodPath E Cbox ω bound v w := by
  set D := latticeDist v w with hD
  rcases Nat.eq_zero_or_pos D with hzero | hpos
  · have hvw : v = w := by
      have := latticeSeg_of_dist_le v w (t := 0) (by omega)
      simpa using this
    subst hvw
    exact isShortGoodPath_self h1 (by simpa using hgood 0)
  · have hlink : ∀ i, i < D →
        IsShortGoodPath E Cbox ω 2 (latticeSeg v w i) (latticeSeg v w (i + 1)) :=
      fun i _ => isShortGoodPath_link (latticeDist_latticeSeg_succ v w i)
        (hgood i) (hgood (i + 1))
    have hpath := isShortGoodPath_of_waypoints (latticeSeg v w) D hpos hlink
    rw [latticeSeg_zero, latticeSeg_of_dist_le v w (le_refl D)] at hpath
    exact hpath.mono (by linarith)

/-- **The deterministic small-radius step.**  A ball all of whose sites are good
carries no chemical-distance failure, as soon as the length budget `Clen * L`
dominates `2 * (2 L)`. -/
theorem not_mem_chemicalDistanceFailureEvent_of_ball_good
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d} {ω : Ω}
    {L : ℕ} (hL : 1 ≤ L) (hClen : 4 ≤ Clen)
    (hgood : ∀ u : Lattice d, latticeDist z u ≤ L → IsPercolationGoodSite E Cbox ω u) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z L := by
  rintro ⟨v, w, hv, hw, -, -, hno⟩
  have hvd : latticeDist z v ≤ L := latticeDist_le_of_inLatticeBallReal hv
  have hwd : latticeDist z w ≤ L := latticeDist_le_of_inLatticeBallReal hw
  have hseg : ∀ t : ℕ, IsPercolationGoodSite E Cbox ω (latticeSeg v w t) :=
    fun t => hgood _ (latticeDist_latticeSeg_le hvd hwd t)
  have hD : latticeDist v w ≤ 2 * L := by
    calc latticeDist v w ≤ latticeDist v z + latticeDist z w := latticeDist_triangle _ _ _
      _ ≤ L + L := by
          rw [latticeDist_comm v z]
          exact Nat.add_le_add hvd hwd
      _ = 2 * L := by ring
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hDR : ((latticeDist v w : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hD
  refine hno (isShortGoodPath_of_latticeSeg_good hseg ?_ ?_)
  · nlinarith
  · nlinarith

/-- **The seed inclusion.**  A chemical-distance failure at radius `L` forces a
bad site in the ball `B_L(z)`. -/
theorem chemicalDistanceFailureEvent_subset_biUnion_percolationBadSite
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d} {L : ℕ}
    (hL : 1 ≤ L) (hClen : 4 ≤ Clen) :
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆
      ⋃ u ∈ latticeBallFinset z L, percolationBadSite E Cbox u := by
  intro ω hω
  by_contra hnot
  refine not_mem_chemicalDistanceFailureEvent_of_ball_good hL hClen ?_ hω
  intro u hu
  by_contra hbad
  exact hnot (mem_biUnion (mem_latticeBallFinset_iff.mpr hu) hbad)

/-! ## The small-radius bound -/

/-- `L < e` and `1 ≤ L` pin the natural radius to `1` or `2`. -/
theorem le_two_of_lt_exp_one {L : ℕ} (h : (L : ℝ) < Real.exp 1) : L ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  have h3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcon
  have := Real.exp_one_lt_d9
  linarith

/-- At a radius `1 ≤ L ≤ 2` the exponent `(log L) ^ 2` is at most `1`. -/
theorem log_sq_le_one {L : ℕ} (hL : 1 ≤ L) (hL2 : L ≤ 2) : Real.log L ^ 2 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h2 : (L : ℝ) ≤ 2 := by exact_mod_cast hL2
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg h1
  have hlog2 : Real.log L ≤ Real.log 2 := Real.log_le_log (by linarith) h2
  have hlt : Real.log 2 < 1 := by
    have h := Real.exp_one_gt_d9
    have : (2 : ℝ) < Real.exp 1 := by linarith
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) this
      _ = 1 := Real.log_exp 1
  nlinarith



theorem smallRadiusBound_of_multiscaleEventProbability [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {Clen c Cfail Cprob cprob q : ℝ}
    (hCbox : 1 ≤ Cbox) (hClen : 4 ≤ Clen) (hCprob : 0 ≤ Cprob)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hccprob : c ≤ cprob) (hA : 0 ≤ cprob * q)
    (hqent : Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q)
    (hE : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hCfail : ((5 : ℝ) ^ d) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) ≤ Cfail) :
    SmallRadiusBound mu E Cbox Clen c Cfail q := by
  intro z L hL hLe
  have hL2 : L ≤ 2 := le_two_of_lt_exp_one hLe
  set B : ℝ := 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)) with hB
  have hbad : ∀ u : Lattice d,
      mu (percolationBadSite E Cbox u) ≤ ENNReal.ofReal B :=
    fun u => measure_percolationBadSite_le mu hCbox hCprob hA hqent hE u
  have hstep := measure_seedFailure_le mu
    (Seed := chemicalDistanceFailureEvent E Cbox Clen z L)
    (F := latticeBallFinset z L)
    (chemicalDistanceFailureEvent_subset_biUnion_percolationBadSite hL hClen) hbad
  refine hstep.trans ?_
  rw [card_latticeBallFinset, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcount : (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (5 : ℝ) ^ d := by
    have : ((2 * L + 1 : ℕ) : ℝ) ≤ 5 := by
      have : (L : ℝ) ≤ 2 := by exact_mod_cast hL2
      push_cast
      linarith
    calc (((2 * L + 1) ^ d : ℕ) : ℝ) = ((2 * L + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
      _ ≤ (5 : ℝ) ^ d := by
          refine pow_le_pow_left₀ (by positivity) this d
  have hBnn : 0 ≤ B := by
    rw [hB]; positivity
  have hexp : Real.exp (-(cprob * q)) ≤ Real.exp (-c * q * Real.log L ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hsq := log_sq_le_one hL hL2
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    nlinarith [mul_nonneg hc hq, sq_nonneg (Real.log L)]
  have hCp : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) := by positivity
  calc (((2 * L + 1) ^ d : ℕ) : ℝ) * B
      ≤ (5 : ℝ) ^ d * B := by
        exact mul_le_mul_of_nonneg_right hcount hBnn
    _ = (5 : ℝ) ^ d * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) *
          Real.exp (-(cprob * q)) := by rw [hB]; ring
    _ ≤ Cfail * Real.exp (-(cprob * q)) := by
        exact mul_le_mul_of_nonneg_right hCfail (Real.exp_pos _).le
    _ ≤ Cfail * Real.exp (-c * q * Real.log L ^ 2) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        have : (0 : ℝ) ≤ (5 : ℝ) ^ d * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) := by
          positivity
        linarith


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
