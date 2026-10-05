module

public import SubdiffusiveProcess.MacroAllCube.AhomDilationLaw
public import SubdiffusiveProcess.MacroAllCube.AhomDilationGlue
public import SubdiffusiveProcess.MacroAllCube.AhomDilationGrid

@[expose] public section

/-!
# Covariance of `ahom` under a spatial dilation of the seed law

**Theorem (`ahom_eq_of_seed`).**  Let `M, M'` be GMC models and `t > 0` with

```text
zeroPotentialLaw M'.P = (zeroPotentialLaw M.P) ∘ (spatialScale t)⁻¹ .
```

Then `ahom M' n = ahom M n` for every cutoff `n`.

This is the infinite-volume covariance of the homogenized coefficient under a
fixed (possibly non-triadic) spatial dilation.  The seed law is *not* assumed
dilation invariant, and nothing about `ahom` beyond its frozen `sInf`
definition is used.

## Proof

`ahom M n ≤ ahom M' n` (the reverse follows with `(M', M, t⁻¹)`):

1. Fix scales `l` (for `M'`) and `m` (for `M`), put `L = 3^m`, `h = t 3^l`, and
   assume `2h ≤ L`.  The grid boxes of side `h` inside `(-L/2, L/2)^d` are the
   dilated triadic cubes `t • Q_k`, `Q_k = ⟨l, k⟩`.
2. Pointwise in the sample, glue ε-minimizers on the boxes and use the affine
   function elsewhere (`dirichletInfOn_le_sum_add_remainder`).
3. Take expectations.  On `t • Q_k` the `M` field has the law of the `M'` field
   on `Q_k` (`map_dilateSample`, `dirFun_smul`), so each box contributes
   `h^d r'_l`, where `r'_l` is the triadic readout of `M'`.  The remainder
   contributes its volume, since the cutoff has mean one.
4. With `N` boxes: `L^d r_m ≤ N h^d r'_l + (L^d - N h^d)`.  Since
   `N h^d ≥ (L - 2h)^d` and `0 ≤ r'_l ≤ 1`, we get `r_m ≤ r'_l + 2dh/L`.
5. `ahom M n ≤ r_m`; letting `m → ∞` gives `ahom M n ≤ r'_l` for every `l`,
   hence `ahom M n ≤ inf_l r'_l = ahom M' n`.
-/

open MeasureTheory ProbabilityTheory Set Homogenization.Book Function
open Homogenization hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped Pointwise

noncomputable section

namespace SubdiffusiveProcess.AhomDilation

variable {d : ℕ}

theorem ahom_le_abarScalarReadout (M : GMCModel d) (n m : ℕ) :
    ahom M n ≤ abarScalarReadout M n m := by
  unfold ahom
  exact csInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact abarScalarReadout_nonneg M n k⟩ ⟨m, rfl⟩

theorem vecNormSq_single (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  rw [vecNormSq, vecDot_single_left]
  simp

/-- **One comparison step at fixed scales.** -/
theorem readout_le_readout_add (M M' : GMCModel d) {t : ℝ} (ht : 0 < t)
    (hmap : Measure.map (dilateSample t) M.P.toMeasure = M'.P.toMeasure)
    (htau : tauSq M'.P = tauSq M.P) (n m l : ℕ)
    (hLh : 2 * (t * (3 : ℝ) ^ l) ≤ (3 : ℝ) ^ m) :
    abarScalarReadout M n m ≤
      abarScalarReadout M' n l + 2 * d * (t * (3 : ℝ) ^ l) / (3 : ℝ) ^ m := by
  set L : ℝ := (3 : ℝ) ^ m with hLdef
  set h : ℝ := t * (3 : ℝ) ^ l with hhdef
  set S := gridIndex d L h with hSdef
  set R : Set (Vec d) := centerBox L \ ⋃ k ∈ S, gridBox h k with hRdef
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  set i0 : Fin d := ⟨0, hd⟩
  set e : Vec d := Pi.single i0 1 with hedef
  have he : vecNormSq e = 1 := vecNormSq_single i0
  have hh : 0 < h := by positivity
  have hL : 0 < L := by positivity
  have hC : centerBox (d := d) L = openCubeSet (originCube d (m : ℤ)) :=
    centerBox_eq_openCubeSet m
  have hCb : Bornology.IsBounded (centerBox (d := d) L) := by
    rw [hC]; exact isBounded_openCubeSet _
  have hRfin : volume R < ⊤ := volume_centerBox_diff_lt_top L h
  -- 1. pointwise gluing
  have hpt : ∀ ω, dirFun M n (centerBox L) e ω ≤
      (∑ k ∈ S, dirFun M n (gridBox h k) e ω) + ∫ x in R, aCutoff M n ω x := by
    intro ω
    have hglue := dirichletInfOn_le_sum_add_remainder (continuous_aCutoff M n ω)
      (fun x => (aCutoff_pos M n ω x).le) (isOpen_centerBox L) hCb S
      (fun k => measurableSet_gridBox h k) (fun k hk => gridBox_subset_centerBox hh hk)
      (fun k _ k' _ hkk' => pairwise_disjoint_gridBox hh hkk') e
    simp only [he, mul_one] at hglue
    exact hglue
  -- 2. integrability of the pieces
  have hcell : ∀ k : Fin d → ℤ, gridBox h k = t • openCubeSet (⟨(l : ℤ), k⟩ : TriadicCube d) :=
    fun k => gridBox_eq_smul_openCubeSet ht l k
  have hint_cells : ∀ k ∈ S, Integrable (dirFun M n (gridBox h k) e) M.P.toMeasure := by
    intro k _
    rw [hcell k]
    exact integrable_dirFun_smul_cube ht hmap htau n _ e
  have hint_rem := integrable_setIntegral_aCutoff M n hRfin
  have hG : Integrable (fun ω => (∑ k ∈ S, dirFun M n (gridBox h k) e ω) +
      ∫ x in R, aCutoff M n ω x) M.P.toMeasure :=
    (integrable_finsetSum S hint_cells).add hint_rem
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω =>
      dirFun_nonneg M n (isOpen_centerBox L).measurableSet e ω) hG
    (Filter.Eventually.of_forall hpt)
  -- 3. the three expectations
  have hLHS : ∫ ω, dirFun M n (centerBox L) e ω ∂M.P.toMeasure =
      L ^ d * abarScalarReadout M n m := by
    rw [hC, integral_dirFun_cube, ← hC, volume_centerBox hL.le,
      ENNReal.toReal_ofReal (by positivity)]
    congr 1
    exact quad_abar_single M n m 0 i0
  have hvolQ : ∀ k : Fin d → ℤ,
      (volume (openCubeSet (⟨(l : ℤ), k⟩ : TriadicCube d))).toReal = ((3 : ℝ) ^ l) ^ d := by
    intro k
    have h1 := gridBox_eq_smul_openCubeSet (d := d) one_pos l k
    rw [one_smul, one_mul] at h1
    rw [← h1, volume_gridBox (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hcellInt : ∀ k ∈ S, ∫ ω, dirFun M n (gridBox h k) e ω ∂M.P.toMeasure =
      h ^ d * abarScalarReadout M' n l := by
    intro k _
    rw [hcell k, integral_dirFun_smul_cube ht hmap htau n _ e, integral_dirFun_cube,
      hvolQ k, quad_abar_single M' n l k i0, hhdef, mul_pow]
    ring
  have hRHS : ∫ ω, ((∑ k ∈ S, dirFun M n (gridBox h k) e ω) +
      ∫ x in R, aCutoff M n ω x) ∂M.P.toMeasure =
      (S.card : ℝ) * h ^ d * abarScalarReadout M' n l +
        (L ^ d - (S.card : ℝ) * h ^ d) := by
    rw [integral_add (integrable_finsetSum S hint_cells) hint_rem,
      integral_finsetSum S hint_cells, Finset.sum_congr rfl hcellInt,
      integral_setIntegral_aCutoff M n hRfin, hRdef,
      volume_centerBox_diff_toReal hh hL.le, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hLHS, hRHS] at hmono
  -- 4. algebra
  set r := abarScalarReadout M n m
  set r' := abarScalarReadout M' n l
  set N : ℝ := (S.card : ℝ)
  have hr'0 : 0 ≤ r' := abarScalarReadout_nonneg M' n l
  have hr'1 : r' ≤ 1 := abarScalarReadout_le_one M' n l
  have hNh : (L - 2 * h) ^ d ≤ N * h ^ d := sub_pow_le_card_mul hh hLh
  have hLd : 0 < L ^ d := pow_pos hL d
  set q : ℝ := (L ^ d - (L - 2 * h) ^ d) / L ^ d with hqdef
  have hq : q ≤ 2 * d * h / L := one_sub_pow_le hh hLh
  have hq0 : 0 ≤ q := by
    apply div_nonneg _ hLd.le
    have : (L - 2 * h) ^ d ≤ L ^ d :=
      pow_le_pow_left₀ (by linarith) (by linarith) d
    linarith
  have hqL : L ^ d - (L - 2 * h) ^ d = q * L ^ d := by
    rw [hqdef]; field_simp
  have hkey : L ^ d * r ≤ L ^ d * (r' + q * (1 - r')) := by
    have h1 : (L - 2 * h) ^ d * (1 - r') ≤ N * h ^ d * (1 - r') :=
      mul_le_mul_of_nonneg_right hNh (by linarith)
    have h2 : L ^ d * (r' + q * (1 - r')) =
        L ^ d - (L - 2 * h) ^ d * (1 - r') := by
      have : L ^ d * (r' + q * (1 - r')) = L ^ d * r' + (q * L ^ d) * (1 - r') := by ring
      rw [this, ← hqL]; ring
    rw [h2]
    nlinarith
  have hr : r ≤ r' + q * (1 - r') := le_of_mul_le_mul_left hkey hLd
  have hq1 : q * (1 - r') ≤ q := by nlinarith
  linarith

/-- For every triadic scale `l` of `M'`, `ahom M n` is below the `M'` readout. -/
theorem ahom_le_readout (M M' : GMCModel d) {t : ℝ} (ht : 0 < t)
    (hmap : Measure.map (dilateSample t) M.P.toMeasure = M'.P.toMeasure)
    (htau : tauSq M'.P = tauSq M.P) (n l : ℕ) :
    ahom M n ≤ abarScalarReadout M' n l := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set h : ℝ := t * (3 : ℝ) ^ l
  have hh : 0 < h := by positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max (2 * h) (2 * d * h / ε))
    (by norm_num : (1 : ℝ) < 3)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hLh : 2 * h ≤ (3 : ℝ) ^ m := (le_max_left _ _).trans hm.le
  have hsmall : 2 * d * h / (3 : ℝ) ^ m < ε := by
    rw [div_lt_iff₀ h3]
    have h2 : 2 * d * h / ε < (3 : ℝ) ^ m := (le_max_right _ _).trans_lt hm
    rw [div_lt_iff₀ hε] at h2
    linarith
  calc ahom M n ≤ abarScalarReadout M n m := ahom_le_abarScalarReadout M n m
    _ ≤ abarScalarReadout M' n l + 2 * d * h / (3 : ℝ) ^ m :=
        readout_le_readout_add M M' ht hmap htau n m l hLh
    _ < abarScalarReadout M' n l + ε := by linarith

/-- **One direction of the covariance.** -/
theorem ahom_le_of_seed (M M' : GMCModel d) {t : ℝ} (ht : 0 < t)
    (hseed : (zeroPotentialLaw M'.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (zeroPotentialLaw M.P).toMeasure)
    (n : ℕ) : ahom M n ≤ ahom M' n := by
  have hmap := map_dilateSample hseed
  have htau := tauSq_eq_of_seed hseed
  show ahom M n ≤ sInf (Set.range (abarScalarReadout M' n))
  exact le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨l, rfl⟩
    exact ahom_le_readout M M' ht hmap htau n l)

/-- **Covariance of the homogenized coefficient under a seed dilation.** -/
theorem ahom_eq_of_seed (M M' : GMCModel d) {t : ℝ} (ht : 0 < t)
    (hseed : (zeroPotentialLaw M'.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (zeroPotentialLaw M.P).toMeasure)
    (n : ℕ) : ahom M' n = ahom M n :=
  le_antisymm (ahom_le_of_seed M' M (inv_pos.mpr ht) (seed_inv ht.ne' hseed) n)
    (ahom_le_of_seed M M' ht hseed n)

/-- The same statement with the seed identity at the level of probability
measures, literally as in `SubdiffusiveProcess.MacroAllCube.ResidualModelData.seed_eq`. -/
theorem ahom_eq_of_seed_eq (M M' : GMCModel d) {t : ℝ} (ht : 0 < t)
    (hseed : zeroPotentialLaw M'.P =
      (zeroPotentialLaw M.P).map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t))
    (n : ℕ) : ahom M' n = ahom M n := by
  refine ahom_eq_of_seed M M' ht ?_ n
  rw [hseed, ProbabilityMeasure.toMeasure_map]

end SubdiffusiveProcess.AhomDilation





