module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section AuxFileTransport
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise



section Transport
open Homogenization

/-- Undilate an `a`-harmonic function on `t • U` to an `a (t • ·)`-harmonic function on `U`. -/
def aux_lane4_lambda_inv_cell_moment_undilateHarmonic {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {t : ℝ} (ht : 0 < t) (u : AHarmonicFunction a (t • U)) :
    AHarmonicFunction (fun y => a (t • y)) U where
  toH1 := u.toH1.undilateSet ht rfl
  isHarmonic := by
    refine ⟨(u.toH1.undilateSet ht rfl).isPotentialOn, ?_⟩
    have h := Homogenization.Book.Ch02.IsSolenoidalOn.undilateSet ht rfl u.isHarmonic.2
    simpa [H1Function.undilateSet_grad] using h

theorem aux_lane4_lambda_inv_cell_moment_volumeAverage_smul {d : ℕ} (U : Set (Vec d))
    {t : ℝ} (ht : 0 < t) (f : Vec d → ℝ) :
    volumeAverage (t • U) f = volumeAverage U (fun y => f (t • y)) := by
  unfold volumeAverage
  have hfin : Module.finrank ℝ (Vec d) = d := Module.finrank_fin_fun ℝ
  rw [Measure.setIntegral_comp_smul_of_pos volume f U ht, Measure.addHaar_smul, hfin,
    abs_of_pos (pow_pos ht d), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, mul_inv]
  ring

theorem aux_lane4_lambda_inv_cell_moment_valueSet_smul_subset {d : ℕ} (U : Set (Vec d))
    {t : ℝ} (ht : 0 < t) (p q : Vec d) (a : CoeffField d) :
    responseJValueSet (t • U) p q a ⊆ responseJValueSet U p q (fun y => a (t • y)) := by
  rintro m ⟨u, rfl⟩
  refine ⟨aux_lane4_lambda_inv_cell_moment_undilateHarmonic ht u, ?_⟩
  rw [aux_lane4_lambda_inv_cell_moment_volumeAverage_smul U ht]
  congr 1
  funext y
  simp [scalarResponseIntegrand, aux_lane4_lambda_inv_cell_moment_undilateHarmonic,
    H1Function.undilateSet_grad]

theorem aux_lane4_lambda_inv_cell_moment_valueSet_smul {d : ℕ} (U : Set (Vec d))
    {t : ℝ} (ht : 0 < t) (p q : Vec d) (a : CoeffField d) :
    responseJValueSet (t • U) p q a = responseJValueSet U p q (fun y => a (t • y)) := by
  refine Set.Subset.antisymm
    (aux_lane4_lambda_inv_cell_moment_valueSet_smul_subset U ht p q a) ?_
  have h := aux_lane4_lambda_inv_cell_moment_valueSet_smul_subset (t • U) (inv_pos.mpr ht) p q
    (fun y => a (t • y))
  have hU : t⁻¹ • t • U = U := inv_smul_smul₀ ht.ne' U
  have ha : (fun y => (fun y => a (t • y)) (t⁻¹ • y)) = a := by
    funext y
    simp [smul_smul, ht.ne']
  rw [hU, ha] at h
  exact h

/-- Real dilations preserve the variational response. -/
theorem aux_lane4_lambda_inv_cell_moment_ResponseJ_smul {d : ℕ} (U : Set (Vec d))
    {t : ℝ} (ht : 0 < t) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (t • U) p q a = ResponseJ U p q (fun y => a (t • y)) := by
  rw [ResponseJ, ResponseJ, aux_lane4_lambda_inv_cell_moment_valueSet_smul U ht p q a]

/-- Translation followed by dilation: the response on `p + t • U`. -/
theorem aux_lane4_lambda_inv_cell_moment_ResponseJ_affine {d : ℕ} (U : Set (Vec d))
    (c : Vec d) {t : ℝ} (ht : 0 < t) (p q : Vec d) (a : CoeffField d) :
    ResponseJ (translateSet c (t • U)) p q a =
      ResponseJ U p q (fun y => a (t • y + c)) := by
  rw [ResponseJ_translateSet_eq_translateCoeffField,
    aux_lane4_lambda_inv_cell_moment_ResponseJ_smul U ht]
  rfl

/-- The response depends on the coefficient only almost everywhere on the domain. -/
theorem aux_lane4_lambda_inv_cell_moment_ResponseJ_congr_ae {d : ℕ} (U : Set (Vec d))
    (p q : Vec d) {a b : CoeffField d} (hab : a =ᵐ[volume.restrict U] b) :
    ResponseJ U p q a = ResponseJ U p q b := by
  have hsub : ∀ {a b : CoeffField d}, a =ᵐ[volume.restrict U] b →
      responseJValueSet U p q a ⊆ responseJValueSet U p q b := by
    intro a b hab
    rintro m ⟨u, rfl⟩
    refine ⟨⟨u.toH1, IsAHarmonicGradient.of_ae_eq_coeff hab u.isHarmonic⟩, ?_⟩
    unfold volumeAverage
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hab] with x hx
    simp only [scalarResponseIntegrand, hx]
  rw [ResponseJ, ResponseJ, Set.Subset.antisymm (hsub hab) (hsub hab.symm)]

/-- Pointwise maximization of the response integrand for a scalar coefficient. -/
theorem aux_lane4_lambda_inv_cell_moment_quad_le {d : ℕ} (s : ℝ) (hs : 0 < s)
    (q ξ : Vec d) :
    -((1 / 2 : ℝ) * vecDot ξ (matVecMul (symmPart (scalarMatrix (d := d) s)) ξ)) -
        vecDot (0 : Vec d) (matVecMul (scalarMatrix (d := d) s) ξ) + vecDot q ξ ≤
      vecNormSq q / (2 * s) := by
  have hsymm : symmPart (scalarMatrix (d := d) s) = scalarMatrix (d := d) s := by
    funext i j
    simp only [symmPart, scalarMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hsymm, matVecMul_scalarMatrix]
  simp only [vecDot, vecNormSq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (s * ξ i - q i)]

/-- For a scalar coefficient bounded below by `B⁻¹` on `U`, the flux response at a unit
vector is at most `B / 2`. -/
theorem aux_lane4_lambda_inv_cell_moment_ResponseJ_le {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) (a : CoeffField d) (s : Vec d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ x ∈ U, a x = scalarMatrix (s x)) (hs : ∀ x ∈ U, 0 < s x ∧ (s x)⁻¹ ≤ B)
    (q : Vec d) (hq : vecNormSq q = 1) :
    ResponseJ U 0 q a ≤ B / 2 := by
  apply Real.sSup_le _ (by positivity)
  rintro m ⟨u, rfl⟩
  have hpt : ∀ x ∈ U, scalarResponseIntegrand U a 0 q u x ≤ B / 2 := by
    intro x hx
    obtain ⟨hs0, hsB⟩ := hs x hx
    have h := aux_lane4_lambda_inv_cell_moment_quad_le (s x) hs0 q (u.toH1.grad x)
    rw [hq] at h
    have h2 : 1 / (2 * s x) ≤ B / 2 := by
      rw [one_div, mul_inv, inv_eq_one_div (2 : ℝ)]
      nlinarith
    simp only [scalarResponseIntegrand, ha x hx]
    linarith
  unfold volumeAverage
  rcases eq_or_ne (volume U).toReal 0 with h0 | h0
  · rw [h0, inv_zero, zero_mul]; positivity
  have hpos : 0 < (volume U).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
  have hfin : volume U < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    exact h0 (by simp [htop])
  by_cases hint : IntegrableOn (scalarResponseIntegrand U a 0 q u) U volume
  · have hle : ∫ x in U, scalarResponseIntegrand U a 0 q u x ∂volume ≤
        ∫ x in U, B / 2 ∂volume :=
      setIntegral_mono_on hint (integrableOn_const hfin.ne) hU hpt
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at hle
    calc (volume U).toReal⁻¹ * ∫ x in U, scalarResponseIntegrand U a 0 q u x ∂volume
        ≤ (volume U).toReal⁻¹ * ((volume U).toReal * (B / 2)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hpos.le)
      _ = B / 2 := by field_simp
  · rw [integral_undef hint, mul_zero]
    positivity

end Transport

end AuxFileTransport

section AuxFileWhitney
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators



section Whitney
open Homogenization

/-! ### An anchored multi-level (Whitney) partition of an open box

The box `a + (0,S)^d` is tiled from its corner by the level-`i` grids of mesh
`T_i = t0 / 3^i`.  Level `i` contributes the grid cubes inside `[0, K_i T_i)^d`
that are not inside `[0, K_{i-1} T_{i-1})^d`, where `K_i = ⌊S / T_i⌋`.  After
`m` levels the uncovered remainder is a boundary shell of width `< T_{m-1}`. -/

def aux_lane4_lambda_inv_cell_moment_wT (t0 : ℝ) (i : ℕ) : ℝ := t0 / 3 ^ i

def aux_lane4_lambda_inv_cell_moment_wK (S t0 : ℝ) (i : ℕ) : ℕ :=
  ⌊S / aux_lane4_lambda_inv_cell_moment_wT t0 i⌋₊

def aux_lane4_lambda_inv_cell_moment_wKp (S t0 : ℝ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 3 * aux_lane4_lambda_inv_cell_moment_wK S t0 i

def aux_lane4_lambda_inv_cell_moment_wLen (S t0 : ℝ) (i : ℕ) : ℝ :=
  (aux_lane4_lambda_inv_cell_moment_wK S t0 i : ℝ) * aux_lane4_lambda_inv_cell_moment_wT t0 i

def aux_lane4_lambda_inv_cell_moment_wBox (d K : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ => Finset.range K

def aux_lane4_lambda_inv_cell_moment_wD (d : ℕ) (S t0 : ℝ) (i : ℕ) : Finset (Fin d → ℕ) :=
  aux_lane4_lambda_inv_cell_moment_wBox d (aux_lane4_lambda_inv_cell_moment_wK S t0 i) \
    aux_lane4_lambda_inv_cell_moment_wBox d (aux_lane4_lambda_inv_cell_moment_wKp S t0 i)

def aux_lane4_lambda_inv_cell_moment_openBox {d : ℕ} (a : Vec d) (S : ℝ) : Set (Vec d) :=
  {x | ∀ k, a k < x k ∧ x k < a k + S}

def aux_lane4_lambda_inv_cell_moment_wPiece {d : ℕ} (a : Vec d) (t0 : ℝ) (i : ℕ)
    (j : Fin d → ℕ) : Set (Vec d) :=
  {x | ∀ k, a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * j k < x k ∧
    x k < a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * (j k + 1)}

def aux_lane4_lambda_inv_cell_moment_wCov {d : ℕ} (a : Vec d) (S t0 : ℝ) : ℕ → Set (Vec d)
  | 0 => ∅
  | m + 1 => {x | ∀ k, x k ≤ a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 m}

def aux_lane4_lambda_inv_cell_moment_wRem {d : ℕ} (a : Vec d) (S t0 : ℝ) (m : ℕ) :
    Set (Vec d) :=
  aux_lane4_lambda_inv_cell_moment_openBox a S \ aux_lane4_lambda_inv_cell_moment_wCov a S t0 m

theorem aux_lane4_lambda_inv_cell_moment_wT_pos {t0 : ℝ} (ht0 : 0 < t0) (i : ℕ) :
    0 < aux_lane4_lambda_inv_cell_moment_wT t0 i := by
  unfold aux_lane4_lambda_inv_cell_moment_wT; positivity

theorem aux_lane4_lambda_inv_cell_moment_wT_succ (t0 : ℝ) (i : ℕ) :
    aux_lane4_lambda_inv_cell_moment_wT t0 i =
      3 * aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) := by
  unfold aux_lane4_lambda_inv_cell_moment_wT
  rw [pow_succ]
  field_simp

theorem aux_lane4_lambda_inv_cell_moment_wK_succ (S t0 : ℝ) (i : ℕ) :
    aux_lane4_lambda_inv_cell_moment_wK S t0 i =
      aux_lane4_lambda_inv_cell_moment_wK S t0 (i + 1) / 3 := by
  unfold aux_lane4_lambda_inv_cell_moment_wK
  rw [aux_lane4_lambda_inv_cell_moment_wT_succ t0 i, ← Nat.floor_div_natCast]
  congr 1
  push_cast
  rw [div_div, mul_comm]

theorem aux_lane4_lambda_inv_cell_moment_wKp_le (S t0 : ℝ) (i : ℕ) :
    aux_lane4_lambda_inv_cell_moment_wKp S t0 i ≤ aux_lane4_lambda_inv_cell_moment_wK S t0 i := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
    simp only [aux_lane4_lambda_inv_cell_moment_wKp]
    rw [aux_lane4_lambda_inv_cell_moment_wK_succ S t0 i]
    exact Nat.mul_div_le _ 3

theorem aux_lane4_lambda_inv_cell_moment_wK_sub_wKp (S t0 : ℝ) (i : ℕ) :
    aux_lane4_lambda_inv_cell_moment_wK S t0 (i + 1) ≤
      aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1) + 2 := by
  simp only [aux_lane4_lambda_inv_cell_moment_wKp]
  rw [aux_lane4_lambda_inv_cell_moment_wK_succ S t0 i]
  have := Nat.div_add_mod (aux_lane4_lambda_inv_cell_moment_wK S t0 (i + 1)) 3
  have := Nat.mod_lt (aux_lane4_lambda_inv_cell_moment_wK S t0 (i + 1)) (by norm_num : 3 > 0)
  omega

theorem aux_lane4_lambda_inv_cell_moment_wLen_le {S t0 : ℝ} (hS : 0 ≤ S) (ht0 : 0 < t0)
    (i : ℕ) : aux_lane4_lambda_inv_cell_moment_wLen S t0 i ≤ S := by
  unfold aux_lane4_lambda_inv_cell_moment_wLen aux_lane4_lambda_inv_cell_moment_wK
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  have h := Nat.floor_le (div_nonneg hS hT.le)
  calc (⌊S / aux_lane4_lambda_inv_cell_moment_wT t0 i⌋₊ : ℝ) *
        aux_lane4_lambda_inv_cell_moment_wT t0 i
      ≤ S / aux_lane4_lambda_inv_cell_moment_wT t0 i * aux_lane4_lambda_inv_cell_moment_wT t0 i :=
        mul_le_mul_of_nonneg_right h hT.le
    _ = S := by field_simp

theorem aux_lane4_lambda_inv_cell_moment_lt_wLen_add {S t0 : ℝ} (ht0 : 0 < t0)
    (i : ℕ) : S < aux_lane4_lambda_inv_cell_moment_wLen S t0 i +
      aux_lane4_lambda_inv_cell_moment_wT t0 i := by
  unfold aux_lane4_lambda_inv_cell_moment_wLen aux_lane4_lambda_inv_cell_moment_wK
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  have h := Nat.lt_floor_add_one (S / aux_lane4_lambda_inv_cell_moment_wT t0 i)
  have h2 := mul_lt_mul_of_pos_right h hT
  rw [div_mul_cancel₀ _ hT.ne', add_mul, one_mul] at h2
  exact h2

theorem aux_lane4_lambda_inv_cell_moment_wKp_len (S t0 : ℝ) (i : ℕ) :
    (aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1) : ℝ) *
        aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) =
      aux_lane4_lambda_inv_cell_moment_wLen S t0 i := by
  simp only [aux_lane4_lambda_inv_cell_moment_wKp, aux_lane4_lambda_inv_cell_moment_wLen,
    aux_lane4_lambda_inv_cell_moment_wT_succ t0 i]
  push_cast
  ring

theorem aux_lane4_lambda_inv_cell_moment_wLen_succ (S t0 : ℝ) (ht0 : 0 < t0) (i : ℕ) :
    aux_lane4_lambda_inv_cell_moment_wLen S t0 i ≤ aux_lane4_lambda_inv_cell_moment_wLen S t0 (i + 1) := by
  rw [← aux_lane4_lambda_inv_cell_moment_wKp_len S t0 i]
  unfold aux_lane4_lambda_inv_cell_moment_wLen
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast aux_lane4_lambda_inv_cell_moment_wKp_le S t0 (i + 1))
    (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 (i + 1)).le

theorem aux_lane4_lambda_inv_cell_moment_wLen_mono (S t0 : ℝ) (ht0 : 0 < t0) {i i' : ℕ}
    (h : i ≤ i') :
    aux_lane4_lambda_inv_cell_moment_wLen S t0 i ≤ aux_lane4_lambda_inv_cell_moment_wLen S t0 i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (aux_lane4_lambda_inv_cell_moment_wLen_succ S t0 ht0 _)

theorem aux_lane4_lambda_inv_cell_moment_mem_wBox {d K : ℕ} {j : Fin d → ℕ} :
    j ∈ aux_lane4_lambda_inv_cell_moment_wBox d K ↔ ∀ k, j k < K := by
  simp [aux_lane4_lambda_inv_cell_moment_wBox, Fintype.mem_piFinset]

/-- Pieces of level `i` lie inside the level-`i` covered box. -/
theorem aux_lane4_lambda_inv_cell_moment_wPiece_lt {d : ℕ} {a : Vec d} {S t0 : ℝ}
    (ht0 : 0 < t0) {i : ℕ} {j : Fin d → ℕ}
    (hj : j ∈ aux_lane4_lambda_inv_cell_moment_wBox d (aux_lane4_lambda_inv_cell_moment_wK S t0 i))
    {x : Vec d} (hx : x ∈ aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) (k : Fin d) :
    a k < x k ∧ x k < a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  have hjk := aux_lane4_lambda_inv_cell_moment_mem_wBox.mp hj k
  have hjk' : ((j k : ℝ) + 1) ≤ aux_lane4_lambda_inv_cell_moment_wK S t0 i := by
    exact_mod_cast hjk
  obtain ⟨h1, h2⟩ := hx k
  constructor
  · have : 0 ≤ aux_lane4_lambda_inv_cell_moment_wT t0 i * j k := by positivity
    linarith
  · unfold aux_lane4_lambda_inv_cell_moment_wLen
    have := mul_le_mul_of_nonneg_left hjk' hT.le
    nlinarith

theorem aux_lane4_lambda_inv_cell_moment_wPiece_subset {d : ℕ} {a : Vec d} {S t0 : ℝ}
    (hS : 0 ≤ S) (ht0 : 0 < t0) {i : ℕ} {j : Fin d → ℕ}
    (hj : j ∈ aux_lane4_lambda_inv_cell_moment_wBox d (aux_lane4_lambda_inv_cell_moment_wK S t0 i)) :
    aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j ⊆
      aux_lane4_lambda_inv_cell_moment_openBox a S := by
  intro x hx k
  obtain ⟨h1, h2⟩ := aux_lane4_lambda_inv_cell_moment_wPiece_lt ht0 hj hx k
  exact ⟨h1, h2.trans_le (by linarith [aux_lane4_lambda_inv_cell_moment_wLen_le hS ht0 i])⟩

/-- A piece of level `i + 1` lies outside the level-`i` covered box. -/
theorem aux_lane4_lambda_inv_cell_moment_wPiece_outside {d : ℕ} {a : Vec d} {S t0 : ℝ}
    (ht0 : 0 < t0) {i : ℕ} {j : Fin d → ℕ}
    (hj : j ∉ aux_lane4_lambda_inv_cell_moment_wBox d (aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1)))
    {x : Vec d} (hx : x ∈ aux_lane4_lambda_inv_cell_moment_wPiece a t0 (i + 1) j) :
    ∃ k, a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i < x k := by
  rw [aux_lane4_lambda_inv_cell_moment_mem_wBox] at hj
  push Not at hj
  obtain ⟨k, hk⟩ := hj
  refine ⟨k, ?_⟩
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 (i + 1)
  have hk' : (aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1) : ℝ) ≤ j k := by exact_mod_cast hk
  rw [← aux_lane4_lambda_inv_cell_moment_wKp_len S t0 i]
  have := mul_le_mul_of_nonneg_right hk' hT.le
  have h1 := (hx k).1
  nlinarith

theorem aux_lane4_lambda_inv_cell_moment_wPiece_disjoint_same {d : ℕ} {a : Vec d} {t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) {j j' : Fin d → ℕ} (hjj : j ≠ j') :
    Disjoint (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j)
      (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hjj
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  obtain ⟨h1, h2⟩ := hx k
  obtain ⟨h1', h2'⟩ := hx' k
  rcases Nat.lt_or_gt_of_ne hk with hlt | hlt
  · have : ((j k : ℝ) + 1) ≤ j' k := by exact_mod_cast hlt
    have := mul_le_mul_of_nonneg_left this hT.le
    linarith
  · have : ((j' k : ℝ) + 1) ≤ j k := by exact_mod_cast hlt
    have := mul_le_mul_of_nonneg_left this hT.le
    linarith

theorem aux_lane4_lambda_inv_cell_moment_wPiece_disjoint_lt {d : ℕ} {a : Vec d} {S t0 : ℝ}
    (ht0 : 0 < t0) {i i' : ℕ} (hii : i < i') {j j' : Fin d → ℕ}
    (hj : j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i)
    (hj' : j' ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i') :
    Disjoint (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j)
      (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i' j') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i'', rfl⟩ : ∃ i'', i' = i'' + 1 := ⟨i' - 1, by omega⟩
  have hj'2 := (Finset.mem_sdiff.mp hj').2
  obtain ⟨k, hk⟩ := aux_lane4_lambda_inv_cell_moment_wPiece_outside ht0 hj'2 hx'
  have hin := (aux_lane4_lambda_inv_cell_moment_wPiece_lt ht0 (Finset.mem_sdiff.mp hj).1 hx k).2
  have hmono := aux_lane4_lambda_inv_cell_moment_wLen_mono S t0 ht0 (show i ≤ i'' by omega)
  linarith

/-- Pieces of the first `m` levels avoid the remainder. -/
theorem aux_lane4_lambda_inv_cell_moment_wPiece_subset_cov {d : ℕ} {a : Vec d} {S t0 : ℝ}
    (ht0 : 0 < t0) {m i : ℕ} (hi : i < m) {j : Fin d → ℕ}
    (hj : j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i) :
    aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j ⊆
      aux_lane4_lambda_inv_cell_moment_wCov a S t0 m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  intro x hx k
  have h := (aux_lane4_lambda_inv_cell_moment_wPiece_lt ht0 (Finset.mem_sdiff.mp hj).1 hx k).2
  have hmono := aux_lane4_lambda_inv_cell_moment_wLen_mono S t0 ht0 (show i ≤ m' by omega)
  linarith

theorem aux_lane4_lambda_inv_cell_moment_measurableSet_wPiece {d : ℕ} (a : Vec d) (t0 : ℝ)
    (i : ℕ) (j : Fin d → ℕ) :
    MeasurableSet (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) := by
  have : aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j =
      Set.pi Set.univ (fun k => Set.Ioo (a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * j k)
        (a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * (j k + 1))) := by
    ext x; simp [aux_lane4_lambda_inv_cell_moment_wPiece, Set.mem_pi]
  rw [this]
  exact MeasurableSet.univ_pi fun k => measurableSet_Ioo

theorem aux_lane4_lambda_inv_cell_moment_volume_wPiece {d : ℕ} (a : Vec d) {t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) (j : Fin d → ℕ) :
    volume (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) =
      ENNReal.ofReal (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d) := by
  have : aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j =
      Set.pi Set.univ (fun k => Set.Ioo (a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * j k)
        (a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * (j k + 1))) := by
    ext x; simp [aux_lane4_lambda_inv_cell_moment_wPiece, Set.mem_pi]
  rw [this, Real.volume_pi_Ioo]
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  have hk : ∀ k : Fin d, a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * (j k + 1) -
      (a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * j k) =
        aux_lane4_lambda_inv_cell_moment_wT t0 i := fun k => by ring
  simp only [hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hT.le]

theorem aux_lane4_lambda_inv_cell_moment_measurableSet_openBox {d : ℕ} (a : Vec d) (S : ℝ) :
    MeasurableSet (aux_lane4_lambda_inv_cell_moment_openBox a S) := by
  have : aux_lane4_lambda_inv_cell_moment_openBox a S =
      Set.pi Set.univ (fun k => Set.Ioo (a k) (a k + S)) := by
    ext x; simp [aux_lane4_lambda_inv_cell_moment_openBox, Set.mem_pi]
  rw [this]
  exact MeasurableSet.univ_pi fun k => measurableSet_Ioo

theorem aux_lane4_lambda_inv_cell_moment_volume_openBox {d : ℕ} (a : Vec d) {S : ℝ}
    (hS : 0 ≤ S) :
    volume (aux_lane4_lambda_inv_cell_moment_openBox a S) = ENNReal.ofReal (S ^ d) := by
  have : aux_lane4_lambda_inv_cell_moment_openBox a S =
      Set.pi Set.univ (fun k => Set.Ioo (a k) (a k + S)) := by
    ext x; simp [aux_lane4_lambda_inv_cell_moment_openBox, Set.mem_pi]
  rw [this, Real.volume_pi_Ioo]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hS]

theorem aux_lane4_lambda_inv_cell_moment_measurableSet_wCov {d : ℕ} (a : Vec d) (S t0 : ℝ)
    (m : ℕ) : MeasurableSet (aux_lane4_lambda_inv_cell_moment_wCov a S t0 m) := by
  cases m with
  | zero => exact MeasurableSet.empty
  | succ m =>
    have : aux_lane4_lambda_inv_cell_moment_wCov a S t0 (m + 1) =
        Set.pi Set.univ (fun k => Set.Iic (a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 m)) := by
      ext x
      simp only [aux_lane4_lambda_inv_cell_moment_wCov, mem_ofPred_eq, Set.mem_pi,
        Set.mem_univ, Set.mem_Iic, forall_const]
    rw [this]
    exact MeasurableSet.univ_pi fun k => measurableSet_Iic

theorem aux_lane4_lambda_inv_cell_moment_measurableSet_wRem {d : ℕ} (a : Vec d) (S t0 : ℝ)
    (m : ℕ) : MeasurableSet (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) :=
  (aux_lane4_lambda_inv_cell_moment_measurableSet_openBox a S).diff
    (aux_lane4_lambda_inv_cell_moment_measurableSet_wCov a S t0 m)

end Whitney

end AuxFileWhitney

section AuxFileWhitneyCover
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators



section WhitneyCover
open Homogenization

/-- The grid hyperplanes of all levels form a null set. -/
theorem aux_lane4_lambda_inv_cell_moment_grid_null {d : ℕ} (a : Vec d) (t0 : ℝ) :
    volume (⋃ (i : ℕ) (k : Fin d) (n : ℤ),
      {x : Vec d | x k = a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * n}) = 0 := by
  refine measure_iUnion_null fun i => measure_iUnion_null fun k => measure_iUnion_null fun n => ?_
  have : {x : Vec d | x k = a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * n} =
      Function.eval k ⁻¹' ({a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * n} : Set ℝ) := by
    ext x; simp
  rw [this, MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_eval_preimage_null _ (Real.volume_singleton)

/-- The floor index puts an off-grid point into its level-`i` grid cube. -/
theorem aux_lane4_lambda_inv_cell_moment_mem_wPiece_floor {d : ℕ} (a : Vec d) {t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) (x : Vec d) (hxa : ∀ k, a k < x k)
    (hZ : ∀ (k : Fin d) (n : ℤ), x k ≠ a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * n) :
    x ∈ aux_lane4_lambda_inv_cell_moment_wPiece a t0 i
      (fun k => ⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 i⌋₊) := by
  intro k
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  have hy : 0 ≤ (x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 i :=
    div_nonneg (by linarith [hxa k]) hT.le
  have h1 := Nat.floor_le hy
  have h2 := Nat.lt_floor_add_one ((x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 i)
  rw [le_div_iff₀ hT] at h1
  rw [div_lt_iff₀ hT] at h2
  have hne := hZ k (⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 i⌋₊ : ℤ)
  push_cast at hne
  constructor
  · rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · exact absurd (by linarith) hne
  · linarith

theorem aux_lane4_lambda_inv_cell_moment_floor_lt_wK {d : ℕ} (a x : Vec d) {S t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) (k : Fin d) (hxa : a k < x k)
    (hx : x k < a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i) :
    ⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 i⌋₊ <
      aux_lane4_lambda_inv_cell_moment_wK S t0 i := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  rw [Nat.floor_lt (div_nonneg (by linarith) hT.le), div_lt_iff₀ hT]
  unfold aux_lane4_lambda_inv_cell_moment_wLen at hx
  linarith

theorem aux_lane4_lambda_inv_cell_moment_wKp_le_floor {d : ℕ} (a x : Vec d) {S t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) (k : Fin d)
    (hx : a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i ≤ x k) :
    aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1) ≤
      ⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1)⌋₊ := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 (i + 1)
  have hlen : 0 ≤ aux_lane4_lambda_inv_cell_moment_wLen S t0 i :=
    mul_nonneg (Nat.cast_nonneg _) (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le
  rw [Nat.le_floor_iff (div_nonneg (by linarith) hT.le), le_div_iff₀ hT]
  rw [← aux_lane4_lambda_inv_cell_moment_wKp_len S t0 i] at hx
  linarith

/-- Off the grid hyperplanes, every point of a covered box lies in a piece of some
level at most the box level. -/
theorem aux_lane4_lambda_inv_cell_moment_wCover_aux {d : ℕ} (hd : 0 < d) (a : Vec d)
    {S t0 : ℝ} (ht0 : 0 < t0) (x : Vec d) (hxa : ∀ k, a k < x k)
    (hZ : ∀ (i : ℕ) (k : Fin d) (n : ℤ), x k ≠ a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * n) :
    ∀ i : ℕ, (∀ k, x k < a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i) →
      ∃ i' ≤ i, ∃ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i',
        x ∈ aux_lane4_lambda_inv_cell_moment_wPiece a t0 i' j := by
  intro i
  induction i with
  | zero =>
    intro hx
    refine ⟨0, le_rfl, fun k => ⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 0⌋₊, ?_,
      aux_lane4_lambda_inv_cell_moment_mem_wPiece_floor a ht0 0 x hxa (hZ 0)⟩
    refine Finset.mem_sdiff.mpr ⟨aux_lane4_lambda_inv_cell_moment_mem_wBox.mpr fun k =>
      aux_lane4_lambda_inv_cell_moment_floor_lt_wK a x ht0 0 k (hxa k) (hx k), ?_⟩
    rw [aux_lane4_lambda_inv_cell_moment_mem_wBox]
    intro h
    exact Nat.not_lt_zero _ (h ⟨0, hd⟩)
  | succ i ih =>
    intro hx
    by_cases hprev : ∀ k, x k < a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 i
    · obtain ⟨i', hi', hrest⟩ := ih hprev
      exact ⟨i', hi'.trans (Nat.le_succ i), hrest⟩
    · push Not at hprev
      obtain ⟨k0, hk0⟩ := hprev
      refine ⟨i + 1, le_rfl,
        fun k => ⌊(x k - a k) / aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1)⌋₊, ?_,
        aux_lane4_lambda_inv_cell_moment_mem_wPiece_floor a ht0 (i + 1) x hxa (hZ (i + 1))⟩
      refine Finset.mem_sdiff.mpr ⟨aux_lane4_lambda_inv_cell_moment_mem_wBox.mpr fun k =>
        aux_lane4_lambda_inv_cell_moment_floor_lt_wK a x ht0 (i + 1) k (hxa k) (hx k), ?_⟩
      rw [aux_lane4_lambda_inv_cell_moment_mem_wBox]
      intro h
      exact absurd (h k0) (not_lt.mpr
        (aux_lane4_lambda_inv_cell_moment_wKp_le_floor a x ht0 i k0 hk0))

/-- The pieces of the first `m` levels and the remainder cover the box up to a null set. -/
theorem aux_lane4_lambda_inv_cell_moment_wCover {d : ℕ} (hd : 0 < d) (a : Vec d) {S t0 : ℝ}
    (ht0 : 0 < t0) (m : ℕ) :
    volume (aux_lane4_lambda_inv_cell_moment_openBox a S \
      ((⋃ i ∈ Finset.range m, ⋃ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
        aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) ∪
        aux_lane4_lambda_inv_cell_moment_wRem a S t0 m)) = 0 := by
  refine measure_mono_null ?_ (aux_lane4_lambda_inv_cell_moment_grid_null a t0)
  intro x hx
  obtain ⟨hxbox, hxnot⟩ := hx
  by_contra hZ
  simp only [Set.mem_iUnion, mem_ofPred_eq, not_exists] at hZ
  have hxa : ∀ k, a k < x k := fun k => (hxbox k).1
  have hcov : x ∈ aux_lane4_lambda_inv_cell_moment_wCov a S t0 m := by
    by_contra h
    exact hxnot (Or.inr ⟨hxbox, h⟩)
  cases m with
  | zero => exact hcov
  | succ m' =>
    have hlt : ∀ k, x k < a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 m' := by
      intro k
      have hle : x k ≤ a k + aux_lane4_lambda_inv_cell_moment_wLen S t0 m' := hcov k
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        apply hZ m' k (aux_lane4_lambda_inv_cell_moment_wK S t0 m' : ℤ)
        rw [h]
        unfold aux_lane4_lambda_inv_cell_moment_wLen
        push_cast
        ring
    obtain ⟨i', hi', j, hj, hxj⟩ :=
      aux_lane4_lambda_inv_cell_moment_wCover_aux hd a ht0 x hxa (fun i k n h => hZ i k n h) m' hlt
    apply hxnot
    left
    simp only [Set.mem_iUnion]
    exact ⟨i', Finset.mem_range.mpr (by omega), j, hj, hxj⟩

theorem aux_lane4_lambda_inv_cell_moment_volReal_wPiece {d : ℕ} (a : Vec d) {t0 : ℝ}
    (ht0 : 0 < t0) (i : ℕ) (j : Fin d → ℕ) :
    volume.real (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) =
      aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d := by
  rw [measureReal_def, aux_lane4_lambda_inv_cell_moment_volume_wPiece a ht0 i j,
    ENNReal.toReal_ofReal (pow_nonneg (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le _)]

theorem aux_lane4_lambda_inv_cell_moment_volReal_openBox {d : ℕ} (a : Vec d) {S : ℝ}
    (hS : 0 ≤ S) :
    volume.real (aux_lane4_lambda_inv_cell_moment_openBox a S) = S ^ d := by
  rw [measureReal_def, aux_lane4_lambda_inv_cell_moment_volume_openBox a hS,
    ENNReal.toReal_ofReal (pow_nonneg hS _)]

theorem aux_lane4_lambda_inv_cell_moment_card_wBox (d K : ℕ) :
    (aux_lane4_lambda_inv_cell_moment_wBox d K).card = K ^ d := by
  simp [aux_lane4_lambda_inv_cell_moment_wBox]

theorem aux_lane4_lambda_inv_cell_moment_wBox_mono (d : ℕ) {K K' : ℕ} (h : K ≤ K') :
    aux_lane4_lambda_inv_cell_moment_wBox d K ⊆ aux_lane4_lambda_inv_cell_moment_wBox d K' := by
  intro j hj
  rw [aux_lane4_lambda_inv_cell_moment_mem_wBox] at hj ⊢
  exact fun k => (hj k).trans_le h

theorem aux_lane4_lambda_inv_cell_moment_card_wD (d : ℕ) (S t0 : ℝ) (i : ℕ) :
    ((aux_lane4_lambda_inv_cell_moment_wD d S t0 i).card : ℝ) =
      (aux_lane4_lambda_inv_cell_moment_wK S t0 i : ℝ) ^ d -
        (aux_lane4_lambda_inv_cell_moment_wKp S t0 i : ℝ) ^ d := by
  have hsub := aux_lane4_lambda_inv_cell_moment_wBox_mono d
    (aux_lane4_lambda_inv_cell_moment_wKp_le S t0 i)
  unfold aux_lane4_lambda_inv_cell_moment_wD
  rw [Finset.card_sdiff_of_subset hsub, aux_lane4_lambda_inv_cell_moment_card_wBox,
    aux_lane4_lambda_inv_cell_moment_card_wBox,
    Nat.cast_sub (Nat.pow_le_pow_left (aux_lane4_lambda_inv_cell_moment_wKp_le S t0 i) d)]
  push_cast
  ring

/-- `x^d - y^d ≤ (x - y) d x^{d-1}` for `0 ≤ y ≤ x`. -/
theorem aux_lane4_lambda_inv_cell_moment_pow_sub_pow_le (d : ℕ) {x y : ℝ} (hy : 0 ≤ y)
    (hxy : y ≤ x) : x ^ d - y ^ d ≤ (x - y) * d * x ^ (d - 1) := by
  have h := abs_pow_sub_pow_le x y d
  have hx : 0 ≤ x := hy.trans hxy
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy hxy d)), abs_of_nonneg (sub_nonneg.mpr hxy),
    abs_of_nonneg hx, abs_of_nonneg hy, max_eq_left hxy] at h
  exact h

/-- Volume of the level-`i+1` pieces: at most `2 d T_{i+1} S^{d-1}`. -/
theorem aux_lane4_lambda_inv_cell_moment_level_volume_le (d : ℕ) {S t0 : ℝ} (hS : 0 ≤ S)
    (ht0 : 0 < t0) (i : ℕ) :
    ((aux_lane4_lambda_inv_cell_moment_wD d S t0 (i + 1)).card : ℝ) *
        aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) ^ d ≤
      2 * d * aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) * S ^ (d - 1) := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 (i + 1)
  rw [aux_lane4_lambda_inv_cell_moment_card_wD, sub_mul, ← mul_pow, ← mul_pow,
    aux_lane4_lambda_inv_cell_moment_wKp_len]
  change aux_lane4_lambda_inv_cell_moment_wLen S t0 (i + 1) ^ d -
      aux_lane4_lambda_inv_cell_moment_wLen S t0 i ^ d ≤ _
  have hle := aux_lane4_lambda_inv_cell_moment_wLen_succ S t0 ht0 i
  have hlen0 : 0 ≤ aux_lane4_lambda_inv_cell_moment_wLen S t0 i :=
    mul_nonneg (Nat.cast_nonneg _) (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le
  have hS' := aux_lane4_lambda_inv_cell_moment_wLen_le hS ht0 (i + 1)
  have h1 := aux_lane4_lambda_inv_cell_moment_pow_sub_pow_le d hlen0 hle
  have hdiff : aux_lane4_lambda_inv_cell_moment_wLen S t0 (i + 1) -
      aux_lane4_lambda_inv_cell_moment_wLen S t0 i ≤ 2 * aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) := by
    rw [← aux_lane4_lambda_inv_cell_moment_wKp_len S t0 i]
    unfold aux_lane4_lambda_inv_cell_moment_wLen
    have hK : (aux_lane4_lambda_inv_cell_moment_wK S t0 (i + 1) : ℝ) ≤
        aux_lane4_lambda_inv_cell_moment_wKp S t0 (i + 1) + 2 := by
      exact_mod_cast aux_lane4_lambda_inv_cell_moment_wK_sub_wKp S t0 i
    nlinarith
  have hpow : aux_lane4_lambda_inv_cell_moment_wLen S t0 (i + 1) ^ (d - 1) ≤ S ^ (d - 1) :=
    pow_le_pow_left₀ (hlen0.trans hle) hS' _
  calc _ ≤ _ := h1
    _ ≤ (2 * aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1)) * d * S ^ (d - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg _)) hpow
          (pow_nonneg (hlen0.trans hle) _) (by positivity)
    _ = _ := by ring

theorem aux_lane4_lambda_inv_cell_moment_level0_volume_le (d : ℕ) {S t0 : ℝ} (hS : 0 ≤ S)
    (ht0 : 0 < t0) :
    ((aux_lane4_lambda_inv_cell_moment_wD d S t0 0).card : ℝ) *
        aux_lane4_lambda_inv_cell_moment_wT t0 0 ^ d ≤ S ^ d := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 0
  rw [aux_lane4_lambda_inv_cell_moment_card_wD, sub_mul, ← mul_pow, ← mul_pow]
  have h0 : 0 ≤ ((aux_lane4_lambda_inv_cell_moment_wKp S t0 0 : ℝ) *
      aux_lane4_lambda_inv_cell_moment_wT t0 0) ^ d := pow_nonneg (by positivity) _
  have h1 : ((aux_lane4_lambda_inv_cell_moment_wK S t0 0 : ℝ) *
      aux_lane4_lambda_inv_cell_moment_wT t0 0) ^ d ≤ S ^ d :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hT.le)
      (aux_lane4_lambda_inv_cell_moment_wLen_le hS ht0 0) d
  linarith

/-- The remainder after `m + 1` levels has volume at most `d T_m S^{d-1}`. -/
theorem aux_lane4_lambda_inv_cell_moment_volReal_wRem_le (d : ℕ) (a : Vec d) {S t0 : ℝ}
    (hS : 0 ≤ S) (ht0 : 0 < t0) (m : ℕ) :
    volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 (m + 1)) ≤
      d * aux_lane4_lambda_inv_cell_moment_wT t0 m * S ^ (d - 1) := by
  have hlen0 : 0 ≤ aux_lane4_lambda_inv_cell_moment_wLen S t0 m :=
    mul_nonneg (Nat.cast_nonneg _) (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 m).le
  have hlenS := aux_lane4_lambda_inv_cell_moment_wLen_le hS ht0 m
  have hsub : aux_lane4_lambda_inv_cell_moment_wRem a S t0 (m + 1) ⊆
      aux_lane4_lambda_inv_cell_moment_openBox a S \
        aux_lane4_lambda_inv_cell_moment_openBox a (aux_lane4_lambda_inv_cell_moment_wLen S t0 m) := by
    rintro x ⟨hx, hxc⟩
    refine ⟨hx, fun hin => hxc ?_⟩
    intro k
    exact (hin k).2.le
  have hinner : aux_lane4_lambda_inv_cell_moment_openBox a (aux_lane4_lambda_inv_cell_moment_wLen S t0 m) ⊆
      aux_lane4_lambda_inv_cell_moment_openBox a S := by
    intro x hx k
    exact ⟨(hx k).1, (hx k).2.trans_le (by linarith)⟩
  have hfin : volume (aux_lane4_lambda_inv_cell_moment_openBox a S) ≠ ⊤ := by
    rw [aux_lane4_lambda_inv_cell_moment_volume_openBox a hS]; exact ENNReal.ofReal_ne_top
  calc volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 (m + 1))
      ≤ volume.real (aux_lane4_lambda_inv_cell_moment_openBox a S \
          aux_lane4_lambda_inv_cell_moment_openBox a (aux_lane4_lambda_inv_cell_moment_wLen S t0 m)) :=
        measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hfin)
    _ = S ^ d - aux_lane4_lambda_inv_cell_moment_wLen S t0 m ^ d := by
        rw [measureReal_sdiff hinner (aux_lane4_lambda_inv_cell_moment_measurableSet_openBox _ _) hfin,
          aux_lane4_lambda_inv_cell_moment_volReal_openBox a hS,
          aux_lane4_lambda_inv_cell_moment_volReal_openBox a hlen0]
    _ ≤ (S - aux_lane4_lambda_inv_cell_moment_wLen S t0 m) * d * S ^ (d - 1) :=
        aux_lane4_lambda_inv_cell_moment_pow_sub_pow_le d hlen0 hlenS
    _ ≤ aux_lane4_lambda_inv_cell_moment_wT t0 m * d * S ^ (d - 1) := by
        have := aux_lane4_lambda_inv_cell_moment_lt_wLen_add (S := S) ht0 m
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
          (pow_nonneg hS _)
    _ = _ := by ring

theorem aux_lane4_lambda_inv_cell_moment_volReal_wRem_le_box (d : ℕ) (a : Vec d) {S t0 : ℝ}
    (hS : 0 ≤ S) (m : ℕ) :
    volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) ≤ S ^ d := by
  have hfin : volume (aux_lane4_lambda_inv_cell_moment_openBox a S) ≠ ⊤ := by
    rw [aux_lane4_lambda_inv_cell_moment_volume_openBox a hS]; exact ENNReal.ofReal_ne_top
  rw [← aux_lane4_lambda_inv_cell_moment_volReal_openBox a hS]
  exact measureReal_mono sdiff_subset hfin

end WhitneyCover

end AuxFileWhitneyCover

section AuxFileCover
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess



section Cover
open Homogenization

/-- Centers of a covering grid of mesh `2ρ` anchored at `b`. -/
def aux_lane4_lambda_inv_cell_moment_gridPt {d : ℕ} (b : Vec d) (ρ : ℝ) (j : Fin d → ℕ) :
    Vec d :=
  fun k => b k + ρ * (2 * (j k : ℝ) + 1)

/-- Every point of the closed box `b + [0, ℓ]^d` is within sup-distance `ρ` of a grid center. -/
theorem aux_lane4_lambda_inv_cell_moment_grid_cover {d : ℕ} (b : Vec d) {ℓ ρ : ℝ}
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (y : Vec d) (hy : ∀ k, b k ≤ y k ∧ y k ≤ b k + ℓ) :
    ∃ j ∈ aux_lane4_lambda_inv_cell_moment_wBox d ⌈ℓ / (2 * ρ)⌉₊,
      ∀ k, |y k - aux_lane4_lambda_inv_cell_moment_gridPt b ρ j k| ≤ ρ := by
  set J := ⌈ℓ / (2 * ρ)⌉₊ with hJ
  have h2ρ : 0 < 2 * ρ := by positivity
  have hJpos : 0 < J := Nat.ceil_pos.mpr (div_pos hℓ h2ρ)
  refine ⟨fun k => min ⌊(y k - b k) / (2 * ρ)⌋₊ (J - 1), ?_, ?_⟩
  · rw [aux_lane4_lambda_inv_cell_moment_mem_wBox]
    intro k
    exact lt_of_le_of_lt (min_le_right _ _) (by omega)
  · intro k
    obtain ⟨h1, h2⟩ := hy k
    have hu : 0 ≤ (y k - b k) / (2 * ρ) := div_nonneg (by linarith) h2ρ.le
    have hfl := Nat.floor_le hu
    have hfl2 := Nat.lt_floor_add_one ((y k - b k) / (2 * ρ))
    have hceil : ℓ / (2 * ρ) ≤ J := Nat.le_ceil _
    unfold aux_lane4_lambda_inv_cell_moment_gridPt
    simp only []
    rw [abs_le]
    rcases le_total ⌊(y k - b k) / (2 * ρ)⌋₊ (J - 1) with hle | hle
    · rw [min_eq_left hle]
      rw [le_div_iff₀ h2ρ] at hfl
      rw [div_lt_iff₀ h2ρ] at hfl2
      constructor <;> nlinarith
    · rw [min_eq_right hle]
      have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hJ1]
      have hfl' : ((J - 1 : ℕ) : ℝ) ≤ ⌊(y k - b k) / (2 * ρ)⌋₊ := by exact_mod_cast hle
      rw [hJ1] at hfl'
      have hu2 : (y k - b k) / (2 * ρ) ≤ ℓ / (2 * ρ) :=
        div_le_div_of_nonneg_right (by linarith) h2ρ.le
      have hlow : ((J : ℝ) - 1) * (2 * ρ) ≤ y k - b k := by
        have := (le_div_iff₀ h2ρ).mp (hfl'.trans hfl)
        linarith
      have hup : y k - b k ≤ (J : ℝ) * (2 * ρ) := by
        have := (div_le_iff₀ h2ρ).mp (hu2.trans hceil)
        linarith
      constructor <;> nlinarith

/-- The local envelope attached to a grid center `g`: infrared sup-norm on `K` plus the
recentered ultraviolet log-norm on the wavelength ball around `g`. -/
def aux_lane4_lambda_inv_cell_moment_env {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (g : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  Real.exp (‖(H om).restrict (K : Set (SpatialCoordinates d))‖ +
    aux_lem_extension_cell_moment_physicalLogNorm M N ((3 : ℝ) ^ N • g) om)

theorem aux_lane4_lambda_inv_cell_moment_env_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (g : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_lane4_lambda_inv_cell_moment_env M H K N g om := Real.exp_pos _

theorem aux_lane4_lambda_inv_cell_moment_env_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (K : Compacts (SpatialCoordinates d)) (N : ℕ) (g : SpatialCoordinates d) :
    Measurable (aux_lane4_lambda_inv_cell_moment_env M H K N g) :=
  ((((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable).comp
    hH).add (aux_lem_extension_cell_moment_physicalLogNorm_measurable M N _)).exp

/-- Pointwise: within sup-distance `3^{-(N+1)}` of `g`, the reciprocal cutoff coefficient is
bounded by the envelope at `g`. -/
theorem aux_lane4_lambda_inv_cell_moment_inv_le_env {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (g x : SpatialCoordinates d) (hxK : x ∈ (K : Set (SpatialCoordinates d)))
    (hxg : ∀ k, |x k - g k| ≤ (3 : ℝ) ^ (-((N : ℤ) + 1))) (om : BilateralField d) :
    (cutoffCoefficient M H om N x)⁻¹ ≤ aux_lane4_lambda_inv_cell_moment_env M H K N g om := by
  set ξ : SpatialCoordinates d := (3 : ℝ) ^ N • (x - g) with hξ
  have h3N : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  have hpt : (3 : ℝ) ^ (-(N : ℤ)) • (ξ + (3 : ℝ) ^ N • g) = x := by
    rw [hξ, ← smul_add, sub_add_cancel, smul_smul, h3N, one_smul]
  have hξmem : ξ ∈ (aux_lem_extension_cell_moment_smallCompact d : Set (SpatialCoordinates d)) := by
    change dist ξ 0 ≤ 1 / 3
    rw [dist_pi_le_iff (by norm_num)]
    intro k
    rw [Real.dist_eq, Pi.zero_apply, sub_zero, hξ, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, abs_mul,
      abs_of_pos (by positivity)]
    have hk := hxg k
    have h3 : (3 : ℝ) ^ N * (3 : ℝ) ^ (-((N : ℤ) + 1)) = 1 / 3 := by
      rw [zpow_neg, zpow_add₀ (by norm_num), zpow_natCast, zpow_one, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (by positivity), one_mul, one_div]
    calc (3 : ℝ) ^ N * |x k - g k| ≤ (3 : ℝ) ^ N * (3 : ℝ) ^ (-((N : ℤ) + 1)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 1 / 3 := h3
  have hb := aux_lem_extension_cell_moment_physicalLogNorm_bounds M H N ((3 : ℝ) ^ N • g) ξ
    hξmem om
  rw [hpt] at hb
  have hH : |H om x| ≤ ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ := by
    have hb' : ‖((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩‖ ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    have heq : ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩ = H om x := rfl
    rw [heq, Real.norm_eq_abs] at hb'
    exact hb'
  have hApos : 0 < cutoffCoefficient M H om N x := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H om N x
  unfold aux_lane4_lambda_inv_cell_moment_env
  rw [← Real.exp_log (inv_pos.mpr hApos), Real.log_inv]
  apply Real.exp_le_exp.mpr
  have := neg_abs_le (Real.log (cutoffCoefficient M H om N x))
  linarith

/-- The maximum of the envelope over a finite grid. -/
def aux_lane4_lambda_inv_cell_moment_envMax {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (b : Vec d) (ρ : ℝ) (J : ℕ) (om : BilateralField d) : ℝ :=
  Homogenization.Book.Ch02.finsetSupReal (aux_lane4_lambda_inv_cell_moment_wBox d J)
    (fun j => aux_lane4_lambda_inv_cell_moment_env M H K N
      (aux_lane4_lambda_inv_cell_moment_gridPt b ρ j) om)

theorem aux_lane4_lambda_inv_cell_moment_finsetSupReal_eq_sup' {α : Type*} (S : Finset α)
    (hS : S.Nonempty) (f : α → ℝ) :
    Homogenization.Book.Ch02.finsetSupReal S f = S.sup' hS f :=
  le_antisymm (Homogenization.Book.Ch02.finsetSupReal_le S hS fun _ hx => Finset.le_sup' f hx)
    (Finset.sup'_le hS f fun _ hx => aux_lem_extension_cell_moment_le_finsetSupReal S f hx)

theorem aux_lane4_lambda_inv_cell_moment_wBox_nonempty (d : ℕ) {J : ℕ} (hJ : 0 < J) :
    (aux_lane4_lambda_inv_cell_moment_wBox d J).Nonempty :=
  ⟨fun _ => 0, aux_lane4_lambda_inv_cell_moment_mem_wBox.mpr fun _ => hJ⟩

theorem aux_lane4_lambda_inv_cell_moment_envMax_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) {J : ℕ} (hJ : 0 < J) :
    Measurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ J) := by
  have hne := aux_lane4_lambda_inv_cell_moment_wBox_nonempty d hJ
  have heq : aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ J =
      (aux_lane4_lambda_inv_cell_moment_wBox d J).sup' hne (fun j om =>
        aux_lane4_lambda_inv_cell_moment_env M H K N
          (aux_lane4_lambda_inv_cell_moment_gridPt b ρ j) om) := by
    funext om
    rw [Finset.sup'_apply]
    exact aux_lane4_lambda_inv_cell_moment_finsetSupReal_eq_sup' _ hne _
  rw [heq]
  exact Finset.measurable_sup' hne fun j _ =>
    aux_lane4_lambda_inv_cell_moment_env_measurable M H hH K N _

/-- Every point of the closed box is controlled by the grid maximum. -/
theorem aux_lane4_lambda_inv_cell_moment_inv_le_envMax {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (b : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : SpatialCoordinates d)
    (hxK : x ∈ (K : Set (SpatialCoordinates d))) (hx : ∀ k, b k ≤ x k ∧ x k ≤ b k + ℓ)
    (om : BilateralField d) :
    (cutoffCoefficient M H om N x)⁻¹ ≤
      aux_lane4_lambda_inv_cell_moment_envMax M H K N b ((3 : ℝ) ^ (-((N : ℤ) + 1)))
        ⌈ℓ / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ om := by
  obtain ⟨j, hj, hjx⟩ := aux_lane4_lambda_inv_cell_moment_grid_cover b
    (ρ := (3 : ℝ) ^ (-((N : ℤ) + 1))) hℓ (by positivity) x hx
  exact (aux_lane4_lambda_inv_cell_moment_inv_le_env M H K N _ x hxK hjx om).trans
    (aux_lem_extension_cell_moment_le_finsetSupReal _ (fun j => aux_lane4_lambda_inv_cell_moment_env
      M H K N (aux_lane4_lambda_inv_cell_moment_gridPt b _ j) om) hj)

end Cover

end AuxFileCover

section AuxFileChart
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section Chart
open Homogenization

/-- The root chart of the cutoff coefficient as an explicit global coefficient field. -/
def aux_lane4_lambda_inv_cell_moment_chartField {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) : CoeffField d :=
  fun x => scalarMatrix (cutoffCoefficient M H om N (fun i => z i + r * x i))

/-- On a chart cell, the inverse Neumann quadratic form is twice the flux response of the
explicit chart field. -/
theorem aux_lane4_lambda_inv_cell_moment_chart_quad {d : ℕ} (E : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) (e : Vec d) :
    vecDot e (matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain Q)
      ((E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r).coeffOn Q)) e) =
      2 * ResponseJ (openCubeSet Q) 0 e (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) := by
  have hae := aux_lem_extension_cell_moment_chart_scalar_identity E M H om N z r hr z r hr
    Set.Subset.rfl Q hQ
  have hsym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric
      ((E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r).coeffOn Q) :=
    hae.mono fun x hx => by rw [hx]; exact scalarMatrix_isSymm _
  have hsplit := E.responseJ_split (Homogenization.Book.Ch02.cubeDomain Q) _ hsym 0 e
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Book.Ch02.cubeDomain_coe,
    aux_lane4_lambda_inv_cell_moment_ResponseJ_congr_ae _ _ _ hae] at hsplit
  have hz1 : vecDot (0 : Vec d) (matVecMul (Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain Q)
      ((E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r).coeffOn Q)) 0) = 0 := by
    simp [vecDot]
  have hz2 : vecDot (0 : Vec d) e = 0 := by simp [vecDot]
  rw [hz1, hz2] at hsplit
  change ResponseJ (openCubeSet Q) 0 e (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) = _ at hsplit
  linarith

/-- A pointwise lower bound on the chart coefficient bounds the cell's `|σ_*⁻¹|`. -/
theorem aux_lane4_lambda_inv_cell_moment_cell_le_of_inv_le {d : ℕ} [NeZero d] (E : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) (X : ℝ) (hX : 0 ≤ X)
    (hinv : ∀ x ∈ openCubeSet Q,
      (cutoffCoefficient M H om N (fun i => z i + r * x i))⁻¹ ≤ X) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) ≤ X := by
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
    (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef _ _).posSemidef hX
  intro e he
  rw [aux_lane4_lambda_inv_cell_moment_chart_quad E M H om N z r hr Q hQ e]
  have h := aux_lane4_lambda_inv_cell_moment_ResponseJ_le (openCubeSet Q)
    (measurableSet_openCubeSet Q) (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r)
    (fun x => cutoffCoefficient M H om N (fun i => z i + r * x i)) X hX (fun x _ => rfl)
    (fun x hx => ⟨_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H om N _, hinv x hx⟩) e he
  linarith

/-- A continuous positive scalar field is elliptic on every bounded measurable set. -/
theorem aux_lane4_lambda_inv_cell_moment_isEllipticFieldOn {d : ℕ} (f : Vec d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (U : Set (Vec d)) (hU : MeasurableSet U)
    (hUb : Bornology.IsBounded U) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U (fun x => scalarMatrix (f x)) := by
  classical
  have hmeas : Measurable (fun x => fun i j : Fin d =>
      if x ∈ U then (fun x => scalarMatrix (d := d) (f x)) x i j else 0) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    refine Measurable.ite hU ?_ measurable_const
    have : Continuous (fun x => scalarMatrix (d := d) (f x) i j) := by
      simp only [scalarMatrix, Matrix.smul_apply, smul_eq_mul]
      exact hf.mul continuous_const
    exact this.measurable
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · refine ⟨1, 1, hmeas, ?_⟩
    intro x hx
    rw [hUe] at hx
    exact absurd hx (Set.notMem_empty x)
  · have hc : IsCompact (closure U) := hUb.isCompact_closure
    obtain ⟨xm, _, hxm⟩ := hc.exists_isMinOn hUne.closure hf.continuousOn
    obtain ⟨xM, _, hxM⟩ := hc.exists_isMaxOn hUne.closure hf.continuousOn
    refine ⟨f xm, f xM, hmeas, ?_⟩
    intro x hx
    have h1 : f xm ≤ f x := hxm (subset_closure hx)
    have h2 : f x ≤ f xM := hxM (subset_closure hx)
    exact (isEllipticMatrix_scalarMatrix (hpos x)).mono (hpos xm) h1 h2

/-- Subadditivity of `in_J` for any finite index type. -/
theorem aux_lane4_lambda_inv_cell_moment_subadd_fintype {d : ℕ} (E : in_J d)
    (U : Homogenization.Book.Ch02.Domain d) (a : CoeffField d) (lam Lam : ℝ)
    (hell : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a) {ι : Type} [Fintype ι]
    (V : ι → Set (Vec d)) (hmeas : ∀ i, MeasurableSet (V i))
    (hsub : ∀ i, V i ⊆ (U : Set (Vec d)))
    (hdisj : ∀ i j, i ≠ j → volume (V i ∩ V j) = 0)
    (hcov : volume ((U : Set (Vec d)) \ ⋃ i, V i) = 0) (p q : Vec d) :
    ResponseJ (U : Set (Vec d)) p q a ≤
      ∑ i, (volume.real (V i) / volume.real (U : Set (Vec d))) * ResponseJ (V i) p q a := by
  classical
  let e := Fintype.equivFin ι
  have hcov' : volume ((U : Set (Vec d)) \ ⋃ i : Fin (Fintype.card ι), (V ∘ e.symm) i) = 0 := by
    have : (⋃ i : Fin (Fintype.card ι), (V ∘ e.symm) i) = ⋃ i, V i :=
      e.symm.surjective.iUnion_comp V
    rw [this]; exact hcov
  have h := E.responseJ_subadditive U a lam Lam hell (Fintype.card ι) (V ∘ e.symm)
    (fun i => hmeas _) (fun i => hsub _)
    (fun i j hij => hdisj _ _ (fun h => hij (e.symm.injective h))) hcov' p q
  refine h.trans (le_of_eq ?_)
  exact Equiv.sum_comp e.symm (fun i => (volume.real (V i) / volume.real (U : Set (Vec d))) *
    ResponseJ (V i) p q a)

end Chart

end AuxFileChart

section AuxFileWhitneySub
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section WhitneySub
open Homogenization

/-- The Whitney family indexed by `Option` of the level/index pairs: `none` is the remainder. -/
def aux_lane4_lambda_inv_cell_moment_wFam {d : ℕ} (a : Vec d) (S t0 : ℝ) (m : ℕ) :
    Option ((Finset.range m).sigma (fun i => aux_lane4_lambda_inv_cell_moment_wD d S t0 i)) →
      Set (Vec d)
  | none => aux_lane4_lambda_inv_cell_moment_wRem a S t0 m
  | some w => aux_lane4_lambda_inv_cell_moment_wPiece a t0 w.1.1 w.1.2

theorem aux_lane4_lambda_inv_cell_moment_wFam_disjoint {d : ℕ} (a : Vec d) {S t0 : ℝ}
    (ht0 : 0 < t0) (m : ℕ)
    (o o' : Option ((Finset.range m).sigma (fun i => aux_lane4_lambda_inv_cell_moment_wD d S t0 i)))
    (hoo : o ≠ o') :
    Disjoint (aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o)
      (aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o') := by
  have hpieceRem : ∀ w : ((Finset.range m).sigma (fun i => aux_lane4_lambda_inv_cell_moment_wD d S t0 i)),
      Disjoint (aux_lane4_lambda_inv_cell_moment_wPiece a t0 w.1.1 w.1.2)
        (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) := by
    intro w
    have hw := Finset.mem_sigma.mp w.2
    have hsub := aux_lane4_lambda_inv_cell_moment_wPiece_subset_cov (a := a) ht0
      (Finset.mem_range.mp hw.1) hw.2
    rw [Set.disjoint_left]
    intro x hx hxr
    exact hxr.2 (hsub hx)
  cases o with
  | none =>
    cases o' with
    | none => exact absurd rfl hoo
    | some w' => exact (hpieceRem w').symm
  | some w =>
    cases o' with
    | none => exact hpieceRem w
    | some w' =>
      have hww : w ≠ w' := fun h => hoo (by rw [h])
      obtain ⟨⟨i, j⟩, hw⟩ := w
      obtain ⟨⟨i', j'⟩, hw'⟩ := w'
      have hm := Finset.mem_sigma.mp hw
      have hm' := Finset.mem_sigma.mp hw'
      simp only [aux_lane4_lambda_inv_cell_moment_wFam]
      rcases lt_trichotomy i i' with hlt | heq | hgt
      · exact aux_lane4_lambda_inv_cell_moment_wPiece_disjoint_lt ht0 hlt hm.2 hm'.2
      · subst heq
        have hjj : j ≠ j' := by
          intro h
          apply hww
          subst h
          rfl
        exact aux_lane4_lambda_inv_cell_moment_wPiece_disjoint_same ht0 i hjj
      · exact (aux_lane4_lambda_inv_cell_moment_wPiece_disjoint_lt ht0 hgt hm'.2 hm.2).symm

/-- Subadditivity over the Whitney partition of a cell. -/
theorem aux_lane4_lambda_inv_cell_moment_subadd_whitney {d : ℕ} (hd : 0 < d) (E : in_J d)
    (U : Homogenization.Book.Ch02.Domain d) (a : Vec d) {S t0 : ℝ} (hS : 0 < S)
    (ht0 : 0 < t0) (m : ℕ)
    (hU : (U : Set (Vec d)) = aux_lane4_lambda_inv_cell_moment_openBox a S)
    (c : CoeffField d) (lam Lam : ℝ) (hell : IsEllipticFieldOn lam Lam (U : Set (Vec d)) c)
    (q : Vec d) :
    ResponseJ (U : Set (Vec d)) 0 q c ≤
      (∑ i ∈ Finset.range m, ∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
        (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
          ResponseJ (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) 0 q c) +
      (volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) / S ^ d) *
        ResponseJ (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) 0 q c := by
  classical
  have hmeas : ∀ o, MeasurableSet (aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o) := by
    intro o
    cases o with
    | none => exact aux_lane4_lambda_inv_cell_moment_measurableSet_wRem a S t0 m
    | some w => exact aux_lane4_lambda_inv_cell_moment_measurableSet_wPiece a t0 _ _
  have hsub : ∀ o, aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o ⊆ (U : Set (Vec d)) := by
    intro o
    rw [hU]
    cases o with
    | none => exact sdiff_subset
    | some w =>
      have hw := Finset.mem_sigma.mp w.2
      exact aux_lane4_lambda_inv_cell_moment_wPiece_subset hS.le ht0 (Finset.mem_sdiff.mp hw.2).1
  have hdisj : ∀ o o', o ≠ o' → volume (aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o ∩
      aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o') = 0 := by
    intro o o' hoo
    rw [(aux_lane4_lambda_inv_cell_moment_wFam_disjoint a ht0 m o o' hoo).inter_eq, measure_empty]
  have hcov : volume ((U : Set (Vec d)) \ ⋃ o, aux_lane4_lambda_inv_cell_moment_wFam a S t0 m o) = 0 := by
    refine measure_mono_null ?_ (aux_lane4_lambda_inv_cell_moment_wCover (S := S) hd a ht0 m)
    rintro x ⟨hxU, hxnot⟩
    rw [hU] at hxU
    refine ⟨hxU, ?_⟩
    rintro (hx | hx)
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi, j, hj, hxj⟩ := hx
      exact hxnot (Set.mem_iUnion.mpr ⟨some ⟨⟨i, j⟩, Finset.mem_sigma.mpr ⟨hi, hj⟩⟩, hxj⟩)
    · exact hxnot (Set.mem_iUnion.mpr ⟨none, hx⟩)
  have h := aux_lane4_lambda_inv_cell_moment_subadd_fintype E U c lam Lam hell
    (aux_lane4_lambda_inv_cell_moment_wFam a S t0 m) hmeas hsub hdisj hcov 0 q
  rw [Fintype.sum_option] at h
  have hU' : volume.real (U : Set (Vec d)) = S ^ d := by
    rw [hU]; exact aux_lane4_lambda_inv_cell_moment_volReal_openBox a hS.le
  rw [hU'] at h
  refine h.trans (le_of_eq ?_)
  rw [add_comm]
  congr 1
  · simp only [aux_lane4_lambda_inv_cell_moment_wFam]
    rw [Finset.sum_coe_sort ((Finset.range m).sigma (fun i => aux_lane4_lambda_inv_cell_moment_wD d S t0 i))
      (fun w => (volume.real (aux_lane4_lambda_inv_cell_moment_wPiece a t0 w.1 w.2) / S ^ d) *
        ResponseJ (aux_lane4_lambda_inv_cell_moment_wPiece a t0 w.1 w.2) 0 q c), Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [aux_lane4_lambda_inv_cell_moment_volReal_wPiece a ht0]

end WhitneySub

end AuxFileWhitneySub

section AuxFilePiece
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section Piece
open Homogenization

/-- Center of a Whitney piece. -/
def aux_lane4_lambda_inv_cell_moment_wCenter {d : ℕ} (a : Vec d) (t0 : ℝ) (i : ℕ)
    (j : Fin d → ℕ) : Vec d :=
  fun k => a k + aux_lane4_lambda_inv_cell_moment_wT t0 i * ((j k : ℝ) + 1 / 2)

theorem aux_lane4_lambda_inv_cell_moment_mem_unitOpen {d : ℕ} {y : Vec d} :
    y ∈ openCubeSet (originCube d 0) ↔ ∀ k, -(1 / 2 : ℝ) < y k ∧ y k < 1 / 2 := by
  simp [openCubeSet, originCube, cubeScaleFactor]

/-- A Whitney piece is the translate of a dilate of the unit open cube. -/
theorem aux_lane4_lambda_inv_cell_moment_wPiece_eq {d : ℕ} (a : Vec d) {t0 : ℝ} (ht0 : 0 < t0)
    (i : ℕ) (j : Fin d → ℕ) :
    aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j =
      translateSet (aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j)
        (aux_lane4_lambda_inv_cell_moment_wT t0 i • openCubeSet (originCube d 0)) := by
  have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hT.ne',
    aux_lane4_lambda_inv_cell_moment_mem_unitOpen]
  simp only [aux_lane4_lambda_inv_cell_moment_wPiece, mem_ofPred_eq, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, aux_lane4_lambda_inv_cell_moment_wCenter]
  refine forall_congr' fun k => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← div_eq_inv_mul, lt_div_iff₀ hT]; linarith
    · rw [← div_eq_inv_mul, div_lt_iff₀ hT]; linarith
  · rintro ⟨h1, h2⟩
    rw [← div_eq_inv_mul, lt_div_iff₀ hT] at h1
    rw [← div_eq_inv_mul, div_lt_iff₀ hT] at h2
    constructor <;> linarith

/-- The response of the chart field on a piece equals the response of the physical cutoff on
the unit cube, read at the physical piece center with the physical piece side. -/
theorem aux_lane4_lambda_inv_cell_moment_piece_response {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (a : Vec d) {t0 : ℝ} (ht0 : 0 < t0) (i : ℕ)
    (j : Fin d → ℕ) (s : ℝ) (hrT : r * aux_lane4_lambda_inv_cell_moment_wT t0 i = s)
    (e : Vec d) :
    ResponseJ (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) 0 e
        (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) =
      ResponseJ (openCubeSet (originCube d 0)) 0 e (fun y => scalarMatrix
        (cutoffCoefficient M H om N (fun k =>
          (z k + r * aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k) + s * y k))) := by
  rw [aux_lane4_lambda_inv_cell_moment_wPiece_eq a ht0 i j,
    aux_lane4_lambda_inv_cell_moment_ResponseJ_affine _ _ (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i)]
  congr 1
  funext y
  simp only [aux_lane4_lambda_inv_cell_moment_chartField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 2
  funext k
  rw [← hrT]
  ring

theorem aux_lane4_lambda_inv_cell_moment_cubeCenter_origin (d : ℕ) :
    cubeCenter (originCube d 0) = 0 := by
  ext k; simp [cubeCenter, originCube]

theorem aux_lane4_lambda_inv_cell_moment_origin_mem_desc (d : ℕ) :
    originCube d 0 ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - ((0 : ℕ) : ℤ)) := by
  simp [descendantsAtScale, originCube]

/-- Pointwise above-wavelength bound for one piece of physical side `3^{-L}`, `L ≤ N`. -/
theorem aux_lane4_lambda_inv_cell_moment_unit_response_le {d : ℕ} [NeZero d] (E : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N L : ℕ) (hL : L ≤ N) (w : SpatialCoordinates d)
    (hK : ∀ x ∈ openCubeSet (originCube d 0),
      (fun k => w k + (3 : ℝ) ^ (-(L : ℤ)) * x k) ∈ (K : Set (SpatialCoordinates d)))
    (om : BilateralField d)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ)
    (hfamily : ∀ N om Q, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((family N om).coeffOn Q).toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (hJgreat : ∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
          ((family N om).coeffOn (originCube d 0)) e e} (J N om))
    (e : Vec d) (he : vecNormSq e = 1) :
    ResponseJ (openCubeSet (originCube d 0)) 0 e (fun y => scalarMatrix
        (cutoffCoefficient M H om N (fun k => w k + (3 : ℝ) ^ (-(L : ℤ)) * y k))) ≤
      Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K L w om) *
        (J (N - L) (aux_lem_extension_cell_moment_zoom (L : ℤ) w om) + 1) := by
  set g : Vec d → ℝ := fun y => cutoffCoefficient M H om N (fun k => w k + (3 : ℝ) ^ (-(L : ℤ)) * y k)
    with hg
  have hgc : Continuous g := by
    refine (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H om N).comp ?_
    exact continuous_pi fun k => continuous_const.add (continuous_const.mul (continuous_apply k))
  have hgp : ∀ y, 0 < g y := fun y => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H om N _
  set aP := (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos hgc hgp
    (Homogenization.Book.Ch02.cubeDomain (originCube d 0))).toCoeffOn with haP
  have hsym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric aP :=
    Filter.Eventually.of_forall fun x => scalarMatrix_isSymm _
  have hsplit := E.responseJ_split _ aP hsym 0 e
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Book.Ch02.cubeDomain_coe] at hsplit
  have hz1 : vecDot (0 : Vec d) (matVecMul (Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (originCube d 0)) aP) 0) = 0 := by simp [vecDot]
  have hz2 : vecDot (0 : Vec d) e = 0 := by simp [vecDot]
  rw [hz1, hz2] at hsplit
  change ResponseJ (openCubeSet (originCube d 0)) 0 e (fun y => scalarMatrix (g y)) = _ at hsplit
  have hquad := Homogenization.Book.Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef
      (Homogenization.Book.Ch02.cubeDomain (originCube d 0)) aP).posSemidef e
  rw [he, mul_one] at hquad
  have hbank := (aux_lem_extension_cell_moment_above_coarse_pointwise M H K N L 0 (by omega)
    (originCube d 0) (aux_lane4_lambda_inv_cell_moment_origin_mem_desc d) w
    (by simpa using hK) om aP (Filter.Eventually.of_forall fun x => rfl)
    ((family (N - (L + 0)) (aux_lem_extension_cell_moment_zoom ((L + 0 : ℕ) : ℤ)
      (w + (3 : ℝ) ^ (-(L : ℤ)) • cubeCenter (originCube d 0)) om)).coeffOn (originCube d 0))
    (hfamily _ _ _) _ (hJgreat _ _)).2
  simp only [aux_lane4_lambda_inv_cell_moment_cubeCenter_origin, smul_zero, add_zero] at hbank
  change Homogenization.Book.Ch02.matrixOperatorNorm _ ≤ _ at hbank
  linarith

end Piece

end AuxFilePiece

section AuxFileCellBound
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellBound
open Homogenization

theorem aux_lane4_lambda_inv_cell_moment_openCubeSet_eq_openBox {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q = aux_lane4_lambda_inv_cell_moment_openBox
      (fun k => ((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q) (cubeScaleFactor Q) := by
  ext x
  simp only [openCubeSet, aux_lane4_lambda_inv_cell_moment_openBox, mem_ofPred_eq]
  refine forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The fixed compact containing the whole root. -/
def aux_lane4_lambda_inv_cell_moment_rootK {d : ℕ} (z : SpatialCoordinates d) :
    Compacts (SpatialCoordinates d) :=
  ⟨Metric.closedBall z 1, isCompact_closedBall _ _⟩

theorem aux_lane4_lambda_inv_cell_moment_mem_rootK {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {p : Vec d} (hp : p ∈ openCubeSet (originCube d 0)) :
    (fun k => z k + r * p k) ∈
      (aux_lane4_lambda_inv_cell_moment_rootK z : Set (SpatialCoordinates d)) := by
  change dist (fun k => z k + r * p k) z ≤ 1
  rw [dist_pi_le_iff (by norm_num)]
  intro k
  have hk := aux_lane4_lambda_inv_cell_moment_mem_unitOpen.mp hp k
  rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hr]
  have : |p k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
  nlinarith [abs_nonneg (p k)]

/-- The above-wavelength piece variable: envelope times matched response plus one. -/
def aux_lane4_lambda_inv_cell_moment_pieceG {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (J : ℕ → BilateralField d → ℝ) (L : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) : ℝ :=
  Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K L w om) *
    (J (N - L) (aux_lem_extension_cell_moment_zoom (L : ℤ) w om) + 1)

/-- The per-cell majorant for `n ≤ N`: Whitney pieces above the wavelength and the grid
envelope on the remainder. -/
def aux_lane4_lambda_inv_cell_moment_cellZ {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (J : ℕ → BilateralField d → ℝ)
    (z : SpatialCoordinates d) (r : ℝ) (a : Vec d) (S t0 : ℝ) (m L0 : ℕ)
    (om : BilateralField d) : ℝ :=
  2 * (∑ i ∈ Finset.range m, ∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
      (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
        aux_lane4_lambda_inv_cell_moment_pieceG M H (aux_lane4_lambda_inv_cell_moment_rootK z) N J
          (L0 + i) (fun k => z k + r * aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k) om) +
    (volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) / S ^ d) *
      aux_lane4_lambda_inv_cell_moment_envMax M H (aux_lane4_lambda_inv_cell_moment_rootK z) N
        (fun k => z k + r * a k) ((3 : ℝ) ^ (-((N : ℤ) + 1)))
        ⌈r * S / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ om

theorem aux_lane4_lambda_inv_cell_moment_pieceG_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (J : ℕ → BilateralField d → ℝ) (hJ0 : ∀ N om, 0 ≤ J N om) (L : ℕ)
    (w : SpatialCoordinates d) (om : BilateralField d) :
    0 ≤ aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w om :=
  mul_nonneg (Real.exp_pos _).le (by linarith [hJ0 (N - L) (aux_lem_extension_cell_moment_zoom (L : ℤ) w om)])

theorem aux_lane4_lambda_inv_cell_moment_envMax_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (N : ℕ) (b : Vec d) (ρ : ℝ) (J : ℕ) (om : BilateralField d) :
    0 ≤ aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ J om :=
  Homogenization.Book.Ch02.finsetSupReal_nonneg _ _ fun _ _ =>
    (aux_lane4_lambda_inv_cell_moment_env_pos M H K N _ om).le

/-- **Pointwise cell bound, `n ≤ N`.** -/
theorem aux_lane4_lambda_inv_cell_moment_cell_le_cellZ {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) (t0 : ℝ) (ht0 : 0 < t0) (m L0 : ℕ)
    (hmN : L0 + m ≤ N + 1) (hrt : ∀ i, r * aux_lane4_lambda_inv_cell_moment_wT t0 i =
      (3 : ℝ) ^ (-((L0 + i : ℕ) : ℤ)))
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ)
    (hfamily : ∀ N om Q, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((family N om).coeffOn Q).toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (hJgreat : ∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
          ((family N om).coeffOn (originCube d 0)) e e} (J N om))
    (hJ0 : ∀ N om, 0 ≤ J N om) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) ≤
      aux_lane4_lambda_inv_cell_moment_cellZ M H N J z r
        (fun k => ((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q) (cubeScaleFactor Q) t0 m L0 om := by
  have : NeZero d := ⟨by omega⟩
  set a : Vec d := fun k => ((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q with ha
  set S : ℝ := cubeScaleFactor Q with hS
  have hSpos : 0 < S := by rw [hS]; unfold cubeScaleFactor; positivity
  have hbox := aux_lane4_lambda_inv_cell_moment_openCubeSet_eq_openBox Q
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  -- nonnegativity of the majorant
  have hZ0 : 0 ≤ aux_lane4_lambda_inv_cell_moment_cellZ M H N J z r a S t0 m L0 om := by
    unfold aux_lane4_lambda_inv_cell_moment_cellZ
    refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (pow_nonneg
        (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le _) (pow_nonneg hSpos.le _))
        (aux_lane4_lambda_inv_cell_moment_pieceG_nonneg M H K N J hJ0 _ _ om)))
      (mul_nonneg (div_nonneg measureReal_nonneg (pow_nonneg hSpos.le _))
        (aux_lane4_lambda_inv_cell_moment_envMax_nonneg M H K N _ _ _ om))
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
    (Homogenization.Book.Ch02.sigmaStarInvCoarse_posDef _ _).posSemidef hZ0
  intro e he
  rw [aux_lane4_lambda_inv_cell_moment_chart_quad E M H om N z r hr Q hQ e]
  -- the chart coefficient is a continuous positive scalar field
  set f : Vec d → ℝ := fun x => cutoffCoefficient M H om N (fun i => z i + r * x i) with hf
  have hfc : Continuous f := by
    refine (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H om N).comp ?_
    exact continuous_pi fun k => continuous_const.add (continuous_const.mul (continuous_apply k))
  have hfp : ∀ x, 0 < f x := fun x => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H om N _
  obtain ⟨lam, Lam, hell⟩ := aux_lane4_lambda_inv_cell_moment_isEllipticFieldOn f hfc hfp
    (openCubeSet Q) (measurableSet_openCubeSet Q) (isBounded_openCubeSet Q)
  have hsub := aux_lane4_lambda_inv_cell_moment_subadd_whitney (by omega) E
    (Homogenization.Book.Ch02.cubeDomain Q) a hSpos ht0 m hbox
    (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) lam Lam hell e
  simp only [Homogenization.Book.Ch02.cubeDomain_coe] at hsub
  -- piece bounds
  have hpiece : ∀ i ∈ Finset.range m, ∀ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
      ResponseJ (aux_lane4_lambda_inv_cell_moment_wPiece a t0 i j) 0 e
          (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) ≤
        aux_lane4_lambda_inv_cell_moment_pieceG M H K N J (L0 + i)
          (fun k => z k + r * aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k) om := by
    intro i hi j hj
    rw [aux_lane4_lambda_inv_cell_moment_piece_response M H om N z r a ht0 i j _ (hrt i) e]
    apply aux_lane4_lambda_inv_cell_moment_unit_response_le E M H K N (L0 + i)
      (by have := Finset.mem_range.mp hi; omega) _ _ om family J hfamily hJgreat e he
    intro x hx
    have hT := aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i
    have hpmem : (fun k => aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k +
        aux_lane4_lambda_inv_cell_moment_wT t0 i * x k) ∈ openCubeSet (originCube d 0) := by
      apply hQ
      rw [hbox]
      apply aux_lane4_lambda_inv_cell_moment_wPiece_subset hSpos.le ht0
        (Finset.mem_sdiff.mp hj).1
      rw [aux_lane4_lambda_inv_cell_moment_wPiece_eq a ht0 i j, mem_translateSet_iff_sub_mem]
      refine ⟨x, hx, ?_⟩
      funext k
      simp
    have hK' := aux_lane4_lambda_inv_cell_moment_mem_rootK z hr hr1 hpmem
    convert hK' using 1
    funext k
    rw [← hrt i]
    ring
  -- remainder bound
  have hrem : ResponseJ (aux_lane4_lambda_inv_cell_moment_wRem a S t0 m) 0 e
      (aux_lane4_lambda_inv_cell_moment_chartField M H om N z r) ≤
      aux_lane4_lambda_inv_cell_moment_envMax M H K N (fun k => z k + r * a k)
        ((3 : ℝ) ^ (-((N : ℤ) + 1))) ⌈r * S / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ om / 2 := by
    apply aux_lane4_lambda_inv_cell_moment_ResponseJ_le _
      (aux_lane4_lambda_inv_cell_moment_measurableSet_wRem a S t0 m) _ f _
      (aux_lane4_lambda_inv_cell_moment_envMax_nonneg M H K N _ _ _ om) (fun x _ => rfl) _ e he
    intro x hx
    refine ⟨hfp x, ?_⟩
    have hxbox : x ∈ aux_lane4_lambda_inv_cell_moment_openBox a S := hx.1
    have hxQ : x ∈ openCubeSet (originCube d 0) := hQ (hbox ▸ hxbox)
    apply aux_lane4_lambda_inv_cell_moment_inv_le_envMax M H K N _ (mul_pos hr hSpos) _
      (aux_lane4_lambda_inv_cell_moment_mem_rootK z hr hr1 hxQ)
    intro k
    obtain ⟨h1, h2⟩ := hxbox k
    constructor <;> nlinarith
  -- combine
  have hsum := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hpiece i hi j hj)
      (div_nonneg (pow_nonneg (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le d)
        (pow_nonneg hSpos.le d))
  have hremw := mul_le_mul_of_nonneg_left hrem
    (div_nonneg (measureReal_nonneg (μ := volume)
      (s := aux_lane4_lambda_inv_cell_moment_wRem a S t0 m)) (pow_nonneg hSpos.le d))
  unfold aux_lane4_lambda_inv_cell_moment_cellZ
  linarith

end CellBound

end AuxFileCellBound

section AuxFileMoments
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section Moments
open Homogenization

/-- `L^q` moment of one above-wavelength piece variable (Hölder at `2q`, `2q`). The rate
`aboveRate d (2q) · δ² · L` is exposed, with no fixed-epsilon loss. -/
theorem aux_lane4_lambda_inv_cell_moment_pieceG_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ CH : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ CH K) ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredAdmissible M H →
      ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (J : ℕ → BilateralField d → ℝ)
        (CJ q : ℝ), 0 ≤ CJ → 1 ≤ q →
        (∀ N, AEStronglyMeasurable (J N) (chaosSampleLaw M).toMeasure) →
        (∀ N, eLpNorm (J N) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal CJ) →
      ∀ (L : ℕ) (w : SpatialCoordinates d),
        AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w) (ENNReal.ofReal q)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Real.exp (Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * M.delta ^ 2 +
            aux_lem_extension_cell_moment_aboveRate d (2 * q) * M.delta ^ 2 +
            aux_lem_extension_cell_moment_aboveRate d (2 * q) * M.delta ^ 2 * L) * (CJ + 1)) := by
  obtain ⟨CH, hCH, hHM⟩ := aux_lem_extension_cell_moment_aboveEnvelope_moment hd
  refine ⟨CH, hCH, ?_⟩
  intro M H hH K N J CJ q hCJ hq hJmeas hJnorm L w
  have hq0 : 0 < q := by linarith
  have hq2 : 0 < 2 * q := by positivity
  let T := aux_lem_extension_cell_moment_zoom (L : ℤ) w
  have hT : MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_lem_extension_cell_moment_zoom_measurePreserving M (L : ℤ) w
  let F : BilateralField d → ℝ := fun om =>
    Real.exp (aux_lem_extension_cell_moment_aboveLogEnvelope M H K L w om)
  let X : BilateralField d → ℝ := fun om => J (N - L) (T om) + 1
  have hJTm : AEStronglyMeasurable (fun om => J (N - L) (T om)) (chaosSampleLaw M).toMeasure :=
    (hJmeas (N - L)).comp_measurePreserving hT
  have hXm : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure :=
    hJTm.add aestronglyMeasurable_const
  have hFm : AEStronglyMeasurable F (chaosSampleLaw M).toMeasure :=
    (aux_lem_extension_cell_moment_aboveEnvelope_measurable M H hH.measurable K L w).exp.aestronglyMeasurable
  have heq : aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w = fun om => F om * X om := rfl
  refine ⟨heq ▸ hFm.mul hXm, ?_⟩
  have hXnorm : eLpNorm X (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CJ + 1) := by
    have hJT : eLpNorm (fun om => J (N - L) (T om)) (ENNReal.ofReal (2 * q))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ := by
      change eLpNorm (J (N - L) ∘ T) (ENNReal.ofReal (2 * q))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CJ
      rw [eLpNorm_comp_measurePreserving (hJmeas (N - L)) hT]
      exact hJnorm (N - L)
    have hone : eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal (2 * q))
        (chaosSampleLaw M).toMeasure = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hq2) ENNReal.ofReal_ne_top]
      simp
    have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * q) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * q by linarith))
    have hadd := eLpNorm_add_le (μ := (chaosSampleLaw M).toMeasure) (f := fun om => J (N - L) (T om)) (g := fun _ : BilateralField d => (1 : ℝ)) hpone
    refine hadd.trans ?_
    rw [hone, ENNReal.ofReal_add hCJ zero_le_one, ENNReal.ofReal_one]
    exact add_le_add hJT (le_refl _)
  have hFnorm := hHM M H hH K L w (2 * q) hq2
  have hproduct := (aux_lem_extension_cell_moment_eLpNorm_mul (chaosSampleLaw M).toMeasure q hq0
    F X hFm hXm).trans (mul_le_mul' hFnorm hXnorm)
  rw [heq]
  refine hproduct.trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- `L^p` moment of the grid maximum of the local envelope. -/
theorem aux_lane4_lambda_inv_cell_moment_envMax_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredAdmissible M H →
      ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) (Jg : ℕ), 0 < Jg →
      ∀ p : ℝ, 0 < p →
        AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (((Jg ^ d : ℕ) : ℝ) ^ (1 / p) *
            Real.exp (Real.log 4 / p + 4 * p * C K * M.delta ^ 2 +
              (2 * Real.log 2 + p *
                (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
                M.delta ^ 2 * ((N : ℝ) + 1))) := by
  obtain ⟨C, hC, hCM⟩ := aux_lem_extension_cell_moment_totalLogNorm_eLpNorm hd
  refine ⟨C, hC, ?_⟩
  intro M H hH K N b ρ Jg hJg p hp
  refine ⟨(aux_lane4_lambda_inv_cell_moment_envMax_measurable M H hH.measurable K N b ρ hJg).aestronglyMeasurable, ?_⟩
  have hb := aux_lem_extension_cell_moment_eLpNorm_finsetSup_le
    (μ := (chaosSampleLaw M).toMeasure) (aux_lane4_lambda_inv_cell_moment_wBox d Jg)
    (fun j => aux_lane4_lambda_inv_cell_moment_env M H K N
      (aux_lane4_lambda_inv_cell_moment_gridPt b ρ j))
    (fun j _ => (aux_lane4_lambda_inv_cell_moment_env_measurable M H hH.measurable K N _).aestronglyMeasurable)
    hp (B := Real.exp (Real.log 4 / p + 4 * p * C K * M.delta ^ 2 +
      (2 * Real.log 2 + p * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
        M.delta ^ 2 * ((N : ℝ) + 1)))
    (fun j _ => by
      have h := hCM M H hH K N ((3 : ℝ) ^ N • aux_lane4_lambda_inv_cell_moment_gridPt b ρ j) 1 p
        zero_le_one hp
      simp only [one_mul, one_pow, mul_one] at h
      exact h)
  rw [aux_lane4_lambda_inv_cell_moment_card_wBox] at hb
  exact hb

end Moments

end AuxFileMoments

section AuxFileArith
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators



section Arith

/-- `exp (x i) ≤ c^i` when `x ≤ log c`. -/
theorem aux_lane4_lambda_inv_cell_moment_exp_le_pow {x c : ℝ} (hc : 0 < c) (hx : x ≤ Real.log c)
    (i : ℕ) : Real.exp (x * i) ≤ c ^ i := by
  rw [← Real.exp_log (pow_pos hc i), Real.log_pow]
  exact Real.exp_le_exp.mpr (by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith)

theorem aux_lane4_lambda_inv_cell_moment_geom_half (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 0) (n := m) (by norm_num) (by norm_num)
  rw [Finset.range_eq_Ico]
  refine h.trans (le_of_eq ?_)
  norm_num

/-- The grid count on a cell of side `r 3^{-n}` at mesh `2·3^{-(N+1)}` is at most `3^{N+1-n}`. -/
theorem aux_lane4_lambda_inv_cell_moment_gridCount_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (n N : ℕ) (hn : n ≤ N + 1) :
    (⌈r * (3 : ℝ) ^ (-(n : ℤ)) / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ : ℝ) ≤
      (3 : ℝ) ^ (N + 1 - n) := by
  have hx : r * (3 : ℝ) ^ (-(n : ℤ)) / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1))) =
      r * (3 : ℝ) ^ (N + 1 - n) / 2 := by
    have h3 : (3 : ℝ) ^ (N + 1 - n) = (3 : ℝ) ^ (-(n : ℤ)) / (3 : ℝ) ^ (-((N : ℤ) + 1)) := by
      rw [← zpow_sub₀ (by norm_num), ← zpow_natCast]
      congr 1
      push_cast [hn]
      ring
    rw [h3]
    field_simp
  rw [hx]
  have hp : (1 : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n) := one_le_pow₀ (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ r * (3 : ℝ) ^ (N + 1 - n) / 2 by positivity)
  have h1 : r * (3 : ℝ) ^ (N + 1 - n) / 2 ≤ (3 : ℝ) ^ (N + 1 - n) / 2 := by
    have := mul_le_mul_of_nonneg_right hr1 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n))
    linarith
  -- the ceiling is an integer below `3^{N+1-n}/2 + 1`
  have h2 : ((⌈r * (3 : ℝ) ^ (N + 1 - n) / 2⌉₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n) := by
    have hlt : ((⌈r * (3 : ℝ) ^ (N + 1 - n) / 2⌉₊ : ℕ) : ℝ) < (3 : ℝ) ^ (N + 1 - n) / 2 + 1 := by
      linarith
    have hint : ((⌈r * (3 : ℝ) ^ (N + 1 - n) / 2⌉₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n) := by
      have h3n : ((3 ^ (N + 1 - n) : ℕ) : ℝ) = (3 : ℝ) ^ (N + 1 - n) := by push_cast; ring
      rw [← h3n]
      have : ⌈r * (3 : ℝ) ^ (N + 1 - n) / 2⌉₊ ≤ 3 ^ (N + 1 - n) := by
        rw [Nat.ceil_le]
        rw [h3n]
        linarith
      exact_mod_cast this
    exact hint
  exact h2

/-- `(J^d)^{1/p} ≤ (3^k)^{1/2}` when `J ≤ 3^k` and `d / p ≤ 1/2`. -/
theorem aux_lane4_lambda_inv_cell_moment_count_rpow_le {d J k : ℕ} {p : ℝ} (hp : 0 < p)
    (hdp : (d : ℝ) / p ≤ 1 / 2) (hJ : (J : ℝ) ≤ (3 : ℝ) ^ k) :
    (((J ^ d : ℕ) : ℝ)) ^ (1 / p) ≤ Real.sqrt 3 ^ k := by
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h1 : (((J ^ d : ℕ) : ℝ)) ^ (1 / p) = (J : ℝ) ^ ((d : ℝ) / p) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ0]
    ring_nf
  rw [h1]
  rcases eq_or_lt_of_le hJ0 with h0 | hpos
  · rw [← h0]
    rcases eq_or_lt_of_le (div_nonneg (Nat.cast_nonneg d) hp.le) with hd0 | hdpos
    · rw [← hd0, Real.rpow_zero]; exact one_le_pow₀ (Real.one_le_sqrt.mpr (by norm_num))
    · rw [Real.zero_rpow hdpos.ne']; positivity
  · have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc (J : ℝ) ^ ((d : ℝ) / p) ≤ ((3 : ℝ) ^ k) ^ ((d : ℝ) / p) :=
          Real.rpow_le_rpow hJ0 hJ (div_nonneg (Nat.cast_nonneg d) hp.le)
      _ ≤ ((3 : ℝ) ^ k) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le h3 hdp
      _ = Real.sqrt 3 ^ k := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)]
          ring_nf

end Arith

end AuxFileArith

section AuxFileCellHelpers
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellHelpers
open Homogenization

/-- Minkowski for a finite nonnegative combination with real moment bounds. -/
theorem aux_lane4_lambda_inv_cell_moment_eLpNorm_sum_le {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (f : ι → α → ℝ) (_hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) (B : ι → ℝ)
    (hB0 : ∀ i ∈ s, 0 ≤ B i) (hB : ∀ i ∈ s, eLpNorm (f i) p μ ≤ ENNReal.ofReal (B i)) :
    eLpNorm (fun x => ∑ i ∈ s, c i * f i x) p μ ≤ ENNReal.ofReal (∑ i ∈ s, c i * B i) := by
  have heq : (fun x => ∑ i ∈ s, c i * f i x) = ∑ i ∈ s, (c i • f i) := by
    funext x
    rw [Finset.sum_apply]
    rfl
  rw [heq]
  refine (eLpNorm_sum_le hp).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i hi => mul_nonneg (hc i hi) (hB0 i hi)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hc i hi), ENNReal.ofReal_mul (hc i hi)]
  exact mul_le_mul' le_rfl (hB i hi)

/-- Minkowski for `c₁ f + c₂ g`. -/
theorem aux_lane4_lambda_inv_cell_moment_eLpNorm_add_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (f g : α → ℝ) (_hf : AEStronglyMeasurable f μ) (_hg : AEStronglyMeasurable g μ)
    (B₁ B₂ : ℝ) (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hB₁ : eLpNorm f p μ ≤ ENNReal.ofReal B₁) (hB₂ : eLpNorm g p μ ≤ ENNReal.ofReal B₂) :
    eLpNorm (fun x => c₁ * f x + c₂ * g x) p μ ≤ ENNReal.ofReal (c₁ * B₁ + c₂ * B₂) := by
  have heq : (fun x => c₁ * f x + c₂ * g x) = c₁ • f + c₂ • g := rfl
  rw [heq]
  refine (eLpNorm_add_le hp).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hc₁, Real.enorm_eq_ofReal hc₂,
    ENNReal.ofReal_add (mul_nonneg hc₁ hB₁0) (mul_nonneg hc₂ hB₂0),
    ENNReal.ofReal_mul hc₁, ENNReal.ofReal_mul hc₂]
  exact add_le_add (mul_le_mul' le_rfl hB₁) (mul_le_mul' le_rfl hB₂)

/-- The level-`i` weight of the Whitney partition is at most `2 d 3^{-i}`. -/
theorem aux_lane4_lambda_inv_cell_moment_level_weight_le {d : ℕ} (hd : 1 ≤ d) {S t0 : ℝ}
    (hS : 0 < S) (ht0 : 0 < t0) (htS : t0 ≤ S) (i : ℕ) :
    ((aux_lane4_lambda_inv_cell_moment_wD d S t0 i).card : ℝ) *
        (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) ≤ 2 * d * (1 / 3 : ℝ) ^ i := by
  have hSd : 0 < S ^ d := pow_pos hS d
  rw [← mul_div_assoc, div_le_iff₀ hSd]
  cases i with
  | zero =>
    have h := aux_lane4_lambda_inv_cell_moment_level0_volume_le d hS.le ht0
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simp only [pow_zero, mul_one]
    nlinarith
  | succ i =>
    have h := aux_lane4_lambda_inv_cell_moment_level_volume_le d hS.le ht0 i
    have hT : aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) ≤ S * (1 / 3 : ℝ) ^ (i + 1) := by
      unfold aux_lane4_lambda_inv_cell_moment_wT
      rw [div_eq_mul_inv, one_div, inv_pow]
      exact mul_le_mul_of_nonneg_right htS (by positivity)
    have hSd' : S ^ d = S * S ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hSd']
    calc _ ≤ 2 * d * aux_lane4_lambda_inv_cell_moment_wT t0 (i + 1) * S ^ (d - 1) := h
      _ ≤ 2 * d * (S * (1 / 3 : ℝ) ^ (i + 1)) * S ^ (d - 1) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by positivity))
            (pow_nonneg hS.le _)
      _ = _ := by ring

/-- Every `x` in the chart cell has its physical point controlled by the cell grid. -/
theorem aux_lane4_lambda_inv_cell_moment_inv_le_envMax_cell {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) (x : Vec d)
    (hx : x ∈ openCubeSet Q) :
    (cutoffCoefficient M H om N (fun i => z i + r * x i))⁻¹ ≤
      aux_lane4_lambda_inv_cell_moment_envMax M H (aux_lane4_lambda_inv_cell_moment_rootK z) N
        (fun k => z k + r * (((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q))
        ((3 : ℝ) ^ (-((N : ℤ) + 1)))
        ⌈r * cubeScaleFactor Q / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ om := by
  have hS : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  apply aux_lane4_lambda_inv_cell_moment_inv_le_envMax M H _ N _ (mul_pos hr hS) _
    (aux_lane4_lambda_inv_cell_moment_mem_rootK z hr hr1 (hQ hx))
  intro k
  have hxb := (aux_lane4_lambda_inv_cell_moment_openCubeSet_eq_openBox Q ▸ hx) k
  obtain ⟨h1, h2⟩ := hxb
  constructor <;> nlinarith

end CellHelpers

end AuxFileCellHelpers

section AuxFileCellCaseI
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellCaseI
open Homogenization

theorem aux_lane4_lambda_inv_cell_moment_desc_facts {d : ℕ} (n : ℕ) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    openCubeSet Q ⊆ openCubeSet (originCube d 0) ∧ cubeScaleFactor Q = (3 : ℝ) ^ (-(n : ℤ)) := by
  refine ⟨openCubeSet_subset_of_mem_descendantsAtScale (by simp [originCube]) hQ, ?_⟩
  have hs := scale_eq_of_mem_descendantsAtScale hQ
  unfold cubeScaleFactor
  rw [hs]
  simp [originCube]

theorem aux_lane4_lambda_inv_cell_moment_coarseS_nonneg {d : ℕ} (Q : TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F := norm_nonneg _

/-- **Per-cell moment, case `n ≤ N < n + ℓ`**: the whole chart cell is controlled by the
grid envelope on the cell, with a bounded number of grid points. -/
theorem aux_lane4_lambda_inv_cell_moment_cell_caseI {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q')
    (hdq' : (d : ℝ) / q' ≤ 1 / 2) (Cenv : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) (Jg : ℕ), 0 < Jg →
      ∀ p : ℝ, 0 < p →
        AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (((Jg ^ d : ℕ) : ℝ) ^ (1 / p) *
            Real.exp (Real.log 4 / p + 4 * p * Cenv K * M.delta ^ 2 +
              (2 * Real.log 2 + p *
                (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
                M.delta ^ 2 * ((N : ℝ) + 1))))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (ℓ N n : ℕ) (hnN : n ≤ N)
    (hNℓ : N < n + ℓ) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.sqrt 3 ^ ℓ *
        Real.exp (Real.log 4 / q' + 4 * q' * Cenv (aux_lane4_lambda_inv_cell_moment_rootK z) * M.delta ^ 2 +
          (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            M.delta ^ 2 * ℓ) *
        Real.exp ((2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          M.delta ^ 2 * n)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hQsub, hS⟩ := aux_lane4_lambda_inv_cell_moment_desc_facts n Q hQ
  have hq'0 : 0 < q' := by linarith
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  set b : Vec d := fun k => z k + r * (((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q) with hb
  set ρ : ℝ := (3 : ℝ) ^ (-((N : ℤ) + 1)) with hρ
  set Jg : ℕ := ⌈r * cubeScaleFactor Q / (2 * ρ)⌉₊ with hJg
  have hJgpos : 0 < Jg := Nat.ceil_pos.mpr (by
    have : 0 < cubeScaleFactor Q := by rw [hS]; positivity
    positivity)
  obtain ⟨hAESM, hmom⟩ := henvM K N b ρ Jg hJgpos q' hq'0
  have hpt : ∀ om, Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) ≤
      aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg om := fun om =>
    aux_lane4_lambda_inv_cell_moment_cell_le_of_inv_le E M H om N z r hr Q hQsub _
      (aux_lane4_lambda_inv_cell_moment_envMax_nonneg M H K N b ρ Jg om)
      (fun x hx => aux_lane4_lambda_inv_cell_moment_inv_le_envMax_cell M H om N z hr hr1 Q hQsub x hx)
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure := by
    apply le_trans (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall fun om => ?_))
      (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)
    rw [Real.norm_of_nonneg (aux_lane4_lambda_inv_cell_moment_coarseS_nonneg _ _)]
    exact (hpt om).trans (le_abs_self _)
  refine (hmono.trans ((eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqq')).trans hmom)).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the grid count
  have hcount : (Jg : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n) := by
    have h := aux_lane4_lambda_inv_cell_moment_gridCount_le hr hr1 n N (by omega)
    rw [hJg, hS, hρ]
    exact h
  have hc1 := aux_lane4_lambda_inv_cell_moment_count_rpow_le (d := d) hq'0 hdq' hcount
  have hsq : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have hc2 : Real.sqrt 3 ^ (N + 1 - n) ≤ Real.sqrt 3 ^ ℓ := pow_le_pow_right₀ hsq (by omega)
  set CR : ℝ := 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
    with hCR
  have hCR0 : 0 ≤ CR := by rw [hCR]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hδ2 : 0 ≤ M.delta ^ 2 := sq_nonneg _
  have hNl : ((N : ℝ) + 1) ≤ (ℓ : ℝ) + n := by
    have : N + 1 ≤ ℓ + n := by omega
    exact_mod_cast this
  have hexp : Real.exp (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 + CR * M.delta ^ 2 * ((N : ℝ) + 1)) ≤
      Real.exp (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 + CR * M.delta ^ 2 * ℓ) *
        Real.exp (CR * M.delta ^ 2 * n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hNl (mul_nonneg hCR0 hδ2)
    nlinarith
  calc (((Jg ^ d : ℕ) : ℝ)) ^ (1 / q') *
        Real.exp (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 + CR * M.delta ^ 2 * ((N : ℝ) + 1))
      ≤ Real.sqrt 3 ^ ℓ * (Real.exp (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 +
          CR * M.delta ^ 2 * ℓ) * Real.exp (CR * M.delta ^ 2 * n)) :=
        mul_le_mul (hc1.trans hc2) hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end CellCaseI

end AuxFileCellCaseI

section AuxFileCellCaseII
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellCaseII
open Homogenization

/-- The level sum of the above-wavelength pieces. -/
theorem aux_lane4_lambda_inv_cell_moment_piece_real {d : ℕ} (hd : 1 ≤ d) {S t0 : ℝ}
    (hS : 0 < S) (ht0 : 0 < t0) (htS : t0 ≤ S) (m L0 : ℕ) (B δ2 P0 CJ : ℝ)
    (hBδ : B * δ2 ≤ Real.log (3 / 2)) (hCJ : 0 ≤ CJ) :
    (∑ i ∈ Finset.range m, ∑ _j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
      (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
        (Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ)) * (CJ + 1))) ≤
      4 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1) := by
  have hterm : ∀ i ∈ Finset.range m, (∑ _j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
      (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
        (Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ)) * (CJ + 1))) ≤
      (2 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1)) * (1 / 2 : ℝ) ^ i := by
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    have hw := aux_lane4_lambda_inv_cell_moment_level_weight_le hd hS ht0 htS i
    have hpow := aux_lane4_lambda_inv_cell_moment_exp_le_pow (x := B * δ2) (c := 3 / 2)
      (by norm_num) hBδ i
    have hexp : Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ)) ≤
        Real.exp P0 * Real.exp (B * δ2 * L0) * (3 / 2 : ℝ) ^ i := by
      calc Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ))
          = Real.exp P0 * Real.exp (B * δ2 * L0) * Real.exp (B * δ2 * i) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
        _ ≤ Real.exp P0 * Real.exp (B * δ2 * L0) * (3 / 2 : ℝ) ^ i :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
    have hb0 : 0 ≤ Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ)) * (CJ + 1) := by positivity
    calc ((aux_lane4_lambda_inv_cell_moment_wD d S t0 i).card : ℝ) *
          (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
          (Real.exp (P0 + B * δ2 * ((L0 + i : ℕ) : ℝ)) * (CJ + 1))
        ≤ (2 * d * (1 / 3 : ℝ) ^ i) *
          (Real.exp P0 * Real.exp (B * δ2 * L0) * (3 / 2 : ℝ) ^ i * (CJ + 1)) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right hexp (by linarith)) hb0 (by positivity)
      _ = (2 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1)) *
          ((1 / 3 : ℝ) ^ i * (3 / 2 : ℝ) ^ i) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  calc _ ≤ ∑ i ∈ Finset.range m,
        (2 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1)) * (1 / 2 : ℝ) ^ i :=
        Finset.sum_le_sum hterm
    _ = (2 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1)) *
        ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ (2 * d * Real.exp P0 * Real.exp (B * δ2 * L0) * (CJ + 1)) * 2 :=
        mul_le_mul_of_nonneg_left (aux_lane4_lambda_inv_cell_moment_geom_half m) (by positivity)
    _ = _ := by ring

/-- The remainder: weight `≤ d 3^{-k}/r` against a grid maximum over `≤ 3^{k+1}` points. -/
theorem aux_lane4_lambda_inv_cell_moment_rem_real (d : ℕ) {r : ℝ}
    (CR δ2 E0 : ℝ) (hCRδ : CR * δ2 ≤ Real.log (Real.sqrt 3))
    (k n : ℕ) (wR X : ℝ) (hwR0 : 0 ≤ wR) (hwR : wR ≤ d * (1 / 3 : ℝ) ^ k / r)
    (hX : X ≤ Real.sqrt 3 ^ (k + 1) * Real.exp (E0 + CR * δ2 * (((n + k : ℕ) : ℝ) + 1))) :
    wR * X ≤ d * Real.sqrt 3 / r * Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) := by
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hpow := aux_lane4_lambda_inv_cell_moment_exp_le_pow (x := CR * δ2) (c := Real.sqrt 3) hs3
    hCRδ k
  have hsplit : Real.exp (E0 + CR * δ2 * (((n + k : ℕ) : ℝ) + 1)) =
      Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) * Real.exp (CR * δ2 * k) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hX' : X ≤ Real.sqrt 3 ^ (k + 1) *
      (Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) * Real.sqrt 3 ^ k) := by
    refine hX.trans ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have h33 : Real.sqrt 3 ^ (k + 1) * Real.sqrt 3 ^ k = Real.sqrt 3 * 3 ^ k := by
    rw [pow_succ, mul_comm (Real.sqrt 3 ^ k) (Real.sqrt 3), mul_assoc, ← mul_pow,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hD0 : 0 ≤ Real.sqrt 3 ^ (k + 1) *
      (Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) * Real.sqrt 3 ^ k) := by positivity
  calc wR * X ≤ (d * (1 / 3 : ℝ) ^ k / r) * (Real.sqrt 3 ^ (k + 1) *
        (Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) * Real.sqrt 3 ^ k)) :=
        (mul_le_mul_of_nonneg_left hX' hwR0).trans (mul_le_mul_of_nonneg_right hwR hD0)
    _ = d * Real.sqrt 3 / r * Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) *
        ((1 / 3 : ℝ) ^ k * 3 ^ k) := by
        rw [show Real.sqrt 3 ^ (k + 1) * (Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n) *
          Real.sqrt 3 ^ k) = (Real.sqrt 3 ^ (k + 1) * Real.sqrt 3 ^ k) *
          (Real.exp E0 * Real.exp (CR * δ2) * Real.exp (CR * δ2 * n)) by ring, h33]
        ring
    _ = _ := by rw [← mul_pow]; norm_num

end CellCaseII

end AuxFileCellCaseII

section AuxFileCellCaseIIMain
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellCaseIIMain
open Homogenization

/-- **Per-cell moment, case `n + ℓ ≤ N`**: Whitney decomposition down to the wavelength. -/
theorem aux_lane4_lambda_inv_cell_moment_cell_caseII {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q')
    (hdq' : (d : ℝ) / q' ≤ 1 / 2) (Cenv : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) (Jg : ℕ), 0 < Jg →
      ∀ p : ℝ, 0 < p →
        AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (((Jg ^ d : ℕ) : ℝ) ^ (1 / p) *
            Real.exp (Real.log 4 / p + 4 * p * Cenv K * M.delta ^ 2 +
              (2 * Real.log 2 + p *
                (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
                M.delta ^ 2 * ((N : ℝ) + 1))))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ)
    (hfamily : ∀ N om Q, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((family N om).coeffOn Q).toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (hJgreat : ∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
          ((family N om).coeffOn (originCube d 0)) e e} (J N om))
    (hJ0 : ∀ N om, 0 ≤ J N om) (CJ P0 B : ℝ) (hCJ : 0 ≤ CJ)
    (hpieceM : ∀ (N L : ℕ) (w : SpatialCoordinates d),
      AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_pieceG M H
        (aux_lane4_lambda_inv_cell_moment_rootK z) N J L w) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_lane4_lambda_inv_cell_moment_pieceG M H
          (aux_lane4_lambda_inv_cell_moment_rootK z) N J L w) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (P0 + B * M.delta ^ 2 * L) * (CJ + 1)))
    (hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2))
    (hCRδ : (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      M.delta ^ 2 ≤ Real.log (Real.sqrt 3))
    (ℓ : ℕ) (hℓ : (1 / 3 : ℝ) ^ ℓ ≤ r) (N n : ℕ) (hnN : n + ℓ ≤ N) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (4 * d * Real.exp P0 * Real.exp (B * M.delta ^ 2 * ((n + ℓ : ℕ) : ℝ)) *
          (CJ + 1)) +
        d * Real.sqrt 3 / r *
          Real.exp (Real.log 4 / q' + 4 * q' * Cenv (aux_lane4_lambda_inv_cell_moment_rootK z) *
            M.delta ^ 2) *
          Real.exp ((2 * Real.log 2 + q' *
            (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * M.delta ^ 2) *
          Real.exp ((2 * Real.log 2 + q' *
            (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * M.delta ^ 2 * n)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hQsub, hS⟩ := aux_lane4_lambda_inv_cell_moment_desc_facts n Q hQ
  have hq'0 : 0 < q' := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  set S : ℝ := cubeScaleFactor Q with hSdef
  have hSpos : 0 < S := by rw [hS]; positivity
  set a : Vec d := fun k => ((Q.index k : ℝ) - 1 / 2) * cubeScaleFactor Q with ha
  set L0 : ℕ := n + ℓ with hL0
  set t0 : ℝ := (3 : ℝ) ^ (-(L0 : ℤ)) / r with ht0def
  set m' : ℕ := N - L0 with hm'
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  have h3ℓ : (1 / 3 : ℝ) ^ ℓ = (3 : ℝ) ^ (-(ℓ : ℤ)) := by
    rw [one_div, inv_pow, zpow_neg, zpow_natCast]
  have htS : t0 ≤ S := by
    rw [ht0def, hS, div_le_iff₀ hr, hL0]
    push_cast
    rw [neg_add, zpow_add₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left (h3ℓ ▸ hℓ) (by positivity)
  have hrt : ∀ i, r * aux_lane4_lambda_inv_cell_moment_wT t0 i = (3 : ℝ) ^ (-((L0 + i : ℕ) : ℤ)) := by
    intro i
    unfold aux_lane4_lambda_inv_cell_moment_wT
    rw [ht0def]
    push_cast
    rw [neg_add, zpow_add₀ (by norm_num), zpow_neg (3 : ℝ) (i : ℤ), zpow_natCast]
    field_simp
  -- pointwise domination by the cell majorant
  have hpt : ∀ om, Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) ≤
      aux_lane4_lambda_inv_cell_moment_cellZ M H N J z r a S t0 (m' + 1) L0 om := fun om =>
    aux_lane4_lambda_inv_cell_moment_cell_le_cellZ hd E M H om N z r hr hr1 Q hQsub t0 ht0
      (m' + 1) L0 (by omega) hrt family J hfamily hJgreat hJ0
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      eLpNorm (aux_lane4_lambda_inv_cell_moment_cellZ M H N J z r a S t0 (m' + 1) L0)
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
    apply le_trans (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall fun om => ?_))
      (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)
    rw [Real.norm_of_nonneg (aux_lane4_lambda_inv_cell_moment_coarseS_nonneg _ _)]
    exact (hpt om).trans (le_abs_self _)
  refine hmono.trans ?_
  -- the pieces
  set b : ℕ → ℝ := fun i => Real.exp (P0 + B * M.delta ^ 2 * ((L0 + i : ℕ) : ℝ)) * (CJ + 1) with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => by rw [hb]; positivity
  set F : ℕ → BilateralField d → ℝ := fun i om =>
    ∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
      (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) *
        aux_lane4_lambda_inv_cell_moment_pieceG M H K N J (L0 + i)
          (fun k => z k + r * aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k) om with hF
  have hcw : ∀ i, 0 ≤ aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d := fun i =>
    div_nonneg (pow_nonneg (aux_lane4_lambda_inv_cell_moment_wT_pos ht0 i).le _)
      (pow_nonneg hSpos.le _)
  have hFi : ∀ i, AEStronglyMeasurable (F i) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (F i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
          (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) * b i) := by
    intro i
    refine ⟨Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      ((hpieceM N (L0 + i) _).1).const_mul _, ?_⟩
    exact aux_lane4_lambda_inv_cell_moment_eLpNorm_sum_le hq1 _ _ (fun j _ => hcw i)
      (fun j om => aux_lane4_lambda_inv_cell_moment_pieceG M H K N J (L0 + i)
        (fun k => z k + r * aux_lane4_lambda_inv_cell_moment_wCenter a t0 i j k) om)
      (fun j _ => (hpieceM N (L0 + i) _).1) (fun _ => b i) (fun _ _ => hb0 i)
      (fun j _ => (hpieceM N (L0 + i) _).2)
  have hFsum : eLpNorm (fun om => ∑ i ∈ Finset.range (m' + 1), F i om) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (m' + 1), ∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
        (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) * b i) := by
    have h := aux_lane4_lambda_inv_cell_moment_eLpNorm_sum_le hq1 (Finset.range (m' + 1))
      (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) F (fun i _ => (hFi i).1)
      (fun i => ∑ j ∈ aux_lane4_lambda_inv_cell_moment_wD d S t0 i,
        (aux_lane4_lambda_inv_cell_moment_wT t0 i ^ d / S ^ d) * b i)
      (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hcw i) (hb0 i)) (fun i _ => (hFi i).2)
    simpa only [one_mul] using h
  -- the remainder
  set ρ : ℝ := (3 : ℝ) ^ (-((N : ℤ) + 1)) with hρ
  set Jg : ℕ := ⌈r * S / (2 * ρ)⌉₊ with hJg
  have hJgpos : 0 < Jg := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨hGm, hGmom⟩ := henvM K N (fun k => z k + r * a k) ρ Jg hJgpos q' hq'0
  have hGq : eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N (fun k => z k + r * a k) ρ Jg)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ _ :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqq')).trans hGmom
  set wR : ℝ := volume.real (aux_lane4_lambda_inv_cell_moment_wRem a S t0 (m' + 1)) / S ^ d with hwR
  have hwR0 : 0 ≤ wR := div_nonneg measureReal_nonneg (pow_nonneg hSpos.le _)
  have hZeq : aux_lane4_lambda_inv_cell_moment_cellZ M H N J z r a S t0 (m' + 1) L0 =
      fun om => 2 * (∑ i ∈ Finset.range (m' + 1), F i om) +
        wR * aux_lane4_lambda_inv_cell_moment_envMax M H K N (fun k => z k + r * a k) ρ Jg om := by
    funext om
    rfl
  rw [hZeq]
  refine (aux_lane4_lambda_inv_cell_moment_eLpNorm_add_le hq1 2 wR (by norm_num) hwR0 _ _
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hFi i).1) hGm _ _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hcw i) (hb0 i))
    (by positivity) hFsum hGq).trans (ENNReal.ofReal_le_ofReal ?_)
  -- real arithmetic
  have hpiece := aux_lane4_lambda_inv_cell_moment_piece_real (by omega : 1 ≤ d) hSpos ht0 htS
    (m' + 1) L0 B (M.delta ^ 2) P0 CJ hBδ hCJ
  have hk : N - n = ℓ + m' := by omega
  have hwRle : wR ≤ d * (1 / 3 : ℝ) ^ (N - n) / r := by
    have hv := aux_lane4_lambda_inv_cell_moment_volReal_wRem_le d a hSpos.le ht0 m'
    rw [hwR, div_le_iff₀ (pow_pos hSpos d)]
    refine hv.trans (le_of_eq ?_)
    have hSd : S ^ d = S * S ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hSd]
    unfold aux_lane4_lambda_inv_cell_moment_wT
    rw [ht0def, hS, hk, hL0]
    have h3 : (1 / 3 : ℝ) ^ (ℓ + m') = (3 : ℝ) ^ (-((ℓ + m' : ℕ) : ℤ)) := by
      rw [one_div, inv_pow, zpow_neg, zpow_natCast]
    rw [h3]
    field_simp
    rw [← zpow_natCast (3 : ℝ) m', ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hcount : (Jg : ℝ) ≤ (3 : ℝ) ^ (N + 1 - n) := by
    have h := aux_lane4_lambda_inv_cell_moment_gridCount_le hr hr1 n N (by omega)
    rw [hJg, hS, hρ]
    exact h
  have hc1 := aux_lane4_lambda_inv_cell_moment_count_rpow_le (d := d) hq'0 hdq' hcount
  have hNk : N + 1 - n = (N - n) + 1 := by omega
  rw [hNk] at hc1
  have hX : ((Jg ^ d : ℕ) : ℝ) ^ (1 / q') *
      Real.exp (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 +
        (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          M.delta ^ 2 * ((N : ℝ) + 1)) ≤
      Real.sqrt 3 ^ ((N - n) + 1) *
        Real.exp ((Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2) +
          (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            M.delta ^ 2 * (((n + (N - n) : ℕ) : ℝ) + 1)) := by
    have hnk : ((n + (N - n) : ℕ) : ℝ) = N := by
      rw [show n + (N - n) = N by omega]
    rw [hnk]
    exact mul_le_mul_of_nonneg_right hc1 (Real.exp_pos _).le
  have hrem := aux_lane4_lambda_inv_cell_moment_rem_real d
    (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2)
    (M.delta ^ 2) (Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2) hCRδ (N - n) n wR _ hwR0
    hwRle hX
  have hL0cast : ((L0 : ℕ) : ℝ) = ((n + ℓ : ℕ) : ℝ) := by rw [hL0]
  rw [hL0cast] at hpiece
  linarith

end CellCaseIIMain

end AuxFileCellCaseIIMain

section AuxFileBelow
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section Below
open Homogenization

/-- Every cell of the root, at every depth, is controlled by the root-grid envelope. -/
theorem aux_lane4_lambda_inv_cell_moment_Y_le_envMax_root {d : ℕ} [NeZero d] (E : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N n : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) ≤
      aux_lane4_lambda_inv_cell_moment_envMax M H (aux_lane4_lambda_inv_cell_moment_rootK z) N
        (fun k => z k - r / 2) ((3 : ℝ) ^ (-((N : ℤ) + 1)))
        ⌈r / (2 * (3 : ℝ) ^ (-((N : ℤ) + 1)))⌉₊ om := by
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  have hne : (descendantsAtScale (originCube d 0) (-(n : ℤ))).Nonempty := by
    rw [← Finset.card_pos]
    have h := aux_lem_extension_cell_moment_card_desc d n
    have heq : (originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by simp [originCube]
    rw [heq] at h
    rw [h]
    positivity
  apply Homogenization.Book.Ch02.finsetSupReal_le _ hne
  intro Q hQ
  have hQ' : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)) := by
    simpa [originCube] using hQ
  obtain ⟨hQsub, _⟩ := aux_lane4_lambda_inv_cell_moment_desc_facts n Q hQ'
  apply aux_lane4_lambda_inv_cell_moment_cell_le_of_inv_le E M H om N z r hr Q hQsub _
    (aux_lane4_lambda_inv_cell_moment_envMax_nonneg M H _ N _ _ _ om)
  intro x hx
  have hxu := hQsub hx
  apply aux_lane4_lambda_inv_cell_moment_inv_le_envMax M H _ N _ hr _
    (aux_lane4_lambda_inv_cell_moment_mem_rootK z hr hr1 hxu)
  intro k
  have hk := aux_lane4_lambda_inv_cell_moment_mem_unitOpen.mp hxu k
  constructor <;> nlinarith

/-- **The `n > N` branch** (indeed valid at every depth): moment order `1/δ` against
`3^{d(N+1)}` grid points gives the linear-in-`δ` extremal rate. -/
theorem aux_lane4_lambda_inv_cell_moment_below {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (Cenv : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) (Jg : ℕ), 0 < Jg →
      ∀ p : ℝ, 0 < p →
        AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (((Jg ^ d : ℕ) : ℝ) ^ (1 / p) *
            Real.exp (Real.log 4 / p + 4 * p * Cenv K * M.delta ^ 2 +
              (2 * Real.log 2 + p *
                (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
                M.delta ^ 2 * ((N : ℝ) + 1))))
    (q : ℝ) (hq : 1 ≤ q) (hδq : M.delta ≤ 1 / q)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (N n : ℕ) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (Real.log 4 * M.delta + 4 * Cenv (aux_lane4_lambda_inv_cell_moment_rootK z) *
          M.delta + ((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
            M.delta + 2 * Real.log 2 * M.delta ^ 2)) *
        Real.exp (((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
          M.delta + 2 * Real.log 2 * M.delta ^ 2) * N)) := by
  have : NeZero d := ⟨by omega⟩
  have hδ := M.shellPrefix.delta_pos
  have hq0 : 0 < q := by linarith
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  set ρ : ℝ := (3 : ℝ) ^ (-((N : ℤ) + 1)) with hρ
  set Jg : ℕ := ⌈r / (2 * ρ)⌉₊ with hJg
  have hJgpos : 0 < Jg := Nat.ceil_pos.mpr (by positivity)
  set p : ℝ := 1 / M.delta with hp
  have hp0 : 0 < p := by positivity
  have hqp : q ≤ p := by
    rw [hp, le_div_iff₀ hδ]
    rw [le_div_iff₀ hq0] at hδq
    linarith
  obtain ⟨hGm, hGmom⟩ := henvM K N (fun k => z k - r / 2) ρ Jg hJgpos p hp0
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N (fun k => z k - r / 2) ρ Jg)
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
    apply le_trans (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall fun om => ?_))
      (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)
    have h0 : 0 ≤ Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r) :=
      Homogenization.Book.Ch02.finsetSupReal_nonneg _ _ fun Q _ =>
        aux_lane4_lambda_inv_cell_moment_coarseS_nonneg _ _
    rw [Real.norm_of_nonneg h0]
    exact (aux_lane4_lambda_inv_cell_moment_Y_le_envMax_root E M H om N n z r hr hr1).trans (le_abs_self _)
  refine (hmono.trans ((eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqp)).trans hGmom)).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the count factor: `(Jg^d)^{δ} ≤ exp (d log 3 (N+1) δ)`
  have hcount : (Jg : ℝ) ≤ (3 : ℝ) ^ (N + 1 - 0) := by
    have h := aux_lane4_lambda_inv_cell_moment_gridCount_le hr hr1 0 N (by omega)
    simpa [hJg, hρ] using h
  have hc : ((Jg ^ d : ℕ) : ℝ) ^ (1 / p) ≤ Real.exp (d * Real.log 3 * M.delta * ((N : ℝ) + 1)) := by
    have hJ0 : (0 : ℝ) ≤ Jg := Nat.cast_nonneg _
    have h1p : 1 / p = M.delta := by rw [hp]; field_simp
    rw [h1p]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ0]
    calc (Jg : ℝ) ^ ((d : ℝ) * M.delta) ≤ ((3 : ℝ) ^ (N + 1 - 0)) ^ ((d : ℝ) * M.delta) :=
          Real.rpow_le_rpow hJ0 hcount (by positivity)
      _ = Real.exp (d * Real.log 3 * M.delta * ((N : ℝ) + 1)) := by
          rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
          congr 1
          push_cast
          ring
  have hp_eq : p = 1 / M.delta := hp
  have hexpo : Real.log 4 / p + 4 * p * Cenv K * M.delta ^ 2 +
      (2 * Real.log 2 + p * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
        M.delta ^ 2 * ((N : ℝ) + 1) =
      Real.log 4 * M.delta + 4 * Cenv K * M.delta +
        (2 * Real.log 2 * M.delta ^ 2 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 *
          M.delta) * ((N : ℝ) + 1) := by
    rw [hp_eq]
    field_simp
  rw [hexpo]
  calc ((Jg ^ d : ℕ) : ℝ) ^ (1 / p) * Real.exp (Real.log 4 * M.delta + 4 * Cenv K * M.delta +
        (2 * Real.log 2 * M.delta ^ 2 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 *
          M.delta) * ((N : ℝ) + 1))
      ≤ Real.exp (d * Real.log 3 * M.delta * ((N : ℝ) + 1)) *
        Real.exp (Real.log 4 * M.delta + 4 * Cenv K * M.delta +
        (2 * Real.log 2 * M.delta ^ 2 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 *
          M.delta) * ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Below

end AuxFileBelow

section AuxFileCellMoment
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section CellMoment
open Homogenization

/-- The envelope-maximum moment property of a fixed model (packaged to keep statements small). -/
def aux_lane4_lambda_inv_cell_moment_EnvMomentProp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cenv : Compacts (SpatialCoordinates d) → ℝ) : Prop :=
  ∀ (K : Compacts (SpatialCoordinates d)) (N : ℕ) (b : Vec d) (ρ : ℝ) (Jg : ℕ), 0 < Jg →
    ∀ p : ℝ, 0 < p →
      AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_lane4_lambda_inv_cell_moment_envMax M H K N b ρ Jg) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((Jg ^ d : ℕ) : ℝ) ^ (1 / p) *
          Real.exp (Real.log 4 / p + 4 * p * Cenv K * M.delta ^ 2 +
            (2 * Real.log 2 + p *
              (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
              M.delta ^ 2 * ((N : ℝ) + 1)))

/-- The piece moment property of a fixed model, root compact and matched response. -/
def aux_lane4_lambda_inv_cell_moment_PieceMomentProp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d))
    (J : ℕ → BilateralField d → ℝ) (CJ q P0 B : ℝ) : Prop :=
  ∀ (N L : ℕ) (w : SpatialCoordinates d),
    AEStronglyMeasurable (aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w)
      (chaosSampleLaw M).toMeasure ∧
    eLpNorm (aux_lane4_lambda_inv_cell_moment_pieceG M H K N J L w) (ENNReal.ofReal q)
        (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (P0 + B * M.delta ^ 2 * L) * (CJ + 1))

/-- The matched-response data of a fixed model. -/
def aux_lane4_lambda_inv_cell_moment_RespProp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ) : Prop :=
  (∀ N om Q, ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((family N om).coeffOn Q).toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x)) ∧
  (∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ
          (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
          ((family N om).coeffOn (originCube d 0)) e e} (J N om)) ∧
  (∀ N om, 0 ≤ J N om)

/-- The per-cell prefactor for `n ≤ N`. -/
def aux_lane4_lambda_inv_cell_moment_Cplus (d : ℕ) (δ r CJ P0 B CR E0 : ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt 3 ^ ℓ * Real.exp (E0 + CR * δ ^ 2 * ℓ) +
    8 * d * (CJ + 1) * Real.exp P0 * Real.exp (B * δ ^ 2 * ℓ) +
    d * Real.sqrt 3 / r * Real.exp E0 * Real.exp (CR * δ ^ 2)

/-- **Uniform per-cell moment for `n ≤ N`.** -/
theorem aux_lane4_lambda_inv_cell_moment_cell_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q')
    (hdq' : (d : ℝ) / q' ≤ 1 / 2) (Cenv : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : aux_lane4_lambda_inv_cell_moment_EnvMomentProp M H Cenv)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ) (hresp : aux_lane4_lambda_inv_cell_moment_RespProp M family J)
    (CJ P0 B R : ℝ) (hCJ : 0 ≤ CJ)
    (hpieceM : aux_lane4_lambda_inv_cell_moment_PieceMomentProp M H
      (aux_lane4_lambda_inv_cell_moment_rootK z) J CJ q P0 B)
    (hBR : B ≤ R)
    (hCRR : 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 ≤ R)
    (hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2))
    (hCRδ : (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      M.delta ^ 2 ≤ Real.log (Real.sqrt 3))
    (ℓ : ℕ) (hℓ : (1 / 3 : ℝ) ^ ℓ ≤ r) (N n : ℕ) (hnN : n ≤ N) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_lane4_lambda_inv_cell_moment_Cplus d M.delta r CJ P0 B
        (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2)
        (Real.log 4 / q' + 4 * q' * Cenv (aux_lane4_lambda_inv_cell_moment_rootK z) * M.delta ^ 2)
        ℓ * Real.exp (R * M.delta ^ 2 * n)) := by
  obtain ⟨hfamily, hJgreat, hJ0⟩ := hresp
  set CR := 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
    with hCR
  set E0 := Real.log 4 / q' + 4 * q' * Cenv (aux_lane4_lambda_inv_cell_moment_rootK z) * M.delta ^ 2
    with hE0
  have hδ2 : 0 ≤ M.delta ^ 2 := sq_nonneg _
  have hexpCR : Real.exp (CR * M.delta ^ 2 * n) ≤ Real.exp (R * M.delta ^ 2 * n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCRR hδ2)
      (Nat.cast_nonneg n))
  have hexpB : Real.exp (B * M.delta ^ 2 * n) ≤ Real.exp (R * M.delta ^ 2 * n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBR hδ2)
      (Nat.cast_nonneg n))
  have hT1 : 0 ≤ Real.sqrt 3 ^ ℓ * Real.exp (E0 + CR * M.delta ^ 2 * ℓ) := by positivity
  have hT2 : 0 ≤ 8 * d * (CJ + 1) * Real.exp P0 * Real.exp (B * M.delta ^ 2 * ℓ) := by positivity
  have hT3 : 0 ≤ d * Real.sqrt 3 / r * Real.exp E0 * Real.exp (CR * M.delta ^ 2) := by positivity
  have hRn : 0 ≤ Real.exp (R * M.delta ^ 2 * n) := (Real.exp_pos _).le
  by_cases hcase : N < n + ℓ
  · have h := aux_lane4_lambda_inv_cell_moment_cell_caseI hd E M H q q' hq hqq' hdq' Cenv henvM
      z r hr hr1 ℓ N n hnN hcase Q hQ
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold aux_lane4_lambda_inv_cell_moment_Cplus
    have := mul_le_mul_of_nonneg_left hexpCR hT1
    nlinarith
  · push Not at hcase
    have h := aux_lane4_lambda_inv_cell_moment_cell_caseII hd E M H q q' hq hqq' hdq' Cenv henvM
      z r hr hr1 family J hfamily hJgreat hJ0 CJ P0 B hCJ hpieceM hBδ hCRδ ℓ hℓ N n hcase Q hQ
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold aux_lane4_lambda_inv_cell_moment_Cplus
    have hsplitB : Real.exp (B * M.delta ^ 2 * ((n + ℓ : ℕ) : ℝ)) =
        Real.exp (B * M.delta ^ 2 * ℓ) * Real.exp (B * M.delta ^ 2 * n) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hsplitB]
    have h2 := mul_le_mul_of_nonneg_left hexpB hT2
    have h3 := mul_le_mul_of_nonneg_left hexpCR hT3
    have h1 : 0 ≤ Real.sqrt 3 ^ ℓ * Real.exp (E0 + CR * M.delta ^ 2 * ℓ) *
        Real.exp (R * M.delta ^ 2 * n) := mul_nonneg hT1 hRn
    nlinarith

end CellMoment

end AuxFileCellMoment

section AuxFileFinal
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess



section Final
open Homogenization

/-- `((3^d)^n)^{1/q} = 3^{dn/q}`. -/
theorem aux_lane4_lambda_inv_cell_moment_card_rpow (d n : ℕ) (q : ℝ) :
    (((3 ^ d) ^ n : ℕ) : ℝ) ^ (1 / q) = (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) := by
  have h : (((3 ^ d) ^ n : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
    rw [show ((d : ℝ) * (n : ℝ)) = ((d * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    rw [← pow_mul]
  rw [h, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **Branch `n ≤ N`**: maximum over the `3^{dn}` cells of the uniform per-cell moment. -/
theorem aux_lane4_lambda_inv_cell_moment_branch_above {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (q : ℝ) (hq : 1 ≤ q)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (Cplus R : ℝ) (hC : 0 ≤ Cplus) (hR : 0 ≤ R)
    (hcell : ∀ N n : ℕ, n ≤ N → ∀ Q ∈ descendantsAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)),
      eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cplus * Real.exp (R * M.delta ^ 2 * n)))
    (N n : ℕ) (hnN : n ≤ N) :
    eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
        Real.exp (R * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))) := by
  have : NeZero d := ⟨by omega⟩
  have hq0 : 0 < q := by linarith
  have hscale : (originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by simp [originCube]
  have h := aux_lem_extension_cell_moment_eLpNorm_finsetSup_le
    (μ := (chaosSampleLaw M).toMeasure) (descendantsAtScale (originCube d 0) (-(n : ℤ)))
    (fun Q om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
    (fun Q hQ => aux_lem_extension_cell_moment_aesm_coarseS_chart hd E M H hH N z r hr z r hr
      Set.Subset.rfl Q (aux_lane4_lambda_inv_cell_moment_desc_facts n Q (hscale ▸ hQ)).1)
    hq0 (B := Cplus * Real.exp (R * M.delta ^ 2 * n))
    (fun Q hQ => hcell N n hnN Q (hscale ▸ hQ))
  have hcard := aux_lem_extension_cell_moment_card_desc d n
  rw [hscale] at hcard
  rw [hcard, aux_lane4_lambda_inv_cell_moment_card_rpow] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : Real.exp (R * M.delta ^ 2 * n) ≤ Real.exp (R * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℝ) ≤ q + q ^ 2 := by nlinarith
    have hRn : 0 ≤ R * M.delta ^ 2 * n := by positivity
    nlinarith
  calc (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) * (Cplus * Real.exp (R * M.delta ^ 2 * n))
      ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
          (Cplus * Real.exp (R * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC) (by positivity)
    _ = _ := by ring

/-- Branch assembly: the two branch estimates give the frozen `if`-shaped bound, with the
rate constant `Cd = 1 + a + b + c` fixed before the model and `Cq = 1 + C₊ + C₋` after. -/
theorem aux_lane4_lambda_inv_cell_moment_assemble (d : ℕ) (q a b c : ℝ) (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (delta Cplus Cminus : ℝ),
        0 ≤ delta → 0 ≤ Cplus → 0 ≤ Cminus →
        ∀ (Y : ℕ → ℕ → Ω → ℝ),
          (∀ N n : ℕ, n ≤ N →
            AEStronglyMeasurable (Y N n) μ ∧
              eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
                ENNReal.ofReal (Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                  Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ)))) →
          (∀ N n : ℕ, N < n →
            AEStronglyMeasurable (Y N n) μ ∧
              eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
                ENNReal.ofReal (Cminus * Real.exp ((b * delta + c * delta ^ 2) * (N : ℝ)))) →
          ∃ Cq : ℝ, 0 < Cq ∧
            ∀ N n : ℕ,
              AEStronglyMeasurable (Y N n) μ ∧
                eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
                  ENNReal.ofReal (Cq * (if n ≤ N then
                    (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                      Real.exp (Cd * (q + q ^ 2) * delta ^ 2 * (n : ℝ))
                  else Real.exp ((Cd * delta + Cd * delta ^ 2) * (N : ℝ)))) := by
  refine ⟨1 + a + b + c, by linarith, ?_⟩
  intro Ω _ μ delta Cplus Cminus hdelta hplus hminus Y hAbove hBelow
  refine ⟨1 + Cplus + Cminus, by linarith, ?_⟩
  intro N n
  have hq2 : 0 ≤ q + q ^ 2 := by nlinarith
  by_cases hn : n ≤ N
  · obtain ⟨hMeas, hNorm⟩ := hAbove N n hn
    refine ⟨hMeas, hNorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [ite_eq_left hn]
    have h3 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) := Real.rpow_nonneg (by norm_num) _
    have hexp : Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) ≤
        Real.exp ((1 + a + b + c) * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hq2) (sq_nonneg delta)) (Nat.cast_nonneg n))
    calc Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) * Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ))
        ≤ (1 + Cplus + Cminus) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
            Real.exp ((1 + a + b + c) * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) h3) hexp (Real.exp_pos _).le
            (by positivity)
      _ = _ := by ring
  · obtain ⟨hMeas, hNorm⟩ := hBelow N n (by omega)
    refine ⟨hMeas, hNorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [ite_eq_right hn]
    have hexp : Real.exp ((b * delta + c * delta ^ 2) * (N : ℝ)) ≤
        Real.exp (((1 + a + b + c) * delta + (1 + a + b + c) * delta ^ 2) * (N : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) hdelta)
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg delta))) (Nat.cast_nonneg N))
    exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- The whole proof after the model, infrared field and root are fixed. -/
theorem aux_lane4_lambda_inv_cell_moment_rooted {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredAdmissible M H)
    (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q') (hdq' : (d : ℝ) / q' ≤ 1 / 2)
    (Cenv CH : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : aux_lane4_lambda_inv_cell_moment_EnvMomentProp M H Cenv)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ) (hresp : aux_lane4_lambda_inv_cell_moment_RespProp M family J)
    (CJ B R Cd : ℝ) (hCJ : 0 ≤ CJ) (hR : 0 ≤ R)
    (hpieceM : ∀ K : Compacts (SpatialCoordinates d),
      aux_lane4_lambda_inv_cell_moment_PieceMomentProp M H K J CJ q
        (Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * M.delta ^ 2 + B * M.delta ^ 2) B)
    (hBR : B ≤ R)
    (hCRR : 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 ≤ R)
    (hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2))
    (hCRδ : (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      M.delta ^ 2 ≤ Real.log (Real.sqrt 3))
    (hδq : M.delta ≤ 1 / q)
    (hasm : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (delta Cplus Cminus : ℝ),
      0 ≤ delta → 0 ≤ Cplus → 0 ≤ Cminus →
      ∀ (Y : ℕ → ℕ → Ω → ℝ),
        (∀ N n : ℕ, n ≤ N →
          AEStronglyMeasurable (Y N n) μ ∧
            eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
              ENNReal.ofReal (Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                Real.exp (R * (q + q ^ 2) * delta ^ 2 * (n : ℝ)))) →
        (∀ N n : ℕ, N < n →
          AEStronglyMeasurable (Y N n) μ ∧
            eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
              ENNReal.ofReal (Cminus * Real.exp
                (((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
                  delta + 2 * Real.log 2 * delta ^ 2) * (N : ℝ)))) →
        ∃ Cq : ℝ, 0 < Cq ∧
          ∀ N n : ℕ,
            AEStronglyMeasurable (Y N n) μ ∧
              eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
                ENNReal.ofReal (Cq * (if n ≤ N then
                  (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                    Real.exp (Cd * (q + q ^ 2) * delta ^ 2 * (n : ℝ))
                else Real.exp ((Cd * delta + Cd * delta ^ 2) * (N : ℝ)))))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ N n : ℕ,
        AEStronglyMeasurable (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            (Homogenization.originCube d 0) (-(n : ℤ))
            (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            (Homogenization.originCube d 0) (-(n : ℤ))
            (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cq * (if n ≤ N then
            (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
              Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
          else Real.exp ((Cd * M.delta + Cd * M.delta ^ 2) * (N : ℝ)))) := by
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 3 : ℝ) < 1)
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  set P0 := Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * M.delta ^ 2 + B * M.delta ^ 2 with hP0
  set CR := 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
    with hCR
  set E0 := Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2 with hE0
  set Cplus := aux_lane4_lambda_inv_cell_moment_Cplus d M.delta r CJ P0 B CR E0 ℓ with hCplus
  have hCplus0 : 0 ≤ Cplus := by
    rw [hCplus]; unfold aux_lane4_lambda_inv_cell_moment_Cplus; positivity
  have hcell : ∀ N n : ℕ, n ≤ N → ∀ Q ∈ descendantsAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)),
      eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cplus * Real.exp (R * M.delta ^ 2 * n)) := by
    intro N n hnN Q hQ
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (aux_lem_extension_cell_moment_aesm_coarseS_chart hd E M H hH.measurable N z r hr z r hr Set.Subset.rfl Q (aux_lane4_lambda_inv_cell_moment_desc_facts n Q hQ).1)]
    exact aux_lane4_lambda_inv_cell_moment_cell_moment hd E M H q q' hq hqq' hdq' Cenv henvM z r hr hr1
      family J hresp CJ P0 B R hCJ (hpieceM K) hBR hCRR hBδ hCRδ ℓ hℓ.le N n hnN Q hQ
  set Cminus := Real.exp (Real.log 4 * M.delta + 4 * Cenv K * M.delta +
    ((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      M.delta + 2 * Real.log 2 * M.delta ^ 2)) with hCminus
  have hmeas : ∀ N n : ℕ, AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
      (chaosSampleLaw M).toMeasure := by
    intro N n
    have h := aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH.measurable N z r hr z r hr
      Set.Subset.rfl n
    simpa [Homogenization.originCube] using h
  exact hasm (BilateralField d) (chaosSampleLaw M).toMeasure M.delta Cplus Cminus hδ0 hCplus0
    (Real.exp_pos _).le
    (fun N n om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr) z r))
    (fun N n hnN => ⟨hmeas N n, aux_lane4_lambda_inv_cell_moment_branch_above hd E M H hH.measurable q hq
      z r hr Cplus R hCplus0 hR hcell N n hnN⟩)
    (fun N n _ => ⟨hmeas N n, by
      rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hmeas N n)]
      exact aux_lane4_lambda_inv_cell_moment_below hd E M H Cenv henvM q hq hδq z r hr hr1 N n⟩)

end Final

end AuxFileFinal



theorem lane4_lambda_inv_cell_moment :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (q : ℝ), 1 ≤ q →
  ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
        ∀ N n : ℕ,
          let Y : BilateralField d → ℝ := fun om =>
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(n : ℤ))
              (E.chart z r hr
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr)
                z r)
          AEStronglyMeasurable Y (chaosSampleLaw M).toMeasure ∧
          eLpNorm Y (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal
              (Cq * (if n ≤ N then
                  (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                    Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
                else
                  Real.exp ((Cd * M.delta + Cd * M.delta ^ 2) * (N : ℝ)))) := by
  intro d hd _ _ E q hq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hq0 : 0 < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlogs3 : 0 < Real.log (Real.sqrt 3) :=
    Real.log_pos (by rw [Real.lt_sqrt (by norm_num)]; norm_num)
  obtain ⟨δresp, CJ, hδresp, hCJ, hresp⟩ :=
    aux_lem_extension_cell_moment_matched_response hd E q hq
  obtain ⟨CH, _hCH0, hpieceM⟩ := aux_lane4_lambda_inv_cell_moment_pieceG_moment hd
  obtain ⟨Cenv, _hCenv0, henvM⟩ := aux_lane4_lambda_inv_cell_moment_envMax_moment hd
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ, q' = max q (2 * d) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = aux_lem_extension_cell_moment_aboveRate d (2 * q) := ⟨_, rfl⟩
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ,
      CR = 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 :=
    ⟨_, rfl⟩
  have hBpos : 0 < B := by
    rw [hB]; exact aux_lem_extension_cell_moment_aboveRate_pos d (2 * q) (by positivity)
  have hq'q : q ≤ q' := by rw [hq']; exact le_max_left _ _
  have hq'0 : 0 < q' := by linarith
  have hCRpos : 0 < CR := by rw [hCR]; positivity
  have hdq' : (d : ℝ) / q' ≤ 1 / 2 := by
    rw [div_le_iff₀ hq'0]
    have : 2 * (d : ℝ) ≤ q' := by rw [hq']; exact le_max_right _ _
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max B CR := ⟨_, rfl⟩
  have hBR : B ≤ R := by rw [hR]; exact le_max_left _ _
  have hCRR : CR ≤ R := by rw [hR]; exact le_max_right _ _
  have hR0 : 0 ≤ R := hBpos.le.trans hBR
  have hb0 : 0 ≤ (d : ℝ) * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 := by
    positivity
  obtain ⟨Cd, hCd, hasm⟩ := aux_lane4_lambda_inv_cell_moment_assemble d q R
    ((d : ℝ) * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2)
    (2 * Real.log 2) hq hR0 hb0 (by positivity)
  refine ⟨min δresp (min (1 / q) (min (Real.sqrt (Real.log (3 / 2) / B))
    (Real.sqrt (Real.log (Real.sqrt 3) / CR)))), Cd,
    lt_min hδresp (lt_min (by positivity) (lt_min (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_pos.mpr (by positivity)))), hCd, ?_⟩
  intro M _Rm H hH z r hr hr1 hδ
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hδresp' : M.delta ≤ δresp := hδ.trans (min_le_left _ _)
  have hδq : M.delta ≤ 1 / q := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB : M.delta ≤ Real.sqrt (Real.log (3 / 2) / B) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδC : M.delta ≤ Real.sqrt (Real.log (Real.sqrt 3) / CR) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2) := by
    have h := pow_le_pow_left₀ hδ0 hδB 2
    rw [Real.sq_sqrt (by positivity), le_div_iff₀ hBpos] at h
    linarith
  have hCRδ : CR * M.delta ^ 2 ≤ Real.log (Real.sqrt 3) := by
    have h := pow_le_pow_left₀ hδ0 hδC 2
    rw [Real.sq_sqrt (by positivity), le_div_iff₀ hCRpos] at h
    linarith
  have hrespM := hresp M hδresp'
  rcases hrespM with ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩
  have hJ0 : ∀ N om, 0 ≤ J N om := by
    intro N om
    obtain ⟨e, _, he⟩ := (hJgreat N om).1
    rw [he]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  subst hCR
  exact aux_lane4_lambda_inv_cell_moment_rooted hd E M H hH q q' hq hq'q hdq' Cenv CH (henvM M H hH)
    family J ⟨hfamily, hJgreat, hJ0⟩ CJ B R Cd hCJ.le hR0
    (fun K N L w => hB ▸ hpieceM M H hH K N J CJ q hCJ.le hq hJmeas hJnorm L w) hBR hCRR
    (hB ▸ hBδ) hCRδ hδq hasm z r hr hr1


end SubdiffusiveProcess.Paper
