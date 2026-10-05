module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5TransferAudit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Packet449PoincareChecks

@[expose] public section

/-!
# Step T of the robust good-cube event: the torsion comparison under a multiplier

Source: the weighted torsion energy and `L²` comparison (Step 5: "Since `1/2 ≤ ϑ ≤ 2` the
form and mass estimates hold for `bϑ`"; "No derivative of `ϑ` is used in this comparison").

The weighted torsion `u` of `b·θ` and the weighted torsion `e` of `b` differ, in raw
Lebesgue `L²(W)`, by at most `4 ε √(P_u P_w ∫_W b)` when `|θ - 1| ≤ ε ≤ 1/2`, where `P_w` is a
weighted and `P_u` an unweighted zero-trace Poincaré constant for `b` alone.  The proof tests
both weak equations with `v = u - e` and uses only pointwise AM-GM, so no integral
Cauchy-Schwarz is needed.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube

variable {d : ℕ}

/-! ## Scale invariance of the weak equation -/

/-- Multiplying the form coefficient and the reference density by one constant leaves a weak
solution a weak solution (the forcing profile is unchanged). -/
theorem isMassiveWeakSolutionOn_const_mul {W : Set (Vec d)} {c rho : Vec d → ℝ}
    {mu : ℝ} (k : ℝ) {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn (fun x => k * c x) (fun x => k * rho x) mu W u f := by
  intro φ
  have h := hu φ
  have h1 : ∫ x in W, (k * rho x) * u.toFun x * φ.toH1Function.toFun x ∂volume
      = k * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have h2 : ∫ x in W, vecDot ((k * c x) • u.grad x) (φ.toH1Function.grad x) ∂volume
      = k * ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [mul_smul, vecDot_smul_left]
  have h3 : ∫ x in W, (k * rho x) * f x * φ.toH1Function.toFun x ∂volume
      = k * ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [h1, h2, h3, ← h]
  ring

/-! ## Integrability on a finite-volume window -/

theorem integrable_vecDot_grad {W : Set (Vec d)} (u v : H1Function W) :
    Integrable (fun x => vecDot (u.grad x) (v.grad x)) (volume.restrict W) := by
  unfold vecDot
  refine integrable_finsetSum _ fun i _ => ?_
  exact (u.gradMemL2 i).integrable_mul (v.gradMemL2 i)

theorem integrable_toFun_mul {W : Set (Vec d)} (u v : H1Function W) :
    Integrable (fun x => u.toFun x * v.toFun x) (volume.restrict W) :=
  u.memL2.integrable_mul v.memL2

theorem integrable_toFun {W : Set (Vec d)} [IsFiniteMeasure (volume.restrict W)]
    (u : H1Function W) :
    Integrable (fun x => u.toFun x) (volume.restrict W) :=
  u.memL2.integrable (by norm_num)

/-- A bounded measurable coefficient preserves integrability on the window. -/
theorem integrable_coeff_mul {W : Set (Vec d)} (hW : MeasurableSet W) {c : Vec d → ℝ}
    {B : ℝ} (hc : AEStronglyMeasurable c (volume.restrict W))
    (hcB : ∀ x ∈ W, |c x| ≤ B) {g : Vec d → ℝ} (hg : Integrable g (volume.restrict W)) :
    Integrable (fun x => c x * g x) (volume.restrict W) := by
  refine hg.bdd_mul (c := B) hc ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  simpa only [Real.norm_eq_abs] using hcB x hx

/-! ## Pointwise AM-GM facts -/

theorem two_mul_abs_vecDot_le (p q : Vec d) {l : ℝ} (hl : 0 < l) :
    2 * |vecDot p q| ≤ vecDot p p / l + l * vecDot q q := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq p q
  have hP : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have hQ : 0 ≤ vecNormSq q := vecNormSq_nonneg q
  unfold vecNormSq at hcs hP hQ
  set t := vecDot p q
  set P := vecDot p p
  set Q := vecDot q q
  have hs : 0 ≤ P / l + l * Q := by positivity
  have hsq : (2 * |t|) ^ 2 ≤ (P / l + l * Q) ^ 2 := by
    have h1 : (2 * |t|) ^ 2 = 4 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
    have h2 : (P / l + l * Q) ^ 2 = (P / l - l * Q) ^ 2 + 4 * (P * Q) := by
      field_simp
      ring
    rw [h1, h2]
    nlinarith [sq_nonneg (P / l - l * Q)]
  exact (sq_le_sq₀ (by positivity) hs).mp hsq

theorem abs_le_amgm (v : ℝ) {a : ℝ} (ha : 0 < a) : 2 * |v| ≤ a * (v * v) + 1 / a := by
  have h : 0 ≤ (a * |v| - 1) ^ 2 := sq_nonneg _
  have hv : |v| * |v| = v * v := abs_mul_abs_self v
  have : 2 * a * |v| ≤ a * a * (v * v) + 1 := by nlinarith
  have ha' : 0 < a := ha
  rw [div_eq_mul_inv]
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  nlinarith [inv_pos.mpr ha]

/-! ## The energy argument -/

/-- The pure-real closing step: with `l = (1-ε)/(2ε)` the AM-GM split absorbs half the
energy, leaving `X² ≤ 4ε²/(1-ε)² · P_w · M² ≤ 16 ε² P_w M²`. -/
theorem torsion_perturbation_real {eps Pw M2 X2 Y2 Z2 T : ℝ}
    (heps : 0 < eps) (heps2 : eps ≤ 1 / 2) (hPw : 0 < Pw) (hX : 0 ≤ X2) (hM : 0 ≤ M2)
    (hY : Y2 ≤ Pw * M2) (hZ : Z2 ≤ Pw * X2)
    (hT1 : (1 - eps) * X2 ≤ T)
    (hT2 : T ≤ eps / 2 * (((1 - eps) / (2 * eps)) / Pw * Z2 +
        Pw / ((1 - eps) / (2 * eps)) * M2) +
      eps / 2 * ((1 - eps) / (2 * eps) * X2 + Y2 / ((1 - eps) / (2 * eps)))) :
    X2 ≤ 16 * eps ^ 2 * Pw * M2 := by
  set l : ℝ := (1 - eps) / (2 * eps) with hldef
  have h1e : 0 < 1 - eps := by linarith
  have hl : 0 < l := div_pos h1e (by linarith)
  have hZl : l / Pw * Z2 ≤ l * X2 := by
    have : l / Pw * Z2 ≤ l / Pw * (Pw * X2) :=
      mul_le_mul_of_nonneg_left hZ (div_nonneg hl.le hPw.le)
    have heq : l / Pw * (Pw * X2) = l * X2 := by field_simp
    linarith
  have hYl : Y2 / l ≤ Pw * M2 / l := div_le_div_of_nonneg_right hY hl.le
  have hPl : Pw / l * M2 = Pw * M2 / l := by ring
  have hT3 : (1 - eps) * X2 ≤ eps * l * X2 + eps * (Pw * M2) / l := by
    have : eps / 2 * (l / Pw * Z2 + Pw / l * M2) + eps / 2 * (l * X2 + Y2 / l) ≤
        eps / 2 * (l * X2 + Pw * M2 / l) + eps / 2 * (l * X2 + Pw * M2 / l) := by
      have he2 : 0 ≤ eps / 2 := by linarith
      rw [hPl]
      have := mul_le_mul_of_nonneg_left (add_le_add_right hZl (Pw * M2 / l)) he2
      have := mul_le_mul_of_nonneg_left (add_le_add_left hYl (l * X2)) he2
      linarith
    have hsum : eps / 2 * (l * X2 + Pw * M2 / l) + eps / 2 * (l * X2 + Pw * M2 / l) =
        eps * l * X2 + eps * (Pw * M2) / l := by ring
    linarith
  have hel : eps * l = (1 - eps) / 2 := by
    rw [hldef]; field_simp
  have hel2 : eps * (Pw * M2) / l = 2 * eps ^ 2 * (Pw * M2) / (1 - eps) := by
    rw [hldef]; field_simp
  rw [hel, hel2] at hT3
  -- `(1 - ε)² X² ≤ 4 ε² P_w M²`
  have hkey : (1 - eps) ^ 2 * X2 ≤ 4 * eps ^ 2 * (Pw * M2) := by
    have hmul := mul_le_mul_of_nonneg_left hT3 (by linarith : (0 : ℝ) ≤ 2 * (1 - eps))
    have hsimp : 2 * (1 - eps) * ((1 - eps) / 2 * X2 + 2 * eps ^ 2 * (Pw * M2) / (1 - eps)) =
        (1 - eps) ^ 2 * X2 + 4 * eps ^ 2 * (Pw * M2) := by
      field_simp
      ring
    rw [hsimp] at hmul
    nlinarith
  have hq : (1 : ℝ) / 4 ≤ (1 - eps) ^ 2 := by nlinarith
  have hPM : 0 ≤ Pw * M2 := mul_nonneg hPw.le hM
  nlinarith

/-- **Step T, abstract energy form.**  The three tested weak equations and the two Poincaré
inputs, stated for plain functions: `fv, fe` are the values of `v = u - e` and `e`, and
`Gev, Gvv, Gee` the pointwise gradient pairings.  Conclusion: the weighted energy of `v` is at
most `16 ε² P_w ∫ b`. -/
theorem torsion_energy_bound_abstract
    {W : Set (Vec d)} (hW : MeasurableSet W)
    {b th fv fe Gev Gvv Gee : Vec d → ℝ} {eps Pw : ℝ}
    (heps : 0 < eps) (heps2 : eps ≤ 1 / 2) (hPw : 0 < Pw)
    (hb0 : ∀ x ∈ W, 0 ≤ b x) (hth : ∀ x ∈ W, |th x - 1| ≤ eps)
    (hGvv : ∀ x ∈ W, 0 ≤ Gvv x)
    (hGev : ∀ l : ℝ, 0 < l → ∀ x ∈ W, 2 * |Gev x| ≤ Gee x / l + l * Gvv x)
    (ib : IntegrableOn b W) (ibV : IntegrableOn (fun x => b x * fv x) W)
    (ibE : IntegrableOn (fun x => b x * fe x) W)
    (ibVV : IntegrableOn (fun x => b x * (fv x * fv x)) W)
    (ibEE : IntegrableOn (fun x => b x * (fe x * fe x)) W)
    (ibGev : IntegrableOn (fun x => b x * Gev x) W)
    (ibGvv : IntegrableOn (fun x => b x * Gvv x) W)
    (ibGee : IntegrableOn (fun x => b x * Gee x) W)
    (ibtV : IntegrableOn (fun x => b x * th x * fv x) W)
    (ibtGev : IntegrableOn (fun x => b x * th x * Gev x) W)
    (ibtGvv : IntegrableOn (fun x => b x * th x * Gvv x) W)
    (hF1 : ∫ x in W, b x * Gev x = ∫ x in W, b x * fv x)
    (hF2 : ∫ x in W, b x * th x * (Gev x + Gvv x) = ∫ x in W, b x * th x * fv x)
    (hF3 : ∫ x in W, b x * Gee x = ∫ x in W, b x * fe x)
    (hPV : ∫ x in W, b x * (fv x * fv x) ≤ Pw * ∫ x in W, b x * Gvv x)
    (hPE : ∫ x in W, b x * (fe x * fe x) ≤ Pw * ∫ x in W, b x * Gee x) :
    ∫ x in W, b x * Gvv x ≤ 16 * eps ^ 2 * Pw * ∫ x in W, b x := by
  obtain ⟨X2, hX2⟩ : ∃ X2, X2 = ∫ x in W, b x * Gvv x := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y2, Y2 = ∫ x in W, b x * Gee x := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2, Z2 = ∫ x in W, b x * (fv x * fv x) := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M2, M2 = ∫ x in W, b x := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = ∫ x in W, b x * th x * Gvv x := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (1 - eps) / (2 * eps) := ⟨_, rfl⟩
  have h1e : 0 < 1 - eps := by linarith
  have hl0 : 0 < l := by rw [hl]; exact div_pos h1e (by linarith)
  rw [← hX2, ← hM2]
  have hX0 : 0 ≤ X2 := by
    rw [hX2]; exact setIntegral_nonneg hW fun x hx => mul_nonneg (hb0 x hx) (hGvv x hx)
  have hM0 : 0 ≤ M2 := by rw [hM2]; exact setIntegral_nonneg hW fun x hx => hb0 x hx
  have hZ : Z2 ≤ Pw * X2 := by rw [hZ2, hX2]; exact hPV
  -- `Y² ≤ P_w M²`
  have hY : Y2 ≤ Pw * M2 := by
    have hpt : ∀ x ∈ W, b x * fe x ≤
        (1 / (2 * Pw)) * (b x * (fe x * fe x)) + (Pw / 2) * b x := by
      intro x hx
      have h2 : fe x ≤ (1 / (2 * Pw)) * (fe x * fe x) + Pw / 2 := by
        have hid : (1 / (2 * Pw)) * (fe x * fe x) + Pw / 2 - fe x =
            (fe x - Pw) ^ 2 / (2 * Pw) := by
          field_simp
          ring
        have : 0 ≤ (fe x - Pw) ^ 2 / (2 * Pw) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_left h2 (hb0 x hx)
      nlinarith
    have iR : IntegrableOn (fun x => (1 / (2 * Pw)) * (b x * (fe x * fe x)) + (Pw / 2) * b x)
        W := (ibEE.const_mul _).add (ib.const_mul _)
    have hmono := setIntegral_mono_on ibE iR hW hpt
    rw [integral_add (ibEE.const_mul _) (ib.const_mul _), integral_const_mul,
      integral_const_mul, ← hF3, ← hY2, ← hM2] at hmono
    have h3 : (1 / (2 * Pw)) * ∫ x in W, b x * (fe x * fe x) ≤ (1 / (2 * Pw)) * (Pw * Y2) := by
      rw [hY2]; exact mul_le_mul_of_nonneg_left hPE (by positivity)
    have h4 : (1 / (2 * Pw)) * (Pw * Y2) = Y2 / 2 := by field_simp
    linarith
  -- lower bound on `T`
  have hT1 : (1 - eps) * X2 ≤ T := by
    rw [hX2, hT, ← integral_const_mul]
    refine setIntegral_mono_on (ibGvv.const_mul _) ibtGvv hW fun x hx => ?_
    have hth1 : 1 - eps ≤ th x := by
      have := (abs_le.mp (hth x hx)).1
      linarith
    have := mul_le_mul_of_nonneg_right hth1 (mul_nonneg (hb0 x hx) (hGvv x hx))
    nlinarith
  -- the identity for `T`
  have i1 : IntegrableOn (fun x => b x * th x * fv x - b x * fv x) W := ibtV.sub ibV
  have i2 : IntegrableOn (fun x => b x * th x * Gev x - b x * Gev x) W := ibtGev.sub ibGev
  have i12 : IntegrableOn (fun x => (b x * th x * fv x - b x * fv x) -
      (b x * th x * Gev x - b x * Gev x)) W := i1.sub i2
  have hTid : T = ∫ x in W, ((b x * th x * fv x - b x * fv x) -
      (b x * th x * Gev x - b x * Gev x)) := by
    rw [integral_sub i1 i2, integral_sub ibtV ibV, integral_sub ibtGev ibGev, ← hF1, ← hF2]
    have hsplit : ∫ x in W, b x * th x * (Gev x + Gvv x) =
        (∫ x in W, b x * th x * Gev x) + T := by
      have hadd := integral_add ibtGev ibtGvv
      have hcongr : ∫ x in W, b x * th x * (Gev x + Gvv x) =
          ∫ x in W, (b x * th x * Gev x + b x * th x * Gvv x) := by
        congr 1
        funext x
        ring
      rw [hcongr, hT]
      exact hadd
    rw [hsplit]
    ring
  -- pointwise AM-GM upper bound
  have hpt : ∀ x ∈ W, ((b x * th x * fv x - b x * fv x) -
      (b x * th x * Gev x - b x * Gev x)) ≤
      eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) +
        eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l) := by
    intro x hx
    have hbx := hb0 x hx
    have hthx := hth x hx
    have hA : 2 * |fv x| ≤ l / Pw * (fv x * fv x) + Pw / l := by
      have h := abs_le_amgm (fv x) (div_pos hl0 hPw)
      rwa [one_div_div] at h
    have hG : 2 * |Gev x| ≤ Gee x / l + l * Gvv x := hGev l hl0 x hx
    have hlhs : ((b x * th x * fv x - b x * fv x) - (b x * th x * Gev x - b x * Gev x)) =
        b x * ((th x - 1) * fv x) - b x * ((th x - 1) * Gev x) := by ring
    have hp1 : (th x - 1) * fv x ≤ eps * |fv x| := by
      calc (th x - 1) * fv x ≤ |(th x - 1) * fv x| := le_abs_self _
        _ = |th x - 1| * |fv x| := abs_mul _ _
        _ ≤ eps * |fv x| := mul_le_mul_of_nonneg_right hthx (abs_nonneg _)
    have hp2 : -((th x - 1) * Gev x) ≤ eps * |Gev x| := by
      calc -((th x - 1) * Gev x) ≤ |(th x - 1) * Gev x| := neg_le_abs _
        _ = |th x - 1| * |Gev x| := abs_mul _ _
        _ ≤ eps * |Gev x| := mul_le_mul_of_nonneg_right hthx (abs_nonneg _)
    have hq1 : b x * ((th x - 1) * fv x) ≤ b x * (eps * |fv x|) :=
      mul_le_mul_of_nonneg_left hp1 hbx
    have hq2 : -(b x * ((th x - 1) * Gev x)) ≤ b x * (eps * |Gev x|) := by
      have := mul_le_mul_of_nonneg_left hp2 hbx
      linarith
    have hbe : 0 ≤ b x * eps / 2 := by positivity
    have hr1 : b x * (eps * |fv x|) ≤
        eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) := by
      have h := mul_le_mul_of_nonneg_left hA hbe
      calc b x * (eps * |fv x|) = b x * eps / 2 * (2 * |fv x|) := by ring
        _ ≤ b x * eps / 2 * (l / Pw * (fv x * fv x) + Pw / l) := h
        _ = eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) := by ring
    have hr2 : b x * (eps * |Gev x|) ≤
        eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l) := by
      have h := mul_le_mul_of_nonneg_left hG hbe
      calc b x * (eps * |Gev x|) = b x * eps / 2 * (2 * |Gev x|) := by ring
        _ ≤ b x * eps / 2 * (Gee x / l + l * Gvv x) := h
        _ = eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l) := by ring
    rw [hlhs]
    linarith
  -- integrate the pointwise bound
  have iR1 : IntegrableOn (fun x => eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x))
      W := ((ibVV.const_mul _).add (ib.const_mul _)).const_mul _
  have iR2 : IntegrableOn (fun x => eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l)) W :=
    ((ibGvv.const_mul _).add (ibGee.div_const _)).const_mul _
  have hT2 : T ≤ eps / 2 * (l / Pw * Z2 + Pw / l * M2) + eps / 2 * (l * X2 + Y2 / l) := by
    rw [hTid]
    have iR : IntegrableOn (fun x => eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) +
        eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l)) W := iR1.add iR2
    have hmono := setIntegral_mono_on i12 iR hW hpt
    have e1 : ∫ x in W, (eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) +
        eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l)) =
        (∫ x in W, eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x)) +
          ∫ x in W, eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l) :=
      integral_add iR1 iR2
    have iA : IntegrableOn (fun x => l / Pw * (b x * (fv x * fv x))) W := ibVV.const_mul _
    have iB : IntegrableOn (fun x => Pw / l * b x) W := ib.const_mul _
    have iC : IntegrableOn (fun x => l * (b x * Gvv x)) W := ibGvv.const_mul _
    have iD : IntegrableOn (fun x => (b x * Gee x) / l) W := ibGee.div_const _
    have e2 : ∫ x in W, eps / 2 * (l / Pw * (b x * (fv x * fv x)) + Pw / l * b x) =
        eps / 2 * (l / Pw * Z2 + Pw / l * M2) := by
      rw [integral_const_mul]
      congr 1
      have hA := integral_add iA iB
      rw [hA, integral_const_mul, integral_const_mul, hZ2, hM2]
    have e3 : ∫ x in W, eps / 2 * (l * (b x * Gvv x) + (b x * Gee x) / l) =
        eps / 2 * (l * X2 + Y2 / l) := by
      rw [integral_const_mul]
      congr 1
      have hC := integral_add iC iD
      rw [hC, integral_const_mul, integral_div, hX2, hY2]
    linarith
  rw [hl] at hT2
  exact torsion_perturbation_real heps heps2 hPw hX0 hM0 hY hZ hT1 hT2

/-- **Step T, the core estimate.**  If `e` is the weighted torsion of `b` and `u` the weighted
torsion of `b·θ` on `W`, with `|θ - 1| ≤ ε ≤ 1/2`, then
`∫_W (u - e)² ≤ 16 ε² P_u P_w ∫_W b`, where `P_w` is a weighted and `P_u` an unweighted
zero-trace Poincaré constant **for `b` alone**. -/
theorem torsion_perturbation_sq
    {W : Set (Vec d)} (hW : MeasurableSet W) [IsFiniteMeasure (volume.restrict W)]
    {b th : Vec d → ℝ} {eps Pw Pu B : ℝ}
    (heps : 0 < eps) (heps2 : eps ≤ 1 / 2) (hPw : 0 < Pw) (hPu : 0 ≤ Pu)
    (hbm : AEStronglyMeasurable b (volume.restrict W))
    (hthm : AEStronglyMeasurable th (volume.restrict W))
    (hb0 : ∀ x ∈ W, 0 ≤ b x) (hbB : ∀ x ∈ W, b x ≤ B)
    (hth : ∀ x ∈ W, |th x - 1| ≤ eps)
    (hPoinW : ∀ f : H10Function W,
      ∫ x in W, b x * (f.toH1Function.toFun x * f.toH1Function.toFun x) ≤
        Pw * ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
    (hPoinU : ∀ f : H10Function W,
      ∫ x in W, f.toH1Function.toFun x * f.toH1Function.toFun x ≤
        Pu * ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
    (e u : H10Function W)
    (he : IsMassiveWeakSolutionOn b b 0 W e.toH1Function (fun _ => 1))
    (hu : IsMassiveWeakSolutionOn (fun x => b x * th x) (fun x => b x * th x) 0 W
      u.toH1Function (fun _ => 1)) :
    ∫ x in W, (u - e).toH1Function.toFun x * (u - e).toH1Function.toFun x ≤
      16 * eps ^ 2 * Pu * Pw * ∫ x in W, b x := by
  obtain ⟨v, hv⟩ : ∃ v : H10Function W, v = u - e := ⟨_, rfl⟩
  have hvg : ∀ x, u.toH1Function.grad x = e.toH1Function.grad x + v.toH1Function.grad x := by
    intro x
    have h : v.toH1Function.grad x = u.toH1Function.grad x - e.toH1Function.grad x := by
      rw [hv]
      change (u.toH1Function - e.toH1Function).grad x = _
      rw [H1Function.sub_grad]
    rw [h]
    abel
  rw [← hv]
  clear hv
  have hbabs : ∀ x ∈ W, |b x| ≤ B := fun x hx => by
    rw [abs_of_nonneg (hb0 x hx)]; exact hbB x hx
  have hB0 : ∀ x ∈ W, 0 ≤ B := fun x hx => (hb0 x hx).trans (hbB x hx)
  have hthabs : ∀ x ∈ W, |th x| ≤ 1 + eps := fun x hx => by
    have h := abs_le.mp (hth x hx)
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  have hbthabs : ∀ x ∈ W, |b x * th x| ≤ B * (1 + eps) := fun x hx => by
    rw [abs_mul]
    exact mul_le_mul (hbabs x hx) (hthabs x hx) (abs_nonneg _) (hB0 x hx)
  have hbthm : AEStronglyMeasurable (fun x => b x * th x) (volume.restrict W) := hbm.mul hthm
  have i1 : Integrable (fun _ : Vec d => (1 : ℝ)) (volume.restrict W) := integrable_const 1
  have ib : Integrable (fun x => b x) (volume.restrict W) := by
    simpa only [mul_one] using integrable_coeff_mul hW hbm hbabs i1
  have hF1 : ∫ x in W, b x * vecDot (e.toH1Function.grad x) (v.toH1Function.grad x) =
      ∫ x in W, b x * v.toH1Function.toFun x := by
    have h := he v
    simp only [zero_mul, zero_add, mul_one, vecDot_smul_left] at h
    exact h
  have hF2 : ∫ x in W, b x * th x * (vecDot (e.toH1Function.grad x) (v.toH1Function.grad x) +
      vecDot (v.toH1Function.grad x) (v.toH1Function.grad x)) =
      ∫ x in W, b x * th x * v.toH1Function.toFun x := by
    have h := hu v
    simp only [zero_mul, zero_add, mul_one, hvg, vecDot_smul_left, vecDot_add_left] at h
    exact h
  have hF3 : ∫ x in W, b x * vecDot (e.toH1Function.grad x) (e.toH1Function.grad x) =
      ∫ x in W, b x * e.toH1Function.toFun x := by
    have h := he e
    simp only [zero_mul, zero_add, mul_one, vecDot_smul_left] at h
    exact h
  have hX := torsion_energy_bound_abstract (fv := fun x => v.toH1Function.toFun x)
    (fe := fun x => e.toH1Function.toFun x)
    (Gev := fun x => vecDot (e.toH1Function.grad x) (v.toH1Function.grad x))
    (Gvv := fun x => vecDot (v.toH1Function.grad x) (v.toH1Function.grad x))
    (Gee := fun x => vecDot (e.toH1Function.grad x) (e.toH1Function.grad x))
    hW heps heps2 hPw hb0 hth
    (fun x _ => vecNormSq_nonneg (v.toH1Function.grad x))
    (fun l hl x _ => by
      have h := two_mul_abs_vecDot_le (e.toH1Function.grad x) (v.toH1Function.grad x) hl
      linarith)
    ib
    (integrable_coeff_mul hW hbm hbabs (integrable_toFun v.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_toFun e.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_toFun_mul v.toH1Function v.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_toFun_mul e.toH1Function e.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_vecDot_grad e.toH1Function v.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_vecDot_grad v.toH1Function v.toH1Function))
    (integrable_coeff_mul hW hbm hbabs (integrable_vecDot_grad e.toH1Function e.toH1Function))
    (integrable_coeff_mul hW hbthm hbthabs (integrable_toFun v.toH1Function))
    (integrable_coeff_mul hW hbthm hbthabs
      (integrable_vecDot_grad e.toH1Function v.toH1Function))
    (integrable_coeff_mul hW hbthm hbthabs
      (integrable_vecDot_grad v.toH1Function v.toH1Function))
    hF1 hF2 hF3 (hPoinW v) (hPoinW e)
  calc ∫ x in W, v.toH1Function.toFun x * v.toH1Function.toFun x
      ≤ Pu * ∫ x in W, b x * vecDot (v.toH1Function.grad x) (v.toH1Function.grad x) :=
        hPoinU v
    _ ≤ Pu * (16 * eps ^ 2 * Pw * ∫ x in W, b x) := mul_le_mul_of_nonneg_left hX hPu
    _ = 16 * eps ^ 2 * Pu * Pw * ∫ x in W, b x := by ring

/-! ## Real forms of the two Poincaré inputs -/

theorem lpSq_two_eq_ofReal_integral {W : Set (Vec d)} (hW : MeasurableSet W)
    {rho f : Vec d → ℝ} (hrho : AEMeasurable rho (volume.restrict W))
    (hf : AEMeasurable f (volume.restrict W)) (hrho0 : ∀ x ∈ W, 0 ≤ rho x)
    (hint : Integrable (fun x => rho x * (f x * f x)) (volume.restrict W)) :
    lpSq rho W 2 f = ENNReal.ofReal (∫ x in W, rho x * (f x * f x)) := by
  rw [Section8Support.LocalResolventIteration.lpSq_two_eq_lintegral]
  unfold weightedMeasure
  rw [restrict_withDensity hW, lintegral_withDensity_eq_lintegral_mul₀ hrho.ennreal_ofReal
    (show AEMeasurable (fun x => ENNReal.ofReal (f x * f x)) (volume.restrict W) from by
      simpa only using! (hf.mul hf).ennreal_ofReal)]
  rw [ofReal_integral_eq_lintegral_ofReal hint ?_]
  · refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hW] with x hx
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hrho0 x hx)]
  · filter_upwards [ae_restrict_mem hW] with x hx
    exact mul_nonneg (hrho0 x hx) (mul_self_nonneg _)

/-- The weighted Poincaré interface in real form. -/
theorem poincare_real_of_weighted {W : Set (Vec d)} (hW : MeasurableSet W)
    {b : Vec d → ℝ} {A F B : ℝ} (hbm : AEStronglyMeasurable b (volume.restrict W))
    (hb0 : ∀ x ∈ W, 0 ≤ b x) (hbB : ∀ x ∈ W, b x ≤ B) (hAF : 0 ≤ A * F)
    (h : PoincareAssumption b b W A F) (f : H10Function W) :
    ∫ x in W, b x * (f.toH1Function.toFun x * f.toH1Function.toFun x) ≤
      (A * F) * ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) := by
  have hbabs : ∀ x ∈ W, |b x| ≤ B := fun x hx => by
    rw [abs_of_nonneg (hb0 x hx)]; exact hbB x hx
  have hint := integrable_coeff_mul hW hbm hbabs
    (integrable_toFun_mul f.toH1Function f.toH1Function)
  have hl := h f
  rw [lpSq_two_eq_ofReal_integral hW hbm.aemeasurable
    f.toH1Function.memL2.aestronglyMeasurable.aemeasurable hb0 hint] at hl
  unfold energy at hl
  have hE : 0 ≤ ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) :=
    setIntegral_nonneg hW fun x hx => mul_nonneg (hb0 x hx) (vecNormSq_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hAF hE)).mp hl

/-- The unweighted (Lebesgue) Poincaré interface in real form. -/
theorem poincare_real_of_unweighted {W : Set (Vec d)} (hW : MeasurableSet W)
    {b : Vec d → ℝ} {A F : ℝ} (hb0 : ∀ x ∈ W, 0 ≤ b x) (hAF : 0 ≤ A * F)
    (h : PoincareAssumption b (fun _ => 1) W A F) (f : H10Function W) :
    ∫ x in W, f.toH1Function.toFun x * f.toH1Function.toFun x ≤
      (A * F) * ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) := by
  have hl := h f
  rw [Packet449.lpSq_one_two_eq_integral] at hl
  unfold energy at hl
  have hE : 0 ≤ ∫ x in W, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x) :=
    setIntegral_nonneg hW fun x hx => mul_nonneg (hb0 x hx) (vecNormSq_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hAF hE)).mp hl

/-! ## The weighted torsion exists -/

/-- An elliptic scalar coefficient admits an actual zero-trace weighted-forcing torsion. -/
theorem exists_weightedTorsion {Q : TriadicCube d} [NeZero d] {b : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (hb2 : MemLp b 2 (volume.restrict (openCubeSet Q))) :
    ∃ e : H10Function (openCubeSet Q),
      IsMassiveWeakSolutionOn b b 0 (openCubeSet Q) e.toH1Function (fun _ => 1) := by
  obtain ⟨v, hv⟩ := exists_isScalarDirichletSolutionOn hEll
    (0 : H1Function (openCubeSet Q)) hb2
  obtain ⟨u, hval, hgrad⟩ := hv.1
  have hgrad' : v.grad = u.toH1Function.grad := by
    funext x
    simpa only [H1Function.zero_grad, Pi.zero_apply, zero_add] using hgrad x
  refine ⟨u, ?_⟩
  intro phi
  have heq := hv.2 phi
  rw [hgrad'] at heq
  simpa only [scalarCoeffField, matVecMul_scalarMatrix, zero_mul, zero_add, mul_one] using heq

/-! ## From the raw square integral to the normalized norm -/

theorem cubeLpNorm_le_of_setIntegral_sq_le {Q : TriadicCube d}
    (f : H1Function (openCubeSet Q)) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫ x in openCubeSet Q, f.toFun x * f.toFun x ≤ K ^ 2 * cubeVolume Q) :
    cubeLpNorm Q 2 f.toFun ≤ K := by
  have hint := setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
    Q f.toFun (Section8Support.WeightedEnergy.h1_memLp_normalizedCubeMeasure Q f)
  rw [Real.rpow_two] at hint
  rw [hint] at h
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  have hsq : (cubeLpNorm Q 2 f.toFun) ^ 2 ≤ K ^ 2 := by
    have := (mul_le_mul_iff_of_pos_left hv).mp (by linarith [h] :
      cubeVolume Q * (cubeLpNorm Q 2 f.toFun) ^ 2 ≤ cubeVolume Q * K ^ 2)
    exact this
  exact (sq_le_sq₀ (cubeLpNorm_nonneg _ _ _) hK).mp hsq

/-! ## Step T, the test transfer -/

/-- **Step T.**  The torsion comparison test of `b` at tolerance `epsT` transfers to `b·θ`
for every multiplier with `|k⁻¹θ - 1| ≤ ε ≤ 1/2` on the cube, at tolerance `epsT + epsX`,
provided `4 ε √(P_u P_w M_b) ≤ epsX · side² / σ`.  The multiplier's scale `k` cancels; only
`‖k⁻¹θ - 1‖_∞` enters, with an additive loss. -/
theorem goodCubeTorsionComparisonTest_mul_of_poincare [NeZero d]
    {Q : TriadicCube d} {b th : Vec d → ℝ} {k eps sigma epsT epsX Pw Pu Mb B lam Lam : ℝ}
    (heps : 0 < eps) (heps2 : eps ≤ 1 / 2) (hPw : 0 < Pw) (hPu : 0 ≤ Pu)
    (hMb : 0 ≤ Mb)
    (hbm : AEStronglyMeasurable b (volume.restrict (openCubeSet Q)))
    (hthm : AEStronglyMeasurable th (volume.restrict (openCubeSet Q)))
    (hb0 : ∀ x ∈ openCubeSet Q, 0 ≤ b x) (hbB : ∀ x ∈ openCubeSet Q, b x ≤ B)
    (hth : ∀ x ∈ openCubeSet Q, |k⁻¹ * th x - 1| ≤ eps)
    (hPoinW : ∀ f : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, b x * (f.toH1Function.toFun x * f.toH1Function.toFun x) ≤
        Pw * ∫ x in openCubeSet Q, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
    (hPoinU : ∀ f : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, f.toH1Function.toFun x * f.toH1Function.toFun x ≤
        Pu * ∫ x in openCubeSet Q, b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (hb2 : MemLp b 2 (volume.restrict (openCubeSet Q)))
    (hmass : ∫ x in openCubeSet Q, b x ≤ Mb * cubeVolume Q)
    (hmargin : 4 * eps * Real.sqrt (Pu * Pw * Mb) ≤ epsX * (cubeScaleFactor Q) ^ 2 / sigma)
    (htest : GoodCubeTorsionComparisonTest Q b sigma epsT) :
    GoodCubeTorsionComparisonTest Q (fun x => b x * th x) sigma (epsT + epsX) := by
  let : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hQm : MeasurableSet (openCubeSet Q) := measurableSet_openCubeSet Q
  intro u w hu hw
  obtain ⟨e, he⟩ := exists_weightedTorsion hEll hb2
  have hu' : IsMassiveWeakSolutionOn (fun x => b x * (k⁻¹ * th x))
      (fun x => b x * (k⁻¹ * th x)) 0 (openCubeSet Q) u.toH1Function (fun _ => 1) := by
    have h := isMassiveWeakSolutionOn_const_mul k⁻¹ hu
    have hfun : (fun x => k⁻¹ * (b x * th x)) = fun x => b x * (k⁻¹ * th x) := by
      funext x; ring
    simpa only [hfun] using h
  have hsq := torsion_perturbation_sq (th := fun x => k⁻¹ * th x) hQm heps heps2 hPw hPu hbm
    (hthm.const_mul k⁻¹) hb0 hbB hth hPoinW hPoinU e u he hu'
  have hK : 0 ≤ 4 * eps * Real.sqrt (Pu * Pw * Mb) := by positivity
  have hue : cubeLpNorm Q 2 (u - e).toH1Function.toFun ≤ 4 * eps * Real.sqrt (Pu * Pw * Mb) := by
    refine cubeLpNorm_le_of_setIntegral_sq_le _ hK (hsq.trans ?_)
    have hsqrt : Real.sqrt (Pu * Pw * Mb) ^ 2 = Pu * Pw * Mb :=
      Real.sq_sqrt (by positivity)
    have hc : 0 ≤ 16 * eps ^ 2 * Pu * Pw := by positivity
    calc 16 * eps ^ 2 * Pu * Pw * ∫ x in openCubeSet Q, b x
        ≤ 16 * eps ^ 2 * Pu * Pw * (Mb * cubeVolume Q) := mul_le_mul_of_nonneg_left hmass hc
      _ = (4 * eps * Real.sqrt (Pu * Pw * Mb)) ^ 2 * cubeVolume Q := by
        rw [mul_pow, mul_pow, hsqrt]; ring
  have hew : cubeLpNorm Q 2 (e - w).toH1Function.toFun ≤
      epsT * (cubeScaleFactor Q) ^ 2 / sigma := by
    have h := htest e w he hw
    have hfun : (e - w).toH1Function.toFun =
        fun x => e.toH1Function.toFun x - w.toH1Function.toFun x := by
      change (e.toH1Function - w.toH1Function).toFun = _
      rw [H1Function.sub_toFun]
    rw [hfun]
    exact h
  have htri := goodCube_h10_cubeLpNorm_sub_triangle Q u e w
  have hfun : (fun x => u.toH1Function.toFun x - w.toH1Function.toFun x) =
      (u - w).toH1Function.toFun := by
    change _ = (u.toH1Function - w.toH1Function).toFun
    rw [H1Function.sub_toFun]
  rw [hfun]
  calc cubeLpNorm Q 2 (u - w).toH1Function.toFun
      ≤ cubeLpNorm Q 2 (u - e).toH1Function.toFun +
          cubeLpNorm Q 2 (e - w).toH1Function.toFun := htri
    _ ≤ epsX * (cubeScaleFactor Q) ^ 2 / sigma + epsT * (cubeScaleFactor Q) ^ 2 / sigma :=
        add_le_add (hue.trans hmargin) hew
    _ = (epsT + epsX) * (cubeScaleFactor Q) ^ 2 / sigma := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube


