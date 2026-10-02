import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane3.DirichletForm

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology RealInnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The dual quadratic functional of a (linear, bounded) map `G`. -/
def aux_mosco_Q (G : H → H) (x f : H) : ℝ := 2 * ⟪f, x⟫ - ⟪f, G f⟫

theorem aux_mosco_Q_add_smul (G : H → H) (hadd : ∀ f g, G (f + g) = G f + G g)
    (hsmul : ∀ (c : ℝ) f, G (c • f) = c • G f) (hsym : ∀ f g, ⟪f, G g⟫ = ⟪g, G f⟫)
    (x f h : H) (t : ℝ) :
    aux_mosco_Q G x (f + t • h) = aux_mosco_Q G x f + 2 * t * ⟪h, x - G f⟫ - t ^ 2 * ⟪h, G h⟫ := by
  simp only [aux_mosco_Q, hadd, hsmul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_sub_right, RCLike.conj_to_real]
  rw [hsym f h]
  ring

theorem aux_mosco_norm_sub_sq_le (G : H → H) (hadd : ∀ f g, G (f + g) = G f + G g)
    (hsmul : ∀ (c : ℝ) f, G (c • f) = c • G f) (hsym : ∀ f g, ⟪f, G g⟫ = ⟪g, G f⟫)
    (CG : ℝ) (hCG : 0 ≤ CG) (hbd : ∀ h, ‖G h‖ ≤ CG * ‖h‖)
    (x : H) (e : ℝ) (hQ : ∀ f, aux_mosco_Q G x f ≤ e) (f : H) :
    ‖x - G f‖ ^ 2 ≤ (CG + 1) * (e - aux_mosco_Q G x f) := by
  set h := x - G f with hh
  set t : ℝ := (CG + 1)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr (by linarith)
  have htG : t * CG ≤ 1 := by
    rw [ht, inv_mul_le_iff₀ (by linarith)]; linarith
  have hGh : ⟪h, G h⟫ ≤ CG * ‖h‖ ^ 2 := by
    calc ⟪h, G h⟫ ≤ ‖h‖ * ‖G h‖ := real_inner_le_norm _ _
      _ ≤ ‖h‖ * (CG * ‖h‖) := mul_le_mul_of_nonneg_left (hbd h) (norm_nonneg _)
      _ = CG * ‖h‖ ^ 2 := by ring
  have hkey := hQ (f + t • h)
  rw [aux_mosco_Q_add_smul G hadd hsmul hsym x f h t, ← hh, real_inner_self_eq_norm_sq] at hkey
  have h2 : t ^ 2 * ⟪h, G h⟫ ≤ t * ‖h‖ ^ 2 := by
    calc t ^ 2 * ⟪h, G h⟫ ≤ t ^ 2 * (CG * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_left hGh (sq_nonneg _)
      _ = t * (t * CG) * ‖h‖ ^ 2 := by ring
      _ ≤ t * 1 * ‖h‖ ^ 2 := by gcongr
      _ = t * ‖h‖ ^ 2 := by ring
  have h3 : t * ‖h‖ ^ 2 ≤ e - aux_mosco_Q G x f := by nlinarith
  calc ‖h‖ ^ 2 = (CG + 1) * (t * ‖h‖ ^ 2) := by
        rw [ht, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]
    _ ≤ (CG + 1) * (e - aux_mosco_Q G x f) := mul_le_mul_of_nonneg_left h3 (by linarith)

theorem aux_mosco_inner_self_near (G : H → H) (hsmul : ∀ (c : ℝ) f, G (c • f) = c • G f)
    (hpos : ∀ f, 0 ≤ ⟪f, G f⟫)
    (x : H) (e : ℝ) (hQ : ∀ f, aux_mosco_Q G x f ≤ e) (f : H) (ε : ℝ)
    (hε : e - ε ≤ aux_mosco_Q G x f) :
    |⟪f, G f⟫ - e| ≤ 2 * Real.sqrt (e * ε) + ε := by
  set α := ⟪f, x⟫ with hα
  set β := ⟪f, G f⟫ with hβ
  have he0 : 0 ≤ e := by
    have h0 := hQ 0
    have hG0 : G 0 = 0 := by simpa using hsmul 0 0
    simp [aux_mosco_Q, hG0] at h0; linarith
  have hβ0 : 0 ≤ β := hpos f
  have hscale : ∀ s : ℝ, 2 * s * α - s ^ 2 * β ≤ e := by
    intro s
    have := hQ (s • f)
    simp only [aux_mosco_Q, hsmul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at this
    nlinarith [this]
  have hαβ : α ^ 2 ≤ e * β := by
    rcases hβ0.eq_or_lt with hb | hb
    · have hα0 : α = 0 := by
        by_contra hne
        have h1 := hscale ((e + 1) / (2 * α))
        rw [← hb, mul_zero, sub_zero] at h1
        have h2 : 2 * ((e + 1) / (2 * α)) * α = e + 1 := by field_simp
        linarith
      rw [hα0, ← hb]; simp
    · have := hscale (α / β)
      have : α ^ 2 / β ≤ e := by
        have h' : 2 * (α / β) * α - (α / β) ^ 2 * β = α ^ 2 / β := by field_simp; ring
        linarith
      rwa [div_le_iff₀ hb] at this
  have hQf : aux_mosco_Q G x f = 2 * α - β := rfl
  have hε0 : 0 ≤ ε := by have := hQ f; linarith
  have hsq : (α - e) ^ 2 ≤ e * ε := by nlinarith
  have hαe : |α - e| ≤ Real.sqrt (e * ε) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq
  have hQle : aux_mosco_Q G x f ≤ e := hQ f
  rw [abs_le] at hαe ⊢
  constructor <;> nlinarith [Real.sqrt_nonneg (e * ε)]

/-- Diagonal extraction: if every row tends to zero, a slowly growing index makes the
diagonal tend to zero. -/
theorem aux_mosco_exists_diag (u : ℕ → ℕ → ℝ) (hu : ∀ k, Tendsto (u k) atTop (𝓝 0)) (hu0 : ∀ k N, 0 ≤ u k N) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ ∀ N, u (κ N) N ≤ 1 / ((κ N : ℝ) + 1) ∨ κ N = 0 := by
  classical
  have hN0 : ∀ k, ∃ n0, ∀ N ≥ n0, u k N < 1 / ((k : ℝ) + 1) := fun k =>
    ((hu k).eventually (gt_mem_nhds (by positivity))).exists_forall_of_atTop
  choose n0 hn0 using hN0
  let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup n0 + k
  have hMk : ∀ k, n0 k ≤ M k := fun k =>
    (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans (Nat.le_add_right _ _)
  have hMge : ∀ k, k ≤ M k := fun k => Nat.le_add_left _ _
  have hMmono : Monotone M := by
    intro a b hab
    exact Nat.add_le_add (Finset.sup_mono fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hab))) hab
  let κ : ℕ → ℕ := fun N => Nat.findGreatest (fun k => M k ≤ N) N
  refine ⟨κ, ?_, fun N => ?_⟩
  · rw [tendsto_atTop_atTop]
    intro K
    refine ⟨M K, fun N hN => ?_⟩
    exact Nat.le_findGreatest ((hMge K).trans hN) hN
  · by_cases h0 : κ N = 0
    · exact Or.inr h0
    · left
      have hspec : M (κ N) ≤ N :=
        Nat.findGreatest_of_ne_zero (P := fun k => M k ≤ N) (n := N) (m := κ N) rfl h0
      exact (hn0 (κ N) N ((hMk _).trans hspec)).le


/-- The recovery sequence, abstractly: a diagonal of solutions of near-maximizing loads. -/
theorem aux_mosco_recovery (G : H → H) (hadd : ∀ f g, G (f + g) = G f + G g)
    (hsmul : ∀ (c : ℝ) f, G (c • f) = c • G f) (CG : ℝ) (hCG : 0 ≤ CG) (hbd : ∀ h, ‖G h‖ ≤ CG * ‖h‖)
    (hGsym : ∀ f g, ⟪f, G g⟫ = ⟪g, G f⟫)
    (hGpos : ∀ f, 0 ≤ ⟪f, G f⟫) (GN : ℕ → H → H)
    (hGN : ∀ f, Tendsto (fun N => GN N f) atTop (𝓝 (G f)))
    (EN : ℕ → H → ℝ≥0∞) (hEN : ∀ N f, EN N (GN N f) ≤ ENNReal.ofReal ⟪f, GN N f⟫)
    (x : H) (e : ℝ) (hQ : ∀ f, aux_mosco_Q G x f ≤ e)
    (hnear : ∀ k : ℕ, ∃ f, e - 1 / ((k : ℝ) + 1) ≤ aux_mosco_Q G x f) :
    ∃ y : ℕ → H, Tendsto y atTop (𝓝 x) ∧ limsup (fun N => EN N (y N)) atTop ≤ ENNReal.ofReal e := by
  choose fk hfk using hnear
  have he0 : 0 ≤ e := by have := hQ 0; simp [aux_mosco_Q] at this; linarith
  let u : ℕ → ℕ → ℝ := fun k N => ‖GN N (fk k) - G (fk k)‖ + |⟪fk k, GN N (fk k)⟫ - ⟪fk k, G (fk k)⟫|
  have hurow : ∀ k, Tendsto (u k) atTop (𝓝 0) := by
    intro k
    have h1 : Tendsto (fun N => ‖GN N (fk k) - G (fk k)‖) atTop (𝓝 0) := by
      simpa using ((hGN (fk k)).sub_const (G (fk k))).norm
    have h2 : Tendsto (fun N => |⟪fk k, GN N (fk k)⟫ - ⟪fk k, G (fk k)⟫|) atTop (𝓝 0) := by
      simpa using (((tendsto_const_nhds (x := fk k)).inner (𝕜 := ℝ) (hGN (fk k))).sub_const
        ⟪fk k, G (fk k)⟫).abs
    simpa using h1.add h2
  obtain ⟨κ, hκ, hκu⟩ := aux_mosco_exists_diag u hurow (fun k N => by positivity)
  have hκne : ∀ᶠ N in atTop, κ N ≠ 0 := hκ.eventually (eventually_ne_atTop 0)
  have h1k : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) + Real.sqrt ((CG + 1) * (1 / ((k : ℝ) + 1))))
      atTop (𝓝 0) := by
    simpa using h1k.add ((h1k.const_mul (CG + 1)).sqrt)
  have hs : Tendsto (fun k : ℕ => e + 2 * Real.sqrt (e * (1 / ((k : ℝ) + 1))) + 2 * (1 / ((k : ℝ) + 1)))
      atTop (𝓝 e) := by
    simpa using ((tendsto_const_nhds (x := e)).add (((h1k.const_mul e).sqrt).const_mul 2)).add
      (h1k.const_mul 2)
  refine ⟨fun N => GN N (fk (κ N)), ?_, ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ (hr.comp hκ)
    filter_upwards [hκne] with N hN
    have hk := (hκu N).resolve_right hN
    have hx := aux_mosco_norm_sub_sq_le G hadd hsmul hGsym CG hCG hbd x e hQ (fk (κ N))
    have hxk : ‖x - G (fk (κ N))‖ ≤ Real.sqrt ((CG + 1) * (1 / ((κ N : ℝ) + 1))) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      refine Real.sqrt_le_sqrt (hx.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
      linarith [hfk (κ N)]
    have hu1 : ‖GN N (fk (κ N)) - G (fk (κ N))‖ ≤ u (κ N) N :=
      le_add_of_nonneg_right (abs_nonneg _)
    calc dist (GN N (fk (κ N))) x ≤ ‖GN N (fk (κ N)) - G (fk (κ N))‖ + ‖G (fk (κ N)) - x‖ := by
          rw [dist_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / ((κ N : ℝ) + 1) + Real.sqrt ((CG + 1) * (1 / ((κ N : ℝ) + 1))) := by
          rw [norm_sub_rev (G _) x]
          exact add_le_add (hu1.trans hk) hxk
  · have hlim : Tendsto (fun N => ENNReal.ofReal (e + 2 * Real.sqrt (e * (1 / ((κ N : ℝ) + 1))) +
        2 * (1 / ((κ N : ℝ) + 1)))) atTop (𝓝 (ENNReal.ofReal e)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hs.comp hκ)
    rw [← hlim.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [hκne] with N hN
    have hk := (hκu N).resolve_right hN
    have hnear := aux_mosco_inner_self_near G hsmul hGpos x e hQ (fk (κ N)) (1 / ((κ N : ℝ) + 1))
      (hfk (κ N))
    have hu2 : |⟪fk (κ N), GN N (fk (κ N))⟫ - ⟪fk (κ N), G (fk (κ N))⟫| ≤ u (κ N) N :=
      le_add_of_nonneg_left (norm_nonneg _)
    refine (hEN N (fk (κ N))).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_le] at hnear hu2
    linarith [hk]

end Abstract

/-- Upper bounds pass through `EReal.toENNReal` of a real supremum. -/
theorem aux_mosco_toENNReal_iSup_le {ι : Type*} (c : ι → ℝ) (L : ℝ≥0∞)
    (h : ∀ i, ENNReal.ofReal (c i) ≤ L) : (⨆ i, ((c i : ℝ) : EReal)).toENNReal ≤ L := by
  by_cases hL : L = ⊤
  · rw [hL]; exact le_top
  have hle : (⨆ i, ((c i : ℝ) : EReal)) ≤ ((L.toReal : ℝ) : EReal) :=
    iSup_le fun i => EReal.coe_le_coe_iff.mpr ((ENNReal.ofReal_le_iff_le_toReal hL).mp (h i))
  calc (⨆ i, ((c i : ℝ) : EReal)).toENNReal ≤ ((L.toReal : ℝ) : EReal).toENNReal :=
        EReal.toENNReal_le_toENNReal hle
    _ = L := by rw [EReal.real_coe_toENNReal, ENNReal.ofReal_toReal hL]

/-- The recovery lemma, specialized to `L²` classes on a domain. -/
theorem aux_mosco_recovery_L2 {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω) (hGsym : ∀ f g : DomainL2 Ω, ⟪f, G g⟫ = ⟪g, G f⟫)
    (hGpos : ∀ f : DomainL2 Ω, 0 ≤ ⟪f, G f⟫) (GN : ℕ → DomainL2 Ω → DomainL2 Ω)
    (hGN : ∀ f, Tendsto (fun N => GN N f) atTop (𝓝 (G f)))
    (EN : ℕ → DomainL2 Ω → ℝ≥0∞) (hEN : ∀ N f, EN N (GN N f) ≤ ENNReal.ofReal ⟪f, GN N f⟫)
    (x : DomainL2 Ω) (e : ℝ) (hQ : ∀ f, aux_mosco_Q (⇑G) x f ≤ e)
    (hnear : ∀ k : ℕ, ∃ f, e - 1 / ((k : ℝ) + 1) ≤ aux_mosco_Q (⇑G) x f) :
    ∃ y : ℕ → DomainL2 Ω, Tendsto y atTop (𝓝 x) ∧
      limsup (fun N => EN N (y N)) atTop ≤ ENNReal.ofReal e :=
  aux_mosco_recovery (⇑G) (fun f g => by simpa using map_add G f g)
    (fun c f => by simpa using map_smul G c f) ‖G‖ (norm_nonneg _) (fun h => G.le_opNorm h)
    hGsym hGpos GN hGN EN hEN x e hQ hnear


section Response
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The solution of the volume load `f`. -/
abbrev aux_mosco_W (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω) : S.space :=
  responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)

theorem aux_mosco_spec (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω)
    (ψ : S.space) :
    sobolevCoefficientForm a (aux_mosco_W S a f : SobolevData Ω) (ψ : SobolevData Ω) =
      ⟪f, (ψ : SobolevData Ω).1⟫ :=
  responseSolution_spec S a _ ψ

/-- The variational inequality `a(v,v) ≥ 2⟪f,v⟫ - ⟪f, G f⟫`. -/
theorem aux_mosco_var (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω)
    (v : S.space) :
    2 * ⟪f, (v : SobolevData Ω).1⟫ - ⟪f, (aux_mosco_W S a f : SobolevData Ω).1⟫ ≤
      sobolevCoefficientForm a (v : SobolevData Ω) (v : SobolevData Ω) := by
  set w := aux_mosco_W S a f
  have h0 := sobolevCoefficientForm_nonneg a ((v : SobolevData Ω) - (w : SobolevData Ω))
  have hwv := aux_mosco_spec S a f v
  have hww := aux_mosco_spec S a f w
  have hvw : sobolevCoefficientForm a (v : SobolevData Ω) (w : SobolevData Ω) =
      sobolevCoefficientForm a (w : SobolevData Ω) (v : SobolevData Ω) :=
    sobolevCoefficientForm_symm a _ _
  simp only [map_sub, ContinuousLinearMap.sub_apply] at h0
  linarith

theorem aux_mosco_sym (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f g : DomainL2 Ω) :
    ⟪f, (aux_mosco_W S a g : SobolevData Ω).1⟫ = ⟪g, (aux_mosco_W S a f : SobolevData Ω).1⟫ := by
  rw [← aux_mosco_spec S a f (aux_mosco_W S a g), ← aux_mosco_spec S a g (aux_mosco_W S a f)]
  exact sobolevCoefficientForm_symm a _ _

theorem aux_mosco_pos (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (f : DomainL2 Ω) :
    0 ≤ ⟪f, (aux_mosco_W S a f : SobolevData Ω).1⟫ := by
  rw [← aux_mosco_spec S a f (aux_mosco_W S a f)]
  exact sobolevCoefficientForm_nonneg a _

/-- The energy of the killed solution bounds the inf-convolution energy at its value. -/
theorem aux_mosco_lift {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph Ω,
      ‖(v : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) v‖)
    (a : PositiveCoefficient Ω) (f : DomainL2 Ω) :
    (⨅ v : {v : killedSobolevGraph Ω //
        (v : SobolevData Ω).1 = (aux_mosco_W (killedResponseSpace hP) a f : SobolevData Ω).1},
      ENNReal.ofReal (sobolevCoefficientForm a (v.val : SobolevData Ω) (v.val : SobolevData Ω))) ≤
      ENNReal.ofReal ⟪f, (aux_mosco_W (killedResponseSpace hP) a f : SobolevData Ω).1⟫ := by
  refine (iInf_le _ ⟨aux_mosco_W (killedResponseSpace hP) a f, rfl⟩).trans ?_
  exact le_of_eq (congrArg ENNReal.ofReal
    (aux_mosco_spec (killedResponseSpace hP) a f (aux_mosco_W (killedResponseSpace hP) a f)))

end Response

/-- classical, cited: Mosco convergence (Mosco 1994, *Composite media and asymptotic
Dirichlet forms*; Dal Maso, *An Introduction to Γ-Convergence*, Ch. 13) applied to the
resolvent formulation of Dirichlet-form convergence (Kuwae–Shioya, *Convergence of
spectral structures*). Strong resolvent convergence of the finite-cutoff killed
Dirichlet forms to a limit operator `G` upgrades to the two Mosco conditions for the
inf-convolution extension of the finite-cutoff energies to the whole `L²` space: the
Γ-liminf inequality along every strongly convergent sequence, and the existence of a
recovery sequence for every point of finite limiting energy. -/
theorem inputs_classical_mosco_liminf {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph Ω,
      ‖(v : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) v‖)
    (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hG : ∀ f : DomainL2 Ω,
      Tendsto (fun N => (responseSolution (killedResponseSpace hP) (a N)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f))) :
    Lane3.MoscoLiminf
      (fun N u => ⨅ v : {v : killedSobolevGraph Ω // (v : SobolevData Ω).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm (a N)
          (v.val : SobolevData Ω) (v.val : SobolevData Ω)))
      (fun u => (limitFormEnergy G u).toENNReal) ∧
    Lane3.MoscoRecovery
      (fun N u => ⨅ v : {v : killedSobolevGraph Ω // (v : SobolevData Ω).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm (a N)
          (v.val : SobolevData Ω) (v.val : SobolevData Ω)))
      (fun u => (limitFormEnergy G u).toENNReal) := by
  classical
  have hGf : ∀ f, Tendsto (fun N => (aux_mosco_W (killedResponseSpace hP) (a N) f : SobolevData Ω).1)
      atTop (𝓝 (G f)) := hG
  -- symmetry and positivity of the limit operator
  have hGsym : ∀ f g, ⟪f, G g⟫ = ⟪g, G f⟫ := by
    intro f g
    refine tendsto_nhds_unique ((tendsto_const_nhds (x := f)).inner (𝕜 := ℝ) (hGf g)) ?_
    have h := (tendsto_const_nhds (x := g)).inner (𝕜 := ℝ) (hGf f)
    refine h.congr fun N => ?_
    exact (aux_mosco_sym (killedResponseSpace hP) (a N) f g).symm
  have hGpos : ∀ f, 0 ≤ ⟪f, G f⟫ := fun f =>
    ge_of_tendsto ((tendsto_const_nhds (x := f)).inner (𝕜 := ℝ) (hGf f))
      (Eventually.of_forall fun N => aux_mosco_pos (killedResponseSpace hP) (a N) f)
  refine ⟨fun x y hy => ?_, fun x => ?_⟩
  · -- the Γ-liminf inequality
    show (limitFormEnergy G x).toENNReal ≤ _
    unfold limitFormEnergy
    refine aux_mosco_toENNReal_iSup_le _ _ fun f => ?_
    have hc : Tendsto (fun n => ENNReal.ofReal (2 * ⟪f, y n⟫ - ⟪f, (aux_mosco_W (killedResponseSpace hP) (a n) f : SobolevData Ω).1⟫))
        atTop (𝓝 (ENNReal.ofReal (2 * ⟪f, x⟫ - ⟪f, G f⟫))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((((tendsto_const_nhds (x := f)).inner (𝕜 := ℝ) hy).const_mul 2).sub
          ((tendsto_const_nhds (x := f)).inner (𝕜 := ℝ) (hGf f)))
    rw [← hc.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    refine le_iInf fun v => ?_
    have hv := aux_mosco_var (killedResponseSpace hP) (a n) f v.val
    have hv1 : (v.val : SobolevData Ω).1 = y n := v.property
    rw [hv1] at hv
    exact ENNReal.ofReal_le_ofReal hv
  · -- the recovery sequence
    by_cases htop : limitFormEnergy G x = ⊤
    · refine ⟨fun _ => x, tendsto_const_nhds, ?_⟩
      show _ ≤ (limitFormEnergy G x).toENNReal
      rw [htop, EReal.toENNReal_top]; exact le_top
    have hE0 : ((0 : ℝ) : EReal) ≤ limitFormEnergy G x := by
      unfold limitFormEnergy
      refine le_trans ?_ (le_iSup _ (0 : DomainL2 Ω))
      simp
    have hbot : limitFormEnergy G x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) hE0
    set e : ℝ := (limitFormEnergy G x).toReal with he
    have hEe : limitFormEnergy G x = (e : EReal) := (EReal.coe_toReal htop hbot).symm
    have hQ : ∀ f, aux_mosco_Q (⇑G) x f ≤ e := by
      intro f
      have h : ((aux_mosco_Q (⇑G) x f : ℝ) : EReal) ≤ limitFormEnergy G x := by
        unfold limitFormEnergy; exact le_iSup (fun f => ((2 * ⟪f, x⟫ - ⟪f, G f⟫ : ℝ) : EReal)) f
      rw [hEe] at h; exact EReal.coe_le_coe_iff.mp h
    have hnear : ∀ k : ℕ, ∃ f, e - 1 / ((k : ℝ) + 1) ≤ aux_mosco_Q (⇑G) x f := by
      intro k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hlt : ((e - 1 / ((k : ℝ) + 1) : ℝ) : EReal) < limitFormEnergy G x := by
        rw [hEe]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
      unfold limitFormEnergy at hlt
      obtain ⟨f, hf⟩ := lt_iSup_iff.mp hlt
      exact ⟨f, (EReal.coe_lt_coe_iff.mp hf).le⟩
    obtain ⟨y, hyx, hlim⟩ := aux_mosco_recovery_L2 G hGsym hGpos
      (fun N f => (aux_mosco_W (killedResponseSpace hP) (a N) f : SobolevData Ω).1) hGf
      (fun N u => ⨅ v : {v : killedSobolevGraph Ω // (v : SobolevData Ω).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm (a N) (v.val : SobolevData Ω) (v.val : SobolevData Ω)))
      (fun N f => aux_mosco_lift hP (a N) f) x e hQ hnear
    have heq : ENNReal.ofReal e = (limitFormEnergy G x).toENNReal := by
      rw [hEe, EReal.real_coe_toENNReal]
    exact ⟨y, hyx, hlim.trans heq.le⟩

end Paper
