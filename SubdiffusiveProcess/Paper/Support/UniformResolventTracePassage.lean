module

public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set Metric SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_ident_trace_passage {d : ℕ} (hd : 2 ≤ d)
    (zc : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube zc
        r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube zc
        r hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : CubeTraceCharacterization hd zc hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube zc
      r hr))
    (z : CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd zc
        r hr Lane4.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd zc
      r hr Lane4.threeQuarterOrder (w3 k) ≤ B)
    (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ) :
    Tendsto (fun k => ∫ x, (s k x - ψ x) ^ 2 ∂(ν k)) atTop
      (𝓝 (∫ x, (T z x - ψ x) ^ 2 ∂μ)) := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube zc
    r hr : Set (SpatialCoordinates d)) with hQs
  have hKc : IsCompact (closure Qs) := (centeredCube_isBounded zc hr).isCompact_closure
  haveI hνfinI : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨⟨C, hC0, htr⟩, hinterp⟩ := lem_19 d hd SInterp zc r hr t ht
  -- finite-cutoff traces: identity on `H^{1/2}` elements, one Lipschitz constant
  have hTk : ∀ k, ∃ Tk : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder →
      Lp ℝ 2 (ν k),
      (∀ (u v w : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder),
        w.val 0 = u.val 0 - v.val 0 →
        ‖Tk u - Tk v‖ ^ 2 ≤ C * (Kμ + (ν k (closure Qs)).toReal) *
          (cubeFractionalL2Norm hd zc r hr halfFractionalOrder w) ^ 2) ∧
      (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (v : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder),
          (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Qs] f →
          ∀ hf : MemLp f 2 (ν k), Tk v = hf.toLp f) ∧
      (∀ u : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder,
        MemLp (u.val 0) 2 (ν k) ∧ ∀ hu : MemLp (u.val 0) 2 (ν k), Tk u = hu.toLp (u.val 0)) := by
    intro k
    obtain ⟨D, hD0, hD⟩ := hνdens k
    obtain ⟨Tk, ⟨_, hlip, hsm, _, hden⟩, _⟩ :=
      htr (ν k) Kμ (hνfin k) (hνsupp k) hKμ (hνgrowth k)
    exact ⟨Tk, hlip, hsm, hden D hD0 hD⟩
  choose Tk hTk_lip hTk_sm hTk_id using hTk
  -- interpolation upgrade
  obtain ⟨vhalf, hvhalf, diff, hdiff, hdiff0⟩ :=
    hinterp Lane4.threeQuarterOrder rfl w3 (z.val 0) B hB
      (by simpa only [hw3] using hs)
  -- smooth approximation of `z` for the limit measure
  obtain ⟨a, f, w, hfsm, haf, hw, hw0⟩ := lem_19_smooth_density d hd zc r hr z
  have hfLp : ∀ n, MemLp (f n) 2 μ := fun n =>
    aux_mfd_prop_uniform_resolvent_smooth_memLp zc r hr μ hμsupp (f n) (hfsm n)
  -- `H^{1/2}` elements with prescribed first coordinate
  obtain ⟨zero, hzero⟩ := hT.1 z z
  obtain ⟨neg, hneg⟩ := hT.1 zero z
  have hS : ∀ k, ∃ Sk : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder,
      Sk.val 0 = s k := by
    intro k
    obtain ⟨Sk, hSk⟩ := hT.1 (diff k) neg
    refine ⟨Sk, ?_⟩
    rw [hSk, hdiff k, hneg, hzero, hw3 k]
    abel
  choose S hSval using hS
  -- constants
  set L : ℝ := Real.sqrt (C * (Kμ + Mbar)) with hLdef
  set Lμ : ℝ := Real.sqrt (Ctr * (Ktr + (μ (closure ((centeredCube zc r hr : Set (SpatialCoordinates d))))).toReal))
    with hLμdef
  have hMbar : ∀ k, 0 ≤ Kμ + Mbar := fun k => by
    have := hνmass k
    have : 0 ≤ (ν k (closure Qs)).toReal := ENNReal.toReal_nonneg
    linarith
  have hlipk : ∀ k (u v w' : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖Tk k u - Tk k v‖ ≤ L * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder w'| := by
    intro k u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hC0 (hMbar k)) ?_
    refine (hTk_lip k u v w' hw').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    linarith [hνmass k]
  have hlipμ : ∀ (u v w' : CubeFractionalL2 (k := 1) hd zc r hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖T u - T v‖ ≤ Lμ * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder w'| := by
    intro u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hCtr (add_nonneg hKtr ENNReal.toReal_nonneg)) ?_
    exact hT.2.1 u v w' hw'
  -- `L²` representatives
  have hψk : ∀ k, MemLp ψ 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) ψ hψ
  have hψμ : MemLp ψ 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ (closure Qs) hKc hμsupp ψ hψ
  have hfk : ∀ n k, MemLp (f n) 2 (ν k) := fun n k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) (f n)
      (hfsm n).continuous
  -- the quantities
  set X : ℕ → ℝ := fun k => ‖Tk k (S k) - (hψk k).toLp ψ‖ with hXdef
  set Y : ℝ := ‖T z - hψμ.toLp ψ‖ with hYdef
  set e : ℕ → ℕ → ℝ := fun n k =>
    ‖Tk k (a n) - (hψk k).toLp ψ‖ - ‖T (a n) - hψμ.toLp ψ‖ with hedef
  have hbound : ∀ n k, |X k - Y| ≤
      L * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder (diff k)| +
        (L + Lμ) * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder (w n)| + |e n k| := by
    intro n k
    have h1 : ‖Tk k (S k) - Tk k z‖ ≤
        L * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder (diff k)| :=
      hlipk k (S k) z (diff k) (by rw [hdiff k, hSval k, hw3 k])
    have h2 : ‖Tk k z - Tk k (a n)‖ ≤
        L * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder (w n)| :=
      hlipk k z (a n) (w n) (hw n)
    have h3 : ‖T z - T (a n)‖ ≤
        Lμ * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder (w n)| :=
      hlipμ z (a n) (w n) (hw n)
    have t1 : |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| ≤ ‖Tk k (S k) - Tk k (a n)‖ := by
      have := abs_norm_sub_norm_le (Tk k (S k) - (hψk k).toLp ψ) (Tk k (a n) - (hψk k).toLp ψ)
      simpa [hXdef, sub_sub_sub_cancel_right] using this
    have t2 : ‖Tk k (S k) - Tk k (a n)‖ ≤ ‖Tk k (S k) - Tk k z‖ + ‖Tk k z - Tk k (a n)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have t3 : |‖T (a n) - hψμ.toLp ψ‖ - Y| ≤ ‖T z - T (a n)‖ := by
      have := abs_norm_sub_norm_le (T (a n) - hψμ.toLp ψ) (T z - hψμ.toLp ψ)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (T (a n)) (T z)] at this
      exact this
    have hsplit : X k - Y = (X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k +
        (‖T (a n) - hψμ.toLp ψ‖ - Y) := by
      simp only [hedef]; ring
    rw [hsplit]
    calc |(X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k + (‖T (a n) - hψμ.toLp ψ‖ - Y)|
        ≤ |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| + |e n k| + |‖T (a n) - hψμ.toLp ψ‖ - Y| :=
          abs_add_three _ _ _
      _ ≤ _ := by nlinarith [t1, t2, t3, h1, h2, h3]
  -- the smooth comparison term converges for each fixed `n`
  have he : ∀ n, Tendsto (e n) atTop (𝓝 0) := by
    intro n
    have hTkan : ∀ k, Tk k (a n) = (hfk n k).toLp (f n) := fun k =>
      hTk_sm k (f n) (hfsm n) (a n) (haf n) (hfk n k)
    have hTan : T (a n) = (hfLp n).toLp (f n) :=
      hT.2.2 (f n) (hfsm n) (a n) (haf n) (hfLp n)
    have hsqk : ∀ k, ‖Tk k (a n) - (hψk k).toLp ψ‖ =
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) := by
      intro k
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (Tk k (a n)) ((hψk k).toLp ψ) (f n) ψ
        (by rw [hTkan k]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hsqμ : ‖T (a n) - hψμ.toLp ψ‖ = Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ) := by
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (T (a n)) (hψμ.toLp ψ) (f n) ψ
        (by rw [hTan]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hcont : Continuous (fun x => (f n x - ψ x) ^ 2) :=
      ((hfsm n).continuous.sub hψ).pow 2
    have hlim := (hW _ hcont).sqrt
    have h2 : Tendsto (fun k => Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) -
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ)) atTop (𝓝 0) := by
      have := hlim.sub_const (Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ))
      rwa [sub_self] at this
    refine h2.congr (fun k => ?_)
    simp only [hedef, hsqk, hsqμ]
  have hdiffabs : Tendsto (fun k => L * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder
      (diff k)|) atTop (𝓝 0) := by
    simpa using (hdiff0.abs).const_mul L
  have hwabs : Tendsto (fun n => (L + Lμ) * |cubeFractionalL2Norm hd zc r hr halfFractionalOrder
      (w n)|) atTop (𝓝 0) := by
    simpa using (hw0.abs).const_mul (L + Lμ)
  have hXY : Tendsto X atTop (𝓝 Y) :=
    aux_prop_uniform_resolvent_ident_eps3 X Y e _ _ hbound hwabs hdiffabs he
  -- back to integrals
  have hXsq : ∀ k, X k ^ 2 = ∫ x, (s k x - ψ x) ^ 2 ∂(ν k) := by
    intro k
    obtain ⟨hmem, hid⟩ := hTk_id k (S k)
    refine aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ ?_ (MemLp.coeFn_toLp _)
    rw [hid hmem]
    refine (MemLp.coeFn_toLp hmem).trans ?_
    rw [hSval k]
  have hYsq : Y ^ 2 = ∫ x, (T z x - ψ x) ^ 2 ∂μ :=
    aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ (Filter.EventuallyEq.refl _ _)
      (MemLp.coeFn_toLp _)
  rw [← hYsq]
  exact (hXY.pow 2).congr hXsq

end Paper
