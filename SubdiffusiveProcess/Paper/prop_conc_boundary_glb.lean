import Mathlib.Tactic
import SubdiffusiveProcess.Compactness.SequentialCompactness
import SubdiffusiveProcess.DirichletForm.FOTProduct
import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Sobolev.CompactResponses
import SubdiffusiveProcess.Paper.prop_boundary
import SubdiffusiveProcess.Paper.prop_conc_boundary_truncation
import SubdiffusiveProcess.Paper.prop_conc_controlled_forms
import SubdiffusiveProcess.Paper.prop_conc_energy_measure_convergence
import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
import SubdiffusiveProcess.Paper.prop_conc_local_affine_order

/-! Deterministic prop conc boundary glb data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace Paper
noncomputable section

/-- Extracted fractional norm bound argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_boundary_glb_fractional_norm_bound (x q V B c : ℝ)
    (_hx : 0 ≤ x) (hq : 0 ≤ q) (hV : 0 < V) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (h : x ^ 2 + V * q ^ 2 ≤ B) :
    q + c * (x / Real.sqrt V) ≤
      Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V) := by
  have hsqV : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hsqB : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
  have hrootV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hrootB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hxB : x ≤ Real.sqrt B := by
    nlinarith only [h, hsqB, hrootB, mul_nonneg hV.le (sq_nonneg q)]
  have hqB : q ≤ Real.sqrt B / Real.sqrt V := by
    apply (le_div_iff₀ hrootV).mpr
    have hprod : 0 ≤ q * Real.sqrt V := mul_nonneg hq hrootV.le
    have hs : (q * Real.sqrt V) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      rw [mul_pow, hsqV, hsqB]
      nlinarith only [h, sq_nonneg x]
    exact (sq_le_sq₀ hprod hrootB).mp hs
  exact add_le_add hqB (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hxB hrootV.le) hc)

/-- Extracted patch compactness argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_boundary_glb_patch_compactness
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (uN : ℕ → S.space) (E0 : ℝ)
    (hEnergy : ∀ n, responseForm S (a n) (uN n) (uN n) ≤ E0) :
    ∃ (sigma : ℕ → ℕ) (u : DomainL2 (centeredCube z r hr)),
      StrictMono sigma ∧ Tendsto (fun n => (uN (sigma n)).val.1) atTop (𝓝 u) := by
  let V : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hV : 0 < V := centeredCube_volume_pos z hr
  let B : ℝ := A.K * max E0 0
  have hB : 0 ≤ B := mul_nonneg A.K_pos.le (le_max_right _ _)
  let c : ℝ := r ^ (-(Lane4.threeQuarterOrder : ℝ))
  have hc : 0 ≤ c := Real.rpow_nonneg hr.le _
  let w : ℕ → CubeFractionalL2 (k := 1) hd z r hr Lane4.threeQuarterOrder :=
    fun n => ⟨fun _ : Fin 1 => (uN n).val.1, (A.coercive n (uN n)).1⟩
  have hBound (n : ℕ) :
      cubeFractionalL2Norm hd z r hr Lane4.threeQuarterOrder (w n) ≤
        Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V) := by
    have h := (A.coercive n (uN n)).2.trans
      (mul_le_mul_of_nonneg_left ((hEnergy n).trans (le_max_left E0 0)) A.K_pos.le)
    have hn := Paper.aux_prop_conc_boundary_glb_fractional_norm_bound ‖(uN n).val.1‖
      (cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => (uN n).val.1)).toReal V B c
      (norm_nonneg _) ENNReal.toReal_nonneg hV hB hc h
    simpa only [cubeFractionalL2Norm, w, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
      using hn
  obtain ⟨sigma, hsigma, u, hu⟩ := A.interpolation.compact_embedding z r hr
    Lane4.threeQuarterOrder (by norm_num [Lane4.threeQuarterOrder]) w
    (Real.sqrt B / Real.sqrt V + c * (Real.sqrt B / Real.sqrt V)) hBound
  refine ⟨sigma, u, hsigma, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hu

/-- Extracted growth lower exponent argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_boundary_glb_growth_lower_exponent {d : ℕ} {mu : Measure (SpatialCoordinates d)} {C t s rr : ℝ} {x : SpatialCoordinates d}
    (hC : 0 ≤ C) (hrr : 0 < rr) (hrr1 : rr ≤ 1) (hst : s ≤ t)
    (h : mu (Metric.ball x rr) ≤ ENNReal.ofReal (C * rr ^ t)) :
    mu (Metric.ball x rr) ≤ ENNReal.ofReal (C * rr ^ s) :=
  h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hrr hrr1 hst) hC))

/-- Extracted controls lower exponent argument from the pre-convergence deterministic proof. -/
noncomputable def aux_prop_conc_boundary_glb_controls_lower_exponent
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (s : ℝ) (hs : (d : ℝ) - 1 < s) (hst : s ≤ A.t) :
    Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a :=
  { A with
    t := s
    t_lower := hs
    t_upper := hst.trans_lt A.t_upper
    cutoffs := by
      intro K O hK hO hKO hOQ
      obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hChi⟩ := A.cutoffs K O hK hO hKO hOQ
      refine ⟨V, chi, chic, B, hV, hKV, hVO, hB, fun n => ?_⟩
      obtain ⟨hcont, hrep, hb, hone, hzero, hE, hgrowth⟩ := hChi n
      refine ⟨hcont, hrep, hb, hone, hzero, hE, ?_⟩
      intro x hx rr hrr hrr1
      exact Paper.aux_prop_conc_boundary_glb_growth_lower_exponent hB hrr hrr1 hst (hgrowth x hx rr hrr hrr1) }

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

/-- Extracted boundary glb of patches argument from the pre-convergence deterministic proof. -/
theorem prop_conc_boundary_glb
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm)
    (q : Set (SpatialCoordinates d))
    (hqcell : q = (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hkilled : DirichletForm.IsKilledDomain EQ.toClosedForm q Dq)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (b beta : SpatialCoordinates d → ℝ)
    (hbeta : ContDiff ℝ ∞ beta)
    (hbetasupp : HasCompactSupport beta)
    (hbetaQ : tsupport beta ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetab : ∀ x ∈ frontier q, beta x = b x)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (betaq : H1Function q)
    (hbetaqfun : betaq.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNcellcont : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ContinuousOn (UN n).toFun
        (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))))
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hHcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Hcell k)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z (3 * r) h3r S aC)
    (GN : ℕ → DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (G : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (hE : ∀ v, EQ.energy v = limitFormEnergy G v)
    (hcore : ∃ C, DirichletForm.IsCoreOn EQ.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (L : ℝ)
    (hResponse : Tendsto (fun n => cellDirichletInfimum (a n) q betaq) atTop (𝓝 L)) :
    IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma q b) L ∧
    (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma q b).Nonempty := by
  subst hqcell
  obtain ⟨E0, hE0⟩ := aux_prop_boundary_energy_bound z r h3r S a aC hacont haC
    UN UNS hUNrep hcellsub Bcell hCellEnergy
  obtain ⟨sigma, uBar, hsigma, huBar⟩ := Paper.aux_prop_conc_boundary_glb_patch_compactness A UNS E0 hE0
  let A' := Paper.aux_prop_conc_controlled_forms_controls_reindex
    (Paper.aux_prop_conc_boundary_glb_controls_lower_exponent A (min A.t t)
      (lt_min A.t_lower ht) (min_le_left _ _)) sigma
  have hG' : Tendsto (fun n => GN (sigma n)) atTop (𝓝 G) :=
    hConv.comp hsigma.tendsto_atTop
  have hMosco := Paper.prop_conc_controlled_forms hS A' _ G
    (fun n => hGN (sigma n)) hG'
  have hMeasures := Paper.prop_conc_energy_measure_convergence BD BDQ EM hcontract hS A'
    _ G (fun n => hGN (sigma n)) hG' EQ hE hcore Gamma
  have hdom := aux_thm_prop_domain_eq_of_energy EQ.toClosedForm G hE
  have hKilled (k : OddGridIndex d (triadicHalf 1)) :
      ∃ D, DirichletForm.IsKilledDomain EQ.toClosedForm
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D :=
    ⟨_, DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _⟩
  obtain ⟨U, Uc, hUdom, hUc, hUrep, _hUunif, hUb, _hUface, _hUorth, hUlim, hUmin⟩ :=
    prop_boundary d hd z r hr h3r EQ Gamma _ rfl Dq hkilled S hS
      (fun n => a (sigma n)) (fun n => aC (sigma n))
      (fun n => hacont (sigma n)) (fun n => haC (sigma n)) (fun n => hell (sigma n))
      b beta hbeta hbetasupp hbetaQ hbetab betaQ hbetaQfun betaq hbetaqfun
      (fun n => UN (sigma n)) (fun n => UNS (sigma n)) (fun n => hUNrep (sigma n))
      uBar huBar hcellsub (fun n => hUNharm (sigma n)) (fun n => hUNtrace (sigma n))
      (fun n => hUNcellcont (sigma n)) (fun n => hUNcellb (sigma n))
      (min A.t t) alpha (lt_min A.t_lower ht) ((min_le_right _ _).trans_lt htd)
      halpha halpha1 Bcell Hcell hBcell hHcell (fun n => hCellEnergy (sigma n))
      (fun n k x hx rr hrr hrr1 => Paper.aux_prop_conc_boundary_glb_growth_lower_exponent (hBcell k)
        hrr hrr1 (min_le_right A.t t) (hCellGrowth (sigma n) k x hx rr hrr hrr1))
      (fun n => hCellHolder (sigma n))
      (by simpa only [hE] using hMosco.lower)
      (by simpa only [← hdom, ← hE] using hMosco.recovery)
      (fun _ => A'.K) (fun _ => A'.K_pos.le) A'.K (fun _ => le_rfl)
      (fun w => (A'.coercive 0 w).1) (fun n w => (A'.coercive n w).2)
      A'.interpolation A'.cutoffs hMeasures
      (fun zc rc hrc hsub D hD w hw wc hwc hrep hzero wq hwq =>
        Paper.prop_conc_boundary_truncation d hd z zc (3 * r) rc h3r hrc hsub
          EQ Gamma hcore D hD w hw wc hwc hrep hzero wq hwq)
      hKilled
  have hL : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L :=
    tendsto_nhds_unique hUlim (hResponse.comp hsigma.tendsto_atTop)
  have hmem : (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ∈
      aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) EQ.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) b :=
    ⟨U, Uc, hUdom, hUc, hUrep, hUb, rfl⟩
  have hleast : IsLeast (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r)
      EQ.toClosedForm Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) b)
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    refine ⟨hmem, ?_⟩
    rintro e ⟨V, Vc, hV, hVc, hVrep, hVb, rfl⟩
    exact hUmin V hV Vc hVc hVrep hVb
  exact ⟨hL ▸ hleast.isGLB, ⟨_, hmem⟩⟩

end
end Paper
