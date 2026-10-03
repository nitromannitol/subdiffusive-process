module

public import SubdiffusiveProcess.Paper.aux_lem_15_layer_tail
public import SubdiffusiveProcess.Paper.lem_layer_norms
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2
public import Mathlib.Tactic

@[expose] public section

/-! Layer sup-norm moments on a level-`k` cell (`eq:mfd-layernorm`, scale-free form): the supremum of the
layer of relative index `n` over the enlarged cell `closedBall z (3 * 3^{-k} / 2)` has the moments
`C δ^κ (3^{-n})^{-γ}` with constants independent of the cell position `z` and of `k`.  The lattice cover
of `3^{n+k}` times the cell is centered at the lattice point nearest to the scaled cell centre (the layer
tail is translation invariant), so its cardinality is `≤ (12 · 3^n)^d`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology
namespace Paper
noncomputable section

theorem aux_prop_conc_fine_layer_moments_site_add {d : ℕ} (m0 m : Fin d → ℤ) :
    aux_lem_15_layer_tail_site (m0 + m) = aux_lem_15_layer_tail_site m0 + aux_lem_15_layer_tail_site m := by
  funext i
  simp only [aux_lem_15_layer_tail_site, Pi.add_apply, Int.cast_add]
  ring

/-- Layer tail on a ball of radius `R` around an arbitrary centre `z`: an explicit lattice cover with
`≤ (4 · 3^j R + 6)^d` sites, all with the same sub-Gaussian tail. -/
theorem aux_prop_conc_fine_layer_moments_tail
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 ≤ R)
    (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map forget
    let P := (commonScaleLaw d nu).toMeasure
    let S : ℕ → BilateralField d → ℝ := fun j omega =>
      sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Metric.closedBall z R)
    ∃ covers : ℕ → ℝ,
      (∀ j, 1 ≤ covers j) ∧
      (∀ j, covers j ≤ (4 * ((3 : ℝ) ^ j * R) + 6) ^ d) ∧
      (∀ j, AEStronglyMeasurable (S j) P) ∧
      (∀ j omega, 0 ≤ S j omega) ∧
      (∀ (j : ℕ) (s : ℝ), 0 ≤ s →
        P {omega | s < S j omega} ≤
          ENNReal.ofReal (2 * covers j * Real.exp (-(s ^ 2 / (delta ^ 2))))) := by
  classical
  intro forget nu P S
  set Q : Set (SpatialCoordinates d) := Metric.closedBall z R with hQdef
  have hQ : IsCompact Q := isCompact_closedBall _ _
  have hQne : Q.Nonempty := ⟨z, Metric.mem_closedBall_self hR⟩
  haveI hQc : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  haveI : Nonempty Q := hQne.to_subtype
  set M : ℕ → ℕ := fun j => ⌈2 * ((3 : ℝ) ^ j * R) + 3 / 2⌉₊ with hMdef
  set L : ℕ → Finset (Fin d → ℤ) := fun j =>
    Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M j : ℤ)) (M j : ℤ)) with hLdef
  have hcardval : ∀ j, (L j).card = (2 * M j + 1) ^ d := by
    intro j
    rw [hLdef]
    exact aux_lem_15_layer_tail_card (M j)
  have hiSup : ∀ j omega, S j omega
      = ⨆ x : Q, ‖(omega (-(j : ℤ)) : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)‖ := by
    intro j omega
    exact aux_lem_15_layer_tail_sSup_eq_iSup Q _
  refine ⟨fun j => ((L j).card : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show (1 : ℝ) ≤ ((L j).card : ℝ)
    have h1 : 1 ≤ (L j).card := by
      rw [hcardval j]
      exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1
  · intro j
    show ((L j).card : ℝ) ≤ (4 * ((3 : ℝ) ^ j * R) + 6) ^ d
    have hMlt : ((M j : ℝ)) < 2 * ((3 : ℝ) ^ j * R) + 3 / 2 + 1 := by
      have h := Nat.ceil_lt_add_one (a := 2 * ((3 : ℝ) ^ j * R) + 3 / 2) (by positivity)
      rw [hMdef]
      exact h
    have hcast : ((L j).card : ℝ) = ((2 * M j + 1 : ℕ) : ℝ) ^ d := by
      rw [hcardval j]; push_cast; ring
    rw [hcast]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    push_cast
    linarith
  · intro j
    have hfun : S j = (fun f : C(SpatialCoordinates d, ℝ) =>
        ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) ∘
        (fun omega : BilateralField d => omega (-(j : ℤ))) := by
      funext omega
      exact hiSup j omega
    rw [hfun]
    exact (((aux_lem_15_layer_tail_continuous Q).measurable).comp
      (measurable_pi_apply _)).aestronglyMeasurable
  · intro j omega
    rw [hiSup j omega]
    exact aux_lem_15_layer_tail_iSup_nonneg Q _
  · intro j s hs
    show P {omega | s < S j omega} ≤
      ENNReal.ofReal (2 * ((L j).card : ℝ) * Real.exp (-(s ^ 2 / (delta ^ 2))))
    have hA : MeasurableSet {f : C(SpatialCoordinates d, ℝ) |
        s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} :=
      (aux_lem_15_layer_tail_continuous Q).measurable measurableSet_Ioi
    have hset : {omega : BilateralField d | s < S j omega}
        = (fun omega : BilateralField d => omega (-(j : ℤ))) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [hiSup j omega]
    rw [hset]
    have htrans := aux_lem_15_layer_tail_transport Praw forget (-(j : ℤ)) _ hA
    rw [show P = (commonScaleLaw d ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map forget)).toMeasure from rfl, htrans]
    -- the lattice point nearest to the scaled centre
    set m0 : Fin d → ℤ := fun i => round (2 * (((3 : ℝ) ^ j) * z i)) with hm0
    have hsubset : (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖}
        ⊆ ⋃ m ∈ L j, {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
            s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (aux_lem_15_layer_tail_site (m0 + m)) g)} := by
      intro g hg
      have hg' : s < sSup ((fun x : SpatialCoordinates d =>
          ‖(layerScaling d (-(j : ℤ)) (forget g)) x‖) '' Q) := by
        rw [aux_lem_15_layer_tail_sSup_eq_iSup]
        exact hg
      obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup (hQne.image _) hg'
      obtain ⟨x, hxQ, rfl⟩ := hb
      have hpow : ((3 : ℝ) ^ (-(-(j : ℤ)))) = (3 : ℝ) ^ (j : ℕ) := by
        rw [neg_neg, zpow_natCast]
      have hyv : (layerScaling d (-(j : ℤ)) (forget g)) x
          = (forget g) (((3 : ℝ) ^ (j : ℕ)) • x) := by
        show (forget g) (((3 : ℝ) ^ (-(-(j : ℤ)))) • x) = _
        rw [hpow]
      have hxz : ∀ i, |x i - z i| ≤ R := by
        intro i
        have h1 : dist x z ≤ R := hxQ
        have h2 : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
        rw [Real.dist_eq] at h2
        exact h2.trans h1
      have hybound : ∀ i, |(((3 : ℝ) ^ (j : ℕ)) • x - aux_lem_15_layer_tail_site m0) i|
          ≤ (3 : ℝ) ^ j * R + 1 / 4 := by
        intro i
        have hxi : (((3 : ℝ) ^ (j : ℕ)) • x - aux_lem_15_layer_tail_site m0) i
            = (3 : ℝ) ^ j * (x i - z i) +
              ((2 * (((3 : ℝ) ^ j) * z i) - (round (2 * (((3 : ℝ) ^ j) * z i)) : ℝ)) / 2) := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aux_lem_15_layer_tail_site, hm0]
          ring
        rw [hxi]
        have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
        have h1 : |(3 : ℝ) ^ j * (x i - z i)| ≤ (3 : ℝ) ^ j * R := by
          rw [abs_mul, abs_of_pos h3]
          exact mul_le_mul_of_nonneg_left (hxz i) h3.le
        have h2 : |(2 * (((3 : ℝ) ^ j) * z i) - (round (2 * (((3 : ℝ) ^ j) * z i)) : ℝ)) / 2| ≤ 1 / 4 := by
          rw [abs_div, abs_two]
          have := abs_sub_round (2 * (((3 : ℝ) ^ j) * z i))
          linarith
        exact (abs_add_le _ _).trans (by linarith)
      have hMle : 2 * ((3 : ℝ) ^ j * R + 1 / 4) + 1 ≤ (M j : ℝ) := by
        rw [hMdef]
        have := Nat.le_ceil (2 * ((3 : ℝ) ^ j * R) + 3 / 2)
        linarith
      obtain ⟨m, hm, hmem⟩ := aux_lem_15_layer_tail_cover ((3 : ℝ) ^ j * R + 1 / 4) (M j) hMle
        (((3 : ℝ) ^ (j : ℕ)) • x - aux_lem_15_layer_tail_site m0) hybound
      refine Set.mem_biUnion (show m ∈ L j by rw [hLdef]; exact hm) ?_
      have hmem' : ((3 : ℝ) ^ (j : ℕ)) • x - aux_lem_15_layer_tail_site (m0 + m) ∈
          Homogenization.openCubeSet (Homogenization.originCube d 0) := by
        rw [aux_prop_conc_fine_layer_moments_site_add, ← sub_sub]
        exact hmem
      have hbound := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.abs_apply_le_g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (aux_lem_15_layer_tail_site (m0 + m)) g)
        hmem'
      rw [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, sub_add_cancel] at hbound
      show s < _
      refine lt_of_lt_of_le ?_ hbound
      simpa [hyv, Real.norm_eq_abs, forget] using! hsb
    calc (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
          ((fun g => layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
            {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖})
        ≤ (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
            (⋃ m ∈ L j, {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
              s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                  (aux_lem_15_layer_tail_site (m0 + m)) g)}) := measure_mono hsubset
      _ ≤ ∑ m ∈ L j, (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
            {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
              s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                  (aux_lem_15_layer_tail_site (m0 + m)) g)} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ L j, ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) :=
          Finset.sum_le_sum (fun m _ =>
            aux_lem_15_layer_tail_translated_tail delta hdelta Praw hG1 hG2 _ s hs)
      _ = ((L j).card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ((L j).card : ℝ) * Real.exp (-(s ^ 2 / (delta ^ 2)))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring

/-- **Scale-free layer moments on the enlarged cell.**  One constant `Cm(d,p,κ,λ,γ)` serves every disorder
`δ ∈ (0,1]`, every model, every cell centre `z`, every level `k` and every relative index `n`. -/
theorem prop_conc_fine_layer_moments
    (d : ℕ) (hd : 2 ≤ d)
    (p kk lam gam : ℝ) (hp : 0 < p) (hkk : 0 ≤ kk) (hlam : 0 ≤ lam) (hgam : 0 < gam) :
    ∃ Cm : ℝ, 0 < Cm ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)),
        SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw →
        SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map forget
        let P := (commonScaleLaw d nu).toMeasure
        ∀ (z : SpatialCoordinates d) (k n : ℕ),
          eLpNorm (fun omega : BilateralField d =>
              (sSup ((fun x : SpatialCoordinates d => ‖omega (-((n + k : ℕ) : ℤ)) x‖) ''
                  Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2))) ^ kk *
                Real.exp (lam * sSup ((fun x : SpatialCoordinates d => ‖omega (-((n + k : ℕ) : ℤ)) x‖) ''
                  Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2))))
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cm * delta ^ kk * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-gam)) := by
  have hCc : (1 : ℝ) ≤ (12 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  obtain ⟨C0, hC0, hLN⟩ := lem_layer_norms d (by omega) ((12 : ℝ) ^ d) hCc
  obtain ⟨Cp, hCp, hLN2⟩ := hLN p hp
  obtain ⟨Cpk, hCpk, hLN3⟩ := hLN2 kk lam hkk hlam
  obtain ⟨Cpkg, hCpkg, hLN4⟩ := hLN3 gam hgam
  refine ⟨Cpkg, hCpkg, ?_⟩
  intro _ _ delta hdelta hdelta1 Praw hG1 hG2 forget nu P z k n
  have hR : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ (-(k : ℝ)) / 2 := by positivity
  have htail := aux_prop_conc_fine_layer_moments_tail d z (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2) hR delta hdelta
    Praw hG1 hG2
  simp only at htail
  obtain ⟨covers, hcov1, hcov2, hSmeas, hSnn, hStail⟩ := htail
  have h3k : (3 : ℝ) ^ (n + k) * ((3 : ℝ) ^ (-(k : ℝ))) = (3 : ℝ) ^ n := by
    rw [pow_add, Real.rpow_neg (by norm_num), Real.rpow_natCast, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
  have hcover : ∀ n' : ℕ, covers (n' + k) ≤ (12 : ℝ) ^ d * ((3 : ℝ) ^ (-(n' : ℝ))) ^ (-(d : ℝ)) := by
    intro n'
    refine (hcov2 (n' + k)).trans ?_
    rw [aux_lem_15_layer_tail_rpow]
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ n' := one_le_pow₀ (by norm_num)
    have hk : (3 : ℝ) ^ (n' + k) * (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2) = (3 / 2) * (3 : ℝ) ^ n' := by
      have := h3k
      have h4 : (3 : ℝ) ^ (n' + k) * (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2) =
          3 / 2 * ((3 : ℝ) ^ (n' + k) * ((3 : ℝ) ^ (-(k : ℝ)))) := by ring
      rw [h4]
      have h5 : (3 : ℝ) ^ (n' + k) * (3 : ℝ) ^ (-(k : ℝ)) = (3 : ℝ) ^ n' := by
        rw [pow_add, Real.rpow_neg (by norm_num), Real.rpow_natCast, mul_assoc,
          mul_inv_cancel₀ (by positivity), mul_one]
      rw [h5]
    rw [hk, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith
  have hres := hLN4 (BilateralField d) P delta hdelta hdelta1
    (fun n' omega => sSup ((fun x : SpatialCoordinates d => ‖omega (-((n' + k : ℕ) : ℤ)) x‖) ''
      Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2)))
    (fun n' => hSmeas (n' + k)) (fun n' omega => hSnn (n' + k) omega)
    (fun n' => covers (n' + k)) (fun n' => hcov1 (n' + k)) hcover
    (by
      intro n' s hs
      refine (hStail (n' + k) s hs).trans (ENNReal.ofReal_le_ofReal ?_)
      have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
      have hle : delta ^ 2 ≤ (12 : ℝ) ^ d * delta ^ 2 := by nlinarith [hCc, hd2]
      have hdiv : s ^ 2 / ((12 : ℝ) ^ d * delta ^ 2) ≤ s ^ 2 / delta ^ 2 := by gcongr
      have hE : Real.exp (-(s ^ 2 / delta ^ 2)) ≤ Real.exp (-(s ^ 2 / ((12 : ℝ) ^ d * delta ^ 2))) :=
        Real.exp_le_exp.mpr (by linarith)
      have hc : (0 : ℝ) ≤ covers (n' + k) := (zero_le_one.trans (hcov1 (n' + k)))
      nlinarith [Real.exp_pos (-(s ^ 2 / delta ^ 2)),
        Real.exp_pos (-(s ^ 2 / ((12 : ℝ) ^ d * delta ^ 2)))])
  have hres2 := (hres.2 n)
  simp only at hres2
  exact hres2.1.trans (ENNReal.ofReal_le_ofReal hres2.2)

end
end Paper
