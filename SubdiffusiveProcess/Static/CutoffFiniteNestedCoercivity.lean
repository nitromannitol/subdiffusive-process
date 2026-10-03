module

public import SubdiffusiveProcess.Static.CutoffLargeCubeCoercivity
public import SubdiffusiveProcess.Static.CutoffMicroscopicCoercivity
public import SubdiffusiveProcess.Static.CubeCoercivityTranslation
public import SubdiffusiveProcess.Static.CutoffCoercivityGeometry
public import SubdiffusiveProcess.Static.LocalNormalization

@[expose] public section

/-! # Exact nested coercivity for cutoffs below the physical scale -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Empty families have the constant one on the exact physical law. -/
theorem exists_empty_local_coercivity {d : ℕ} (M : GMCModel d) (A : AnchoredC11Sample d → Vec d → ℝ)
    (c : Fin 0 → Vec d) (s0 s1 : Fin 0 → ℝ) (q : ℝ) :
    ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal 1 ∧
      ∀ᵐ ω ∂localAnchoredLaw M, localCoercivityEstimates (A ω) c s0 s1 (K ω) 5 := by
  refine ⟨fun _ => 1, measurable_const, fun _ => le_rfl, ?_, ?_⟩
  · simp
  · exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i

theorem exists_finite_origin_cube_bank (d : ℕ) [NeZero d] (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∃ B : ℝ, 0 < B ∧ ∀ L m : ℕ, L ≤ m → ∀ s : ℝ, a ≤ s → s ≤ b → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
          ∀ᵐ ω ∂M.P.toMeasure,
            cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) 0 s (K ω) := by
  obtain ⟨J, ht, hb⟩ := exists_coercivity_chart_scale (b := b) ha
  obtain ⟨δ0, Bl, hδ0, hBl, hl⟩ := exists_large_cube_coercivity d J a b ha hab ht hb q hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM
  obtain ⟨Bm, hBm, hm⟩ := exists_microscopic_cube_coercivity M J a b ha hab hb q hq
  refine ⟨Bl + Bm, add_pos hBl hBm, ?_⟩
  intro L m hLm s has hsb z
  by_cases hJm : J ≤ m
  · obtain ⟨K, hK, hK1, hKn, hKc⟩ := hl M hM L m hLm hJm s has hsb z
    exact ⟨K, hK, hK1, hKn.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hBm.le)), hKc⟩
  · obtain ⟨K, hK, hK1, hKn, hKc⟩ := hm L m hLm (lt_of_not_ge hJm) s has hsb z
    exact ⟨K, hK, hK1, hKn.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hBl.le)), hKc⟩

theorem exists_finite_centered_cube {d : ℕ} (M : GMCModel d) {q B a : ℝ}
    (ha : 0 < a) {L m : ℕ} (s : ℝ) (has : a ≤ s) (z y : Vec d)
    (hbank : ∀ w : Vec d, ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
      ∀ᵐ ω ∂M.P.toMeasure,
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L m w ω) 0 s (K ω)) :
    ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
      ∀ᵐ ω ∂M.P.toMeasure,
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) y s (K ω) := by
  obtain ⟨K, hK, hK1, hKn, hKc⟩ := hbank (z + (3 : ℝ) ^ m • y)
  refine ⟨K, hK, hK1, hKn, ?_⟩
  filter_upwards [hKc] with ω hω
  have heq : finiteCoercivityCoefficient M L m (z + (3 : ℝ) ^ m • y) ω =
      fun x => finiteCoercivityCoefficient M L m z ω (y + x) := by
    funext x
    simp only [finiteCoercivityCoefficient, smul_add, add_assoc]
  rw [heq] at hω
  exact cubeCoercivityEstimates_translate y (ha.trans_le has) _ hω

theorem exists_uniform_finite_nested_coercivity (d p : ℕ) [NeZero d]
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∃ C : ℝ, 0 < C ∧ ∀ L m : ℕ, L ≤ m → ∀ z : Vec d,
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂localAnchoredLaw M,
            localCoercivityEstimates (localCoefficient M (L : WithTop ℕ) m z ω) c s0 s1 (K ω) 5 := by
  classical
  by_cases hp : p = 0
  · subst p
    exact ⟨1, zero_lt_one, fun M _ => ⟨1, zero_lt_one, fun L m _ z =>
      exists_empty_local_coercivity M (localCoefficient M (L : WithTop ℕ) m z) c s0 s1 q⟩⟩
  obtain ⟨a, b, ha, hab, h0, h1⟩ := exists_coercivity_geometry (Nat.pos_of_ne_zero hp) s0 s1 hs
  obtain ⟨δ0, hδ0, hbank⟩ := exists_finite_origin_cube_bank d a b ha hab q hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM
  obtain ⟨B, hB, hBbank⟩ := hbank M hM
  refine ⟨(1 + 4 * (p : ℝ) * B) ^ q, by positivity, ?_⟩
  intro L m hLm z
  let S := fun (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)) =>
    (1 - ((k : ℕ) : ℝ) / 2 ^ n) * s0 i + (((k : ℕ) : ℝ) / 2 ^ n) * s1 i
  have hfamily : ∀ (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)),
      ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
        eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
        ∀ᵐ ω ∂M.P.toMeasure,
          cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) (c i) (S n i k) (K ω) := by
    intro n i k
    have hh := dyadic_side_bounds (hs i).2.le n k
    exact exists_finite_centered_cube M ha (S n i k) ((h0 i).trans hh.1) z (c i)
      (hBbank L m hLm (S n i k) ((h0 i).trans hh.1) (hh.2.trans (h1 i)))
  choose Z hZ hZ1 hZn hZc using hfamily
  obtain ⟨K, hK, hK1, hKmom, hKc⟩ := exists_dyadic_coercivity_constant M.P.toMeasure
    (finiteCoercivityCoefficient M L m z) c s0 s1 hq hB.le Z
    (fun n i k => (hZ n i k).aestronglyMeasurable) hZn hZc
  have heq : ∀ ω : AnchoredC11Sample d,
      finiteCoercivityCoefficient M L m z ω.1 = localCoefficient M (L : WithTop ℕ) m z ω := by
    intro ω
    funext x
    have hj : localIndex (L : WithTop ℕ) m = L := by
      change min m L = L
      exact min_eq_right hLm
    simp only [finiteCoercivityCoefficient, localCoefficient,
      localDensity_finite_of_le M hLm, hj]
  refine ⟨fun ω => K ω.1, hK.comp measurable_subtype_coe, fun ω => hK1 ω.1, ?_, ?_⟩
  · rwa [anchored_moment_eq M K hK q]
  · have hh := (measurePreserving_anchoredVal M).quasiMeasurePreserving.ae hKc
    simpa only [heq] using hh

end SubdiffusiveProcess.Static
