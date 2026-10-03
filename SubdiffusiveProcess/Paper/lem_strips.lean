module

public import SubdiffusiveProcess.Paper.aux_translated_grid_cover
public import SubdiffusiveProcess.Paper.aux_local_growth_cover_mass
public import SubdiffusiveProcess.Paper.aux_cell_mass_from_local_growth
public import SubdiffusiveProcess.Paper.aux_frostman_zero_of_dimension_lt_exponent
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal

noncomputable section
namespace Paper



theorem lem_strips
    (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (t : ℝ), (d : ℝ) - 1 < t →
        let b : ℝ := t * (t - (d : ℝ) + 1) / (t + 1)
        0 < b ∧
          ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
            ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
              let Q : Opens (SpatialCoordinates d) := centeredCube z R hR
              ∀ (a : SpatialCoordinates d) (nu : Measure (SpatialCoordinates d))
                [IsFiniteMeasure nu] (K : ℝ) (hK : 0 ≤ K),
                (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                  ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
                    nu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) ≤
                      ENNReal.ofReal (K * rad ^ t)) →
              let actualCell : ℝ → (Fin d → ℤ) → Set (SpatialCoordinates d) :=
                fun ell idx =>
                  (Q : Set (SpatialCoordinates d)) ∩
                    {x | ∀ i : Fin d,
                      a i + (idx i : ℝ) * ell ≤ x i ∧
                        x i < a i + ((idx i : ℝ) + 1) * ell}
              let strips : ℝ → ℝ → Set (SpatialCoordinates d) :=
                fun ell r =>
                  (Q : Set (SpatialCoordinates d)) ∩
                    {x | ∃ i : Fin d, ∃ j : ℤ,
                      |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}
              let maxBox : ℝ → ℝ≥0∞ :=
                fun ell => iSup (fun idx : Fin d → ℤ => nu (actualCell ell idx))
              (∀ ell : ℝ, 0 < ell → ell ≤ 1 →
                ∀ r : ℝ, 0 < r → Cc * r < ell →
                  nu (strips ell r) ≤
                      ENNReal.ofReal
                        (Cd * K * (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1)) ∧
                    maxBox ell ≤ ENNReal.ofReal (Cd * K * ell ^ t)) ∧
              (∀ r : ℝ, 0 < r → r ≤ r0 →
                let ell : ℝ := r ^ ((t - (d : ℝ) + 1) / (t + 1))
                0 < ell ∧ ell ≤ 1 ∧ Cc * r < ell ∧
                  nu (strips ell r) ≤
                    ENNReal.ofReal (Cd * K * (max 1 R) ^ d * r ^ b) ∧
                  maxBox ell ≤ ENNReal.ofReal (Cd * K * r ^ b)) ∧
              (∀ r : ℝ, 0 < r →
                (Cc * r < r ^ ((t - (d : ℝ) + 1) / (t + 1)) ↔
                  Cc < r ^ (-(d : ℝ) / (t + 1)))) := by
  obtain ⟨Ccov, hCcov, hcover⟩ :=
    aux_translated_grid_cover d hd Cc hCc
  let Cd : ℝ := max Ccov 1
  have hCd : 0 < Cd := by
    dsimp [Cd]
    exact lt_max_of_lt_left hCcov
  have hCcovCd : Ccov ≤ Cd := by
    exact le_max_left _ _
  refine ⟨Cd, hCd, ?_⟩
  intro t ht
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdR
  have htpos : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have hdg : 0 < t - (d : ℝ) + 1 := by linarith
  have hb : 0 < t * (t - (d : ℝ) + 1) / (t + 1) := by
    positivity
  refine ⟨hb, ?_⟩
  let alpha : ℝ := -(t + 1) / (d : ℝ)
  let beta : ℝ := -(d : ℝ) / (t + 1)
  let r0 : ℝ := min 1 (Cc ^ alpha / 2)
  have hpow0 : 0 < Cc ^ alpha := Real.rpow_pos_of_pos hCc _
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min zero_lt_one (div_pos hpow0 (by norm_num))
  have hr01 : r0 ≤ 1 := min_le_left _ _
  have hpow_inv : (Cc ^ alpha) ^ beta = Cc := by
    calc
      (Cc ^ alpha) ^ beta = Cc ^ (alpha * beta) := by
        rw [← Real.rpow_mul (le_of_lt hCc)]
      _ = Cc := by
        rw [show alpha * beta = 1 by
          dsimp [alpha, beta]
          field_simp
          , Real.rpow_one]
  have hsep_all : ∀ r : ℝ, 0 < r → r ≤ r0 → Cc * r < r ^
      ((t - (d : ℝ) + 1) / (t + 1)) := by
    intro r hr hr0'
    have hrA : r < Cc ^ alpha := by
      have hhalf : Cc ^ alpha / 2 < Cc ^ alpha := by linarith
      exact lt_of_le_of_lt (hr0'.trans (min_le_right _ _)) hhalf
    have hbeta : beta < 0 := by
      dsimp [beta]
      exact div_neg_of_neg_of_pos (by linarith) ht1
    have hpow : (Cc ^ alpha) ^ beta < r ^ beta := by
      exact Real.rpow_lt_rpow_of_neg hr hrA hbeta
    have hpow' : Cc < r ^ beta := by simpa [hpow_inv] using hpow
    have heq : ((t - (d : ℝ) + 1) / (t + 1)) - 1 = beta := by
      dsimp [beta]
      field_simp
      ring
    have hq : (t - (d : ℝ) + 1) / (t + 1) =
        (((t - (d : ℝ) + 1) / (t + 1)) - 1) + 1 := by ring
    rw [hq, Real.rpow_add hr, Real.rpow_one, heq]
    exact mul_lt_mul_of_pos_right hpow' hr
  have hsep_iff : ∀ r : ℝ, 0 < r →
      (Cc * r < r ^ ((t - (d : ℝ) + 1) / (t + 1)) ↔
        Cc < r ^ (-(d : ℝ) / (t + 1))) := by
    intro r hr
    have heq : ((t - (d : ℝ) + 1) / (t + 1)) - 1 =
        -(d : ℝ) / (t + 1) := by
      field_simp
      ring
    have hq : (t - (d : ℝ) + 1) / (t + 1) =
        (((t - (d : ℝ) + 1) / (t + 1)) - 1) + 1 := by ring
    rw [hq, Real.rpow_add hr, Real.rpow_one, heq]
    constructor
    · intro h
      exact lt_of_mul_lt_mul_right h hr.le
    · intro h
      exact mul_lt_mul_of_pos_right h hr
  refine ⟨r0, hr0, hr01, ?_⟩
  intro z R hR
  dsimp
  intro a nu hnu K hK hgrowth
  refine ⟨?_, ?_, ?_⟩
  · intro ell hell hell1 r hr hsep
    by_cases htD : t ≤ (d : ℝ)
    · obtain ⟨hstripCover, hcellCover⟩ :=
        hcover t ht htD z R hR a ell r hell hell1 hr hsep
      obtain ⟨nStrip, stripCenters, stripRadii, hstripSub, hstripMem, hstripSum⟩ :=
        hstripCover
      obtain ⟨nCell, cellCenters, cellRadii, hcellSub, hcellMem, hcellSum⟩ :=
        hcellCover
      constructor
      · exact (aux_local_growth_cover_mass d hd Cc hCc z R hR a t ell r Ccov
          ht hell hell1 hr hsep hCcov.le nStrip stripCenters stripRadii nu K hK
          hstripMem hstripSub hstripSum hgrowth).trans
          (ENNReal.ofReal_mono (by
            have hnonneg : 0 ≤ K * (max 1 R) ^ d * ell⁻¹ *
                r ^ (t - (d : ℝ) + 1) := by positivity
            gcongr))
      · exact (aux_cell_mass_from_local_growth d hd Cc hCc z R hR a t ell r Ccov
          ht hell hell1 hr hsep hCcov.le nCell cellCenters cellRadii nu K hK
          (by
            intro idx
            exact ⟨hcellMem idx, hcellSub idx, hcellSum idx⟩) hgrowth).trans
          (ENNReal.ofReal_mono (by
            have hnonneg : 0 ≤ K * ell ^ t := by positivity
            gcongr))
    · have htD' : (d : ℝ) < t := lt_of_not_ge htD
      have hzero := aux_frostman_zero_of_dimension_lt_exponent d hd z R hR t htD'
        nu K hK hgrowth
      have hQzero : nu (centeredCube z R hR : Set (SpatialCoordinates d)) = 0 := hzero
      constructor
      · exact (measure_mono_null (by
          intro x hx
          exact hx.1) hQzero).trans_le (by positivity)
      · apply iSup_le
        intro idx
        exact (measure_mono_null (by
          intro x hx
          exact hx.1) hQzero).trans_le (by positivity)
  · intro r hr hr0'
    let ell : ℝ := r ^ ((t - (d : ℝ) + 1) / (t + 1))
    have hell : 0 < ell := by
      dsimp [ell]
      positivity
    have hell1 : ell ≤ 1 := by
      dsimp [ell]
      apply Real.rpow_le_one
      · exact hr.le
      · exact hr0'.trans hr01
      · positivity
    have hsep := hsep_all r hr hr0'
    have hscale : ell⁻¹ * r ^ (t - (d : ℝ) + 1) = r ^
        (t * (t - (d : ℝ) + 1) / (t + 1)) := by
      dsimp [ell]
      rw [← Real.rpow_neg hr.le]
      rw [← Real.rpow_add hr]
      rw [show -((t - (d : ℝ) + 1) / (t + 1)) +
          (t - (d : ℝ) + 1) =
          t * (t - (d : ℝ) + 1) / (t + 1) by field_simp; ring]
    have hcellscale : ell ^ t = r ^
        (t * (t - (d : ℝ) + 1) / (t + 1)) := by
      dsimp [ell]
      calc
        (r ^ ((t - (d : ℝ) + 1) / (t + 1))) ^ t =
            r ^ (((t - (d : ℝ) + 1) / (t + 1)) * t) := by
              exact (Real.rpow_mul hr.le _ _).symm
        _ = r ^ (t * (t - (d : ℝ) + 1) / (t + 1)) := by
              congr 1
              ring
    have hgeneral : ∀ ell : ℝ, 0 < ell → ell ≤ 1 →
        ∀ r : ℝ, 0 < r → Cc * r < ell →
          nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
            {x | ∃ i : Fin d, ∃ j : ℤ,
              |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}) ≤
              ENNReal.ofReal
                (Cd * K * (max 1 R) ^ d * ell⁻¹ * r ^
                  (t - (d : ℝ) + 1)) ∧
          iSup (fun idx : Fin d → ℤ =>
            nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
              {x | ∀ i : Fin d,
                a i + (idx i : ℝ) * ell ≤ x i ∧
                  x i < a i + ((idx i : ℝ) + 1) * ell})) ≤
            ENNReal.ofReal (Cd * K * ell ^ t) := by
      intro ell hell hell1 r hr hsep
      by_cases htD : t ≤ (d : ℝ)
      · obtain ⟨hstripCover, hcellCover⟩ :=
          hcover t ht htD z R hR a ell r hell hell1 hr hsep
        obtain ⟨nStrip, stripCenters, stripRadii, hstripSub, hstripMem, hstripSum⟩ :=
          hstripCover
        obtain ⟨nCell, cellCenters, cellRadii, hcellSub, hcellMem, hcellSum⟩ :=
          hcellCover
        constructor
        · exact (aux_local_growth_cover_mass d hd Cc hCc z R hR a t ell r Ccov
            ht hell hell1 hr hsep hCcov.le nStrip stripCenters stripRadii nu K hK
            hstripMem hstripSub hstripSum hgrowth).trans
            (ENNReal.ofReal_mono (by
              have hnonneg : 0 ≤ K * (max 1 R) ^ d * ell⁻¹ *
                  r ^ (t - (d : ℝ) + 1) := by positivity
              gcongr))
        · exact (aux_cell_mass_from_local_growth d hd Cc hCc z R hR a t ell r Ccov
            ht hell hell1 hr hsep hCcov.le nCell cellCenters cellRadii nu K hK
            (by
              intro idx
              exact ⟨hcellMem idx, hcellSub idx, hcellSum idx⟩) hgrowth).trans
            (ENNReal.ofReal_mono (by
              have hnonneg : 0 ≤ K * ell ^ t := by positivity
              gcongr))
      · have hzero := aux_frostman_zero_of_dimension_lt_exponent d hd z R hR t
          (lt_of_not_ge htD) nu K hK hgrowth
        constructor
        · exact (measure_mono_null (by intro x hx; exact hx.1) hzero).trans_le (by positivity)
        · apply iSup_le
          intro idx
          exact (measure_mono_null (by intro x hx; exact hx.1) hzero).trans_le
            (by positivity)
    rcases hgeneral ell hell hell1 r hr hsep with ⟨hstrip, hcell⟩
    refine ⟨hell, hell1, hsep, ?_, ?_⟩
    · have hstrip' : nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∃ i : Fin d, ∃ j : ℤ,
            |x i - (a i + (j : ℝ) * r ^
              ((t - (d : ℝ) + 1) / (t + 1)))| ≤ Cc * r}) ≤
          ENNReal.ofReal (Cd * K * (max 1 R) ^ d * ell⁻¹ *
            r ^ (t - (d : ℝ) + 1)) := by
        simpa only [ell] using hstrip
      calc
        _ ≤ ENNReal.ofReal (Cd * K * (max 1 R) ^ d * ell⁻¹ *
            r ^ (t - (d : ℝ) + 1)) := hstrip'
        _ = ENNReal.ofReal (Cd * K * (max 1 R) ^ d * r ^
            (t * (t - (d : ℝ) + 1) / (t + 1))) := by
          apply congrArg ENNReal.ofReal
          calc
            Cd * K * (max 1 R) ^ d * ell⁻¹ * r ^
                (t - (d : ℝ) + 1) =
                (Cd * K * (max 1 R) ^ d) *
                  (ell⁻¹ * r ^ (t - (d : ℝ) + 1)) := by ring
            _ = (Cd * K * (max 1 R) ^ d) * r ^
                (t * (t - (d : ℝ) + 1) / (t + 1)) := by rw [hscale]
    · have hcell' : iSup (fun idx : Fin d → ℤ =>
          nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
            {x | ∀ i : Fin d,
              a i + (idx i : ℝ) * r ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ x i ∧
                x i < a i + ((idx i : ℝ) + 1) *
                  r ^ ((t - (d : ℝ) + 1) / (t + 1))})) ≤
          ENNReal.ofReal (Cd * K * ell ^ t) := by
        simpa only [ell] using hcell
      calc
        _ ≤ ENNReal.ofReal (Cd * K * ell ^ t) := hcell'
        _ = ENNReal.ofReal (Cd * K * r ^
            (t * (t - (d : ℝ) + 1) / (t + 1))) := by rw [hcellscale]
  · exact hsep_iff

end Paper
