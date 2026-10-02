import SubdiffusiveProcess.Static.CutoffHarmonicMacroscopicCarrier
import SubdiffusiveProcess.Static.CutoffStoppingMomentAtAlpha
import SubdiffusiveProcess.Static.HarmonicCellNativeGrowth
import SubdiffusiveProcess.Static.HarmonicEnergyStoppingMoments

/-! # Closed uniform macroscopic harmonic cutoff cell budget -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_uniform_cutoffHarmonicCell_macroscopic_growth
    (d : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        ∃ C : ℝ, 0 < C ∧
          ∀ j k : ℕ, j ≤ k → ∀ z : Vec d,
            ∃ G : PotentialSample d → ℝ, Measurable G ∧
              (∀ omega, 1 ≤ G omega) ∧
              eLpNorm G (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
              ∀ᵐ omega ∂M.P.toMeasure,
                CutoffHarmonicCellMacroscopicGrowth M j k z omega (G omega) := by
  classical
  by_cases hd : 2 ≤ d
  · letI : NeZero d := ⟨by omega⟩
    obtain ⟨deltaE, Cenergy, CE, hdeltaE, hCenergy, hCE, henergy⟩ :=
      exists_uniform_cutoffDirichletEnergy_moment_bound d (4*q) (by linarith)
    obtain ⟨deltaS, CH, CS, hdeltaS, hCH, hCS, hstopping⟩ :=
      exists_uniform_cutoffStopping_moment_bound_at_alpha d (7/8) (d : ℝ) (2*q)
        (by norm_num) (by positivity) (by linarith)
    let Cd := sourceDirichletEnergyConstant d Cenergy ⟨1/16, by norm_num⟩ *
      (1+(d : ℝ)+(d : ℝ)^2)
    have hCd : 0 ≤ Cd := mul_nonneg
      (sourceDirichletEnergyConstant_nonneg d hCenergy.le _) (by positivity)
    let A := (1+CH^2)*(6 : ℝ)^((d : ℝ)-1/4)*(Cd+3*(d : ℝ))^2
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    let C := 1+A*(CE+1)^2*CS
    have hC : 0 < C := by dsimp only [C]; positivity
    refine ⟨min deltaE deltaS, lt_min hdeltaE hdeltaS, ?_⟩
    intro M hM
    refine ⟨C, hC, ?_⟩
    intro j k hjk z
    obtain ⟨K, hKmeas, hKone, hKN, hKE⟩ :=
      henergy M (hM.trans (min_le_left _ _)) j k hjk z
    obtain ⟨X, hXmeas, hXpos, _hXmem, hXN, hXH⟩ :=
      hstopping M (hM.trans (min_le_right _ _)) j k z
    let Z := fun omega => (3 : ℝ)^((d : ℝ)*(X omega : ℝ))
    have hZmeas : Measurable Z :=
      (measurable_of_countable (fun n : ℕ => (3 : ℝ)^((d : ℝ)*(n : ℝ)))).comp hXmeas
    have hZ : ∀ omega, 0 ≤ Z omega := fun omega => by dsimp only [Z]; positivity
    let G := fun omega => 1+A*(K omega+1)^2*Z omega
    have hGmeas : Measurable G := measurable_const.add
      (((hKmeas.add measurable_const).pow_const 2).const_mul A |>.mul hZmeas)
    refine ⟨G, hGmeas, fun omega =>
      le_add_of_nonneg_right (mul_nonneg (mul_nonneg hA (sq_nonneg _)) (hZ omega)), ?_, ?_⟩
    · exact harmonic_energy_stopping_norm M.P.toMeasure K Z hKmeas hZmeas hq hA hCE.le hCS hKN hXN
    · filter_upwards [hKE] with omega henergyOmega
      intro f hf hc B hB hb u hu hh x hx r hr _hrr
      let h := cutoffHarmonicCellH2Datum f hf hc
      have hunit := harmonicCell_scalarDirichlet M j k z omega hu hh
      obtain ⟨F, hF, hprice⟩ := harmonicCell_zeroLift_price hCenergy.le f hf hc hB hb
      have he := henergyOmega h F hunit hF
      rw [harmonicCell_physicalEnergyNorm_eq M j k (translatePotentialSample z omega) h F hunit hF] at he
      have hK0 : 0 ≤ K omega := zero_le_one.trans (hKone omega)
      have hscale := centeredCubeScale_pos (k : ℤ)
      have hwhole : vectorNormalizedL2On (cube d (k : ℤ))
          (fun y => Real.sqrt (aCutoff M j (translatePotentialSample z omega) y) •
            (centeredCubeRawDilation (k : ℤ) u).grad y) ≤
          Real.sqrt (ahom M j)*((3 : ℝ)^k)⁻¹*B*(Cd*K omega) := by
        refine (he.trans (mul_le_mul_of_nonneg_left hprice (by positivity))).trans_eq ?_
        dsimp only [Cd, centeredCubeScale]
        rw [zpow_natCast]
        ring
      have hphysical := harmonicCell_physicalDirichlet M j k (translatePotentialSample z omega) hunit
      have hdatum := (harmonicDatum_rawDilation_holder_bounds f hf hc hB hb (k : ℤ)).1
      have hholder := hXH omega _ _ (fun _ => 0) hphysical
        (Section6TheoremC.memHolder_zero _ _) hdatum
      have hgrowth := harmonicCell_native_energy_growth hd M j k hjk z omega
        f hf hc hB hb u hCH.le (mul_nonneg hCd hK0) (X omega) hwhole hholder x hx hr
      refine hgrowth.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsmall : Cd*K omega+3*(d : ℝ) ≤ (Cd+3*(d : ℝ))*(K omega+1) := by
        have hp : 0 ≤ 3*(d : ℝ)*K omega := by positivity
        nlinarith only [hCd, hp]
      have hsq : (Cd*K omega+3*(d : ℝ))^2 ≤
          (Cd+3*(d : ℝ))^2*(K omega+1)^2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hsmall _
      have hmajor : (1+CH^2)*(6 : ℝ)^((d : ℝ)-1/4)*
          (Cd*K omega+3*(d : ℝ))^2*Z omega ≤ G omega := by
        calc
          _ ≤ (1+CH^2)*(6 : ℝ)^((d : ℝ)-1/4)*
              ((Cd+3*(d : ℝ))^2*(K omega+1)^2)*Z omega :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (hZ omega)
          _ = A*(K omega+1)^2*Z omega := by dsimp only [A]; ring
          _ ≤ G omega := by dsimp only [G]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmajor (sq_nonneg B))
        (by positivity)
  · refine ⟨1, by norm_num, ?_⟩
    intro M _hM
    exact False.elim (hd M.shellPrefix.dimension)

end SubdiffusiveProcess.Static
