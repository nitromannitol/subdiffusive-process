module

public import SubdiffusiveProcess.Paper.rem_resolved_meshes

@[expose] public section

/-! Level-`Lam` finite-cutoff one-step residual of `rem_resolved_meshes`: the same statement for the
relabelled stationary cutoff coefficient of an arbitrary level `Lam`, provided the root exponent
`N - k + 1` does not exceed `Lam` (the root cube lies below the top scale).  This contains the
original statement (`Lam = N + L`) and also covers cubes larger than the top scale of the field
(`Lam < N`), which is what the infrared-free coefficient on a cube of side `3^j > 1` needs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- **The finite-cutoff one-step residual** (`R2`).  For a finite infrared coefficient
`a = c_F · a_{N+L}(3^N ·)` on `Q` (the relabelled cutoff coefficient of `in_6_16`), an arbitrary
essentially bounded mean-zero source and weak Neumann solution, and a root of depth `k` with
active faces `I`, at every target depth `n` inside the tightened prefix window
(`n + ℒ ≤ N-k+1`), the folded one-center estimate transported to `Q`:
`E(3^{n-N}/2) ≤ C₁ (s/R_k)^{t₀} [E(3R_k) + (c_F · ref)^{-1} ‖f‖_∞² R_k^{d+2}]` with the root
reference `ref = It.ref (N+L) (N-k+1-2) (3^N·centre) (relabel N ω)`. -/
def aux_neumann_ht_finite_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (Kt C1 delta1 : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
    (_ : in_poincare d hd E) (_ : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (_ : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
    M.delta ≤ delta1 →
    ∀ (omega : BilateralField d) (N Lam : ℕ) (cF : ℝ), 0 < cF →
    ∀ a : PositiveCoefficient (unitNeumannCube d),
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y = cF * (Sreg.cutoffOn Lam (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y)) →
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (n k : ℕ),
      1 ≤ k → k ≤ N → N - k + 1 ≤ Lam → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2 →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1 →
      aux_rem_resolved_meshes_energy a u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
        C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (cF * It.ref Lam (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
              (aux_rem_resolved_meshes_relabel N omega))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))


theorem neumann_ht_finite_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ)) :
    ∃ Kt C1 delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 0 ≤ C1 ∧ 0 < delta1 ∧
        ∀ Rstar : ℝ, aux_neumann_ht_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1 := by
  obtain ⟨Cf, Kf, hCf, hKf, hfold⟩ := aux_rem_resolved_meshes_folded_uniform_all d hd
  obtain ⟨Ch, hCh, hsrc⟩ := aux_rem_resolved_meshes_fin_source d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hα1 : (t0 + 2 - (d : ℝ)) / 2 < 1 := by linarith
  have hα2 : 1 / 2 ≤ (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have hαeq : 2 * (1 - (t0 + 2 - (d : ℝ)) / 2) = (d : ℝ) - t0 := by ring
  have ht0 : 0 ≤ t0 := by linarith
  have h1α : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  refine ⟨Kf, 2 * Cf ^ 2 * max 1 (Ch ^ 2 * d * 6 ^ (d + 2)),
    min (min (1 / 2) (((1 - (t0 + 2 - (d : ℝ)) / 2) / Cf) ^ 2)) Cf⁻¹, hKf,
    mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _)),
    lt_min (lt_min (by norm_num) (by positivity)) (inv_pos.mpr hCf), ?_⟩
  intro Rstar M E Poinc Ext Sreg It hdet hδ omega N Lam cF hcF a ha f hf Kf0 hKf0 hfb hf0 u hu y hy I n k
    hk1 hkN hlev _hRkR _hn8 hI hwin
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδC : M.delta ≤ Cf⁻¹ := hδ.trans (min_le_right _ _)
  have hαr := aux_rem_resolved_meshes_alpha_range Cf ((t0 + 2 - (d : ℝ)) / 2) hCf hα1 hα2
    M.delta hδpos (hδ.trans (min_le_left _ _))
  -- the source: a measurable everywhere-bounded representative, same weak equation
  obtain ⟨f2, hf2m, hf2b, hff2⟩ := aux_rem_resolved_meshes_clamp f hf Kf0 hKf0 hfb
  have hf20 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 y) = 0 := by
    rw [← hf0]; exact integral_congr_ae hff2.symm
  have hu2 : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) ψ =
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          f2 x * (ψ : SobolevData (unitNeumannCube d)).1 x := by
    intro ψ
    rw [hu ψ]
    apply integral_congr_ae
    filter_upwards [hff2] with x hx
    rw [hx]
  -- scales
  have hl : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (N - k + 1) := by positivity
  have hRk : (0 : ℝ) < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have h3m := aux_rem_resolved_meshes_fin_scales N k hkN
  have hρeq : (3 : ℝ) ^ (N - k + 1) / 2 =
      (3 : ℝ) ^ (N : ℤ) * (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)) := by
    rw [h3m]; ring
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := aux_rem_resolved_meshes_root_package Sreg Lam
    (aux_rem_resolved_meshes_relabel N omega) ((3 : ℝ) ^ (N : ℤ)) hl cF hcF a ha f2 hf2m Kf0
    hKf0 hf2b hf20 u hu2 y hy I Lstar ((3 : ℝ) ^ (-((k : ℤ))) / 2) hLstar hRk
    (aux_rem_resolved_meshes_fin_Rk k hk1) hI ((3 : ℝ) ^ (N - k + 1)) hR hρeq
  -- the divergence-form source on the root cube
  have hFrm : Measurable (fun x : SpatialCoordinates d => ((cF * (3 : ℝ) ^ (N : ℤ))⁻¹ *
      f2 (((3 : ℝ) ^ (N : ℤ))⁻¹ • coordinateFold ((3 : ℝ) ^ (N : ℤ) •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x))) :=
    measurable_const.mul (hf2m.comp ((continuous_const_smul _).comp
      (coordinateFold_continuous _ _ _)).measurable)
  have hMF : 0 ≤ (cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf0 := by positivity
  have hFrb : ∀ x : SpatialCoordinates d, |(cF * (3 : ℝ) ^ (N : ℤ))⁻¹ *
      f2 (((3 : ℝ) ^ (N : ℤ))⁻¹ • coordinateFold ((3 : ℝ) ^ (N : ℤ) •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x)| ≤
      (cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf0 := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hcF hl))]
    exact mul_le_mul_of_nonneg_left (hf2b _) (by positivity)
  obtain ⟨g, hgrad, hHol, hgae, hid, hGb⟩ := hsrc ((3 : ℝ) ^ (N : ℤ) •
    aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR _ hFrm _ hMF hFrb
  have hweq : ∀ φ : killedSobolevGraph (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR),
      sobolevCoefficientForm fc (ut : SobolevData (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR))
        (φ : SobolevData (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR)) =
      -inner ℝ hgrad (subspaceGradient (killedSobolevGraph (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR)) φ) :=
    fun φ => (hueq φ).trans (hid φ)
  -- the prefix window
  have hmL : N - k + 1 ≤ Lam := hlev
  have hnm : n ≤ N - k + 1 := by omega
  have hnz : (n : ℤ) ≤ ((N - k + 1 : ℕ) : ℤ) - (It.prefixLen ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kf) (N - k + 1)
      (aux_rem_resolved_meshes_relabel N omega) : ℤ) := by
    have h := hwin
    omega
  have hcore := hfold M E Poinc Ext Sreg It hdet hδC ((t0 + 2 - (d : ℝ)) / 2) hαr Lam
    (N - k + 1) n ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I) hR
    (aux_rem_resolved_meshes_relabel N omega) I (aux_rem_resolved_meshes_faceSet y I) hmL hnm hnz
    fc hfc g hgrad ut hHol hgae hweq
  -- unfold the normalized norms through the root-cube energy identity
  have hn3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hnρ : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (N - k + 1) := pow_le_pow_right₀ (by norm_num) hnm
  have hEs := hE ((3 : ℝ) ^ n) hn3 hnρ
  have hE3 := hE ((3 : ℝ) ^ (N - k + 1)) hR le_rfl
  have hvol : ∀ (r : ℝ) (hr : 0 < r), volume.real (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) = r ^ d := by
    intro r hr
    rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  simp only [normalizedEnergyNorm] at hcore
  rw [hEs, hE3, hvol, hvol] at hcore
  have hrad_s : (3 : ℝ) ^ n / (2 * (3 : ℝ) ^ (N : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]; simp only [zpow_natCast]; ring
  have hrad_3 : (3 : ℝ) ^ (N - k + 1) / (2 * (3 : ℝ) ^ (N : ℤ)) =
      3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) := by
    rw [h3m]; field_simp
  rw [hrad_s, hrad_3] at hcore
  have hEnn : ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      0 ≤ aux_rem_resolved_meshes_energy a u A := fun A hA => by
    rw [aux_rem_resolved_meshes_energy_local a u A hA]; exact localGradientEnergy_nonneg _ _ _
  have hm : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hkN, Nat.cast_one]
  have hG0 : 0 ≤ halfHolderSeminorm (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR : Set (SpatialCoordinates d)) g :=
    Real.sSup_nonneg (fun v hv => by
      obtain ⟨x, -, y', -, -, rfl⟩ := hv
      positivity)
  exact aux_rem_resolved_meshes_final_arith d t0 ((t0 + 2 - (d : ℝ)) / 2) hαeq ht0 n (N - k + 1) N k
    I.card hm Cf Ch cF _ Kf0 _ _ _ hCf.le hCh hcF (It.ref_pos _ _ _ _) hKf0
    (hEnn _ measurableSet_ball) (hEnn _ measurableSet_ball) hG0
    (by simpa only [mul_assoc] using hcore) hGb

end SubdiffusiveProcess.Paper
