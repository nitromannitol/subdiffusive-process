module

public import SubdiffusiveProcess.Paper.lem_as_regularity_two_mesh
public import SubdiffusiveProcess.Paper.lem_as_regularity_native_allowance
public import SubdiffusiveProcess.Paper.lem_as_regularity_reference_extremes
public import SubdiffusiveProcess.Paper.lem_as_regularity_primitive_witness
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.Paper.inputs_hES_witness
public import SubdiffusiveProcess.Paper.cor_neumann_source

@[expose] public section

/-! One pathwise constant controls the energy of every bounded-source Neumann
solution at every resolved radius and every cutoff on the unit cube. The proof
composes the original prefix bank with deterministic iteration and coarse
global coercivity; microscopic radii and Holder estimates are not claimed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A coarse root ellipticity bound controls the global energy of every bounded-source Neumann solution. -/
theorem aux_lem_as_regularity_neumann_resolved_global {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (Pc : in_poincare d hd E) (a : PositiveCoefficient (unitNeumannCube d))
    (K : ℝ) (hK : (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a
      (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ K)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f x| ≤ Kf)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hu : SolvesNeumann a f u) :
    aux_rem_resolved_meshes_energy a u Set.univ ≤ Pc.C ^ 2 * K * Kf ^ 2 := by
  rw [aux_rem_resolved_meshes_energy_local a u _ MeasurableSet.univ]
  have hg := aux_cor_neumann_source_global_energy_ae hd E Pc a f hf Kf hKf hfb u hu
  have hh := mul_le_mul_of_nonneg_left hK (mul_nonneg (sq_nonneg Kf) (sq_nonneg Pc.C))
  refine (localGradientEnergy_le a MeasurableSet.univ _).trans (hg.trans (hh.trans_eq ?_))
  ring

/-- Resolved-radius Neumann energy has one constant uniform over the cutoff, source and solution. -/
theorem lem_as_regularity_neumann_resolved (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) f u →
        ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ K * Kf ^ 2 * rad ^ t := by
  have dimNZ : NeZero d := ⟨by omega⟩
  let t0 := ((d : ℝ) + t) / 2
  let etaLoss := t0 - t
  have ht01 : (d : ℝ) - 1 < t0 := by dsimp only [t0]; linarith only [ht1, ht2]
  have ht02 : t0 < (d : ℝ) := by dsimp only [t0]; linarith only [ht2]
  have heta : 0 < etaLoss := by dsimp only [etaLoss, t0]; linarith only [ht2]
  have heta1 : etaLoss < t0 - ((d : ℝ) - 1) := by dsimp only [etaLoss]; linarith only [ht1]
  obtain ⟨eps, rate, ds, Cstep, c, heps, hrate, hds, hCs, hc, hstep⟩ :=
    lem_as_regularity_neumann_onestep d hd E D t0 ht01 ht02
  obtain ⟨xi, A, hxi, hA, hgap, hentropy⟩ := exists_mesh_allowance_slopes d c etaLoss hc heta
  obtain ⟨Cresp, dr, hCr, hdr, hresponses⟩ := inputs_responses_witness d hd 1 le_rfl
  let q : ℝ := 256 * d + 32
  have hq : 1 ≤ q := by
    dsimp only [q]
    linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hsq : 8 * (d : ℝ) < (1 / 32 : ℝ) * q := by dsimp only [q]; linarith
  obtain ⟨db, hdb, hbank⟩ := lem_as_regularity_native_allowance d hd E Pc Xc Sf W Cp D inputs_hES_witness
    Step Dbase Interp Cresp hCr (1 / 32) eps q rate A (by norm_num) heps hq hsq hrate hA
    2 1 1 xi zero_le_one hxi hentropy
  obtain ⟨dv, hdv, href⟩ := lem_as_regularity_reference_extremes d hd 1 zero_lt_one
  obtain ⟨dc, hdc, hcoarse⟩ := lem_as_coarse d hd E Pc Xc Sf W Cp D inputs_hES_witness
    Step Dbase Interp 1 (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨Cgeo, hCgeo, hmesh⟩ := lem_as_regularity_two_mesh d hd t0 etaLoss ht01 ht02 heta heta1
  refine ⟨min ds (min dr (min db (min dv (min 1 dc)))),
    lt_min hds (lt_min hdr (lt_min hdb (lt_min hdv (lt_min zero_lt_one hdc)))), ?_⟩
  intro M Rm Sreg It H hIR hdelta
  have hds' := hdelta.trans (min_le_left _ _)
  have hdr' := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdb' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdv' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hdc' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Rm0, hRm0, -⟩ := hresponses M hdr'
  obtain ⟨pot, F, P, R, Draw, Z, good, hEta, hPS⟩ :=
    lem_as_regularity_primitive_witness M (1 / 32) eps (by norm_num) heps
  filter_upwards [hstep M Rm0 H hIR hds' pot F P R Draw Z good hEta hPS,
    hbank M Rm0 Sreg It H hIR hdb' hRm0 pot hEta F P R Draw Z good hPS,
    href M Rm0 H hIR hdv', hcoarse M Rm Sreg It H hIR hdc'
      (fun _ => (1 / 2 : ℝ)) 1 one_pos ⟨0, by norm_num⟩] with omega hs hb hv hk
  obtain ⟨B, hB, hb⟩ := hb
  obtain ⟨V, hV, hv⟩ := hv
  obtain ⟨Klam, hKl, hk⟩ := hk
  let U := Cstep ^ (d + 1) * Real.exp (c * (d + 1 : ℕ) * B)
  have hU : 0 < U := mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hCs) _) (Real.exp_pos _)
  have hfactor : 0 < Pc.C ^ 2 * Klam + V := add_pos_of_nonneg_of_pos (by positivity) hV
  refine ⟨Cgeo * U * (2 : ℝ) ^ t * (Pc.C ^ 2 * Klam + V), by positivity, ?_⟩
  intro N f Kf hKf hf hfb hf0 u hu x hx rad hrad
  let a := cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos
  have hLam := (hk true).1 1 (Or.inl rfl) N
  simp only [ite_true] at hLam
  have hlam : (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ Klam :=
    (le_add_of_nonneg_left (E.Lam_pos _ _ _ _ _ _ _ _).le).trans hLam
  have hglobal := aux_lem_as_regularity_neumann_resolved_global hd E Pc a Klam hlam f hf Kf hKf hfb u hu
  have hmacro := hmesh M H omega N a u Kf (fun j z => Z N j z omega) (fun j z => Draw N j z omega)
    rate xi B V Cstep c hxi.le hB.le hV.le hCs hc hgap (hb N)
    (fun k hkn z hz => by simpa only [one_mul, Real.rpow_natCast] using hv N k hkn z hz)
    (fun y hy I s k hk1 hkN hsrange hsmin hs0 hsR hI =>
      hs N f hf Kf hKf hfb hf0 u hu y hy I 10 (by norm_num) s k hk1 hkN hsrange hsmin hs0 hsR hI)
    x hx rad hrad
  have hradpos : 0 < rad := lt_of_lt_of_le (zpow_pos (by norm_num) _) hrad
  have hpow : (2 * rad) ^ (t0 - etaLoss) = (2 : ℝ) ^ t * rad ^ t := by
    rw [show t0 - etaLoss = t by dsimp only [etaLoss]; ring,
      Real.mul_rpow (by norm_num) hradpos.le]
  rw [hpow] at hmacro
  have hsum : aux_rem_resolved_meshes_energy a u Set.univ + V * Kf ^ 2 ≤
      (Pc.C ^ 2 * Klam + V) * Kf ^ 2 := by nlinarith only [hglobal]
  have hmono : localGradientEnergy a
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        aux_rem_resolved_meshes_energy a u (Metric.ball x rad) := by
    exact (aux_rem_resolved_meshes_energy_local a u
      (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)).symm.trans_le
      (aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ Set.inter_subset_left)
  refine hmono.trans (hmacro.trans ((mul_le_mul_of_nonneg_left hsum ?_).trans_eq ?_))
  · positivity
  · dsimp only [U]
    ring

end SubdiffusiveProcess.Paper
