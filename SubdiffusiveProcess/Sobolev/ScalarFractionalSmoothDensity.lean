import SubdiffusiveProcess.Sobolev.FractionalSubtraction
import SubdiffusiveProcess.Sobolev.FractionalFullUpstream
import SubdiffusiveProcess.Sobolev.SmoothFractionalUpstream
import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDensity
import Homogenization.Sobolev.Fractional.EuclideanWspSmoothGraph
import Homogenization.Sobolev.Fractional.EuclideanWspLpMembership
import SubdiffusiveProcess.CoarseGrainingVocab.PaperFractionalDualBridge

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

private def firstIndex {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

private noncomputable def scalarEmbed {d : ℕ} (hd : 2 ≤ d)
    {Ω : Opens (SpatialCoordinates d)} (f : DomainL2 Ω) :
    Fin d → DomainL2 Ω := Pi.single (firstIndex hd) f

private theorem scalarEmbed_norm_sq {d : ℕ} (hd : 2 ≤ d)
    {Ω : Opens (SpatialCoordinates d)} (f : DomainL2 Ω) :
    ∑ i : Fin d, ‖scalarEmbed hd f i‖ ^ 2 = ‖f‖ ^ 2 := by
  classical
  rw [Finset.sum_eq_single (firstIndex hd)]
  · simp [scalarEmbed]
  · intro b hb hne
    simp [scalarEmbed, hne]
  · simp

private theorem scalarEmbed_seminorm_eq {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1) (f : DomainL2
      (centeredCube (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr)) :
    cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s (scalarEmbed hd f) =
      cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s (fun _ : Fin 1 => f) := by
  classical
  let Ω : Opens (SpatialCoordinates d) := centeredCube
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict (Ω : Set (SpatialCoordinates d))
  have hzero : ∀ i : Fin d, i ≠ firstIndex hd →
      ∀ᵐ x ∂μ, (scalarEmbed hd f i : SpatialCoordinates d → ℝ) x = 0 := by
    intro i hi
    have hi0 : scalarEmbed hd f i = (0 : DomainL2 Ω) := by
      simp [scalarEmbed, hi]
    rw [hi0]
    exact Lp.coeFn_zero ℝ (1 : ℝ≥0∞) (volume.restrict (Ω : Set (SpatialCoordinates d)))
  unfold cubeFractionalL2Seminorm
  congr 2
  apply lintegral_congr_ae
  have hzero_all : ∀ᵐ x ∂μ, ∀ i : Fin d, i ≠ firstIndex hd →
      (scalarEmbed hd f i : SpatialCoordinates d → ℝ) x = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : i = firstIndex hd
    · filter_upwards with x
      intro h
      exact (h hi).elim
    · filter_upwards [hzero i hi] with x hx
      intro _
      exact hx
  filter_upwards [hzero_all] with x hx
  apply lintegral_congr_ae
  filter_upwards [hzero_all] with y hy
  rw [Finset.sum_eq_single (firstIndex hd)]
  · simp [scalarEmbed]
  · intro b hb hne
    rw [hx b hne, hy b hne]
    norm_num
  · simp

private noncomputable def scalarVector {d : ℕ} (hd : 2 ≤ d)
    {Q : Homogenization.TriadicCube d}
    {hr : 0 < Homogenization.cubeScaleFactor Q}
    {s : Set.Ioo (0 : ℝ) 1}
    (f : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s) :
    CubeFractionalL2 (k := d) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s := by
  let g : Fin d → DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr) := scalarEmbed hd (f.val 0)
  have hg : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s g < ⊤ := by
    rw [scalarEmbed_seminorm_eq hd Q hr s (f.val 0)]
    have heq : (fun _ : Fin 1 => f.val 0) = f.val := by
      funext i
      fin_cases i
      rfl
    rw [heq]
    exact f.property
  exact ⟨g, hg⟩

private theorem scalarNorm_eq_scalarVectorNorm {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s) :
    cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s f =
      cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s (scalarVector hd f) := by
  unfold cubeFractionalL2Norm
  dsimp [scalarVector]
  rw [scalarEmbed_seminorm_eq hd Q hr s (f.val 0)]
  have heq : (fun _ : Fin 1 => f.val 0) = f.val := by
    funext i
    fin_cases i
    rfl
  rw [heq]
  rw [scalarEmbed_norm_sq hd (f.val 0)]
  simp

private theorem scalarEmbed_memLp_normalized {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (f : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr)) :
    MemLp (fun x => Homogenization.HilbertVec.ofVec
      (fun i => scalarEmbed hd f i x)) (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure Q) := by
  let Ω : Opens (SpatialCoordinates d) := centeredCube
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
  let U := Homogenization.cubeBoundedMeasurableDomain Q
  have hhilbert : MemLp (fun x => Homogenization.HilbertVec.ofVec
      (fun i => scalarEmbed hd f i x)) (2 : ℝ≥0∞)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    by_cases hi : i = firstIndex hd
    · subst i
      simpa only [scalarEmbed, firstIndex, Homogenization.HilbertVec.ofVec,
        PiLp.toLp_apply] using (Lp.memLp f)
    · have hi0 : scalarEmbed hd f i = (0 : DomainL2 Ω) := by
        simp [scalarEmbed, hi]
      simpa only [Homogenization.HilbertVec.ofVec, PiLp.toLp_apply, hi0] using
        (Lp.memLp (0 : DomainL2 Ω))
  have hrawmemU : MemLp (fun x => Homogenization.HilbertVec.ofVec
      (fun i => scalarEmbed hd f i x)) (2 : ℝ≥0∞) U.restrictedVolume := by
    rw [Homogenization.cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
    rw [← centeredCube_restrict_volume_eq_cubeMeasure Q hr]
    exact hhilbert
  have hnormmemU : MemLp (fun x => Homogenization.HilbertVec.ofVec
      (fun i => scalarEmbed hd f i x)) (2 : ℝ≥0∞) U.normalizedVolume := by
    exact (U.memLp_normalizedVolume_iff (2 : ℝ≥0∞) _).mpr hrawmemU
  simpa only [U,
    Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    using hnormmemU

private theorem scalarEmbed_eSeminorm_lt_top {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s) :
    Homogenization.cubeEuclideanWspESeminorm Q s
        Homogenization.FiniteLpExponent.two
        (fun x i => scalarEmbed hd (f.val 0) i x) < ⊤ := by
  have hsemi : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s (scalarEmbed hd (f.val 0)) < ⊤ := by
    rw [scalarEmbed_seminorm_eq hd Q hr s (f.val 0)]
    have heq : (fun _ : Fin 1 => f.val 0) = f.val := by
      funext i
      fin_cases i
      rfl
    rw [heq]
    exact f.property
  have hpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm Q s
      Homogenization.FiniteLpExponent.two
      (fun x i => scalarEmbed hd (f.val 0) i x) < ⊤ := by
    rw [← cubeFractionalL2Seminorm_eq_paperFractionalSeminorm hd Q hr s
      (scalarEmbed hd (f.val 0))]
    exact hsemi
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm at hpaper
  have hc : (ENNReal.ofReal (s : ℝ)) ^
      ((Homogenization.FiniteLpExponent.two.exponent.toReal)⁻¹) ≠ 0 := by
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr s.2.1)
      ENNReal.ofReal_ne_top).ne'
  rcases ENNReal.mul_lt_top_iff.mp hpaper with h | h | h
  · exact h.2
  · exact (hc h).elim
  · simp [h]

private theorem scalarProjection_seminorm_le {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (H : Fin d → DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr)) :
    cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s (fun _ : Fin 1 => H (firstIndex hd)) ≤
      cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s H := by
  classical
  unfold cubeFractionalL2Seminorm
  apply ENNReal.rpow_le_rpow
  · apply mul_le_mul_right
    apply lintegral_mono
    intro x
    apply lintegral_mono
    intro y
    apply ENNReal.div_le_div
    · apply ENNReal.ofReal_le_ofReal
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d => (H i x - H i y) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ (firstIndex hd))
      simpa using h
    · exact le_rfl
  · positivity

end SubdiffusiveProcess

namespace SubdiffusiveProcess

theorem exists_scalarCubeFractionalL2_globalSmooth_sub_norm_lt
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (u : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s,
      (∃ g : SpatialCoordinates d → ℝ,
        ContDiff ℝ ∞ g ∧
        (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] g) ∧
      ∃ w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr s,
        w.val 0 = u.val 0 - v.val 0 ∧
        cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr s w < ε := by
  let Ffun : Homogenization.Vec d → Homogenization.Vec d :=
    fun x i => scalarEmbed hd (u.val 0) i x
  have hFmem : MemLp (fun x => Homogenization.HilbertVec.ofVec (Ffun x))
      (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure Q) := by
    simpa only [Ffun] using scalarEmbed_memLp_normalized hd Q hr (u.val 0)
  have hFsemi :
      Homogenization.cubeEuclideanWspESeminorm Q s
        Homogenization.FiniteLpExponent.two Ffun < ⊤ :=
    scalarEmbed_eSeminorm_lt_top hd Q hr s u
  letI : NeZero d := ⟨by omega⟩
  have hWsp : Homogenization.MemCubeEuclideanWsp Q s
      Homogenization.FiniteLpExponent.two Ffun :=
    Homogenization.memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top
      hFmem hFsemi
  let G : Homogenization.CubeEuclideanWspL2Field Q s
      Homogenization.FiniteLpExponent.two :=
    { toCubeEuclideanWspField :=
        { toCubeEuclideanLpField :=
            { toField := Ffun, euclideanMemLp := hFmem }
          euclideanMemWsp := hWsp }
      euclideanMemL2 := hFmem }
  obtain ⟨h, hhfull, hhl2⟩ :=
    Homogenization.exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt
      G (epsilon := ENNReal.ofReal (ε / 4))
      (ENNReal.ofReal_pos.mpr (by linarith))
  let Ω : Opens (SpatialCoordinates d) := centeredCube
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
  let U := Homogenization.cubeBoundedMeasurableDomain Q
  have coordMem (i : Fin d) :
      MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    have hi : MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        (Homogenization.normalizedCubeMeasure Q) := by
      simpa only [Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using
        h.euclideanMemLp_two.eval_piLp i
    have hiU : MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        U.normalizedVolume := by
      simpa only [U,
        Homogenization.cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hi
    have hiR : MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        U.restrictedVolume :=
      (U.memLp_normalizedVolume_iff (2 : ℝ≥0∞) _).mp hiU
    rw [Homogenization.cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure] at hiR
    rw [← centeredCube_restrict_volume_eq_cubeMeasure Q hr] at hiR
    simpa only [Ω] using hiR
  let H : Fin d → DomainL2 Ω :=
    fun i => (coordMem i).toLp (fun x => h.toField x i)
  have hHcoord (i : Fin d) :
      ∀ᵐ x ∂(Homogenization.normalizedCubeMeasure Q),
        (H i : SpatialCoordinates d → ℝ) x = h.toField x i := by
    have hi : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
        (H i : SpatialCoordinates d → ℝ) x = h.toField x i :=
      MemLp.coeFn_toLp (coordMem i)
    have hicube : ∀ᵐ x ∂Homogenization.cubeMeasure Q,
        (H i : SpatialCoordinates d → ℝ) x = h.toField x i := by
      simpa only [Ω, ← centeredCube_restrict_volume_eq_cubeMeasure Q hr] using hi
    exact Measure.ae_smul_measure hicube
      (ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹))
  have hHae :
      (fun x i => H i x) =ᵐ[Homogenization.normalizedCubeMeasure Q]
        h.toField := by
    have hall : ∀ᵐ x ∂(Homogenization.normalizedCubeMeasure Q), ∀ i : Fin d,
        (H i : SpatialCoordinates d → ℝ) x = h.toField x i :=
      ae_all_iff.mpr hHcoord
    filter_upwards [hall] with x hx
    funext i
    exact hx i
  have hHsemi : Homogenization.cubeEuclideanWspESeminorm Q s
      Homogenization.FiniteLpExponent.two (fun x i => H i x) < ⊤ := by
    rw [Homogenization.cubeEuclideanWspESeminorm_congr_ae hHae]
    exact h.memCubeEuclideanWsp.eSeminorm_lt_top
  have hHpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm Q s
      Homogenization.FiniteLpExponent.two (fun x i => H i x) < ⊤ := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm
    exact ENNReal.mul_lt_top (by finiteness) hHsemi
  have hHlocal : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s H < ⊤ := by
    rw [cubeFractionalL2Seminorm_eq_paperFractionalSeminorm hd Q hr s H]
    exact hHpaper
  have hvsemi : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s
      (fun _ : Fin 1 => H (firstIndex hd)) < ⊤ :=
    lt_of_le_of_lt (scalarProjection_seminorm_le hd Q hr s H) hHlocal
  let v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s :=
    ⟨fun _ : Fin 1 => H (firstIndex hd), hvsemi⟩
  have hvrep : ∃ g : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ g ∧
      (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] g := by
    let g : SpatialCoordinates d → ℝ := fun x => h.toField x (firstIndex hd)
    refine ⟨g, (contDiff_pi.mp h.contDiff) (firstIndex hd), ?_⟩
    have hc := MemLp.coeFn_toLp (coordMem (firstIndex hd))
    simpa only [v, H, g, Ω] using hc
  have hwsemi : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s
      (fun _ : Fin 1 => u.val 0 - v.val 0) < ⊤ := by
    apply cubeFractionalL2Seminorm_sub_lt_top hd
      (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr s
      u.val v.val u.property v.property
  let w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s :=
    ⟨fun _ : Fin 1 => u.val 0 - v.val 0, hwsemi⟩
  let E : Fin d → DomainL2 Ω :=
    fun i => scalarEmbed hd (u.val 0) i - H i
  have hEcoord (i : Fin d) :
      ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
        (E i : SpatialCoordinates d → ℝ) x = Ffun x i - h.toField x i := by
    have hsub := Lp.coeFn_sub (scalarEmbed hd (u.val 0) i) (H i)
    have hscalar : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
        (scalarEmbed hd (u.val 0) i : SpatialCoordinates d → ℝ) x =
          Ffun x i := by
      by_cases hi : i = firstIndex hd
      · subst i
        filter_upwards [] with x
        rfl
      · have hi0 : scalarEmbed hd (u.val 0) i =
            (0 : DomainL2 Ω) := by simp [scalarEmbed, hi]
        rw [hi0]
        have hz := Lp.coeFn_zero ℝ (1 : ℝ≥0∞)
          (volume.restrict (Ω : Set (SpatialCoordinates d)))
        filter_upwards [hz] with x hx
        simpa only [Ffun, scalarEmbed, Pi.single_apply, hi, ↓reduceIte,
          Pi.zero_apply] using hx
    filter_upwards [hsub, hscalar,
      MemLp.coeFn_toLp (coordMem i)] with x hxsub hxscalar hxH
    calc
      (E i : SpatialCoordinates d → ℝ) x =
          ((scalarEmbed hd (u.val 0) i : SpatialCoordinates d → ℝ) x -
            (H i : SpatialCoordinates d → ℝ) x) := hxsub
      _ = Ffun x i - h.toField x i := by rw [hxscalar, hxH]
  have hEae :
      (fun x i => E i x) =ᵐ[Homogenization.normalizedCubeMeasure Q]
        (fun x => Ffun x - h.toField x) := by
    have hEv : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
        ∀ i : Fin d, (E i : SpatialCoordinates d → ℝ) x =
          Ffun x i - h.toField x i := ae_all_iff.mpr hEcoord
    have hEcube : ∀ᵐ x ∂Homogenization.cubeMeasure Q, ∀ i : Fin d,
        (E i : SpatialCoordinates d → ℝ) x = Ffun x i - h.toField x i := by
      simpa only [Ω, ← centeredCube_restrict_volume_eq_cubeMeasure Q hr] using hEv
    have hEnorm := Measure.ae_smul_measure hEcube
      (ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹))
    filter_upwards [hEnorm] with x hx
    funext i
    exact hx i
  have hUlocal : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s
      (scalarEmbed hd (u.val 0)) < ⊤ := by
    rw [scalarEmbed_seminorm_eq hd Q hr s (u.val 0)]
    simpa only [show (fun _ : Fin 1 => u.val 0) = u.val by
      funext i; fin_cases i; rfl] using u.property
  have hElocal : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s E < ⊤ := by
    apply cubeFractionalL2Seminorm_sub_lt_top hd
      (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr s
      (scalarEmbed hd (u.val 0)) H hUlocal hHlocal
  let e : CubeFractionalL2 (k := d) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s := ⟨E, hElocal⟩
  have hscalar_le : cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s w ≤
      cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr s e := by
    unfold cubeFractionalL2Norm
    apply add_le_add
    · exact ENNReal.toReal_mono (ne_of_lt (by simpa only [e] using hElocal))
        (scalarProjection_seminorm_le hd Q hr s E)
    · apply mul_le_mul_of_nonneg_left
      · have hratio :
            Real.sqrt (∑ i : Fin 1, ‖w.val i‖ ^ 2) /
                Real.sqrt (volume.real
                  (centeredCube (Homogenization.cubeCenter Q)
                    (Homogenization.cubeScaleFactor Q) hr :
                    Set (SpatialCoordinates d))) ≤
              Real.sqrt (∑ i : Fin d, ‖e.val i‖ ^ 2) /
                Real.sqrt (volume.real
                  (centeredCube (Homogenization.cubeCenter Q)
                    (Homogenization.cubeScaleFactor Q) hr :
                    Set (SpatialCoordinates d))) := by
          apply div_le_div_of_nonneg_right
          · apply Real.sqrt_le_sqrt
            have hs := Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin d)))
              (f := fun i : Fin d => ‖E i‖ ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ (firstIndex hd))
            simpa [Fin.sum_univ_succ, e, w, v, E, scalarEmbed, firstIndex] using hs
          · exact Real.sqrt_nonneg _
        exact hratio
      · exact Real.rpow_nonneg (le_of_lt hr) _
  have hfullE : Homogenization.cubeEuclideanWspFullENorm Q s
      Homogenization.FiniteLpExponent.two (fun x i => E i x) =
      Homogenization.cubeEuclideanWspFullENorm Q s
        Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) := by
    exact Homogenization.cubeEuclideanWspFullENorm_congr_ae hEae
  have hswap : Homogenization.cubeEuclideanWspFullENorm Q s
      Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) =
      Homogenization.cubeEuclideanWspFullENorm Q s
        Homogenization.FiniteLpExponent.two (fun x => h.toField x - Ffun x) := by
    have hnorm :
        (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
            Homogenization.FiniteLpExponent.two.exponent (fun x => Ffun x - h.toField x) =
          (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
            Homogenization.FiniteLpExponent.two.exponent (fun x => h.toField x - Ffun x) := by
      unfold Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpENorm
      apply (Homogenization.cubeBoundedMeasurableDomain Q).normalizedLpENorm_congr_ae
      filter_upwards [] with x
      have hv : Ffun x - h.toField x = -(h.toField x - Ffun x) := by
        ext i
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      rw [hv]
      rw [Homogenization.euclideanNorm_eq_norm_ofVec,
        Homogenization.euclideanNorm_eq_norm_ofVec]
      have hof : Homogenization.HilbertVec.ofVec
          (-(h.toField x - Ffun x)) =
          -Homogenization.HilbertVec.ofVec (h.toField x - Ffun x) := by
        ext i
        rfl
      rw [hof, norm_neg]
    have hsemi :
        Homogenization.cubeEuclideanWspESeminorm Q s
            Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) =
          Homogenization.cubeEuclideanWspESeminorm Q s
            Homogenization.FiniteLpExponent.two (fun x => h.toField x - Ffun x) := by
      unfold Homogenization.cubeEuclideanWspESeminorm
      have hk : Homogenization.cubeEuclideanWspKernel s
          Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) =
          -(Homogenization.cubeEuclideanWspKernel s
            Homogenization.FiniteLpExponent.two (fun x => h.toField x - Ffun x)) := by
        funext z
        simp only [Homogenization.cubeEuclideanWspKernel_apply]
        have hv :
            (Ffun z.1 - h.toField z.1) - (Ffun z.2 - h.toField z.2) =
              -((h.toField z.1 - Ffun z.1) - (h.toField z.2 - Ffun z.2)) := by
          ext i
          simp only [Pi.sub_apply, Pi.neg_apply]
          ring
        rw [hv]
        have hof : Homogenization.HilbertVec.ofVec
            (-((h.toField z.1 - Ffun z.1) - (h.toField z.2 - Ffun z.2))) =
            -Homogenization.HilbertVec.ofVec
              ((h.toField z.1 - Ffun z.1) - (h.toField z.2 - Ffun z.2)) := by
          ext i
          rfl
        rw [hof]
        rw [smul_neg]
        change -(Homogenization.euclideanDist z.1 z.2 ^
            (-(s.1 + (d : ℝ) /
              Homogenization.FiniteLpExponent.two.exponent.toReal)) •
            Homogenization.HilbertVec.ofVec
              ((h.toField z.1 - Ffun z.1) -
                (h.toField z.2 - Ffun z.2))) =
          -(Homogenization.euclideanDist z.1 z.2 ^
            (-(s.1 + (d : ℝ) /
              Homogenization.FiniteLpExponent.two.exponent.toReal)) •
            Homogenization.HilbertVec.ofVec
              ((h.toField z.1 - Ffun z.1) -
                (h.toField z.2 - Ffun z.2)))
        rfl
      rw [hk, eLpNorm_neg]
    simp only [Homogenization.cubeEuclideanWspFullENorm,
      Homogenization.cubeEuclideanWspScalePowerWeight]
    rw [hnorm, hsemi]
  have hpaper_le : SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s
      Homogenization.FiniteLpExponent.two (fun x i => E i x) ≤
      2 * Homogenization.cubeEuclideanWspFullENorm Q s
        Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) := by
    calc
      _ ≤ 2 * Homogenization.cubeEuclideanWspFullENorm Q s
          Homogenization.FiniteLpExponent.two (fun x i => E i x) :=
        SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm_le_two_mul_cubeEuclideanWspFullENorm
          Q s Homogenization.FiniteLpExponent.two (fun x i => E i x)
      _ = _ := by rw [hfullE]
  have hpaper_lt : SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s
      Homogenization.FiniteLpExponent.two (fun x i => E i x) <
      ENNReal.ofReal (ε / 2) := by
    calc
      _ ≤ 2 * Homogenization.cubeEuclideanWspFullENorm Q s
          Homogenization.FiniteLpExponent.two (fun x => Ffun x - h.toField x) := hpaper_le
      _ < 2 * ENNReal.ofReal (ε / 4) := by
        have hh := ENNReal.mul_lt_mul_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by finiteness) (by simpa only [G] using hhfull)
        simpa only [hswap, mul_comm] using hh
      _ = ENNReal.ofReal (ε / 2) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        congr 1
        ring
  have hfinal : cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s w < ε := by
    have hnorm := cubeFractionalL2Norm_eq_paperFractionalFullNorm hd Q hr s e
    have hreal : (SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s
        Homogenization.FiniteLpExponent.two (fun x i => E i x)).toReal < ε := by
      have hle := ENNReal.toReal_mono (by finiteness) hpaper_lt.le
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ ε / 2)] at hle
      linarith
    exact lt_of_le_of_lt hscalar_le (by simpa only [hnorm] using hreal)
  refine ⟨v, hvrep, w, ?_, ?_⟩
  · rfl
  · exact hfinal

end SubdiffusiveProcess
