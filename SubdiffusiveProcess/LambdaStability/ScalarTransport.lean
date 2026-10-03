module

public import SubdiffusiveProcess.LambdaStability.ScalarCarriers
public import SubdiffusiveProcess.LambdaStability.MonotoneCap

@[expose] public section

/-! Stability for the scalar response probes, with their literal unit-sphere loads. -/
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

def probeEnergy (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) (B A : Mat d) : ℝ :=
  ∑' l : ℕ, Ch02.geometricWeight t 2 l * probeShell w P (P.scale - (l : ℤ)) g B A

def probeError (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) (B A : Mat d) : ℝ := Real.sqrt (probeEnergy w P t g B A)

omit [NeZero d] in
theorem probeEnergy_nonneg (w : Vec d) (P : TriadicCube d) {t : ℝ} (ht : 0 < t)
    (g : CoeffField d) (B A : Mat d) : 0 ≤ probeEnergy w P t g B A := by
  apply tsum_nonneg
  intro l
  rw [Ch02.geometricWeight_eq_old]
  exact mul_nonneg (geometricWeight_nonneg l (by positivity)) (probeShell_nonneg _ _ _ _ _ _)

theorem probeEnergy_summable (w : Vec d) (P : TriadicCube d) {t : ℝ} (ht : 0 < t)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) : Summable (fun l : ℕ =>
      Ch02.geometricWeight t 2 l * probeShell w P (P.scale - (l : ℤ)) g B A) := by
  simp only [Ch02.geometricWeight_eq_old]
  exact summable_geometricWeight_mul_of_nonneg_of_le (by positivity)
    (fun l => probeShell_nonneg _ _ _ _ _ _)
    (fun l => probeShell_le_bound w P (by omega) hEll B A)

theorem probeMax_le_energy_cap {K Q : TriadicCube d} {u : ℝ} (hu : 0 < u)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) (hQ : Q ∈ descendantsAtScale K Q.scale) :
    probeMax (openCubeSet Q) g B A ≤
      (3 : ℝ) ^ (2 * u * (((K.scale - Q.scale).toNat : ℕ) : ℝ)) *
        probeEnergy 0 K u g B A := by
  have hQK := scale_le_of_mem_descendantsAtScale hQ
  let j : ℕ := (K.scale - Q.scale).toNat
  have hj : K.scale - (j : ℤ) = Q.scale := by dsimp [j]; omega
  have hsum := probeEnergy_summable 0 K hu hEll B A
  simp only [Ch02.geometricWeight_eq_old] at hsum
  have hcap := shell_le_rpow_mul_tsum (s := u) (q := 2) (by positivity)
    (fun l => probeShell_nonneg 0 K _ g B A) (probeShell_monotone K hEll B A) hsum j
  have hcell := probeMax_le_gridShell hEll B A hQ (le_refl Q.scale)
  rw [hj] at hcap
  refine hcell.trans (hcap.trans_eq ?_)
  simp only [probeEnergy, Ch02.geometricWeight_eq_old]
  congr 2
  dsimp [j]
  ring

theorem probeMax_offGrid_le_cap {w : Vec d} {R K : TriadicCube d} {u : ℝ}
    (hu0 : 0 < u) (hu : u < 1 / 2)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    probeMax (offGridCube w R) g B A ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          probeEnergy 0 K u g B A) := by
  classical
  set c : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) * probeEnergy 0 K u g B A with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (probeEnergy_nonneg 0 K hu0 g B A)
  let cap : TriadicCube d → ℝ := fun Q =>
    c * (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ))
  have hcap : ∀ Q : maximalCubes (offGridCube w R),
      probeMax (openCubeSet (Q : TriadicCube d)) g B A ≤ cap Q := by
    intro Q
    have hQR : (Q : TriadicCube d).scale ≤ R.scale :=
      scale_le_of_maximalCubeIn_offGridCube Q.2
    have hQK := hQR.trans hRK
    have hdesc := mem_descendantsAtScale_of_cubeSet_subset (Q.2.1.trans hKsub) hQK
    have hraw := probeMax_le_energy_cap hu0 hEll B A hdesc
    have hdepth : (K.scale - (Q : TriadicCube d).scale).toNat =
        (K.scale - R.scale).toNat + (R.scale - (Q : TriadicCube d).scale).toNat := by omega
    refine hraw.trans_eq ?_
    dsimp [cap]
    rw [hc, hdepth]
    push_cast
    rw [show 2 * u * ((((K.scale - R.scale).toNat : ℕ) : ℝ) +
        (((R.scale - (Q : TriadicCube d).scale).toNat : ℕ) : ℝ)) =
        2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ) +
        2 * u * (((R.scale - (Q : TriadicCube d).scale).toNat : ℕ) : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring
  obtain ⟨hcapSum, hcapLe⟩ := summable_and_tsum_maximalCubes_cap_le w R hu0 hu hc0
  apply csSup_le (probeSet_nonempty _ _ _ _)
  rintro y ⟨e, he, rfl⟩
  have hcover := responseJ_offGridCube_le_tsum_maximalCubes
    (hEll.mono (isOpen_offGridCube w R).measurableSet (Set.subset_univ _)) cap
    (fun Q => (probeResponse_le_max (Ch02.cubeDomain (Q : TriadicCube d))
      (hEll.mono (Ch02.cubeDomain (Q : TriadicCube d)).measurableSet (Set.subset_univ _))
        B A e he).trans (hcap Q))
    hcapSum
  refine hcover.trans ((mul_le_mul_of_nonneg_left hcapLe
    (inv_nonneg.mpr (cubeVolume_pos R).le)).trans_eq ?_)
  have hv := (cubeVolume_pos R).ne'
  have hden : 1 - 2 * u ≠ 0 := (by linarith only [hu] : 0 < 1 - 2 * u).ne'
  field_simp

theorem probeShell_le_cap {w : Vec d} {P K : TriadicCube d} {u : ℝ}
    (hu0 : 0 < u) (hu : u < 1 / 2)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K)
    (hPK : P.scale ≤ K.scale) (l : ℕ) :
    probeShell w P (P.scale - (l : ℤ)) g B A ≤
      (12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          probeEnergy 0 K u g B A)) * (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
  apply Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty P (by omega))
  intro R hR
  have hscale := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hRP := cubeSet_subset_of_mem_descendantsAtScale (by omega : P.scale - (l : ℤ) ≤ P.scale) hR
  have hsub : offGridCube w R ⊆ cubeSet K := by
    intro z hz
    apply hcontain
    exact mem_translateSet_iff_sub_mem.2 (hRP (openCubeSet_subset_cubeSet R
      (mem_translateSet_iff_sub_mem.1 hz)))
  have hraw := probeMax_offGrid_le_cap hu0 hu hEll B A hsub (by omega : R.scale ≤ K.scale)
  have hdepth : (K.scale - R.scale).toNat = (K.scale - P.scale).toNat + l := by omega
  refine hraw.trans_eq ?_
  rw [hdepth]
  push_cast
  rw [show 2 * u * ((((K.scale - P.scale).toNat : ℕ) : ℝ) + (l : ℝ)) =
    2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ) + 2 * u * (l : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring

theorem probeError_le {w : Vec d} {P K : TriadicCube d} {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (ht : t ≤ 1 / 2)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K)
    (hPK : P.scale ≤ K.scale) :
    probeError w P t g B A ≤
      Real.sqrt (12 * (d : ℝ) / (1 - 2 * s) * (t / (t - s))) *
        ((3 : ℝ) ^ (s * (((K.scale - P.scale).toNat : ℕ) : ℝ)) * probeError 0 K s g B A) := by
  have hslt : s < 1 / 2 := hst.trans_le ht
  have hden : 0 < 1 - 2 * s := by linarith
  set E := probeError 0 K s g B A with hE
  set Y := (3 : ℝ) ^ (s * (((K.scale - P.scale).toNat : ℕ) : ℝ)) with hY
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
  have hEsq : E ^ 2 = probeEnergy 0 K s g B A :=
    Real.sq_sqrt (probeEnergy_nonneg 0 K hs g B A)
  have hYsq : Y ^ 2 = (3 : ℝ) ^ (2 * s * (((K.scale - P.scale).toNat : ℕ) : ℝ)) := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    congr 1
    ring
  let cap := 12 * (d : ℝ) / (1 - 2 * s) * (Y ^ 2 * E ^ 2)
  have hcap0 : 0 ≤ cap := by dsimp [cap]; positivity
  have hseries := finite_norm_le_of_shell_cap (q := 2) hs hst (by norm_num) hcap0
    (fun l => probeShell w P (P.scale - (l : ℤ)) g B A)
    (fun l => probeShell_nonneg _ _ _ _ _ _)
    (fun l => by dsimp [cap]; rw [hYsq, hEsq]; exact probeShell_le_cap hs hslt hEll B A hcontain hPK l)
  norm_num only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] at hseries
  have hconst : t / (t - s) * cap =
      (12 * (d : ℝ) / (1 - 2 * s) * (t / (t - s))) * (Y * E) ^ 2 := by
    dsimp [cap]
    ring
  have hC0 : 0 ≤ 12 * (d : ℝ) / (1 - 2 * s) * (t / (t - s)) := by
    have ht0 := hs.trans hst
    have hdiff := sub_pos.mpr hst
    positivity
  unfold probeError
  refine (Real.sqrt_le_sqrt (hseries.trans_eq hconst)).trans_eq ?_
  rw [Real.sqrt_mul hC0, Real.sqrt_sq (mul_nonneg hY0 hE0)]

end SubdiffusiveProcess.LambdaStability
