import SubdiffusiveProcess.Paper.annealed_limit_identity
import SubdiffusiveProcess.Paper.stationary_defects
import SubdiffusiveProcess.Paper.stationary_family
import SubdiffusiveProcess.Paper.in_moments
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.lem_fmono_annealed_subadditivity
import SubdiffusiveProcess.Paper.lem_fmono_uniform_bound
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Homogenization.Book.Ch02.Matrices
import Mathlib.Tactic

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_fmono (d : ℕ) (hd : 2 ≤ d) (hJ : Paper.in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
          ∀ (family : ℕ → BilateralField d → TriadicCoeffFamily d),
            (∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
              ∀ᵐ x ∂volume.restrict (openCubeSet Q),
                ((family N ω).coeffOn Q).toCoeffField x =
                  scalarMatrix
                    (cutoffCoefficient model
                      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)) →
              let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
              let Pmat : ℕ → ℕ → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ :=
                fun N k ω =>
                  Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
                    ((family N ω).coeffOn (Qk k))
              let Rmat : ℕ → ℕ → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ :=
                fun N k ω =>
                  Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
                    ((family N ω).coeffOn (Qk k))
              let EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
                fun N k i j =>
                  ∫ ω, Pmat N k ω i j ∂(chaosSampleLaw model).toMeasure
              let ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
                fun N k i j =>
                  ∫ ω, Rmat N k ω i j ∂(chaosSampleLaw model).toMeasure
              let f : ℕ → ℕ → ℝ :=
                fun N k =>
                  Matrix.trace
                      (EP N k + ER N k -
                        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2
              (∀ (N k : ℕ) (pvec : Fin d → ℝ),
                  pvec ⬝ᵥ pvec ≤ pvec ⬝ᵥ (EP N k).mulVec pvec) ∧
                (∀ (N k : ℕ) (pvec : Fin d → ℝ),
                  pvec ⬝ᵥ pvec ≤ pvec ⬝ᵥ (ER N k).mulVec pvec) ∧
                (∀ (N k : ℕ), 0 ≤ f N k) ∧
                (∀ (N k : ℕ), f N (k + 1) ≤ f N k) ∧
                (∃ Fk : ℕ → ℝ, ∃ eta : ℝ,
                  (∀ k, IsLUB (range (fun N => f N k)) (Fk k)) ∧
                    0 ≤ eta ∧ Antitone Fk ∧
                    Filter.Tendsto Fk Filter.atTop (nhds eta)) := by
  obtain ⟨delta0, hdelta0, C, hC, Hunif⟩ :=
    lem_fmono_uniform_bound d hd hJ
  refine ⟨delta0, hdelta0, ?_⟩
  intro instM instB model hmodel family hfamily
  let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
  let Pmat : ℕ → ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ :=
    fun N k ω => Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
      ((family N ω).coeffOn (Qk k))
  let Rmat : ℕ → ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ :=
    fun N k ω => Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
      ((family N ω).coeffOn (Qk k))
  let EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
    fun N k i j => ∫ ω, Pmat N k ω i j ∂(chaosSampleLaw model).toMeasure
  let ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
    fun N k i j => ∫ ω, Rmat N k ω i j ∂(chaosSampleLaw model).toMeasure
  let f : ℕ → ℕ → ℝ :=
    fun N k => Matrix.trace (EP N k + ER N k - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2
  have hsub := lem_fmono_annealed_subadditivity d hd model family hfamily
  have hbound : ∀ (N k : ℕ), f N k ≤ C * model.delta ^ 2 :=
    fun N k => Hunif model hmodel family hfamily N k
  have hEP_mono : ∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ (EP N (k + 1)).mulVec pvec ≤ pvec ⬝ᵥ (EP N k).mulVec pvec :=
    fun N k pvec => hsub.2.1 N k pvec
  have hER_mono : ∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ (ER N (k + 1)).mulVec pvec ≤ pvec ⬝ᵥ (ER N k).mulVec pvec :=
    fun N k pvec => hsub.2.2.1 N k pvec
  have hlim_both : ∀ (N : ℕ) (i j : Fin d),
      Filter.Tendsto (fun k => EP N k i j) Filter.atTop
          (nhds ((1 : Matrix (Fin d) (Fin d) ℝ) i j)) ∧
        Filter.Tendsto (fun k => ER N k i j) Filter.atTop
          (nhds ((1 : Matrix (Fin d) (Fin d) ℝ) i j)) :=
    fun N i j => hsub.2.2.2 N i j
  have hquad : ∀ (E : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ),
      (∀ (N k : ℕ) (pvec : Fin d → ℝ),
        pvec ⬝ᵥ (E N (k + 1)).mulVec pvec ≤ pvec ⬝ᵥ (E N k).mulVec pvec) →
      (∀ (N : ℕ) (i j : Fin d),
        Filter.Tendsto (fun k => E N k i j) Filter.atTop
          (nhds ((1 : Matrix (Fin d) (Fin d) ℝ) i j))) →
      ∀ (N k : ℕ) (pvec : Fin d → ℝ),
        pvec ⬝ᵥ pvec ≤ pvec ⬝ᵥ (E N k).mulVec pvec := by
    intro E hmono hlim N k pvec
    have hanti : Antitone (fun m => pvec ⬝ᵥ (E N m).mulVec pvec) :=
      antitone_nat_of_succ_le (fun m => hmono N m pvec)
    have hsum : Filter.Tendsto (fun m => ∑ i, ∑ j, pvec i * pvec j * E N m i j)
        Filter.atTop
        (nhds (∑ i, ∑ j, pvec i * pvec j * (1 : Matrix (Fin d) (Fin d) ℝ) i j)) := by
      apply tendsto_finset_sum
      intro i _
      apply tendsto_finset_sum
      intro j _
      exact (hlim N i j).const_mul (pvec i * pvec j)
    have hquadlim : Filter.Tendsto (fun m => pvec ⬝ᵥ (E N m).mulVec pvec)
        Filter.atTop (nhds (pvec ⬝ᵥ pvec)) := by
      have h1 : ∀ m, pvec ⬝ᵥ (E N m).mulVec pvec
          = ∑ i, ∑ j, pvec i * pvec j * E N m i j := by
        intro m
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      have h2 : pvec ⬝ᵥ pvec
          = ∑ i, ∑ j, pvec i * pvec j * (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
        simp only [dotProduct, Matrix.one_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      simpa only [h1, h2] using hsum
    exact le_of_tendsto hquadlim
      (Filter.eventually_atTop.mpr ⟨k, fun m hm => hanti hm⟩)
  have hEP_loewner : ∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ pvec ≤ pvec ⬝ᵥ (EP N k).mulVec pvec :=
    hquad EP hEP_mono (fun N i j => (hlim_both N i j).1)
  have hER_loewner : ∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ pvec ≤ pvec ⬝ᵥ (ER N k).mulVec pvec :=
    hquad ER hER_mono (fun N i j => (hlim_both N i j).2)
  have hsingle : ∀ i : Fin d,
      (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (Pi.single i (1 : ℝ)) = 1 := by
    intro i
    rw [dotProduct_single, Pi.single_eq_same, one_mul]
  have dot_single : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d),
      (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (M.mulVec (Pi.single i (1 : ℝ))) = M i i := by
    intro M i
    rw [Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.col, Matrix.transpose_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hEP_diag : ∀ (N k : ℕ) (i : Fin d), (1 : ℝ) ≤ (EP N k) i i := by
    intro N k i
    have h := hEP_loewner N k (Pi.single i (1 : ℝ))
    rwa [hsingle i, dot_single (EP N k) i] at h
  have hER_diag : ∀ (N k : ℕ) (i : Fin d), (1 : ℝ) ≤ (ER N k) i i := by
    intro N k i
    have h := hER_loewner N k (Pi.single i (1 : ℝ))
    rwa [hsingle i, dot_single (ER N k) i] at h
  have trace_eq : ∀ M : Matrix (Fin d) (Fin d) ℝ, Matrix.trace M = ∑ i, M i i := by
    intro M
    simp only [Matrix.trace]
    rfl
  have hsum_one : (∑ _i : Fin d, (1 : ℝ)) = (d : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h2ii : ∀ i : Fin d, (2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i = 2 := by
    intro i
    rw [Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num
  have hpw : ∀ (M M' : Matrix (Fin d) (Fin d) ℝ) (i : Fin d),
      (M + M' - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i = M i i + M' i i - 2 := by
    intro M M' i
    simp only [Matrix.sub_apply, Matrix.add_apply, h2ii i]
  have hdec : ∀ (M M' : Matrix (Fin d) (Fin d) ℝ),
      Matrix.trace (M + M' - 2 • (1 : Matrix (Fin d) (Fin d) ℝ))
        = Matrix.trace M + Matrix.trace M' - 2 * (d : ℝ) := by
    intro M M'
    rw [trace_eq, trace_eq, trace_eq]
    calc ∑ i, (M + M' - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i
        = ∑ i, (M i i + M' i i - 2) := Finset.sum_congr rfl (fun i _ => hpw M M' i)
      _ = (∑ i, M i i) + (∑ i, M' i i) - 2 * (d : ℝ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have htrace_nonneg : ∀ (N k : ℕ), 0 ≤ f N k := by
    intro N k
    have hEPd : (d : ℝ) ≤ Matrix.trace (EP N k) := by
      rw [trace_eq, ← hsum_one]
      exact Finset.sum_le_sum (fun i _ => hEP_diag N k i)
    have hERd : (d : ℝ) ≤ Matrix.trace (ER N k) := by
      rw [trace_eq, ← hsum_one]
      exact Finset.sum_le_sum (fun i _ => hER_diag N k i)
    dsimp only [f]
    rw [hdec]
    linarith
  have hEP_diag_mono : ∀ (N k : ℕ) (i : Fin d), (EP N (k + 1)) i i ≤ (EP N k) i i := by
    intro N k i
    have h := hEP_mono N k (Pi.single i (1 : ℝ))
    rwa [dot_single (EP N (k + 1)) i, dot_single (EP N k) i] at h
  have hER_diag_mono : ∀ (N k : ℕ) (i : Fin d), (ER N (k + 1)) i i ≤ (ER N k) i i := by
    intro N k i
    have h := hER_mono N k (Pi.single i (1 : ℝ))
    rwa [dot_single (ER N (k + 1)) i, dot_single (ER N k) i] at h
  have hf_mono : ∀ (N k : ℕ), f N (k + 1) ≤ f N k := by
    intro N k
    have hEPt : Matrix.trace (EP N (k + 1)) ≤ Matrix.trace (EP N k) := by
      rw [trace_eq, trace_eq]
      exact Finset.sum_le_sum (fun i _ => hEP_diag_mono N k i)
    have hERt : Matrix.trace (ER N (k + 1)) ≤ Matrix.trace (ER N k) := by
      rw [trace_eq, trace_eq]
      exact Finset.sum_le_sum (fun i _ => hER_diag_mono N k i)
    dsimp only [f]
    rw [hdec, hdec]
    linarith
  refine ⟨hEP_loewner, hER_loewner, htrace_nonneg, hf_mono, ?_⟩
  let Fk : ℕ → ℝ := fun k => sSup (range (fun N => f N k))
  have hFk_eq : ∀ k, Fk k = sSup (range (fun N => f N k)) := fun k => rfl
  have hFk_bdd : ∀ k, BddAbove (range (fun N => f N k)) := fun k =>
    ⟨C * model.delta ^ 2, fun x hx => by
      rcases hx with ⟨N, rfl⟩
      exact hbound N k⟩
  have hFk_ne : ∀ k, (range (fun N => f N k)).Nonempty := fun k => ⟨f 0 k, ⟨0, rfl⟩⟩
  have hFk_lub : ∀ k, IsLUB (range (fun N => f N k)) (Fk k) :=
    fun k => isLUB_csSup (hFk_ne k) (hFk_bdd k)
  have hFk_nonneg : ∀ k, 0 ≤ Fk k := by
    intro k
    exact le_trans (htrace_nonneg 0 k) (le_csSup (hFk_bdd k) ⟨0, rfl⟩)
  have hFk_anti : Antitone Fk := by
    apply antitone_nat_of_succ_le
    intro k
    rw [hFk_eq (k + 1), hFk_eq k]
    apply csSup_le (hFk_ne (k + 1))
    intro a ha
    rcases ha with ⟨N, rfl⟩
    exact le_trans (hf_mono N k) (le_csSup (hFk_bdd k) ⟨N, rfl⟩)
  have hFk_bddBelow : BddBelow (range Fk) :=
    ⟨0, fun x hx => by rcases hx with ⟨k, rfl⟩; exact hFk_nonneg k⟩
  refine ⟨Fk, ⨅ k, Fk k, hFk_lub, ?_, hFk_anti, ?_⟩
  · exact le_ciInf (fun k => hFk_nonneg k)
  · exact tendsto_atTop_ciInf hFk_anti hFk_bddBelow


end Paper
