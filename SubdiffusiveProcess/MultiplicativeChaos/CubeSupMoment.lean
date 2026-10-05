module

public import SubdiffusiveProcess.MultiplicativeChaos.DoobLp
public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

/-!
# The supremum over the cutoffs of a nonnegative martingale

`mfd:prop-chaos-growth` needs the growth bound to hold for EVERY cutoff with
ONE random constant, so the cube masses have to be controlled by their
supremum over the cutoff.  This file turns a uniform `L^p` bound on a
nonnegative martingale into an `L^p` bound on that supremum, by combining
Mathlib's weak maximal inequality with `doob_lp_maximal` on the finite maxima
and passing to the limit by monotone convergence.

The supremum is taken of the `p`-th powers, `⨆ N, ofReal (f N ^ p)`, rather
than the `p`-th power of the supremum: the two agree, and this form avoids
having to commute `(⨆ ·) ^ p` with the supremum.
-/

open MeasureTheory Filter

open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- A nonnegative martingale whose `p`-th moments are bounded by `B` uniformly
in the cutoff has `∫⁻ ⨆ N, f N ^ p ≤ 2 ^ p * p/(p-1) * B`. -/
theorem lintegral_iSup_pow_le_of_martingale
    {Omega : Type*} {m0 : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] {F : Filtration ℕ m0} {f : ℕ → Omega → ℝ}
    (hmart : Martingale f F mu) (hnn : ∀ N omega, 0 ≤ f N omega)
    (p : ℕ) (hp : 2 ≤ p) (B : ℝ)
    (hint : ∀ N, Integrable (fun omega => f N omega ^ p) mu)
    (hmom : ∀ N, ∫ omega, f N omega ^ p ∂mu ≤ B) :
    ∫⁻ omega, ⨆ N, ENNReal.ofReal (f N omega ^ p) ∂mu ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * ((p : ℝ) / ((p : ℝ) - 1))) *
        ENNReal.ofReal B := by
  classical
  have hsub : Submartingale f F mu := hmart.submartingale
  have hf0 : (0 : ℕ → Omega → ℝ) ≤ f := fun N omega => hnn N omega
  have hfmble : ∀ N, Measurable (f N) := fun N =>
    ((hmart.stronglyAdapted N).mono (F.le N)).measurable
  set S : ℕ → Omega → ℝ := fun n omega =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => f k omega)
    with hSdef
  have hSmble : ∀ n, Measurable (S n) := by
    intro n
    have h := Finset.measurable_sup' (s := Finset.range (n + 1))
      Finset.nonempty_range_add_one (f := f) (fun k _ => hfmble k)
    have hfun : S n = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one f := by
      funext omega
      simp [hSdef, Finset.sup'_apply]
    rw [hfun]
    exact h
  have hfle : ∀ n omega, f n omega ≤ S n omega := by
    intro n omega
    exact Finset.le_sup' (fun k => f k omega) (Finset.self_mem_range_succ n)
  have hSnn : ∀ n omega, 0 ≤ S n omega := by
    intro n omega
    refine le_trans (hnn 0 omega) ?_
    exact Finset.le_sup' (fun k => f k omega)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  -- Doob at each finite horizon.
  have hstep : ∀ n, ∫⁻ omega, ENNReal.ofReal (S n omega ^ p) ∂mu
      ≤ ENNReal.ofReal ((2 : ℝ) ^ p * ((p : ℝ) / ((p : ℝ) - 1))) *
        ENNReal.ofReal B := by
    intro n
    have hweak : ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t * mu {omega | t ≤ S n omega} ≤
          ∫⁻ omega in {omega | t ≤ S n omega},
            ENNReal.ofReal (f n omega) ∂mu := by
      intro t ht
      have hmax := MeasureTheory.maximal_ineq hsub hf0 (ε := t.toNNReal) n
      have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
      rw [hcoe] at hmax
      have hbridge : ENNReal.ofReal
            (∫ omega in {omega | t ≤ S n omega}, f n omega ∂mu)
          = ∫⁻ omega in {omega | t ≤ S n omega},
              ENNReal.ofReal (f n omega) ∂mu :=
        ofReal_integral_eq_lintegral_ofReal
          ((hsub.integrable n).restrict)
          (Filter.Eventually.of_forall (fun omega => hnn n omega))
      rw [hbridge] at hmax
      refine le_trans (le_of_eq ?_) hmax
      simp only [hSdef, ENNReal.ofReal]
    have hdoob := doob_lp_maximal (S n) (f n) p hp (hSmble n) (hSnn n)
      (hfmble n) (hnn n) hweak
    refine le_trans hdoob ?_
    refine mul_le_mul_right ?_ _
    have heq : ∫⁻ omega, ENNReal.ofReal (f n omega ^ p) ∂mu
        = ENNReal.ofReal (∫ omega, f n omega ^ p ∂mu) :=
      (ofReal_integral_eq_lintegral_ofReal (hint n)
        (Filter.Eventually.of_forall
          (fun omega => pow_nonneg (hnn n omega) p))).symm
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (hmom n)
  -- The two suprema agree pointwise.
  have hsup : ∀ omega, (⨆ N, ENNReal.ofReal (f N omega ^ p))
      = ⨆ n, ENNReal.ofReal (S n omega ^ p) := by
    intro omega
    refine le_antisymm (iSup_le fun N => le_iSup_of_le N ?_)
      (iSup_le fun n => ?_)
    · refine ENNReal.ofReal_le_ofReal ?_
      have h0 : 0 ≤ f N omega := hnn N omega
      have h1 : f N omega ≤ S N omega := hfle N omega
      gcongr
    · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup'
        (Finset.nonempty_range_add_one (n := n)) (fun k => f k omega)
      have hval : S n omega = f k omega := hkeq
      rw [hval]
      exact le_iSup (fun N => ENNReal.ofReal (f N omega ^ p)) k
  -- Monotone convergence.
  have hmono : Monotone fun n omega => ENNReal.ofReal (S n omega ^ p) := by
    intro n m hnm omega
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ S n omega := hSnn n omega
    have h1 : S n omega ≤ S m omega := by
      refine Finset.sup'_mono (fun k => f k omega) ?_ Finset.nonempty_range_add_one
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    gcongr
  calc ∫⁻ omega, ⨆ N, ENNReal.ofReal (f N omega ^ p) ∂mu
      = ∫⁻ omega, ⨆ n, ENNReal.ofReal (S n omega ^ p) ∂mu := by
        simp_rw [hsup]
    _ = ⨆ n, ∫⁻ omega, ENNReal.ofReal (S n omega ^ p) ∂mu :=
        lintegral_iSup (fun n => ((hSmble n).pow_const p).ennreal_ofReal) hmono
    _ ≤ _ := iSup_le hstep

end SubdiffusiveProcess
