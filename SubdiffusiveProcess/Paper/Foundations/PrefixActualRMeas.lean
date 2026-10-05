module

public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMeas

@[expose] public section

noncomputable section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

private theorem countable_triagonal_centers {d : ℕ} (n : ℕ) (z : Vec d) :
    Set.Countable {x : Vec d | OnTriadicGrid n (x - z)} := by
  let f : (Fin d → ℤ) → Vec d := fun k i => z i + (3 : ℝ) ^ n * (k i : ℝ)
  apply (Set.countable_range f).mono
  intro x hx
  have hx' : ∀ i : Fin d, ∃ k : ℤ,
      (x - z) i = (3 : ℝ) ^ n * k := hx
  let k : Fin d → ℤ := fun i => Classical.choose (hx' i)
  refine ⟨k, ?_⟩
  funext i
  have hi : x i - z i = (3 : ℝ) ^ n * (k i : ℝ) := by
    simpa only [Pi.sub_apply] using (Classical.choose_spec (hx' i))
  dsimp [f]
  linarith

private theorem countable_response_centers {d : ℕ} (n j : ℕ) (z : Vec d) :
    Set.Countable {x : Vec d | OnTriadicGrid n (x - z) ∧
      x - z ∈ cube d j \ cube d (j - 1)} := by
  exact (countable_triagonal_centers n z).mono (fun x hx => hx.1)

private def Jterm {d : ℕ} (M : GMCModel d) (n : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ENNReal :=
  sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
    u = ENNReal.ofReal (section6Response M n n omega x e)}

theorem aux_lem_prefix_limit_actual_Rsc_meas {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
          sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M n n omega x e)}}) := by
  let I : Type := {jn : ℕ × ℕ // jn.1 ≤ m ∧ jn.2 + 2 ≤ jn.1}
  let X : I → Type := fun a => {x : Vec d // OnTriadicGrid a.1.2 (x - z) ∧
    x - z ∈ cube d a.1.1 \ cube d (a.1.1 - 1)}
  have hX (a : I) : Countable (X a) := by
    exact (countable_response_centers a.1.2 a.1.1 z).to_subtype
  let F : (a : I) → X a → PotentialSample d → ENNReal := by
    exact fun a x omega =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (a.1.2 : ℝ)) / 8))) *
        Jterm M a.1.2 omega x.1
  have hm (a : I) (x : X a) : Measurable (F a x) := by
    exact (aux_lem_prefix_limit_actual_J_meas M a.1.2 x.1).const_mul _
  have hsup : Measurable (fun omega : PotentialSample d =>
      ⨆ a : I, ⨆ x : X a, F a x omega) := by
    exact Measurable.iSup (fun a => Measurable.iSup (fun x => hm a x))
  convert hsup using 1
  funext omega
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨j, n, hj, hn, x, hxgrid, hxann, rfl⟩
    let a : I := ⟨(j, n), hj, hn⟩
    let y : X a := ⟨x, hxgrid, hxann⟩
    exact le_iSup_of_le a (le_iSup_of_le y (le_refl _))
  · refine iSup_le fun a => iSup_le fun x => ?_
    exact le_sSup ⟨a.1.1, a.1.2, a.2.1, a.2.2,
      x.1, x.2.1, x.2.2, rfl⟩

theorem aux_lem_prefix_limit_actual_Dsc_first_meas {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)}) := by
  let I : Type := {jl : ℕ × ℕ // jl.1 ≤ k ∧ jl.2 ≤ k ∧ jl.2 + 2 ≤ jl.1}
  let X : I → Type := fun a => {x : Vec d | OnTriadicGrid a.1.2 (x - z) ∧
    x - z ∈ cube d a.1.1 \ cube d (a.1.1 - 1)}
  have hX (a : I) : Countable (X a) := by
    exact ((countable_triagonal_centers a.1.2 z).mono (fun x hx => hx.1)).to_subtype
  let F : (a : I) → X a → PotentialSample d → ENNReal :=
    fun a x omega =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (a.1.2 : ℝ)))) *
        (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
          u = ENNReal.ofReal (section6Response M a.1.2 a.1.2 omega x.1 e)}) 1) ^
          (1 / 2 : ℝ)
  have hm (a : I) (x : X a) : Measurable (F a x) := by
    have hJ := aux_lem_prefix_limit_actual_J_meas M a.1.2 x.1
    have hmin : Measurable (fun omega : PotentialSample d =>
        min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
          u = ENNReal.ofReal (section6Response M a.1.2 a.1.2 omega x.1 e)}) 1) :=
      hJ.min measurable_const
    exact ((ENNReal.continuous_rpow_const.measurable.comp hmin).const_mul _)
  have hsup : Measurable (fun omega : PotentialSample d =>
      ⨆ a : I, ⨆ x : X a, F a x omega) := by
    exact Measurable.iSup (fun a => Measurable.iSup (fun x => hm a x))
  convert hsup using 1
  funext omega
  apply le_antisymm
  · apply sSup_le
    rintro v ⟨j, l, hj, hl, hlj, x, hxgrid, hxann, rfl⟩
    let a : I := ⟨(j, l), hj, hl, hlj⟩
    let y : X a := ⟨x, hxgrid, hxann⟩
    exact le_iSup_of_le a (le_iSup_of_le y (le_refl _))
  · refine iSup_le fun a => iSup_le fun x => ?_
    exact le_sSup ⟨a.1.1, a.1.2, a.2.1, a.2.2.1, a.2.2.2,
      x.1, x.2.1, x.2.2, rfl⟩

theorem aux_lem_prefix_limit_actual_Rraw_aemeas {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω]
    (M : GMCModel d) (s eps : ℝ) (μ : Measure Ω)
    (eta : ℕ → Ω → PotentialSample d)
    (hEtaMeas : ∀ N, AEMeasurable (eta N) μ)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → Ω → ENNReal)
    (Z : ℕ → ℕ → Vec d → Ω → ℝ)
    (rawGood : ℕ → ℕ → Vec d → Ω → Prop)
    (hPrimitive : ∀ᵐ omega ∂μ, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N m : ℕ) (z : Vec d) :
    AEMeasurable (fun omega => (Rraw N m z omega).toReal) μ := by
  have hcanonical : AEMeasurable
      (fun omega => (sSup {v : ENNReal | ∃ j n : ℕ,
        j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
          sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M n n (eta N omega) x e)}}).toReal) μ := by
    exact (ENNReal.measurable_toReal.comp
      (aux_lem_prefix_limit_actual_Rsc_meas M s m z)).comp_aemeasurable
        (hEtaMeas N)
  apply hcanonical.congr
  filter_upwards [hPrimitive] with omega hps
  obtain ⟨_, _, _, _, _, _, hR, _⟩ := hps N
  exact congrArg ENNReal.toReal (hR m z).symm

end SubdiffusiveProcess.Paper
