/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

import RLTheory.Defs
import RLTheory.MeasureTheory.MeasurableSpace.Constructions
import RLTheory.Probability.MarkovChain.Defs
import RLTheory.MeasureTheory.Function.L1Space.Integrable

open RLTheory
open MeasureTheory MeasureTheory.Measure Filtration
open ProbabilityTheory.Kernel
open ProbabilityTheory
open Finset Bornology
open NNReal ENNReal Preorder Filter


namespace ProbabilityTheory

namespace MarkovChain

universe u
variable {S : Type u} [MeasurableSpace S]

/-- The (constant) state-type family for trajectories. Marked `@[reducible]`
so `X S i` unfolds to `S` under `instances` transparency: the Ionescu–Tulcea
`traj` machinery states its kernel domains as `Π i : Iic n, X S i`, and instance
synthesis must see these as defeq to `Iic n → S` to fire the `expand_kernel`
Markov instances. -/
@[reducible] def X (S : Type u) : ℕ → Type u := fun _ => S

instance : ∀ n, MeasurableSpace (X (S := S) n) := by
  intro n; unfold X; infer_instance

noncomputable def kernel_comap_trivial
  (κ : Kernel S S) (n : ℕ):
  Kernel (Iic n → S) S := by
  let g : (Iic n → S) → S :=
    fun history => history ⟨n, by simp [mem_Iic]⟩
  have hg : Measurable g := by apply measurable_pi_apply
  exact κ.comap g hg

noncomputable def expand_kernel
  (M : HomMarkovChainSpec S) (n : ℕ) :
  Kernel (Iic n → S) S :=
  M.kernel.comap (fun history : Iic n → S => history ⟨n, mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance instExpandKernelIsMarkov (M : HomMarkovChainSpec S) (n : ℕ) :
  IsMarkovKernel (expand_kernel M n) := by
  haveI := M.markov_kernel
  unfold expand_kernel
  exact IsMarkovKernel.comap M.kernel (measurable_pi_apply _)

noncomputable def traj_prob₀
  (M : HomMarkovChainSpec S) (x₀ : Iic 0 → S)
  : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := X S) (expand_kernel M) 0
  exact ⟨κ x₀, inferInstance⟩

noncomputable def traj_prob
  (M : HomMarkovChainSpec S) : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := X S) (expand_kernel M) 0
  let f : S → (Iic 0 → S) := fun s => (fun _ : Iic 0 => s)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro x
    unfold f
    apply measurable_id
  let init := M.init.map hf.aemeasurable
  haveI : IsProbabilityMeasure (init : Measure (Iic 0 → S)) := init.2
  let prob := init.1.bind κ
  refine ⟨prob, ?_⟩
  show IsProbabilityMeasure (κ ∘ₘ (init : Measure (Iic 0 → S)))
  infer_instance

end MarkovChain

end ProbabilityTheory
