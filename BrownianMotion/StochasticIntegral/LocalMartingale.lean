/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Martingale.Basic

/-! # Local (sub)martingales

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A stochastic process is a local martingale if it satisfies the martingale property locally. -/
def IsLocalMartingale (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) :
    Prop :=
  Locally (fun X ↦ rightContinuous X ∧ Martingale X 𝓕 P) 𝓕 X P

/-- A stochastic process is a local submartingale if it satisfies the submartingale property
locally. -/
def IsLocalSubmartingale [LE E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (Submartingale · 𝓕 P) 𝓕 X P

lemma Martingale.IsLocalMartingale (hRC : rightContinuous X) (hX : Martingale X 𝓕 P) :
    IsLocalMartingale X 𝓕 P :=
  locally_of_prop ⟨hRC, hX⟩

lemma Submartingale.IsLocalSubmartingale [LE E] (hX : Submartingale X 𝓕 P) :
    IsLocalSubmartingale X 𝓕 P :=
  locally_of_prop hX

omit [TopologicalSpace ι] [OrderTopology ι] in
lemma Martingale.of_indicator_stoppingTime_pos {τ : Ω → WithTop ι}
    (hX : Martingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) 𝓕 P :=
  ⟨fun i ↦ (hX.1 i).indicator <| 𝓕.mono bot_le _ (IsStoppingTime.measurableSet_gt hτ ⊥),
   fun i j hij ↦ (condExp_indicator (hX.integrable j) <| 𝓕.mono bot_le _
    (IsStoppingTime.measurableSet_gt hτ ⊥)).trans <| (ae_eq_restrict_iff_indicator_ae_eq <|
    𝓕.le _ _  (IsStoppingTime.measurableSet_gt hτ ⊥)).1 (hX.2 i j hij).restrict⟩

class HasDiscreteApproxSequence (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) where
    exists_discreteApproxSequence {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
      Nonempty (DiscreteApproxSequence 𝓕 P τ)

noncomputable
def IsStoppingTime.discreteApproxSequence
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) (P : Measure Ω) [HasDiscreteApproxSequence 𝓕 P] :
    DiscreteApproxSequence 𝓕 P τ :=
  (HasDiscreteApproxSequence.exists_discreteApproxSequence hτ).some

variable [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι]
  [MetrizableSpace ι] [IsFiniteMeasure P]

-- TODO: generalize to Banach space
#check stoppedValue_ae_eq_condExp_of_le_const_of_discreteApproxSequence
lemma Martingale.of_stoppedProcess [HasDiscreteApproxSequence 𝓕 P]
    {τ : Ω → WithTop ι} {X : ι → Ω → ℝ}
    (hRC : rightContinuous X) (hX : Martingale X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess X τ) 𝓕 P := by
  refine ⟨?_, fun i j hij ↦ ?_⟩
  · sorry
  · rw [stoppedProcess_eq_stoppedValue]
    simp only
    have := stoppedValue_ae_eq_condExp_of_le_const_of_discreteApproxSequence
      (𝓕 := 𝓕) (n := j) hX hRC ((isStoppingTime_const 𝓕 j).min hτ) (by simp)
      (IsStoppingTime.discreteApproxSequence ((isStoppingTime_const 𝓕 j).min hτ) P)
    refine (condExp_congr_ae this).trans ?_
    sorry
    -- refine (condExp_condExp_of_le ?_ _).trans ?_
    -- · sorry
    -- ·
    -- refine IsStoppingTime.measurableSpace_mono

/-- Right continuous martingales are a stable class. -/
lemma isStable_martingale :
    IsStable 𝓕 (fun X : ι → Ω → E ↦ rightContinuous X ∧ Martingale X 𝓕 P) := by
  intro X ⟨hRC, hX⟩ τ hτ
  refine ⟨?_, ?_, fun i j hij ↦ ?_⟩
  · sorry
  · sorry
  ·
    sorry

/-- Submartingales are a stable class. -/
lemma isStable_submartingale : IsStable 𝓕 (fun X : ι → Ω → ℝ ↦ Submartingale X 𝓕 P) := by
  sorry

end ProbabilityTheory
