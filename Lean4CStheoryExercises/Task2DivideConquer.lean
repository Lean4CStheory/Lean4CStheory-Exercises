/- Copyright (c) Kelin Luo, 2026. All rights reserved. -/
import Lean4CStheoryExercises.Init
import Lean4CStheory.Asymptotics.MasterTheorem.NatRecurrences

namespace Lean4CStheoryExercises.Task2DivideConquer

/-!
# Task 2B: Majority Elements and Divide and Conquer (10 points)

Open this file in the course project, as for Task 1.
Fill each `sorry`. Keep the statements and exercise tags unchanged.
Do not add axioms. Record AI prompts in `-- Prompt:` comments.
Complete Q.1-Q.2 before executing the algorithm, and Q.5-Q.9 in order.
Warnings about `sorry` are expected until finished.

A majority element occurs strictly more than half the time.
For example, 2 is the majority of [2, 1, 2, 3, 2], but [1, 2, 1, 2]
has no majority. An empty list also has no majority.

Algorithm: split the list into two halves and recursively obtain a candidate
from each half. Verify those candidates against the whole list. A candidate
that is a majority of one half need not be a majority of the whole list.

The algorithm is defined entirely in this file. We use only the
library's Master Theorem corollary, not a library implementation of the algorithm.
-/

/-! ## 1. Verify and combine candidates -/

-- List.count counts occurrences, including repeated equal values.
example : [4, 1, 4, 4].count 4 = 3 := by decide

/-- An element is a majority when its occurrence count is strictly more than half. -/
def IsMajority (a : Nat) (xs : List Nat) : Prop :=
  xs.length < 2 * xs.count a

-- The result of a timed operation is (answer, number of equality tests).
-- A missing candidate needs no scan. Checking a candidate scans the whole list.
-- (1 point) Exercise Q.1: complete the test for a strict majority.
@[exercise "Q.1" 1]
def verifyCandidate (xs : List Nat) : Option Nat → Option Nat × Nat
  | none => (none, 0)
  | some a => ((if xs.length < sorry then some a else none), xs.length)

-- (1 point) Exercise Q.2: choose the result after the left candidate fails verification.
@[exercise "Q.2" 1]
def combineCandidates (xs : List Nat) (left right : Option Nat) : Option Nat × Nat :=
  let checkedLeft := verifyCandidate xs left
  match checkedLeft.1 with
  | some a => (some a, checkedLeft.2)
  | none =>
      let checkedRight := verifyCandidate xs right
      (sorry, checkedLeft.2 + checkedRight.2)

-- Provided: each candidate check costs at most one full scan.
/-- Verifying a candidate performs at most one equality test per input element. -/
lemma verifyCandidate_cost_le (xs : List Nat) (candidate : Option Nat) :
    (verifyCandidate xs candidate).2 ≤ xs.length := by
  cases candidate with
  | none => exact Nat.zero_le _
  | some a => exact le_rfl

/-- Combining two candidates performs at most two full scans. -/
lemma combineCandidates_cost_le (xs : List Nat) (left right : Option Nat) :
    (combineCandidates xs left right).2 ≤ 2 * xs.length := by
  have hleft := verifyCandidate_cost_le xs left
  have hright := verifyCandidate_cost_le xs right
  cases h : (verifyCandidate xs left).1 <;>
    simp only [combineCandidates, h] <;> omega

/-!
## 2. Why two candidates suffice

If an element is not a majority in either half, each half contains at most
half its entries equal to that element. Adding the counts rules out a majority
in the whole list. This fact justifies looking only at the two recursive candidates.
-/

-- (2 points) Exercise Q.3: prove the key fact for any split, including unequal halves.
/-- A majority of an appended list is a majority in at least one of its two parts. -/
@[exercise "Q.3" 2]
theorem majority_in_one_half (a : Nat) (left right : List Nat)
    (h : IsMajority a (left ++ right)) :
    IsMajority a left ∨ IsMajority a right := by
  unfold IsMajority at *
  simp only [List.length_append, List.count_append] at h
  sorry

/-! ## 3. The recursive algorithm

The provided recursion returns both the candidate and its comparison count.
The halves always have sizes floor(n/2) and ceil(n/2), including odd n.
Empty and singleton inputs require no equality tests.

We count equality tests inside List.count. Splitting, length calculations,
option tests, and arithmetic are not charged in this model. The final bound
is a comparison bound, not a claim about the bit cost of natural-number arithmetic.
-/

def majorityRun : List Nat → Option Nat × Nat
  | [] => (none, 0)
  | [x] => (some x, 0)
  | x :: y :: rest =>
      let input := x :: y :: rest
      let half := input.length / 2
      let left := input.take half
      let right := input.drop half
      let leftRun := majorityRun left
      let rightRun := majorityRun right
      let combined := combineCandidates input leftRun.1 rightRun.1
      (combined.1, leftRun.2 + rightRun.2 + combined.2)
termination_by xs => xs.length
decreasing_by
  all_goals simp_wf
  all_goals omega

def majority (xs : List Nat) : Option Nat := (majorityRun xs).1

def majorityCost (xs : List Nat) : Nat := (majorityRun xs).2

-- (1 point) Exercise Q.4: check a majority and a tie.
@[exercise "Q.4" 1]
theorem majority_examples :
    majority [2, 1, 2, 3, 2] = some 2 ∧ majority [1, 2, 1, 2] = none := by
  sorry

/-!
After Q.1-Q.2, uncomment these lines to inspect the result and comparison count:
-/
-- #eval majorityRun [2, 1, 2, 3, 2]
-- #eval majorityRun []
-- #eval majorityRun [7]

/-! ## 4. Derive the recurrence and apply the Master Theorem

First derive the algorithm's one-step comparison bound. Then relate that bound
to a size-only function. We supply the induction scaffolding; students complete
the recurrence arithmetic and the Master Theorem application.

`T =O f` means that T(n) is at most a constant multiple of f(n) for all
sufficiently large n. `ceilLog2 n` is the ceiling of log_2(n) for positive n.
-/

open Lean4CStheory.Asymptotics
open Lean4CStheory.Asymptotics.MasterTheorem

-- (1 point) Exercise Q.5: derive the recurrence from majorityRun and the combine bound.
/-- A nontrivial majority call costs its two recursive calls plus at most two scans. -/
@[exercise "Q.5" 1]
theorem majority_cost_step (x y : Nat) (rest : List Nat) :
    let input := x :: y :: rest
    majorityCost input ≤
      majorityCost (input.take (input.length / 2)) +
      majorityCost (input.drop (input.length / 2)) + 2 * input.length := by
  dsimp only
  let input := x :: y :: rest
  let left := input.take (input.length / 2)
  let right := input.drop (input.length / 2)
  let recursiveCost := majorityCost left + majorityCost right
  let combineCost := (combineCandidates input (majority left) (majority right)).2
  have hcombine : combineCost ≤ 2 * input.length :=
    combineCandidates_cost_le input (majority left) (majority right)
  rw [majorityCost, majorityRun]
  change recursiveCost + combineCost ≤ recursiveCost + 2 * input.length
  sorry

-- Provided: a size-only upper bound, with the same two subproblem sizes.
def majorityBound : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      majorityBound ((n + 2) / 2) +
        majorityBound (n + 2 - (n + 2) / 2) + 2 * (n + 2)

-- (1 point) Exercise Q.6: prove the size recurrence from its definition.
/-- The size bound satisfies the balanced two-branch recurrence with linear extra work. -/
@[exercise "Q.6" 1]
theorem majority_bound_step (n : Nat) (hn : 2 ≤ n) :
    majorityBound n =
      majorityBound (n / 2) + majorityBound (n - n / 2) + 2 * n := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  subst n
  sorry

-- (1 point) Exercise Q.7: use Q.5-Q.6 to bound the algorithm by the size recurrence.
/-- Every input's comparison count is bounded by the size-only recurrence. -/
@[exercise "Q.7" 1]
theorem majority_cost_le_bound (xs : List Nat) :
    majorityCost xs ≤ majorityBound xs.length := by
  fun_induction majorityRun xs with
  | case1 => simp only [majorityCost, majorityRun, List.length_nil, majorityBound, le_refl]
  | case2 x =>
      simp only [majorityCost, majorityRun, List.length_cons, List.length_nil,
        Nat.zero_add, majorityBound, le_refl]
  | case3 x y rest input half left right leftRun rightRun combined ihLeft ihRight =>
      have hhalf : half ≤ input.length := Nat.div_le_self _ _
      have hleft : left.length = input.length / 2 := by
        simp only [left, List.length_take, Nat.min_eq_left hhalf, half]
      have hright : right.length = input.length - input.length / 2 := by
        simp only [right, List.length_drop, half]
      have hsize : 2 ≤ input.length := by simp only [input, List.length_cons]; omega
      have hstep := majority_cost_step x y rest
      change majorityCost input ≤ majorityCost left + majorityCost right +
        2 * input.length at hstep
      rw [hleft] at ihLeft
      rw [hright] at ihRight
      change majorityCost input ≤ majorityBound input.length
      rw [majority_bound_step input.length hsize]
      sorry

-- (1 point) Exercise Q.8: apply the library's Master Theorem to Q.6.
/-- The majority comparison recurrence has an O(n log n) upper bound. -/
@[exercise "Q.8" 1]
theorem majority_bound_bigO :
    majorityBound =O (fun n => n * ceilLog2 n) := by
  have hrec : ∀ n ≥ 2,
      majorityBound n ≤
        majorityBound (n / 2) + majorityBound (n - n / 2) + 2 * n := by
    intro n hn
    exact (majority_bound_step n hn).le
  sorry

-- (1 point) Exercise Q.9: transfer Q.8's bound to the algorithm using Q.7.
/-- Majority detection uses O(n log n) equality tests uniformly over all input lists. -/
@[exercise "Q.9" 1]
theorem majority_comparisons_bigO :
    ∃ C N : Nat, ∀ xs : List Nat, N ≤ xs.length →
      majorityCost xs ≤ C * (xs.length * ceilLog2 xs.length) := by
  obtain ⟨C, N, hbound⟩ := majority_bound_bigO
  refine ⟨C, N, ?_⟩
  intro xs hxs
  sorry

/-!
The splits are balanced by construction, so the bound applies to every input.
Q.3 proves the key candidate-selection fact; a full inductive correctness proof
of majorityRun is outside this task's scope.
-/

end Lean4CStheoryExercises.Task2DivideConquer
