/- Copyright (c) Kelin Luo, 2026. All rights reserved. -/
import Lean4CStheoryExercises.Init

namespace Lean4CStheoryExercises.Task2DynamicProgramming

/-!
# Task 2C: Weighted Interval Scheduling (6 points)

Open this file in the course project, as for Task 1.
Fill each `sorry`. Keep the statements and exercise tags unchanged.
Do not add axioms. Record AI prompts in `-- Prompt:` comments.
Complete W.1-W.2 before the later proofs and execution checks.
Warnings about `sorry` are expected until finished.

Goal: choose non-overlapping jobs with maximum total weight.
A job ending when another starts is compatible with it.
Assume positive durations and weights, with jobs sorted by finish time.
Reference: DynamicProgramming.pdf.

## 1. Find the compatible prefix

Each blank needs only one expression or proof line.
The table-building code is supplied; you only complete the main choices.
`⟨1, 3, 5⟩` is a job starting at 1, finishing at 3, with weight 5.
`#[0, 5, 6]` is an array of stored answers. `decide` checks a concrete example.
-/

structure Job where
  start : Nat
  finish : Nat
  weight : Nat
  deriving Repr, DecidableEq

def ValidJob (j : Job) : Prop := j.start < j.finish ∧ 0 < j.weight

example : ValidJob ⟨1, 3, 5⟩ := by simp [ValidJob]

-- Provided: our input assumptions. You do not need to implement sorting.
def Prepared (jobs : List Job) : Prop :=
  (∀ j ∈ jobs, ValidJob j) ∧
  jobs.Pairwise (fun a b => a.finish <= b.finish)

-- Worked example: takeWhile keeps the initial entries satisfying a condition.
example : ([1, 3, 6].takeWhile (fun finish => finish <= 4)).length = 2 := by
  decide

-- (1 point) Exercise W.1: an earlier job must finish by the new job's start.
-- The result is p(j), the number of earlier compatible jobs.
-- p(j) counts a prefix of the sorted list; it is not an array index of a job.
@[exercise "W.1" 1]
def predecessor (earlier : List Job) (job : Job) : Nat :=
  (earlier.takeWhile (fun j => j.finish <= sorry)).length

/-!
## 2. Complete the recurrence

OPT(j) is the best weight using the first j jobs; OPT(0) = 0.
For job j, choose the better of:
  skip: OPT(j-1)
  take: job.weight + OPT(p(j))
-/

-- Worked example: skipping gives 8; taking gives 6 + 5, so choose 11.
example : max 8 (6 + 5) = 11 := by decide

-- (1 point) Exercise W.2: complete the "take this job" value.
@[exercise "W.2" 1]
def bestValue (skip weight compatibleBest : Nat) : Nat :=
  max skip (sorry)

-- Provided: read the skip and take values from the table.
-- table[k] stores OPT(k); getD reads an entry, with a default of 0.
def nextValue (table : Array Nat) (weight p : Nat) : Nat :=
  bestValue (table.getD (table.size - 1) 0) weight (table.getD p 0)

-- Provided: build the table one job at a time, starting with OPT(0) = 0.
-- You do not need to change this code.
def buildTable (jobs : List Job) : Array Nat :=
  let (_, table) := jobs.foldl (fun (state : List Job × Array Nat) job =>
    let (earlier, table) := state
    let p := predecessor earlier job
    (earlier ++ [job], table.push (nextValue table job.weight p))) ([], #[0])
  table

def optimumValue (jobs : List Job) : Nat :=
  let table := buildTable jobs
  table.getD (table.size - 1) 0

/-!
## 3. Prove properties of the recurrence

These exercises check the max operation, not the full scheduling theorem.
-/

-- Worked example: max is at least its left argument.
example (a b : Nat) : a <= max a b := by
  exact Nat.le_max_left a b

-- (1 point) Exercise W.3: either candidate is bounded by the chosen value.
-- The first half is given.
-- unfold exposes the definition; constructor splits the two claims.
@[exercise "W.3" 1]
theorem recurrence_candidates (skip weight compatibleBest : Nat) :
    skip <= bestValue skip weight compatibleBest ∧
    weight + compatibleBest <= bestValue skip weight compatibleBest := by
  unfold bestValue
  constructor
  · exact Nat.le_max_left _ _
  · sorry

-- (1 point) Exercise W.4: if both choices are at most bound, so is their max.
@[exercise "W.4" 1]
theorem recurrence_upper (skip weight compatibleBest bound : Nat)
    (hskip : skip <= bound) (htake : weight + compatibleBest <= bound) :
    bestValue skip weight compatibleBest <= bound := by
  unfold bestValue
  sorry

/-! ## 4. Check a small example -/

-- Provided sample, sorted by finish. p values are [0, 0, 1, 3].
def sample : List Job :=
  [⟨1, 3, 5⟩, ⟨2, 5, 6⟩, ⟨4, 6, 5⟩, ⟨6, 7, 4⟩]

example : Prepared sample := by simp [Prepared, sample, ValidJob]

/-!
Work through the sample before W.5 (job numbers start at 1):
  job   weight   p(j)   skip   take                OPT(j)
  1     5        0     0      5 + OPT(0) = 5       5
  2     6        0     5      6 + OPT(0) = 6       6
  3     5        1     6      5 + OPT(1) = 10      10
  4     4        3     10     4 + OPT(3) = 14      14
The table also includes OPT(0)=0 at its beginning.
-/

-- (1 point) Exercise W.5: check the table.
@[exercise "W.5" 1]
theorem sample_table : buildTable sample = #[0, 5, 6, 10, 14] := by
  sorry

-- (1 point) Exercise W.6: earliest-finish greedy is not safe with weights.
-- It would choose the first two jobs for weight 4, missing the weight-10 job.
@[exercise "W.6" 1]
theorem greedy_counterexample :
    optimumValue [⟨0, 2, 2⟩, ⟨2, 4, 2⟩, ⟨0, 5, 10⟩] = 10 := by
  sorry

/-!
After W.1-W.2, uncomment these lines:
-/
-- #eval buildTable sample  -- #[0, 5, 6, 10, 14]
-- #eval optimumValue []    -- 0

/-!
Takeaway: when taking job j, add OPT(p(j)) because those earlier jobs
finish before j starts. OPT(j-1) might include a job that overlaps with j.

Given: this simple implementation takes O(n^2) time and O(n) space.
-/

end Lean4CStheoryExercises.Task2DynamicProgramming
