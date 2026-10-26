/- Copyright (c) Kelin Luo, 2026. All rights reserved. -/
import Lean4CStheoryExercises.Init

namespace Lean4CStheoryExercises.Task2Greedy

/-!
# Task 2A: Greedy Box Packing (6 points)

Open this file in the course project, as for Task 1.
Fill each `sorry`. Keep the statements and exercise tags unchanged.
Do not add axioms. Record AI prompts in `-- Prompt:` comments.
Complete G.1-G.2 before G.5. Warnings about `sorry` are expected until finished.
In a definition, replace `sorry` with an expression; after `by`, use a tactic.

Goal: pack as many items as possible, with ONE item per box.
An item fits when its size is at most the box capacity.
Greedy rule: choose the largest remaining item that fits.

Reference: Greedy.pdf.

## 1. Complete the algorithm

`some x` means an item was found; `none` means no item fits.
Work from top to bottom. Each blank needs only one expression or proof line.
`item :: rest` means the first item followed by the remaining list.
`exact h` uses an existing proof h. `decide` checks a concrete example.
-/

-- Provided: combine one candidate with the best choice from the remaining items.
def keepLarger (candidate : Nat) : Option Nat -> Option Nat
  | none => some candidate
  | some best => some (max candidate best)

example : keepLarger 19 (some 16) = some 19 := by decide

-- By hand: with capacity 5 and items [4, 8, 3], skip 8 and choose 4 over 3.
-- After removing 4, the next box receives the remaining items [8, 3].

-- (1 point) Exercise G.1: choose the larger of this item and the best remaining item.
-- The recursive call is already written.
@[exercise "G.1" 1]
def largestFit (capacity : Nat) : List Nat -> Option Nat
  | [] => none
  | item :: rest =>
      let best := largestFit capacity rest
      if item <= capacity then
        sorry
      else best

-- (1 point) Exercise G.2: remove the chosen item before packing the next box.
-- Remove only one occurrence when several items have the chosen size.
@[exercise "G.2" 1]
def removeChosen (items : List Nat) (item : Nat) : List Nat :=
  sorry

-- Provided: the full packing loop. No changes needed here.
-- Output pairs are (capacity, item size).
def pack : List Nat -> List Nat -> List (Nat × Nat)
  | [], _ => []
  | capacity :: boxes, items =>
      match largestFit capacity items with
      | none => pack boxes items
      | some item => (capacity, item) :: pack boxes (removeChosen items item)

/-!
## 2. Prove the safety step

Use the order relationships between the item sizes and box capacities.
-/

-- (1 point) Exercise G.3: if two items fit, the larger one also fits.
@[exercise "G.3" 1]
theorem larger_fits (a b capacity : Nat)
    (ha : a <= capacity) (hb : b <= capacity) : max a b <= capacity := by
  sorry

/-!
Suppose box c holds item x and box d holds the greedy choice g.
Because g is the largest item that fits c, we have x <= g.
Swap the items: put g in c and x in d. Both still fit, and the number
of packed items stays the same. This is the key exchange step.
-/

-- (2 points) Exercise G.4: show that both items fit after swapping.
-- Example: c=5, d=8, x=3, g=4. After swapping, 4<=5 and 3<=8.
-- constructor splits "A and B" into two goals, one for each bullet below.
@[exercise "G.4" 2]
theorem exchange_safe (c d x g : Nat)
    (hgreedy : g <= c) (hlargest : x <= g) (hother : g <= d) :
    g <= c ∧ x <= d := by
  constructor
  · exact hgreedy
  · -- We know x <= g and g <= d. Join these two inequalities.
    sorry

/-! ## 3. Check your algorithm -/

-- (1 point) Exercise G.5: two items of the same size are still separate items.
@[exercise "G.5" 1]
theorem duplicate_items :
    pack [5, 5] [4, 4, 8] = [(5, 4), (5, 4)] := by
  sorry

/-!
After G.1-G.2, uncomment these lines to test your code:
-/
-- #eval largestFit 25 [45, 41, 20, 19, 16]  -- some 20
-- #eval (pack [60, 40, 25, 17, 12] [45, 41, 20, 19, 16]).length  -- 4

/-!
Optional question: why does swapping preserve the number packed?
This exercise proves the swap step, not full optimality. The other cases
(an empty box or an unpacked greedy item) are discussed in the slides.

Given: this list implementation takes O(n*m) time for n boxes and m items.
-/

end Lean4CStheoryExercises.Task2Greedy
