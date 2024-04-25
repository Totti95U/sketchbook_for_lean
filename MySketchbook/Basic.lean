import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Set
import Std

open Nat

#print Nat

namespace my_sketch
  def range : ℕ → Set ℕ
  | 0     => {}
  | n + 1 => (range n) ∪ {n}

  def Is_Injective {X Y : Type} (f : X → Y) : Prop := ∀ (x₁ x₂ : X), f x₁ = f x₂ → x₁ = x₂
  def Is_Surjective {X Y : Type} (f : X → Y) : Prop := ∀ y : Y, ∃ x : X , f x = y
  def Is_Bijective {X Y : Type} (f : X → Y) : Prop := Is_Injective (f) ∧ Is_Surjective (f)

  postfix:0 " is injective" => Is_Injective
  postfix:0 " is surjective" => Is_Surjective
  postfix:0 " is bijective" => Is_Bijective

  example : range 0 = {} := by
    rfl

  example : range 1 = {0} := by
    rw [range]
    rw [range]
    exact Set.empty_union {zero}

  example : range 2 = {0, 1} := by
    repeat rw [range]
    rw [Set.empty_union]
    rfl

  lemma range_contains_smaller_numbers {n k : ℕ} : k < n → k ∈ range n := by
    intro h
    induction n with
    | zero =>
      exfalso
      exact not_succ_le_zero k h
    | succ n hd =>
      rw [range]
      have h' : k < n ∨ k = n := by exact Nat.lt_succ_iff_lt_or_eq.mp h
      rcases h' with h1 | h2
      -- case : k < n
      · replace hd := hd h1
        left
        exact hd
      -- case : k = n
      · rw [← h2]
        right
        trivial

  lemma mem_of_range_is_small {n k : ℕ} : k ∈ range n → k < n := by
    intro h
    induction n with
    | zero =>
      exfalso
      rw [range] at h
      exact h
    | succ n hd =>
      rw [range] at h
      rcases h with h1 | h2
      · replace hd := hd h1
        exact lt.step hd
      · have h2' : k = n := by exact h2
        rw [h2']
        exact lt.base n

  theorem mem_of_range_iff {n k : ℕ} : k ∈ range n  ↔ k < n := by
    exact ⟨mem_of_range_is_small, range_contains_smaller_numbers⟩

  lemma range_is_increasing {n m : ℕ} : n ≤ m → range n ⊆ range m := by
    intro h x hx
    rw [mem_of_range_iff] at hx
    rw [mem_of_range_iff]
    exact Nat.lt_of_lt_of_le hx h

  lemma rev_of_range_is_increasing {n m : ℕ} : range n ⊆ range m → n ≤ m := by
    intro h
    induction m with
    | zero => sorry
    | succ m  hm =>
      induction n with
      | zero => exact Nat.zero_le (succ m)
      | succ n hn =>
        repeat rw [range] at h
        replace h : range n ⊆ range m := by
          intro x hx


  theorem range_is_injective : range is injective := by
    intro n m h
    rw [Set.Subset.antisymm_iff] at h
    have h1 := rev_of_range_is_increasing h.left
    have h2 := rev_of_range_is_increasing h.right
    exact Nat.le_antisymm h1 h2

end my_sketch
