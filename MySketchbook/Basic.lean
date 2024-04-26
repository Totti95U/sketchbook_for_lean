import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Init.Set
import Std

open Nat

universe u

#print Nat

namespace my_sketch
  def range : ℕ → Set ℕ
  | 0     => {}
  | n + 1 => (range n) ∪ {n}

  def Is_Injective {X Y : Type u} (f : X → Y) : Prop := ∀ (x₁ x₂ : X), f x₁ = f x₂ → x₁ = x₂
  def Is_Surjective {X Y : Type u} (f : X → Y) : Prop := ∀ y : Y, ∃ x : X , f x = y
  def Is_Bijective {X Y : Type u} (f : X → Y) : Prop := Is_Injective (f) ∧ Is_Surjective (f)

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

  theorem is_in_range_succ (n : ℕ) : n ∈ range (succ n) := by
    exact Set.mem_union_right (range n) rfl

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

  lemma range_is_increasing' {n m : ℕ} : range n ⊆ range m ↔ n ≤ m := by
    constructor
    · intro h
      cases n with
      | zero =>
        exact Nat.zero_le m
      | succ n =>
        replace h := h (mem_of_range_iff.mpr (lt.base n))
        rw [mem_of_range_iff] at h
        linarith
    · exact range_is_increasing

  theorem range_is_injective : range is injective := by
    intro n m h
    rw [Set.Subset.antisymm_iff] at h
    repeat rw [range_is_increasing'] at h
    linarith

  theorem range_is_not_surjective: ¬ (range is surjective) := by
    rw [Is_Surjective]
    push_neg
    use {1}
    by_contra! h
    have ⟨n, h⟩ := h
    cases n with
    | zero =>
      rw [range] at h
      have h' : 1 ∈ ∅ := by
       rw [h]
       exact rfl
      exact h'
    | succ n =>
      have h' : 0 < succ n := by exact zero_lt_succ n
      rw [← mem_of_range_iff] at h'
      rw [h] at h'
      exact Nat.zero_ne_one h'

end my_sketch
