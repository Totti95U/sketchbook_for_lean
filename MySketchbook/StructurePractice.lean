-- reference: https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html

import Std
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace my_sketch
-- ext をつけると, "その構造が等しい ↔ 各要素が等しい" と設定される
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

namespace Point
  def add (a b : Point) : Point :=
    ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

  def add' (a b : Point) : Point where
    x := a.x + b.x
    y := a.y + b.y
    z := a.z + b.z

  -- protected をつけると `Point` を open しても `Point.add_comm` でないと呼び出せなくなる
  protected theorem add_comm (a b : Point) : add a b = add b a := by
    rw [add, add]
    ext <;> dsimp
    repeat' apply add_comm

  example (a b : Point) : add a b = add b a := by simp [add, add_comm]

  -- 自明なことは lean 君もちゃんとわかっている
  theorem add_x (a b : Point) : (add a b).x = a.x + b.x := by rfl

  -- パターンマッチングも使える
  def addAlt : Point → Point → Point
    | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

  def addAlt' : Point → Point → Point
    | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

  theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
    rfl

  theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
    rw [addAlt, addAlt]
    -- the same proof still works, but the goal view here is harder to read
    ext <;> dsimp
    repeat' apply add_comm

  -- 練習問題
  protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
    rw [add, add, add, add]
    ext <;> dsimp
    repeat' apply add_assoc

  def smul (r : ℝ) (a : Point) : Point :=
    ⟨r * a.x, r * a.y, r * a.z⟩

  theorem smul_distrib (r : ℝ) (a b : Point) :
      (smul r a).add (smul r b) = smul r (a.add b) := by
    rw [add, add, smul, smul, smul]
    ext <;> dsimp
    repeat' rw [mul_add]

  -- `structure` にはデータが満たすべき "制約" をつけることができる
  -- `StandardTwoSimplex` は標準2単体の点を表す構造である
  structure StandardTwoSimplex where
    x : ℝ
    y : ℝ
    z : ℝ
    x_nonneg : 0 ≤ x
    y_nonneg : 0 ≤ y
    z_nonneg : 0 ≤ z
    sum_eq : x + y + z = 1

  -- そのような構造に関する関数は例えば次のように定義される
  def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex where
    x := a.y
    y := a.x
    z := a.z
    x_nonneg := a.y_nonneg
    y_nonneg := a.x_nonneg
    z_nonneg := a.z_nonneg
    sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

-- 単体内の2点の中点はまた単体に属する
-- noncomputable は 実数の除算をするためにつけている
noncomputable def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

-- どうように2点を内分する点は単体に属する
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1) (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (sub_nonneg_of_le lambda_le) b.x_nonneg)

  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (sub_nonneg_of_le lambda_le) b.y_nonneg)

  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (sub_nonneg_of_le lambda_le) b.z_nonneg)

  sum_eq := by calc
    lambda * a.x + (1 - lambda) * b.x + (lambda * a.y + (1 - lambda) * b.y) + (lambda * a.z + (1 - lambda) * b.z) = lambda * (a.x  + a.y + a.z) + (1 - lambda) * (b.x + b.y + b.z) := by ring
    _ = lambda + (1 - lambda) := by simp [a.sum_eq, b.sum_eq]
    _ = 1 := by linarith

  -- 構造にはパラメータを付加することもできる
  open BigOperators

  -- n-標準単体
  structure StandardSimplex (n : ℕ) where
    V : Fin n → ℝ
    NonNeg : ∀ i : Fin n, 0 ≤ V i
    sum_eq_one : (∑ i, V i) = 1

  namespace StandardSimplex

    noncomputable def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n where
      V i := (a.V i + b.V i) / 2
      NonNeg := by
        intro i
        apply div_nonneg
        · linarith [a.NonNeg i, b.NonNeg i]
        norm_num
      sum_eq_one := by
        simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, a.sum_eq_one, b.sum_eq_one]
        field_simp

  end StandardSimplex

  -- 構造を使うことで性質をまとめることもできる
  structure IsLinear (f : ℝ → ℝ) where
    is_additive : ∀ x y, f (x + y) = f x + f y
    preserves_mul : ∀ x c, f (c * x) = c * f x

  section
  variable (f : ℝ → ℝ) (linf : IsLinear f)

  #check linf.is_additive
  #check linf.preserves_mul

  end

  -- 列挙以外の方法でも構造は定義できる
  def Point'' := ℝ × ℝ × ℝ

  def IsLinear' (f : ℝ → ℝ) :=
    (∀ x y, f (x + y) = f x + f y) ∧ (∀ x c, f (c * x) = c * f x)

  -- 部分型の一例として正実数の型を作ってみる
  def PReal := { y : ℝ | 0 < y }

  section
  variable (x : PReal)

  #check x
  #check x.val
  #check x.property
  #check x.1
  #check x.2

  end

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2


end my_sketch
