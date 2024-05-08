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
end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

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

    -- Finset.sum_mul と Finset.sum_add_distrib を使うといい感じらしい
    def weightedAverage (n : ℕ) (lambda : ℝ) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1) (a b : StandardSimplex n) : StandardSimplex n where
      V i := lambda * a.V i + (1 - lambda) * b.V i
      NonNeg := by
        intro i
        apply add_nonneg
        · exact mul_nonneg lambda_nonneg (a.NonNeg i)
        · exact mul_nonneg (sub_nonneg_of_le lambda_le) (b.NonNeg i)

      sum_eq_one := by
        sorry

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

  -- シグマ型の例として標準単体全体の方を紹介しよう
  def StdSimplex := Σ n : ℕ, StandardSimplex n

  section
  variable (s : StdSimplex)

  #check s.fst
  #check s.snd

  #check s.1
  #check s.2

  end
  /-
  上の例でみたように structure の代わりに product 型 や sigma 型を使うこともできる. しかし prod や sigma は各メンバの名前が固定のものになり, またどのような型を持っているのかの認識が難しくなる. structure を使うことで, 各メンバにカスタムネームをつけることができ, さらに型の表記が簡単になる
  -/

-- 代数的構造の一例として型α上に定まる群耕造を定義してみよう
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

-- ↓これは Mathlib のGroup. ctrl+clickで定義が見れる
#check Group

-- 便利なので群全体の型も定義しよう
structure Group₁Cat where
  α : Type*
  str : Group₁ α

-- lean において同型は次のように扱う
section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

-- Mathlibは偉いので同型の合成ができる
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) := rfl

example (x : α) : (f.trans g) x = g (f x) := rfl

example : (f.trans g : α → γ) = g ∘ f := rfl

example (α : Type*) : Equiv.Perm α = (α ≃ α) := rfl

end

def permGroup {α : Type*} : Group₁ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.refl_trans
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y  z)
  zero_add : ∀ x : α, add zero x = x
  add_zero : ∀ x : α, add x zero = x
  add_left_neg : ∀ x : α, add (neg x) x = zero

namespace Point
  def neg (a : Point) : Point :=
    ⟨-a.x, -a.y, -a.z⟩

  def zero : Point := ⟨0, 0, 0⟩

  def addGroupPoint : AddGroup₁ Point := sorry

end Point

/-
structure を使った型の定義では通常の数学をするのに困難が生じることがある
たとえば ℝ は Group でも Commutative Ring でも Metric Space でもある
このように複数の属性を持っていることを Lean に伝えるのに structure を使った定義は難しい
そこで Lean では `class` `instance` `[]記法` によってそれを実現できるようにサポートしている
-/

-- `structure` の代わりに `class` を使う
class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

-- `def` の代わりに `instance` を使う
instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

-- `[self : Group₂ α]` が現れる
#check Group₂.mul

-- `[Group₂ α]` を使うことで `α` には `Group₂` の構造が乗っかっていて, そのことを活用してほしいと Lean に伝えることができる
def mySquare {α : Type*} [Group₂ α] (x : α) := Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f := rfl

example : mySquare f = f.trans f := rfl

end

-- `class` と `instance` を使うことで記法を統一することができる
/-
例えば, 任意の `Group` インスタンスの演算としては `+`,
任意の `AddGroup` インスタンスの演算として `*`,
任意の `Ring` インスタンスの演算としては `+` と `*`

が使えるようになっている. これは `class` と `instance` を用いたことによる恩恵である
-/

-- 次のようにすることで `Group₂` に記法を追加できる

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α := ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α := ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α := ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) := rfl

end

-- 演習問題として AddGroup₂ を実装してみる

class AddGroup₂ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α , add (add x y) z = add x (add y z)
  zero_add : ∀ x : α , add zero x = x
  add_zero : ∀ x : α , add x zero = x
  add_left_neg : ∀ x : α , add (neg x) x = zero

instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α := ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α := ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α := ⟨AddGroup₂.neg⟩

instance : AddGroup₂ Point where
  add := Point.add
  zero := ⟨0, 0, 0⟩
  neg a := ⟨-a.x, -a.y, -a.z⟩
  add_assoc := Point.add_assoc
  zero_add := sorry
  add_zero := sorry
  add_left_neg := sorry

-- § 6.3 Building the Gaussian Integers

end my_sketch
