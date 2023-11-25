import Mathlib.Data.Int.Basic --#
import Mathlib.Algebra.Order.Group.Abs --#
import Mathlib.Algebra.Order.Ring.CharZero --#

/-! # 整除関係

## 定義

まず言葉の定義から始めましょう．

整数 $a, b ∈ ℤ$ が与えられたとします．このとき $a$ が $b$ を割り切るとは，ある $z ∈ ℤ$ が存在して $a z = b$ となることを言います．これを $a ∣ b$ と書きます．
-/

/-! $a ∣ b$ であることを次のようにも言いますが，すべて同じ意味です．
* $b$ は $a$ で割り切れる
* $b$ は $a$ の倍数(multiple)である
* $a$ は $b$ の約数(divisor)である

$a ∣ b$ でないとき，斜線を入れて $a ∤ b$ と書きます．-/

/-! ## Lean での定義

Lean では，「割り切れる」ということは `Dvd` という型クラスで表現されます．その際，`∣` という記法も定義されています． -/

section --#

-- inductive Dvd.{u_1} : Type u_1 → Type u_1
-- number of parameters: 1
-- constructors:
-- Dvd.mk : {α : Type u_1} → (α → α → Prop) → Dvd α
#print Dvd

variable (α : Type) [self : Dvd α]

#check ((· ∣ ·) : α → α → Prop)

end --#

/-! そして整数 `Int` は `Dvd` のインスタンスです．これは `Int.instDvdInt` という名前で呼ばれています． -/

-- Int.instDvdInt
#synth Dvd Int

#check ((· ∣ ·) : ℤ → ℤ → Prop)

/-! ## 基本的な性質

定義からすぐに従う基本的な性質として，まずどんな整数 $a ∈ℤ$ に対しても $1 ∣ a$ であり，かつ $a ∣ a$ です．
-/

/-- 1 はなんでも割り切る -/
theorem one_dvd (a : ℤ) : 1 ∣ a := by
  use a
  simp

/-- 必ず自分自身で割り切れる -/
theorem dvd_refl (a : ℤ) : a ∣ a := by
  use 1
  simp

/-! また，$a × 0 = 0$ なので任意の整数は $0$ を割り切ります．-/

theorem dvd_zero (a : ℤ) : a ∣ 0 := by
  use 0
  simp

/-! さらに，整数 $a, b, c ∈ ℤ$ について $a b ∣ c$ ならば $a ∣ c$ かつ $b ∣ c$ も成り立ちます． -/

theorem dvd_of_mul_right_dvd (a b c : ℤ) : a * b ∣ c → a ∣ c ∧ b ∣ c := by
  -- `a * b ∣ c` だと仮定します
  intro h

  -- 整除関係の定義から， `c = a * b * k` となる `k` が取れます．
  have ⟨k, hk⟩ := h
  clear h

  constructor
  case left =>
    -- したがって `a ∣ c` であることが従います．
    use b * k
    simp [hk, mul_assoc]

  case right =>
    -- 同様に `b ∣ c` であることも従います．
    use a * k
    simp [hk, ←mul_assoc]
    rw [show a * b = b * a from by simp [mul_comm]]
