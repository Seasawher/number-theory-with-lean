import Mathlib.Data.Int.Basic --#
import Mathlib.Algebra.Order.Group.Abs --#
import Mathlib.Algebra.Order.Ring.CharZero --#

/-! # 整除関係

## 定義

まず言葉の定義から始めましょう．

整数 $a, b ∈ ℤ$ が与えられたとします．このとき $a$ が $b$ を割り切るとは，ある $z ∈ ℤ$ が存在して $a z = b$ となることを言います．これを $a ∣ b$ と書きます．
-/

/-! 「$a$ が $b$ を割り切る」というのは $a$ 目線の言い方ですが，$b$ 目線では「$b$ は $a$ の倍数(multiple)である」と言います．
また，$a$ で $b$ が割り切れないとき，斜線を入れて $a ∤ b$ と書きます．-/

example (a b : ℤ) : a ∣ b ↔ ∃ z : ℤ, a * z = b := by
  dsimp [(· ∣ ·)]
  aesop

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

/-! さらに，整数 $a, b, c ∈ ℤ$ について $a b ∣ c$ ならば $a ∣ c$ が成り立ちます． -/

theorem dvd_of_mul_right_dvd (a b c : ℤ) : a * b ∣ c → a ∣ c := by
  -- `a * b ∣ c` だと仮定します
  intro h
  -- 整除関係の定義から， `c = a * b * k` となる `k` が取れます．
  have ⟨k, hk⟩ := h
  -- したがって `a ∣ c` であることが従います．
  use b * k
  simp [hk, mul_assoc]
