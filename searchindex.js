Object.assign(window.search, {"doc_urls":["index.html#lean-で学ぶ初めての整数論","index.html#本書の読む際の注意","index.html#リンク集","Prerequisite.html#前提条件","Euclid.html#直線の格子点とeuclid-のアルゴリズム","Divisibility.html#整除関係","Divisibility.html#定義","Divisibility.html#lean-での定義","Divisibility.html#基本的な性質","Divisibility.html#演習問題","CommonDivisor.html#公約数","CommonDivisor.html#公約数と最大公約数","CommonDivisor.html#lean-での定義","INDEXING.html#index"],"index":{"documentStore":{"docInfo":{"0":{"body":3,"breadcrumbs":2,"title":1},"1":{"body":7,"breadcrumbs":1,"title":0},"10":{"body":0,"breadcrumbs":1,"title":0},"11":{"body":14,"breadcrumbs":1,"title":0},"12":{"body":43,"breadcrumbs":2,"title":1},"13":{"body":14,"breadcrumbs":2,"title":1},"2":{"body":26,"breadcrumbs":1,"title":0},"3":{"body":9,"breadcrumbs":0,"title":0},"4":{"body":20,"breadcrumbs":2,"title":1},"5":{"body":0,"breadcrumbs":1,"title":0},"6":{"body":14,"breadcrumbs":1,"title":0},"7":{"body":36,"breadcrumbs":2,"title":1},"8":{"body":75,"breadcrumbs":1,"title":0},"9":{"body":21,"breadcrumbs":1,"title":0}},"docs":{"0":{"body":"定理証明支援系 Lean を使って，整数論を学んでいこうという本です． Lean の解説ではなく数学の解説を目的としているため，読者が Lean にある程度慣れていることを仮定しています．","breadcrumbs":"Lean で学ぶ初めての整数論 » Lean で学ぶ初めての整数論","id":"0","title":"Lean で学ぶ初めての整数論"},"1":{"body":"本書のすべての Lean コードブロックには Lean Playground へジャンプするボタンが搭載されています．しかし必要な import 文などが含まれていないため，ほとんどの場合そのままでは動かないと思います．右上にある編集(suggest an edit)ボタン をクリックすると，元の *.lean ファイルにジャンプすることができますから，それを Playground にコピーして実行してください．","breadcrumbs":"Lean で学ぶ初めての整数論 » 本書の読む際の注意","id":"1","title":"本書の読む際の注意"},"10":{"body":"この節では大小関係も考えるので，話を整数 $ℤ$ から自然数 $ℕ$ に限定します．","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 公約数 » 公約数","id":"10","title":"公約数"},"11":{"body":"2 つの自然数 $a$ と $b$ に対して，そのどちらの約数でもあるような自然数のことを，公約数(common divisor)といいます．言い換えると，$d ∈ ℕ$ が $a$ と $b$ の公約数であるとは，$d ∣ a$ かつ $d ∣ b$ が成り立つことです． 整除関係の節 で見たように，$1$ はどんな自然数の約数でもあるため，$a$, $b$ の公約数は必ず1つは存在します．かつ，公約数が無限に存在することはありえません．したがって，最大のものが存在します．それを $a$ と $b$ の最大公約数(greatest common divisor)と呼ぶことにして，$\\gcd(a, b)$ と書きます．","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 公約数 » 公約数と最大公約数","id":"11","title":"公約数と最大公約数"},"12":{"body":"有限集合から最大のものを取ってくるだけなので，じかに計算することができます． def gcd (a b : ℕ) : ℕ := Id.run do -- `do` の代わりに `Id.run do` とすることで， -- pure code の中で do notation を使えます． -- 細かいことなので気にしなくていいです. -- `a` と `b` のうち小さい方までの自然数全体 let xs := List.reverse $ List.range $ min a b for x in xs do if x ∣ a ∧ x ∣ b then return x -- このコードは実行されませんが必要です return 0 #guard gcd 12 18 = 6 #guard gcd 37 92 = 1 -- だいたい 2000 ~ 2200ms 程度\n#time #eval gcd 12345678 87654321 上記の gcd 関数で解決するように見えますが，そうではありません．$\\min (a, b)$ に比例する計算時間が必要になるため，#time の出力を見ればわかるように少し桁が大きくなっただけでかなり計算に時間がかかるようになります． また，これは後で分かることですが，公約数という概念が持つ構造を生かし切れていません．公約数を計算するもっと良い方法があります．","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 公約数 » Lean での定義","id":"12","title":"Lean での定義"},"13":{"body":"$a ∣ b$ , 1 倍数(multiple), 1 公約数(common divisor), 1 割り切る, 1 最大公約数(greatest common divisor), 1 約数(divisor), 1","breadcrumbs":"Index » Index","id":"13","title":"Index"},"2":{"body":"無料で閲覧できるものに限定して，参考になりそうな資料を紹介します．Lean については，次のようなものがあります． Mathematics in Lean Lean で数学がどのように形式化できるか解説する教科書です． The mechanics of proof 数学的な証明の書き方について，Lean を使って説明した教科書です．一部 Mathlib にないタクティクを使っているところがあるので，読まれる際は注意してください． Lean4 タクティク逆引きリスト Lean 4 の基本的なタクティク・コマンドの早見表です． 整数論については，次のようなものがあります. A Computational Introduction to Number Theory and Algebra \"Computational\" とある通り，アルゴリズムの計算量の話題や暗号理論への応用などに詳しい本です．それだけでなく，解析的整数論の話題も含まれ，最低限の予備知識で最大限に整数論を楽しむことができます． Elementary Number Theory: Primes, Congruences, and Secrets 未読 Number Theory: In Context and Interactive 未読","breadcrumbs":"Lean で学ぶ初めての整数論 » リンク集","id":"2","title":"リンク集"},"3":{"body":"Lean は定理証明支援系なので，話の中で必要になるすべての概念・定義をすべて実装する必要があります．完璧に形式的で，機械が読めるような証明を書かなければいけないことを考えると，仕方のないことです． だからといって，「自然数の足し算は可換」とか「整数の掛け算と足し算は交換する」といったことをいちいち証明していると本題に入れなくなってしまうので，本書では適当にライブラリを引用することにします． どこまでを仮定として認めるかですが，数学の教科書に書いてあるような書き方をすると 選択公理や排中律 [1] 整数には負の数，ゼロ，正の数がある 任意の2つの整数 $a, b$ は大小が比較できる．専門的な言い方をすると，整数には線形順序(全順序)が入っている． 整数には足し算，引き算，掛け算，べき乗が定義されている 足し算や掛け算は順序によらないし，括弧が不要．そして足し算と掛け算の間には分配法則が成り立つ．専門的な言い方をすると，整数は可換環をなす． といったことについてはライブラリの使用を認めます． それは Lean に置き換えると，ℤ が LinearOrderedCommRing という型クラスのインスタンスであることを認める，ということです．これは Mathlib/Data/Int/Order/Basic.lean で主張されているため，import Mathlib.Data.Int.Order.Basic を使用することは認めるということになります．なお，場合によりもっと狭い範囲に制限することもあります． 選択公理や排中律という言葉の意味が分からなくても大丈夫です．","breadcrumbs":"前提条件 » 前提条件","id":"3","title":"前提条件"},"4":{"body":"整数の割り算についてご存じでしょうか． 整数 $a, b ∈ ℤ$ $(b ≠ 0)$ に対して, $a$ を $b$ で割ったときの余り $r$ $(0 ≤ r < b)$ が計算できるのでした． この割り算という手続きは，方程式に解があるかどうか，解があるとしたらそれがどんなものかを調べる方法を提供してくれます． 仮に $a = b x$ という方程式が与えられたら，これが整数の範囲，つまり $x ∈ ℤ$ という条件下で解を持つかどうかは, $a$ を $b$ で割ったときの余りで判定できます．余りが 0 なら解があり，0 でなければ解はありません． シンプルな話ですが，これをもっと推し進めてみましょう．変数を1つ増やして，2変数にしてみます．つまり，直線 $a x + b y = c$ を考えます．これが格子点を持つかどうか，どうやったら判定できるでしょうか．言い換えれば，$x, y ∈ ℤ$ となるような解があるかどうか，あるとしてそれが何か，どうしたら計算できるでしょうか． これから見ていくように，この問題は Euclid のアルゴリズムと呼ばれる手続きを使うことで解くことができます．","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 直線の格子点とEuclid のアルゴリズム","id":"4","title":"直線の格子点とEuclid のアルゴリズム"},"5":{"body":"","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 整除関係 » 整除関係","id":"5","title":"整除関係"},"6":{"body":"まず言葉の定義から始めましょう． 整数 $a, b ∈ ℤ$ が与えられたとします．このとき $a$ が $b$ を割り切るとは，ある $z ∈ ℤ$ が存在して $a z = b$ となることを言います．これを $a ∣ b$ と書きます． $a ∣ b$ であることを次のようにも言いますが，すべて同じ意味です． $b$ は $a$ で割り切れる $b$ は $a$ の倍数(multiple)である $a$ は $b$ の約数(divisor)である $a ∣ b$ でないとき，斜線を入れて $a ∤ b$ と書きます．","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 整除関係 » 定義","id":"6","title":"定義"},"7":{"body":"Lean では，「割り切れる」ということは Dvd という型クラスで表現されます．その際，∣ という記法も定義されています． -- inductive Dvd.{u_1} : Type u_1 → Type u_1\n-- number of parameters: 1\n-- constructors:\n-- Dvd.mk : {α : Type u_1} → (α → α → Prop) → Dvd α\n#print Dvd variable (α : Type) [self : Dvd α] #check ((· ∣ ·) : α → α → Prop) そして整数 Int や自然数 Nat は Dvd のインスタンスです. -- Int.instDvdInt\n#synth Dvd Int -- Nat.instDvdNat\n#synth Dvd Nat","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 整除関係 » Lean での定義","id":"7","title":"Lean での定義"},"8":{"body":"以下で紹介する性質は ℤ だけでなく ℕ でも成り立ちますが，今回は代表して ℤ の話として説明します． 定義からすぐに従う基本的な性質として，まずどんな整数 $a ∈ℤ$ に対しても $1 ∣ a$ であり，かつ $a ∣ a$ です． /-- 1 はなんでも割り切る -/\ntheorem one_dvd (a : ℤ) : 1 ∣ a := by use a simp /-- 必ず自分自身で割り切れる -/\ntheorem dvd_refl (a : ℤ) : a ∣ a := by use 1 simp また，$a × 0 = 0$ なので任意の整数は $0$ を割り切ります． theorem dvd_zero (a : ℤ) : a ∣ 0 := by use 0 simp さらに，整数 $a, b, c ∈ ℤ$ について $a b ∣ c$ ならば $a ∣ c$ かつ $b ∣ c$ も成り立ちます． theorem dvd_of_mul_right_dvd (a b c : ℤ) : a * b ∣ c → a ∣ c ∧ b ∣ c := by -- `a * b ∣ c` だと仮定します intro h -- 整除関係の定義から， `c = a * b * k` となる `k` が取れます． have ⟨k, hk⟩ := h clear h constructor case left => -- したがって `a ∣ c` であることが従います． use b * k simp [hk, mul_assoc] case right => -- 同様に `b ∣ c` であることも従います． use a * k simp [hk, ←mul_assoc] rw [show a * b = b * a from by simp [mul_comm]]","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 整除関係 » 基本的な性質","id":"8","title":"基本的な性質"},"9":{"body":"次の sorry の部分を埋めてみてください． variable (a b c : ℤ) -- 割り算の定義の確認\nexample : a ∣ b ↔ ∃ c : ℤ, b = a * c := by sorry -- 倍数に何か乗じても倍数\nexample (h : a ∣ b) : a ∣ b * c := by sorry example : ∃ a, 11 ∣ (2 ^ a + 1) := by sorry","breadcrumbs":"直線の格子点とEuclid のアルゴリズム » 整除関係 » 演習問題","id":"9","title":"演習問題"}},"length":14,"save":true},"fields":["title","body","breadcrumbs"],"index":{"body":{"root":{"0":{"df":3,"docs":{"12":{"tf":1.0},"4":{"tf":2.0},"8":{"tf":2.23606797749979}}},"1":{"1":{"df":1,"docs":{"9":{"tf":1.0}}},"2":{"3":{"4":{"5":{"6":{"7":{"8":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":1,"docs":{"12":{"tf":1.0}}},"8":{"df":1,"docs":{"12":{"tf":1.0}}},"df":7,"docs":{"11":{"tf":1.0},"12":{"tf":1.0},"13":{"tf":2.449489742783178},"3":{"tf":1.0},"7":{"tf":1.0},"8":{"tf":2.0},"9":{"tf":1.0}}},"2":{"0":{"0":{"0":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"2":{"0":{"0":{"df":0,"docs":{},"m":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":3,"docs":{"11":{"tf":1.0},"3":{"tf":1.0},"9":{"tf":1.0}}},"3":{"7":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"4":{"df":1,"docs":{"2":{"tf":1.0}}},"6":{"df":1,"docs":{"12":{"tf":1.0}}},"8":{"7":{"6":{"5":{"4":{"3":{"2":{"1":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"9":{"2":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"a":{"df":0,"docs":{},"l":{"df":0,"docs":{},"g":{"df":0,"docs":{},"e":{"b":{"df":0,"docs":{},"r":{"a":{"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}},"b":{"df":8,"docs":{"11":{"tf":2.449489742783178},"12":{"tf":2.23606797749979},"13":{"tf":1.0},"3":{"tf":1.0},"4":{"tf":2.6457513110645907},"6":{"tf":3.1622776601683795},"8":{"tf":3.4641016151377544},"9":{"tf":2.23606797749979}}},"c":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"e":{"df":1,"docs":{"8":{"tf":1.4142135623730951}}}}},"df":3,"docs":{"4":{"tf":1.0},"8":{"tf":3.4641016151377544},"9":{"tf":2.0}},"h":{"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"k":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"r":{"df":1,"docs":{"8":{"tf":1.0}}}},"df":0,"docs":{}}},"o":{"d":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":0,"docs":{},"o":{"df":0,"docs":{},"n":{"df":2,"docs":{"11":{"tf":1.0},"13":{"tf":1.4142135623730951}}}}},"p":{"df":0,"docs":{},"u":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.4142135623730951}}}}}},"n":{"df":0,"docs":{},"g":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"df":0,"docs":{},"e":{"df":0,"docs":{},"n":{"c":{"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}}}}},"s":{"df":0,"docs":{},"t":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"c":{"df":0,"docs":{},"t":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":2,"docs":{"7":{"tf":1.0},"8":{"tf":1.0}}}}}},"df":0,"docs":{}}}}},"t":{"df":0,"docs":{},"e":{"df":0,"docs":{},"x":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}}}}}}},"d":{"df":1,"docs":{"11":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"f":{"df":1,"docs":{"12":{"tf":1.0}}}},"i":{"df":0,"docs":{},"v":{"df":0,"docs":{},"i":{"df":0,"docs":{},"s":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{")":{"df":0,"docs":{},"と":{"df":0,"docs":{},"い":{"df":0,"docs":{},"い":{"df":0,"docs":{},"ま":{"df":0,"docs":{},"す":{"df":0,"docs":{},"．":{"df":0,"docs":{},"言":{"df":0,"docs":{},"い":{"df":0,"docs":{},"換":{"df":0,"docs":{},"え":{"df":0,"docs":{},"る":{"df":0,"docs":{},"と":{"df":0,"docs":{},"，":{"$":{"d":{"df":1,"docs":{"11":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}}}}}}}},"呼":{"df":0,"docs":{},"ぶ":{"df":0,"docs":{},"こ":{"df":0,"docs":{},"と":{"df":0,"docs":{},"に":{"df":0,"docs":{},"し":{"df":0,"docs":{},"て":{"df":0,"docs":{},"，":{"$":{"\\":{"df":0,"docs":{},"g":{"c":{"d":{"(":{"a":{"df":1,"docs":{"11":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}}}}}},"df":2,"docs":{"13":{"tf":1.7320508075688772},"6":{"tf":1.0}}}}}}}},"v":{"d":{".":{"df":0,"docs":{},"m":{"df":0,"docs":{},"k":{"df":1,"docs":{"7":{"tf":1.0}}}},"{":{"df":0,"docs":{},"u":{"_":{"1":{"df":1,"docs":{"7":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"_":{"df":0,"docs":{},"o":{"df":0,"docs":{},"f":{"_":{"df":0,"docs":{},"m":{"df":0,"docs":{},"u":{"df":0,"docs":{},"l":{"_":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":0,"docs":{},"g":{"df":0,"docs":{},"h":{"df":0,"docs":{},"t":{"_":{"d":{"df":0,"docs":{},"v":{"d":{"df":1,"docs":{"8":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}}},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"f":{"df":0,"docs":{},"l":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"z":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":1,"docs":{"8":{"tf":1.0}}}}}}},"df":1,"docs":{"7":{"tf":2.6457513110645907}}},"df":0,"docs":{}}},"df":0,"docs":{},"e":{"d":{"df":0,"docs":{},"i":{"df":0,"docs":{},"t":{"df":1,"docs":{"1":{"tf":1.0}}}}},"df":0,"docs":{},"l":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":1,"docs":{"2":{"tf":1.0}}}}},"df":0,"docs":{}}}}}}},"u":{"c":{"df":0,"docs":{},"l":{"df":0,"docs":{},"i":{"d":{"df":1,"docs":{"4":{"tf":1.4142135623730951}}},"df":0,"docs":{}}}},"df":0,"docs":{}},"v":{"a":{"df":0,"docs":{},"l":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}},"x":{"a":{"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":0,"docs":{},"l":{"df":1,"docs":{"9":{"tf":1.7320508075688772}}}}}},"df":0,"docs":{}}},"g":{"c":{"d":{"df":1,"docs":{"12":{"tf":2.23606797749979}}},"df":0,"docs":{}},"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"t":{"df":0,"docs":{},"e":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"df":2,"docs":{"11":{"tf":1.0},"13":{"tf":1.0}}}}}}},"df":0,"docs":{}}},"u":{"a":{"df":0,"docs":{},"r":{"d":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}},"df":0,"docs":{}}},"df":0,"docs":{}}},"h":{"df":2,"docs":{"8":{"tf":1.7320508075688772},"9":{"tf":1.0}},"k":{"df":1,"docs":{"8":{"tf":1.7320508075688772}}}},"i":{"d":{".":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}}},"df":0,"docs":{}},"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"t":{"df":2,"docs":{"1":{"tf":1.0},"3":{"tf":1.0}}}}}}},"n":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"x":{"df":1,"docs":{"13":{"tf":1.0}}}},"u":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"d":{"df":0,"docs":{},"v":{"d":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}}},"df":1,"docs":{"7":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"r":{"a":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"r":{"df":0,"docs":{},"o":{"d":{"df":0,"docs":{},"u":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"df":1,"docs":{"8":{"tf":1.0}}}}}}},"k":{"df":1,"docs":{"8":{"tf":2.23606797749979}}},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"n":{"4":{"df":1,"docs":{"2":{"tf":1.0}}},"df":6,"docs":{"0":{"tf":2.0},"1":{"tf":1.7320508075688772},"12":{"tf":1.0},"2":{"tf":2.0},"3":{"tf":1.4142135623730951},"7":{"tf":1.4142135623730951}}}},"df":0,"docs":{},"f":{"df":0,"docs":{},"t":{"df":1,"docs":{"8":{"tf":1.0}}}}},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"d":{"c":{"df":0,"docs":{},"o":{"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":0,"docs":{},"r":{"df":1,"docs":{"3":{"tf":1.0}}}}}}},"df":0,"docs":{}},"df":0,"docs":{}}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}}},"s":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"r":{"a":{"df":0,"docs":{},"n":{"df":0,"docs":{},"g":{"df":1,"docs":{"12":{"tf":1.0}}}}},"df":0,"docs":{},"e":{"df":0,"docs":{},"v":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"s":{"df":1,"docs":{"12":{"tf":1.0}}}}}}}}},"df":0,"docs":{}}}}},"m":{"a":{"df":0,"docs":{},"t":{"df":0,"docs":{},"h":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"l":{"df":0,"docs":{},"i":{"b":{".":{"d":{"a":{"df":0,"docs":{},"t":{"a":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{".":{"b":{"a":{"df":0,"docs":{},"s":{"df":1,"docs":{"3":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}},"/":{"d":{"a":{"df":0,"docs":{},"t":{"a":{"/":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"/":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"/":{"b":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"i":{"c":{".":{"df":0,"docs":{},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"n":{"df":1,"docs":{"3":{"tf":1.0}}}},"df":0,"docs":{}}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}}}}},"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"h":{"a":{"df":0,"docs":{},"n":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{}},"i":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.0}}}},"u":{"df":0,"docs":{},"l":{"_":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"s":{"df":0,"docs":{},"o":{"c":{"df":1,"docs":{"8":{"tf":1.4142135623730951}}},"df":0,"docs":{}}}}},"c":{"df":0,"docs":{},"o":{"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"df":0,"docs":{}},"df":0,"docs":{},"t":{"df":0,"docs":{},"i":{"df":0,"docs":{},"p":{"df":0,"docs":{},"l":{"df":2,"docs":{"13":{"tf":1.0},"6":{"tf":1.0}}}}}}}}},"n":{"a":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"d":{"df":0,"docs":{},"v":{"d":{"df":0,"docs":{},"n":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}}},"df":1,"docs":{"7":{"tf":1.4142135623730951}}}},"df":0,"docs":{},"o":{"df":0,"docs":{},"t":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}}},"u":{"df":0,"docs":{},"m":{"b":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":2,"docs":{"2":{"tf":1.7320508075688772},"7":{"tf":1.0}}}}},"df":0,"docs":{}}}},"o":{"df":0,"docs":{},"n":{"df":0,"docs":{},"e":{"_":{"d":{"df":0,"docs":{},"v":{"d":{"df":1,"docs":{"8":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"p":{"a":{"df":0,"docs":{},"r":{"a":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}}},"df":0,"docs":{}}},"df":0,"docs":{},"l":{"a":{"df":0,"docs":{},"y":{"df":0,"docs":{},"g":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":0,"docs":{},"u":{"df":0,"docs":{},"n":{"d":{"df":1,"docs":{"1":{"tf":1.4142135623730951}}},"df":0,"docs":{}}}}}}}},"df":0,"docs":{}},"r":{"df":0,"docs":{},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":1,"docs":{"2":{"tf":1.0}}}},"n":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}},"o":{"df":0,"docs":{},"o":{"df":0,"docs":{},"f":{"df":1,"docs":{"2":{"tf":1.0}}}},"p":{"df":1,"docs":{"7":{"tf":1.4142135623730951}}}}},"u":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.0}}}}}},"r":{"df":1,"docs":{"4":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"t":{"df":0,"docs":{},"u":{"df":0,"docs":{},"r":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}}}},"i":{"df":0,"docs":{},"g":{"df":0,"docs":{},"h":{"df":0,"docs":{},"t":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"w":{"df":1,"docs":{"8":{"tf":1.0}}}},"s":{"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}}}},"df":0,"docs":{},"l":{"df":0,"docs":{},"f":{"df":1,"docs":{"7":{"tf":1.0}}}}},"h":{"df":0,"docs":{},"o":{"df":0,"docs":{},"w":{"df":1,"docs":{"8":{"tf":1.0}}}}},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":1,"docs":{"8":{"tf":2.449489742783178}}}}},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":1,"docs":{"9":{"tf":2.0}}}}}},"y":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"df":0,"docs":{},"h":{"df":1,"docs":{"7":{"tf":1.4142135623730951}}}}}}},"t":{"df":0,"docs":{},"h":{"df":0,"docs":{},"e":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"df":1,"docs":{"8":{"tf":2.0}}}},"i":{"df":1,"docs":{"2":{"tf":1.7320508075688772}}}}}}},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}},"y":{"df":0,"docs":{},"p":{"df":0,"docs":{},"e":{"df":1,"docs":{"7":{"tf":2.0}}}}}},"u":{"_":{"1":{"df":1,"docs":{"7":{"tf":1.7320508075688772}}},"df":0,"docs":{}},"df":0,"docs":{},"s":{"df":1,"docs":{"8":{"tf":2.23606797749979}}}},"v":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"a":{"b":{"df":0,"docs":{},"l":{"df":2,"docs":{"7":{"tf":1.0},"9":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}},"x":{"df":2,"docs":{"12":{"tf":2.0},"4":{"tf":1.7320508075688772}},"s":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}},"y":{"df":1,"docs":{"4":{"tf":1.4142135623730951}}},"z":{"df":1,"docs":{"6":{"tf":1.4142135623730951}}}}},"breadcrumbs":{"root":{"0":{"df":3,"docs":{"12":{"tf":1.0},"4":{"tf":2.0},"8":{"tf":2.23606797749979}}},"1":{"1":{"df":1,"docs":{"9":{"tf":1.0}}},"2":{"3":{"4":{"5":{"6":{"7":{"8":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":1,"docs":{"12":{"tf":1.0}}},"8":{"df":1,"docs":{"12":{"tf":1.0}}},"df":7,"docs":{"11":{"tf":1.0},"12":{"tf":1.0},"13":{"tf":2.449489742783178},"3":{"tf":1.0},"7":{"tf":1.0},"8":{"tf":2.0},"9":{"tf":1.0}}},"2":{"0":{"0":{"0":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"2":{"0":{"0":{"df":0,"docs":{},"m":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":3,"docs":{"11":{"tf":1.0},"3":{"tf":1.0},"9":{"tf":1.0}}},"3":{"7":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"4":{"df":1,"docs":{"2":{"tf":1.0}}},"6":{"df":1,"docs":{"12":{"tf":1.0}}},"8":{"7":{"6":{"5":{"4":{"3":{"2":{"1":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"9":{"2":{"df":1,"docs":{"12":{"tf":1.0}}},"df":0,"docs":{}},"a":{"df":0,"docs":{},"l":{"df":0,"docs":{},"g":{"df":0,"docs":{},"e":{"b":{"df":0,"docs":{},"r":{"a":{"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}},"b":{"df":8,"docs":{"11":{"tf":2.449489742783178},"12":{"tf":2.23606797749979},"13":{"tf":1.0},"3":{"tf":1.0},"4":{"tf":2.6457513110645907},"6":{"tf":3.1622776601683795},"8":{"tf":3.4641016151377544},"9":{"tf":2.23606797749979}}},"c":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"e":{"df":1,"docs":{"8":{"tf":1.4142135623730951}}}}},"df":3,"docs":{"4":{"tf":1.0},"8":{"tf":3.4641016151377544},"9":{"tf":2.0}},"h":{"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"k":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"r":{"df":1,"docs":{"8":{"tf":1.0}}}},"df":0,"docs":{}}},"o":{"d":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":0,"docs":{},"o":{"df":0,"docs":{},"n":{"df":2,"docs":{"11":{"tf":1.0},"13":{"tf":1.4142135623730951}}}}},"p":{"df":0,"docs":{},"u":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.4142135623730951}}}}}},"n":{"df":0,"docs":{},"g":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"df":0,"docs":{},"e":{"df":0,"docs":{},"n":{"c":{"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}}}}},"s":{"df":0,"docs":{},"t":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"c":{"df":0,"docs":{},"t":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":2,"docs":{"7":{"tf":1.0},"8":{"tf":1.0}}}}}},"df":0,"docs":{}}}}},"t":{"df":0,"docs":{},"e":{"df":0,"docs":{},"x":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}}}}}}},"d":{"df":1,"docs":{"11":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"f":{"df":1,"docs":{"12":{"tf":1.0}}}},"i":{"df":0,"docs":{},"v":{"df":0,"docs":{},"i":{"df":0,"docs":{},"s":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{")":{"df":0,"docs":{},"と":{"df":0,"docs":{},"い":{"df":0,"docs":{},"い":{"df":0,"docs":{},"ま":{"df":0,"docs":{},"す":{"df":0,"docs":{},"．":{"df":0,"docs":{},"言":{"df":0,"docs":{},"い":{"df":0,"docs":{},"換":{"df":0,"docs":{},"え":{"df":0,"docs":{},"る":{"df":0,"docs":{},"と":{"df":0,"docs":{},"，":{"$":{"d":{"df":1,"docs":{"11":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}}}}}}}},"呼":{"df":0,"docs":{},"ぶ":{"df":0,"docs":{},"こ":{"df":0,"docs":{},"と":{"df":0,"docs":{},"に":{"df":0,"docs":{},"し":{"df":0,"docs":{},"て":{"df":0,"docs":{},"，":{"$":{"\\":{"df":0,"docs":{},"g":{"c":{"d":{"(":{"a":{"df":1,"docs":{"11":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}}}}}},"df":2,"docs":{"13":{"tf":1.7320508075688772},"6":{"tf":1.0}}}}}}}},"v":{"d":{".":{"df":0,"docs":{},"m":{"df":0,"docs":{},"k":{"df":1,"docs":{"7":{"tf":1.0}}}},"{":{"df":0,"docs":{},"u":{"_":{"1":{"df":1,"docs":{"7":{"tf":1.0}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"_":{"df":0,"docs":{},"o":{"df":0,"docs":{},"f":{"_":{"df":0,"docs":{},"m":{"df":0,"docs":{},"u":{"df":0,"docs":{},"l":{"_":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":0,"docs":{},"g":{"df":0,"docs":{},"h":{"df":0,"docs":{},"t":{"_":{"d":{"df":0,"docs":{},"v":{"d":{"df":1,"docs":{"8":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}}},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"f":{"df":0,"docs":{},"l":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"z":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":1,"docs":{"8":{"tf":1.0}}}}}}},"df":1,"docs":{"7":{"tf":2.6457513110645907}}},"df":0,"docs":{}}},"df":0,"docs":{},"e":{"d":{"df":0,"docs":{},"i":{"df":0,"docs":{},"t":{"df":1,"docs":{"1":{"tf":1.0}}}}},"df":0,"docs":{},"l":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":1,"docs":{"2":{"tf":1.0}}}}},"df":0,"docs":{}}}}}}},"u":{"c":{"df":0,"docs":{},"l":{"df":0,"docs":{},"i":{"d":{"df":9,"docs":{"10":{"tf":1.0},"11":{"tf":1.0},"12":{"tf":1.0},"4":{"tf":2.0},"5":{"tf":1.0},"6":{"tf":1.0},"7":{"tf":1.0},"8":{"tf":1.0},"9":{"tf":1.0}}},"df":0,"docs":{}}}},"df":0,"docs":{}},"v":{"a":{"df":0,"docs":{},"l":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}},"x":{"a":{"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":0,"docs":{},"l":{"df":1,"docs":{"9":{"tf":1.7320508075688772}}}}}},"df":0,"docs":{}}},"g":{"c":{"d":{"df":1,"docs":{"12":{"tf":2.23606797749979}}},"df":0,"docs":{}},"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"t":{"df":0,"docs":{},"e":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"df":2,"docs":{"11":{"tf":1.0},"13":{"tf":1.0}}}}}}},"df":0,"docs":{}}},"u":{"a":{"df":0,"docs":{},"r":{"d":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}},"df":0,"docs":{}}},"df":0,"docs":{}}},"h":{"df":2,"docs":{"8":{"tf":1.7320508075688772},"9":{"tf":1.0}},"k":{"df":1,"docs":{"8":{"tf":1.7320508075688772}}}},"i":{"d":{".":{"df":0,"docs":{},"r":{"df":0,"docs":{},"u":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}}},"df":0,"docs":{}},"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"t":{"df":2,"docs":{"1":{"tf":1.0},"3":{"tf":1.0}}}}}}},"n":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"x":{"df":1,"docs":{"13":{"tf":1.7320508075688772}}}},"u":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"d":{"df":0,"docs":{},"v":{"d":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}}},"df":1,"docs":{"7":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"r":{"a":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"r":{"df":0,"docs":{},"o":{"d":{"df":0,"docs":{},"u":{"c":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"df":1,"docs":{"8":{"tf":1.0}}}}}}},"k":{"df":1,"docs":{"8":{"tf":2.23606797749979}}},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"n":{"4":{"df":1,"docs":{"2":{"tf":1.0}}},"df":6,"docs":{"0":{"tf":2.449489742783178},"1":{"tf":2.0},"12":{"tf":1.4142135623730951},"2":{"tf":2.23606797749979},"3":{"tf":1.4142135623730951},"7":{"tf":1.7320508075688772}}}},"df":0,"docs":{},"f":{"df":0,"docs":{},"t":{"df":1,"docs":{"8":{"tf":1.0}}}}},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"d":{"c":{"df":0,"docs":{},"o":{"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":0,"docs":{},"r":{"df":1,"docs":{"3":{"tf":1.0}}}}}}},"df":0,"docs":{}},"df":0,"docs":{}}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}}},"s":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"r":{"a":{"df":0,"docs":{},"n":{"df":0,"docs":{},"g":{"df":1,"docs":{"12":{"tf":1.0}}}}},"df":0,"docs":{},"e":{"df":0,"docs":{},"v":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":0,"docs":{},"s":{"df":1,"docs":{"12":{"tf":1.0}}}}}}}}},"df":0,"docs":{}}}}},"m":{"a":{"df":0,"docs":{},"t":{"df":0,"docs":{},"h":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"l":{"df":0,"docs":{},"i":{"b":{".":{"d":{"a":{"df":0,"docs":{},"t":{"a":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{".":{"b":{"a":{"df":0,"docs":{},"s":{"df":1,"docs":{"3":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}},"/":{"d":{"a":{"df":0,"docs":{},"t":{"a":{"/":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"/":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"/":{"b":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"i":{"c":{".":{"df":0,"docs":{},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"n":{"df":1,"docs":{"3":{"tf":1.0}}}},"df":0,"docs":{}}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}}}},"df":0,"docs":{}}}}},"df":0,"docs":{}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}},"df":1,"docs":{"2":{"tf":1.0}}},"df":0,"docs":{}}}}}},"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"h":{"a":{"df":0,"docs":{},"n":{"df":1,"docs":{"2":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{}},"i":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.0}}}},"u":{"df":0,"docs":{},"l":{"_":{"a":{"df":0,"docs":{},"s":{"df":0,"docs":{},"s":{"df":0,"docs":{},"o":{"c":{"df":1,"docs":{"8":{"tf":1.4142135623730951}}},"df":0,"docs":{}}}}},"c":{"df":0,"docs":{},"o":{"df":0,"docs":{},"m":{"df":0,"docs":{},"m":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"df":0,"docs":{}},"df":0,"docs":{},"t":{"df":0,"docs":{},"i":{"df":0,"docs":{},"p":{"df":0,"docs":{},"l":{"df":2,"docs":{"13":{"tf":1.0},"6":{"tf":1.0}}}}}}}}},"n":{"a":{"df":0,"docs":{},"t":{".":{"df":0,"docs":{},"i":{"df":0,"docs":{},"n":{"df":0,"docs":{},"s":{"df":0,"docs":{},"t":{"d":{"df":0,"docs":{},"v":{"d":{"df":0,"docs":{},"n":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}},"df":0,"docs":{}}},"df":0,"docs":{}}},"df":0,"docs":{}}}}}},"df":1,"docs":{"7":{"tf":1.4142135623730951}}}},"df":0,"docs":{},"o":{"df":0,"docs":{},"t":{"a":{"df":0,"docs":{},"t":{"df":1,"docs":{"12":{"tf":1.0}}}},"df":0,"docs":{}}},"u":{"df":0,"docs":{},"m":{"b":{"df":0,"docs":{},"e":{"df":0,"docs":{},"r":{"df":2,"docs":{"2":{"tf":1.7320508075688772},"7":{"tf":1.0}}}}},"df":0,"docs":{}}}},"o":{"df":0,"docs":{},"n":{"df":0,"docs":{},"e":{"_":{"d":{"df":0,"docs":{},"v":{"d":{"df":1,"docs":{"8":{"tf":1.0}}},"df":0,"docs":{}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"p":{"a":{"df":0,"docs":{},"r":{"a":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}}},"df":0,"docs":{}}},"df":0,"docs":{},"l":{"a":{"df":0,"docs":{},"y":{"df":0,"docs":{},"g":{"df":0,"docs":{},"r":{"df":0,"docs":{},"o":{"df":0,"docs":{},"u":{"df":0,"docs":{},"n":{"d":{"df":1,"docs":{"1":{"tf":1.4142135623730951}}},"df":0,"docs":{}}}}}}}},"df":0,"docs":{}},"r":{"df":0,"docs":{},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":1,"docs":{"2":{"tf":1.0}}}},"n":{"df":0,"docs":{},"t":{"df":1,"docs":{"7":{"tf":1.0}}}}},"o":{"df":0,"docs":{},"o":{"df":0,"docs":{},"f":{"df":1,"docs":{"2":{"tf":1.0}}}},"p":{"df":1,"docs":{"7":{"tf":1.4142135623730951}}}}},"u":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.0}}}}}},"r":{"df":1,"docs":{"4":{"tf":1.4142135623730951}},"e":{"df":0,"docs":{},"t":{"df":0,"docs":{},"u":{"df":0,"docs":{},"r":{"df":0,"docs":{},"n":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}}}},"i":{"df":0,"docs":{},"g":{"df":0,"docs":{},"h":{"df":0,"docs":{},"t":{"df":1,"docs":{"8":{"tf":1.0}}}}}},"w":{"df":1,"docs":{"8":{"tf":1.0}}}},"s":{"df":0,"docs":{},"e":{"c":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"t":{"df":1,"docs":{"2":{"tf":1.0}}}}}},"df":0,"docs":{},"l":{"df":0,"docs":{},"f":{"df":1,"docs":{"7":{"tf":1.0}}}}},"h":{"df":0,"docs":{},"o":{"df":0,"docs":{},"w":{"df":1,"docs":{"8":{"tf":1.0}}}}},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"p":{"df":1,"docs":{"8":{"tf":2.449489742783178}}}}},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"df":1,"docs":{"9":{"tf":2.0}}}}}},"y":{"df":0,"docs":{},"n":{"df":0,"docs":{},"t":{"df":0,"docs":{},"h":{"df":1,"docs":{"7":{"tf":1.4142135623730951}}}}}}},"t":{"df":0,"docs":{},"h":{"df":0,"docs":{},"e":{"df":0,"docs":{},"o":{"df":0,"docs":{},"r":{"df":0,"docs":{},"e":{"df":0,"docs":{},"m":{"df":1,"docs":{"8":{"tf":2.0}}}},"i":{"df":1,"docs":{"2":{"tf":1.7320508075688772}}}}}}},"i":{"df":0,"docs":{},"m":{"df":0,"docs":{},"e":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}}},"y":{"df":0,"docs":{},"p":{"df":0,"docs":{},"e":{"df":1,"docs":{"7":{"tf":2.0}}}}}},"u":{"_":{"1":{"df":1,"docs":{"7":{"tf":1.7320508075688772}}},"df":0,"docs":{}},"df":0,"docs":{},"s":{"df":1,"docs":{"8":{"tf":2.23606797749979}}}},"v":{"a":{"df":0,"docs":{},"r":{"df":0,"docs":{},"i":{"a":{"b":{"df":0,"docs":{},"l":{"df":2,"docs":{"7":{"tf":1.0},"9":{"tf":1.0}}}},"df":0,"docs":{}},"df":0,"docs":{}}}},"df":0,"docs":{}},"x":{"df":2,"docs":{"12":{"tf":2.0},"4":{"tf":1.7320508075688772}},"s":{"df":1,"docs":{"12":{"tf":1.4142135623730951}}}},"y":{"df":1,"docs":{"4":{"tf":1.4142135623730951}}},"z":{"df":1,"docs":{"6":{"tf":1.4142135623730951}}}}},"title":{"root":{"df":0,"docs":{},"e":{"df":0,"docs":{},"u":{"c":{"df":0,"docs":{},"l":{"df":0,"docs":{},"i":{"d":{"df":1,"docs":{"4":{"tf":1.0}}},"df":0,"docs":{}}}},"df":0,"docs":{}}},"i":{"df":0,"docs":{},"n":{"d":{"df":0,"docs":{},"e":{"df":0,"docs":{},"x":{"df":1,"docs":{"13":{"tf":1.0}}}}},"df":0,"docs":{}}},"l":{"df":0,"docs":{},"e":{"a":{"df":0,"docs":{},"n":{"df":3,"docs":{"0":{"tf":1.0},"12":{"tf":1.0},"7":{"tf":1.0}}}},"df":0,"docs":{}}}}}},"lang":"English","pipeline":["trimmer","stopWordFilter","stemmer"],"ref":"id","version":"0.9.5"},"results_options":{"limit_results":30,"teaser_word_count":30},"search_options":{"bool":"OR","expand":true,"fields":{"body":{"boost":1},"breadcrumbs":{"boost":1},"title":{"boost":2}}}});