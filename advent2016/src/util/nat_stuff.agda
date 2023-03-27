
module util.nat_stuff where

open import Agda.Builtin.Nat using (Nat ; suc ; div-helper ; mod-helper ; _+_ ; _-_ ; _*_ ; _<_ ; _==_)
open import Data.Nat using (pred)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using () renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)

non-negify : Int → Nat
non-negify (pos x) = x
non-negify _ = 0


max : Nat → Nat → Nat
max a b = if a < b then b else a

div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)

private
  gcd-h : Nat → Nat → Nat → Nat
  gcd-h _ 0 x = x
  gcd-h _ x 0 = x
  gcd-h _ 1 _ = 1
  gcd-h _ _ 1 = 1
  gcd-h 0 _ _ = 0
  gcd-h (suc lm) a b with (a == b)
  gcd-h (suc lm) a b | true = a
  gcd-h (suc lm) a b | false = gcd-h lm b (mod-nat a b)

gcd : Nat → Nat → Nat
gcd a b = gcd-h (max a b) a b

private

  min-xy-sol-h : Nat → Nat → Nat → Nat → Int → Maybe Nat
  min-xy-sol-h 0 _ _ _ _ = nothing
  min-xy-sol-h (suc lm) y a b c with ((0 < non-negify(pos (b * y) +z c)) ∧ (mod-nat (non-negify (pos a +z pos (b * y) +z c)) a == 0))
  min-xy-sol-h (suc lm) y a b c | true = just y
  min-xy-sol-h (suc lm) y a b c | false = min-xy-sol-h lm (suc y) a b c

-- min x,y in `a*x = b*y + c`
min-xy-sol : Nat → Nat → Int → Maybe (Nat × Nat)
min-xy-sol a b c = output
  where
    ym : Maybe Nat
    ym = min-xy-sol-h (suc (a * b)) 0 a b c
    output : Maybe (Nat × Nat)
    output with ym
    output | nothing = nothing
    output | (just y) = just (div-nat (non-negify (pos(b * y) +z c)) a , y)

-- finding min non-negative n for `a + n ≡ b (mod x)` and `d + n ≡ e (mod y)` 
lin-mod-system : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Maybe Nat
lin-mod-system (a , b , x) (d , e , y) with (min-xy-sol x y (pos (a + e) -z pos b -z pos d))
lin-mod-system (a , b , x) (d , e , y) | nothing = nothing
lin-mod-system (a , b , x) (d , e , y) | (just (q , r)) = just (mod-nat (b + x * q - a) (div-nat (x * y) (gcd x y)))

test-min-xy-sol-a : (min-xy-sol 5 2 (negsuc 0)) ≡ just (1 , 3)
test-min-xy-sol-a = refl

test-min-xy-sol-b : (min-xy-sol 2 5 (negsuc 0)) ≡ just (2 , 1)
test-min-xy-sol-b = refl

test-min-xy-sol-c : (min-xy-sol 10 3 (negsuc 5)) ≡ just (3 , 12)
test-min-xy-sol-c = refl

test-gcd-a : gcd 3 7 ≡ 1
test-gcd-a = refl

test-gcd-b : gcd 10 15 ≡ 5
test-gcd-b = refl

test-lin-mod-a : lin-mod-system (4 , 9 , 10) (1 , 0 , 3) ≡ just 5
test-lin-mod-a = refl

test-lin-mod-b : lin-mod-system (4 , 4 , 5) (1 , 0 , 2) ≡ just 5
test-lin-mod-b = refl

test-lin-mod-c : lin-mod-system (1 , 1 , 2) (1 , 1 , 3) ≡ just 0
test-lin-mod-c = refl

