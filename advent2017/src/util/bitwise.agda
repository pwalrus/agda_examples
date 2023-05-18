
module util.bitwise where

open import util.nat_stuff using (div-nat ; mod-nat)
open import Agda.Builtin.Nat using (Nat ; _-_ ; _*_)
open import Data.Nat using (suc ; pred ; _+_)
open import Agda.Builtin.Bool using (Bool)
open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; map ; replicate ; concat ; applyUpTo ; length ; reverse ; zip ; foldr)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_ ; intersperse ; toList)
open import Data.Product using (uncurry)
open import Function using (_∘_ ; const)
open import Agda.Builtin.Equality using (refl ; _≡_)


pad-bits : List Bool → List Bool
pad-bits xs = concat (xs ∷ (applyUpTo (const false) needed) ∷ [])
  where
    needed : Nat
    needed = (32 - length xs)
 
to-bool : Nat → Bool
to-bool 0 = false
to-bool _ = true

to-nat : Bool → Nat
to-nat false = 0
to-nat true = 1

show-bool : Bool → String
show-bool false = "0"
show-bool true = "1"

show-b-list : List Bool → String
show-b-list = intersperse "" ∘ map show-bool

to-bin-h : Nat → Nat → List Bool
to-bin-h 0 _ = []
to-bin-h _ 0 = []
to-bin-h (suc lm) x = (to-bool rem) ∷ to-bin-h lm (div-nat x 2)
  where
    rem : Nat
    rem = mod-nat x 2

to-bin : Nat → List Bool
to-bin 0 = pad-bits []
to-bin x = pad-bits (to-bin-h x x)

private 
  from-bin-h : Nat → List Bool → Nat
  from-bin-h y [] = y
  from-bin-h y (x ∷ xs) = from-bin-h (2 * y + (to-nat x)) xs

from-bin : List Bool → Nat
from-bin xs = from-bin-h 0 (reverse xs)

xor : Bool → Bool → Bool
xor false false = false
xor true false = true
xor false true = true
xor true true = false

bitwise-xor : Nat → Nat → Nat
bitwise-xor a b = (from-bin ∘ map (uncurry xor)) (zip lhs rhs)
  where
    lhs : List Bool
    lhs = to-bin a
    rhs : List Bool
    rhs = to-bin b

from-hex : Char → List Bool
from-hex '0' = false ∷ false ∷ false ∷ false ∷ []
from-hex '1' = false ∷ false ∷ false ∷ true ∷ []
from-hex '2' = false ∷ false ∷ true ∷ false ∷ []
from-hex '3' = false ∷ false ∷ true ∷ true ∷ []
from-hex '4' = false ∷ true ∷ false ∷ false ∷ []
from-hex '5' = false ∷ true ∷ false ∷ true ∷ []
from-hex '6' = false ∷ true ∷ true ∷ false ∷ []
from-hex '7' = false ∷ true ∷ true ∷ true ∷ []
from-hex '8' = true ∷ false ∷ false ∷ false ∷ []
from-hex '9' = true ∷ false ∷ false ∷ true ∷ []
from-hex 'a' = true ∷ false ∷ true ∷ false ∷ []
from-hex 'b' = true ∷ false ∷ true ∷ true ∷ []
from-hex 'c' = true ∷ true ∷ false ∷ false ∷ []
from-hex 'd' = true ∷ true ∷ false ∷ true ∷ []
from-hex 'e' = true ∷ true ∷ true ∷ false ∷ []
from-hex 'f' = true ∷ true ∷ true ∷ true ∷ []
from-hex _ = []

from-hex-str : String → List Bool
from-hex-str = concat ∘ map from-hex ∘ toList



test-from-bin-a : from-bin (false ∷ true ∷ true ∷ true ∷ false ∷ false ∷ []) ≡ 14
test-from-bin-a = refl

test-from-bin-b : (from-bin ∘ to-bin) 25 ≡ 25
test-from-bin-b = refl

test-bitwise-xor-a : bitwise-xor 9 10 ≡ 3
test-bitwise-xor-a = refl

test-bitwise-xor-b : bitwise-xor 0 65  ≡ 65
test-bitwise-xor-b = refl

test-bitwise-xor-c : foldr bitwise-xor 0 (65 ∷ 27 ∷ 9 ∷ 1 ∷ 4 ∷ 3 ∷ 40 ∷ 50 ∷ 91 ∷ 7 ∷ 6 ∷ 0 ∷ 2 ∷ 5 ∷ 68 ∷ 22 ∷ []) ≡ 64
test-bitwise-xor-c = refl

test-from-hex : (intersperse "" ∘ map show-bool ∘ from-hex-str) "a0c2" ≡ "1010000011000010"
test-from-hex = refl
