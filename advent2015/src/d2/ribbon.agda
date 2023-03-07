module d2.ribbon where

open import Data.Bool.Base using (if_then_else_)
open import Data.List using (List ; foldr ; map ; [] ; _∷_)
open import Agda.Builtin.Nat using (Nat ; _+_ ; _*_ ; suc ; _<_)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList)

open import d2.boxes using (nat-parts ; find-parts)
open import Agda.Builtin.Equality using (refl ; _≡_)


merge-smallest : Nat → List Nat → Nat → List Nat
merge-smallest 0 _ _ = []
merge-smallest (suc n) [] p = p ∷ []
merge-smallest (suc n) (x ∷ xs) p = if p < x
  then (p ∷ (merge-smallest n xs x))
  else (x ∷ (merge-smallest n xs p))

min-two-helper : List Nat → List Nat → List Nat
min-two-helper found [] = found
min-two-helper found (x ∷ xs) = min-two-helper (merge-smallest 2 found x) xs

min-two : List Nat → List Nat
min-two lst = min-two-helper [] lst

calc-param : List Nat → Nat
calc-param lst =  2 * (foldr _+_ 0 (min-two lst))


calc-bow : List Nat -> Nat
calc-bow x = foldr _*_ 1 x

combine-parts : List Nat → Nat
combine-parts parts = (calc-bow parts) + (calc-param parts)

parse-and-calc : List Char → Nat
parse-and-calc x = combine-parts ( nat-parts ( find-parts 'x' x)) 

parse-and-calc-all : String → Nat
parse-and-calc-all inp = foldr _+_ 0 (map parse-and-calc (find-parts '\n' (primStringToList inp)))


calc-ribbon : String → String
calc-ribbon x = show (parse-and-calc-all x)

test-calc-ribbon-a : parse-and-calc (primStringToList "2x3x4") ≡ 34
test-calc-ribbon-a = refl

test-calc-ribbon-b : parse-and-calc (primStringToList "1x1x10") ≡ 14
test-calc-ribbon-b = refl
