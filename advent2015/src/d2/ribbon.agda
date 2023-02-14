module d2.ribbon where

open import Data.Bool.Base using (if_then_else_)
open import Data.List using (List ; foldr ; map ; [] ; _∷_)
open import Agda.Builtin.Nat using (Nat ; _+_ ; _*_ ; suc ; _<_)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList)

open import d2.boxes using (nat_parts ; find_parts)

merge_smallest : Nat → List Nat → Nat → List Nat
merge_smallest 0 _ _ = []
merge_smallest (suc n) [] p = p ∷ []
merge_smallest (suc n) (x ∷ xs) p = if p < x
  then (p ∷ (merge_smallest n xs x))
  else (x ∷ (merge_smallest n xs p))

min_two_helper : List Nat → List Nat → List Nat
min_two_helper found [] = found
min_two_helper found (x ∷ xs) = min_two_helper (merge_smallest 2 found x) xs

min_two : List Nat → List Nat
min_two lst = min_two_helper [] lst

calc_param : List Nat → Nat
calc_param lst =  2 * (foldr _+_ 0 (min_two lst))


calc_bow : List Nat -> Nat
calc_bow x = foldr _*_ 1 x

combine_parts : List Nat → Nat
combine_parts parts = (calc_bow parts) + (calc_param parts)

parse_and_calc : List Char → Nat
parse_and_calc x = combine_parts ( nat_parts ( find_parts 'x' x)) 

parse_and_calc_all : String → Nat
parse_and_calc_all inp = foldr _+_ 0 (map parse_and_calc (find_parts '\n' (primStringToList inp)))


calc_ribbon : String → String
calc_ribbon x = show (parse_and_calc_all x)
