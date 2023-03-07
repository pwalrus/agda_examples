module d3.robo_moves where

open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.List using (List ; _∷_ ; [])

open import Agda.Builtin.String using (String ; primStringToList ; primStringFromList)
open import Data.String.Base using (_++_)
open import d3.moves using (start-loc ; add-all-moves ; list-len ; Location ; unique-insert-loc)
open import Agda.Builtin.Equality using (refl ; _≡_)

record ListPair : Set where
   field
     lhs : List Char
     rhs : List Char

show-pair : ListPair → String
show-pair p = primStringFromList (ListPair.lhs p) ++ ";" ++ primStringFromList (ListPair.rhs p)


add-two : Char -> Char -> ListPair -> ListPair
add-two l r pair = record {
   lhs = l ∷ (ListPair.lhs pair) ;
   rhs = r ∷ (ListPair.rhs pair) }

split-list : List Char → ListPair
split-list [] = record { lhs = [] ; rhs = [] }
split-list (l ∷ []) = record { lhs = l ∷ [] ; rhs = [] }
split-list (l ∷ r ∷ xs) = add-two l r (split-list xs)

merge-unique : List Location → List Location → List Location
merge-unique a [] = a
merge-unique a (x ∷ xs) = merge-unique (unique-insert-loc a x) xs

run-two-sides : ListPair -> List Location
run-two-sides x = merge-unique (add-all-moves (ListPair.lhs x) start-loc (start-loc ∷ [])) (add-all-moves (ListPair.rhs x) start-loc (start-loc ∷ []))

calc-unique-loc-b : String → String
calc-unique-loc-b x = show (list-len (run-two-sides (split-list (primStringToList x))))
