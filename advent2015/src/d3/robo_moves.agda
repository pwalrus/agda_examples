module d3.robo_moves where

open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.List using (List ; _∷_ ; [])

open import Agda.Builtin.String using (String ; primStringToList ; primStringFromList)
open import Data.String.Base using (_++_)
open import d3.moves using (start_loc ; add_all_moves ; list_len ; Location ; unique_insert_loc)


record ListPair : Set where
   field
     lhs : List Char
     rhs : List Char

show_pair : ListPair → String
show_pair p = primStringFromList (ListPair.lhs p) ++ ";" ++ primStringFromList (ListPair.rhs p)


add_two : Char -> Char -> ListPair -> ListPair
add_two l r pair = record {
   lhs = l ∷ (ListPair.lhs pair) ;
   rhs = r ∷ (ListPair.rhs pair) }

split_list : List Char → ListPair
split_list [] = record { lhs = [] ; rhs = [] }
split_list (l ∷ []) = record { lhs = l ∷ [] ; rhs = [] }
split_list (l ∷ r ∷ xs) = add_two l r (split_list xs)

merge_unique : List Location → List Location → List Location
merge_unique a [] = a
merge_unique a (x ∷ xs) = merge_unique (unique_insert_loc a x) xs

run_two_sides : ListPair -> List Location
run_two_sides x = merge_unique (add_all_moves (ListPair.lhs x) start_loc (start_loc ∷ [])) (add_all_moves (ListPair.rhs x) start_loc (start_loc ∷ []))

calc_unique_loc : String → String
calc_unique_loc x = show (list_len (run_two_sides (split_list (primStringToList x))))
