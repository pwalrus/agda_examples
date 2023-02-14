module d5.more_word where

open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List using (foldr; map)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; _<_ ; _+_)
open import Data.Nat.Show using (show)
open import Agda.Builtin.String using (String ; primStringToList ; primStringFromList)
open import Data.String using (_++_)
open import Agda.Builtin.Bool using (Bool ; true; false)
open import d2.boxes using (find_parts)
open import d5.nice_word using (n_bool)

record WordQual : Set where
  field
    has_dd : Bool
    has_rep : Bool

default_qual : WordQual
default_qual = record {
  has_dd = false ;
  has_rep = false
  }

add_dd : WordQual -> WordQual
add_dd old = record {
  has_dd = true ;
  has_rep = WordQual.has_rep old 
  }

add_rep : WordQual -> WordQual
add_rep old = record {
  has_dd = WordQual.has_dd old ;
  has_rep = true
  }

show_wq : WordQual -> String
show_wq qual = 
  (show (n_bool (WordQual.has_dd qual))) ++ ";" ++ 
  (show (n_bool (WordQual.has_rep qual))) ++ " "

is_nice : WordQual → Bool
is_nice qual = (WordQual.has_dd qual) ∧ (WordQual.has_rep qual)

check_dd_help : Char → Char → List Char → Bool
check_dd_help _ _ [] = false
check_dd_help _ _ (x ∷ []) = false
check_dd_help a b (l ∷ r ∷ xs) = ((a == l) ∧ (b == r)) ∨ check_dd_help a b (r ∷ xs)

check_dd : List Char → Bool
check_dd [] = false
check_dd (x ∷ []) = false
check_dd (l ∷ r ∷ xs) = (check_dd_help l r xs) ∨ check_dd (r ∷ xs)

check_rep : List Char → Bool
check_rep [] = false
check_rep (x ∷ []) = false
check_rep (a ∷ b ∷ []) = false
check_rep (a ∷ b ∷ c ∷ xs) = (a == c) ∨ check_rep (b ∷ c ∷ xs)

eval_word : List Char → WordQual
eval_word x = record {has_dd = check_dd x ; has_rep = check_rep x}

judge_word : List Char → Nat
judge_word x = n_bool (is_nice (eval_word x))

judge_words : String → String
judge_words x = show (foldr _+_ 0 (map judge_word (find_parts '\n' (primStringToList x)))) ++ "\n"
