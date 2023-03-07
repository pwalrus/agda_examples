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
open import util.list_stuff using (find-parts)
open import d5.nice_word using (n-bool)

record WordQual : Set where
  field
    has-dd : Bool
    has-rep : Bool

default-qual : WordQual
default-qual = record {
  has-dd = false ;
  has-rep = false
  }

add-dd : WordQual -> WordQual
add-dd old = record {
  has-dd = true ;
  has-rep = WordQual.has-rep old 
  }

add-rep : WordQual -> WordQual
add-rep old = record {
  has-dd = WordQual.has-dd old ;
  has-rep = true
  }

show-wq : WordQual -> String
show-wq qual = 
  (show (n-bool (WordQual.has-dd qual))) ++ ";" ++ 
  (show (n-bool (WordQual.has-rep qual))) ++ " "

is-nice : WordQual → Bool
is-nice qual = (WordQual.has-dd qual) ∧ (WordQual.has-rep qual)

check-dd-help : Char → Char → List Char → Bool
check-dd-help _ _ [] = false
check-dd-help _ _ (x ∷ []) = false
check-dd-help a b (l ∷ r ∷ xs) = ((a == l) ∧ (b == r)) ∨ check-dd-help a b (r ∷ xs)

check-dd : List Char → Bool
check-dd [] = false
check-dd (x ∷ []) = false
check-dd (l ∷ r ∷ xs) = (check-dd-help l r xs) ∨ check-dd (r ∷ xs)

check-rep : List Char → Bool
check-rep [] = false
check-rep (x ∷ []) = false
check-rep (a ∷ b ∷ []) = false
check-rep (a ∷ b ∷ c ∷ xs) = (a == c) ∨ check-rep (b ∷ c ∷ xs)

eval-word : List Char → WordQual
eval-word x = record {has-dd = check-dd x ; has-rep = check-rep x}

judge-word : List Char → Nat
judge-word x = n-bool (is-nice (eval-word x))

judge-words-b : String → String
judge-words-b x = show (foldr _+_ 0 (map judge-word (find-parts '\n' (primStringToList x)))) ++ "\n"
