module d5.nice_word where

open import Data.Bool.Base using (if_then_else_ ; _∧_ ; not)
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

record WordQual : Set where
  field
    v_count : Nat
    contains_a : Bool
    contains_e : Bool
    contains_i : Bool
    contains_o : Bool
    contains_u : Bool
    contains_double : Bool
    contains_forbidden : Bool

default_qual : WordQual
default_qual = record {
  v_count = 0 ;
  contains_a = false ;
  contains_e = false ;
  contains_i = false ;
  contains_o = false ;
  contains_u = false ;
  contains_double = false ;
  contains_forbidden = false
  }

add_a : WordQual -> WordQual
add_a old = record {
  v_count = WordQual.v_count old + 1 ;
  contains_a = true ;
  contains_e = WordQual.contains_e old ;
  contains_i = WordQual.contains_i old ;
  contains_o = WordQual.contains_o old ;
  contains_u = WordQual.contains_u old ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = WordQual.contains_forbidden old 
  }

add_e : WordQual -> WordQual
add_e old = record {
  v_count = WordQual.v_count old + 1 ;
  contains_a = WordQual.contains_a old ;
  contains_e = true ;
  contains_i = WordQual.contains_i old ;
  contains_o = WordQual.contains_o old ;
  contains_u = WordQual.contains_u old ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = WordQual.contains_forbidden old 
  }
  
add_i : WordQual -> WordQual
add_i old = record {
  v_count = WordQual.v_count old + 1 ;
  contains_a = WordQual.contains_a old ;
  contains_e = WordQual.contains_e old ;
  contains_i = true ;
  contains_o = WordQual.contains_o old ;
  contains_u = WordQual.contains_u old ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = WordQual.contains_forbidden old 
  }

add_o : WordQual -> WordQual
add_o old = record {
  v_count = WordQual.v_count old + 1 ;
  contains_a = WordQual.contains_a old ;
  contains_e = WordQual.contains_e old ;
  contains_i = WordQual.contains_i old ;
  contains_o = true ;
  contains_u = WordQual.contains_u old ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = WordQual.contains_forbidden old 
  }

add_u : WordQual -> WordQual
add_u old = record {
  v_count = WordQual.v_count old + 1 ;
  contains_a = WordQual.contains_a old ;
  contains_e = WordQual.contains_e old ;
  contains_i = WordQual.contains_i old ;
  contains_o = WordQual.contains_o old ;
  contains_u = true ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = WordQual.contains_forbidden old 
  }

add_double : WordQual -> WordQual
add_double old = record {
  v_count = WordQual.v_count old ;
  contains_a = WordQual.contains_a old ;
  contains_e = WordQual.contains_e old ;
  contains_i = WordQual.contains_i old ;
  contains_o = WordQual.contains_o old ;
  contains_u = WordQual.contains_u old  ;
  contains_double = true ;
  contains_forbidden = WordQual.contains_forbidden old 
  }

add_forb : WordQual -> WordQual
add_forb old = record {
  v_count = WordQual.v_count old ;
  contains_a = WordQual.contains_a old ;
  contains_e = WordQual.contains_e old ;
  contains_i = WordQual.contains_i old ;
  contains_o = WordQual.contains_o old ;
  contains_u = WordQual.contains_u old  ;
  contains_double = WordQual.contains_double old ;
  contains_forbidden = true
  }

n_bool : Bool → Nat
n_bool true = 1
n_bool false = 0

show_wq : WordQual -> String
show_wq qual = 
  show (WordQual.v_count qual) ++ " " ++
  (show (n_bool (WordQual.contains_a qual))) ++ " " ++ 
  (show (n_bool (WordQual.contains_e qual))) ++ " " ++
  (show (n_bool (WordQual.contains_i qual))) ++ " " ++
  (show (n_bool (WordQual.contains_o qual))) ++ " " ++
  (show (n_bool (WordQual.contains_u qual))) ++ " " ++
  (show (n_bool (WordQual.contains_double qual))) ++ " " ++
  (show (n_bool (WordQual.contains_forbidden qual)))

three_vowel : WordQual → Bool
three_vowel qual = 2 < WordQual.v_count qual

is_nice : WordQual → Bool
is_nice qual = (three_vowel qual) ∧ (WordQual.contains_double qual) ∧ not (WordQual.contains_forbidden qual)

update_double : Char → Char → WordQual → WordQual
update_double 'a' 'a' old = add_a (add_double old)
update_double 'a' 'b' old = add_a (add_forb old)
update_double 'c' 'd' old = add_forb old
update_double 'p' 'q' old = add_forb old
update_double 'x' 'y' old = add_forb old
update_double 'a' _ old = add_a old
update_double 'e' 'e' old = add_e (add_double old)
update_double 'e' _ old = add_e old
update_double 'i' 'i' old = add_i (add_double old)
update_double 'i' _ old = add_i old
update_double 'o' 'o' old = add_o (add_double old)
update_double 'o' _ old = add_o old
update_double 'u' 'u' old = add_u (add_double old)
update_double 'u' _ old = add_u old
update_double a b old = if a == b then (add_double old) else old

eval_word : List Char → WordQual → WordQual
eval_word [] old = old
eval_word (x ∷ []) old = update_double x ' ' old 
eval_word (l ∷ r ∷ xs) old = eval_word (r ∷ xs) (update_double l r old)

judge_word : List Char → Nat
judge_word x = n_bool (is_nice (eval_word x default_qual))

judge_words : String → String
judge_words x = show (foldr _+_ 0 (map judge_word (find_parts '\n' (primStringToList x)))) ++ "\n"
