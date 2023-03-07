module d5.nice_word where

open import util.list_stuff using (find-parts)
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
open import Agda.Builtin.Equality using (refl ; _≡_)

record WordQual : Set where
  field
    v-count : Nat
    contains-a : Bool
    contains-e : Bool
    contains-i : Bool
    contains-o : Bool
    contains-u : Bool
    contains-double : Bool
    contains-forbidden : Bool

default-qual : WordQual
default-qual = record {
  v-count = 0 ;
  contains-a = false ;
  contains-e = false ;
  contains-i = false ;
  contains-o = false ;
  contains-u = false ;
  contains-double = false ;
  contains-forbidden = false
  }

add-a : WordQual -> WordQual
add-a old = record {
  v-count = WordQual.v-count old + 1 ;
  contains-a = true ;
  contains-e = WordQual.contains-e old ;
  contains-i = WordQual.contains-i old ;
  contains-o = WordQual.contains-o old ;
  contains-u = WordQual.contains-u old ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = WordQual.contains-forbidden old 
  }

add-e : WordQual -> WordQual
add-e old = record {
  v-count = WordQual.v-count old + 1 ;
  contains-a = WordQual.contains-a old ;
  contains-e = true ;
  contains-i = WordQual.contains-i old ;
  contains-o = WordQual.contains-o old ;
  contains-u = WordQual.contains-u old ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = WordQual.contains-forbidden old 
  }
  
add-i : WordQual -> WordQual
add-i old = record {
  v-count = WordQual.v-count old + 1 ;
  contains-a = WordQual.contains-a old ;
  contains-e = WordQual.contains-e old ;
  contains-i = true ;
  contains-o = WordQual.contains-o old ;
  contains-u = WordQual.contains-u old ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = WordQual.contains-forbidden old 
  }

add-o : WordQual -> WordQual
add-o old = record {
  v-count = WordQual.v-count old + 1 ;
  contains-a = WordQual.contains-a old ;
  contains-e = WordQual.contains-e old ;
  contains-i = WordQual.contains-i old ;
  contains-o = true ;
  contains-u = WordQual.contains-u old ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = WordQual.contains-forbidden old 
  }

add-u : WordQual -> WordQual
add-u old = record {
  v-count = WordQual.v-count old + 1 ;
  contains-a = WordQual.contains-a old ;
  contains-e = WordQual.contains-e old ;
  contains-i = WordQual.contains-i old ;
  contains-o = WordQual.contains-o old ;
  contains-u = true ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = WordQual.contains-forbidden old 
  }

add-double : WordQual -> WordQual
add-double old = record {
  v-count = WordQual.v-count old ;
  contains-a = WordQual.contains-a old ;
  contains-e = WordQual.contains-e old ;
  contains-i = WordQual.contains-i old ;
  contains-o = WordQual.contains-o old ;
  contains-u = WordQual.contains-u old  ;
  contains-double = true ;
  contains-forbidden = WordQual.contains-forbidden old 
  }

add-forb : WordQual -> WordQual
add-forb old = record {
  v-count = WordQual.v-count old ;
  contains-a = WordQual.contains-a old ;
  contains-e = WordQual.contains-e old ;
  contains-i = WordQual.contains-i old ;
  contains-o = WordQual.contains-o old ;
  contains-u = WordQual.contains-u old  ;
  contains-double = WordQual.contains-double old ;
  contains-forbidden = true
  }

n-bool : Bool → Nat
n-bool true = 1
n-bool false = 0

show-wq : WordQual -> String
show-wq qual = 
  show (WordQual.v-count qual) ++ " " ++
  (show (n-bool (WordQual.contains-a qual))) ++ " " ++ 
  (show (n-bool (WordQual.contains-e qual))) ++ " " ++
  (show (n-bool (WordQual.contains-i qual))) ++ " " ++
  (show (n-bool (WordQual.contains-o qual))) ++ " " ++
  (show (n-bool (WordQual.contains-u qual))) ++ " " ++
  (show (n-bool (WordQual.contains-double qual))) ++ " " ++
  (show (n-bool (WordQual.contains-forbidden qual)))

three-vowel : WordQual → Bool
three-vowel qual = 2 < WordQual.v-count qual

is-nice : WordQual → Bool
is-nice qual = (three-vowel qual) ∧ (WordQual.contains-double qual) ∧ not (WordQual.contains-forbidden qual)

update-double : Char → Char → WordQual → WordQual
update-double 'a' 'a' old = add-a (add-double old)
update-double 'a' 'b' old = add-a (add-forb old)
update-double 'c' 'd' old = add-forb old
update-double 'p' 'q' old = add-forb old
update-double 'x' 'y' old = add-forb old
update-double 'a' _ old = add-a old
update-double 'e' 'e' old = add-e (add-double old)
update-double 'e' _ old = add-e old
update-double 'i' 'i' old = add-i (add-double old)
update-double 'i' _ old = add-i old
update-double 'o' 'o' old = add-o (add-double old)
update-double 'o' _ old = add-o old
update-double 'u' 'u' old = add-u (add-double old)
update-double 'u' _ old = add-u old
update-double a b old = if a == b then (add-double old) else old

eval-word : List Char → WordQual → WordQual
eval-word [] old = old
eval-word (x ∷ []) old = update-double x ' ' old 
eval-word (l ∷ r ∷ xs) old = eval-word (r ∷ xs) (update-double l r old)

judge-word : List Char → Nat
judge-word x = n-bool (is-nice (eval-word x default-qual))

judge-words : String → String
judge-words x = show (foldr _+_ 0 (map judge-word (find-parts '\n' (primStringToList x)))) ++ "\n"

test-judge-word-a : judge-word (primStringToList "ugknbfddgicrmopn") ≡ 1
test-judge-word-a = refl

test-judge-word-b : judge-word (primStringToList "aaa") ≡ 1
test-judge-word-b = refl

test-judge-word-c : judge-word (primStringToList "jchzalrnumimnmhp") ≡ 0
test-judge-word-c = refl

test-judge-word-d : judge-word (primStringToList "haegwjzuvuyypxyu") ≡ 0
test-judge-word-d = refl

test-judge-word-e : judge-word (primStringToList "dvszwmarrgswjxmb") ≡ 0
test-judge-word-e = refl
