

module d10.look where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (length)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Function.Base using (_∘_)

conseq : List Char → List (List Char)
conseq [] = []
conseq (x ∷ xs) with (conseq xs)
conseq (x ∷ xs) | [] = (x ∷ []) ∷ []
conseq (x ∷ xs) | ([] ∷ ys) = (x ∷ []) ∷ ys
conseq (x ∷ xs) | ((h ∷ t) ∷ ys) with (x == h)
conseq (x ∷ xs) | ((h ∷ t) ∷ ys) | true = (x ∷ h ∷ t) ∷ ys
conseq (x ∷ xs) | ((h ∷ t) ∷ ys) | false = (x ∷ []) ∷ (h ∷ t) ∷ ys


conv : List (List Char) → String
conv [] = ""
conv ([] ∷ xs) = conv xs
conv ((h ∷ t) ∷ xs) = (show (length (h ∷ t))) ++ (fromList (h ∷ [])) ++ conv xs

look_and_see : String → String
look_and_see = conv ∘ conseq ∘ toList

look_and_see_iter : Nat → String → String
look_and_see_iter 0 x = x
look_and_see_iter (suc p) x = look_and_see_iter p (look_and_see x)

look_and_see_len : String → String
look_and_see_len = show ∘ length ∘ toList ∘ (look_and_see_iter 50)

test_look_and_seea : look_and_see "1"  ≡ "11"
test_look_and_seea = refl

test_look_and_seeb : look_and_see "11"  ≡ "21"
test_look_and_seeb = refl

test_look_and_seec : look_and_see "21"  ≡ "1211"
test_look_and_seec = refl

test_look_and_seed : look_and_see "1211"  ≡ "111221"
test_look_and_seed = refl

test_look_and_seee : look_and_see "111221"  ≡ "312211"
test_look_and_seee = refl
