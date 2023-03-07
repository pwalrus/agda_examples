

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

look-and-see : String → String
look-and-see = conv ∘ conseq ∘ toList

look-and-see-iter : Nat → String → String
look-and-see-iter 0 x = x
look-and-see-iter (suc p) x = look-and-see-iter p (look-and-see x)

look-and-see-len : String → String
look-and-see-len = show ∘ length ∘ toList ∘ (look-and-see-iter 50)

test-look-and-seea : look-and-see "1"  ≡ "11"
test-look-and-seea = refl

test-look-and-seeb : look-and-see "11"  ≡ "21"
test-look-and-seeb = refl

test-look-and-seec : look-and-see "21"  ≡ "1211"
test-look-and-seec = refl

test-look-and-seed : look-and-see "1211"  ≡ "111221"
test-look-and-seed = refl

test-look-and-seee : look-and-see "111221"  ≡ "312211"
test-look-and-seee = refl
