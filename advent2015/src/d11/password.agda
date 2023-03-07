
module d11.password where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (length)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Show using (show ; readMaybe)
open import Data.Nat.Properties using (_≟_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)
open import Function.Base using (_∘_)

inc-char : Char → (Char × Bool)
inc-char 'z' = 'a' , true
inc-char x =  (primNatToChar ∘ suc ∘ primCharToNat) x , false

inc-pass-help : List Char → Bool × List Char
inc-pass-help [] = false , []
inc-pass-help (x ∷ []) with (inc-char x)
inc-pass-help (x ∷ []) | (y , f) = f , (y ∷ [])
inc-pass-help (x ∷ xs) with (inc-pass-help xs)
inc-pass-help (x ∷ xs) | (false , t) = false , (x ∷ t)
inc-pass-help (x ∷ xs) | (true , t) with (inc-char x)
inc-pass-help (x ∷ xs) | (true , t) | (z , f) = f , (z ∷ t)

snd : {A B : Set} → A × B → B
snd (x , y) = y

inc-pass : String → String
inc-pass  = fromList ∘ snd ∘ inc-pass-help ∘ toList

n-eq : Nat → Nat → Bool
n-eq a b = isYes (a ≟ b)

fst-cond : List Char → Bool
fst-cond [] = false
fst-cond (_ ∷ []) = false
fst-cond (_ ∷ _ ∷ []) = false
fst-cond (a ∷ b ∷ c ∷ xs) = ((n-eq (suc (primCharToNat a)) (primCharToNat b)) ∧ (n-eq (suc (primCharToNat b)) (primCharToNat c))) ∨ (fst-cond (b ∷ c ∷ xs))

snd-cond-b : List Char → Bool
snd-cond-b [] = false
snd-cond-b (_ ∷ []) = false
snd-cond-b (a ∷ b ∷ xs) = (a == b) ∨ (snd-cond-b (b ∷ xs))

snd-cond : List Char → Bool
snd-cond [] = false
snd-cond (_ ∷ []) = false
snd-cond (_ ∷ _ ∷ []) = false
snd-cond (a ∷ b ∷ xs) = ((a == b) ∧ (snd-cond-b xs)) ∨ (snd-cond (b ∷ xs))

trd-cond : List Char → Bool
trd-cond [] = true
trd-cond (x ∷ xs) = if ((x == 'i') ∨ (x == 'o') ∨ (x == 'l')) then false else (trd-cond xs)


iter-inc : Nat → String → String
iter-inc 0 _ = ""
iter-inc (suc l) y = if ((fst-cond x-ch) ∧ (snd-cond x-ch) ∧ (trd-cond x-ch)) then x else (iter-inc l x)
  where
    x : String
    x = inc-pass y
    x-ch : List Char
    x-ch = toList x

next-pass : String → String
next-pass x = "\nsol :" ++ (iter-inc 10000000 x) ++ "\n"

test-inc-pass : inc-pass "abzz" ≡ "acaa"
test-inc-pass = refl

test-fst-cond-t : fst-cond (toList "sssqrswww") ≡ true
test-fst-cond-t = refl

test-fst-cond-f : fst-cond (toList "sssqswww") ≡ false
test-fst-cond-f = refl

test-snd-cond-t : snd-cond (toList "saaswwt") ≡ true
test-snd-cond-t = refl

test-snd_cond-f : snd-cond (toList "saaat") ≡ false
test-snd_cond-f = refl

test-trd-cond-t : trd-cond (toList "saaat") ≡ true
test-trd-cond-t = refl

test-trd-cond-f : trd-cond (toList "saoaat") ≡ false
test-trd-cond-f = refl

test-iter-inc : iter-inc 10000 "abcffga" ≡ "abcffgg"
test-iter-inc = refl
