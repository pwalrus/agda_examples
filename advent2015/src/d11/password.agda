
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

inc_char : Char → (Char × Bool)
inc_char 'z' = 'a' , true
inc_char x =  (primNatToChar ∘ suc ∘ primCharToNat) x , false

inc_pass_help : List Char → Bool × List Char
inc_pass_help [] = false , []
inc_pass_help (x ∷ []) with (inc_char x)
inc_pass_help (x ∷ []) | (y , f) = f , (y ∷ [])
inc_pass_help (x ∷ xs) with (inc_pass_help xs)
inc_pass_help (x ∷ xs) | (false , t) = false , (x ∷ t)
inc_pass_help (x ∷ xs) | (true , t) with (inc_char x)
inc_pass_help (x ∷ xs) | (true , t) | (z , f) = f , (z ∷ t)

snd : {A B : Set} → A × B → B
snd (x , y) = y

inc_pass : String → String
inc_pass  = fromList ∘ snd ∘ inc_pass_help ∘ toList

n_eq : Nat → Nat → Bool
n_eq a b = isYes (a ≟ b)

fst_cond : List Char → Bool
fst_cond [] = false
fst_cond (_ ∷ []) = false
fst_cond (_ ∷ _ ∷ []) = false
fst_cond (a ∷ b ∷ c ∷ xs) = ((n_eq (suc (primCharToNat a)) (primCharToNat b)) ∧ (n_eq (suc (primCharToNat b)) (primCharToNat c))) ∨ (fst_cond (b ∷ c ∷ xs))

snd_cond_b : List Char → Bool
snd_cond_b [] = false
snd_cond_b (_ ∷ []) = false
snd_cond_b (a ∷ b ∷ xs) = (a == b) ∨ (snd_cond_b (b ∷ xs))

snd_cond : List Char → Bool
snd_cond [] = false
snd_cond (_ ∷ []) = false
snd_cond (_ ∷ _ ∷ []) = false
snd_cond (a ∷ b ∷ xs) = ((a == b) ∧ (snd_cond_b xs)) ∨ (snd_cond (b ∷ xs))

trd_cond : List Char → Bool
trd_cond [] = true
trd_cond (x ∷ xs) = if ((x == 'i') ∨ (x == 'o') ∨ (x == 'l')) then false else (trd_cond xs)


iter_inc : Nat → String → String
iter_inc 0 _ = ""
iter_inc (suc l) y = if ((fst_cond x_ch) ∧ (snd_cond x_ch) ∧ (trd_cond x_ch)) then x else (iter_inc l x)
  where
    x : String
    x = inc_pass y
    x_ch : List Char
    x_ch = toList x

next_pass : String → String
next_pass x = "\nsol :" ++ (iter_inc 10000000 x) ++ "\n"

test_inc_pass : inc_pass "abzz" ≡ "acaa"
test_inc_pass = refl

test_fst_cond_t : fst_cond (toList "sssqrswww") ≡ true
test_fst_cond_t = refl

test_fst_cond_f : fst_cond (toList "sssqswww") ≡ false
test_fst_cond_f = refl

test_snd_cond_t : snd_cond (toList "saaswwt") ≡ true
test_snd_cond_t = refl

test_snd_cond_f : snd_cond (toList "saaat") ≡ false
test_snd_cond_f = refl

test_trd_cond_t : trd_cond (toList "saaat") ≡ true
test_trd_cond_t = refl

test_trd_cond_f : trd_cond (toList "saoaat") ≡ false
test_trd_cond_f = refl

test_iter_inc : iter_inc 10000 "abcffga" ≡ "abcffgg"
test_iter_inc = refl
