
module d12.json where

open import util.list_stuff using (unmaybe ; trim)
open import util.json using (JsonObj ; parse-json ; str ; dict ; num ; lst)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (fromList ; toList ; _++_)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties using (_==_)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (length ; concat ; reverse ; map ; foldr)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (readMaybe)
open import Data.Nat.Properties using (_≟_)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_+_ ; _-_)
open import Data.Integer.Show using (show)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)
open import Function.Base using (_∘_)

is-red : (String × JsonObj) → Bool
is-red (_ , (str "red")) = true
is-red _ = false

has-red : JsonObj → Bool
has-red (dict d) = foldr _∨_ false (map is-red d)
has-red _ = false

add-up-all-h : Nat → JsonObj → Int
add-up-all-h _ (num k) = k
add-up-all-h (suc l) (lst d) = foldr _+_ (pos 0) (map (add-up-all-h l) d)
add-up-all-h (suc l) (dict d) with (has-red (dict d))
add-up-all-h (suc l) (dict d) | false = foldr _+_ (pos 0) (map ((add-up-all-h l) ∘ proj₂) d)
add-up-all-h (suc l) (dict d) | true = pos 0
add-up-all-h _ _ = pos 0

sum-all : String → String
sum-all x with (parse-json x)
sum-all x | nothing = "\nfailed parse\n"
sum-all x | (just tree) = "\ncount: " ++ (show (add-up-all-h ((length ∘ toList) x) tree)) ++ "\n"

test-add-up-all-a : sum-all "[1,2,3]" ≡ "\ncount: 6\n"
test-add-up-all-a = refl

test-add-up-all-aa : sum-all "{\"a\":2,\"b\":4}" ≡ "\ncount: 6\n"
test-add-up-all-aa = refl

test-add-up-all-b : sum-all "[[[3]]]" ≡ "\ncount: 3\n"
test-add-up-all-b = refl

test-add-up-all-ba : sum-all "{\"a\":{\"b\":4},\"c\":-1}" ≡ "\ncount: 3\n"
test-add-up-all-ba = refl

test-add-up-all-c : sum-all "{\"a\":[-1,1]}" ≡ "\ncount: 0\n"
test-add-up-all-c = refl

test-add-up-all-d : sum-all "[]" ≡ "\ncount: 0\n"
test-add-up-all-d = refl
