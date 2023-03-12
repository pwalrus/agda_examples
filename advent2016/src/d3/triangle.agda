module d3.triangle where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


parse-line : String → Maybe (List Nat)
parse-line x with (words x)
parse-line x | [] = nothing
parse-line x | _ ∷ [] = nothing
parse-line x | _ ∷ _ ∷ [] = nothing
parse-line x | a ∷ b ∷ c ∷ _ with (readMaybe 10 a)
parse-line x | a ∷ b ∷ c ∷ _ | nothing = nothing
parse-line x | a ∷ b ∷ c ∷ _ | (just an) with (readMaybe 10 b)
parse-line x | a ∷ b ∷ c ∷ _ | (just an) | nothing = nothing
parse-line x | a ∷ b ∷ c ∷ _ | (just an) | (just bn) with (readMaybe 10 c)
parse-line x | a ∷ b ∷ c ∷ _ | (just an) | (just bn) | nothing = nothing
parse-line x | a ∷ b ∷ c ∷ _ | (just an) | (just bn) | (just cn) = just (an ∷ bn ∷ cn ∷ [])

sort-tri : List Nat → List Nat
sort-tri (a ∷ b ∷ c ∷ _) with (a < b)
sort-tri (a ∷ b ∷ c ∷ _) | true with (c < b)
sort-tri (a ∷ b ∷ c ∷ _) | true | true = a ∷ c ∷ b ∷ []
sort-tri (a ∷ b ∷ c ∷ _) | true | false = a ∷ b ∷ c ∷ []
sort-tri (a ∷ b ∷ c ∷ _) | false with (a < c)
sort-tri (a ∷ b ∷ c ∷ _) | false | true = b ∷ a ∷ c ∷ []
sort-tri (a ∷ b ∷ c ∷ _) | false | false = b ∷ c ∷ a ∷ []
sort-tri _ = []

valid-sorted : List Nat → Bool
valid-sorted (a ∷ b ∷ c ∷ _) = c < a + b
valid-sorted _ = false

valid-line : String → Bool
valid-line x with (parse-line x)
valid-line x | nothing = false
valid-line x | (just y) = valid-sorted (sort-tri y)

rotate-triples : List (List Nat) → List (List Nat)
rotate-triples ((a ∷ b ∷ c ∷ []) ∷ (d ∷ e ∷ f ∷ []) ∷ (x ∷ y ∷ z ∷ []) ∷ xs) =
  (a ∷ d ∷ x ∷ []) ∷ (b ∷ e ∷ y ∷ []) ∷ (c ∷ f ∷ z ∷ []) ∷ (rotate-triples xs)
rotate-triples _ = []

check-all-triangles : String → String
check-all-triangles x = (show count-valid) ++ "\n"
  where
    tris : List (List Nat)
    tris = (rotate-triples ∘ unmaybe ∘ (map (parse-line)) ∘ lines) x
    validation : List Bool
    validation = map (valid-sorted ∘ sort-tri) tris
    count-valid : Nat
    count-valid = foldr _+_ 0 (map (λ {q → if q then 1 else 0}) validation)

test-sort-tri : sort-tri  (5 ∷ 10 ∷ 25 ∷ []) ≡ 5 ∷ 10 ∷ 25 ∷ []
test-sort-tri = refl

test-valid-sorted : valid-sorted  (5 ∷ 10 ∷ 25 ∷ []) ≡ false
test-valid-sorted = refl

test-valid-line-a : valid-line "5 10 25" ≡ false
test-valid-line-a = refl

