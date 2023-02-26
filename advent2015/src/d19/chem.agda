module d19.chem where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; has_val ; set_val ; all_values ; all-keys ; LTPair) renaming (read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_) renaming (_==_ to _==n_ ; _-_ to nat-diff)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

data RepRule : Set where
  rep : String → String → RepRule

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

parse-line-w : List String → Maybe RepRule
parse-line-w (lhs ∷ "=>" ∷ rhs ∷ _) = just (rep lhs rhs)
parse-line-w _ = nothing

parse-line : String → Maybe RepRule
parse-line = parse-line-w ∘ words

last-non-blank-h : List String → Maybe String
last-non-blank-h [] = nothing
last-non-blank-h (x ∷ []) with (trim x == "")
last-non-blank-h (x ∷ []) | false = just (trim x)
last-non-blank-h (x ∷ []) | true = nothing
last-non-blank-h (x ∷ xs) with (last-non-blank-h xs)
last-non-blank-h (x ∷ xs) | (just y) = just y
last-non-blank-h (x ∷ xs) | nothing with (trim x == "")
last-non-blank-h (x ∷ xs) | nothing | false = just (trim x) 
last-non-blank-h (x ∷ xs) | nothing | true = nothing

append-all-front-all : {A : Set} → List A → List (List A) → List (List A)
append-all-front-all [] inp = inp
append-all-front-all (x ∷ xs) inp with (append-all-front-all xs inp)
append-all-front-all (x ∷ xs) inp | tail = append-front-all x tail

apply-rule-ch : Nat → RepRule → List Char → List (List Char)
apply-rule-ch _ _ [] = [] ∷ []
apply-rule-ch 0 _ _ = []
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ []) with (toList lhs)
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ []) | (a ∷ []) =
  if (a ==c x)
  then ((toList rhs) ∷ [])
  else ((x ∷ []) ∷ [])
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ []) | _ = (x ∷ []) ∷ []
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) with (toList lhs)
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) | (a ∷ []) with (apply-rule-ch l (rep lhs rhs) (y ∷ xs))
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) | (a ∷ []) | tail =
  if (a ==c x)
  then (concat ((append-front-all x tail) ∷ (append-all-front-all {Char} (toList rhs) ((y ∷ xs) ∷ [])) ∷ []))
  else (append-front-all x tail)
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) | (a ∷ b ∷ []) with (apply-rule-ch l (rep lhs rhs) xs)
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) | (a ∷ b ∷ []) | tail =
  if ((a ==c x) ∧ (b ==c y))
  then (concat ((append-all-front-all (x ∷ y ∷ []) tail) ∷ (append-all-front-all {Char} (toList rhs) (xs ∷ [])) ∷ []))
  else (append-front-all x (apply-rule-ch l (rep lhs rhs) (y ∷ xs)))
apply-rule-ch (suc l) (rep lhs rhs) (x ∷ y ∷ xs) | _ = append-front-all x (apply-rule-ch l (rep lhs rhs) (y ∷ xs))

apply-rule : String → RepRule  → List String
apply-rule x rule = (map fromList) (apply-rule-ch (length (toList x)) rule (toList x))

all-replace : String → List String
all-replace x = unique-list
  where
    rules : List RepRule
    rules = (unmaybe ∘ (map parse-line) ∘ lines) x
    mlast : Maybe String
    mlast = last-non-blank-h (lines x)
    last : String
    last with mlast
    last | nothing = ""
    last | (just x) = x
    all-applied : List String
    all-applied = concat (map (apply-rule last) rules)
    tree : LookupStrTree Bool
    tree = build-str-tree (map (λ {q → (q , true)}) all-applied)
    unique-list : List String
    unique-list = filterᵇ (λ {q → not (q == last)} ) (all-keys tree)

count-replace : String → String
count-replace x = "sol: " ++ (show ∘ length ∘ all-replace) x ++ "\n"

test-parse-line : parse-line "H => HO" ≡ just (rep "H" "HO")
test-parse-line = refl

test-parse-line-a : parse-line "Al => ThF" ≡ just (rep "Al" "ThF")
test-parse-line-a = refl

test-all-replace : (unlines ∘ all-replace) "H => HO\nH => OH\nO => HH\n\nHOH" ≡ "OHOH\nHOOH\nHOHO\nHHHH"
test-all-replace = refl

test-all-replace-b : (unlines ∘ all-replace) "HO => ABC\nOH => DEF\nH => HO\nH => OH\nO => HH\n\nHOH" ≡ "OHOH\nHOOH\nHOHO\nHHHH\nHDEF\nABCH"
test-all-replace-b = refl
