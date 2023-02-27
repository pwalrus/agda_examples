module d19.chem where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements) renaming (trim to trim-ch)
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

apply-rule : String → RepRule  → List String
apply-rule x (rep f t) = all-replacements (f , t) x

unique-only : List String → List String
unique-only x = unique-list
  where
    tree : LookupStrTree Bool
    tree = build-str-tree (map (λ {q → (q , true)}) x)
    unique-list : List String
    unique-list = all-keys tree

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
    unique-list : List String
    unique-list = filterᵇ (λ {q → not (q == last)} ) (unique-only all-applied)

apply-all-rules : List RepRule → List String → List String
apply-all-rules _ [] = []
apply-all-rules rules (x ∷ xs) = unique-only (concat (rec-sol ∷ (apply-all-rules rules xs) ∷ []))
  where
    rec-sol : List String
    rec-sol = concat (map (apply-rule x) rules)

search-rec-breadth : Nat → Nat → String → List RepRule → List String → Maybe (Nat × String)
search-rec-breadth step 0 _ _ _ = nothing
search-rec-breadth _ _ _ _ [] = nothing
search-rec-breadth step (suc l) target db currents with (filterᵇ (λ { q → (q == target)} ) currents)
search-rec-breadth step (suc l) target db currents | (current ∷ _) = just (step , current)
search-rec-breadth step (suc l) target db currents | _ with (apply-all-rules db  currents)
search-rec-breadth step (suc l) target db currents | _ | nexts with (search-rec-breadth (suc step) l target db nexts)
search-rec-breadth step (suc l) target db currents | _ | nexts | nothing = nothing
search-rec-breadth step (suc l) target db currents | _ | nexts | (just (sol)) = just sol

search-rec-depth : Nat → Nat → String → List RepRule → List String → Maybe (Nat × String)
search-rec-depth step 0 _ _ _ = nothing
search-rec-depth step (suc l) target db currents with (currents)
search-rec-depth step (suc l) target db currents | [] = nothing
search-rec-depth step (suc l) target db currents | (current ∷ rest) with (current == target)
search-rec-depth step (suc l) target db currents | (current ∷ rest) | true = just (step , current)
search-rec-depth step (suc l) target db currents | (current ∷ rest) | false with ((concat ∘ map (apply-rule current)) db)
search-rec-depth step (suc l) target db currents | (current ∷ rest) | false | deeper = search-rec-depth (suc step) l target db (concat (deeper ∷ rest ∷ []))

steps-to-e-from : String → String → String
steps-to-e-from x start = output
  where
    rules : List RepRule
    rules = (unmaybe ∘ (map parse-line) ∘ lines) x
    rev-rules : List RepRule
    rev-rules = map (λ {(rep f t) → rep t f}) rules
    mlast : Maybe String
    mlast = last-non-blank-h (lines x)
    last : String
    last with mlast
    last | nothing = ""
    last | (just x) = x
    msol : Maybe (Nat × String)
    msol = search-rec-depth 0 1000 "e" rev-rules (start ∷ [])
    output : String
    output with msol
    output | nothing = "not found\n"
    output | (just sol) = show (proj₁ sol) ++ ", " ++ proj₂ sol ++ "\n"

steps-to-e-from-last : String → String
steps-to-e-from-last x = steps-to-e-from x last
  where
    mlast : Maybe String
    mlast = last-non-blank-h (lines x)
    last : String
    last with mlast
    last | nothing = ""
    last | (just x) = x

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

test-steps-from-e-to : steps-to-e-from "H => HO\nH => OH\nO => HH\ne => H\ne => O\n\nHOH" "HOH" ≡ "3, e\n"
test-steps-from-e-to = refl

test-steps-from-e-to-a : steps-to-e-from "H => HO\nH => OH\nO => HH\ne => H\ne => O\n\nHOH" "HOHOHO" ≡ "6, e\n"
test-steps-from-e-to-a = refl
