module d7.tower where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (∣_∣) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record Prog : Set where
  constructor prg
  field
    name : String
    weight : Nat
    above : List String

remove-f-paren : List Char → List Char
remove-f-paren ('(' ∷ xs) = xs
remove-f-paren xs = xs

remove-paren : String → String
remove-paren = fromList ∘ rem-dot ')' ∘ remove-f-paren ∘ trim-ch ∘ toList

parse-row-w : List String → Maybe Prog
parse-row-w (nm ∷ mw ∷ "->" ∷ xs) with (readMaybe 10 (remove-paren mw))
parse-row-w (nm ∷ mw ∷ "->" ∷ xs) | nothing = nothing
parse-row-w (nm ∷ mw ∷ "->" ∷ xs) | just (w) = just (prg nm w (map (fromList ∘ rem-dot ',' ∘ toList) xs))
parse-row-w (nm ∷ mw ∷ _) with (readMaybe 10 (remove-paren mw))
parse-row-w (nm ∷ mw ∷ _) | just (w) = just (prg nm w [])
parse-row-w (nm ∷ mw ∷ _) | nothing = nothing
parse-row-w _ = nothing

parse-row : String → Maybe Prog
parse-row = parse-row-w ∘ words

show-row : Prog → String
show-row (prg nm w []) = nm ++ " (" ++ show w ++ ")"
show-row (prg nm w xs) = nm ++ " (" ++ show w ++ ") -> " ++ intersperse ", " xs


name-in-child-list : Prog → Prog → Bool
name-in-child-list (prg nm _ _) (prg _ _ xs) = any (λ {q → q == nm}) xs

filter-out-child-nodes : List Prog → List Prog
filter-out-child-nodes xs = filterᵇ (λ {a → not (any (name-in-child-list a) xs)}) xs

find-root-node : String → String
find-root-node x = "root node: " ++  (unlines ∘ map show-row ∘ filter-out-child-nodes) nodes ++ "\n"
  where
    nodes : List Prog
    nodes = (unmaybe ∘ map parse-row ∘ lines) x

mk-tree : List Prog → LookupStrTree Prog
mk-tree = build-str-tree ∘ map (λ {q → Prog.name q , q})

weight-of : Nat → LookupStrTree Prog → String → Nat
weight-of 0 _ _ = 0
weight-of (suc lm) db nm with (read-tree nm db)
weight-of (suc lm) db nm | (just (prg _ w xs)) = w + foldr _+_ 0 (map (weight-of lm db) xs)
weight-of (suc lm) db nm | nothing = 0

calc-balance : Nat → String → LookupStrTree Prog → List (String × Nat)
calc-balance lm nm db = (map (λ {q → q , weight-of lm db q}) ∘ Prog.above) current
  where
    current : Prog
    current = fromMaybe (prg "" 0 []) (read-tree nm db)

is-balanced : List (String × Nat) → Bool
is-balanced = all (λ {(a , b) → a ==n b}) ∘ conseq ∘ map proj₂

odd-one : List (String × Nat) → String × Nat
odd-one [] = "" , 0
odd-one (x ∷ []) = x
odd-one (x ∷ xs) with (length (filterᵇ (λ {(_ , w1) → w1 ==n proj₂ x}) xs))
odd-one (x ∷ xs) | 0 = x
odd-one (x ∷ xs) | _ = (fromMaybe ("" , 0) ∘ head ∘ filterᵇ (λ {(_ , w1) → not (w1 ==n proj₂ x)})) xs

first-unbalanced : Nat → LookupStrTree Prog → List Prog → Maybe (Prog × List (String × Nat))
first-unbalanced 0 _ _ = nothing
first-unbalanced _ _ [] = nothing
first-unbalanced (suc lm) db (x ∷ xs) = output
  where
   balance : List (String × Nat)
   balance = calc-balance lm (Prog.name x) db
   output : Maybe (Prog × List (String × Nat))
   output with (is-balanced balance)
   output | false with (odd-one balance)
   output | false | (odd-nm , _) with (read-tree odd-nm db)
   output | false | (odd-nm , _) | (just next-prg) with (first-unbalanced lm db (next-prg ∷ []))
   output | false | (odd-nm , _) | (just next-prg) | nothing = just (x , balance)
   output | false | (odd-nm , _) | (just next-prg) | found = found
   output | false | (odd-nm , _) | nothing = nothing
   output | true = first-unbalanced lm db xs

find-unbalanced-node : String → String
find-unbalanced-node x = output ++ "\n"
  where
    nodes : List Prog
    nodes = (unmaybe ∘ map parse-row ∘ lines) x
    tree : LookupStrTree Prog
    tree = mk-tree nodes
    output : String
    output with (first-unbalanced (length nodes) tree nodes)
    output | nothing = "no imbalance found."
    output | (just (prg nm w _ , pairs)) = "unbalanced: " ++ nm ++ " " ++ show w ++ " -> " ++ (intersperse ", " ∘ map (λ {(a , b) → a ++ ":" ++ show b })) pairs

test-parse-row-a : (show-row ∘ fromMaybe (prg "nope" 0 []) ∘ parse-row) "pbga (66)" ≡ "pbga (66)"
test-parse-row-a = refl

test-parse-row-b : (show-row ∘ fromMaybe (prg "nope" 0 []) ∘ parse-row) "fwft (72) -> ktlj, cntj, xhth" ≡ "fwft (72) -> ktlj, cntj, xhth"
test-parse-row-b = refl

test-fixture : String
test-fixture = "pbga (66)\n" ++
  "xhth (57)\n" ++
  "ebii (61)\n" ++
  "havc (66)\n" ++
  "ktlj (57)\n" ++
  "fwft (72) -> ktlj, cntj, xhth\n" ++
  "qoyq (66)\n" ++
  "padx (45) -> pbga, havc, qoyq\n" ++
  "tknk (41) -> ugml, padx, fwft\n" ++
  "jptl (61)\n" ++
  "ugml (68) -> gyxo, ebii, jptl\n" ++
  "gyxo (61)\n" ++
  "cntj (57)"

test-find-root-node : find-root-node test-fixture ≡ "root node: tknk (41) -> ugml, padx, fwft\n"
test-find-root-node = refl

test-weight-of-a : weight-of 1000 ((mk-tree ∘ unmaybe ∘ map parse-row ∘ lines) test-fixture) "ugml" ≡ 251
test-weight-of-a = refl

test-weight-of-b : weight-of 1000 ((mk-tree ∘ unmaybe ∘ map parse-row ∘ lines) test-fixture) "padx" ≡ 243
test-weight-of-b = refl

test-odd-one : odd-one (("padx" , 243) ∷ ("ugml" , 251) ∷ ("fwft" , 243) ∷ []) ≡ ("ugml" , 251)
test-odd-one = refl

test-find-unbalanced-node : find-unbalanced-node test-fixture ≡ "unbalanced: tknk 41 -> ugml:251, padx:243, fwft:243\n"
test-find-unbalanced-node = refl
