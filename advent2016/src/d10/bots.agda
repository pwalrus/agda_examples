module d10.bots where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ) renaming (trim to trim-ch)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

output_offs : Nat
output_offs = 100000

data BotId : Set where
  bot : Nat → BotId
  output : Nat → BotId

use-id : BotId → Nat
use-id (bot id) = id
use-id (output id) = output_offs + id

mk-id : Nat → BotId
mk-id x = if suc x < output_offs then (bot x) else (output (x - output_offs))

eq-bot : BotId → BotId → Bool
eq-bot (bot x) (bot y) = x ==n y
eq-bot (output x) (output y) = x ==n y
eq-bot _ _ = false

data BotInst : Set where
  give-val : BotId → Nat → BotInst
  comp-vals : BotId → BotId → BotId → BotInst

eq-inst : BotInst → BotInst → Bool
eq-inst (give-val x a) (give-val y b) = (eq-bot x y) ∧ (a ==n b)
eq-inst (comp-vals i1 i2 i3) (comp-vals j1 j2 j3) = (eq-bot i1 j1) ∧ (eq-bot i2 j2) ∧ (eq-bot i3 j3)
eq-inst _ _ = false

state-to-inst : Nat × List Nat → List BotInst
state-to-inst (x , xs) = map (λ{q → give-val (mk-id x) q}) xs

show-id : BotId → String
show-id (bot id) = "bot " ++ show id
show-id (output id) = "output " ++ show id

show-inst : BotInst → String
show-inst (give-val bid v) = "value " ++ show v ++ " goes to " ++ show-id bid
show-inst (comp-vals i1 i2 i3) = show-id i1 ++ " gives low to " ++ show-id i2 ++ " and high to " ++ show-id i3

show-state : LookupNatTree (List Nat) × List BotInst → String
show-state (db , prog) = (unlines ∘ concat) (((map show-inst) ∘ concat) (map state-to-inst (all-kv db)) ∷ (map show-inst prog) ∷ [])

is-init : BotInst → Bool
is-init (give-val _ _) = true
is-init _ = false

same-init : BotInst → BotInst → Bool
same-init (give-val x _) (give-val y _) = eq-bot x y
same-init _ _ = false

parse-bot-id : String → Nat → Maybe BotId
parse-bot-id "output" id = just (output id)
parse-bot-id "bot" id = just (bot id)
parse-bot-id _ _ = nothing

read-maybe-2 : String → String → Maybe (Nat × Nat)
read-maybe-2 xm ym with (readMaybe 10 xm)
read-maybe-2 xm ym | (just x) with (readMaybe 10 ym)
read-maybe-2 xm ym | (just x) | (just y) = just (x , y)
read-maybe-2 xm ym | (just x) | nothing = nothing
read-maybe-2 xm ym | nothing = nothing

read-maybe-3 : String → String → String → Maybe (Nat × Nat × Nat)
read-maybe-3 xm ym zm with (read-maybe-2 xm ym)
read-maybe-3 xm ym zm | (just (x , y)) with (readMaybe 10 zm)
read-maybe-3 xm ym zm | (just (x , y)) | (just z) = just (x , y , z)
read-maybe-3 xm ym zm | (just (x , y)) | nothing = nothing
read-maybe-3 xm ym zm | nothing = nothing

parse-comp-vals : Nat → String → Nat → String → Nat → Maybe BotInst
parse-comp-vals id t1 id1 t2 id2 with (parse-bot-id t1 id1)
parse-comp-vals id t1 id1 t2 id2 | (just b1) with (parse-bot-id t2 id2)
parse-comp-vals id t1 id1 t2 id2 | (just b1) | (just b2) = just (comp-vals (bot id) b1 b2)
parse-comp-vals id t1 id1 t2 id2 | (just b1) | nothing = nothing
parse-comp-vals id t1 id1 t2 id2 | nothing = nothing

parse-line-w : List String → Maybe BotInst
parse-line-w ("value" ∷ vm ∷ "goes" ∷ "to" ∷ t1 ∷ idm ∷ _) with (read-maybe-2 vm idm)
parse-line-w ("value" ∷ vm ∷ "goes" ∷ "to" ∷ t1 ∷ idm ∷ _) | (just (v , id)) with (parse-bot-id t1 id)
parse-line-w ("value" ∷ vm ∷ "goes" ∷ "to" ∷ t1 ∷ idm ∷ _) | (just (v , id)) | (just b1) = just (give-val b1 v)
parse-line-w ("value" ∷ vm ∷ "goes" ∷ "to" ∷ t1 ∷ idm ∷ _) | (just (v , id)) | nothing = nothing
parse-line-w ("value" ∷ vm ∷ "goes" ∷ "to" ∷ t1 ∷ idm ∷ _) | _ = nothing
parse-line-w ("bot" ∷ idm ∷ "gives" ∷ "low" ∷ "to" ∷ t1 ∷ id1m ∷ "and" ∷ "high" ∷ "to" ∷ t2 ∷ id2m ∷ _) with (read-maybe-3 idm id1m id2m)
parse-line-w ("bot" ∷ idm ∷ "gives" ∷ "low" ∷ "to" ∷ t1 ∷ id1m ∷ "and" ∷ "high" ∷ "to" ∷ t2 ∷ id2m ∷ _) | (just (id , id1 , id2)) = parse-comp-vals id t1 id1 t2 id2
parse-line-w ("bot" ∷ idm ∷ "gives" ∷ "low" ∷ "to" ∷ t1 ∷ id1m ∷ "and" ∷ "high" ∷ "to" ∷ t2 ∷ id2m ∷ _) | nothing = nothing
parse-line-w _ = nothing

parse-line : String → Maybe BotInst
parse-line = parse-line-w ∘ words

collapse-init-eq-class : List BotInst → (Nat × List Nat)
collapse-init-eq-class ((give-val b1 v) ∷ xs) = (use-id b1) , (v ∷ proj₂ (collapse-init-eq-class xs))
collapse-init-eq-class _ = 0 , []

init-tree : List BotInst → LookupNatTree (List Nat)
init-tree xs = build-nat-tree pairs
  where
    init-only : List BotInst
    init-only = filterᵇ is-init xs
    classes : List (List BotInst)
    classes = eq-classes same-init init-only
    pairs : List (Nat × List Nat)
    pairs = map collapse-init-eq-class classes

curr-inv : Nat → LookupNatTree (List Nat) → List Nat
curr-inv id db with (read-tree id db)
curr-inv id db | (just lst) = lst
curr-inv id db | nothing = []

add-val : Nat → BotId → LookupNatTree (List Nat) → LookupNatTree (List Nat)
add-val v bid db = set-tree (use-id bid) (v ∷ (curr-inv (use-id bid) db)) db

clear-val : BotId → LookupNatTree (List Nat) → LookupNatTree (List Nat)
clear-val bid db = rem-tree (use-id bid) db

max-nat : List Nat → Nat
max-nat [] = 0
max-nat (x ∷ []) = x
max-nat (x ∷ xs) = if (x < y) then y else x
  where
    y : Nat
    y = max-nat xs

min-nat : List Nat → Nat
min-nat [] = 0
min-nat (x ∷ []) = x
min-nat (x ∷ xs) = if (x < y) then x else y
  where
    y : Nat
    y = max-nat xs

apply-inst : BotInst → LookupNatTree (List Nat) → LookupNatTree (List Nat)
apply-inst (give-val _ _ ) db = db
apply-inst (comp-vals (output _) _ _) db = db
apply-inst (comp-vals (bot id) bl bh) db = new-db
  where
    curr : List Nat
    curr = curr-inv id db
    new-db : LookupNatTree (List Nat)
    new-db with (length curr ==n 2)
    new-db | true = clear-val (bot id) (add-val (max-nat curr) bh (add-val (min-nat curr) bl db))
    new-db | false = db

available-output : BotId → LookupNatTree (List Nat) → Bool
available-output (output _) _ = true
available-output (bot id) db = length (curr-inv id db) < 2

valid-inst : BotInst → LookupNatTree (List Nat) → Bool
valid-inst (give-val _ _ ) _ = false
valid-inst (comp-vals (output _) _ _) _ = false
valid-inst (comp-vals (bot id) bl bh) db = (length (curr-inv id db) ==n 2) ∧ (available-output bl db) ∧ (available-output bh db)

done : List BotInst → LookupNatTree (List Nat) → Bool
done prog db = false 
  --(all (λ {q → not (valid-inst q db)}) prog)
  --∨ (has-val 100000 db ∧ has-val 100001 db ∧ has-val 100002 db)
  --∨ (any (λ {(_ , v) → (min-nat v ==n 17) ∧ (max-nat v ==n 61) }) (all-kv db))

show-list : List Nat → String
show-list xs = "[" ++ intersperse ", " (map show xs) ++ "]"

show-tree : LookupNatTree (List Nat) → String
show-tree db = unlines rows
  where
    rows : List String
    rows = map (λ {(k , v) → show k ++ ":" ++ show-list v }) (all-kv db)

first-match : {A : Set} → (A → Bool) → List A → Maybe (A × List A)
first-match f [] = nothing
first-match f (x ∷ xs) with (f x)
first-match f (x ∷ xs) | true  = just (x , xs)
first-match f (x ∷ xs) | false with (first-match f xs)
first-match f (x ∷ xs) | false | nothing = nothing
first-match f (x ∷ xs) | false | just (y , ys) = just (y , x ∷ ys)

apply-all-inst : Nat → List BotInst → LookupNatTree (List Nat) → (LookupNatTree (List Nat) × List BotInst)
apply-all-inst 0 prog db = db , prog
apply-all-inst (suc lm) prog db = next
  where
    next : LookupNatTree (List Nat) × List BotInst
    next with (done prog db)
    next | true = (db , prog)
    next | false with (partitionᵇ (λ {q → valid-inst q db}) prog)
    next | false | ([] , rem) = db , rem
    next | false | (valid , rem) = (apply-all-inst lm rem (foldr apply-inst db valid))

calc-final-state : String → String
calc-final-state x = show-tree (proj₁ (apply-all-inst (length prog) (filterᵇ (not ∘ is-init) prog) db)) ++ "\n"
  where
    prog : List BotInst
    prog = (unmaybe ∘ (map parse-line) ∘ lines) x
    db : LookupNatTree (List Nat)
    db = init-tree prog

calc-one-step : String → String
calc-one-step x = show-state (apply-all-inst 1 (filterᵇ (not ∘ is-init) prog) db) ++ "\n"
  where
    prog : List BotInst
    prog = (unmaybe ∘ (map parse-line) ∘ lines) x
    db : LookupNatTree (List Nat)
    db = init-tree prog

test-parse-line-a : show-inst (fromMaybe (give-val (bot 0) 0) (parse-line "value 5 goes to bot 2")) ≡ "value 5 goes to bot 2"
test-parse-line-a = refl

test-parse-line-b : parse-line "bot 2 gives low to bot 1 and high to bot 0" ≡ just (comp-vals (bot 2) (bot 1) (bot 0))
test-parse-line-b = refl

test-parse-line-c : show-inst (fromMaybe (give-val (bot 0) 0) (parse-line "bot 0 gives low to output 2 and high to output 0")) ≡ "bot 0 gives low to output 2 and high to output 0"
test-parse-line-c = refl

test-parse-line-d : show-inst (fromMaybe (give-val (bot 0) 0) (parse-line "value 3 goes to output 19")) ≡ "value 3 goes to output 19"
test-parse-line-d = refl

test-init-tree : (show-tree ∘ init-tree ∘ unmaybe ∘ (map parse-line) ∘ lines)
  ("value 11 goes to output 19\n" ++ "value 5 goes to bot 2\n")
  ≡ "2:[5]\n100019:[11]"
test-init-tree = refl

test-apply-all : calc-final-state
  ("value 5 goes to bot 2\n" ++
  "bot 2 gives low to bot 1 and high to bot 0\n" ++
  "value 3 goes to bot 1\n" ++
  "bot 1 gives low to output 1 and high to bot 0\n" ++
  "bot 0 gives low to output 2 and high to output 0\n" ++
  "value 2 goes to bot 2")
  ≡ "100000:[5]\n100001:[2]\n100002:[3]\n"
test-apply-all = refl


