module d22.magic where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f) renaming (trim to trim-ch)
open import util.lookup using (LookupNatTree ; build-nat-tree ; has_val ; all_values ; all-keys ; all-kv ; LTPair) renaming (set_val to set-tree ; read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
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


data Effect : Set where
  noeff : Effect
  shield : Nat → Effect
  poison : Nat → Effect
  recharge : Nat → Effect

step-timer : List Effect → List Effect
step-timer [] = []
step-timer (shield (suc t) ∷ xs) = (shield t) ∷ (step-timer xs)
step-timer (poison (suc t) ∷ xs) = (poison t) ∷ (step-timer xs)
step-timer (recharge (suc t) ∷ xs) = (recharge t) ∷ (step-timer xs)
step-timer (_ ∷ xs) = step-timer xs

show-eff : Effect → String
show-eff (shield x) = "shield:" ++ show x
show-eff (poison x) = "poison:" ++ show x
show-eff (recharge x) = "recharge:" ++ show x
show-eff _ = ""

show-eff-l : List Effect → String
show-eff-l x = "[" ++ intersperse "," (map show-eff x) ++ "]"

data Spell : Set where
  spell : String → Nat → Nat → Nat → Effect → Spell

sp-dam : Spell → Nat
sp-dam (spell _ _ dam _ _) = dam

sp-heal : Spell → Nat
sp-heal (spell _ _ _ heal _) = heal

sp-cost : Spell → Nat
sp-cost (spell _ cost _ _ _) = cost

sp-name : Spell → String
sp-name (spell name _ _ _ _) = name

sp-eff : Spell → Effect
sp-eff (spell _ _ _ _ eff) = eff

all-spells : List Spell
all-spells =
  (spell "Magic Missile" 53 4 0 noeff) ∷
  (spell "Drain" 73 2 2 noeff) ∷
  (spell "Shield" 113 0 0 (shield 6)) ∷
  (spell "Poison" 173 0 0 (poison 6)) ∷
  (spell "Recharge" 229 0 0 (recharge 5)) ∷ []

sp-by : String → Spell
sp-by name with (filterᵇ (λ {q → sp-name q == name}) all-spells)
sp-by name | (x ∷ _) = x
sp-by name | [] =   (spell "No Spell" 1000 0 0 noeff)

show-sp-l : List Spell → String
show-sp-l x = "[" ++ intersperse "," (map sp-name x) ++ "]"

eval-sp-l : List Spell → Nat
eval-sp-l = (foldr _+_ 0) ∘ (map sp-cost)

data StatBundle : Set where
  statb : Nat → Nat → StatBundle

data Situation : Set where
  sit : StatBundle → Nat → Nat → Nat → List Effect → Situation

show-sit : Situation → String
show-sit (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) = show p-hp ++ "/" ++ show p-mana ++ " vs " ++ show b-hp ++ " with " ++ show-eff-l eff

show-sitm : Maybe Situation → String
show-sitm (just (sit (statb b-dam b-arm) p-hp p-mana b-hp eff)) = show p-hp ++ "/" ++ show p-mana ++ " vs " ++ show b-hp
show-sitm nothing = "failed cast"

p-mana : Situation → Nat
p-mana (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) = p-mana

act-eff : Situation → List Effect
act-eff (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) = eff

p-dead : Situation → Bool
p-dead (sit (statb b-dam b-arm) 0 p-mana b-hp eff) = true
p-dead _ = false

b-dead : Situation → Bool
b-dead (sit (statb b-dam b-arm) p-hp p-mana 0 eff) = true
b-dead _ = false

eff-dam : List Effect → Nat
eff-dam [] = 0
eff-dam ((poison (suc _)) ∷ xs) = 3
eff-dam (_ ∷ xs) = eff-dam xs

eff-arm : List Effect → Nat
eff-arm [] = 0
eff-arm ((shield (suc _)) ∷ xs) = 7
eff-arm (_ ∷ xs) = eff-arm xs

eff-rec : List Effect → Nat
eff-rec [] = 0
eff-rec ((recharge (suc _)) ∷ xs) = 101
eff-rec (_ ∷ xs) = eff-rec xs

can-afford : Spell → Nat → Bool
can-afford (spell _ cost _ _ _) mana = cost < (suc mana)

valid-effect : Spell → List Effect → Bool
valid-effect (spell _ _ _ _ noeff) _ = true
valid-effect (spell _ _ _ _ _) [] = true
valid-effect (spell _ _ _ _ (poison _)) (poison (suc _) ∷ _) = false
valid-effect (spell _ _ _ _ (shield _)) (shield (suc _) ∷ _) = false
valid-effect (spell _ _ _ _ (recharge _)) (recharge (suc _) ∷ _) = false
valid-effect sp (_ ∷ xs) = valid-effect sp xs

apply-p-damage : Situation → Spell → Situation
apply-p-damage (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) sp =
  sit (statb b-dam b-arm) (p-hp + (sp-heal sp)) p-mana (b-hp -(sp-dam sp)) (sp-eff sp ∷ eff)

apply-eff-damage : Situation → Situation
apply-eff-damage (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) =
  sit (statb b-dam b-arm) p-hp (p-mana + (eff-rec eff)) (b-hp - (eff-dam eff)) eff

apply-cost : Situation → Spell → Situation
apply-cost (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) sp  =
  sit (statb b-dam b-arm) p-hp (p-mana - (sp-cost sp)) b-hp eff

apply-b-damage : Situation → Situation
apply-b-damage (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) =
  sit (statb b-dam b-arm) (p-hp - (b-dam - (eff-arm eff))) p-mana b-hp eff

apply-eff-timer : Situation → Situation
apply-eff-timer (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) =
  sit (statb b-dam b-arm) p-hp p-mana b-hp (step-timer eff)

drop-point : Situation → Situation
drop-point (sit (statb b-dam b-arm) p-hp p-mana b-hp eff) =
  sit (statb b-dam b-arm) (p-hp - 1) p-mana b-hp eff

calc-turn : Spell → Situation → Bool → Maybe Situation
calc-turn sp situation hard with (apply-eff-timer (apply-eff-damage (if hard then (drop-point situation) else situation)))
calc-turn sp situation hard | pre-turn with (can-afford sp (p-mana pre-turn) ∧ (valid-effect sp (act-eff pre-turn)) ∧ (not (p-dead pre-turn)))
calc-turn sp situation hard | pre-turn | false = nothing
calc-turn sp situation hard | pre-turn | true with (apply-p-damage (apply-cost pre-turn sp) sp)
calc-turn sp situation hard | pre-turn | true | p-turn with (p-dead p-turn)
calc-turn sp situation hard | pre-turn | true | p-turn | true = just p-turn
calc-turn sp situation hard | pre-turn | true | p-turn | false with (apply-eff-timer (apply-eff-damage p-turn))
calc-turn sp situation hard | pre-turn | true | p-turn | false | eff-turn with (b-dead eff-turn)
calc-turn sp situation hard | pre-turn | true | p-turn | false | eff-turn | true = just eff-turn
calc-turn sp situation hard | pre-turn | true | p-turn | false | eff-turn | false = just (apply-b-damage eff-turn)

calc-turn-with-hist : List Spell → Spell → Situation → Bool → Maybe (List Spell × Situation)
calc-turn-with-hist hist sp sit1 hard with (calc-turn sp sit1 hard)
calc-turn-with-hist hist sp sit1 hard | nothing = nothing
calc-turn-with-hist hist sp sit1 hard | (just sit2) = just ((concat (hist ∷ (sp ∷ []) ∷ [])) , sit2)

calc-spell-seq : List Spell → Situation → Bool → List String
calc-spell-seq [] sit1 _ = show-sit sit1 ∷ []
calc-spell-seq (sp ∷ xs) sit1 hard with (calc-turn sp sit1 hard)
calc-spell-seq (sp ∷ xs) sit1 hard | nothing = (show-sit sit1 ++ " ==> " ++ (sp-name sp) ++ " ==> " ++ show-sitm nothing) ∷ []
calc-spell-seq (sp ∷ xs) sit1 hard | (just sit2) with (calc-spell-seq xs sit2 hard)
calc-spell-seq (sp ∷ xs) sit1 hard | (just sit2) | tail = (show-sit sit1 ++ " ==> " ++ sp-name sp) ∷ tail

search-valid-h-layer : Nat → Bool → (List Spell × Situation) → (List (List Spell × Situation) × List (List Spell × Situation))
search-valid-h-layer best hard (hist , sit1) = complete , inprogress
  where
    next-level : List (List Spell × Situation)
    next-level = unmaybe (map (λ {sp → calc-turn-with-hist hist sp sit1 hard }) all-spells)
    complete : List (List Spell × Situation)
    complete = filterᵇ (λ {(_ , q) →  b-dead q ∧ (not (p-dead q))}) next-level
    inprogress : List (List Spell × Situation)
    inprogress = filterᵇ (λ {(hist , q) → ((not (b-dead q))) ∧ (not (p-dead q)) ∧ (eval-sp-l hist < (suc best))}) next-level

search-valid-h : Nat → Nat → List (List Spell × Situation) → Bool → List (List Spell × Situation)
search-valid-h 0 _ _ _ = []
search-valid-h _ _ [] _ = []
search-valid-h (suc l) best queue hard = concat (complete ∷ (search-valid-h l new-best inprogress hard) ∷ [])
  where
    next-layers : List (List (List Spell × Situation) × List (List Spell × Situation))
    next-layers = map (search-valid-h-layer best hard) queue
    complete : List (List Spell × Situation)
    complete = concat (map proj₁ next-layers)
    new-best-m : Maybe Nat
    new-best-m = min-by-f (λ {q → q}) (map (λ {(hist , _) → eval-sp-l hist}) complete)
    new-best : Nat
    new-best with new-best-m
    new-best | nothing = best
    new-best | just x = if x < best then x else best
    inprogress : List (List Spell × Situation)
    inprogress = concat (map proj₂ next-layers)

cheapest-spells : Situation → Bool → (Nat × List Spell)
cheapest-spells sit1 hard = min-score
  where
    valid : List (List Spell × Situation)
    valid = search-valid-h 1000 10000000 (([] , sit1) ∷ []) hard
    scored : List (Nat × List Spell)
    scored = map (λ {(hist , _) → (eval-sp-l hist , hist)}) valid
    min-score : Nat × List Spell
    min-score with (min-by-f (λ {(q , _) → q}) scored)
    min-score | nothing = (10000000 , [])
    min-score | (just p) = p

start-hp : Nat
start-hp = 50

start-mana : Nat
start-mana = 500

boss-hp : Nat
boss-hp = 71

boss-bundle : StatBundle
boss-bundle = statb 10 10

cheapest-real-spells : String → String
cheapest-real-spells _ = show (proj₁ pair) ++ " <-- " ++ show-sp-l (proj₂ pair) ++ "\n"
  where
    pair : Nat × List Spell
    pair = cheapest-spells (sit boss-bundle start-hp start-mana boss-hp []) true

test-calc-turn : show-sitm (calc-turn (spell "Magic Missile" 53 4 0 noeff) (sit (statb 10 10) start-hp start-mana 51 []) false) ≡ "40/447 vs 47"
test-calc-turn = refl

test-calc-seq : unlines ( calc-spell-seq (map sp-by ("Poison" ∷ "Magic Missile" ∷ [])) (sit (statb 8 10) 10 250 13 []) false) ≡
  "10/250 vs 13 with [] ==> Poison\n" ++
  "2/77 vs 10 with [poison:5] ==> Magic Missile\n" ++
  "2/24 vs 0 with [poison:3]"
test-calc-seq = refl

test-calc-seq-c : unlines ( calc-spell-seq (map sp-by ("Poison" ∷ "Recharge" ∷ "Magic Missile" ∷ "Poison" ∷ "Drain" ∷ "Magic Missile" ∷ [])) (sit (statb 9 10) 50 500 41 []) false) ≡
  "50/500 vs 41 with [] ==> Poison\n" ++
  "41/327 vs 38 with [poison:5] ==> Recharge\n" ++
  "32/199 vs 32 with [recharge:4,poison:3] ==> Magic Missile\n" ++
  "23/348 vs 22 with [recharge:2,poison:1] ==> Poison\n" ++
  "14/377 vs 16 with [poison:5,recharge:0] ==> Drain\n" ++
  "7/304 vs 8 with [poison:3] ==> Magic Missile\n" ++
  "7/251 vs 0 with [poison:1]"
test-calc-seq-c = refl

test-calc-seq-b : unlines ( calc-spell-seq (
  (sp-by "Recharge") ∷
  (sp-by "Shield") ∷
  (sp-by "Drain") ∷
  (sp-by "Poison") ∷
  (sp-by "Magic Missile") ∷ []) (sit (statb 8 10) 10 250 14 []) false) ≡
  "10/250 vs 14 with [] ==> Recharge\n" ++
  "2/122 vs 14 with [recharge:4] ==> Shield\n" ++
  "1/211 vs 14 with [shield:5,recharge:2] ==> Drain\n" ++
  "2/340 vs 12 with [shield:3,recharge:0] ==> Poison\n" ++
  "1/167 vs 9 with [poison:5,shield:1] ==> Magic Missile\n" ++
  "1/114 vs 0 with [poison:3]"
test-calc-seq-b = refl

test-calc-seq-b-hard : unlines ( calc-spell-seq (
  (sp-by "Recharge") ∷
  (sp-by "Shield") ∷
  (sp-by "Drain") ∷
  (sp-by "Poison") ∷
  (sp-by "Magic Missile") ∷ []) (sit (statb 8 10) 10 250 14 []) true) ≡
  "10/250 vs 14 with [] ==> Recharge\n" ++
  "1/122 vs 14 with [recharge:4] ==> Shield ==> failed cast"
test-calc-seq-b-hard = refl

test-search-valid-h : length (search-valid-h 150 100000 (([] ,
  (sit (statb 8 10) 10 250 13 [])) ∷ []) false) ≡ 1
test-search-valid-h = refl

test-cheapest-spells-ex : (show ∘ proj₁) (cheapest-spells (sit (statb 8 10) 10 250 13 []) false) ≡ "226"
test-cheapest-spells-ex = refl

test-cheapest-spells-ex-b : (show ∘ proj₁) (cheapest-spells (sit (statb 8 10) 10 250 14 []) false) ≡ "641"
test-cheapest-spells-ex-b = refl

--test-cheapest-real : cheapest-real-spells "" ≡ ""
--test-cheapest-real = refl
