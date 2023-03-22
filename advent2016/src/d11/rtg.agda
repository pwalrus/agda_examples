module d11.rtg where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth-dedup)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo ; scanr ; reverse)
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

data EType : Set where
  gener : EType
  chip : EType

eq-et : EType → EType → Bool
eq-et chip chip = true
eq-et gener gener = true
eq-et _ _ = false


data Equip : Set where
  equip : EType → String → Equip

is-chip : Equip → Bool
is-chip (equip chip _) = true
is-chip _ = false

right-gen : Equip → Equip
right-gen (equip _ elem) = equip gener elem

show-equip : Equip → String
show-equip (equip chip name) = (fromList ∘ (take 2) ∘ toList) name ++ "M"
show-equip (equip gener name) = (fromList ∘ (take 2) ∘ toList) name ++ "G" 

eq-equip : Equip → Equip → Bool
eq-equip (equip t1 s1) (equip t2 s2) = (eq-et t1 t2) ∧ (s1 == s2)

lt-equip : Equip → Equip → Bool
lt-equip (equip chip _) (equip gener _) = true
lt-equip (equip gener _) (equip chip _) = false
lt-equip (equip chip x) (equip chip y) = str-lt x y
lt-equip (equip gener x) (equip gener y) = str-lt x y

data FloorDesc : Set where
  floor : Nat → List Equip → FloorDesc

equip-on : FloorDesc → List Equip
equip-on (floor _ xs) = xs

data Move : Set where
  mup : List Equip → Move
  mdown : List Equip → Move

rev-move : Move → Move
rev-move (mup x) = mdown x
rev-move (mdown x) = mup x

show-move : Move → String
show-move (mup xs) = "up:" ++ intersperse "," (map show-equip xs)
show-move (mdown xs) = "down:" ++ intersperse "," (map show-equip xs)

record EqState : Set where
  constructor eqs
  field
    ele : Nat
    eql : List (List Equip)
    hist : List Move

show-state : EqState → String
show-state (eqs curr xs _) = unlines str-line
  where
    pairs : List (Nat × List Equip)
    pairs = enumerate xs
    str-line : List String
    str-line = map (λ {(idx , lst) → padRight ' ' 3 (show (suc idx)) ++ padRight ' ' 3 (if suc idx ==n curr then "E" else "") ++ (intersperse "," (map show-equip lst)) }) pairs

order-of-appearance : EqState → List String
order-of-appearance (eqs curr xs _) = deduplicateᵇ _==_ names 
  where
    names : List String
    names = map (λ {(equip _ n) → n}) (concat xs)

floor-count-str : List Equip → String
floor-count-str xs = "M" ++ (show ∘ length ∘ proj₁) divs ++ "G" ++ (show ∘ length ∘ proj₂) divs
  where
    divs : List Equip × List Equip
    divs = partitionᵇ is-chip xs

show-anon-state : EqState → String
show-anon-state (eqs curr xs mvs) = show-state renamed
  where
    ooa : List String
    ooa = order-of-appearance (eqs curr xs mvs)
    renamed : EqState
    renamed = (eqs curr (map (map (λ {(equip t1 n) → (equip t1 ((show ∘ (fromMaybe 0) ∘ (index-of _==_ ooa)) n))} )) xs) mvs)

show-anon-state2 : EqState → String
show-anon-state2 (eqs curr xs _) = unlines str-line
  where
    pairs : List (Nat × List Equip)
    pairs = enumerate xs
    str-line : List String
    str-line = map (λ {(idx , lst) → padRight ' ' 3 (show (suc idx)) ++ padRight ' ' 3 (if suc idx ==n curr then "E" else "") ++ (floor-count-str lst) }) pairs

split-and : String → String
split-and xs with (all-replacements (", and " , ", ") xs)
split-and xs | [] with (all-replacements (" and " , ", ") xs)
split-and xs | [] | [] = xs
split-and xs | [] | (y ∷ _) = y
split-and xs | (y ∷ _) = y

drop-hyphen : String → String
drop-hyphen xs with (split '-' xs)
drop-hyphen xs | [] = xs
drop-hyphen xs | ("" ∷ x ∷ _) = x
drop-hyphen xs | (x ∷ _) = x

rem-dot-str : String → String
rem-dot-str = fromList ∘ (rem-dot '.') ∘ toList

parse-ordinal : String → Maybe Nat
parse-ordinal "first" = just 1
parse-ordinal "second" = just 2
parse-ordinal "third" = just 3
parse-ordinal "forth" = just 4
parse-ordinal "fourth" = just 4
parse-ordinal "fifth" = just 5
parse-ordinal _ = nothing

parse-eq-single : List String → Maybe Equip
parse-eq-single ("a" ∷ t1 ∷ "microchip" ∷ _) = just (equip chip (drop-hyphen t1))
parse-eq-single ("a" ∷ t1 ∷ "generator" ∷ _) = just (equip gener (drop-hyphen t1))
parse-eq-single _ = nothing

parse-eq-list : Nat → String → Maybe FloorDesc
parse-eq-list f "nothing relevant." = just (floor f [])
parse-eq-list f xs = output
  where
    parts : List String
    parts = ((split ',') ∘ split-and ∘ rem-dot-str) xs
    output : Maybe FloorDesc
    output with ((hard-unmaybe ∘ (map (parse-eq-single ∘ words))) parts)
    output | nothing = nothing
    output | (just ys) = just (floor f (quick-sort lt-equip ys))

parse-line-w : List String → Maybe FloorDesc
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ "nothing" ∷ _) with (parse-ordinal ordinal)
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ "nothing" ∷ _) | (just f) = just (floor f [])
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ "nothing" ∷ _) | nothing = nothing
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ xs) with (parse-ordinal ordinal)
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ xs) | (just f) = parse-eq-list f (unwords xs)
parse-line-w (_ ∷ ordinal ∷ "floor" ∷ "contains" ∷ xs) | _ = nothing
parse-line-w _ = nothing

parse-line : String → Maybe FloorDesc
parse-line = parse-line-w ∘ words

parse-batch : String → EqState
--parse-batch x = ((eqs 1) ∘ (map equip-on) ∘ (fromMaybe []) ∘ hard-unmaybe ∘ (map parse-line) ∘ lines) x
parse-batch x = ((eqs 1) ∘ (map equip-on) ∘ unmaybe ∘ (map parse-line) ∘ lines) x []

atOne : {A : Set} → Nat → List (List A) → List A
atOne 0 _ = []
atOne _ [] = []
atOne 1 (x ∷ _) = x
atOne (suc l) (x ∷ xs) = atOne l xs

isIn : {A : Set} → (A → A → Bool) → A → List A → Bool
isIn eq x [] = false
isIn eq x (y ∷ ys) = if (eq x y) then true else (isIn eq x ys)

remAll : {A : Set} → (A → A → Bool) → List A → List A → List A
remAll eq [] b = []
remAll eq (x ∷ xs) b = if (isIn eq x b) then (remAll eq xs b) else x ∷ (remAll eq xs b)

atOneUp : {A : Set} → Nat → (A → A → Bool) → (A → A → Bool) → List A → List (List A) → List (List A)
atOneUp 0 eq lt _ _ = []
atOneUp _ eq lt _ [] = []
atOneUp 1 eq lt mv (x ∷ y ∷ xs) = ((remAll eq x mv) ∷ (quick-sort lt (concat (y ∷ mv ∷ []))) ∷ xs)
atOneUp (suc l) eq lt mv (x ∷ xs) = x ∷ (atOneUp l eq lt mv xs)

atOneDown : {A : Set} → Nat → (A → A → Bool) → (A → A → Bool) → List A → List (List A) → List (List A)
atOneDown 0 eq lt _ _ = []
atOneDown _ eq lt _ [] = []
atOneDown 1 eq lt _ xs = xs
atOneDown 2 eq lt mv (x ∷ y ∷ xs) = (quick-sort lt (concat (x ∷ mv ∷ []))) ∷ (remAll eq y mv) ∷ xs
atOneDown (suc l) eq lt mv (x ∷ xs) = x ∷ (atOneDown l eq lt mv xs)

curr-floor-inv : EqState → List Equip
curr-floor-inv (eqs curr xs _) = atOne curr xs

move-one-item : {A : Set} → List A → List (List A)
move-one-item = map (λ {q → q ∷ []})

move-two-item : {A : Set} → List A → List (List A)
move-two-item [] = []
move-two-item (x ∷ xs) = concat ((map (λ{q → x ∷ q ∷ []}) xs) ∷ (move-two-item xs) ∷ [])

move-max-two : {A : Set} → List A → List (List A)
move-max-two xs = concat((move-one-item xs) ∷ (move-two-item xs) ∷ [])

move-list : EqState → List Move
move-list (eqs curr xs _) = concat (up-moves ∷ down-moves ∷ [])
  where
    cargos : List (List Equip)
    cargos = move-max-two (curr-floor-inv (eqs curr xs []))
    up-moves : List Move
    up-moves = if curr < (length xs) then (map mup cargos) else []
    down-moves : List Move
    down-moves = if 1 < curr then (map mdown cargos) else []

apply-move : Move → EqState → EqState
apply-move (mup inv) (eqs curr xs mvs) = (eqs (suc curr) (atOneUp curr eq-equip lt-equip inv xs) (mup inv ∷ mvs))
apply-move (mdown inv) (eqs curr xs mvs) = (eqs (pred curr) (atOneDown curr eq-equip lt-equip inv xs) (mdown inv ∷ mvs))

has-gen : List Equip → Equip → Bool
has-gen gens chp = isIn eq-equip (right-gen chp) gens

valid-floor : List Equip → Bool
valid-floor [] = true
valid-floor xs = (length gens ==n 0) ∨ (all (has-gen gens) chips)
  where
    chips : List Equip
    chips = filterᵇ is-chip xs
    gens : List Equip
    gens = filterᵇ (not ∘ is-chip) xs

unpack-history : EqState → List String
unpack-history (eqs curr xs mvs) = prior-states
  where
    prior-states : List String
    prior-states = ((map show-state) ∘ (scanr apply-move (eqs curr xs [])) ∘ reverse ∘ (map rev-move)) mvs

contains-repeats : EqState → Bool
contains-repeats (eqs curr xs mvs) = isIn _==_ current-str prior-states
  where
    current-str : String
    current-str = show-state (eqs curr xs mvs)
    prior-states : List String
    prior-states = (take ((length mvs) - 1) ∘ unpack-history) (eqs curr xs mvs)

valid-state : Nat → EqState → Bool
valid-state cap (eqs curr xs mvs) = all valid-floor xs ∧ (length mvs < cap) ∧ not (contains-repeats (eqs curr xs mvs))

is-n-down : Nat → EqState → Bool
is-n-down s (eqs curr xs mvs) with (head mvs)
is-n-down s (eqs curr xs mvs) | (just (mdown eqls)) = s ==n length eqls
is-n-down s (eqs curr xs mvs) | _ = false

is-n-up : Nat → EqState → Bool
is-n-up s (eqs curr xs mvs) with (head mvs)
is-n-up s (eqs curr xs mvs) | (just (mup eqls)) = s ==n length eqls
is-n-up s (eqs curr xs mvs) | _ = false

prefer-one-down : List EqState → List EqState
prefer-one-down xs with (any (is-n-down 1) xs)
prefer-one-down xs | true = filterᵇ (not ∘ is-n-down 2) xs
prefer-one-down xs | false = xs

prefer-two-up : List EqState → List EqState
prefer-two-up xs with (any (is-n-up 2) xs)
prefer-two-up xs | true = filterᵇ (not ∘ is-n-up 1) xs
prefer-two-up xs | false = xs

valid-next-states : Nat → EqState → List EqState
valid-next-states cap state = (prefer-two-up ∘ prefer-one-down ∘ filterᵇ (valid-state cap) ∘ map (λ {q → apply-move q state }) ∘ move-list) state

at-top-floor : EqState → Bool
at-top-floor (eqs curr xs mvs) with xs
at-top-floor (eqs curr xs mvs) | ([] ∷ [] ∷ [] ∷ ys) = true
at-top-floor (eqs curr xs mvs) | _ = false

show-minimal-moves : String → String
show-minimal-moves x = output ++ "\n"
  where
    init-state : EqState
    init-state = parse-batch x
    final-state : Maybe EqState
    final-state = search-rec-breadth-dedup 10000000 show-anon-state2 at-top-floor (valid-next-states 2000) (init-state ∷ [])
    output : String
    output with final-state
    output | nothing = "no path found"
    output | (just fstt) = "steps: " ++ show (length (EqState.hist fstt)) ++ "\n" ++ (intersperse "," ∘ map show-move) (EqState.hist fstt) ++ "\n" ++ show-state fstt


test-split-and : split-and "The first floor contains a hydrogen-compatible microchip and a lithium-compatible microchip." ≡ "The first floor contains a hydrogen-compatible microchip, a lithium-compatible microchip."
test-split-and = refl

test-parse-single-eq : parse-eq-single (words " a hydrogen-compatible microchip") ≡ just (equip chip "hydrogen")
test-parse-single-eq = refl

test-big-split : ((split ',') ∘ split-and ∘ rem-dot-str) " a hydrogen-compatible microchip and a lithium-compatible microchip." ≡ " a hydrogen-compatible microchip" ∷ " a lithium-compatible microchip" ∷ []
test-big-split = refl

test-parse-line-a : (parse-line "The first floor contains a hydrogen-compatible microchip and a lithium-compatible microchip.") ≡ just (floor 1 ((equip chip "hydrogen") ∷ (equip chip "lithium") ∷ []))
test-parse-line-a = refl

test-parse-line-b : (parse-line "The second floor contains a hydrogen generator.") ≡ just (floor 2 ((equip gener "hydrogen") ∷ []))
test-parse-line-b = refl

test-parse-line-c : (parse-line "The third floor contains a lithium generator.") ≡ just (floor 3 ((equip gener "lithium") ∷ []))
test-parse-line-c = refl

test-parse-line-d : (parse-line "The fourth floor contains nothing relevant.") ≡ just (floor 4 [])
test-parse-line-d = refl

test-fixture : String
test-fixture = "The first floor contains a hydrogen-compatible microchip and a lithium-compatible microchip.\n" ++
  "The second floor contains a hydrogen generator.\n" ++
  "The third floor contains a lithium generator.\n" ++
  "The fourth floor contains nothing relevant."

fixt-lm : Equip
fixt-lm = equip chip "lithium"

fixt-hm : Equip
fixt-hm = equip chip "hydrogen"

fixt-lg : Equip
fixt-lg = equip gener "lithium"

fixt-hg : Equip
fixt-hg = equip gener "hydrogen"

test-show-equip : (unlines ∘ map (intersperse "," ∘ map show-equip)) (EqState.eql (parse-batch test-fixture)) ≡ "hyM,liM\nhyG\nliG\n"
test-show-equip = refl

test-move-list : (unlines ∘ (map show-move) ∘ move-list ∘ parse-batch) test-fixture ≡ "up:hyM\nup:liM\nup:hyM,liM"
test-move-list = refl

test-show-state : (show-state ∘ parse-batch) test-fixture ≡
  "1  E  hyM,liM\n" ++
  "2     hyG\n" ++
  "3     liG\n" ++
  "4     "
test-show-state = refl

test-apply-move : (show-state ∘ apply-move (mup (fixt-hm ∷ [])) ∘ parse-batch) test-fixture ≡
  "1     liM\n" ++
  "2  E  hyM,hyG\n" ++
  "3     liG\n" ++
  "4     "
test-apply-move = refl

test-valid-state-a : ((valid-state 10) ∘ apply-move (mup (fixt-hm ∷ [])) ∘ parse-batch) test-fixture ≡ true
test-valid-state-a = refl

test-valid-state-b : ((valid-state 10) ∘ apply-move (mup (fixt-lm ∷ [])) ∘ parse-batch) test-fixture ≡ false
test-valid-state-b = refl

test-contains-repeats-a : (contains-repeats ∘ apply-move (mup (fixt-hm ∷ [])) ∘ parse-batch) test-fixture ≡ false
test-contains-repeats-a = refl

test-contains-repeats-b : (contains-repeats ∘ apply-move (mdown (fixt-hm ∷ [])) ∘ apply-move (mup (fixt-hm ∷ [])) ∘ parse-batch) test-fixture ≡ true
test-contains-repeats-b = refl

test-valid-next-states : (unlines ∘ (map show-state) ∘ (valid-next-states 10))
  (eqs 2
  (
    (fixt-lm ∷ []) ∷
    (fixt-hm ∷ fixt-hg ∷ []) ∷
    (fixt-lg ∷ []) ∷
    [] ∷ [])
  (mup (fixt-hm ∷ []) ∷ [])
  ) ≡
    "1     liM\n2     \n3  E  hyM,hyG,liG\n4     "
test-valid-next-states = refl

--slow on type-check but fast when compiled
--test-show-minimal-moves : show-minimal-moves test-fixture ≡
--  "steps: 11\n" ++
--  "up:liM,liG,up:liM,liG,up:liM,liG,down:liG,down:liG,down:liG,up:hyM,hyG,down:hyG,up:liG,hyG,up:hyG,hyM,up:hyM\n" ++
--  "1     \n" ++
--  "2     \n" ++
--  "3     \n" ++
--  "4  E  hyM,liM,hyG,liG"
--test-show-minimal-moves = refl

test-fixture2 : String
test-fixture2 =
  "The first floor contains a polonium generator, a thulium generator, a thulium-compatible microchip, a promethium generator, a ruthenium generator, a ruthenium-compatible microchip, a cobalt generator, and a cobalt-compatible microchip, a elerium generator, a elerium-compatible microchip, a dilithium generator, a dilithium-compatible microchip.\n" ++
  "The second floor contains a polonium-compatible microchip and a promethium-compatible microchip.\n" ++
  "The third floor contains nothing relevant.\n" ++
  "The fourth floor contains nothing relevant."

test-parse-batch-2 : show-anon-state (parse-batch test-fixture2) ≡
  "1  E  0M,1M,2M,3M,4M,0G,1G,2G,5G,6G,3G,4G\n" ++
  "2     5M,6M\n" ++
  "3     \n" ++
  "4     "
test-parse-batch-2 = refl

test-parse-batch-3 : show-anon-state2 (parse-batch test-fixture2) ≡
  "1  E  M5G7\n" ++
  "2     M2G0\n" ++
  "3     M0G0\n" ++
  "4     M0G0"
test-parse-batch-3 = refl
