module d13.scan where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap ; is-in ; unique-insert) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; unique-list)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar ; padLeft)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primToLower)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record Scanner : Set where
  constructor scanr
  field
    depth : Nat
    range : Nat
    current : Nat

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

parse-scanner : String → Maybe Scanner
parse-scanner inp with (wordsByᵇ (λ {q → q ==c ':'}) inp)
parse-scanner inp | x ∷ y ∷ [] with ((readMaybe 10 ∘ trim) x , (readMaybe 10 ∘ trim) y)
parse-scanner inp | x ∷ y ∷ [] | (just a , just b) = just (scanr a b 0)
parse-scanner inp | x ∷ y ∷ [] | _ = nothing
parse-scanner inp | _ = nothing

show-scanner : Scanner → String
show-scanner (scanr a b _) = show a ++ ": " ++ show b

show-scanner-d : Scanner → String
show-scanner-d (scanr d r c) = show d ++ ": " ++ show r ++ " (" ++ show c ++ ")"

increment-sc : Scanner → Scanner
increment-sc (scanr d r c) = scanr d r (mod-nat (suc c) (2 * r - 2))

at-start : Scanner → Bool
at-start (scanr _ _ 0) = true
at-start (scanr _ r x) = x ==n 0


record State : Set where
  constructor state
  field
    position : Nat
    scanners : List Scanner
    caught : List Scanner

show-state : State → String
show-state (state p xs c) = "at: " ++ show p ++ ", sc: " ++ (intersperse "|" ∘ map show-scanner-d) xs ++ ", c: " ++ (intersperse "|" ∘ map show-scanner) c

elem-at : {A : Set} → Nat → List A → Maybe A
elem-at _ [] = nothing
elem-at 0 (x ∷ _) = just x
elem-at (suc i) (_ ∷ xs) = elem-at i xs

update-state : State → Maybe State
update-state (state p xs c) with ((head ∘ filterᵇ (λ {q → not (Scanner.depth q < p)})) xs)
update-state (state p xs c) | (just x) with ((p ==n Scanner.depth x) ∧ at-start x)
update-state (state p xs c) | (just x) | true = just (state (suc p) (map increment-sc xs) (x ∷ c))
update-state (state p xs c) | (just x) | false = just (state (suc p) (map increment-sc xs) c)
update-state (state p xs c) | _ = nothing

final-state-h : Nat → State → State
final-state-h 0 st = st
final-state-h (suc lm) st with (update-state st)
final-state-h (suc lm) st | (just new-st) = final-state-h lm new-st
final-state-h (suc lm) st | nothing = st

final-state : State → State
final-state st = final-state-h ((suc ∘ foldr max 0 ∘ map Scanner.depth ∘ State.scanners) st) st

damage : List Scanner → Nat
damage = foldr _+_ 0 ∘ map (λ {(scanr a b _) → a * b})

show-summary : (Nat × State) → String
show-summary (idx , state _ _ c) = "delay: " ++ show idx ++ ", damage: " ++ show (damage c)

delay : (Nat × State) → (Nat × State)
delay (idx , state p xs c) = (suc idx , state p (map increment-sc xs) c)

delay-until-perfect : Nat → (Nat × State) → Maybe (Nat × State)
delay-until-perfect 0 _ = nothing
delay-until-perfect (suc lm) (idx , st) = output
  where
    final : State
    final = final-state st
    dmg : Nat
    dmg = (length ∘ State.caught) final
    output : Maybe (Nat × State)
    output with (dmg)
    output | 0 = just (idx , final)
    output | _ = delay-until-perfect lm (delay (idx , st))

final-scanner-state : String → String
final-scanner-state x = output ++ "\n"
  where
    scanners : List Scanner
    scanners = (unmaybe ∘ map parse-scanner ∘ lines) x
    init-state : State
    init-state = state 0 scanners []
    sol : Maybe (Nat × State)
    sol = delay-until-perfect 100000000 (0 , init-state)
    output : String
    output with sol
    output | nothing = "no solution found."
    output | just (idx , st) = show-summary (idx , st)

test-parse-row : (show-scanner ∘ fromMaybe (scanr 0 0 0) ∘ parse-scanner) "1: 2" ≡ "1: 2"
test-parse-row = refl

test-fixture : String
test-fixture = "0: 3\n" ++
  "1: 2\n" ++
  "4: 4\n" ++
  "6: 4"

test-scanners : List Scanner
test-scanners = (unmaybe ∘ map parse-scanner ∘ lines) test-fixture

test-final-state : (show-state ∘ final-state) (state 0 test-scanners []) ≡
  "at: 7, sc: 0: 3 (3)|1: 2 (1)|4: 4 (1)|6: 4 (1), c: 6: 4|0: 3"
test-final-state = refl

test-delay-until-perfect : final-scanner-state test-fixture ≡ "delay: 10, damage: 0\n"
test-delay-until-perfect = refl
