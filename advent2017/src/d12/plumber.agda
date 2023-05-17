module d12.plumber where

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


record Prog : Set where
  constructor prg
  field
    name : Nat
    linked : List Nat

parse-row-w : List String → Maybe Prog
parse-row-w (nm ∷ "<->" ∷ xs) with (readMaybe 10 nm)
parse-row-w (nm ∷ "<->" ∷ xs) | nothing = nothing
parse-row-w (nm ∷ "<->" ∷ xs) | just (n) = just (prg n ((unmaybe ∘ map (readMaybe 10 ∘ fromList ∘ rem-dot ',' ∘ toList)) xs))
parse-row-w _ = nothing

parse-row : String → Maybe Prog
parse-row = parse-row-w ∘ words

show-prog : Prog → String
show-prog (prg n xs) = show n ++ " <-> " ++ (intersperse ", " ∘ map show) xs

add-all-found : LookupNatTree Bool → List Nat → LookupNatTree Bool
add-all-found db [] = db
add-all-found db (x ∷ xs) = add-all-found (set-tree x true db) xs

connected-from-node-h : Nat → LookupNatTree Bool → List Nat → LookupNatTree Prog → List Nat
connected-from-node-h 0 _ _ _ = []
connected-from-node-h (suc lm) found new-group nodes = output
  where
    neighbors : List Nat
    neighbors = (concat ∘ map Prog.linked ∘ unmaybe ∘ map (λ {q → read-tree q nodes})) new-group
    new-found : LookupNatTree Bool
    new-found = add-all-found found new-group
    new-neigh : List Nat
    new-neigh = filterᵇ (λ {q → not (has-val q new-found)}) neighbors
    output : List Nat
    output with new-neigh
    output | [] = (map proj₁ ∘ all-kv) new-found
    output | _ = connected-from-node-h lm new-found new-neigh nodes

connected-from-node : Nat → List Prog → List Nat
connected-from-node start nodes = (quick-sort _<_ ∘ connected-from-node-h (suc (length nodes)) (build-nat-tree []) (start ∷ [])) ( build-nat-tree (map (λ {q → Prog.name q , q}) nodes))

connected-groups-h : Nat → List Prog → List (List Nat) → List (List Nat)
connected-groups-h 0 _ _ = []
connected-groups-h _ [] xs = xs
connected-groups-h (suc lm) nodes xs = connected-groups-h lm remaining (first-group ∷ xs)
  where
    start : Nat
    start = (Prog.name ∘ fromMaybe (prg 0 []) ∘ head) nodes
    first-group : List Nat
    first-group = connected-from-node start nodes
    found : LookupNatTree Bool
    found = build-nat-tree (map (λ {q → q , true}) first-group)
    remaining : List Prog
    remaining = filterᵇ (λ {q → not(has-val (Prog.name q) found)}) nodes

connected-groups : List Prog → List (List Nat)
connected-groups nodes = connected-groups-h (suc(length nodes)) nodes []

show-connected : List Nat → String
show-connected xs = "{" ++ (intersperse ", " ∘ map show) xs ++ "}, size: " ++ show (length xs)

show-groups : List (List Nat) → String
show-groups xs = (intersperse "|" ∘ map show ∘ map length) xs ++ "\ntotal: " ++ show (length xs)

connected-to-root : String → String
connected-to-root x = (show-connected ∘ connected-from-node 0) nodes ++ "\n"
  where
    nodes : List Prog
    nodes = (unmaybe ∘ map parse-row ∘ lines) x

not-connected-to-root : String → String
not-connected-to-root x = (show-groups ∘ connected-groups) nodes ++ "\n"
  where
    nodes : List Prog
    nodes = (unmaybe ∘ map parse-row ∘ lines) x

test-parse-row : (show-prog ∘ fromMaybe (prg 0 []) ∘ parse-row) "3 <-> 2, 4" ≡ "3 <-> 2, 4"
test-parse-row = refl

test-fixture : String
test-fixture = "0 <-> 2\n" ++
  "1 <-> 1\n" ++
  "2 <-> 0, 3, 4\n" ++
  "3 <-> 2, 4\n" ++
  "4 <-> 2, 3, 6\n" ++
  "5 <-> 6\n" ++
  "6 <-> 4, 5"

test-prog : List Prog
test-prog = (unmaybe ∘ map parse-row ∘ lines) test-fixture

test-connected : show-connected (connected-from-node 0 test-prog) ≡ "{0, 2, 3, 4, 5, 6}, size: 6"
test-connected = refl

test-connected-groups : show-groups (connected-groups test-prog) ≡ "1|6\ntotal: 2"
test-connected-groups = refl

