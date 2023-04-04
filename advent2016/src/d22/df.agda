
module d22.df where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; build-str-tree ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth-dedup)
open import util.hash using (hash-md5)
open import util.nat_stuff using (mod-nat ; div-nat ; lin-mod-system)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
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
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record DFSize : Set where
  constructor dfs
  field
    name : Nat × Nat
    size : Nat
    used : Nat
    avail : Nat

record DFMove : Set where
  constructor dfm
  field
    lhs : Nat × Nat
    rhs : Nat × Nat

eq-pt : Nat × Nat → Nat × Nat → Bool
eq-pt (a , b) (c , d) = (a ==n c) ∧ (b ==n d)

eq-move : DFMove → DFMove → Bool
eq-move (dfm p1 p2) (dfm q1 q2) = (eq-pt p1 q1) ∧ (eq-pt p2 q2)

show-move : DFMove → String
show-move (dfm (x1 , y1) (x2 , y2)) = show x1 ++ "," ++ show y1 ++ "->" ++ show x2 ++ "," ++ show y2

record  DFSit : Set where
  constructor dfsit
  field
    db : LookupNatTree DFSize
    blanks : LookupNatTree Bool
    goal : Nat × Nat
    hist : List DFMove

has-last-move : DFMove → DFSit → Bool
has-last-move m1 sit with (DFSit.hist sit)
has-last-move m1 sit | [] = false
has-last-move m1 sit | (m2 ∷ _) = eq-move m1 m2

show-df : DFSize → String
show-df (dfs (x , y) _ _ _) = show x ++ "," ++ show y

show-df-all : DFSize → String
show-df-all (dfs (x , y) sz us av) = show-df (dfs (x , y) sz us av) ++ ": " ++ show us ++ "/" ++ show sz

show-sit-anon : DFSit → String
show-sit-anon (dfsit _ bl (x , y) _) = show x ++ "," ++ show y ++ "|" ++ (intersperse "," ∘ map show ∘ map proj₁ ∘ all-kv) bl

show-sit : DFSit → String
show-sit (dfsit db bl (x , y) _) = "goal: " ++ show x ++ "," ++ show y ++ "\n" ++ unlines df-list
  where
    df-list : List String
    df-list = (map show-df-all ∘ map proj₂ ∘ all-kv) db

neighbors : Nat × Nat → List (Nat × Nat)
neighbors (0 , 0) = (1 , 0) ∷ (0 , 1) ∷ []
neighbors (0 , suc y) = (1 , suc y) ∷ (0 , suc (suc y)) ∷ (0 , y) ∷ []
neighbors (suc x , 0) = ((suc x) , 1) ∷ (suc (suc x) , 0) ∷ (x , 0) ∷ []
neighbors (suc x , suc y) = (suc x , y) ∷ (suc (suc x) , suc y) ∷ (suc x , suc (suc y)) ∷ (x , (suc y)) ∷ []

nid : Nat × Nat → Nat
nid (x , y) = 100 * x + y

rem-t : String → String
rem-t = fromList ∘ rem-dot 'T' ∘ toList

rem-fst : String → String
rem-fst = fromList ∘ drop 1 ∘ toList

parse-node-w : List String → Maybe (Nat × Nat)
parse-node-w ("node" ∷ xm ∷ ym ∷ _) with ((readMaybe 10 ∘ rem-fst) xm , (readMaybe 10 ∘ rem-fst) ym)
parse-node-w ("node" ∷ xm ∷ ym ∷ _) | (just x , just y) = just (x , y)
parse-node-w ("node" ∷ xm ∷ ym ∷ _) | _ = nothing
parse-node-w _ = nothing

parse-name-w : List String → Maybe (Nat × Nat)
parse-name-w ("" ∷ "dev" ∷ "grid" ∷ nodename ∷ _) = parse-node-w (split '-' nodename)
parse-name-w _ = nothing

parse-name : String → Maybe (Nat × Nat)
parse-name = parse-name-w ∘ split '/'

parse-line-w : List String → Maybe DFSize
parse-line-w (nmm ∷ szm ∷ usm ∷ avm ∷ _) with (parse-name nmm , (readMaybe 10 ∘ rem-t) szm)
parse-line-w (nmm ∷ szm ∷ usm ∷ avm ∷ _) | (just nm , just sz ) with ((readMaybe 10 ∘ rem-t) usm , (readMaybe 10 ∘ rem-t) avm)
parse-line-w (nmm ∷ szm ∷ usm ∷ avm ∷ _) | (just nm , just sz ) | (just us , just av ) = just (dfs nm sz us av)
parse-line-w (nmm ∷ szm ∷ usm ∷ avm ∷ _) | (just nm , just sz ) | _ = nothing
parse-line-w (nmm ∷ szm ∷ usm ∷ avm ∷ _) | _ = nothing
parse-line-w _ = nothing

parse-line : String → Maybe DFSize
parse-line = parse-line-w ∘ words

parse-batch : String → LookupNatTree DFSize
parse-batch = build-nat-tree ∘ map (λ {q → nid (DFSize.name q) , q}) ∘ unmaybe ∘ map parse-line ∘ lines

get-neigh :  DFSize → LookupNatTree DFSize → List DFSize
get-neigh nd db = unmaybe (map (λ { q → read-tree (nid q) db }) (neighbors (DFSize.name nd)))

is-viable : DFSize → DFSize → Bool
is-viable (dfs nm1 sz1 us1 av1) (dfs nm2 sz2 us2 av2) = (0 < us1) ∧ (us1 < av2) ∧ not (nid nm1 ==n nid nm2)

add-front : {A : Set} → A × List A → List (A × A)
add-front (x , xs) = map (λ {q → x , q}) xs

all-viable : LookupNatTree DFSize → List (DFSize × DFSize)
all-viable db = concat viable-neigh
  where
    all-nodes : List DFSize
    all-nodes = (map proj₂ ∘ all-kv) db
    viable-neigh : List (List (DFSize × DFSize))
    viable-neigh = map (filterᵇ (uncurry is-viable) ∘ add-front ∘ λ {q → q , all-nodes}) all-nodes 

count-viable : String → String
count-viable x = "viable: " ++ (show ∘ length ∘ all-viable) db ++ "\n"
  where
    db : LookupNatTree DFSize
    db = parse-batch x

is-done : DFSit → Bool
is-done (dfsit db bl (x , y) h) = (x ==n 0) ∧ (y ==n 0)

apply-move-db : DFMove → LookupNatTree DFSize → LookupNatTree DFSize
apply-move-db (dfm p1 p2) db = output
  where
    output : LookupNatTree DFSize
    output with (read-tree (nid p1) db)
    output | (just n1) with (read-tree (nid p2) db)
    output | (just n1) | (just n2) = set-tree (nid p2) (dfs p2 (DFSize.size n2) (DFSize.used n1 + DFSize.used n2) (DFSize.size n2 - DFSize.used n2 - DFSize.used n1)) (set-tree (nid p1) (dfs p1 (DFSize.size n1) 0 (DFSize.size n1)) db)
    output | (just n1) | _ = db
    output | _ = db
    
apply-move : DFMove → DFSit → DFSit
apply-move (dfm p1 p2) (dfsit db bl g h) = (dfsit new-db new-blank new-goal ((dfm p1 p2) ∷ h))
  where
    new-db : LookupNatTree DFSize
    new-db = apply-move-db (dfm p1 p2) db
    new-blank : LookupNatTree Bool
    new-blank = rem-tree (nid p2) (set-tree (nid p1) true bl)
    new-goal : Nat × Nat
    new-goal = if (eq-pt p1 g) then p2 else g

next-moves : DFSit → List DFSit
next-moves (dfsit db bl g h) = map (λ {q → apply-move q (dfsit db bl g h)}) new-moves
  where
    all-nodes : List DFSize
    all-nodes = (map proj₂ ∘ all-kv) db
    viable-neigh : List (DFSize × DFSize)
    viable-neigh = concat (map (filterᵇ (uncurry is-viable) ∘ add-front ∘ λ {q → q , get-neigh q db}) all-nodes)
    new-moves : List DFMove
    new-moves = map (λ {((dfs p1 _ _ _) , (dfs p2 _ _ _)) → dfm p1 p2 }) viable-neigh

check-move-seq : DFSit → List DFMove → List DFSit
check-move-seq sit [] = sit ∷ []
check-move-seq sit (mv ∷ xs) = output
  where
    next : List DFSit
    next = next-moves sit
    output : List DFSit
    output with (any (has-last-move mv) next)
    output | true = sit ∷ (check-move-seq (apply-move mv sit) xs)
    output | false = sit ∷ []

search-bf-moves : DFSit → Maybe DFSit
search-bf-moves sit = proj₁ res
  where
    res : Maybe DFSit × LookupStrTree Bool
    res = search-rec-breadth-dedup 1000000000 show-sit-anon is-done next-moves (sit ∷ [])

list-blanks : LookupNatTree DFSize → List (Nat × Nat)
list-blanks = map DFSize.name ∘ filterᵇ (λ {(dfs _ _ us _) → us ==n 0}) ∘ map proj₂ ∘ all-kv

top-right-corner : LookupNatTree DFSize → (Nat × Nat)
top-right-corner db = (fromMaybe (0 , 0) ∘ head ∘ drop ((length top-row) - 1)) top-row
  where
    top-row : List (Nat × Nat)
    top-row = (filterᵇ (λ {q → proj₂ q ==n 0}) ∘ map DFSize.name ∘ map proj₂ ∘ all-kv) db


find-data-moves : String → String
find-data-moves x = output ++ "\n"
  where
    db : LookupNatTree DFSize
    db = parse-batch x
    init-sit : DFSit
    init-sit = dfsit db (build-nat-tree (map (λ {q → nid q , true}) (list-blanks db))) (top-right-corner db) []
    res : Maybe DFSit
    res = search-bf-moves init-sit
    output : String
    output with res
    output | (just (dfsit _ _ g hist)) = "size: " ++ show (length hist) ++ "\n" ++ (intersperse "|" ∘ map show-move) hist
    output | _ = "no solution found."

test-parse-name-a : parse-name "/dev/grid/node-x0-y0" ≡ just (0 , 0)
test-parse-name-a = refl

test-parse-line-a : parse-line "/dev/grid/node-x0-y0     85T   68T    17T   80%" ≡ just (dfs (0 , 0) 85 68 17)
test-parse-line-a = refl

test-get-neigh : (intersperse "|" ∘ map show-df ∘ get-neigh (dfs (0 , 2) 0 0 0)) (parse-batch (
  "/dev/grid/node-x0-y0     85T   68T    17T   80%\n" ++
  "/dev/grid/node-x0-y1     89T   66T    23T   74%\n" ++
  "/dev/grid/node-x0-y2     89T   69T    20T   77%\n" ++
  "/dev/grid/node-x0-y3     92T   71T    21T   77%\n" ++
  "/dev/grid/node-x0-y4     89T   69T    20T   77%\n"
  )) ≡ "0,3|0,1"
test-get-neigh = refl

test-fixture : String
test-fixture = (
  "Filesystem            Size  Used  Avail  Use%\n" ++
  "/dev/grid/node-x0-y0   10T    8T     2T   80%\n" ++
  "/dev/grid/node-x0-y1   11T    6T     5T   54%\n" ++
  "/dev/grid/node-x0-y2   32T   28T     4T   87%\n" ++
  "/dev/grid/node-x1-y0    9T    7T     2T   77%\n" ++
  "/dev/grid/node-x1-y1    8T    0T     8T    0%\n" ++
  "/dev/grid/node-x1-y2   11T    7T     4T   63%\n" ++
  "/dev/grid/node-x2-y0   10T    6T     4T   60%\n" ++
  "/dev/grid/node-x2-y1    9T    8T     1T   88%\n" ++
  "/dev/grid/node-x2-y2    9T    6T     3T   66%"
  )

test-list-blanks : (unlines ∘ map (λ {(x , y) → show x ++ "," ++ show y}) ∘ list-blanks) (parse-batch test-fixture)
  ≡ "1,1"
test-list-blanks = refl

test-next-moves-a : (unlines ∘ map show-sit-anon ∘ next-moves) (dfsit (parse-batch
  test-fixture) (build-nat-tree []) (0 , 2) [])
  ≡ "0,2|1\n0,2|100\n0,2|102"
test-next-moves-a = refl

test-next-moves-b : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "2,0|0\n2,0|101\n1,0|200"
test-next-moves-b = refl

test-next-moves-c : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "2,0|100\n1,0|201"
test-next-moves-c = refl

test-next-moves-d : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (2 , 1) (2 , 0)) ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "1,0|101\n1,0|200\n1,0|202"
test-next-moves-d = refl

test-next-moves-e : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (1 , 1) (2 , 1)) ∘ apply-move (dfm (2 , 1) (2 , 0)) ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "1,0|1\n1,1|100\n1,0|102\n1,0|201"
test-next-moves-e = refl

test-next-moves-f : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (0 , 1) (1 , 1)) ∘ apply-move (dfm (1 , 1) (2 , 1)) ∘ apply-move (dfm (2 , 1) (2 , 0)) ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "1,0|0\n1,0|101"
test-next-moves-f = refl

test-next-moves-g : (unlines ∘ map show-sit-anon ∘ next-moves ∘ apply-move (dfm (0 , 0) (0 , 1)) ∘ apply-move (dfm (0 , 1) (1 , 1)) ∘ apply-move (dfm (1 , 1) (2 , 1)) ∘ apply-move (dfm (2 , 1) (2 , 0)) ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡ "1,0|1\n0,0|100"
test-next-moves-g = refl

test-check-move-seq-a : (unlines ∘ map show-sit-anon ∘ check-move-seq (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) []) ∘ reverse) ((dfm (1 , 0) (0 , 0)) ∷ (dfm (0 , 0) (0 , 1)) ∷ (dfm (0 , 1) (1 , 1)) ∷ (dfm (1 , 1) (2 , 1)) ∷ (dfm (2 , 1) (2 , 0)) ∷ (dfm (2 , 0) (1 , 0)) ∷ (dfm (1 , 0) (1 , 1)) ∷ []) ≡
  "2,0|\n" ++
  "2,0|100\n" ++
  "1,0|200\n" ++
  "1,0|201\n" ++
  "1,0|101\n" ++
  "1,0|1\n" ++
  "1,0|0\n" ++
  "0,0|100"
test-check-move-seq-a = refl

test-show-sit-d : (show-sit ∘ apply-move (dfm (2 , 1) (2 , 0)) ∘ apply-move (dfm (2 , 0) (1 , 0)) ∘ apply-move (dfm (1 , 0) (1 , 1)))
  (dfsit (parse-batch test-fixture) (build-nat-tree []) (2 , 0) [])
  ≡
  "goal: 1,0\n" ++
  "0,0: 8/10\n" ++
  "0,1: 6/11\n" ++
  "0,2: 28/32\n" ++
  "1,0: 6/9\n" ++
  "1,1: 7/8\n" ++
  "1,2: 7/11\n" ++
  "2,0: 8/10\n" ++
  "2,1: 0/9\n" ++
  "2,2: 6/9"
test-show-sit-d = refl

test-find-data-moves-a : find-data-moves (
  "Filesystem            Size  Used  Avail  Use%\n" ++
  "/dev/grid/node-x0-y0   10T    0T     10T   80%\n" ++
  "/dev/grid/node-x1-y0   11T    0T     11T   54%\n" ++
  "/dev/grid/node-x2-y0   11T    6T     5T   54%\n")
  ≡ "size: 2\n1,0->0,0|2,0->1,0\n"
test-find-data-moves-a = refl

--test-find-data-moves-b : find-data-moves test-fixture
--  ≡ "size: 7\n1,0->0,0|0,0->0,1|0,1->1,1|1,1->2,1|2,1->2,0|2,0->1,0|1,0->1,1\n"
--test-find-data-moves-b = refl
