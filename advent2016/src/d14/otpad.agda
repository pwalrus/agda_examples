module d14.otpad where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth-dedup)
open import util.hash using (hash-md5)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
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
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


contains-same : Nat → List Char → Bool
contains-same 0 _ = true
contains-same 1 _ = true
contains-same 2 (x ∷ y ∷ _) = x ==c y
contains-same 2 _ = false
contains-same (suc n) (x ∷ y ∷ xs) = (x ==c y) ∧ (contains-same n (y ∷ xs))
contains-same (suc n) _ = false

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

list-ntuple-ch : Nat → List Char → List Char
list-ntuple-ch _ [] = []
list-ntuple-ch _ (_ ∷ []) = []
list-ntuple-ch _ (_ ∷ _ ∷ []) = []
list-ntuple-ch n (x ∷ xs) with (contains-same n (x ∷ xs))
list-ntuple-ch n (x ∷ xs) | true = x ∷ []
list-ntuple-ch n (x ∷ xs) | false = (list-ntuple-ch n xs)

contains-ntuple-ch : Nat → List Char → Bool
contains-ntuple-ch _ [] = false
contains-ntuple-ch _ (_ ∷ []) = false
contains-ntuple-ch _ (_ ∷ _ ∷ []) = false
contains-ntuple-ch n (x ∷ xs) = (contains-same n (x ∷ xs)) ∨ (contains-ntuple-ch n xs)

contains-triple : String → Bool
contains-triple = (contains-ntuple-ch 3) ∘ toList

isIn : {A : Set} → (A → A → Bool) → A → List A → Bool
isIn eq x [] = false
isIn eq x (y ∷ ys) = if (eq x y) then true else (isIn eq x ys)

contains-quint : String → Char → Bool
contains-quint xs ch = (isIn _==c_ ch ∘ (list-ntuple-ch 5) ∘ toList) xs

apply-n : {A : Set} → Nat → (A → A) → (A → A)
apply-n 0 _ = id
apply-n 1 f = f
apply-n (suc n) f = f ∘ (apply-n n f)

salted-hash : String → Nat → String
salted-hash salt start = (apply-n 2017 hash-md5) (salt ++ show start)

memoz : {A : Set} → LookupNatTree A → (Nat → A) → Nat → (A × LookupNatTree A)
memoz db f n with (read-tree n db)
memoz db f n | nothing with (f n)
memoz db f n | nothing | m = m , (set-tree n m db)
memoz db f n | (just m) = m , db


check-for-quints : LookupNatTree String → Nat → Nat → String → List Char → (Bool × LookupNatTree String)
check-for-quints db 0 _ _ _ = (false , db)
check-for-quints db (suc lm) start salt chs with (memoz db (salted-hash salt) start)
check-for-quints db (suc lm) start salt chs | (hsh , ndb) with (any (contains-quint hsh) chs)
check-for-quints db (suc lm) start salt chs | (hsh , ndb) | true = (true , ndb)
check-for-quints db (suc lm) start salt chs | (hsh , ndb) | false = check-for-quints ndb lm (suc start) salt chs

iter-for-triples : LookupNatTree String → Nat → Nat → String → Maybe (Nat × List Char × LookupNatTree String)
iter-for-triples db 0 _ _ = nothing
iter-for-triples db (suc lm) start salt with (memoz db (salted-hash salt) start)
iter-for-triples db (suc lm) start salt | (hsh , ndb) with (list-ntuple-ch 3 (toList hsh))
iter-for-triples db (suc lm) start salt | (hsh , ndb) | [] = iter-for-triples db lm (suc start) salt
iter-for-triples db (suc lm) start salt | (hsh , ndb) | xs with (check-for-quints ndb 1000 (suc start) salt xs)
iter-for-triples db (suc lm) start salt | (hsh , ndb) | xs | (true , nndb) = just (start , xs , ndb)
iter-for-triples db (suc lm) start salt | (hsh , ndb) | xs | (false , nndb) = iter-for-triples ndb lm (suc start) salt

find-n-keys : LookupNatTree String → Nat → Nat → Nat → String → Maybe (List (Nat × List Char))
find-n-keys db 0 _ _ _ = nothing
find-n-keys db _ 0 _ _ = just []
find-n-keys db (suc lm) (suc needed) start salt = next-keys
  where
    fst-key : Maybe (Nat × List Char × LookupNatTree String)
    fst-key = iter-for-triples db 1000000 start salt
    next-keys : Maybe (List (Nat × List Char))
    next-keys with fst-key
    next-keys | nothing = nothing
    next-keys | (just (idx , chs , ndb)) with (find-n-keys ndb lm needed (suc idx) salt)
    next-keys | (just (idx , chs , ndb)) | nothing = nothing
    next-keys | (just (idx , chs , ndb)) | (just xs) = just ((idx , chs) ∷ xs)

show-trip-list : List (Nat × List Char) → String
show-trip-list = unlines ∘ (map (λ {(n , (idx , xs)) → padRight ' ' 4 (show n) ++ padRight ' ' 8 (show idx) ++ " " ++ fromList xs})) ∘ enumerate

find-otp-index : String → String
find-otp-index x =  "\n" ++ output ++ "\n"
  where
    salt : String
    salt = (trim x)
    init-db : LookupNatTree String
    init-db = build-nat-tree ((0 , salted-hash salt 0) ∷ [])
    output : String
    output with (find-n-keys init-db 1000000 64 0 salt)
    output | nothing = "no trip found"
    output | (just xs) = show-trip-list xs

test-contains-triple-a : contains-triple "0034e0923cc38887a57bd7b1d4f953df" ≡ true
test-contains-triple-a = refl

test-contains-triple-b : contains-triple "0034e0923cc38a87a57bd7b1d4f953df" ≡ false
test-contains-triple-b = refl

test-contains-quint-a : contains-quint "0034e0923cc38887a57bd7b1d4f953df" '8' ≡ false
test-contains-quint-a = refl

test-contains-quint-b : contains-quint "3aeeeee1367614f3061d165a5fe3cac3" 'e' ≡ true
test-contains-quint-b = refl
