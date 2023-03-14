import Data.Digest.Pure.MD5
import Data.ByteString.Lazy.Char8
import Data.List

hash_it :: String -> String
hash_it x = show ( md5 (pack x) )

hash_with_salt :: String -> Int -> String
hash_with_salt salt idx = hash_it (salt ++ (show idx))

has_leading :: String -> Bool
has_leading ('0' : '0' : '0' : '0' : '0' : xs) = True
has_leading _ = False

find_hash :: String -> [Int] -> Int
find_hash salt [] = -1
find_hash salt (idx : xs) = if has_leading (hash_with_salt salt idx)
   then idx
   else find_hash salt xs

max_iter :: Int
max_iter = 10000000

find_idx_seq :: String -> Int -> Int -> [Int]
find_idx_seq salt l start = if l < 1
  then next : []
  else next : find_idx_seq salt (l - 1) (next + 1)
  where
    next :: Int
    next =  find_hash salt [start..start+max_iter] 

find_pass :: String -> [String]
find_pass salt = Prelude.map (hash_with_salt salt) (find_idx_seq salt 100 1)

calc_hash :: String -> String
calc_hash salt = "\n" ++ Data.List.concat (Data.List.intersperse "\n" (find_pass salt)) ++ "\n"

main :: IO ()
main = Prelude.interact calc_hash

