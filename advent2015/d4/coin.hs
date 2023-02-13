import Data.Digest.Pure.MD5
import Data.ByteString.Lazy.Char8

hash_it :: String -> String
hash_it x = show ( md5 (pack x) )

hash_with_salt :: String -> Int -> String
hash_with_salt salt idx = hash_it (salt ++ (show idx))

has_leading :: String -> Bool
has_leading ('0' : '0' : '0' : '0' : '0' : '0' : xs) = True
has_leading _ = False

find_hash :: String -> [Int] -> Int
find_hash salt [] = -1
find_hash salt (idx : xs) = if has_leading (hash_with_salt salt idx)
   then idx
   else find_hash salt xs

calc_hash :: String -> String
calc_hash salt = (show (find_hash salt [1..100000000])) ++ "\n"

main :: IO ()
main = Prelude.interact calc_hash

