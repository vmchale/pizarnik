module F ( thread ) where

thread :: [a -> a] -> a -> a
thread = foldr (.) id
