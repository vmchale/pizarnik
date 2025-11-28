module Q ( (@<>) ) where

infixr 7 @<>

(@<>) :: (Monoid m, Foldable f) => (a -> m) -> f a -> m
(@<>) = foldMap
