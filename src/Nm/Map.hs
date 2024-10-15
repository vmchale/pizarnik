module Nm.Map ( NmMap (..)
              , insert
              , member
              , intersectionWith
              , isSubmapOf
              , elems
              , fromList
              , toList
              ) where

import           Control.Arrow  ((&&&))
import           Data.Bifunctor (first)
import qualified Data.IntMap    as IM
import qualified Data.Text      as T
import           Nm
import           Pr
import           Prettyprinter  (Pretty (pretty), vsep)

data NmMap a = NmMap { xx :: !(IM.IntMap a), context :: IM.IntMap T.Text }

instance Semigroup (NmMap a) where (<>) (NmMap x0 c0) (NmMap x1 c1) = NmMap (x0<>x1) (c0<>c1)

instance Functor NmMap where fmap f (NmMap x c) = NmMap (f<$>x) c
instance Foldable NmMap where foldMap f (NmMap x _) = foldMap f x
instance Traversable NmMap where traverse f (NmMap x c) = NmMap <$> traverse f x <*> pure c

insert :: Nm a -> b -> NmMap b -> NmMap b
insert (Nm n (U i) _) y (NmMap x ctx)= NmMap (IM.insert i y x) (IM.insert i n ctx)

member :: Nm a -> NmMap b -> Bool
member (Nm _ (U i) _) (NmMap x _) = i `IM.member` x

isSubmapOf :: NmMap a -> NmMap b -> Bool
isSubmapOf (NmMap x _) (NmMap y _) = IM.isSubmapOfBy (\_ _ -> True) x y

intersectionWith :: (a -> b -> c) -> NmMap a -> NmMap b -> NmMap c
intersectionWith f (NmMap x0 c0) (NmMap x1 c1) = NmMap (IM.intersectionWith f x0 x1) (IM.intersection c0 c1)

elems :: NmMap a -> [a]
elems (NmMap x _) = IM.elems x

toList :: NmMap a -> [(T.Text, a)]
toList (NmMap x ns) = map (first (ns IM.!)) (IM.toList x)

instance Pretty a => Pretty (NmMap a) where
    pretty nms = vsep (pB<$>Nm.Map.toList nms)

fromList :: [(Nm a, b)] -> NmMap b
fromList xs = NmMap { xx = IM.fromList [ (i,x) | (Nm _ (U i) _, x) <- xs ], context = IM.fromList (map ((unU.un) &&& text) (fst<$>xs)) }
