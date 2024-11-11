module TS ( tsort ) where


import           Data.Graph       (graphFromEdges, reverseTopSort)
import           Nm

tsort :: [(MN, [MN])] -> [MN]
tsort adjL = snd3.f <$> reverseTopSort g
    where adjLG = fmap (\(x,y) -> ((),x,y)) adjL
          (g, f, _) = graphFromEdges adjLG

snd3 (_,y,_) = y
