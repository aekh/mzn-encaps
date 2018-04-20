{-| -}
module Visualiser where

import qualified Data.Graph.Inductive as GI
import qualified Data.Maybe as DM

import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes.Complete as GV
import Data.GraphViz.Printing (toDot, renderDot)
--import           Data.GraphViz.Types.Generalised   as G
--import           Data.GraphViz.Types.Monadic
import qualified Data.Text.Lazy                    as L
import           Data.Word
--import           WriteRunDot

import FMD

visualise :: FMD -> String
visualise fmd =
  L.unpack $ renderDot $ toDot $ GV.graphToDot ex1Params $ fmdToInductive fmd

fmdToInductive :: FMD -> GI.Gr L.Text L.Text
fmdToInductive (FMD _ vs es) =
  GI.mkGraph (map vertexToGINode (zip [0..] vs)) (map edgeToGIEdge es)

vertexToGINode :: (Int, Vertex) -> GI.LNode L.Text
vertexToGINode (i, Vertex expr) = (i, L.pack (show expr))

edgeToGIEdge :: Edge -> GI.LEdge L.Text
edgeToGIEdge (Edge r i1 i2) = (i1, i2, L.pack (show r))

ex1Params :: GV.GraphvizParams n L.Text L.Text () L.Text
ex1Params = GV.nonClusteredParams { GV.globalAttributes = ga
                                  , GV.fmtNode          = fn
                                  , GV.fmtEdge          = fe
                                  }
  where fn (_,l)   = [GV.textLabel l]
        fe (_,_,l) = [GV.textLabel l]

        ga = [ GV.GraphAttrs [ GV.RankDir   GV.FromLeft
                             , GV.BgColor   [GV.toWColor GV.White]
                             ]
             , GV.NodeAttrs  [ GV.shape     GV.Circle
                             , GV.FillColor (myColorCL 2)
                             , GV.style     GV.filled
                             ]
             ]

myColorCL :: Word8 -> GV.ColorList
myColorCL n | n == 1 = c $ (GV.RGB 127 108 138)
            | n == 2 = c $ (GV.RGB 175 177 112)
            | n == 3 = c $ (GV.RGB 226 206 179)
            | n == 4 = c $ (GV.RGB 172 126 100)
 where c rgb = GV.toColorList [rgb]

myColor :: Word8 -> GV.Attribute
myColor n = GV.Color $ myColorCL n
