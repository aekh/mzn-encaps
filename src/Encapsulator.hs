module Encapsulator where

import CST
import FMD
import qualified Encapsulator.Extractor as E
import qualified Encapsulator.Ranker as R
import qualified Encapsulator.Substitutor as S
import qualified Encapsulator.Common as C

import Debug.Trace

heurs :: R.Heuristics a => [C.Heurs a]
heurs = R.heurs

atts :: [C.Attitude]
atts = R.atts

extractCST :: CST -> Int -> Int -> Int -> FMD
extractCST fmd breadth heur att =
  E.fmd fmd breadth (heurs !! heur) (atts !! att)

encapsulateFMD :: FMD -> Int -> Int -> Int -> (FMD, PredicateItem)
encapsulateFMD fmd rank heur att =
  S.substitute fmd rank (heurs !! heur) (atts !! att)

{-
transformString :: String -> Settings -> Either String String
transformString str set =
  case extractString str of
    Left err -> Left err
    Right model ->
      let cuts = A.suggest model (rank set) (heur1 set) (heur2 set)
      in Right $ show $ A.modify model (cuts !! (rank set - 1))

extractString :: String -> Either String Model
extractString str = case parseString str of
  Left err -> Left err
  Right cst -> Right $ A.model cst

listBest :: String -> Settings -> Either String String
listBest = undefined

info :: Model -> String
info = infoShowModel
-}
