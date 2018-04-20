module Output where

import Visualiser
import FMD
import CST

produceGraph :: FMD -> String
produceGraph = visualise

produceMzn :: FMD -> CST -> Maybe PredicateItem -> String
produceMzn fmd (Model is) mPredicate =
  rest ++ "\n" ++ constraints ++ "\n" ++ predicate
  where constraints = show $ Model $ fmdToItems fmd
        predicate = case mPredicate of
                      Just x -> show x ++ ";"
                      _ -> ""
        rest = show $ Model $ filter f is
        f (IConstraintItem _) = False
        f _ = True
