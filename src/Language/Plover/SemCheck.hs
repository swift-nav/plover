module Language.Plover.SemCheck where

import Language.Plover.Types
import Data.Map

data GlobalDefs = GlobalDefs { bindings :: Map Variable DefBinding }

