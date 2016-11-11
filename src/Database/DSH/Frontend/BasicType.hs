-- | BasicType type class.  This module exists only to break horrible cyclic
-- dependencies resulting from usage of pervaisve usage of TH
module Database.DSH.Frontend.BasicType where

class BasicType a where
