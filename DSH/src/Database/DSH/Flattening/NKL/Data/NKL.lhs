%if False
\begin{code}
{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving  #-}
module Database.DSH.Flattening.NKL.Data.NKL 
  ( Expr(..)
  , Typed(..)
  , freeVars
  , Prim1Op(..)
  , Prim2Op(..)
  , Prim1(..)
  , Prim2(..)
  , Column
  , Key
  ) where

import           Text.PrettyPrint.HughesPJ

import           Database.DSH.Flattening.Common.Data.Op
import           Database.DSH.Flattening.Common.Data.Val(Val())
import           Database.DSH.Flattening.Common.Data.Type(Type, Typed, typeOf)
  
import qualified Data.Set as S

type Column = (String, Type)

type Key = [String]
\end{code}
%endif
%{
%include syntaxdef.fmt
%include nkl.fmt
The following syntax diagram describes our input language, the Nested Kernel Language.
% The code below defines the NKL grammar
\newcommand{\NKLGrammar}{
\begin{code}
data Expr  =  Table Type String [Column] [Key]  -- \textrm{Reference database table $n$}
           |  App Type Expr Expr                -- \textrm{Application of two expressions}
           |  AppE1 Type (Prim1 Type) Expr             -- \textrm{Application of a primitive to a single argument}
           |  AppE2 Type (Prim2 Type) Expr Expr        -- \textrm{Application of a primitive to two arguments}
           |  BinOp Type Oper Expr Expr         -- \textrm{Application of a binary opertor $\oplus$ to two arguments}
           |  Lam Type String Expr              -- \textrm{Lambda abstraction}
           |  If Type Expr Expr Expr            -- \textrm{Conditional}
           |  Const Type Val                    -- \textrm{Constant value}
           |  Var Type String                   -- \textrm{Variable}
\end{code}
}
%}
\NKLGrammar

%if False
\begin{code}
instance Show Expr where
  show e = render $ pp e
  
pp :: Expr -> Doc
pp (Table _ n _ _)    = text "table" <+> text n
pp (App _ e1 e2)      = (parens $ pp e1) <+> (parens $ pp e2)
pp (AppE1 _ p1 e)     = (text $ show p1) <+> (parens $ pp e)
pp (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (parens $ pp e1) <+> (parens $ pp e2)
pp (BinOp _ o e1 e2)  = (parens $ pp e1) <+> (text $ show o) <+> (parens $ pp e2)
pp (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pp e
pp (If _ c t e)       = text "if" <+> pp c <+> text "then" <+> (parens $ pp t) <+> text "else" <+> (parens $ pp e)
pp (Const _ v)        = text $ show v
pp (Var _ s)          = text s

deriving instance Eq Expr
deriving instance Ord Expr
\end{code}
%endif

The primitive operations supported by the NKL are the following:

Unary primitive operations:
%{
%include syntaxdef.fmt
%include NKLPrims.fmt
\begin{code}
data Prim1Op = Length |  Not |  Concat 
             | Sum | Avg | The | Fst | Snd 
             | Head | Minimum | Maximum 
             | IntegerToDouble | Tail 
             | Reverse | And | Or 
             | Init | Last | Nub 
             deriving (Eq, Ord)
             
data Prim1 t = Prim1 Prim1Op t deriving (Eq, Ord)
\end{code}

%if False
\begin{code}

instance Show Prim1Op where
  show Length = "length"
  show Not = "not"
  show Concat = "concat"
  show Sum = "sum"
  show Avg = "avg"
  show The = "the"
  show Fst = "fst"
  show Snd = "snd"
  show Head = "head"
  show Minimum = "minimum"
  show Maximum = "maximum"
  show IntegerToDouble = "integerToDouble"
  show Tail = "tail"
  show Reverse = "reverse"
  show And = "and"
  show Or = "or"
  show Init = "init"
  show Last = "last"
  show Nub = "nub"
  
instance Show (Prim1 t) where
  show (Prim1 o _) = show o

\end{code}
%endif

Binary primitive operations:

\begin{code}
data Prim2Op = Map | GroupWithKey
             | SortWith | Pair
             | Filter | Append
             | Index | Take
             | Drop | Zip
             | TakeWhile
             | DropWhile
             | CartProduct
             deriving (Eq, Ord)
             
data Prim2 t = Prim2 Prim2Op t deriving (Eq, Ord)
\end{code}
%}
%if False
\begin{code}
instance Show Prim2Op where
  show Map = "map"
  show GroupWithKey = "groupWithKey"
  show SortWith = "sortWith"
  show Pair = "pair"
  show Filter = "filter"
  show Append = "append"
  show Index = "index"
  show Take = "take"
  show Drop = "drop"
  show Zip = "zip"
  show TakeWhile = "takeWhile"
  show DropWhile = "dropWhile"
  show CartProduct = "cartProduct"
  
instance Show (Prim2 t) where
  show (Prim2 o _) = show o

\end{code}
\begin{code}
instance Typed Expr where
    typeOf (Table t _ _ _) = t
    typeOf (App t _ _) = t
    typeOf (AppE1 t _ _) = t
    typeOf (AppE2 t _ _ _) = t
    typeOf (Lam t _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
\end{code}
%endif

We define a function |fvs| to compute the set of free variable in an NKL-expression:
%{
%include nkl.fmt
%format (freeVars (x)) = " fvs (" x ") "
%format `S.union` = " \cup "
%format S.empty = " \emptyset "
%format (S.singleton (x)) = " \{ x \} "

\begin{code}
freeVars :: Expr -> S.Set String
freeVars (Table _ _ _ _) = S.empty
freeVars (App _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (AppE1 _ _ e1) = freeVars e1
freeVars (AppE2 _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Lam _ x e) = (freeVars e) S.\\ S.singleton x
freeVars (If _ e1 e2 e3) = freeVars e1 `S.union` freeVars e2 `S.union` freeVars e3
freeVars (BinOp _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Const _ _) = S.empty
freeVars (Var _ x) = S.singleton x
\end{code}
%}
