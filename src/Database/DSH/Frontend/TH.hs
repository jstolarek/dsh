{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Frontend.TH
    ( deriveDSH
    , deriveQA
    , deriveTA
    , deriveView
    , deriveElim
    , deriveSmartConstructors
    , generateTableSelectors
    -- FIXME don't expose tuple constructors but use qualified names
    , DSH.TupleConst(..)
    , DSH.TupElem(..)
    , DSH.Exp(..)
    , DSH.Fun(..)
    ) where

import           Control.Monad
import           Data.Char
import           Data.List

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import qualified Database.DSH.Frontend.Internals  as DSH
import           Database.DSH.Frontend.TupleTypes
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.TH

import           Database.DSH.Provenance.Where.Common


-----------------------------------------
-- Deriving all DSH-relevant instances --
-----------------------------------------

deriveDSH :: Name -> Q [Dec]
deriveDSH n = do
  qaDecs    <- deriveQA n
  -- elimDecs  <- deriveElim n
  cc        <- countConstructors n
  viewDecs  <- if cc == 1
                  then deriveView n
                  else return []
  scDecs    <- deriveSmartConstructors n
  return (qaDecs {- ++ elimDecs -} ++ viewDecs ++ scDecs)

-----------------
-- Deriving QA --
-----------------

-- | Derive QA instances for data types and newtypes.
deriveQA :: Name -> Q [Dec]
deriveQA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs _ cons _names) ->
      deriveTyConQA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs _ con  _names) ->
      deriveTyConQA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConQA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConQA name tyVarBndrs cons = do
  let context       = map (\tv -> nameTyApp ''DSH.QA (VarT (tyVarBndrToName tv)))
                          tyVarBndrs
  let typ           = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead  = AppT (ConT ''DSH.QA) typ
  let repDec        = deriveRep typ cons
  toExpDec <- deriveToExp cons
  frExpDec <- deriveFrExp cons
  return [InstanceD Nothing context instanceHead [repDec,toExpDec,frExpDec]]

-- Deriving the Rep type function

-- | Derive the representation type 'Rep' for a data type
deriveRep :: Type -> [Con] -> Dec
deriveRep typ cons = TySynInstD ''DSH.Rep $ TySynEqn [typ] (deriveRepCons cons)

-- | Derive the representation type 'Rep' for the complete type (all
-- constructors).
deriveRepCons :: [Con] -> Type
deriveRepCons []                   = error errMsgExoticType
-- The representation of a type with only one constructor is the
-- representation of that constructor.
deriveRepCons [c]                  = deriveRepCon c
-- The representation of a type with multiple constructors is a tuple
-- of the representation types for all individual constructors (each
-- wrapped in a list).
deriveRepCons cs | length cs <= 16 = mkTupleType $ map (AppT (ConT ''[]) . deriveRepCon) cs
deriveRepCons _                    = error errMsgTypeTooBroad


-- | Derive the representation type 'Rep' for a single constructor
deriveRepCon :: Con -> Type
deriveRepCon con = case conToTypes con of
  -- A constructor without fields is represented by the empty type
  []                   -> ConT ''()
  -- The representation of a constructor with only one field is the
  -- field type itself.
  [t]                  -> t
  -- Constructors with more fields (up to 16) are represented by a
  -- tuple that contains values for all fields.
  ts | length ts <= 16 -> mkTupleType $ map (AppT (ConT ''DSH.Rep)) ts
  _  | otherwise       -> error errMsgTypeTooBroad

-- Deriving the toExp function of the QA class

deriveToExp :: [Con] -> Q Dec
deriveToExp [] = fail errMsgExoticType
deriveToExp cons = do
  clauses <- sequence (zipWith3 deriveToExpClause (repeat (length cons)) [0 .. ] cons)
  return (FunD 'DSH.toExp clauses)

deriveToExpClause :: Int -- Total number of constructors
                  -> Int -- Index of the constructor
                  -> Con
                  -> Q Clause
deriveToExpClause 0 _ _ = fail errMsgExoticType
deriveToExpClause 1 _ con = do
  (pat1,names1) <- conToPattern con
  exp1 <- deriveToExpMainExp names1
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
-- FIXME adapt code for types with multiple constructors to new tuple
-- regime.
deriveToExpClause _n _i _con = $unimplemented
{-
  (pat1,names1) <- conToPattern con
  let exp1 = deriveToExpMainExp names1
  expList1 <- [| DSH.ListE [ $(return exp1) ] |]
  expEmptyList <- [| DSH.ListE [] |]
  let lists = concat [ replicate i expEmptyList
                     , [expList1]
                     , replicate (n - i - 1) expEmptyList]
  let exp2 = foldr1 (AppE . AppE (ConE 'DSH.PairE)) lists
  let body1 = NormalB exp2
  return (Clause [pat1] body1 [])
-}

deriveToExpMainExp :: [Name] -> Q Exp
deriveToExpMainExp []     = return $ ConE 'DSH.UnitE
deriveToExpMainExp [name] = return $ AppE (VarE 'DSH.toExp) (VarE name)
deriveToExpMainExp names  = mkTupConstTerm $ map (AppE (VarE 'DSH.toExp) . VarE) names

-- Deriving to frExp function of the QA class

deriveFrExp :: [Con] -> Q Dec
deriveFrExp cons = do
  clauses <- sequence (zipWith3 deriveFrExpClause (repeat (length cons)) [0 .. ] cons)
  imp     <- impossible
  let lastClause = Clause [WildP] (NormalB imp) []
  return (FunD 'DSH.frExp (clauses ++ [lastClause]))

deriveFrExpClause :: Int -- Total number of constructors
                  -> Int -- Index of the constructor
                  -> Con
                  -> Q Clause
deriveFrExpClause 1 _ con = do
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let exp1 = foldl AppE
                   (ConE (conToName con))
                   (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
-- FIXME adapt code for types with multiple constructors to new tuple
-- regime.
deriveFrExpClause _n _i _con = $unimplemented
{-
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let patList1 = ConP 'DSH.ListE [ConP '(:) [pat1,WildP]]
  let lists = replicate i WildP ++ [patList1] ++ replicate (n - i - 1) WildP
  let pat2 = foldr1 (\p1 p2 -> ConP 'DSH.PairE [p1,p2]) lists
  let exp1 = foldl AppE
                   (ConE (conToName con))
                   (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat2] body1 [])
-}

deriveFrExpMainPat :: [Name] -> Pat
deriveFrExpMainPat [] = ConP 'DSH.UnitE []
deriveFrExpMainPat [name] = VarP name
deriveFrExpMainPat names  = mkTuplePat names

-----------------
-- Deriving TA --
-----------------

deriveTA :: Name -> Q [Dec]
deriveTA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs _ cons _names) ->
      deriveTyConTA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs _ con  _names) ->
      deriveTyConTA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConTA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConTA name tyVarBndrs _cons = do
  let context       = map (\tv -> nameTyApp ''DSH.BasicType (VarT (tyVarBndrToName tv)))
                          tyVarBndrs
  let typ           = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead  = AppT (ConT ''DSH.TA) typ
  return [InstanceD Nothing context instanceHead []]

-------------------
-- Deriving View --
-------------------

deriveView :: Name -> Q [Dec]
deriveView name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs _ [con] _names) ->
      deriveTyConView name1 tyVarBndrs con
    TyConI (NewtypeD _cxt name1 tyVarBndrs _ con  _names) ->
      deriveTyConView name1 tyVarBndrs con
    _ -> fail errMsgExoticType

deriveTyConView :: Name -> [TyVarBndr] -> Con -> Q [Dec]
deriveTyConView name tyVarBndrs con = do
  let context = map (\tv -> nameTyApp ''DSH.QA (VarT (tyVarBndrToName tv)))
                    tyVarBndrs
  let typ1 = AppT (ConT ''DSH.Q)
                  (foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs))
  let instanceHead = AppT (ConT ''DSH.View) typ1
  let typs = conToTypes con
  let typ2 = if null typs
                then AppT (ConT ''DSH.Q) (ConT ''())
                else foldl AppT (TupleT (length typs)) (map (AppT (ConT ''DSH.Q)) typs)
  let toViewDecTF = TySynInstD ''DSH.ToView $ TySynEqn [typ1] typ2
  viewDec <- deriveToView (length typs)
  return [InstanceD Nothing context instanceHead [toViewDecTF, viewDec]]

deriveToView :: Int -> Q Dec
deriveToView n = do
  en <- newName "e"
  let ep = VarP en
  let pat1 = ConP 'DSH.Q [ep]

  tupElems <- mapM (\i -> [| DSH.Q $ $(mkTupElemTerm n i (VarE en)) |]) [1..n]

  let body1 = TupE $ tupElems
  let clause1 = Clause [pat1] (NormalB body1) []
  return (FunD 'DSH.view [clause1])

-------------------
-- Deriving Elim --
-------------------

deriveElim :: Name -> Q [Dec]
deriveElim name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs _ cons _names) ->
      deriveTyConElim name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs _ con  _names) ->
      deriveTyConElim name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConElim :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConElim name tyVarBndrs cons = do
  resultTyName <- newName "r"
  let resTy = VarT resultTyName
  let ty = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let context = nameTyApp ''DSH.QA (resTy) :
                map (\tv -> nameTyApp ''DSH.QA (VarT (tyVarBndrToName tv)))
                    tyVarBndrs
  let instanceHead = AppT (AppT (ConT ''DSH.Elim) ty) resTy
  let eliminatorDec = deriveEliminator ty resTy cons
  elimDec <- deriveElimFun cons
  return [InstanceD Nothing context instanceHead [eliminatorDec,elimDec]]

-- Deriving the Eliminator type function

deriveEliminator :: Type -> Type -> [Con] -> Dec
deriveEliminator typ resTy cons =
  TySynInstD ''DSH.Eliminator $ TySynEqn [typ,resTy] (deriveEliminatorCons resTy cons)

deriveEliminatorCons :: Type -> [Con] -> Type
deriveEliminatorCons _ []  = error errMsgExoticType
deriveEliminatorCons resTy cs  =
  foldr (AppT . AppT ArrowT . deriveEliminatorCon resTy)
        (AppT (ConT ''DSH.Q) resTy)
        cs

deriveEliminatorCon :: Type -> Con -> Type
deriveEliminatorCon resTy con =
  foldr (AppT . AppT ArrowT . AppT (ConT ''DSH.Q))
        (AppT (ConT ''DSH.Q) resTy)
        (conToTypes con)

-- Deriving the elim function of the Elim type class

deriveElimFun :: [Con] -> Q Dec
deriveElimFun cons = do
  clause1 <- deriveElimFunClause cons
  return (FunD 'DSH.elim [clause1])

deriveElimFunClause :: [Con] -> Q Clause
deriveElimFunClause = $unimplemented
-- deriveElimFunClause cons = do
--   en  <- newName "e"
--   fns <- mapM (\ _ -> newName "f") cons
--   let fes = map VarE fns
--   let pats1 = ConP 'DSH.Q [VarP en] : map VarP fns

--   fes2 <- zipWithM deriveElimToLamExp fes (map (length . conToTypes) cons)

--   let e       = VarE en
--   liste <- [| DSH.ListE $(listE $ deriveElimFunClauseExp (return e) (map return fes2)) |]
--   let concate = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Concat)) liste
--   let heade   = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Head)) concate
--   let qe      = AppE (ConE 'DSH.Q) heade
--   return (Clause pats1 (NormalB qe) [])

-- deriveElimToLamExp :: Exp -> Int -> Q Exp
-- deriveElimToLamExp f 0 =
--   return (AppE (VarE 'const) (AppE (VarE 'DSH.unQ) f))
-- deriveElimToLamExp f 1 = do
--   xn <- newName "x"
--   let xe = VarE xn
--   let xp = VarP xn
--   let qe = AppE (ConE 'DSH.Q) xe
--   let fappe = AppE f qe
--   let unqe = AppE (VarE 'DSH.unQ) fappe
--   return (LamE [xp] unqe)
-- deriveElimToLamExp f n = do
--   xn <- newName "x"
--   let xe = VarE xn
--   let xp = VarP xn
--   let fste = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Fst)) xe
--   let snde = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Snd)) xe
--   let qe = AppE (ConE 'DSH.Q) fste
--   let fappe = AppE f qe
--   f' <- deriveElimToLamExp fappe (n - 1)
--   return (LamE [xp] (AppE f' snde))

-- deriveElimFunClauseExp :: Q Exp -> [Q Exp] -> [Q Exp]
-- deriveElimFunClauseExp _ [] = error errMsgExoticType
-- deriveElimFunClauseExp e [f] = [ [| DSH.ListE [$f $e] |] ]
-- deriveElimFunClauseExp e fs = go e fs
--   where
--   go :: Q Exp -> [Q Exp] -> [Q Exp]
--   go _ []  = error errMsgExoticType
--   -- FIXME PairE
--   go e1 [f1] = do
--     [ [| DSH.AppE F.Map (DSH.TupleConstE (DSH.Tuple2E (DSH.LamE $f1) $e1)) |] ]
--   go e1 (f1 : fs1) = do
--     let mape = [| DSH.AppE F.Map (DSH.TupleConstE (DSH.Tuple2E (DSH.LamE $f1) (DSH.AppE F.Fst $e1))) |]
--     let snde = [| DSH.AppE F.Snd $e1 |]
--     mape : go snde fs1

---------------------------------
-- Deriving Smart Constructors --
---------------------------------

deriveSmartConstructors :: Name -> Q [Dec]
deriveSmartConstructors name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt typConName tyVarBndrs _ cons _names) -> do
      decss <- do
          zipWithM (deriveSmartConstructor typConName tyVarBndrs (length cons))
                   [0 .. ] cons
      return (concat decss)
    TyConI (NewtypeD _cxt typConName tyVarBndrs _ con  _names) ->
      deriveSmartConstructor typConName tyVarBndrs 1 0 con
    _ -> fail errMsgExoticType

deriveSmartConstructor :: Name -> [TyVarBndr] -> Int -> Int -> Con -> Q [Dec]
deriveSmartConstructor typConName tyVarBndrs n i con = do
  let conArgTypes = conToTypes con

  -- A list of Bools that says which constructor fields have where-provenance
  -- annotation
  provAnnotMap <- mapM hasWhereProvenanceAnnotation conArgTypes

  let -- if there's at least one field with a where-provenance annotation return
      -- the list pass in as argument, otherwise return empty list
      whenProv xs = if or provAnnotMap then [xs] else []

      -- zip a list with provenance annotation map using zipping function f
      zipProv f = zipWith f provAnnotMap

      -- smart constructor names
      smartConNames =
        let smartConName = toSmartConName (conToName con)
        in  whenProv (toSmartConProvName smartConName) ++ [smartConName]

      boundTyps = map (VarT . tyVarBndrToName) tyVarBndrs

      -- return type of a smart constructor
      resTyp = AppT (ConT ''DSH.Q) (foldl AppT (ConT typConName) boundTyps)

      smartConContext = map (nameTyApp ''DSH.QA) boundTyps

      -- builds smart constructor arrow type using a supplied list of
      -- constructor argument types
      buildSmartConTy tys = foldr (AppT . AppT ArrowT . AppT (ConT ''DSH.Q))
                                  resTyp tys

      -- if a given field has provenance annotation we must apply ProvData type
      -- family to that argument's type
      conArgProvTypes =
          zipProv (\prov ty -> if prov then AppT (ConT ''ProvData) ty else ty)
                  conArgTypes

      -- final types of smart constructors
      smartConTys = map buildSmartConTy (conArgTypes : whenProv conArgProvTypes)

      -- smart constructor type annotations
      smartConDecs =
         zipWith (\name ty -> SigD name (ForallT tyVarBndrs smartConContext ty))
                 smartConNames smartConTys

  ns <- mapM (\_ -> newName "e") (conToTypes con)

  let -- expressions used to construct body of a smart constructor with
      -- provenance.  Each expression corresponding to a field must be extended
      -- with empty provenance annottation.  Type annotation is required to
      -- eliminate type ambiguity.
      esProv = zipProv (\prov (name, ty) ->
                     if prov
                     then AppE (VarE (mkName "unQ"))
                               (SigE (AppE (VarE (mkName "emptyProvQ"))
                                           (VarE name))
                                     (AppT (ConT ''DSH.Q) ty))
                     else VarE name) (zip ns conArgTypes)

  let es = map VarE ns : whenProv esProv

  let -- fields without where provenance are unwrapped from Q
      smartConPats = map (ConP 'DSH.Q . return . VarP) ns :
        whenProv (zipProv (\prov pat -> if prov
                                        then (VarP pat)
                                        else (ConP 'DSH.Q (return (VarP pat))))
                          ns)

  -- FIXME PairE -> TupleE
  smartConExps <- mapM (\e -> if null e
                              then return $ ConE 'DSH.UnitE
                              else mkTupConstTerm e) es

  smartConBodies <- mapM (deriveSmartConBody n i) smartConExps
  let smartConClauses = zipWith (\pat body -> [Clause pat (NormalB body) []])
                                smartConPats smartConBodies

  let funDecs = zipWith FunD smartConNames smartConClauses

  return $ concat (transpose [ smartConDecs, funDecs ])

deriveSmartConBody :: Int -- Total number of constructors
                   -> Int -- Index of the constructor
                   -> Exp
                   -> Q Exp
deriveSmartConBody 0 _ _ = fail errMsgExoticType
deriveSmartConBody 1 _ e = return (AppE (ConE 'DSH.Q) e)
deriveSmartConBody n i e = do
  listExp <- [| DSH.ListE [ $(return e) ] |]
  emptyListExp <- [| DSH.ListE [] |]
  let lists = concat [ replicate i emptyListExp
                     , [listExp]
                     , replicate (n - i - 1) emptyListExp
                     ]
  tupleExp <- mkTupConstTerm lists
  return $ AppE (ConE 'DSH.Q) tupleExp

toSmartConName :: Name -> Name
toSmartConName name1 = case nameBase name1 of
  "()"                -> mkName "unit"
  '(' : cs            -> mkName ("tuple" ++ show (length (filter (== ',') cs) + 1))
  c : cs | isAlpha c  -> mkName (toLower c : cs)
  cs                  -> mkName (':' : cs)

toSmartConProvName :: Name -> Name
toSmartConProvName name = mkName ((nameBase name) ++ "Prov")


----------------------------------------
-- Generating lifted record selectors --
----------------------------------------

{-

For a record declaration like

data R = R { a :: Integer, b :: Text, c :: WhereProv Bool Integer }

we generate the following lifted selectors:

aQ :: Q R -> Q Integer
aQ (view -> (a, _, _)) = a

bQ :: Q R -> Q Text
bQ (view -> (_, b, _)) = b

cQ :: Q R -> Q (WhereProv Bool Integer)
cQ (view -> (_, _, c)) = c

c_dataQ :: Q R -> Q (ProvData (WhereProv Bool Integer))
c_dataQ (view -> (_, _, c)) = dataQ c

c_provQ :: Q R -> Q (ProvAnnot (WhereProv Bool Integer))
c_prvQ (view -> (_, _, c)) = provQ c
-}

-- | Create lifted record selectors
generateTableSelectors :: Name -> Q [Dec]
generateTableSelectors name = do
  info <- reify name
  case info of
    TyConI (DataD _ typName [] _ [RecC _ fields] _) ->
        concat <$> mapM instSelectors fields
      where fieldNames    = map (\(f, _, _) -> f) fields
            instSelectors = generateTableSelector typName fieldNames
    _ -> fail errMsgBaseRecCons

generateTableSelector :: Name -> [Name] -> VarStrictType -> Q [Dec]
generateTableSelector typeName allFieldNames vst@(fieldName, _strict, typ) = do
  let selName = case fieldName of
                  Name (OccName n) _ -> mkName $ n ++ "Q"

  let selType = AppT (AppT ArrowT (AppT (ConT ''DSH.Q) (ConT typeName)))
                     (AppT (ConT ''DSH.Q) typ)
      sigDec  = SigD selName selType

  fieldVarName <- newName "x"
  let projectField f | f == fieldName = VarP fieldVarName
      projectField _                  = WildP

      tupPat   = map projectField allFieldNames

      argPat   = ViewP (VarE 'DSH.view) (TupP tupPat)

      bodyExp  = NormalB $ VarE fieldVarName

      funDec   = FunD selName [Clause [argPat] bodyExp []]

  hasProv  <- hasWhereProvenanceAnnotation typ
  provDecs <- if hasProv
              then generateProvenanceTableSelectors typeName allFieldNames vst
              else return []

  return $ [sigDec, funDec] ++ provDecs

generateProvenanceTableSelectors :: Name -> [Name] -> VarStrictType -> Q [Dec]
generateProvenanceTableSelectors typeName allFieldNames (fieldName, _, ty) = do
  let selNames = case fieldName of
                   Name (OccName n) _ -> [ mkName $ n ++ "_dataQ"
                                         , mkName $ n ++ "_provQ" ]

  let mkSelType t = AppT (AppT ArrowT (AppT (ConT ''DSH.Q) (ConT typeName)))
                         (AppT (ConT ''DSH.Q) t)
      selTypes = [ mkSelType (AppT (ConT ''ProvData ) ty)
                 , mkSelType (AppT (ConT ''ProvAnnot) ty) ]
      sigDecs  = zipWith SigD selNames selTypes

  fieldVarName <- newName "x"
  let projectField f | f == fieldName = VarP fieldVarName
      projectField _                  = WildP

      tupPat   = map projectField allFieldNames

      argPat   = ViewP (VarE 'DSH.view) (TupP tupPat)

      bodyExps = [ NormalB $ AppE (VarE (mkName "dataQ")) (VarE fieldVarName)
                 , NormalB $ AppE (VarE (mkName "provQ")) (VarE fieldVarName) ]

      funDecs  = zipWith (\sel body -> FunD sel [Clause [argPat] body []])
                         selNames bodyExps

  return $ concat (transpose ([sigDecs, funDecs]))

-- Helper Functions

-- | From a list of operand patterns, construct a DSH tuple term
-- pattern.
-- @
-- TupleE (Tuple3E a b) -> ...
-- @
mkTuplePat :: [Name] -> Pat
mkTuplePat names = ConP 'DSH.TupleConstE
                        [ConP (innerConst "" $ length names) (map VarP names)]

-- | Generate a (flat) tuple type from the list of element types.
mkTupleType :: [Type] -> Type
mkTupleType ts = foldl' AppT (TupleT $ length ts) ts

-- | Return the types of all fields of a constructor.
-- FIXME missing cases for GADTs
conToTypes :: Con -> [Type]
conToTypes (NormalC _name strictTypes) = map snd strictTypes
conToTypes (RecC _name varStrictTypes) = map (\(_,_,t) -> t) varStrictTypes
conToTypes (InfixC st1 _name st2) = [snd st1,snd st2]
conToTypes (ForallC _tyVarBndrs _cxt con) = conToTypes con
conToTypes GadtC{} = error "Can't derive database representation: GATDs are not supported"
conToTypes RecGadtC{} = error "Can't derive database representation: GATDs are not supported"

tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV name) = name
tyVarBndrToName (KindedTV name _kind) = name

-- | For a given constructor, create a pattern that matches the
-- constructor and binds all fields to the names returned.
conToPattern :: Con -> Q (Pat,[Name])
conToPattern (NormalC name strictTypes) = do
  ns <- mapM (\ _ -> newName "x") strictTypes
  return (ConP name (map VarP ns),ns)
conToPattern (RecC name varStrictTypes) = do
  ns <- mapM (\ _ -> newName "x") varStrictTypes
  return (ConP name (map VarP ns),ns)
conToPattern (InfixC st1 name st2) = do
  ns <- mapM (\ _ -> newName "x") [st1,st2]
  return (ConP name (map VarP ns),ns)
conToPattern (ForallC _tyVarBndr _cxt con) = conToPattern con
conToPattern GadtC{} = error "Can't derive database representation: GATDs are not supported"
conToPattern RecGadtC{} = error "Can't derive database representation: GATDs are not supported"

conToName :: Con -> Name
conToName (NormalC name _)  = name
conToName (RecC name _)     = name
conToName (InfixC _ name _) = name
conToName (ForallC _ _ con) = conToName con
conToName GadtC{}           = error "Can't derive database representation: GATDs are not supported"
conToName RecGadtC{}        = error "Can't derive database representation: GATDs are not supported"

countConstructors :: Name -> Q Int
countConstructors name = do
  info <- reify name
  case info of
    TyConI (DataD    _ _ _ _ cons _)  -> return (length cons)
    TyConI (NewtypeD {})              -> return 1
    _ -> fail errMsgExoticType

-- Returns name of top-most type constructor
tyConName :: Type -> Maybe Name
tyConName (ConT n  ) = Just n
tyConName (AppT t _) = tyConName t
tyConName (SigT t _) = tyConName t
tyConName _          = Nothing

-- Looks through a type synonym
lookThrough :: Name -> Q (Maybe Type)
lookThrough name = do
  info <- reify name
  case info of
    TyConI (TySynD _ _ ty) -> return (Just ty)
    _                      -> return Nothing

-- Returns true if the type is a WhereProv (possibly behind a type synonym)
hasWhereProvenanceAnnotation :: Type -> Q Bool
hasWhereProvenanceAnnotation ty =
    case tyConName ty of
      Nothing   -> return False
      Just name ->
          if name == ''WhereProv
          then return True
          else do
            ty' <- lookThrough name
            case ty' of
              Nothing   -> return False
              Just ty'' -> hasWhereProvenanceAnnotation ty''

-- Error messages

errMsgExoticType :: String
errMsgExoticType =
  "Automatic derivation of DSH related type class instances only works for Haskell 98\n"
  ++ "types. Derivation of View patterns is only supported for single-constructor data\n"
  ++ "types."

errMsgBaseRecCons :: String
errMsgBaseRecCons =
  "Generation of lifted record selectors is only supported for records of base types."

errMsgTypeTooBroad :: String
errMsgTypeTooBroad =
  "DSH currently supports data types with up to 16 constructors and in which \n"
  ++ "all constructors have up to 16 fields."
