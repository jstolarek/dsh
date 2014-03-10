module Database.DSH.VL.Render.Dot(renderVLDot, renderTblVal) where

import qualified Data.IntMap                 as Map
import           Data.List

import           Text.PrettyPrint

import qualified Database.Algebra.Dag        as Dag
import           Database.Algebra.Dag.Common as C
import           Database.DSH.VL.Lang

nodeToDoc :: AlgNode -> Doc
nodeToDoc n = (text "id:") <+> (int n)

tagsToDoc :: [Tag] -> Doc
tagsToDoc ts = vcat $ map text ts

labelToDoc :: AlgNode -> String -> Doc -> [Tag] -> Doc
labelToDoc n s as ts = (nodeToDoc n) $$ ((text s) <> (parens as)) $$ (tagsToDoc $ nub ts)

lookupTags :: AlgNode -> NodeMap [Tag] -> [Tag]
lookupTags n m = Map.findWithDefault [] n m

renderFun :: Doc -> [Doc] -> Doc
renderFun name args = name <> parens (hsep $ punctuate comma args)

renderAggrFun :: AggrFun -> Doc
renderAggrFun (AggrSum t c) = renderFun (text "sum" <> char '_' <> renderColumnType t) 
                                        [renderExpr1 c]
renderAggrFun (AggrMin c)   = renderFun (text "min") [renderExpr1 c]
renderAggrFun (AggrMax c)   = renderFun (text "max") [renderExpr1 c]
renderAggrFun (AggrAvg c)   = renderFun (text "avg") [renderExpr1 c]
renderAggrFun AggrCount     = renderFun (text "count") []

renderColumnType :: VLType -> Doc
renderColumnType = text . show

renderData :: [[VLVal]] -> Doc
renderData [] = brackets empty
renderData xs = (flip (<>) semi . sep . punctuate semi . map renderRow) xs

renderRow :: [VLVal] -> Doc
renderRow = hcat . punctuate comma . map renderTblVal

renderTblVal :: VLVal -> Doc
renderTblVal (VLInt i) = integer $ fromIntegral i
renderTblVal (VLNat i) = text "#" <> (integer $ fromIntegral i)
renderTblVal (VLBool b) = text $ show b
renderTblVal (VLString s) = doubleQuotes $ text $ escape s
renderTblVal (VLDouble d) = double d
renderTblVal VLUnit = text "()"

escape :: String -> String
escape (x@'\\':xs) = '\\':'\\':'\\':x:escape xs
escape (x@'\'':xs) = '\\':x:escape xs
escape (x@'"':xs) = '\\':'\\':x:escape xs
escape (x:xs) = x:escape xs
escape [] = []

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderTableType :: TypedColumn -> Doc
renderTableType (c, t) = text c <> text "::" <> renderColumnType t

renderTableKeys :: [Key] -> Doc
renderTableKeys [x] = renderTableKey x
renderTableKeys (x:xs) = renderTableKey x $$ renderTableKeys xs
renderTableKeys [] = text "NOKEY"

renderTableKey :: Key -> Doc
renderTableKey [x] = text x
renderTableKey (x:xs) = text x <> comma <+> renderTableKey xs
renderTableKey [] = text "NOKEY"

renderProj :: Doc -> Expr1 -> Doc
renderProj d e = d <> colon <> renderExpr1 e

renderExpr1 :: Expr1 -> Doc
renderExpr1 (BinApp1 op e1 e2) = (parenthize1 e1) <+> (text $ show op) <+> (parenthize1 e2)
renderExpr1 (UnApp1 op e)      = (text $ show op) <+> (parens $ renderExpr1 e)
renderExpr1 (Constant1 val)    = renderTblVal val
renderExpr1 (Column1 c)        = text "col" <> int c

parenthize1 :: Expr1 -> Doc
parenthize1 e@(Constant1 _)   = renderExpr1 e
parenthize1 e@(Column1 _)     = renderExpr1 e
parenthize1 e@(BinApp1 _ _ _) = parens $ renderExpr1 e
parenthize1 e@(UnApp1 _ _)    = parens $ renderExpr1 e

renderExpr2 :: Expr2 -> Doc
renderExpr2 (BinApp2 op e1 e2)   = (parenthize2 e1) <+> (text $ show op) <+> (parenthize2 e2)
renderExpr2 (UnApp2 op e)        = (text $ show op) <+> (parens $ renderExpr2 e)
renderExpr2 (Constant2 val)      = renderTblVal val
renderExpr2 (Column2Left (L c))  = text "lcol" <> int c
renderExpr2 (Column2Right (R c)) = text "rcol" <> int c

parenthize2 :: Expr2 -> Doc
parenthize2 e@(Constant2 _)    = renderExpr2 e
parenthize2 e@(Column2Left _)  = renderExpr2 e
parenthize2 e@(Column2Right _) = renderExpr2 e
parenthize2 e@(BinApp2 _ _ _)  = parens $ renderExpr2 e
parenthize2 e@(UnApp2 _ _)     = parens $ renderExpr2 e

-- create the node label from an operator description
opDotLabel :: NodeMap [Tag] -> AlgNode -> VL -> Doc
opDotLabel tm i (NullaryOp (SingletonDescr)) = labelToDoc i "SingletonDescr" empty (lookupTags i tm)
opDotLabel tm i (NullaryOp (Lit tys vals)) = labelToDoc i "LIT"
        (bracketList renderColumnType tys <> comma
        $$ renderData vals) (lookupTags i tm)
opDotLabel tm i (NullaryOp (TableRef n tys ks)) = labelToDoc i "TableRef"
        (quotes (text n) <> comma <+> bracketList (\t -> renderTableType t <> text "\n") tys <> comma $$ renderTableKeys ks)
        (lookupTags i tm)
opDotLabel tm i (UnOp UniqueS _) = labelToDoc i "UniqueS" empty (lookupTags i tm)
opDotLabel tm i (UnOp Number _) = labelToDoc i "Number" empty (lookupTags i tm)
opDotLabel tm i (UnOp NumberS _) = labelToDoc i "NumberS" empty (lookupTags i tm)
opDotLabel tm i (UnOp DescToRename _) = labelToDoc i "DescToRename" empty (lookupTags i tm)
opDotLabel tm i (UnOp Segment _) = labelToDoc i "Segment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Unsegment _) = labelToDoc i "Unsegment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Reverse _) = labelToDoc i "Reverse" empty (lookupTags i tm)
opDotLabel tm i (UnOp ReverseS _) = labelToDoc i "ReverseS" empty (lookupTags i tm)
opDotLabel tm i (UnOp R1 _) = labelToDoc i "R1" empty (lookupTags i tm)
opDotLabel tm i (UnOp R2 _) = labelToDoc i "R2" empty (lookupTags i tm)
opDotLabel tm i (UnOp R3 _) = labelToDoc i "R3" empty (lookupTags i tm)
opDotLabel tm i (UnOp (Project pCols) _) =
  labelToDoc i "Project" pLabel (lookupTags i tm)
  where pLabel = valCols
        valCols = bracketList (\(j, p) -> renderProj (itemLabel j) p) $ zip ([1..] :: [Int]) pCols
        itemLabel j = (text "i") <> (int j)
opDotLabel tm i (UnOp (Select e) _) = labelToDoc i "Select" (renderExpr1 e) (lookupTags i tm)
opDotLabel tm i (UnOp Only _) = labelToDoc i "Only" empty (lookupTags i tm)
opDotLabel tm i (UnOp Singleton _) = labelToDoc i "Singleton" empty (lookupTags i tm)
opDotLabel tm i (UnOp (SelectPos1 o (N p)) _)  = labelToDoc i "SelectPos1" ((text $ show o) <+> int p) (lookupTags i tm)
opDotLabel tm i (UnOp (SelectPos1S o (N p)) _) = labelToDoc i "SelectPos1S" ((text $ show o) <+> int p) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupAggr g as) _) = labelToDoc i "GroupAggr" (bracketList renderExpr1 g <+> bracketList renderAggrFun as) (lookupTags i tm)
opDotLabel tm i (UnOp (Aggr a) _) = labelToDoc i "Aggr" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (Reshape n) _) = 
  labelToDoc i "Reshape" (integer n) (lookupTags i tm)
opDotLabel tm i (BinOp (AggrS a) _ _) = labelToDoc i "AggrS" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (SortSimple cols) _) = labelToDoc i "SortSimple" (bracketList renderExpr1 cols) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupSimple cols) _) = labelToDoc i "GroupSimple" (bracketList renderExpr1 cols) (lookupTags i tm)
opDotLabel tm i (BinOp GroupBy _ _) = labelToDoc i "GroupBy" empty (lookupTags i tm)
opDotLabel tm i (BinOp Sort _ _) = labelToDoc i "Sort" empty (lookupTags i tm)
opDotLabel tm i (BinOp DistPrim _ _) = labelToDoc i "DistPrim" empty (lookupTags i tm)
opDotLabel tm i (BinOp DistDesc _ _) = labelToDoc i "DistDesc" empty (lookupTags i tm)
opDotLabel tm i (BinOp DistSeg _ _) = labelToDoc i "DistSeg" empty (lookupTags i tm)
opDotLabel tm i (BinOp PropRename _ _) = labelToDoc i "PropRename" empty (lookupTags i tm)
opDotLabel tm i (BinOp PropFilter _ _) = labelToDoc i "PropFilter" empty (lookupTags i tm)
opDotLabel tm i (BinOp PropReorder _ _) = labelToDoc i "PropReorder" empty (lookupTags i tm)
opDotLabel tm i (BinOp Append _ _) = labelToDoc i "Append" empty (lookupTags i tm)
opDotLabel tm i (BinOp Restrict _ _) = labelToDoc i "Restrict" empty (lookupTags i tm)
opDotLabel tm i (BinOp (BinExpr expr) _ _) = labelToDoc i "BinExpr" (renderExpr2 expr) (lookupTags i tm)
opDotLabel tm i (BinOp (SelectPos o) _ _) = labelToDoc i "SelectPos" (text $ show o) (lookupTags i tm)
opDotLabel tm i (BinOp (SelectPosS o) _ _) = labelToDoc i "SelectPosS" (text $ show o) (lookupTags i tm)
opDotLabel tm i (BinOp Zip _ _) = labelToDoc i "Zip" empty (lookupTags i tm)
opDotLabel tm i (BinOp ZipS _ _) = labelToDoc i "ZipS" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProduct _ _) = labelToDoc i "CartProduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProductS _ _) = labelToDoc i "CartProductS" empty (lookupTags i tm)
opDotLabel tm i (BinOp NestProductS _ _) = labelToDoc i "NestProductS" empty (lookupTags i tm)
opDotLabel tm i (BinOp (EquiJoin e1 e2) _ _) =
  labelToDoc i "EquiJoin" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (EquiJoinS e1 e2) _ _) =
  labelToDoc i "EquiJoinS" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (NestJoinS e1 e2) _ _) =
  labelToDoc i "NestJoinS" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoin e1 e2) _ _) =
  labelToDoc i "SemiJoin" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoinS e1 e2) _ _) =
  labelToDoc i "SemiJoinS" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoin e1 e2) _ _) =
  labelToDoc i "AntiJoin" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoinS e1 e2) _ _) =
  labelToDoc i "AntiJoinS" ((renderExpr1 e1) <+> (renderExpr1 e2)) (lookupTags i tm)
opDotLabel tm i (UnOp (ReshapeS n) _) = 
  labelToDoc i "ReshapeS" (integer n) (lookupTags i tm)
opDotLabel tm i (UnOp Transpose _) = labelToDoc i "Transpose" empty (lookupTags i tm)
opDotLabel tm i (TerOp Combine _ _ _) = labelToDoc i "Combine" empty (lookupTags i tm)
opDotLabel tm i (BinOp TransposeS _ _) = labelToDoc i "TransposeS" empty (lookupTags i tm)

opDotColor :: VL -> DotColor
opDotColor (BinOp DistDesc _ _)        = DCRed
opDotColor (BinOp CartProduct _ _)     = DCRed
opDotColor (BinOp CartProductS _ _)    = DCRed
opDotColor (BinOp NestProductS _ _)    = DCRed
opDotColor (BinOp (EquiJoin _ _) _ _)  = DCGreen
opDotColor (BinOp (EquiJoinS _ _) _ _) = DCGreen
opDotColor (BinOp (NestJoinS _ _) _ _) = DCGreen
opDotColor (BinOp (SemiJoin _ _) _ _)  = DCGreen
opDotColor (BinOp (SemiJoinS _ _) _ _) = DCGreen
opDotColor (BinOp (AntiJoin _ _) _ _)  = DCGreen
opDotColor (BinOp (AntiJoinS _ _) _ _) = DCGreen
opDotColor (BinOp Zip _ _)             = DCYelloGreen
opDotColor (BinOp Sort _ _)            = DCTomato
opDotColor (UnOp (SortSimple _) _)     = DCTomato
opDotColor (BinOp GroupBy _ _)         = DCTomato
opDotColor (UnOp (GroupSimple _) _)    = DCTomato
opDotColor (BinOp PropRename _ _)      = DCTan
opDotColor (BinOp PropReorder _ _)     = DCTan
opDotColor (BinOp DistSeg _ _)         = DCTan
opDotColor (BinOp Restrict _ _)        = DCDodgerBlue
opDotColor (TerOp Combine _ _ _)       = DCDodgerBlue
opDotColor (UnOp (Select _) _)         = DCLightSkyBlue
opDotColor (UnOp (Aggr _) _)           = DCCrimson
opDotColor (BinOp (AggrS _) _ _)       = DCCrimson
opDotColor (UnOp (GroupAggr _ _) _)    = DCTomato
opDotColor (UnOp (Project _) _)        = DCLightSkyBlue
opDotColor (BinOp (BinExpr _) _ _)     = DCDodgerBlue
opDotColor (UnOp Transpose _)          = DCHotPink
opDotColor (BinOp TransposeS _ _)      = DCHotPink
opDotColor (UnOp (ReshapeS _) _)       = DCHotPink
opDotColor (UnOp (Reshape _) _)        = DCHotPink
opDotColor _ = DCGray

-- Dot colors
data DotColor = DCTomato
              | DCSalmon
              | DCGray
              | DimDCGray
              | DCGold
              | DCTan
              | DCRed
              | DCCrimson
              | DCGreen
              | DCSeaGreen
              | DCYelloGreen
              | DCSienna
              | DCBeige
              | DCDodgerBlue
              | DCLightSkyBlue
              | DCHotPink

renderColor :: DotColor -> Doc
renderColor DCTomato = text "tomato"
renderColor DCSalmon = text "salmon"
renderColor DCGray = text "gray"
renderColor DimDCGray = text "dimgray"
renderColor DCGold = text "gold"
renderColor DCTan = text "tan"
renderColor DCRed = text "red"
renderColor DCCrimson = text "crimson"
renderColor DCGreen = text "green"
renderColor DCSeaGreen = text "seagreen"
renderColor DCYelloGreen = text "yellowgreen"
renderColor DCSienna = text "sienna"
renderColor DCBeige = text "beige"
renderColor DCDodgerBlue = text "dodgerblue"
renderColor DCLightSkyBlue = text "lightskyblue"
renderColor DCHotPink      = text "hotpink"

escapeLabel :: String -> String
escapeLabel s = concatMap escapeChar s

escapeChar :: Char -> [Char]
escapeChar '\n' = ['\\', 'n']
escapeChar '\\' = ['\\', '\\']
escapeChar '\"' = ['\\', '"']
escapeChar c = [c]

-- Type of Dot style options
data DotStyle = Solid

-- label of Dot nodes
type DotLabel = String

-- id of Dot nodes
type DotNodeID = Int

-- Type of Dot nodes
data DotNode = DotNode DotNodeID DotLabel DotColor (Maybe DotStyle)

-- Type of Dot edges
data DotEdge = DotEdge DotNodeID DotNodeID

-- Generate the preamble of a Dot file
preamble :: Doc
preamble = graphAttributes $$ nodeAttributes
    where nodeAttributes = text "node" <+> (brackets $ text "style=filled" <> comma <+> text "shape=box") <> semi
          graphAttributes = text "ordering=out;"

renderDotNode :: DotNode -> Doc
renderDotNode (DotNode n l c s) =
    int n
    <+> (brackets $ (((text "label=") <> (doubleQuotes $ text l))
                     <> comma
                     <+> (text "color=") <> (renderColor c)
                     <> styleDoc))
    <> semi
    where styleDoc =
              case s of
                  Just Solid -> comma <+> text "solid"
                  Nothing -> empty

renderDotEdge :: DotEdge -> Doc
renderDotEdge (DotEdge u v) = int u <+> text "->" <+> int v <> semi

-- | Render a Dot document from the preamble, nodes and edges
renderDot :: [DotNode] -> [DotEdge] -> Doc
renderDot ns es = text "digraph" <> (braces $ preamble $$ nodeSection $$ edgeSection)
    where nodeSection = vcat $ map renderDotNode ns
          edgeSection = vcat $ map renderDotEdge es

-- | Create an abstract Dot node from an X100 operator description
constructDotNode :: [AlgNode] -> NodeMap [Tag] -> (AlgNode, VL) -> DotNode
constructDotNode rootNodes ts (n, op) =
    if elem n rootNodes then
        DotNode n l c (Just Solid)
    else
        DotNode n l c Nothing
    where l = escapeLabel $ render $ opDotLabel ts n op
          c = opDotColor op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
-- FIXME no apparent reason to use topological ordering here
extractGraphStructure :: Dag.AlgebraDag VL
                     -> ([(AlgNode, VL)], [(AlgNode, AlgNode)])
extractGraphStructure d = (operators, childs)
    where nodes = Dag.topsort d
          operators = zip nodes $ map (flip Dag.operator d) nodes
          childs = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render an VL plan into a dot file (GraphViz).
renderVLDot :: NodeMap [Tag] -> [AlgNode] -> NodeMap VL -> String
renderVLDot ts roots m = render $ renderDot dotNodes dotEdges
    where (opLabels, edges) = extractGraphStructure d
          d = Dag.mkDag m roots
          dotNodes = map (constructDotNode roots ts) opLabels
          dotEdges = map constructDotEdge edges