module Main(main) where

import Data.List (delete)
import Data.Polynomial

main :: IO ()
main = do
  putStrLn $ unlines $ pprTable $ structureTable poly
  putStrLn "<!-- ****** -->"
  putStrLn $ unlines $ pprTable $ joinTable poly
  where
    poly = T . T . S . T . S . S . T $ U

-- * Html

data Table = Table { thead :: [TR], tbody :: [TR] }
data TR = TR { rowAttrClass :: [String], rowContent :: [TCell] }
data TCell = TCell { cellType :: CellType, cellAttrClass :: [String], cellContent :: String }
data CellType = TD | TH

td, th :: [String] -> String -> TCell
td classes content = TCell TD classes content
th classes content = TCell TH classes content

addCell :: TCell -> TR -> TR
addCell cell tr = tr{ rowContent = cell : rowContent tr }

-- * HTML printing

mkTag :: String -> [String] -> String
mkTag tagName [] = "<" ++ tagName ++ ">"
mkTag tagName classes = "<" ++ tagName ++ " class=\"" ++ unwords classes ++ "\">"

mkEndTag :: String -> String
mkEndTag tagName = "</" ++ tagName ++ ">"

enclose :: String -> [String] -> [String] -> [String]
enclose tagName classes content = [mkTag tagName classes] ++ map ("  " ++) content ++ [mkEndTag tagName]

pprTable :: Table -> [String]
pprTable table =
  enclose "table" [] $
   enclose "thead" [] (thead table >>= pprTR) ++
   enclose "tbody" [] (tbody table >>= pprTR)

pprTR :: TR -> [String]
pprTR TR{ rowAttrClass = classes, rowContent = cells } =
  enclose "tr" classes [ cells >>= pprTCell ]

pprTCell :: TCell -> String
pprTCell TCell { cellType=ct, cellAttrClass = classes, cellContent = content }
  = beginTag ++ content ++ endTag
  where
    tagName = case ct of
      TH -> "th"
      TD -> "td"
    beginTag = mkTag tagName classes
    endTag = mkEndTag tagName

--------------------------------

structureTable :: Poly -> Table
structureTable p = Table [addCell (th [] "") header] bodyRows
  where
    sig = polySignature p
    spans = polySpans p
    header = signatureHeader sig
    headerRow = rowContent header

    bodyRows = makeBodyRow <$> spans
    makeBodyRow n =
      TR [] $ th [] "???" : markRow
      where
        markRow = zipWith marker [0..] headerRow
        marker i headerCell = td (mark ++ cellAttrClass headerCell) ""
          where
            mark | i < n = ["mark"]
                 | otherwise = []

joinTable :: Poly -> Table
joinTable p = Table [addCell (th [] "") header] bodyRows
  where
    sig = polySignature p
    header = signatureHeader sig
    headerRow = rowContent header
    bodyRows = makeBodyRow <$> headerRow
    makeBodyRow headerCell
      | isGap     = TR ("rowgap" : rowsep) ((toGap . noSep) headerCell : map (toGap . toTD) headerRow)
      | otherwise = TR rowsep (noSep headerCell : map toTD headerRow)
      where
        classes = cellAttrClass headerCell

        toGap cell = cell { cellContent = "" }
        toTD cell = cell{ cellType = TD }
        noSep cell = cell{ cellAttrClass = delete "sep" (cellAttrClass cell) }

        isGap = "gap" `elem` classes
        isSep = "sep" `elem` classes

        rowsep = [ "rowsep" | isSep ]

polySignature :: Poly -> [Int]
polySignature = go 0
  where
    go n U = [n]
    go n (S p) = n : go n p
    go n (T p) = go (n + 1) p

polySpans :: Poly -> [Int]
polySpans = go 0
  where
    go n U = [n]
    go n (S U) = [n, n + 1]
    go n (S (S p)) = n : go (n + 1) (S p)
    go n (S (T p)) = n : go (n + 1) p
    go n (T p) = go (n + 1) p

signatureHeader :: [Int] -> TR
signatureHeader sig = TR [] (addSepClass (go 0 sig))
  where
    go _ [] = []
    go n (m : rest)
      | n == m    = th ["gap"] "" : addSepClass (go m rest)
      | otherwise = replicate (m - n) (th ["val"] "●") ++ addSepClass (go m rest)

    addSepClass [] = []
    addSepClass (cell:rest) = cell{ cellAttrClass = "sep" : cellAttrClass cell } : rest