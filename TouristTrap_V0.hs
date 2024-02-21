import Data.List
import Data.Char

-- 1: defining a model

data Entity = Ent Int deriving (Show, Eq)
data Domain = Domain [Entity] deriving Show
type InterpBool = [(String,[[Entity]])]
type Interp a = [(String, [([Entity], a)])]
data Model = Model Domain InterpBool (Interp Entity) (Interp Int) (Interp String) (Interp (Model -> Model))

instance Show Model where
  show (Model d ib ie ii is imm) =
      "Domain" ++ "\n" ++
      show d ++ "\n" ++
      "Interpretation for Bool:" ++ "\n" ++
      show ib ++ "\n" ++
      "Interpretation for Entity:" ++ "\n" ++
      show ie ++ "\n" ++
      "Interpretation for Int:" ++ "\n" ++
      show ii ++ "\n" ++
      "Interpretation for String:" ++ "\n" ++
      show is ++ "\n" ++
      "Interpretation for (Model -> Model) cannot be displayed."

-- 1.1: Lookup functions for a model.

domHighestIndex :: Domain -> Int
domHighestIndex (Domain d) = maximum [i | (Ent i) <- d]

modelGetDomain :: Model -> Domain
modelGetDomain (Model d _ _ _ _ _) = d

modelGetDomainList :: Model -> [Entity]
modelGetDomainList (Model (Domain l) _ _ _ _ _) = l

modelGetIB :: Model -> InterpBool
modelGetIB (Model _ ib _ _ _ _) = ib

modelGetIE :: Model -> Interp Entity
modelGetIE (Model _ _ ie _ _ _) = ie

modelGetII :: Model -> Interp Int
modelGetII (Model _ _ _ ii _ _) = ii

modelGetIS :: Model -> Interp String
modelGetIS (Model _ _ _ _ is _) = is

iblookup1 :: String -> Model -> (Entity -> Bool)
iblookup1 s (Model _ ib _ _ _ _) = \x -> [x] `elem` l
              where l = if (s `elem` [a | (a,b) <- ib]) then (snd (head [(a,b) | (a,b) <- ib, a==s])) else []

iblookup2 :: String -> Model -> (Entity -> Entity -> Bool)
iblookup2 s (Model _ ib _ _ _ _) = \x -> \y -> [y,x] `elem` l
              where l = if (s `elem` [a | (a,b) <- ib]) then (snd (head [(a,b) | (a,b) <- ib, a==s])) else []

ielookup :: String -> [Entity] -> Model -> Entity
ielookup s l (Model _ _ ie _ _ _) = snd (head [(c,d) | (c,d) <- (snd (head [(a,b) | (a,b) <- ie, a==s])), c==l])

-- 1.2 Other helper functions for the model

ibAlter :: ([[Entity]] -> [[Entity]] -> [[Entity]]) -> (String, [[Entity]]) -> InterpBool -> InterpBool
ibAlter operator (s2,l2) ib = [if (s1 /= s2) then (s1,l1) else (s1, nub (operator l1 l2)) | (s1,l1) <- ib']
                        where ib' = if s2 `elem` [s | (s,t) <- ib] then ib else ib ++ [(s2, [])]

ibAlterSequential :: [(InterpBool -> InterpBool)] -> InterpBool -> InterpBool
ibAlterSequential (f:[]) ib = f ib
ibAlterSequential (f:fx) ib = ibAlterSequential fx (f ib)

iaAlter :: Eq a => ([([Entity], a)] -> [([Entity], a)] -> [([Entity], a)]) -> (String, [([Entity], a)]) -> Interp a -> Interp a
iaAlter operator (s2,l2) ia = [if (s1 /= s2) then (s1,l1) else (s1, nub (operator l1 l2)) | (s1,l1) <- ia']
                        where ia' = if s2 `elem` [s | (s,t) <- ia] then ia else ia ++ [(s2, [])]

iaAlterSequential :: [(Interp a -> Interp a)] -> Interp a -> Interp a
iaAlterSequential (f:[]) ia = f ia
iaAlterSequential (f:fx) ia = iaAlterSequential fx (f ia)

-- 2: parsing

data ParseTree a b = Ep | Leaf a | Branch b [ParseTree a b] deriving Eq

instance (Show a, Show b) => Show (ParseTree a b) where
  show Ep              = "[]"
  show (Leaf t)        = show t
  show (Branch l ts)   = "[." ++ show l ++ " " ++ show ts ++ "]"

-- 2.1: tools for traversing a parse tree

type Pos = [Int]

pos :: ParseTree a b -> [Pos]
pos Ep           = [[]]
pos (Leaf _)     = [[]]
pos (Branch _ ts) = [] : [i:p | (i,t) <- zip [0..] ts, p <- pos t]

subtree :: ParseTree a b -> Pos -> ParseTree a b
subtree t             []     = t
subtree (Branch _ ts) (i:is) = subtree (ts!!i) is

subtrees :: ParseTree a b -> [ParseTree a b]
subtrees t = [subtree t p | p <- pos t]

-- 3: LEXICON

-- 3.1: defining a category

data Feat = Masc | Fem | Neutr | MascOrFem
          | Sg | Pl
          | Fst | Snd | Thrd
          | Nom | AccOrDat
          | Pers | Refl | Wh
          | Tense | Infl
          | On | With | By | To | From | Of
          deriving (Eq, Show, Ord)

type Agreement = [Feat]

type CatLabel = String
type Phon = String
data Cat = Cat Phon CatLabel Agreement [Cat] deriving Eq

instance Show Cat where
  show (Cat "_" label agr subcatlist) = label ++ show agr
  show (Cat phon label agr subcatlist) = phon ++ " " ++ label ++ show agr

gender, number, person, gcase, pronType, tense, prepType :: Agreement -> Agreement
gender = filter (`elem` [MascOrFem, Masc, Fem, Neutr])
number = filter (`elem` [Sg,Pl])
person = filter (`elem` [Fst,Snd,Thrd])
gcase = filter (`elem` [Nom, AccOrDat])
pronType = filter (`elem` [Pers,Refl,Wh])
tense = filter (`elem` [Tense,Infl])
prepType = filter (`elem` [On,With,By,To,From])

-- 3.2: helper functions for categories

prune :: Agreement -> Agreement
prune fs = if (Masc `elem` fs || Fem `elem` fs) then (delete MascOrFem fs) else fs

combine :: Cat -> Cat -> [Agreement]
combine cat1 cat2 = 
  [ feats | length (gender feats) <= 1,
            length (number feats) <= 1,
            length (person feats) <= 1,
            length (gcase feats) <= 1,
            length (pronType feats) <= 1,
            length (tense feats) <= 1,
            length (prepType feats) <= 1]
  where
    feats = (prune . nub . sort) (fs cat1 ++ fs cat2)

agree :: Cat -> Cat -> Bool
agree cat1 cat2 = not (null (combine cat1 cat2))

assign :: Feat -> Cat -> [Cat]
assign f c@(Cat phon label fs subcatlist) =
  [Cat phon label fs' subcatlist | fs' <- combine c (Cat "" "" [f] [])]

phon :: Cat -> String
phon (Cat ph _ _ _) = ph

catLabel :: Cat -> CatLabel
catLabel (Cat _ label _ _) = label

fs :: Cat -> Agreement
fs (Cat _ _ agr _) = agr

subcatList :: Cat -> [Cat]
subcatList (Cat _ _ _ cats) = cats

-- 3.3: the actual lexicon

lexicon :: String -> [Cat]
lexicon "who" = [Cat "who" "NP" [Wh,Thrd,MascOrFem] [], Cat "who" "REL" [MascOrFem] []]
lexicon "player1" = [Cat "player1" "NP" [Thrd,Sg,MascOrFem] []]
lexicon "player2" = [Cat "player2" "NP" [Thrd,Sg,MascOrFem] []]
lexicon "player" = [Cat "player" "CN" [Thrd,Sg,MascOrFem] []]
lexicon "number" = [Cat "number" "CN" [Thrd,Sg,Neutr] []]
lexicon "museum" = [Cat "museum" "CN" [Thrd,Sg,Neutr] []]
lexicon "cathedral" = [Cat "cathedral" "CN" [Thrd,Sg,Neutr] []]
lexicon "winery" = [Cat "winery" "CN" [Thrd,Sg,Neutr] []]
lexicon "wineries" = [Cat "winery" "CN" [Thrd,Pl,Neutr] []]
lexicon "provinces" = [Cat "province" "CN" [Thrd,Pl,Neutr] []]
lexicon "the_louvre" = [Cat "the_louvre" "NP" [Thrd,Sg,Neutr] []]
lexicon "helipad" = [Cat "helipad" "CN" [Sg,Neutr] []]
lexicon "starts" = [Cat "starts" "VP" [Tense] []]
lexicon "has" = [Cat "has" "VP" [Tense] [Cat "_" "NP" [AccOrDat] []]]
lexicon "have" = [Cat "has" "VP" [Tense] [Cat "_" "NP" [AccOrDat] []]]
lexicon "receives" = [Cat "receives" "VP" [Tense] [Cat "_" "NP" [AccOrDat] []]]
lexicon "a" = [Cat "a" "DET" [] []]
lexicon "each" = [Cat "each" "DET" [] []]
lexicon "of" = [Cat "of" "PREP" [Of] []]
lexicon "to" = [Cat "to" "PREP" [To] []]
lexicon "the" = [Cat "the" "DET" [] []]
lexicon "they" = [Cat "they" "NP" [Pers,Thrd,Pl,Nom] []]
lexicon "equal" = [Cat "equal" "ADJ" [] []]
lexicon _ = []

-- 3.4: parsing with a non-stack parser

scan :: String -> String
scan [] = []
scan (x:xs) | x `elem` ".,?" = ' ':x:scan xs
            | otherwise = x:scan xs

type Words = [String]

lexer :: String -> Words
lexer = preproc . words . (map toLower) . scan

preproc :: Words -> Words
preproc [] = []
preproc ["."] = []
preproc ["?"] = []
preproc (",":xs) = preproc xs
preproc ("did":"not":xs) = "didn't": preproc xs
preproc ("nothing":xs) = "no":"thing":preproc xs
preproc ("nobody":xs) = "no":"person":preproc xs
preproc ("something":xs) = "some":"thing":preproc xs
preproc ("somebody":xs) = "some":"person":preproc xs
preproc ("everything":xs) = "every":"thing":preproc xs
preproc ("everybody":xs) = "every":"person":preproc xs
preproc ("less":"than":xs) = "less_than":preproc xs
preproc ("more":"than":xs) = "more_than":preproc xs
preproc ("at":"least":xs) = "at_least":preproc xs
preproc ("at":"most":xs) = "at_most":preproc xs
preproc (x:xs) = x:preproc xs

lookupWord :: (String -> [Cat]) -> String -> [Cat]
lookupWord db w = [ c | c <- db w ]

collectCats :: (String -> [Cat]) -> Words -> [[Cat]]
collectCats db words =
  let
    listing = map (\x -> (x,lookupWord db x)) words
    unknown = map fst (filter (null.snd) listing)
  in
    if unknown /= [] then
      error ("unknown words: " ++ show unknown)
    else initCats (map snd listing)

initCats :: [[Cat]] -> [[Cat]]
initCats [] = [[]]
initCats (cs:rests) = [c:rest | c <- cs, rest <- initCats rests]

t2c :: ParseTree Cat Cat -> Cat
t2c (Leaf c) = c
t2c (Branch c _) = c

agreeC :: ParseTree Cat Cat -> ParseTree Cat Cat -> Bool
agreeC t1 t2 = agree (t2c t1) (t2c t2)

assignT :: Feat -> ParseTree Cat Cat -> [ParseTree Cat Cat]
assignT f (Leaf c) =  [Leaf c' | c' <- assign f c]
assignT f (Branch c ts) = [Branch c' ts | c' <- assign f c]

match :: [Cat] -> [Cat] -> Bool
match [] [] = True
match _ [] = False
match [] _ = False
match (x:xs) (y:ys) = catLabel x == catLabel y && agree x y && match xs ys

-- 3.5 Stack Parser

type StackParser a b = [a] -> [a] -> [(b,[a],[a])]

type SPARSER a b = StackParser a (ParseTree a b)

infixr 4 <||>

(<||>) :: StackParser a b -> StackParser a b -> StackParser a b
(p1 <||> p2) stack xs = p1 stack xs ++ p2 stack xs

infixl 6 <::>
(<::>) :: StackParser a b -> StackParser a [b] -> StackParser a [b]
(p <::> q) us xs = [(r:rs,ws,zs) | (r,vs,ys) <- p us xs, (rs,ws,zs) <- q vs ys]

succeedS :: b -> StackParser a b
succeedS r us xs = [(r,us,xs)]

manyS :: StackParser a b -> StackParser a [b]
manyS p = (p <::> manyS p) <||> succeedS []

push :: Cat -> SPARSER Cat Cat -> SPARSER Cat Cat
push c p stack = p (c:stack)

pop :: CatLabel -> SPARSER Cat Cat
pop c [] xs = []
pop c (u:us) xs | catLabel u == c = [(Leaf u, us, xs)]
                | otherwise = []

leafPS :: CatLabel -> SPARSER Cat Cat
leafPS l _ [] = []
leafPS l s (c:cs) = [(Leaf c,s,cs) | catLabel c == l]

prsTXT :: SPARSER Cat Cat
prsTXT = conjR <||> prsS

conjR :: SPARSER Cat Cat
conjR = \ us xs ->
  [ (Branch (Cat "_" "TXT" [] [])[s,conj,txt], ws, zs) |
      (s,vs,ys) <- prsS us xs,
      (conj,vs1,ys1) <- leafPS "CONJ" vs ys,
      (txt,ws,zs) <- prsTXT vs1 ys1      
  ]

prsS :: SPARSER Cat Cat
prsS = spR <||> cond1R <||> cond2R

spR :: SPARSER Cat Cat
spR = \ us xs ->
  [ (Branch (Cat "_" "S" (fs (t2c np)) []) [np',vp],ws,zs) |
        (np,vs,ys) <- prsNP us xs,
        (vp,ws,zs) <- prsVP vs ys,
        np' <- assignT Nom np,
        agreeC np vp,
        subcatList (t2c vp) == [] ]

cond1R :: SPARSER Cat Cat
cond1R = \ us xs ->
  [ (Branch (Cat "_" "S" [] []) [cond,s1,s2], ws,zs) |
    (cond,vs,ys) <- leafPS "COND" us xs,
    (s1,vs1,ys1) <- prsS vs ys,
    (s2,ws,zs) <- prsS vs1 ys1 ]

cond2R :: SPARSER Cat Cat
cond2R = \ us xs ->
  [ (Branch (Cat "_" "S" [] []) [cond,s1,s2], ws,zs) |
      (cond,vs,ys) <- leafPS "COND" us xs,
      (s1,vs1,ys1) <- prsS vs ys,
      (_,vs2,ys2) <- leafPS "THEN" vs1 ys1,
      (s2,ws,zs) <- prsS vs2 ys2  ]

prsNP :: SPARSER Cat Cat
prsNP = leafPS "NP" <||> npR <||> pop "NP"

npR :: SPARSER Cat Cat
npR = \ us xs ->
  [ (Branch (Cat "_" "NP" fs []) [det,cn], (us++ws), zs) |
      (det,vs,ys) <- prsDET [] xs,
      (cn,ws,zs) <- prsCN vs ys,
      fs <- combine (t2c det) (t2c cn),
      agreeC det cn  ]

prsDET :: SPARSER Cat Cat
prsDET = leafPS "DET"

prsCN :: SPARSER Cat Cat
prsCN = leafPS "CN" <||> cnrelR

prsVP :: SPARSER Cat Cat
prsVP = finVpR <||> auxVpR

vpR :: SPARSER Cat Cat
vpR = \us xs ->
  [(Branch (Cat "_" "VP" (fs (t2c vp)) []) (vp:xps), ws,zs) |
      (vp,vs,ys) <- leafPS "VP" us xs,
      subcatlist <- [subcatList (t2c vp)],
      (xps,ws,zs) <- prsNPsorPPs vs ys,
      match subcatlist (map t2c xps)  ]

finVpR :: SPARSER Cat Cat
finVpR = \ us xs -> [(vp',vs,ys) | (vp,vs,ys) <- vpR us xs, vp' <- assignT Tense vp]

auxVpR :: SPARSER Cat Cat
auxVpR = \us xs ->
    [ (Branch (Cat "_" "VP" (fs (t2c aux)) []) [aux,inf'], ws, zs) |
          (aux,vs,ys) <- prsAUX us xs,
          (inf,ws,zs) <- vpR vs ys,
          inf' <- assignT Infl inf  ]

prsAUX :: SPARSER Cat Cat
prsAUX = leafPS "AUX" <||> pop "AUX"

prsPP :: SPARSER Cat Cat
prsPP = ppR <||> pop "PP"

ppR :: SPARSER Cat Cat
ppR = \ us xs ->
  [ (Branch (Cat "_" "PP" fs []) [prep,np'], ws, zs) |
      (prep,vs,ys) <- prsPREP us xs,
      (np,ws,zs) <- prsNP vs ys,
      np' <- assignT AccOrDat np,
      fs <- combine (t2c prep) (t2c np') ]

prsPREP :: SPARSER Cat Cat
prsPREP = leafPS "PREP"

prsNPorPP :: SPARSER Cat Cat
prsNPorPP = prsNP <||> prsPP

prsNPsorPPs :: [Cat] -> [Cat] -> [([ParseTree Cat Cat], [Cat], [Cat])]
prsNPsorPPs = manyS prsNPorPP

cnrelR :: SPARSER Cat Cat
cnrelR = \us xs ->
    [ (Branch (Cat "_" "CN" (fs (t2c cn)) []) [cn,rel], ws, zs) |
      (cn,vs,ys) <- leafPS "CN" us xs,
      (rel,ws,zs) <- prsREL vs ys,
      agreeC cn rel  ]

prsREL :: SPARSER Cat Cat
prsREL = relclauseR <||> thatlessR

relclauseR :: SPARSER Cat Cat
relclauseR = \us xs ->
  [(Branch (Cat "_" "COMP" fs []) [rel,s], ws, zs) |
        (rel,vs,ys) <- leafPS "REL" us xs,
        fs <- [fs (t2c rel)],
        gap <- [Cat "#" "NP" fs []],
        (s,ws,zs) <- push gap prsS vs ys  ]

thatlessR :: SPARSER Cat Cat
thatlessR = \ us xs ->
    [ (Branch (Cat "_" "COMP" [] []) [s], vs, ys) |
      gap <- [Cat "#" "NP" [AccOrDat] []],
      (s,vs,ys) <- push gap prsS us xs,
      notElem Wh (fs (t2c s))      ]

prsYN :: SPARSER Cat Cat
prsYN = \us xs ->
  [(Branch (Cat "_" "YN" [] []) [aux,s], ws, zs) |
      (aux,vs,ys) <- prsAUX us xs,
      gap <- [Cat "#" "AUX" (fs (t2c aux)) [] ],
      (s,ws,zs) <- push gap prsS vs ys    ]

isWH :: ParseTree Cat Cat -> Bool
isWH tr = Wh `elem` (fs (t2c tr))

prsWH :: SPARSER Cat Cat
prsWH = \us xs ->
  [ (Branch (Cat "_" "WH" [] []) [wh,yn],ws,zs) |
    (wh,vs,ys) <- prsNPorPP us xs,
    isWH wh,
    gapfs <- [filter (/= Wh) (fs (t2c wh))],
    gap <- [Cat "#" (catLabel (t2c wh)) gapfs []],
    (yn,ws,zs) <- push gap prsYN vs ys    ]

parses :: String -> [ParseTree Cat Cat]
parses str = let ws = lexer str
             in [s | catlist <- collectCats lexicon ws,
                 (s,[],[]) <- prsTXT [] catlist ++ prsYN [] catlist ++ prsWH [] catlist]

-- 4: semantic interpretation of parsed sentences in a model

transS :: ParseTree Cat Cat -> Model -> Bool
transS (Branch (Cat _ "S" _ _) [np,vp]) m = (transNP np m) (transVP vp m)

transNP :: ParseTree Cat Cat -> Model -> (Entity -> Bool) -> Bool
transNP (Leaf (Cat name "NP" _ _)) m = \p -> p (ielookup name [] m)

transNPPred :: ParseTree Cat Cat -> Model -> Entity -> Bool
transNPPred (Branch (Cat _ "NP" _ _) [Leaf (Cat "a" "DET" _ _), Leaf (Cat name "CN" _ _)]) m = iblookup1 name m

transVP :: ParseTree Cat Cat -> Model -> Entity -> Bool
transVP (Branch (Cat _ "VP" _ _) [Leaf (Cat "has" "VP" _ _), Branch (Cat _ "NP" _ _) [Leaf (Cat "a" "DET" _ _), Leaf cn]]) m = \y -> any (\x -> (((itransCN (Leaf cn) m) x) && (iblookup2 "has" m) x y)) (modelGetDomainList m)
transVP (Branch (Cat _ "VP" _ _) [Leaf (Cat name "VP" _ [])]) m = iblookup1 name m
transVP (Branch (Cat _ "VP" _ _) [Leaf (Cat name "VP" _ [_]),np]) m =
      \ subj -> (transNP np m)(\ obj -> (iblookup2 name m) obj subj)

transPP :: ParseTree Cat Cat -> Model -> Entity -> Bool
transPP (Branch (Cat _ "PP" _ _) [Leaf (Cat "with" "PREP" _ _), Branch (Cat _ "NP" _ _) [Leaf (Cat "a" "DET" _ _), Leaf (Cat name "CN" _ _)]]) m = \x -> (iblookup1 name m) x

transDET :: ParseTree Cat Cat -> (Entity -> Bool) -> ((Int -> Bool), (Entity -> Bool))
transDET (Leaf (Cat "a" "DET" _ _)) = \x -> ((>=1),x)
transDET (Leaf (Cat "no" "DET" _ _)) = \x -> ((==0),x)

itransS :: ParseTree Cat Cat -> Model -> Model
itransS (Branch (Cat _ "S" _ _) [np,vp]) m = (itransVP vp m) (itransNP np m)

itransVP :: ParseTree Cat Cat -> Model -> [Entity] -> Model
itransVP (Branch (Cat _ "VP" _ _) [Leaf (Cat "receives" "VP" _ _), np]) (Model (Domain d) ib ie ii is ia) elist = Model (Domain (d ++ newentities)) newIB ie ii is ia
                      where newentities = if ((length elist) > 0) then [Ent x | x <- [(1 + domHighestIndex (Domain d))..((length elist) + domHighestIndex (Domain d))]] else []
                            etups = zip elist newentities
                            newIB = ibAlterSequential [ibAlter (++) (itransNPname np, [[a] | a <- newentities]), ibAlter (++) ("has", [[a,b] | (a,b) <- etups])] ib

itransNPname :: ParseTree Cat Cat -> String
itransNPname (Branch (Cat _ "NP" _ _) [Leaf (Cat "a" "DET" _ _), Leaf (Cat name "CN" _ _)]) = name

itransNP :: ParseTree Cat Cat -> Model -> [Entity]
itransNP (Branch (Cat _ "NP" _ _) [Leaf (Cat "each" "DET" _ _), Leaf (Cat name "CN" _ _)]) m = [x | x <- (modelGetDomainList m), (iblookup1 name m) x]
itransNP (Branch (Cat _ "NP" _ _) [Leaf (Cat "each" "DET" _ _), Branch (Cat _ "CN" _ _) [cn,comp]]) m = [x | x <- (modelGetDomainList m), (itransCN cn m) x, (itransCOMP comp m) x]

itransCN :: ParseTree Cat Cat -> Model -> Entity -> Bool
itransCN (Leaf (Cat "cathedral" "CN" _ _)) m = iblookup1 "cathedral" m
itransCN (Leaf (Cat "museum" "CN" _ _)) m = iblookup1 "museum" m
itransCN (Leaf (Cat "player" "CN" _ _)) m = iblookup1 "player" m
itransCN (Leaf (Cat "winery" "CN" _ _)) m = iblookup1 "winery" m
itransCN (Branch (Cat _ "CN" _ _) [Leaf (Cat name1 "CN" _ _), compbranch]) m = \x -> (((itransCN (Leaf (Cat "" name1 [] []))) m) x && (itransCOMP compbranch m) x)
                  
itransCOMP :: ParseTree Cat Cat -> Model -> Entity -> Bool
itransCOMP (Branch (Cat _ "COMP" _ _) [Leaf (Cat _ "REL" _ _), (Branch (Cat _ "S" _ _) [_, vp])]) m = transVP vp m 

testtransS :: ParseTree Cat Cat -> Model -> Bool
testtransS (Branch (Cat _ "S" _ _) [np,vp]) m = (testtransVP vp m) (testtransNP np m) 

testtransVP :: ParseTree Cat Cat -> Model -> (Int -> Bool, Entity -> Bool) -> Bool
testtransVP (Branch (Cat _ "VP" _ _) [tv,dobj]) m (op, func) = op (length [x | x <- (modelGetDomainList m), func x, ((testtranstransitiveVP tv m) (testtransNP dobj m)) x])

testtranstransitiveVP :: ParseTree Cat Cat -> Model -> ((Int -> Bool), (Entity -> Bool)) -> Entity -> Bool
testtranstransitiveVP (Leaf (Cat "has" "VP" _ _)) m (op, func) = \x -> (op) (length [y | y <- (modelGetDomainList m), func y, (iblookup2 "has" m) y x])

testtransNP :: ParseTree Cat Cat -> Model -> ((Int -> Bool), (Entity -> Bool))
testtransNP (Branch (Cat _ "NP" _ _) [Leaf det, Leaf cn]) m = (testtransDET (Leaf det) m) (itransCN (Leaf cn) m)

testtransDET :: ParseTree Cat Cat -> Model -> (Entity -> Bool) -> ((Int -> Bool), (Entity -> Bool))
testtransDET (Leaf (Cat "each" "DET" _ _)) m = \x -> ((==(length [y | y <- modelGetDomainList m, x y])), x)
testtransDET (Leaf (Cat "a" "DET" _ _)) m = \x -> ((>=1), x)

-- 5: Test lines

test_dom = Domain [Ent x | x <- [1..20]]
test_ibool = [("starts", [[Ent 1]]), ("has", [[Ent 1, Ent 5],[Ent 1, Ent 10],[Ent 2, Ent 11],[Ent 3, Ent 12]]), ("helipad", [[Ent 10]]), ("player", [[Ent 1], [Ent 2], [Ent 3], [Ent 4]]), ("museum", [[Ent 11], [Ent 12], [Ent 13], [Ent 14]])]
test_ientity = [("player1",[([],Ent 1)]), ("player2",[([],Ent 2)]), ("player3",[([],Ent 3)]), ("player4",[([],Ent 4)]), ("the_louvre",[([],Ent 5)])]
test_model1 = Model test_dom test_ibool test_ientity [] [] []
test_sentence1 = "each player who has a museum receives a cathedral"
test_parse1 = head (parses test_sentence1)
test_sem1 = itransS test_parse1
s = subtrees test_parse1
test_model2 = test_sem1 test_model1
test_sentence2 = "each player receives a winery"
test_parse2 = head (parses test_sentence2)
test_sem2 = itransS test_parse2
test_model3 = test_sem2 test_model2
test_sentence3 = "each player receives a number of wineries equal to the number of provinces they have"