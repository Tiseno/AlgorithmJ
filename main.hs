{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use section" #-}
{-# HLINT ignore "Use zipWithM" #-}
{-# HLINT ignore "Use list comprehension" #-}
import           Control.Monad.Trans.State
import           Data.Bifunctor            (second)
import qualified Data.Char                 as Char
import qualified Data.Map                  as Map
import qualified Data.Set                  as Set
import qualified Debug.Trace               as Debug

type Name = String

data AST
  = AstUnit
  | AstBool Bool
  | AstInt Int
  | AstStr String
  | Id Name
  | Let Name AST AST
  | Abs Name AST
  | Apply AST AST
  deriving (Show, Eq)

prettyAst :: AST -> String
prettyAst AstUnit = "()"
prettyAst (AstBool n) = show n
prettyAst (AstInt n) = show n
prettyAst (AstStr n) = show n
prettyAst (Id n) = n
prettyAst (Let n i1 i2) =
  "(let " ++ n ++ " = " ++ prettyAst i1 ++ " in " ++ prettyAst i2 ++ ")"
prettyAst (Abs n i) = "(\\" ++ n ++ " -> " ++ prettyAst i ++ ")"
prettyAst (Apply i1 i2) = "(app " ++ prettyAst i1 ++ " " ++ prettyAst i2 ++ ")"

data Type
  = TConst String
  | TVar String
  | TApply String [Type]
  | TForall [String] Type
  | TError String
  deriving (Show, Eq, Ord)

tUnit = TConst "()"

tBool = TConst "Bool"

tInt = TConst "Int"

tStr = TConst "Str"

tFn t0 t1 = TApply "->" [t0, t1]

prettyType' (TConst x) = x
prettyType' (TVar x) = x
prettyType' (TApply "->" [t0@(TApply "->" _), t1]) =
  "(" ++ prettyType' t0 ++ ")->" ++ prettyType' t1
prettyType' (TApply "->" [t0, t1]) = prettyType' t0 ++ "->" ++ prettyType' t1
prettyType' (TApply n t) = n ++ " " ++ unwords (fmap prettyTypeR t)
prettyType' (TForall q t) = unwords q ++ " . " ++ prettyType' t
prettyType' (TError "") = "Error"
prettyType' (TError e) = "Error(" ++ e ++ ")"

prettyTypeR t@(TApply _ _)  = "(" ++ prettyType' t ++ ")"
prettyTypeR t@(TForall _ _) = "(" ++ prettyType' t ++ ")"
prettyTypeR t               = prettyType' t

prettyType t = ":" ++ prettyTypeR t

data ASTTC
  = TcUnit Type
  | TcBool Type Bool
  | TcInt Type Int
  | TcStr Type String
  | TcId Type Name
  | TcLet Type Name Type ASTTC ASTTC
  | TcAbs Type Name ASTTC
  | TcApply Type ASTTC ASTTC
  deriving (Show, Eq)

typeOf :: ASTTC -> Type
typeOf (TcUnit t)           = t
typeOf (TcBool t n)         = t
typeOf (TcInt t n)          = t
typeOf (TcStr t n)          = t
typeOf (TcId t _)           = t
typeOf (TcLet t n t' i1 i2) = t
typeOf (TcAbs t n i)        = t
typeOf (TcApply t i1 i2)    = t

prettyAstTc :: ASTTC -> String
prettyAstTc (TcUnit t) = "()" ++ prettyType t
prettyAstTc (TcBool t n) = show n ++ prettyType t
prettyAstTc (TcInt t n) = show n ++ prettyType t
prettyAstTc (TcStr t n) = show n ++ prettyType t
prettyAstTc (TcId t n) = n ++ prettyType t
prettyAstTc (TcLet t n t' i1 i2) =
  "(let " ++
  n ++
  prettyType t' ++
  " = " ++ prettyAstTc i1 ++ " in " ++ prettyAstTc i2 ++ ")" ++ prettyType t
prettyAstTc (TcAbs t n i) =
  "(\\" ++ n ++ " -> " ++ prettyAstTc i ++ ")" ++ prettyType t
prettyAstTc (TcApply t i1 i2) =
  "(app " ++ prettyAstTc i1 ++ " " ++ prettyAstTc i2 ++ ")" ++ prettyType t

type Ctx = Map.Map String Type

flattenError (TError s) = TError ""
flattenError t          = t

type TypeVars = Map.Map Type Type

type CheckState = (TypeVars, Int)

newvar :: State CheckState Type
newvar = do
  (tv, st) <- get
  let new = st + 1
  put (tv, new)
  pure $ TVar $ "t" ++ show new

makeRoot :: Type -> State CheckState Type
makeRoot (TApply n t) = do
  t' <- mapM makeRoot t
  pure $ TApply n t'
makeRoot t@(TVar x) = do
  found <- find t
  if t == found
    then pure found
    else makeRoot found
makeRoot t = pure t

find :: Type -> State CheckState Type
find t = do
  (tv, _) <- get
  case Map.lookup t tv of
    Nothing -> pure t
    Just t0 -> find t0

setTypeReference :: Type -> Type -> State CheckState ()
setTypeReference ta tb = do
  (tv, st) <- get
  put (Map.insert ta tb tv, st)
  pure ()

unify :: Type -> Type -> State CheckState (Either String ())
unify a b = do
  ta <- find a
  tb <- find b
  unify' ta tb

isVar (TVar _) = True
isVar _        = False

firstLeft :: [Either a b] -> Either a ()
firstLeft ((Left l):es)  = Left l
firstLeft ((Right l):es) = firstLeft es
firstLeft []             = Right ()

isIn :: Type -> Type -> Bool
isIn ta tb
  | ta == tb = True
isIn ta (TApply _ ts) = any (isIn ta) ts
isIn ta (TForall _ tb) = ta `isIn` tb
isIn _ _ = False

unify' :: Type -> Type -> State CheckState (Either String ())
unify' (TError e) _ = pure $ Left ""
unify' _ (TError e) = pure $ Left ""
unify' ta tb
  | ta == tb = pure $ Right ()
unify' ta@(TApply c0 p0) tb@(TApply c1 p1) =
  if c0 == c1 && length p0 == length p1
    then do
      m <- mapM (uncurry unify) (zip p0 p1)
      pure $ firstLeft m
    else pure $ Left "Different type structure"
unify' ta tb@(TVar _) = unify' tb ta
unify' ta@(TVar _) tb = do
  if ta `isIn` tb
    then pure $ Left "Infinite type"
    else do
      setTypeReference ta tb
      pure $ Right ()
unify' ta tb =
  pure $
  Left $
  "Type '" ++ prettyType' ta ++ "' does not match '" ++ prettyType' tb ++ "'"

replace :: Type -> (Type, Type) -> Type
replace (TApply n t) (sub, r) = TApply n (fmap (flip replace (sub, r)) t)
replace (TForall q t) (sub, r) =
  error "TForall quantifier in replace should not happen"
replace t (sub, r)
  | sub == t = r
  | otherwise = t

inst :: Type -> State CheckState Type
inst (TForall quantifiers t) = do
  substitutions <- mapM createSubstitution (fmap TVar quantifiers)
  pure $ foldl replace t substitutions
  where
    createSubstitution :: Type -> State CheckState (Type, Type)
    createSubstitution s = do
      t <- newvar
      pure (s, t)
inst t = pure t

-- TODO do this in a nicer way
collectNewTypeVars :: Int -> Type -> [Type]
collectNewTypeVars n t = Set.toList $ Set.fromList $ collectNewTypeVars' n t
  where
    collectNewTypeVars' :: Int -> Type -> [Type]
    collectNewTypeVars' _ t@(TConst _) = []
    collectNewTypeVars' n t@(TVar ('t':m)) =
      if n < read m
        then [t]
        else []
    collectNewTypeVars' n t@(TApply _ ts) = concatMap (collectNewTypeVars' n) ts
    collectNewTypeVars' n t@(TForall _ p) = collectNewTypeVars' n p
    collectNewTypeVars' _ t@(TError _) = []

qualify :: Int -> Type -> Type
qualify n t =
  let newTypeVars :: [Type] = collectNewTypeVars n t
      names = fmap (\i -> [Char.chr (97 + i)]) [0 ..]
      substitutions :: [(Type, Type)] =
        fmap (second TVar) (zip newTypeVars names)
   in TForall (take (length newTypeVars) names) $ foldl replace t substitutions

checkSt :: (Ctx, AST) -> State CheckState ASTTC
checkSt (ctx, AstUnit) = pure $ TcUnit tUnit
checkSt (ctx, AstBool b) = pure $ TcBool tBool b
checkSt (ctx, AstInt i) = pure $ TcInt tInt i
checkSt (ctx, AstStr s) = pure $ TcStr tStr s
checkSt (ctx, Id x) = do
  case Map.lookup x ctx of
    Nothing -> pure $ TcId (TError $ "Unbound identifier " ++ x) x
    Just s -> do
      t <- inst s
      pure $ TcId t x
checkSt (ctx, Let x e0 e1) = do
  (_, st) <- get
  e0tc <- checkSt (ctx, e0)
  -- TODO add x = newvar to the context before checking e0 to support recursive definitions
  let t = flattenError (typeOf e0tc)
  let s = qualify st t
  let newCtx = Map.insert x s ctx
  e1tc <- checkSt (newCtx, e1)
  t'' <- makeRoot (flattenError (typeOf e1tc))
  pure $ TcLet t'' x s e0tc e1tc
checkSt (ctx, Abs x e) = do
  t <- newvar
  let newCtx = Map.insert x t ctx
  etc <- checkSt (newCtx, e)
  t' <- makeRoot (tFn t (typeOf etc))
  pure $ TcAbs t' x etc
checkSt (ctx, Apply e0 e1) = do
  e0tc <- checkSt (ctx, e0)
  let t0 = typeOf e0tc
  e1tc <- checkSt (ctx, e1)
  let t1 = typeOf e1tc
  t' <- newvar
  unifyResult <- unify t0 (tFn t1 t')
  let t = either TError (const t') unifyResult
  t'' <- makeRoot t
  pure $ TcApply t'' e0tc e1tc

binaryOp t = tFn t (tFn t t)

tkvMap = TApply "Map" [TVar "k", TVar "v"]

builtin :: Ctx
builtin =
  Map.fromList
    [ ("Map.empty", TForall ["k", "v"] tkvMap)
    , ( "Map.insert"
      , TForall ["k", "v"] (tFn (TVar "k") (tFn (TVar "v") (tFn tkvMap tkvMap))))
    , ("getLine", TApply "IO" [tStr])
    , ("putStr", tFn tStr (TApply "IO" [tUnit]))
    , ( ">>="
      , TForall
          ["a", "b"]
          (tFn
             (TApply "IO" [TVar "a"])
             (tFn
                (tFn (TVar "a") (TApply "IO" [TVar "b"]))
                (TApply "IO" [TVar "b"]))))
    , ("+", binaryOp tInt)
    , ("-", binaryOp tInt)
    , ("*", binaryOp tInt)
    , ("++", binaryOp tStr)
    , ("&&", binaryOp tBool)
    , ("||", binaryOp tBool)
    , ("x", tInt)
    , ("const", TForall ["a", "b"] (tFn (TVar "a") (tFn (TVar "b") (TVar "a"))))
    , ("id", TForall ["a"] (tFn (TVar "a") (TVar "a")))
    ]

check :: AST -> (ASTTC, CheckState)
check p = runState (checkSt (builtin, p)) (Map.empty, 0)

mog = (>>=) getLine

checkProgram :: AST -> IO ()
checkProgram program = do
  putStrLn "\n@@@@@@@@@@@@@@@@@@@@@@@@@"
  putStrLn $ prettyAst program
  let (checkedProgram, st) = check program
  putStrLn $ prettyAstTc checkedProgram
  print st
  putStrLn ""

programs =
  [ Let "main" (Apply (Apply (Id "+") (AstInt 1)) (AstInt 2)) (Id "main")
  , Apply (Apply (Id "const") (AstInt 1)) (AstInt 1)
  , Apply (Id ">>=") (Id "getLine")
  , Apply (Apply (Id ">>=") (Id "getLine")) (Id "putStr")
  , Apply (Id ">>=") (AstInt 0)
  , Abs "x" (Apply (Id "+") (Id "x"))
  , Let "$" (Abs "fn" (Abs "x" (Apply (Id "fn") (Id "x")))) (Id "$")
  , Let "myid" (Abs "x" (Id "x")) (Apply (Id "myid") (AstInt 1))
  -- , Apply (Id ">>=") (Id "getLine")
  -- , Let "x" (Apply (Id ">>=") (Id "getLine")) (Apply (Id "x") (Id "putStr"))
  -- , Abs "x" (Apply (Id "x") (Id "x"))
  -- , Apply
  --     (Apply (Apply (Id "id") (Id ">>=")) (Apply (Id "id") (Id "getLine")))
  --     (Apply (Id "id") (Id "putStr"))
  -- , Let "id" (Abs "x" (Id "x")) (Apply (Apply (Id "pre") (Apply (Id "id") (AstStr "hello"))) (Apply (Id "id") (AstInt 1)))
  -- , Apply (Id "Map.insert") (AstStr "key")
  -- , Apply (Apply (Id "Map.insert") (AstStr "key")) (AstInt 1)
  -- , Apply
  --     (Apply (Apply (Id "Map.insert") (AstStr "key")) (AstInt 1))
  --     (Id "Map.empty")
  ]

main = do
  mapM_ checkProgram programs
