{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use section" #-}
{-# HLINT ignore "Use zipWithM" #-}
import           Control.Monad.Trans.State
import qualified Data.Map                  as Map
import qualified Data.Maybe                as Maybe
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

prettyIR :: AST -> String
prettyIR AstUnit = "()"
prettyIR (AstBool n) = show n
prettyIR (AstInt n) = show n
prettyIR (AstStr n) = show n
prettyIR (Id n) = n
prettyIR (Let n i1 i2) =
  "(let " ++ n ++ " = " ++ prettyIR i1 ++ " in " ++ prettyIR i2 ++ ")"
prettyIR (Abs n i) = "(\\" ++ n ++ " -> " ++ prettyIR i ++ ")"
prettyIR (Apply i1 i2) = "(app " ++ prettyIR i1 ++ " " ++ prettyIR i2 ++ ")"

data Type
  = TUnit
  | TBool
  | TInt
  | TStr
  | TVar String
  | TApply String [Type]
  | TForall [String] Type
  | TError String
  deriving (Show, Eq, Ord)

tFn t0 t1 = TApply "->" [t0, t1]

prettyType' TUnit = "()"
prettyType' TBool = "B"
prettyType' TInt = "I"
prettyType' TStr = "S"
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
  | TcLet Type Name ASTTC ASTTC
  | TcAbs Type Name ASTTC
  | TcApply Type ASTTC ASTTC
  deriving (Show, Eq)

typeOf :: ASTTC -> Type
typeOf (TcUnit t)        = t
typeOf (TcBool t n)      = t
typeOf (TcInt t n)       = t
typeOf (TcStr t n)       = t
typeOf (TcId t _)        = t
typeOf (TcLet t n i1 i2) = t
typeOf (TcAbs t n i)     = t
typeOf (TcApply t i1 i2) = t

prettyIRTC :: ASTTC -> String
prettyIRTC (TcUnit t) = "()" ++ prettyType t
prettyIRTC (TcBool t n) = show n ++ prettyType t
prettyIRTC (TcInt t n) = show n ++ prettyType t
prettyIRTC (TcStr t n) = show n ++ prettyType t
prettyIRTC (TcId t n) = n ++ prettyType t
prettyIRTC (TcLet t n i1 i2) =
  "(let " ++
  n ++
  prettyType (typeOf i1) ++
  " = " ++ prettyIRTC i1 ++ " in " ++ prettyIRTC i2 ++ ")" ++ prettyType t
prettyIRTC (TcAbs t n i) =
  "(abs " ++ n ++ " -> " ++ prettyIRTC i ++ ")" ++ prettyType t
prettyIRTC (TcApply t i1 i2) =
  "(app " ++ prettyIRTC i1 ++ " " ++ prettyIRTC i2 ++ ")" ++ prettyType t

type Ctx = Map.Map String Type

flattenError (TError s) = TError ""
flattenError t          = t

type TypeVars = Map.Map Type Type

type CheckState = (TypeVars, Int)

newvar :: State CheckState Type
newvar = do
  (tv, st) <- get
  put (tv, st + 1)
  pure $ TVar $ "t" ++ show st

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
  if tb `isIn` ta
    then pure $ Left "Infinite type"
    else do
      setTypeReference tb ta
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

checkSt :: (Ctx, AST) -> State CheckState ASTTC
checkSt (ctx, AstUnit) = pure $ TcUnit TUnit
checkSt (ctx, AstBool b) = pure $ TcBool TBool b
checkSt (ctx, AstInt i) = pure $ TcInt TInt i
checkSt (ctx, AstStr s) = pure $ TcStr TStr s
checkSt (ctx, Id x) = do
  case Map.lookup x ctx of
    Nothing -> pure $ TcId (TError $ "Unbound identifier " ++ x) x
    Just s -> do
      t <- inst s
      pure $ TcId t x
checkSt (ctx, Let x e0 e1) = do
  e0tc <- checkSt (ctx, e0)
  let t = flattenError (typeOf e0tc)
  let newCtx = Map.insert x t ctx
  e1tc <- checkSt (newCtx, e1)
  let t' = flattenError (typeOf e1tc)
  t'' <- makeRoot t
  -- TODO qualify new type variables in t''
  -- let s = qualify t'' ctx
  pure $ TcLet t'' x e0tc e1tc
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

builtin :: Ctx
builtin =
  Map.fromList
    [ ("getLine", TApply "IO" [TStr])
    , ("putStr", tFn TStr (TApply "IO" [TUnit]))
    , ( ">>="
      , TForall
          ["a", "b"]
          (tFn
             (TApply "IO" [TVar "a"])
             (tFn
                (tFn (TVar "a") (TApply "IO" [TVar "b"]))
                (TApply "IO" [TVar "b"]))))
    , ("+", binaryOp TInt)
    , ("-", binaryOp TInt)
    , ("*", binaryOp TInt)
    , ("++", binaryOp TStr)
    , ("&&", binaryOp TBool)
    , ("||", binaryOp TBool)
    , ("x", TInt)
    , ("const", TForall ["a", "b"] (tFn (TVar "a") (tFn (TVar "b") (TVar "a"))))
    -- , ("id", TForall ["a"] (tFn (TVar "a") (TVar "a")))
    , ("pre", tFn TStr (tFn TInt TStr))
    ]

check :: AST -> (ASTTC, CheckState)
check p = runState (checkSt (builtin, p)) (Map.empty, 0)

mog = (>>=) getLine

checkProgram :: AST -> IO ()
checkProgram program = do
  putStrLn "\n@@@@@@@@@@@@@@@@@@@@@@@@@"
  putStrLn $ prettyIR program
  let (checkedProgram, st) = check program
  putStrLn $ prettyIRTC checkedProgram
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
  -- , Apply (Id ">>=") (Id "getLine")
  -- , Let "x" (Apply (Id ">>=") (Id "getLine")) (Apply (Id "x") (Id "putStr"))
  -- , Abs "x" (Apply (Id "x") (Id "x"))
  -- , Apply
  --     (Apply (Apply (Id "id") (Id ">>=")) (Apply (Id "id") (Id "getLine")))
  --     (Apply (Id "id") (Id "putStr"))
  -- , Let "id" (Abs "x" (Id "x")) (Apply (Apply (Id "pre") (Apply (Id "id") (AstStr "hello"))) (Apply (Id "id") (AstInt 1)))
  ]

main = do
  mapM_ checkProgram programs
