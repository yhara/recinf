-- 多相の型推論(アルゴリズムW)
-- p.227-
--  - 多相型があると、「主要な型判定」が存在しない
--  - そのためアルゴリズムWは、「与えられた型環境の下で」最も一般的な型判定を求める
--    - 完成したプログラム＝閉じた式、なので実用上は困ることはない

import Test.Hspec
import Data.Map
import Data.List
import Control.Monad.State
--{-# LANGUAGE TypeSynonymInstances #-}
-- 

type Label = String
type Name = String

-- Types

data Prim = PBool Bool | PInt Int
  deriving (Eq, Show)
type VId = Int
data MonoTy = TyPrim Prim
            | TyVar VId
            | TyFun MonoTy MonoTy
  deriving (Eq, Show)
type TyScm = ([VId], MonoTy)

varIds :: MonoTy -> [VId]
varIds (TyPrim _) = []
varIds (TyVar id) = [id]
varIds (TyFun t1 t2) = varIds t1 ++ varIds t2

freeTypeIds :: TyScm -> [VId]
freeTypeIds (ids, t) = (varIds t) Data.List.\\ ids

isMono :: TyScm -> Bool
isMono (ids, ty) = Prelude.null ids

-- 多相型の型変数を、freshなTyVarで置き換えたものを返す
-- TyScmが単相のときはそれをそのまま返す
--instantiate :: Int -> TyScm -> (Int, MonoTy)
--instantiate i (ids, ty) =
--  let l = length ids in
--  let ss = fromList $
--             Prelude.map (\(id,newid) -> (id, TyVar newid))
--                         (zip ids [i..i+l-1]) in
--    (i+l, substMonoTy ss ty)
--
instantiate :: TyScm -> StateT Int Maybe MonoTy
instantiate (ids, ty) = do
  ss <- foldM (\sum id -> do
                ty <- newTyVar
                return $ Data.Map.insert id ty sum)
              empty
              ids
  return $ substMonoTy ss ty

-- p.220のCls
-- tsの型変数のうち、envに現れないものを多相にしたもの
typeCls :: MonoTy -> TyEnv -> TyScm
typeCls ty env =
  let envIds = concatMap freeTypeIds (elems env) in
  (varIds ty Data.List.\\ envIds, ty)

--ftv :: TyScm -> [VId]
--ftv (TyPrim _) = []
--ftv (TyVar i) = [i]
--ftv (TyFun ts1 ts2) = (ftv ts1) ++ (ftv ts2)

occursTy :: Int -> MonoTy -> Bool
occursTy i (TyPrim _) = False
occursTy i (TyVar ii) = (i == ii)
occursTy i (TyFun ty1 ty2) = occursTy i ty1 || occursTy i ty2

occurs :: Int -> TyScm -> Bool
occurs i (_, ty) = occursTy i ty

-- p.165 なぜ型変数、型スキーマが必要か？
-- 「与えられた式に対して、それを満たす型判定の集合を求める」には、
-- 型判定の集合(一般には無限)を表す方法が必要。
-- そこで型変数を使って、「(a->a)->a」みたいに表す。
-- 型スキーマ＝型変数を含んだ型

type Subst = Map VId MonoTy

substMonoTy :: Subst -> MonoTy -> MonoTy
substMonoTy ss t@(TyPrim _) = t
substMonoTy ss t@(TyVar i) =
  case Data.Map.lookup i ss of
    Just ts -> ts
    Nothing -> t
substMonoTy ss (TyFun ts1 ts2) =
  TyFun (substMonoTy ss ts1) (substMonoTy ss ts2)

substTyScm :: Subst -> TyScm -> TyScm
substTyScm ss (ids, ty) = (ids, substMonoTy ss ty)

substSubst :: Subst -> Subst -> Subst
substSubst ss target = Data.Map.map (substMonoTy ss) target

-- Unification

type TyEq = (MonoTy, MonoTy)
type Constraints = ([TyEq], Subst)

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substMonoTy ss t1, substMonoTy ss t2)

unify :: [TyEq] -> Maybe Subst
unify tyeqs = unify' tyeqs Data.Map.empty
  where
    unify' :: [TyEq] -> Subst -> Maybe Subst
    unify' [] subst = Just subst
    unify' ((ts1, ts2):rest) subst =
      case (ts1, ts2) of
        (TyVar id1, TyVar id2) | id1 == id2 ->
          unify' rest subst
        (TyVar id1, _) -> 
          if occursTy id1 ts2
          then Nothing
          else let ss = Data.Map.singleton id1 ts2 in
                 unify' (Prelude.map (substTyEq ss) rest)
                        (Data.Map.union ss (substSubst ss subst))
        (_, TyVar id2) ->
          unify' ((ts2, ts1):rest) subst
        (TyFun t1 t2, TyFun t3 t4) ->
          unify' ((t1, t3):(t2, t4):rest) subst

-- Inference

data Expr
  = ELit Prim 
  | EVar Name
  | EAbs Name Expr
  | EApp Expr Expr
  | ELet Name Expr Expr
  deriving (Eq, Show)

-- TyEnvにはTyScmが入っている(p.228図5.7 下から2行目より)
type TyEnv = Map Name TyScm
substTyEnv :: Subst -> TyEnv -> TyEnv
substTyEnv ss env = Data.Map.map (substTyScm ss) env 

-- p.171のmatches
-- matches({e1,...,en}) = ...
--   各eiとejについて
--     両者で重複しているキーxについて,(ei[x],ej[x])をとる
-- つまり、e1,...,enからすべての方程式を抽出する
--extractTyEqs :: TyEnv -> TyEnv -> [TyEq]
--extractTyEqs e1 e2 = elems $ intersectionWith (,) e1 e2
--
--infer :: Int -> Expr -> Maybe (Int, TyEnv, TyScm)
--infer i (ELit prim) =
--  Just (i, Data.Map.empty, TyPrim prim)
--infer i (EVar name) =
--  Just (i+1, Data.Map.singleton name (TyVar i), TyVar i)
--infer i (EAbs name expr) = do
--  (i', env, tret) <- infer i expr
--  case Data.Map.lookup name env of
--    Just targ -> Just (i', delete name env, TyFun targ tret)
--    Nothing -> Just (i'+1, env, TyFun (TyVar i') tret)
--infer i (EApp fexpr aexpr) = do
--  (i',  e1, t1) <- infer i fexpr
--  (i'', e2, t2) <- infer i' aexpr
--  let tret = TyVar i''
--  ss <- unify ((extractTyEqs e1 e2) ++ [(t1, TyFun t2 tret)])
--  return (i''+1,
--          union (substTyEnv ss e1) (substTyEnv ss e2),
--          substTyScm ss tret)

-- W

newTyVar :: StateT Int Maybe MonoTy
newTyVar = do
  newId <- get
  put (newId+1)
  return (TyVar newId)

inferW :: TyEnv -> Expr -> Maybe (Int, Subst, MonoTy)
inferW env expr = do
  ((subst, ty), i) <- runStateT (inferW' env expr) 0
  return (i, subst, ty)

inferW' :: TyEnv -> Expr -> StateT Int Maybe (Subst, MonoTy)
-- リテラル: その型を返す
inferW' env (ELit prim) = do
  return (empty, TyPrim prim)
-- 変数参照: 変数をinstantiateしたものを返す(未定義の変数参照はNothing)
inferW' env (EVar name) = do
  ts <- lift $ Data.Map.lookup name env
  ty <- instantiate ts
  return (empty, ty)
-- 関数抽象: 
inferW' env (EAbs name bodyExpr) = do
  argTy <- newTyVar
  let innerEnv = Data.Map.insert name ([], argTy) env
  (s1, retTy) <- inferW' innerEnv bodyExpr
  return (s1, TyFun (substMonoTy s1 argTy) retTy)
-- 関数適用: 
inferW' env (EApp funExpr argExpr) = do
  (s1, t1) <- inferW' env funExpr
  (s2, t2) <- inferW' (substTyEnv s1 env) argExpr
  bodyTy <- newTyVar
  s3 <- lift $ unify [((substMonoTy s2 t1), TyFun t2 bodyTy)]
  return (unions [s3, s2, s1], substMonoTy s3 bodyTy)
-- let式: 
inferW' env (ELet name varExpr bodyExpr) = do
  (s1, t1) <- inferW' env varExpr
  let tyRo = typeCls t1 (substTyEnv s1 env)
  let newEnv = Data.Map.insert name tyRo (substTyEnv s1 env)
  (s2, t2) <- inferW' newEnv bodyExpr
  return (Data.Map.union s1 s2, t2)

-- Main

--ts = [
--  (TyVar 1, TyVar 2),
--  (TyVar 2, TyPrim PBool)
--  ]
--main = print $ unify (ts, [])
--

main = hspec $ do
  describe "hi" $ do
    it "1" $ do
      1 `shouldBe` 1

--  describe "ftv" $ do
--    it "primitive" $ do
--      ftv (TyPrim $ PBool True) `shouldBe` []
--
--    it "var" $ do
--      ftv (TyVar 3) `shouldBe` [3]
--
--    it "fun" $ do
--      ftv (TyFun (TyVar 3) (TyPrim $ PInt 99)) `shouldBe` [3]
  
--  describe "infer" $ do
--    it "primitive" $ do
--      infer 0 (ELit $ PInt 99)
--      `shouldBe`
--      Just (0, empty, (TyPrim $ PInt 99))
--
--    it "varref" $ do
--      infer 0 (EVar "x")
--      `shouldBe`
--      Just (1, fromList [("x", TyVar 0)], (TyVar 0))
--
--    it "abs" $ do
--      infer 0 (EAbs "x" (EVar "x"))
--      `shouldBe`
--      Just (1, empty, (TyFun (TyVar 0) (TyVar 0)))

  describe "inferW" $ do
    it "primitive" $ do
      inferW empty (ELit $ PInt 99)
      `shouldBe`
      Just (0, empty, (TyPrim $ PInt 99))

--    it "varref" $ do
--      inferW empty (EVar "x")
--      `shouldBe`
--      Just (1, fromList [(0, TyVar 0)], (TyVar 0))

    it "abs" $ do
      inferW empty (EAbs "x" (ELit $ PInt 99))
      `shouldBe`
      Just (1, empty, (TyFun (TyVar 0) (TyPrim $ PInt 99)))
