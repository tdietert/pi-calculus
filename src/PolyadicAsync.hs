{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PolyadicAsync where

import Protolude hiding (TypeError)
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Sequence hiding (zip)
import Unbound.Generics.LocallyNameless

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

type PName = Name Proc

type Bindings = Bind [PName]

data Proc
  = PNil
  | PName { pName :: PName }
  | PPar Proc Proc
  | POutput Proc [Proc]
  | PInput Proc (Bindings Proc)
  | PReplInput Proc (Bindings Proc)
  | PRestrict (Bind (PName,TProc) Proc)
  deriving (Show, Generic)

data TVar = TV (Name TProc)
  deriving (Show, Generic)

-- | The type of pi-calculus values
data TProc
  = TChan [TProc]
  | TProc
  deriving (Show, Eq, Generic)

instance Alpha TProc
instance Alpha Proc

instance Subst Proc TProc
instance Subst Proc Proc where
  isvar p =
    case p of
      PName nm -> Just (SubstName nm)
      _ -> Nothing

nil :: Proc
nil = PNil

var :: [Char] -> Proc
var x = PName (s2n x)

par :: Proc -> Proc -> Proc
par p q = PPar p q

output :: [Char] -> [[Char]] -> Proc
output x ys = POutput (var x) (map var ys)

input :: [Char] -> [[Char]] -> Proc -> Proc
input x ys p = PInput (var x) (bind (map s2n ys) p)

replinput :: [Char] -> [[Char]] -> Proc -> Proc
replinput x ys p = PReplInput (var x) (bind (map s2n ys) p)

res :: [Char] -> TProc -> Proc -> Proc
res x t p = PRestrict (bind (s2n x, t) p)

chan :: [TProc] -> TProc
chan = TChan

--------------------------------------------------------------------------------
-- Typechecking
--------------------------------------------------------------------------------

type TypeEnv = Map PName TProc

data TypeError
  = TypeError Proc TProc TProc
  | InvalidChanType Proc TProc
  | UnboundVariable (Name Proc)
  deriving (Show)

type TypecheckM = FreshMT (ExceptT TypeError (Reader TypeEnv))

runTypecheckM :: TypecheckM a -> Either TypeError a
runTypecheckM = flip runReader mempty . runExceptT . runFreshMT

lookupTypeEnv :: PName -> TypecheckM (Maybe TProc)
lookupTypeEnv pnm = do
  env <- ask
  pure (Map.lookup pnm env)

extendTypeEnv :: [(PName,TProc)] -> TypecheckM a -> TypecheckM a
extendTypeEnv xts = local (Map.union $ Map.fromList xts)

typecheck :: Proc -> TypecheckM TProc
typecheck p =
  case p of
    PNil -> pure TProc
    PName x -> do
      mType <- lookupTypeEnv x
      case mType of
        Nothing -> throwError (UnboundVariable x)
        Just t -> pure t
    PPar p q -> do
      typecheck p
      typecheck q
      pure TProc
    POutput x ys -> do
      xType <- typecheck x
      ysTypes <- mapM typecheck ys
      if xType == TChan ysTypes
        then pure TProc
        else throwError (TypeError x xType (TChan ysTypes))
    PInput x bys -> do
      xType <- typecheck x
      case xType of
        TProc -> throwError (InvalidChanType x xType)
        TChan ts -> do
          (ys, p) <- unbind bys
          extendTypeEnv (zip ys ts) (typecheck p)
    PReplInput x bys -> do
      xType <- typecheck x
      case xType of
        TProc -> throwError (InvalidChanType x xType)
        TChan ts -> do
          (ys, p) <- unbind bys
          extendTypeEnv (zip ys ts) (typecheck p)
    PRestrict bx -> do
      ((x,t),p) <- unbind bx
      case t of
        TProc -> throwError (InvalidChanType (PName x) t)
        TChan _ -> extendTypeEnv [(x,t)] (typecheck p)

--------------------------------------------------------------------------------
-- Evaluation by Abstract Machine
--------------------------------------------------------------------------------

data ChanQueueElem
  = Reader (Bindings Proc)
  | Writer [Proc]
  | ReplReader (Bindings Proc)
  deriving (Show)

type ChanQueue = Seq ChanQueueElem
type Heap = Map PName ChanQueue
type RunQueue = Seq Proc

data MachineState = MachineState
  { evalHeap :: Heap
  , evalRunQueue :: RunQueue
  } deriving (Show)

initMachineState :: Proc -> MachineState
initMachineState proc = MachineState
  { evalHeap = mempty
  , evalRunQueue = proc :<| Empty
  }

data EvalError
  = NonExistentChan PName
  | ChanQueueEmpty PName
  deriving (Show)

data ReductionRule
  = RuleNil
  | RulePrl
  | RuleRes
  | RuleInpW
  | RuleInpR
  | RuleOutW
  | RuleOutR
  | RuleOutRStar
  | RuleReplW
  | RuleReplR
  deriving (Show)

data ReductionStep =
  ReductionStep ReductionRule MachineState
  deriving (Show)

type EvalM a =
  FreshMT
    (StateT MachineState
      (WriterT [ReductionStep]
        (Except EvalError
        )
      )
    ) a

runEvalM :: MachineState -> EvalM () -> Either EvalError [ReductionStep]
runEvalM machineState =
  fmap snd . runExcept . runWriterT . flip evalStateT machineState . runFreshMT

runMachine :: Proc -> Either EvalError [ReductionStep]
runMachine initProc =
    runEvalM (initMachineState initProc) machineLoop
  where
    machineLoop = do
      mProc <- dequeueRunQueue
      case mProc of
        -- If no processes in run queue, terminate.
        Nothing -> pure ()
        -- Otherwise, evaluate the process at the head of the run queue
        Just proc -> eval proc >> machineLoop

-- | Evaluate a process at the head of the run queue, returning the reduction
-- rule used to evaluate the given process expression.
eval :: Proc -> EvalM ()
eval proc = do
  rule <-
    case proc of
      -- [Rule Nil]
      PNil -> pure RuleNil
      PName pnm -> panic "Trying to eval a name..."
      -- [Rule Prl]
      PPar p q -> do
        pushRunQueue p
        enqueueRunQueue q
        pure RulePrl
      -- [Rule Res]
      PRestrict bxp -> do
        ((x,_),p) <- unbind bxp
        insertHeap x Empty
        pushRunQueue p
        pure RuleRes
      PInput (PName c) bxs -> do
        cq <- lookupHeap c
        case cq of
          -- [Rule Inp-W]
          Writer pas :<| ws -> do
            (xs, p) <- unbind bxs
            let as = map pName pas
                pxs = map PName xs
                p' = substs (zip as pxs) p
            insertHeap c ws
            pushRunQueue p'
            pure RuleInpW
          -- [Rule Inp-R]
          rs -> do
            insertHeap c (rs |> Reader bxs)
            pure RuleInpR
      POutput (PName c) pas -> do
        cq <- lookupHeap c
        case cq of
          -- [Rule Out-R]
          Reader bxs :<| rs -> do
            (xs, q) <- unbind bxs
            insertHeap c rs
            let as = map pName pas
                pxs = map PName xs
                q' = substs (zip as pxs) q
            enqueueRunQueue q'
            pure RuleOutR
          -- [Rule Out-R*]
          rr@(ReplReader bxs) :<| rs -> do
            (xs, q) <- unbind bxs
            insertHeap c (rs |> rr)
            let as = map pName pas
                pxs = map PName xs
                q' = substs (zip as pxs) q
            enqueueRunQueue q'
            pure RuleOutRStar
          -- [Rule Out-W]
          ws -> do
            insertHeap c (ws |> Writer pas)
            pure RuleOutW
      PReplInput (PName c) bxs -> do
        cq <- lookupHeap c
        case cq of
          -- [Rule Repl-W]
          Writer pas :<| ws -> do
            (xs, p) <- unbind bxs
            insertHeap c ws
            pushRunQueue proc
            let as = map pName pas
                pxs = map PName xs
                p' = substs (zip as pxs) p
            enqueueRunQueue p'
            pure RuleReplW
          -- [Rule Repl-R]
          rs -> do
            insertHeap c (rs |> ReplReader bxs)
            pure RuleReplR

  -- Emit the reduction rule and resulting machine state
  machineState <- get
  tell [ReductionStep rule machineState]

-- Helpers
--------------------------------------------------------------------------------

pushRunQueue :: Proc -> EvalM ()
pushRunQueue p =
  modify $ \evalState ->
    let currRunQueue = evalRunQueue evalState
    in evalState { evalRunQueue = p <| currRunQueue }

enqueueRunQueue :: Proc -> EvalM ()
enqueueRunQueue p =
  modify $ \evalState ->
    let currRunQueue = evalRunQueue evalState
    in evalState { evalRunQueue = currRunQueue |> p }

dequeueRunQueue :: EvalM (Maybe Proc)
dequeueRunQueue = do
  currRunQueue <- gets evalRunQueue
  case currRunQueue of
    Empty -> pure Nothing
    p :<| rest -> do
      modify $ \evalState ->
        evalState { evalRunQueue = rest }
      pure (Just p)

insertHeap :: PName -> ChanQueue -> EvalM ()
insertHeap pnm cq =
  modify $ \evalState ->
    evalState { evalHeap = Map.insert pnm cq (evalHeap evalState) }

-- | Looks up a channel queue for the given channel name
lookupHeap :: PName -> EvalM ChanQueue
lookupHeap pnm = do
  heap <- gets evalHeap
  case Map.lookup pnm heap of
    Nothing -> throwError (NonExistentChan pnm)
    Just cq -> pure cq

-- | Returns the head of the channel queue for a given channel name in the heap
peekChanQueue :: PName -> EvalM ChanQueueElem
peekChanQueue pnm = do
  cq <- lookupHeap pnm
  case cq of
    Empty -> throwError (ChanQueueEmpty pnm)
    cqe :<| cqes -> pure cqe

-- | Returns the head of the channel queue of the given channel name in the
-- heap, removing it from the queue.
dequeueChanQueue :: PName -> EvalM ChanQueueElem
dequeueChanQueue pnm = do
  cq <- lookupHeap pnm
  case cq of
    Empty -> throwError (ChanQueueEmpty pnm)
    cqe :<| cqes -> do
      insertHeap pnm cqes
      pure cqe

-- | Places a channel queue element at the end of the channel queue for the
-- given process name in the heap.
enqueueChanQueue :: PName -> ChanQueueElem -> EvalM ()
enqueueChanQueue pnm cqe = do
  cq <- lookupHeap pnm
  insertHeap pnm (cq |> cqe)

--------------------------------------------------------------------------------
-- Running a Process
--------------------------------------------------------------------------------

data ProcError
  = ProcTypeError TypeError
  | ProcEvalError EvalError
  deriving (Show)

process :: Proc -> Either ProcError [ReductionStep]
process proc = do
  first ProcTypeError (runTypecheckM (typecheck proc))
  first ProcEvalError (runMachine proc)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

runExampleReduction :: IO ()
runExampleReduction = do
  case process exampleReduction of
    Left err -> panic (show err)
    Right reds -> mapM_ print reds

exampleReduction :: Proc
exampleReduction =
  res "x" (chan [])
    (par
      (output "x" [])
      (replinput "x" [] nil)
    )

asyncToSync :: Proc -> Proc -> Proc
asyncToSync p q =
  res "k" (chan [])
    $ res "a" (chan [])
      $ res "c" (chan [chan [], chan []])
        $ output "c" ["a", "k"]
            `par`
          input "k" [] p
            `par`
          input "c" ["x", "k"] (output "k" [] `par` q)
