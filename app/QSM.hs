module QSM where

import Control.Exception
import Data.Bifunctor (first)
import Data.Map
import Data.Set
import System.FilePath  ((</>))
import System.IO.Error
import Test.StateMachine
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified GHC.IO.Exception as GHC
import qualified System.Directory as IO
import qualified System.IO        as IO

data Dir  = Dir [String] deriving (Ord, Eq, Show)
data File = File {dir :: Dir, name :: String} deriving (Ord, Eq, Show)

data Mock = M {
    dirs  :: Set Dir
  , files :: Map File String
  , open  :: Map MHandle File
  , next  :: MHandle
  }

type MHandle = Int

emptyMock :: Mock
emptyMock = M (Set.singleton (Dir [])) Map.empty Map.empty 0

data Err = AlreadyExists | DoesNotExist | HandleClosed | Busy

type MockOp a = Mock -> (Either Err a, Mock)

mRead :: File -> MockOp String
mRead f m@(M _ fs hs _)
  | alreadyOpen               = (Left Busy         , m)
  | Just s <- Map.lookup f fs = (Right s           , m)
  | otherwise                 = (Left DoesNotExist , m)
  where
    alreadyOpen = f `List.elem` Map.elems hs

parent :: Dir -> Dir
parent (Dir fp) = Dir (init fp)

mMkDir :: Dir -> MockOp ()
mMkDir d m@(M ds fs hs n)
  | d        `Set.member`    ds = (Left AlreadyExists, m)
  | parent d `Set.notMember` ds = (Left DoesNotExist, m)
  | otherwise                   = (Right (), M (Set.insert d ds) fs hs n)

mOpen :: File -> MockOp MHandle
mOpen f m@(M ds fs hs n)
  | alreadyOpen   = (Left Busy, m)
  | not dirExists = (Left DoesNotExist, m)
  | fileExists    = (Right n, M ds fs hs' n')
  | otherwise     = (Right n, M ds (Map.insert f "" fs) hs' n')
  where
    hs' = Map.insert n f hs
    n'  = succ n

    fileExists  =     f `Map.member` fs
    dirExists   = dir f `Set.member` ds
    alreadyOpen = f `List.elem` Map.elems hs

mWrite :: MHandle -> String -> MockOp ()
mWrite h s m@(M ds fs hs n)
  | Just f <- Map.lookup h hs = (Right (), M ds (Map.adjust (++ s) f fs) hs n)
  | otherwise                 = (Left HandleClosed, m)

mClose :: MHandle -> MockOp ()
mClose h (M ds fs hs n) = (Right (), M ds fs (Map.delete h hs) n)

fromIOError :: IOError -> Maybe Err
fromIOError e =
    case ioeGetErrorType e of
      GHC.AlreadyExists    -> Just AlreadyExists
      GHC.NoSuchThing      -> Just DoesNotExist
      GHC.ResourceBusy     -> Just Busy
      GHC.IllegalOperation -> Just HandleClosed
      otherwise            -> Nothing

data Cmd h =
    MkDir Dir
  | Open File
  | Write h String
  | Close h
  | Read File

data Success h = Unit () | Handle h | String String

newtype Resp h = Resp (Either Err (Success h))

runMock :: Cmd MHandle -> Mock -> (Resp MHandle, Mock)
runMock (MkDir d)   = first (Resp . fmap Unit)   . mMkDir d
runMock (Open  f)   = first (Resp . fmap Handle) . mOpen  f
runMock (Write h s) = first (Resp . fmap Unit)   . mWrite h s
runMock (Close h)   = first (Resp . fmap Unit)   . mClose h
runMock (Read  f)   = first (Resp . fmap String) . mRead  f

dirFP :: FilePath -> Dir -> FilePath
dirFP root (Dir d) = List.foldl' (</>) root d

fileFP :: FilePath -> File -> FilePath
fileFP root (File d f) = dirFP root d </> f

runIO :: FilePath -> Cmd IO.Handle -> IO (Resp IO.Handle)
runIO root = catchErr . go
  where
    go :: Cmd IO.Handle -> IO (Success IO.Handle)
    go (MkDir d)   = Unit   <$> IO.createDirectory (dirFP root d)
    go (Open  f)   = Handle <$> IO.openFile (fileFP root f) IO.AppendMode
    go (Write h s) = Unit   <$> IO.hPutStr h s
    go (Close h)   = Unit   <$> IO.hClose  h
    go (Read  f)   = String <$> IO.readFile (fileFP root f)

catchErr :: IO (Success h) -> IO (Resp h)
catchErr act = catch (Resp . Right <$> act) handler
  where
    handler :: IOError -> IO (Resp h)
    handler e = maybe (throwIO e) (return . Resp . Left) (fromIOError e)
