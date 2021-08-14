{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE InstanceSigs #-}

module OniAdaptor where

import Smedlmon

import Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Morph
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer
import Data.Functor.Identity

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.StablePtr
import Foreign.Marshal.Utils
import Foreign.Storable

deriving instance Show Typ
deriving instance Show EventKind
deriving instance Show Event_definition
deriving instance Show RaisedEvent





newConf :: StateT CRep Identity [RaisedEvent]
newConf = StateT $ \s -> return ([], mon_oni_new)

process :: RaisedEvent -> StateT CRep Identity [RaisedEvent]
process re = StateT $ \s -> return ((Prelude.snd (parseCC_processEvent s re)), (Prelude.fst (parseCC_processEvent s re)))



processE e = case  e of
       Just re ->  do                     
                     process re                    
       Nothing -> newConf



ihandleEvent :: CRep -> Maybe RaisedEvent ->  ([RaisedEvent], CRep)
ihandleEvent rep re = runState (do
                                    processE re
                                )
                       rep


foreign export ccall cInitialRep :: IO (Ptr ())


opaque :: a -> IO (Ptr ())
opaque = fmap castStablePtrToPtr . newStablePtr

inspect :: Ptr () -> IO a
inspect = deRefStablePtr . castPtrToStablePtr

inspectAndFree :: Ptr () -> IO a
inspectAndFree p = inspect p `finally` freeStablePtr (castPtrToStablePtr p)

cInitialRep :: IO (Ptr ())
cInitialRep =
               do                 
                 opaque mon_oni_new

mkCInt :: Int -> CInt
mkCInt n = fromIntegral n

foreign export ccall chandleImported :: CString -> Ptr () -> IO (Ptr ())

chandleImported :: CString -> Ptr () -> IO (Ptr ())
chandleImported str st = do
                         str' <- peekCString str                         
                         st' <- inspectAndFree st
                         let a = (createRaised parseCC str' Imported [] [])
                         
                         let (lst,st'') = (ihandleEvent st' a)
                         mapM_ putStrLn (Prelude.map show lst)

                         opaque st''


                      