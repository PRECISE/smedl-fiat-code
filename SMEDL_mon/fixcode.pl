#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified Prelude
import qualified HString
import qualified Data.Char
import qualified Data.List
import qualified Data.Ratio
import qualified GHC.Real
import qualified Data.Function
import qualified Data.Maybe
import Debug.Trace
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/'\\000'/0/g;

    s/\(ilist2_tl \(HString\.nsucc/(unsafeCoerce ilist2_tl (HString.nsucc/g;
    s/\(ilist_tl \(HString\.nsucc/(unsafeCoerce ilist_tl (HString.nsucc/g;

    s/    \(aST_rect/    (unsafeCoerce aST_rect/;

    s/Data\.Char\.chr \(Npos /Data.Char.chr (id /g;
    s/parse_nonterminal_subproof _ _ _ _ _ _ =/parse_nonterminal_subproof _ _ _ _ _ _ = Prelude.undefined/;

    print;
}
