all: oni_adaptor.o /
	ghc --make -no-hs-main -optc-O test_9228.c regenc.c regparse.c st.c ascii.c regcomp.c regerror.c iso8859_1.c gb18030.c oni_adaptor -o test

oni_adaptor.o	: oni_adaptor.hs smedlmon.o
	ghc -c -O oni_adaptor.hs

smedlmon.o: smedlmon.hs
	ghc smedlmon.hs

clean: 
	rm -f *.hi *.o test
