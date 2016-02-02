ifdef DEBUG
OCAMLC = ocamlc.opt -g
SUF = .cmo
else 
ifdef PROF
OCAMLC = ocamlopt.opt -p
SUF = .cmx
else 
OCAMLC = ocamlopt.opt
SUF = .cmx
endif
endif
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc

MODULES = flags     \
	  config    \
	  util      \
	  monad     \
          printer   \
	  pos       \
	  var       \
	  unique    \
	  trie      \
	  varmap    \
	  varset    \
	  types     \
	  fixity    \
	  nstbl     \
	  absyn     \
	  lineno    \
	  lexer     \
	  parser    \
	  perm      \
	  internal  \
	  isym      \
	  termgraph \
	  tcenv     \
	  translate \
	  index     \
	  subst     \
	  eval      \
	  explain   \
	  unify     \
	  negelim   \
          tc        \
	  runtime   \
	  solve     \
	  boundsolve     \
	  check
INTERFACES = flags  \
	  util   \
	  monad     \
	  printer   \
	  pos	    \
	  var       \
	  unique    \
	  trie      \
	  varmap    \
	  varset    \
	  types     \
	  fixity    \
	  nstbl     \
	  absyn     \
	  lineno    \
	  parser    \
	  perm      \
	  internal  \
	  isym      \
	  termgraph \
	  tcenv     \
	  translate \
	  index     \
	  subst     \
	  eval      \
	  explain   \
	  unify     \
	  negelim   \
	  tc        \
	  runtime   \
	  solve     \
	  boundsolve     \
          check

SRCS = $(addsuffix .ml, $(MODULES))
OBJS = $(addsuffix $(SUF), $(MODULES))
ISRCS = $(addsuffix .mli, $(INTERFACES))
IOBJS = $(addsuffix .cmi, $(INTERFACES))
GEN = parser.ml parser.mli lexer.ml parser.output



all : $(IOBJS) $(OBJS) aprolog

include .depend

aprolog: $(IOBJS) $(OBJS) main$(SUF)
	$(OCAMLC) $(OBJS) main$(SUF) -o $@

%.cmi : %.mli
	$(OCAMLC) -c $< -o $@

%$(SUF) : %.ml
	$(OCAMLC) -c $< -o $@

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml %.mli: %.mly
	$(OCAMLYACC) $<

%.output : %.mly
	$(OCAMLYACC) -v $<


depend :  parser.ml parser.mli lexer.ml
	$(OCAMLDEP) $(ISRCS) $(SRCS) parser.ml parser.mli lexer.ml main.ml > .depend

clean : 
	rm -rf *.dump *.o *.cmi *.cmo *.cmx *~ $(GEN) aprolog

distclean :  clean
	rm .depend	

