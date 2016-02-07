ifdef DEBUG
OCAMLC = ocamlc.opt -g
SUF = .cmo
EXT_SUF = .cma
else 
ifdef PROF
OCAMLC = ocamlopt.opt -p
SUF = .cmx
EXT_SUF = .cmxa
else 
OCAMLC = ocamlopt.opt
SUF = .cmx
EXT_SUF = .cmxa
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
          tc        \
	  runtime   \
	  solve     \
	  boundsolve \
	  string_set \
	  string_map \
	  dependency_graph \
	  negelim   \
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
	  tc        \
	  runtime   \
	  solve     \
	  boundsolve \
	  string_set \
	  string_map \
	  dependency_graph \
	  negelim   \
          check

EXT_MODULES = str

SRCS = $(addsuffix .ml, $(MODULES))
OBJS =  $(addsuffix $(SUF), $(MODULES))
ISRCS = $(addsuffix .mli, $(INTERFACES))
IOBJS = $(addsuffix .cmi, $(INTERFACES))
GEN = parser.ml parser.mli lexer.ml parser.output
EXT_LIBS = $(addsuffix $(EXT_SUF), $(EXT_MODULES))

all : $(IOBJS) $(OBJS) aprolog

include .depend

aprolog: $(IOBJS) $(OBJS) main$(SUF)
	$(OCAMLC) $(EXT_LIBS) $(OBJS) main$(SUF) -o $@

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

