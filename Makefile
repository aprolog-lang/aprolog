INSTALL = $(HOME)/local/aprolog


all : bin/aprolog

src/config.ml : configure

configure : 
	./configure.sh $(INSTALL)

bin/aprolog : aprolog
	cp src/aprolog bin

aprolog : src/config.ml
	make -C src aprolog

examples : bin/aprolog
	make -C examples all


clean : 
	rm -rf *~
	make -C src clean
	make -C examples clean

spotless : clean
	rm -f src/config.ml
	rm -f bin/aprolog

%.tar.gz : %/
	tar czf $@ $<

%.zip : %/
	zip -R $@ $<

install : bin/aprolog
	./install.sh . $(INSTALL)

uninstall : 
	./uninstall.sh $(INSTALL)
