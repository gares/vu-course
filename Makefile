COQC=coqc
VFILES=$(wildcard *.v)
HTML=$(VFILES:%.v=%.html)

html: $(HTML)

run: jscoq.stamp html
	@echo
	@echo "Go to: http://localhost:8000/demo.html"
	@echo
	python3 -m http.server 8000 || python -m SimpleHTTPServer 8000

%.html: %.v header.html footer.html Makefile setup.stamp jscoq.stamp
	# if does not work, then html ok but no links
	-$(COQC) $< > /dev/null
	udoc/_build/install/default/bin/udoc --with-header header.html --with-footer footer.html -t $* $< -o $@

jscoq.stamp: jscoq.tgz
	tar -xzf jscoq.tgz
	touch $@

setup.stamp: 
	git submodule update --init --remote
	which dune
	cd udoc && make all
	touch setup.stamp


PWD=$(shell pwd)
OPAMROOT=$(PWD)/_opam
export OPAMROOT
# The default addon is mathcomp, but if you don't build jscoq first you
# don't have coq_makefile, so the addon cannot be built.
# Also, the last bit of make addons fails, but it is run again at make dist
build-jscoq:
	dpkg -l gcc-multilib || sudo apt-get install gcc-multilib
	which npm
	opam init -j 2 -y --compiler 4.07.1
	eval `opam env` && cd jscoq-src && \
		git submodule update --init --remote && \
		etc/toolchain-setup.sh && \
		make coq     && \
		make jscoq  ADDONS= && \
		make addons  ; \
		make jscoq   && \
		make dist
	mv jscoq-src/_build/dist/ jscoq-src/_build/jscoq
	cd jscoq-src/_build/ && tar -czf ../../jscoq.tgz jscoq

