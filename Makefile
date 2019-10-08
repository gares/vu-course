PWD=$(shell pwd)
OPAMROOT=$(PWD)/_opam
export OPAMROOT

# The default addon is mathcomp, but if you don't build jscoq first you
# don't have coq_makefile, so the addon cannot be built.
# Also, the last bit of make addons fails, but it is run again at make dist
build-jscoq:
	eval `opam env` && cd jscoq-src && \
		make coq     && \
		make jscoq  ADDONS= && \
		make addons  ; \
		make jscoq   && \
		make dist
	mv jscoq-src/_build/dist/ jscoq-src/_build/jscoq
	cd jscoq-src/_build/ && tar -czf ../../jscoq.tgz jscoq

run:
	chromium --allow-file-access-from-files --js-flags="--harmony-tailcalls" --js-flags="--stack-size=65536" jscoq/

setup: 
	dpkg -l gcc-multilib || sudo apt-get install gcc-multilib
	which npm
	opam init -j 2 -y --compiler 4.07.1
	git submodule update --init --remote
	cd jscoq-src && git submodule update --init --remote && \
		etc/toolchain-setup.sh
	cd udoc && make all

