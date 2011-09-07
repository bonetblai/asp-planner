SUBDIRS = src bin lib include

all:
	@echo "**Making all in `pwd`"
	for i in $(SUBDIRS); do \
	  (cd $$i; make all) ; \
	done

clean:
	@echo "**Making clean in `pwd`"
	for i in $(SUBDIRS) asp-paper; do \
	  (cd $$i; make clean) ; \
	done

install:
	@echo "**Making install in `pwd`"
	for i in $(SUBDIRS); do \
	  (cd $$i; make install) ; \
	done

dist:
	@echo "**Making dist in `pwd`"
	for i in $(SUBDIRS) asp-paper; do \
	  (cd $$i; make dist) ; \
	done
