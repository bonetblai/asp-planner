SUBDIRS = relational functional

all:
	@echo "**Making all in `pwd`"
	for i in $(SUBDIRS); do \
	  (cd $$i; make all) ; \
	done

clean:
	@echo "**Making clean in `pwd`"
	for i in $(SUBDIRS); do \
	  (cd $$i; make clean) ; \
	done

dist:
	@echo "**Making dist in `pwd`"
	for i in $(SUBDIRS); do \
	  (cd $$i; make dist) ; \
	done
