include module.mk

all: ; 
FORCE: ;

%.vo: FORCE 
	make -C .. certia/$@

testmk:
	make -f module.mk


clean:
	rm -f *.vo
	rm -f *.html