all:
	export TIMED
	@+$(MAKE) -C theories-FOL all

force Makefile: ;

%: force
	@+$(MAKE) -C theories-FOL $@

.PHONY: all force
