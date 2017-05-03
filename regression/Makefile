DIRS = spurious-check-complete spurious-check-abstract spurious-check-concrete kiki-modular termination kiki preconditions interprocedural invariants

test:
	$(foreach var,$(DIRS), make -C $(var) test;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)
