.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset11

rocq:
	$(ROCQ) Pset11Sig.v
	$(ROCQ) Pset11.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos