.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset13

rocq:
	$(ROCQ) Pset13Sig.v
	$(ROCQ) Pset13Example.v
	$(ROCQ) Pset13.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos