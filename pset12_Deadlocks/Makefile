.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset12

rocq:
	$(ROCQ) Pset12Sig.v
	$(ROCQ) Pset12.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos