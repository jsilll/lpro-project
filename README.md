# Group Identification
- [Lourenço Abecasis](lourenco.abecasis@tecnico.ulisboa.pt), 93931
- [Francisco Abrunhosa](francisco.abrunhosa@tecnico.ulisboa.pt), 95580
- [João Silveira](joao.freixial.silveira@tecnico.ulisboa.pt), 95597

# Implemented Features
### Task 1 (Imp.v)
- Extend com - João Silveira and Francisco Abrunhosa
- New notation - João Silveira and Francisco Abrunhosa
- Examples p1 and p2 - João Silveira and Francisco Abrunhosa

### Task 2 (Interpreter.v)
- Implementation of step-indexed evaluator - João Silveira and Lourenço Abecasis
- Proof of equivalence1 - Lourenço Abecasis
- Proof of inequivalence1 - Everyone (DUVIDA)
- Proof of p1_equivalent_p2 - Everyone (DUVIDA)

### Task 3 (RelationalEvaluation.v)
- Definition of ceval - João Silveira and Francisco Abrunhosa
- Proof of break_ignore - João Silveira
- Proof of while_continue - João Silveira
- Proof of while_stops_on_break - Francisco Abrunhosa
- Proof of seq_continue - Francisco Abrunhosa
- Proof of seq_stops_on_break - Lourenço Abecasis
- Proof of while_break_true - Lourenço Abecasis

### Task 3 (AdditionalProperties.v)
- Proof of ceval_step_more - João Silveira
- Proof of ceval_step__ceval - Francisco Abrunhosa
- Proof of ceval__ceval_step - Lourenço Abecasis
- Informal proof of ceval_deterministic' - João Silveira

# Extras
TODO: Identify and describe additional work that you have done,
      so that it can be considered for extra credits.

# Generating the Makefile
```
coq_makefile -f _CoqProject -o Makefile
```