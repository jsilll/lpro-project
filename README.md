# Project Setup 

Generating the Makefile:
```
coq_makefile -f _CoqProject -o Makefile
```
# Group Identification
- Lourenço Abecasis, [Email](lourenco.abecasis@tecnico.ulisboa.pt), 93931
- Francisco Abrunhosa, [Email](francisco.abrunhosa@tecnico.ulisboa.pt), 95580
- João Silveira, [Email](joao.freixial.silveira@tecnico.ulisboa.pt), 95597

# Implemented Features
### Task 1 (Imp.v)
- [x] Extend com - FA, JS
- [x] New notation - FA, JS
- [x] Examples p1 and p2 - FA, JS

### Task 2 (Interpreter.v)
- [x] Implementation of step-indexed evaluator - LA, JS
- [x] Proof of equivalence1 - LA
- [x] Proof of inequivalence1 - LA, FA, JS
- [x] Proof of p1_equivalent_p2 - LA, FA, JS

### Task 3 (RelationalEvaluation.v)
- [x] Definition of ceval - JS, FA
- [x] Proof of break_ignore - JS
- [x] Proof of while_continue - JS
- [x] Proof of while_stops_on_break - FA
- [x] Proof of seq_continue - FA
- [x] Proof of seq_stops_on_break - LA
- [x] Proof of while_break_true - LA

### Task 3 (AdditionalProperties.v)
- [x] Proof of ceval_step_more - JS
- [x] Proof of ceval_step__ceval - FA
- [x] Proof of ceval__ceval_step - LA
- [x] Informal proof of ceval_deterministic' - JS