const { RegParser } = require('./classes');
const DirectDFA = require('./classes/DirectDFA');

const regexpStr = '(b|b)*abb(a|b)*';

const parser = new RegParser(regexpStr);
const {
  nfa,
  fsm,
  executionTime: nfaExecutionTime,
} = parser.parseToNFA();
console.log('NFA TIME', nfaExecutionTime);

const {
  dfa,
  executionTime: dfaExecutionTime,
} = nfa.toDFA();
console.log('DFA TIME', dfaExecutionTime);

const directDFA = new DirectDFA(regexpStr);

const {
  fsm,
  executionTime: directExecutionTime,
} = directDFA.parseToDFA();
console.log('Direct DFA TIME', directExecutionTime);
