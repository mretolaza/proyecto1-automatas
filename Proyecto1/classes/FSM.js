const { sortBy } = require('lodash');

const DotConverter = require('./DotConverter');
const { Lexer } = require('./Lexer');
const {
  TOKEN_TYPE,
} = require('../constants');

const _states = (transitions, state) => {
  if (transitions[state] !== undefined) {
    return Object.keys(transitions[state])
      .map((key) => ({
        id: key,
        label: transitions[state][key],
      }));
  }
  return [];
};

const _move = (fromStates, letter, transitions) => {
  let toStates = [];
  while (fromStates.length) {
    const fromState = fromStates.shift();
    const stack = _states(transitions, fromState);

    for (let i = 0; i < stack.length; i++) {
      const {
        id: nextId, label,
      } = stack[i];
      if (label === letter) {
        toStates.push(nextId);
      }
    }
  }

  toStates = sortBy(toStates);
  return toStates;
};

const _EPSILONClosure = (fromStates, transitions) => {
  let closure = [];
  const stack = [];
  for (let i = 0; i < fromStates.length; i++) {
    closure.push(fromStates[i]);
    stack.push(fromStates[i]);
  }

  while (stack.length) {
    const stateId = stack.shift();
    const states = _states(transitions, stateId);
    for (let i = 0; i < states.length; i++) {
      const {
        id: nextId, label,
      } = states[i];

      if (label === TOKEN_TYPE.EPSILON
        && closure.indexOf(nextId) === -1) {
        closure.push(nextId);
        stack.push(nextId);
      }
    }
  }
  closure = sortBy(closure);
  return closure;
};

class FSM {
  constructor() {
    this.initialState = '';
    this.acceptStates = [];
    this.numOfStates = 0;
    this.type = '';
    this.transitions = {};
  }

  toDotScript() {
    return DotConverter.toDotScript(this);
  }

  validateWord(word) {
    const lexer = new Lexer(word);

    const stateStack = [[this.initialState]];
    let validWord = false;

    let letter = lexer.nextToken().text;

    while (stateStack.length) {
      const actualStates = stateStack.shift();

      const epsilonStates = _EPSILONClosure(actualStates, this.transitions);
      const statesToMove = _move(
        epsilonStates,
        letter !== TOKEN_TYPE.END ? letter : TOKEN_TYPE.EPSILON,
        this.transitions,
      );

      if (letter !== TOKEN_TYPE.END) {
        letter = lexer.nextToken().text;
      }

      for (let i = 0; i < statesToMove.length; i++) {
        if (this.acceptStates.includes(statesToMove[i])
          && letter === TOKEN_TYPE.END) {
          validWord = true;
        }
      }

      if (statesToMove.length > 0) {
        stateStack.push(statesToMove);
      }
    }

    return validWord;
  }
}

module.exports = FSM;
