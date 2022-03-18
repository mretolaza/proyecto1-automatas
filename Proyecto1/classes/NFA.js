/* eslint-disable global-require */
const { sortBy } = require('lodash');
const { performance } = require('universal-perf-hooks');

const FSM = require('./FSM');
const { TOKEN_TYPE } = require('./Lexer');

const _EPSILONClosure = (nfaStates, nfaGraph) => {
  let closure = [];
  const stack = [];
  for (let i = 0; i < nfaStates.length; ++i) {
    stack.push(nfaStates[i]);
    closure.push(nfaStates[i]);
  }
  while (stack.length) {
    const stateId = stack.shift();
    for (let i = 0; i < nfaGraph[stateId].length; ++i) {
      const nextId = nfaGraph[stateId][i][1];
      const label = nfaGraph[stateId][i][0];
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

const _move = (dfaState, letter, id2States, nfaGraph) => {
  const stateArray = id2States[dfaState.id];
  let result = [];
  for (let i = 0; i < stateArray.length; ++i) {
    const id = stateArray[i];
    for (let k = 0; k < nfaGraph[id].length; ++k) {
      const label = nfaGraph[id][k][0];
      if (label === letter) {
        result.push(nfaGraph[id][k][1]);
      }
    }
  }
  result = sortBy(result);
  return result;
};

const constructGraph = function (startState) {
  const nfaGraph = {};
  const queue = [];
  queue.push(startState);
  const vis = {};
  while (queue.length) {
    const state = queue.shift();
    nfaGraph[state.id] = [];
    for (let i = 0; i < (state.nextStates).length; ++i) {
      const nextId = state.nextStates[i][1].id;
      const label = state.nextStates[i][0].text;
      // const nextState = state.nextStates[i][1];
      nfaGraph[state.id].push([label, nextId]);
      if (nextId in vis) {
        continue;
      }
      vis[nextId] = 1;
      queue.push(state.nextStates[i][1]);
    }
  }

  return nfaGraph;
};

class NFA {
  constructor(startState, endState) {
    this.startState = startState;
    this.endState = endState;
  }

  toDFA() {
    const beginTime = performance.now();

    const nfaGraph = constructGraph(this.startState);
    const alphabetTable = {};
    for (const id in nfaGraph) {
      for (let j = 0; j < nfaGraph[id].length; ++j) {
        const label = nfaGraph[id][j][0];
        if (!alphabetTable.hasOwnProperty(label)
          && label !== TOKEN_TYPE.EPSILON) {
          alphabetTable[label] = 1;
        }
      }
    }

    const dStates = [];
    const states2Id = {}; // [1, 2, 3] => id
    const id2States = {}; // id => [1, 2, 3]
    let id = 0;
    const closure = _EPSILONClosure([this.startState.id], nfaGraph);
    states2Id[JSON.stringify(closure)] = id;
    id2States[id] = closure;
    dStates.push({ id: id++, nextStates: {}, vis: false });

    dStates[dStates.length - 1].accept = closure.indexOf(this.endState.id) !== -1;
    dStates[dStates.length - 1].initial = closure.indexOf(this.startState.id) !== -1;
    let unvisCnt = 1;
    while (unvisCnt) {
      const [unvisState] = dStates.filter((state) => !state.vis);
      unvisState.vis = true;
      --unvisCnt;
      for (const letter in alphabetTable) {
        if (letter === TOKEN_TYPE.EPSILON) { continue; }

        const nextStates = _EPSILONClosure(
          _move(unvisState, letter, id2States, nfaGraph), nfaGraph,
        );

        if (!nextStates.length) { continue; }
        const nextStatesString = JSON.stringify(nextStates);
        if (!states2Id.hasOwnProperty(nextStatesString)) {
          states2Id[nextStatesString] = id;
          id2States[id] = nextStates;
          dStates.push({
            id: id++,
            nextStates: {},
            vis: false,
            accept: nextStates.indexOf(this.endState.id) !== -1,
            initial: nextStates.indexOf(this.startState.id) !== -1,
          });
          ++unvisCnt;
        }

        unvisState.nextStates[letter] = nextStates;
      }
    }

    const dfa = new FSM();
    dfa.type = 'DFA';
    dfa.numOfStates = id;
    const numberToLetter = (number) => 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ'[number];

    for (let i = 0; i < dStates.length; ++i) {
      if (dStates[i].initial) { dfa.initialState = numberToLetter(dStates[i].id); }
      if (dStates[i].accept) { dfa.acceptStates.push(numberToLetter(dStates[i].id)); }

      for (const letter in alphabetTable) {
        if (!dStates[i].nextStates[letter]) { continue; }
        const arrayId = [];
        for (let j = 0; j < dStates[i].nextStates[letter].length; ++j) {
          arrayId.push(dStates[i].nextStates[letter][j]);
        }

        if (arrayId.length) {
          if (!dfa.transitions[numberToLetter(dStates[i].id)]) {
            dfa.transitions[numberToLetter(dStates[i].id)] = {};
          }

          dfa.transitions[
            numberToLetter(dStates[i].id)
          ][
            numberToLetter(states2Id[JSON.stringify(arrayId)])
          ] = letter;
        }
      }
    }

    const executionTime = performance.now() - beginTime;
    return {
      executionTime,
      dfa,
    };
  }
}

module.exports = NFA;
