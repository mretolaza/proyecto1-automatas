const DOTSCRIPTHEADER = 'digraph finite_state_machine {\n  rankdir = LR;\n';
const DOTSCRIPTEND = '}\n';

module.exports.toDotScript = function (fsm) {
  const states = [];
  let transitionDotScript = '  node [shape = circle];\n';
  for (const fromId in fsm.transitions) {
    for (const transition in fsm.transitions[fromId]) {
      let toId;
      let label;

      if (fsm.type === 'DirectDFA') {
        toId = fsm.transitions[fromId][transition];
        label = transition;
      } else {
        toId = transition;
        label = fsm.transitions[fromId][transition];
      }

      transitionDotScript += `  ${[fromId]}->${toId} [label="${label}"];\n`;

      if (states.findIndex((state) => state === fromId) === -1) {
        states.push(fromId);
      }
      if (states.findIndex((state) => state === toId) === -1) {
        states.push(toId);
      }
    }
  }
  let initialStatesDotScript = '';
  let initialStatesStartDotScript = '  node [shape = plaintext];\n';
  let acceptStatesDotScript = '';

  states.forEach((state) => {
    if (fsm.acceptStates.indexOf(state) !== -1) {
      acceptStatesDotScript += `  node [shape = doublecircle]; ${state};\n`;
    }
    if (fsm.initialState === state) {
      initialStatesStartDotScript += `  "" -> ${state} [label = "start"];\n`;
      // accept is higher priority than initial state.
      if (fsm.acceptStates.indexOf(state) === -1) { initialStatesDotScript += `  node [shape = circle]; ${state};\n`; }
    }
  });
  return DOTSCRIPTHEADER + initialStatesDotScript + acceptStatesDotScript
      + initialStatesStartDotScript + transitionDotScript + DOTSCRIPTEND;
};
