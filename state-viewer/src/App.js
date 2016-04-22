import React, { Component } from 'react';
import JSONTree from 'react-json-tree';

// TODO(joel): allow loading from any location, not just this path that we
// happen to dump to at the moment.
import data from 'json!../../statedump.json';

function ControlStack({controlStack}) {
  return <JSONTree data={controlStack} expandAll />;
}

function EnvStack({envStack}) {
  const vals = envStack.map(([{refPointer}]) => refPointer);
  return (
    <JSONTree data={vals} expandAll />
  );
}

function Heap({heap}) {
  // flatten this a bit to make it easier to read
  const vals = heap.theHeap.map(([{refPointer}, {tag, contents}]) => ({
    pointer: refPointer,
    tag,
    contents,
  }));

  return (
    <JSONTree data={vals} expandAll />
  );
}

export default class App extends Component {
  render() {
    const {heap, controlStack, envStack} = data;
    return (
      <div>
        <div style={{fontFamily: 'monospace', fontSize: 15}}>
          <h2>Heap</h2>
          <Heap heap={data.heap} />
        </div>
        <div style={{fontFamily: 'monospace', fontSize: 15}}>
          <h2>Control Stack</h2>
          <ControlStack controlStack={controlStack} />
        </div>
        <div style={{fontFamily: 'monospace', fontSize: 15}}>
          <h2>Env Stack</h2>
          <EnvStack envStack={envStack} />
        </div>
      </div>
    );
  }
}
