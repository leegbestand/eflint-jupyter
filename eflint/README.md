# eFLINT

Haskell implementation of the eFLINT language, providing an interpreter for exploring normative behaviour, testing normative models and interacting with a normative model for runtime verification and simulation.

## Installation

Requires GHC, the glorius Glasgow Haskell Compiler, and Cabal, Haskell's old skool package manager. On unix:

```
apt-get install cabal-install ghc
cabal update
```

Then in your local copy of this directory:

```
cabal configure
cabal build
cabal install 
```

When using an older version of cabal (based on build version 1), use `cabal v1-configure` and `cabal v1-build` and `cabal v1-install` instead.

Upon successful installation:

* the executables `eflint-repl` and `eflint-server` are available
* the script `examples/run_tests.sh` should run successfully and produce no output.

## Run tests

Execute the script `run_tests.sh` to execute all the tests in folder `tests/`. 
This applies the executable `eflint-repl` (in `--test-mode`) to all the `.eflint` files in `tests/`. 

A test that fails is a test that has queries evaluating to false. All other output by the tool is suppressed.

Input to a test, determining the truth-values of instances of open-types, is provided in a file with the same name but with extension `.eflint.input`.

## Executable `eflint-repl`

Run eFLINT as a REPL.

`eflint-repl <FILE.eflint>` or `eflint-repl`

The scenario in `FILE` is ignored (although this may change in the future).
Once loaded, type `:help` to see the available commands.

## Executable `eflint-server`

### Usage

`eflint-server <FILE.eflint> <PORT> <OPTIONS*>`

with `<OPTIONS>` either:

* `--debug` (increases verbosity of the server)

### Protocol

The `eflint-server` listens to commands on the given `<PORT>`.

If a command is executed successfully this might result in the server updating its internal state.
If this is the case then the response will contain a field `newstate : <INTEGER>`.

---
#### Responses
Responses from the protocol can have one of the following forms.

**Status response**
```
{
    response                 : "success",
    old-state                : <INTEGER>,
    new-state                : <INTEGER>,

    source_contents          : <VALUE*>,
    target_contents          : <VALUE*>,
    created_facts            : <VALUE*>,
    terminated_facts         : <VALUE*>,

    violations               : <VIOLATION*>,
    output-events            : <EVENT*>
    errors                   : <ERROR*>
    query-results            : <BOOL*>

    new-duties               : <VALUE*>,
    new-enabled-transitions  : <VALUE*>,
    new-disabled-transitions : <VALUE*>,
    all-duties               : <VALUE*>,
    all-enabled-transitions  : <VALUE*>,
    all-disabled-transitions : <VALUE*>,
}
```
Where `<VIOLATION*>` is an array of elements of the form:
```
{
    violation : "trigger",
    value     : <VALUE>
}
{
    violation : "duty",
    value     : <VALUE>
}
{
    violation : "invariant",
    invariant : <STRING>
}
```
A `<VALUE>` is either an `<ATOM>` of the form
```
{
    tagged-type : <STRING>,
    fact-type   : <STRING>,
    value       : <STRING>|<INTEGER>,
    textual     : <STRING>
}
```

or a `<COMPOSITE>` of the form

```
{
    tagged-type : <STRING>,
    fact-type   : <STRING>,
    value       : <VALUE*>
    textual     : <STRING>
    
}
```
and `<VALUE*>` is an array of values.

**Facts response**
```
{
    values : <VALUE*>
}
```
**Path response**
```
{
    edges : <EDGE*>
}
```
Where `<EDGE*>` is an array of elements of the form:
```
{
    phrase                   : <STRING>,
    source_id                : <INTEGER>,
    target_id                : <INTEGER>,

    source_contents          : <VALUE*>,
    target_contents          : <VALUE*>,
    created_facts            : <VALUE*>,
    terminated_facts         : <VALUE*>,

    violations               : <VIOLATION*>,
    output-events            : <EVENT*>
    errors                   : <ERROR*>
    query-results            : <BOOL*>

    new-duties               : <VALUE*>,
    new-enabled-transitions  : <VALUE*>,
    new-disabled-transitions : <VALUE*>,
    all-duties               : <VALUE*>,
    all-enabled-transitions  : <VALUE*>,
    all-disabled-transitions : <VALUE*>,
}
```
**Head/Leaf nodes response**
```
{
    state_id             : <INTEGER>,
    state_contents       : <VALUE*>,
    duties               : <VALUE*>,
    enabled-transitions  : <VALUE*>,
    disabled-transitions : <VALUE*>,
}
```
**Exported graph response**
```
{
    current : <INTEGER>
    nodes   : <GRAPH_NODES*>,
    EDGES   : <GRAPH_EDGES*>
}
```
Where `<GRAPH_NODES*>` and `<GRAPH_EDGES*>` are JSON objects of the nodes and edges in the current graph.

**Loaded graph response**
```
{
    response  : "success"
}
```
**Killed response**
```
{
    response  : "bye world..."
}
```
**Invalid revert response**
```
{
    response   : "invalid state"
}
```
**Invalid command response**
```
{
    response   : "invalid command"
}
```
**Invalid input response**

Any input that does not follow the format discussed in the **Commands** section will be rejected by the server, responding with
```
{
    response  : "invalid input"
}
```
**Field description (make one for every response or make this universal?)**

| field | meaning |
| ------ | ------ |
| old-state | the number identifying the previous state the server was in |
| new-state | the number identifying the state the server is currently in |
| source_contents | the list of `<VALUE>` that exist in the previous state|
| target_contents | the list of `<VALUE>` that exist in the designated/next state|
| created_facts | the list of `<VALUE>` that exist in the designated/next state but not in the previous state|
| terminated_facts | the list of `<VALUE>` that exist in the previous state but not in the designated/next state|
||
| violations | the duty violations, invariant violations, or non-compliant/disabled actions and events that were caused by the command that receives this response |
| output-events | the list of output events (executed-transition) TODO|
| errors | the list of errors (non-deterministic transition/disabled transition/compilation error) TODO|
| query-results | the list of query results (True/False) TODO|
||
| new-duties | the new duties brought into existence by the command that receives this response |
| new-enabled-transitions | the actions and events that can be triggered and will not cause a violation which were disabled in the previous state  |
| new-disabled-actions | the actions and events that cannot be triggered or cause a violation when triggered which were enabled in the previous state |
| all-duties | the duties present in the current state |
| all-enabled-transitions | all actions and events that can be triggered and will not cause a violation  |
| all-disabled-actions | all actions and events that cannot be triggered or cause a violation when triggered |
| old-state | the number identifying the previous state the server was in |
| new-state | the number identifying the state the server is currently in |
||
| phrase | a string that was executed as a phrase to create the corresponding edge |
| source_id | the number identifying the previous state of an edge |
| target_id | the number identifying the next state of an edge |

---

#### Commands
Valid commands have one of the following forms.

##### Status report
The `eflint-server` can check the status of the server by retrieving the last edge to the current state of the server.

```
{
    command : "status"
}
```
If the server is ready and waiting for further commands, it will respond with information about its current state with a **Status response**

##### Killing the server
The `eflint-server` can kill a server with the following form:
```
{
    command : "kill"
}
```
The server will gracefully terminate with a **Killed response**

##### Facts
The `eflint-server` can return all the facts in the current state using the following form:
```
{
    command : "facts"
}
```
A successful request will respond with a **Facts response**.
##### Path
The `eflint-server` can return all the edges between the current state and the root state. If an <INTEGER> is provided for the value in the request form, the `eflint-server` will return all the edges between the current state and state assocciated with the provided <INTEGER>. A history request is in one of the following forms:
```
{
    command : "history",
    value   : <INTEGER>
}
{
    command : "history"
}
```
A successful request will respond with a **Path response**.

##### Leaf nodes/head nodes
The `eflint-server` can return all the leaf nodes of the execution graph/server using the following form:
```
{
    command : "trace-heads"
}
```
A successful request will respond with a **Head/Leaf nodes response**.
##### Executing phrases
The `eflint-server` can send and execute arbitrary phrases to the server, in the textual format accepted by `eflint-repl` (see the relevant documentation in the section "Executable `eflint-repl`") using the following form:
```
{
    command : "phrase",
    text    : <STRING>
}
```
The response can be that of a **status response**, **Invalid input response**, or **invalid command response**

##### Backtracking
The `eflint-server` can backtrack to one of its previous states (configurations), triggered by a command of the form:
```
{
    command   : "revert",
    value     : <INTEGER>
}
```
The provided `<INTEGER>` should be a positive number previously been sent as part of a response or be a negative number, in which case the server will revert to its initial state. A successful backtrack will respond with a **Status response** in the new state, or a **Invalid revert response** when it fails.
##### Creation and termination events
The `eflint-server` can create or terminate `<VALUE>` instances using the following forms:
```
{
    command   : "create",
    value     : <VALUE>
}
{
    command   : "terminate",
    value     : <VALUE>
}
```

An event either fails because the provided value is not a value in the normative model or succeeds, resulting in a new state. A successful creation or termination will respond with a **Status response**, or an **Invalid input response** when it fails.


##### Queries
The `eflint-server` can query `<VALUE>` instances whether they are present, absent, or enabled  using the following forms:
```
{
    command   : "test-present",
    value     : <VALUE>
}
{
    command   : "test-absent",
    value     : <VALUE>
}
{
    command   : "enabled",
    value     : <VALUE>
}
```

A query either fails because the provided value is not a value in the normative model, or succeeds because it is present or absent. A successful query will respond with a **Status response**, or an **Invalid input response** when it fails.

##### Actions & Events
The `eflint-server` can execute an action request in one of the following forms:
```
{
    command     : "action",
    act-type    : <STRING>,
    actor       : <STRING>|<VALUE>,
    recipient   : <STRING>|<VALUE>,
    objects     : <(STRING|VALUE)*>,
    force       : "true"|"false" //default is false
}
{
    command     : "action|event",
    value       : <VALUE>,
    force       : "true"|"false" //default is false
}
```
An invalid action may occur if the fields do not constitute a valid action according to the server's normative model (e.g. based on type-checking). The error contains a message indicating what went wrong (structure not specified). A successful action will respond with a **Status response**, or an **Invalid input response** when it fails.
