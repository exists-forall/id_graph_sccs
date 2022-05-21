# `id_graph_sccs`

**Download:** [crates.io/crates/id_graph_sccs](https://crates.io/crates/id_graph_sccs)

**Docs:** [docs.rs/id_graph_sccs](https://crates.io/crates/id_graph_sccs)

---

A small crate for finding the [strongly-connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) of a directed graph.

This crate is built on the [`id_collections`](https://crates.io/crates/id_collections) crate, and is designed to work with graphs in which nodes are labeled by integer indices belonging to a contiguous range from zero to some upper bound. The edges of the input graph do not need to be stored in any particular format; the caller provides the outgoing edges for each node via a callback function which is invoked lazily as the algorithm traverses the graph.

The implementation of the algorithm does not rely on recursion, so it is safe to run it on arbitrarily large graphs without risking a stack overflow.

# Examples

```rust
use id_collections::{id_type, IdVec};
use id_graph_sccs::{find_components, Sccs, Scc, SccKind};

#[id_type]
struct NodeId(u32);

#[id_type]
struct SccId(u32);

// Note: you are not required to store the edges of the input graph in an 'IdVec'; all that
// matters is that you are able to pass a closure to the 'find_components' function which
// returns the edges for a given node.
let mut graph: IdVec<NodeId, Vec<NodeId>> = IdVec::new();

let node_a = graph.push(Vec::new());
let node_b = graph.push(Vec::new());
let node_c = graph.push(Vec::new());
let node_d = graph.push(Vec::new());

graph[node_a].extend([node_a, node_b]);
graph[node_b].extend([node_c]);
graph[node_c].extend([node_b, node_d]);

let sccs: Sccs<SccId, NodeId> = find_components(graph.count(), |node| &graph[node]);

// We can iterate over 'sccs' to obtain the components of the graph:
let mut components: Vec<Scc<NodeId>> = Vec::new();
for (_scc_id, component) in &sccs {
    components.push(component);
}

assert_eq!(components.len(), 3);

assert_eq!(components[0].kind, SccKind::Acyclic);
assert_eq!(components[0].nodes, &[node_d]);

assert_eq!(components[1].kind, SccKind::Cyclic);
assert!(components[1].nodes.contains(&node_b));
assert!(components[1].nodes.contains(&node_c));

assert_eq!(components[2].kind, SccKind::Cyclic);
assert_eq!(components[2].nodes, &[node_a]);
```
