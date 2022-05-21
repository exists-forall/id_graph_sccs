//! A small crate for finding the [strongly-connected components](https://en.wikipedia.org/wiki/Strongly_connected_component)
//! of a directed graph.
//!
//! This crate is built on the [`id_collections`](https://crates.io/crates/id_collections) crate,
//! and is designed to work with graphs in which nodes are labeled by integer indices belonging to a
//! contiguous range from zero to some upper bound. The edges of the input graph do not need to be
//! stored in any particular format; the caller provides the outgoing edges for each node via a
//! callback function which is invoked lazily as the algorithm traverses the graph.
//!
//! The implementation of the algorithm does not rely on recursion, so it is safe to run it on
//! arbitrarily large graphs without risking a stack overflow.
//!
//! # Examples
//!
//! ```
//! use id_collections::{id_type, IdVec};
//! use id_graph_sccs::{find_components, Sccs, Scc, SccKind};
//!
//! #[id_type]
//! struct NodeId(u32);
//!
//! #[id_type]
//! struct SccId(u32);
//!
//! // Note: you are not required to store the edges of the input graph in an 'IdVec'; all that
//! // matters is that you are able to pass a closure to the 'find_components' function which
//! // returns the edges for a given node.
//! let mut graph: IdVec<NodeId, Vec<NodeId>> = IdVec::new();
//!
//! let node_a = graph.push(Vec::new());
//! let node_b = graph.push(Vec::new());
//! let node_c = graph.push(Vec::new());
//! let node_d = graph.push(Vec::new());
//!
//! graph[node_a].extend([node_a, node_b]);
//! graph[node_b].extend([node_c]);
//! graph[node_c].extend([node_b, node_d]);
//!
//! let sccs: Sccs<SccId, NodeId> = find_components(graph.count(), |node| &graph[node]);
//!
//! // We can iterate over 'sccs' to obtain the components of the graph:
//! let mut components: Vec<Scc<NodeId>> = Vec::new();
//! for (_scc_id, component) in &sccs {
//!     components.push(component);
//! }
//!
//! assert_eq!(components.len(), 3);
//!
//! assert_eq!(components[0].kind, SccKind::Acyclic);
//! assert_eq!(components[0].nodes, &[node_d]);
//!
//! assert_eq!(components[1].kind, SccKind::Cyclic);
//! assert!(components[1].nodes.contains(&node_b));
//! assert!(components[1].nodes.contains(&node_c));
//!
//! assert_eq!(components[2].kind, SccKind::Cyclic);
//! assert_eq!(components[2].nodes, &[node_a]);
//! ```
use id_collections::{count::IdRangeIter, id::ToPrimIntUnchecked, Count, Id, IdMap, IdVec};
use num_traits::{CheckedSub, One, ToPrimitive};
use std::{borrow::Borrow, fmt::Debug, iter::FusedIterator};

/// Indicates if a component contains a cycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SccKind {
    /// Indicates that the component does not contain a cycle. This implies that the component has
    /// exactly one node.
    Acyclic,
    /// Indicates that the component contains a cycle. A cyclic component may have one node with a
    /// self-loop, or it may have multiple nodes.
    Cyclic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SccInfo {
    slice_end: usize,
    kind: SccKind,
}

/// A sequence of strongly-connected components in a graph.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sccs<SccId: Id, NodeId: Id> {
    raw_nodes: Vec<NodeId>,
    scc_info: IdVec<SccId, SccInfo>,
}

impl<SccId: Id + Debug, NodeId: Id + Debug> Debug for Sccs<SccId, NodeId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self).finish()
    }
}

impl<SccId: Id, NodeId: Id> Default for Sccs<SccId, NodeId> {
    fn default() -> Self {
        Self::new()
    }
}

/// A single strongly-connected component in a graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Scc<'a, NodeId: Id> {
    /// Indicates if the component contains a cycle.
    pub kind: SccKind,
    /// The nodes in the component.
    pub nodes: &'a [NodeId],
}

impl<SccId: Id, NodeId: Id> Sccs<SccId, NodeId> {
    /// Create a new, empty sequence of components.
    pub fn new() -> Self {
        Sccs {
            raw_nodes: Vec::new(),
            scc_info: IdVec::new(),
        }
    }

    /// Creates a new, empty sequence of components, with space preallocated to hold `capacity`
    /// nodes.
    pub fn with_node_capacity(capacity: usize) -> Self {
        Sccs {
            raw_nodes: Vec::with_capacity(capacity),
            scc_info: IdVec::new(),
        }
    }

    /// Pushes a new component of kind [`SccKind::Acyclic`] onto the end of the sequence.
    ///
    /// Returns the id of the newly-inserted component.
    ///
    /// # Panics
    ///
    /// Panics if the length of the sequence overflows `SccId`.
    pub fn push_acyclic_component(&mut self, node: NodeId) -> SccId {
        self.raw_nodes.push(node);
        self.scc_info.push(SccInfo {
            slice_end: self.raw_nodes.len(),
            kind: SccKind::Acyclic,
        })
    }

    /// Pushes a new component of kind [`SccKind::Cyclic`] onto the end of the sequence.
    ///
    /// Returns the id of the newly-inserted component.
    ///
    /// # Panics
    ///
    /// Panics if `nodes` is empty, or if the length of the sequence overflows `SccId`.
    pub fn push_cyclic_component(&mut self, nodes: &[NodeId]) -> SccId {
        if nodes.is_empty() {
            panic!("SCC must contain at least one node");
        }
        self.raw_nodes.extend_from_slice(nodes);
        self.scc_info.push(SccInfo {
            slice_end: self.raw_nodes.len(),
            kind: SccKind::Cyclic,
        })
    }

    /// Returns the number of components in the sequence.
    pub fn count(&self) -> Count<SccId> {
        self.scc_info.count()
    }

    /// Returns the component with the given `id`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is not contained in [`self.count()`](Sccs::count).
    pub fn component<S: Borrow<SccId>>(&self, id: S) -> Scc<'_, NodeId> {
        let id = *id.borrow();
        let prev_id = id
            .to_index()
            .checked_sub(&SccId::Index::one())
            .map(SccId::from_index);
        let slice_start = match prev_id {
            Some(prev_id) => self.scc_info[prev_id].slice_end,
            None => 0,
        };
        let info = &self.scc_info[id];
        Scc {
            kind: info.kind,
            nodes: &self.raw_nodes[slice_start..info.slice_end],
        }
    }
}

impl<'a, SccId: Id, NodeId: Id> IntoIterator for &'a Sccs<SccId, NodeId> {
    type IntoIter = SccsIter<'a, SccId, NodeId>;
    type Item = (SccId, Scc<'a, NodeId>);

    fn into_iter(self) -> Self::IntoIter {
        SccsIter {
            sccs: self,
            inner: self.count().into_iter(),
        }
    }
}

/// An iterator over the strongly-connected components in a graph.
///
/// This type is returned by [`Sccs::into_iter`](struct.Sccs.html#method.into_iter).
#[derive(Debug)]
pub struct SccsIter<'a, SccId: Id, NodeId: Id> {
    sccs: &'a Sccs<SccId, NodeId>,
    inner: IdRangeIter<SccId>,
}

impl<'a, SccId: Id, NodeId: Id> Iterator for SccsIter<'a, SccId, NodeId> {
    type Item = (SccId, Scc<'a, NodeId>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|id| (id, self.sccs.component(id)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth(n).map(|id| (id, self.sccs.component(id)))
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.inner.last().map(|id| (id, self.sccs.component(id)))
    }
}

impl<'a, SccId: Id, NodeId: Id> FusedIterator for SccsIter<'a, SccId, NodeId> {}

impl<'a, SccId: Id, NodeId: Id> DoubleEndedIterator for SccsIter<'a, SccId, NodeId> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|id| (id, self.sccs.component(id)))
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.inner
            .nth_back(n)
            .map(|id| (id, self.sccs.component(id)))
    }
}

impl<'a, SccId: Id, NodeId: Id> ExactSizeIterator for SccsIter<'a, SccId, NodeId> {
    #[inline]
    fn len(&self) -> usize {
        // We know the bounds fit inside a 'usize', because they're derived from the size of an
        // IdVec.
        self.inner.end_index().to_usize_unchecked() - self.inner.start_index().to_usize_unchecked()
    }
}

/// Finds the strongly-connected components in a directed graph in dependency order.
///
/// The input graph is given implicitly by the `node_count` and `node_dependencies` arguments. The
/// nodes of the input graph are given by the set of all ids in the range specified by `node_count`,
/// and the edges outgoing from each node are given by the `node_dependencies` function. The
/// `node_dependencies` function is guaranteed to be called exactly once per node in the graph.
///
/// The returned sequence of components is guaranteed to be given in *dependency order*, meaning
/// that if `node_dependencies(n1)` contains a node `n2`, then `n2` is guaranteed to belong either
/// to the same component as `n1`, or to an earlier component in the sequence.
///
/// # Panics
///
/// Panics if `node_dependencies` returns a node not contained in the range specified by
/// `node_count`.
///
/// Panics if the number of connected components in the graph overflows `SccId`.
pub fn find_components<SccId, NodeId, NodeDependenciesFn, NodeDependencies, Dependency>(
    node_count: Count<NodeId>,
    mut node_dependencies: NodeDependenciesFn,
) -> Sccs<SccId, NodeId>
where
    SccId: Id,
    NodeId: Id,
    NodeDependenciesFn: FnMut(NodeId) -> NodeDependencies,
    NodeDependencies: IntoIterator<Item = Dependency>,
    Dependency: Borrow<NodeId>,
{
    // We use Tarjan's algorithm, performing the depth-first search using an explicit Vec-based
    // stack instead of recursion to avoid stack overflows on large graphs.

    #[derive(Clone, Copy, Debug)]
    enum NodeState {
        Unvisited,
        OnSearchStack { index: u32, low_link: u32 },
        OnSccStack { index: u32 },
        Complete,
    }

    #[derive(Clone, Copy)]
    enum Action<NodeId> {
        TryVisit {
            parent: Option<NodeId>,
            node: NodeId,
        },
        FinishVisit {
            parent: Option<NodeId>,
            node: NodeId,
        },
    }

    let node_capacity = node_count.to_value().to_usize().unwrap_or(usize::MAX);

    let mut sccs = Sccs::with_node_capacity(node_capacity);

    let mut node_states = IdVec::from_count_with(node_count, |_| NodeState::Unvisited);
    let mut node_self_loops = IdMap::with_capacity(node_capacity);
    let mut scc_stack = Vec::new();
    let mut search_stack = Vec::new();
    let mut next_index = 0;

    for search_root in node_count {
        search_stack.push(Action::TryVisit {
            parent: None,
            node: search_root,
        });
        while let Some(action) = search_stack.pop() {
            match action {
                Action::TryVisit { parent, node } => {
                    match node_states[node] {
                        NodeState::Unvisited => {
                            node_states[node] = NodeState::OnSearchStack {
                                index: next_index,
                                low_link: next_index,
                            };
                            next_index += 1;
                            scc_stack.push(node);

                            search_stack.push(Action::FinishVisit { parent, node });
                            // We need to explicitly track self-loops so that when we obtain a size-1
                            // SCC we can determine if it's cyclic or acyclic.
                            let mut has_self_loop = false;
                            for dependency in node_dependencies(node) {
                                let dependency = *dependency.borrow();
                                if !node_count.contains(dependency) {
                                    panic!(
                                        "node id of type {} with index {} is out of bounds for \
                                         node count {}",
                                        std::any::type_name::<NodeId>(),
                                        dependency.to_index(),
                                        node_count.to_value()
                                    );
                                }
                                if dependency == node {
                                    has_self_loop = true;
                                }
                                search_stack.push(Action::TryVisit {
                                    parent: Some(node),
                                    node: dependency,
                                });
                            }
                            node_self_loops.insert_vacant(node, has_self_loop);
                        }

                        NodeState::OnSearchStack { index, low_link: _ }
                        | NodeState::OnSccStack { index } => {
                            if let Some(parent) = parent {
                                if let NodeState::OnSearchStack {
                                    index: _,
                                    low_link: parent_low_link,
                                } = &mut node_states[parent]
                                {
                                    *parent_low_link = (*parent_low_link).min(index);
                                } else {
                                    unreachable!("parent should be on search stack");
                                }
                            }
                        }

                        NodeState::Complete => {}
                    }
                }

                Action::FinishVisit { parent, node } => {
                    let (index, low_link) =
                        if let NodeState::OnSearchStack { index, low_link } = node_states[node] {
                            (index, low_link)
                        } else {
                            unreachable!("node should be on search stack");
                        };

                    node_states[node] = NodeState::OnSccStack { index };

                    if let Some(parent) = parent {
                        if let NodeState::OnSearchStack {
                            index: _,
                            low_link: parent_low_link,
                        } = &mut node_states[parent]
                        {
                            *parent_low_link = (*parent_low_link).min(low_link);
                        } else {
                            unreachable!("parent should be on search stack")
                        }
                    }

                    if low_link == index {
                        let mut scc_start = scc_stack.len();
                        loop {
                            scc_start -= 1;
                            let scc_node = scc_stack[scc_start];
                            debug_assert!(matches!(
                                node_states[scc_node],
                                NodeState::OnSccStack { .. }
                            ));
                            node_states[scc_node] = NodeState::Complete;
                            if scc_node == node {
                                break;
                            }
                        }
                        let scc_slice = &scc_stack[scc_start..];
                        if scc_slice.len() == 1 && !node_self_loops[node] {
                            sccs.push_acyclic_component(scc_slice[0]);
                        } else {
                            sccs.push_cyclic_component(scc_slice);
                        };
                        scc_stack.truncate(scc_start);
                    }
                }
            }
        }
    }

    sccs
}
