package desclib

import (
	"slices"

	"github.com/hmdsefi/gograph"
	"github.com/hmdsefi/gograph/connectivity"
	"google.golang.org/protobuf/reflect/protoreflect"
)

// This file builds the message reference graph of a set of protobuf files and
// classifies every message by how it participates in a cycle of that graph.
//
// The graph has one node per message type -- keyed by fully qualified name, so
// that a message reached through several files is a single node -- and one edge
// per field whose type is another message. A message is recursive exactly when
// it lies on a cycle:
//
//   - self recursive:      the message has a field of its own type, so the
//                          cycle is the single self loop M -> M.
//   - mutually recursive:  the message sits in a strongly connected component
//                          of two or more messages, so it reaches itself only
//                          by going through some other message first.
//
// A message can be both, and a component can contain both kinds of cycle, which
// is why the two are tracked as independent flags rather than as an enumeration.
//
// The graph itself is a gograph.Graph, which supplies the two traversals this
// analysis needs: Tarjan's algorithm for the strongly connected components, and
// a topological sort of the resulting condensation for the reachability pass.
// Only the construction of the graph is specific to protobuf, and two
// representation details of compiled descriptors matter there:
//
//   - Map fields are internally a repeated synthetic "entry" message. Counting
//     those entries as nodes would report `map<string, Node>` inside Node as a
//     two message cycle (Node <-> NodeEntry) when it is really Node referring to
//     itself, so entries are skipped and the edge goes straight to the map value
//     type.
//   - An extension field declared inside message M extends some other message X.
//     The reference it creates is from X, not from M, so the edge is attributed
//     to the extendee.

// RefEdge is one message-to-message reference, created by a single field.
type RefEdge struct {
	From      protoreflect.FullName
	To        protoreflect.FullName
	Field     protoreflect.FieldDescriptor
	ViaMap    bool
	Repeated  bool
	Extension bool
}

// RefNode is one message type in the reference graph.
type RefNode struct {
	Desc protoreflect.MessageDescriptor
	Name protoreflect.FullName
	// File is the path of the file declaring this message, which is not
	// necessarily one of the files the analysis was asked about: it can be
	// an import pulled in to close the graph.
	File string
	// Out holds one entry per referring field, so a message with two fields
	// of the same type has two edges here where the underlying graph, which
	// does not carry field information and rejects parallel edges, has one.
	Out []RefEdge
}

// RefGraph is the message reference graph of a set of files.
type RefGraph struct {
	nodes map[protoreflect.FullName]*RefNode
	// order is the node set sorted by name, so that every traversal, and
	// therefore every report built from one, is deterministic.
	order []protoreflect.FullName
	graph gograph.Graph[protoreflect.FullName]
}

// Node returns the graph node for a message, or nil if the message is not in
// the graph (map entries never are).
func (g *RefGraph) Node(name protoreflect.FullName) *RefNode {
	return g.nodes[name]
}

// Names returns the messages in the graph, sorted.
func (g *RefGraph) Names() []protoreflect.FullName { return g.order }

// BuildRefGraph builds the reference graph spanning roots and, transitively,
// everything they import. Imports have to be followed to get the reachability
// pass right: a message is not recursive for having a google.protobuf.Struct
// field, but it does contain recursion, because Struct is recursive in the file
// it comes from.
//
// A cycle itself never spans files. Referring to a type in another file needs an
// import, and protobuf rejects circular imports, so the message reference graph
// projected onto files is a sub-relation of an acyclic one. Cross-file cycles
// are still reported rather than assumed away, as a check on that reasoning.
func BuildRefGraph(roots []protoreflect.FileDescriptor) *RefGraph {
	g := &RefGraph{
		nodes: make(map[protoreflect.FullName]*RefNode),
		graph: gograph.New[protoreflect.FullName](gograph.Directed()),
	}

	seen := make(map[string]bool)
	queue := slices.Clone(roots)
	for len(queue) > 0 {
		fd := queue[0]
		queue = queue[1:]
		if fd == nil || seen[fd.Path()] {
			continue
		}
		seen[fd.Path()] = true

		for i := range fd.Imports().Len() {
			queue = append(queue, fd.Imports().Get(i).FileDescriptor)
		}

		eachMessage(fd, func(md protoreflect.MessageDescriptor) {
			g.addNode(md)
			for f := range FieldIter(md) {
				g.addFieldEdge(md.FullName(), f, false)
			}
			for x := range ExtensionIter(md) {
				g.addExtensionEdge(x)
			}
		})
		for x := range FileExtensionIter(fd) {
			g.addExtensionEdge(x)
		}
	}

	// A field can point at a message whose file was never queued -- it should
	// not happen, since a used type must be imported, but a node missing here
	// would silently hide the cycle running through it. Sweep once more over
	// anything an edge introduced, by index because addNode appends. The
	// target comes from fieldTarget rather than from the field, so that a map
	// field still adds its value type and not the entry standing in for it.
	for i := 0; i < len(g.order); i++ {
		for _, e := range g.nodes[g.order[i]].Out {
			if g.nodes[e.To] != nil {
				continue
			}
			if target, _ := fieldTarget(e.Field); target != nil {
				g.addNode(target)
			}
		}
	}

	slices.Sort(g.order)
	return g
}

// eachMessage visits every message declared in a file, nested ones included and
// synthetic map entries excluded.
func eachMessage(fd protoreflect.FileDescriptor, fn func(protoreflect.MessageDescriptor)) {
	var rec func(protoreflect.MessageDescriptors)
	rec = func(mds protoreflect.MessageDescriptors) {
		for i := range mds.Len() {
			md := mds.Get(i)
			if !md.IsMapEntry() {
				fn(md)
			}
			rec(md.Messages())
		}
	}
	rec(fd.Messages())
}

func (g *RefGraph) addNode(md protoreflect.MessageDescriptor) *RefNode {
	if n, ok := g.nodes[md.FullName()]; ok {
		return n
	}
	n := &RefNode{Desc: md, Name: md.FullName(), File: md.ParentFile().Path()}
	g.nodes[md.FullName()] = n
	g.order = append(g.order, md.FullName())
	g.graph.AddVertexByLabel(md.FullName())
	return n
}

// addFieldEdge records the reference a field creates, if it creates one.
func (g *RefGraph) addFieldEdge(from protoreflect.FullName, f protoreflect.FieldDescriptor, ext bool) {
	target, viaMap := fieldTarget(f)
	if target == nil {
		return
	}
	n := g.nodes[from]
	if n == nil {
		return
	}
	n.Out = append(n.Out, RefEdge{
		From:      from,
		To:        target.FullName(),
		Field:     f,
		ViaMap:    viaMap,
		Repeated:  f.Cardinality() == protoreflect.Repeated,
		Extension: ext,
	})
	// The error here is ErrEdgeAlreadyExists, which just means some earlier
	// field of this message already had the same type.
	_, _ = g.graph.AddEdge(gograph.NewVertex(from), gograph.NewVertex(target.FullName()))
}

// addExtensionEdge attributes an extension field to the message it extends,
// which is the message that actually gains the reference.
func (g *RefGraph) addExtensionEdge(x protoreflect.ExtensionDescriptor) {
	extendee := x.ContainingMessage()
	if extendee == nil {
		return
	}
	if g.nodes[extendee.FullName()] == nil {
		g.addNode(extendee)
	}
	g.addFieldEdge(extendee.FullName(), x, true)
}

// fieldTarget is the message a field refers to, looking through the synthetic
// entry message of a map field to the map's value type.
func fieldTarget(f protoreflect.FieldDescriptor) (protoreflect.MessageDescriptor, bool) {
	if f.IsMap() {
		v := f.MapValue()
		if isMessageKind(v.Kind()) {
			return v.Message(), true
		}
		return nil, true
	}
	if isMessageKind(f.Kind()) {
		return f.Message(), false
	}
	return nil, false
}

func isMessageKind(k protoreflect.Kind) bool {
	return k == protoreflect.MessageKind || k == protoreflect.GroupKind
}

// MsgRecursion is how one message participates in the recursion of the graph.
type MsgRecursion struct {
	Name protoreflect.FullName
	File string
	// Self is set when the message has a field of its own type.
	Self bool
	// Mutual is set when the message reaches itself only through another
	// message, i.e. its strongly connected component has several members.
	Mutual bool
	// Group indexes Analysis.Groups, or is -1 when the message is not
	// recursive at all.
	Group int
	// Contains is set when the message can reach a recursive message,
	// itself included. It is the "needs a recursive parser" predicate:
	// a value of this message can nest to unbounded depth.
	Contains bool
}

// Recursive reports whether the message lies on a cycle.
func (m MsgRecursion) Recursive() bool { return m.Self || m.Mutual }

// RecursionGroup is one cyclic strongly connected component of the graph.
type RecursionGroup struct {
	// Members is sorted by name.
	Members []protoreflect.FullName
	// Files is the set of files declaring the members, sorted. Protobuf
	// forbids circular imports, so a cycle cannot span files and this is
	// expected to be a single file; see BuildRefGraph.
	Files []string
	// Edges are the references between members, i.e. the edges that make up
	// the cycles.
	Edges []RefEdge
	// Self is set when some member has a field of its own type.
	Self bool
}

// CrossFile reports whether the cycle spans more than one file.
func (r RecursionGroup) CrossFile() bool { return len(r.Files) > 1 }

// Analysis is the recursion classification of a whole reference graph.
type Analysis struct {
	Graph  *RefGraph
	Groups []RecursionGroup
	Msgs   map[protoreflect.FullName]MsgRecursion
}

// Msg returns the classification of a message. Messages outside the graph --
// map entries -- come back as the zero value with no group.
func (a *Analysis) Msg(name protoreflect.FullName) MsgRecursion {
	if m, ok := a.Msgs[name]; ok {
		return m
	}
	return MsgRecursion{Name: name, Group: -1}
}

// AnalyzeRecursion classifies every message of the graph. A message is
// recursive exactly when its strongly connected component has several members,
// or is a single member with a self loop -- Tarjan's algorithm reports a self
// referencing message as a component of one, so the self loop has to be read
// off the edges rather than off the component.
func AnalyzeRecursion(g *RefGraph) *Analysis {
	a := &Analysis{Graph: g, Msgs: make(map[protoreflect.FullName]MsgRecursion, len(g.order))}
	for _, name := range g.order {
		a.Msgs[name] = MsgRecursion{Name: name, File: g.nodes[name].File, Group: -1}
	}

	comps := components(g)
	comp := make(map[protoreflect.FullName]int, len(g.order))
	for i, members := range comps {
		for _, name := range members {
			comp[name] = i
		}
	}

	// cyclic[i] says whether component i is a cycle rather than a lone
	// acyclic message; groupOf[i] is where it landed in a.Groups.
	cyclic := make([]bool, len(comps))
	groupOf := make([]int, len(comps))
	for i, members := range comps {
		groupOf[i] = -1

		selfLoop := make(map[protoreflect.FullName]bool)
		var edges []RefEdge
		for _, name := range members {
			for _, e := range g.nodes[name].Out {
				if comp[e.To] != i {
					continue
				}
				edges = append(edges, e)
				if e.To == name {
					selfLoop[name] = true
				}
			}
		}

		// A component of one message with no self loop is an ordinary
		// acyclic message, not a recursive one.
		if len(members) == 1 && !selfLoop[members[0]] {
			continue
		}
		cyclic[i] = true

		files := make([]string, 0, len(members))
		for _, name := range members {
			files = append(files, g.nodes[name].File)
		}
		slices.Sort(files)
		files = slices.Compact(files)

		groupOf[i] = len(a.Groups)
		for _, name := range members {
			m := a.Msgs[name]
			m.Self = selfLoop[name]
			m.Mutual = len(members) > 1
			m.Group = groupOf[i]
			a.Msgs[name] = m
		}
		a.Groups = append(a.Groups, RecursionGroup{
			Members: members,
			Files:   files,
			Edges:   edges,
			Self:    len(selfLoop) > 0,
		})
	}

	a.markContains(comp, cyclic)
	return a
}

// components returns the strongly connected components of the graph, each one
// sorted by name and the components themselves sorted by their first member.
// Tarjan visits the vertices in map order, so without this the component order,
// and every report built from it, would vary between runs.
func components(g *RefGraph) [][]protoreflect.FullName {
	sccs := connectivity.Tarjan(g.graph)

	comps := make([][]protoreflect.FullName, 0, len(sccs))
	for _, scc := range sccs {
		members := make([]protoreflect.FullName, 0, len(scc))
		for _, v := range scc {
			members = append(members, v.Label())
		}
		slices.Sort(members)
		comps = append(comps, members)
	}
	slices.SortFunc(comps, func(x, y []protoreflect.FullName) int {
		return slices.Compare(x, y)
	})
	return comps
}

// markContains flags every message that can reach a recursive one. Contracting
// each component to a single vertex turns the reference graph into a DAG, so a
// component contains recursion when it is itself cyclic or when any component
// it points at does -- which one pass over the reverse topological order of the
// condensation settles.
func (a *Analysis) markContains(comp map[protoreflect.FullName]int, cyclic []bool) {
	cond := gograph.New[int](gograph.Directed())
	for i := range cyclic {
		cond.AddVertexByLabel(i)
	}
	for _, name := range a.Graph.order {
		for _, e := range a.Graph.nodes[name].Out {
			to, ok := comp[e.To]
			if !ok || to == comp[name] {
				continue
			}
			_, _ = cond.AddEdge(gograph.NewVertex(comp[name]), gograph.NewVertex(to))
		}
	}

	contains := slices.Clone(cyclic)
	// The condensation of any graph is acyclic, so the sort cannot fail;
	// were it to, every recursive message is still flagged, and only the
	// messages merely containing one would be missed.
	if order, err := gograph.TopologySort(cond); err == nil {
		for i := len(order) - 1; i >= 0; i-- {
			c := order[i].Label()
			for _, succ := range order[i].Neighbors() {
				if contains[succ.Label()] {
					contains[c] = true
					break
				}
			}
		}
	}

	for _, name := range a.Graph.order {
		if contains[comp[name]] {
			m := a.Msgs[name]
			m.Contains = true
			a.Msgs[name] = m
		}
	}
}
