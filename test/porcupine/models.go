package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"hash/fnv"
	"math"
	"os"
	"sort"
	"strconv"

	"github.com/anishathalye/porcupine"
)

// val mirrors linproof's Val: null, an integer or a string.
type val struct {
	kind uint8 // 0 null, 1 int, 2 string
	i    int64
	s    string
}

func (v val) String() string {
	switch v.kind {
	case 1:
		return strconv.FormatInt(v.i, 10)
	case 2:
		return strconv.Quote(v.s)
	}
	return "null"
}

func (v val) json() any {
	switch v.kind {
	case 1:
		return v.i
	case 2:
		return v.s
	}
	return nil
}

func parseVal(raw json.RawMessage) (val, error) {
	if len(raw) == 0 || string(raw) == "null" {
		return val{}, nil
	}
	var x any
	dec := json.NewDecoder(bytesReader(raw))
	dec.UseNumber()
	if err := dec.Decode(&x); err != nil {
		return val{}, err
	}
	switch t := x.(type) {
	case json.Number:
		i, err := t.Int64()
		if err != nil {
			return val{}, fmt.Errorf("not an int64: %s", t)
		}
		return val{kind: 1, i: i}, nil
	case string:
		return val{kind: 2, s: t}, nil
	}
	return val{}, fmt.Errorf("unsupported value %s", raw)
}

// Register operations, as in linproof's RegInput/RegOutput.
type regInput struct {
	key  string
	op   uint8 // 0 read, 1 write, 2 cas
	a, b val
}

type regOutput struct {
	kind uint8 // 0 value, 1 ok, 2 fail, 3 unknown (never returned)
	v    val
}

func hashVal(v val) uint64 {
	h := fnv.New64a()
	h.Write([]byte{v.kind})
	h.Write([]byte(strconv.FormatInt(v.i, 10)))
	h.Write([]byte(v.s))
	return h.Sum64()
}

// registerModel is linproof's register (withCas=false) or cas-register, per key.
func registerModel(withCas bool) porcupine.Model {
	return porcupine.Model{
		Partition: func(history []porcupine.Operation) [][]porcupine.Operation {
			return partition(history, func(op porcupine.Operation) string { return op.Input.(regInput).key })
		},
		Init: func() any { return val{} },
		Step: func(state, input, output any) (bool, any) {
			s := state.(val)
			in := input.(regInput)
			out := output.(regOutput)
			switch in.op {
			case 0:
				return out.kind == 3 || (out.kind == 0 && out.v == s), s
			case 1:
				return out.kind == 3 || out.kind == 1, in.a
			default:
				if !withCas {
					return false, s
				}
				match := s == in.a
				switch out.kind {
				case 3:
					if match {
						return true, in.b
					}
					return true, s
				case 1:
					return match, in.b
				case 2:
					return !match, s
				}
				return false, s
			}
		},
		Hash: func(state any) uint64 { return hashVal(state.(val)) },
	}
}

// Key-value operations, as in linproof's KVInput/KVOutput.
type kvInput struct {
	key   string
	op    uint8 // 0 get, 1 put, 2 append
	value string
}

type kvOutput struct {
	value   string
	unknown bool
}

func kvModel() porcupine.Model {
	return porcupine.Model{
		Partition: func(history []porcupine.Operation) [][]porcupine.Operation {
			return partition(history, func(op porcupine.Operation) string { return op.Input.(kvInput).key })
		},
		Init: func() any { return "" },
		Step: func(state, input, output any) (bool, any) {
			s := state.(string)
			in := input.(kvInput)
			out := output.(kvOutput)
			switch in.op {
			case 0:
				return out.unknown || out.value == s, s
			case 1:
				return true, in.value
			default:
				return true, s + in.value
			}
		},
		Hash: func(state any) uint64 {
			h := fnv.New64a()
			h.Write([]byte(state.(string)))
			return h.Sum64()
		},
	}
}

func partition(history []porcupine.Operation, key func(porcupine.Operation) string) [][]porcupine.Operation {
	m := map[string][]porcupine.Operation{}
	for _, op := range history {
		k := key(op)
		m[k] = append(m[k], op)
	}
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	out := make([][]porcupine.Operation, 0, len(keys))
	for _, k := range keys {
		out = append(out, m[k])
	}
	return out
}

// jsonOp is one line of linproof's history format.
type jsonOp struct {
	Process *int64          `json:"process,omitempty"`
	Call    int64           `json:"call"`
	Return  *int64          `json:"return,omitempty"`
	Op      string          `json:"op"`
	Key     json.RawMessage `json:"key,omitempty"`
	Input   json.RawMessage `json:"input,omitempty"`
	Output  json.RawMessage `json:"output,omitempty"`
}

// readHistory reads a linproof history file and converts it into Porcupine operations
// for the given model. Operations that never returned get a return time after every
// other event and an "unknown" output that the models accept in any state, which is
// how Porcupine's own Jepsen tests encode them.
func readHistory(path, model string) ([]porcupine.Operation, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var raw []jsonOp
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<26)
	for sc.Scan() {
		line := sc.Bytes()
		if len(trimSpace(line)) == 0 {
			continue
		}
		var op jsonOp
		if err := json.Unmarshal(line, &op); err != nil {
			return nil, fmt.Errorf("%s: %v", path, err)
		}
		raw = append(raw, op)
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	var maxT int64
	for _, op := range raw {
		maxT = max(maxT, op.Call)
		if op.Return != nil {
			maxT = max(maxT, *op.Return)
		}
	}
	end := maxT + 1
	if end == math.MaxInt64 {
		return nil, fmt.Errorf("timestamps too large")
	}
	ops := make([]porcupine.Operation, 0, len(raw))
	for i, op := range raw {
		ret := end
		if op.Return != nil {
			ret = *op.Return
		}
		key := ""
		if len(op.Key) > 0 && string(op.Key) != "null" {
			var k any
			if err := json.Unmarshal(op.Key, &k); err != nil {
				return nil, err
			}
			key = fmt.Sprint(k)
		}
		var in, out any
		switch model {
		case "register", "cas-register":
			ri := regInput{key: key}
			ro := regOutput{kind: 3}
			switch op.Op {
			case "read":
				ri.op = 0
				if op.Return != nil {
					v, err := parseVal(op.Output)
					if err != nil {
						return nil, err
					}
					ro = regOutput{kind: 0, v: v}
				}
			case "write":
				ri.op = 1
				v, err := parseVal(op.Input)
				if err != nil {
					return nil, err
				}
				ri.a = v
				if op.Return != nil {
					ro = regOutput{kind: 1}
				}
			case "cas":
				ri.op = 2
				var pair []json.RawMessage
				if err := json.Unmarshal(op.Input, &pair); err != nil || len(pair) != 2 {
					return nil, fmt.Errorf("line %d: bad cas input", i+1)
				}
				a, err1 := parseVal(pair[0])
				b, err2 := parseVal(pair[1])
				if err1 != nil || err2 != nil {
					return nil, fmt.Errorf("line %d: bad cas input", i+1)
				}
				ri.a, ri.b = a, b
				if op.Return != nil {
					if string(op.Output) == "true" {
						ro = regOutput{kind: 1}
					} else {
						ro = regOutput{kind: 2}
					}
				}
			default:
				return nil, fmt.Errorf("line %d: unknown op %q", i+1, op.Op)
			}
			in, out = ri, ro
		case "kv":
			ki := kvInput{key: key}
			ko := kvOutput{unknown: op.Return == nil}
			switch op.Op {
			case "get":
				ki.op = 0
				if op.Return != nil {
					if err := json.Unmarshal(op.Output, &ko.value); err != nil {
						return nil, fmt.Errorf("line %d: bad get output", i+1)
					}
				}
			case "put", "append":
				ki.op = 1
				if op.Op == "append" {
					ki.op = 2
				}
				if err := json.Unmarshal(op.Input, &ki.value); err != nil {
					return nil, fmt.Errorf("line %d: bad input", i+1)
				}
			default:
				return nil, fmt.Errorf("line %d: unknown op %q", i+1, op.Op)
			}
			in, out = ki, ko
		default:
			return nil, fmt.Errorf("unknown model %q", model)
		}
		client := 0
		if op.Process != nil {
			client = int(*op.Process)
		}
		ops = append(ops, porcupine.Operation{ClientId: client, Input: in, Call: op.Call, Output: out, Return: ret})
	}
	return ops, nil
}

func modelFor(name string) (porcupine.Model, error) {
	switch name {
	case "register":
		return registerModel(false), nil
	case "cas-register":
		return registerModel(true), nil
	case "kv":
		return kvModel(), nil
	}
	return porcupine.Model{}, fmt.Errorf("unknown model %q", name)
}
