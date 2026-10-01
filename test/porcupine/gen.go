package main

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"sort"
)

// genConfig describes one random history.
type genConfig struct {
	Model   string  // register, cas-register or kv
	Procs   int     // concurrent client slots
	Ops     int     // operations
	Values  int     // size of the value domain (registers)
	Keys    int     // 0: no keys (registers only); otherwise number of keys
	Pending float64 // probability that an operation never returns
	MaxDur  int     // maximum operation duration
	MaxGap  int     // maximum think time between a client's operations
}

// randomConfig picks a configuration for seed-driven differential testing. Sizes are
// kept small enough that an exhaustive search is quick for both checkers even when
// the history is not linearizable.
func randomConfig(rng *rand.Rand, model string) genConfig {
	cfg := genConfig{
		Model:   model,
		Procs:   1 + rng.Intn(5),
		Ops:     1 + rng.Intn(30),
		Values:  1 + rng.Intn(4),
		Pending: []float64{0, 0, 0.05, 0.15, 0.3}[rng.Intn(5)],
		MaxDur:  rng.Intn(8),
		MaxGap:  rng.Intn(4),
	}
	switch {
	case model == "kv":
		cfg.Keys = 1 + rng.Intn(3)
	case rng.Intn(4) == 0:
		cfg.Keys = 1 + rng.Intn(3)
	}
	return cfg
}

type simOp struct {
	op     jsonOp
	key    string
	lp     float64 // linearization point
	effect bool    // the operation takes effect (always, unless it never returned)
	// for cas: decide at simulation time whether it is meant to succeed
	casHit bool
	idx    int
}

func i64(x int64) *int64 { return &x }

func rawJSON(v any) json.RawMessage {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	return b
}

func randVal(rng *rand.Rand, n int) val {
	if rng.Intn(10) == 0 {
		return val{kind: 2, s: fmt.Sprintf("s%d", rng.Intn(n))}
	}
	return val{kind: 1, i: int64(rng.Intn(n))}
}

// generate produces a history that is linearizable by construction: every operation
// gets a linearization point inside its interval, outputs are computed by running the
// sequential specification in that order, and operations that never return take
// effect or not at random.
func generate(rng *rand.Rand, cfg genConfig) []jsonOp {
	next := make([]int64, cfg.Procs)
	pid := make([]int64, cfg.Procs)
	for p := range pid {
		pid[p] = int64(p)
	}
	sims := make([]*simOp, 0, cfg.Ops)
	for i := 0; i < cfg.Ops; i++ {
		p := rng.Intn(cfg.Procs)
		call := next[p] + int64(rng.Intn(cfg.MaxGap+1))
		dur := int64(rng.Intn(cfg.MaxDur + 1))
		s := &simOp{idx: i, effect: true}
		s.op.Process = i64(pid[p])
		s.op.Call = call
		if cfg.Keys > 0 {
			s.key = fmt.Sprintf("k%d", rng.Intn(cfg.Keys))
			s.op.Key = rawJSON(s.key)
		}
		pending := rng.Float64() < cfg.Pending
		if pending {
			// A crashed client: its operation may take effect at any later time.
			s.effect = rng.Intn(2) == 0
			s.lp = float64(call) + rng.Float64()*float64(dur+5)
			pid[p] += int64(cfg.Procs)
			next[p] = call + 1
		} else {
			ret := call + dur
			s.op.Return = i64(ret)
			s.lp = float64(call) + rng.Float64()*float64(dur)
			next[p] = ret + 1
		}
		switch cfg.Model {
		case "kv":
			switch rng.Intn(3) {
			case 0:
				s.op.Op = "get"
			case 1:
				s.op.Op = "put"
				s.op.Input = rawJSON(fmt.Sprintf("p%d.", i))
			default:
				s.op.Op = "append"
				s.op.Input = rawJSON(fmt.Sprintf("a%d.", i))
			}
		default:
			r := rng.Intn(3)
			if cfg.Model == "register" {
				r = rng.Intn(2)
			}
			switch r {
			case 0:
				s.op.Op = "read"
			case 1:
				s.op.Op = "write"
				s.op.Input = rawJSON(randVal(rng, cfg.Values).json())
			default:
				s.op.Op = "cas"
				s.casHit = rng.Intn(2) == 0
			}
		}
		sims = append(sims, s)
	}
	// Run the sequential specification in linearization-point order.
	order := make([]*simOp, len(sims))
	copy(order, sims)
	sort.SliceStable(order, func(a, b int) bool { return order[a].lp < order[b].lp })
	regs := map[string]val{}
	strs := map[string]string{}
	for _, s := range order {
		switch s.op.Op {
		case "read":
			if s.op.Return != nil {
				s.op.Output = rawJSON(regs[s.key].json())
			}
		case "write":
			if s.effect {
				v, _ := parseVal(s.op.Input)
				regs[s.key] = v
			}
		case "cas":
			cur := regs[s.key]
			exp := cur
			if !s.casHit {
				exp = randVal(rng, cfg.Values)
			}
			nv := randVal(rng, cfg.Values)
			s.op.Input = rawJSON([]any{exp.json(), nv.json()})
			ok := exp == cur
			if s.op.Return != nil {
				s.op.Output = rawJSON(ok)
			}
			if ok && s.effect {
				regs[s.key] = nv
			}
		case "get":
			if s.op.Return != nil {
				s.op.Output = rawJSON(strs[s.key])
			}
		case "put":
			if s.effect {
				var v string
				_ = json.Unmarshal(s.op.Input, &v)
				strs[s.key] = v
			}
		case "append":
			if s.effect {
				var v string
				_ = json.Unmarshal(s.op.Input, &v)
				strs[s.key] += v
			}
		}
	}
	out := make([]jsonOp, len(sims))
	for i, s := range sims {
		out[i] = s.op
	}
	return out
}

// corrupt changes one returned operation: its output, or its timing. The result may or
// may not be linearizable; the two checkers must agree either way.
func corrupt(rng *rand.Rand, ops []jsonOp, cfg genConfig) []jsonOp {
	out := make([]jsonOp, len(ops))
	copy(out, ops)
	var returned []int
	for i, op := range out {
		if op.Return != nil {
			returned = append(returned, i)
		}
	}
	if len(returned) == 0 {
		return out
	}
	i := returned[rng.Intn(len(returned))]
	op := out[i]
	if rng.Intn(3) == 0 || op.Op == "write" || op.Op == "put" || op.Op == "append" {
		// Move the interval, keeping it well formed.
		dur := *op.Return - op.Call
		shift := int64(rng.Intn(11) - 5)
		call := max(op.Call+shift, 0)
		if rng.Intn(2) == 0 {
			dur = int64(rng.Intn(int(dur) + 1))
		}
		op.Call = call
		op.Return = i64(call + dur)
	} else {
		switch op.Op {
		case "read":
			cur, _ := parseVal(op.Output)
			v := randVal(rng, cfg.Values+1)
			if rng.Intn(4) == 0 {
				v = val{}
			}
			if v == cur {
				v = val{kind: 1, i: int64(cfg.Values + 7)}
			}
			op.Output = rawJSON(v.json())
		case "cas":
			op.Output = rawJSON(string(op.Output) != "true")
		case "get":
			var s string
			_ = json.Unmarshal(op.Output, &s)
			if s == "" || rng.Intn(2) == 0 {
				s += "z."
			} else {
				s = s[:len(s)-1]
			}
			op.Output = rawJSON(s)
		}
	}
	out[i] = op
	return out
}
