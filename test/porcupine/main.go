// Command porcupine-diff tests linproof against Porcupine
// (github.com/anishathalye/porcupine).
//
//	go run . diff  -linproof BIN [-model M] [-seed S] [-n N]  random histories, verdicts must agree
//	go run . check [-model M] FILE...                         Porcupine's verdict on linproof files
//	go run . bench -linproof BIN [-model M] [-runs R] FILE... time both checkers on the same files
//	go run . gen   [-model M] [-seed S] [-ops N] ... -o FILE  write one random history
package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	"github.com/anishathalye/porcupine"
)

func bytesReader(b []byte) io.Reader { return bytes.NewReader(b) }
func trimSpace(b []byte) []byte      { return bytes.TrimSpace(b) }

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: porcupine-diff diff|check|bench|gen [flags]")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "diff":
		err = cmdDiff(os.Args[2:])
	case "check":
		err = cmdCheck(os.Args[2:])
	case "bench":
		err = cmdBench(os.Args[2:])
	case "gen":
		err = cmdGen(os.Args[2:])
	default:
		err = fmt.Errorf("unknown command %q", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(1)
	}
}

func writeHistory(path string, ops []jsonOp) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	w := bufio.NewWriter(f)
	enc := json.NewEncoder(w)
	for _, op := range ops {
		if err := enc.Encode(op); err != nil {
			f.Close()
			return err
		}
	}
	if err := w.Flush(); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}

// porcupineVerdict runs Porcupine on a linproof history file.
func porcupineVerdict(path, model string) (bool, time.Duration, error) {
	ops, err := readHistory(path, model)
	if err != nil {
		return false, 0, err
	}
	m, err := modelFor(model)
	if err != nil {
		return false, 0, err
	}
	t0 := time.Now()
	ok := porcupine.CheckOperations(m, ops)
	return ok, time.Since(t0), nil
}

var quietLine = regexp.MustCompile(`^(.*): (linearizable|not linearizable)$`)

// linproofVerdicts runs linproof once on many files (quiet mode) and returns the verdicts.
func linproofVerdicts(bin, model string, files []string) (map[string]bool, error) {
	args := append([]string{"check", "-q", "--model", model}, files...)
	cmd := exec.Command(bin, args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		if ee, ok := err.(*exec.ExitError); !ok || ee.ExitCode() != 1 {
			return nil, fmt.Errorf("linproof: %v: %s", err, stderr.String())
		}
	}
	res := map[string]bool{}
	for _, line := range strings.Split(string(out), "\n") {
		if m := quietLine.FindStringSubmatch(line); m != nil {
			res[m[1]] = m[2] == "linearizable"
		}
	}
	return res, nil
}

type diffCase struct {
	seed      int64
	file      string
	corrupted bool
	porcupine bool
}

// runDiff generates n histories with seeds seed0..seed0+n-1 (odd offsets corrupted),
// checks each with both tools and returns the cases on which they disagree.
func runDiff(bin, model string, seed0 int64, n int, dir string, log io.Writer) ([]diffCase, map[string]int, error) {
	counts := map[string]int{}
	var bad []diffCase
	const batch = 400
	for start := 0; start < n; start += batch {
		var cases []diffCase
		var files []string
		for i := start; i < min(start+batch, n); i++ {
			seed := seed0 + int64(i)
			rng := rand.New(rand.NewSource(seed))
			cfg := randomConfig(rng, model)
			h := generate(rng, cfg)
			corrupted := i%2 == 1
			if corrupted {
				h = corrupt(rng, h, cfg)
			}
			file := filepath.Join(dir, fmt.Sprintf("%s-%d.jsonl", model, seed))
			if err := writeHistory(file, h); err != nil {
				return nil, nil, err
			}
			pv, _, err := porcupineVerdict(file, model)
			if err != nil {
				return nil, nil, fmt.Errorf("seed %d: %v", seed, err)
			}
			cases = append(cases, diffCase{seed, file, corrupted, pv})
			files = append(files, file)
		}
		lv, err := linproofVerdicts(bin, model, files)
		if err != nil {
			return nil, nil, err
		}
		for _, c := range cases {
			got, ok := lv[c.file]
			kind := "constructed"
			if c.corrupted {
				kind = "corrupted"
			}
			verdict := "linearizable"
			if !c.porcupine {
				verdict = "not-linearizable"
			}
			counts[kind+"/"+verdict]++
			switch {
			case !ok:
				fmt.Fprintf(log, "seed %d: linproof gave no verdict for %s\n", c.seed, c.file)
				bad = append(bad, c)
			case got != c.porcupine:
				fmt.Fprintf(log, "MISMATCH seed %d (%s): porcupine=%v linproof=%v file %s\n", c.seed, kind, c.porcupine, got, c.file)
				bad = append(bad, c)
			case !c.corrupted && !got:
				fmt.Fprintf(log, "seed %d: a history linearizable by construction was rejected: %s\n", c.seed, c.file)
				bad = append(bad, c)
			}
		}
	}
	return bad, counts, nil
}

func cmdDiff(args []string) error {
	fs := flag.NewFlagSet("diff", flag.ExitOnError)
	bin := fs.String("linproof", "", "path to the linproof binary")
	model := fs.String("model", "cas-register", "register, cas-register or kv")
	seed := fs.Int64("seed", 1, "first seed")
	n := fs.Int("n", 1000, "number of histories")
	keep := fs.Bool("keep", false, "keep the generated files")
	_ = fs.Parse(args)
	if *bin == "" {
		return fmt.Errorf("-linproof is required")
	}
	dir, err := os.MkdirTemp("", "linproof-diff-")
	if err != nil {
		return err
	}
	if !*keep {
		defer os.RemoveAll(dir)
	}
	bad, counts, err := runDiff(*bin, *model, *seed, *n, dir, os.Stdout)
	if err != nil {
		return err
	}
	keys := make([]string, 0, len(counts))
	for k := range counts {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	fmt.Printf("model %s, seeds %d..%d: ", *model, *seed, *seed+int64(*n)-1)
	for _, k := range keys {
		fmt.Printf("%s=%d ", k, counts[k])
	}
	fmt.Println()
	if len(bad) > 0 {
		return fmt.Errorf("%d disagreements (files kept in %s)", len(bad), dir)
	}
	fmt.Println("all verdicts agree")
	return nil
}

func cmdCheck(args []string) error {
	fs := flag.NewFlagSet("check", flag.ExitOnError)
	model := fs.String("model", "cas-register", "register, cas-register or kv")
	_ = fs.Parse(args)
	for _, f := range fs.Args() {
		ok, d, err := porcupineVerdict(f, *model)
		if err != nil {
			return err
		}
		v := "linearizable"
		if !ok {
			v = "not linearizable"
		}
		fmt.Printf("%s: %s (%.2f ms)\n", f, v, float64(d.Microseconds())/1000)
	}
	return nil
}

var checkTime = regexp.MustCompile(`\((\d+)\.(\d+) ms`)

func median(xs []float64) float64 {
	s := append([]float64(nil), xs...)
	sort.Float64s(s)
	return s[len(s)/2]
}

func cmdBench(args []string) error {
	fs := flag.NewFlagSet("bench", flag.ExitOnError)
	bin := fs.String("linproof", "", "path to the linproof binary")
	model := fs.String("model", "cas-register", "register, cas-register or kv")
	runs := fs.Int("runs", 5, "runs per file (the median is reported)")
	_ = fs.Parse(args)
	if *bin == "" {
		return fmt.Errorf("-linproof is required")
	}
	fmt.Printf("%-28s %6s %8s %12s %12s %12s\n", "file", "ops", "verdict", "porcupine", "linproof", "linproof-cli")
	var totP, totL, totW float64
	for _, f := range fs.Args() {
		ops, err := readHistory(f, *model)
		if err != nil {
			return err
		}
		var pt, lt, wt []float64
		var pv, lv bool
		for r := 0; r < *runs; r++ {
			ok, d, err := porcupineVerdict(f, *model)
			if err != nil {
				return err
			}
			pv = ok
			pt = append(pt, float64(d.Nanoseconds())/1e6)
			t0 := time.Now()
			out, err := exec.Command(*bin, "check", "--model", *model, f).Output()
			wall := time.Since(t0)
			if err != nil {
				if ee, ok := err.(*exec.ExitError); !ok || ee.ExitCode() != 1 {
					return fmt.Errorf("linproof on %s: %v", f, err)
				}
			}
			lv = bytes.Contains(out, []byte("\nLINEARIZABLE"))
			m := checkTime.FindSubmatch(out)
			if m == nil {
				return fmt.Errorf("no timing in linproof output for %s", f)
			}
			ms, _ := strconv.ParseFloat(string(m[1])+"."+string(m[2]), 64)
			lt = append(lt, ms)
			wt = append(wt, float64(wall.Nanoseconds())/1e6)
		}
		if pv != lv {
			return fmt.Errorf("%s: verdicts differ (porcupine %v, linproof %v)", f, pv, lv)
		}
		v := "ok"
		if !pv {
			v = "VIOLATION"
		}
		p, l, w := median(pt), median(lt), median(wt)
		totP += p
		totL += l
		totW += w
		fmt.Printf("%-28s %6d %8s %9.2f ms %9.2f ms %9.2f ms\n", filepath.Base(f), len(ops), v, p, l, w)
	}
	fmt.Printf("%-28s %6s %8s %9.2f ms %9.2f ms %9.2f ms\n", "total", "", "", totP, totL, totW)
	return nil
}

func cmdGen(args []string) error {
	fs := flag.NewFlagSet("gen", flag.ExitOnError)
	model := fs.String("model", "cas-register", "register, cas-register or kv")
	seed := fs.Int64("seed", 1, "seed")
	ops := fs.Int("ops", 100, "operations")
	procs := fs.Int("procs", 5, "concurrent clients")
	values := fs.Int("values", 5, "value domain size")
	keys := fs.Int("keys", 0, "number of keys (0: unkeyed register)")
	pending := fs.Float64("pending", 0.05, "probability that an operation never returns")
	maxDur := fs.Int("dur", 10, "maximum duration")
	maxGap := fs.Int("gap", 3, "maximum think time")
	bad := fs.Bool("corrupt", false, "corrupt one operation")
	out := fs.String("o", "", "output file")
	_ = fs.Parse(args)
	if *out == "" {
		return fmt.Errorf("-o is required")
	}
	if *model == "kv" && *keys == 0 {
		*keys = 1
	}
	cfg := genConfig{Model: *model, Procs: *procs, Ops: *ops, Values: *values, Keys: *keys,
		Pending: *pending, MaxDur: *maxDur, MaxGap: *maxGap}
	rng := rand.New(rand.NewSource(*seed))
	h := generate(rng, cfg)
	if *bad {
		h = corrupt(rng, h, cfg)
	}
	return writeHistory(*out, h)
}
