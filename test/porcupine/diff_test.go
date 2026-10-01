package main

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// linproofBin returns the linproof binary to test, or skips the test.
func linproofBin(t *testing.T) string {
	t.Helper()
	bin := os.Getenv("LINPROOF")
	if bin == "" {
		bin = "../../.lake/build/bin/linproof"
	}
	abs, err := filepath.Abs(bin)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(abs); err != nil {
		t.Skipf("linproof binary not found at %s (build it with `lake build`, or set LINPROOF)", abs)
	}
	return abs
}

func envInt(name string, def int) int {
	if v := os.Getenv(name); v != "" {
		if n, err := strconv.Atoi(v); err == nil {
			return n
		}
	}
	return def
}

// TestDifferential compares linproof with Porcupine on random histories. Seeds are fixed
// (LINPROOF_DIFF_SEED, default 1) and every disagreement is reported with its seed. Half
// of the histories are linearizable by construction; the other half have one operation
// corrupted.
func TestDifferential(t *testing.T) {
	bin := linproofBin(t)
	n := envInt("LINPROOF_DIFF_N", 1000)
	seed := int64(envInt("LINPROOF_DIFF_SEED", 1))
	for _, model := range []string{"register", "cas-register", "kv"} {
		t.Run(model, func(t *testing.T) {
			var log bytes.Buffer
			bad, counts, err := runDiff(bin, model, seed, n, t.TempDir(), &log)
			if err != nil {
				t.Fatal(err)
			}
			if len(bad) > 0 {
				t.Fatalf("%d disagreements (seeds from %d):\n%s", len(bad), seed, log.String())
			}
			if counts["corrupted/not-linearizable"] == 0 || counts["corrupted/linearizable"] == 0 {
				t.Fatalf("the generator should produce both verdicts: %v", counts)
			}
			t.Logf("model %s, seeds %d..%d: %v", model, seed, seed+int64(n)-1, counts)
		})
	}
}

// porcupineDir locates the Porcupine module, whose test data are real histories.
func porcupineDir(t *testing.T) string {
	t.Helper()
	out, err := exec.Command("go", "list", "-m", "-f", "{{.Dir}}", "github.com/anishathalye/porcupine").Output()
	if err != nil {
		t.Skipf("cannot locate the porcupine module: %v", err)
	}
	return strings.TrimSpace(string(out))
}

// convertLog runs tools/jepsen2jsonl.py on a Jepsen-style log.
func convertLog(t *testing.T, src, dst string) {
	t.Helper()
	out, err := exec.Command("python3", "../../tools/jepsen2jsonl.py", src).Output()
	if err != nil {
		t.Skipf("python3 converter unavailable: %v", err)
	}
	if err := os.WriteFile(dst, out, 0o644); err != nil {
		t.Fatal(err)
	}
}

// TestPorcupineTestData checks the 102 Jepsen etcd histories and the 6 key-value histories
// that ship with Porcupine. linproof, Porcupine on the converted files, and the verdicts
// recorded in Porcupine's own tests must all agree.
func TestPorcupineTestData(t *testing.T) {
	bin := linproofBin(t)
	dir := porcupineDir(t)
	src, err := os.ReadFile(filepath.Join(dir, "porcupine_test.go"))
	if err != nil {
		t.Skipf("porcupine test source unavailable: %v", err)
	}
	expected := map[string]bool{}
	for _, m := range regexp.MustCompile(`checkJepsen\(t, (\d+), (true|false)\)`).FindAllStringSubmatch(string(src), -1) {
		n, _ := strconv.Atoi(m[1])
		expected[fmt.Sprintf("etcd_%03d", n)] = m[2] == "true"
	}
	for _, name := range []string{"c01-ok", "c01-bad", "c10-ok", "c10-bad", "c50-ok", "c50-bad"} {
		expected[name] = strings.HasSuffix(name, "-ok")
	}
	if len(expected) < 100 {
		t.Fatalf("found only %d expected verdicts", len(expected))
	}

	tmp := t.TempDir()
	byModel := map[string][]string{}
	for name := range expected {
		var log, model string
		if strings.HasPrefix(name, "etcd_") {
			log, model = filepath.Join(dir, "test_data", "jepsen", name+".log"), "cas-register"
		} else {
			log, model = filepath.Join(dir, "test_data", "kv", name+".txt"), "kv"
		}
		dst := filepath.Join(tmp, name+".jsonl")
		convertLog(t, log, dst)
		byModel[model] = append(byModel[model], dst)
	}
	checked := 0
	for model, files := range byModel {
		lv, err := linproofVerdicts(bin, model, files)
		if err != nil {
			t.Fatal(err)
		}
		for _, f := range files {
			name := strings.TrimSuffix(filepath.Base(f), ".jsonl")
			pv, _, err := porcupineVerdict(f, model)
			if err != nil {
				t.Fatal(err)
			}
			got, ok := lv[f]
			switch {
			case !ok:
				t.Errorf("%s: no verdict from linproof", name)
			case got != expected[name]:
				t.Errorf("%s: linproof says %v, Porcupine's tests expect %v", name, got, expected[name])
			case pv != expected[name]:
				t.Errorf("%s: Porcupine on the converted file says %v, its tests expect %v", name, pv, expected[name])
			}
			checked++
		}
	}
	t.Logf("%d real histories: linproof, Porcupine and Porcupine's expectations agree", checked)
}
