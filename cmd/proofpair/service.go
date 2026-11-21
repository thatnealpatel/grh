package main

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
)

func checkService(ctx context.Context) error {
	if os.Getuid() == 0 || os.Getuid() != os.Geteuid() {
		return fmt.Errorf("run as the dedicated unprivileged VM user")
	}
	membership, err := os.ReadFile("/proc/self/cgroup")
	if err != nil {
		return err
	}
	if strings.TrimSpace(string(membership)) != "0::"+cgroup {
		return fmt.Errorf("must run inside the dedicated systemd service on unified cgroup v2")
	}
	bus := fmt.Sprintf("/run/user/%d/bus", os.Getuid())
	if _, err := os.Lstat(bus); !os.IsNotExist(err) && !os.IsPermission(err) {
		return fmt.Errorf("Yah must not be able to migrate shells to a systemd user scope: %s", bus)
	}
	want := map[string]string{
		"MainPID": strconv.Itoa(os.Getpid()), "ControlGroup": cgroup,
		"Type": "exec", "Restart": "no", "Delegate": "no", "PrivateTmp": "yes",
		"NoNewPrivileges": "yes", "ProtectControlGroups": "yes", "ProtectSystem": "strict",
		"RuntimeMaxUSec": "2h", "TimeoutStopUSec": "10s", "RuntimeRandomizedExtraUSec": "0",
		"TimeoutStopFailureMode": "kill", "KillMode": "control-group", "SendSIGKILL": "yes",
	}
	args := []string{"--system", "show", unit}
	for key := range want {
		args = append(args, "--property="+key)
	}
	cmd := exec.CommandContext(ctx, "/usr/bin/systemctl", args...)
	cmd.Env = []string{"LC_ALL=C", "SYSTEMD_BUS_TIMEOUT=5s"}
	data, err := cmd.Output()
	if err != nil {
		return fmt.Errorf("read trusted systemd service properties: %w", err)
	}
	return checkProperties(want, string(data))
}

func checkProperties(want map[string]string, data string) error {
	seen := map[string]bool{}
	for line := range strings.Lines(data) {
		key, value, _ := strings.Cut(strings.TrimSuffix(line, "\n"), "=")
		if expected, ok := want[key]; !ok || seen[key] || value != expected {
			return fmt.Errorf("unexpected systemd property: %s", key)
		}
		seen[key] = true
	}
	if len(seen) != len(want) {
		return fmt.Errorf("missing systemd properties")
	}
	return nil
}
