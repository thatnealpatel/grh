package main

import (
	"context"
	"errors"
	"testing"
	"testing/synctest"
	"time"
)

func TestPauseBetweenCycles(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		start := time.Now()
		if err := pauseBetweenCycles(context.Background()); err != nil {
			t.Fatalf("pause: %v", err)
		}
		if elapsed := time.Since(start); elapsed != 30*time.Minute {
			t.Fatalf("pause lasted %s, want 30m", elapsed)
		}
	})
}

func TestPauseBetweenCyclesCanceled(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())
		defer cancel()
		start := time.Now()
		result := make(chan error, 1)
		go func() { result <- pauseBetweenCycles(ctx) }()
		synctest.Sleep(time.Minute)
		cancel()
		if err := <-result; !errors.Is(err, context.Canceled) {
			t.Fatalf("pause: got %v, want %v", err, context.Canceled)
		}
		if elapsed := time.Since(start); elapsed != time.Minute {
			t.Fatalf("canceled pause lasted %s, want 1m", elapsed)
		}
	})
}
