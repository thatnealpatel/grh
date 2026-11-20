// Package pimodel compares Pi's selected model with its response receipt.
package pimodel

import "strings"

// Native removes the exe-dev extension's
// final @integration component. Other
// providers have no such alias contract.
func Native(provider, id string) string {
	if strings.HasPrefix(provider, "exe-dev-") {
		if i := strings.LastIndexByte(id, '@'); i > 0 && i < len(id)-1 {
			return id[:i]
		}
	}
	return id
}

func Matches(provider, id, responseProvider, responseID string) bool {
	return provider == responseProvider && (responseID == id || responseID == Native(provider, id))
}
