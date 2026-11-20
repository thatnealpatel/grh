package mathlane

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"strings"
	"unicode/utf8"
)

const maxReplyBytes = 16 << 10

func meaningful(s string) bool { return strings.TrimSpace(s) != "" }

// Require a single flat JSON object, without
// prose fences, unknown fields or duplicate
// decisions. A broken response is not a
// mathematical rejection.
func decodeReply(data []byte, into any) error {
	if len(data) > maxReplyBytes || !utf8.Valid(data) {
		return errors.New("invalid reply size or encoding")
	}
	dec := json.NewDecoder(bytes.NewReader(data))
	if tok, err := dec.Token(); err != nil || tok != json.Delim('{') {
		return errors.New("expected a JSON object")
	}
	seen := make(map[string]bool)
	for dec.More() {
		tok, err := dec.Token()
		if err != nil {
			return err
		}
		name, ok := tok.(string)
		if !ok || seen[strings.ToLower(name)] {
			return fmt.Errorf("invalid or repeated reply field %q", tok)
		}
		seen[strings.ToLower(name)] = true
		tok, err = dec.Token()
		if err != nil {
			return err
		}
		switch tok.(type) {
		case string, bool:
		default:
			return fmt.Errorf("reply field %q must be a string or boolean", name)
		}
	}
	if _, err := dec.Token(); err != nil {
		return err
	}
	if _, err := dec.Token(); err != io.EOF {
		return errors.New("unexpected text after reply")
	}
	dec = json.NewDecoder(bytes.NewReader(data))
	dec.DisallowUnknownFields()
	return dec.Decode(into)
}
