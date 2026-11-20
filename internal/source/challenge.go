package source

import (
	"context"
	"crypto/rand"
	"fmt"
	"image"
	"image/draw"
	"image/png"
	"math/big"
	"os"
	"path/filepath"
	"slices"
)

func challengePages(ctx context.Context, dir string, pages []*image.RGBA) (paths, codes []string, err error) {
	for i, page := range pages {
		var code string
		for {
			if err := ctx.Err(); err != nil {
				return nil, nil, err
			}
			n, err := rand.Int(rand.Reader, big.NewInt(1_000_000_000_000))
			if err != nil {
				return nil, nil, fmt.Errorf("generate page challenge: %w", err)
			}
			code = fmt.Sprintf("%012d", n.Int64())
			if !slices.Contains(codes, code) {
				break
			}
		}
		path := fmt.Sprintf("page-%d.png", i+1)
		if err := writeChallenge(filepath.Join(dir, path), page, code); err != nil {
			return nil, nil, fmt.Errorf("write challenged image %d: %w", i+1, err)
		}
		paths, codes = append(paths, path), append(codes, code)
	}
	return paths, codes, nil
}

func writeChallenge(path string, page *image.RGBA, code string) error {
	// Append a separate white strip. The
	// complete opaque RGB8 page above it
	// is copied pixel for pixel, including
	// all four margins.
	bounds := page.Bounds()
	strip := image.Rect(bounds.Min.X, bounds.Max.Y, bounds.Max.X, bounds.Max.Y+144)
	img := image.NewRGBA(bounds.Union(strip))
	draw.Draw(img, bounds, page, bounds.Min, draw.Src)
	draw.Draw(img, strip, image.White, image.Point{}, draw.Src)

	// Large seven-segment digits remain
	// visible when the full page is scaled
	// for viewing. The PNG encoder emits
	// no challenge metadata.
	segments := [...]image.Rectangle{
		image.Rect(12, 0, 36, 12),  // top
		image.Rect(36, 12, 48, 42), // upper right
		image.Rect(36, 54, 48, 84), // lower right
		image.Rect(12, 84, 36, 96), // bottom
		image.Rect(0, 54, 12, 84),  // lower left
		image.Rect(0, 12, 12, 42),  // upper left
		image.Rect(12, 42, 36, 54), // center
	}
	masks := [...]uint8{0x3f, 0x06, 0x5b, 0x4f, 0x66, 0x6d, 0x7d, 0x07, 0x7f, 0x6f}
	const pitch = 72
	x := strip.Min.X + (strip.Dx()-(len(code)-1)*pitch-48)/2
	for i := range len(code) {
		origin := image.Pt(x+i*pitch, strip.Min.Y+24)
		for j, segment := range segments {
			if masks[code[i]-'0']&(1<<j) != 0 {
				draw.Draw(img, segment.Add(origin), image.Black, image.Point{}, draw.Src)
			}
		}
	}

	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
	if err != nil {
		return err
	}
	err = png.Encode(f, img)
	closeErr := f.Close()
	if err != nil {
		return err
	}
	return closeErr
}
