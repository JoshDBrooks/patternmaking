"""Generate a multi-size .ico for the Patternmaking app."""
from PIL import Image, ImageDraw


def rounded_rect(draw, box, radius, fill):
    draw.rounded_rectangle(box, radius=radius, fill=fill)


def render(size):
    scale = size / 256.0
    img = Image.new('RGBA', (size, size), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)

    def s(v):
        return v * scale

    # Background rounded square (accent blue)
    rounded_rect(d, [s(8), s(8), s(248), s(248)], radius=s(48), fill=(10, 132, 255, 255))

    # White pattern-piece silhouette: a panel with one curved side
    # (approx a shorts/bodice front). Points in 256-space.
    outline = [
        (70, 60), (170, 60),           # waist (top)
        (188, 150),                    # side seam out to hip
        (150, 205),                    # hem
        (95, 205),                     # hem inner
    ]
    pts = [(s(x), s(y)) for x, y in outline]
    d.polygon(pts, fill=(255, 255, 255, 255))

    # Crotch-curve suggestion: a darker notch arc on the lower-left
    d.pieslice([s(40), s(150), s(120), s(240)], start=270, end=360,
               fill=(10, 132, 255, 255))

    # Grain-line arrow down the middle
    ax = s(128)
    d.line([(ax, s(85)), (ax, s(180))], fill=(10, 132, 255, 255), width=max(1, int(s(6))))
    # arrow heads
    ah = s(12)
    d.line([(ax, s(85)), (ax - ah, s(85) + ah)], fill=(10, 132, 255, 255), width=max(1, int(s(6))))
    d.line([(ax, s(85)), (ax + ah, s(85) + ah)], fill=(10, 132, 255, 255), width=max(1, int(s(6))))
    d.line([(ax, s(180)), (ax - ah, s(180) - ah)], fill=(10, 132, 255, 255), width=max(1, int(s(6))))
    d.line([(ax, s(180)), (ax + ah, s(180) - ah)], fill=(10, 132, 255, 255), width=max(1, int(s(6))))

    return img


sizes = [16, 24, 32, 48, 64, 128, 256]
imgs = [render(sz) for sz in sizes]
# Save as .ico with all sizes embedded (use the largest as base)
imgs[-1].save('pattern.ico', format='ICO',
              sizes=[(sz, sz) for sz in sizes])
print('wrote pattern.ico')
