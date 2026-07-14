#!/usr/bin/env python3
"""Wavy flag + pentagon logo candidates, monochrome."""
import math
from PIL import Image, ImageDraw

OUT = "."
S = 4
W = H = 1024
INK = (26, 28, 32, 255)      # near-black
PAPER = (255, 255, 255, 255)

def wave(x, fx0, fx1, amp, freq, phase):
    t = (x - fx0) / (fx1 - fx0)
    return amp * math.sin(2*math.pi*freq*t + phase)

def flag_polygon(fx0, fx1, ytop, ybot, amp, freq, phase, steps=80):
    top, bot = [], []
    for i in range(steps + 1):
        x = fx0 + (fx1 - fx0) * i / steps
        o = wave(x, fx0, fx1, amp, freq, phase)
        top.append((x, ytop + o)); bot.append((x, ybot + o))
    return top + bot[::-1]

def pentagon_pts(cx, cy, R, rot=-math.pi/2):
    return [(cx + R*math.cos(rot + 2*math.pi*k/5),
             cy + R*math.sin(rot + 2*math.pi*k/5)) for k in range(5)]

def new():
    img = Image.new("RGBA", (W*S, H*S), PAPER)
    return img, ImageDraw.Draw(img)

def finish(img, name):
    img.resize((W, H), Image.LANCZOS).save(f"{OUT}/{name}.png")
    print("wrote", name)

def draw_pole(d, x, y0, y1, w, col=INK, knob=True):
    d.rectangle([x-w, y0, x+w, y1], fill=col)
    if knob:
        d.ellipse([x-w*2, y0-w*3, x+w*2, y0+w], fill=col)

# 1: solid flag on pole, white pentagon graph (nodes + edges)
def p1():
    img, d = new(); sc = lambda v: int(v*S)
    px = sc(170); draw_pole(d, px, sc(120), sc(960), sc(13))
    fx0, fx1, yt, yb = px, sc(940), sc(200), sc(700); amp, fr, ph = sc(40), 1.25, 1.0
    d.polygon(flag_polygon(fx0, fx1, yt, yb, amp, fr, ph), fill=INK)
    cx, cy = sc(560), (yt+yb)//2; R = sc(185)
    P = [(x, y + wave(x, fx0, fx1, amp, fr, ph)) for (x, y) in pentagon_pts(cx, cy, R)]
    for k in range(5):
        d.line([P[k], P[(k+1) % 5]], fill=PAPER, width=sc(8))
    for (x, y) in P:
        r = sc(20); d.ellipse([x-r, y-r, x+r, y+r], fill=PAPER)
    finish(img, "pf1")

# 2: solid flag, NO pole, white pentagon outline only
def p2():
    img, d = new(); sc = lambda v: int(v*S)
    fx0, fx1, yt, yb = sc(110), sc(910), sc(300), sc(800); amp, fr, ph = sc(46), 1.2, 0.6
    d.polygon(flag_polygon(fx0, fx1, yt, yb, amp, fr, ph), fill=INK)
    cx, cy = (fx0+fx1)//2, (yt+yb)//2; R = sc(190)
    P = [(x, y + wave(x, fx0, fx1, amp, fr, ph)) for (x, y) in pentagon_pts(cx, cy, R)]
    for k in range(5):
        d.line([P[k], P[(k+1) % 5]], fill=PAPER, width=sc(12))
    finish(img, "pf2")

# 3: line-art flag outline on pole, ink pentagon graph
def p3():
    img, d = new(); sc = lambda v: int(v*S)
    px = sc(170); draw_pole(d, px, sc(120), sc(960), sc(12), knob=True)
    fx0, fx1, yt, yb = px, sc(940), sc(200), sc(700); amp, fr, ph = sc(40), 1.25, 1.0
    poly = flag_polygon(fx0, fx1, yt, yb, amp, fr, ph)
    d.line(poly + [poly[0]], fill=INK, width=sc(9), joint="curve")
    cx, cy = sc(560), (yt+yb)//2; R = sc(185)
    P = [(x, y + wave(x, fx0, fx1, amp, fr, ph)) for (x, y) in pentagon_pts(cx, cy, R)]
    for k in range(5):
        d.line([P[k], P[(k+1) % 5]], fill=INK, width=sc(8))
    for (x, y) in P:
        r = sc(19); d.ellipse([x-r, y-r, x+r, y+r], fill=INK)
    finish(img, "pf3")

# 4: solid flag on pole, white pentagram star
def p4():
    img, d = new(); sc = lambda v: int(v*S)
    px = sc(170); draw_pole(d, px, sc(120), sc(960), sc(13))
    fx0, fx1, yt, yb = px, sc(940), sc(200), sc(700); amp, fr, ph = sc(40), 1.25, 1.0
    d.polygon(flag_polygon(fx0, fx1, yt, yb, amp, fr, ph), fill=INK)
    cx, cy = sc(560), (yt+yb)//2; R = sc(195)
    P = [(x, y + wave(x, fx0, fx1, amp, fr, ph)) for (x, y) in pentagon_pts(cx, cy, R)]
    order = [0, 2, 4, 1, 3]  # pentagram
    for k in range(5):
        d.line([P[order[k]], P[order[(k+1) % 5]]], fill=PAPER, width=sc(8))
    finish(img, "pf4")

# 5: solid flag, no pole, white pentagon outline + vertex dots
def p5():
    img, d = new(); sc = lambda v: int(v*S)
    fx0, fx1, yt, yb = sc(110), sc(910), sc(300), sc(800); amp, fr, ph = sc(46), 1.2, 0.6
    d.polygon(flag_polygon(fx0, fx1, yt, yb, amp, fr, ph), fill=INK)
    cx, cy = (fx0+fx1)//2, (yt+yb)//2; R = sc(190)
    P = [(x, y + wave(x, fx0, fx1, amp, fr, ph)) for (x, y) in pentagon_pts(cx, cy, R)]
    for k in range(5):
        d.line([P[k], P[(k+1) % 5]], fill=PAPER, width=sc(9))
    for (x, y) in P:
        r = sc(22); d.ellipse([x-r, y-r, x+r, y+r], fill=PAPER)
    finish(img, "pf5")

for fn in (p1, p2, p3, p4, p5):
    fn()
print("done")
