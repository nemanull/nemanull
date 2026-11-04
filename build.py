#!/usr/bin/env python3
"""Render the profile card: card-dark.svg, card-light.svg and card.md (the same card as text).

The look follows Andrew6rant's profile card (github.com/Andrew6rant): portrait on the left, a
neofetch-style panel on the right, GitHub's colours, no window chrome.
profile.toml decides what the card says and portrait.txt is the ASCII portrait. The optional
portrait.colors says which part of the picture each character belongs to (h hair, s skin,
g glasses, c clothes, m mouth/nose) so each theme can colour it; without it the portrait is
one colour. The live numbers come from the GitHub GraphQL API and the blog's RSS feed.
Lines-of-code totals are cached per repository in cache/stats.json, so a daily run only
re-walks repositories whose default branch moved.

    python3 build.py              # token from GH_TOKEN / GITHUB_TOKEN, else `gh auth token`
    python3 build.py --offline    # reuse the cached numbers, no network
    python3 build.py --md         # only write card.md, leave the SVGs alone (for reviewing)
"""
import base64
import datetime as dt
import email.utils
import json
import os
import pathlib
import re
import subprocess
import sys
import time
import tomllib
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape, quoteattr

ROOT = pathlib.Path(__file__).resolve().parent
CACHE = ROOT / "cache" / "stats.json"
API = "https://api.github.com/graphql"

# Layout grid, as on Andrew6rant's card: 16 px text on 20 px lines for both portrait and panel,
# 15 px left margin, first baseline 30 px from the top. Every glyph of the embedded font
# (DejaVu Sans Mono) is 1233/2048 em wide, and this grid keeps the portrait's proportions.
# card.md uses the same grid, column for column.
ADVANCE = 1233 / 2048
FONT, LINE = 16, 20
LEFT, RIGHT = 15, 20                      # side margins
TOP, BOTTOM = 30, 20                      # first baseline from the top, bottom edge from the last
GAP_COLS = 2                              # blank columns between portrait and panel
PANEL_COLS = 62                           # ". " + 60 columns of `Key: ..... value`
RULE_END = "-—-"                          # how the header rules end: `name -————————-—-`
# Commits that touch more lines than this are vendored deps / generated files / notebook
# outputs, not code anyone wrote, so they're left out of the lines-of-code total.
MAX_COMMIT_LINES = 10_000

# GitHub's own palette, the same colours Andrew6rant's card uses.
THEMES = {
    "dark": dict(
        bg="#161b22", text="#c9d1d9", key="#ffa657", value="#a5d6ff", dots="#616e7f",
        add="#3fb950", rem="#f85149",
        # only used with portrait.colors: hair dimmer than skin, so it reads as dark hair
        parts=dict(h="#787069", s="#f0dccd", g="#6f7d92", c="#c9d1d9", m="#d49f8c"),
    ),
    "light": dict(
        bg="#f6f8fa", text="#24292f", key="#953800", value="#0a3069", dots="#c2cfde",
        add="#1a7f37", rem="#cf222e",
        parts=dict(h="#2b2522", s="#8f6c5e", g="#2f3a48", c="#6e7781", m="#9a4a3c"),
    ),
}


# ---------------------------------------------------------------- GitHub API

def token():
    for name in ("GH_TOKEN", "GITHUB_TOKEN"):
        if os.environ.get(name):
            return os.environ[name]
    return subprocess.run(["gh", "auth", "token"], capture_output=True, text=True, check=True).stdout.strip()


def gql(query, **variables):
    body = json.dumps({"query": query, "variables": variables}).encode()
    headers = {"Authorization": f"bearer {token()}", "User-Agent": "profile-card-build"}
    for attempt in range(5):
        try:
            req = urllib.request.Request(API, data=body, headers=headers)
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = json.load(resp)
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError) as e:
            if attempt == 4 or getattr(e, "code", 502) < 500:
                raise
            time.sleep(2 ** attempt)
            continue
        if data.get("errors"):
            raise RuntimeError(data["errors"])
        return data["data"]


OVERVIEW = """
query($login: String!, $after: String, $privacy: RepositoryPrivacy) {
  user(login: $login) {
    id createdAt
    followers { totalCount }
    repositories(ownerAffiliations: OWNER, privacy: $privacy, isFork: false, first: 100, after: $after) {
      totalCount
      pageInfo { hasNextPage endCursor }
      nodes { nameWithOwner stargazerCount defaultBranchRef { target { oid } } }
    }
    repositoriesContributedTo(first: 100, privacy: $privacy, includeUserRepositories: false,
        contributionTypes: [COMMIT, PULL_REQUEST, REPOSITORY, PULL_REQUEST_REVIEW]) {
      totalCount
      nodes { nameWithOwner defaultBranchRef { target { oid } } }
    }
  }
}"""

HISTORY = """
query($owner: String!, $name: String!, $id: ID!, $after: String) {
  repository(owner: $owner, name: $name) {
    defaultBranchRef { target { ... on Commit {
      history(first: 100, after: $after, author: {id: $id}) {
        totalCount
        pageInfo { hasNextPage endCursor }
        nodes { additions deletions }
      }
    } } }
  }
}"""


def contributions(login, created, now):
    """Contribution totals (what the green calendar counts): all-time, past year, and commits."""
    parts = ["past: contributionsCollection { contributionCalendar { totalContributions } }"]
    for year in range(created.year, now.year + 1):
        start = max(created, dt.datetime(year, 1, 1, tzinfo=dt.UTC))
        end = min(now, dt.datetime(year, 12, 31, 23, 59, 59, tzinfo=dt.UTC))
        parts.append(f'y{year}: contributionsCollection(from: "{start:%Y-%m-%dT%H:%M:%SZ}", '
                     f'to: "{end:%Y-%m-%dT%H:%M:%SZ}") {{ totalCommitContributions '
                     f'restrictedContributionsCount contributionCalendar {{ totalContributions }} }}')
    user = gql(f'query($login: String!) {{ user(login: $login) {{ {" ".join(parts)} }} }}', login=login)["user"]
    past = user.pop("past")["contributionCalendar"]["totalContributions"]
    total = sum(y["contributionCalendar"]["totalContributions"] for y in user.values())
    commits = sum(y["totalCommitContributions"] + y["restrictedContributionsCount"] for y in user.values())
    return total, past, commits


def repo_loc(name_with_owner, head, uid, cached):
    if cached and cached.get("oid") == head and cached.get("max") == MAX_COMMIT_LINES:
        return cached
    owner, name = name_with_owner.split("/")
    add = rem = commits = 0
    after = None
    while True:
        repo = gql(HISTORY, owner=owner, name=name, id=uid, after=after)["repository"]
        history = repo["defaultBranchRef"]["target"]["history"]
        commits = history["totalCount"]
        for node in history["nodes"]:
            if node["additions"] + node["deletions"] <= MAX_COMMIT_LINES:
                add += node["additions"]
                rem += node["deletions"]
        if not history["pageInfo"]["hasNextPage"]:
            break
        after = history["pageInfo"]["endCursor"]
    return {"oid": head, "max": MAX_COMMIT_LINES, "additions": add, "deletions": rem, "commits": commits}


def fetch_stats(login, cache, include_private=False):
    now = dt.datetime.now(dt.UTC).replace(microsecond=0)
    privacy = None if include_private else "PUBLIC"
    owned, after = [], None
    while True:
        user = gql(OVERVIEW, login=login, after=after, privacy=privacy)["user"]
        page = user["repositories"]
        owned += page["nodes"]
        if not page["pageInfo"]["hasNextPage"]:
            break
        after = page["pageInfo"]["endCursor"]
    created = dt.datetime.fromisoformat(user["createdAt"].replace("Z", "+00:00"))
    contributed = user["repositoriesContributedTo"]

    repos = {}
    for r in owned + contributed["nodes"]:
        if r["defaultBranchRef"]:  # empty repositories have no branch
            repos[r["nameWithOwner"]] = r["defaultBranchRef"]["target"]["oid"]
    loc = {}
    for nwo, head in sorted(repos.items()):
        try:
            loc[nwo] = repo_loc(nwo, head, user["id"], cache.get("loc", {}).get(nwo))
        except Exception as e:  # one flaky repo shouldn't sink the card; keep its old numbers
            print(f"warning: {nwo}: {e}", file=sys.stderr)
            if nwo in cache.get("loc", {}):
                loc[nwo] = cache["loc"][nwo]

    total_contrib, past_year, commits = contributions(login, created, now)
    return {
        "updated": now.isoformat(),
        "created": user["createdAt"],
        "repos": page["totalCount"],
        "contributed": contributed["totalCount"],
        "stars": sum(r["stargazerCount"] for r in owned),
        "followers": user["followers"]["totalCount"],
        "commits": commits,
        "contributions": total_contrib,
        "past_year": past_year,
        "additions": sum(v["additions"] for v in loc.values()),
        "deletions": sum(v["deletions"] for v in loc.values()),
        "loc": loc,
    }


# ---------------------------------------------------------------- blog

def fetch_blog(url):
    """Post count and the newest post's title from the blog's RSS feed."""
    req = urllib.request.Request(url, headers={"User-Agent": "profile-card-build"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        items = ET.fromstring(resp.read()).find("channel").findall("item")

    def published(item):
        try:
            return email.utils.parsedate_to_datetime(item.findtext("pubDate")).timestamp()
        except (TypeError, ValueError):
            return 0.0

    newest = max(items, key=published)  # ties keep feed order, which lists newest first
    return {"posts": len(items), "latest": " ".join(newest.findtext("title").split())}


# ---------------------------------------------------------------- text layout

def since(start, today):
    years, months, days = today.year - start.year, today.month - start.month, today.day - start.day
    if days < 0:
        months -= 1
        days += (today.replace(day=1) - dt.timedelta(days=1)).day
    if months < 0:
        years, months = years - 1, months + 12
    unit = lambda n, word: f"{n} {word}{'' if n == 1 else 's'}"
    return f"{unit(years, 'year')}, {unit(months, 'month')}, {unit(days, 'day')}"


DANGLING = {"a", "an", "and", "at", "for", "in", "of", "on", "or", "the", "to", "with"}


# Panel lines are lists of (text, css class) segments: t plain text, k key, v value, d dots,
# a added lines, x removed lines.

def fit(value, room):
    """Cut a value that's longer than `room` at a word and add "..."."""
    if len(value) <= room:
        return value
    words = value[: room - 2].split(" ")
    words = words[:-1] if len(words) > 1 else [value[: room - 3]]  # drop the half-cut word
    while len(words) > 1 and words[-1].lower() in DANGLING:
        words.pop()
    return " ".join(words).rstrip(" ,;:-") + "..."


def key_spans(key):
    """`Languages.Real`: the words in the key colour, the dots between them plain."""
    out = []
    for i, word in enumerate(key.split(".")):
        out += [(".", "t")] * (i > 0) + [(word, "k")]
    return out


def value_spans(value):
    """A value in the value colour, except `{Key: n}` groups, which are coloured as key and value."""
    out = []
    for piece in re.split(r"(\{[^{}:]+: [^{}]+\})", value):
        group = re.fullmatch(r"\{([^{}:]+): ([^{}]+)\}", piece)
        if group:
            out += [("{", "t"), (group[1], "k"), (": ", "t"), (group[2], "v"), ("}", "t")]
        elif piece:
            out.append((piece, "v"))
    return out


def leader(key, value, width):
    """`Key: ........ value`, exactly `width` characters long. `value` is text or segments."""
    if isinstance(value, str):
        value = value_spans(fit(value, width - len(key) - 4))
    dots = width - len(key) - 3 - sum(len(text) for text, _ in value)
    return [*key_spans(key), (":", "t"), (" " + "." * max(dots, 1) + " ", "d"), *value]


def rule(label, width):
    """`label -————————-—-`, exactly `width` characters long."""
    return [(label + " -" + "—" * (width - len(label) - 2 - len(RULE_END)) + RULE_END, "t")]


def panel_lines(cfg, stats, today):
    W = PANEL_COLS - 2  # the `Key: ... value` part, after the ". " that starts every line
    dot = [(". ", "d")]
    fmt = lambda n: f"{n:,}"
    values = {"posts": "?", "latest": "?", **stats.get("blog", {}),
              "uptime": since(dt.date.fromisoformat(str(cfg["uptime_since"])), today)}

    lines = [rule(cfg["header"], PANEL_COLS)]
    for block in cfg["block"]:
        if block.get("title"):
            lines += [[], rule("- " + block["title"], PANEL_COLS)]
        elif len(lines) > 1:
            lines.append(dot)  # blank lines between untitled blocks keep their dot
        for key, value in block.get("lines", []):
            lines.append(dot + leader(key, value.format(**values), W))
        rows = block.get("stats", [])
        nums = {k: fmt(v) for k, v in stats.items() if isinstance(v, int)}
        pairs = [[(k, v.format(**nums)) for k, v in row if v != "{loc}"] for row in rows]
        left = max((len(r[0][0]) + len(r[0][1]) + 7 for r in pairs if len(r) == 2), default=0)
        for row, cells in zip(rows, pairs):
            if row[0][1] == "{loc}":
                net = stats["additions"] - stats["deletions"]
                lines.append(dot + leader(row[0][0], [
                    (fmt(net), "v"), (" ( ", "t"), (fmt(stats["additions"]) + "++", "a"), (", ", "t"),
                    (fmt(stats["deletions"]) + "--", "x"), (" )", "t")], W))
            elif len(cells) == 2:  # two columns, separators aligned down the block
                (lk, lv), (rk, rv) = cells
                lines.append(dot + leader(lk, lv, left) + [(" | ", "t")] + leader(rk, rv, W - left - 3))
            else:
                lines.append(dot + leader(*cells[0], W))
    return lines


# ---------------------------------------------------------------- SVG

def art_spans(row, codes):
    """One <tspan> per run of characters from the same part of the picture."""
    if not codes:
        return escape(row)
    out, run, cur = [], "", None
    for ch, code in zip(row, codes.ljust(len(row), ".")):
        code = cur if ch == " " or code == "." else code  # spaces join whatever run they're in
        if code != cur and run:
            out.append(f'<tspan class="p{cur}">{escape(run)}</tspan>' if cur else escape(run))
            run = ""
        cur, run = code, run + ch
    if run:
        out.append(f'<tspan class="p{cur}">{escape(run)}</tspan>' if cur else escape(run))
    return "".join(out)


def render(theme, cfg, art, colors, lines):
    t = THEMES[theme]
    cw = FONT * ADVANCE
    panel_x = LEFT + (max(len(row) for row in art) + GAP_COLS) * cw
    width = round(panel_x + PANEL_COLS * cw + RIGHT)
    height = TOP + (max(len(art), len(lines)) - 1) * LINE + BOTTOM

    font = base64.b64encode((ROOT / "assets" / "mono.woff2").read_bytes()).decode()
    css = f"""
@font-face {{ font-family: 'CardMono'; src: url(data:font/woff2;base64,{font}) format('woff2'); }}
text {{ font-family: 'CardMono', 'DejaVu Sans Mono', Menlo, Consolas, monospace; font-size: {FONT}px;
  white-space: pre; fill: {t['text']}; }}
{" ".join(f".p{k} {{ fill: {v}; }}" for k, v in t["parts"].items())}
.k {{ fill: {t['key']}; }} .v {{ fill: {t['value']}; }} .d {{ fill: {t['dots']}; }}
.a {{ fill: {t['add']}; }} .x {{ fill: {t['rem']}; }}
"""
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" xml:space="preserve" width="{width}" height="{height}" '
           f'viewBox="0 0 {width} {height}" role="img" aria-label={quoteattr(cfg["alt"])}>',
           f"<title>{escape(cfg['alt'])}</title>",
           f"<style>{css}</style>",
           f'<rect width="{width}" height="{height}" rx="15" fill="{t["bg"]}"/>']
    for i, row in enumerate(art):
        if row.strip():
            codes = colors[i] if colors and i < len(colors) else ""
            out.append(f'<text x="{LEFT}" y="{TOP + i * LINE}">{art_spans(row, codes)}</text>')
    for i, segs in enumerate(lines):
        if segs:
            spans = "".join(escape(s) if c == "t" else f'<tspan class="{c}">{escape(s)}</tspan>' for s, c in segs)
            out.append(f'<text x="{panel_x:.2f}" y="{TOP + i * LINE}">{spans}</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def text_card(cfg, art, lines):
    """card.md: the card as plain text in a code block, on the same grid as the SVG."""
    left_cols = max(len(row) for row in art) + GAP_COLS
    body = []
    for i in range(max(len(art), len(lines))):
        left = art[i] if i < len(art) else ""
        right = "".join(text for text, _ in lines[i]) if i < len(lines) else ""
        body.append((left.ljust(left_cols) + right).rstrip())
    return "\n".join([
        "```text",
        *body,
        "```",
        "",
    ])


def main():
    cfg = tomllib.loads((ROOT / "profile.toml").read_text())
    art = (ROOT / "portrait.txt").read_text().rstrip("\n").split("\n")
    colors_file = ROOT / "portrait.colors"
    colors = colors_file.read_text().rstrip("\n").split("\n") if colors_file.exists() else None
    cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    stats = cache
    if "--offline" not in sys.argv:
        try:
            stats = fetch_stats(cfg["user"], cache, cfg.get("include_private", False))
        except Exception as e:
            if not cache:
                raise
            # keep yesterday's numbers rather than skipping the render (uptime still moves)
            print(f"::warning::GitHub stats fetch failed, using cached numbers: {e}")
        if cfg.get("blog_feed"):
            try:
                stats["blog"] = fetch_blog(cfg["blog_feed"])
            except Exception as e:
                print(f"::warning::blog feed fetch failed, using cached numbers: {e}")
                if "blog" in cache:
                    stats["blog"] = cache["blog"]
        CACHE.parent.mkdir(exist_ok=True)
        CACHE.write_text(json.dumps(stats, indent=1, sort_keys=True) + "\n")
    lines = panel_lines(cfg, stats, dt.date.today())
    (ROOT / "card.md").write_text(text_card(cfg, art, lines), encoding="utf-8")
    if "--md" not in sys.argv:
        for theme in THEMES:
            (ROOT / f"card-{theme}.svg").write_text(render(theme, cfg, art, colors, lines), encoding="utf-8")
    print(f"repos {stats['repos']} (+{stats['contributed']}) · stars {stats['stars']} · commits {stats['commits']} "
          f"· followers {stats['followers']} · loc +{stats['additions']:,} -{stats['deletions']:,}"
          f" · blog {stats.get('blog', {}).get('posts', '?')} posts")


if __name__ == "__main__":
    main()
