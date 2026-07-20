# Auditable Agent Coordination

Status: parked on 2026-07-19; revised 2026-07-20 after reviewing agent-deck (`~/agent-deck`). We
are continuing with manual lead/worker handoffs for now. Adopting agent-deck wholesale is rejected:
it is tmux-centric and would displace the zellij-based workflow, and it carries far more surface
(TUI, MCP pooling, chat bridges, watchers) than we need. Its coordination *model*, however, is
better than our original design on two points, adopted below.

## What we want

The useful part of the `.NOTIF_LEAD` / `.NOTIF_WORKER_N` idea is not the files themselves. It is a
small, local coordination system with:

- an explicit autonomy switch (`on`, `paused`, or `stopped`);
- addressed messages between a lead and named workers;
- reliable wakeups, acknowledgements, and retries;
- an append-only, human-readable history with timestamps;
- a concise current-state view; and
- recovery after an agent process or terminal disappears.

`STATUS.md` should remain the human summary of the current workstream. It should not also be the
message queue: concurrent writers, overwritten messages, and ambiguous acknowledgement would make
both roles less reliable.

## What agent-deck actually does

Agent-deck (Go, tmux-based session manager) separates its coordination into layers that map
directly onto our requirements:

- **Registry vs. messages.** SQLite holds only the session registry, a status cache, and
  multi-process polling claims — never messages. The agent-to-agent channel (child→parent
  completion events) is a durable filesystem outbox: fsync'd JSONL per recipient, a write-ahead
  staging file, and a consumed-turn ledger giving at-least-once delivery with exactly-once effects,
  plus last-wins-per-sender flood control and a bounded dead-letter path
  (`internal/session/inbox*.go`).
- **Status from hooks, not scraping.** Agent lifecycle hooks (Claude Code `Stop`,
  `UserPromptSubmit`, etc.) exec a handler that writes a per-session status file;
  a single derivation function turns those into running/waiting/idle/error. tmux pane scraping is
  only a staleness fallback (`internal/sessionstatus`).
- **Delivery at turn boundaries.** The recipient's own Claude Code `Stop` hook drains its inbox
  and, if messages are pending, returns `{"decision": "block", "reason": <messages>}` — pending
  mail becomes the next turn's input with no supervisor process and no injection. A persisted
  counter caps consecutive blocks to prevent loops (`inbox_stophook.go`).
- **Level-triggered correctness, edge-triggered latency.** A periodic heartbeat prompt makes the
  conductor reconcile (drain inbox, scan waiting sessions). An idle-gated, debounced keystroke
  "wake nudge" exists purely to cut latency; the code is explicit that correctness never depends
  on the nudge landing (`inbox_nudge.go`). This is our ".NOTIF files as derived doorbells"
  principle, independently reached.
- **The conductor is just an agent.** Supervision is an ordinary agent session driven by a prompt
  plus a plain CLI (`status --json`, `list --json`, `session output`, `session send`,
  `inbox drain self`), with memory in `state.json` / `task-log.md`. No privileged channel exists.
- **The weak point is keystroke injection.** All live steering is `tmux send-keys`, and despite
  heavy hardening (readiness waits, composer-draft guard, atomic text+Enter, bounded execs) the
  code admits residual races: a send into a pane that turns busy mid-delivery merely queues
  keystrokes, and the chat-bridge's inbound queue is in-memory and lossy on crash.

## Verdict on our original plan

The original conclusion was directionally right — durable log as source of truth, doorbells
advisory, `STATUS.md` kept out of the queue, acks/dedup/history required. Agent-deck validates all
of that. Two pieces of our design should change, and one should not:

1. **Drop the app-server supervisor.** Delivery via the recipient's own `Stop` hook plus a periodic
   heartbeat replaces the supervisor's wakeup role entirely, with no long-running process to
   operate or recover. It also removes the Codex-app-server coupling: Claude Code workers are
   covered by hooks; Codex workers get status via its `notify` hook and delivery via the idle
   doorbell.
2. **Replace the MCP server with a tiny CLI.** Agents already have shells; a `coord` CLI works
   identically from Claude Code, Codex, cron, and the human, needs no server lifecycle, and is
   trivially testable. MCP adds surface without adding capability here.
3. **Keep SQLite as the single store.** Agent-deck hand-rolls outbox/WAL/ledger semantics across
   four file families because it grew incrementally under multi-process writers. One SQLite
   database gives the same ordering, durability, and transactional acknowledgement in far less
   code. Registry, events, and autonomy state live in one inspectable file.

Do not copy: keystroke injection as the primary delivery path (agent-deck's own most-hardened and
still most-fragile component), in-memory queues anywhere, or the chat-platform bridge layer.

## Revised design

One SQLite database plus a small `coord` CLI, delivery through the agents' own hooks, and zellij
only as a latency doorbell:

- **Store.** SQLite tables: `agents` (name, kind, zellij session/pane id, last status, last seen),
  `events` (as before: `id, timestamp, run_id, sender, recipient, kind, payload,
  related_event_id, delivery_state, acknowledged_at`), `control` (autonomy state). Lifecycle
  events (start/exit, assignment, progress, blocked, completion, pause, resume, timeout) are
  ordinary rows; a `coord log` command renders the chronological timeline.
- **CLI.** `coord send <recipient> <message>`, `coord drain [--stop-hook]` (reads by cursor and
  acknowledges transactionally), `coord status`, `coord pause | resume | stop`, `coord log`.
- **Delivery, Claude Code workers/lead.** `Stop` hook runs `coord drain --stop-hook`: with
  autonomy `on` and pending mail it emits `{"decision": "block", "reason": ...}` (with a persisted
  loop cap, per agent-deck); `SessionStart`/`UserPromptSubmit`/`Stop` also stamp status rows,
  giving running/waiting detection without scraping.
- **Delivery, Codex workers.** `notify` hook stamps turn-complete status; steering an idle Codex
  session uses the doorbell below.
- **Doorbell.** For a recipient idle at its prompt (no turn ending, so no hook fires), nudge via
  `zellij action write-chars --pane-id <id>` with a fixed "[INBOX] run coord drain" line —
  idle-gated and debounced, and never authoritative. zellij 0.44.3 supports `--pane-id` targeting
  on `write-chars` and `dump-screen` and stable IDs from `list-panes`, so the tmux primitives
  agent-deck relies on all exist; `dump-screen` remains available as a last-resort status
  fallback.
- **Heartbeat.** Optional systemd timer that nudges the lead only when it is idle and mail or
  waiting workers exist — the level-triggered backstop for anything the hooks miss.

## Safe implementation order

1. SQLite schema, `coord` CLI (send/drain/status/log), autonomy switch enforced inside the CLI.
   Test ordering, restart recovery, and duplicate delivery before any automation.
2. Claude Code hook integration: status stamping plus drain-on-Stop with the loop cap. This alone
   makes lead/worker mail work with zero new processes.
3. zellij doorbell and the optional heartbeat timer; Codex `notify` stamping. Doorbells stay
   derived hints, never authoritative state.

## Alternatives considered

| Option | Useful property | Why it is not the default here |
| --- | --- | --- |
| agent-deck wholesale | Complete, battle-tested implementation of this model | tmux-centric (displaces zellij workflow); TUI/bridges/pooling surface far beyond our need; steering rests on keystroke injection |
| Codex built-in subagents | Direct routing inside a live lead thread | Does not by itself provide the desired cross-process durable audit protocol |
| Codex app-server supervisor | Thread lifecycle and streamed notifications without TUI automation | Superseded: hook-based delivery + heartbeat needs no supervisor process and covers Claude Code too |
| MCP Tasks | Standard task state and polling | The Tasks facility is experimental and is not a complete push mailbox |
| A2A | Tasks, messages, artifacts, streaming, and push notifications | More protocol and deployment surface than a single-host workflow needs |
| Redis Streams | Durable ordered streams and consumer groups | Requires a service and operational lifecycle that SQLite avoids |
| LangGraph | Checkpoints, persistence, and interrupt/resume workflows | Would make LangGraph the workflow runtime rather than lightly supervising the agents |
| Temporal | Strong durable workflow execution | Disproportionately heavy for a local lead and a few workers |
| `STATUS.md` plus `.NOTIF_*` | Transparent and almost free | Not reliable enough to be the source of truth |

## Current references

- [agent-deck](https://github.com/asheshgoplani/agent-deck) — local copy at `~/agent-deck`; see
  `internal/session/inbox*.go` (durable outbox), `internal/sessionstatus` (hook-derived status),
  `conductor/conductor-claude.md` (conductor prompt and CLI surface)
- [Codex app-server protocol](https://learn.chatgpt.com/docs/app-server)
- [Model Context Protocol Tasks](https://modelcontextprotocol.io/specification/2025-11-25/basic/utilities/tasks)
- [A2A protocol specification](https://a2a-protocol.org/latest/specification/)
- [Redis Streams](https://redis.io/docs/latest/develop/data-types/streams/)
- [LangGraph persistence](https://docs.langchain.com/oss/python/langgraph/persistence)
