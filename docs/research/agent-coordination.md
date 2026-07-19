# Auditable Agent Coordination

Status: parked on 2026-07-19. We are continuing with manual lead/worker handoffs for now.

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

## Conclusion

If we resume this work, the best fit is a thin local supervisor using the Codex app-server protocol
and a SQLite append-only event log. Within one live Codex thread, built-in subagent routing remains
the simplest way to assign and receive work. The supervisor is for persistence and wakeup across
turns or processes, not a replacement for that routing.

Expose the event log to agents through a very small local MCP server:

- `coord.send(recipient, message)`
- `coord.inbox(agent, after_cursor)`
- `coord.ack(agent, event_id)`
- `coord.status()`
- `coord.pause()` / `coord.resume()` / `coord.stop()`
- `coord.history(after_cursor, filters)`

Codex app-server already exposes thread lifecycle, turn start/steering, and streamed notifications,
so the supervisor would not need to automate a terminal UI. SQLite supplies ordering,
transactions, durable acknowledgements, and an inspectable history without another service.

An event should minimally record:

```text
id, timestamp, run_id, sender, recipient, kind, payload,
related_event_id, delivery_state, acknowledged_at
```

The supervisor should also append lifecycle events such as worker start/exit, assignment, progress,
blocked, completion, pause, resume, and timeout. A simple command should render these as a
chronological text timeline for audit.

## Why notification files are only optional

A touched `.NOTIF_*` file can be a convenient local doorbell, but filesystem notifications may
coalesce, a watcher may be absent during the touch, and the file carries no inherent ordering,
payload, acknowledgement, or retry state. If retained, these files should be derived wakeup hints:
the durable event is committed to SQLite first, then the relevant file is touched. On wakeup the
consumer reads its inbox by cursor; correctness never depends on observing the touch.

## Alternatives considered

| Option | Useful property | Why it is not the default here |
| --- | --- | --- |
| Codex built-in subagents | Direct routing inside a live lead thread | Does not by itself provide the desired cross-process durable audit protocol |
| MCP Tasks | Standard task state and polling | The Tasks facility is experimental and is not a complete push mailbox |
| A2A | Tasks, messages, artifacts, streaming, and push notifications | More protocol and deployment surface than a single-host workflow needs |
| Redis Streams | Durable ordered streams and consumer groups | Requires a service and operational lifecycle that SQLite avoids |
| LangGraph | Checkpoints, persistence, and interrupt/resume workflows | Would make LangGraph the workflow runtime rather than lightly supervising Codex |
| Temporal | Strong durable workflow execution | Disproportionately heavy for a local lead and a few workers |
| `STATUS.md` plus `.NOTIF_*` | Transparent and almost free | Not reliable enough to be the source of truth |

## Safe implementation order

If manual coordination becomes the bottleneck, implement this in three bounded steps:

1. Add the SQLite schema, CLI/MCP inbox operations, acknowledgements, and timeline renderer. Test
   ordering, restart recovery, and duplicate delivery before adding automatic wakeups.
2. Add the app-server supervisor and the autonomy state machine. When paused, messages remain
   durable but no new turns start; when stopped, running work is explicitly cancelled according to
   policy.
3. Add optional `.NOTIF_*` doorbells and hook-produced audit events only as conveniences. They must
   not become authoritative state.

## Current references

- [Codex app-server protocol](https://learn.chatgpt.com/docs/app-server)
- [Model Context Protocol Tasks](https://modelcontextprotocol.io/specification/2025-11-25/basic/utilities/tasks)
- [A2A protocol specification](https://a2a-protocol.org/latest/specification/)
- [Redis Streams](https://redis.io/docs/latest/develop/data-types/streams/)
- [LangGraph persistence](https://docs.langchain.com/oss/python/langgraph/persistence)

