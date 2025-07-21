---
layout: layouts/post
title: "Designing the Built-in AI web APIs"
date: 2025-07-21T00:00:00Z
tags: [other]
blurb: The built-in AI APIs like the prompt API have some unique design considerations. TODO more catchy.
---

For the last year I've been working as part of the Chrome built-in AI team on [a set of APIs](https://developer.chrome.com/docs/ai/built-in-apis) to bring various AI models to the web browser. [As with all APIs we ship](https://www.chromium.org/blink/guidelines/web-platform-changes-guidelines/), our goal is to make these APIs compelling enough that other browsers adopt them, and they become part of the web's standard library.

Working in such a fast-moving space brings tension with the usual process for building web APIs. When exposing other platform capabilities like [USB](https://developer.mozilla.org/en-US/docs/Web/API/WebUSB_API), [payments](https://developer.mozilla.org/en-US/docs/Web/API/Payment_Request_API), or [codecs](https://developer.mozilla.org/en-US/docs/Web/API/WebCodecs_API), we can draw on years or decades of work in native platforms. But with built-in AI APIs, especially for language model-backed APIs like the [prompt API](https://github.com/webmachinelearning/prompt-api), our precedent is barely [two years old](https://www.wired.com/story/chatgpt-api-ai-gold-rush/). Moreover, there are interesting differences between HTTP APIs and client-side APIs, and vendor-specific APIs versus those designed for a wide range of possible future implementations.

## Starting from precedent

The starting place for API design is the core loop: apart from any initialization or state management, when a developer wants to prompt a language model, what does the code for that look like? Even with only two years' experience for language model prompting, the ecosystem has roughly converged on a shape here.

The consensus shape is that language model prompt consists of a series of messages, with one of three roles: `"user"`, `"assistant"`, and `"system"` (or sometimes `"developer"`). A moderate-complexity example might look something like this:

```js
[
  { role: "system", content: "Predict up to 5 emojis as a response to a comment. Output emojis, comma-separated." },
  { role: "user", content: "This is amazing!" },
  { role: "assistant", content: "❤️, ➕" },
  { role: "user", content: "LGTM" },
  { role: "assistant", content: "👍, 🚢" }
]
```

But, the exact details of this format are nontrivial! The main complicating factors are:

* Multimodal inputs and outputs: how do we represent images and audio clips?
* Constraints: Can you include a system message later in the conversation? If the model is not capable of outputting audio, can you add an assistant message whose content is audio?
* Semantics: Are you allowed to have multiple assistant messages in a row? Is that the same or different from concatenating the two messages, and if the same, do you include a space in that concatenation? How does that compare to array-valued `content`s?
* Shorthands: all existing APIs allow passing in just a string, instead of the above role-denominated array, as a shorthand for a user-message. Should `{ content: "a string" }` be treated the same?

You can try to piece together answers to these questions from the various providers' API documentation. The answers are not always the same, and they can change between versions even within a single provider. But part of the process of writing a web specification is nailing these things down in a way that multiple browsers could implement. Briefly, [the answer we've come up with](https://webmachinelearning.github.io/prompt-api/#prompt-processing) involves normalizing everything into an array of the messages of the form `{ role, content: Array<{ type, value }>, prefix? }`, with various constraint checks added. Only certain shorthands are allowed, to give a good balance between conciseness and [ambiguity](https://github.com/webmachinelearning/prompt-api/pull/89#issuecomment-2756808994).

The core concepts shared between all APIs: completions API (various flavors), responses API, client-side prompt API

Mention HTTP translation APIs, maybe language detection APIs as well

## Client-first versus server-based APIs

Client-side APIs vs. server-based APIs?

- Tool-calling via actual JS functions
- Statefulness possible instead of stateless-ish HTTP
- Considerations about downloading and warmup and concurrent usage, instead of a server that's always on
  - Warmup in particular informs a lot, e.g. sharedContext, append(), cloning
  - destroy() and AbortSignals to release resources

Some things unique (?) or worth contrasting about the prompt API: context window limits and overflow event; strategy for the preservation of context and system prompt

## Interoperability and futureproofing

Interop challenges:

- Sampling hyperparameters
- Prompt injection for task-based APIs
- Tokenization

Multilingual and multimodal challenges! expectedInputs, expectedOutputs

In general, the forward-looking design (discuss the web's backward-compatibility constraints) which leads to a lot of extension points around possible LORAs or similar, which are a bit iffy. E.g. lots of creation-time options that could, in theory, trigger downloads.

Fit in availability testing somewhere? Maybe on the interop challenges section.
