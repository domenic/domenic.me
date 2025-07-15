---
layout: layouts/post
title: "My Participation in the METR AI Productivity Study"
date: 2025-07-15T00:00:00Z
tags: [other]
blurb: An experience report for my participation in the METR's study "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity".
---

[METR](https://metr.org/) recently released a paper, "[Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity](https://metr.org/blog/2025-07-10-early-2025-ai-experienced-os-dev-study/)". It was a randomized controlled trial where developers were given some tasks to work on using AI, and some without. The surprising headline result was that developers using AI took on-average 19% longer to complete their tasks!

I was one of the developers participating in this study, using [jsdom](https://github.com/jsdom/jsdom) as the project in question. This essay gives some more detail on my experience, which might be helpful for those hoping for insight into what these results mean.

## What I worked on

The jsdom project is an attempt at writing most of a web browser engine in JavaScript. It has [some significant limitations](https://github.com/jsdom/jsdom/blob/main/README.md#unimplemented-parts-of-the-web-platform) and [lots of gaps](https://github.com/jsdom/jsdom/issues?q=is%3Aissue%20state%3Aopen%20type%3AFeature), but we get pretty far. A lot of people use it for automated testing and web scraping. It has just over 1 million lines of code in the main repository, with some other [supporting repositories](https://github.com/jsdom). A large part of jsdom development is trying to reproduce web specifications in code, and pass the corresponding [web platform tests](https://web-platform-tests.org/).

These days I am the sole active maintainer. My main goal has been to respond to pull requests from community contributors. The METR study gave me an opportunity to put those aside, and write my own code to tackle the backlog of bug reports that had been particularly nagging me, feature requests that I thought were overdue for fulfillment, and shore up some long-standing infrastructure and test coverage deficits.

I was asked to assemble possible work items ahead of time for the study, broken up into &leq;2 hour chunks. I ended up with 19 such work items. Each of them generated at least one pull request, as well as an "implementation report" where I wrote up what it was like working on that item, with a special focus on what it was like working with AI or not being allowed to use AI.

<details>
  <summary>Expand to see the full list of issues, pull requests, and implementation reports</summary>

  <table>
    <thead>
      <tr>
        <th>Issue</th>
        <th>Task description</th>
        <th>PR</th>
        <th>Report</th>
    </thead>
    <tbody>
      <tr>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/291">Issue</a>
        <td>Update our URL parser for recent changes to the Unicode UTS46 standard and its URL Standard integration
        <td><a href="https://github.com/web-platform-tests/wpt/pull/51371">PR 1</a><br><a href="https://github.com/jsdom/tr46/pull/66">PR 2</a><br><a href="https://github.com/jsdom/whatwg-url/pull/295">PR 3</a>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/291#issuecomment-2726095582">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/292">Issue</a>
        <td>Small URL parser change to follow the latest spec changes
        <td><a href="https://github.com/jsdom/whatwg-url/pull/297">PR</a>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/292#issuecomment-2726292692">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/293">Issue</a>
        <td>Another small URL parser change to follow the latest spec changes
        <td><a href="https://github.com/jsdom/whatwg-url/pull/298">PR</a>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/293#issuecomment-2726298374">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/268">Issue</a>
        <td>Get code coverage of our URL parser to 100%
        <td><a href="https://github.com/web-platform-tests/wpt/pull/51369">PR 1</a><br><a href="https://github.com/web-platform-tests/wpt/pull/51370">PR 2</a><br><a href="https://github.com/jsdom/whatwg-url/pull/294">PR 3</a>
        <td><a href="https://github.com/jsdom/whatwg-url/issues/268#issuecomment-2726153730">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/pull/2926">Issue</a>
        <td>Push a previous maintainer's draft PR for some basic SVG element support over the finish line (split into two chunks)
        <td><a href="https://github.com/jsdom/jsdom/pull/3843">PR</a>
        <td>
          <a href="https://github.com/jsdom/jsdom/pull/3843#issuecomment-2727260557">Report&nbsp;1</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3843#issuecomment-2746042863">Report&nbsp;2</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3154">Issue</a>
        <td>Investigate why our test suite was sometimes taking >70 seconds for a single test on CI
        <td>
          <a href="https://github.com/web-platform-tests/wpt/pull/51373">PR&nbsp;1</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3837">PR&nbsp;2</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3838">PR&nbsp;3</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3839">PR&nbsp;4</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3840">PR&nbsp;5</a>
        <td><a href="https://github.com/jsdom/jsdom/issues/3154#issuecomment-2726445990">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/2264">Issue</a>
        <td>Add linting to our locally-written new web platform tests
        <td><a href="https://github.com/jsdom/jsdom/pull/3845">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3845#issuecomment-2746061041">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3835">Issue</a>
        <td>Allow writing <em>failing</em> new web platform tests, to capture bugs we should fix in the future
        <td><a href="https://github.com/jsdom/jsdom/pull/3846">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3846#issuecomment-2746102183">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues?q=is%3Aissue%20label%3A%22metr%20uplift%22%20label%3Aselectors%20label%3A%22has%20to-upstream%20test%22">24&nbsp;issues</a>
        <td>Add test coverage for known bugs related to CSS selectors (some of which had been fixed, some of were fixed by a new selector engine <a href="https://github.com/jsdom/jsdom/pull/3854">later</a>)
        <td><a href="https://github.com/jsdom/jsdom/pull/3848">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3848#issuecomment-2764469976">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues?q=is%3Aissue%20label%3A%22metr%20uplift%22%20-label%3Aselectors%20label%3A%22has%20to-upstream%20test%22">11&nbsp;issues</a>
        <td>Add test coverage for other known bugs, unrelated to CSS selectors (most of which had been fixed in the past or were fixed soon after the test appeared)
        <td>
          <a href="https://github.com/jsdom/jsdom/pull/3857">PR&nbsp;1</a><br>
          <a href="https://github.com/jsdom/jsdom/pull/3859">PR&nbsp;2</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3859#issuecomment-2799890637">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/2005">Issue</a>
        <td>Add an option to disable the processing of CSS, for speed
        <td><a href="https://github.com/jsdom/jsdom/pull/3861">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3861#issuecomment-2799972478">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues?q=label%3A%22metr%20uplift%22%20label%3A%22event%20classes%22">8&nbsp;issues</a>
        <td>Implement certain event classes or properties, even if the related spec was not fully supported
        <td><a href="https://github.com/jsdom/jsdom/pull/3862">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3862#issuecomment-2816751792">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3616">Issue</a>
        <td>Implement indexed access on form elements, like <code>formElement[0]</code> giving the 0th form control in that form
        <td><a href="https://github.com/jsdom/jsdom/pull/3849">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3849#issuecomment-2764480625">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3320">Issue</a>
        <td>Replace our dependency on the <code>form-data</code> npm package with our own implementation
        <td><a href="https://github.com/jsdom/jsdom/pull/3850">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3850#issuecomment-2764516655">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3732">Issue</a>
        <td>Fix <code>ElementInternals</code> accessibility getters/setters being totally broken
        <td><a href="https://github.com/jsdom/jsdom/pull/3865">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3865#issuecomment-2817021910">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3596">Issue</a>
        <td>Overhaul our system for <a href="https://github.com/jsdom/jsdom/blob/main/README.md#virtual-consoles">reporting errors</a> to the developer
        <td><a href="https://github.com/jsdom/jsdom/pull/3866">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3866#issuecomment-2817066114">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3836">Issue</a>
        <td>Use the HTML Standard's user agent stylesheet instead of an old copy of Chromium's
        <td><a href="https://github.com/jsdom/jsdom/pull/3867">PR</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3867#issuecomment-2817083829">Report</a>
      <tr>
        <td><a href="https://github.com/jsdom/jsdom/issues/3565">Issue</a>
        <td>Fix an edge-case using <code>Object.defineProperty()</code> on <code>HTMLSelectElement</code> instances
        <td><a href="https://github.com/jsdom/webidl2js/pull/272">PR&nbsp;1</a><br><a href="https://github.com/jsdom/jsdom/pull/3868">PR&nbsp;2</a>
        <td><a href="https://github.com/jsdom/jsdom/pull/3868#issuecomment-2817104265">Report</a>
  </table>
</details>

I did this work over the course of about a month, from March through April 2025, on weekends. The total time spent, measured by screen recordings, was 31.25 hours.

The screen recordings are worth calling out. Because of them, I was guaranteed to be "on" while working on these issues: I didn't tab away or get distracted easily, because someone was always watching what I was doing.

## How was the slowdown measured?

It's important to note randomized controlled trials aren't magic. Just like we can't test a drug and placebo on the same patient, this study didn't somehow have me working on the exact same tasks with vs. without AI. Instead, we try to average over a large-enough number of tasks so that, under reasonable assumptions about the underlying mechanisms, we can derive estimates and error bounds for the effect of the treatment.

[Appendix D](https://metr.org/Early_2025_AI_Experienced_OS_Devs_Study.pdf#page=27) of the paper goes into more detail. They use a log-linear model, which is a reasonable model for task completion time and justified by the log-normal distribution of task times observed in the study (and [elsewhere](https://erikbern.com/2019/04/15/why-software-projects-take-longer-than-you-think-a-statistical-model.html)). It is given as input the initial, pre-work time estimate we provided as a measure of task difficulty, as well as the treatment flag (0 for no AI, 1 for AI-allowed) and a random noise term. Various checks against the actual data confirm that this model makes sense: e.g., the model errors were not skewed systematically in any direction, and specializing the model to be different per-developer does not change the outcome much. The end result is that, with enough data, they are able to produce estimates for the slowdown, as well as the 95% confidence intervals.

My personal experience makes me wonder: did they just get unlucky? For example, from the with-AI bucket, my [performance optimization task](github.com/jsdom/jsdom/issues/3154#issuecomment-2726445990) ended up taking 4 hours 7 minutes, instead of my estimated 30 minutes; my [write lots of tests task](https://github.com/jsdom/jsdom/pull/3848#issuecomment-2764469976) took 4 hours 20 minutes, instead of my estimated 1 hour. Maybe those tasks would have taken even longer without AI!

But this isn't really the right way of thinking about it. There were many misestimates in the other direction too: e.g., [this bugfix task](https://github.com/jsdom/whatwg-url/issues/292#issuecomment-2726292692) took 6 minutes without AI, compared to an estimated 20 minutes. I think it's better to trust the law of large numbers, and the power of well-structured statistical analysis, than to second-guess what might have happened in a different randomization setup. This is part of why the study's authors [emphasize](https://x.com/joel_bkr/status/1944886738931081726) that there is only good statistical power when you look at the results in aggregate.

## My prior AI-coding experience

Prior to this study, I had not had significant experience with agentic coding workflows like Cursor's agent mode.

A large part of this is due to my position on the Chrome team at Google, which means I am prohibited by policy from using most cutting-edge AI coding tools in my day job. Google employees are required to only ever use internally-developed Gemini-based tooling, not anything external like Cursor, Claude Code, or even GitHub Copilot. And the internal tooling Google does develop targets the private "google3" codebase, not the Chromium open-source codebase where I work.

(With the release of Gemini CLI in late June 2025, we finally had something usable. But I gave it a try for a solid week and kept running into basic problems that other tools have already solved, like [out of memory errors](https://github.com/google-gemini/gemini-cli/issues/1740#issuecomment-3026084546) due to inefficient file-searching, or [a file-patching tool that couldn't handle whitespace](https://github.com/google-gemini/gemini-cli/issues/1971).)

So prior to the METR study, I had only been able to spend weekend side-project time on AI coding. And during that time, I mainly used GitHub Copilot's tab completion, plus the web interfaces for ChatGPT and Claude when I wanted to generate new files or functions completely from scratch.

That said, I'm skeptical of [those who claim](https://x.com/eshear/status/1944895440224501793) that this lack of experience was a major contributor to the slowdown experienced. Agent mode is just not that hard to learn to use; the short training that METR provided, plus some pre-reading, felt like plenty to me. It's possible there's still something I'm missing here, and more intense practice would be helpful. Perhaps you'll be able to judge from yourself from the experience report below.

## My experience with AI during the study

It's worth remembering the state of AI tooling in March 2025. Claude Code had just come out in research preview on 2025-02-24 (general release wasn't until 2025-05-22). Cursor's agent mode only became the default on 2025-02-19. Delegation-centric parallelization tools like [OpenAI Codex](https://openai.com/codex/) or [Google Jules](https://jules.google/) had not been released yet. In general, I think the best hope for true efficiency gains will come from these sorts of workflows, where you command an army of agents in parallel, but the METR study was not set up to measure those: we worked on one task at a time.

The majority of the time I worked on AI-allowed tasks, it was with Cursor's agent mode, with the model set to one of "auto" (Claude Sonnet 3.5, I believe?), Claude Sonnet 3.7 (thinking mode), or gemini-2.5-pro-exp-03-25. I never had the patience to use the "MAX" modes. I made [one attempt](https://github.com/jsdom/jsdom/pull/3848#issuecomment-2764469976:~:text=I%20tried%20Claude%20Code%20first%2C%20excited%20because%20I%20felt%20this%20was%20a%20use%20case%20where%20a%20fully%20agentic%20setup%20would%20shine.) to use Claude Code, but gave up after wasting a decent amount of time because it didn't work well enough under Windows Subsystem for Linux to run integration tests against my local test server. I also went back to web chat interfaces a few times, e.g. to learn about the current state of Node.js profiling tools, or to ask o3-mini-high to microoptimize some specific string manipulation code.

I was most surprised at how bad at fitting into the existing codebase's style these tools were. This was very evident when [asking it to churn out tons of tests](https://github.com/jsdom/jsdom/pull/3848#issuecomment-2764469976). Despite many examples in sibling directories, they did not pick up on simple things like: include a link to the fixed issue in the test header; don't duplicate the test name in the `<title>` and the `test()` function; reproduce the user's reported bug exactly instead of imagining novel things to test; etc. And of course, the stupid excessive comments. On a greenfield or throwaway project, these things don't matter much. We can just let the agent's preferences rule the day. But when fitting into a 1m+ LOC codebase, consistency is important. This meant that I had to continually check their work, and refine my prompt so that the next attempt would avoid the same pitfalls.

Eventually, for some of these repetitive test-writing tasks, I refined my prompt enough to get into a good flow, where they produced three or four tests in a row with no changes needed. (Even then, they kept failing to use Git for some reason, so I had to interrupt to commit each change.) But they would always eventually go off the rails, maybe due to context length overflow, usually in quite bizarre ways. In such cases restarting the session and copying my carefully-crafted prompt back in would get us back on track, but it wasted time.

My second biggest surprise was how bad the models are at implemementing web specifications. This is most on display when I was [implementing various event classes](https://github.com/jsdom/jsdom/pull/3862#issuecomment-2816751792). Web specifications are basically computer code, written in a strange formal dialect of English. Translating them into actual programming languages should be trivial for these models. But the few times I tried to prompt the model to just implement by reading the specification did not go well. I can list a couple of contributing factors here:

* The tool use was still sub-par. For example, web specifications are written as HTML, so simply pasting in a link like [this one](https://dom.spec.whatwg.org/#event-flatten-more) is not enough to get the resulting extract of the specification into the context window, in a format like Markdown which the models are good at understanding. (This seems solvable if I code up my own MCP server or similar.)

* The models have strong, but outdated or wrong, priors for how web specifications are supposed to work. That is, old versions of these specifications were already in their training data, and then got lossily-compressed into the weights. So instead of implementing properly, by reading the specification text and then translating it into code, they seem to want to write the code off-the-cuff based on their existing priors.

This latter tendency was most hilariously on display when I [got in an argument](https://x.com/domenic/status/1911342216024395879) with Gemini 2.5 Pro preview about how it should not make up a new constant `CSSRule.LAYER_STATEMENT_RULE`. Old CSS rules, like `@charset`, got such named constants (see [the spec](https://drafts.csswg.org/cssom/#the-cssrule-interface) for `CSSRule.CHARSET_RULE`). New rules, like `@layer`, do not, since such numeric constants are a holdover from when people were designing web APIs as if they were Java APIs. But Gemini really, really wanted to follow the pattern it knew from its training data, and refused to implement CSS layers without also adding a `CSSRule.LAYER_STATEMENT_RULE` constant with the totally-hallucinated value of `16`. I recommend reading [its polite-but-firm sophistry](https://x.com/domenic/status/1911342216024395879/photo/1) about how even if the spec didn't contain these constants, there's some other "combined, effective standard" that includes this constant.

## My feelings on AI-assisted productivity

In retrospect, it's not too surprising that AI was a drag on velocity, while subjectively feeling like a speedup. When I go through the implementation reports, and notice all the stumbling and missteps, that's a lot of wasted time. Whereas, for the no-AI-allowed tasks, I just sat down, started the screen recording, and coded, with no distractions.

Sometimes, tasks with AI felt _more engaging_ than it would have been otherwise. This was especially the case for repetitive ones like writing lots of tests or lots of similar classes. Making them into an interactive game, where I try to get the agent to do all the work with minimal manual intervention, was more fun than churning out very similar code over and over. But I don't think it was faster.

A big productivity drag is that these agents were still not smart enough, at least out of the box. I mentioned some of the specific pain points above, but others come up over and over in my implementation reports. They weren't able to coordinate across multiple repositories. They need [careful review to avoid inelegant code](https://github.com/jsdom/jsdom/pull/3845#issuecomment-2746061041:~:text=I%20gave%20it%20detailed%20instructions,clean%20the%20new%20code%20was.%29). They get stuck in loops doing simple things like [fixing linter errors](https://github.com/jsdom/jsdom/pull/3859#issuecomment-2799890637:~:text=Although%20it%20was%20pretty%20smart%20most%20of%20the%20time%2C%20it%20had%20a%20few%20moments%20of%20extreme%20stupidity%20such%20as%20not%20understanding%20how%20to%20fix%20a%20linter%20error%20asking%20it%20to%20change%20const%20x%20=%20y.x%20to%20const%20%7B%20x%20%7D%20=%20y.) or [lexicographically sorting filenames](https://github.com/jsdom/jsdom/pull/3848#:~:text=It%20had%20real%20troubles%20with%20lexicographically%20sorting%20the%20test%20filenames%20within%20the%20expectations%20file%2C%20which%20was%20surprisingly%20dumb.%20Like%2C%20it%20kept%20moving%20the%20line%20one%20line%20backward%2C%20running%20the%20tests%20and%20getting%20the%20sorting%20error%2C%20and%20repeating%2C%20instead%20of%20just%20inserting%20it%20into%20the%20right%20place.). They can't [traverse directories to find a relevant-looking file](https://github.com/jsdom/jsdom/pull/3862#issuecomment-2816751792:~:text=A%20final%20thing%20to%20note,few%20more%20to%20run%20it.) in any reasonable amount of time.

These sorts of things are all fixable, with enough scaffolding. And I am eager for the companies working on these to drill into such problem cases and build out the necessary tools. But until then, I suspect attempts to pair-program with the AI in a large project like this will need more constant handholding and constant awareness of the models' limitations.

The more promising approach, though, is abandoning the pair-programming model in favor of the parallel-agents model. These days, if I were shooting for maximum productivity on these sorts of issues, I would spend a lot of up-front time writing detailed issue descriptions, including specific implementation suggestions. Then I would try to run all nine of the AI-allowed tasks in parallel, using something like Claude Code or OpenAI Codex. If one of the agents gets stuck in a loop on linter errors, or takes thirty minutes to traverse the directory tree to find the right tests to enable, it wouldn't matter, because I'd be busy reviewing the code of one of the other agents.

I still think large, existing open-source codebases with established patterns face a more unique challenge than when you [create something from scratch](https://www.indragie.com/blog/i-shipped-a-macos-app-built-entirely-by-claude-code) and can focus entirely on the quality of the end product. But we'll get there. Human beings' time writing code is limited.
