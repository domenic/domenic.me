---
layout: layouts/post
title: "My Participation in the METR AI Productivity Study"
date: 2025-07-15T00:00:00Z
tags: [other]
blurb: An experience report for my participation in the METR's study "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity".
---

[METR](https://metr.org/) recently released a paper, "[Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity](https://metr.org/blog/2025-07-10-early-2025-ai-experienced-os-dev-study/)". It was a randomized controlled trial where developers were given some tasks to work on using AI, and some without. The surprising headline result was that developers using AI took on-average 19% longer to complete their tasks!

I was one of the developers participating in this study, using [jsdom](https://github.com/jsdom/jsdom) as the project in question. This essay gives some more detail on my experience, which might be helpful for those hoping for insight into what these results mean.

## The study setup

The jsdom project is an attempt at writing most of a web browser engine in JavaScript. It has [some significant limitations](https://github.com/jsdom/jsdom/blob/main/README.md#unimplemented-parts-of-the-web-platform) and [lots of gaps](https://github.com/jsdom/jsdom/issues?q=is%3Aissue%20state%3Aopen%20type%3AFeature), but we get pretty far. A lot of people use it for automated testing and web scraping. It has just over 1 million lines of code in the main repository, with some other [supporting repositories](https://github.com/jsdom). A large part of jsdom development is trying to reproduce web specifications in code, and pass the corresponding [web platform tests](https://web-platform-tests.org/).

These days I am the sole active maintainer. My main goal has been to respond to pull requests from community contributors, and to a lesser extent to bug reports. The METR study gave me an opportunity to get through the backlog of bug reports that had been particularly nagging me, feature requests that I thought were very fair, and shore up some long-standing infrastructure and test coverage deficits.

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

I did this work over the course of about a month, on weekends. The total time spent, measured by screen recordings, was 31.25 hours.

The screen recordings are worth calling out. Because of them, I was guaranteed to be "on" while working on these issues: I didn't tab away or get distracted easily, because someone was always watching what I was doing.

## How was the slowdown measured?

It's important to note randomized controlled trials aren't magic. Just like we can't test a drug and placebo on the same patient, this study didn't somehow have me working on the exact same tasks with vs. without AI. Instead, we try to average over a large-enough number of tasks so that, under reasonable assumptions about the underlying mechanisms, we can derive estimates and error bounds for the effect of the treatment.

[Appendix D](https://metr.org/Early_2025_AI_Experienced_OS_Devs_Study.pdf#page=27) of the paper goes into more detail. They use a log-linear model, which (ChatGPT assures me) is a reasonable model for task completion time. It is given as input the initial, pre-work time estimate we provided as a measure of task difficulty, as well as the treatment flag (0 for no AI, 1 for AI-allowed) and a random noise term. Various checks against the actual data confirm that this model makes sense: e.g., the model errors were not skewed systematically in any direction, and specializing the model to be different per-developer does not change the outcome much. The end result is that, with enough data, they are able to produce estimates for the slowdown, as well as the 95% confidence intervals.

My personal exprience makes me wonder: did they just get unlucky? For example, from the with-AI bucket, my [performance optimization task](github.com/jsdom/jsdom/issues/3154#issuecomment-2726445990) ended up taking 4 hours 7 minutes, instead of my estimated 30 minutes; my [write lots of tests task](https://github.com/jsdom/jsdom/pull/3848#issuecomment-2764469976) took 4 hours 20 minutes, instead of my estimated 1 hour. Maybe those tasks would have taken even longer without AI!

But this isn't really the right way of thinking about it. There were many misestimates in the other direction too: e.g., [this bugfix task](https://github.com/jsdom/whatwg-url/issues/292#issuecomment-2726292692) took 6 minutes without AI, compared to an estimated 20 minutes. I think it's better to trust the law of large numbers, and the power of well-structured statistical analysis, than to second-guess what might have happened in a different randomization setup.

## How I used AI during the study

