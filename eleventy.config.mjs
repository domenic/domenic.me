'use strict';
import { feedPlugin } from '@11ty/eleventy-plugin-rss';
import pluginSyntaxHighlight from '@11ty/eleventy-plugin-syntaxhighlight';
import markdownIt from 'markdown-it';
import markdownItAnchor from 'markdown-it-anchor';
import adjustHeadingLevel from './adjust-heading-level.mjs';
import metadata from './src/_data/metadata.json' with { type: 'json' };

export default async (eleventyConfig) => {
  eleventyConfig.addTransform('image-carousel-rss', function (content) {
    if (!content.includes('<image-carousel')) {
      return content;
    }

    const carouselRegex = /<image-carousel\b([^>]*)>[\s\S]*?<\/image-carousel>/g;

    // Validate: every carousel must have an id
    for (const [, attrs] of content.matchAll(carouselRegex)) {
      if (!/\bid=/.test(attrs)) {
        throw new Error(`<image-carousel> in ${this.inputPath} is missing a required id attribute`);
      }
    }

    if (!this.baseHref) {
      return content;
    }

    // RSS context: replace carousels with fallback text
    content = content.replace(carouselRegex, (match, attrs) => {
      const id = attrs.match(/\bid="([^"]+)"/)?.[1];
      const rssText = attrs.match(/\brsstext="([^"]+)"/)?.[1] ?? 'an image carousel';
      const absoluteURL = new URL(`${this.url}#${id}`, this.baseHref).href;
      return `<p><em>See <a href="${absoluteURL}">the web version</a> for ${rssText}.</em></p>`;
    });

    // Strip the carousel script tag
    content = content.replace(/<script\b[^>]*\bsrc="[^"]*image-carousel[^"]*"[^>]*><\/script>\s*/g, '');

    return content;
  });

  eleventyConfig.addPlugin(feedPlugin, {
    type: 'atom',
    outputPath: 'feed.xml',
    collection: {
      name: 'posts',
      limit: 10
    },
    metadata: transformMetadataForFeedPlugin(metadata)
  });

  eleventyConfig.addPlugin(pluginSyntaxHighlight);

  eleventyConfig.addPassthroughCopy('src/css');
  eleventyConfig.addPassthroughCopy('src/js');
  eleventyConfig.addPassthroughCopy('src/images');
  eleventyConfig.addPassthroughCopy({ 'node_modules/prismjs/themes/prism.css': 'css/prism.css' });
  eleventyConfig.addPassthroughCopy({ 'node_modules/prismjs/themes/prism-dark.css': 'css/prism-dark.css' });

  eleventyConfig.setLibrary(
    'md',
    markdownIt({
      html: true,
      typographer: true
    })
    .use(adjustHeadingLevel, { firstLevel: 2 })
    .use(markdownItAnchor, {
      tabIndex: false
    })
  );

  addFilters(eleventyConfig);

  eleventyConfig.addCollection('posts', collection => {
    return collection.getFilteredByGlob('src/posts/*.md');
  });

  return {
    templateFormats: [
      'md',
      'njk',
      'html'
    ],

    markdownTemplateEngine: 'liquid',
    htmlTemplateEngine: 'njk',
    dataTemplateEngine: 'njk',

    passthroughFileCopy: true,
    dir: {
      input: 'src',
      includes: '_includes',
      data: '_data',
      output: 'dist',
    }
  };
};

function addFilters(eleventyConfig) {
  const readableDTF = new Intl.DateTimeFormat('en-US', {
    year: 'numeric',
    month: 'long',
    day: 'numeric',
    timeZone: 'UTC'
  });
  eleventyConfig.addFilter('readableDate', dateObj => {
    return readableDTF.format(dateObj);
  });

  eleventyConfig.addFilter('getYear', dateObj => {
    return dateObj.getUTCFullYear();
  });

  eleventyConfig.addFilter('slugToPermalink', string => {
    return string.replace(/^\/posts\/\d{4}-\d{2}-\d{2}-/, '') + '/';
  });

  eleventyConfig.addFilter('exclude', (array, arrayToExclude) => {
    return array.filter(item => !arrayToExclude.includes(item));
  });
}

function transformMetadataForFeedPlugin(metadata) {
  return { ...metadata, subtitle: metadata.description };
}
