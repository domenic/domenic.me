const sheet = new CSSStyleSheet();
sheet.replaceSync(`
  :host {
    display: flex;
    align-items: center;
    gap: 0.5rem;
    border: 1px solid var(--color-border);
    border-radius: 6px;
    padding: 1rem;
  }

  .slides {
    display: grid;
    flex: 1;
    min-width: 0;
  }

  /* All figures overlap in the same grid cell. Using visibility instead of
     display ensures hidden figures still contribute to the cell's height,
     so the container stays the size of the tallest caption. */
  ::slotted(figure) {
    grid-area: 1 / 1;
    visibility: hidden;
    border: none !important;
    padding: 0 !important;
  }

  button {
    background: none;
    border: 1px solid var(--color-border);
    border-radius: 4px;
    padding: 0.25rem 0.75rem;
    cursor: pointer;
    color: var(--color-text);
    font-size: 1.25rem;
    line-height: 1;
    flex-shrink: 0;
  }
`);

class ImageCarousel extends HTMLElement {
  #figures;
  #index = 0;
  #activeSheet = new CSSStyleSheet();

  connectedCallback() {
    this.#figures = [...this.querySelectorAll(':scope > figure')];
    if (this.#figures.length === 0) {
      return;
    }

    const shadow = this.attachShadow({ mode: 'open' });
    shadow.adoptedStyleSheets = [sheet, this.#activeSheet];

    const prev = document.createElement('button');
    prev.textContent = '\u2039';
    prev.setAttribute('aria-label', 'Previous image');
    prev.addEventListener('click', () => this.#showSlide(this.#index - 1));

    const slides = document.createElement('div');
    slides.className = 'slides';
    slides.append(document.createElement('slot'));

    const next = document.createElement('button');
    next.textContent = '\u203a';
    next.setAttribute('aria-label', 'Next image');
    next.addEventListener('click', () => this.#showSlide(this.#index + 1));

    shadow.append(prev, slides, next);

    shadow.addEventListener('keydown', e => {
      if (e.key === 'ArrowLeft') {
        this.#showSlide(this.#index - 1);
      } else if (e.key === 'ArrowRight') {
        this.#showSlide(this.#index + 1);
      }
    });

    this.#showSlide(0);
  }

  #showSlide(index) {
    const len = this.#figures.length;
    this.#index = ((index % len) + len) % len;

    this.#activeSheet.replaceSync(
      `::slotted(figure:nth-of-type(${this.#index + 1})) { visibility: visible; }`
    );

    // Pre-decode adjacent images so navigation is instantaneous
    for (const offset of [-1, 1]) {
      const img = this.#figures[((this.#index + offset) % len + len) % len].querySelector('img');
      img?.decode().catch(() => {});
    }
  }
}

customElements.define('image-carousel', ImageCarousel);
