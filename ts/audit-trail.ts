// injects data-audit paths into the DOM for debugging
export function annotateAudits(): void {
    document
        .querySelectorAll<HTMLElement>('[data-audit]')
        .forEach(el => {
            const tag = document.createElement('span');
            tag.textContent = el.dataset.audit;
            tag.style.cssText = 'position:absolute; top:0; right:0; font-size:0.6rem; opacity:0.3;';
            el.style.position = 'relative';
            el.appendChild(tag);
        });
}

window.addEventListener('DOMContentLoaded', annotateAudits);
