// simple onboarding story injection
export function scaffoldNarrative(): void {
    const main = document.querySelector('main');
    if (!main) return;
    const intro = document.createElement('p');
    intro.textContent = 'Welcome to Absolute Zero – let your mind settle into silence.';
    main.prepend(intro);
}

window.addEventListener('DOMContentLoaded', scaffoldNarrative);
