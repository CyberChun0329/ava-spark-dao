const preference = 'spark-dao:language';
let language = 'zh';

export const b = (zh, en) => ({ zh, en });
export const localized = render => b(render('zh'), render('en'));

function isBilingual(value) {
  return typeof value?.zh === 'string' && typeof value?.en === 'string';
}

export function inLanguage(value, locale) {
  return isBilingual(value) ? value[locale] : value;
}

// Use leaf elements so a language change leaves open details, fields and buttons in place.
export function setText(element, value) {
  if (isBilingual(value)) {
    element.dataset.zh = value.zh;
    element.dataset.en = value.en;
  } else {
    delete element.dataset.zh;
    delete element.dataset.en;
  }
  element.textContent = inLanguage(value, language) ?? '';
}

export function initLanguage() {
  const buttons = document.querySelectorAll('[data-language]');
  const select = locale => {
    language = locale;
    document.documentElement.lang = locale === 'en' ? 'en' : 'zh-CN';
    for (const element of document.querySelectorAll('[data-en]')) {
      element.dataset.zh ??= element.textContent;
      element.textContent = element.dataset[locale];
    }
    for (const element of document.querySelectorAll('[data-en-aria-label]')) {
      element.dataset.zhAriaLabel ??= element.getAttribute('aria-label');
      element.setAttribute('aria-label', element.dataset[`${locale}AriaLabel`]);
    }
    for (const button of buttons) button.setAttribute('aria-pressed', String(button.dataset.language === locale));
  };
  try {
    if (localStorage.getItem(preference) === 'en') language = 'en';
  } catch { /* Language switching also works when browser storage is unavailable. */ }
  select(language);
  for (const button of buttons) button.addEventListener('click', () => {
    const locale = button.dataset.language;
    if (locale === language) return;
    select(locale);
    try { localStorage.setItem(preference, locale); }
    catch { /* Keep the choice for the current page. */ }
  });
}
