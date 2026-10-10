# -*- coding: utf-8 -*-
"""
Bale multi-source news publisher for Persian news agencies.
Designed for Railway.
"""

import json
import os
import re
import time
import mimetypes
import difflib
import unicodedata
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from datetime import datetime, timezone
from html import unescape
from urllib.parse import urljoin, urlparse, urlunparse, parse_qsl, urlencode

import requests
from bs4 import BeautifulSoup

# ==================== SETTINGS ====================
BOT_TOKEN = os.environ.get("BOT_TOKEN", "1895533466:Cr_JVOePGVsItl7oImyHopLDXtZgGFBB2c8")

DESTINATION_CHAT = "@akhbar_polirical"
CHANNEL_LINK = "https://ble.ir/akhbar_polirical"

INITIAL_POST_COUNT = 0
MAX_NEW_POSTS_PER_CYCLE = 5
CHECK_INTERVAL_SECONDS = 60

MAX_ARTICLE_BODY_CHARS = 550
MAX_CAPTION_CHARS = 950

STATE_FILE = os.environ.get("STATE_FILE", "/data/bale_state.json")
REQUEST_TIMEOUT = 12
MAX_IMAGE_BYTES = 9 * 1024 * 1024
MAX_VIDEO_BYTES = 49 * 1024 * 1024

API_BASE = "https://tapi.bale.ai/bot{}/{}"
ARTICLE_PATH_RE = re.compile(r"/fa/news/\d{4}/\d{1,2}/\d{1,2}/\d+", re.I)
DIRECT_VIDEO_EXTENSIONS = (".mp4", ".m4v", ".mov", ".webm")

TASNIM_LISTING_URL = "https://www.tasnimnews.ir/fa"
SOURCES = [
    {"name": "تسنیم", "kind": "html", "url": TASNIM_LISTING_URL,
     "domains": ("tasnimnews.ir", "tasnimnews.com")},
    {"name": "ایسنا", "kind": "rss", "url": "https://www.isna.ir/rss",
     "domains": ("isna.ir",)},
    {"name": "ایرنا", "kind": "rss", "url": "https://www.irna.ir/rss",
     "domains": ("irna.ir",)},
    {"name": "مهر", "kind": "rss", "url": "https://www.mehrnews.com/rss",
     "domains": ("mehrnews.com",)},
]

session = requests.Session()
session.headers.update({
    "User-Agent": "Mozilla/5.0 (Linux; Android 12) AppleWebKit/537.36 Chrome/124.0 Mobile Safari/537.36",
    "Accept-Language": "fa-IR,fa;q=0.9,en;q=0.7",
})


def log(message):
    print(time.strftime("[%H:%M:%S]"), message, flush=True)


def bale_request(method, *, data=None, files=None, timeout=60):
    url = API_BASE.format(BOT_TOKEN.strip(), method)
    response = session.post(url, data=data, files=files, timeout=timeout)
    try:
        result = response.json()
    except ValueError:
        raise RuntimeError("پاسخ بله JSON معتبر نبود: HTTP " + str(response.status_code))
    if response.status_code >= 400 or not result.get("ok"):
        description = result.get("description") or response.text[:500]
        raise RuntimeError("خطای API بله در " + method + ": " + str(description))
    return result.get("result")


def validate_settings():
    if not BOT_TOKEN or BOT_TOKEN.startswith("توکن_") or ":" not in BOT_TOKEN:
        raise RuntimeError("توکن BOT_TOKEN معتبر نیست. آن را در Environment Variables تنظیم کن.")
    me = session.get(API_BASE.format(BOT_TOKEN.strip(), "getMe"), timeout=REQUEST_TIMEOUT)
    me.raise_for_status()
    result = me.json()
    if not result.get("ok"):
        raise RuntimeError("توکن پذیرفته نشد.")
    bot = result.get("result", {})
    log("اتصال به بله موفق شد: @" + str(bot.get("username", "bot")))


def clean_text(value):
    if not value:
        return ""
    value = value.replace("\u200c", "\u200c").replace("\xa0", " ")
    value = re.sub(r"[ \t\r\f\v]+", " ", value)
    value = re.sub(r"\n[ \t]+", "\n", value)
    value = re.sub(r"\n{3,}", "\n\n", value)
    return value.strip()


def absolute_url(url, base):
    if not url:
        return ""
    url = url.strip()
    if url.startswith("//"):
        return "https:" + url
    return urljoin(base, url)


def fetch_soup(url):
    response = session.get(url, timeout=REQUEST_TIMEOUT)
    response.raise_for_status()
    response.encoding = response.apparent_encoding or response.encoding
    return BeautifulSoup(response.text, "html.parser"), response.url


def local_xml_name(tag):
    return str(tag).rsplit("}", 1)[-1].split(":")[-1].lower()


def strip_html(value):
    if not value:
        return ""
    try:
        text = BeautifulSoup(unescape(str(value)), "html.parser").get_text(" ", strip=True)
    except Exception:
        text = re.sub(r"<[^>]+>", " ", str(value))
    return clean_text(unescape(text))


def normalize_url(url):
    if not url:
        return ""
    url = absolute_url(url, "https://example.com/")
    parts = urlparse(url)
    netloc = (parts.netloc or "").lower()
    path = re.sub(r"/+", "/", parts.path or "/").rstrip("/") or "/"
    tracking = {"fbclid", "gclid", "dclid", "ref", "ref_src", "from", "source"}
    query = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
             if not k.lower().startswith("utm_") and k.lower() not in tracking]
    query.sort()
    return urlunparse((parts.scheme.lower() or "https", netloc, path, "", urlencode(query, doseq=True), ""))


def url_dedupe_key(url):
    cleaned = normalize_url(url)
    parts = urlparse(cleaned)
    host = (parts.hostname or "").lower()
    if host.startswith("www."):
        host = host[4:]
    if host == "tasnimnews.ir":
        host = "tasnimnews.com"
    path = (parts.path or "/").rstrip("/") or "/"
    query = urlencode(sorted(parse_qsl(parts.query, keep_blank_values=True)), doseq=True)
    return urlunparse(("https", host, path, "", query, ""))


def item_allowed_for_source(url, source):
    try:
        host = (urlparse(url).hostname or "").lower()
    except Exception:
        return False
    host = host[4:] if host.startswith("www.") else host
    return any(host == d or host.endswith("." + d) for d in source["domains"])


def parse_published_time(value):
    if not value:
        return 0.0
    value = clean_text(value)
    try:
        dt = parsedate_to_datetime(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.timestamp()
    except Exception:
        pass
    try:
        candidate = value.replace("Z", "+00:00")
        dt = datetime.fromisoformat(candidate)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.timestamp()
    except Exception:
        return 0.0


def child_text_by_names(element, wanted_names):
    wanted = {x.lower() for x in wanted_names}
    for child in list(element):
        if local_xml_name(child.tag) in wanted:
            if child.text and child.text.strip():
                return child.text.strip()
            if child.get("href"):
                return child.get("href").strip()
    return ""


def parse_rss_source(source):
    response = session.get(source["url"], timeout=REQUEST_TIMEOUT)
    response.raise_for_status()
    try:
        root = ET.fromstring(response.content)
    except ET.ParseError as exc:
        raise RuntimeError("ساختار RSS قابل خواندن نیست: " + str(exc))

    entries = [node for node in root.iter() if local_xml_name(node.tag) in ("item", "entry")]
    out = []
    for entry in entries[:45]:
        title_raw = child_text_by_names(entry, ("title",))
        title = strip_html(title_raw)
        link = ""
        for child in list(entry):
            if local_xml_name(child.tag) == "link":
                href = child.get("href")
                rel = (child.get("rel") or "alternate").lower()
                if href and rel in ("alternate", "canonical", ""):
                    link = href.strip()
                    break
                if child.text and child.text.strip():
                    link = child.text.strip()
                    break
        if not link:
            link = child_text_by_names(entry, ("guid", "id"))
        link = absolute_url(link, source["url"])
        parsed_link = urlparse(link)
        if not title or not parsed_link.scheme.startswith("http") or not item_allowed_for_source(link, source):
            continue
        if parsed_link.path in ("", "/", "/rss", "/fa/rss"):
            continue

        desc_raw = child_text_by_names(entry, ("encoded", "description", "summary", "content", "subtitle"))
        description = strip_html(desc_raw)
        image_url = ""
        video_urls = []
        for node in entry.iter():
            lname = local_xml_name(node.tag)
            media_url = node.get("url") or node.get("href")
            mime = (node.get("type") or node.get("medium") or "").lower()
            if not media_url:
                continue
            media_url = absolute_url(media_url, link)
            if lname in ("thumbnail", "content", "enclosure"):
                if not image_url and ("image" in mime or lname == "thumbnail" or re.search(r"\.(jpg|jpeg|png|webp)(?:$|\?)", media_url, re.I)):
                    image_url = media_url
                if ("video" in mime or re.search(r"\.(mp4|m4v|mov|webm)(?:$|\?)", media_url, re.I)):
                    video_urls.append(media_url)
        if not image_url and desc_raw:
            try:
                img = BeautifulSoup(unescape(desc_raw), "html.parser").find("img")
                if img:
                    image_url = absolute_url(img.get("src") or img.get("data-src") or "", link)
            except Exception:
                pass
        published = parse_published_time(child_text_by_names(entry, ("pubdate", "published", "updated", "date", "issued")))
        link = normalize_url(link)
        out.append({
            "url": link, "title": title, "description": description,
            "image_url": image_url, "video_urls": video_urls,
            "source_name": source["name"], "published_at": published,
        })
    return out


def parse_tasnim_listing(source):
    soup, page_url = fetch_soup(source["url"])
    out, seen = [], set()
    for index, anchor in enumerate(soup.find_all("a", href=True)):
        href = anchor.get("href", "").strip()
        if not ARTICLE_PATH_RE.search(urlparse(href).path):
            continue
        full_url = absolute_url(href, page_url)
        if not item_allowed_for_source(full_url, source):
            continue
        full_url = normalize_url(full_url)
        dedupe_key = url_dedupe_key(full_url)
        if dedupe_key in seen:
            continue
        seen.add(dedupe_key)
        title = strip_html(anchor.get_text(" ", strip=True))
        if len(title) < 8:
            title = ""
        published = 0.0
        match = re.search(r"/fa/news/(\d{4})/(\d{1,2})/(\d{1,2})/", urlparse(full_url).path)
        if match:
            try:
                published = datetime(int(match.group(1)), int(match.group(2)), int(match.group(3)), tzinfo=timezone.utc).timestamp()
            except Exception:
                pass
        published += max(0, 1000 - index) * 0.001
        out.append({"url": full_url, "title": title, "description": "", "image_url": "",
                    "video_urls": [], "source_name": source["name"], "published_at": published})
    return out[:45]


def collect_latest_items():
    all_items = []
    for source in SOURCES:
        try:
            items = parse_tasnim_listing(source) if source["kind"] == "html" else parse_rss_source(source)
            log(f"{source['name']}: {len(items)} خبر از منبع دریافت شد.")
            all_items.extend(items)
        except Exception as error:
            log(f"منبع {source['name']} فعلاً در دسترس نیست: {error}")

    unique, seen = [], set()
    for item in sorted(all_items, key=lambda x: x.get("published_at", 0), reverse=True):
        key = url_dedupe_key(item.get("url", ""))
        if not key or key in seen:
            continue
        seen.add(key)
        item["url"] = normalize_url(item.get("url", ""))
        unique.append(item)
    return unique


def extract_jsonld_article(soup):
    results = []
    for script in soup.find_all("script", attrs={"type": "application/ld+json"}):
        raw = script.string or script.get_text(" ", strip=True)
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue
        stack = data if isinstance(data, list) else [data]
        while stack:
            item = stack.pop(0)
            if isinstance(item, list):
                stack.extend(item)
            elif isinstance(item, dict):
                if isinstance(item.get("@graph"), list):
                    stack.extend(item["@graph"])
                kind = item.get("@type", "")
                kinds = kind if isinstance(kind, list) else [kind]
                if any("article" in str(k).lower() or "news" in str(k).lower() for k in kinds):
                    results.append(item)
    return results[0] if results else {}


def get_meta(soup, *names):
    for name in names:
        tag = soup.find("meta", attrs={"property": name}) or soup.find("meta", attrs={"name": name})
        if tag and tag.get("content"):
            return clean_text(tag["content"])
    return ""


def find_article_body(soup, jsonld):
    body = jsonld.get("articleBody")
    if isinstance(body, str) and len(clean_text(body)) > 150:
        return clean_text(body)

    selectors = [
        "article .news-content", "article .news-body", "article .article-body",
        ".news-content", ".news-body", ".news_body", ".news-content-body",
        ".article-body", ".article-content", ".single-content", ".content-text",
        ".news-text", ".body-content", "article", "main",
    ]
    for selector in selectors:
        node = soup.select_one(selector)
        if node:
            paragraphs = [clean_text(p.get_text(" ", strip=True)) for p in node.find_all("p")]
            paragraphs = [p for p in paragraphs if len(p) >= 25 and not p.startswith(("واژه های کاربردی", "انتهای پیام"))]
            joined = "\n\n".join(dict.fromkeys(paragraphs))
            if len(joined) >= 200:
                return joined

    heading = soup.find("h1")
    node = heading
    for _ in range(8):
        if not node or not getattr(node, "parent", None):
            break
        node = node.parent
        paragraphs = [clean_text(p.get_text(" ", strip=True)) for p in node.find_all("p")]
        paragraphs = [p for p in paragraphs if len(p) >= 25]
        joined = "\n\n".join(dict.fromkeys(paragraphs))
        if len(joined) >= 200:
            return joined

    paragraphs = []
    for p in soup.find_all("p"):
        text = clean_text(p.get_text(" ", strip=True))
        if len(text) >= 35 and not any(word in text for word in ("ما را دنبال کنید", "درباره ما", "پربیننده‌ترین اخبار")):
            paragraphs.append(text)
    return "\n\n".join(dict.fromkeys(paragraphs))


def extract_image_url(soup, jsonld, base_url):
    image = jsonld.get("image") if jsonld else None
    if isinstance(image, list) and image:
        image = image[0]
    if isinstance(image, dict):
        image = image.get("url") or image.get("contentUrl")
    if isinstance(image, str) and image:
        return absolute_url(image, base_url)

    candidate = get_meta(soup, "og:image", "twitter:image")
    if candidate:
        return absolute_url(candidate, base_url)

    containers = soup.select("article, main, .news-content, .news-body, .article-content")
    search_nodes = containers or [soup]
    for container in search_nodes:
        for img in container.find_all("img"):
            src = img.get("data-src") or img.get("data-original") or img.get("src")
            if not src:
                continue
            full = absolute_url(src, base_url)
            low = full.lower()
            if any(word in low for word in ("logo", "avatar", "icon", "placeholder")):
                continue
            if low.startswith("http"):
                return full
    return ""


def extract_direct_video_urls(soup, jsonld, base_url):
    found = []
    candidates = []
    for meta_name in ("og:video", "og:video:url", "twitter:player:stream"):
        value = get_meta(soup, meta_name)
        if value:
            candidates.append(value)
    for video in soup.find_all("video"):
        if video.get("src"):
            candidates.append(video.get("src"))
        for source in video.find_all("source"):
            if source.get("src"):
                candidates.append(source.get("src"))
    if isinstance(jsonld, dict):
        for key in ("contentUrl", "embedUrl"):
            val = jsonld.get("video")
            if isinstance(val, dict) and val.get(key):
                candidates.append(val[key])
            elif isinstance(val, str):
                candidates.append(val)
    for candidate in candidates:
        full = absolute_url(candidate, base_url)
        path = urlparse(full).path.lower()
        if path.endswith(DIRECT_VIDEO_EXTENSIONS) and full not in found:
            found.append(full)
    return found[:2]


def parse_article(url, source_name="", fallback_title="", fallback_body="", fallback_image="", fallback_videos=None):
    soup, final_url = fetch_soup(url)
    jsonld = extract_jsonld_article(soup)
    title = (jsonld.get("headline") if jsonld else "") or get_meta(soup, "og:title", "twitter:title")
    if not title:
        heading = soup.find("h1")
        title = heading.get_text(" ", strip=True) if heading else "خبر جدید"
    title = clean_text(title)
    suffixes = ["خبرگزاری تسنیم", "تسنیم", "ایسنا", "مهر", "تابناک", "خبرآنلاین", "عصر ایران", "باشگاه خبرنگاران جوان"]
    if source_name:
        suffixes.append(source_name)
    suffix_pattern = "|".join(re.escape(x) for x in sorted(set(suffixes), key=len, reverse=True))
    title = re.sub(r"\s*[-|–]\s*(?:" + suffix_pattern + r")\s*$", "", clean_text(title)).strip()
    if not title or title == "خبر جدید":
        title = clean_text(fallback_title) or "خبر جدید"
    body = find_article_body(soup, jsonld) or clean_text(fallback_body)
    image_url = extract_image_url(soup, jsonld, final_url) or fallback_image
    video_urls = extract_direct_video_urls(soup, jsonld, final_url)
    if not video_urls and fallback_videos:
        video_urls = list(fallback_videos)
    return {
        "url": normalize_url(final_url),
        "title": title,
        "body": body,
        "image_url": image_url,
        "video_urls": video_urls,
        "source_name": source_name or "منبع خبر",
    }


def markdown_escape(text):
    text = text or ""
    for char in ("\\", "*", "_", "`", "[", "]"):
        text = text.replace(char, "\\" + char)
    return text


def markdown_url(url):
    from urllib.parse import quote
    return quote(url, safe=":/?#[]@!$&'()*+,;=%-._~")


def source_footer(url, source_name="منبع خبر"):
    source_link = f"[منبع: {markdown_escape(source_name)}]({markdown_url(url)})"
    channel_link = f"[کانال ما]({markdown_url(CHANNEL_LINK)})"
    return source_link + "\n" + channel_link


def style_body(body):
    body = clean_text(body)
    paragraphs = [p.strip() for p in re.split(r"\n\s*\n", body) if p.strip()]
    styled = []
    for index, paragraph in enumerate(paragraphs):
        symbol = "🔷" if index % 2 == 0 else "🔶"
        styled.append(symbol + " " + markdown_escape(paragraph))
    return "\n\n".join(styled)


def choose_excerpt(body, budget):
    body = clean_text(body)
    if len(body) <= max(0, budget):
        return body, len(body)
    if budget <= 0:
        return "", 0
    candidate = body[:budget]
    cut = max(candidate.rfind("\n\n"), candidate.rfind(". "), candidate.rfind("؟ "), candidate.rfind("! "))
    if cut >= budget * 0.55:
        if candidate[cut:cut+2] in (". ", "؟ ", "! "):
            candidate = candidate[:cut+1]
        else:
            candidate = candidate[:cut]
    return candidate.rstrip(), len(candidate.rstrip())


def truncate_article_body(body, limit=MAX_ARTICLE_BODY_CHARS):
    body = clean_text(body)
    if len(body) <= limit:
        return body
    excerpt, _ = choose_excerpt(body, max(1, limit - 1))
    if not excerpt:
        excerpt = body[:max(1, limit - 1)].rstrip()
    return excerpt.rstrip() + "…"


def build_caption(title, body, url, source_name="منبع خبر", max_chars=MAX_CAPTION_CHARS):
    title_md = "*" + markdown_escape(clean_text(title)) + "*"
    footer = source_footer(url, source_name)
    body = truncate_article_body(body, MAX_ARTICLE_BODY_CHARS)
    budget = max(0, max_chars - len(title_md) - len(footer) - 8)
    excerpt, _ = choose_excerpt(body, budget)
    caption = title_md
    if excerpt:
        caption += "\n\n" + style_body(excerpt)
    caption += "\n\n" + footer
    while len(caption) > max_chars and excerpt:
        excerpt, _ = choose_excerpt(excerpt, max(0, len(excerpt) - 40))
        caption = title_md + ("\n\n" + style_body(excerpt) if excerpt else "") + "\n\n" + footer
    return caption, len(excerpt)


def split_text(text, limit=3900):
    text = text.strip()
    pieces = []
    while len(text) > limit:
        cut = text.rfind("\n\n", 0, limit)
        if cut < int(limit * 0.55):
            cut = text.rfind("\n", 0, limit)
        if cut < int(limit * 0.55):
            cut = limit
        pieces.append(text[:cut].strip())
        text = text[cut:].strip()
    if text:
        pieces.append(text)
    return pieces


def download_bytes(url, max_bytes):
    response = session.get(url, stream=True, timeout=REQUEST_TIMEOUT)
    response.raise_for_status()
    content_type = response.headers.get("Content-Type", "application/octet-stream").split(";")[0].strip().lower()
    size_header = response.headers.get("Content-Length")
    if size_header and int(size_header) > max_bytes:
        response.close()
        raise RuntimeError("حجم فایل از سقف ارسال بله بیشتر است.")
    data = bytearray()
    for chunk in response.iter_content(chunk_size=64 * 1024):
        if not chunk:
            continue
        data.extend(chunk)
        if len(data) > max_bytes:
            response.close()
            raise RuntimeError("حجم فایل از سقف ارسال بله بیشتر است.")
    response.close()
    return bytes(data), content_type


def send_photo_url(image_url, caption):
    data_bytes, content_type = download_bytes(image_url, MAX_IMAGE_BYTES)
    if not content_type.startswith("image/"):
        raise RuntimeError("آدرس تصویر، فایل تصویری برنگرداند.")
    ext = mimetypes.guess_extension(content_type) or ".jpg"
    if ext == ".jpe":
        ext = ".jpg"
    files = {"photo": ("news_image" + ext, data_bytes, content_type)}
    bale_request("sendPhoto", data={
        "chat_id": DESTINATION_CHAT,
        "caption": caption,
        "parse_mode": "Markdown",
    }, files=files, timeout=90)


def send_video_url(video_url, caption):
    data_bytes, content_type = download_bytes(video_url, MAX_VIDEO_BYTES)
    if not content_type.startswith("video/") and not video_url.lower().split("?")[0].endswith(DIRECT_VIDEO_EXTENSIONS):
        raise RuntimeError("آدرس ویدئو، فایل ویدئویی مستقیم برنگرداند.")
    ext = os.path.splitext(urlparse(video_url).path)[1].lower() or ".mp4"
    files = {"video": ("news_video" + ext, data_bytes, content_type or "video/mp4")}
    bale_request("sendVideo", data={
        "chat_id": DESTINATION_CHAT,
        "caption": caption,
        "parse_mode": "Markdown",
    }, files=files, timeout=120)


def publish_article(article):
    title = clean_text(article.get("title")) or "خبر جدید"
    body = truncate_article_body(article.get("body", ""))
    url = article["url"]
    source_name = article.get("source_name") or "منبع خبر"
    caption, _ = build_caption(title, body, url, source_name)

    for video_url in (article.get("video_urls", []) or [])[:1]:
        try:
            send_video_url(video_url, caption)
            log(f"خبر و ویدئو ارسال شد ({source_name}): {title[:65]}")
            return
        except Exception as error:
            log("ویدئو قابل ارسال نبود؛ تصویر/متن را امتحان می‌کنم: " + str(error))

    image_url = article.get("image_url") or ""
    if image_url:
        try:
            send_photo_url(image_url, caption)
            log(f"خبر و تصویر ارسال شد ({source_name}): {title[:65]}")
            return
        except Exception as error:
            log("تصویر قابل ارسال نبود؛ متن را ارسال می‌کنم: " + str(error))

    text = "*" + markdown_escape(title) + "*"
    if body:
        text += "\n\n" + style_body(body)
    text += "\n\n" + source_footer(url, source_name)
    bale_request("sendMessage", data={
        "chat_id": DESTINATION_CHAT,
        "text": text,
        "parse_mode": "Markdown",
        "disable_web_page_preview": "true",
    }, timeout=60)
    log(f"خبر متنی ارسال شد ({source_name}): {title[:65]}")


def load_state():
    defaults = {
        "sent_urls": [],
        "sent_titles": [],
        "ignored_urls": [],
    }
    if not os.path.exists(STATE_FILE):
        return defaults
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as file:
            data = json.load(file)
        if not isinstance(data, dict):
            raise ValueError("invalid state")
        for key, value in defaults.items():
            data.setdefault(key, value)
        return data
    except Exception as error:
        log("فایل وضعیت خوانده نشد: " + str(error))
        return defaults


def save_state(state):
    try:
        os.makedirs(os.path.dirname(STATE_FILE), exist_ok=True)
    except Exception:
        pass
    for key, limit in (("sent_urls", 3000), ("sent_titles", 1000), ("ignored_urls", 4000)):
        state[key] = list(dict.fromkeys(state.get(key, [])))[-limit:]
    temp_name = STATE_FILE + ".tmp"
    with open(temp_name, "w", encoding="utf-8") as file:
        json.dump(state, file, ensure_ascii=False, indent=2)
    os.replace(temp_name, STATE_FILE)


def normalize_title(title):
    title = clean_text(title).lower()
    title = title.replace("ي", "ی").replace("ك", "ک").replace("ۀ", "ه")
    title = re.sub(r"[\u064B-\u065F\u0670]", "", title)
    title = re.sub(r"(?:خبرگزاری|خبرگزاریِ|گزارش)\s+", "", title)
    title = re.sub(r"[^0-9a-z\u0600-\u06ff]+", " ", title)
    return " ".join(title.split())


def title_is_duplicate(title, previous_titles):
    current = normalize_title(title)
    if len(current) < 12:
        return False
    tokens = {t for t in current.split() if len(t) > 1}
    for old_title in previous_titles[-800:]:
        old = normalize_title(old_title)
        if not old or len(old) < 12:
            continue
        if current == old:
            return True
        ratio = difflib.SequenceMatcher(None, current, old).ratio()
        if ratio >= 0.88:
            return True
        old_tokens = {t for t in old.split() if len(t) > 1}
        if len(tokens) >= 4 and len(old_tokens) >= 4:
            overlap = len(tokens & old_tokens)
            smaller = min(len(tokens), len(old_tokens))
            if overlap >= 4 and overlap / max(1, smaller) >= 0.82:
                return True
    return False


def process_new_articles(state):
    items = collect_latest_items()
    if not items:
        log("از هیچ‌کدام از منابع خبری، مطلب قابل استفاده دریافت نشد.")
        return

    sent_norm = {url_dedupe_key(u) for u in state.get("sent_urls", [])}
    ignored_norm = {url_dedupe_key(u) for u in state.get("ignored_urls", [])}

    new_items = []
    url_seen_this_poll = set()
    for item in items:
        url_key = url_dedupe_key(item.get("url", ""))
        if not url_key or url_key in sent_norm or url_key in ignored_norm:
            continue
        if url_key in url_seen_this_poll:
            continue
        url_seen_this_poll.add(url_key)
        title = clean_text(item.get("title", ""))
        if title and title_is_duplicate(title, state.get("sent_titles", [])):
            state.setdefault("ignored_urls", []).append(normalize_url(item.get("url", "")))
            ignored_norm.add(url_key)
            log("خبر مشابهِ قبلی بود و رد شد: " + title[:70])
            continue
        new_items.append(item)

    if not new_items:
        log("خبر تازه و غیرتکراری پیدا نشد.")
        return

    chosen = new_items[:MAX_NEW_POSTS_PER_CYCLE]
    log(f"{len(chosen)} خبر تازه برای ارسال انتخاب شد.")

    sent_this_poll = 0
    for item in chosen:
        url = item["url"]
        url_key = url_dedupe_key(url)
        title_hint = clean_text(item.get("title", ""))
        sent_norm = {url_dedupe_key(u) for u in state.get("sent_urls", [])}
        ignored_norm = {url_dedupe_key(u) for u in state.get("ignored_urls", [])}
        if url_key in sent_norm or url_key in ignored_norm:
            continue
        if title_hint and title_is_duplicate(title_hint, state.get("sent_titles", [])):
            state.setdefault("ignored_urls", []).append(normalize_url(url))
            save_state(state)
            continue

        try:
            try:
                article = parse_article(
                    url,
                    source_name=item.get("source_name", "منبع خبر"),
                    fallback_title=title_hint,
                    fallback_body=item.get("description", ""),
                    fallback_image=item.get("image_url", ""),
                    fallback_videos=item.get("video_urls", []),
                )
            except Exception as scrape_error:
                log("صفحهٔ خبر باز نشد؛ از خلاصهٔ RSS استفاده می‌کنم: " + str(scrape_error))
                article = {
                    "url": url,
                    "title": title_hint or "خبر جدید",
                    "body": item.get("description", ""),
                    "image_url": item.get("image_url", ""),
                    "video_urls": item.get("video_urls", []),
                    "source_name": item.get("source_name", "منبع خبر"),
                }
            if not article.get("title") or article.get("title") == "خبر جدید":
                article["title"] = title_hint or "خبر جدید"
            if not article.get("body"):
                article["body"] = item.get("description", "")
            if not article.get("image_url"):
                article["image_url"] = item.get("image_url", "")
            article["source_name"] = item.get("source_name", "منبع خبر")

            publish_article(article)

            state.setdefault("sent_urls", []).extend([normalize_url(url), normalize_url(article.get("url", url))])
            actual_title = clean_text(article.get("title") or title_hint)
            if actual_title:
                state.setdefault("sent_titles", []).append(actual_title)
            sent_this_poll += 1
            save_state(state)
            log("خبر با موفقیت ثبت شد: " + actual_title[:80])
            time.sleep(1.5)
        except KeyboardInterrupt:
            raise
        except Exception as error:
            log("ارسال خبر ناموفق بود: " + url + " | " + str(error))
            time.sleep(1)


def main():
    print("=" * 52)
    print("ربات خبرخوان چندخبرگزاری")
    print("=" * 52)
    validate_settings()
    state = load_state()
    while True:
        try:
            process_new_articles(state)
        except KeyboardInterrupt:
            log("ربات متوقف شد.")
            break
        except Exception as error:
            log("خطای بررسی اخبار: " + str(error))
        time.sleep(CHECK_INTERVAL_SECONDS)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        log("ربات متوقف شد.")
    except Exception as fatal_error:
        print("خطای شروع ربات:", fatal_error)
