import datetime
import math
from datetime import timezone, timedelta
import requests
from bs4 import BeautifulSoup
import os
import csv
import pickle
from collections import defaultdict
from io import BytesIO

# =========================================================
# CONSTANTES GLOBALES
# =========================================================
COL_TZ = timezone(timedelta(hours=-5))   # America/Bogota

VALID_NOT_STARTED_STATUSES = {"NS"}

ODDS_API_KEY = os.getenv("ODDS_API_KEY", "TU_API_KEY_AQUI")
ODDS_API_BASE = "https://api.the-odds-api.com/v4"

ODDS_API_SPORT_KEYS = {
    "football":   "soccer_epl",
    "basketball": "basketball_nba",
    "tenis":      "tennis_atp",
}

MAX_ODDS_API_CALLS_PER_RUN = 5
_odds_api_calls_used = 0

_HTTP_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                   "AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/120.0.0.0 Safari/537.36"),
    "Accept-Language": "en-US,en;q=0.9",
}

# Headers específicos para stats.nba.com (requeridos o devuelve 403)
_NBA_HEADERS = {
    "Host": "stats.nba.com",
    "Connection": "keep-alive",
    "User-Agent": _HTTP_HEADERS["User-Agent"],
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Origin": "http://stats.nba.com",
    "Referer": "http://stats.nba.com/",
    "x-nba-stats-origin": "stats",
    "x-nba-stats-token": "true",
}

# Rutas de caché para modelos
_CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".cache")
os.makedirs(_CACHE_DIR, exist_ok=True)

# Caché por circuito (ATP/WTA) para no mezclar ratings
_ELO_TENNIS_CACHE_TEMPLATE = os.path.join(_CACHE_DIR, "elo_tennis_{circuit}.pkl")
_NBA_METRICS_CACHE = os.path.join(_CACHE_DIR, "nba_metrics.pkl")

# Constantes del modelo Elo
ELO_INITIAL = 1500.0
ELO_K_CONSTANT = 32.0
ELO_SCALE = 400.0

ROUND_COEFF = {
    "F": 1.0, "BR": 0.95, "SF": 0.9, "QF": 0.85, "RR": 0.85,
    "R16": 0.8, "R32": 0.8, "R64": 0.75, "R128": 0.75, "ER": 0.75,
}
SERIES_COEFF = {
    "Grand Slam": 1.0, "Masters Cup": 0.9, "Masters": 0.85,
    "ATP500": 0.8, "ATP250": 0.75, "International": 0.75,
}
SURFACES = {"Hard", "Clay", "Grass", "Carpet"}


# =========================================================
# HELPERS DE FECHA/HORA
# =========================================================
def _now_col() -> datetime.datetime:
    return datetime.datetime.now(COL_TZ)


def _today_col() -> str:
    return _now_col().strftime("%Y-%m-%d")


def _parse_time_str(time_str: str) -> tuple[int, int, int] | None:
    """Parsea 'HH:MM:SS' o 'HH:MM'. Devuelve (h, m, s) o None."""
    if not time_str:
        return None
    try:
        parts = time_str.strip().split(":")
        h = int(parts[0])
        m = int(parts[1]) if len(parts) > 1 else 0
        s = int(parts[2]) if len(parts) > 2 else 0
        return (h, m, s)
    except Exception:
        return None


def _utc_to_col(dt_utc: datetime.datetime) -> datetime.datetime:
    return dt_utc.astimezone(COL_TZ)


def _event_datetime_col_utc(match: dict) -> datetime.datetime | None:
    """
    Devuelve el datetime del evento en zona Colombia, o None si no se puede.

    Estrategia (en orden de prioridad):
    1. `strTimestamp` — ISO 8601 explícito en UTC.
    2. `dateEvent` + `strTime` — ambos tratados como UTC.
    3. `strTime` + fecha Colombia de hoy — último recurso.

    Prueba TRES fechas base UTC (ayer, hoy, mañana) para cubrir la frontera
    de día: un partido a las 02:00 UTC del 11/09 es 21:00 COL del 10/09.
    """
    now_col = _now_col()

    # --- Opción 1: strTimestamp ---
    ts = match.get("strTimestamp")
    if ts:
        try:
            dt_utc = datetime.datetime.fromisoformat(ts.replace("Z", "+00:00"))
            if dt_utc.tzinfo is None:
                dt_utc = dt_utc.replace(tzinfo=timezone.utc)
            return _utc_to_col(dt_utc)
        except Exception:
            pass

    # --- Opción 2: dateEvent + strTime ---
    de = match.get("dateEvent")
    t = _parse_time_str(match.get("strTime", ""))
    if t is None:
        return None

    today_utc = now_col.astimezone(timezone.utc).date()
    base_dates = [
        today_utc - timedelta(days=1),
        today_utc,
        today_utc + timedelta(days=1),   # fix: cubre partidos de madrugada UTC
    ]
    if de:
        try:
            base_dates.append(datetime.date.fromisoformat(de))
        except Exception:
            pass

    for base in base_dates:
        try:
            dt_utc = datetime.datetime.combine(
                base, datetime.time(*t), tzinfo=timezone.utc
            )
            dt_col = _utc_to_col(dt_utc)
            if dt_col.date() == now_col.date():
                return dt_col
        except Exception:
            continue

    # --- Opción 3: último recurso (asumir Colombia) ---
    try:
        return datetime.datetime.combine(
            now_col.date(), datetime.time(*t), tzinfo=COL_TZ
        )
    except Exception:
        return None


# =========================================================
# FALLBACK: THE ODDS API
# =========================================================
def _fetch_odds_api(sport_key: str,
                    home_team: str,
                    away_team: str,
                    commence_time_iso: str | None = None) -> dict | None:
    global _odds_api_calls_used

    if not ODDS_API_KEY or ODDS_API_KEY == "TU_API_KEY_AQUI":
        return None
    if _odds_api_calls_used >= MAX_ODDS_API_CALLS_PER_RUN:
        print("[INFO] The Odds API: límite de llamadas por ejecución alcanzado.")
        return None

    try:
        url_events = f"{ODDS_API_BASE}/sports/{sport_key}/events"
        r = requests.get(url_events,
                         params={"apiKey": ODDS_API_KEY, "dateFormat": "iso"},
                         timeout=15)
        if r.status_code != 200:
            print(f"[WARN] The Odds API events HTTP {r.status_code}")
            return None
        events = r.json() or []

        def _norm(s: str) -> str:
            return (s or "").lower().replace(".", "").replace("-", " ").strip()

        target_home = _norm(home_team)
        target_away = _norm(away_team)

        event_id = None
        matched_event = None
        for ev in events:
            ev_home = _norm(ev.get("home_team", ""))
            ev_away = _norm(ev.get("away_team", ""))
            if (target_home in ev_home or ev_home in target_home) and \
               (target_away in ev_away or ev_away in target_away):
                ct = ev.get("commence_time", "")
                if commence_time_iso and ct and ct < commence_time_iso:
                    continue
                event_id = ev.get("id")
                matched_event = ev
                break

        if not event_id:
            return None

        _odds_api_calls_used += 1
        url_odds = f"{ODDS_API_BASE}/sports/{sport_key}/events/{event_id}/odds"
        r2 = requests.get(url_odds, params={
            "apiKey": ODDS_API_KEY,
            "regions": "eu",
            "markets": "h2h,totals",
            "oddsFormat": "decimal",
            "dateFormat": "iso",
        }, timeout=15)
        if r2.status_code != 200:
            print(f"[WARN] The Odds API odds HTTP {r2.status_code}")
            return None

        data = r2.json()
        bookmakers = data.get("bookmakers", []) or []
        if not bookmakers:
            return None

        best_home_odd = 0.0
        best_over_odd = 0.0
        for bm in bookmakers:
            for market in bm.get("markets", []):
                if market.get("key") == "h2h":
                    for outcome in market.get("outcomes", []):
                        if outcome.get("name") == matched_event.get("home_team"):
                            best_home_odd = max(best_home_odd,
                                                float(outcome.get("price", 0) or 0))
                elif market.get("key") == "totals":
                    for outcome in market.get("outcomes", []):
                        if outcome.get("name") == "Over":
                            best_over_odd = max(best_over_odd,
                                                float(outcome.get("price", 0) or 0))

        return {
            "h2h_home": best_home_odd or None,
            "over": best_over_odd or None,
            "source": "The Odds API",
            "event_id": event_id,
        }
    except Exception as e:
        print(f"[WARN] The Odds API error: {e}")
        return None


# =========================================================
# FOREBET: VALIDACIÓN DE URL CON FALLBACK
# =========================================================
def _fetch_forebet_football_html(today_col: str) -> str | None:
    """
    Intenta obtener el HTML de Forebet para fútbol.
    Orden:
      1. URL con fecha exacta: predictions-1x2/YYYY-MM-DD
      2. URL "for-today" sin fecha (fallback)
    Valida HTTP 200, tamaño > 5000 bytes e indicios de tabla.
    """
    urls_to_try = [
        f"https://www.forebet.com/en/football-predictions/predictions-1x2/{today_col}",
        "https://www.forebet.com/en/football-tips-and-predictions-for-today",
    ]

    for url in urls_to_try:
        try:
            r = requests.get(url, headers=_HTTP_HEADERS, timeout=15)
            if r.status_code != 200:
                print(f"[WARN] Forebet HTTP {r.status_code} en: {url}")
                continue
            html = r.text or ""
            if len(html) < 5000:
                print(f"[WARN] Forebet respuesta muy corta ({len(html)} bytes): {url}")
                continue
            has_table = ("predictions-1x2" in html or "Prob" in html or
                         "1X2" in html or "homeTeam" in html or "awayTeam" in html)
            if not has_table:
                print(f"[WARN] Forebet sin indicios de tabla en: {url}")
                continue
            print(f"[INFO] Forebet OK con URL: {url}")
            return html
        except Exception as e:
            print(f"[WARN] Forebet error en {url}: {e}")
            continue

    print("[WARN] Forebet: ninguna URL devolvió datos válidos.")
    return None


def _scrape_forebet_rows(html: str) -> list[dict]:
    """Extrae filas de predicciones del HTML de Forebet."""
    out = []
    if not html:
        return out
    try:
        soup = BeautifulSoup(html, "html.parser")
        rows = soup.select("div.rcnt")[:12]
        for row in rows:
            try:
                home_el = row.select_one(".homeTeam")
                away_el = row.select_one(".awayTeam")
                probs = row.select(".fprc span")
                if not (home_el and away_el and len(probs) >= 3):
                    continue
                home = home_el.get_text(strip=True)
                away = away_el.get_text(strip=True)
                p_home = int(probs[0].get_text(strip=True).replace("%", "")) / 100
                odd_el = row.select_one(".avg")
                try:
                    ref_odd = float(odd_el.get_text(strip=True)) if odd_el else None
                except ValueError:
                    ref_odd = None
                out.append({
                    "teams": [home, away],
                    "prob_home": p_home,
                    "odds": ref_odd,
                })
            except Exception:
                continue
    except Exception as e:
        print(f"[WARN] Forebet parse error: {e}")
    return out


# =========================================================
# MODELO ELO PARA TENIS (datos reales: tennis-data.co.uk)
# =========================================================
def _download_tennis_data(year: int, circuit: str = "atp") -> list[dict] | None:
    """
    Descarga el archivo de resultados de tennis-data.co.uk para un año dado.

    El sitio sirve Excel (.xlsx / .xls), no CSV. Se intenta:
      1. .xlsx (años recientes)
      2. .xls  (años antiguos)
      3. .csv  (algunos años tienen versión CSV)

    Circuit: 'atp' o 'wta'.
    URL ATP: http://www.tennis-data.co.uk/YYYY/YYYY.{ext}
    URL WTA: http://www.tennis-data.co.uk/YYYYw/YYYY.{ext}
    """
    if circuit.lower() == "atp":
        base = f"http://www.tennis-data.co.uk/{year}/{year}"
    else:
        base = f"http://www.tennis-data.co.uk/{year}w/{year}"

    extensions = [".xlsx", ".xls", ".csv"]

    for ext in extensions:
        url = base + ext
        try:
            r = requests.get(url, headers=_HTTP_HEADERS, timeout=30)
            print(f"[DEBUG] tennis-data {year}{ext}: status={r.status_code} "
                  f"content_type={r.headers.get('Content-Type')} "
                  f"len={len(r.content)}")
            if r.status_code != 200:
                continue

            if ext == ".csv":
                text = r.text
                if len(text) < 1000:
                    continue
                reader = csv.DictReader(text.splitlines())
                return list(reader)
            else:
                # Excel: usar pandas (más robusto para .xlsx y .xls)
                try:
                    import pandas as pd
                except ImportError:
                    print("[WARN] pandas no instalado. "
                          "Ejecuta: pip install pandas openpyxl xlrd")
                    return None
                df = pd.read_excel(BytesIO(r.content))
                return df.to_dict(orient="records")
        except Exception as e:
            print(f"[WARN] tennis-data.co.uk {year} {ext}: {e}")
            continue

    print(f"[WARN] tennis-data.co.uk: no se pudo descargar {year} ({circuit})")
    return None


def _build_elo_ratings(start_year: int = 2000,
                       end_year: int | None = None,
                       circuit: str = "atp") -> dict:
    """
    Construye ratings Elo generales y por superficie a partir de los archivos
    históricos de tennis-data.co.uk.

    Estructura devuelta:
    {
      "general": {player_name: rating},
      "Hard":    {player_name: rating},
      "Clay":    {player_name: rating},
      "Grass":   {player_name: rating},
      "Carpet":  {player_name: rating},
      "_meta":   {"last_match_date": "...", "matches_processed": N, ...}
    }

    Fórmula Elo:
      R_new = R_old + K_eff * (S - E)
      E = 1 / (1 + 10^((R_opp - R_player)/400))
      K_eff = K_base * coeff_round * coeff_series
    """
    if end_year is None:
        end_year = _now_col().year

    # Cache por circuito (ATP/WTA no se mezclan)
    cache_path = _ELO_TENNIS_CACHE_TEMPLATE.format(circuit=circuit)
    if os.path.exists(cache_path):
        try:
            with open(cache_path, "rb") as f:
                cached = pickle.load(f)
            meta = cached.get("_meta", {})
            if meta.get("built_date") == _today_col() and \
               meta.get("circuit") == circuit:
                print(f"[INFO] Elo tenis cargado de cache ({circuit}).")
                return cached
        except Exception:
            pass

    print(f"[INFO] Construyendo Elo tenis {circuit} {start_year}-{end_year}...")

    ratings = {"general": defaultdict(lambda: ELO_INITIAL)}
    for s in SURFACES:
        ratings[s] = defaultdict(lambda: ELO_INITIAL)

    matches_processed = 0
    last_date = ""

    for year in range(start_year, end_year + 1):
        rows = _download_tennis_data(year, circuit)
        if not rows:
            continue

        def _parse_date(r):
            d = (r.get("Date") or "").strip()
            for fmt in ("%d/%m/%Y", "%Y-%m-%d", "%d/%m/%y"):
                try:
                    return datetime.datetime.strptime(d, fmt).date()
                except Exception:
                    continue
            return datetime.date.min

        rows_sorted = sorted(rows, key=_parse_date)

        for row in rows_sorted:
            winner = (row.get("Winner") or "").strip()
            loser = (row.get("Loser") or "").strip()
            if not winner or not loser:
                continue

            surface_raw = (row.get("Surface") or "").strip()
            surface = surface_raw if surface_raw in SURFACES else "Hard"
            round_raw = (row.get("Round") or "").strip()
            series_raw = (row.get("Series") or "").strip()

            coeff_round = ROUND_COEFF.get(round_raw, 0.8)
            coeff_series = SERIES_COEFF.get(series_raw, 0.75)
            k_eff = ELO_K_CONSTANT * coeff_round * coeff_series

            # Elo general
            rw = ratings["general"][winner]
            rl = ratings["general"][loser]
            e_w = 1.0 / (1.0 + 10 ** ((rl - rw) / ELO_SCALE))
            ratings["general"][winner] = rw + k_eff * (1.0 - e_w)
            ratings["general"][loser] = rl + k_eff * (0.0 - (1.0 - e_w))

            # Elo por superficie
            rw_s = ratings[surface][winner]
            rl_s = ratings[surface][loser]
            e_w_s = 1.0 / (1.0 + 10 ** ((rl_s - rw_s) / ELO_SCALE))
            ratings[surface][winner] = rw_s + k_eff * (1.0 - e_w_s)
            ratings[surface][loser] = rl_s + k_eff * (0.0 - (1.0 - e_w_s))

            matches_processed += 1
            d = _parse_date(row)
            if d != datetime.date.min:
                last_date = d.isoformat()

    result = {
        "general": dict(ratings["general"]),
        "_meta": {
            "built_date": _today_col(),
            "circuit": circuit,
            "last_match_date": last_date,
            "matches_processed": matches_processed,
            "start_year": start_year,
            "end_year": end_year,
        },
    }
    for s in SURFACES:
        result[s] = dict(ratings[s])

    try:
        with open(cache_path, "wb") as f:
            pickle.dump(result, f)
    except Exception as e:
        print(f"[WARN] No se pudo guardar cache Elo: {e}")

    print(f"[INFO] Elo tenis construido: {matches_processed} partidos, "
          f"última fecha {last_date}.")
    return result


def _tennis_elo_prob(elo_data: dict, player_a: str, player_b: str,
                     surface: str = "Hard") -> float:
    """
    Devuelve P(player_a gana) según Elo, usando superficie si hay datos
    suficientes para ambos jugadores; si no, usa Elo general.
    """
    surface = surface if surface in SURFACES else "Hard"
    ra_s = elo_data.get(surface, {}).get(player_a)
    rb_s = elo_data.get(surface, {}).get(player_b)

    if ra_s is not None and rb_s is not None and \
       (ra_s != ELO_INITIAL or rb_s != ELO_INITIAL):
        ra, rb = ra_s, rb_s
    else:
        ra = elo_data.get("general", {}).get(player_a, ELO_INITIAL)
        rb = elo_data.get("general", {}).get(player_b, ELO_INITIAL)

    return 1.0 / (1.0 + 10 ** ((rb - ra) / ELO_SCALE))


# =========================================================
# MODELO POISSON PARA BASKET (NBA Stats API con headers correctos)
# =========================================================
def _fetch_nba_team_metrics(season: str | None = None) -> dict | None:
    """
    Obtiene métricas avanzadas por equipo desde NBA Stats API
    (endpoint teamestimatedmetrics).

    Requiere headers específicos (x-nba-stats-origin, x-nba-stats-token)
    o la API devuelve 403.

    Devuelve dict {team_name_lower: {off_rating, def_rating, pace}} o None.
    """
    if season is None:
        now = _now_col()
        if now.month >= 10:
            season = f"{now.year}-{str(now.year + 1)[-2:]}"
        else:
            season = f"{now.year - 1}-{str(now.year)[-2:]}"

    # Cache de hoy
    if os.path.exists(_NBA_METRICS_CACHE):
        try:
            with open(_NBA_METRICS_CACHE, "rb") as f:
                cached = pickle.load(f)
            meta = cached.get("_meta", {})
            if meta.get("built_date") == _today_col() and \
               meta.get("season") == season:
                print(f"[INFO] NBA metrics cargados de cache ({season}).")
                return cached
        except Exception:
            pass

    url = "https://stats.nba.com/stats/teamestimatedmetrics"
    params = {
        "LeagueID": "00",
        "Season": season,
        "SeasonType": "Regular Season",
    }

    try:
        r = requests.get(url, headers=_NBA_HEADERS, params=params, timeout=20)
        if r.status_code != 200:
            print(f"[WARN] NBA Stats API HTTP {r.status_code}")
            return None
        data = r.json()
        result_sets = data.get("resultSets", [])
        if not result_sets:
            return None
        rs = result_sets[0]
        headers_ = rs.get("headers", [])
        rows = rs.get("rowSet", [])

        def _idx(name):
            try:
                return headers_.index(name)
            except ValueError:
                return None

        i_team = _idx("TEAM_NAME")
        i_off = _idx("E_OFF_RATING")
        i_def = _idx("E_DEF_RATING")
        i_pace = _idx("E_PACE")
        if None in (i_team, i_off, i_def, i_pace):
            print("[WARN] NBA Stats API: columnas esperadas no encontradas.")
            return None

        out = {"_meta": {"built_date": _today_col(), "season": season}}
        for row in rows:
            team = (row[i_team] or "").strip().lower()
            try:
                out[team] = {
                    "off_rating": float(row[i_off]),
                    "def_rating": float(row[i_def]),
                    "pace": float(row[i_pace]),
                }
            except Exception:
                continue

        try:
            with open(_NBA_METRICS_CACHE, "wb") as f:
                pickle.dump(out, f)
        except Exception as e:
            print(f"[WARN] No se pudo guardar cache NBA: {e}")

        print(f"[INFO] NBA metrics cargados: {len(out)-1} equipos ({season}).")
        return out
    except Exception as e:
        print(f"[WARN] NBA Stats API error: {e}")
        return None


def _nba_match_prob(metrics: dict, home_team: str, away_team: str) -> float | None:
    """
    Estima P(home gana) usando eficiencia ofensiva/defensiva y pace.

    Modelo (basado en datos reales de NBA Stats API):
      - Posesiones esperadas = pace_promedio
      - Puntos esperados home = pace × (off_home + def_away) / 200
      - Puntos esperados away = pace × (off_away + def_home) / 200
      - P(home) = 1 / (1 + exp(-(pts_home - pts_away) / 10))
    """
    if not metrics:
        return None
    h = metrics.get(home_team.strip().lower())
    a = metrics.get(away_team.strip().lower())
    if not h or not a:
        return None

    pace = (h["pace"] + a["pace"]) / 2.0
    pts_home = pace * (h["off_rating"] + a["def_rating"]) / 200.0
    pts_away = pace * (a["off_rating"] + h["def_rating"]) / 200.0
    diff = pts_home - pts_away
    return 1.0 / (1.0 + math.exp(-diff / 10.0))


# =========================================================
# 1. OBTENCIÓN DE FIXTURES (multi-source)
# =========================================================
def _fetch_sport_fixtures(sport_name: str,
                          thesportsdb_sport: str,
                          today_col: str,
                          extra_builder=None) -> list:
    """
    Devuelve fixtures para un deporte, filtrados por estado NS y hora futura
    en zona Colombia. Consulta TheSportsDB para varias fechas y deduplica
    por idEvent.
    """
    now_col = _now_col()
    out = []
    seen_ids = set()

    today_utc = now_col.astimezone(timezone.utc).date()
    dates_to_query = {
        today_col,
        (today_utc - timedelta(days=1)).isoformat(),
        today_utc.isoformat(),
        (today_utc + timedelta(days=1)).isoformat(),
    }

    for d in dates_to_query:
        try:
            url = (f"https://www.thesportsdb.com/api/v1/json/3/"
                   f"eventsday.php?d={d}&s={thesportsdb_sport}")
            r = requests.get(url, headers=_HTTP_HEADERS, timeout=15)
            data = r.json()
            for match in (data.get("events") or []):
                event_id = match.get("idEvent", "")
                if event_id and event_id in seen_ids:
                    continue
                if event_id:
                    seen_ids.add(event_id)

                status = (match.get("strStatus") or "").upper()
                if status not in VALID_NOT_STARTED_STATUSES:
                    continue

                dt_col = _event_datetime_col_utc(match)
                if dt_col is None:
                    continue
                if dt_col <= now_col:
                    continue
                if dt_col.date() != now_col.date():
                    continue

                fixture = {
                    "source": "TheSportsDB",
                    "date": today_col,
                    "teams": [match.get("strHomeTeam", ""),
                              match.get("strAwayTeam", "")],
                    "league": match.get("strLeague", ""),
                    "time": dt_col.strftime("%H:%M"),
                    "datetime_col": dt_col.isoformat(),
                    "status": status,
                    "event_id": event_id,
                    "odds": None,
                    "odds_source": None,
                    "raw": match,
                }
                if extra_builder:
                    fixture.update(extra_builder(match))
                out.append(fixture)
        except Exception as e:
            print(f"[WARN] TheSportsDB {sport_name} d={d}: {e}")

    return out


def get_real_fixtures(sports: list) -> dict:
    now_col = _now_col()
    today_col = _today_col()
    fixtures = {}

    print(f"[DEBUG] Hoy Colombia: {today_col} | ahora: {now_col.strftime('%H:%M')}")

    # ---------------- FÚTBOL ----------------
    if "football" in sports:
        def _fb_extra(m):
            # Proxy xG: tiros a puerta / 2 (no es xG real, es aproximación)
            return {
                "xG_home": round((m.get("intHomeShotsOnTarget") or 0) / 2, 1),
                "xG_away": round((m.get("intAwayShotsOnTarget") or 0) / 2, 1),
                "prob_home": None,
            }

        fb = _fetch_sport_fixtures("football", "Soccer", today_col,
                                   extra_builder=_fb_extra)

        forebet_html = _fetch_forebet_football_html(today_col)
        forebet_rows = _scrape_forebet_rows(forebet_html)
        if forebet_rows:
            print(f"[INFO] Forebet: {len(forebet_rows)} filas extraídas.")
        for row in forebet_rows:
            home_fb, away_fb = row["teams"][0], row["teams"][1]
            for f in fb:
                fh, fa = f["teams"][0], f["teams"][1]
                if (fh.lower() in home_fb.lower() or
                        home_fb.lower() in fh.lower()) and \
                   (fa.lower() in away_fb.lower() or
                        away_fb.lower() in fa.lower()):
                    f["prob_home"] = row["prob_home"]
                    if row.get("odds") and not f.get("odds"):
                        f["odds"] = row["odds"]
                        f["odds_source"] = "Forebet"
                    break

        for fx in fb:
            if not fx.get("odds"):
                fallback = _fetch_odds_api(ODDS_API_SPORT_KEYS["football"],
                                           fx["teams"][0], fx["teams"][1],
                                           fx.get("datetime_col"))
                if fallback and fallback.get("h2h_home"):
                    fx["odds"] = fallback["h2h_home"]
                    fx["odds_source"] = "The Odds API"

        fixtures["football"] = fb

    # ---------------- BALONCESTO ----------------
    if "basketball" in sports:
        bb = _fetch_sport_fixtures("basketball", "Basketball", today_col)
        nba_metrics = _fetch_nba_team_metrics()
        if nba_metrics:
            for fx in bb:
                p = _nba_match_prob(nba_metrics, fx["teams"][0], fx["teams"][1])
                if p is not None:
                    fx["prob_home"] = p
                    fx["prob_source"] = "Poisson (NBA Stats API)"
                if not fx.get("odds"):
                    fallback = _fetch_odds_api(ODDS_API_SPORT_KEYS["basketball"],
                                               fx["teams"][0], fx["teams"][1],
                                               fx.get("datetime_col"))
                    if fallback and fallback.get("h2h_home"):
                        fx["odds"] = fallback["h2h_home"]
                        fx["odds_source"] = "The Odds API"
        fixtures["basketball"] = bb

    # ---------------- TENIS ----------------
    if "tenis" in sports:
        def _tennis_extra(m):
            league = (m.get("strLeague") or "").lower()
            surface = "hard" if "hard" in league else (
                "clay" if "clay" in league else "grass"
            )
            return {"surface": surface, "tournament": m.get("strLeague", "")}

        tn = _fetch_sport_fixtures("tenis", "Tennis", today_col,
                                   extra_builder=_tennis_extra)
        elo_data = _build_elo_ratings()
        for fx in tn:
            p = _tennis_elo_prob(elo_data, fx["teams"][0], fx["teams"][1],
                                 fx.get("surface", "Hard").capitalize())
            fx["prob_home"] = p
            fx["prob_source"] = f"Elo {fx.get('surface', 'Hard').capitalize()}"
            if not fx.get("odds"):
                fallback = _fetch_odds_api(ODDS_API_SPORT_KEYS["tenis"],
                                           fx["teams"][0], fx["teams"][1],
                                           fx.get("datetime_col"))
                if fallback and fallback.get("h2h_home"):
                    fx["odds"] = fallback["h2h_home"]
                    fx["odds_source"] = "The Odds API"
        fixtures["tenis"] = tn

    return fixtures


# =========================================================
# 2. VALIDACIÓN COMÚN
# =========================================================
def _is_valid_fixture(event: dict) -> bool:
    now_col = _now_col()
    today_col = _today_col()
    if event.get("date") != today_col:
        return False
    if (event.get("status") or "").upper() not in VALID_NOT_STARTED_STATUSES:
        return False
    dt_iso = event.get("datetime_col")
    if dt_iso:
        try:
            dt = datetime.datetime.fromisoformat(dt_iso)
            if dt <= now_col:
                return False
        except Exception:
            return False
    return True


# =========================================================
# 3. ANÁLISIS POR DEPORTE
# =========================================================
def _logistic(x: float, k: float = 0.8) -> float:
    return 1.0 / (1.0 + math.exp(-k * x))


def analyze_football_pro(event: dict) -> dict:
    if not _is_valid_fixture(event):
        return {"sport": "football", "ev": -100.0, "skip_reason": "inválido"}

    ref_odd = event.get("odds")
    if not ref_odd:
        return {"sport": "football", "ev": -100.0,
                "skip_reason": "sin cuota disponible"}

    p_forebet = event.get("prob_home")
    xG_home = event.get("xG_home", 0.0)
    xG_away = event.get("xG_away", 0.0)

    if p_forebet:
        prob = p_forebet
        model_label = "Forebet"
    else:
        # Fallback: logística sobre diferencia de xG (proxy)
        diff = xG_home - xG_away
        prob = _logistic(diff, k=0.8)
        prob = min(max(prob, 0.35), 0.75)
        model_label = f"xG proxy logístico ({xG_home:.1f}-{xG_away:.1f})"

    # EV CORRECTO: EV = p × odd − 1
    ev = (prob * ref_odd) - 1.0

    return {
        "sport": "football",
        "market": "1X2 (local)",
        "team": event["teams"][0],
        "odds": round(ref_odd, 2),
        "odds_source": event.get("odds_source") or event.get("source"),
        "ev": round(ev, 2),
        "stake": 0,
        "reason": (f"{model_label} | P={prob*100:.1f}% | "
                   f"EV {ev*100:.1f}% | "
                   f"fuente cuota: {event.get('odds_source') or event.get('source')}"),
    }


def analyze_basketball_pro(event: dict) -> dict:
    if not _is_valid_fixture(event):
        return {"sport": "basketball", "ev": -100.0, "skip_reason": "inválido"}

    prob = event.get("prob_home")
    if prob is None:
        return {"sport": "basketball", "ev": -100.0,
                "skip_reason": "sin métricas NBA para este partido"}

    ref_odd = event.get("odds")
    if not ref_odd:
        return {"sport": "basketball", "ev": -100.0,
                "skip_reason": "sin cuota disponible"}

    # EV CORRECTO: EV = p × odd − 1
    ev = (prob * ref_odd) - 1.0

    return {
        "sport": "basketball",
        "market": "1X2 (local)",
        "teams": event["teams"],
        "odds": round(ref_odd, 2),
        "odds_source": event.get("odds_source"),
        "ev": round(ev, 2),
        "stake": 0,
        "reason": (f"{event.get('prob_source', 'Poisson')} | "
                   f"P={prob*100:.1f}% | EV {ev*100:.1f}%"),
    }


def analyze_tennis_pro(event: dict) -> dict:
    if not _is_valid_fixture(event):
        return {"sport": "tenis", "ev": -100.0, "skip_reason": "inválido"}

    prob = event.get("prob_home")
    if prob is None:
        return {"sport": "tenis", "ev": -100.0,
                "skip_reason": "sin Elo para este jugador"}

    ref_odd = event.get("odds")
    if not ref_odd:
        return {"sport": "tenis", "ev": -100.0,
                "skip_reason": "sin cuota disponible"}

    # EV CORRECTO: EV = p × odd − 1
    ev = (prob * ref_odd) - 1.0

    return {
        "sport": "tenis",
        "market": "ML",
        "player": event["teams"][0],
        "odds": round(ref_odd, 2),
        "odds_source": event.get("odds_source"),
        "ev": round(ev, 2),
        "stake": 0,
        "reason": (f"{event.get('prob_source', 'Elo')} | "
                   f"P={prob*100:.1f}% | EV {ev*100:.1f}%"),
    }


# =========================================================
# 4. PIPELINE PRINCIPAL
# =========================================================
def build_picks(sports: list, bank_cop: float,
                min_ev: float = 0.10, max_picks: int = 3) -> list:
    fixtures = get_real_fixtures(sports)

    analysers = {
        "football":   analyze_football_pro,
        "basketball": analyze_basketball_pro,
        "tenis":      analyze_tennis_pro,
    }
    stake_pct = {"football": 0.06, "basketball": 0.08, "tenis": 0.07}

    picks = []
    for sport, events in fixtures.items():
        analyser = analysers.get(sport)
        if not analyser:
            continue
        for ev in events:
            result = analyser(ev)
            if result.get("ev", -100) < min_ev:
                continue
            result["stake"] = round(bank_cop * stake_pct.get(sport, 0.05), 0)
            result["sport"] = sport
            result["source"] = ev.get("source")
            result["time_col"] = ev.get("time")
            result["fixture"] = ev
            picks.append(result)

    picks.sort(key=lambda p: p["ev"], reverse=True)
    return picks[:max_picks]


# =========================================================
# 5. EJEMPLO DE USO
# =========================================================
if __name__ == "__main__":
    bank = 1_000_000  # COP
    picks = build_picks(["football", "basketball", "tenis"], bank_cop=bank)
    print(f"FECHA: {_today_col()} | Banca: {bank:,.0f} COP")
    print(f"{len(picks)} picks VERDE.\n")
    for i, p in enumerate(picks, 1):
        print(f"## PICK {i}: {p['sport'].upper()}")
        print(f"- Fuente: {p.get('source')} | Hora COL: {p.get('time_col')}")
        print(f"- {p.get('market')} | Cuota: {p.get('odds')} "
              f"({p.get('odds_source')}) | EV: {p['ev']*100:.1f}%")
        print(f"- Stake: {p.get('stake'):,.0f} COP")
        print(f"- Razón: {p.get('reason')}\n")
