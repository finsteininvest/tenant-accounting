#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Rent Ledger – einfache Mietshaus-Buchhaltung
Features:
- Bankauszug importieren
- Splits (mehrere Konten/Mietparteien pro Zahlung)
- Auto-Regeln (LIKE + Regex) mit fixed/percent/remainder
- Leases (Sollwerte) + Monats-Soll/Ist-Check
- Aging (Offene Posten) per Stichtag mit FIFO-Anrechnung
- Nebenkostenabrechnungs-Forderungen (NKA) als manuelle Forderungen inkl. Teilzahlungen
"""

import argparse, csv, datetime as dt, decimal, os, sqlite3, sys, calendar, re
from datetime import date, timedelta
from typing import Optional, List, Tuple

DB_FILE = "rent_ledger.db"

# ---------- Helpers ----------

def conn():
    cx = sqlite3.connect(DB_FILE)
    cx.execute("PRAGMA foreign_keys=ON;")
    return cx

def d2c(v: decimal.Decimal) -> int:
    q = (v * 100).quantize(decimal.Decimal("1"))
    return int(q)

def c2s(cents: Optional[int]) -> str:
    if cents is None: return "-"
    return f"{cents/100:.2f}"

def parse_amount(s: str) -> decimal.Decimal:
    s = str(s).strip().replace(" ", "")
    if "," in s and "." in s:
        s = s.replace(".", "").replace(",", ".")
    elif "," in s and "." not in s:
        s = s.replace(",", ".")
    return decimal.Decimal(s)

def parse_date(s: str) -> str:
    s = s.strip()
    for fmt in ("%Y-%m-%d", "%d.%m.%Y", "%d/%m/%Y"):
        try:
            return dt.datetime.strptime(s, fmt).date().isoformat()
        except ValueError:
            pass
    raise ValueError(f"Unbekanntes Datumsformat: {s}")

def ensure_column(cx, table, col, ddl_type):
    cols = [r[1] for r in cx.execute(f"PRAGMA table_info({table})")]
    if col not in cols:
        cx.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl_type}")

def ensure_db():
    created = not os.path.exists(DB_FILE)
    with conn() as cx:
        cx.executescript("""
        PRAGMA foreign_keys=ON;

        CREATE TABLE IF NOT EXISTS tenants (
            id TEXT PRIMARY KEY,
            name TEXT NOT NULL,
            unit TEXT
        );

        CREATE TABLE IF NOT EXISTS accounts (
            number TEXT PRIMARY KEY,
            name TEXT NOT NULL,
            kind TEXT
        );

        CREATE TABLE IF NOT EXISTS bank (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            op_date TEXT NOT NULL,
            amount_cents INTEGER NOT NULL,
            description TEXT
        );

        CREATE TABLE IF NOT EXISTS splits (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            bank_id INTEGER NOT NULL REFERENCES bank(id) ON DELETE CASCADE,
            account TEXT NOT NULL REFERENCES accounts(number),
            tenant_id TEXT REFERENCES tenants(id),
            amount_cents INTEGER NOT NULL,
            note TEXT
        );

        CREATE TABLE IF NOT EXISTS rules (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            match_desc_like TEXT,
            min_amount_cents INTEGER,
            max_amount_cents INTEGER,
            sign TEXT DEFAULT 'any',
            priority INTEGER DEFAULT 100,
            active INTEGER DEFAULT 1
        );

        CREATE TABLE IF NOT EXISTS rule_parts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            rule_id INTEGER NOT NULL REFERENCES rules(id) ON DELETE CASCADE,
            account TEXT NOT NULL REFERENCES accounts(number),
            tenant_id TEXT REFERENCES tenants(id),
            kind TEXT NOT NULL,                  -- fixed | percent | remainder
            value_cents INTEGER,
            value_percent REAL,
            note_template TEXT
        );

        CREATE TABLE IF NOT EXISTS leases (
            tenant_id TEXT NOT NULL REFERENCES tenants(id),
            since_date TEXT NOT NULL,
            until_date TEXT,
            rent_cents INTEGER NOT NULL,
            nk_cents INTEGER NOT NULL,
            due_day INTEGER NOT NULL,
            tolerance_cents INTEGER DEFAULT 0,
            grace_days INTEGER DEFAULT 3,
            PRIMARY KEY (tenant_id, since_date)
        );

        -- Manuelle Forderungen (z. B. Nebenkostenabrechnung Nachzahlung)
        CREATE TABLE IF NOT EXISTS manual_charges (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT NOT NULL REFERENCES tenants(id),
            kind TEXT NOT NULL,              -- 'nka' oder anderes Label
            due_date TEXT NOT NULL,          -- Fälligkeitsdatum (YYYY-MM-DD)
            amount_cents INTEGER NOT NULL,   -- positiv = Forderung, negativ = Gutschrift
            issued_date TEXT,                -- optional
            note TEXT
        );

        CREATE VIEW IF NOT EXISTS v_bank_with_sum AS
        SELECT b.id, b.op_date, b.amount_cents AS bank_amount,
               IFNULL(SUM(s.amount_cents), 0) AS split_sum,
               b.description
        FROM bank b
        LEFT JOIN splits s ON s.bank_id = b.id
        GROUP BY b.id;
        """)

        ensure_column(cx, "rules", "match_desc_regex", "TEXT")

        if created:
            defaults = [
                ("0300","Grundstücke","asset"),
                ("0310","Gebäude","asset"),
                ("0380","Technische Anlagen","asset"),
                ("1000","Bank","asset"),
                ("1360","Mietkautionen","liability"),
                ("2000","Mietforderungen","asset"),
                ("2005","Nebenkostenforderungen","asset"),
                ("2200","Verbindlichkeiten L+L","liability"),
                ("3000","Mieterträge Nettomieten","income"),
                ("3010","Betriebskostenvorauszahlungen","income"),
                ("3020","Erträge BK-Abrechnung","income"),
                ("3030","Sonstige Mieterträge","income"),
                ("4000","Strom Allgemein","expense"),
                ("4010","Wasser/Abwasser","expense"),
                ("4020","Gas/Fernwärme","expense"),
                ("4030","Heizkosten (Brennstoff)","expense"),
                ("4040","Müllabfuhr","expense"),
                ("4050","Straßenreinigung/Winterdienst","expense"),
                ("4060","Gartenpflege","expense"),
                ("4070","Hausmeister (extern)","expense"),
                ("5000","Reparaturen Gebäude","expense"),
                ("5010","Wartung (Heizung/Aufzug/Brand)","expense"),
                ("5100","Verwaltungskosten","expense"),
                ("5200","Rechts- und Beratungskosten","expense"),
                ("5300","Bankgebühren","expense"),
                ("7000","Grundsteuer","expense"),
                ("7010","Versicherungen","expense"),
            ]
            cx.executemany("INSERT OR IGNORE INTO accounts(number,name,kind) VALUES (?,?,?)", defaults)

# ---------- Rules ----------

def sign_of(cents: int) -> str:
    if cents > 0: return "in"
    if cents < 0: return "out"
    return "any"

def match_rule(rule, bank_row) -> bool:
    # rule: (id,name,like,min,max,sign,priority,active,regex)
    _, _, like, min_c, max_c, sign, _, active, regex = rule
    if not active: return False
    b_id, b_date, b_amt, b_desc = bank_row

    if like:
        like_str = like.strip()
        if like_str:
            if like_str.strip("%") not in (b_desc or ""):
                return False

    if regex:
        try:
            if re.search(regex, (b_desc or ""), flags=re.IGNORECASE) is None:
                return False
        except re.error:
            return False

    if min_c is not None and b_amt < min_c: return False
    if max_c is not None and b_amt > max_c: return False
    if sign != 'any' and sign_of(b_amt) != sign: return False
    return True

def apply_rule_to_bank(cx, rule_id: int, bank_id: int):
    b = cx.execute("SELECT id, op_date, amount_cents, description FROM bank WHERE id=?", (bank_id,)).fetchone()
    if not b: return (False, "Bank-ID nicht gefunden.")
    r = cx.execute("""SELECT id,name,match_desc_like,min_amount_cents,max_amount_cents,sign,priority,active,match_desc_regex
                      FROM rules WHERE id=?""", (rule_id,)).fetchone()
    if not r: return (False, "Regel nicht gefunden.")
    if not match_rule(r, b): return (False, "Regel passt nicht auf diese Bankzeile.")

    parts = cx.execute("""SELECT id, account, tenant_id, kind, value_cents, value_percent, note_template
                          FROM rule_parts WHERE rule_id=? ORDER BY id""", (rule_id,)).fetchall()
    if not parts: return (False, "Regel hat keine Parts.")

    bank_amt = b[2]
    remaining = bank_amt
    splits_to_insert = []

    for p in parts:
        _, account, tenant_id, kind, val_c, val_p, note_t = p
        if kind == 'fixed':
            if val_c is None: return (False, "fixed-Part ohne value_cents.")
            amt = int(val_c)
            if (bank_amt > 0 and amt < 0) or (bank_amt < 0 and amt > 0):
                amt = -amt
            remaining -= amt
            splits_to_insert.append((account, tenant_id, amt, note_t))

    percent_sum = 0.0
    percent_parts = []
    for p in parts:
        _, account, tenant_id, kind, val_c, val_p, note_t = p
        if kind == 'percent':
            if val_p is None: return (False, "percent-Part ohne value_percent.")
            percent_sum += float(val_p)
            percent_parts.append((account, tenant_id, float(val_p), note_t))
    if percent_sum > 100.000001:
        return (False, f"Percent-Summe {percent_sum}% > 100%.")

    for (account, tenant_id, pct, note_t) in percent_parts:
        cents = int(round(bank_amt * pct / 100.0))
        remaining -= cents
        splits_to_insert.append((account, tenant_id, cents, note_t))

    remainder_parts = [(p[1], p[2], p[6]) for p in parts if p[3] == 'remainder']
    if len(remainder_parts) > 1: return (False, "Mehr als ein remainder-Part definiert.")
    if len(remainder_parts) == 1:
        account, tenant_id, note_t = remainder_parts[0]
        splits_to_insert.append((account, tenant_id, remaining, note_t))
        remaining = 0

    total = sum(a[2] for a in splits_to_insert)
    if total != bank_amt:
        return (False, f"Summe Splits {c2s(total)} ≠ Bankbetrag {c2s(bank_amt)}. Fehlt ein remainder?")

    for (account, tenant_id, amt, note_t) in splits_to_insert:
        cx.execute("INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (?,?,?,?,?)",
                   (bank_id, account, tenant_id, amt, note_t or f"Auto: Regel {r[1]}"))
    return (True, f"{len(splits_to_insert)} Splits erzeugt (Regel '{r[1]}').")

# ---------- Bank / Splits ----------

def cmd_init(args):
    ensure_db()
    print("Datenbank ist bereit. Standardkonten wurden (ggf.) angelegt.")

def cmd_add_tenant(args):
    with conn() as cx:
        cx.execute("INSERT INTO tenants(id,name,unit) VALUES (?,?,?)",(args.id, args.name, args.unit))
    print(f"Mietpartei {args.id} angelegt.")

def cmd_add_account(args):
    with conn() as cx:
        cx.execute("INSERT INTO accounts(number,name,kind) VALUES (?,?,?)",(args.number, args.name, args.kind))
    print(f"Konto {args.number} – {args.name} angelegt.")

def cmd_import_bank(args):
    ensure_db()
    added = 0
    with open(args.csv, newline="", encoding=args.encoding) as f, conn() as cx:
        reader = csv.DictReader(f, delimiter=args.delimiter)
        for row in reader:
            try:
                date_iso = parse_date(row[args.col_date])
                amt = d2c(parse_amount(row[args.col_amount]))
                desc = row.get(args.col_desc, "").strip()
            except Exception as e:
                if args.strict: raise
                print("Übersprungen wegen Fehler:", e, "→ Zeile:", row)
                continue
            cx.execute("INSERT INTO bank(op_date,amount_cents,description) VALUES (?,?,?)",(date_iso, amt, desc))
            added += 1
    print(f"{added} Bankzeilen importiert.")

def cmd_list_bank(args):
    with conn() as cx:
        rows = cx.execute("SELECT id, op_date, amount_cents, description FROM bank ORDER BY id DESC LIMIT ?",(args.limit,)).fetchall()
    if not rows:
        print("Keine Bankzeilen."); return
    print("ID  | Datum      | Betrag   | Verwendungszweck")
    print("----+------------+----------+------------------")
    for r in rows:
        print(f"{r[0]:<4}| {r[1]:<10} | {c2s(r[2]):>8} | {r[3]}")

def cmd_bank_detail(args):
    with conn() as cx:
        b = cx.execute("SELECT id, op_date, amount_cents, description FROM bank WHERE id=?", (args.bank_id,)).fetchone()
        if not b: print("Bank-ID nicht gefunden."); return
        s = cx.execute("""SELECT s.id, s.account, a.name, s.tenant_id, s.amount_cents, s.note
                          FROM splits s JOIN accounts a ON a.number = s.account
                          WHERE s.bank_id=? ORDER BY s.id""", (args.bank_id,)).fetchall()
        sum_splits = sum(row[4] for row in s)
    print(f"Bank-ID {b[0]} | {b[1]} | Betrag {c2s(b[2])} | {b[3]}")
    print(f"Splits (Summe: {c2s(sum_splits)}, Diff zu Bank: {c2s(sum_splits - b[2])})")
    if not s:
        print("  (keine Splits)")
    else:
        print("  Split-ID | Konto | Kontoname                         | Mieter | Betrag   | Notiz")
        print("  ---------+-------+------------------------------------+--------+----------+------")
        for row in s:
            print(f"  {row[0]:<8} | {row[1]:<5} | {row[2]:<34} | {row[3] or '-':<6} | {c2s(row[4]):>8} | {row[5] or ''}")

def cmd_add_split(args):
    # args.bank_id (int), args.triples (list[str])
    if len(args.triples) % 3 != 0:
        print("Fehler: Splits müssen Dreiergruppen sein: ACCOUNT AMOUNT TENANT_ID")
        print("Beispiel: add-split 2231 3000 58000 M001 3010 18000 M001 3020 5000 M001")
        return

    def parse_amount_token(tok: str) -> int:
        # erlaubt entweder Cents als Integer-String ("58000") oder Euro mit ,/. ("580,00"/"580.00")
        if any(ch in tok for ch in [",", "."]):
            return d2c(parse_amount(tok))
        # sonst als Cents interpretieren
        try:
            return int(tok)
        except ValueError:
            # Fallback: doch als Euro versuchen
            return d2c(parse_amount(tok))

    with conn() as cx:
        # 1) Bankzeile prüfen
        b = cx.execute("SELECT amount_cents FROM bank WHERE id=?", (args.bank_id,)).fetchone()
        if not b:
            print("Bank-ID nicht gefunden."); 
            return
        bank_amount = b[0]

        inserted = []
        # 2) Dreiergruppen verarbeiten
        for i in range(0, len(args.triples), 3):
            account = args.triples[i]
            amount_cents = parse_amount_token(args.triples[i+1])
            tenant_id = args.triples[i+2]
            if tenant_id == "-" or tenant_id == "":
                tenant_id = None

            # Konto prüfen
            a = cx.execute("SELECT 1 FROM accounts WHERE number=?", (account,)).fetchone()
            if not a:
                print(f"Konto {account} unbekannt. Lege es ggf. mit add-account an.")
                return

            # Mietpartei prüfen (falls gesetzt)
            if tenant_id:
                t = cx.execute("SELECT 1 FROM tenants WHERE id=?", (tenant_id,)).fetchone()
                if not t:
                    print(f"Mietpartei {tenant_id} unbekannt. Lege sie mit add-tenant an.")
                    return

            cx.execute(
                "INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (?,?,?,?,?)",
                (args.bank_id, account, tenant_id, amount_cents, "")
            )
            inserted.append((account, tenant_id, amount_cents))

        # 3) Zusammenfassung / Abgleich
        tot = cx.execute("SELECT IFNULL(SUM(amount_cents),0) FROM splits WHERE bank_id=?", (args.bank_id,)).fetchone()[0]
        diff = tot - bank_amount

    # Ausgabe
    print(f"{len(inserted)} Splits hinzugefügt zu Bank-ID {args.bank_id}:")
    for acc, tid, amt in inserted:
        print(f"  Konto {acc} | Mieter {tid or '-'} | Betrag {c2s(amt)}")
    print(f"Summe Splits = {c2s(tot)} | Bankbetrag = {c2s(bank_amount)} | Differenz = {c2s(diff)}")
    if diff != 0:
        print("WARNUNG: Splits stimmen noch nicht mit der Bankzeile überein.")

def cmd_delete_split(args):
    with conn() as cx:
        cx.execute("DELETE FROM splits WHERE id=?", (args.split_id,))
    print("Split gelöscht.")

def cmd_report_tenant(args):
    with conn() as cx:
        t = cx.execute("SELECT id,name,unit FROM tenants WHERE id=?", (args.tenant_id,)).fetchone()
        if not t: print("Mietpartei nicht gefunden."); return
        rows = cx.execute("""
        SELECT a.number, a.name, IFNULL(SUM(s.amount_cents),0) AS sum_cents
        FROM accounts a
        JOIN splits s ON s.account = a.number
        WHERE s.tenant_id=?
        GROUP BY a.number,a.name
        ORDER BY a.number
        """, (args.tenant_id,)).fetchall()
        total = sum(r[2] for r in rows)
    print(f"Bericht Mietpartei {t[0]} – {t[1]} ({t[2] or '-'})")
    print("Konto  | Kontoname                           | Summe")
    print("-------+-------------------------------------+----------")
    for r in rows:
        print(f"{r[0]:<6} | {r[1]:<35} | {c2s(r[2]):>8}")
    print("-------+-------------------------------------+----------")
    print(f"Gesamt: {c2s(total)}")

def cmd_report_account(args):
    q = """
        SELECT a.number,
               a.name,
               SUM(s.amount_cents) AS sum_cents
        FROM accounts a
        LEFT JOIN splits s ON s.account = a.number
    """
    params = []
    if args.since or args.until:
        q += " LEFT JOIN bank b ON b.id = s.bank_id"

    q += " WHERE 1=1"

    if args.since:
        q += " AND b.op_date >= ?"
        params.append(args.since)
    if args.until:
        q += " AND b.op_date <= ?"
        params.append(args.until)

    q += """
        GROUP BY a.number, a.name
        ORDER BY a.number
    """

    with conn() as cx:
        rows = cx.execute(q, params).fetchall()

    if not rows:
        print("Keine Kontobewegungen gefunden.")
        return

    grand_total = 0
    print("Konto   | Bezeichnung               | Saldo")
    print("--------+---------------------------+----------")
    for number, name, sum_cents in rows:
        sum_cents = sum_cents or 0
        grand_total += sum_cents
        print(f"{number:<7} | {name[:27]:<27} | {c2s(sum_cents):>8}")

    print("--------+---------------------------+----------")
    print(f"SUMME                          | {c2s(grand_total):>8}")


def cmd_unbalanced(args):
    with conn() as cx:
        rows = cx.execute("""
        SELECT id, op_date, bank_amount, split_sum, description,
               (split_sum - bank_amount) AS diff
        FROM v_bank_with_sum
        WHERE diff != 0
        ORDER BY id
        """).fetchall()
    if not rows:
        print("Alles ausgeglichen."); return
    print("Unausgeglichene Bankzeilen (Summe Splits ≠ Bankbetrag):")
    print("ID  | Datum      | Bank    | Splits  | Diff    | Text")
    print("----+------------+---------+---------+---------+----------------")
    for r in rows:
        print(f"{r[0]:<4}| {r[1]:<10} | {c2s(r[2]):>7} | {c2s(r[3]):>7} | {c2s(r[5]):>7} | {r[4]}")

def cmd_example_demo(args):
    ensure_db()
    with conn() as cx:
        cx.execute("INSERT OR IGNORE INTO tenants(id,name,unit) VALUES ('M001','Herr Müller','Whg 1 OG')")
        cx.execute("INSERT OR IGNORE INTO tenants(id,name,unit) VALUES ('M002','Frau Schmidt','Whg 2 OG')")
        cx.execute("INSERT INTO bank(op_date,amount_cents,description) VALUES (?,?,?)", ("2025-08-01", d2c(decimal.Decimal("1050")), "Miete + NK Müller"))
        cx.execute("INSERT INTO bank(op_date,amount_cents,description) VALUES (?,?,?)", ("2025-08-01", d2c(decimal.Decimal("1200")), "Miete + NK Schmidt"))
        cx.execute("INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (1,'3000','M001',?,?)", (d2c(decimal.Decimal("850")), "Nettomiete Aug"))
        cx.execute("INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (1,'3010','M001',?,?)", (d2c(decimal.Decimal("200")), "NK-VZ Aug"))
        cx.execute("INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (2,'3000','M002',?,?)", (d2c(decimal.Decimal("950")), "Nettomiete Aug"))
        cx.execute("INSERT INTO splits(bank_id,account,tenant_id,amount_cents,note) VALUES (2,'3010','M002',?,?)", (d2c(decimal.Decimal("250")), "NK-VZ Aug"))
        # Beispiel: NKA-Nachzahlung 180 € für M001, fällig 2025-09-15
        cx.execute("INSERT INTO manual_charges(tenant_id,kind,due_date,amount_cents,issued_date,note) VALUES (?,?,?,?,?,?)",
                   ('M001','nka','2025-09-15', d2c(decimal.Decimal('180')), '2025-09-01', 'BK-Abrechnung 2024 Nachzahlung'))
    print("Demo-Daten eingespielt.")

def cmd_list_tenants(args):
    with conn() as cx:
        rows = cx.execute("""
            SELECT id, name, IFNULL(unit, '')
            FROM tenants
            ORDER BY id
        """).fetchall()
    if not rows:
        print("Keine Mietparteien angelegt.")
        return
    print("ID    | Name                       | Einheit")
    print("------+----------------------------+----------------")
    for tid, name, unit in rows:
        print(f"{tid:<5} | {name[:26]:<26} | {unit}")

# ---------- Leases / Rent Check ----------

def month_bounds(yyyymm: str) -> Tuple[str, str]:
    y, m = map(int, yyyymm.split("-"))
    first = date(y, m, 1)
    last_day = calendar.monthrange(y, m)[1]
    last = date(y, m, last_day)
    return first.isoformat(), last.isoformat()

def active_leases_in_month(cx, yyyymm: str):
    first, last = month_bounds(yyyymm)
    return cx.execute("""
      SELECT tenant_id, since_date, until_date, rent_cents, nk_cents, due_day, tolerance_cents, grace_days
      FROM leases
      WHERE since_date <= ?
        AND (until_date IS NULL OR until_date >= ?)
      ORDER BY tenant_id, since_date
    """, (last, first)).fetchall()

def sum_paid_for(cx, tenant_id: str, accounts: List[str], yyyymm: str) -> int:
    first, last = month_bounds(yyyymm)
    q = f"""
      SELECT IFNULL(SUM(s.amount_cents),0)
      FROM splits s
      JOIN bank b ON b.id = s.bank_id
      WHERE s.tenant_id=? AND s.account IN ({",".join("?"*len(accounts))})
        AND b.op_date BETWEEN ? AND ?
    """
    params = [tenant_id, *accounts, first, last]
    return cx.execute(q, params).fetchone()[0]

def date_paid_full(cx, tenant_id: str, accounts: List[str], yyyymm: str, target_cents: int) -> Optional[str]:
    first, last = month_bounds(yyyymm)
    rows = cx.execute(f"""
      SELECT b.op_date, s.amount_cents
      FROM splits s
      JOIN bank b ON b.id=s.bank_id
      WHERE s.tenant_id=? AND s.account IN ({",".join("?"*len(accounts))})
        AND b.op_date BETWEEN ? AND ?
      ORDER BY b.op_date, s.id
    """, [tenant_id, *accounts, first, last]).fetchall()
    run = 0
    for d, c in rows:
        run += c
        if run >= target_cents:
            return d
    return None

def cmd_add_lease(args):
    rent_c = d2c(parse_amount(args.rent_eur))
    nk_c   = d2c(parse_amount(args.nk_eur))
    tol_c  = d2c(parse_amount(args.tol_eur))
    with conn() as cx:
        cx.execute("""
          INSERT INTO leases(tenant_id,since_date,until_date,rent_cents,nk_cents,due_day,tolerance_cents,grace_days)
          VALUES (?,?,?,?,?,?,?,?)
          ON CONFLICT(tenant_id, since_date) DO UPDATE SET
            until_date=excluded.until_date,
            rent_cents=excluded.rent_cents,
            nk_cents=excluded.nk_cents,
            due_day=excluded.due_day,
            tolerance_cents=excluded.tolerance_cents,
            grace_days=excluded.grace_days
        """, (args.tenant_id, args.since, args.until, rent_c, nk_c, args.due_day, tol_c, args.grace))
    print(f"Lease gespeichert für {args.tenant_id} ab {args.since}.")

def cmd_rent_check(args):
    rent_accounts = [a.strip() for a in args.rent_accounts.split(",") if a.strip()]
    nk_accounts   = [a.strip() for a in args.nk_accounts.split(",") if a.strip()]
    with conn() as cx:
        leases = active_leases_in_month(cx, args.month)
        if not leases:
            print("Keine aktiven Leases in diesem Monat."); return
        print(f"Soll/Ist {args.month}")
        print("Mieter | Soll Miete | Ist Miete | Soll NK | Ist NK | Status | Verspätet?")
        print("------ +-----------+-----------+--------+--------+--------+-----------")
        for (tid, since, until, rent_c, nk_c, due_day, tol_c, grace) in leases:
            paid_rent = sum_paid_for(cx, tid, rent_accounts, args.month)
            paid_nk   = sum_paid_for(cx, tid, nk_accounts, args.month)

            def status_component(paid, due):
                if abs(paid - due) <= tol_c:
                    return "OK"
                return "Teil" if paid > 0 and paid < due - tol_c else ("Über" if paid > due + tol_c else "Fehlt")

            st_rent = status_component(paid_rent, rent_c)
            st_nk   = status_component(paid_nk, nk_c)

            late_flag = "-"
            y, m = map(int, args.month.split("-"))
            due_date = date(y, m, min(due_day, calendar.monthrange(y, m)[1]))
            if st_rent == "OK":
                d_paid = date_paid_full(cx, tid, rent_accounts, args.month, rent_c - tol_c)
                if d_paid:
                    limit = due_date.toordinal() + grace
                    late_flag = "zu spät" if date.fromisoformat(d_paid).toordinal() > limit else "OK"

            overall = "OK" if st_rent=="OK" and st_nk=="OK" else ("Teil" if "Teil" in (st_rent, st_nk) or ("OK" in (st_rent, st_nk) and ("Fehlt" in (st_rent, st_nk))) else ("Fehlt" if st_rent=="Fehlt" and st_nk=="Fehlt" else "Über"))

            def euro(c): return f"{c2s(c)}"
            print(f"{tid:<6}| {euro(rent_c):>10} | {euro(paid_rent):>10} | {euro(nk_c):>6} | {euro(paid_nk):>6} | {overall:<6} | {late_flag}")

# ---------- Aging (incl. NKA) ----------

def add_months(d: date, n: int) -> date:
    m = d.month - 1 + n
    y = d.year + m // 12
    m = m % 12 + 1
    last_day = calendar.monthrange(y, m)[1]
    return date(y, m, min(d.day, last_day))

def iter_months(start_yyyymm: str, end_yyyymm: str):
    y, m = map(int, start_yyyymm.split("-"))
    cur = date(y, m, 1)
    y2, m2 = map(int, end_yyyymm.split("-"))
    end = date(y2, m2, 1)
    while cur <= end:
        yield f"{cur.year:04d}-{cur.month:02d}"
        cur = add_months(cur, 1)

def make_due_date(yyyymm: str, due_day: int) -> date:
    y, m = map(int, yyyymm.split("-"))
    last_day = calendar.monthrange(y, m)[1]
    return date(y, m, min(due_day, last_day))

def fetch_payments(cx, tenant_id: str, accounts: List[str], start_date: str, end_date: str):
    rows = cx.execute(f"""
      SELECT b.op_date, s.amount_cents
      FROM splits s
      JOIN bank b ON b.id = s.bank_id
      WHERE s.tenant_id=? AND s.account IN ({",".join("?"*len(accounts))})
        AND b.op_date BETWEEN ? AND ?
      ORDER BY b.op_date, s.id
    """, [tenant_id, *accounts, start_date, end_date]).fetchall()
    return [(date.fromisoformat(d), c) for (d, c) in rows if c > 0]

class Charge:
    __slots__ = ("tenant_id","kind","due_date","amount_cents","open_cents")
    def __init__(self, tenant_id, kind, due_date: date, amount_cents: int):
        self.tenant_id = tenant_id
        self.kind = kind     # 'rent' | 'nk' | 'nka'
        self.due_date = due_date
        self.amount_cents = amount_cents
        self.open_cents = amount_cents

def build_monthly_charges(cx, month: str):
    charges = []
    for (tid, since, until, rent_c, nk_c, due_day, tol_c, grace) in active_leases_in_month(cx, month):
        d = make_due_date(month, due_day)
        if rent_c:
            charges.append(Charge(tid, "rent", d, rent_c))
        if nk_c:
            charges.append(Charge(tid, "nk", d, nk_c))
    return charges

def fetch_manual_charges(cx, tenant_id: str, start_date: str, end_date: str, kinds: List[str] = None):
    kinds = kinds or ['nka']
    q = f"""
      SELECT tenant_id, kind, due_date, amount_cents, note
      FROM manual_charges
      WHERE tenant_id=?
        AND kind IN ({",".join("?"*len(kinds))})
        AND due_date BETWEEN ? AND ?
      ORDER BY due_date, id
    """
    rows = cx.execute(q, [tenant_id, *kinds, start_date, end_date]).fetchall()
    charges = []
    for tid, kind, d, amt, note in rows:
        charges.append(Charge(tid, kind, date.fromisoformat(d), int(amt)))
    return charges

def apply_payments_fifo(charges: List[Charge], payments: List[Tuple[date,int]], asof: date,
                        priority: str = "oldest"):
    charges = [c for c in charges if c.due_date <= asof and c.open_cents > 0]
    def sort_key(c: Charge):
        if priority == "rent_first":
            pr = 0 if c.kind == "rent" else (1 if c.kind == "nk" else 2)
            return (pr, c.due_date)
        if priority == "nk_first":
            pr = 0 if c.kind == "nk" else (1 if c.kind == "rent" else 2)
            return (pr, c.due_date)
        if priority == "nka_first":
            pr = 0 if c.kind == "nka" else (1 if c.kind == "rent" else 2)
            return (pr, c.due_date)
        return (c.due_date,)
    charges.sort(key=sort_key)
    payments = [(d, amt) for (d, amt) in payments if d <= asof]
    for _, amt in payments:
        remaining = amt
        for c in charges:
            if remaining <= 0: break
            if c.open_cents <= 0: continue
            take = min(c.open_cents, remaining)
            c.open_cents -= take
            remaining -= take
    return charges

def bucket_for(days_overdue: int) -> str:
    if days_overdue <= 30: return "0-30"
    if days_overdue <= 60: return "31-60"
    if days_overdue <= 90: return "61-90"
    return "90+"

def cmd_tenant_transactions(args):
    q = """
        SELECT s.account,
               a.name AS account_name,
               b.op_date,
               b.id AS bank_id,
               s.amount_cents,
               IFNULL(b.description, '') AS description,
               IFNULL(s.note, '') AS note
        FROM splits s
        JOIN bank b ON b.id = s.bank_id
        JOIN accounts a ON a.number = s.account
        WHERE s.tenant_id = ?
    """
    params = [args.tenant_id]

    if args.since:
        q += " AND b.op_date >= ?"
        params.append(args.since)
    if args.until:
        q += " AND b.op_date <= ?"
        params.append(args.until)

    q += " ORDER BY s.account, b.op_date, b.id"

    with conn() as cx:
        rows = cx.execute(q, params).fetchall()

    if not rows:
        print(f"Keine Buchungen für Mieter {args.tenant_id} gefunden.")
        return

    current_account = None
    current_account_name = None
    account_total = 0
    grand_total = 0

    for (account, account_name, date, bank_id, amt, desc, note) in rows:
        if current_account != account:
            # Kontoabschluss falls nicht erstes Konto
            if current_account is not None:
                print(f"    Summe Konto {current_account}: {c2s(account_total)}")
                print()
                grand_total += account_total
                account_total = 0

            current_account = account
            current_account_name = account_name
            print(f"Konto {account} – {account_name}")
            print("Datum      | BankID | Betrag   | Verwendungszweck / Notiz")
            print("-----------+--------+----------+--------------------------")

        note_str = f" ({note})" if note else ""
        print(f"{date:<10} | {bank_id:<6} | {c2s(amt):>8} | {desc}{note_str}")
        account_total += amt

    # Letztes Konto abschließen
    print(f"    Summe Konto {current_account}: {c2s(account_total)}")
    grand_total += account_total

    print("=" * 50)
    print(f"Gesamtsumme alle Konten: {c2s(grand_total)}")


def cmd_rent_aging(args):
    asof = date.fromisoformat(args.asof)
    if args.from_month:
        start_month = args.from_month
    else:
        start_base = date(asof.year, asof.month, 1)
        tmp = add_months(start_base, -11)
        start_month = f"{tmp.year:04d}-{tmp.month:02d}"
    end_month = f"{asof.year:04d}-{asof.month:02d}"

    rent_accounts = [a.strip() for a in args.rent_accounts.split(",") if a.strip()]
    nk_accounts   = [a.strip() for a in args.nk_accounts.split(",") if a.strip()]
    nka_accounts  = [a.strip() for a in args.nka_accounts.split(",") if a.strip()]

    with conn() as cx:
        tenants = cx.execute("SELECT id,name,unit FROM tenants ORDER BY id").fetchall()
        any_output = False
        header_printed = False
        for (tid, tname, tunit) in tenants:
            charges: List[Charge] = []
            for mm in iter_months(start_month, end_month):
                active = cx.execute("""
                    SELECT tenant_id FROM leases
                    WHERE tenant_id=? AND since_date <= ? AND (until_date IS NULL OR until_date >= ?)
                """, (tid, month_bounds(mm)[1], month_bounds(mm)[0])).fetchone()
                if not active: 
                    continue
                month_charges = build_monthly_charges(cx, mm)
                charges.extend([c for c in month_charges if c.tenant_id == tid])
            # Ergänze manuelle NKA-Forderungen über den Zeitraum
            start_date_range = month_bounds(start_month)[0]
            end_date_range = month_bounds(end_month)[1]
            charges.extend(fetch_manual_charges(cx, tid, start_date_range, end_date_range, kinds=['nka']))

            if not charges:
                continue

            first_month = next(iter(iter_months(start_month, end_month)))
            start_date = month_bounds(first_month)[0]
            payments = []
            payments += fetch_payments(cx, tid, rent_accounts, start_date, asof.isoformat())
            payments += fetch_payments(cx, tid, nk_accounts,   start_date, asof.isoformat())
            payments += fetch_payments(cx, tid, nka_accounts,  start_date, asof.isoformat())

            charges = apply_payments_fifo(charges, payments, asof, priority=args.priority)

            buckets = {"0-30":0, "31-60":0, "61-90":0, "90+":0}
            total_open = 0
            detail_rows = []
            for c in charges:
                if c.open_cents <= 0: continue
                days = (asof - c.due_date).days
                b = bucket_for(days)
                buckets[b] += c.open_cents
                total_open += c.open_cents
                if args.detail:
                    detail_rows.append((c.due_date.isoformat(), c.kind, c.amount_cents, c.open_cents, days))

            if total_open > 0:
                if not header_printed:
                    print(f"Aging per {asof.isoformat()}  (Zeitraum ab {start_month})  Priorität: {args.priority}")
                    print("Tenant | Name              | 0-30     | 31-60    | 61-90    | 90+      | Summe")
                    print("-------+-------------------+----------+----------+----------+----------+----------")
                    header_printed = True
                print(f"{tid:<6} | {tname[:19]:<19} | {c2s(buckets['0-30']):>8} | {c2s(buckets['31-60']):>8} | "
                      f"{c2s(buckets['61-90']):>8} | {c2s(buckets['90+']):>8} | {c2s(total_open):>8}")
                any_output = True

                if args.detail and detail_rows:
                    print("       | Details: (Fälligkeit | Art | Ursprung | Offen | Tage)")
                    for (d,k,amt,open_amt,days) in sorted(detail_rows):
                        art = {"rent":"Miete", "nk":"NK", "nka":"NKA"}[k]
                        print(f"       |   {d} | {art:<3} | {c2s(amt):>8} | {c2s(open_amt):>8} | {days:>3}")
        if not any_output:
            print(f"Keine offenen Posten per {asof.isoformat()} im Zeitraum ab {start_month}.")

def cmd_unassigned_bank(args):
    q = """
        SELECT b.id, b.op_date, b.amount_cents, b.description
        FROM bank b
        LEFT JOIN splits s ON s.bank_id = b.id
        WHERE s.bank_id IS NULL
    """
    params = []

    if args.since:
        q += " AND b.op_date >= ?"
        params.append(args.since)
    if args.until:
        q += " AND b.op_date <= ?"
        params.append(args.until)

    q += " ORDER BY b.op_date, b.id"
    if args.limit:
        q += " LIMIT ?"
        params.append(args.limit)

    with conn() as cx:
        rows = cx.execute(q, params).fetchall()

    if not rows:
        print("Keine unzugeordneten Bankbuchungen gefunden.")
        return

    print("ID   | Datum      | Betrag   | Verwendungszweck")
    print("-----+------------+----------+------------------")
    for (bid, d, amt, desc) in rows:
        print(f"{bid:<4} | {d:<10} | {c2s(amt):>8} | {desc or ''}")


# ---------- NKA CLI ----------

def cmd_add_nka(args):
    amt_c = d2c(parse_amount(args.amount_eur))
    with conn() as cx:
        t = cx.execute("SELECT 1 FROM tenants WHERE id=?", (args.tenant_id,)).fetchone()
        if not t:
            print("Mietpartei unbekannt. Lege sie mit add-tenant an."); return
        cx.execute("INSERT INTO manual_charges(tenant_id,kind,due_date,amount_cents,issued_date,note) VALUES (?,?,?,?,?,?)",
                   (args.tenant_id, 'nka', args.due_date, amt_c, args.issued_date, args.note))
        rid = cx.execute("SELECT last_insert_rowid()").fetchone()[0]
    print(f"NKA-Forderung #{rid} für {args.tenant_id} am {args.due_date} über {c2s(amt_c)} € gespeichert.")

def cmd_list_nka(args):
    asof = date.fromisoformat(args.asof) if args.asof else date.today()
    nka_accounts = [a.strip() for a in args.nka_accounts.split(",") if a.strip()]

    with conn() as cx:
        # Alle NKA-Forderungen des Mieters laden
        rows = cx.execute("""
            SELECT id, due_date, amount_cents, IFNULL(issued_date, ''), IFNULL(note,'')
            FROM manual_charges
            WHERE tenant_id=? AND kind='nka'
            ORDER BY due_date, id
        """, (args.tenant_id,)).fetchall()

    if not rows:
        print("Keine NKA-Forderungen gefunden.")
        return

    if not args.with_payments:
        # Klassische Ausgabe (ohne Zahlungs-/Offen-Spalten)
        print(f"NKA-Forderungen für {args.tenant_id}:")
        print("ID  | Fälligkeit | Betrag   | Abrechn.-Dat. | Notiz")
        print("----+------------+----------+---------------+------")
        for r in rows:
            print(f"{r[0]:<4}| {r[1]:<10} | {c2s(r[2]):>8} | {r[3] or '-':<13} | {r[4] or ''}")
        return

    # Mit Zahlungen/Offen:
    # Zahlungen bis zum Stichtag aus den angegebenen NKA-Konten holen
    start_date = "1900-01-01"
    payments = fetch_payments(conn(), args.tenant_id, nka_accounts, start_date, asof.isoformat())
    # payments ist Liste [(date, amount_cents>0), ...]; summiere zu einem "Pool"
    payment_pool = sum(amt for (_, amt) in payments)

    print(f"NKA-Forderungen für {args.tenant_id} (inkl. Zahlungen bis {asof.isoformat()}):")
    print("ID  | Fälligkeit | Ursprung | Bezahlt  | Offen    | Abrechn.-Dat. | Notiz")
    print("----+------------+----------+----------+----------+---------------+------")

    total_orig = 0
    total_paid = 0
    total_open = 0

    for (cid, due_date, amount_cents, issued_date, note) in rows:
        orig = int(amount_cents)
        total_orig += orig

        paid_here = 0
        open_here = 0

        if orig >= 0:
            # Forderung: per FIFO aus payment_pool bedienen
            paid_here = min(orig, max(0, payment_pool))
            open_here = orig - paid_here
            payment_pool -= paid_here
        else:
            # Gutschrift: als "Kredit" behandeln -> erhöht Zahlungspool
            payment_pool += abs(orig)
            paid_here = 0
            open_here = 0  # Gutschrift ist nicht "offen"

        total_paid += paid_here
        total_open += open_here

        print(f"{cid:<4}| {due_date:<10} | {c2s(orig):>8} | {c2s(paid_here):>8} | {c2s(open_here):>8} | {issued_date or '-':<13} | {note or ''}")

    print("----+------------+----------+----------+----------+---------------+------")
    print(f"SUM |            | {c2s(total_orig):>8} | {c2s(total_paid):>8} | {c2s(total_open):>8} |")


def cmd_delete_nka(args):
    with conn() as cx:
        cx.execute("DELETE FROM manual_charges WHERE id=?", (args.nka_id,))
    print("NKA-Forderung gelöscht.")

# ---------- CLI ----------

def build_parser():
    p = argparse.ArgumentParser(description="Rent Ledger – Bankauszug-Splits für Mietverwaltung (inkl. NKA)")
    sub = p.add_subparsers(dest="cmd")

    sp = sub.add_parser("init-db", help="DB anlegen + Standardkonten laden")
    sp.set_defaults(func=cmd_init)

    sp = sub.add_parser("add-tenant", help="Mietpartei anlegen")
    sp.add_argument("id", help="z.B. M001")
    sp.add_argument("name")
    sp.add_argument("--unit", default="")
    sp.set_defaults(func=cmd_add_tenant)

    sp = sub.add_parser("add-account", help="Konto anlegen")
    sp.add_argument("number")
    sp.add_argument("name")
    sp.add_argument("--kind", default="other", choices=["asset","liability","income","expense","other"])
    sp.set_defaults(func=cmd_add_account)

    sp = sub.add_parser("import-bank", help="Bankauszug (CSV) importieren")
    sp.add_argument("csv")
    sp.add_argument("--delimiter", default=";")
    sp.add_argument("--encoding", default="utf-8")
    sp.add_argument("--col-date", default="Datum")
    sp.add_argument("--col-amount", default="Betrag")
    sp.add_argument("--col-desc", default="Verwendungszweck")
    sp.add_argument("--strict", action="store_true", help="Bei Fehlern abbrechen")
    sp.set_defaults(func=cmd_import_bank)

    sp = sub.add_parser("tenant-transactions", help="Alle Buchungen eines Mieters anzeigen, gruppiert nach Konto")
    sp.add_argument("tenant_id", help="Mieter-ID")
    sp.add_argument("--since", help="Startdatum YYYY-MM-DD", default=None)
    sp.add_argument("--until", help="Enddatum YYYY-MM-DD", default=None)
    sp.set_defaults(func=cmd_tenant_transactions)

    sp = sub.add_parser("list-bank", help="Bankzeilen anzeigen")
    sp.add_argument("--limit", type=int, default=20)
    sp.set_defaults(func=cmd_list_bank)

    sp = sub.add_parser("bank-detail", help="Details + Splits zu einer Bank-ID")
    sp.add_argument("bank_id", type=int)
    sp.set_defaults(func=cmd_bank_detail)

    sp = sub.add_parser("add-split", help="Mehrere Splits zu einer Bank-ID hinzufügen")
    sp.add_argument("bank_id", type=int, help="Bankzeilen-ID")
    # accept variable-length list of triples: ACCOUNT AMOUNT TENANT_ID
    sp.add_argument(
        "triples",
        nargs="+",
        help="Wiederholte Dreiergruppen: ACCOUNT AMOUNT_CENTS TENANT_ID (z. B. 3000 58000 M001 3010 18000 M001)"
    )
    sp.set_defaults(func=cmd_add_split)

    sp = sub.add_parser("delete-split", help="Split löschen")
    sp.add_argument("split_id", type=int)
    sp.set_defaults(func=cmd_delete_split)

    sp = sub.add_parser("report-tenant", help="Bericht je Mietpartei")
    sp.add_argument("tenant_id")
    sp.set_defaults(func=cmd_report_tenant)

    sp = sub.add_parser("report-account", help="Summen pro Konto anzeigen")
    sp.add_argument("--since", help="Startdatum YYYY-MM-DD", default=None)
    sp.add_argument("--until", help="Enddatum YYYY-MM-DD", default=None)
    sp.set_defaults(func=cmd_report_account)

    sp = sub.add_parser("unbalanced", help="Bankzeilen mit fehlender/überschüssiger Split-Summe")
    sp.set_defaults(func=cmd_unbalanced)

    sp = sub.add_parser("demo", help="Demo-Daten einspielen")
    sp.set_defaults(func=cmd_example_demo)

    sp = sub.add_parser("list-tenants", help="Alle Mietparteien anzeigen")
    sp.set_defaults(func=cmd_list_tenants)

    sp = sub.add_parser("unassigned-bank", help="Bankbuchungen ohne jegliche Splits anzeigen")
    sp.add_argument("--since", help="Startdatum YYYY-MM-DD", default=None)
    sp.add_argument("--until", help="Enddatum YYYY-MM-DD", default=None)
    sp.add_argument("--limit", type=int, help="Maximale Anzahl Zeilen", default=None)
    sp.set_defaults(func=cmd_unassigned_bank)

    # Regeln
    sp = sub.add_parser("add-rule", help="Auto-Split-Regel anlegen")
    sp.add_argument("name")
    sp.add_argument("--like", dest="match_desc_like", default=None, help="SQL-like Pattern, z.B. %%Müller%%")
    sp.add_argument("--regex", dest="match_desc_regex", default=None, help="Python-Regex (case-insensitive)")
    sp.add_argument("--min", dest="min_amount", default=None, help="Mindestbetrag")
    sp.add_argument("--max", dest="max_amount", default=None, help="Höchstbetrag")
    sp.add_argument("--sign", choices=["in","out","any"], default="any")
    sp.add_argument("--priority", type=int, default=100)
    sp.add_argument("--active", type=int, default=1)
    sp.set_defaults(func=cmd_add_rule)

    sp = sub.add_parser("add-rule-part", help="Part zu Regel hinzufügen")
    sp.add_argument("rule_id", type=int)
    sp.add_argument("account")
    sp.add_argument("kind", choices=["fixed","percent","remainder"])
    sp.add_argument("--tenant-id")
    sp.add_argument("--value-cents", default=None, help="nur bei fixed (z.B. 85000 für 850,00)")
    sp.add_argument("--value-percent", type=float, default=None, help="nur bei percent, z.B. 60.0")
    sp.add_argument("--note", default="")
    sp.set_defaults(func=cmd_add_rule_part)

    sp = sub.add_parser("list-rules", help="Regeln anzeigen")
    sp.set_defaults(func=cmd_list_rules)

    sp = sub.add_parser("test-rule", help="Testet eine Regel gegen eine Bank-ID")
    sp.add_argument("rule_id", type=int)
    sp.add_argument("bank_id", type=int)
    sp.set_defaults(func=cmd_test_rule)

    sp = sub.add_parser("apply-rules", help="Regeln auf Bankzeilen anwenden")
    sp.add_argument("--bank-id", type=int, help="nur auf diese Bank-ID")
    sp.add_argument("--only-unbalanced", action="store_true", help="nur Bankzeilen mit Diff != 0")
    sp.set_defaults(func=cmd_apply_rules)

    # Leases & Checks
    sp = sub.add_parser("add-lease", help="Mietvertrag/Sollwerte erfassen")
    sp.add_argument("tenant_id")
    sp.add_argument("--since", required=True, help="YYYY-MM-DD")
    sp.add_argument("--until", default=None, help="optional YYYY-MM-DD")
    sp.add_argument("--rent-eur", required=True, help="z.B. 850,00")
    sp.add_argument("--nk-eur", required=True, help="z.B. 200,00")
    sp.add_argument("--due-day", type=int, default=3)
    sp.add_argument("--tol-eur", default="0,00")
    sp.add_argument("--grace", type=int, default=3)
    sp.set_defaults(func=cmd_add_lease)

    sp = sub.add_parser("rent-check", help="Soll/Ist-Check für einen Monat (YYYY-MM)")
    sp.add_argument("month", help="YYYY-MM")
    sp.add_argument("--rent-accounts", default="3000")
    sp.add_argument("--nk-accounts", default="3010")
    sp.set_defaults(func=cmd_rent_check)

    # Aging
    sp = sub.add_parser("rent-aging", help="Aging (Offene Posten) je Mietpartei zum Stichtag")
    sp.add_argument("asof", help="Stichtag YYYY-MM-DD")
    sp.add_argument("--from-month", default=None, help="Startmonat YYYY-MM (Default: 12 Monate vor asof)")
    sp.add_argument("--rent-accounts", default="3000")
    sp.add_argument("--nk-accounts", default="3010")
    sp.add_argument("--nka-accounts", default="3020")
    sp.add_argument("--priority", choices=["oldest","rent_first","nk_first","nka_first"], default="oldest")
    sp.add_argument("--detail", action="store_true", help="Offene Einzelpositionen je Tenant anzeigen")
    sp.set_defaults(func=cmd_rent_aging)

    # NKA
    sp = sub.add_parser("add-nka", help="NKA-Forderung erfassen (Nebenkostenabrechnung)")
    sp.add_argument("tenant_id")
    sp.add_argument("due_date", help="Fälligkeit YYYY-MM-DD")
    sp.add_argument("amount_eur", help="Nachzahlung in EUR (positiv). Für Gutschrift negativ eingeben.")
    sp.add_argument("--issued", dest="issued_date", default=None, help="Rechnungs-/Abrechnungsdatum YYYY-MM-DD")
    sp.add_argument("--note", default="", help="Notiz")
    sp.set_defaults(func=cmd_add_nka)

    # NKA: Liste mit optionalem Zahlungs-/Offen-Status
    sp = sub.add_parser("list-nka", help="NKA-Forderungen eines Mieters anzeigen")
    sp.add_argument("tenant_id")
    sp.add_argument("--asof", default=None, help="Stichtag YYYY-MM-DD (Default: heute)")
    sp.add_argument(
        "--nka-accounts",
        default="3020",
        help="Konten (Komma-getrennt), die NKA-Zahlungen enthalten, z. B. 3020"
    )
    sp.add_argument(
        "--with-payments",
        action="store_true",
        help="Geleistete Zahlungen und offene Beträge je Forderung anzeigen"
    )
    sp.set_defaults(func=cmd_list_nka)


    sp = sub.add_parser("delete-nka", help="NKA-Forderung löschen (ID)")
    sp.add_argument("nka_id", type=int)
    sp.set_defaults(func=cmd_delete_nka)

    return p

# ---------- Rules CLI entry helpers reuse ----------
def cmd_list_rules(args):
    with conn() as cx:
        rules = cx.execute("""SELECT id,name,match_desc_like,min_amount_cents,max_amount_cents,sign,priority,active,match_desc_regex
                              FROM rules ORDER BY priority, id""").fetchall()
        print("ID | Pri | Akt | Name              | LIKE         | REGEX                 | Min   | Max   | Sign")
        print("---+-----+-----+--------------------+--------------+-----------------------+-------+-------+-----")
        for r in rules:
            rid,name,like,minc,maxc,sign,pri,act,regex = r
            print(f"{rid:<2} | {pri:<3} | {act:<3} | {name:<18} | {like or '-':<12} | {regex or '-':<21} | "
                  f"{c2s(minc) if minc is not None else '-':>5} | {c2s(maxc) if maxc is not None else '-':>5} | {sign}")
        parts = cx.execute("""SELECT rp.id, rp.rule_id, rp.account, a.name, rp.tenant_id, rp.kind, rp.value_cents, rp.value_percent
                              FROM rule_parts rp JOIN accounts a ON a.number=rp.account
                              ORDER BY rp.rule_id, rp.id""").fetchall()
        if parts:
            print("\nParts:")
            print("PartID | Rule | Konto | Kontoname                       | Mieter | Art      | Wert")
            print("-------+------+-------+-----------------------------------+--------+----------+-----------")
            for p in parts:
                pid, rid, acc, accn, tid, kind, vc, vp = p
                val = f"{c2s(vc)}" if vc is not None else (f"{vp}%" if vp is not None else "-")
                print(f"{pid:<6} | {rid:<4} | {acc:<5} | {accn:<33} | {tid or '-':<6} | {kind:<8} | {val:>9}")

def cmd_add_rule(args):
    with conn() as cx:
        min_c = d2c(parse_amount(args.min_amount)) if args.min_amount else None
        max_c = d2c(parse_amount(args.max_amount)) if args.max_amount else None
        cx.execute("""INSERT INTO rules
           (name,match_desc_like,min_amount_cents,max_amount_cents,sign,priority,active,match_desc_regex)
           VALUES (?,?,?,?,?,?,?,?)""",
           (args.name, args.match_desc_like, min_c, max_c, args.sign, args.priority, args.active, args.match_desc_regex))
        rid = cx.execute("SELECT last_insert_rowid()").fetchone()[0]
    print(f"Regel #{rid} '{args.name}' angelegt.")

def cmd_add_rule_part(args):
    if args.kind == "fixed" and args.value_cents is None:
        print("Für kind=fixed bitte --value-cents angeben (z.B. 85000 für 850,00)."); return
    if args.kind == "percent" and args.value_percent is None:
        print("Für kind=percent bitte --value-percent angeben (z.B. 60.0)."); return
    vc = int(args.value_cents) if args.value_cents else None
    with conn() as cx:
        a = cx.execute("SELECT 1 FROM accounts WHERE number=?", (args.account,)).fetchone()
        if not a: print("Konto unbekannt. Lege es mit add-account an."); return
        if args.tenant_id:
            t = cx.execute("SELECT 1 FROM tenants WHERE id=?", (args.tenant_id,)).fetchone()
            if not t: print("Mietpartei unbekannt. Lege sie mit add-tenant an."); return
        cx.execute("""INSERT INTO rule_parts(rule_id,account,tenant_id,kind,value_cents,value_percent,note_template)
                      VALUES (?,?,?,?,?,?,?)""",
                   (args.rule_id, args.account, args.tenant_id, args.kind, vc, args.value_percent, args.note))
        pid = cx.execute("SELECT last_insert_rowid()").fetchone()[0]
    print(f"Part #{pid} zu Regel {args.rule_id} angelegt.")

def cmd_test_rule(args):
    ok = False
    with conn() as cx:
        ok, msg = apply_rule_to_bank(cx, args.rule_id, args.bank_id)
        print(("OK: " if ok else "NEIN: ") + msg)
        if ok:
            cx.commit()  # <- WICHTIG: Änderungen sichtbar machen
    if ok:
        # jetzt erst mit neuer Verbindung Details anzeigen
        cmd_bank_detail(argparse.Namespace(bank_id=args.bank_id))

def cmd_apply_rules(args):
    with conn() as cx:
        if args.bank_id:
            bank_rows = cx.execute("SELECT id, op_date, amount_cents, description FROM bank WHERE id=?", (args.bank_id,)).fetchall()
        elif args.only_unbalanced:
            bank_rows = cx.execute("""
                SELECT b.id, b.op_date, b.amount_cents, b.description
                FROM v_bank_with_sum v
                JOIN bank b ON b.id=v.id
                WHERE (v.split_sum - v.bank_amount) != 0
                ORDER BY b.id
            """).fetchall()
        else:
            bank_rows = cx.execute("SELECT id, op_date, amount_cents, description FROM bank ORDER BY id").fetchall()

        rules = cx.execute("""SELECT id,name,match_desc_like,min_amount_cents,max_amount_cents,sign,priority,active,match_desc_regex
                              FROM rules WHERE active=1 ORDER BY priority, id""").fetchall()

        applied = 0
        for b in bank_rows:
            v = cx.execute("SELECT split_sum FROM v_bank_with_sum WHERE id=?", (b[0],)).fetchone()
            if v and v[0] == b[2]:
                continue
            for r in rules:
                if match_rule(r, b):
                    ok, msg = apply_rule_to_bank(cx, r[0], b[0])
                    if ok:
                        applied += 1
                        break
        print(f"Regel-Anwendung fertig. {applied} Bankzeilen automatisch gesplittet.")

def main(argv=None):
    ensure_db()
    parser = build_parser()
    args = parser.parse_args(argv)
    if not hasattr(args, "func"):
        parser.print_help(); return 0
    try:
        args.func(args)
    except Exception as e:
        print("Fehler:", e)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
