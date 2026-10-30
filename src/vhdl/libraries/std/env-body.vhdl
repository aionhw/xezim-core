-- The body of package STD.ENV (IEEE 1076-2019 §16.5), written for xezim:
-- the calendar and time conversions in VHDL. The subprograms that need the
-- tool or the operating system (GETENV, EPOCH, the directory, file
-- location and assertion functions, ...) have no body here: xezim provides
-- them natively (xezim-core src/vhdl/lower), as it does XEZIM_TZ_OFFSET
-- below. A time record is converted as a calendar date in the proleptic
-- Gregorian calendar; month 0 is January and dayofyear 0 is January 1.

package body ENV is

  constant DIR_SEPARATOR : STRING := "/";

  -- The local time's offset from UTC, in seconds, at time TIMER (seconds
  -- since the epoch). Native.
  impure function XEZIM_TZ_OFFSET(TIMER : REAL) return REAL;

  -- Days since 1970-01-01 of a date (month 1..12).
  function XEZIM_DAYS(Y, M, D : INTEGER) return INTEGER is
    variable yy, era, yoe, doy, doe, mp : INTEGER;
  begin
    if M <= 2 then
      yy := Y - 1;
    else
      yy := Y;
    end if;
    if yy >= 0 then
      era := yy / 400;
    else
      era := (yy - 399) / 400;
    end if;
    yoe := yy - era * 400;
    if M > 2 then
      mp := M - 3;
    else
      mp := M + 9;
    end if;
    doy := (153 * mp + 2) / 5 + D - 1;
    doe := yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + doe - 719468;
  end function;

  function GMTIME(TIMER : REAL) return TIME_RECORD is
    variable r : TIME_RECORD;
    variable whole : REAL;
    variable days, secs, z, era, doe, yoe, doy, mp, d, m, y, us : INTEGER;
  begin
    -- Floors: the nearest integers, less one when above.
    days := INTEGER(TIMER / 86400.0);
    if REAL(days) * 86400.0 > TIMER then
      days := days - 1;
    end if;
    whole := TIMER - REAL(days) * 86400.0;
    secs := INTEGER(whole);
    if REAL(secs) > whole then
      secs := secs - 1;
    end if;
    us := INTEGER((whole - REAL(secs)) * 1.0e6 - 0.5);
    if us < 0 then
      us := 0;
    elsif us > 999_999 then
      us := 999_999;
    end if;
    if secs >= 86400 then
      secs := secs - 86400;
      days := days + 1;
    end if;
    z := days + 719468;
    if z >= 0 then
      era := z / 146097;
    else
      era := (z - 146096) / 146097;
    end if;
    doe := z - era * 146097;
    yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    y := yoe + era * 400;
    doy := doe - (365 * yoe + yoe / 4 - yoe / 100);
    mp := (5 * doy + 2) / 153;
    d := doy - (153 * mp + 2) / 5 + 1;
    if mp < 10 then
      m := mp + 3;
    else
      m := mp - 9;
    end if;
    if m <= 2 then
      y := y + 1;
    end if;
    r.microsecond := us;
    r.second := secs mod 60;
    r.minute := (secs / 60) mod 60;
    r.hour := secs / 3600;
    r.day := d;
    r.month := m - 1;
    r.year := y;
    r.weekday := DAYOFWEEK'VAL((days + 4) mod 7);
    r.dayofyear := days - XEZIM_DAYS(y, 1, 1);
    return r;
  end function;

  function LOCALTIME(TIMER : REAL) return TIME_RECORD is
  begin
    return GMTIME(TIMER + XEZIM_TZ_OFFSET(TIMER));
  end function;

  impure function LOCALTIME return TIME_RECORD is
  begin
    return LOCALTIME(EPOCH);
  end function;

  impure function GMTIME return TIME_RECORD is
  begin
    return GMTIME(EPOCH);
  end function;

  -- Seconds since the epoch of a time record read as UTC.
  function EPOCH(TREC : TIME_RECORD) return REAL is
  begin
    return REAL(XEZIM_DAYS(TREC.year, TREC.month + 1, TREC.day)) * 86400.0
      + REAL(TREC.hour * 3600 + TREC.minute * 60 + TREC.second)
      + REAL(TREC.microsecond) * 1.0e-6;
  end function;

  function LOCALTIME(TREC : TIME_RECORD) return TIME_RECORD is
  begin
    return LOCALTIME(EPOCH(TREC));
  end function;

  function GMTIME(TREC : TIME_RECORD) return TIME_RECORD is
  begin
    return GMTIME(EPOCH(TREC));
  end function;

  function "+"(TREC : TIME_RECORD; DELTA : REAL) return TIME_RECORD is
  begin
    return GMTIME(EPOCH(TREC) + DELTA);
  end function;

  function "+"(DELTA : REAL; TREC : TIME_RECORD) return TIME_RECORD is
  begin
    return GMTIME(EPOCH(TREC) + DELTA);
  end function;

  function "-"(TREC : TIME_RECORD; DELTA : REAL) return TIME_RECORD is
  begin
    return GMTIME(EPOCH(TREC) - DELTA);
  end function;

  function "-"(DELTA : REAL; TREC : TIME_RECORD) return TIME_RECORD is
  begin
    return GMTIME(DELTA - EPOCH(TREC));
  end function;

  function "-"(TR1, TR2 : TIME_RECORD) return REAL is
  begin
    return EPOCH(TR1) - EPOCH(TR2);
  end function;

  function TIME_TO_SECONDS(TIME_VAL : IN TIME) return REAL is
  begin
    return REAL(TIME_VAL / 1 ns) * 1.0e-9 + REAL((TIME_VAL mod 1 ns) / 1 fs) * 1.0e-15;
  end function;

  function SECONDS_TO_TIME(REAL_VAL : IN REAL) return TIME is
  begin
    return REAL_VAL * 1 sec;
  end function;

  -- n as a decimal of at least w digits.
  function XEZIM_DIGITS(n, w : INTEGER) return STRING is
    constant s : STRING := INTEGER'IMAGE(n);
  begin
    if s'length >= w then
      return s;
    end if;
    return (1 to w - s'length => '0') & s;
  end function;

  function TO_STRING(TREC : TIME_RECORD;
                     FRAC_DIGITS : INTEGER range 0 to 6 := 0)
                     return STRING is
    constant base : STRING := XEZIM_DIGITS(TREC.year, 4) & "-"
      & XEZIM_DIGITS(TREC.month + 1, 2) & "-" & XEZIM_DIGITS(TREC.day, 2) & "T"
      & XEZIM_DIGITS(TREC.hour, 2) & ":" & XEZIM_DIGITS(TREC.minute, 2) & ":"
      & XEZIM_DIGITS(TREC.second, 2);
    constant us : STRING := XEZIM_DIGITS(TREC.microsecond, 6);
  begin
    if FRAC_DIGITS = 0 then
      return base;
    end if;
    return base & "." & us(1 to FRAC_DIGITS);
  end function;

end package body ENV;
