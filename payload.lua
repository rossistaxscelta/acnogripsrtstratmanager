local script = {}   -- payload: le funzioni dell'app vengono restituite al loader
--[[
  No Grip SRT - Strategy manager  (app Lua per Assetto Corsa + CSP)
  - Schermata principale: live + checklist guidata + 3 pulsanti (Info sessione, Test gomme, Strategia consigliata)
  - Notifiche a schermo (centro, in alto) quando un passo viene completato
  - Test mescola automatico di 20 minuti (parte all'uscita dai box, 1 giro di uscita scartato)
    oppure manuale (pulsante a schermo + tasto volante/tastiera, che serve anche a stoppare ed elaborare)
  - Consumo carburante memorizzato per auto+circuito
  - Perdita pit da drive through (giri entrata/uscita vs passo medio del test) + 5 s fissi + servizio dalla fisica
  - Serbatoio, tempi pit, pressioni ideali, vita gomme e massa auto letti dalla fisica (car.ini / tyres.ini)
  - Moltiplicatori server (usura gomme, consumo carburante) applicati all'algoritmo
  - Finestra pit obbligatoria opzionale
  - Strategia: pressioni a freddo consigliate sulla vettura vista dall'alto
  - Trasparenza dello sfondo regolabile (testi con ombra sempre leggibili)
]]

-- ============================================================
-- Costanti
-- ============================================================
local TEST_SECONDS = 20 * 60
local SKIP_LAPS = 1            -- solo il giro di uscita dai box
local EXTRA_PIT = 5            -- frenata + ripartenza ai box (s)
local EOL_GRIP = 94            -- fine vita gomma: % di grip residuo sulla curva usura
local CLIFF_FALLBACK = 1.5     -- se la curva usura non e' leggibile: perdita (s) oltre cui cambiare gomme
local HEADER = (__dirname and (__dirname .. '/header.png')) or 'header.png'
local HEADER_RATIO = 0.2918    -- altezza / larghezza di header.png
local CAR_IMG = (__dirname and (__dirname .. '/car_top.png')) or 'car_top.png'
local CAR_W, CAR_H = 300, 440  -- dimensioni di car_top.png
local WHEEL_POS = { { 52, 115 }, { 248, 115 }, { 52, 325 }, { 248, 325 } }  -- centri ruote (AC: ant sx, ant dx, post sx, post dx)
local HC_MAX_DELTA = 0.8       -- Hillclimb: al traguardo delta dall'ideale tra ~0 e +0.8 psi
local HC_RESERVE = 1.0         -- Hillclimb: litri di sicurezza residui a fine salita
local function psiInt(x) return math.floor(x + 0.5) end   -- .5 e oltre sale, sotto scende
local SYNTH = 1000             -- offset sul campo w per marcare i giri simulati (stop anticipato)

-- ============================================================
-- Impostazioni persistenti
-- ============================================================
local S = ac.storage{
  mode = 1,              -- 1 = giri, 2 = minuti
  raceValue = '20',
  margin = '1',          -- giri di margine carburante
  autoTest = true,
  pitWin = false,        -- finestra pit obbligatoria
  hillclimb = false,     -- Hillclimb MODE
  pwStart = '',
  pwEnd = '',
  bgTransp = 0,          -- trasparenza sfondo finestra: 0 = opaco, massimo 80
  -- archivi (per auto+circuito)
  data = '',
  pdata = '',
  fuelDB = '',
  laneDB = '',
}

-- ============================================================
-- Utility
-- ============================================================
local function num(s, d)
  local v = tonumber((tostring(s):gsub(',', '.')))
  return v or d
end

local function fmtLap(t)
  if not t or t <= 0 then return '--' end
  local m = math.floor(t / 60)
  return string.format('%d:%06.3f', m, t - m * 60)
end

local function fmtHMS(sec)
  sec = math.max(0, sec or 0)
  local h = math.floor(sec / 3600)
  local m = math.floor((sec % 3600) / 60)
  local s = math.floor(sec % 60)
  if h > 0 then return string.format('%d:%02d:%02d', h, m, s) end
  return string.format('%d:%02d', m, s)
end

local function median(t)
  local c = {}
  for i, v in ipairs(t) do c[i] = v end
  table.sort(c)
  local n = #c
  if n == 0 then return 0 end
  if n % 2 == 1 then return c[(n + 1) / 2] end
  return (c[n / 2] + c[n / 2 + 1]) / 2
end

local function avgLast(t, n)
  local cnt, sum = 0, 0
  for i = math.max(1, #t - n + 1), #t do sum = sum + t[i]; cnt = cnt + 1 end
  if cnt == 0 then return 0 end
  return sum / cnt
end

local function san(s) return (tostring(s):gsub('[|;=]', '_')) end

local function kvLoad(str)
  local t = {}
  for k, v in string.gmatch(str or '', '([^=;]+)=([^;]*);') do t[k] = v end
  return t
end

local function kvSave(t)
  local p = {}
  for k, v in pairs(t) do p[#p + 1] = k .. '=' .. v .. ';' end
  return table.concat(p)
end

local RED, GREEN, YELLOW, GREY, WHITE =
  rgbm(1, 0.35, 0.35, 1), rgbm(0.4, 1, 0.5, 1), rgbm(1, 0.85, 0.3, 1), rgbm(0.75, 0.75, 0.75, 1), rgbm(1, 1, 1, 1)

-- testo (dimensione base maggiorata per la guida)
local FS = 16
local function T(str, col, size)
  col = col or WHITE
  size = size or FS
  if not pcall(ui.dwriteTextWrapped, str, size, col) then
    if not pcall(ui.dwriteText, str, size, col) then ui.textColored(str, col) end
  end
end

-- pulsante con testo in grassetto (testo disegnato due volte con 1 px di scarto)
local boldOK = true
local function btn(label, size, color)
  local lines = {}
  for l in (label .. '\n'):gmatch('(.-)\n') do lines[#lines + 1] = l end
  local fs = FS
  local lh = fs * 1.3
  local tws, maxw = {}, 0
  for i, l in ipairs(lines) do
    local w = #l * fs * 0.58
    pcall(function() w = ui.measureDWriteText(l, fs).x end)
    tws[i] = w
    maxw = math.max(maxw, w)
  end
  size = size or vec2(maxw + 28, #lines * lh + 14)
  local pushed = 0
  if color then
    pcall(function()
      ui.pushStyleColor(ui.StyleColor.Button, color)
      ui.pushStyleColor(ui.StyleColor.ButtonHovered, rgbm(color.r * 1.15, color.g * 1.15, color.b * 1.15, color.mult))
      ui.pushStyleColor(ui.StyleColor.ButtonActive, rgbm(color.r * 0.85, color.g * 0.85, color.b * 0.85, color.mult))
      pushed = 3
    end)
  end
  if not boldOK then
    local c = ui.button(label, size)
    if pushed > 0 then ui.popStyleColor(pushed) end
    return c
  end
  local pos = ui.getCursor()
  local clicked = ui.button('##' .. label, size)
  if pushed > 0 then ui.popStyleColor(pushed) end
  local ok = pcall(function()
    local total = #lines * lh
    for i, l in ipairs(lines) do
      local p = vec2(pos.x + (size.x - tws[i]) / 2, pos.y + (size.y - total) / 2 + (i - 1) * lh)
      ui.dwriteDrawText(l, fs, p, WHITE)
      ui.dwriteDrawText(l, fs, p + vec2(0.9, 0), WHITE)
    end
  end)
  if not ok then boldOK = false end
  return clicked
end

-- ============================================================
-- Notifiche a schermo (centro, in alto)
-- ============================================================
local toasts = {}
local flash = { t = -1 }   -- flash rosso a fine salita (Hillclimb)

local function notify(msg, dur)
  table.insert(toasts, { text = msg, dur = dur or 6, t = 0 })
end

local function wrapText(text, maxChars)
  local lines, cur = {}, ''
  for word in string.gmatch(text, '%S+') do
    if cur == '' then cur = word
    elseif #cur + 1 + #word <= maxChars then cur = cur .. ' ' .. word
    else lines[#lines + 1] = cur; cur = word end
  end
  if cur ~= '' then lines[#lines + 1] = cur end
  return lines
end

function script.toastUI(dt)
  local t = toasts[1]
  if not t then return end
  local sw = 1920
  pcall(function() sw = ac.getUI().windowSize.x end)

  local size = 19
  local w = math.min(780, sw * 0.62)
  local cw = size * 0.52
  local lines = wrapText(t.text, math.max(10, math.floor((w - 48) / cw)))
  local lh = size * 1.4
  local h = 28 + #lines * lh

  local a = math.min(1, t.t / 0.25, (t.dur - t.t) / 0.5)
  a = math.max(0, a)

  ui.transparentWindow('ngs_toast', vec2((sw - w) / 2, 36), vec2(w, h), function()
    local o = vec2(0, 0)
    ui.drawRectFilled(o, o + vec2(w, h), rgbm(0.05, 0.05, 0.07, 0.9 * a), 10)
    ui.drawRect(o, o + vec2(w, h), rgbm(0.9, 0.1, 0.1, a), 10)
    for i, line in ipairs(lines) do
      local tw = #line * cw
      pcall(function() tw = ui.measureDWriteText(line, size).x end)
      ui.setCursor(vec2(math.max(8, (w - tw) / 2), 14 + (i - 1) * lh))
      ui.dwriteText(line, size, rgbm(1, 1, 1, a))
    end
  end)
end

-- ============================================================
-- Tasto volante/tastiera configurabile (avvia test / stoppa ed elabora)
-- ============================================================
local ctrlBtn = nil
pcall(function() ctrlBtn = ac.ControlButton('app.NoGripSRT_StrategyManager/testButton') end)

-- ============================================================
-- Fisica della vettura (data.acd) e modificatori server
-- ============================================================
local iniCache = {}
local function iniOf(file)
  if iniCache[file] == nil then
    local ok, ini = pcall(ac.INIConfig.carData, 0, file)
    iniCache[file] = (ok and ini) or false
  end
  return iniCache[file] or nil
end

local function iniNum(file, sec, key)
  local ini = iniOf(file)
  if not ini then return 0 end
  local ok, v = pcall(function() return ini:get(sec, key, 0) end)
  return (ok and tonumber(v)) or 0
end

-- moltiplicatori server: (carburante, gomme)
local function rates()
  local ok, f, t = pcall(function()
    local s = ac.getSim()
    return s.fuelConsumptionRate, s.tyreConsumptionRate
  end)
  f = ok and tonumber(f) or nil
  t = ok and tonumber(t) or nil
  return f or 1, t or 1
end

local function trackLengthKm()
  local ok, v = pcall(function() return ac.getSim().trackLengthM end)
  return ((ok and tonumber(v)) or 0) / 1000
end

local function tankCapacity(car)
  local v = iniNum('car.ini', 'FUEL', 'MAX_FUEL')
  if v > 0 then return v, 'fisica' end
  return car.maxFuel or 0, 'sim'
end

-- secondi per cambio gomme, secondi per litro, origine
local function pitTimes()
  local tyre = iniNum('car.ini', 'PIT_STOP', 'TYRE_CHANGE_TIME_SEC')
  local lit = iniNum('car.ini', 'PIT_STOP', 'FUEL_LITER_TIME_SEC')
  local src = (tyre > 0 and lit > 0) and 'fisica' or 'default'
  if tyre <= 0 then tyre = 6 end
  if lit <= 0 then lit = 0.1 end
  return tyre, lit, src
end

-- pressioni ideali a caldo (ant, post) della mescola con indice compIdx
local function idealPressure(compIdx)
  local sf = compIdx == 0 and 'FRONT' or ('FRONT_' .. compIdx)
  local sr = compIdx == 0 and 'REAR' or ('REAR_' .. compIdx)
  local f = iniNum('tyres.ini', sf, 'PRESSURE_IDEAL')
  local r = iniNum('tyres.ini', sr, 'PRESSURE_IDEAL')
  if f > 0 and r > 0 then return f, r end
  return 0, 0
end

-- effetto del carburante sul tempo (s/L): stimato dalla massa dell'auto (car.ini) e dal passo
local function fuelEffect(pace)
  local mass = iniNum('car.ini', 'BASIC', 'TOTALMASS')
  if mass <= 0 then mass = 1200 end
  return 0.4 * 0.75 / mass * pace
end

-- indice mescola dal nome
local compIdxByName, compBuilt = {}, false
local function compoundIndexOf(name)
  if not compBuilt then
    for i = 0, 15 do
      local ok, n = pcall(ac.getTyresName, 0, i)
      if ok and n and n ~= '' then compIdxByName[(tostring(n):gsub('[|;]', ''))] = i end
    end
    compBuilt = true
  end
  if compIdxByName[name] then return compIdxByName[name] end
  local n = tostring(name):match('^Mescola (%d+)$')
  return n and tonumber(n) or nil
end

-- km virtuali a cui la gomma arriva a fine vita (curva usura WEAR_CURVE in tyres.ini)
local eolCache = {}
local function eolKm(idx)
  if eolCache[idx] ~= nil then return eolCache[idx] or nil end
  local res = false
  local ini = iniOf('tyres.ini')
  if ini then
    local sec = idx == 0 and 'FRONT' or ('FRONT_' .. idx)
    local ok, file = pcall(function() return ini:get(sec, 'WEAR_CURVE', '') end)
    if ok and file and tostring(file) ~= '' then
      local ok2, lut = pcall(ac.DataLUT11.carData, 0, tostring(file))
      if ok2 and lut then
        local ok0, v0 = pcall(function() return lut:get(0) end)
        v0 = ok0 and tonumber(v0) or nil
        if v0 and v0 > 0 then
          local thr = (v0 <= 1.5) and (EOL_GRIP / 100) or EOL_GRIP
          for x = 0, 3000, 0.5 do
            local ok3, v = pcall(function() return lut:get(x) end)
            v = ok3 and tonumber(v) or nil
            if v and v < thr then res = x; break end
          end
          if res == 0 then res = false end
        end
      end
    end
  end
  eolCache[idx] = res
  return res or nil
end

-- ============================================================
-- Stato runtime e archivi
-- ============================================================
local st = {
  clock = 0,
  lastLapCount = -1, lapStartFuel = 0, lapHadPit = false,
  fuelLaps = {}, recent = {},
  raceRunning = false, raceElapsed = 0,
  wasInPit = nil, dt = nil, dtSample = nil, mandDone = false,
  testing = false, testEnding = false, testElapsed = 0,
  testLapN = 0, testSkipNext = false, testComp = nil, testW = 1,
  pHist = {}, coldP = nil, idealF = 0, idealR = 0,
}

local page = 'home'
local function goStrategyFlash() page = 'strategy'; flash.t = 0 end
local loaded = false
local curKey, trackKey
local tests, pdata = {}, {}        -- solo auto+circuito corrente
local restData, restP = {}, {}     -- righe di altre combinazioni (non toccate)
local fuelDB, laneDB = {}, {}
local fuelBase, fuelN = nil, 0     -- consumo base (L/giro a moltiplicatore 1.0)

-- in Hillclimb MODE il consumo e' per salita (dall'uscita box al traguardo) e ha un archivio separato
local function fuelKey() return S.hillclimb and (curKey .. '#hc') or curKey end
local function loadFuel()
  fuelBase, fuelN = nil, 0
  local b, n = tostring(fuelDB[fuelKey()] or ''):match('^([%d%.]+),(%d+)$')
  if b then fuelBase, fuelN = tonumber(b), tonumber(n) end
end

local function saveData()
  local parts = {}
  for _, line in ipairs(restData) do parts[#parts + 1] = line end
  for name, list in pairs(tests) do
    for _, r in ipairs(list) do
      parts[#parts + 1] = string.format('%s|%s|%d|%.3f|%.2f|%.2f;', curKey, name, r.n, r.t, r.f, r.w or 1)
    end
  end
  S.data = table.concat(parts)

  local pp = {}
  for _, line in ipairs(restP) do pp[#pp + 1] = line end
  for name, p in pairs(pdata) do
    pp[#pp + 1] = string.format('%s|%s|%.2f|%.2f|%.2f|%.2f|%.2f|%.2f|%.2f|%.2f|%.2f|%.2f|%d;', curKey, name,
      p.cold[1], p.cold[2], p.cold[3], p.cold[4], p.hot[1], p.hot[2], p.hot[3], p.hot[4], p.tF or 0, p.tR or 0,
      p.stable and 1 or 0)
  end
  S.pdata = table.concat(pp)
end

local function loadAll()
  tests, pdata, restData, restP = {}, {}, {}, {}
  for key, name, n, t, f, w in string.gmatch(S.data or '',
      '([^|;]+)|([^|;]+)|(%d+)|([%d%.]+)|([%d%.]+)|([%d%.]+);') do
    if key == curKey then
      tests[name] = tests[name] or {}
      table.insert(tests[name], { n = tonumber(n), t = tonumber(t), f = tonumber(f), w = tonumber(w) })
    else
      restData[#restData + 1] = string.format('%s|%s|%d|%.3f|%.2f|%.2f;', key, name, tonumber(n), tonumber(t), tonumber(f), tonumber(w))
    end
  end
  local pat = '([^|;]+)|([^|;]+)' .. string.rep('|([%d%.]+)', 10) .. '|([01]);'
  for key, name, c1, c2, c3, c4, h1, h2, h3, h4, tF, tR, s in string.gmatch(S.pdata or '', pat) do
    if key == curKey then
      pdata[name] = {
        cold = { tonumber(c1), tonumber(c2), tonumber(c3), tonumber(c4) },
        hot = { tonumber(h1), tonumber(h2), tonumber(h3), tonumber(h4) },
        tF = tonumber(tF), tR = tonumber(tR), stable = s == '1',
      }
    else
      restP[#restP + 1] = string.format('%s|%s|%s|%s|%s|%s|%s|%s|%s|%s|%s|%s|%s;', key, name, c1, c2, c3, c4, h1, h2, h3, h4, tF, tR, s)
    end
  end
  fuelDB, laneDB = kvLoad(S.fuelDB), kvLoad(S.laneDB)
  loadFuel()
end

local function ensureLoaded()
  if loaded then return true end
  local ok, tid, cid = pcall(function() return ac.getTrackID(), ac.getCarID(0) end)
  if not ok or not tid or not cid then return false end
  trackKey = san(tid)
  curKey = san(cid) .. '@' .. trackKey
  loadAll()
  loaded = true
  return true
end

local function compName(car)
  local ok, n = pcall(ac.getTyresName, 0, car.compoundIndex)
  if ok and n and n ~= '' then return (tostring(n):gsub('[|;]', '')) end
  return 'Mescola ' .. tostring(car.compoundIndex)
end

local function lapFrac(car)
  local s = car.splinePosition or 0
  if car.lapCount == 0 and s > 0.9 then s = 0 end
  return s
end

local function isRaceSession()
  local ok, r = pcall(function() return ac.getSim().raceSessionType == ac.SessionType.Race end)
  return ok and r or false
end

local function wheelPressures(car)
  local p = {}
  for i = 1, 4 do p[i] = car.wheels[i - 1].tyrePressure end
  return p
end

local function synCount(list)
  local c = 0
  for _, r in ipairs(list or {}) do if (r.w or 1) >= SYNTH then c = c + 1 end end
  return c
end

-- ============================================================
-- Analisi mescole (con riparametrazione sul moltiplicatore usura del server)
-- I giri simulati (stop anticipato) contano solo per il passo medio, non per la regressione.
-- ============================================================
local function analyze(list)
  local raw, sumT = {}, 0
  local synSum, synN = 0, 0
  local wRec = nil
  for _, r in ipairs(list) do
    if (r.w or 1) >= SYNTH then
      if r.n > SKIP_LAPS then synSum = synSum + r.t; synN = synN + 1 end
    elseif r.n > SKIP_LAPS then
      raw[#raw + 1] = { x = r.n - SKIP_LAPS, t = r.t, f = r.f }
      sumT = sumT + r.t
      wRec = wRec or r.w
    end
  end
  if #raw < 3 then return nil, #raw end
  local k = fuelEffect(sumT / #raw)

  local pts, ys = {}, {}
  for i, r in ipairs(raw) do pts[i] = { x = r.x, y = r.t - k * r.f, t = r.t }; ys[i] = pts[i].y end
  local med = median(ys)
  local good = {}
  for _, p in ipairs(pts) do if p.y <= med * 1.04 then good[#good + 1] = p end end
  if #good < 3 then return nil, #good end

  local n, sx, sy, sxx, sxy = #good, 0, 0, 0, 0
  for _, p in ipairs(good) do
    sx = sx + p.x; sy = sy + p.y; sxx = sxx + p.x * p.x; sxy = sxy + p.x * p.y
  end
  local den = n * sxx - sx * sx
  local b = den > 0 and (n * sxy - sx * sy) / den or 0
  local a = (sy - b * sx) / n
  local ss, best, rawSum = 0, 1e9, 0
  for _, p in ipairs(good) do
    local r = p.y - (a + b * p.x)
    ss = ss + r * r
    if p.t < best then best = p.t end
    rawSum = rawSum + p.t
  end

  -- degrado riportato all'usura gomme del server attuale
  wRec = wRec or 1
  local _, wNow = rates()
  local scale = wRec > 0 and (wNow / wRec) or 1
  return { n = n, nSyn = synN, a = a, b = b * scale, k = k, sd = math.sqrt(ss / math.max(1, n - 2)),
           best = best, rawMean = (rawSum + synSum) / (n + synN), scale = scale }
end

-- vita gomma in giri: dalla curva usura della fisica, altrimenti dal degrado misurato
local function tyreLife(name, b, tr)
  if tr <= 0 then return 999, 'server' end
  local idx = compoundIndexOf(name)
  local km = idx and eolKm(idx)
  local trackKm = trackLengthKm()
  if km and trackKm > 0 then
    local laps = math.floor(km / (trackKm * tr))
    if laps >= 2 then return laps, 'fisica' end
  end
  if b > 0.002 then return math.max(1, math.floor(CLIFF_FALLBACK / b)), 'stima' end
  return 999, 'stima'
end

-- ============================================================
-- Drive through: giri di entrata/uscita vs passo medio del test
-- ============================================================
local function laneLoss()
  local v = tonumber(laneDB[trackKey or ''])
  if v then return v, 'misurata' end
  return 18, 'stima'
end

local function hasDT()
  return tonumber(laneDB[trackKey or '']) ~= nil or st.dtSample ~= nil
end

local function resolveDT()
  local s = st.dtSample
  if not s then return end
  if st.testing and st.testComp == s.comp then return end   -- aspetta il passo medio finale
  local list = tests[s.comp]
  if not list then return end
  local an = analyze(list)
  if not an then return end
  local loss = s.sum - s.count * an.rawMean
  if loss > 0.5 and loss < 120 then
    laneDB[trackKey] = string.format('%.2f', loss)
    S.laneDB = kvSave(laneDB)
    notify(string.format('Drive through completato: perdita in corsia box %.1f s.', loss))
  end
  st.dtSample = nil
end

-- ============================================================
-- Test (automatico o manuale), stop anticipato, pressioni
-- ============================================================
local function startTest(car, name)
  local _, tr = rates()
  st.testing, st.testEnding, st.testElapsed = true, false, 0
  st.testLapN, st.testSkipNext, st.testComp, st.testW = 0, true, name, tr
  st.pHist = {}
  st.coldP = wheelPressures(car)                         -- pressioni a freddo (inizio test)
  st.idealF, st.idealR = idealPressure(car.compoundIndex) -- ideali dalla fisica
  tests[name] = {}
  pdata[name] = nil
  saveData()
  notify('Test con mescola ' .. name .. ' avviato: 20 minuti, il primo giro viene scartato.')
end

-- kind: true = completato, 'early' = stop anticipato con proiezione, false = interrotto
local function endTest(kind)
  local name = st.testComp
  st.testing, st.testEnding = false, false
  saveData()
  resolveDT()
  if not name then return end
  if kind == true then
    local msg = 'Test con mescola ' .. name .. ' completato! Torna ai pit per studiare i dati oppure avvia il test con la mescola successiva.'
    if not hasDT() then msg = msg .. ' Manca il drive through: fallo prima di rientrare ai box.' end
    notify(msg, 14)
  elseif kind == 'early' then
    notify('Test con mescola ' .. name .. ' fermato: dati elaborati e proiettati fino a 20 minuti. Torna ai pit per studiare i dati oppure avvia il test con la mescola successiva.', 14)
  end
end

-- aggiunge giri simulati (sul modello misurato) fino ai 20 minuti
local function simulateRemainder(name, an)
  local list = tests[name]
  local last
  for i = #list, 1, -1 do if (list[i].w or 1) < SYNTH then last = list[i]; break end end
  if not last then return 0 end
  local remaining = TEST_SECONDS - st.testElapsed
  local fpl = 0
  if #st.fuelLaps > 0 then
    fpl = avgLast(st.fuelLaps, 5)
  elseif fuelBase then
    local fr = rates()
    fpl = fuelBase * fr
  end
  local n, f, tsum, count = last.n, last.f, 0, 0
  while count < 80 do
    n = n + 1
    f = math.max(0, f - fpl)
    local t = an.a + an.b * (n - SKIP_LAPS) + an.k * f
    if t <= 10 or tsum + t > remaining then break end
    tsum = tsum + t
    table.insert(list, { n = n, t = t, f = f, w = st.testW + SYNTH })
    count = count + 1
  end
  return count
end

local function testStart(car)
  if st.testing then return end
  local name = compName(car)
  if tests[name] and #tests[name] > 0 then
    notify('Test gia\' presente per ' .. name .. ': usa "Rifai test" nella scheda Test gomme.', 7)
    return
  end
  startTest(car, name)
end

local function testStop(car)
  if not st.testing then return end
  if not hasDT() then
    notify('Per elaborare i dati serve prima il drive through: fallo senza fermarti in corsia box.', 8)
    return
  end
  local name = st.testComp
  local an = analyze(tests[name] or {})
  if not an then
    notify('Dati insufficienti: servono almeno 3 giri puliti dopo il primo giro.', 7)
    return
  end
  simulateRemainder(name, an)
  endTest('early')
end

-- azione del tasto: stoppa se il test e' in corso, altrimenti avvia (solo con test automatico disattivato)
local function testAction(car)
  if S.hillclimb then
    notify('Hillclimb MODE attiva: i test da 20 minuti sono disattivati.', 5)
    return
  end
  if st.testing then testStop(car)
  elseif not S.autoTest then testStart(car)
  else notify('Test automatico attivo: parte da solo all\'uscita dai box.', 5) end
end

local function updatePressure(car)
  table.insert(st.pHist, wheelPressures(car))
  local k = #st.pHist
  local from = math.max(1, k - 2)
  local cnt = k - from + 1
  local hot, stable = { 0, 0, 0, 0 }, cnt >= 3
  for i = 1, 4 do
    local mn, mx, sum = 1e9, -1e9, 0
    for j = from, k do
      local v = st.pHist[j][i]
      mn = math.min(mn, v); mx = math.max(mx, v); sum = sum + v
    end
    hot[i] = sum / cnt
    if mx - mn > 0.2 then stable = false end
  end
  local was = pdata[st.testComp] and pdata[st.testComp].stable
  pdata[st.testComp] = { cold = st.coldP, hot = hot, stable = stable, tF = st.idealF, tR = st.idealR }
  if stable and not was then notify('Pressioni gomme stabilizzate: dati sufficienti per la pressione consigliata.') end
end

local function onPitExit(car)
  if S.hillclimb then
    -- Hillclimb: la misura parte dal transito su AC_START_0 (vedi hcUpdate), non dall'uscita box
    return
  end
  if st.dt then
    if st.dt.stopped then st.dt = nil
    else st.dt.exited = true; st.dt.endLap = car.lapCount end
  end
  if S.autoTest and not st.testing and not isRaceSession() then
    local name = compName(car)
    if not tests[name] or #tests[name] == 0 then startTest(car, name) end
  end
end

-- ============================================================
-- Carburante (memorizzato per auto+circuito, normalizzato sul moltiplicatore server)
-- ============================================================
local function learnFuel(used)
  local fr = rates()
  if fr <= 0 then return false end
  local x = used / fr
  if fuelBase and fuelN >= 3 and (x > fuelBase * 1.3 or x < fuelBase * 0.7) then return false end
  if not fuelBase then
    fuelBase, fuelN = x, 1
  else
    local n = math.min(fuelN, 9)
    fuelBase = (fuelBase * n + x) / (n + 1)
    fuelN = math.min(fuelN + 1, 10)
  end
  fuelDB[fuelKey()] = string.format('%.4f,%d', fuelBase, fuelN)
  S.fuelDB = kvSave(fuelDB)
  return true
end

local function fuelPerLap()
  local fr = rates()
  if #st.fuelLaps >= 2 then return avgLast(st.fuelLaps, 5), 'misurato' end
  if fuelBase then return fuelBase * fr, 'memorizzato' end
  if #st.fuelLaps == 1 then return st.fuelLaps[1], 'misurato' end
  return 0, 'sconosciuto'
end

local function setHillclimb(on)
  if st.testing then endTest(false) end
  S.hillclimb = on
  st.hc, st.dt, st.dtSample = nil, nil, nil
  st.fuelLaps = {}
  loadFuel()
  if on then
    notify('Hillclimb MODE attiva: transita dalla partenza e raggiungi il traguardo.', 5)
  else
    notify('Hillclimb MODE disattivata.', 4)
  end
end

-- ============================================================
-- Hillclimb MODE: fine salita (traguardo) -> consumo per salita e pressioni
-- ============================================================
local function hcFinish(car)
  local h = st.hc
  st.hc = nil
  if not h or h.comp ~= compName(car) then return end

  local used = h.fuel0 - car.fuel
  if used > 0.01 then
    pcall(learnFuel, used)
    table.insert(st.fuelLaps, used)
    if #st.fuelLaps > 10 then table.remove(st.fuelLaps, 1) end
    notify(string.format('Consumo salita: %.2f L. Da caricare: %.1f L (con %.0f L di riserva).', used, used + HC_RESERVE, HC_RESERVE), 8)
  end

  local hot = wheelPressures(car)
  local idF, idR = idealPressure(car.compoundIndex)
  local name = h.comp .. ' [HC]'
  local stable = false
  if idF > 0 and idR > 0 then
    stable = true
    for i = 1, 4 do
      local delta = hot[i] - (i <= 2 and idF or idR)
      if delta < -0.5 or delta > HC_MAX_DELTA then stable = false end
    end
  end
  pdata[name] = { cold = h.cold, hot = hot, stable = stable, tF = idF, tR = idR }
  saveData()
  goStrategyFlash()
end

-- ============================================================
-- Finestra pit
-- ============================================================
-- nil = nessun problema; 'invalid' = valori mancanti/incoerenti; 'incompat' = finestra oltre la durata della gara
local function pitWindowIssue()
  if not S.pitWin then return nil end
  local ws, we = num(S.pwStart, 0), num(S.pwEnd, 0)
  if ws <= 0 or we <= ws then return 'invalid' end
  local dur = num(S.raceValue, 0)
  if dur > 0 and (we > dur or ws >= dur) then return 'incompat' end
  return nil
end

local PIT_ERR_INCOMPAT = 'ERRORE: durata totale gara non compatibile con finestra pit.'

local function pitWindow()
  if not S.pitWin then return nil end
  local issue = pitWindowIssue()
  if issue then return nil, issue end
  return { ws = num(S.pwStart, 0), we = num(S.pwEnd, 0) }
end

local function pitWindowState(car)
  local w, invalid = pitWindow()
  if invalid then return invalid end
  if not w then return nil end
  local cur = (S.mode == 1) and (car.lapCount + lapFrac(car)) or (st.raceElapsed / 60)
  if cur < w.ws then return 'before', w.ws - cur, w end
  if cur <= w.we then return 'open', w.we - cur, w end
  return 'closed', 0, w
end

-- Transito su AC_START_0 / AC_FINISH_0: posizione dei nodi della pista + punto di minima distanza
local gates = { tried = false }
local function nodePos(name)
  local ok, pos = pcall(function()
    local n = ac.findNodes('trackRoot:yes'):findNodes(name)
    if not n or n:size() == 0 then return nil end
    for _, fn in ipairs({ 'getWorldPosition', 'getPosition' }) do
      local ok2, v = pcall(function() return n[fn](n) end)
      if ok2 and v and v.x then return vec3(v.x, v.y, v.z) end
    end
    return nil
  end)
  if ok then return pos end
  return nil
end

local function gateTracker(name)
  return { name = name, pos = nil, prev = nil, minD = nil }
end
local gStart, gFinish = gateTracker('AC_START_0'), gateTracker('AC_FINISH_0')

-- true nel frame in cui l'auto ha appena superato il punto di massimo avvicinamento al nodo
local function gatePassed(g, car)
  if not g.pos then return false end
  local d = (car.position - g.pos):length()
  local passed = false
  if g.prev and d > g.prev and g.minD and g.minD < 25 and car.speedKmh > 3 then
    passed = true
    g.minD = nil
  end
  if d < 25 and (not g.minD or d < g.minD) then g.minD = d end
  if d > 80 then g.minD = nil end
  g.prev = d
  return passed
end

local function hcUpdate(car)
  if not gates.tried then
    gates.tried = true
    gStart.pos, gFinish.pos = nodePos('AC_START_0'), nodePos('AC_FINISH_0')
    gates.ok = gStart.pos ~= nil and gFinish.pos ~= nil
  end
  local startNow, finishNow = false, false
  if gates.ok then
    startNow = gatePassed(gStart, car)
    finishNow = gatePassed(gFinish, car)
  else
    -- ripiego: il cronometro del giro riparte al transito dello start
    local lt = car.lapTimeMs or 0
    local pl = st.hcPrevLT or 0
    if (lt > 0 and pl <= 0) or (lt + 500 < pl) then startNow = true end
    st.hcPrevLT = lt
  end
  if startNow and not st.hc then
    st.hc = { fuel0 = car.fuel, cold = wheelPressures(car), comp = compName(car) }
    notify('Salita iniziata (AC_START_0): misuro consumo e pressioni fino al traguardo.', 5)
  elseif finishNow and st.hc then
    hcFinish(car)
  end
end

-- ============================================================
-- Raccolta dati
-- ============================================================
local function onLap(car)
  local t = car.previousLapTimeMs / 1000
  local fEnd = car.fuel
  local clean = (not st.lapHadPit) and t > 10

  if S.hillclimb then
    hcFinish(car)
    st.lapStartFuel = car.fuel
    st.lapHadPit = car.isInPitlane or false
    return
  end

  if clean then
    st.sessN = (st.sessN or 0) + 1
    st.sessSum = (st.sessSum or 0) + t
    if not st.sessBest or t < st.sessBest then st.sessBest = t end
  end

  if st.testing and compName(car) ~= st.testComp then endTest(false) end

  -- giri toccati dalla corsia box durante un drive through
  if st.dt then
    local idx = car.lapCount - 1
    if idx >= st.dt.startLap then
      st.dt.sum = st.dt.sum + t
      st.dt.count = st.dt.count + 1
      if st.dt.exited and idx >= st.dt.endLap then
        st.dtSample = { sum = st.dt.sum, count = st.dt.count, comp = compName(car) }
        st.dt = nil
        resolveDT()
      end
    end
  end

  if clean then
    local used = st.lapStartFuel - fEnd
    local hadFuel = fuelBase ~= nil
    if used > 0.01 and learnFuel(used) then
      table.insert(st.fuelLaps, used)
      if #st.fuelLaps > 10 then table.remove(st.fuelLaps, 1) end
      if not hadFuel then
        notify(string.format('Consumo carburante rilevato: %.2f L/giro.', used))
      end
    end
    table.insert(st.recent, t)
    if #st.recent > 10 then table.remove(st.recent, 1) end
  end

  if st.testing then
    if st.testSkipNext then
      st.testSkipNext = false            -- primo giro (uscita dai box): ignorato
    else
      st.testLapN = st.testLapN + 1
      if clean then
        table.insert(tests[st.testComp], { n = st.testLapN, t = t, f = (st.lapStartFuel + fEnd) / 2, w = st.testW })
        if st.testLapN > SKIP_LAPS then updatePressure(car) end
      end
    end
    if st.testEnding then endTest(true) end
  end

  st.lapStartFuel = fEnd
  st.lapHadPit = car.isInPitlane or false
end

function script.update(dt)
  -- notifiche
  local tst = toasts[1]
  if tst then
    tst.t = tst.t + dt
    if tst.t >= tst.dur then table.remove(toasts, 1) end
  end

  if flash.t >= 0 then
    flash.t = flash.t + dt
    if flash.t > 3.5 then flash.t = -1 end
  end

  local car = ac.getCar(0)
  if not car then return end
  if not ensureLoaded() then return end

  -- tasto configurabile
  if ctrlBtn then
    local ok, pressed = pcall(function() return ctrlBtn:pressed() end)
    if ok and pressed then testAction(car) end
  end

  st.clock = st.clock + dt
  if st.raceRunning then st.raceElapsed = st.raceElapsed + dt end

  -- corsia box: ingresso / uscita
  local inPit = car.isInPitlane or false
  if st.wasInPit == nil then st.wasInPit = inPit end
  if inPit and not st.wasInPit then
    st.dt = { startLap = car.lapCount, sum = 0, count = 0, stopped = false }
    st.hc = nil
  end
  if inPit and car.speedKmh < 3 then
    if st.dt then st.dt.stopped = true end
    if not st.mandDone and pitWindowState(car) == 'open' then
      st.mandDone = true
      notify('Sosta obbligatoria effettuata dentro la finestra pit.')
    end
  end
  if inPit then st.lapHadPit = true end
  local exited = st.wasInPit and not inPit
  st.wasInPit = inPit
  if exited then onPitExit(car) end
  if S.hillclimb then hcUpdate(car) end

  if st.testing then
    st.testElapsed = st.testElapsed + dt
    if st.testElapsed >= TEST_SECONDS then st.testEnding = true end
  end

  if st.lastLapCount < 0 or car.lapCount < st.lastLapCount then
    st.lastLapCount = car.lapCount
    st.lapStartFuel = car.fuel
    st.lapHadPit = inPit
    return
  end
  if car.lapCount > st.lastLapCount then
    st.lastLapCount = car.lapCount
    onLap(car)
  end
end

-- ============================================================
-- Contesto gara
-- ============================================================
local function refPace()
  if #st.recent > 0 then return avgLast(st.recent, 5) end
  return 0
end

local function context(car)
  local cap, capSrc = tankCapacity(car)
  local fpl, fplSrc = fuelPerLap()
  local tyreSec, litSec, pitSrc = pitTimes()
  local lane, laneSrc = laneLoss()
  local fr, tr = rates()
  local w = pitWindow()
  local ctx = {
    fpl = fpl, fplSrc = fplSrc, cap = cap, capSrc = capSrc,
    margin = num(S.margin, 1), refPace = refPace(),
    lane = lane, laneSrc = laneSrc, extra = EXTRA_PIT,
    tyreSec = tyreSec, litSec = litSec, pitSrc = pitSrc, fr = fr, tr = tr,
    pit = w ~= nil, pws = w and w.ws or 0, pwe = w and w.we or 0,
  }
  local v = num(S.raceValue, 0)
  if S.mode == 1 then ctx.laps = math.max(1, math.floor(v)) else ctx.seconds = v * 60 end
  return ctx
end

local function lapsLeft(car, pace)
  local s = lapFrac(car)
  if S.mode == 1 then
    return math.max(0, num(S.raceValue, 0) - car.lapCount - s)
  end
  if pace <= 0 then return nil end
  local rem = num(S.raceValue, 0) * 60 - st.raceElapsed
  local toLine = (1 - s) * pace
  if rem <= toLine then return 1 - s end
  return (1 - s) + math.ceil((rem - toLine) / pace)
end

-- ============================================================
-- Pianificazione per mescola
-- ============================================================
local function planFor(an, ctx, name)
  local k = an.k
  local b = math.max(0, an.b)
  local life, lifeSrc = tyreLife(name, b, ctx.tr)
  local fpl, cap = ctx.fpl, ctx.cap

  local fuelRange = (fpl > 0 and cap > 0) and math.max(1, math.floor(cap / fpl - ctx.margin)) or 999
  local maxStint = math.max(1, math.min(life, fuelRange))

  local function build(L, pace)
    local need = (L + ctx.margin) * fpl
    local fuelStops = (fpl > 0 and cap > 0) and math.max(0, math.ceil(need / cap - 1e-9) - 1) or 0
    local tyreStops = math.max(0, math.ceil(L / life - 1e-9) - 1)
    local stops = math.max(fuelStops, tyreStops)
    local winOK, ws, we = true, nil, nil
    local stints = {}

    if ctx.pit then
      stops = math.max(stops, 1)
      if ctx.laps then ws, we = ctx.pws, ctx.pwe
      else ws, we = ctx.pws * 60 / math.max(pace, 1), ctx.pwe * 60 / math.max(pace, 1) end
      local even = L / (stops + 1)
      if ws >= L then
        winOK = false
        for i = 1, stops + 1 do stints[i] = even end
      else
        local s1 = math.max(ws, math.min(even, we))
        s1 = math.min(s1, L - 1)
        if s1 > maxStint then winOK = false; s1 = maxStint end
        local rest = L - s1
        while rest / stops > maxStint and stops < 60 do stops = stops + 1 end
        local r = rest / stops
        stints[1] = s1
        for i = 1, stops do stints[i + 1] = r end
      end
    else
      for i = 1, stops + 1 do stints[i] = L / (stops + 1) end
    end

    local avgFuel = math.min(need, cap > 0 and cap or need) / 2
    -- sosta = corsia + frenata/ripartenza + max(rifornimento, cambio gomme) (in parallelo in AC)
    local perStopFuel = fpl > 0 and math.min(cap > 0 and cap or 1e9, need / (stops + 1)) or 0
    local service = math.max(perStopFuel * ctx.litSec, ctx.tyreSec)
    local pitStop = ctx.lane + ctx.extra + service

    local degr, longest = 0, 0
    for _, s in ipairs(stints) do
      degr = degr + b * s * (s + 1) / 2
      longest = math.max(longest, s)
    end
    local total = L * (an.a + k * avgFuel) + degr + stops * pitStop

    local stopLaps, acc = {}, 0
    for i = 1, stops do acc = acc + stints[i]; stopLaps[i] = acc end

    return { L = L, total = total, stops = stops, per = L / (stops + 1), longest = longest, life = life, lifeSrc = lifeSrc,
             pitStop = pitStop, fuelStops = fuelStops, tyreStops = tyreStops, need = need,
             stopLaps = stopLaps, winOK = winOK, maxStint = maxStint, pace = total / L }
  end

  local p
  if ctx.laps then
    p = build(ctx.laps, 0)
  else
    local ref = ctx.refPace > 0 and ctx.refPace or an.rawMean
    local q = build(math.max(1, math.floor(ctx.seconds / ref) + 1), ref)
    local pace = an.a + k * (math.min(q.need, ctx.cap > 0 and ctx.cap or q.need) / 2) + b * (q.per + 1) / 2
    p = build(math.max(1, math.floor(ctx.seconds / pace) + 1), pace)
  end
  p.score = p.total / p.L
  p.extrap = p.longest > (an.n + SKIP_LAPS) * 1.5
  return p
end

-- ============================================================
-- UI: componenti
-- ============================================================
local function field(label, key, width, flags)
  ui.setNextItemWidth(width or 90)
  local v, ch = ui.inputText('##' .. key, S[key], flags or ui.InputTextFlags.CharsDecimal)
  if ch then S[key] = v end
  ui.sameLine()
  T(label)
end

local function checkbox(id, label, val)
  local ch = ui.checkbox('##' .. id, val)
  ui.sameLine()
  T(label)
  return ch
end

local function tick(done, label)
  if done then
    local ok = pcall(ui.icon, ui.Icons.Confirm, vec2(16, 16), GREEN)
    if not ok then T('OK', GREEN) end
  else
    T('-', GREY)
  end
  ui.sameLine(46)
  T(label, done and GREEN or WHITE)
end

local function drawBackground()
  local tr = math.max(0, math.min(80, num(S.bgTransp, 0)))
  local a = 1 - tr / 100
  ui.drawRectFilled(vec2(0, 0), ui.windowSize(), rgbm(0.04, 0.045, 0.06, a), 6)
end

-- logo, centrato se scale >= 0.6
local function drawHeader(scale)
  local avail = ui.availableSpaceX()
  local iw = math.floor(avail * scale)
  local x0 = ui.getCursorX()
  if scale >= 0.6 then x0 = x0 + (avail - iw) / 2 end
  local y0 = ui.getCursorY()
  local size = vec2(iw, iw * HEADER_RATIO)
  ui.setCursor(vec2(x0, y0))
  local hsrc = NGS and NGS.asset('header.png') or nil
  if hsrc then
    ui.image(hsrc, size)
  elseif NGS then
    pcall(ui.dwriteText, 'NO GRIP SRT - STRATEGY MANAGER', 20, rgbm(0.95, 0.15, 0.15, 1))
    ui.dummy(vec2(size.x, math.max(1, size.y - 24)))
  else
    ui.image(HEADER, size)
  end
  return iw
end

local function pressTargets(name, p)
  local hc = name:sub(-5) == ' [HC]'
  local d = 0
  return (p.tF or 0) + d, (p.tR or 0) + d, hc
end

local function drawPressure(name, compact)
  local p = pdata[name]
  if not p then
    T('    pressioni: dati non ancora sufficienti', GREY)
    return
  end
  if not compact then
    T(string.format('    P. caldo misurate: ant %.1f/%.1f  post %.1f/%.1f psi', p.hot[1], p.hot[2], p.hot[3], p.hot[4]))
  end
  if (p.tF or 0) <= 0 or (p.tR or 0) <= 0 then
    T('    pressione ideale non leggibile dalla fisica (tyres.ini)', YELLOW)
    return
  end
  local tF2, tR2, isHC = pressTargets(name, p)
  local rec = {}
  for i = 1, 4 do rec[i] = p.cold[i] + ((i <= 2 and tF2 or tR2) - p.hot[i]) end
  T(string.format('    P. a freddo consigliate: ant %d/%d  post %d/%d psi%s',
    psiInt(rec[1]), psiInt(rec[2]), psiInt(rec[3]), psiInt(rec[4]), p.stable and '' or '  (in assestamento)'), p.stable and GREEN or YELLOW)
  if not compact then
    T(string.format('    target a caldo%s: ant %.1f  post %.1f psi', isHC and ' al traguardo (delta 0..+0.8)' or ' (fisica)', tF2, tR2))
  end
end

-- testo grande in grassetto a una posizione (coordinate finestra)
local function bigText(str, size, col, pos)
  local function put(at)
    ui.setCursor(at)
    local ok = pcall(ui.dwriteText, str, size, col)
    if not ok then ui.textColored(str, col) end
  end
  put(pos)
  put(pos + vec2(0.9, 0))
end

-- vettura vista dall'alto con la pressione a freddo consigliata su ogni ruota
local function drawPressureCar(name)
  local p = pdata[name]
  if not p then
    T('    pressioni: dati non ancora sufficienti', GREY)
    return
  end
  if (p.tF or 0) <= 0 or (p.tR or 0) <= 0 then
    T('    pressione ideale non leggibile dalla fisica (tyres.ini)', YELLOW)
    return
  end
  local tF2, tR2, isHC = pressTargets(name, p)
  local rec = {}
  for i = 1, 4 do rec[i] = p.cold[i] + ((i <= 2 and tF2 or tR2) - p.hot[i]) end

  T('Pressioni a freddo da impostare nel setup (psi)', p.stable and GREEN or YELLOW)

  local avail = ui.availableSpaceX()
  local iw = math.min(196, avail - 20)
  local sc = iw / CAR_W
  local ih = CAR_H * sc
  local x0 = ui.getCursorX() + (avail - iw) / 2
  ui.dummy(vec2(0, 22))
  local y0 = ui.getCursorY()
  ui.setCursor(vec2(x0, y0))
  local csrc = NGS and NGS.asset('car_top.png') or nil
  if csrc then ui.image(csrc, vec2(iw, ih)) elseif not NGS then ui.image(CAR_IMG, vec2(iw, ih)) end
  local after = ui.getCursor()

  local fs = 18
  for i = 1, 4 do
    local str = string.format('%d', psiInt(rec[i]))
    local tw = #str * fs * 0.55
    pcall(function() tw = ui.measureDWriteText(str, fs).x end)
    local cx = x0 + WHEEL_POS[i][1] * sc
    local cy = y0 + WHEEL_POS[i][2] * sc
    bigText(str, fs, rgbm(0.04, 0.04, 0.06, 1), vec2(cx - tw / 2, cy - fs * 0.6))
  end
  ui.setCursor(after)
end

-- ============================================================
-- UI: azioni test (pulsante a schermo + tasto)
-- ============================================================
local function bindingControl()
  T('Tasto volante/tastiera: avvia test / stoppa ed elabora', GREY)
  if ctrlBtn then
    local ok = pcall(function() ctrlBtn:control(vec2(220, 0)) end)
    if not ok then T('Assegna il tasto dalle impostazioni controlli di CSP.', YELLOW) end
  else
    T('Assegnazione tasto non disponibile in questa versione di CSP.', YELLOW)
  end
end

local function drawTestActions(car, withBinding)
  if S.hillclimb then return end
  local w = ui.availableSpaceX()
  if st.testing then
    if btn('Stoppa test ed elabora dati', vec2(w, 34)) then testStop(car) end
    if not hasDT() then
      T('Prima fai il drive through (obbligatorio per elaborare).', YELLOW)
    end
  elseif not S.autoTest then
    local comp = compName(car)
    if tests[comp] and #tests[comp] > 0 then
      T('Test gia\' presente per ' .. comp .. ': usa "Rifai test" in Test gomme.', GREY)
    elseif btn('Avvia test', vec2(w, 34)) then
      testStart(car)
    end
  end
  if withBinding then bindingControl() end
end

-- ============================================================
-- UI: schermata principale (live + checklist + navigazione)
-- ============================================================
local function drawLiveHC(car)
  local ctx = context(car)
  T(string.format('Carburante: %.1f L  /  %.0f L', car.fuel, ctx.cap))
  T('Mescola: ' .. compName(car))
end

local function drawLive(car)
  if S.hillclimb then drawLiveHC(car); return end
  local comp = compName(car)
  local pace = refPace()
  local ctx = context(car)
  local fpl = ctx.fpl

  T(string.format('Mescola: %s    Giro: %d', comp, car.lapCount + 1))
  T('Ultimo: ' .. fmtLap(car.previousLapTimeMs / 1000) .. '    Passo medio (5): ' .. fmtLap(avgLast(st.recent, 5)))
  if st.testing then
    T(string.format('TEST %s  %s / %s', st.testComp, fmtHMS(st.testElapsed), fmtHMS(TEST_SECONDS)), YELLOW)
  end

  T(string.format('Carburante: %.1f L / %.0f L', car.fuel, ctx.cap))
  if fpl > 0 then
    T(string.format('Consumo: %.2f L/giro (%s)   Autonomia: %.1f giri', fpl, ctx.fplSrc, car.fuel / fpl))
  else
    T('Consumo non noto per questo circuito: completa un giro pulito.', YELLOW)
  end

  local left = lapsLeft(car, pace)
  if left and fpl > 0 then
    local needed = (left + ctx.margin) * fpl
    local delta = car.fuel - needed
    T(string.format('Giri rimanenti: %.1f   Necessari: %.1f L', left, needed))
    if delta >= 0 then
      T(string.format('Margine +%.1f L (%.1f giri): arrivi senza sosta', delta, delta / fpl), GREEN)
    else
      local stops = ctx.cap > 0 and math.ceil(-delta / ctx.cap - 1e-9) or 1
      T(string.format('Mancano %.1f L: serve rifornimento (%d sosta/e)', -delta, stops), RED)
    end
  elseif S.mode == 2 and pace <= 0 then
    T('Modalita\' tempo: servono giri puliti.', YELLOW)
  end

  if S.mode == 2 then
    T('Tempo rimanente: ' .. fmtHMS(num(S.raceValue, 0) * 60 - st.raceElapsed))
    if ui.button(st.raceRunning and 'Pausa timer' or 'Avvia timer') then st.raceRunning = not st.raceRunning end
    ui.sameLine()
    if ui.button('Reset timer') then st.raceElapsed = 0; st.raceRunning = false end
  end

  local state, remain, w = pitWindowState(car)
  if state == 'incompat' then
    T(PIT_ERR_INCOMPAT, RED)
  elseif state == 'invalid' then
    T('Finestra pit abilitata ma non valida: controlla Info sessione.', RED)
  elseif state then
    local unit = S.mode == 1 and 'giri' or 'min'
    if st.mandDone then
      T('Sosta obbligatoria: effettuata', GREEN)
    elseif state == 'before' then
      T(string.format('Finestra pit %g-%g %s: apre tra %.1f %s', w.ws, w.we, unit, remain, unit), YELLOW)
    elseif state == 'open' then
      T(string.format('FINESTRA PIT APERTA: chiude tra %.1f %s', remain, unit), GREEN)
    else
      T('Finestra pit chiusa', RED)
    end
  end
end

local function drawChecklistHC(car)
  local comp = compName(car)
  local p = pdata[comp .. ' [HC]']
  tick(st.hc ~= nil or p ~= nil, 'Transita dalla partenza')
  tick(p ~= nil, 'Transita dal traguardo')
end

local function drawChecklist(car)
  if S.hillclimb then drawChecklistHC(car); return end
  local comp = compName(car)
  local td = tests[comp]
  local running = st.testing and st.testComp == comp
  local started = running or (td ~= nil and #td > 0)
  local finished = (not running) and td ~= nil and #td > 0
  local p = pdata[comp]

  T('Cosa fare con la mescola ' .. comp, YELLOW)
  tick(started, S.autoTest and 'Esci dai box: il test di 20 min parte da solo'
                          or 'Avvia il test (pulsante o tasto): 20 min')
  tick(fuelBase ~= nil or #st.fuelLaps > 0, 'Giri puliti senza box: rilevo consumo e passo')
  tick(tonumber(laneDB[trackKey or '']) ~= nil, 'Fai un drive through senza fermarti')
  tick(p ~= nil and p.stable == true, 'Pressioni gomme stabilizzate (automatico)')
  tick(finished, 'Completa i 20 minuti (o stoppa con il tasto)')
  if finished then
    T('Poi torna ai pit: cambia mescola e rifai il test, oppure apri la Strategia consigliata.', GREY)
  end
end

local function drawHCButton()
  local w = ui.availableSpaceX()
  local col = S.hillclimb and rgbm(0.10, 0.55, 0.20, 1) or nil
  if btn('Hillclimb MODE', vec2(w, 38), col) then setHillclimb(not S.hillclimb) end
end

local function drawNav()
  local w = ui.availableSpaceX()
  local bw = math.floor((w - 16) / 3)
  if btn('Info\nsessione', vec2(bw, 52)) then page = 'info' end
  ui.sameLine()
  if btn('Test\ngomme', vec2(bw, 52)) then page = 'tests' end
  ui.sameLine()
  if btn('Strategia\nconsigliata', vec2(bw, 52)) then page = 'strategy' end
end

local function drawHome(car)
  drawHeader(0.7)
  ui.dummy(vec2(0, 12))
  drawNav()
  ui.dummy(vec2(0, 2))
  drawHCButton()
  ui.dummy(vec2(0, 2))
  ui.separator()
  drawLive(car)
  ui.separator()
  drawChecklist(car)
  drawTestActions(car, false)
end

-- ============================================================
-- UI: Info sessione
-- ============================================================
local function drawInfo(car)
  if S.hillclimb then
    T(string.format('Carburante: %.1f L  /  %.0f L', car.fuel, context(car).cap))
    T('Mescola: ' .. compName(car))
    ui.separator()
    local tr0 = math.max(0, math.min(80, num(S.bgTransp, 0)))
    T(string.format('Trasparenza finestra: %d%%  (0 = opaca, max 80)', math.floor(tr0 + 0.5)))
    ui.setNextItemWidth(260)
    local nv = ui.slider('##bgtransp', tr0, 0, 80, '%.0f')
    if type(nv) == 'number' then S.bgTransp = math.max(0, math.min(80, nv)) end
    ui.sameLine()
    if btn('-') then S.bgTransp = math.max(0, tr0 - 10) end
    ui.sameLine()
    if btn('+') then S.bgTransp = math.min(80, tr0 + 10) end
    return
  end
  T('Durata gara / sessione / stint')
  ui.setNextItemWidth(110)
  ui.combo('##mode', S.mode == 1 and 'Giri' or 'Minuti', function()
    if ui.selectable('Giri', S.mode == 1) then S.mode = 1 end
    if ui.selectable('Minuti', S.mode == 2) then S.mode = 2 end
  end)
  ui.sameLine()
  field(S.mode == 1 and 'giri' or 'minuti', 'raceValue', 70)
  field('Margine carburante (giri)', 'margin')

  ui.separator()
  if checkbox('pitwin', 'Finestra pit obbligatoria', S.pitWin) then S.pitWin = not S.pitWin end
  if S.pitWin then
    local unit = S.mode == 1 and 'giro' or 'minuto'
    field('Inizio finestra (' .. unit .. ')', 'pwStart', 70)
    field('Fine finestra (' .. unit .. ')', 'pwEnd', 70)
    local ws, we = num(S.pwStart, 0), num(S.pwEnd, 0)
    local issue = pitWindowIssue()
    if issue == 'incompat' then
      T(PIT_ERR_INCOMPAT, RED)
      T(string.format('Gara: %g %s, finestra pit: %g-%g.', num(S.raceValue, 0), S.mode == 1 and 'giri' or 'minuti', ws, we), RED)
    elseif issue == 'invalid' then
      T('Inserisci inizio e fine (la fine deve essere dopo l\'inizio).', YELLOW)
    else
      T(string.format('Sosta obbligatoria tra %g e %g (%s)', ws, we, S.mode == 1 and 'giri' or 'minuti'), GREEN)
    end
  end

  ui.separator()
  local tr = math.max(0, math.min(80, num(S.bgTransp, 0)))
  T(string.format('Trasparenza finestra: %d%%  (0 = opaca, max 80)', math.floor(tr + 0.5)))
  ui.setNextItemWidth(260)
  local nv = ui.slider('##bgtransp', tr, 0, 80, '%.0f')
  if type(nv) == 'number' then S.bgTransp = math.max(0, math.min(80, nv)) end
  ui.sameLine()
  if btn('-') then S.bgTransp = math.max(0, tr - 10) end
  ui.sameLine()
  if btn('+') then S.bgTransp = math.min(80, tr + 10) end

  ui.separator()
  T('Dati letti automaticamente')
  local ctx = context(car)
  T(string.format('Server: usura gomme x%.2f | consumo carburante x%.2f', ctx.tr, ctx.fr),
    (ctx.tr ~= 1 or ctx.fr ~= 1) and YELLOW or GREY)
  T(string.format('Serbatoio: %.0f L (%s)', ctx.cap, ctx.capSrc), ctx.capSrc == 'fisica' and GREEN or YELLOW)
  T(string.format('Pit: gomme %.1f s | rifornimento %.2f s/L (%s)', ctx.tyreSec, ctx.litSec, ctx.pitSrc),
    ctx.pitSrc == 'fisica' and GREEN or YELLOW)
  if ctx.fpl > 0 then
    T(string.format('Consumo: %.2f L/giro (%s, %d campioni)', ctx.fpl, ctx.fplSrc, fuelN), GREEN)
  else
    T('Consumo: non ancora noto per questa combinazione auto/circuito', YELLOW)
  end
  T(string.format('Perdita corsia box: %.1f s (%s) + %d s frenata/ripartenza', ctx.lane, ctx.laneSrc, EXTRA_PIT),
    ctx.laneSrc == 'misurata' and GREEN or YELLOW)
  local ref = ctx.refPace > 0 and ctx.refPace or 100
  T(string.format('Effetto carburante: %.3f s/L (calcolato dalla massa dell\'auto)', fuelEffect(ref)), GREY)

  ui.separator()
  if btn('Azzera consumo memorizzato') then
    fuelBase, fuelN = nil, 0
    fuelDB[fuelKey()] = nil
    S.fuelDB = kvSave(fuelDB)
    st.fuelLaps = {}
  end
  ui.sameLine()
  if btn('Azzera perdita corsia') then
    laneDB[trackKey] = nil
    S.laneDB = kvSave(laneDB)
  end
end

-- ============================================================
-- UI: Test gomme
-- ============================================================
local function drawTest(car)
  local comp = compName(car)
  T('Mescola montata: ' .. comp)
  if S.hillclimb then
    T('Hillclimb MODE attiva: i test da 20 minuti sono disattivati. Le pressioni si rilevano a ogni salita.', YELLOW)
    return
  end

  if checkbox('autotest', 'Test automatico all\'uscita dai box', S.autoTest) then S.autoTest = not S.autoTest end

  if st.testing then
    T(string.format('TEST IN CORSO su %s: %s / %s%s', st.testComp, fmtHMS(st.testElapsed), fmtHMS(TEST_SECONDS),
      st.testEnding and '  (finisce al traguardo)' or ''), YELLOW)
    T(string.format('Giri registrati: %d', tests[st.testComp] and #tests[st.testComp] or 0))
    if btn('Interrompi senza elaborare') then endTest(false) end
  elseif tests[comp] and #tests[comp] > 0 then
    local syn = synCount(tests[comp])
    if syn > 0 then
      T(string.format('Test anticipato per %s: proiettato a 20 min (%d giri simulati)', comp, syn), GREEN)
    else
      T('Test completato per ' .. comp, GREEN)
    end
    if btn('Rifai test su ' .. comp) then tests[comp] = {}; pdata[comp] = nil; saveData() end
  elseif S.autoTest then
    T('In attesa: il test parte all\'uscita dai box con ' .. comp, GREY)
  else
    T('Test automatico disattivato: avvia con il pulsante o con il tasto.', GREY)
  end

  drawTestActions(car, true)

  local lane, src = laneLoss()
  if st.dtSample then
    T('Drive through registrato: calcolo a fine test (serve il passo medio).', YELLOW)
  elseif st.dt then
    T('Drive through in corso...', YELLOW)
  elseif src == 'misurata' then
    T(string.format('Perdita drive through misurata: %.1f s', lane), GREEN)
  else
    T('Durante il test fai un drive through (senza fermarti in corsia).', YELLOW)
  end

  ui.separator()
  T('Risultati (normalizzati sul carburante)')
  local any = false
  for name, list in pairs(tests) do
    if #list > 0 or (st.testing and name == st.testComp) then
      any = true
      local an, cnt = analyze(list)
      if an then
        T(string.format('%s: %d giri | best %s | medio %s', name, an.n, fmtLap(an.best), fmtLap(an.rawMean)))
        T(string.format('    degrado %+.3f s/giro | consistenza +/-%.3f s', an.b, an.sd))
      else
        T(string.format('%s: dati insufficienti (%d giri utili, ne servono almeno 3)', name, cnt or 0), YELLOW)
      end
      drawPressure(name)
    end
  end
  if not any then T('Nessun test salvato per questo circuito.', GREY)
  elseif btn('Cancella test di questo circuito') then tests = {}; pdata = {}; saveData() end
end

-- ============================================================
-- UI: Strategia consigliata
-- ============================================================
local function fmtStops(p, ctx)
  local t = {}
  for i, lap in ipairs(p.stopLaps) do
    if ctx.laps then t[i] = string.format('%d', math.floor(lap + 0.5))
    else t[i] = string.format('%d', math.floor(lap * p.pace / 60 + 0.5)) end
  end
  return table.concat(t, ', ')
end

local function drawStrategyHC(car)
  local ctx = context(car)
  local comp = compName(car)
  if ctx.fpl > 0 then
    T(string.format('Carburante da caricare: %.1f L', ctx.fpl + HC_RESERVE), GREEN)
  else
    T('Completa una salita (partenza -> traguardo) per vedere il carburante.', YELLOW)
  end
  T('Mescola: ' .. comp)
  ui.separator()
  local nm = comp .. ' [HC]'
  if pdata[nm] then
    drawPressureCar(nm)
  else
    T('Pressioni: fai una salita completa.', GREY)
  end
end

local function drawStrategy(car)
  if S.hillclimb then drawStrategyHC(car); return end
  local ctx = context(car)
  local results = {}
  for name, list in pairs(tests) do
    local an = analyze(list)
    if an then
      local p = planFor(an, ctx, name)
      p.name, p.an = name, an
      results[#results + 1] = p
    end
  end

  if S.mode == 1 then
    T(string.format('Gara: %d giri', ctx.laps))
  else
    T(string.format('Gara: %s (giri stimati per mescola)', fmtHMS(ctx.seconds)))
  end
  if ctx.pit then
    T(string.format('Finestra pit obbligatoria: %g-%g %s', ctx.pws, ctx.pwe, S.mode == 1 and 'giri' or 'minuti'))
  elseif S.pitWin then
    if pitWindowIssue() == 'incompat' then T(PIT_ERR_INCOMPAT, RED)
    else T('Finestra pit abilitata ma non valida (Info sessione).', YELLOW) end
  end
  if ctx.fpl <= 0 then
    T('Consumo sconosciuto: pianificazione carburante non inclusa.', YELLOW)
  else
    T(string.format('Consumo %.2f L/giro | serbatoio %.0f L | autonomia %d giri',
      ctx.fpl, ctx.cap, math.floor(ctx.cap / ctx.fpl)))
  end
  T(string.format('Perdita corsia %.1f s (%s) | sosta = corsia + %d s + servizio', ctx.lane, ctx.laneSrc, ctx.extra))
  if ctx.laneSrc ~= 'misurata' then
    T('Drive through non ancora misurato: la perdita e\' una stima.', YELLOW)
  end
  if ctx.tr ~= 1 or ctx.fr ~= 1 then
    T(string.format('Parametri riscalati sul server: usura gomme x%.2f, carburante x%.2f', ctx.tr, ctx.fr), YELLOW)
  end
  ui.separator()

  if #results == 0 then
    T('Serve almeno un test mescola valido (completa un test dalla schermata principale).', GREY)
    return
  end
  table.sort(results, function(x, y) return x.score < y.score end)
  local best = results[1]

  T('CONSIGLIATA: ' .. best.name, GREEN)
  drawPressureCar(best.name)
  ui.separator()

  for i, p in ipairs(results) do
    local head
    if S.mode == 1 then
      head = string.format('%d) %s  -  %s', i, p.name, fmtHMS(p.total))
    else
      head = string.format('%d) %s  -  %d giri stimati', i, p.name, p.L)
    end
    T(head, i == 1 and GREEN or WHITE)
    local gap = (p.score - best.score) * best.L
    T(string.format('    soste: %d (carb. %d / gomme %d) | stint ~%.0f giri | sosta ~%.0f s',
      p.stops, p.fuelStops, p.tyreStops, p.per, p.pitStop))
    if p.stops > 0 then
      T(string.format('    soste a %s: %s', S.mode == 1 and 'giro' or 'minuto ~', fmtStops(p, ctx)))
    end
    T(string.format('    vs migliore: %s | degrado %+.3f s/giro | consist. +/-%.3f s',
      i == 1 and '--' or string.format('+%.1f s', gap), p.an.b, p.an.sd))
    if p.life < 999 then T(string.format('    vita gomma stimata: ~%d giri (%s)', p.life, p.lifeSrc)) end
    if ctx.pit then
      if p.winOK then
        T('    finestra pit rispettata', GREEN)
      else
        T(string.format('    finestra pit NON raggiungibile: stint max ~%d giri', p.maxStint), RED)
      end
    end
    if p.extrap then T('    ! stint piu\' lungo del test: stima estrapolata', YELLOW) end
  end

  ui.separator()
  if best.fuelStops > 0 or best.stops > 0 then
    T(string.format('Carburante in partenza: %.1f L, rifornimenti di circa %.1f L',
      math.min(best.need, ctx.cap), best.need / (best.stops + 1)))
  else
    T(string.format('Carburante in partenza consigliato: %.1f L', best.need))
  end
end

-- ============================================================
-- Finestra principale
-- ============================================================
local titles = { info = 'Info sessione', tests = 'Test gomme', strategy = 'Strategia consigliata' }

local function drawSub(car)
  drawHeader(0.42)
  ui.sameLine()
  if btn('< Home', vec2(math.floor(ui.availableSpaceX()), 40)) then page = 'home' end
  ui.dummy(vec2(0, 4))
  T(titles[page] or '', YELLOW)
  ui.separator()
  if page == 'info' then drawInfo(car)
  elseif page == 'tests' then drawTest(car)
  else drawStrategy(car) end
end

function script.windowMain(dt)
  local car = ac.getCar(0)
  if not car then return end
  pcall(ui.setWindowFontScale, 1.15)
  -- Hillclimb: durante la salita solo il logo, senza sfondo
  if S.hillclimb and st.hc and loaded then
    drawHeader(0.7)
    return
  end
  -- Modalita' normale durante l'acquisizione dati (test in corso): logo + riepilogo giri
  if (not S.hillclimb) and st.testing and loaded then
    local wsz = ui.windowSize()
    local hdrH = math.floor(ui.availableSpaceX() * 0.7) * HEADER_RATIO
    ui.drawRectFilled(vec2(0, 0), vec2(wsz.x, hdrH + 30 + 4 * 40 + 40), rgbm(0.04, 0.045, 0.06, 0.8), 6)
    drawHeader(0.7)
    local avg = (st.sessN and st.sessN > 0) and fmtLap(st.sessSum / st.sessN) or '--'
    local best = st.sessBest and fmtLap(st.sessBest) or '--'
    local last = car.previousLapTimeMs > 0 and fmtLap(car.previousLapTimeMs / 1000) or '--'
    local FUCHSIA = rgbm(1, 0.15, 0.85, 1)
    local function row(txt, col)
      local pos = ui.getCursor()
      local pushed = pcall(ui.pushDWriteFont, 'Impact')
      local ok = pcall(ui.dwriteDrawText, txt, 28, pos, col)
      if pushed then pcall(ui.popDWriteFont) end
      if not ok then bigText(txt, 26, col, pos) end
      ui.setCursor(pos)
      ui.dummy(vec2(10, 40))
    end
    ui.dummy(vec2(0, 6))
    row(fmtHMS(math.max(0, TEST_SECONDS - st.testElapsed)), YELLOW)
    row('Giro medio: ' .. avg, GREEN)
    row('Giro veloce: ' .. best, FUCHSIA)
    row('Ultimo giro: ' .. last, WHITE)
    return
  end
  drawBackground()
  if not loaded then T('Caricamento dati auto/circuito...'); return end
  if page == 'home' then drawHome(car) else drawSub(car) end
  -- lampeggio rosso ai bordi della finestra dell'app (fine salita)
  if flash.t >= 0 then
    local FL = 3.5
    local a = (0.5 + 0.5 * math.sin(flash.t * 14)) * math.min(1, (FL - flash.t) / 0.8)
    local ws = ui.windowSize()
    local bw = 28
    for i = 0, 9 do
      local c = rgbm(0.95, 0.05, 0.05, a * (1 - i / 10) * 0.8)
      local o, e = i * bw / 10, bw / 10
      ui.drawRectFilled(vec2(0, o), vec2(ws.x, o + e), c)
      ui.drawRectFilled(vec2(0, ws.y - o - e), vec2(ws.x, ws.y - o), c)
      ui.drawRectFilled(vec2(o, 0), vec2(o + e, ws.y), c)
      ui.drawRectFilled(vec2(ws.x - o - e, 0), vec2(ws.x - o, ws.y), c)
    end
  end
end

return { update = script.update, windowMain = script.windowMain, toastUI = script.toastUI }
