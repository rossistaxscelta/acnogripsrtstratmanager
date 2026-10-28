-- Codice di prova da pubblicare sul server (payload.lua). Gira solo in memoria.
local t = 0
return {
  update = function(dt) t = t + dt end,
  windowMain = function(dt)
    ui.text('PAYLOAD IN RAM: funziona!')
    ui.text(string.format('Tempo di esecuzione: %.1f s', t))
    ui.text('SteamID: ' .. tostring(ac.getSteamID()))
    ui.text('Nessun file di questo codice e\' sul tuo PC.')
  end,
}
