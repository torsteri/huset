/* Huset – interaktiv tomtesjekk.
   Data: Geonorge adresse-API, Kartverket eiendom-API (eiendomsgrense), OpenStreetMap via Overpass (bygninger).
   Kart: Esri flyfoto / Kartverket topo. Regler: SAK10 § 4-1 og Bærums kommuneplan (utnytting).
   Alt kjører i nettleseren. Ingenting lagres. */
(function () {
  'use strict';

  var REGLER = {
    maksAreal: 50, maksMone: 4.0, maksGesims: 3.0, minNabo: 1.0, minBygg: 1.0,
    bya: { '3201': { prosent: 20, parkering: 36, kilde: 'Bærum KPA § 28.2.3' } }
  };
  var TYPER = {
    bod:      { navn: 'Bod',           L: 4, B: 3, gesims: 2.4, vinkel: 27, bolig: false },
    garasje:  { navn: 'Garasje',       L: 6, B: 6, gesims: 2.6, vinkel: 22, bolig: false },
    dobbel:   { navn: 'Dobbelgarasje', L: 8, B: 6, gesims: 2.6, vinkel: 18, bolig: false },
    anneks:   { navn: 'Anneks',        L: 6, B: 5, gesims: 2.6, vinkel: 27, bolig: true }
  };
  var OVERPASS = ['https://overpass-api.de/api/interpreter', 'https://overpass.kumi.systems/api/interpreter'];

  var $ = function (id) { return document.getElementById(id); };
  var state = { eiendom: null, bygg: [], knr: null, adresse: null, sone: null, nytt: null, sjekket: null };
  var map, dragging = null;

  // ------------------------------------------------------------ geometri (lokale meter)
  function proj(lat0) {
    var kx = 111320 * Math.cos(lat0 * Math.PI / 180), ky = 110540;
    return {
      til: function (lon, lat, o) { return [(lon - o[0]) * kx, (lat - o[1]) * ky]; },
      fra: function (x, y, o) { return [o[0] + x / kx, o[1] + y / ky]; }
    };
  }
  function rektangel(senter, L, B, rot) {
    var p = proj(senter[1]), a = rot * Math.PI / 180, c = Math.cos(a), s = Math.sin(a);
    var hj = [[-L / 2, -B / 2], [L / 2, -B / 2], [L / 2, B / 2], [-L / 2, B / 2]].map(function (q) {
      return p.fra(q[0] * c - q[1] * s, q[0] * s + q[1] * c, senter);
    });
    hj.push(hj[0]);
    return turf.polygon([hj]);
  }
  // Saltak som striper med økende høyde, så 3D-visningen viser takformen.
  function takstriper(n) {
    var o = n.senter, p = proj(o[1]), a = n.rot * Math.PI / 180, c = Math.cos(a), s = Math.sin(a);
    var N = 8, ut = [], stig = (n.B / 2) * Math.tan(n.vinkel * Math.PI / 180);
    for (var i = 0; i < N; i++) {
      var y0 = -n.B / 2 + i * n.B / N, y1 = y0 + n.B / N, ym = (y0 + y1) / 2;
      var h = n.gesims + stig * (1 - Math.abs(ym) / (n.B / 2));
      var hj = [[-n.L / 2, y0], [n.L / 2, y0], [n.L / 2, y1], [-n.L / 2, y1], [-n.L / 2, y0]].map(function (q) {
        return p.fra(q[0] * c - q[1] * s, q[0] * s + q[1] * c, o);
      });
      ut.push(turf.polygon([hj], { h: h, b: n.gesims }));
    }
    return turf.featureCollection(ut);
  }
  function mone(n) { return n.gesims + (n.B / 2) * Math.tan(n.vinkel * Math.PI / 180) + 0.2; }
  function avstand(polyA, polyB) {
    // minste avstand mellom to polygoner i meter (0 hvis de overlapper)
    if (turf.booleanIntersects(polyA, polyB)) return 0;
    var la = linjerAv(polyA), lb = linjerAv(polyB), m = Infinity;
    var naer = function (c, ls) { ls.forEach(function (l) { m = Math.min(m, turf.pointToLineDistance(turf.point(c), l, { units: 'meters' })); }); };
    turf.coordEach(polyA, function (c) { naer(c, lb); });
    turf.coordEach(polyB, function (c) { naer(c, la); });
    return m;
  }
  // Alle kantlinjer som enkle LineStrings (tomter og bygg kan ha hull eller flere deler).
  function linjerAv(poly) { return turf.flatten(turf.polygonToLine(poly)).features; }
  function trygg(f, fallback) { try { return f(); } catch (e) { return fallback; } }

  // ------------------------------------------------------------ data
  function hent(url, opts) {
    return fetch(url, opts).then(function (r) { if (!r.ok) throw new Error(r.status); return r.json(); });
  }
  function sokAdresse(q) {
    return hent('https://ws.geonorge.no/adresser/v1/sok?' + new URLSearchParams({ sok: q, treffPerSide: 6, fuzzy: 'true', utkoordsys: 4258 }))
      .then(function (d) { return d.adresser || []; });
  }
  function hentEiendom(a) {
    var q = new URLSearchParams({ kommunenummer: a.kommunenummer, gardsnummer: a.gardsnummer, bruksnummer: a.bruksnummer,
      festenummer: a.festenummer || 0, omrade: 'true', utkoordsys: 4258 });
    return hent('https://api.kartverket.no/eiendom/v1/geokoding?' + q).then(function (d) {
      var f = (d.features || []).filter(function (x) { return x.geometry && /Polygon/.test(x.geometry.type); });
      if (!f.length) throw new Error('Fant ikke eiendomsgrensen');
      var hoved = f.filter(function (x) { return x.properties && x.properties['hovedområde']; })[0] || f[0];
      return turf.feature(hoved.geometry, hoved.properties);
    });
  }
  function hentBygg(eiendom) {
    var b = turf.bbox(turf.buffer(eiendom, 25, { units: 'meters' }));
    var q = '[out:json][timeout:20];(way["building"](' + [b[1], b[0], b[3], b[2]].join(',') + '););out geom;';
    var forsok = function (i) {
      if (i >= OVERPASS.length) return Promise.resolve([]);
      return hent(OVERPASS[i], { method: 'POST', body: 'data=' + encodeURIComponent(q),
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' } })
        .catch(function () { return forsok(i + 1); });
    };
    return forsok(0).then(function (d) {
      return ((d && d.elements) || []).filter(function (e) { return e.geometry && e.geometry.length > 3; }).map(function (e) {
        var ring = e.geometry.map(function (g) { return [g.lon, g.lat]; });
        if (ring[0][0] !== ring[ring.length - 1][0]) ring.push(ring[0]);
        var t = e.tags || {}, h = parseFloat(t.height) || (parseFloat(t['building:levels']) || 0) * 3 || (turf.area(turf.polygon([ring])) > 40 ? 7 : 3);
        return turf.polygon([ring], { h: h, type: t.building });
      });
    });
  }

  // Reserve: bygninger fra OpenStreetMap-vektorfliser (OpenFreeMap, z14), lest direkte.
  var flisUrl = null;
  function byggFraFliser(eiendom) {
    var omr = turf.buffer(eiendom, 25, { units: 'meters' }), b = turf.bbox(omr), z = 14;
    var tx = function (lon) { return Math.floor((lon + 180) / 360 * Math.pow(2, z)); };
    var ty = function (lat) { var r = lat * Math.PI / 180; return Math.floor((1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * Math.pow(2, z)); };
    var fliser = [];
    for (var x = tx(b[0]); x <= tx(b[2]); x++) for (var y = ty(b[3]); y <= ty(b[1]); y++) fliser.push([x, y]);
    var url = flisUrl ? Promise.resolve(flisUrl) : hent('https://tiles.openfreemap.org/planet').then(function (t) { return (flisUrl = t.tiles[0]); });
    return url.then(function (u) {
      return Promise.all(fliser.map(function (t) {
        return fetch(u.replace('{z}', z).replace('{x}', t[0]).replace('{y}', t[1]))
          .then(function (r) { return r.arrayBuffer(); })
          .then(function (buf) { return window.lesFlis(new Uint8Array(buf), t[0], t[1], z, 'building'); })
          .catch(function () { return []; });
      }));
    }).then(function (lister) {
      // Flisene slår sammen mange bygg til ett MultiPolygon. Del dem opp igjen.
      var ut = [];
      [].concat.apply([], lister).forEach(function (f) {
        if (!f.geometry || !/Polygon/.test(f.geometry.type)) return;
        var h = (f.properties && f.properties.render_height) || 6;
        var polys = f.geometry.type === 'Polygon' ? [f.geometry.coordinates] : f.geometry.coordinates;
        polys.forEach(function (c) {
          var p = turf.polygon(c, { h: h });
          if (turf.booleanIntersects(p, omr) && turf.area(p) > 4) ut.push(p);
        });
      });
      // Samme bygg kan komme med fra to fliser (flisene overlapper litt). Behold én, den største.
      ut.sort(function (x, y) { return turf.area(y) - turf.area(x); });
      var ferdig = [];
      ut.forEach(function (p) {
        var dup = ferdig.some(function (q) {
          var i = trygg(function () { return turf.intersect(turf.featureCollection([q, p])); }, null);
          return i && turf.area(i) > 0.5 * turf.area(p);
        });
        if (!dup) ferdig.push(p);
      });
      return ferdig;
    }).catch(function () { return []; });
  }

  // Planer for tomta fra DiBKs nasjonale arealplanbase (åpen WMS, GetFeatureInfo).
  var NAP = 'https://nap.ft.dibk.no/services/wms/';
  function wmsInfo(tjeneste, lag, pt) {
    var d = 0.00015, lat = pt[1], lon = pt[0];
    var q = new URLSearchParams({ service: 'WMS', version: '1.3.0', request: 'GetFeatureInfo', layers: lag, query_layers: lag,
      crs: 'EPSG:4326', bbox: [lat - d, lon - d, lat + d, lon + d].join(','), width: 101, height: 101, i: 50, j: 50,
      info_format: 'application/json', feature_count: 20 });
    return hent(NAP + tjeneste + '/?' + q).then(function (r) { return (r.features || []).map(function (f) { return f.properties || {}; }); });
  }
  function hentPlaner(eiendom) {
    var pt = turf.getCoord(turf.pointOnFeature(eiendom));
    var rp = ['rpomrade_vn1', 'rpomrade_vn2', 'rpomrade_vn3', 'arealformal_vn1', 'arealformal_vn2', 'arealformal_vn3'].join(',');
    return Promise.all([
      medTid(wmsInfo('reguleringsplaner', rp, pt), 8000, null),
      medTid(wmsInfo('kommuneplaner', 'kpomrade,arealformal_kp', pt), 8000, null)
    ]).then(function (r) {
      var reg = r[0] || [], kp = r[1] || [];
      return {
        ok: r[0] !== null,
        planer: reg.filter(function (x) { return /RpOmråde/.test(x.objekttypenavn || '') && !/uregulert/i.test(x.plannavn || ''); }),
        formaal: reg.filter(function (x) { return /formål/i.test(x.objekttypenavn || ''); }),
        kp: kp.filter(function (x) { return /KpOmråde/.test(x.objekttypenavn || ''); }),
        kpFormaal: kp.filter(function (x) { return /formål/i.test(x.objekttypenavn || ''); })
      };
    });
  }
  function formaalTekst(f) {
    var k = String(f['reguleringsformål'] || f['arealformål'] || f['formål'] || '');
    var u = f.utnyttingstall ? ' Utnyttelse i planen: ' + f.utnyttingstall + (/BYA|bebygd/i.test(String(f.utnyttingstype)) || f.utnyttingstype == '2' ? ' % BYA' : '') + '.' : '';
    var navn = /^11/.test(k) || /^1[0-9]{3}$/.test(k) && k < 1200 ? 'boligformål' : /^1/.test(k) ? 'bebyggelse' : /^[56]/.test(k) ? 'landbruk, natur eller friluft (LNF)' : 'formål med kode ' + k;
    return { navn: navn, bolig: /bolig|bebyggelse/.test(navn), utnytt: u };
  }

  // ------------------------------------------------------------ soner
  function lagSoner() {
    var e = state.eiendom;
    var innenfor = trygg(function () { return turf.buffer(e, -REGLER.minNabo, { units: 'meters' }); }, null);
    var fire = trygg(function () { return turf.buffer(e, -4, { units: 'meters' }); }, null);
    var paTomta = state.bygg.filter(function (b) { return turf.booleanIntersects(b, e); });
    var forbudt = paTomta.map(function (b) { return turf.buffer(b, REGLER.minBygg, { units: 'meters' }); });
    var lov = innenfor;
    forbudt.forEach(function (f) { lov = lov && trygg(function () { return turf.difference(turf.featureCollection([lov, f])); }, lov); });
    var randRod = innenfor ? trygg(function () { return turf.difference(turf.featureCollection([e, innenfor])); }, null) : e;
    var randGul = innenfor && fire ? trygg(function () { return turf.difference(turf.featureCollection([innenfor, fire])); }, null) : null;
    state.sone = { lov: lov, rod: randRod, gul: randGul, forbudt: forbudt, paTomta: paTomta };
  }

  // ------------------------------------------------------------ regler
  function sjekk() {
    var n = state.nytt, e = state.eiendom, poly = rektangel(n.senter, n.L, n.B, n.rot), ut = [];
    var areal = n.L * n.B, m = mone(n);
    function r(ok, tittel, tekst) { ut.push({ ok: ok, tittel: tittel, tekst: tekst }); }

    r(areal <= REGLER.maksAreal, 'Areal', fmt(areal) + ' m² (maks ' + REGLER.maksAreal + ' m²)');
    r(!n.bolig, 'Bruk', n.bolig ? 'Anneks til å bo eller sove i krever alltid søknad' : 'Ikke til beboelse');
    var inne = turf.booleanWithin(poly, e);
    var dNabo = inne ? minAvstandTilGrense(poly, e) : 0;
    r(inne && dNabo >= REGLER.minNabo, 'Avstand til nabogrense', inne ? fmt(dNabo) + ' m (minst 1 m)' : 'Bygget står utenfor eiendommen din');
    var dBygg = Infinity;
    state.sone.paTomta.forEach(function (b) { dBygg = Math.min(dBygg, avstand(poly, b)); });
    if (dBygg === Infinity) r(null, 'Avstand til andre bygg', 'Fant ingen bygg på tomta i kartdataene. Sjekk selv at det er minst 1 m');
    else r(dBygg >= REGLER.minBygg, 'Avstand til andre bygg', fmt(dBygg) + ' m (minst 1 m)');
    r(m <= REGLER.maksMone, 'Mønehøyde', fmt(m) + ' m (maks 4 m)');
    r(n.gesims <= REGLER.maksGesims, 'Gesimshøyde', fmt(n.gesims) + ' m (maks 3 m)');

    var bya = REGLER.bya[state.knr];
    var tomt = turf.area(e);
    if (bya) {
      var eks = 0, smaa = 0;
      state.sone.paTomta.forEach(function (b) {
        var a = trygg(function () { return turf.area(turf.intersect(turf.featureCollection([b, e]))); }, 0);
        eks += a; if (a >= 15 && a <= 60) smaa += a;
      });
      // Parkering teller 18 m² per plass. Står det en garasje eller carport der, er plassene trolig allerede med.
      var park = Math.max(0, bya.parkering - smaa);
      var tot = eks + park + areal, maks = tomt * bya.prosent / 100;
      var utn = tot <= maks ? true : (tot <= maks * 1.05 ? null : false);
      r(utn, 'Utnyttelse av tomta', fmt(tot / tomt * 100) + ' % av ' + bya.prosent + ' % tillatt: ' + fmt(eks) + ' m² bygg i dag' +
        (park ? ', ' + fmt(park) + ' m² parkering' : '') + ' og ' + fmt(areal) + ' m² nytt, på ' + Math.round(tomt) + ' m² tomt.' +
        (utn === null ? ' Det er på grensen, og kartdataene er ikke nøyaktige nok til å avgjøre det. Vi måler for deg' : '') +
        (utn === false ? ' Byggene som står der fra før bruker det meste av tomta' : ''));
    } else {
      var eks2 = 0;
      state.sone.paTomta.forEach(function (b) { eks2 += trygg(function () { return turf.area(turf.intersect(turf.featureCollection([b, e]))); }, 0); });
      var pst = (eks2 + areal) / tomt * 100;
      r(pst <= 20 ? true : null, 'Utnyttelse av tomta', 'Med det nye bygget er ' + fmt(pst) + ' % av tomta bebygd (' + fmt(eks2) + ' m² i dag og ' + fmt(areal) +
        ' m² nytt, på ' + Math.round(tomt) + ' m²). Vanlig grense i småhusområder rundt Oslo er 20–24 %, ' +
        (pst <= 20 ? 'så dette ser trygt ut.' : 'så dette må sjekkes mot planen for tomta din. Vi gjør det for deg.'));
    }
    var innsyn = { '3201': ['https://www.arealplaner.no/baerum3201/', 'Bærums planregister'],
      '3203': ['https://www.arealplaner.no/asker3203/', 'Askers planregister'],
      '0301': ['https://od2.pbe.oslo.kommune.no/kart/', 'Oslos plankart'] }[state.knr];
    var pl = state.plan, lenke = function (url, t) { return '<a href="' + url + '" target="_blank" rel="noopener">' + t + '</a>'; };
    if (pl && pl.planer.length) {
      var p0 = pl.planer[0], aar = (p0.ikrafttredelsesdato || '').slice(0, 4), f0 = pl.formaal[0] ? formaalTekst(pl.formaal[0]) : null;
      if (f0 && !f0.bolig) r(false, 'Formål i planen', 'Tomta er regulert til ' + f0.navn + '. Da kan du ikke bygge uten søknad');
      r(null, 'Reguleringsplanen', 'Tomta er regulert i «' + p0.plannavn + '»' + (aar ? ' fra ' + aar : '') + (f0 ? ', til ' + f0.navn + '.' : '.') + (f0 ? f0.utnytt : '') +
        ' Planen kan ha egne regler for høyde, plassering og avstand til vei. ' + (p0.link ? lenke(p0.link, 'Les planen') + ', eller la oss lese den for deg.' : 'Vi leser den for deg.') +
        (pl.planer.length > 1 ? ' (' + (pl.planer.length - 1) + ' plan til gjelder også her.)' : ''));
    } else if (pl && pl.ok) {
      var k0 = pl.kpFormaal[0] ? formaalTekst(pl.kpFormaal[0]) : null;
      if (k0 && !k0.bolig) r(false, 'Formål i kommuneplanen', 'Tomta ligger i ' + k0.navn + '. Da kan du ikke bygge uten søknad');
      r(k0 && k0.bolig ? true : null, 'Reguleringsplanen', 'Tomta er ikke regulert, så kommuneplanen gjelder' + (k0 ? ': ' + k0.navn + '.' : '.') +
        (pl.kp[0] && pl.kp[0].plannavn ? ' (' + pl.kp[0].plannavn + ')' : ''));
    } else {
      r(null, 'Reguleringsplanen', (pl === null ? 'Henter planen for tomta… ' : 'Fant ikke planen automatisk. ') +
        'Vi leser den og bekrefter svaret ditt' + (innsyn ? ', eller du kan se den selv i ' + lenke(innsyn[0], innsyn[1]) + ' (gnr/bnr ' +
        state.adresse.gardsnummer + '/' + state.adresse.bruksnummer + ').' : '.'));
    }

    var brudd = ut.filter(function (x) { return x.ok === false; });
    state.sjekket = { regler: ut, brudd: brudd, poly: poly, mone: m, areal: areal };
    visResultat();
    oppdaterKart();
  }
  function minAvstandTilGrense(poly, e) {
    var m = Infinity, ls = linjerAv(e);
    turf.coordEach(poly, function (c) {
      ls.forEach(function (l) { m = Math.min(m, turf.pointToLineDistance(turf.point(c), l, { units: 'meters' })); });
    });
    return m;
  }
  function fmt(x) { return (Math.round(x * 10) / 10).toString().replace('.', ','); }

  // ------------------------------------------------------------ visning
  function visResultat() {
    var s = state.sjekket, n = state.nytt;
    var ok = !s.brudd.length;
    var tvil = s.regler.filter(function (x) { return x.ok === null && x.tittel !== 'Reguleringsplanen'; });
    var dom = $('dom'), navn = TYPER[n.type].navn;
    dom.className = 'dom ' + (!ok ? 'rod' : tvil.length ? 'gul' : 'gronn');
    dom.innerHTML = !ok
      ? '<b>Ikke slik den står nå.</b> Det som stopper: ' + s.brudd.map(function (b) { return b.tittel.toLowerCase(); }).join(', ') + '. Prøv å flytte eller gjøre den mindre.'
      : tvil.length
        ? '<b>Nesten.</b> ' + navn + ' på ' + fmt(s.areal) + ' m² her ser ut til å gå uten søknad, men ' + tvil.map(function (b) { return b.tittel.toLowerCase(); }).join(' og ') + ' må sjekkes nærmere.'
        : '<b>Ser bra ut.</b> ' + navn + ' på ' + fmt(s.areal) + ' m² her kan trolig settes opp uten søknad.';
    var mk = $('merke'); mk.hidden = false; mk.className = dom.className.replace('dom ', '');
    mk.textContent = !ok ? '✕ Ikke lov slik' : tvil.length ? '! Nesten, sjekk utnyttelse' : '✓ Lov uten søknad';
    if (tvil.length && ok) mk.textContent = '! Nesten: ' + tvil.map(function (b) { return b.tittel.toLowerCase(); }).join(', ');
    $('regler').innerHTML = s.regler.map(function (x) {
      var k = x.ok === true ? 'ok' : x.ok === false ? 'bad' : 'warn', ikon = x.ok === true ? '✓' : x.ok === false ? '✕' : '!';
      return '<li class="' + k + '"><span class="ikon">' + ikon + '</span><div><b>' + x.tittel + '</b><br>' + x.tekst + '</div></li>';
    }).join('');
    $('h-mone').textContent = fmt(s.mone) + ' m';
    $('f-plass').value = JSON.stringify({ type: n.type, L: n.L, B: n.B, rot: n.rot, senter: n.senter.map(function (v) { return +v.toFixed(6); }),
      gesims: n.gesims, vinkel: n.vinkel, ok: ok });
  }

  function oppdaterKart() {
    if (!map.getSource('nytt')) return;
    var s = state.sjekket, ok = !s.brudd.length;
    map.getSource('nytt').setData(s.poly);
    map.getSource('tak').setData(takstriper(state.nytt));
    map.setPaintProperty('nytt-linje', 'line-color', ok ? '#1f9d55' : '#d93025');
    map.setPaintProperty('tak', 'fill-extrusion-color', ok ? '#3fae6a' : '#e5534b');
  }

  function tegnTomt() {
    var tom = turf.featureCollection([]), z = state.sone;
    var set = function (id, data) { map.getSource(id).setData(data || tom); };
    set('eiendom', state.eiendom);
    set('lov', z.lov); set('rod', z.rod); set('gul', z.gul);
    set('forbudt', turf.featureCollection(z.forbudt));
    set('bygg', turf.featureCollection(state.bygg));
    var b = turf.bbox(state.eiendom);
    map.fitBounds([[b[0], b[1]], [b[2], b[3]]], { padding: 60, duration: 0, maxZoom: 20 });
  }

  function initKart() {
    map = new maplibregl.Map({
      container: 'kart', attributionControl: { compact: true }, maxPitch: 70,
      style: {
        version: 8,
        sources: {
          foto: { type: 'raster', tileSize: 256, maxzoom: 19, attribution: 'Flyfoto © Esri, Maxar',
            tiles: ['https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}'] },
          omt: { type: 'vector', url: 'https://tiles.openfreemap.org/planet', attribution: '© OpenStreetMap' },
          topo: { type: 'raster', tileSize: 256, maxzoom: 18, attribution: '© Kartverket',
            tiles: ['https://cache.kartverket.no/v1/wmts/1.0.0/topo/default/webmercator/{z}/{y}/{x}.png'] }
        },
        layers: [
          { id: 'topo', type: 'raster', source: 'topo', layout: { visibility: 'none' } },
          { id: 'foto', type: 'raster', source: 'foto' }
        ]
      },
      center: [10.57, 59.9], zoom: 12
    });
    window.husetKart = map;
    map.addControl(new maplibregl.NavigationControl({ visualizePitch: true }), 'top-right');
    map.on('load', function () {
      var tom = { type: 'FeatureCollection', features: [] };
      ['eiendom', 'lov', 'rod', 'gul', 'forbudt', 'bygg', 'nytt', 'tak'].forEach(function (id) { map.addSource(id, { type: 'geojson', data: tom }); });
      map.addLayer({ id: 'lov', type: 'fill', source: 'lov', paint: { 'fill-color': '#22c55e', 'fill-opacity': 0.28 } });
      map.addLayer({ id: 'gul', type: 'fill', source: 'gul', paint: { 'fill-color': '#facc15', 'fill-opacity': 0.18 } });
      map.addLayer({ id: 'rod', type: 'fill', source: 'rod', paint: { 'fill-color': '#ef4444', 'fill-opacity': 0.45 } });
      map.addLayer({ id: 'forbudt', type: 'fill', source: 'forbudt', paint: { 'fill-color': '#ef4444', 'fill-opacity': 0.4 } });
      map.addLayer({ id: 'eiendom-linje', type: 'line', source: 'eiendom', paint: { 'line-color': '#ffffff', 'line-width': 3 } });
      map.addLayer({ id: 'eiendom-stiplet', type: 'line', source: 'eiendom', paint: { 'line-color': '#111', 'line-width': 3, 'line-dasharray': [2, 2] } });
      map.addLayer({ id: 'nabobygg', type: 'fill-extrusion', source: 'omt', 'source-layer': 'building', minzoom: 14,
        paint: { 'fill-extrusion-color': '#b9bec4', 'fill-extrusion-opacity': 0.55,
          'fill-extrusion-height': ['coalesce', ['get', 'render_height'], 6], 'fill-extrusion-base': ['coalesce', ['get', 'render_min_height'], 0] } });
      map.addLayer({ id: 'bygg', type: 'line', source: 'bygg', paint: { 'line-color': '#374151', 'line-width': 2 } });
      map.addLayer({ id: 'tak', type: 'fill-extrusion', source: 'tak', paint: { 'fill-extrusion-color': '#3fae6a', 'fill-extrusion-height': ['get', 'h'], 'fill-extrusion-base': 0, 'fill-extrusion-opacity': 0.95 } });
      map.addLayer({ id: 'nytt', type: 'fill', source: 'nytt', paint: { 'fill-color': '#ffffff', 'fill-opacity': 0.01 } });
      map.addLayer({ id: 'nytt-linje', type: 'line', source: 'nytt', paint: { 'line-color': '#1f9d55', 'line-width': 3 } });

      // Dra bygget
      var start = function (e) {
        e.preventDefault(); dragging = { fra: e.lngLat, senter: state.nytt.senter.slice() };
        map.dragPan.disable(); map.getCanvas().style.cursor = 'grabbing';
      };
      map.on('mousedown', 'nytt', start);
      map.on('touchstart', 'nytt', function (e) { if (e.points && e.points.length === 1) start(e); });
      map.on('mouseenter', 'nytt', function () { if (!dragging) map.getCanvas().style.cursor = 'grab'; });
      map.on('mouseleave', 'nytt', function () { if (!dragging) map.getCanvas().style.cursor = ''; });
      var flytt = function (e) {
        if (!dragging) return;
        state.nytt.senter = [dragging.senter[0] + e.lngLat.lng - dragging.fra.lng, dragging.senter[1] + e.lngLat.lat - dragging.fra.lat];
        sjekk();
      };
      map.on('mousemove', flytt); map.on('touchmove', flytt);
      var slutt = function () { if (dragging) { dragging = null; map.dragPan.enable(); map.getCanvas().style.cursor = ''; } };
      map.on('mouseup', slutt); map.on('touchend', slutt);
      map.on('click', function (e) {
        if (!state.eiendom || dragging) return;
        if (map.queryRenderedFeatures(e.point, { layers: ['nytt'] }).length) return;
        if (turf.booleanPointInPolygon([e.lngLat.lng, e.lngLat.lat], state.eiendom)) { state.nytt.senter = [e.lngLat.lng, e.lngLat.lat]; sjekk(); }
      });
      state.kartKlar = true; venter.splice(0).forEach(function (f) { f(); });
      var p = new URLSearchParams(location.search).get('adresse');
      if (p) { $('sok').value = p; velgForste(p); }
    });
  }

  // ------------------------------------------------------------ flyt
  function startPlassering() {
    var t = TYPER[$('type').value];
    var rot = husRetning();
    state.nytt = { type: $('type').value, L: t.L, B: t.B, rot: rot, gesims: t.gesims, vinkel: t.vinkel, bolig: t.bolig,
      senter: finnPlass(t.L, t.B, rot) };
    syncKontroller();
    sjekk();
  }
  // Finn et sted der bygget får plass i den grønne sonen, nærmest huset.
  function finnPlass(L, B, rot) {
    var lov = state.sone.lov, e = state.eiendom;
    var mal = trygg(function () { return turf.getCoord(turf.centerOfMass(lov)); }, null) || turf.getCoord(turf.centroid(hus || e));
    if (!lov) return turf.getCoord(turf.centroid(e));
    var b = turf.bbox(lov), p = proj(b[1]), o = [b[0], b[1]], maks = p.til(b[2], b[3], o), best = null, bestD = Infinity;
    var steg = Math.max(1, Math.max(maks[0], maks[1]) / 40);
    for (var x = 0; x <= maks[0]; x += steg) for (var y = 0; y <= maks[1]; y += steg) {
      var c = p.fra(x, y, o);
      if (!turf.booleanPointInPolygon(c, lov)) continue;
      var d = turf.distance(c, mal);
      if (d >= bestD) continue;
      if (trygg(function () { return turf.booleanWithin(rektangel(c, L, B, rot), lov); }, false)) { best = c; bestD = d; }
    }
    return best || trygg(function () { return turf.getCoord(turf.pointOnFeature(lov)); }, null) || turf.getCoord(turf.centroid(e));
  }
  function husRetning() {
    // Legg bygget parallelt med huset, det ser naturlig ut og passer ofte best.
    var hus = state.sone.paTomta.slice().sort(function (a, b) { return turf.area(b) - turf.area(a); })[0];
    if (!hus) return 0;
    var c = turf.getCoords(hus)[0], best = 0, lang = 0;
    for (var i = 0; i < c.length - 1; i++) {
      var d = turf.distance(c[i], c[i + 1], { units: 'meters' });
      if (d > lang) { lang = d; best = turf.bearing(c[i], c[i + 1]); }
    }
    return Math.round(90 - best);
  }
  function syncKontroller() {
    var n = state.nytt;
    $('L').value = n.L; $('B').value = n.B; $('rot').value = ((n.rot % 180) + 180) % 180; $('gesims').value = n.gesims;
    $('v-L').textContent = fmt(n.L) + ' m'; $('v-B').textContent = fmt(n.B) + ' m'; $('v-rot').textContent = Math.round($('rot').value) + '°';
    $('v-gesims').textContent = fmt(n.gesims) + ' m';
  }

  function velgAdresse(a) {
    state.adresse = a; state.knr = a.kommunenummer;
    $('verktoy').hidden = false;
    $('status').textContent = 'Henter eiendomsgrense og bygninger for ' + a.adressetekst + '…';
    $('tittel').textContent = a.adressetekst + ', ' + titleCase(a.poststed || '');
    $('matr').textContent = 'Gnr/bnr ' + a.gardsnummer + '/' + a.bruksnummer + ' · ' + titleCase(a.kommunenavn || '');
    $('f-adresse').value = a.adressetekst + ', ' + a.postnummer + ' ' + titleCase(a.poststed || '') + ' (' + a.gardsnummer + '/' + a.bruksnummer + ')';
    $('f-kommune').value = titleCase(a.kommunenavn || '');
    map.resize();
    $('verktoy').scrollIntoView({ behavior: 'smooth', block: 'start' });
    var nr = (state.forsok = (state.forsok || 0) + 1);
    hentEiendom(a).then(function (e) {
      if (nr !== state.forsok) return;
      state.eiendom = e; state.bygg = []; state.plan = null;
      hentPlaner(e).then(function (pl) { if (nr === state.forsok) { state.plan = pl; klar(function () { if (state.nytt) sjekk(); }); } })
        .catch(function () {});
      // Vis tomta med en gang, bygningene kommer etterpå.
      klar(function () { lagSoner(); tegnTomt(); startPlassering(); });
      $('status').textContent = 'Tomt på ' + Math.round(turf.area(e)) + ' m². Henter bygningene rundt…';
      // Bygninger: vektorfliser først (raskt), så Overpass. Gir opp etter noen sekunder.
      return medTid(byggFraFliser(e), 7000, []).then(function (b) {
        return b.length ? b : medTid(hentBygg(e), 7000, []);
      }).then(function (bygg) {
        if (nr !== state.forsok) return;
        state.bygg = bygg;
        klar(function () {
          lagSoner(); tegnTomt(); startPlassering();
        });
        $('status').textContent = 'Tomt på ' + Math.round(turf.area(state.eiendom)) + ' m². Dra bygget rundt på kartet.' +
          (state.bygg.length ? '' : ' Fant ingen bygninger i kartdataene, så avstand til huset må du sjekke selv.');
      });
    }).catch(function (feil) {
      if (window.console) console.warn('Tomtesjekk:', feil);
      if (nr !== state.forsok) return;
      $('status').textContent = 'Fant ikke eiendomsgrensen for denne adressen. Prøv en annen adresse, eller send den til oss under.';
    });
  }
  // Kjør når kartet er lastet (adressen kan komme før kartet er klart).
  var venter = [];
  function klar(f) { if (state.kartKlar) f(); else venter.push(f); }
  function medTid(p, ms, reserve) {
    return Promise.race([p.catch(function () { return reserve; }), new Promise(function (ok) { setTimeout(function () { ok(reserve); }, ms); })]);
  }
  function titleCase(s) { return s.toLowerCase().replace(/(^|[\s-])\S/g, function (c) { return c.toUpperCase(); }); }

  function velgForste(q) { sokAdresse(q).then(function (l) { if (l.length) velgAdresse(l[0]); }); }

  // ------------------------------------------------------------ oppsett
  document.addEventListener('DOMContentLoaded', function () {
    initKart();
    var timer, liste = $('forslag');
    $('sok').addEventListener('input', function () {
      clearTimeout(timer);
      var q = this.value.trim();
      if (q.length < 3) { liste.hidden = true; return; }
      timer = setTimeout(function () {
        sokAdresse(q).then(function (l) {
          liste.innerHTML = l.map(function (a, i) {
            return '<li role="option" data-i="' + i + '">' + a.adressetekst + ', <span>' + a.postnummer + ' ' + titleCase(a.poststed || '') + '</span></li>';
          }).join('');
          liste.hidden = !l.length;
          Array.prototype.forEach.call(liste.children, function (li) {
            li.addEventListener('click', function () { liste.hidden = true; $('sok').value = li.textContent; velgAdresse(l[+li.dataset.i]); });
          });
        }).catch(function () {});
      }, 250);
    });
    $('sokform').addEventListener('submit', function (e) { e.preventDefault(); liste.hidden = true; velgForste($('sok').value); });

    $('type').addEventListener('change', function () { if (state.eiendom) { var s = state.nytt.senter; startPlassering(); state.nytt.senter = s; sjekk(); } });
    [['L', 'L'], ['B', 'B'], ['rot', 'rot'], ['gesims', 'gesims']].forEach(function (k) {
      $(k[0]).addEventListener('input', function () { if (!state.nytt) return; state.nytt[k[1]] = parseFloat(this.value); syncKontroller(); sjekk(); });
    });
    $('vis3d').addEventListener('click', function () {
      var tre = map.getPitch() < 10;
      map.easeTo({ pitch: tre ? 60 : 0, bearing: tre ? -25 : 0, duration: 800 });
      this.textContent = tre ? 'Vis ovenfra' : 'Vis i 3D';
    });
    $('lag').addEventListener('click', function () {
      var foto = map.getLayoutProperty('foto', 'visibility') !== 'none';
      map.setLayoutProperty('foto', 'visibility', foto ? 'none' : 'visible');
      map.setLayoutProperty('topo', 'visibility', foto ? 'visible' : 'none');
      this.textContent = foto ? 'Flyfoto' : 'Kart';
    });
  });
})();
