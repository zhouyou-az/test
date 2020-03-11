window.WeatherWind = (function() {
    var PARTICLE_LINE_WIDTH = 1;                // 线宽
    var VELOCITY_SCALE_MAX = 0.5;               // 最大风速度系数
    var VELOCITY_SCALE_MIN = 0.1;               // 最小网速系数
    var NULL_WIND_VECTOR = [NaN, NaN, null];    // 没有风数据时的标识 [u, v, magnitude]
    var PARTICLE_MULTIPLIER_MAX = 1 / 70;       // 风场粒子密度最大系数
    var PARTICLE_MULTIPLIER_MIN = 1 / 500;      // 风场粒子密度最小系统
    var PARTICLE_REDUCTION = 0.7;               // 手机设备时粒子密度再降低
    var FRAME_RATE = 30;                        // 运行帧数
    var MAX_PARTICLE_AGE = 80;                  // 粒子生命周期
    var LINE_SIZE_MAX = 0.97;                   // 线长最大系数
    var LINE_SIZE_MIN = 0.5;                    // 线长最小系数
    var LINE_COLOR = '#ffffff';                 // 默认线颜色 

    var Windy = {};
    var cxtParticle;    // 画风粒子的 canvas
    var cxtMask;        // 画风场背景的 canvas
    var invert;         // 用于像素点转经纬度
    var project;        // 用于经纬度转像素点

    var timer;
    var timerInterpolate;
    var timerFrame;
    var width, height;
    var dataCurrent;
    var gridCurrent;
    var columnsCurrent;
    var colorsForMask;
    var colorsForParticle;

    var lineColorCurrent;
    var fadeFillStyleCurrent;
    var lineWidthCurrent;
    var paticleMultiplierCurrent;   // 粒子系数
    var velocityScaleCurrent;       // 速度系统
    var particleCount;              // 粒子数

    function _log() {
        // console.log.apply(console, arguments);
    }
    function isMobile() {
        return (/android|blackberry|iemobile|ipad|iphone|ipod|opera mini|webos/i).test(navigator.userAgent);
    }
    function isValue(x) {
        return x !== null && x !== undefined;
    }
    function floorMod(a, n) {
        return a - n * Math.floor(a / n);
    }
    function distort(projection, λ, φ, x, y, scale, wind) {
        wind[0] *= scale;
        wind[1] *= scale;
        return wind;
        // var u = wind[0] * scale;
        // var v = wind[1] * scale;
        // var d = distortion(projection, λ, φ, x, y);

        // // Scale distortion vectors by u and v, then add.
        // wind[0] = d[0] * u + d[2] * v;
        // wind[1] = d[1] * u + d[3] * v;
        // return wind;
    };

    var getBlurWorker = (function() {
        var blurWorker;
        function _getWorker() {
            function b() {
                function a(a) {
                    i = new Uint16Array(a), d = new Uint16Array(a), e = new Uint16Array(a)
                }
        
                function b(a) {
                    j = new Uint32Array(a), f = new Uint32Array(a)
                }
        
                function c(c, k, l, m, n, o, p, q) {
                    q = q || 3, q |= 0;
                    var r = o * p;
                    r > i.length && a(r), r = Math.max(o, p), r > j.length && b(r);
                    var s, t, u, v, w, x, y, z, A, B, C, w, D, x, y, z, E, D = 0,
                        F = 0,
                        G = 0,
                        H = o - 1,
                        I = p - 1,
                        J = q + 1,
                        K = g[q],
                        L = h[q],
                        M = (1e7 * K >>> L) / 1e7,
                        N = j,
                        O = f,
                        P = i,
                        Q = d,
                        R = e,
                        S = c.data;
                    for (B = 0; o > B; B++) N[B] = ((x = B + J) < H ? x : H) << 2, O[B] = (x = B - q) > 0 ? x << 2 : 0;
                    for (v = 0; p > v; v++) {
                        for (s = S[G] * J, t = S[G + 1] * J, u = S[G + 2] * J, w = 1; q >= w; w++) x = G + ((w > H ? H : w) << 2), s += S[x], t += S[x + 1], u += S[x + 2];
                        for (D = 0; o > D; D++) P[F] = s, Q[F] = t, R[F] = u, y = G + N[D], z = G + O[D], s += S[y] - S[z], t += S[y + 1] - S[z + 1], u += S[y + 2] - S[z + 2], F++;
                        G += o << 2
                    }
                    for (C = 0; p > C; C++) N[C] = ((x = C + J) < I ? x : I) * o, O[C] = (x = C - q) > 0 ? x * o : 0;
                    for (D = 0; o > D; D++) {
                        for (A = D, s = P[A] * J, t = Q[A] * J, u = R[A] * J, w = 1; q >= w; w++) A += w > I ? 0 : o, s += P[A], t += Q[A], u += R[A];
                        for (F = D << 2, E = o << 2, v = 0; p > v; v++) S[F] = s * M, S[F + 1] = t * M, S[F + 2] = u * M, y = D + N[v], z = D + O[v], s += P[y] - P[z], t += Q[y] - Q[z], u += R[y] - R[z], F += E
                    }
                    return c
                }
                var d, e, f, g = [1, 57, 41, 21, 203, 34, 97, 73, 227, 91, 149, 62, 105, 45, 39, 137, 241, 107, 3, 173, 39, 71, 65, 238, 219, 101, 187, 87, 81, 151, 141, 133],
                    h = [0, 9, 10, 10, 14, 12, 14, 14, 16, 15, 16, 15, 16, 15, 15, 17, 18, 17, 12, 18, 16, 17, 17, 19, 19, 18, 19, 18, 18, 19, 19, 19, 20, 19, 20, 20, 20, 20, 20, 20],
                    i = [],
                    j = [];
                self.onmessage = function(a) {
                    postMessage(c(a.data.imageData, a.data.x0, a.data.y0, a.data.xMax, a.data.yMax, a.data.width, a.data.height, a.data.radius))
                }
            }
            var c, d, e = null,
                f = window.URL || window.webkitURL;
            if (!window.Worker) {
                console.error("Web Worker not supported")
            }
            try {
                d = "(" + b.toString() + ")()";
                try {
                    c = new Blob([d], {
                        type: "application/javascript"
                    })
                } catch (g) {
                    window.BlobBuilder = window.BlobBuilder || window.WebKitBlobBuilder || window.MozBlobBuilder, c = new BlobBuilder, c.append(d), c = blob.getBlob(), a.event("Using old version of BlobBuilder, just for info")
                }
                try {
                    e = new Worker(f.createObjectURL(c))
                } catch (g) {
                    console.error("Unable to createObjectURL " + g);
                }
            } catch (g) {
                console.error("Failed to stringyfy blurFunction " + g);
            }
            return e
        }

        return function(cb) {
            if (!blurWorker) {
                blurWorker = _getWorker();
            }
            blurWorker.onmessage = function(e) {
                cb && cb(e);
            }
            return blurWorker;
        }
    })();
    function distortion(projection, λ, φ, x, y) {
        var τ = 2 * Math.PI;
        var H = Math.pow(10, -5.2);
        var hλ = λ < 0 ? H : -H;
        var hφ = φ < 0 ? H : -H;

        var pλ = project([φ, λ + hλ]);
        var pφ = project([φ + hφ, λ]);

        // Meridian scale factor (see Snyder, equation 4-3), where R = 1. This handles issue where length of 1º λ
        // changes depending on φ. Without this, there is a pinching effect at the poles.
        var k = Math.cos(φ / 360 * τ);
        return [
            (pλ[0] - x) / hλ / k,
            (pλ[1] - y) / hλ / k,
            (pφ[0] - x) / hφ,
            (pφ[1] - y) / hφ
        ];
    };
    function bilinearInterpolateVector(x, y, g00, g10, g01, g11) {
        var rx = (1 - x);
        var ry = (1 - y);
        var a = rx * ry, b = x * ry, c = rx * y, d = x * y;
        var u = g00[0] * a + g10[0] * b + g01[0] * c + g11[0] * d;
        var v = g00[1] * a + g10[1] * b + g01[1] * c + g11[1] * d;
        return [u, v, Math.sqrt(u * u + v * v)];
    }
    function createWindBuilder(uComp, vComp) {
        var uData = uComp.data, vData = vComp.data;
        return {
            header: uComp.header,
            data: function (i) {
                return [uData[i], vData[i]];
            },
            interpolate: bilinearInterpolateVector
        }
    }
    function createBuilder() {
        var uComp = null, vComp = null, scalar = null;
        
        dataCurrent.forEach(function (record) {
            switch (record.header.parameterCategory + "," + record.header.parameterNumber) {
                case "2,2": uComp = record; break;
                case "2,3": vComp = record; break;
                default:
                    scalar = record;
            }
        });

        return createWindBuilder(uComp, vComp);
    }
    function buildGrid() {
        var builder = createBuilder(dataCurrent);

        var header = builder.header;
        var λ0 = header.lo1, φ0 = header.la1;  // the grid's origin (e.g., 0.0E, 90.0N)
        var Δλ = header.dx, Δφ = header.dy;    // distance between grid points (e.g., 2.5 deg lon, 2.5 deg lat)
        var ni = header.nx, nj = header.ny;    // number of grid points W-E and N-S (e.g., 144 x 73)
        var date = new Date(header.refTime);
        date.setHours(date.getHours() + header.forecastTime);

        var grid = [], p = 0;
        var isContinuous = Math.floor(ni * Δλ) >= 360;
        for (var j = 0; j < nj; j++) {
            var row = [];
            for (var i = 0; i < ni; i++ , p++) {
                row[i] = builder.data(p);
            }
            if (isContinuous) {
                row.push(row[0]);
            }
            grid[j] = row;
        }

        function interpolate(λ, φ) {
            var i = floorMod(λ - λ0, 360) / Δλ;  // calculate longitude index in wrapped range [0, 360)
            var j = (φ0 - φ) / Δφ;                 // calculate latitude index in direction +90 to -90

            var fi = Math.floor(i), ci = fi + 1;
            var fj = Math.floor(j), cj = fj + 1;

            var row;
            if ((row = grid[fj])) {
                var g00 = row[fi];
                var g10 = row[ci];
                if (isValue(g00) && isValue(g10) && (row = grid[cj])) {
                    var g01 = row[fi];
                    var g11 = row[ci];
                    if (isValue(g01) && isValue(g11)) {
                        return builder.interpolate(i - fi, j - fj, g00, g10, g01, g11);
                    }
                }
            }
            return null;
        }

        gridCurrent = {
            date: date,
            interpolate: interpolate
        };
    }
    function field(x, y) {
        var column = columnsCurrent[Math.round(x)];
        return column && column[Math.round(y)] || NULL_WIND_VECTOR;
    }
    field.release = function () {
        columnsCurrent = [];
    };
    field.randomize = function (o) {  // UNDONE: this method is terrible
        var x, y;
        var safetyNet = 0;
        do {
            x = Math.round(Math.floor(Math.random() * width));
            y = Math.round(Math.floor(Math.random() * height))
        } while (field(x, y)[2] === null && safetyNet++ < 30);
        o.x = x;
        o.y = y;
        return o;
    };
    function interpolateField(cb) {
        var projection = {};
        var columns = [];
        var x = 0;
        function interpolateColumn(x) {
            var column = [];
            for (var y = 0; y <= height; y += 2) {
                var coord = invert([x, y]);
                if (coord) {
                    var λ = coord[0], φ = coord[1];
                    if (isFinite(λ)) {
                        var wind = gridCurrent.interpolate(λ, φ);
                        if (wind) {
                            wind = distort(projection, λ, φ, x, y, velocityScaleCurrent, wind);
                            column[y + 1] = column[y] = wind;

                        }
                    }
                }
            }
            columns[x + 1] = columns[x] = column;
        }
        (function batchInterpolate() {
            var start = Date.now();
            while (x < width) {
                interpolateColumn(x);
                x += 2;
                if ((Date.now() - start) > 1000) { //MAX_TASK_TIME) {
                    timerInterpolate = setTimeout(batchInterpolate, 25);
                    return;
                }
            }
            // createField(columns, bounds, callback);
            columnsCurrent = columns;
            cb();
        })();

    }
    function animate() {
        var buckets = [];

        var particles = [];
        for (var i = 0; i < particleCount; i++) {
            particles.push(field.randomize({ age: Math.floor(Math.random() * MAX_PARTICLE_AGE) + 0 }));
        }

        function evolve() {
            buckets.forEach(function (bucket) { bucket.length = 0; });
            particles.forEach(function (particle) {
                if (particle.age > MAX_PARTICLE_AGE) {
                    field.randomize(particle).age = 0;
                }
                var x = particle.x;
                var y = particle.y;
                var v = field(x, y);  // vector at current position
                var m = v[2];
                if (m === null) {
                    particle.age = MAX_PARTICLE_AGE;  // particle has escaped the grid, never to return...
                }
                else {
                    var xt = x + v[0];
                    var yt = y + v[1];
                    if (field(xt, yt)[2] !== null) {
                        // Path from (x,y) to (xt,yt) is visible, so add this particle to the appropriate draw bucket.
                        particle.xt = xt;
                        particle.yt = yt;
                        var cInfo = _getColorParticle(v[2]);
                        if (cInfo.index > -1) {
                            if (!buckets[cInfo.index]) {
                                buckets[cInfo.index] = [];
                            }
                            buckets[cInfo.index].push(particle);
                            particle.c = cInfo.c;
                        }
                    }
                    else {
                        // Particle isn't visible, but it still moves through the field.
                        particle.x = xt;
                        particle.y = yt;
                    }
                }
                particle.age += 1;
            });
        }

        function draw() {
            // Fade existing particle trails.
            var prev = cxtParticle.globalCompositeOperation;
            cxtParticle.globalCompositeOperation = "destination-in";
            cxtParticle.fillStyle = fadeFillStyleCurrent;
            // cxtParticle.fillStyle = 'rgba(255, 0, 0, 0.99)';
            cxtParticle.fillRect(0, 0, width, height);
            cxtParticle.globalCompositeOperation = prev;

            
            cxtParticle.lineWidth = lineWidthCurrent;
            cxtParticle.strokeStyle = lineColorCurrent;

            // Draw new particle trails.
            buckets.forEach(function (bucket, i) {
                if (bucket.length > 0) {
                    cxtParticle.beginPath();
                    cxtParticle.strokeStyle = bucket[0].c;
                    bucket.forEach(function (particle) {
                        cxtParticle.moveTo(particle.x, particle.y);
                        cxtParticle.lineTo(particle.xt, particle.yt);
                        particle.x = particle.xt;
                        particle.y = particle.yt;
                    });
                    cxtParticle.stroke();
                }
            });
        }

        (function frame() {
            try {
                cancelAnimationFrame(timerFrame);
                timer = setTimeout(function () {
                    timerFrame = requestAnimationFrame(frame);
                    evolve();
                    draw();
                }, 1000 / FRAME_RATE);
            } catch (e) {
                console.error(e);
            }
        })();
    }
    function config(opts) {
        var particleConf = opts.particle;
        if (particleConf) {
            var canvasParticle = particleConf.canvas;
            if (canvasParticle) {
                width = canvasParticle.width;
                height = canvasParticle.height;
                cxtParticle = canvasParticle.getContext('2d');
                lineWidthCurrent = particleConf.lineWidth || PARTICLE_LINE_WIDTH;
                lineColorCurrent = particleConf.lineColor || LINE_COLOR;
            }
            // 粒子系数
            var densityRatio = particleConf.densityRatio;
            if (!(densityRatio >= 0 && densityRatio <= 1)) {
                densityRatio = 0.5;
            }
            paticleMultiplierCurrent = densityRatio;

            // 速度系数
            var particleVelocityScale = particleConf.speedRatio;
            if (!(particleVelocityScale >= 0 && particleVelocityScale <= 1)) {
                particleVelocityScale = 0.5;
            }
            velocityScaleCurrent = VELOCITY_SCALE_MIN + (VELOCITY_SCALE_MAX - VELOCITY_SCALE_MIN) * particleVelocityScale;

            // 线长系数
            var sizeRatio = particleConf.sizeRatio;
            if (!(sizeRatio >= 0 && sizeRatio <= 1)) {
                sizeRatio = 0.5;
            }
            var alpha = LINE_SIZE_MIN + (LINE_SIZE_MAX - LINE_SIZE_MIN) * sizeRatio;
            fadeFillStyleCurrent = 'rgba(0,0,0,'+alpha+')';
            // 对颜色值进行处理
            colorsForParticle = particleConf.colors;
        }
        var maskConf = opts.mask;
        if (maskConf) {
            var canvasMask = maskConf.canvas;
            if (canvasMask) {
                cxtMask = canvasMask.getContext('2d');
            }
            // 对颜色值进行处理
            colorsForMask = maskConf.colors.map(function(v) {
                var c = v[1] || 'rgba(0, 0, 0, 0)';
                var m = /rgba\((\d+),(\d+),(\d+),([\d.]+)\)/.exec(c.replace(/\s/g, ''));
                if (m) {
                    var color = [parseInt(m[1]), parseInt(m[2]), parseInt(m[3]), Math.floor(parseFloat(m[4]) * 255)];
                    return [v[0], color];
                }
            });
        }
        dataCurrent = opts.data || dataCurrent;    // 绑定数据
        project = opts.project;
        invert = opts.invert; 
    }
    function _getColor(v) {
        var c = [0,0,0,0];
        for (var i = 0, j = colorsForMask.length-1; i<j; i++) {
            var item = colorsForMask[i];
            var itemNext = colorsForMask[i + 1];
            if (item[0] <= v && v < itemNext[0]) {
                c = item[1];
                break;
            }
        }
        return c;
    }
    function _getColorParticle(v) {
        var index = -1;
        if (colorsForParticle) {
            for (var i = 0, j = colorsForParticle.length-1; i<j; i++) {
                var item = colorsForParticle[i];
                var itemNext = colorsForParticle[i + 1];
                if (item[0] <= v && v < itemNext[0]) {
                    c = item[1];
                    index = i;
                    break;
                }
            }
            
            return {
                c: c,
                index: index
            }
        } else {
            return {
                c: lineColorCurrent,
                index: 0
            }
        }
    }
    function drawMask() {
        if (cxtMask) {
            var timeStart = new Date();
            var imgData = cxtMask.getImageData(0, 0, width, height);
            var data = imgData.data;
            columnsCurrent.forEach(function(column, x) {
                column.forEach(function(v, y) {
                    var windSpeed = v[2];
                    var color = _getColor(windSpeed);
                    var i = (y * width + x) * 4;
                    data[i] = color[0];
                    data[i + 1] = color[1];
                    data[i + 2] = color[2];
                    data[i + 3] = 100;
                });
            });
            cxtMask.putImageData(imgData, 0, 0);
            _log('mask takes', new Date() - timeStart, 'ms');

            var t1 = new Date();
            getBlurWorker(function(e) {
                cxtMask.putImageData(e.data, 0, 0);
                _log('blur mask task '+(new Date() - t1)+' ms');
            }).postMessage({
                imageData: imgData,
                width: width,
                height: height,
                radius: 2,
                opacityScale: 1.5
            });
        }
    }
    
    function start(data) {
        stop();

        if (data) {
            dataCurrent = data;
        }
        if (!dataCurrent) {
            throw new Error('please set data');
        }

        if (cxtParticle) {
            var canvas = cxtParticle.canvas;
            width = canvas.width;
            height = canvas.height;
            cxtParticle.clearRect(0, 0, width, height);

            var particle_multiplier = PARTICLE_MULTIPLIER_MIN + (PARTICLE_MULTIPLIER_MAX - PARTICLE_MULTIPLIER_MIN) * paticleMultiplierCurrent;
            particleCount = width * height * particle_multiplier;
            if (isMobile()) {
                particleCount *= PARTICLE_REDUCTION;
            }
            particleCount = Math.round(particleCount);
            // particleCount = Math.min(6000, particleCount);
            _log('particleCount =', particleCount);
            _log('speed =', velocityScaleCurrent);
            _log('alpha =', fadeFillStyleCurrent);
        }
        if (cxtMask) {
            cxtMask.clearRect(0, 0, width, height);
        }

        var timeStart = new Date();
        // requestAnimationFrame(function() {
            buildGrid();
            interpolateField(function() {
                _log('deal data takes', new Date() - timeStart, 'ms');
                animate();
                drawMask();
            });
        // });
    }
    function stop() {        
        clearTimeout(timer);
        cancelAnimationFrame(timerFrame);
        clearTimeout(timerInterpolate);
        field.release();
    }
    function clean() {
        stop();
        if (cxtParticle) {
            cxtParticle.clearRect(0, 0, width, height);
        }
        if (cxtMask) {
            cxtMask.clearRect(0, 0, width, height);
        }
    }
    function setData(data) {
        dataCurrent = data;
    }
    function isReady() {
        return !!dataCurrent;
    }

    Windy.start = start;
    Windy.stop = stop;
    Windy.clean = clean;
    Windy.config = config;
    Windy.setData = setData;
    Windy.isReady = isReady;
    return Windy;
})();