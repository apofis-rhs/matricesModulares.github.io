// ================= Aritmética entera / modular (BigInt) =================
// a mod m, siempre en el rango 0..m-1, da positivo 

const mod = (a, m) => ((a % m) + m) % m;

// Máximo común divisor (Euclides)
function mcd(a, b) {
    a = a < 0n ? -a : a;
    b = b < 0n ? -b : b;
    while (b) [a, b] = [b, a % b];
    return a;
}

// Inverso de a mod m con Euclides extendido (null si no existe)
function inversoModular(a, m) {
    let [r0, r1] = [mod(a, m), m];
    let [s0, s1] = [1n, 0n];
    while (r1 !== 0n) {
        const q = r0 / r1;
        [r0, r1] = [r1, r0 - q * r1];
        [s0, s1] = [s1, s0 - q * s1];
    }
    return r0 === 1n ? mod(s0, m) : null;
}

// ================= Racionales exactos (fracciones) =================
// Representación: { n: numerador, d: denominador } (BigInt)
function Q(n, d = 1n) {
    if (d === 0n) throw new Error('Hay una división entre cero.');
    if (d < 0n) { n = -n; d = -d; }
    const g = mcd(n, d);
    return { n: n / g, d: d / g };
}

//implementan la suma, resta, multiplicación y división de fracciones mediante las fórmulas algebraicas estándar
const qSum  = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d);
const qRes  = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d);
const qMul  = (a, b) => Q(a.n * b.n, a.d * b.d);
const qDiv  = (a, b) => Q(a.n * b.d, a.d * b.n);
const qCero = a => a.n === 0n;
const qStr  = a => (a.d === 1n ? a.n.toString() : `${a.n}/${a.d}`);
const fmt   = v => (typeof v === 'bigint' ? v.toString() : qStr(v));
const CERO = Q(0n);

//onvierte lo que el usuario teclea en un objeto fracción Q
// Si el texto no es válido, devuelve null. Si el denominador es 0, lanza un error.

function parsearRacional(texto) {
    const t = texto.replace(/\s+/g, '');
    const partes = t.split('/');
    const token = /^([+-]?)(\d+)(?:\.(\d+))?$/;
    const aRacional = s => {
        const r = token.exec(s);
        if (!r) return null;
        const dec = r[3] || '';
        return Q(BigInt(r[1] + r[2] + dec), 10n ** BigInt(dec.length));
    };
    if (partes.length > 2) return null;
    const num = aRacional(partes[0]);
    if (!num) return null;
    if (partes.length === 1) return num;
    const den = aRacional(partes[1]);
    if (!den) return null;
    if (qCero(den)) throw new Error('El denominador no puede ser 0.');
    return qDiv(num, den);
}



// Racional -> residuo mod m  (a/b = a · b⁻¹ mod m)
// Si no existe el inverso, lanza un error
function residuo(q, m) {
    const inv = inversoModular(q.d, m);
    if (inv === null) {
        throw new Error(
            `la fracción ${qStr(q)} no existe mod ${m}, porque mcd(${q.d}, ${m}) = ${mcd(q.d, m)} ≠ 1.`
        );
    }
    return mod(mod(q.n, m) * inv, m);
}

// ================= Matrices (2x2 y 3x3) =================
// Crea una matriz n×n con la función f(i,j) que genera cada celda

const crear = (n, f) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => f(i, j)));


// Multiplicación de matrices cuadradas n×n de racionales exactos
function multiplicarQ(A, B) {
    const n = A.length;
    return crear(n, (i, j) => {
        let s = CERO;
        for (let k = 0; k < n; k++) s = qSum(s, qMul(A[i][k], B[k][j]));
        return s;
    });
}

// Multiplicación de matrices cuadradas n×n de enteros (BigInt)
function multiplicarEnteros(A, B) {
    const n = A.length;
    return crear(n, (i, j) => {
        let s = 0n;
        for (let k = 0; k < n; k++) s += A[i][k] * B[k][j];
        return s;
    });
}


// Determinante de matrices 2x2 y 3x3 de racionales exactos
function determinanteQ(A) {
    const m2 = (a, b, c, d) => qRes(qMul(a, d), qMul(b, c));
    if (A.length === 2) return m2(A[0][0], A[0][1], A[1][0], A[1][1]);
    const [[a, b, c], [d, e, f], [g, h, i]] = A;
    const t1 = qMul(a, m2(e, f, h, i));
    const t2 = qMul(b, m2(d, f, g, i));
    const t3 = qMul(c, m2(d, e, g, h));
    return qSum(qRes(t1, t2), t3);
}


// Adjunta de matrices 2x2 y 3x3 de racionales exactos
function adjuntaQ(A) {
    const neg = x => qRes(CERO, x);
    const m2 = (a, b, c, d) => qRes(qMul(a, d), qMul(b, c));
    if (A.length === 2) {
        return [[A[1][1], neg(A[0][1])], [neg(A[1][0]), A[0][0]]];
    }
    const [[a, b, c], [d, e, f], [g, h, i]] = A;
    // Transpuesta de la matriz de cofactores
    return [
        [m2(e, f, h, i),      neg(m2(b, c, h, i)),  m2(b, c, e, f)],
        [neg(m2(d, f, g, i)), m2(a, c, g, i),       neg(m2(a, c, d, f))],
        [m2(d, e, g, h),      neg(m2(a, b, g, h)),  m2(a, b, d, e)]
    ];
}

// ================= Interfaz =================
const $ = id => document.getElementById(id);
const pantallas = ['pantalla-1', 'pantalla-2', 'pantalla-resultado'];
let estado = { n: 3, m: 26n, op: 'multiplicacion' };

function mostrar(id) {
    pantallas.forEach(p => {
        $(p).classList.toggle('activa', p === id);
        $(p).classList.toggle('oculta', p !== id);
    });
}

function crearGridEntrada(contenedor, n) {
    contenedor.innerHTML = '';
    contenedor.style.gridTemplateColumns = `repeat(${n}, auto)`;
    for (let i = 0; i < n * n; i++) {
        const inp = document.createElement('input');
        inp.type = 'text';
        inp.inputMode = 'text';
        inp.value = '0';
        inp.addEventListener('focus', () => inp.select());
        contenedor.appendChild(inp);
    }
}

function pintarMatriz(contenedor, M) {
    contenedor.innerHTML = '';
    contenedor.style.gridTemplateColumns = `repeat(${M.length}, auto)`;
    M.flat().forEach(v => {
        const d = document.createElement('div');
        d.className = 'celda';
        d.textContent = fmt(v);
        d.title = fmt(v);
        contenedor.appendChild(d);
    });
}

// Lee la matriz como racionales (exactos) y también como residuos mod m
function leerMatriz(contenedor, n, nombre, m) {
    const inputs = contenedor.querySelectorAll('input');
    const MQ = [], MR = [];
    for (let i = 0; i < n; i++) {
        const filaQ = [], filaR = [];
        for (let j = 0; j < n; j++) {
            const pos = `Matriz ${nombre}, posición (${i + 1},${j + 1})`;
            const txt = inputs[i * n + j].value.trim();
            let q;
            try {
                q = parsearRacional(txt);
            } catch (e) {
                throw new Error(`${pos}: ${e.message}`);
            }
            if (!q) throw new Error(`${pos}: escribe un entero, una fracción (3/4) o un decimal (0.5).`);
            try {
                filaR.push(residuo(q, m));
            } catch (e) {
                throw new Error(`${pos}: ${e.message}`);
            }
            filaQ.push(q);
        }
        MQ.push(filaQ);
        MR.push(filaR);
    }
    return { Q: MQ, R: MR };
}

// --- Pantalla 1 -> 2
$('btn-siguiente').addEventListener('click', () => {
    const txtMod = $('modulo').value.trim();
    if (!/^\d+$/.test(txtMod) || BigInt(txtMod) < 2n) {
        $('error-1').textContent = 'El módulo debe ser un entero mayor o igual a 2.';
        return;
    }
    $('error-1').textContent = '';

    const nuevoN = parseInt($('tamano').value, 10);
    const cambio = nuevoN !== estado.n || !$('grid-a').children.length;
    estado.n = nuevoN;
    estado.m = BigInt(txtMod);
    estado.op = $('operacion').value;

    if (cambio) {
        crearGridEntrada($('grid-a'), estado.n);
        crearGridEntrada($('grid-b'), estado.n);
    }
    $('bloque-b').classList.toggle('oculta', estado.op !== 'multiplicacion');
    $('error-2').textContent = '';
    mostrar('pantalla-2');
});

$('btn-volver').addEventListener('click', () => mostrar('pantalla-1'));

// --- Cálculo
$('btn-calcular').addEventListener('click', () => {
    try {
        const { n, m, op } = estado;
        const A = leerMatriz($('grid-a'), n, 'A', m);

        if (op === 'multiplicacion') {
            const B = leerMatriz($('grid-b'), n, 'B', m);
            const crudo = multiplicarQ(A.Q, B.Q);
            const final = multiplicarEnteros(A.R, B.R).map(f => f.map(x => mod(x, m)));
            const hayFracciones = [...A.Q.flat(), ...B.Q.flat()].some(q => q.d !== 1n);
            mostrarResultado({
                desc: `A × B  (módulo ${m})`,
                etiquetaCrudo: 'A × B (sin módulo)',
                etiquetaMod: `A × B mod ${m}`,
                crudo,
                final,
                nota: hayFracciones
                    ? `Cada fracción a/b se convierte a a · b⁻¹ mod ${m} antes de multiplicar. ` +
                      'Los negativos se llevan al rango 0 a m−1.'
                    : 'Cada celda es la suma de productos fila × columna, reducida mod m (los negativos se llevan al rango 0 a m−1).'
            });
        } else {
            mostrarResultado(calcularInversa(A, m));
        }
    } catch (e) {
        $('error-2').textContent = e.message;
    }
});

// --- Cálculo de la inversa mod m
function calcularInversa(A, m) {
    // PASO 1: comprobar que la matriz tiene inversa mod m
    const detQ = determinanteQ(A.Q);
    const detMod = residuo(detQ, m);
    const g = mcd(detMod, m); // si detMod = 0, mcd(0, m) = m
    if (g !== 1n) {
        throw new Error(
            `La matriz NO tiene inversa mod ${m}: det(A) = ${qStr(detQ)} ≡ ${detMod} (mod ${m}) ` +
            `y mcd(${detMod}, ${m}) = ${g}, que es distinto de 1.`
        );
    }

    // PASO 2: calcular la inversa. Exacta (en fracciones) y reducida mod m
    const invQ = adjuntaQ(A.Q).map(f => f.map(x => qDiv(x, detQ)));
    const final = invQ.map(f => f.map(x => residuo(x, m)));

    // PASO 3: verificar A · A⁻¹ ≡ I (mod m)
    const prod = multiplicarEnteros(A.R, final).map(f => f.map(x => mod(x, m)));
    const esIdentidad = prod.every((f, i) => f.every((x, j) => x === (i === j ? 1n : 0n)));
    if (!esIdentidad) throw new Error('Error interno: la verificación A · A⁻¹ = I falló.');

    return {
        desc: `Inversa de A  (módulo ${m})`,
        etiquetaCrudo: 'A⁻¹ exacta (sin módulo)',
        etiquetaMod: `A⁻¹ mod ${m}`,
        crudo: invQ,
        final,
        nota: `✔ Sí tiene inversa: det(A) = ${qStr(detQ)} ≡ ${detMod} (mod ${m}), mcd(${detMod}, ${m}) = 1. ` +
              `Verificado: A · A⁻¹ ≡ I (mod ${m}).`
    };
}

function mostrarResultado(r) {
    $('descripcion-resultado').textContent = r.desc;
    $('etiqueta-crudo').textContent = r.etiquetaCrudo;
    $('etiqueta-mod').textContent = r.etiquetaMod;
    pintarMatriz($('grid-crudo'), r.crudo);
    pintarMatriz($('grid-resultado'), r.final);
    $('nota-resultado').textContent = r.nota;
    mostrar('pantalla-resultado');
}

// --- Navegación final
$('btn-editar').addEventListener('click', () => mostrar('pantalla-2'));
$('btn-reiniciar').addEventListener('click', () => {
    $('grid-a').innerHTML = '';
    $('grid-b').innerHTML = '';
    mostrar('pantalla-1');
});
