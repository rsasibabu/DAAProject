const $ = (id) => document.getElementById(id);
const stage = $("stage"), list = $("stepList"), curCard = document.querySelector(".current");

const INFO = {
  bubble:    { t: "O(n²)",      s: "O(1)" },
  selection: { t: "O(n²)",      s: "O(1)" },
  insertion: { t: "O(n²)",      s: "O(1)" },
  shell:     { t: "O(n²)",      s: "O(1)" },
  merge:     { t: "O(n log n)", s: "O(n)" },
  quick:     { t: "O(n log n)", s: "O(log n)" },
  heap:      { t: "O(n log n)", s: "O(1)" },
};

const GAP = 8, PAD_X = 24;

let initial = [], steps = [], pos = -1, timer = null;
let bars = [], labels = [], lay = {}, currentFrame = null;

/* ---------- Step generators (every bar keeps a stable id) ---------- */
function build(algo, input) {
  const a = [...input];
  const ids = a.map((_, i) => i);
  const out = [];
  const sorted = new Set();
  const n = a.length;

  const push = (cmp, title, desc, piv = [], range = null) =>
    out.push({ ids: [...ids], cmp, piv, range, sorted: [...sorted], title, desc });

  const swap = (i, j) => {
    [a[i], a[j]] = [a[j], a[i]];
    [ids[i], ids[j]] = [ids[j], ids[i]];
  };

  /* Bubble */
  if (algo === "bubble") {
    for (let i = 0; i < n - 1; i++) {
      for (let j = 0; j < n - i - 1; j++) {
        push([j, j + 1], `Compare ${a[j]} and ${a[j + 1]}`, `Check whether ${a[j]} is greater than ${a[j + 1]}.`);
        if (a[j] > a[j + 1]) {
          const l = a[j], r = a[j + 1];
          swap(j, j + 1);
          push([j, j + 1], `Swap ${l} and ${r}`, "The left value is larger, so swap these neighbouring values.");
        } else {
          push([j, j + 1], "Keep the values in place", "These neighbours are already in ascending order.");
        }
      }
      sorted.add(n - i - 1);
      push([], `${a[n - i - 1]} reaches its final position`, "The largest remaining value has reached the right end.");
    }
  }

  /* Selection */
  if (algo === "selection") {
    for (let i = 0; i < n - 1; i++) {
      let min = i;
      for (let j = i + 1; j < n; j++) {
        push([j, min], `Compare ${a[j]} and ${a[min]}`, `Is ${a[j]} smaller than the current minimum ${a[min]}?`);
        if (a[j] < a[min]) min = j;
      }
      if (min !== i) {
        const x = a[i], y = a[min];
        swap(i, min);
        push([i, min], `Swap ${x} and ${y}`, "Move the smallest remaining value to the front of the unsorted part.");
      }
      sorted.add(i);
      push([], `${a[i]} reaches its final position`, "The smallest remaining value is now fixed.");
    }
  }

  /* Insertion */
  if (algo === "insertion") {
    sorted.add(0);
    for (let i = 1; i < n; i++) {
      let j = i;
      while (j > 0) {
        push([j - 1, j], `Compare ${a[j - 1]} and ${a[j]}`, `Check whether ${a[j - 1]} is greater than ${a[j]}.`);
        if (a[j - 1] > a[j]) {
          const x = a[j - 1], y = a[j];
          swap(j - 1, j);
          push([j - 1, j], `Shift ${y} left past ${x}`, "The left value is larger, so move the new value one step left.");
          j--;
        } else break;
      }
      sorted.add(i);
      push([], `Insert value at index ${j}`, "The sorted prefix has grown by one element.");
    }
  }

  /* Shell */
  if (algo === "shell") {
    for (let gap = n >> 1; gap > 0; gap >>= 1) {
      push([], `Gap = ${gap}`, `Insertion-sort the elements that are ${gap} positions apart.`);
      for (let i = gap; i < n; i++) {
        let j = i;
        while (j >= gap) {
          push([j - gap, j], `Compare ${a[j - gap]} and ${a[j]}`, `They are ${gap} apart. Is ${a[j - gap]} greater than ${a[j]}?`);
          if (a[j - gap] > a[j]) {
            const x = a[j - gap], y = a[j];
            swap(j - gap, j);
            push([j - gap, j], `Swap ${x} and ${y}`, "Out of order across the gap, so swap them.");
            j -= gap;
          } else break;
        }
      }
    }
  }

  /* Merge (in-place: the smaller right value slides into position) */
  if (algo === "merge") {
    const merge = (l, m, r) => {
      let i = l, j = m + 1, mid = m;
      push([], `Merge indices ${l} to ${r}`, "Combine two sorted halves into one sorted run.", [], [l, r]);
      while (i <= mid && j <= r) {
        push([i, j], `Compare ${a[i]} and ${a[j]}`, `Which is smaller, ${a[i]} or ${a[j]}?`, [], [l, r]);
        if (a[i] <= a[j]) {
          i++;
        } else {
          const v = a[j], id = ids[j];
          for (let k = j; k > i; k--) { a[k] = a[k - 1]; ids[k] = ids[k - 1]; }
          a[i] = v; ids[i] = id;
          push([i], `Insert ${v} at index ${i}`, "The right value is smaller, so it slides in front of the left run.", [], [l, r]);
          i++; mid++; j++;
        }
      }
      push([], `Indices ${l} to ${r} merged`, "This run is now sorted.", [], [l, r]);
    };
    const ms = (l, r) => {
      if (l >= r) return;
      const m = (l + r) >> 1;
      ms(l, m);
      ms(m + 1, r);
      merge(l, m, r);
    };
    ms(0, n - 1);
  }

  /* Quick (Lomuto, last element as pivot) */
  if (algo === "quick") {
    const qs = (lo, hi) => {
      if (lo > hi) return;
      if (lo === hi) {
        sorted.add(lo);
        push([], `${a[lo]} is in place`, "A single element is already sorted.", [], [lo, hi]);
        return;
      }
      const p = a[hi];
      push([], `Choose pivot ${p}`, "The last element of the range becomes the pivot.", [hi], [lo, hi]);
      let i = lo - 1;
      for (let j = lo; j < hi; j++) {
        push([j], `Compare ${a[j]} with pivot ${p}`, `Is ${a[j]} smaller than ${p}?`, [hi], [lo, hi]);
        if (a[j] < p) {
          i++;
          if (i !== j) {
            const x = a[i], y = a[j];
            swap(i, j);
            push([i, j], `Swap ${x} and ${y}`, "Move the smaller value into the left partition.", [hi], [lo, hi]);
          }
        }
      }
      if (i + 1 !== hi) swap(i + 1, hi);
      sorted.add(i + 1);
      push([], `Pivot ${p} placed at index ${i + 1}`, "Everything on the left is smaller, everything on the right is larger.", [], [lo, hi]);
      qs(lo, i);
      qs(i + 2, hi);
    };
    qs(0, n - 1);
  }

  /* Heap */
  if (algo === "heap") {
    const sift = (size, root) => {
      while (true) {
        let big = root;
        const L = 2 * root + 1, R = L + 1;
        if (L < size) {
          push([L, big], `Compare ${a[L]} and ${a[big]}`, "Check the left child against the current largest.", [], [0, size - 1]);
          if (a[L] > a[big]) big = L;
        }
        if (R < size) {
          push([R, big], `Compare ${a[R]} and ${a[big]}`, "Check the right child against the current largest.", [], [0, size - 1]);
          if (a[R] > a[big]) big = R;
        }
        if (big === root) break;
        const x = a[root], y = a[big];
        swap(root, big);
        push([root, big], `Swap ${x} and ${y}`, "Move the larger child up to restore the max-heap.", [], [0, size - 1]);
        root = big;
      }
    };
    push([], "Build a max-heap", "Rearrange the array so every parent is larger than its children.");
    for (let i = (n >> 1) - 1; i >= 0; i--) sift(n, i);
    for (let end = n - 1; end > 0; end--) {
      const x = a[0], y = a[end];
      swap(0, end);
      sorted.add(end);
      push([0, end], `Move ${x} to the end`, `The root is the largest value, so swap it with ${y} and fix it in place.`);
      sift(end, 0);
    }
  }

  for (let i = 0; i < n; i++) sorted.add(i);
  push([], "Sorting complete", "Every element is now in its final position.");
  return out;
}

/* ---------- Stage: persistent bars that slide ---------- */
function buildStage() {
  stage.innerHTML = "";
  const max = Math.max(...initial, 1);
  bars = initial.map((v) => {
    const b = document.createElement("div");
    b.className = "bar";
    b.innerHTML = `<span>${v}</span>`;
    b.dataset.v = Math.max(v, 0) / max;
    stage.appendChild(b);
    return b;
  });
  labels = initial.map((_, i) => {
    const l = document.createElement("span");
    l.className = "idx";
    l.textContent = i;
    stage.appendChild(l);
    return l;
  });
  layout();
}

function layout() {
  const n = initial.length;
  const W = stage.clientWidth, H = stage.clientHeight;
  const bw = Math.min(48, (W - PAD_X * 2 - GAP * (n - 1)) / n);
  const total = n * bw + (n - 1) * GAP;
  const avail = Math.min(H * 0.5, 230);          // smaller bars
  const base = (H - (avail + 26)) / 2 + 26;      // centre the whole group
  lay = { bw, x0: (W - total) / 2 };

  bars.forEach((b) => {
    b.style.width = bw + "px";
    b.style.height = Math.round(avail * (0.25 + 0.75 * b.dataset.v)) + "px";
    b.style.bottom = base + "px";
  });
  labels.forEach((l, i) => {
    l.style.width = bw + "px";
    l.style.bottom = base - 24 + "px";
    l.style.transform = `translate3d(${lay.x0 + i * (bw + GAP)}px,0,0)`;
  });
}

function applyFrame(f) {
  currentFrame = f;
  f.ids.forEach((id, p) => {
    const b = bars[id];
    const isCmp = f.cmp.includes(p);
    const isPiv = !isCmp && f.piv.includes(p);
    const isSorted = !isCmp && !isPiv && f.sorted.includes(p);
    const outside = f.range && (p < f.range[0] || p > f.range[1]);
    b.style.setProperty("--x", lay.x0 + p * (lay.bw + GAP) + "px");
    b.classList.toggle("checking", isCmp);
    b.classList.toggle("pivot", isPiv);
    b.classList.toggle("sorted", isSorted);
    b.classList.toggle("dim", !!outside && !isSorted && !isCmp && !isPiv);
  });
}

function snap(fn) {
  stage.classList.add("no-anim");
  fn();
  void stage.offsetWidth;
  stage.classList.remove("no-anim");
}

function setSpeed() {
  const d = 1100 - $("speed").value * 100;
  stage.style.setProperty("--dur", Math.max(90, d * 0.85) + "ms");
  return d;
}

/* ---------- Showing a step ---------- */
function show(idx) {
  pos = idx;
  const f = steps[idx];
  if (!f) return;
  setSpeed();
  applyFrame(f);

  $("curTitle").textContent = f.title;
  $("curDesc").textContent = f.desc;
  curCard.classList.remove("fade"); void curCard.offsetWidth; curCard.classList.add("fade");

  $("stepText").textContent = `Step ${idx + 1} / ${steps.length}`;
  list.querySelector(".active")?.classList.remove("active");
  const li = list.children[idx];
  if (li) {
    li.classList.add("active");
    li.scrollIntoView({ block: "center", behavior: "smooth" });
  }
}

function buildList() {
  list.innerHTML = steps.map((s, i) =>
    `<li data-i="${i}"><em>#${i + 1}</em><b>${s.title}</b><p>${s.desc}</p></li>`).join("");
}

/* ---------- Controls ---------- */
function parseInput() {
  const nums = $("input").value.split(/[\s,]+/).filter(Boolean).map(Number);
  if (!nums.length || nums.length > 20 || nums.some((n) => !Number.isInteger(n))) {
    alert("Please enter 1 to 20 integers separated by commas or spaces.");
    return null;
  }
  return nums;
}

function prepare() {
  stop();
  const nums = parseInput();
  if (!nums) return;
  const algo = $("algo").value;
  initial = nums;
  steps = build(algo, initial);
  pos = -1;

  $("count").textContent = `${initial.length} elements`;
  $("time-c").textContent = INFO[algo].t;
  $("space-c").textContent = INFO[algo].s;
  $("stepText").textContent = `Step 0 / ${steps.length}`;
  $("curTitle").textContent = "Press Start to begin";
  $("curDesc").textContent = "The visualizer will explain every comparison and swap here.";
  buildList();
  buildStage();
  snap(() => applyFrame({ ids: initial.map((_, i) => i), cmp: [], piv: [], range: null, sorted: [] }));
}

function tick() {
  if (pos + 1 >= steps.length) return stop();
  show(pos + 1);
  timer = setTimeout(tick, setSpeed());
}

function start() {
  if (timer) return;
  if (pos + 1 >= steps.length) prepare();
  $("start").disabled = true;
  tick();
}

function stop() {
  clearTimeout(timer);
  timer = null;
  $("start").disabled = false;
}

$("apply").onclick = prepare;
$("algo").onchange = prepare;
$("start").onclick = start;
$("pause").onclick = stop;
$("reset").onclick = prepare;
$("speed").oninput = setSpeed;
list.onclick = (e) => {
  const li = e.target.closest("li");
  if (li) { stop(); show(+li.dataset.i); }
};
window.addEventListener("resize", () => snap(() => { layout(); if (currentFrame) applyFrame(currentFrame); }));

prepare();