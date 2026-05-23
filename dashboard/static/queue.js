// Client-side sort/filter for the queue page.

(function () {
  const data = window.queueData || [];
  const tbody = document.getElementById('queue-tbody');
  const search = document.getElementById('search');
  const rowCount = document.getElementById('row-count');
  const chips = document.querySelectorAll('.chip');
  const headers = document.querySelectorAll('th.sortable');

  let activeTrackFilter = 'all';
  let activeStatusFilter = null;
  let searchTerm = '';
  let sortKey = 'composite';
  let sortDir = -1; // -1 desc, 1 asc

  function escapeHtml(s) {
    return String(s || '')
      .replace(/&/g, '&amp;').replace(/</g, '&lt;')
      .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }

  function axisBars(axes) {
    const axisOrder = ['reuse', 'canonicality', 'hardware', 'tractability', 'prerequisites', 'effort'];
    const labels = { reuse: 'Reuse', canonicality: 'Canon', hardware: 'Hardware',
                     tractability: 'Tract', prerequisites: 'Prereq', effort: 'Effort' };
    return '<span class="axes-row">' + axisOrder.map(a => {
      const v = axes[a] || 0;
      return `<span class="axis-bar" title="${labels[a]}: ${v}/10"><span class="fill-${v}"></span></span>`;
    }).join('') + '</span>';
  }

  function rowHtml(e, rank) {
    const params = e.params ? ` <code>${escapeHtml(e.params)}</code>` : '';
    const rationale = (e.rationale || '').slice(0, 180) + (e.rationale && e.rationale.length > 180 ? '…' : '');
    return `<tr data-track="${e.track}" data-status="${e.status}">
      <td class="num">${rank}</td>
      <td class="code-id"><a href="../code/${e.slug}/index.html">${escapeHtml(e.code_id)}</a></td>
      <td>${escapeHtml(e.name)}${params}</td>
      <td class="num"><strong>${e.composite.toFixed(2)}</strong></td>
      <td class="num">${e.axes.reuse ?? ''}</td>
      <td class="num">${e.axes.canonicality ?? ''}</td>
      <td class="num">${e.axes.hardware ?? ''}</td>
      <td class="num">${e.axes.tractability ?? ''}</td>
      <td class="num">${e.axes.prerequisites ?? ''}</td>
      <td class="num">${e.axes.effort ?? ''}</td>
      <td><span class="badge ${e.track}">${e.track}</span></td>
      <td><span class="badge ${e.status}">${e.status.replace(/_/g, ' ')}</span></td>
      <td class="rationale">${escapeHtml(rationale)}</td>
    </tr>`;
  }

  function filterAndSort() {
    let filtered = data.filter(e => {
      if (activeTrackFilter !== 'all' && e.track !== activeTrackFilter) return false;
      if (activeStatusFilter && e.status !== activeStatusFilter) return false;
      if (searchTerm) {
        const t = searchTerm.toLowerCase();
        if (!e.code_id.toLowerCase().includes(t)
            && !e.name.toLowerCase().includes(t)
            && !(e.rationale || '').toLowerCase().includes(t)) {
          return false;
        }
      }
      return true;
    });

    filtered.sort((a, b) => {
      let av, bv;
      if (sortKey === 'composite') { av = a.composite; bv = b.composite; }
      else if (['reuse','canonicality','hardware','tractability','prerequisites','effort'].includes(sortKey)) {
        av = a.axes[sortKey] || 0;
        bv = b.axes[sortKey] || 0;
      } else if (sortKey === 'rank') {
        av = a.composite; bv = b.composite; // rank = composite desc
        return -sortDir * (av - bv);
      } else {
        av = String(a[sortKey] || ''); bv = String(b[sortKey] || '');
        return sortDir * av.localeCompare(bv);
      }
      return sortDir * (av - bv);
    });

    tbody.innerHTML = filtered.map((e, i) => rowHtml(e, i + 1)).join('');
    rowCount.textContent = `${filtered.length} of ${data.length} codes`;
  }

  search.addEventListener('input', e => { searchTerm = e.target.value; filterAndSort(); });

  chips.forEach(chip => {
    chip.addEventListener('click', () => {
      const track = chip.dataset.track;
      const status = chip.dataset.status;
      if (track) {
        chips.forEach(c => { if (c.dataset.track) c.classList.remove('active'); });
        chip.classList.add('active');
        activeTrackFilter = track;
        activeStatusFilter = null;
        chips.forEach(c => { if (c.dataset.status) c.classList.remove('active'); });
      } else if (status) {
        // Toggle
        if (activeStatusFilter === status) {
          activeStatusFilter = null;
          chip.classList.remove('active');
        } else {
          activeStatusFilter = status;
          chips.forEach(c => { if (c.dataset.status) c.classList.remove('active'); });
          chip.classList.add('active');
        }
      }
      filterAndSort();
    });
  });

  headers.forEach(h => {
    h.addEventListener('click', () => {
      const newKey = h.dataset.sort;
      if (sortKey === newKey) sortDir = -sortDir;
      else { sortKey = newKey; sortDir = (newKey === 'code_id' || newKey === 'name') ? 1 : -1; }
      headers.forEach(other => other.classList.remove('sorted-asc', 'sorted-desc'));
      h.classList.add(sortDir < 0 ? 'sorted-desc' : 'sorted-asc');
      filterAndSort();
    });
  });

  filterAndSort();
})();
