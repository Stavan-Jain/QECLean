# Pinned eczoo_data snapshot

The catalog is built from a pinned snapshot of
[github.com/errorcorrectionzoo/eczoo_data](https://github.com/errorcorrectionzoo/eczoo_data).

**Pinned SHA:** `6f4da6d3284db17edb4100adfd38b73b0766c6d4`

## Refresh procedure

To update the catalog to a newer snapshot:

```bash
cd pipeline/cache
rm -rf eczoo_data
git clone --depth 1 https://github.com/errorcorrectionzoo/eczoo_data.git
cd eczoo_data && git rev-parse HEAD   # update this file with the new SHA
cd ../../..
python3 scripts/ingest_zoo.py          # regenerate catalog/zoo.yaml
```

After regeneration, re-score by spawning the `qec-prioritizer` agent.
