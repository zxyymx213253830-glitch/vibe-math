"""Keep retired pointer bytes outside the live acceptance filename pattern."""
from pathlib import Path
import hashlib,json,datetime
run=Path(__file__).resolve().parent; archive=run/'canonical-block-retired-export-manifests'
record=run/'canonical-retired-pointer-isolation.json'; assert not record.exists()
rows=[]
for name in ['CanonicalBlockSpectrum','CanonicalBlockShear']:
    src=archive/('acceptance-canonical-block-'+name+'.json')
    dst=archive/('retired-'+src.name)
    assert src.resolve().parent==archive.resolve() and not dst.exists()
    h=hashlib.sha256(src.read_bytes()).hexdigest(); src.rename(dst)
    assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
    rows.append(dict(old=src.name,new=dst.name,sha256=h))
record.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    reason='Global current acceptance verifier scans acceptance-*.json recursively, including archive folders. Retired files are data, not live pointers; preserve bytes with retired prefix.',files=rows),indent=2)+'\n',encoding='utf-8')
print('ISOLATED2_RETIRED_POINTERS; BYTES_UNCHANGED')
