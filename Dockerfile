# The scorer builds this on linux/amd64 and runs it with no network. The
# digest is the image we labeled every commit in: its Python and SQLite
# decide which sqlglot tests run, so keep it if your image runs them.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90

COPY requirements.lock /app/requirements.lock
RUN pip install --no-cache-dir -r /app/requirements.lock && \
    python -c "import os, shutil, tarfile, urllib.request; url = 'https://github.com/tobymao/sqlglot/archive/eb11aec4be8cb2122afe713a4816662c3f0fb2fa.tar.gz'; urllib.request.urlretrieve(url, '/tmp/sg.tgz'); tarfile.open('/tmp/sg.tgz').extractall('/tmp', filter='tar'); shutil.move('/tmp/sqlglot-eb11aec4be8cb2122afe713a4816662c3f0fb2fa', '/app/sqlglot'); os.remove('/tmp/sg.tgz')" && \
    chmod -R a+rX /app

COPY blast_map.json.gz selector.py /app/
RUN chmod a+r /app/blast_map.json.gz /app/selector.py

ENV PYTHONPATH=/app/sqlglot SKIP_INTEGRATION=0 PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
CMD ["python", "/app/selector.py"]
