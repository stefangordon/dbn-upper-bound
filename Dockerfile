# Tested Linux reproduction image. The digest fixes the base filesystem.
FROM ubuntu:24.04@sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 python3-venv gcc libc6-dev libflint-dev libgmp-dev libmpfr-dev
RUN python3 -m venv /opt/dbn-venv
ENV PATH="/opt/dbn-venv/bin:$PATH"
ENV PYTHONDONTWRITEBYTECODE=1
COPY requirements.txt /opt/dbn-requirements.txt
RUN pip install --no-cache-dir -r /opt/dbn-requirements.txt

WORKDIR /paper
COPY . /paper
ENTRYPOINT ["python", "verify.py"]
CMD ["--regenerate"]
