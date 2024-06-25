# docker build -t smtcoq/smtcoq-capi:latest .
# docker run -it smtcoq/smtcoq-capi:latest
# docker push smtcoq/smtcoq-capi:latest
# docker run -w /home/coq/smtcoq -v "$(pwd):/home/coq/smtcoq" -it smtcoq/smtcoq-capi:latest


############################################################
# Dockerfile to build SMTCoq C API
############################################################

FROM coqorg/coq:8.19.2-ocaml-4.09.1-flambda

USER coq
WORKDIR /home/coq

################### INSTALL SMTCOQ C API ###################
RUN git clone https://github.com/smtcoq/smtcoq.git && \
    cd smtcoq && \
    git checkout extrapi-coq-8.19 && \
    opam install -y ./coq-smtcoq-extrapi.opam && \
    cd .. && \
    rm -rf smtcoq
