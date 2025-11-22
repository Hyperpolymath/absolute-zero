# Dockerfile for Absolute Zero
#
# Complete environment for CNO proof verification and interpreter execution
#
# Build: docker build -t absolute-zero .
# Run:   docker run --rm absolute-zero just verify-all
#
# Author: Jonathan D. A. Jewell
# Project: Absolute Zero

FROM fedora:39

LABEL maintainer="jonathan@metadatastician.art"
LABEL description="Absolute Zero - Formal Verification of Certified Null Operations"
LABEL version="0.1.0"

# ============================================================================
# Install System Dependencies
# ============================================================================

RUN dnf update -y && \
    dnf install -y \
    # Build tools
    gcc \
    make \
    cmake \
    git \
    curl \
    wget \
    # Proof assistants
    coq \
    z3 \
    # Programming languages
    nodejs \
    npm \
    python3 \
    python3-pip \
    opam \
    # Utilities
    just \
    && dnf clean all

# ============================================================================
# Install ReScript
# ============================================================================

RUN npm install -g rescript@11.1

# ============================================================================
# Install Lean 4 (optional)
# ============================================================================

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# ============================================================================
# Set up working directory
# ============================================================================

WORKDIR /absolute-zero

# ============================================================================
# Copy project files
# ============================================================================

# Copy package files first for better caching
COPY package.json package-lock.json* ./
RUN npm install || true

# Copy rest of project
COPY . .

# ============================================================================
# Build everything
# ============================================================================

# Build TypeScript
RUN npm run build || echo "TypeScript build not configured"

# Build Coq proofs
RUN cd proofs/coq/common && coqc CNO.v
RUN cd proofs/coq/malbolge && coqc -R ../common CNO MalbolgeCore.v

# Make scripts executable
RUN chmod +x proofs/z3/verify.sh
RUN chmod +x interpreters/brainfuck/brainfuck.py
RUN chmod +x interpreters/whitespace/whitespace.py

# ============================================================================
# Default command: verify all proofs
# ============================================================================

CMD ["just", "verify-all"]

# ============================================================================
# Usage Examples
# ============================================================================

# Build image:
#   docker build -t absolute-zero .
#
# Run verification:
#   docker run --rm absolute-zero just verify-all
#
# Run tests:
#   docker run --rm absolute-zero just test-all
#
# Interactive shell:
#   docker run --rm -it absolute-zero /bin/bash
#
# Run specific verification:
#   docker run --rm absolute-zero just verify-coq
#   docker run --rm absolute-zero just verify-z3
#
# Run interpreter tests:
#   docker run --rm absolute-zero python3 interpreters/brainfuck/brainfuck.py
