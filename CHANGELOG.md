# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.5.3] - 2025-12-24

### Added
- Added method `OwnedTemplate::compile_compact` to coalesce adjacent text spans caused by the presence of escaped brackets like `{{` and `}}`.

## [0.5.2] - 2025-12-08

### Added
- Added method `TemplateSpans::offset` to return the current byte offset inside the template string.
- Added `Placeholder` manifest implementation, which ignores the expression type and writes a placeholder value in its place.
- Added `ManifestMut::finalize_state` to run custom cleanup code after rendering is complete.
