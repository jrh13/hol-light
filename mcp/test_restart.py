"""Focused tests for config-aware HOL restarts."""

import asyncio
import json
import os
import time

import pytest

import server


class FakeProcess:
    def __init__(self, pid=1234):
        self.pid = pid
        self.alive = True

    def poll(self):
        return None if self.alive else 0

    def kill(self):
        self.alive = False

    def wait(self, timeout=None):
        self.alive = False
        return 0


def make_config(tmp_path, checkpoint="base", **values):
    raw = {
        "checkpoint": checkpoint,
        "timeout": values.pop("timeout", 600),
        "max_output_chars": values.pop("max_output_chars", 4000),
        "checkpoint_recipes": values.pop("checkpoint_recipes", {
            "base": {"include_dirs": [], "loads": []},
        }),
    }
    raw.update(values)
    return server._effective_config(raw, str(tmp_path / "hol-mcp.toml"))


@pytest.fixture(autouse=True)
def restore_runtime():
    runtime = server._runtime_config
    checkpoint_name = server.CHECKPOINT_NAME
    startup_mode = server._startup_mode
    checkpoint_active = server._checkpoint_active
    checkpoint_error = server._checkpoint_error
    checkpoint_fingerprint = server._checkpoint_fingerprint
    restart_required = server._restart_required
    restart_error = server._restart_error
    proc = server._proc
    yield
    server._apply_runtime_config(runtime)
    server.CHECKPOINT_NAME = checkpoint_name
    server._startup_mode = startup_mode
    server._checkpoint_active = checkpoint_active
    server._checkpoint_error = checkpoint_error
    server._checkpoint_fingerprint = checkpoint_fingerprint
    server._restart_required = restart_required
    server._restart_error = restart_error
    server._proc = proc


def test_config_reload_and_one_shot_override(monkeypatch, tmp_path):
    config = make_config(
        tmp_path,
        checkpoint="gcm",
        timeout=321,
        max_output_chars=987,
        checkpoint_recipes={
            "base": {"include_dirs": [], "loads": []},
            "gcm": {"include_dirs": [], "loads": []},
        },
    )
    selected = []
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(
        server, "_restart_process",
        lambda checkpoint: (selected.append(checkpoint) is None, None),
    )
    monkeypatch.setattr(server, "_proc", FakeProcess())

    overridden = server._hol_restart_sync("base", False, lambda *_: None)
    configured = server._hol_restart_sync(None, False, lambda *_: None)

    assert overridden["success"] is True
    assert overridden["checkpoint"] == "base"
    assert overridden["configured_checkpoint"] == "gcm"
    assert overridden["checkpoint_overridden"] is True
    assert configured["checkpoint"] == "gcm"
    assert configured["checkpoint_overridden"] is False
    assert selected == ["base", "gcm"]
    assert server.TIMEOUT == 321
    assert server.MAX_OUTPUT_CHARS == 987


def test_rebuild_requires_recipe(monkeypatch, tmp_path):
    config = make_config(tmp_path, checkpoint="unbuilt", checkpoint_recipes={})
    proc = FakeProcess()
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is False
    assert result["stage"] == "config_validation"
    assert "checkpoint_recipes.unbuilt" in result["error"]
    # The failure explains that only "base" is exempt from needing a recipe.
    assert "base" in result["error"]
    assert result["hol_preserved"] is True
    assert proc.alive is True


def test_base_rebuilds_without_explicit_recipe(monkeypatch, tmp_path):
    # "base" is vanilla HOL Light: it can be rebuilt even when the config
    # defines no checkpoint_recipes (e.g. an older hol-mcp.toml).
    config = make_config(tmp_path, checkpoint="base", checkpoint_recipes={})
    commands = []

    def run_command(command, stage):
        commands.append(command)
        if "--output-dir" in command:
            output_dir = command[command.index("--output-dir") + 1]
            os.makedirs(output_dir)
            open(os.path.join(output_dir, "ckpt_test.dmtcp"), "wb").close()

    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_run_restart_command", run_command)
    monkeypatch.setattr(server, "_install_checkpoint", lambda *_: (True, None))
    monkeypatch.setattr(server, "_restart_process", lambda _: (True, None))
    monkeypatch.setattr(server, "_proc", FakeProcess())

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is True
    assert result["rebuilt"] is True
    # The base recipe carries no include dirs or extra loads.
    checkpoint_command = commands[2]
    assert checkpoint_command[checkpoint_command.index("--name") + 1] == "base"
    assert "-I" not in checkpoint_command
    # Nothing follows --output-dir <dir> (no loads appended).
    assert checkpoint_command[-2] == "--output-dir"


def test_config_without_checkpoint_recipes_key_defaults_to_empty(tmp_path):
    # Backward compat: an older hol-mcp.toml has no [checkpoint_recipes].
    # Parsing must not crash and recipes must default to an empty table.
    config = server._effective_config(
        {"checkpoint": "base", "timeout": 600, "max_output_chars": 4000},
        str(tmp_path / "hol-mcp.toml"),
    )
    assert config["checkpoint_recipes"] == {}


def test_reload_without_recipes_still_restarts(monkeypatch, tmp_path):
    # A plain restart (no rebuild) must work against a recipe-less config.
    config = server._effective_config(
        {"checkpoint": "base"}, str(tmp_path / "hol-mcp.toml")
    )
    proc = FakeProcess()
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_restart_process", lambda _: (True, None))
    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, False, lambda *_: None)

    assert result["success"] is True
    assert result["config_reloaded"] is True


def test_hol_status_survives_missing_recipes(monkeypatch, tmp_path):
    # hol_status never consults checkpoint_recipes, so an old config that
    # lacks them must not crash it.
    config = server._effective_config(
        {"checkpoint": "base"}, str(tmp_path / "hol-mcp.toml")
    )
    server._apply_runtime_config(config)
    monkeypatch.setattr(server, "_proc", None)

    status = json.loads(server.hol_status())

    assert status["alive"] is False
    assert status["configured_checkpoint"] == "base"


def test_relative_recipe_paths_use_config_directory(tmp_path):
    config_dir = tmp_path / "project"
    config_dir.mkdir()
    config = server._effective_config(
        {
            "checkpoint": "gcm",
            "checkpoint_recipes": {
                "gcm": {
                    "include_dirs": ["../s2n-bignum"],
                    "loads": ['needs "common/gcm.ml"'],
                }
            },
        },
        str(config_dir / "hol-mcp.toml"),
    )

    assert config["checkpoint_recipes"]["gcm"]["include_dirs"] == [
        str(tmp_path / "s2n-bignum")
    ]


def test_rebuild_orders_build_and_checkpoint_recipe(monkeypatch, tmp_path):
    include_dir = tmp_path / "s2n"
    include_dir.mkdir()
    config = make_config(
        tmp_path,
        checkpoint="gcm",
        checkpoint_recipes={
            "gcm": {
                "include_dirs": [str(include_dir)],
                "loads": ['needs "arm/proofs/base.ml"', 'needs "common/gcm.ml"'],
            }
        },
    )
    commands = []

    def run_command(command, stage):
        commands.append(command)
        if "--output-dir" in command:
            output_dir = command[command.index("--output-dir") + 1]
            os.makedirs(output_dir)
            (open(os.path.join(output_dir, "ckpt_test.dmtcp"), "wb")).close()

    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_run_restart_command", run_command)
    monkeypatch.setattr(
        server, "_install_checkpoint", lambda *_: (True, None)
    )
    monkeypatch.setattr(server, "_restart_process", lambda _: (True, None))
    monkeypatch.setattr(server, "_proc", FakeProcess())
    monkeypatch.setattr(server, "_restart_required", True)
    monkeypatch.setattr(server, "_restart_error", "previous build failed")

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is True
    assert result["rebuilt"] is True
    assert server._restart_required is False
    assert commands[0] == ["make", "clean"]
    assert commands[1] == ["make"]
    checkpoint_command = commands[2]
    assert checkpoint_command[checkpoint_command.index("-I") + 1] == str(include_dir)
    assert checkpoint_command[-2:] == [
        'needs "arm/proofs/base.ml"',
        'needs "common/gcm.ml"',
    ]


def test_build_failure_quarantines_hol_and_preserves_checkpoint(
    monkeypatch, tmp_path
):
    checkpoint_dir = tmp_path / "hol-base.ckpt"
    checkpoint_dir.mkdir()
    checkpoint_file = checkpoint_dir / "ckpt_old.dmtcp"
    checkpoint_file.write_bytes(b"old")
    config = make_config(tmp_path)
    proc = FakeProcess()

    def fail_build(command, stage):
        if command == ["make"]:
            raise RuntimeError("build failed")

    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_run_restart_command", fail_build)
    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is False
    assert result["stage"] == "build"
    assert result["hol_preserved"] is False
    assert result["pid"] is None
    assert proc.alive is False
    assert server._restart_required is True
    assert checkpoint_file.read_bytes() == b"old"
    with pytest.raises(RuntimeError, match="failed HOL/checkpoint rebuild"):
        server._start_hol()

    retry = server._hol_restart_sync(None, False, lambda *_: None)
    assert retry["success"] is False
    assert "hol_restart(rebuild_hol_and_checkpoint=true)" in retry["error"]


def test_checkpoint_generation_failure_quarantines_hol(
    monkeypatch, tmp_path
):
    checkpoint_dir = tmp_path / "hol-base.ckpt"
    checkpoint_dir.mkdir()
    checkpoint_file = checkpoint_dir / "ckpt_old.dmtcp"
    checkpoint_file.write_bytes(b"old")
    config = make_config(tmp_path)
    proc = FakeProcess()

    def fail_generation(command, stage):
        if "--output-dir" in command:
            raise RuntimeError("checkpoint generation failed")

    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_run_restart_command", fail_generation)
    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is False
    assert result["stage"] == "checkpoint_creation"
    assert result["hol_preserved"] is False
    assert proc.alive is False
    assert server._restart_required is True
    assert checkpoint_file.read_bytes() == b"old"


def test_checkpoint_install_failure_reports_error_without_rollback(
    monkeypatch, tmp_path
):
    # Install does not roll back on failure: the caller quarantines HOL and
    # requires a fresh rebuild, so a failed install just reports the error.
    final_dir = tmp_path / "hol-base.ckpt"
    final_dir.mkdir()
    (final_dir / "ckpt_old.dmtcp").write_bytes(b"old")
    staged_dir = tmp_path / ".staged"
    staged_dir.mkdir()
    (staged_dir / "ckpt_new.dmtcp").write_bytes(b"new")

    def fail_install(source, destination):
        raise OSError("simulated install failure")

    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server.os, "replace", fail_install)

    installed, error = server._install_checkpoint("base", str(staged_dir))

    assert installed is False
    assert "simulated install failure" in error


def test_recording_dir_change_rejected_without_side_effects(
    monkeypatch, tmp_path
):
    config = make_config(tmp_path, recording_dir=str(tmp_path / "new"))
    proc = FakeProcess()
    restarted = False

    def restart(_):
        nonlocal restarted
        restarted = True
        return True, None

    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_restart_process", restart)
    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, False, lambda *_: None)

    assert result["success"] is False
    assert result["stage"] == "config_validation"
    assert result["hol_preserved"] is True
    assert restarted is False
    assert proc.alive is True


def test_install_failure_quarantines_hol(monkeypatch, tmp_path):
    config = make_config(tmp_path)
    proc = FakeProcess()
    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "_reload_config", lambda: config)
    monkeypatch.setattr(server, "_run_restart_command", lambda *_: None)
    monkeypatch.setattr(
        server,
        "_build_checkpoint",
        lambda *_: str(tmp_path / ".staged"),
    )
    monkeypatch.setattr(
        server,
        "_install_checkpoint",
        lambda *_: (False, "install failed"),
    )

    monkeypatch.setattr(server, "_proc", proc)

    result = server._hol_restart_sync(None, True, lambda *_: None)

    assert result["success"] is False
    assert result["stage"] == "checkpoint_install"
    assert result["hol_preserved"] is False
    assert result["startup_mode"] is None
    assert result["pid"] is None
    assert proc.alive is False
    assert server._restart_required is True


def test_status_detects_replaced_checkpoint(monkeypatch, tmp_path):
    checkpoint_dir = tmp_path / "hol-base.ckpt"
    checkpoint_dir.mkdir()
    checkpoint_file = checkpoint_dir / "ckpt_one.dmtcp"
    checkpoint_file.write_bytes(b"first")
    monkeypatch.setattr(server, "HOL_DIR", str(tmp_path))
    monkeypatch.setattr(server, "CHECKPOINT_NAME", "base")
    monkeypatch.setattr(
        server, "_checkpoint_fingerprint",
        server._fingerprint_checkpoint("base"),
    )

    checkpoint_file.write_bytes(b"replacement")
    status = json.loads(server.hol_status())

    assert status["checkpoint_stale"] is True
    assert status["checkpoint_fingerprint"][0]["name"] == "ckpt_one.dmtcp"
    assert isinstance(status["restart_required"], bool)


def test_progress_milestones_and_heartbeat(monkeypatch):
    class FakeContext:
        def __init__(self):
            self.reports = []

        async def report_progress(self, progress, total=None, message=None):
            self.reports.append((progress, total, message))

    def slow_restart(checkpoint, rebuild_hol_and_checkpoint, progress):
        for stage in (
            "config_validation",
            "clean",
            "build",
            "checkpoint_creation",
            "restart",
        ):
            progress(stage, stage)
        time.sleep(0.6)
        return {"success": True}

    context = FakeContext()
    monkeypatch.setattr(server, "_hol_restart_sync", slow_restart)
    monkeypatch.setattr(server, "RESTART_HEARTBEAT_SECONDS", 0.05)

    result = json.loads(
        asyncio.run(
            server.hol_restart(rebuild_hol_and_checkpoint=True, ctx=context)
        )
    )
    messages = [report[2] for report in context.reports]

    assert result["success"] is True
    assert set(messages[:5]) == {
        "config_validation",
        "clean",
        "build",
        "checkpoint_creation",
        "restart",
    }
    assert any("elapsed" in message for message in messages)
