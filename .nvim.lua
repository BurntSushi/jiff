if vim.env.NEOVIM_JIFF_CARGO_FEATURES == nil then
  vim.lsp.config('rust_analyzer', {
    settings = {
      ['rust-analyzer'] = {
        cargo = {
          features = 'all',
        },
        check = {
          features = 'all',
        },
      },
    },
  })
else
  -- This is useful for viewing diagnostics for a specific feature config. It
  -- tries to disable all targets and workspace-wide commands, along with any
  -- default features. Instead, the only features enabled are what's in the
  -- `NEOVIM_JIFF_CARGO_FEATURES` environment variable.
  --
  -- Note that as of 2026-06-13, while this shows diagnostics under the
  -- provided feature configuration, other rust-analyzer tasks like
  -- goto-definition still use the project wide workspace configuration. Under
  -- that model, crates like `jiff-cli` enable `jiff`'s `std` feature, which
  -- means we aren't limited to just the features there. I believe the only
  -- way to fix this is to have a proper workspace `Cargo.toml` and a separate
  -- `Cargo.toml` for Jiff. But that's a bigger change. ---AG
  local root = vim.fn.getcwd()
  local features = {}
  for feature in vim.env.NEOVIM_JIFF_CARGO_FEATURES:gmatch('[^,]+') do
    table.insert(features, feature)
  end
  vim.lsp.config('rust_analyzer', {
    settings = {
      ['rust-analyzer'] = {
        linkedProjects = {
          root .. '/Cargo.toml',
        },
        cargo = {
          noDefaultFeatures = true,
          features = features,
          workspace = false,
          allTargets = false,
        },
        check = {
          workspace = false,
          allTargets = false,
        },
      },
    },
  })
end
