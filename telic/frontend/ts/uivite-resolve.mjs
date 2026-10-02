import { createRequire } from "node:module";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const require = createRequire(import.meta.url);
const ts = require("typescript");
const input = JSON.parse(fs.readFileSync(0, "utf8"));
const root = path.resolve(input.projectRoot);
const workspaceRoot = path.resolve(input.workspaceRoot);
const files = input.files;
const projectRequire = createRequire(pathToFileURL(path.join(root, "package.json")));
const server = await projectRequire("vite").createServer({
  root,
  configFile: input.config,
  configFileDependencies: [],
  server: { middlewareMode: true },
  appType: "custom",
  logLevel: "silent",
});
const resolutions = {};
try {
  for (const file of files) {
    const absolute = path.resolve(workspaceRoot, file.path);
    const kind = /\.(tsx|jsx)$/.test(file.path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(file.path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
    const source = ts.createSourceFile(file.path, file.text, ts.ScriptTarget.Latest, true, kind);
    for (const statement of source.statements) {
      const specifier = ts.isImportDeclaration(statement) || ts.isExportDeclaration(statement)
        ? statement.moduleSpecifier
        : null;
      if (!specifier || !ts.isStringLiteralLike(specifier) || !specifier.text.startsWith(".")) continue;
      const id = `${file.path}\0${specifier.text}`;
      const result = await server.pluginContainer.resolveId(specifier.text, absolute);
      if (!result || result.external) {
        resolutions[id] = null;
        continue;
      }
      const resolved = result.id.split("?")[0];
      let decoded;
      try { decoded = resolved.startsWith("file:") ? fileURLToPath(resolved) : decodeURIComponent(resolved); }
      catch { resolutions[id] = null; continue; }
      if (!path.isAbsolute(decoded)) decoded = path.resolve(root, decoded.replace(/^\//, ""));
      const withinProject = path.relative(root, decoded);
      const relative = path.relative(workspaceRoot, decoded).split(path.sep).join("/");
      resolutions[id] = withinProject === ".." || withinProject.startsWith(`..${path.sep}`) || path.isAbsolute(withinProject) ? null : relative;
    }
  }
  process.stdout.write(JSON.stringify({ resolutions }));
} finally {
  await server.close();
}
