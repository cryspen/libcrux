import tomlkit
import os
import sys

libcrux_root = sys.argv[1]
workspace_toml_path = os.path.join(libcrux_root, 'Cargo.toml')
crate_toml_path = os.path.join(libcrux_root, 'libcrux-ml-kem/Cargo.toml')
package_toml_path = os.path.join(libcrux_root, 'libcrux-ml-kem/pqcp/repo/Cargo.toml')

with open(workspace_toml_path, 'r') as workspace_toml_f:
    with open(crate_toml_path, 'r') as crate_toml_f:
        workspace_toml = tomlkit.parse(workspace_toml_f.read())
        crate_toml = tomlkit.parse(crate_toml_f.read())

        package_toml = tomlkit.document()

        package = tomlkit.table()
        package["name"] = crate_toml["package"]["name"]
        package["description"] = crate_toml["package"]["description"]
        package["readme"] = crate_toml["package"]["readme"]
        package["version"] = workspace_toml["workspace"]["package"]["version"]
        package["authors"] = workspace_toml["workspace"]["package"]["authors"]
        package["license"] = workspace_toml["workspace"]["package"]["license"]
        package["edition"] = workspace_toml["workspace"]["package"]["edition"]
        package["repository"] = workspace_toml["workspace"]["package"]["repository"]
        package_toml["package"] = package


        package_toml["workspace"] = tomlkit.table()
        package_toml["workspace"]["members"] = ["."]


        deps = tomlkit.table()
        for dep in crate_toml["dependencies"]:
            deps[dep] = {"version": crate_toml["dependencies"][dep]["version"]}
        package_toml["dependencies"] = deps
        package_toml["features"] = crate_toml["features"]
        package_toml["dev-dependencies"] = crate_toml["dev-dependencies"]

        package_toml["profile"] = tomlkit.table()
        package_toml["profile"]["release"] = workspace_toml["profile"]["release"]

        with open(package_toml_path, 'w') as package_toml_f:
            package_toml_f.write(tomlkit.dumps(package_toml))
