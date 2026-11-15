# GitHub login and push

Run these commands from your local project directory. Browser login authenticates directly with GitHub:

```sh
gh auth login --hostname github.com --git-protocol https --web
gh auth setup-git --hostname github.com
gh auth status
```

For a new remote repository:

```sh
gh repo create expanding-codes-polynomial-stretch --public --source=. --remote=origin --push
```

Change the repository name if desired, use `OWNER/REPO` for another owner, or choose `--private` for private visibility. If the remote already exists, add its URL and push:

```sh
git remote add origin https://github.com/YOUR_USERNAME/YOUR_REPOSITORY.git
git push -u origin main
```

The privacy cleanup replaced the local initial history. If an existing private remote already stored the earlier snapshot, the recommended public-release route is to leave it private and create a fresh repository from the sanitized `main`. Use a different repository and remote name, for example:

```sh
gh repo create expanding-codes-polynomial-stretch-public --public --source=. --remote=public
git push -u public main
```

To update the old private repository's branch as well, after reviewing the sanitized local tree:

```sh
git push --force-with-lease origin main
```

Keep that old remote private: a force-push alone can leave earlier commits accessible through cached views or existing copies. See [GitHub's history-cleanup guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository).

Git authorship and GitHub authentication are separate. The sanitized local commit uses a neutral contributor identity; choose your own public name and GitHub-provided noreply email for future commits if desired:

```sh
git config --local user.name "Your public name"
git config --local user.email "YOUR_GITHUB_NOREPLY_EMAIL"
```

On a Mac without GitHub CLI, install it with `brew install gh` first. On other platforms, follow the [official installation instructions](https://cli.github.com/).

`.env`, authentication caches, and local recovery files are ignored. The staged-content guard is enabled through `core.hooksPath=.githooks`; after a fresh clone, run `./tools/setup-repo` to enable it there. `.env.example` contains only a variable name. Credentials stay on the local device; no token belongs in a remote URL or Git command.

References: [browser authentication](https://cli.github.com/manual/gh_auth_login), [creating a remote](https://cli.github.com/manual/gh_repo_create), and [credential-helper setup](https://cli.github.com/manual/gh_auth_setup-git).
