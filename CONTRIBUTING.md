# 開発者向け情報

## lean2md

リポジトリのルート(このファイルがあるディレクトリ)で下記を実行します．すると，`NTL` ディレクトリ直下にある `NTL/*.lean` ファイルから markdown ファイルが生成されます．

```bash
python scripts/lean2md.py NTL NTL
```

なお, ワークスペースの推奨の拡張機能をインストールしていれば，上記のコマンドは `NTL/*.lean` ファイルを編集するごとに自動で実行されます．