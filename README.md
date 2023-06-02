# categorical-crypto

## Notes from the 2023 IO Agda Workshop in Parma, Italy

(The exercises are inside the [UU.lagda.md](UU.lagda.md) file.)



To generate html, 

```
git clone https://github.com/input-output-hk/agda-workshop-2023
cd agda-workshop-2023
agda --library-file=$HOME/.agda/libraries --html --html-highlight=all UU.lagda.md
git checkout -b gh-pages  # only use `-b` the first time
\cp -a html/* .
git add .
git commit -m "updating html"
git push
```
