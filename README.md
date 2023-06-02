# categorical-crypto

## Notes from the 2023 IO Agda Workshop in Parma, Italy

(The exercises are inside the [UU.lagda.md](UU.lagda.md) file.)



To generate html, 

```
git clone https://github.com/input-output-hk/categorical-crypto.git
cd categorical-crypto/Parma
agda --library-file=$HOME/.agda/libraries --html --html-highlight=all UU.lagda.md
git checkout gh-pages
\cp -a Parma/*.html ../
git add ../*.html
\cp ../{UU,index}.md
git commit -m "updating html"
git push
```
