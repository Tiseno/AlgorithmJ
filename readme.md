# Hindley Milner [Algorithm J](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_J)

```
$ runhaskell main.hs example/infinite.j
\x -> (x x)
(\x -> (x:t1 x:t1):Error(Infinite type)):(t1->Error(Infinite type))
```

## TODO
* Recursive definitions

