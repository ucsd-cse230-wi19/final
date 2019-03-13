
# CSE 230 Wi19 Takehome Final 

## Notes

1. **Due Sunday 3/24, 23:59:59**

2. Split into three problems `Problem{1,2,3}.hs`

3. `Problem3.hs` is probably the easiest; you can try it by just doing

       `make`

   to build all the imported modules and then editing and rechecking with 

       `cd src && stack exec -- liquid Problem3.hs` 

   However, doing "automatic" verification is super slow with current LH: 
   you may want to use the DAFNY verifier designed specifically to do 
   `vc`-based checking using the supplied links, to first figure out 
   the "right" invariants and then just "translate" those back to 
   fill in the correct `inv`.

## Download

1. Use the _fork link_ from the class website to create your private clone of the starter code.

2. Do `git clone https://github.com/ucsd-cse230-wi19/final-XXX` where `XXX` is your private repo.

## Link to Upstream

3. Link your clone to the "upstream" to get any updates

```
$ make upstream
```

after this you can get "updates" (in case we modify the starter code), with

```
$ make update
```

## Do the Assignment 

4. Edit the files and run LH 

```
$ make 
```

repeat this until LH says "SAFE"

## Submit 

5. Save (and submit) your work with:

```
$ git commit -a -m MESSAGE
$ git push
```
