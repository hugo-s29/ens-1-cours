# Compress ColaNote PDFs (because they're WAY TOO HEAVY)
#
# Should NEVER be ran directly, only copy the required line
# and run it in a shell
# otherwise it'll create endless versions of PDFs...

convert -density 125 log/dm1-uncompressed.pdf -quality 99 -compress Zip log/dm1.pdf
convert -density 125 log/td-uncompressed.pdf -quality 99 -compress Zip log/td.pdf
convert -density 125 proba/dm1-uncompressed.pdf -quality 99 -compress Zip proba/dm1.pdf
convert -density 125 proba/td-uncompressed.pdf -quality 99 -compress Zip proba/td.pdf
