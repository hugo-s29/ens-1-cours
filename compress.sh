# Compress ColaNote PDFs (because they're WAY TOO HEAVY)

convert -density 125 log/dm1-uncompressed.pdf -quality 99 -compress Zip log/dm1.pdf
convert -density 125 proba/td-uncompressed.pdf -quality 99 -compress Zip proba/td.pdf
