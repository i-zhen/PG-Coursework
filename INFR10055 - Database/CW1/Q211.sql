SELECT COUNT(A.artist) FROM ALBUM AS A, ARTIST AS B
WHERE A.year = (SELECT MIN(year) FROM album where artist = A.artist) 
	AND A.rating = 5
	AND A.artist = B.name 
	AND B.type = 'BAND'
	AND B.country = 'USA'