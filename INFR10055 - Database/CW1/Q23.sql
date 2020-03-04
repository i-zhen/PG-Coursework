SELECT title FROM (
	SELECT * FROM ALBUM AS A, ARTIST AS B /*Select the table C which the artists is band */
	WHERE A.artist = B.name AND B.type = 'BAND') AS C
WHERE C.rating > ALL(
	SELECT D.rating FROM ALBUM AS D      /*Select the table which the years smaller than C */
	WHERE D.artist = C.artist AND D.year < C.year
	)