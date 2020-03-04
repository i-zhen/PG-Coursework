SELECT (A1.title, B1.title) FROM(
	SELECT B.title, B.rating, A.country, B.year
	FROM Artist AS A
	INNER JOIN ALBUM AS B
	ON A.name = B.artist) AS A1,
	(SELECT B.title, B.rating, A.country, B.year
	FROM Artist AS A
	INNER JOIN ALBUM AS B
	ON A.name = B.artist) AS B1
WHERE A1.country != B1.country AND A1.year = B1.year AND A1.rating > B1.rating