SELECT * FROM (
	SELECT A.name, COUNT(B.title) AS CNT, A.country
	FROM Artist AS A
	INNER JOIN ALBUM AS B
	ON A.name = B.artist
	GROUP BY A.name) AS C,
	(SELECT A.name, COUNT(B.title) AS CNT, A.country
	FROM Artist AS A
	INNER JOIN ALBUM AS B
	ON A.name = B.artist
	GROUP BY A.name) AS D
WHERE D.name != C.name AND C.cnt > D.cnt AND C.country = D.country

