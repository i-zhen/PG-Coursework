SELECT A1.title FROM
	(SELECT * FROM Album AS A, Artist AS B
	WHERE A.artist = B.name AND B.country = 'UK') AS A1
WHERE A1.rating > (SELECT AVG(Rating) FROM ALBUM WHERE YEAR = A1.YEAR) /*Compute the same year average rating*/