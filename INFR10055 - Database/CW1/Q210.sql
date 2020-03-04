SELECT DISTINCT A.artist FROM ALBUM AS A
WHERE (SELECT COUNT(type) FROM album where type = 'STUDIO' AND artist = A.artist) >= 3 AND
	(SELECT COUNT(type) FROM album where type = 'LIVE' AND artist = A.artist) >= 2 AND
	(SELECT COUNT(type) FROM album where type = 'COMPILATION' AND artist = A.artist) >= 1
	AND NOT EXISTS (SELECT * FROM Album WHERE A.artist = artist AND rating < 3)