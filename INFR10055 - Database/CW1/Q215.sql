SELECT * FROM ALBUM AS A,
	(SELECT album_title, COUNT(track_no) AS CNT FROM TRACKLIST
	GROUP BY album_title) AS B
WHERE A.title = B.album_title
ORDER BY CAST(B.cnt AS NUMERIC) / CAST(A.rating AS NUMERIC)