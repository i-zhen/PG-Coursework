CREATE TABLE Tracklist 
(
	Album_Title varchar(255) NOT NULL,
	Album_Artist varchar(255) NOT NULL,
	Track_No INTEGER NOT NULL,
	Track_Title varchar(255) NOT NULL,
	Track_Length TIME NOT NULL,
	PRIMARY KEY (Album_Title, Album_Artist, Track_No),
	FOREIGN KEY(Album_Title, Album_Artist) REFERENCES Album(Title, Artist)
);