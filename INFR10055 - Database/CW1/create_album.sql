CREATE TYPE ENUMTYPE_album AS ENUM ('STUDIO', 'LIVE','COMPILATION');
CREATE TABLE album 
(
	Title varchar(255) NOT NULL,
	Artist varchar(255) NOT NULL,
	Type ENUMTYPE_album NOT NULL,
	Year INTEGER NOT NULL,
	Rating INTEGER NOT NULL,
	CHECK(Rating >= 1 AND Rating <= 5),
	PRIMARY KEY (Title, Artist),
	FOREIGN KEY(Artist) REFERENCES Artist(Name)
);
