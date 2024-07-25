public class CF {

public /*@ pure @*/static String codiceMese(int mese){
    switch(mese){
        case 1: return "A";
        case 2: return "B";
        case 3: return "C";
        case 4: return "D";
        case 5: return "E";
        case 6: return "H";
        case 7: return "L";
        case 8: return "M";
        case 9: return "P";
        case 10: return "R";
        case 11: return "S";
        case 12: return "T";
    }
    throw new IllegalArgumentException();
}

public  /*@ pure @*/ static String codiceCognome(String cognome) {
    return getConsonanti(cognome)
            .concat(getVocali(cognome))
            .concat("xxx")
            .substring(0,3);
}

public   /*@ pure @*/ static String codiceNome(String nome) {

    String n = nome.split(",")[0];
    String codice="";
    String consonanti=getConsonanti(n);

    if(consonanti.length()>=4){
        //prima terza quarta
        codice+=consonanti.charAt(0)+consonanti.charAt(2)+consonanti.charAt(3);
    }else{
        //come cognome
        codice=codiceCognome(nome);
    }
    return codice;
}

private   /*@ pure @*/ static String getConsonanti(String str){
    return str.replaceAll("[aeiou]", "");

}

private   /*@ pure @*/ static String getVocali(String str){
    return str.replaceAll("[^aeiou]", "");
}

public   /*@ pure @*/ static String codiceGiorno(int giorno, char sesso){
    if(sesso=='f'){
        giorno+=40;
    }
    return giorno<10 ? "0"+giorno : ""+giorno;
}

public   /*@ pure @*/ static String codiceAnno(int anno){
    return (anno%100)<10 ? "0"+anno : ""+anno;

}
}
