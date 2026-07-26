pub(super) static VERSION: Option<&str> = Some("2026c");

pub(crate) static MAP: &'static [jcore::tz::tzif::MaybeNamedTimeZone<
    &'static jcore::tz::tzif::TimeZone,
>] = &[
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Abidjan")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Accra")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Addis_Ababa")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Algiers")),
        tz: &crate::timezones::AFRICA_ALGIERS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Asmara")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Asmera")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Bamako")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Bangui")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Banjul")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Bissau")),
        tz: &crate::timezones::AFRICA_BISSAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Blantyre")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Brazzaville")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Bujumbura")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Cairo")),
        tz: &crate::timezones::AFRICA_CAIRO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Casablanca")),
        tz: &crate::timezones::AFRICA_CASABLANCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Ceuta")),
        tz: &crate::timezones::AFRICA_CEUTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Conakry")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Dakar")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Dar_es_Salaam")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Djibouti")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Douala")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/El_Aaiun")),
        tz: &crate::timezones::AFRICA_EL_AAIUN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Freetown")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Gaborone")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Harare")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Johannesburg")),
        tz: &crate::timezones::AFRICA_JOHANNESBURG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Juba")),
        tz: &crate::timezones::AFRICA_JUBA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Kampala")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Khartoum")),
        tz: &crate::timezones::AFRICA_KHARTOUM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Kigali")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Kinshasa")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Lagos")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Libreville")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Lome")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Luanda")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Lubumbashi")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Lusaka")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Malabo")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Maputo")),
        tz: &crate::timezones::AFRICA_BLANTYRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Maseru")),
        tz: &crate::timezones::AFRICA_JOHANNESBURG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Mbabane")),
        tz: &crate::timezones::AFRICA_JOHANNESBURG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Mogadishu")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Monrovia")),
        tz: &crate::timezones::AFRICA_MONROVIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Nairobi")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Ndjamena")),
        tz: &crate::timezones::AFRICA_NDJAMENA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Niamey")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Nouakchott")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Ouagadougou")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Porto-Novo")),
        tz: &crate::timezones::AFRICA_BANGUI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Sao_Tome")),
        tz: &crate::timezones::AFRICA_SAO_TOME,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Timbuktu")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Tripoli")),
        tz: &crate::timezones::AFRICA_TRIPOLI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Tunis")),
        tz: &crate::timezones::AFRICA_TUNIS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Africa/Windhoek")),
        tz: &crate::timezones::AFRICA_WINDHOEK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Adak")),
        tz: &crate::timezones::AMERICA_ADAK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Anchorage")),
        tz: &crate::timezones::AMERICA_ANCHORAGE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Anguilla")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Antigua")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Araguaina")),
        tz: &crate::timezones::AMERICA_ARAGUAINA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/Buenos_Aires",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_BUENOS_AIRES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/Catamarca",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_CATAMARCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/ComodRivadavia",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_CATAMARCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Cordoba")),
        tz: &crate::timezones::AMERICA_ARGENTINA_CORDOBA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Jujuy")),
        tz: &crate::timezones::AMERICA_ARGENTINA_JUJUY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/La_Rioja",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_LA_RIOJA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Mendoza")),
        tz: &crate::timezones::AMERICA_ARGENTINA_MENDOZA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/Rio_Gallegos",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_RIO_GALLEGOS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Salta")),
        tz: &crate::timezones::AMERICA_ARGENTINA_SALTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/San_Juan",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_SAN_JUAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Argentina/San_Luis",
        )),
        tz: &crate::timezones::AMERICA_ARGENTINA_SAN_LUIS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Tucuman")),
        tz: &crate::timezones::AMERICA_ARGENTINA_TUCUMAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Argentina/Ushuaia")),
        tz: &crate::timezones::AMERICA_ARGENTINA_USHUAIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Aruba")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Asuncion")),
        tz: &crate::timezones::AMERICA_ASUNCION,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Atikokan")),
        tz: &crate::timezones::AMERICA_ATIKOKAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Atka")),
        tz: &crate::timezones::AMERICA_ADAK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Bahia")),
        tz: &crate::timezones::AMERICA_BAHIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Bahia_Banderas")),
        tz: &crate::timezones::AMERICA_BAHIA_BANDERAS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Barbados")),
        tz: &crate::timezones::AMERICA_BARBADOS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Belem")),
        tz: &crate::timezones::AMERICA_BELEM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Belize")),
        tz: &crate::timezones::AMERICA_BELIZE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Blanc-Sablon")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Boa_Vista")),
        tz: &crate::timezones::AMERICA_BOA_VISTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Bogota")),
        tz: &crate::timezones::AMERICA_BOGOTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Boise")),
        tz: &crate::timezones::AMERICA_BOISE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Buenos_Aires")),
        tz: &crate::timezones::AMERICA_ARGENTINA_BUENOS_AIRES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cambridge_Bay")),
        tz: &crate::timezones::AMERICA_CAMBRIDGE_BAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Campo_Grande")),
        tz: &crate::timezones::AMERICA_CAMPO_GRANDE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cancun")),
        tz: &crate::timezones::AMERICA_CANCUN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Caracas")),
        tz: &crate::timezones::AMERICA_CARACAS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Catamarca")),
        tz: &crate::timezones::AMERICA_ARGENTINA_CATAMARCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cayenne")),
        tz: &crate::timezones::AMERICA_CAYENNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cayman")),
        tz: &crate::timezones::AMERICA_ATIKOKAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Chicago")),
        tz: &crate::timezones::AMERICA_CHICAGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Chihuahua")),
        tz: &crate::timezones::AMERICA_CHIHUAHUA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Ciudad_Juarez")),
        tz: &crate::timezones::AMERICA_CIUDAD_JUAREZ,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Coral_Harbour")),
        tz: &crate::timezones::AMERICA_ATIKOKAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cordoba")),
        tz: &crate::timezones::AMERICA_ARGENTINA_CORDOBA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Costa_Rica")),
        tz: &crate::timezones::AMERICA_COSTA_RICA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Coyhaique")),
        tz: &crate::timezones::AMERICA_COYHAIQUE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Creston")),
        tz: &crate::timezones::AMERICA_CRESTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Cuiaba")),
        tz: &crate::timezones::AMERICA_CUIABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Curacao")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Danmarkshavn")),
        tz: &crate::timezones::AMERICA_DANMARKSHAVN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Dawson")),
        tz: &crate::timezones::AMERICA_DAWSON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Dawson_Creek")),
        tz: &crate::timezones::AMERICA_DAWSON_CREEK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Denver")),
        tz: &crate::timezones::AMERICA_DENVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Detroit")),
        tz: &crate::timezones::AMERICA_DETROIT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Dominica")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Edmonton")),
        tz: &crate::timezones::AMERICA_EDMONTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Eirunepe")),
        tz: &crate::timezones::AMERICA_EIRUNEPE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/El_Salvador")),
        tz: &crate::timezones::AMERICA_EL_SALVADOR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Ensenada")),
        tz: &crate::timezones::AMERICA_ENSENADA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Fort_Nelson")),
        tz: &crate::timezones::AMERICA_FORT_NELSON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Fort_Wayne")),
        tz: &crate::timezones::AMERICA_FORT_WAYNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Fortaleza")),
        tz: &crate::timezones::AMERICA_FORTALEZA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Glace_Bay")),
        tz: &crate::timezones::AMERICA_GLACE_BAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Godthab")),
        tz: &crate::timezones::AMERICA_GODTHAB,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Goose_Bay")),
        tz: &crate::timezones::AMERICA_GOOSE_BAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Grand_Turk")),
        tz: &crate::timezones::AMERICA_GRAND_TURK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Grenada")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Guadeloupe")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Guatemala")),
        tz: &crate::timezones::AMERICA_GUATEMALA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Guayaquil")),
        tz: &crate::timezones::AMERICA_GUAYAQUIL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Guyana")),
        tz: &crate::timezones::AMERICA_GUYANA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Halifax")),
        tz: &crate::timezones::AMERICA_HALIFAX,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Havana")),
        tz: &crate::timezones::AMERICA_HAVANA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Hermosillo")),
        tz: &crate::timezones::AMERICA_HERMOSILLO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Indiana/Indianapolis",
        )),
        tz: &crate::timezones::AMERICA_FORT_WAYNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Knox")),
        tz: &crate::timezones::AMERICA_INDIANA_KNOX,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Marengo")),
        tz: &crate::timezones::AMERICA_INDIANA_MARENGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Indiana/Petersburg",
        )),
        tz: &crate::timezones::AMERICA_INDIANA_PETERSBURG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Tell_City")),
        tz: &crate::timezones::AMERICA_INDIANA_TELL_CITY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Vevay")),
        tz: &crate::timezones::AMERICA_INDIANA_VEVAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Vincennes")),
        tz: &crate::timezones::AMERICA_INDIANA_VINCENNES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indiana/Winamac")),
        tz: &crate::timezones::AMERICA_INDIANA_WINAMAC,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Indianapolis")),
        tz: &crate::timezones::AMERICA_FORT_WAYNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Inuvik")),
        tz: &crate::timezones::AMERICA_INUVIK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Iqaluit")),
        tz: &crate::timezones::AMERICA_IQALUIT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Jamaica")),
        tz: &crate::timezones::AMERICA_JAMAICA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Jujuy")),
        tz: &crate::timezones::AMERICA_ARGENTINA_JUJUY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Juneau")),
        tz: &crate::timezones::AMERICA_JUNEAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Kentucky/Louisville",
        )),
        tz: &crate::timezones::AMERICA_KENTUCKY_LOUISVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/Kentucky/Monticello",
        )),
        tz: &crate::timezones::AMERICA_KENTUCKY_MONTICELLO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Knox_IN")),
        tz: &crate::timezones::AMERICA_INDIANA_KNOX,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Kralendijk")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/La_Paz")),
        tz: &crate::timezones::AMERICA_LA_PAZ,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Lima")),
        tz: &crate::timezones::AMERICA_LIMA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Los_Angeles")),
        tz: &crate::timezones::AMERICA_LOS_ANGELES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Louisville")),
        tz: &crate::timezones::AMERICA_KENTUCKY_LOUISVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Lower_Princes")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Maceio")),
        tz: &crate::timezones::AMERICA_MACEIO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Managua")),
        tz: &crate::timezones::AMERICA_MANAGUA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Manaus")),
        tz: &crate::timezones::AMERICA_MANAUS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Marigot")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Martinique")),
        tz: &crate::timezones::AMERICA_MARTINIQUE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Matamoros")),
        tz: &crate::timezones::AMERICA_MATAMOROS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Mazatlan")),
        tz: &crate::timezones::AMERICA_MAZATLAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Mendoza")),
        tz: &crate::timezones::AMERICA_ARGENTINA_MENDOZA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Menominee")),
        tz: &crate::timezones::AMERICA_MENOMINEE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Merida")),
        tz: &crate::timezones::AMERICA_MERIDA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Metlakatla")),
        tz: &crate::timezones::AMERICA_METLAKATLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Mexico_City")),
        tz: &crate::timezones::AMERICA_MEXICO_CITY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Miquelon")),
        tz: &crate::timezones::AMERICA_MIQUELON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Moncton")),
        tz: &crate::timezones::AMERICA_MONCTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Monterrey")),
        tz: &crate::timezones::AMERICA_MONTERREY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Montevideo")),
        tz: &crate::timezones::AMERICA_MONTEVIDEO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Montreal")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Montserrat")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Nassau")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/New_York")),
        tz: &crate::timezones::AMERICA_NEW_YORK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Nipigon")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Nome")),
        tz: &crate::timezones::AMERICA_NOME,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Noronha")),
        tz: &crate::timezones::AMERICA_NORONHA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/North_Dakota/Beulah",
        )),
        tz: &crate::timezones::AMERICA_NORTH_DAKOTA_BEULAH,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/North_Dakota/Center",
        )),
        tz: &crate::timezones::AMERICA_NORTH_DAKOTA_CENTER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik(
            "America/North_Dakota/New_Salem",
        )),
        tz: &crate::timezones::AMERICA_NORTH_DAKOTA_NEW_SALEM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Nuuk")),
        tz: &crate::timezones::AMERICA_GODTHAB,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Ojinaga")),
        tz: &crate::timezones::AMERICA_OJINAGA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Panama")),
        tz: &crate::timezones::AMERICA_ATIKOKAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Pangnirtung")),
        tz: &crate::timezones::AMERICA_IQALUIT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Paramaribo")),
        tz: &crate::timezones::AMERICA_PARAMARIBO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Phoenix")),
        tz: &crate::timezones::AMERICA_CRESTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Port-au-Prince")),
        tz: &crate::timezones::AMERICA_PORT_MINUS_AU_MINUS_PRINCE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Port_of_Spain")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Porto_Acre")),
        tz: &crate::timezones::AMERICA_PORTO_ACRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Porto_Velho")),
        tz: &crate::timezones::AMERICA_PORTO_VELHO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Puerto_Rico")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Punta_Arenas")),
        tz: &crate::timezones::AMERICA_PUNTA_ARENAS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Rainy_River")),
        tz: &crate::timezones::AMERICA_RAINY_RIVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Rankin_Inlet")),
        tz: &crate::timezones::AMERICA_RANKIN_INLET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Recife")),
        tz: &crate::timezones::AMERICA_RECIFE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Regina")),
        tz: &crate::timezones::AMERICA_REGINA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Resolute")),
        tz: &crate::timezones::AMERICA_RESOLUTE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Rio_Branco")),
        tz: &crate::timezones::AMERICA_PORTO_ACRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Rosario")),
        tz: &crate::timezones::AMERICA_ARGENTINA_CORDOBA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Santa_Isabel")),
        tz: &crate::timezones::AMERICA_ENSENADA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Santarem")),
        tz: &crate::timezones::AMERICA_SANTAREM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Santiago")),
        tz: &crate::timezones::AMERICA_SANTIAGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Santo_Domingo")),
        tz: &crate::timezones::AMERICA_SANTO_DOMINGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Sao_Paulo")),
        tz: &crate::timezones::AMERICA_SAO_PAULO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Scoresbysund")),
        tz: &crate::timezones::AMERICA_SCORESBYSUND,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Shiprock")),
        tz: &crate::timezones::AMERICA_DENVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Sitka")),
        tz: &crate::timezones::AMERICA_SITKA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Barthelemy")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Johns")),
        tz: &crate::timezones::AMERICA_ST_JOHNS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Kitts")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Lucia")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Thomas")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/St_Vincent")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Swift_Current")),
        tz: &crate::timezones::AMERICA_SWIFT_CURRENT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Tegucigalpa")),
        tz: &crate::timezones::AMERICA_TEGUCIGALPA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Thule")),
        tz: &crate::timezones::AMERICA_THULE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Thunder_Bay")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Tijuana")),
        tz: &crate::timezones::AMERICA_ENSENADA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Toronto")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Tortola")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Vancouver")),
        tz: &crate::timezones::AMERICA_VANCOUVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Virgin")),
        tz: &crate::timezones::AMERICA_ANGUILLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Whitehorse")),
        tz: &crate::timezones::AMERICA_WHITEHORSE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Winnipeg")),
        tz: &crate::timezones::AMERICA_RAINY_RIVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Yakutat")),
        tz: &crate::timezones::AMERICA_YAKUTAT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("America/Yellowknife")),
        tz: &crate::timezones::AMERICA_EDMONTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Casey")),
        tz: &crate::timezones::ANTARCTICA_CASEY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Davis")),
        tz: &crate::timezones::ANTARCTICA_DAVIS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/DumontDUrville")),
        tz: &crate::timezones::ANTARCTICA_DUMONTDURVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Macquarie")),
        tz: &crate::timezones::ANTARCTICA_MACQUARIE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Mawson")),
        tz: &crate::timezones::ANTARCTICA_MAWSON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/McMurdo")),
        tz: &crate::timezones::ANTARCTICA_MCMURDO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Palmer")),
        tz: &crate::timezones::ANTARCTICA_PALMER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Rothera")),
        tz: &crate::timezones::ANTARCTICA_ROTHERA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/South_Pole")),
        tz: &crate::timezones::ANTARCTICA_MCMURDO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Syowa")),
        tz: &crate::timezones::ANTARCTICA_SYOWA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Troll")),
        tz: &crate::timezones::ANTARCTICA_TROLL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Antarctica/Vostok")),
        tz: &crate::timezones::ANTARCTICA_VOSTOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Arctic/Longyearbyen")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Aden")),
        tz: &crate::timezones::ANTARCTICA_SYOWA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Almaty")),
        tz: &crate::timezones::ASIA_ALMATY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Amman")),
        tz: &crate::timezones::ASIA_AMMAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Anadyr")),
        tz: &crate::timezones::ASIA_ANADYR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Aqtau")),
        tz: &crate::timezones::ASIA_AQTAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Aqtobe")),
        tz: &crate::timezones::ASIA_AQTOBE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ashgabat")),
        tz: &crate::timezones::ASIA_ASHGABAT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ashkhabad")),
        tz: &crate::timezones::ASIA_ASHGABAT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Atyrau")),
        tz: &crate::timezones::ASIA_ATYRAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Baghdad")),
        tz: &crate::timezones::ASIA_BAGHDAD,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Bahrain")),
        tz: &crate::timezones::ASIA_BAHRAIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Baku")),
        tz: &crate::timezones::ASIA_BAKU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Bangkok")),
        tz: &crate::timezones::ASIA_BANGKOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Barnaul")),
        tz: &crate::timezones::ASIA_BARNAUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Beirut")),
        tz: &crate::timezones::ASIA_BEIRUT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Bishkek")),
        tz: &crate::timezones::ASIA_BISHKEK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Brunei")),
        tz: &crate::timezones::ASIA_BRUNEI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Calcutta")),
        tz: &crate::timezones::ASIA_CALCUTTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Chita")),
        tz: &crate::timezones::ASIA_CHITA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Choibalsan")),
        tz: &crate::timezones::ASIA_CHOIBALSAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Chongqing")),
        tz: &crate::timezones::ASIA_CHONGQING,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Chungking")),
        tz: &crate::timezones::ASIA_CHONGQING,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Colombo")),
        tz: &crate::timezones::ASIA_COLOMBO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Dacca")),
        tz: &crate::timezones::ASIA_DACCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Damascus")),
        tz: &crate::timezones::ASIA_DAMASCUS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Dhaka")),
        tz: &crate::timezones::ASIA_DACCA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Dili")),
        tz: &crate::timezones::ASIA_DILI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Dubai")),
        tz: &crate::timezones::ASIA_DUBAI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Dushanbe")),
        tz: &crate::timezones::ASIA_DUSHANBE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Famagusta")),
        tz: &crate::timezones::ASIA_FAMAGUSTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Gaza")),
        tz: &crate::timezones::ASIA_GAZA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Harbin")),
        tz: &crate::timezones::ASIA_CHONGQING,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Hebron")),
        tz: &crate::timezones::ASIA_HEBRON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ho_Chi_Minh")),
        tz: &crate::timezones::ASIA_HO_CHI_MINH,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Hong_Kong")),
        tz: &crate::timezones::ASIA_HONG_KONG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Hovd")),
        tz: &crate::timezones::ASIA_HOVD,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Irkutsk")),
        tz: &crate::timezones::ASIA_IRKUTSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Istanbul")),
        tz: &crate::timezones::ASIA_ISTANBUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Jakarta")),
        tz: &crate::timezones::ASIA_JAKARTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Jayapura")),
        tz: &crate::timezones::ASIA_JAYAPURA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Jerusalem")),
        tz: &crate::timezones::ASIA_JERUSALEM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kabul")),
        tz: &crate::timezones::ASIA_KABUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kamchatka")),
        tz: &crate::timezones::ASIA_KAMCHATKA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Karachi")),
        tz: &crate::timezones::ASIA_KARACHI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kashgar")),
        tz: &crate::timezones::ASIA_KASHGAR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kathmandu")),
        tz: &crate::timezones::ASIA_KATHMANDU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Katmandu")),
        tz: &crate::timezones::ASIA_KATHMANDU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Khandyga")),
        tz: &crate::timezones::ASIA_KHANDYGA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kolkata")),
        tz: &crate::timezones::ASIA_CALCUTTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Krasnoyarsk")),
        tz: &crate::timezones::ASIA_KRASNOYARSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kuala_Lumpur")),
        tz: &crate::timezones::ASIA_KUALA_LUMPUR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kuching")),
        tz: &crate::timezones::ASIA_BRUNEI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Kuwait")),
        tz: &crate::timezones::ANTARCTICA_SYOWA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Macao")),
        tz: &crate::timezones::ASIA_MACAO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Macau")),
        tz: &crate::timezones::ASIA_MACAO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Magadan")),
        tz: &crate::timezones::ASIA_MAGADAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Makassar")),
        tz: &crate::timezones::ASIA_MAKASSAR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Manila")),
        tz: &crate::timezones::ASIA_MANILA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Muscat")),
        tz: &crate::timezones::ASIA_DUBAI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Nicosia")),
        tz: &crate::timezones::ASIA_NICOSIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Novokuznetsk")),
        tz: &crate::timezones::ASIA_NOVOKUZNETSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Novosibirsk")),
        tz: &crate::timezones::ASIA_NOVOSIBIRSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Omsk")),
        tz: &crate::timezones::ASIA_OMSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Oral")),
        tz: &crate::timezones::ASIA_ORAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Phnom_Penh")),
        tz: &crate::timezones::ASIA_BANGKOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Pontianak")),
        tz: &crate::timezones::ASIA_PONTIANAK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Pyongyang")),
        tz: &crate::timezones::ASIA_PYONGYANG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Qatar")),
        tz: &crate::timezones::ASIA_BAHRAIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Qostanay")),
        tz: &crate::timezones::ASIA_QOSTANAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Qyzylorda")),
        tz: &crate::timezones::ASIA_QYZYLORDA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Rangoon")),
        tz: &crate::timezones::ASIA_RANGOON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Riyadh")),
        tz: &crate::timezones::ANTARCTICA_SYOWA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Saigon")),
        tz: &crate::timezones::ASIA_HO_CHI_MINH,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Sakhalin")),
        tz: &crate::timezones::ASIA_SAKHALIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Samarkand")),
        tz: &crate::timezones::ASIA_SAMARKAND,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Seoul")),
        tz: &crate::timezones::ASIA_SEOUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Shanghai")),
        tz: &crate::timezones::ASIA_CHONGQING,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Singapore")),
        tz: &crate::timezones::ASIA_KUALA_LUMPUR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Srednekolymsk")),
        tz: &crate::timezones::ASIA_SREDNEKOLYMSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Taipei")),
        tz: &crate::timezones::ASIA_TAIPEI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tashkent")),
        tz: &crate::timezones::ASIA_TASHKENT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tbilisi")),
        tz: &crate::timezones::ASIA_TBILISI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tehran")),
        tz: &crate::timezones::ASIA_TEHRAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tel_Aviv")),
        tz: &crate::timezones::ASIA_JERUSALEM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Thimbu")),
        tz: &crate::timezones::ASIA_THIMBU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Thimphu")),
        tz: &crate::timezones::ASIA_THIMBU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tokyo")),
        tz: &crate::timezones::ASIA_TOKYO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Tomsk")),
        tz: &crate::timezones::ASIA_TOMSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ujung_Pandang")),
        tz: &crate::timezones::ASIA_MAKASSAR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ulaanbaatar")),
        tz: &crate::timezones::ASIA_CHOIBALSAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ulan_Bator")),
        tz: &crate::timezones::ASIA_CHOIBALSAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Urumqi")),
        tz: &crate::timezones::ASIA_KASHGAR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Ust-Nera")),
        tz: &crate::timezones::ASIA_UST_MINUS_NERA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Vientiane")),
        tz: &crate::timezones::ASIA_BANGKOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Vladivostok")),
        tz: &crate::timezones::ASIA_VLADIVOSTOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Yakutsk")),
        tz: &crate::timezones::ASIA_YAKUTSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Yangon")),
        tz: &crate::timezones::ASIA_RANGOON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Yekaterinburg")),
        tz: &crate::timezones::ASIA_YEKATERINBURG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Asia/Yerevan")),
        tz: &crate::timezones::ASIA_YEREVAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Azores")),
        tz: &crate::timezones::ATLANTIC_AZORES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Bermuda")),
        tz: &crate::timezones::ATLANTIC_BERMUDA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Canary")),
        tz: &crate::timezones::ATLANTIC_CANARY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Cape_Verde")),
        tz: &crate::timezones::ATLANTIC_CAPE_VERDE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Faeroe")),
        tz: &crate::timezones::ATLANTIC_FAEROE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Faroe")),
        tz: &crate::timezones::ATLANTIC_FAEROE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Jan_Mayen")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Madeira")),
        tz: &crate::timezones::ATLANTIC_MADEIRA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Reykjavik")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/South_Georgia")),
        tz: &crate::timezones::ATLANTIC_SOUTH_GEORGIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/St_Helena")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Atlantic/Stanley")),
        tz: &crate::timezones::ATLANTIC_STANLEY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/ACT")),
        tz: &crate::timezones::AUSTRALIA_ACT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Adelaide")),
        tz: &crate::timezones::AUSTRALIA_ADELAIDE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Brisbane")),
        tz: &crate::timezones::AUSTRALIA_BRISBANE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Broken_Hill")),
        tz: &crate::timezones::AUSTRALIA_BROKEN_HILL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Canberra")),
        tz: &crate::timezones::AUSTRALIA_ACT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Currie")),
        tz: &crate::timezones::AUSTRALIA_CURRIE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Darwin")),
        tz: &crate::timezones::AUSTRALIA_DARWIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Eucla")),
        tz: &crate::timezones::AUSTRALIA_EUCLA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Hobart")),
        tz: &crate::timezones::AUSTRALIA_CURRIE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/LHI")),
        tz: &crate::timezones::AUSTRALIA_LHI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Lindeman")),
        tz: &crate::timezones::AUSTRALIA_LINDEMAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Lord_Howe")),
        tz: &crate::timezones::AUSTRALIA_LHI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Melbourne")),
        tz: &crate::timezones::AUSTRALIA_MELBOURNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/NSW")),
        tz: &crate::timezones::AUSTRALIA_ACT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/North")),
        tz: &crate::timezones::AUSTRALIA_DARWIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Perth")),
        tz: &crate::timezones::AUSTRALIA_PERTH,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Queensland")),
        tz: &crate::timezones::AUSTRALIA_BRISBANE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/South")),
        tz: &crate::timezones::AUSTRALIA_ADELAIDE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Sydney")),
        tz: &crate::timezones::AUSTRALIA_ACT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Tasmania")),
        tz: &crate::timezones::AUSTRALIA_CURRIE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Victoria")),
        tz: &crate::timezones::AUSTRALIA_MELBOURNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/West")),
        tz: &crate::timezones::AUSTRALIA_PERTH,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Australia/Yancowinna")),
        tz: &crate::timezones::AUSTRALIA_BROKEN_HILL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Brazil/Acre")),
        tz: &crate::timezones::AMERICA_PORTO_ACRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Brazil/DeNoronha")),
        tz: &crate::timezones::AMERICA_NORONHA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Brazil/East")),
        tz: &crate::timezones::AMERICA_SAO_PAULO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Brazil/West")),
        tz: &crate::timezones::AMERICA_MANAUS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("CET")),
        tz: &crate::timezones::CET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("CST6CDT")),
        tz: &crate::timezones::AMERICA_CHICAGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Atlantic")),
        tz: &crate::timezones::AMERICA_HALIFAX,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Central")),
        tz: &crate::timezones::AMERICA_RAINY_RIVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Eastern")),
        tz: &crate::timezones::AMERICA_MONTREAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Mountain")),
        tz: &crate::timezones::AMERICA_EDMONTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Newfoundland")),
        tz: &crate::timezones::AMERICA_ST_JOHNS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Pacific")),
        tz: &crate::timezones::AMERICA_VANCOUVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Saskatchewan")),
        tz: &crate::timezones::AMERICA_REGINA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Canada/Yukon")),
        tz: &crate::timezones::AMERICA_WHITEHORSE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Chile/Continental")),
        tz: &crate::timezones::AMERICA_SANTIAGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Chile/EasterIsland")),
        tz: &crate::timezones::CHILE_EASTERISLAND,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Cuba")),
        tz: &crate::timezones::AMERICA_HAVANA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("EET")),
        tz: &crate::timezones::EET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("EST")),
        tz: &crate::timezones::AMERICA_ATIKOKAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("EST5EDT")),
        tz: &crate::timezones::AMERICA_NEW_YORK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Egypt")),
        tz: &crate::timezones::AFRICA_CAIRO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Eire")),
        tz: &crate::timezones::EIRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+1")),
        tz: &crate::timezones::ETC_GMT_PLUS_1,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+10")),
        tz: &crate::timezones::ETC_GMT_PLUS_10,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+11")),
        tz: &crate::timezones::ETC_GMT_PLUS_11,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+12")),
        tz: &crate::timezones::ETC_GMT_PLUS_12,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+2")),
        tz: &crate::timezones::ETC_GMT_PLUS_2,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+3")),
        tz: &crate::timezones::ETC_GMT_PLUS_3,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+4")),
        tz: &crate::timezones::ETC_GMT_PLUS_4,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+5")),
        tz: &crate::timezones::ETC_GMT_PLUS_5,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+6")),
        tz: &crate::timezones::ETC_GMT_PLUS_6,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+7")),
        tz: &crate::timezones::ETC_GMT_PLUS_7,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+8")),
        tz: &crate::timezones::ETC_GMT_PLUS_8,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT+9")),
        tz: &crate::timezones::ETC_GMT_PLUS_9,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-1")),
        tz: &crate::timezones::ETC_GMT_MINUS_1,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-10")),
        tz: &crate::timezones::ETC_GMT_MINUS_10,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-11")),
        tz: &crate::timezones::ETC_GMT_MINUS_11,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-12")),
        tz: &crate::timezones::ETC_GMT_MINUS_12,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-13")),
        tz: &crate::timezones::ETC_GMT_MINUS_13,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-14")),
        tz: &crate::timezones::ETC_GMT_MINUS_14,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-2")),
        tz: &crate::timezones::ETC_GMT_MINUS_2,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-3")),
        tz: &crate::timezones::ETC_GMT_MINUS_3,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-4")),
        tz: &crate::timezones::ETC_GMT_MINUS_4,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-5")),
        tz: &crate::timezones::ETC_GMT_MINUS_5,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-6")),
        tz: &crate::timezones::ETC_GMT_MINUS_6,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-7")),
        tz: &crate::timezones::ETC_GMT_MINUS_7,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-8")),
        tz: &crate::timezones::ETC_GMT_MINUS_8,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT-9")),
        tz: &crate::timezones::ETC_GMT_MINUS_9,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/GMT0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/Greenwich")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/UCT")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/UTC")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/Universal")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Etc/Zulu")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Amsterdam")),
        tz: &crate::timezones::CET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Andorra")),
        tz: &crate::timezones::EUROPE_ANDORRA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Astrakhan")),
        tz: &crate::timezones::EUROPE_ASTRAKHAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Athens")),
        tz: &crate::timezones::EET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Belfast")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Belgrade")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Berlin")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Bratislava")),
        tz: &crate::timezones::EUROPE_BRATISLAVA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Brussels")),
        tz: &crate::timezones::CET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Bucharest")),
        tz: &crate::timezones::EUROPE_BUCHAREST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Budapest")),
        tz: &crate::timezones::EUROPE_BUDAPEST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Busingen")),
        tz: &crate::timezones::EUROPE_BUSINGEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Chisinau")),
        tz: &crate::timezones::EUROPE_CHISINAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Copenhagen")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Dublin")),
        tz: &crate::timezones::EIRE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Gibraltar")),
        tz: &crate::timezones::EUROPE_GIBRALTAR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Guernsey")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Helsinki")),
        tz: &crate::timezones::EUROPE_HELSINKI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Isle_of_Man")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Istanbul")),
        tz: &crate::timezones::ASIA_ISTANBUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Jersey")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Kaliningrad")),
        tz: &crate::timezones::EUROPE_KALININGRAD,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Kiev")),
        tz: &crate::timezones::EUROPE_KIEV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Kirov")),
        tz: &crate::timezones::EUROPE_KIROV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Kyiv")),
        tz: &crate::timezones::EUROPE_KIEV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Lisbon")),
        tz: &crate::timezones::EUROPE_LISBON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Ljubljana")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/London")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Luxembourg")),
        tz: &crate::timezones::CET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Madrid")),
        tz: &crate::timezones::EUROPE_MADRID,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Malta")),
        tz: &crate::timezones::EUROPE_MALTA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Mariehamn")),
        tz: &crate::timezones::EUROPE_HELSINKI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Minsk")),
        tz: &crate::timezones::EUROPE_MINSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Monaco")),
        tz: &crate::timezones::EUROPE_MONACO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Moscow")),
        tz: &crate::timezones::EUROPE_MOSCOW,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Nicosia")),
        tz: &crate::timezones::ASIA_NICOSIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Oslo")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Paris")),
        tz: &crate::timezones::EUROPE_MONACO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Podgorica")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Prague")),
        tz: &crate::timezones::EUROPE_BRATISLAVA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Riga")),
        tz: &crate::timezones::EUROPE_RIGA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Rome")),
        tz: &crate::timezones::EUROPE_ROME,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Samara")),
        tz: &crate::timezones::EUROPE_SAMARA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/San_Marino")),
        tz: &crate::timezones::EUROPE_ROME,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Sarajevo")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Saratov")),
        tz: &crate::timezones::EUROPE_SARATOV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Simferopol")),
        tz: &crate::timezones::EUROPE_SIMFEROPOL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Skopje")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Sofia")),
        tz: &crate::timezones::EUROPE_SOFIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Stockholm")),
        tz: &crate::timezones::ARCTIC_LONGYEARBYEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Tallinn")),
        tz: &crate::timezones::EUROPE_TALLINN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Tirane")),
        tz: &crate::timezones::EUROPE_TIRANE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Tiraspol")),
        tz: &crate::timezones::EUROPE_CHISINAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Ulyanovsk")),
        tz: &crate::timezones::EUROPE_ULYANOVSK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Uzhgorod")),
        tz: &crate::timezones::EUROPE_KIEV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Vaduz")),
        tz: &crate::timezones::EUROPE_BUSINGEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Vatican")),
        tz: &crate::timezones::EUROPE_ROME,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Vienna")),
        tz: &crate::timezones::EUROPE_VIENNA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Vilnius")),
        tz: &crate::timezones::EUROPE_VILNIUS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Volgograd")),
        tz: &crate::timezones::EUROPE_VOLGOGRAD,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Warsaw")),
        tz: &crate::timezones::EUROPE_WARSAW,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Zagreb")),
        tz: &crate::timezones::EUROPE_BELGRADE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Zaporozhye")),
        tz: &crate::timezones::EUROPE_KIEV,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Europe/Zurich")),
        tz: &crate::timezones::EUROPE_BUSINGEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Factory")),
        tz: &crate::timezones::FACTORY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GB")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GB-Eire")),
        tz: &crate::timezones::EUROPE_BELFAST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GMT")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GMT+0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GMT-0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("GMT0")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Greenwich")),
        tz: &crate::timezones::ETC_GMT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("HST")),
        tz: &crate::timezones::HST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Hongkong")),
        tz: &crate::timezones::ASIA_HONG_KONG,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Iceland")),
        tz: &crate::timezones::AFRICA_ABIDJAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Antananarivo")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Chagos")),
        tz: &crate::timezones::INDIAN_CHAGOS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Christmas")),
        tz: &crate::timezones::ASIA_BANGKOK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Cocos")),
        tz: &crate::timezones::ASIA_RANGOON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Comoro")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Kerguelen")),
        tz: &crate::timezones::INDIAN_KERGUELEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Mahe")),
        tz: &crate::timezones::ASIA_DUBAI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Maldives")),
        tz: &crate::timezones::INDIAN_KERGUELEN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Mauritius")),
        tz: &crate::timezones::INDIAN_MAURITIUS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Mayotte")),
        tz: &crate::timezones::AFRICA_ADDIS_ABABA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Indian/Reunion")),
        tz: &crate::timezones::ASIA_DUBAI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Iran")),
        tz: &crate::timezones::ASIA_TEHRAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Israel")),
        tz: &crate::timezones::ASIA_JERUSALEM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Jamaica")),
        tz: &crate::timezones::AMERICA_JAMAICA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Japan")),
        tz: &crate::timezones::ASIA_TOKYO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Kwajalein")),
        tz: &crate::timezones::KWAJALEIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Libya")),
        tz: &crate::timezones::AFRICA_TRIPOLI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("MET")),
        tz: &crate::timezones::CET,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("MST")),
        tz: &crate::timezones::AMERICA_CRESTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("MST7MDT")),
        tz: &crate::timezones::AMERICA_DENVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Mexico/BajaNorte")),
        tz: &crate::timezones::AMERICA_ENSENADA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Mexico/BajaSur")),
        tz: &crate::timezones::AMERICA_MAZATLAN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Mexico/General")),
        tz: &crate::timezones::AMERICA_MEXICO_CITY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("NZ")),
        tz: &crate::timezones::ANTARCTICA_MCMURDO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("NZ-CHAT")),
        tz: &crate::timezones::NZ_MINUS_CHAT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Navajo")),
        tz: &crate::timezones::AMERICA_DENVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("PRC")),
        tz: &crate::timezones::ASIA_CHONGQING,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("PST8PDT")),
        tz: &crate::timezones::AMERICA_LOS_ANGELES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Apia")),
        tz: &crate::timezones::PACIFIC_APIA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Auckland")),
        tz: &crate::timezones::ANTARCTICA_MCMURDO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Bougainville")),
        tz: &crate::timezones::PACIFIC_BOUGAINVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Chatham")),
        tz: &crate::timezones::NZ_MINUS_CHAT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Chuuk")),
        tz: &crate::timezones::ANTARCTICA_DUMONTDURVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Easter")),
        tz: &crate::timezones::CHILE_EASTERISLAND,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Efate")),
        tz: &crate::timezones::PACIFIC_EFATE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Enderbury")),
        tz: &crate::timezones::PACIFIC_ENDERBURY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Fakaofo")),
        tz: &crate::timezones::PACIFIC_FAKAOFO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Fiji")),
        tz: &crate::timezones::PACIFIC_FIJI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Funafuti")),
        tz: &crate::timezones::PACIFIC_FUNAFUTI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Galapagos")),
        tz: &crate::timezones::PACIFIC_GALAPAGOS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Gambier")),
        tz: &crate::timezones::PACIFIC_GAMBIER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Guadalcanal")),
        tz: &crate::timezones::PACIFIC_GUADALCANAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Guam")),
        tz: &crate::timezones::PACIFIC_GUAM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Honolulu")),
        tz: &crate::timezones::HST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Johnston")),
        tz: &crate::timezones::HST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Kanton")),
        tz: &crate::timezones::PACIFIC_ENDERBURY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Kiritimati")),
        tz: &crate::timezones::PACIFIC_KIRITIMATI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Kosrae")),
        tz: &crate::timezones::PACIFIC_KOSRAE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Kwajalein")),
        tz: &crate::timezones::KWAJALEIN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Majuro")),
        tz: &crate::timezones::PACIFIC_FUNAFUTI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Marquesas")),
        tz: &crate::timezones::PACIFIC_MARQUESAS,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Midway")),
        tz: &crate::timezones::PACIFIC_MIDWAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Nauru")),
        tz: &crate::timezones::PACIFIC_NAURU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Niue")),
        tz: &crate::timezones::PACIFIC_NIUE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Norfolk")),
        tz: &crate::timezones::PACIFIC_NORFOLK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Noumea")),
        tz: &crate::timezones::PACIFIC_NOUMEA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Pago_Pago")),
        tz: &crate::timezones::PACIFIC_MIDWAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Palau")),
        tz: &crate::timezones::PACIFIC_PALAU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Pitcairn")),
        tz: &crate::timezones::PACIFIC_PITCAIRN,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Pohnpei")),
        tz: &crate::timezones::PACIFIC_GUADALCANAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Ponape")),
        tz: &crate::timezones::PACIFIC_GUADALCANAL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Port_Moresby")),
        tz: &crate::timezones::ANTARCTICA_DUMONTDURVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Rarotonga")),
        tz: &crate::timezones::PACIFIC_RAROTONGA,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Saipan")),
        tz: &crate::timezones::PACIFIC_GUAM,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Samoa")),
        tz: &crate::timezones::PACIFIC_MIDWAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Tahiti")),
        tz: &crate::timezones::PACIFIC_TAHITI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Tarawa")),
        tz: &crate::timezones::PACIFIC_FUNAFUTI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Tongatapu")),
        tz: &crate::timezones::PACIFIC_TONGATAPU,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Truk")),
        tz: &crate::timezones::ANTARCTICA_DUMONTDURVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Wake")),
        tz: &crate::timezones::PACIFIC_FUNAFUTI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Wallis")),
        tz: &crate::timezones::PACIFIC_FUNAFUTI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Pacific/Yap")),
        tz: &crate::timezones::ANTARCTICA_DUMONTDURVILLE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Poland")),
        tz: &crate::timezones::EUROPE_WARSAW,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Portugal")),
        tz: &crate::timezones::EUROPE_LISBON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("ROC")),
        tz: &crate::timezones::ASIA_TAIPEI,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("ROK")),
        tz: &crate::timezones::ASIA_SEOUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Singapore")),
        tz: &crate::timezones::ASIA_KUALA_LUMPUR,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Turkey")),
        tz: &crate::timezones::ASIA_ISTANBUL,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("UCT")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Alaska")),
        tz: &crate::timezones::AMERICA_ANCHORAGE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Aleutian")),
        tz: &crate::timezones::AMERICA_ADAK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Arizona")),
        tz: &crate::timezones::AMERICA_CRESTON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Central")),
        tz: &crate::timezones::AMERICA_CHICAGO,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/East-Indiana")),
        tz: &crate::timezones::AMERICA_FORT_WAYNE,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Eastern")),
        tz: &crate::timezones::AMERICA_NEW_YORK,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Hawaii")),
        tz: &crate::timezones::HST,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Indiana-Starke")),
        tz: &crate::timezones::AMERICA_INDIANA_KNOX,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Michigan")),
        tz: &crate::timezones::AMERICA_DETROIT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Mountain")),
        tz: &crate::timezones::AMERICA_DENVER,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Pacific")),
        tz: &crate::timezones::AMERICA_LOS_ANGELES,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("US/Samoa")),
        tz: &crate::timezones::PACIFIC_MIDWAY,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("UTC")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Universal")),
        tz: &crate::timezones::ETC_UCT,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("W-SU")),
        tz: &crate::timezones::EUROPE_MOSCOW,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("WET")),
        tz: &crate::timezones::EUROPE_LISBON,
    },
    jcore::tz::tzif::MaybeNamedTimeZone {
        name: Some(jcore::util::SmallStr::statik("Zulu")),
        tz: &crate::timezones::ETC_UCT,
    },
];
