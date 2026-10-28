import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A9

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows11993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11993 = true := by
  rw [show D2M8K2.u11993 = KTree.node D2M8K2.t12000 (nat_lit 25581698) (nat_lit 4123374192) (nat_lit 0) D2M8K2.t12001 from rfl, allE_node, rows12000, irow11993, rows12001]
  all_goals rfl

theorem atot11993 : totK PD2M8K2 D2M8K2.u11993 = [0, 398229015134, 938787044629, 431423986467, 27914443105, 0, 0, 0] := by
  rw [show D2M8K2.u11993 = KTree.node D2M8K2.t12000 (nat_lit 25581698) (nat_lit 4123374192) (nat_lit 0) D2M8K2.t12001 from rfl, totK_node, tot12000, tot12001]
  decide +kernel

theorem arows11994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11994 = true := by
  rw [show D2M8K2.u11994 = KTree.node D2M8K2.t12002 (nat_lit 25583176) (nat_lit 2128665925) (nat_lit 0) D2M8K2.t12003 from rfl, allE_node, rows12002, irow11994, rows12003]
  all_goals rfl

theorem atot11994 : totK PD2M8K2 D2M8K2.u11994 = [0, 106853892906, 740031927836, 782809677641, 119596009665, 1095107716, 0, 0] := by
  rw [show D2M8K2.u11994 = KTree.node D2M8K2.t12002 (nat_lit 25583176) (nat_lit 2128665925) (nat_lit 0) D2M8K2.t12003 from rfl, totK_node, tot12002, tot12003]
  decide +kernel

theorem arows11996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11996 = true := by
  rw [show D2M8K2.u11996 = KTree.node D2M8K2.t12004 (nat_lit 25588952) (nat_lit 3194713555) (nat_lit 0) D2M8K2.t12005 from rfl, allE_node, rows12004, irow11996, rows12005]
  all_goals rfl

theorem atot11996 : totK PD2M8K2 D2M8K2.u11996 = [308784744087, 784037673931, 403673973068, 176526402374, 81046118049, 3882006667, 0, 0] := by
  rw [show D2M8K2.u11996 = KTree.node D2M8K2.t12004 (nat_lit 25588952) (nat_lit 3194713555) (nat_lit 0) D2M8K2.t12005 from rfl, totK_node, tot12004, tot12005]
  decide +kernel

theorem arows11997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11997 = true := by
  rw [show D2M8K2.u11997 = KTree.node D2M8K2.t12006 (nat_lit 25590548) (nat_lit 3019407853) (nat_lit 0) D2M8K2.t12007 from rfl, allE_node, rows12006, irow11997, rows12007]
  all_goals rfl

theorem atot11997 : totK PD2M8K2 D2M8K2.u11997 = [125330033888, 676114145953, 848132928095, 153641623143, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11997 = KTree.node D2M8K2.t12006 (nat_lit 25590548) (nat_lit 3019407853) (nat_lit 0) D2M8K2.t12007 from rfl, totK_node, tot12006, tot12007]
  decide +kernel

theorem arows12000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12000 = true := by
  rw [show D2M8K2.u12000 = KTree.node D2M8K2.t12008 (nat_lit 25592646) (nat_lit 3849525874) (nat_lit 0) D2M8K2.t12009 from rfl, allE_node, rows12008, irow12000, rows12009]
  all_goals rfl

theorem atot12000 : totK PD2M8K2 D2M8K2.u12000 = [370533709805, 939253905520, 496473535293, 40476251394, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12000 = KTree.node D2M8K2.t12008 (nat_lit 25592646) (nat_lit 3849525874) (nat_lit 0) D2M8K2.t12009 from rfl, totK_node, tot12008, tot12009]
  decide +kernel

theorem arows12001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12001 = true := by
  rw [show D2M8K2.u12001 = KTree.node D2M8K2.t12010 (nat_lit 25594184) (nat_lit 3367753302) (nat_lit 0) D2M8K2.t12011 from rfl, allE_node, rows12010, irow12001, rows12011]
  all_goals rfl

theorem atot12001 : totK PD2M8K2 D2M8K2.u12001 = [0, 406278054877, 940980256746, 443381645018, 30749515097, 0, 0, 0] := by
  rw [show D2M8K2.u12001 = KTree.node D2M8K2.t12010 (nat_lit 25594184) (nat_lit 3367753302) (nat_lit 0) D2M8K2.t12011 from rfl, totK_node, tot12010, tot12011]
  decide +kernel

theorem arows12003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12003 = true := by
  rw [show D2M8K2.u12003 = KTree.node D2M8K2.t12012 (nat_lit 25598982) (nat_lit 3798507859) (nat_lit 0) D2M8K2.t12013 from rfl, allE_node, rows12012, irow12003, rows12013]
  all_goals rfl

theorem atot12003 : totK PD2M8K2 D2M8K2.u12003 = [318059220318, 798457368041, 557562979230, 137378117136, 6804944647, 0, 0, 0] := by
  rw [show D2M8K2.u12003 = KTree.node D2M8K2.t12012 (nat_lit 25598982) (nat_lit 3798507859) (nat_lit 0) D2M8K2.t12013 from rfl, totK_node, tot12012, tot12013]
  decide +kernel

theorem arows12004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12004 = true := by
  rw [show D2M8K2.u12004 = KTree.node D2M8K2.t12014 (nat_lit 25600459) (nat_lit 1599363829) (nat_lit 0) D2M8K2.t12015 from rfl, allE_node, rows12014, irow12004, rows12015]
  all_goals rfl

theorem atot12004 : totK PD2M8K2 D2M8K2.u12004 = [107587333398, 636830389512, 820050631042, 218592114502, 9664716404, 0, 0, 0] := by
  rw [show D2M8K2.u12004 = KTree.node D2M8K2.t12014 (nat_lit 25600459) (nat_lit 1599363829) (nat_lit 0) D2M8K2.t12015 from rfl, totK_node, tot12014, tot12015]
  decide +kernel

theorem arows12008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12008 = true := by
  rw [show D2M8K2.u12008 = KTree.node D2M8K2.t12016 (nat_lit 25605775) (nat_lit 1870894709) (nat_lit 0) D2M8K2.t12017 from rfl, allE_node, rows12016, irow12008, rows12017]
  all_goals rfl

theorem atot12008 : totK PD2M8K2 D2M8K2.u12008 = [267638374850, 795262137986, 625619011220, 123743918321, 3579068459, 0, 0, 0] := by
  rw [show D2M8K2.u12008 = KTree.node D2M8K2.t12016 (nat_lit 25605775) (nat_lit 1870894709) (nat_lit 0) D2M8K2.t12017 from rfl, totK_node, tot12016, tot12017]
  decide +kernel

theorem arows12009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12009 = true := by
  rw [show D2M8K2.u12009 = KTree.node D2M8K2.t12018 (nat_lit 25607252) (nat_lit 2950984232) (nat_lit 0) D2M8K2.t12019 from rfl, allE_node, rows12018, irow12009, rows12019]
  all_goals rfl

theorem atot12009 : totK PD2M8K2 D2M8K2.u12009 = [157134559685, 681897150348, 779846636422, 184128561025, 3346911662, 0, 0, 0] := by
  rw [show D2M8K2.u12009 = KTree.node D2M8K2.t12018 (nat_lit 25607252) (nat_lit 2950984232) (nat_lit 0) D2M8K2.t12019 from rfl, totK_node, tot12018, tot12019]
  decide +kernel

theorem arows12011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12011 = true := by
  rw [show D2M8K2.u12011 = KTree.node D2M8K2.t12020 (nat_lit 25608954) (nat_lit 3336112379) (nat_lit 0) D2M8K2.t12021 from rfl, allE_node, rows12020, irow12011, rows12021]
  all_goals rfl

theorem atot12011 : totK PD2M8K2 D2M8K2.u12011 = [0, 396604853789, 950416661775, 413431495983, 22416853141, 0, 0, 0] := by
  rw [show D2M8K2.u12011 = KTree.node D2M8K2.t12020 (nat_lit 25608954) (nat_lit 3336112379) (nat_lit 0) D2M8K2.t12021 from rfl, totK_node, tot12020, tot12021]
  decide +kernel

theorem arows12012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12012 = true := by
  rw [show D2M8K2.u12012 = KTree.node D2M8K2.t12022 (nat_lit 25610602) (nat_lit 3971632560) (nat_lit 0) D2M8K2.t12023 from rfl, allE_node, rows12022, irow12012, rows12023]
  all_goals rfl

theorem atot12012 : totK PD2M8K2 D2M8K2.u12012 = [0, 179208208531, 759325681950, 710208427109, 99026585797, 1310285577, 0, 0] := by
  rw [show D2M8K2.u12012 = KTree.node D2M8K2.t12022 (nat_lit 25610602) (nat_lit 3971632560) (nat_lit 0) D2M8K2.t12023 from rfl, totK_node, tot12022, tot12023]
  decide +kernel

theorem arows12015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12015 = true := by
  rw [show D2M8K2.u12015 = KTree.node D2M8K2.t12024 (nat_lit 25612980) (nat_lit 1178301025) (nat_lit 0) D2M8K2.t12025 from rfl, allE_node, rows12024, irow12015, rows12025]
  all_goals rfl

theorem atot12015 : totK PD2M8K2 D2M8K2.u12015 = [0, 293657815830, 852302437494, 623541813981, 60855394236, 0, 0, 0] := by
  rw [show D2M8K2.u12015 = KTree.node D2M8K2.t12024 (nat_lit 25612980) (nat_lit 1178301025) (nat_lit 0) D2M8K2.t12025 from rfl, totK_node, tot12024, tot12025]
  decide +kernel

theorem arows12016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12016 = true := by
  rw [show D2M8K2.u12016 = KTree.node D2M8K2.t12026 (nat_lit 25619473) (nat_lit 1557258648) (nat_lit 0) D2M8K2.t12027 from rfl, allE_node, rows12026, irow12016, rows12027]
  all_goals rfl

theorem atot12016 : totK PD2M8K2 D2M8K2.u12016 = [0, 376971720732, 941649411039, 465561345578, 35517778840, 0, 0, 0] := by
  rw [show D2M8K2.u12016 = KTree.node D2M8K2.t12026 (nat_lit 25619473) (nat_lit 1557258648) (nat_lit 0) D2M8K2.t12027 from rfl, totK_node, tot12026, tot12027]
  decide +kernel

theorem arows12018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12018 = true := by
  rw [show D2M8K2.u12018 = KTree.node D2M8K2.t12028 (nat_lit 25620994) (nat_lit 3992414094) (nat_lit 0) D2M8K2.t12029 from rfl, allE_node, rows12028, irow12018, rows12029]
  all_goals rfl

theorem atot12018 : totK PD2M8K2 D2M8K2.u12018 = [0, 160189047771, 740237705744, 751999648831, 118420391141, 2160984415, 0, 0] := by
  rw [show D2M8K2.u12018 = KTree.node D2M8K2.t12028 (nat_lit 25620994) (nat_lit 3992414094) (nat_lit 0) D2M8K2.t12029 from rfl, totK_node, tot12028, tot12029]
  decide +kernel

theorem arows12019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12019 = true := by
  rw [show D2M8K2.u12019 = KTree.node D2M8K2.t12030 (nat_lit 25626555) (nat_lit 3787378992) (nat_lit 0) D2M8K2.t12031 from rfl, allE_node, rows12030, irow12019, rows12031]
  all_goals rfl

theorem atot12019 : totK PD2M8K2 D2M8K2.u12019 = [0, 277321003449, 815982642870, 590548175998, 99745190092, 2770420231, 0, 0] := by
  rw [show D2M8K2.u12019 = KTree.node D2M8K2.t12030 (nat_lit 25626555) (nat_lit 3787378992) (nat_lit 0) D2M8K2.t12031 from rfl, totK_node, tot12030, tot12031]
  decide +kernel

theorem arows12027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12027 = true := by
  rw [show D2M8K2.u12027 = KTree.node D2M8K2.t12032 (nat_lit 25628024) (nat_lit 2297739096) (nat_lit 0) D2M8K2.t12033 from rfl, allE_node, rows12032, irow12027, rows12033]
  all_goals rfl

theorem atot12027 : totK PD2M8K2 D2M8K2.u12027 = [0, 149221269572, 687234227933, 763968186499, 177275694121, 4811815119, 0, 0] := by
  rw [show D2M8K2.u12027 = KTree.node D2M8K2.t12032 (nat_lit 25628024) (nat_lit 2297739096) (nat_lit 0) D2M8K2.t12033 from rfl, totK_node, tot12032, tot12033]
  decide +kernel

theorem arows12028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12028 = true := by
  rw [show D2M8K2.u12028 = KTree.node D2M8K2.t12034 (nat_lit 25629754) (nat_lit 3892781461) (nat_lit 0) D2M8K2.t12035 from rfl, allE_node, rows12034, irow12028, rows12035]
  all_goals rfl

theorem atot12028 : totK PD2M8K2 D2M8K2.u12028 = [0, 228941785813, 682591641551, 624504226650, 217240001768, 16939352947, 0, 0] := by
  rw [show D2M8K2.u12028 = KTree.node D2M8K2.t12034 (nat_lit 25629754) (nat_lit 3892781461) (nat_lit 0) D2M8K2.t12035 from rfl, totK_node, tot12034, tot12035]
  decide +kernel

theorem arows12030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12030 = true := by
  rw [show D2M8K2.u12030 = KTree.node D2M8K2.t12036 (nat_lit 25631261) (nat_lit 2283863316) (nat_lit 0) D2M8K2.t12037 from rfl, allE_node, rows12036, irow12030, rows12037]
  all_goals rfl

theorem atot12030 : totK PD2M8K2 D2M8K2.u12030 = [0, 200308193445, 767845223767, 692040530946, 116239888390, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12030 = KTree.node D2M8K2.t12036 (nat_lit 25631261) (nat_lit 2283863316) (nat_lit 0) D2M8K2.t12037 from rfl, totK_node, tot12036, tot12037]
  decide +kernel

theorem arows12031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12031 = true := by
  rw [show D2M8K2.u12031 = KTree.node D2M8K2.t12038 (nat_lit 25636752) (nat_lit 3736141441) (nat_lit 0) D2M8K2.t12039 from rfl, allE_node, rows12038, irow12031, rows12039]
  all_goals rfl

theorem atot12031 : totK PD2M8K2 D2M8K2.u12031 = [0, 255633637046, 846485376520, 632063673668, 58839116387, 0, 0, 0] := by
  rw [show D2M8K2.u12031 = KTree.node D2M8K2.t12038 (nat_lit 25636752) (nat_lit 3736141441) (nat_lit 0) D2M8K2.t12039 from rfl, totK_node, tot12038, tot12039]
  decide +kernel

theorem arows12034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12034 = true := by
  rw [show D2M8K2.u12034 = KTree.node D2M8K2.t12040 (nat_lit 25638969) (nat_lit 1836439462) (nat_lit 0) D2M8K2.t12041 from rfl, allE_node, rows12040, irow12034, rows12041]
  all_goals rfl

theorem atot12034 : totK PD2M8K2 D2M8K2.u12034 = [0, 156131278421, 737235749410, 771294577128, 114788492043, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12034 = KTree.node D2M8K2.t12040 (nat_lit 25638969) (nat_lit 1836439462) (nat_lit 0) D2M8K2.t12041 from rfl, totK_node, tot12040, tot12041]
  decide +kernel

theorem arows12035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12035 = true := by
  rw [show D2M8K2.u12035 = KTree.node D2M8K2.t12042 (nat_lit 25641225) (nat_lit 1850731021) (nat_lit 0) D2M8K2.t12043 from rfl, allE_node, rows12042, irow12035, rows12043]
  all_goals rfl

theorem atot12035 : totK PD2M8K2 D2M8K2.u12035 = [0, 334962797878, 895231714758, 523943670319, 43251055801, 0, 0, 0] := by
  rw [show D2M8K2.u12035 = KTree.node D2M8K2.t12042 (nat_lit 25641225) (nat_lit 1850731021) (nat_lit 0) D2M8K2.t12043 from rfl, totK_node, tot12042, tot12043]
  decide +kernel

theorem arows12037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12037 = true := by
  rw [show D2M8K2.u12037 = KTree.node D2M8K2.t12044 (nat_lit 25642898) (nat_lit 3584004288) (nat_lit 0) D2M8K2.t12045 from rfl, allE_node, rows12044, irow12037, rows12045]
  all_goals rfl

theorem atot12037 : totK PD2M8K2 D2M8K2.u12037 = [0, 75915933367, 505552065236, 878121005257, 292317880366, 13189998508, 0, 0] := by
  rw [show D2M8K2.u12037 = KTree.node D2M8K2.t12044 (nat_lit 25642898) (nat_lit 3584004288) (nat_lit 0) D2M8K2.t12045 from rfl, totK_node, tot12044, tot12045]
  decide +kernel

theorem arows12038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12038 = true := by
  rw [show D2M8K2.u12038 = KTree.node D2M8K2.t12046 (nat_lit 25644337) (nat_lit 1403630470) (nat_lit 0) D2M8K2.t12047 from rfl, allE_node, rows12046, irow12038, rows12047]
  all_goals rfl

theorem atot12038 : totK PD2M8K2 D2M8K2.u12038 = [0, 331541708481, 931021407772, 493344411858, 30539397491, 0, 0, 0] := by
  rw [show D2M8K2.u12038 = KTree.node D2M8K2.t12046 (nat_lit 25644337) (nat_lit 1403630470) (nat_lit 0) D2M8K2.t12047 from rfl, totK_node, tot12046, tot12047]
  decide +kernel

theorem arows12042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12042 = true := by
  rw [show D2M8K2.u12042 = KTree.node D2M8K2.t12048 (nat_lit 25646202) (nat_lit 3905709340) (nat_lit 0) D2M8K2.t12049 from rfl, allE_node, rows12048, irow12042, rows12049]
  all_goals rfl

theorem atot12042 : totK PD2M8K2 D2M8K2.u12042 = [0, 90796588535, 624039098798, 876974085754, 182825611978, 4917684815, 0, 0] := by
  rw [show D2M8K2.u12042 = KTree.node D2M8K2.t12048 (nat_lit 25646202) (nat_lit 3905709340) (nat_lit 0) D2M8K2.t12049 from rfl, totK_node, tot12048, tot12049]
  decide +kernel

theorem arows12043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12043 = true := by
  rw [show D2M8K2.u12043 = KTree.node D2M8K2.t12050 (nat_lit 25647996) (nat_lit 3166438693) (nat_lit 0) D2M8K2.t12051 from rfl, allE_node, rows12050, irow12043, rows12051]
  all_goals rfl

theorem atot12043 : totK PD2M8K2 D2M8K2.u12043 = [0, 291952518771, 842673665537, 590791670294, 70782720617, 0, 0, 0] := by
  rw [show D2M8K2.u12043 = KTree.node D2M8K2.t12050 (nat_lit 25647996) (nat_lit 3166438693) (nat_lit 0) D2M8K2.t12051 from rfl, totK_node, tot12050, tot12051]
  decide +kernel

theorem arows12045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12045 = true := by
  rw [show D2M8K2.u12045 = KTree.node D2M8K2.t12052 (nat_lit 25650172) (nat_lit 3271624560) (nat_lit 0) D2M8K2.t12053 from rfl, allE_node, rows12052, irow12045, rows12053]
  all_goals rfl

theorem atot12045 : totK PD2M8K2 D2M8K2.u12045 = [0, 0, 431709751829, 972239474726, 351611671618, 13851876900, 0, 0] := by
  rw [show D2M8K2.u12045 = KTree.node D2M8K2.t12052 (nat_lit 25650172) (nat_lit 3271624560) (nat_lit 0) D2M8K2.t12053 from rfl, totK_node, tot12052, tot12053]
  decide +kernel

theorem arows12046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12046 = true := by
  rw [show D2M8K2.u12046 = KTree.node D2M8K2.t12054 (nat_lit 25651686) (nat_lit 3793660679) (nat_lit 0) D2M8K2.t12055 from rfl, allE_node, rows12054, irow12046, rows12055]
  all_goals rfl

theorem atot12046 : totK PD2M8K2 D2M8K2.u12046 = [0, 0, 289215520760, 867954530330, 498990872745, 56695532495, 1310517177, 0] := by
  rw [show D2M8K2.u12046 = KTree.node D2M8K2.t12054 (nat_lit 25651686) (nat_lit 3793660679) (nat_lit 0) D2M8K2.t12055 from rfl, totK_node, tot12054, tot12055]
  decide +kernel

theorem arows12049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12049 = true := by
  rw [show D2M8K2.u12049 = KTree.node D2M8K2.t12056 (nat_lit 25657353) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t12057 from rfl, allE_node, rows12056, irow12049, rows12057]
  all_goals rfl

theorem atot12049 : totK PD2M8K2 D2M8K2.u12049 = [0, 0, 231024869940, 830528441777, 584034264612, 61502386540, 0, 0] := by
  rw [show D2M8K2.u12049 = KTree.node D2M8K2.t12056 (nat_lit 25657353) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t12057 from rfl, totK_node, tot12056, tot12057]
  decide +kernel

theorem arows12050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12050 = true := by
  rw [show D2M8K2.u12050 = KTree.node D2M8K2.t12058 (nat_lit 25661190) (nat_lit 3822535073) (nat_lit 0) D2M8K2.t12059 from rfl, allE_node, rows12058, irow12050, rows12059]
  all_goals rfl

theorem atot12050 : totK PD2M8K2 D2M8K2.u12050 = [0, 0, 425369336066, 959223957432, 370425259145, 15099382554, 0, 0] := by
  rw [show D2M8K2.u12050 = KTree.node D2M8K2.t12058 (nat_lit 25661190) (nat_lit 3822535073) (nat_lit 0) D2M8K2.t12059 from rfl, totK_node, tot12058, tot12059]
  decide +kernel

theorem arows12052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12052 = true := by
  rw [show D2M8K2.u12052 = KTree.node D2M8K2.t12060 (nat_lit 25664451) (nat_lit 762503820) (nat_lit 0) D2M8K2.t12061 from rfl, allE_node, rows12060, irow12052, rows12061]
  all_goals rfl

theorem atot12052 : totK PD2M8K2 D2M8K2.u12052 = [0, 0, 369433353808, 970368159088, 383636563366, 16205762792, 0, 0] := by
  rw [show D2M8K2.u12052 = KTree.node D2M8K2.t12060 (nat_lit 25664451) (nat_lit 762503820) (nat_lit 0) D2M8K2.t12061 from rfl, totK_node, tot12060, tot12061]
  decide +kernel

theorem arows12053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12053 = true := by
  rw [show D2M8K2.u12053 = KTree.node D2M8K2.t12062 (nat_lit 25667834) (nat_lit 3459057828) (nat_lit 0) D2M8K2.t12063 from rfl, allE_node, rows12062, irow12053, rows12063]
  all_goals rfl

theorem atot12053 : totK PD2M8K2 D2M8K2.u12053 = [0, 0, 410809318635, 949653210985, 384647107698, 17615883313, 0, 0] := by
  rw [show D2M8K2.u12053 = KTree.node D2M8K2.t12062 (nat_lit 25667834) (nat_lit 3459057828) (nat_lit 0) D2M8K2.t12063 from rfl, totK_node, tot12062, tot12063]
  decide +kernel

theorem arows12058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12058 = true := by
  rw [show D2M8K2.u12058 = KTree.node D2M8K2.t12064 (nat_lit 25675158) (nat_lit 3783726318) (nat_lit 0) D2M8K2.t12065 from rfl, allE_node, rows12064, irow12058, rows12065]
  all_goals rfl

theorem atot12058 : totK PD2M8K2 D2M8K2.u12058 = [0, 267455471707, 761808280359, 635417437680, 162525684350, 8863302705, 0, 0] := by
  rw [show D2M8K2.u12058 = KTree.node D2M8K2.t12064 (nat_lit 25675158) (nat_lit 3783726318) (nat_lit 0) D2M8K2.t12065 from rfl, totK_node, tot12064, tot12065]
  decide +kernel

theorem arows12059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12059 = true := by
  rw [show D2M8K2.u12059 = KTree.node D2M8K2.t12066 (nat_lit 25676669) (nat_lit 2281325512) (nat_lit 0) D2M8K2.t12067 from rfl, allE_node, rows12066, irow12059, rows12067]
  all_goals rfl

theorem atot12059 : totK PD2M8K2 D2M8K2.u12059 = [0, 174865245605, 647791135708, 694828333332, 271929018635, 25307930630, 0, 0] := by
  rw [show D2M8K2.u12059 = KTree.node D2M8K2.t12066 (nat_lit 25676669) (nat_lit 2281325512) (nat_lit 0) D2M8K2.t12067 from rfl, totK_node, tot12066, tot12067]
  decide +kernel

theorem arows12061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12061 = true := by
  rw [show D2M8K2.u12061 = KTree.node D2M8K2.t12068 (nat_lit 25677849) (nat_lit 1276862334) (nat_lit 0) D2M8K2.t12069 from rfl, allE_node, rows12068, irow12061, rows12069]
  all_goals rfl

theorem atot12061 : totK PD2M8K2 D2M8K2.u12061 = [0, 126464223337, 542209492945, 834989439053, 315723895586, 12192077010, 0, 0] := by
  rw [show D2M8K2.u12061 = KTree.node D2M8K2.t12068 (nat_lit 25677849) (nat_lit 1276862334) (nat_lit 0) D2M8K2.t12069 from rfl, totK_node, tot12068, tot12069]
  decide +kernel

theorem arows12062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12062 = true := by
  rw [show D2M8K2.u12062 = KTree.node D2M8K2.t12070 (nat_lit 25679690) (nat_lit 4200050348) (nat_lit 0) D2M8K2.t12071 from rfl, allE_node, rows12070, irow12062, rows12071]
  all_goals rfl

theorem atot12062 : totK PD2M8K2 D2M8K2.u12062 = [0, 200130710680, 776441914573, 697765444406, 140161559245, 4143089693, 0, 0] := by
  rw [show D2M8K2.u12062 = KTree.node D2M8K2.t12070 (nat_lit 25679690) (nat_lit 4200050348) (nat_lit 0) D2M8K2.t12071 from rfl, totK_node, tot12070, tot12071]
  decide +kernel

theorem arows12065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12065 = true := by
  rw [show D2M8K2.u12065 = KTree.node D2M8K2.t12072 (nat_lit 25681906) (nat_lit 3934122493) (nat_lit 0) D2M8K2.t12073 from rfl, allE_node, rows12072, irow12065, rows12073]
  all_goals rfl

theorem atot12065 : totK PD2M8K2 D2M8K2.u12065 = [0, 287574551533, 804731448456, 627035414243, 107744970485, 1227322468, 0, 0] := by
  rw [show D2M8K2.u12065 = KTree.node D2M8K2.t12072 (nat_lit 25681906) (nat_lit 3934122493) (nat_lit 0) D2M8K2.t12073 from rfl, totK_node, tot12072, tot12073]
  decide +kernel

theorem arows12066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12066 = true := by
  rw [show D2M8K2.u12066 = KTree.node D2M8K2.t12074 (nat_lit 25683366) (nat_lit 3749681023) (nat_lit 0) D2M8K2.t12075 from rfl, allE_node, rows12074, irow12066, rows12075]
  all_goals rfl

theorem atot12066 : totK PD2M8K2 D2M8K2.u12066 = [0, 136930472414, 650957418468, 771091277084, 211748033792, 9642442870, 0, 0] := by
  rw [show D2M8K2.u12066 = KTree.node D2M8K2.t12074 (nat_lit 25683366) (nat_lit 3749681023) (nat_lit 0) D2M8K2.t12075 from rfl, totK_node, tot12074, tot12075]
  decide +kernel

theorem arows12068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12068 = true := by
  rw [show D2M8K2.u12068 = KTree.node D2M8K2.t12076 (nat_lit 25685218) (nat_lit 3118198323) (nat_lit 0) D2M8K2.t12077 from rfl, allE_node, rows12076, irow12068, rows12077]
  all_goals rfl

theorem atot12068 : totK PD2M8K2 D2M8K2.u12068 = [0, 236038451305, 766269314556, 665625148096, 130905738118, 3540641832, 0, 0] := by
  rw [show D2M8K2.u12068 = KTree.node D2M8K2.t12076 (nat_lit 25685218) (nat_lit 3118198323) (nat_lit 0) D2M8K2.t12077 from rfl, totK_node, tot12076, tot12077]
  decide +kernel

theorem arows12069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12069 = true := by
  rw [show D2M8K2.u12069 = KTree.node D2M8K2.t12078 (nat_lit 25686736) (nat_lit 2851302346) (nat_lit 0) D2M8K2.t12079 from rfl, allE_node, rows12078, irow12069, rows12079]
  all_goals rfl

theorem atot12069 : totK PD2M8K2 D2M8K2.u12069 = [0, 177550997700, 805690829969, 756451070271, 82591691403, 0, 0, 0] := by
  rw [show D2M8K2.u12069 = KTree.node D2M8K2.t12078 (nat_lit 25686736) (nat_lit 2851302346) (nat_lit 0) D2M8K2.t12079 from rfl, totK_node, tot12078, tot12079]
  decide +kernel

theorem arows12073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12073 = true := by
  rw [show D2M8K2.u12073 = KTree.node D2M8K2.t12080 (nat_lit 25688930) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t12081 from rfl, allE_node, rows12080, irow12073, rows12081]
  all_goals rfl

theorem atot12073 : totK PD2M8K2 D2M8K2.u12073 = [0, 296403079267, 801197410807, 599054899004, 123254358943, 3880716147, 0, 0] := by
  rw [show D2M8K2.u12073 = KTree.node D2M8K2.t12080 (nat_lit 25688930) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t12081 from rfl, totK_node, tot12080, tot12081]
  decide +kernel

theorem arows12074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12074 = true := by
  rw [show D2M8K2.u12074 = KTree.node D2M8K2.t12082 (nat_lit 25690554) (nat_lit 3895382182) (nat_lit 0) D2M8K2.t12083 from rfl, allE_node, rows12082, irow12074, rows12083]
  all_goals rfl

theorem atot12074 : totK PD2M8K2 D2M8K2.u12074 = [0, 90526578066, 581173900010, 861354450545, 250789434307, 6235238167, 0, 0] := by
  rw [show D2M8K2.u12074 = KTree.node D2M8K2.t12082 (nat_lit 25690554) (nat_lit 3895382182) (nat_lit 0) D2M8K2.t12083 from rfl, totK_node, tot12082, tot12083]
  decide +kernel

theorem arows12076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12076 = true := by
  rw [show D2M8K2.u12076 = KTree.node D2M8K2.t12084 (nat_lit 25754804) (nat_lit 3555118837) (nat_lit 0) D2M8K2.t12085 from rfl, allE_node, rows12084, irow12076, rows12085]
  all_goals rfl

theorem atot12076 : totK PD2M8K2 D2M8K2.u12076 = [0, 327517158298, 820025231751, 478920701288, 133121827883, 11591256473, 0, 0] := by
  rw [show D2M8K2.u12076 = KTree.node D2M8K2.t12084 (nat_lit 25754804) (nat_lit 3555118837) (nat_lit 0) D2M8K2.t12085 from rfl, totK_node, tot12084, tot12085]
  decide +kernel

theorem arows12077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12077 = true := by
  rw [show D2M8K2.u12077 = KTree.node D2M8K2.t12086 (nat_lit 25756037) (nat_lit 1216940612) (nat_lit 0) D2M8K2.t12087 from rfl, allE_node, rows12086, irow12077, rows12087]
  all_goals rfl

theorem atot12077 : totK PD2M8K2 D2M8K2.u12077 = [0, 84236580386, 670077550487, 866130135134, 131569303150, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12077 = KTree.node D2M8K2.t12086 (nat_lit 25756037) (nat_lit 1216940612) (nat_lit 0) D2M8K2.t12087 from rfl, totK_node, tot12086, tot12087]
  decide +kernel

theorem arows12080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12080 = true := by
  rw [show D2M8K2.u12080 = KTree.node D2M8K2.t12088 (nat_lit 25758438) (nat_lit 3868185851) (nat_lit 0) D2M8K2.t12089 from rfl, allE_node, rows12088, irow12080, rows12089]
  all_goals rfl

theorem atot12080 : totK PD2M8K2 D2M8K2.u12080 = [0, 369796396239, 915306561434, 509588283914, 45556645415, 0, 0, 0] := by
  rw [show D2M8K2.u12080 = KTree.node D2M8K2.t12088 (nat_lit 25758438) (nat_lit 3868185851) (nat_lit 0) D2M8K2.t12089 from rfl, totK_node, tot12088, tot12089]
  decide +kernel

theorem arows12081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12081 = true := by
  rw [show D2M8K2.u12081 = KTree.node D2M8K2.t12090 (nat_lit 25759898) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t12091 from rfl, allE_node, rows12090, irow12081, rows12091]
  all_goals rfl

theorem atot12081 : totK PD2M8K2 D2M8K2.u12081 = [0, 53304886208, 506318996715, 861773941156, 348275513081, 23593757536, 0, 0] := by
  rw [show D2M8K2.u12081 = KTree.node D2M8K2.t12090 (nat_lit 25759898) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t12091 from rfl, totK_node, tot12090, tot12091]
  decide +kernel

theorem arows12083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12083 = true := by
  rw [show D2M8K2.u12083 = KTree.node D2M8K2.t12092 (nat_lit 25764636) (nat_lit 3509774347) (nat_lit 0) D2M8K2.t12093 from rfl, allE_node, rows12092, irow12083, rows12093]
  all_goals rfl

theorem atot12083 : totK PD2M8K2 D2M8K2.u12083 = [0, 269758578888, 721435017840, 625321455935, 192355044608, 6557415438, 0, 0] := by
  rw [show D2M8K2.u12083 = KTree.node D2M8K2.t12092 (nat_lit 25764636) (nat_lit 3509774347) (nat_lit 0) D2M8K2.t12093 from rfl, totK_node, tot12092, tot12093]
  decide +kernel

theorem arows12084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12084 = true := by
  rw [show D2M8K2.u12084 = KTree.node D2M8K2.t12094 (nat_lit 25766116) (nat_lit 2518079875) (nat_lit 0) D2M8K2.t12095 from rfl, allE_node, rows12094, irow12084, rows12095]
  all_goals rfl

theorem atot12084 : totK PD2M8K2 D2M8K2.u12084 = [0, 175730764912, 758301706210, 751150162481, 128851247479, 1198073392, 0, 0] := by
  rw [show D2M8K2.u12084 = KTree.node D2M8K2.t12094 (nat_lit 25766116) (nat_lit 2518079875) (nat_lit 0) D2M8K2.t12095 from rfl, totK_node, tot12094, tot12095]
  decide +kernel

theorem arows12090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12090 = true := by
  rw [show D2M8K2.u12090 = KTree.node D2M8K2.t12096 (nat_lit 25767779) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t12097 from rfl, allE_node, rows12096, irow12090, rows12097]
  all_goals rfl

theorem atot12090 : totK PD2M8K2 D2M8K2.u12090 = [0, 171277143297, 646553771865, 735138759551, 219155995059, 12052611869, 0, 0] := by
  rw [show D2M8K2.u12090 = KTree.node D2M8K2.t12096 (nat_lit 25767779) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t12097 from rfl, totK_node, tot12096, tot12097]
  decide +kernel

theorem arows12091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12091 = true := by
  rw [show D2M8K2.u12091 = KTree.node D2M8K2.t12098 (nat_lit 25769152) (nat_lit 3488826477) (nat_lit 0) D2M8K2.t12099 from rfl, allE_node, rows12098, irow12091, rows12099]
  all_goals rfl

theorem atot12091 : totK PD2M8K2 D2M8K2.u12091 = [0, 247424073658, 807772065884, 639615126614, 88664764353, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12091 = KTree.node D2M8K2.t12098 (nat_lit 25769152) (nat_lit 3488826477) (nat_lit 0) D2M8K2.t12099 from rfl, totK_node, tot12098, tot12099]
  decide +kernel

theorem arows12093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12093 = true := by
  rw [show D2M8K2.u12093 = KTree.node D2M8K2.t12100 (nat_lit 25771464) (nat_lit 3606661954) (nat_lit 0) D2M8K2.t12101 from rfl, allE_node, rows12100, irow12093, rows12101]
  all_goals rfl

theorem atot12093 : totK PD2M8K2 D2M8K2.u12093 = [0, 218100562819, 728271321925, 706084055483, 134134532401, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12093 = KTree.node D2M8K2.t12100 (nat_lit 25771464) (nat_lit 3606661954) (nat_lit 0) D2M8K2.t12101 from rfl, totK_node, tot12100, tot12101]
  decide +kernel

theorem arows12094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12094 = true := by
  rw [show D2M8K2.u12094 = KTree.node D2M8K2.t12102 (nat_lit 25773025) (nat_lit 1419479865) (nat_lit 0) D2M8K2.t12103 from rfl, allE_node, rows12102, irow12094, rows12103]
  all_goals rfl

theorem atot12094 : totK PD2M8K2 D2M8K2.u12094 = [0, 185228615791, 757785589620, 718592038767, 123221000375, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12094 = KTree.node D2M8K2.t12102 (nat_lit 25773025) (nat_lit 1419479865) (nat_lit 0) D2M8K2.t12103 from rfl, totK_node, tot12102, tot12103]
  decide +kernel

theorem arows12097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12097 = true := by
  rw [show D2M8K2.u12097 = KTree.node D2M8K2.t12104 (nat_lit 25774782) (nat_lit 3983798251) (nat_lit 0) D2M8K2.t12105 from rfl, allE_node, rows12104, irow12097, rows12105]
  all_goals rfl

theorem atot12097 : totK PD2M8K2 D2M8K2.u12097 = [0, 0, 384943075043, 952772927785, 381309938758, 18349103821, 0, 0] := by
  rw [show D2M8K2.u12097 = KTree.node D2M8K2.t12104 (nat_lit 25774782) (nat_lit 3983798251) (nat_lit 0) D2M8K2.t12105 from rfl, totK_node, tot12104, tot12105]
  decide +kernel

theorem arows12098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12098 = true := by
  rw [show D2M8K2.u12098 = KTree.node D2M8K2.t12106 (nat_lit 25776381) (nat_lit 1391988882) (nat_lit 0) D2M8K2.t12107 from rfl, allE_node, rows12106, irow12098, rows12107]
  all_goals rfl

theorem atot12098 : totK PD2M8K2 D2M8K2.u12098 = [0, 0, 202623259598, 785446274176, 631423892223, 89707485241, 1217496766, 0] := by
  rw [show D2M8K2.u12098 = KTree.node D2M8K2.t12106 (nat_lit 25776381) (nat_lit 1391988882) (nat_lit 0) D2M8K2.t12107 from rfl, totK_node, tot12106, tot12107]
  decide +kernel

theorem arows12100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12100 = true := by
  rw [show D2M8K2.u12100 = KTree.node D2M8K2.t12108 (nat_lit 25778839) (nat_lit 2324127606) (nat_lit 0) D2M8K2.t12109 from rfl, allE_node, rows12108, irow12100, rows12109]
  all_goals rfl

theorem atot12100 : totK PD2M8K2 D2M8K2.u12100 = [0, 0, 333369584983, 876905978355, 536953209851, 49306593886, 0, 0] := by
  rw [show D2M8K2.u12100 = KTree.node D2M8K2.t12108 (nat_lit 25778839) (nat_lit 2324127606) (nat_lit 0) D2M8K2.t12109 from rfl, totK_node, tot12108, tot12109]
  decide +kernel

theorem arows12101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12101 = true := by
  rw [show D2M8K2.u12101 = KTree.node D2M8K2.t12110 (nat_lit 25785464) (nat_lit 3831663796) (nat_lit 0) D2M8K2.t12111 from rfl, allE_node, rows12110, irow12101, rows12111]
  all_goals rfl

theorem atot12101 : totK PD2M8K2 D2M8K2.u12101 = [0, 0, 351514989066, 950143298518, 468596192757, 32678169994, 0, 0] := by
  rw [show D2M8K2.u12101 = KTree.node D2M8K2.t12110 (nat_lit 25785464) (nat_lit 3831663796) (nat_lit 0) D2M8K2.t12111 from rfl, totK_node, tot12110, tot12111]
  decide +kernel

theorem arows12105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12105 = true := by
  rw [show D2M8K2.u12105 = KTree.node D2M8K2.t12112 (nat_lit 25786955) (nat_lit 2774376777) (nat_lit 0) D2M8K2.t12113 from rfl, allE_node, rows12112, irow12105, rows12113]
  all_goals rfl

theorem atot12105 : totK PD2M8K2 D2M8K2.u12105 = [0, 0, 173269053777, 716474013043, 730464885257, 150044177197, 2318623666, 0] := by
  rw [show D2M8K2.u12105 = KTree.node D2M8K2.t12112 (nat_lit 25786955) (nat_lit 2774376777) (nat_lit 0) D2M8K2.t12113 from rfl, totK_node, tot12112, tot12113]
  decide +kernel

theorem arows12106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12106 = true := by
  rw [show D2M8K2.u12106 = KTree.node D2M8K2.t12114 (nat_lit 25788796) (nat_lit 2343296499) (nat_lit 0) D2M8K2.t12115 from rfl, allE_node, rows12114, irow12106, rows12115]
  all_goals rfl

theorem atot12106 : totK PD2M8K2 D2M8K2.u12106 = [0, 0, 234210689862, 753023317884, 569694773407, 145916304435, 10786826731, 0] := by
  rw [show D2M8K2.u12106 = KTree.node D2M8K2.t12114 (nat_lit 25788796) (nat_lit 2343296499) (nat_lit 0) D2M8K2.t12115 from rfl, totK_node, tot12114, tot12115]
  decide +kernel

theorem arows12108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12108 = true := by
  rw [show D2M8K2.u12108 = KTree.node D2M8K2.t12116 (nat_lit 25790409) (nat_lit 1836876593) (nat_lit 0) D2M8K2.t12117 from rfl, allE_node, rows12116, irow12108, rows12117]
  all_goals rfl

theorem atot12108 : totK PD2M8K2 D2M8K2.u12108 = [0, 0, 178718781984, 773279779375, 680192035750, 90948133812, 1032241984, 0] := by
  rw [show D2M8K2.u12108 = KTree.node D2M8K2.t12116 (nat_lit 25790409) (nat_lit 1836876593) (nat_lit 0) D2M8K2.t12117 from rfl, totK_node, tot12116, tot12117]
  decide +kernel

theorem arows12109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12109 = true := by
  rw [show D2M8K2.u12109 = KTree.node D2M8K2.t12118 (nat_lit 25792507) (nat_lit 2220107020) (nat_lit 0) D2M8K2.t12119 from rfl, allE_node, rows12118, irow12109, rows12119]
  all_goals rfl

theorem atot12109 : totK PD2M8K2 D2M8K2.u12109 = [0, 0, 329441131866, 825667136173, 499413658548, 89453154106, 3598673838, 0] := by
  rw [show D2M8K2.u12109 = KTree.node D2M8K2.t12118 (nat_lit 25792507) (nat_lit 2220107020) (nat_lit 0) D2M8K2.t12119 from rfl, totK_node, tot12118, tot12119]
  decide +kernel

theorem arows12112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12112 = true := by
  rw [show D2M8K2.u12112 = KTree.node D2M8K2.t12120 (nat_lit 25796217) (nat_lit 1840745792) (nat_lit 0) D2M8K2.t12121 from rfl, allE_node, rows12120, irow12112, rows12121]
  all_goals rfl

theorem atot12112 : totK PD2M8K2 D2M8K2.u12112 = [0, 318914202916, 800429486390, 521925450999, 136815957032, 9043051330, 0, 0] := by
  rw [show D2M8K2.u12112 = KTree.node D2M8K2.t12120 (nat_lit 25796217) (nat_lit 1840745792) (nat_lit 0) D2M8K2.t12121 from rfl, totK_node, tot12120, tot12121]
  decide +kernel

theorem arows12113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12113 = true := by
  rw [show D2M8K2.u12113 = KTree.node D2M8K2.t12122 (nat_lit 25797513) (nat_lit 1573081913) (nat_lit 0) D2M8K2.t12123 from rfl, allE_node, rows12122, irow12113, rows12123]
  all_goals rfl

theorem atot12113 : totK PD2M8K2 D2M8K2.u12113 = [0, 84364237255, 696449229773, 852541925536, 128839467056, 1310517177, 0, 0] := by
  rw [show D2M8K2.u12113 = KTree.node D2M8K2.t12122 (nat_lit 25797513) (nat_lit 1573081913) (nat_lit 0) D2M8K2.t12123 from rfl, totK_node, tot12122, tot12123]
  decide +kernel

theorem arows12115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12115 = true := by
  rw [show D2M8K2.u12115 = KTree.node D2M8K2.t12124 (nat_lit 25799883) (nat_lit 3451625294) (nat_lit 0) D2M8K2.t12125 from rfl, allE_node, rows12124, irow12115, rows12125]
  all_goals rfl

theorem atot12115 : totK PD2M8K2 D2M8K2.u12115 = [0, 368565758706, 916822541054, 508789829478, 46880418815, 0, 0, 0] := by
  rw [show D2M8K2.u12115 = KTree.node D2M8K2.t12124 (nat_lit 25799883) (nat_lit 3451625294) (nat_lit 0) D2M8K2.t12125 from rfl, totK_node, tot12124, tot12125]
  decide +kernel

theorem arows12116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12116 = true := by
  rw [show D2M8K2.u12116 = KTree.node D2M8K2.t12126 (nat_lit 25801412) (nat_lit 3340106819) (nat_lit 0) D2M8K2.t12127 from rfl, allE_node, rows12126, irow12116, rows12127]
  all_goals rfl

theorem atot12116 : totK PD2M8K2 D2M8K2.u12116 = [0, 49739141399, 512014051461, 908211272585, 335069356733, 15066332673, 0, 0] := by
  rw [show D2M8K2.u12116 = KTree.node D2M8K2.t12126 (nat_lit 25801412) (nat_lit 3340106819) (nat_lit 0) D2M8K2.t12127 from rfl, totK_node, tot12126, tot12127]
  decide +kernel

theorem arows12121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12121 = true := by
  rw [show D2M8K2.u12121 = KTree.node D2M8K2.t12128 (nat_lit 25803003) (nat_lit 3665525704) (nat_lit 0) D2M8K2.t12129 from rfl, allE_node, rows12128, irow12121, rows12129]
  all_goals rfl

theorem atot12121 : totK PD2M8K2 D2M8K2.u12121 = [0, 342562501730, 926553450579, 505659314341, 44740072903, 0, 0, 0] := by
  rw [show D2M8K2.u12121 = KTree.node D2M8K2.t12128 (nat_lit 25803003) (nat_lit 3665525704) (nat_lit 0) D2M8K2.t12129 from rfl, totK_node, tot12128, tot12129]
  decide +kernel

theorem arows12122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12122 = true := by
  rw [show D2M8K2.u12122 = KTree.node D2M8K2.t12130 (nat_lit 25805408) (nat_lit 3817391977) (nat_lit 0) D2M8K2.t12131 from rfl, allE_node, rows12130, irow12122, rows12131]
  all_goals rfl

theorem atot12122 : totK PD2M8K2 D2M8K2.u12122 = [0, 155237236290, 661686496776, 789595652368, 163743188113, 4532804645, 0, 0] := by
  rw [show D2M8K2.u12122 = KTree.node D2M8K2.t12130 (nat_lit 25805408) (nat_lit 3817391977) (nat_lit 0) D2M8K2.t12131 from rfl, totK_node, tot12130, tot12131]
  decide +kernel

theorem arows12124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12124 = true := by
  rw [show D2M8K2.u12124 = KTree.node D2M8K2.t12132 (nat_lit 25807178) (nat_lit 4029013571) (nat_lit 0) D2M8K2.t12133 from rfl, allE_node, rows12132, irow12124, rows12133]
  all_goals rfl

theorem atot12124 : totK PD2M8K2 D2M8K2.u12124 = [0, 269866180596, 851079338653, 619530994469, 68234731967, 0, 0, 0] := by
  rw [show D2M8K2.u12124 = KTree.node D2M8K2.t12132 (nat_lit 25807178) (nat_lit 4029013571) (nat_lit 0) D2M8K2.t12133 from rfl, totK_node, tot12132, tot12133]
  decide +kernel

theorem arows12125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12125 = true := by
  rw [show D2M8K2.u12125 = KTree.node D2M8K2.t12134 (nat_lit 25808881) (nat_lit 1380420553) (nat_lit 0) D2M8K2.t12135 from rfl, allE_node, rows12134, irow12125, rows12135]
  all_goals rfl

theorem atot12125 : totK PD2M8K2 D2M8K2.u12125 = [0, 93572726759, 557270883290, 837054200246, 271885806891, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12125 = KTree.node D2M8K2.t12134 (nat_lit 25808881) (nat_lit 1380420553) (nat_lit 0) D2M8K2.t12135 from rfl, totK_node, tot12134, tot12135]
  decide +kernel

theorem arows12128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12128 = true := by
  rw [show D2M8K2.u12128 = KTree.node D2M8K2.t12136 (nat_lit 25810277) (nat_lit 1988388010) (nat_lit 0) D2M8K2.t12137 from rfl, allE_node, rows12136, irow12128, rows12137]
  all_goals rfl

theorem atot12128 : totK PD2M8K2 D2M8K2.u12128 = [0, 345349101557, 919849090930, 523606003647, 43636316495, 0, 0, 0] := by
  rw [show D2M8K2.u12128 = KTree.node D2M8K2.t12136 (nat_lit 25810277) (nat_lit 1988388010) (nat_lit 0) D2M8K2.t12137 from rfl, totK_node, tot12136, tot12137]
  decide +kernel

theorem arows12129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12129 = true := by
  rw [show D2M8K2.u12129 = KTree.node D2M8K2.t12138 (nat_lit 25812090) (nat_lit 3905709340) (nat_lit 0) D2M8K2.t12139 from rfl, allE_node, rows12138, irow12129, rows12139]
  all_goals rfl

theorem atot12129 : totK PD2M8K2 D2M8K2.u12129 = [0, 0, 499997612595, 1013495519758, 270856921259, 6350335412, 0, 0] := by
  rw [show D2M8K2.u12129 = KTree.node D2M8K2.t12138 (nat_lit 25812090) (nat_lit 3905709340) (nat_lit 0) D2M8K2.t12139 from rfl, totK_node, tot12138, tot12139]
  decide +kernel

theorem arows12131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12131 = true := by
  rw [show D2M8K2.u12131 = KTree.node D2M8K2.t12140 (nat_lit 25817529) (nat_lit 1855267513) (nat_lit 0) D2M8K2.t12141 from rfl, allE_node, rows12140, irow12131, rows12141]
  all_goals rfl

theorem atot12131 : totK PD2M8K2 D2M8K2.u12131 = [0, 0, 313140427113, 877102384213, 460011182443, 49738255694, 1138244013, 0] := by
  rw [show D2M8K2.u12131 = KTree.node D2M8K2.t12140 (nat_lit 25817529) (nat_lit 1855267513) (nat_lit 0) D2M8K2.t12141 from rfl, totK_node, tot12140, tot12141]
  decide +kernel

theorem arows12132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12132 = true := by
  rw [show D2M8K2.u12132 = KTree.node D2M8K2.t12142 (nat_lit 25820150) (nat_lit 4004501502) (nat_lit 0) D2M8K2.t12143 from rfl, allE_node, rows12142, irow12132, rows12143]
  all_goals rfl

theorem atot12132 : totK PD2M8K2 D2M8K2.u12132 = [0, 0, 258023702172, 849288955516, 604082475995, 51185396166, 0, 0] := by
  rw [show D2M8K2.u12132 = KTree.node D2M8K2.t12142 (nat_lit 25820150) (nat_lit 4004501502) (nat_lit 0) D2M8K2.t12143 from rfl, totK_node, tot12142, tot12143]
  decide +kernel

theorem arows12136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12136 = true := by
  rw [show D2M8K2.u12136 = KTree.node D2M8K2.t12144 (nat_lit 25823481) (nat_lit 1863757960) (nat_lit 0) D2M8K2.t12145 from rfl, allE_node, rows12144, irow12136, rows12145]
  all_goals rfl

theorem atot12136 : totK PD2M8K2 D2M8K2.u12136 = [0, 0, 492009277407, 973015559539, 297272658036, 7494038793, 0, 0] := by
  rw [show D2M8K2.u12136 = KTree.node D2M8K2.t12144 (nat_lit 25823481) (nat_lit 1863757960) (nat_lit 0) D2M8K2.t12145 from rfl, totK_node, tot12144, tot12145]
  decide +kernel

theorem arows12137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12137 = true := by
  rw [show D2M8K2.u12137 = KTree.node D2M8K2.t12146 (nat_lit 25827242) (nat_lit 3945143271) (nat_lit 0) D2M8K2.t12147 from rfl, allE_node, rows12146, irow12137, rows12147]
  all_goals rfl

theorem atot12137 : totK PD2M8K2 D2M8K2.u12137 = [0, 0, 357918097098, 944685017929, 440002598824, 26114289015, 0, 0] := by
  rw [show D2M8K2.u12137 = KTree.node D2M8K2.t12146 (nat_lit 25827242) (nat_lit 3945143271) (nat_lit 0) D2M8K2.t12147 from rfl, totK_node, tot12146, tot12147]
  decide +kernel

theorem arows12139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12139 = true := by
  rw [show D2M8K2.u12139 = KTree.node D2M8K2.t12148 (nat_lit 25830541) (nat_lit 1034785921) (nat_lit 0) D2M8K2.t12149 from rfl, allE_node, rows12148, irow12139, rows12149]
  all_goals rfl

theorem atot12139 : totK PD2M8K2 D2M8K2.u12139 = [0, 0, 394792121944, 947360153536, 387868445328, 19235720740, 0, 0] := by
  rw [show D2M8K2.u12139 = KTree.node D2M8K2.t12148 (nat_lit 25830541) (nat_lit 1034785921) (nat_lit 0) D2M8K2.t12149 from rfl, totK_node, tot12148, tot12149]
  decide +kernel

theorem arows12140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12140 = true := by
  rw [show D2M8K2.u12140 = KTree.node D2M8K2.t12150 (nat_lit 25832115) (nat_lit 1145115675) (nat_lit 0) D2M8K2.t12151 from rfl, allE_node, rows12150, irow12140, rows12151]
  all_goals rfl

theorem atot12140 : totK PD2M8K2 D2M8K2.u12140 = [0, 0, 92049777499, 708347797017, 773448755560, 126681286925, 2162517376, 0] := by
  rw [show D2M8K2.u12140 = KTree.node D2M8K2.t12150 (nat_lit 25832115) (nat_lit 1145115675) (nat_lit 0) D2M8K2.t12151 from rfl, totK_node, tot12150, tot12151]
  decide +kernel

theorem arows12143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12143 = true := by
  rw [show D2M8K2.u12143 = KTree.node D2M8K2.t12152 (nat_lit 25837952) (nat_lit 2979930019) (nat_lit 0) D2M8K2.t12153 from rfl, allE_node, rows12152, irow12143, rows12153]
  all_goals rfl

theorem atot12143 : totK PD2M8K2 D2M8K2.u12143 = [0, 383685229917, 889980731585, 374452058412, 75040061451, 38808591981, 2751766863, 0] := by
  rw [show D2M8K2.u12143 = KTree.node D2M8K2.t12152 (nat_lit 25837952) (nat_lit 2979930019) (nat_lit 0) D2M8K2.t12153 from rfl, totK_node, tot12152, tot12153]
  decide +kernel

theorem arows12144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12144 = true := by
  rw [show D2M8K2.u12144 = KTree.node D2M8K2.t12154 (nat_lit 25839690) (nat_lit 3819401436) (nat_lit 0) D2M8K2.t12155 from rfl, allE_node, rows12154, irow12144, rows12155]
  all_goals rfl

theorem atot12144 : totK PD2M8K2 D2M8K2.u12144 = [0, 104566897012, 677703907517, 865041276906, 150605575101, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12144 = KTree.node D2M8K2.t12154 (nat_lit 25839690) (nat_lit 3819401436) (nat_lit 0) D2M8K2.t12155 from rfl, totK_node, tot12154, tot12155]
  decide +kernel

theorem arows12146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12146 = true := by
  rw [show D2M8K2.u12146 = KTree.node D2M8K2.t12156 (nat_lit 25841623) (nat_lit 2356955982) (nat_lit 0) D2M8K2.t12157 from rfl, allE_node, rows12156, irow12146, rows12157]
  all_goals rfl

theorem atot12146 : totK PD2M8K2 D2M8K2.u12146 = [0, 315358862361, 908744491585, 561278136288, 51474797436, 0, 0, 0] := by
  rw [show D2M8K2.u12146 = KTree.node D2M8K2.t12156 (nat_lit 25841623) (nat_lit 2356955982) (nat_lit 0) D2M8K2.t12157 from rfl, totK_node, tot12156, tot12157]
  decide +kernel

theorem arows12147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12147 = true := by
  rw [show D2M8K2.u12147 = KTree.node D2M8K2.t12158 (nat_lit 25843203) (nat_lit 3647447937) (nat_lit 0) D2M8K2.t12159 from rfl, allE_node, rows12158, irow12147, rows12159]
  all_goals rfl

theorem atot12147 : totK PD2M8K2 D2M8K2.u12147 = [0, 0, 376560680231, 953920883737, 444303227114, 27185641738, 0, 0] := by
  rw [show D2M8K2.u12147 = KTree.node D2M8K2.t12158 (nat_lit 25843203) (nat_lit 3647447937) (nat_lit 0) D2M8K2.t12159 from rfl, totK_node, tot12158, tot12159]
  decide +kernel

theorem arows12154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12154 = true := by
  rw [show D2M8K2.u12154 = KTree.node D2M8K2.t12160 (nat_lit 25847961) (nat_lit 1860182871) (nat_lit 0) D2M8K2.t12161 from rfl, allE_node, rows12160, irow12154, rows12161]
  all_goals rfl

theorem atot12154 : totK PD2M8K2 D2M8K2.u12154 = [0, 352754736181, 871626737880, 484761759378, 85799883769, 5618966238, 0, 0] := by
  rw [show D2M8K2.u12154 = KTree.node D2M8K2.t12160 (nat_lit 25847961) (nat_lit 1860182871) (nat_lit 0) D2M8K2.t12161 from rfl, totK_node, tot12160, tot12161]
  decide +kernel

theorem arows12155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12155 = true := by
  rw [show D2M8K2.u12155 = KTree.node D2M8K2.t12162 (nat_lit 25849514) (nat_lit 4126665669) (nat_lit 0) D2M8K2.t12163 from rfl, allE_node, rows12162, irow12155, rows12163]
  all_goals rfl

theorem atot12155 : totK PD2M8K2 D2M8K2.u12155 = [0, 71819796256, 549245979693, 881652791291, 268051604234, 10659061882, 0, 0] := by
  rw [show D2M8K2.u12155 = KTree.node D2M8K2.t12162 (nat_lit 25849514) (nat_lit 4126665669) (nat_lit 0) D2M8K2.t12163 from rfl, totK_node, tot12162, tot12163]
  decide +kernel

theorem arows12157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12157 = true := by
  rw [show D2M8K2.u12157 = KTree.node D2M8K2.t12164 (nat_lit 25854767) (nat_lit 2765524874) (nat_lit 0) D2M8K2.t12165 from rfl, allE_node, rows12164, irow12157, rows12165]
  all_goals rfl

theorem atot12157 : totK PD2M8K2 D2M8K2.u12157 = [0, 334303533822, 888697248446, 529978645660, 69587190741, 2524036228, 0, 0] := by
  rw [show D2M8K2.u12157 = KTree.node D2M8K2.t12164 (nat_lit 25854767) (nat_lit 2765524874) (nat_lit 0) D2M8K2.t12165 from rfl, totK_node, tot12164, tot12165]
  decide +kernel

theorem arows12158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12158 = true := by
  rw [show D2M8K2.u12158 = KTree.node D2M8K2.t12166 (nat_lit 25856264) (nat_lit 2243853902) (nat_lit 0) D2M8K2.t12167 from rfl, allE_node, rows12166, irow12158, rows12167]
  all_goals rfl

theorem atot12158 : totK PD2M8K2 D2M8K2.u12158 = [0, 93373242333, 631028819480, 854120242438, 214119911039, 4901932702, 0, 0] := by
  rw [show D2M8K2.u12158 = KTree.node D2M8K2.t12166 (nat_lit 25856264) (nat_lit 2243853902) (nat_lit 0) D2M8K2.t12167 from rfl, totK_node, tot12166, tot12167]
  decide +kernel

theorem arows12161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12161 = true := by
  rw [show D2M8K2.u12161 = KTree.node D2M8K2.t12168 (nat_lit 25878670) (nat_lit 4002987039) (nat_lit 0) D2M8K2.t12169 from rfl, allE_node, rows12168, irow12161, rows12169]
  all_goals rfl

theorem atot12161 : totK PD2M8K2 D2M8K2.u12161 = [265999872914, 620396437062, 348137158229, 343835540169, 202277596553, 17080783126, 0, 0] := by
  rw [show D2M8K2.u12161 = KTree.node D2M8K2.t12168 (nat_lit 25878670) (nat_lit 4002987039) (nat_lit 0) D2M8K2.t12169 from rfl, totK_node, tot12168, tot12169]
  decide +kernel

theorem arows12162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12162 = true := by
  rw [show D2M8K2.u12162 = KTree.node D2M8K2.t12170 (nat_lit 25880192) (nat_lit 2699980799) (nat_lit 0) D2M8K2.t12171 from rfl, allE_node, rows12170, irow12162, rows12171]
  all_goals rfl

theorem atot12162 : totK PD2M8K2 D2M8K2.u12162 = [169294685987, 737211893773, 755950092589, 128886517591, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12162 = KTree.node D2M8K2.t12170 (nat_lit 25880192) (nat_lit 2699980799) (nat_lit 0) D2M8K2.t12171 from rfl, totK_node, tot12170, tot12171]
  decide +kernel

theorem arows12164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12164 = true := by
  rw [show D2M8K2.u12164 = KTree.node D2M8K2.t12172 (nat_lit 25885759) (nat_lit 1852441472) (nat_lit 0) D2M8K2.t12173 from rfl, allE_node, rows12172, irow12164, rows12173]
  all_goals rfl

theorem atot12164 : totK PD2M8K2 D2M8K2.u12164 = [282139642862, 852502647950, 618954131202, 66111165826, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12164 = KTree.node D2M8K2.t12172 (nat_lit 25885759) (nat_lit 1852441472) (nat_lit 0) D2M8K2.t12173 from rfl, totK_node, tot12172, tot12173]
  decide +kernel

theorem arows12165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12165 = true := by
  rw [show D2M8K2.u12165 = KTree.node D2M8K2.t12174 (nat_lit 25887268) (nat_lit 3726738556) (nat_lit 0) D2M8K2.t12175 from rfl, allE_node, rows12174, irow12165, rows12175]
  all_goals rfl

theorem atot12165 : totK PD2M8K2 D2M8K2.u12165 = [128474520331, 633303681378, 788271086114, 207952454066, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u12165 = KTree.node D2M8K2.t12174 (nat_lit 25887268) (nat_lit 3726738556) (nat_lit 0) D2M8K2.t12175 from rfl, totK_node, tot12174, tot12175]
  decide +kernel

theorem arows12169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12169 = true := by
  rw [show D2M8K2.u12169 = KTree.node D2M8K2.t12176 (nat_lit 25889123) (nat_lit 2359780618) (nat_lit 0) D2M8K2.t12177 from rfl, allE_node, rows12176, irow12169, rows12177]
  all_goals rfl

theorem atot12169 : totK PD2M8K2 D2M8K2.u12169 = [251330795430, 779899946410, 639213247060, 123454903043, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u12169 = KTree.node D2M8K2.t12176 (nat_lit 25889123) (nat_lit 2359780618) (nat_lit 0) D2M8K2.t12177 from rfl, totK_node, tot12176, tot12177]
  decide +kernel

theorem arows12170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12170 = true := by
  rw [show D2M8K2.u12170 = KTree.node D2M8K2.t12178 (nat_lit 25890685) (nat_lit 1166694131) (nat_lit 0) D2M8K2.t12179 from rfl, allE_node, rows12178, irow12170, rows12179]
  all_goals rfl

theorem atot12170 : totK PD2M8K2 D2M8K2.u12170 = [156124401511, 661509424285, 756228324106, 195845130735, 7233348802, 0, 0, 0] := by
  rw [show D2M8K2.u12170 = KTree.node D2M8K2.t12178 (nat_lit 25890685) (nat_lit 1166694131) (nat_lit 0) D2M8K2.t12179 from rfl, totK_node, tot12178, tot12179]
  decide +kernel

theorem arows12172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12172 = true := by
  rw [show D2M8K2.u12172 = KTree.node D2M8K2.t12180 (nat_lit 25892497) (nat_lit 1560874839) (nat_lit 0) D2M8K2.t12181 from rfl, allE_node, rows12180, irow12172, rows12181]
  all_goals rfl

theorem atot12172 : totK PD2M8K2 D2M8K2.u12172 = [246245450870, 758970166628, 640181982879, 141145595965, 5035903252, 0, 0, 0] := by
  rw [show D2M8K2.u12172 = KTree.node D2M8K2.t12180 (nat_lit 25892497) (nat_lit 1560874839) (nat_lit 0) D2M8K2.t12181 from rfl, totK_node, tot12180, tot12181]
  decide +kernel

theorem arows12173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12173 = true := by
  rw [show D2M8K2.u12173 = KTree.node D2M8K2.t12182 (nat_lit 25893745) (nat_lit 1413379578) (nat_lit 0) D2M8K2.t12183 from rfl, allE_node, rows12182, irow12173, rows12183]
  all_goals rfl

theorem atot12173 : totK PD2M8K2 D2M8K2.u12173 = [177877115015, 759480938255, 745774343868, 112792240151, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u12173 = KTree.node D2M8K2.t12182 (nat_lit 25893745) (nat_lit 1413379578) (nat_lit 0) D2M8K2.t12183 from rfl, totK_node, tot12182, tot12183]
  decide +kernel

theorem arows12176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12176 = true := by
  rw [show D2M8K2.u12176 = KTree.node D2M8K2.t12184 (nat_lit 25896027) (nat_lit 1591046068) (nat_lit 0) D2M8K2.t12185 from rfl, allE_node, rows12184, irow12176, rows12185]
  all_goals rfl

theorem atot12176 : totK PD2M8K2 D2M8K2.u12176 = [250628176038, 780120724687, 628977887660, 124793778235, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u12176 = KTree.node D2M8K2.t12184 (nat_lit 25896027) (nat_lit 1591046068) (nat_lit 0) D2M8K2.t12185 from rfl, totK_node, tot12184, tot12185]
  decide +kernel

theorem arows12177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12177 = true := by
  rw [show D2M8K2.u12177 = KTree.node D2M8K2.t12186 (nat_lit 25898173) (nat_lit 1217259329) (nat_lit 0) D2M8K2.t12187 from rfl, allE_node, rows12186, irow12177, rows12187]
  all_goals rfl

theorem atot12177 : totK PD2M8K2 D2M8K2.u12177 = [72446816662, 505603302919, 873890362529, 290259416137, 9938656398, 0, 0, 0] := by
  rw [show D2M8K2.u12177 = KTree.node D2M8K2.t12186 (nat_lit 25898173) (nat_lit 1217259329) (nat_lit 0) D2M8K2.t12187 from rfl, totK_node, tot12186, tot12187]
  decide +kernel

theorem arows12179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12179 = true := by
  rw [show D2M8K2.u12179 = KTree.node D2M8K2.t12188 (nat_lit 25900048) (nat_lit 3532979887) (nat_lit 0) D2M8K2.t12189 from rfl, allE_node, rows12188, irow12179, rows12189]
  all_goals rfl

theorem atot12179 : totK PD2M8K2 D2M8K2.u12179 = [0, 351835062665, 932146832561, 446884711743, 31194220652, 0, 0, 0] := by
  rw [show D2M8K2.u12179 = KTree.node D2M8K2.t12188 (nat_lit 25900048) (nat_lit 3532979887) (nat_lit 0) D2M8K2.t12189 from rfl, totK_node, tot12188, tot12189]
  decide +kernel

theorem arows12180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12180 = true := by
  rw [show D2M8K2.u12180 = KTree.node D2M8K2.t12190 (nat_lit 25901581) (nat_lit 1384601311) (nat_lit 0) D2M8K2.t12191 from rfl, allE_node, rows12190, irow12180, rows12191]
  all_goals rfl

theorem atot12180 : totK PD2M8K2 D2M8K2.u12180 = [0, 118928644007, 675722687385, 787263905120, 145401435901, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12180 = KTree.node D2M8K2.t12190 (nat_lit 25901581) (nat_lit 1384601311) (nat_lit 0) D2M8K2.t12191 from rfl, totK_node, tot12190, tot12191]
  decide +kernel

theorem arows12185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12185 = true := by
  rw [show D2M8K2.u12185 = KTree.node D2M8K2.t12192 (nat_lit 25906894) (nat_lit 3999430264) (nat_lit 0) D2M8K2.t12193 from rfl, allE_node, rows12192, irow12185, rows12193]
  all_goals rfl

theorem atot12185 : totK PD2M8K2 D2M8K2.u12185 = [0, 372598100149, 952257512748, 434383008666, 18915990292, 0, 0, 0] := by
  rw [show D2M8K2.u12185 = KTree.node D2M8K2.t12192 (nat_lit 25906894) (nat_lit 3999430264) (nat_lit 0) D2M8K2.t12193 from rfl, totK_node, tot12192, tot12193]
  decide +kernel

theorem arows12186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12186 = true := by
  rw [show D2M8K2.u12186 = KTree.node D2M8K2.t12194 (nat_lit 25910523) (nat_lit 3723772572) (nat_lit 0) D2M8K2.t12195 from rfl, allE_node, rows12194, irow12186, rows12195]
  all_goals rfl

theorem atot12186 : totK PD2M8K2 D2M8K2.u12186 = [0, 364078707935, 941769549425, 453671269146, 25435280443, 0, 0, 0] := by
  rw [show D2M8K2.u12186 = KTree.node D2M8K2.t12194 (nat_lit 25910523) (nat_lit 3723772572) (nat_lit 0) D2M8K2.t12195 from rfl, totK_node, tot12194, tot12195]
  decide +kernel

theorem arows12188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12188 = true := by
  rw [show D2M8K2.u12188 = KTree.node D2M8K2.t12196 (nat_lit 25913486) (nat_lit 3864278121) (nat_lit 0) D2M8K2.t12197 from rfl, allE_node, rows12196, irow12188, rows12197]
  all_goals rfl

theorem atot12188 : totK PD2M8K2 D2M8K2.u12188 = [0, 377416045299, 948066515053, 430220536653, 21118070844, 0, 0, 0] := by
  rw [show D2M8K2.u12188 = KTree.node D2M8K2.t12196 (nat_lit 25913486) (nat_lit 3864278121) (nat_lit 0) D2M8K2.t12197 from rfl, totK_node, tot12196, tot12197]
  decide +kernel

theorem arows12189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12189 = true := by
  rw [show D2M8K2.u12189 = KTree.node D2M8K2.t12198 (nat_lit 25916808) (nat_lit 3605856933) (nat_lit 0) D2M8K2.t12199 from rfl, allE_node, rows12198, irow12189, rows12199]
  all_goals rfl

theorem atot12189 : totK PD2M8K2 D2M8K2.u12189 = [0, 376890354176, 951210145924, 429846609243, 20461197944, 0, 0, 0] := by
  rw [show D2M8K2.u12189 = KTree.node D2M8K2.t12198 (nat_lit 25916808) (nat_lit 3605856933) (nat_lit 0) D2M8K2.t12199 from rfl, totK_node, tot12198, tot12199]
  decide +kernel

theorem arows12192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12192 = true := by
  rw [show D2M8K2.u12192 = KTree.node D2M8K2.t12200 (nat_lit 25924076) (nat_lit 3712679515) (nat_lit 0) D2M8K2.t12201 from rfl, allE_node, rows12200, irow12192, rows12201]
  all_goals rfl

theorem atot12192 : totK PD2M8K2 D2M8K2.u12192 = [318686858394, 792279915613, 563460943490, 153055544327, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u12192 = KTree.node D2M8K2.t12200 (nat_lit 25924076) (nat_lit 3712679515) (nat_lit 0) D2M8K2.t12201 from rfl, totK_node, tot12200, tot12201]
  decide +kernel

theorem arows12193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12193 = true := by
  rw [show D2M8K2.u12193 = KTree.node D2M8K2.t12202 (nat_lit 25925571) (nat_lit 3724153277) (nat_lit 0) D2M8K2.t12203 from rfl, allE_node, rows12202, irow12193, rows12203]
  all_goals rfl

theorem atot12193 : totK PD2M8K2 D2M8K2.u12193 = [125185423002, 620085479957, 762478417955, 295156377418, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u12193 = KTree.node D2M8K2.t12202 (nat_lit 25925571) (nat_lit 3724153277) (nat_lit 0) D2M8K2.t12203 from rfl, totK_node, tot12202, tot12203]
  decide +kernel

theorem arows12195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12195 = true := by
  rw [show D2M8K2.u12195 = KTree.node D2M8K2.t12204 (nat_lit 25926796) (nat_lit 3710769412) (nat_lit 0) D2M8K2.t12205 from rfl, allE_node, rows12204, irow12195, rows12205]
  all_goals rfl

theorem atot12195 : totK PD2M8K2 D2M8K2.u12195 = [157096909914, 587434137670, 774926525403, 294808142922, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u12195 = KTree.node D2M8K2.t12204 (nat_lit 25926796) (nat_lit 3710769412) (nat_lit 0) D2M8K2.t12205 from rfl, totK_node, tot12204, tot12205]
  decide +kernel

theorem arows12196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12196 = true := by
  rw [show D2M8K2.u12196 = KTree.node D2M8K2.t12206 (nat_lit 25928316) (nat_lit 2915596568) (nat_lit 0) D2M8K2.t12207 from rfl, allE_node, rows12206, irow12196, rows12207]
  all_goals rfl

theorem atot12196 : totK PD2M8K2 D2M8K2.u12196 = [256677910013, 807008363586, 628831617129, 103647469188, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u12196 = KTree.node D2M8K2.t12206 (nat_lit 25928316) (nat_lit 2915596568) (nat_lit 0) D2M8K2.t12207 from rfl, totK_node, tot12206, tot12207]
  decide +kernel

theorem arows12200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12200 = true := by
  rw [show D2M8K2.u12200 = KTree.node D2M8K2.t12208 (nat_lit 25930046) (nat_lit 2292161770) (nat_lit 0) D2M8K2.t12209 from rfl, allE_node, rows12208, irow12200, rows12209]
  all_goals rfl

theorem atot12200 : totK PD2M8K2 D2M8K2.u12200 = [157178836392, 641981390112, 767433849048, 226309608780, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u12200 = KTree.node D2M8K2.t12208 (nat_lit 25930046) (nat_lit 2292161770) (nat_lit 0) D2M8K2.t12209 from rfl, totK_node, tot12208, tot12209]
  decide +kernel

theorem arows12201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12201 = true := by
  rw [show D2M8K2.u12201 = KTree.node D2M8K2.t12210 (nat_lit 25931714) (nat_lit 3883325262) (nat_lit 0) D2M8K2.t12211 from rfl, allE_node, rows12210, irow12201, rows12211]
  all_goals rfl

theorem atot12201 : totK PD2M8K2 D2M8K2.u12201 = [256836792690, 805021298480, 638553849703, 100885369549, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u12201 = KTree.node D2M8K2.t12210 (nat_lit 25931714) (nat_lit 3883325262) (nat_lit 0) D2M8K2.t12211 from rfl, totK_node, tot12210, tot12211]
  decide +kernel

theorem arows12203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12203 = true := by
  rw [show D2M8K2.u12203 = KTree.node D2M8K2.t12212 (nat_lit 25933426) (nat_lit 2721148909) (nat_lit 0) D2M8K2.t12213 from rfl, allE_node, rows12212, irow12203, rows12213]
  all_goals rfl

theorem atot12203 : totK PD2M8K2 D2M8K2.u12203 = [160882570615, 641917453906, 758549997949, 227529587690, 12040273252, 0, 0, 0] := by
  rw [show D2M8K2.u12203 = KTree.node D2M8K2.t12212 (nat_lit 25933426) (nat_lit 2721148909) (nat_lit 0) D2M8K2.t12213 from rfl, totK_node, tot12212, tot12213]
  decide +kernel

theorem arows12204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12204 = true := by
  rw [show D2M8K2.u12204 = KTree.node D2M8K2.t12214 (nat_lit 25934830) (nat_lit 3645277160) (nat_lit 0) D2M8K2.t12215 from rfl, allE_node, rows12214, irow12204, rows12215]
  all_goals rfl

theorem atot12204 : totK PD2M8K2 D2M8K2.u12204 = [264340839740, 827299814877, 620020294005, 85583212352, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u12204 = KTree.node D2M8K2.t12214 (nat_lit 25934830) (nat_lit 3645277160) (nat_lit 0) D2M8K2.t12215 from rfl, totK_node, tot12214, tot12215]
  decide +kernel

theorem arows12207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12207 = true := by
  rw [show D2M8K2.u12207 = KTree.node D2M8K2.t12216 (nat_lit 25936783) (nat_lit 2426140697) (nat_lit 0) D2M8K2.t12217 from rfl, allE_node, rows12216, irow12207, rows12217]
  all_goals rfl

theorem atot12207 : totK PD2M8K2 D2M8K2.u12207 = [155484015133, 673575169572, 839781086778, 180919663091, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u12207 = KTree.node D2M8K2.t12216 (nat_lit 25936783) (nat_lit 2426140697) (nat_lit 0) D2M8K2.t12217 from rfl, totK_node, tot12216, tot12217]
  decide +kernel

theorem arows12208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12208 = true := by
  rw [show D2M8K2.u12208 = KTree.node D2M8K2.t12218 (nat_lit 25938896) (nat_lit 3028361899) (nat_lit 0) D2M8K2.t12219 from rfl, allE_node, rows12218, irow12208, rows12219]
  all_goals rfl

theorem atot12208 : totK PD2M8K2 D2M8K2.u12208 = [174544416507, 741860476495, 731702211132, 151728624716, 3681172965, 0, 0, 0] := by
  rw [show D2M8K2.u12208 = KTree.node D2M8K2.t12218 (nat_lit 25938896) (nat_lit 3028361899) (nat_lit 0) D2M8K2.t12219 from rfl, totK_node, tot12218, tot12219]
  decide +kernel

theorem arows12210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12210 = true := by
  rw [show D2M8K2.u12210 = KTree.node D2M8K2.t12220 (nat_lit 25944612) (nat_lit 2548550142) (nat_lit 0) D2M8K2.t12221 from rfl, allE_node, rows12220, irow12210, rows12221]
  all_goals rfl

theorem atot12210 : totK PD2M8K2 D2M8K2.u12210 = [0, 371865405617, 921338270162, 483214780869, 44011643655, 0, 0, 0] := by
  rw [show D2M8K2.u12210 = KTree.node D2M8K2.t12220 (nat_lit 25944612) (nat_lit 2548550142) (nat_lit 0) D2M8K2.t12221 from rfl, totK_node, tot12220, tot12221]
  decide +kernel

theorem arows12211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12211 = true := by
  rw [show D2M8K2.u12211 = KTree.node D2M8K2.t12222 (nat_lit 25945804) (nat_lit 3818173758) (nat_lit 0) D2M8K2.t12223 from rfl, allE_node, rows12222, irow12211, rows12223]
  all_goals rfl

theorem atot12211 : totK PD2M8K2 D2M8K2.u12211 = [0, 180653652570, 733331080313, 691052181007, 201600625429, 21385604922, 0, 0] := by
  rw [show D2M8K2.u12211 = KTree.node D2M8K2.t12222 (nat_lit 25945804) (nat_lit 3818173758) (nat_lit 0) D2M8K2.t12223 from rfl, totK_node, tot12222, tot12223]
  decide +kernel

theorem arows12217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12217 = true := by
  rw [show D2M8K2.u12217 = KTree.node D2M8K2.t12224 (nat_lit 25947294) (nat_lit 3949526937) (nat_lit 0) D2M8K2.t12225 from rfl, allE_node, rows12224, irow12217, rows12225]
  all_goals rfl

theorem atot12217 : totK PD2M8K2 D2M8K2.u12217 = [0, 113125941864, 492826671130, 806435355259, 346692197116, 15536268932, 0, 0] := by
  rw [show D2M8K2.u12217 = KTree.node D2M8K2.t12224 (nat_lit 25947294) (nat_lit 3949526937) (nat_lit 0) D2M8K2.t12225 from rfl, totK_node, tot12224, tot12225]
  decide +kernel

theorem arows12218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12218 = true := by
  rw [show D2M8K2.u12218 = KTree.node D2M8K2.t12226 (nat_lit 25948841) (nat_lit 1805851422) (nat_lit 0) D2M8K2.t12227 from rfl, allE_node, rows12226, irow12218, rows12227]
  all_goals rfl

theorem atot12218 : totK PD2M8K2 D2M8K2.u12218 = [0, 296090048489, 887174893688, 570682355407, 48940784077, 0, 0, 0] := by
  rw [show D2M8K2.u12218 = KTree.node D2M8K2.t12226 (nat_lit 25948841) (nat_lit 1805851422) (nat_lit 0) D2M8K2.t12227 from rfl, totK_node, tot12226, tot12227]
  decide +kernel

theorem arows12220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12220 = true := by
  rw [show D2M8K2.u12220 = KTree.node D2M8K2.t12228 (nat_lit 25950680) (nat_lit 3449960287) (nat_lit 0) D2M8K2.t12229 from rfl, allE_node, rows12228, irow12220, rows12229]
  all_goals rfl

theorem atot12220 : totK PD2M8K2 D2M8K2.u12220 = [0, 156620130629, 661293803812, 787976464174, 195045483740, 5159868635, 0, 0] := by
  rw [show D2M8K2.u12220 = KTree.node D2M8K2.t12228 (nat_lit 25950680) (nat_lit 3449960287) (nat_lit 0) D2M8K2.t12229 from rfl, totK_node, tot12228, tot12229]
  decide +kernel

theorem arows12221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12221 = true := by
  rw [show D2M8K2.u12221 = KTree.node D2M8K2.t12230 (nat_lit 25952364) (nat_lit 3105335751) (nat_lit 0) D2M8K2.t12231 from rfl, allE_node, rows12230, irow12221, rows12231]
  all_goals rfl

theorem atot12221 : totK PD2M8K2 D2M8K2.u12221 = [0, 256421121796, 860022949735, 627726866856, 65830359970, 0, 0, 0] := by
  rw [show D2M8K2.u12221 = KTree.node D2M8K2.t12230 (nat_lit 25952364) (nat_lit 3105335751) (nat_lit 0) D2M8K2.t12231 from rfl, totK_node, tot12230, tot12231]
  decide +kernel

theorem arows12224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12224 = true := by
  rw [show D2M8K2.u12224 = KTree.node D2M8K2.t12232 (nat_lit 25954292) (nat_lit 1329452817) (nat_lit 0) D2M8K2.t12233 from rfl, allE_node, rows12232, irow12224, rows12233]
  all_goals rfl

theorem atot12224 : totK PD2M8K2 D2M8K2.u12224 = [0, 160122128994, 654653248413, 772999244520, 197347094689, 5218872685, 0, 0] := by
  rw [show D2M8K2.u12224 = KTree.node D2M8K2.t12232 (nat_lit 25954292) (nat_lit 1329452817) (nat_lit 0) D2M8K2.t12233 from rfl, totK_node, tot12232, tot12233]
  decide +kernel

theorem arows12225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12225 = true := by
  rw [show D2M8K2.u12225 = KTree.node D2M8K2.t12234 (nat_lit 25955664) (nat_lit 3210682224) (nat_lit 0) D2M8K2.t12235 from rfl, allE_node, rows12234, irow12225, rows12235]
  all_goals rfl

theorem atot12225 : totK PD2M8K2 D2M8K2.u12225 = [0, 263662697756, 863547972810, 627488432028, 53537040599, 0, 0, 0] := by
  rw [show D2M8K2.u12225 = KTree.node D2M8K2.t12234 (nat_lit 25955664) (nat_lit 3210682224) (nat_lit 0) D2M8K2.t12235 from rfl, totK_node, tot12234, tot12235]
  decide +kernel

theorem arows12227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12227 = true := by
  rw [show D2M8K2.u12227 = KTree.node D2M8K2.t12236 (nat_lit 25958345) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t12237 from rfl, allE_node, rows12236, irow12227, rows12237]
  all_goals rfl

theorem atot12227 : totK PD2M8K2 D2M8K2.u12227 = [0, 189804930358, 723222859475, 772050333422, 139935006777, 1415142070, 0, 0] := by
  rw [show D2M8K2.u12227 = KTree.node D2M8K2.t12236 (nat_lit 25958345) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t12237 from rfl, totK_node, tot12236, tot12237]
  decide +kernel

theorem arows12228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12228 = true := by
  rw [show D2M8K2.u12228 = KTree.node D2M8K2.t12238 (nat_lit 25960118) (nat_lit 3982192391) (nat_lit 0) D2M8K2.t12239 from rfl, allE_node, rows12238, irow12228, rows12239]
  all_goals rfl

theorem atot12228 : totK PD2M8K2 D2M8K2.u12228 = [0, 139227593975, 664499053697, 806015286101, 187486899931, 2484078857, 0, 0] := by
  rw [show D2M8K2.u12228 = KTree.node D2M8K2.t12238 (nat_lit 25960118) (nat_lit 3982192391) (nat_lit 0) D2M8K2.t12239 from rfl, totK_node, tot12238, tot12239]
  decide +kernel

theorem arows12232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12232 = true := by
  rw [show D2M8K2.u12232 = KTree.node D2M8K2.t12240 (nat_lit 25962173) (nat_lit 2317401966) (nat_lit 0) D2M8K2.t12241 from rfl, allE_node, rows12240, irow12232, rows12241]
  all_goals rfl

theorem atot12232 : totK PD2M8K2 D2M8K2.u12232 = [330162333768, 793659837565, 389486682438, 166393451555, 92150948647, 6818291842, 0, 0] := by
  rw [show D2M8K2.u12232 = KTree.node D2M8K2.t12240 (nat_lit 25962173) (nat_lit 2317401966) (nat_lit 0) D2M8K2.t12241 from rfl, totK_node, tot12240, tot12241]
  decide +kernel

theorem arows12233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12233 = true := by
  rw [show D2M8K2.u12233 = KTree.node D2M8K2.t12242 (nat_lit 25963469) (nat_lit 1607859423) (nat_lit 0) D2M8K2.t12243 from rfl, allE_node, rows12242, irow12233, rows12243]
  all_goals rfl

theorem atot12233 : totK PD2M8K2 D2M8K2.u12233 = [92351439535, 655048563855, 872005194173, 154152046208, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12233 = KTree.node D2M8K2.t12242 (nat_lit 25963469) (nat_lit 1607859423) (nat_lit 0) D2M8K2.t12243 from rfl, totK_node, tot12242, tot12243]
  decide +kernel

theorem arows12235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12235 = true := by
  rw [show D2M8K2.u12235 = KTree.node D2M8K2.t12244 (nat_lit 25965773) (nat_lit 1998270282) (nat_lit 0) D2M8K2.t12245 from rfl, allE_node, rows12244, irow12235, rows12245]
  all_goals rfl

theorem atot12235 : totK PD2M8K2 D2M8K2.u12235 = [366154427616, 932704584083, 498328512666, 41533211736, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12235 = KTree.node D2M8K2.t12244 (nat_lit 25965773) (nat_lit 1998270282) (nat_lit 0) D2M8K2.t12245 from rfl, totK_node, tot12244, tot12245]
  decide +kernel

theorem arows12236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12236 = true := by
  rw [show D2M8K2.u12236 = KTree.node D2M8K2.t12246 (nat_lit 25967285) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t12247 from rfl, allE_node, rows12246, irow12236, rows12247]
  all_goals rfl

theorem atot12236 : totK PD2M8K2 D2M8K2.u12236 = [31771015393, 467692529202, 891240553281, 392521725051, 29376414733, 0, 0, 0] := by
  rw [show D2M8K2.u12236 = KTree.node D2M8K2.t12246 (nat_lit 25967285) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t12247 from rfl, totK_node, tot12246, tot12247]
  decide +kernel

theorem arows12239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12239 = true := by
  rw [show D2M8K2.u12239 = KTree.node D2M8K2.t12248 (nat_lit 25968650) (nat_lit 3125301250) (nat_lit 0) D2M8K2.t12249 from rfl, allE_node, rows12248, irow12239, rows12249]
  all_goals rfl

theorem atot12239 : totK PD2M8K2 D2M8K2.u12239 = [268476451792, 741638459843, 618265684452, 192168739726, 8036391702, 0, 0, 0] := by
  rw [show D2M8K2.u12239 = KTree.node D2M8K2.t12248 (nat_lit 25968650) (nat_lit 3125301250) (nat_lit 0) D2M8K2.t12249 from rfl, totK_node, tot12248, tot12249]
  decide +kernel

theorem arows12240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12240 = true := by
  rw [show D2M8K2.u12240 = KTree.node D2M8K2.t12250 (nat_lit 25970110) (nat_lit 3906092754) (nat_lit 0) D2M8K2.t12251 from rfl, allE_node, rows12250, irow12240, rows12251]
  all_goals rfl

theorem atot12240 : totK PD2M8K2 D2M8K2.u12240 = [171260146135, 725925134031, 764994763356, 140707973612, 2309606161, 0, 0, 0] := by
  rw [show D2M8K2.u12240 = KTree.node D2M8K2.t12250 (nat_lit 25970110) (nat_lit 3906092754) (nat_lit 0) D2M8K2.t12251 from rfl, totK_node, tot12250, tot12251]
  decide +kernel

theorem arows12242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12242 = true := by
  rw [show D2M8K2.u12242 = KTree.node D2M8K2.t12252 (nat_lit 25975380) (nat_lit 3220772877) (nat_lit 0) D2M8K2.t12253 from rfl, allE_node, rows12252, irow12242, rows12253]
  all_goals rfl

theorem atot12242 : totK PD2M8K2 D2M8K2.u12242 = [227973854741, 695791761589, 676025114890, 189808360850, 10740121073, 0, 0, 0] := by
  rw [show D2M8K2.u12242 = KTree.node D2M8K2.t12252 (nat_lit 25975380) (nat_lit 3220772877) (nat_lit 0) D2M8K2.t12253 from rfl, totK_node, tot12252, tot12253]
  decide +kernel

theorem arows12243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12243 = true := by
  rw [show D2M8K2.u12243 = KTree.node D2M8K2.t12254 (nat_lit 25976564) (nat_lit 3706580909) (nat_lit 0) D2M8K2.t12255 from rfl, allE_node, rows12254, irow12243, rows12255]
  all_goals rfl

theorem atot12243 : totK PD2M8K2 D2M8K2.u12243 = [196858023842, 777599239390, 714347432938, 107587842741, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u12243 = KTree.node D2M8K2.t12254 (nat_lit 25976564) (nat_lit 3706580909) (nat_lit 0) D2M8K2.t12255 from rfl, totK_node, tot12254, tot12255]
  decide +kernel

theorem arows12248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12248 = true := by
  rw [show D2M8K2.u12248 = KTree.node D2M8K2.t12256 (nat_lit 25978873) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t12257 from rfl, allE_node, rows12256, irow12248, rows12257]
  all_goals rfl

theorem atot12248 : totK PD2M8K2 D2M8K2.u12248 = [253148051332, 752944625949, 667430533363, 138395842612, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u12248 = KTree.node D2M8K2.t12256 (nat_lit 25978873) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t12257 from rfl, totK_node, tot12256, tot12257]
  decide +kernel

theorem arows12249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12249 = true := by
  rw [show D2M8K2.u12249 = KTree.node D2M8K2.t12258 (nat_lit 25980725) (nat_lit 1286539893) (nat_lit 0) D2M8K2.t12259 from rfl, allE_node, rows12258, irow12249, rows12259]
  all_goals rfl

theorem atot12249 : totK PD2M8K2 D2M8K2.u12249 = [72979709436, 599336085092, 879056172790, 225164905864, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u12249 = KTree.node D2M8K2.t12258 (nat_lit 25980725) (nat_lit 1286539893) (nat_lit 0) D2M8K2.t12259 from rfl, totK_node, tot12258, tot12259]
  decide +kernel

theorem arows12251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12251 = true := by
  rw [show D2M8K2.u12251 = KTree.node D2M8K2.t12260 (nat_lit 25982989) (nat_lit 1193905979) (nat_lit 0) D2M8K2.t12261 from rfl, allE_node, rows12260, irow12251, rows12261]
  all_goals rfl

theorem atot12251 : totK PD2M8K2 D2M8K2.u12251 = [0, 363869118773, 934369767134, 435155681686, 25562053177, 0, 0, 0] := by
  rw [show D2M8K2.u12251 = KTree.node D2M8K2.t12260 (nat_lit 25982989) (nat_lit 1193905979) (nat_lit 0) D2M8K2.t12261 from rfl, totK_node, tot12260, tot12261]
  decide +kernel

theorem arows12252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12252 = true := by
  rw [show D2M8K2.u12252 = KTree.node D2M8K2.t12262 (nat_lit 25984643) (nat_lit 2840541388) (nat_lit 0) D2M8K2.t12263 from rfl, allE_node, rows12262, irow12252, rows12263]
  all_goals rfl

theorem atot12252 : totK PD2M8K2 D2M8K2.u12252 = [0, 133325856969, 719006543342, 774460112786, 115844398946, 1206465782, 0, 0] := by
  rw [show D2M8K2.u12252 = KTree.node D2M8K2.t12262 (nat_lit 25984643) (nat_lit 2840541388) (nat_lit 0) D2M8K2.t12263 from rfl, totK_node, tot12262, tot12263]
  decide +kernel

theorem arows12255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12255 = true := by
  rw [show D2M8K2.u12255 = KTree.node D2M8K2.t12264 (nat_lit 25986789) (nat_lit 1229071624) (nat_lit 0) D2M8K2.t12265 from rfl, allE_node, rows12264, irow12255, rows12265]
  all_goals rfl

theorem atot12255 : totK PD2M8K2 D2M8K2.u12255 = [0, 353134603054, 923623612863, 506084334577, 36770327518, 0, 0, 0] := by
  rw [show D2M8K2.u12255 = KTree.node D2M8K2.t12264 (nat_lit 25986789) (nat_lit 1229071624) (nat_lit 0) D2M8K2.t12265 from rfl, totK_node, tot12264, tot12265]
  decide +kernel

theorem arows12256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12256 = true := by
  rw [show D2M8K2.u12256 = KTree.node D2M8K2.t12266 (nat_lit 25989748) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t12267 from rfl, allE_node, rows12266, irow12256, rows12267]
  all_goals rfl

theorem atot12256 : totK PD2M8K2 D2M8K2.u12256 = [0, 375482294289, 952573246478, 450667465532, 28288117611, 0, 0, 0] := by
  rw [show D2M8K2.u12256 = KTree.node D2M8K2.t12266 (nat_lit 25989748) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t12267 from rfl, totK_node, tot12266, tot12267]
  decide +kernel

theorem arows12258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12258 = true := by
  rw [show D2M8K2.u12258 = KTree.node D2M8K2.t12268 (nat_lit 25991452) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t12269 from rfl, allE_node, rows12268, irow12258, rows12269]
  all_goals rfl

theorem atot12258 : totK PD2M8K2 D2M8K2.u12258 = [0, 25543652753, 521901239260, 892168368301, 271984958554, 13016197374, 0, 0] := by
  rw [show D2M8K2.u12258 = KTree.node D2M8K2.t12268 (nat_lit 25991452) (nat_lit 3969568137) (nat_lit 0) D2M8K2.t12269 from rfl, totK_node, tot12268, tot12269]
  decide +kernel

theorem arows12259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12259 = true := by
  rw [show D2M8K2.u12259 = KTree.node D2M8K2.t12270 (nat_lit 25996588) (nat_lit 3747039492) (nat_lit 0) D2M8K2.t12271 from rfl, allE_node, rows12270, irow12259, rows12271]
  all_goals rfl

theorem atot12259 : totK PD2M8K2 D2M8K2.u12259 = [0, 371045284951, 930784986800, 465480474105, 31204651175, 0, 0, 0] := by
  rw [show D2M8K2.u12259 = KTree.node D2M8K2.t12270 (nat_lit 25996588) (nat_lit 3747039492) (nat_lit 0) D2M8K2.t12271 from rfl, totK_node, tot12270, tot12271]
  decide +kernel

theorem arows12263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12263 = true := by
  rw [show D2M8K2.u12263 = KTree.node D2M8K2.t12272 (nat_lit 25998362) (nat_lit 4185538621) (nat_lit 0) D2M8K2.t12273 from rfl, allE_node, rows12272, irow12263, rows12273]
  all_goals rfl

theorem atot12263 : totK PD2M8K2 D2M8K2.u12263 = [0, 109700327074, 667071173281, 779929799550, 152576501977, 4574395652, 0, 0] := by
  rw [show D2M8K2.u12263 = KTree.node D2M8K2.t12272 (nat_lit 25998362) (nat_lit 4185538621) (nat_lit 0) D2M8K2.t12273 from rfl, totK_node, tot12272, tot12273]
  decide +kernel

theorem arows12264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12264 = true := by
  rw [show D2M8K2.u12264 = KTree.node D2M8K2.t12274 (nat_lit 26000202) (nat_lit 2477092382) (nat_lit 0) D2M8K2.t12275 from rfl, allE_node, rows12274, irow12264, rows12275]
  all_goals rfl

theorem atot12264 : totK PD2M8K2 D2M8K2.u12264 = [90010399694, 447255464411, 797187935769, 435614187431, 37595607491, 0, 0, 0] := by
  rw [show D2M8K2.u12264 = KTree.node D2M8K2.t12274 (nat_lit 26000202) (nat_lit 2477092382) (nat_lit 0) D2M8K2.t12275 from rfl, totK_node, tot12274, tot12275]
  decide +kernel

theorem arows12266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12266 = true := by
  rw [show D2M8K2.u12266 = KTree.node D2M8K2.t12276 (nat_lit 26004123) (nat_lit 3673339773) (nat_lit 0) D2M8K2.t12277 from rfl, allE_node, rows12276, irow12266, rows12277]
  all_goals rfl

theorem atot12266 : totK PD2M8K2 D2M8K2.u12266 = [316643988852, 894409922886, 521868363723, 40584050924, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12266 = KTree.node D2M8K2.t12276 (nat_lit 26004123) (nat_lit 3673339773) (nat_lit 0) D2M8K2.t12277 from rfl, totK_node, tot12276, tot12277]
  decide +kernel

theorem arows12267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12267 = true := by
  rw [show D2M8K2.u12267 = KTree.node D2M8K2.t12278 (nat_lit 26005927) (nat_lit 2357814271) (nat_lit 0) D2M8K2.t12279 from rfl, allE_node, rows12278, irow12267, rows12279]
  all_goals rfl

theorem atot12267 : totK PD2M8K2 D2M8K2.u12267 = [147788873918, 680451022467, 832037196319, 153787523213, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12267 = KTree.node D2M8K2.t12278 (nat_lit 26005927) (nat_lit 2357814271) (nat_lit 0) D2M8K2.t12279 from rfl, totK_node, tot12278, tot12279]
  decide +kernel

theorem arows12270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12270 = true := by
  rw [show D2M8K2.u12270 = KTree.node D2M8K2.t12280 (nat_lit 26007716) (nat_lit 3106899223) (nat_lit 0) D2M8K2.t12281 from rfl, allE_node, rows12280, irow12270, rows12281]
  all_goals rfl

theorem atot12270 : totK PD2M8K2 D2M8K2.u12270 = [270198296156, 842300431884, 602258393853, 102387878809, 10443687594, 0, 0, 0] := by
  rw [show D2M8K2.u12270 = KTree.node D2M8K2.t12280 (nat_lit 26007716) (nat_lit 3106899223) (nat_lit 0) D2M8K2.t12281 from rfl, totK_node, tot12280, tot12281]
  decide +kernel

theorem arows12271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12271 = true := by
  rw [show D2M8K2.u12271 = KTree.node D2M8K2.t12282 (nat_lit 26009263) (nat_lit 2238799728) (nat_lit 0) D2M8K2.t12283 from rfl, allE_node, rows12282, irow12271, rows12283]
  all_goals rfl

theorem atot12271 : totK PD2M8K2 D2M8K2.u12271 = [42866401516, 376754539194, 882457000097, 468412248525, 26967797195, 0, 0, 0] := by
  rw [show D2M8K2.u12271 = KTree.node D2M8K2.t12282 (nat_lit 26009263) (nat_lit 2238799728) (nat_lit 0) D2M8K2.t12283 from rfl, totK_node, tot12282, tot12283]
  decide +kernel

theorem arows12273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12273 = true := by
  rw [show D2M8K2.u12273 = KTree.node D2M8K2.t12284 (nat_lit 26014259) (nat_lit 2864044449) (nat_lit 0) D2M8K2.t12285 from rfl, allE_node, rows12284, irow12273, rows12285]
  all_goals rfl

theorem atot12273 : totK PD2M8K2 D2M8K2.u12273 = [378446677273, 945602682540, 479579809903, 35572509608, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12273 = KTree.node D2M8K2.t12284 (nat_lit 26014259) (nat_lit 2864044449) (nat_lit 0) D2M8K2.t12285 from rfl, totK_node, tot12284, tot12285]
  decide +kernel

theorem arows12274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12274 = true := by
  rw [show D2M8K2.u12274 = KTree.node D2M8K2.t12286 (nat_lit 26015910) (nat_lit 3877539324) (nat_lit 0) D2M8K2.t12287 from rfl, allE_node, rows12286, irow12274, rows12287]
  all_goals rfl

theorem atot12274 : totK PD2M8K2 D2M8K2.u12274 = [18591110785, 511268836171, 944114235390, 291498904086, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u12274 = KTree.node D2M8K2.t12286 (nat_lit 26015910) (nat_lit 3877539324) (nat_lit 0) D2M8K2.t12287 from rfl, totK_node, tot12286, tot12287]
  decide +kernel

theorem arows12286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12286 = true := by
  rw [show D2M8K2.u12286 = KTree.node D2M8K2.t12288 (nat_lit 26017272) (nat_lit 2686065782) (nat_lit 0) D2M8K2.t12289 from rfl, allE_node, rows12288, irow12286, rows12289]
  all_goals rfl

theorem atot12286 : totK PD2M8K2 D2M8K2.u12286 = [333142164854, 885622037119, 541194480428, 60056043446, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12286 = KTree.node D2M8K2.t12288 (nat_lit 26017272) (nat_lit 2686065782) (nat_lit 0) D2M8K2.t12289 from rfl, totK_node, tot12288, tot12289]
  decide +kernel

theorem arows12287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12287 = true := by
  rw [show D2M8K2.u12287 = KTree.node D2M8K2.t12290 (nat_lit 26018840) (nat_lit 3721919425) (nat_lit 0) D2M8K2.t12291 from rfl, allE_node, rows12290, irow12287, rows12291]
  all_goals rfl

theorem atot12287 : totK PD2M8K2 D2M8K2.u12287 = [91718010228, 667635598535, 879078452147, 164836697200, 2165917952, 0, 0, 0] := by
  rw [show D2M8K2.u12287 = KTree.node D2M8K2.t12290 (nat_lit 26018840) (nat_lit 3721919425) (nat_lit 0) D2M8K2.t12291 from rfl, totK_node, tot12290, tot12291]
  decide +kernel

theorem arows12289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12289 = true := by
  rw [show D2M8K2.u12289 = KTree.node D2M8K2.t12292 (nat_lit 26020778) (nat_lit 4117642644) (nat_lit 0) D2M8K2.t12293 from rfl, allE_node, rows12292, irow12289, rows12293]
  all_goals rfl

theorem atot12289 : totK PD2M8K2 D2M8K2.u12289 = [326274180204, 857491935713, 547664573371, 86452036857, 2814597007, 0, 0, 0] := by
  rw [show D2M8K2.u12289 = KTree.node D2M8K2.t12292 (nat_lit 26020778) (nat_lit 4117642644) (nat_lit 0) D2M8K2.t12293 from rfl, totK_node, tot12292, tot12293]
  decide +kernel

theorem arows12290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12290 = true := by
  rw [show D2M8K2.u12290 = KTree.node D2M8K2.t12294 (nat_lit 26023044) (nat_lit 2781556781) (nat_lit 0) D2M8K2.t12295 from rfl, allE_node, rows12294, irow12290, rows12295]
  all_goals rfl

theorem atot12290 : totK PD2M8K2 D2M8K2.u12290 = [0, 420326024920, 965660761389, 366063383232, 17133510885, 0, 0, 0] := by
  rw [show D2M8K2.u12290 = KTree.node D2M8K2.t12294 (nat_lit 26023044) (nat_lit 2781556781) (nat_lit 0) D2M8K2.t12295 from rfl, totK_node, tot12294, tot12295]
  decide +kernel

theorem arows12293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12293 = true := by
  rw [show D2M8K2.u12293 = KTree.node D2M8K2.t12296 (nat_lit 26024937) (nat_lit 1916366651) (nat_lit 0) D2M8K2.t12297 from rfl, allE_node, rows12296, irow12293, rows12297]
  all_goals rfl

theorem atot12293 : totK PD2M8K2 D2M8K2.u12293 = [0, 286499495932, 854853679724, 534240368772, 62451104627, 1239866073, 0, 0] := by
  rw [show D2M8K2.u12293 = KTree.node D2M8K2.t12296 (nat_lit 26024937) (nat_lit 1916366651) (nat_lit 0) D2M8K2.t12297 from rfl, totK_node, tot12296, tot12297]
  decide +kernel

theorem arows12294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12294 = true := by
  rw [show D2M8K2.u12294 = KTree.node D2M8K2.t12298 (nat_lit 26027464) (nat_lit 3831628960) (nat_lit 0) D2M8K2.t12299 from rfl, allE_node, rows12298, irow12294, rows12299]
  all_goals rfl

theorem atot12294 : totK PD2M8K2 D2M8K2.u12294 = [0, 199003207278, 777593711522, 738700764146, 85516987752, 0, 0, 0] := by
  rw [show D2M8K2.u12294 = KTree.node D2M8K2.t12298 (nat_lit 26027464) (nat_lit 3831628960) (nat_lit 0) D2M8K2.t12299 from rfl, totK_node, tot12298, tot12299]
  decide +kernel

theorem arows12296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12296 = true := by
  rw [show D2M8K2.u12296 = KTree.node D2M8K2.t12300 (nat_lit 26028670) (nat_lit 3909563016) (nat_lit 0) D2M8K2.t12301 from rfl, allE_node, rows12300, irow12296, rows12301]
  all_goals rfl

theorem atot12296 : totK PD2M8K2 D2M8K2.u12296 = [0, 391782801324, 968697845765, 429458595551, 23793415913, 0, 0, 0] := by
  rw [show D2M8K2.u12296 = KTree.node D2M8K2.t12300 (nat_lit 26028670) (nat_lit 3909563016) (nat_lit 0) D2M8K2.t12301 from rfl, totK_node, tot12300, tot12301]
  decide +kernel

theorem arows12297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12297 = true := by
  rw [show D2M8K2.u12297 = KTree.node D2M8K2.t12302 (nat_lit 26035314) (nat_lit 3451040612) (nat_lit 0) D2M8K2.t12303 from rfl, allE_node, rows12302, irow12297, rows12303]
  all_goals rfl

theorem atot12297 : totK PD2M8K2 D2M8K2.u12297 = [0, 263288827348, 827157353310, 613620912311, 79102616854, 1171084559, 0, 0] := by
  rw [show D2M8K2.u12297 = KTree.node D2M8K2.t12302 (nat_lit 26035314) (nat_lit 3451040612) (nat_lit 0) D2M8K2.t12303 from rfl, totK_node, tot12302, tot12303]
  decide +kernel

theorem arows12301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12301 = true := by
  rw [show D2M8K2.u12301 = KTree.node D2M8K2.t12304 (nat_lit 26037013) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t12305 from rfl, allE_node, rows12304, irow12301, rows12305]
  all_goals rfl

theorem atot12301 : totK PD2M8K2 D2M8K2.u12301 = [0, 117140089354, 593125281726, 793905077265, 236922176757, 11934365838, 0, 0] := by
  rw [show D2M8K2.u12301 = KTree.node D2M8K2.t12304 (nat_lit 26037013) (nat_lit 1243102186) (nat_lit 0) D2M8K2.t12305 from rfl, totK_node, tot12304, tot12305]
  decide +kernel

theorem arows12302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12302 = true := by
  rw [show D2M8K2.u12302 = KTree.node D2M8K2.t12306 (nat_lit 26038485) (nat_lit 1736213203) (nat_lit 0) D2M8K2.t12307 from rfl, allE_node, rows12306, irow12302, rows12307]
  all_goals rfl

theorem atot12302 : totK PD2M8K2 D2M8K2.u12302 = [0, 305402984584, 905899831427, 540002566533, 39693242656, 0, 0, 0] := by
  rw [show D2M8K2.u12302 = KTree.node D2M8K2.t12306 (nat_lit 26038485) (nat_lit 1736213203) (nat_lit 0) D2M8K2.t12307 from rfl, totK_node, tot12306, tot12307]
  decide +kernel

theorem arows12304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12304 = true := by
  rw [show D2M8K2.u12304 = KTree.node D2M8K2.t12308 (nat_lit 26040483) (nat_lit 3458224104) (nat_lit 0) D2M8K2.t12309 from rfl, allE_node, rows12308, irow12304, rows12309]
  all_goals rfl

theorem atot12304 : totK PD2M8K2 D2M8K2.u12304 = [0, 163963065441, 693832469613, 728904262862, 154318869085, 4720618446, 0, 0] := by
  rw [show D2M8K2.u12304 = KTree.node D2M8K2.t12308 (nat_lit 26040483) (nat_lit 3458224104) (nat_lit 0) D2M8K2.t12309 from rfl, totK_node, tot12308, tot12309]
  decide +kernel

theorem arows12305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12305 = true := by
  rw [show D2M8K2.u12305 = KTree.node D2M8K2.t12310 (nat_lit 26042665) (nat_lit 1451707094) (nat_lit 0) D2M8K2.t12311 from rfl, allE_node, rows12310, irow12305, rows12311]
  all_goals rfl

theorem atot12305 : totK PD2M8K2 D2M8K2.u12305 = [182717929658, 612477704967, 663163731683, 316849252881, 27798800829, 0, 0, 0] := by
  rw [show D2M8K2.u12305 = KTree.node D2M8K2.t12310 (nat_lit 26042665) (nat_lit 1451707094) (nat_lit 0) D2M8K2.t12311 from rfl, totK_node, tot12310, tot12311]
  decide +kernel

theorem arows12308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12308 = true := by
  rw [show D2M8K2.u12308 = KTree.node D2M8K2.t12312 (nat_lit 26045915) (nat_lit 2736102266) (nat_lit 0) D2M8K2.t12313 from rfl, allE_node, rows12312, irow12308, rows12313]
  all_goals rfl

theorem atot12308 : totK PD2M8K2 D2M8K2.u12308 = [229696409040, 778932785252, 659189012728, 112654957093, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u12308 = KTree.node D2M8K2.t12312 (nat_lit 26045915) (nat_lit 2736102266) (nat_lit 0) D2M8K2.t12313 from rfl, totK_node, tot12312, tot12313]
  decide +kernel

theorem arows12309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12309 = true := by
  rw [show D2M8K2.u12309 = KTree.node D2M8K2.t12314 (nat_lit 26048286) (nat_lit 3846353272) (nat_lit 0) D2M8K2.t12315 from rfl, allE_node, rows12314, irow12309, rows12315]
  all_goals rfl

theorem atot12309 : totK PD2M8K2 D2M8K2.u12309 = [250509358440, 808290656861, 691577281915, 81856774622, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12309 = KTree.node D2M8K2.t12314 (nat_lit 26048286) (nat_lit 3846353272) (nat_lit 0) D2M8K2.t12315 from rfl, totK_node, tot12314, tot12315]
  decide +kernel

theorem arows12311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12311 = true := by
  rw [show D2M8K2.u12311 = KTree.node D2M8K2.t12316 (nat_lit 26049509) (nat_lit 2355619753) (nat_lit 0) D2M8K2.t12317 from rfl, allE_node, rows12316, irow12311, rows12317]
  all_goals rfl

theorem atot12311 : totK PD2M8K2 D2M8K2.u12311 = [175307437418, 705217039696, 704216260968, 219539875415, 21383112939, 0, 0, 0] := by
  rw [show D2M8K2.u12311 = KTree.node D2M8K2.t12316 (nat_lit 26049509) (nat_lit 2355619753) (nat_lit 0) D2M8K2.t12317 from rfl, totK_node, tot12316, tot12317]
  decide +kernel

theorem arows12312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12312 = true := by
  rw [show D2M8K2.u12312 = KTree.node D2M8K2.t12318 (nat_lit 26050993) (nat_lit 1344398349) (nat_lit 0) D2M8K2.t12319 from rfl, allE_node, rows12318, irow12312, rows12319]
  all_goals rfl

theorem atot12312 : totK PD2M8K2 D2M8K2.u12312 = [127020531876, 521100781737, 781873084375, 352631810998, 15981252100, 0, 0, 0] := by
  rw [show D2M8K2.u12312 = KTree.node D2M8K2.t12318 (nat_lit 26050993) (nat_lit 1344398349) (nat_lit 0) D2M8K2.t12319 from rfl, totK_node, tot12318, tot12319]
  decide +kernel

theorem arows12317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12317 = true := by
  rw [show D2M8K2.u12317 = KTree.node D2M8K2.t12320 (nat_lit 26052519) (nat_lit 3623179397) (nat_lit 0) D2M8K2.t12321 from rfl, allE_node, rows12320, irow12317, rows12321]
  all_goals rfl

theorem atot12317 : totK PD2M8K2 D2M8K2.u12317 = [294067549413, 881257954950, 584180874245, 53259611338, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12317 = KTree.node D2M8K2.t12320 (nat_lit 26052519) (nat_lit 3623179397) (nat_lit 0) D2M8K2.t12321 from rfl, totK_node, tot12320, tot12321]
  decide +kernel

theorem arows12318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12318 = true := by
  rw [show D2M8K2.u12318 = KTree.node D2M8K2.t12322 (nat_lit 26054238) (nat_lit 3585813394) (nat_lit 0) D2M8K2.t12323 from rfl, allE_node, rows12322, irow12318, rows12323]
  all_goals rfl

theorem atot12318 : totK PD2M8K2 D2M8K2.u12318 = [84672624166, 537698624988, 853131689590, 278862319474, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u12318 = KTree.node D2M8K2.t12322 (nat_lit 26054238) (nat_lit 3585813394) (nat_lit 0) D2M8K2.t12323 from rfl, totK_node, tot12322, tot12323]
  decide +kernel

theorem arows12320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12320 = true := by
  rw [show D2M8K2.u12320 = KTree.node D2M8K2.t12324 (nat_lit 26055897) (nat_lit 1877547576) (nat_lit 0) D2M8K2.t12325 from rfl, allE_node, rows12324, irow12320, rows12325]
  all_goals rfl

theorem atot12320 : totK PD2M8K2 D2M8K2.u12320 = [336608155233, 903996832966, 543820237402, 45708553826, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12320 = KTree.node D2M8K2.t12324 (nat_lit 26055897) (nat_lit 1877547576) (nat_lit 0) D2M8K2.t12325 from rfl, totK_node, tot12324, tot12325]
  decide +kernel

theorem arows12321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12321 = true := by
  rw [show D2M8K2.u12321 = KTree.node D2M8K2.t12326 (nat_lit 26057612) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t12327 from rfl, allE_node, rows12326, irow12321, rows12327]
  all_goals rfl

theorem atot12321 : totK PD2M8K2 D2M8K2.u12321 = [86527685341, 512635135437, 867345469446, 296983034022, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u12321 = KTree.node D2M8K2.t12326 (nat_lit 26057612) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t12327 from rfl, totK_node, tot12326, tot12327]
  decide +kernel

theorem arows12324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12324 = true := by
  rw [show D2M8K2.u12324 = KTree.node D2M8K2.t12328 (nat_lit 26058968) (nat_lit 3500368473) (nat_lit 0) D2M8K2.t12329 from rfl, allE_node, rows12328, irow12324, rows12329]
  all_goals rfl

theorem atot12324 : totK PD2M8K2 D2M8K2.u12324 = [358558880073, 932641026673, 507642909484, 41342799017, 0, 0, 0, 0] := by
  rw [show D2M8K2.u12324 = KTree.node D2M8K2.t12328 (nat_lit 26058968) (nat_lit 3500368473) (nat_lit 0) D2M8K2.t12329 from rfl, totK_node, tot12328, tot12329]
  decide +kernel

theorem arows12325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12325 = true := by
  rw [show D2M8K2.u12325 = KTree.node D2M8K2.t12330 (nat_lit 26060646) (nat_lit 2917531415) (nat_lit 0) D2M8K2.t12331 from rfl, allE_node, rows12330, irow12325, rows12331]
  all_goals rfl

theorem atot12325 : totK PD2M8K2 D2M8K2.u12325 = [0, 586677597424, 1004829648112, 220223372402, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u12325 = KTree.node D2M8K2.t12330 (nat_lit 26060646) (nat_lit 2917531415) (nat_lit 0) D2M8K2.t12331 from rfl, totK_node, tot12330, tot12331]
  decide +kernel

theorem arows12327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12327 = true := by
  rw [show D2M8K2.u12327 = KTree.node D2M8K2.t12332 (nat_lit 26066166) (nat_lit 3768856327) (nat_lit 0) D2M8K2.t12333 from rfl, allE_node, rows12332, irow12327, rows12333]
  all_goals rfl

theorem atot12327 : totK PD2M8K2 D2M8K2.u12327 = [0, 341517711471, 944182151021, 444163140543, 23418410187, 0, 0, 0] := by
  rw [show D2M8K2.u12327 = KTree.node D2M8K2.t12332 (nat_lit 26066166) (nat_lit 3768856327) (nat_lit 0) D2M8K2.t12333 from rfl, totK_node, tot12332, tot12333]
  decide +kernel

theorem arows12328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12328 = true := by
  rw [show D2M8K2.u12328 = KTree.node D2M8K2.t12334 (nat_lit 26068112) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t12335 from rfl, allE_node, rows12334, irow12328, rows12335]
  all_goals rfl

theorem atot12328 : totK PD2M8K2 D2M8K2.u12328 = [0, 165681719444, 742596201892, 745088655721, 109604223322, 1138244013, 0, 0] := by
  rw [show D2M8K2.u12328 = KTree.node D2M8K2.t12334 (nat_lit 26068112) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t12335 from rfl, totK_node, tot12334, tot12335]
  decide +kernel

theorem arows12332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12332 = true := by
  rw [show D2M8K2.u12332 = KTree.node D2M8K2.t12336 (nat_lit 26069912) (nat_lit 3642913123) (nat_lit 0) D2M8K2.t12337 from rfl, allE_node, rows12336, irow12332, rows12337]
  all_goals rfl

theorem atot12332 : totK PD2M8K2 D2M8K2.u12332 = [0, 351014644406, 958086421766, 457943763660, 25509251790, 0, 0, 0] := by
  rw [show D2M8K2.u12332 = KTree.node D2M8K2.t12336 (nat_lit 26069912) (nat_lit 3642913123) (nat_lit 0) D2M8K2.t12337 from rfl, totK_node, tot12336, tot12337]
  decide +kernel

theorem arows12333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12333 = true := by
  rw [show D2M8K2.u12333 = KTree.node D2M8K2.t12338 (nat_lit 26073227) (nat_lit 2361429863) (nat_lit 0) D2M8K2.t12339 from rfl, allE_node, rows12338, irow12333, rows12339]
  all_goals rfl

theorem atot12333 : totK PD2M8K2 D2M8K2.u12333 = [0, 387518576550, 944751739408, 446103758937, 25897365295, 0, 0, 0] := by
  rw [show D2M8K2.u12333 = KTree.node D2M8K2.t12338 (nat_lit 26073227) (nat_lit 2361429863) (nat_lit 0) D2M8K2.t12339 from rfl, totK_node, tot12338, tot12339]
  decide +kernel

theorem arows12335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12335 = true := by
  rw [show D2M8K2.u12335 = KTree.node D2M8K2.t12340 (nat_lit 26076528) (nat_lit 3668362707) (nat_lit 0) D2M8K2.t12341 from rfl, allE_node, rows12340, irow12335, rows12341]
  all_goals rfl

theorem atot12335 : totK PD2M8K2 D2M8K2.u12335 = [0, 351602936814, 952908522816, 476048696609, 24663448840, 0, 0, 0] := by
  rw [show D2M8K2.u12335 = KTree.node D2M8K2.t12340 (nat_lit 26076528) (nat_lit 3668362707) (nat_lit 0) D2M8K2.t12341 from rfl, totK_node, tot12340, tot12341]
  decide +kernel

theorem arows12336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12336 = true := by
  rw [show D2M8K2.u12336 = KTree.node D2M8K2.t12342 (nat_lit 26079553) (nat_lit 1551245451) (nat_lit 0) D2M8K2.t12343 from rfl, allE_node, rows12342, irow12336, rows12343]
  all_goals rfl

theorem atot12336 : totK PD2M8K2 D2M8K2.u12336 = [0, 367509756657, 918085891188, 467674501195, 35187629387, 0, 0, 0] := by
  rw [show D2M8K2.u12336 = KTree.node D2M8K2.t12342 (nat_lit 26079553) (nat_lit 1551245451) (nat_lit 0) D2M8K2.t12343 from rfl, totK_node, tot12342, tot12343]
  decide +kernel

theorem arows12339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12339 = true := by
  rw [show D2M8K2.u12339 = KTree.node D2M8K2.t12344 (nat_lit 26081088) (nat_lit 2683807702) (nat_lit 0) D2M8K2.t12345 from rfl, allE_node, rows12344, irow12339, rows12345]
  all_goals rfl

theorem atot12339 : totK PD2M8K2 D2M8K2.u12339 = [0, 75082883077, 645417999349, 846214295091, 182924497526, 3251202861, 0, 0] := by
  rw [show D2M8K2.u12339 = KTree.node D2M8K2.t12344 (nat_lit 26081088) (nat_lit 2683807702) (nat_lit 0) D2M8K2.t12345 from rfl, totK_node, tot12344, tot12345]
  decide +kernel

theorem arows12340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12340 = true := by
  rw [show D2M8K2.u12340 = KTree.node D2M8K2.t12346 (nat_lit 26128254) (nat_lit 3913508866) (nat_lit 0) D2M8K2.t12347 from rfl, allE_node, rows12346, irow12340, rows12347]
  all_goals rfl

theorem atot12340 : totK PD2M8K2 D2M8K2.u12340 = [0, 398509134359, 950992725206, 419717342961, 28839393758, 1725911522, 0, 0] := by
  rw [show D2M8K2.u12340 = KTree.node D2M8K2.t12346 (nat_lit 26128254) (nat_lit 3913508866) (nat_lit 0) D2M8K2.t12347 from rfl, totK_node, tot12346, tot12347]
  decide +kernel

theorem arows12342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12342 = true := by
  rw [show D2M8K2.u12342 = KTree.node D2M8K2.t12348 (nat_lit 26129778) (nat_lit 2444759915) (nat_lit 0) D2M8K2.t12349 from rfl, allE_node, rows12348, irow12342, rows12349]
  all_goals rfl

theorem atot12342 : totK PD2M8K2 D2M8K2.u12342 = [0, 101536020149, 667426210485, 870767452106, 151465500773, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12342 = KTree.node D2M8K2.t12348 (nat_lit 26129778) (nat_lit 2444759915) (nat_lit 0) D2M8K2.t12349 from rfl, totK_node, tot12348, tot12349]
  decide +kernel

theorem arows12343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12343 = true := by
  rw [show D2M8K2.u12343 = KTree.node D2M8K2.t12350 (nat_lit 26135020) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t12351 from rfl, allE_node, rows12350, irow12343, rows12351]
  all_goals rfl

theorem atot12343 : totK PD2M8K2 D2M8K2.u12343 = [0, 340111949293, 930813680621, 491899685134, 28692121409, 0, 0, 0] := by
  rw [show D2M8K2.u12343 = KTree.node D2M8K2.t12350 (nat_lit 26135020) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t12351 from rfl, totK_node, tot12350, tot12351]
  decide +kernel

theorem arows12349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12349 = true := by
  rw [show D2M8K2.u12349 = KTree.node D2M8K2.t12352 (nat_lit 26136740) (nat_lit 2760736178) (nat_lit 0) D2M8K2.t12353 from rfl, allE_node, rows12352, irow12349, rows12353]
  all_goals rfl

theorem atot12349 : totK PD2M8K2 D2M8K2.u12349 = [0, 58286174097, 510581751788, 905052930924, 266039743806, 12983449796, 0, 0] := by
  rw [show D2M8K2.u12349 = KTree.node D2M8K2.t12352 (nat_lit 26136740) (nat_lit 2760736178) (nat_lit 0) D2M8K2.t12353 from rfl, totK_node, tot12352, tot12353]
  decide +kernel

theorem arows12350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12350 = true := by
  rw [show D2M8K2.u12350 = KTree.node D2M8K2.t12354 (nat_lit 26138756) (nat_lit 2862694654) (nat_lit 0) D2M8K2.t12355 from rfl, allE_node, rows12354, irow12350, rows12355]
  all_goals rfl

theorem atot12350 : totK PD2M8K2 D2M8K2.u12350 = [0, 347947993520, 943633797250, 482043610132, 26210564136, 0, 0, 0] := by
  rw [show D2M8K2.u12350 = KTree.node D2M8K2.t12354 (nat_lit 26138756) (nat_lit 2862694654) (nat_lit 0) D2M8K2.t12355 from rfl, totK_node, tot12354, tot12355]
  decide +kernel

theorem arows12352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12352 = true := by
  rw [show D2M8K2.u12352 = KTree.node D2M8K2.t12356 (nat_lit 26140475) (nat_lit 2130495937) (nat_lit 0) D2M8K2.t12357 from rfl, allE_node, rows12356, irow12352, rows12357]
  all_goals rfl

theorem atot12352 : totK PD2M8K2 D2M8K2.u12352 = [0, 54618809271, 498623695614, 917775875007, 274993963252, 13184317400, 0, 0] := by
  rw [show D2M8K2.u12352 = KTree.node D2M8K2.t12356 (nat_lit 26140475) (nat_lit 2130495937) (nat_lit 0) D2M8K2.t12357 from rfl, totK_node, tot12356, tot12357]
  decide +kernel

theorem arows12353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12353 = true := by
  rw [show D2M8K2.u12353 = KTree.node D2M8K2.t12358 (nat_lit 26141908) (nat_lit 3750081348) (nat_lit 0) D2M8K2.t12359 from rfl, allE_node, rows12358, irow12353, rows12359]
  all_goals rfl

theorem atot12353 : totK PD2M8K2 D2M8K2.u12353 = [0, 367326529273, 924168694622, 468517078894, 33297026998, 0, 0, 0] := by
  rw [show D2M8K2.u12353 = KTree.node D2M8K2.t12358 (nat_lit 26141908) (nat_lit 3750081348) (nat_lit 0) D2M8K2.t12359 from rfl, totK_node, tot12358, tot12359]
  decide +kernel

theorem arows12356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12356 = true := by
  rw [show D2M8K2.u12356 = KTree.node D2M8K2.t12360 (nat_lit 26143610) (nat_lit 2804911782) (nat_lit 0) D2M8K2.t12361 from rfl, allE_node, rows12360, irow12356, rows12361]
  all_goals rfl

theorem atot12356 : totK PD2M8K2 D2M8K2.u12356 = [0, 86868443710, 608908584106, 884357027327, 201398850670, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12356 = KTree.node D2M8K2.t12360 (nat_lit 26143610) (nat_lit 2804911782) (nat_lit 0) D2M8K2.t12361 from rfl, totK_node, tot12360, tot12361]
  decide +kernel

theorem arows12357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12357 = true := by
  rw [show D2M8K2.u12357 = KTree.node D2M8K2.t12362 (nat_lit 26145733) (nat_lit 1149479442) (nat_lit 0) D2M8K2.t12363 from rfl, allE_node, rows12362, irow12357, rows12363]
  all_goals rfl

theorem atot12357 : totK PD2M8K2 D2M8K2.u12357 = [0, 234955712631, 815793413566, 627937386720, 88192525253, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12357 = KTree.node D2M8K2.t12362 (nat_lit 26145733) (nat_lit 1149479442) (nat_lit 0) D2M8K2.t12363 from rfl, totK_node, tot12362, tot12363]
  decide +kernel

theorem arows12359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12359 = true := by
  rw [show D2M8K2.u12359 = KTree.node D2M8K2.t12364 (nat_lit 26148315) (nat_lit 1461759581) (nat_lit 0) D2M8K2.t12365 from rfl, allE_node, rows12364, irow12359, rows12365]
  all_goals rfl

theorem atot12359 : totK PD2M8K2 D2M8K2.u12359 = [0, 0, 460949779934, 963660870022, 317164440019, 17886425318, 0, 0] := by
  rw [show D2M8K2.u12359 = KTree.node D2M8K2.t12364 (nat_lit 26148315) (nat_lit 1461759581) (nat_lit 0) D2M8K2.t12365 from rfl, totK_node, tot12364, tot12365]
  decide +kernel

theorem arows12360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12360 = true := by
  rw [show D2M8K2.u12360 = KTree.node D2M8K2.t12366 (nat_lit 26149917) (nat_lit 1454504571) (nat_lit 0) D2M8K2.t12367 from rfl, allE_node, rows12366, irow12360, rows12367]
  all_goals rfl

theorem atot12360 : totK PD2M8K2 D2M8K2.u12360 = [0, 0, 163613328602, 779112245046, 655720359970, 91636885613, 1209030869, 0] := by
  rw [show D2M8K2.u12360 = KTree.node D2M8K2.t12366 (nat_lit 26149917) (nat_lit 1454504571) (nat_lit 0) D2M8K2.t12367 from rfl, totK_node, tot12366, tot12367]
  decide +kernel

theorem arows12364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12364 = true := by
  rw [show D2M8K2.u12364 = KTree.node D2M8K2.t12368 (nat_lit 26155740) (nat_lit 3149023000) (nat_lit 0) D2M8K2.t12369 from rfl, allE_node, rows12368, irow12364, rows12369]
  all_goals rfl

theorem atot12364 : totK PD2M8K2 D2M8K2.u12364 = [0, 0, 455478884327, 969891130030, 326973872841, 13546714812, 0, 0] := by
  rw [show D2M8K2.u12364 = KTree.node D2M8K2.t12368 (nat_lit 26155740) (nat_lit 3149023000) (nat_lit 0) D2M8K2.t12369 from rfl, totK_node, tot12368, tot12369]
  decide +kernel

theorem arows12365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12365 = true := by
  rw [show D2M8K2.u12365 = KTree.node D2M8K2.t12370 (nat_lit 26159624) (nat_lit 3690024426) (nat_lit 0) D2M8K2.t12371 from rfl, allE_node, rows12370, irow12365, rows12371]
  all_goals rfl

theorem atot12365 : totK PD2M8K2 D2M8K2.u12365 = [0, 0, 439452796519, 964342884022, 343507665200, 14992389632, 0, 0] := by
  rw [show D2M8K2.u12365 = KTree.node D2M8K2.t12370 (nat_lit 26159624) (nat_lit 3690024426) (nat_lit 0) D2M8K2.t12371 from rfl, totK_node, tot12370, tot12371]
  decide +kernel

theorem arows12367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12367 = true := by
  rw [show D2M8K2.u12367 = KTree.node D2M8K2.t12372 (nat_lit 26162825) (nat_lit 1321763883) (nat_lit 0) D2M8K2.t12373 from rfl, allE_node, rows12372, irow12367, rows12373]
  all_goals rfl

theorem atot12367 : totK PD2M8K2 D2M8K2.u12367 = [0, 0, 382973249544, 950855930901, 394970803426, 21949701645, 0, 0] := by
  rw [show D2M8K2.u12367 = KTree.node D2M8K2.t12372 (nat_lit 26162825) (nat_lit 1321763883) (nat_lit 0) D2M8K2.t12373 from rfl, totK_node, tot12372, tot12373]
  decide +kernel

theorem arows12368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12368 = true := by
  rw [show D2M8K2.u12368 = KTree.node D2M8K2.t12374 (nat_lit 26172621) (nat_lit 1494925353) (nat_lit 0) D2M8K2.t12375 from rfl, allE_node, rows12374, irow12368, rows12375]
  all_goals rfl

theorem atot12368 : totK PD2M8K2 D2M8K2.u12368 = [0, 188814269997, 737235877053, 752961763027, 139930917848, 1369587937, 0, 0] := by
  rw [show D2M8K2.u12368 = KTree.node D2M8K2.t12374 (nat_lit 26172621) (nat_lit 1494925353) (nat_lit 0) D2M8K2.t12375 from rfl, totK_node, tot12374, tot12375]
  decide +kernel

theorem arows12371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12371 = true := by
  rw [show D2M8K2.u12371 = KTree.node D2M8K2.t12376 (nat_lit 26173774) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t12377 from rfl, allE_node, rows12376, irow12371, rows12377]
  all_goals rfl

theorem atot12371 : totK PD2M8K2 D2M8K2.u12371 = [0, 251067951314, 773232551784, 607135353652, 185546490512, 21400436502, 0, 0] := by
  rw [show D2M8K2.u12371 = KTree.node D2M8K2.t12376 (nat_lit 26173774) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t12377 from rfl, totK_node, tot12376, tot12377]
  decide +kernel

theorem arows12372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12372 = true := by
  rw [show D2M8K2.u12372 = KTree.node D2M8K2.t12378 (nat_lit 26175228) (nat_lit 2658869214) (nat_lit 0) D2M8K2.t12379 from rfl, allE_node, rows12378, irow12372, rows12379]
  all_goals rfl

theorem atot12372 : totK PD2M8K2 D2M8K2.u12372 = [0, 66560335648, 449166622623, 878053973109, 386318267573, 16098541941, 0, 0] := by
  rw [show D2M8K2.u12372 = KTree.node D2M8K2.t12378 (nat_lit 26175228) (nat_lit 2658869214) (nat_lit 0) D2M8K2.t12379 from rfl, totK_node, tot12378, tot12379]
  decide +kernel

theorem arows12374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12374 = true := by
  rw [show D2M8K2.u12374 = KTree.node D2M8K2.t12380 (nat_lit 26176513) (nat_lit 1418466873) (nat_lit 0) D2M8K2.t12381 from rfl, allE_node, rows12380, irow12374, rows12381]
  all_goals rfl

theorem atot12374 : totK PD2M8K2 D2M8K2.u12374 = [0, 346408873782, 923377748338, 517788304842, 39362004387, 0, 0, 0] := by
  rw [show D2M8K2.u12374 = KTree.node D2M8K2.t12380 (nat_lit 26176513) (nat_lit 1418466873) (nat_lit 0) D2M8K2.t12381 from rfl, totK_node, tot12380, tot12381]
  decide +kernel

theorem arows12375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12375 = true := by
  rw [show D2M8K2.u12375 = KTree.node D2M8K2.t12382 (nat_lit 26178316) (nat_lit 3877811141) (nat_lit 0) D2M8K2.t12383 from rfl, allE_node, rows12382, irow12375, rows12383]
  all_goals rfl

theorem atot12375 : totK PD2M8K2 D2M8K2.u12375 = [0, 66623131732, 580293379724, 880821384124, 242130747526, 11873025674, 0, 0] := by
  rw [show D2M8K2.u12375 = KTree.node D2M8K2.t12382 (nat_lit 26178316) (nat_lit 3877811141) (nat_lit 0) D2M8K2.t12383 from rfl, totK_node, tot12382, tot12383]
  decide +kernel

theorem arows12380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12380 = true := by
  rw [show D2M8K2.u12380 = KTree.node D2M8K2.t12384 (nat_lit 26180311) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t12385 from rfl, allE_node, rows12384, irow12380, rows12385]
  all_goals rfl

theorem atot12380 : totK PD2M8K2 D2M8K2.u12380 = [0, 346591274728, 913832820171, 524231781474, 45854674189, 0, 0, 0] := by
  rw [show D2M8K2.u12380 = KTree.node D2M8K2.t12384 (nat_lit 26180311) (nat_lit 2375701447) (nat_lit 0) D2M8K2.t12385 from rfl, totK_node, tot12384, tot12385]
  decide +kernel

theorem arows12381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12381 = true := by
  rw [show D2M8K2.u12381 = KTree.node D2M8K2.t12386 (nat_lit 26182106) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t12387 from rfl, allE_node, rows12386, irow12381, rows12387]
  all_goals rfl

theorem atot12381 : totK PD2M8K2 D2M8K2.u12381 = [0, 82003072397, 581461265736, 862234558644, 245364896556, 12040273252, 0, 0] := by
  rw [show D2M8K2.u12381 = KTree.node D2M8K2.t12386 (nat_lit 26182106) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t12387 from rfl, totK_node, tot12386, tot12387]
  decide +kernel

theorem arows12383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12383 = true := by
  rw [show D2M8K2.u12383 = KTree.node D2M8K2.t12388 (nat_lit 26183507) (nat_lit 2653316580) (nat_lit 0) D2M8K2.t12389 from rfl, allE_node, rows12388, irow12383, rows12389]
  all_goals rfl

theorem atot12383 : totK PD2M8K2 D2M8K2.u12383 = [0, 341796845744, 918326187866, 520766628417, 44274709678, 0, 0, 0] := by
  rw [show D2M8K2.u12383 = KTree.node D2M8K2.t12388 (nat_lit 26183507) (nat_lit 2653316580) (nat_lit 0) D2M8K2.t12389 from rfl, totK_node, tot12388, tot12389]
  decide +kernel

theorem arows12384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12384 = true := by
  rw [show D2M8K2.u12384 = KTree.node D2M8K2.t12390 (nat_lit 26185562) (nat_lit 4217839901) (nat_lit 0) D2M8K2.t12391 from rfl, allE_node, rows12390, irow12384, rows12391]
  all_goals rfl

theorem atot12384 : totK PD2M8K2 D2M8K2.u12384 = [0, 111463607843, 660985761597, 883270314415, 179995990834, 3880716147, 0, 0] := by
  rw [show D2M8K2.u12384 = KTree.node D2M8K2.t12390 (nat_lit 26185562) (nat_lit 4217839901) (nat_lit 0) D2M8K2.t12391 from rfl, totK_node, tot12390, tot12391]
  decide +kernel

theorem arows12387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12387 = true := by
  rw [show D2M8K2.u12387 = KTree.node D2M8K2.t12392 (nat_lit 26187633) (nat_lit 1364278351) (nat_lit 0) D2M8K2.t12393 from rfl, allE_node, rows12392, irow12387, rows12393]
  all_goals rfl

theorem atot12387 : totK PD2M8K2 D2M8K2.u12387 = [0, 214454954508, 776127738588, 698050738188, 122707991737, 1325368197, 0, 0] := by
  rw [show D2M8K2.u12387 = KTree.node D2M8K2.t12392 (nat_lit 26187633) (nat_lit 1364278351) (nat_lit 0) D2M8K2.t12393 from rfl, totK_node, tot12392, tot12393]
  decide +kernel

theorem arows12388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12388 = true := by
  rw [show D2M8K2.u12388 = KTree.node D2M8K2.t12394 (nat_lit 26210420) (nat_lit 3652605966) (nat_lit 0) D2M8K2.t12395 from rfl, allE_node, rows12394, irow12388, rows12395]
  all_goals rfl

theorem atot12388 : totK PD2M8K2 D2M8K2.u12388 = [0, 243838384780, 729682041698, 622997826502, 180475166822, 8405174358, 0, 0] := by
  rw [show D2M8K2.u12388 = KTree.node D2M8K2.t12394 (nat_lit 26210420) (nat_lit 3652605966) (nat_lit 0) D2M8K2.t12395 from rfl, totK_node, tot12394, tot12395]
  decide +kernel

theorem arows12390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12390 = true := by
  rw [show D2M8K2.u12390 = KTree.node D2M8K2.t12396 (nat_lit 26212030) (nat_lit 3804635706) (nat_lit 0) D2M8K2.t12397 from rfl, allE_node, rows12396, irow12390, rows12397]
  all_goals rfl

theorem atot12390 : totK PD2M8K2 D2M8K2.u12390 = [0, 161483599102, 725024413589, 757988571536, 117126006925, 1310166938, 0, 0] := by
  rw [show D2M8K2.u12390 = KTree.node D2M8K2.t12396 (nat_lit 26212030) (nat_lit 3804635706) (nat_lit 0) D2M8K2.t12397 from rfl, totK_node, tot12396, tot12397]
  decide +kernel

theorem arows12391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12391 = true := by
  rw [show D2M8K2.u12391 = KTree.node D2M8K2.t12398 (nat_lit 26214369) (nat_lit 1816062054) (nat_lit 0) D2M8K2.t12399 from rfl, allE_node, rows12398, irow12391, rows12399]
  all_goals rfl

theorem atot12391 : totK PD2M8K2 D2M8K2.u12391 = [0, 319223117698, 865749032663, 590481828696, 59832494654, 0, 0, 0] := by
  rw [show D2M8K2.u12391 = KTree.node D2M8K2.t12398 (nat_lit 26214369) (nat_lit 1816062054) (nat_lit 0) D2M8K2.t12399 from rfl, totK_node, tot12398, tot12399]
  decide +kernel

theorem arows12395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12395 = true := by
  rw [show D2M8K2.u12395 = KTree.node D2M8K2.t12400 (nat_lit 26215947) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t12401 from rfl, allE_node, rows12400, irow12395, rows12401]
  all_goals rfl

theorem atot12395 : totK PD2M8K2 D2M8K2.u12395 = [0, 98090759061, 624119759043, 828123921737, 265463219676, 13604428459, 0, 0] := by
  rw [show D2M8K2.u12395 = KTree.node D2M8K2.t12400 (nat_lit 26215947) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t12401 from rfl, totK_node, tot12400, tot12401]
  decide +kernel

theorem arows12396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12396 = true := by
  rw [show D2M8K2.u12396 = KTree.node D2M8K2.t12402 (nat_lit 26217535) (nat_lit 2139176882) (nat_lit 0) D2M8K2.t12403 from rfl, allE_node, rows12402, irow12396, rows12403]
  all_goals rfl

theorem atot12396 : totK PD2M8K2 D2M8K2.u12396 = [0, 267998909027, 785571561526, 639568412051, 125549613351, 1409560813, 0, 0] := by
  rw [show D2M8K2.u12396 = KTree.node D2M8K2.t12402 (nat_lit 26217535) (nat_lit 2139176882) (nat_lit 0) D2M8K2.t12403 from rfl, totK_node, tot12402, tot12403]
  decide +kernel

theorem arows12398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12398 = true := by
  rw [show D2M8K2.u12398 = KTree.node D2M8K2.t12404 (nat_lit 26218960) (nat_lit 3384911032) (nat_lit 0) D2M8K2.t12405 from rfl, allE_node, rows12404, irow12398, rows12405]
  all_goals rfl

theorem atot12398 : totK PD2M8K2 D2M8K2.u12398 = [0, 171045894958, 712966502811, 766306918155, 153925656383, 2309606161, 0, 0] := by
  rw [show D2M8K2.u12398 = KTree.node D2M8K2.t12404 (nat_lit 26218960) (nat_lit 3384911032) (nat_lit 0) D2M8K2.t12405 from rfl, totK_node, tot12404, tot12405]
  decide +kernel

theorem arows12399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12399 = true := by
  rw [show D2M8K2.u12399 = KTree.node D2M8K2.t12406 (nat_lit 26224233) (nat_lit 1900243730) (nat_lit 0) D2M8K2.t12407 from rfl, allE_node, rows12406, irow12399, rows12407]
  all_goals rfl

theorem atot12399 : totK PD2M8K2 D2M8K2.u12399 = [0, 245517993875, 724557341989, 644442444967, 168171440093, 10740121073, 0, 0] := by
  rw [show D2M8K2.u12399 = KTree.node D2M8K2.t12406 (nat_lit 26224233) (nat_lit 1900243730) (nat_lit 0) D2M8K2.t12407 from rfl, totK_node, tot12406, tot12407]
  decide +kernel

theorem arows12402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12402 = true := by
  rw [show D2M8K2.u12402 = KTree.node D2M8K2.t12408 (nat_lit 26225451) (nat_lit 3722933930) (nat_lit 0) D2M8K2.t12409 from rfl, allE_node, rows12408, irow12402, rows12409]
  all_goals rfl

theorem atot12402 : totK PD2M8K2 D2M8K2.u12402 = [0, 177781631315, 766642706478, 737150118375, 109149606395, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12402 = KTree.node D2M8K2.t12408 (nat_lit 26225451) (nat_lit 3722933930) (nat_lit 0) D2M8K2.t12409 from rfl, totK_node, tot12408, tot12409]
  decide +kernel

theorem arows12403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12403 = true := by
  rw [show D2M8K2.u12403 = KTree.node D2M8K2.t12410 (nat_lit 26227733) (nat_lit 2183272644) (nat_lit 0) D2M8K2.t12411 from rfl, allE_node, rows12410, irow12403, rows12411]
  all_goals rfl

theorem atot12403 : totK PD2M8K2 D2M8K2.u12403 = [0, 252582328900, 759358078093, 653442521820, 131344077316, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12403 = KTree.node D2M8K2.t12410 (nat_lit 26227733) (nat_lit 2183272644) (nat_lit 0) D2M8K2.t12411 from rfl, totK_node, tot12410, tot12411]
  decide +kernel

theorem arows12405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12405 = true := by
  rw [show D2M8K2.u12405 = KTree.node D2M8K2.t12412 (nat_lit 26229641) (nat_lit 1776290947) (nat_lit 0) D2M8K2.t12413 from rfl, allE_node, rows12412, irow12405, rows12413]
  all_goals rfl

theorem atot12405 : totK PD2M8K2 D2M8K2.u12405 = [0, 115139470398, 623800996343, 838976917822, 198811982478, 4880895167, 0, 0] := by
  rw [show D2M8K2.u12405 = KTree.node D2M8K2.t12412 (nat_lit 26229641) (nat_lit 1776290947) (nat_lit 0) D2M8K2.t12413 from rfl, totK_node, tot12412, tot12413]
  decide +kernel

theorem arows12406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12406 = true := by
  rw [show D2M8K2.u12406 = KTree.node D2M8K2.t12414 (nat_lit 26252791) (nat_lit 2357548626) (nat_lit 0) D2M8K2.t12415 from rfl, allE_node, rows12414, irow12406, rows12415]
  all_goals rfl

theorem atot12406 : totK PD2M8K2 D2M8K2.u12406 = [0, 363092797389, 940456191994, 445019232394, 23577915511, 0, 0, 0] := by
  rw [show D2M8K2.u12406 = KTree.node D2M8K2.t12414 (nat_lit 26252791) (nat_lit 2357548626) (nat_lit 0) D2M8K2.t12415 from rfl, totK_node, tot12414, tot12415]
  decide +kernel

theorem arows12413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12413 = true := by
  rw [show D2M8K2.u12413 = KTree.node D2M8K2.t12416 (nat_lit 26254663) (nat_lit 2336060891) (nat_lit 0) D2M8K2.t12417 from rfl, allE_node, rows12416, irow12413, rows12417]
  all_goals rfl

theorem atot12413 : totK PD2M8K2 D2M8K2.u12413 = [0, 92870497502, 663540104384, 896106792447, 146440869589, 1310517177, 0, 0] := by
  rw [show D2M8K2.u12413 = KTree.node D2M8K2.t12416 (nat_lit 26254663) (nat_lit 2336060891) (nat_lit 0) D2M8K2.t12417 from rfl, totK_node, tot12416, tot12417]
  decide +kernel

theorem arows12414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12414 = true := by
  rw [show D2M8K2.u12414 = KTree.node D2M8K2.t12418 (nat_lit 26256436) (nat_lit 3905536107) (nat_lit 0) D2M8K2.t12419 from rfl, allE_node, rows12418, irow12414, rows12419]
  all_goals rfl

theorem atot12414 : totK PD2M8K2 D2M8K2.u12414 = [0, 324526706947, 902434734531, 547737530025, 52484106522, 0, 0, 0] := by
  rw [show D2M8K2.u12414 = KTree.node D2M8K2.t12418 (nat_lit 26256436) (nat_lit 3905536107) (nat_lit 0) D2M8K2.t12419 from rfl, totK_node, tot12418, tot12419]
  decide +kernel

theorem arows12416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12416 = true := by
  rw [show D2M8K2.u12416 = KTree.node D2M8K2.t12420 (nat_lit 26258132) (nat_lit 3219401551) (nat_lit 0) D2M8K2.t12421 from rfl, allE_node, rows12420, irow12416, rows12421]
  all_goals rfl

theorem atot12416 : totK PD2M8K2 D2M8K2.u12416 = [0, 85737809554, 516508967392, 870974915966, 328881612974, 15066332673, 0, 0] := by
  rw [show D2M8K2.u12416 = KTree.node D2M8K2.t12420 (nat_lit 26258132) (nat_lit 3219401551) (nat_lit 0) D2M8K2.t12421 from rfl, totK_node, tot12420, tot12421]
  decide +kernel

theorem arows12417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12417 = true := by
  rw [show D2M8K2.u12417 = KTree.node D2M8K2.t12422 (nat_lit 26263232) (nat_lit 3640172007) (nat_lit 0) D2M8K2.t12423 from rfl, allE_node, rows12422, irow12417, rows12423]
  all_goals rfl

theorem atot12417 : totK PD2M8K2 D2M8K2.u12417 = [0, 353480266432, 932315010624, 510023571673, 38808189929, 0, 0, 0] := by
  rw [show D2M8K2.u12417 = KTree.node D2M8K2.t12422 (nat_lit 26263232) (nat_lit 3640172007) (nat_lit 0) D2M8K2.t12423 from rfl, totK_node, tot12422, tot12423]
  decide +kernel

theorem arows12420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12420 = true := by
  rw [show D2M8K2.u12420 = KTree.node D2M8K2.t12424 (nat_lit 26264872) (nat_lit 2806732849) (nat_lit 0) D2M8K2.t12425 from rfl, allE_node, rows12424, irow12420, rows12425]
  all_goals rfl

theorem atot12420 : totK PD2M8K2 D2M8K2.u12420 = [0, 31911208960, 487178485111, 950150589847, 301797948871, 13170675918, 0, 0] := by
  rw [show D2M8K2.u12420 = KTree.node D2M8K2.t12424 (nat_lit 26264872) (nat_lit 2806732849) (nat_lit 0) D2M8K2.t12425 from rfl, totK_node, tot12424, tot12425]
  decide +kernel

theorem arows12421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12421 = true := by
  rw [show D2M8K2.u12421 = KTree.node D2M8K2.t12426 (nat_lit 26266220) (nat_lit 3724118943) (nat_lit 0) D2M8K2.t12427 from rfl, allE_node, rows12426, irow12421, rows12427]
  all_goals rfl

theorem atot12421 : totK PD2M8K2 D2M8K2.u12421 = [0, 372248093754, 914446905991, 478214740266, 39747349929, 0, 0, 0] := by
  rw [show D2M8K2.u12421 = KTree.node D2M8K2.t12426 (nat_lit 26266220) (nat_lit 3724118943) (nat_lit 0) D2M8K2.t12427 from rfl, totK_node, tot12426, tot12427]
  decide +kernel

theorem arows12423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12423 = true := by
  rw [show D2M8K2.u12423 = KTree.node D2M8K2.t12428 (nat_lit 26267939) (nat_lit 2037295930) (nat_lit 0) D2M8K2.t12429 from rfl, allE_node, rows12428, irow12423, rows12429]
  all_goals rfl

theorem atot12423 : totK PD2M8K2 D2M8K2.u12423 = [0, 68494424605, 615603861457, 899522491550, 202329338982, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12423 = KTree.node D2M8K2.t12428 (nat_lit 26267939) (nat_lit 2037295930) (nat_lit 0) D2M8K2.t12429 from rfl, totK_node, tot12428, tot12429]
  decide +kernel

theorem arows12424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12424 = true := by
  rw [show D2M8K2.u12424 = KTree.node D2M8K2.t12430 (nat_lit 26270041) (nat_lit 1490478914) (nat_lit 0) D2M8K2.t12431 from rfl, allE_node, rows12430, irow12424, rows12431]
  all_goals rfl

theorem atot12424 : totK PD2M8K2 D2M8K2.u12424 = [0, 276258830605, 842187300159, 602376656102, 76284630394, 1210106048, 0, 0] := by
  rw [show D2M8K2.u12424 = KTree.node D2M8K2.t12430 (nat_lit 26270041) (nat_lit 1490478914) (nat_lit 0) D2M8K2.t12431 from rfl, totK_node, tot12430, tot12431]
  decide +kernel

theorem arows12428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12428 = true := by
  rw [show D2M8K2.u12428 = KTree.node D2M8K2.t12432 (nat_lit 26272362) (nat_lit 3806201269) (nat_lit 0) D2M8K2.t12433 from rfl, allE_node, rows12432, irow12428, rows12433]
  all_goals rfl

theorem atot12428 : totK PD2M8K2 D2M8K2.u12428 = [0, 196857167206, 719386436981, 706968508006, 160456686064, 3724448267, 0, 0] := by
  rw [show D2M8K2.u12428 = KTree.node D2M8K2.t12432 (nat_lit 26272362) (nat_lit 3806201269) (nat_lit 0) D2M8K2.t12433 from rfl, totK_node, tot12432, tot12433]
  decide +kernel

theorem arows12429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12429 = true := by
  rw [show D2M8K2.u12429 = KTree.node D2M8K2.t12434 (nat_lit 26294766) (nat_lit 3976992532) (nat_lit 0) D2M8K2.t12435 from rfl, allE_node, rows12434, irow12429, rows12435]
  all_goals rfl

theorem atot12429 : totK PD2M8K2 D2M8K2.u12429 = [0, 212842211144, 763984583893, 672005084788, 101382230879, 1326647619, 0, 0] := by
  rw [show D2M8K2.u12429 = KTree.node D2M8K2.t12434 (nat_lit 26294766) (nat_lit 3976992532) (nat_lit 0) D2M8K2.t12435 from rfl, totK_node, tot12434, tot12435]
  decide +kernel

theorem arows12431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12431 = true := by
  rw [show D2M8K2.u12431 = KTree.node D2M8K2.t12436 (nat_lit 26297183) (nat_lit 2032104383) (nat_lit 0) D2M8K2.t12437 from rfl, allE_node, rows12436, irow12431, rows12437]
  all_goals rfl

theorem atot12431 : totK PD2M8K2 D2M8K2.u12431 = [0, 266401506709, 826766223784, 655569776066, 68364421721, 0, 0, 0] := by
  rw [show D2M8K2.u12431 = KTree.node D2M8K2.t12436 (nat_lit 26297183) (nat_lit 2032104383) (nat_lit 0) D2M8K2.t12437 from rfl, totK_node, tot12436, tot12437]
  decide +kernel

theorem arows12432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12432 = true := by
  rw [show D2M8K2.u12432 = KTree.node D2M8K2.t12438 (nat_lit 26298418) (nat_lit 3590768311) (nat_lit 0) D2M8K2.t12439 from rfl, allE_node, rows12438, irow12432, rows12439]
  all_goals rfl

theorem atot12432 : totK PD2M8K2 D2M8K2.u12432 = [0, 158068269428, 658315877339, 733430964782, 244160894562, 18317572719, 0, 0] := by
  rw [show D2M8K2.u12432 = KTree.node D2M8K2.t12438 (nat_lit 26298418) (nat_lit 3590768311) (nat_lit 0) D2M8K2.t12439 from rfl, totK_node, tot12438, tot12439]
  decide +kernel

theorem arows12435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12435 = true := by
  rw [show D2M8K2.u12435 = KTree.node D2M8K2.t12440 (nat_lit 26299950) (nat_lit 4007938163) (nat_lit 0) D2M8K2.t12441 from rfl, allE_node, rows12440, irow12435, rows12441]
  all_goals rfl

theorem atot12435 : totK PD2M8K2 D2M8K2.u12435 = [0, 171550951199, 663285363809, 766559646419, 209789978155, 5393550755, 0, 0] := by
  rw [show D2M8K2.u12435 = KTree.node D2M8K2.t12440 (nat_lit 26299950) (nat_lit 4007938163) (nat_lit 0) D2M8K2.t12441 from rfl, totK_node, tot12440, tot12441]
  decide +kernel

theorem arows12436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12436 = true := by
  rw [show D2M8K2.u12436 = KTree.node D2M8K2.t12442 (nat_lit 26301566) (nat_lit 2974609724) (nat_lit 0) D2M8K2.t12443 from rfl, allE_node, rows12442, irow12436, rows12443]
  all_goals rfl

theorem atot12436 : totK PD2M8K2 D2M8K2.u12436 = [0, 247653881575, 799268814909, 643695476820, 94218110238, 1128973710, 0, 0] := by
  rw [show D2M8K2.u12436 = KTree.node D2M8K2.t12442 (nat_lit 26301566) (nat_lit 2974609724) (nat_lit 0) D2M8K2.t12443 from rfl, totK_node, tot12442, tot12443]
  decide +kernel

theorem arows12438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12438 = true := by
  rw [show D2M8K2.u12438 = KTree.node D2M8K2.t12444 (nat_lit 26303336) (nat_lit 2416944347) (nat_lit 0) D2M8K2.t12445 from rfl, allE_node, rows12444, irow12438, rows12445]
  all_goals rfl

theorem atot12438 : totK PD2M8K2 D2M8K2.u12438 = [0, 171610040655, 650572553530, 736869509162, 204431036638, 11780292382, 0, 0] := by
  rw [show D2M8K2.u12438 = KTree.node D2M8K2.t12444 (nat_lit 26303336) (nat_lit 2416944347) (nat_lit 0) D2M8K2.t12445 from rfl, totK_node, tot12444, tot12445]
  decide +kernel

theorem arows12439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12439 = true := by
  rw [show D2M8K2.u12439 = KTree.node D2M8K2.t12446 (nat_lit 26304946) (nat_lit 3271032775) (nat_lit 0) D2M8K2.t12447 from rfl, allE_node, rows12446, irow12439, rows12447]
  all_goals rfl

theorem atot12439 : totK PD2M8K2 D2M8K2.u12439 = [0, 247792200639, 800594369529, 648422687852, 94234053623, 1162740214, 0, 0] := by
  rw [show D2M8K2.u12439 = KTree.node D2M8K2.t12446 (nat_lit 26304946) (nat_lit 3271032775) (nat_lit 0) D2M8K2.t12447 from rfl, totK_node, tot12446, tot12447]
  decide +kernel

theorem arows12444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12444 = true := by
  rw [show D2M8K2.u12444 = KTree.node D2M8K2.t12448 (nat_lit 26306693) (nat_lit 1560703932) (nat_lit 0) D2M8K2.t12449 from rfl, allE_node, rows12448, irow12444, rows12449]
  all_goals rfl

theorem atot12444 : totK PD2M8K2 D2M8K2.u12444 = [0, 175594001528, 658847905949, 741437288585, 203078728237, 11947333746, 0, 0] := by
  rw [show D2M8K2.u12444 = KTree.node D2M8K2.t12448 (nat_lit 26306693) (nat_lit 1560703932) (nat_lit 0) D2M8K2.t12449 from rfl, totK_node, tot12448, tot12449]
  decide +kernel

theorem arows12445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12445 = true := by
  rw [show D2M8K2.u12445 = KTree.node D2M8K2.t12450 (nat_lit 26308069) (nat_lit 1291002695) (nat_lit 0) D2M8K2.t12451 from rfl, allE_node, rows12450, irow12445, rows12451]
  all_goals rfl

theorem atot12445 : totK PD2M8K2 D2M8K2.u12445 = [0, 268522251993, 857990577655, 617992474804, 69075799110, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12445 = KTree.node D2M8K2.t12450 (nat_lit 26308069) (nat_lit 1291002695) (nat_lit 0) D2M8K2.t12451 from rfl, totK_node, tot12450, tot12451]
  decide +kernel

theorem arows12447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12447 = true := by
  rw [show D2M8K2.u12447 = KTree.node D2M8K2.t12452 (nat_lit 26310002) (nat_lit 4010717053) (nat_lit 0) D2M8K2.t12453 from rfl, allE_node, rows12452, irow12447, rows12453]
  all_goals rfl

theorem atot12447 : totK PD2M8K2 D2M8K2.u12447 = [0, 0, 514897286992, 1024674587037, 265335380177, 5253830308, 0, 0] := by
  rw [show D2M8K2.u12447 = KTree.node D2M8K2.t12452 (nat_lit 26310002) (nat_lit 4010717053) (nat_lit 0) D2M8K2.t12453 from rfl, totK_node, tot12452, tot12453]
  decide +kernel

theorem arows12448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12448 = true := by
  rw [show D2M8K2.u12448 = KTree.node D2M8K2.t12454 (nat_lit 26315288) (nat_lit 3643045608) (nat_lit 0) D2M8K2.t12455 from rfl, allE_node, rows12454, irow12448, rows12455]
  all_goals rfl

theorem atot12448 : totK PD2M8K2 D2M8K2.u12448 = [0, 0, 247006810639, 823153310433, 543872119447, 76369688689, 1138244013, 0] := by
  rw [show D2M8K2.u12448 = KTree.node D2M8K2.t12454 (nat_lit 26315288) (nat_lit 3643045608) (nat_lit 0) D2M8K2.t12455 from rfl, totK_node, tot12454, tot12455]
  decide +kernel

theorem arows12451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12451 = true := by
  rw [show D2M8K2.u12451 = KTree.node D2M8K2.t12456 (nat_lit 26317904) (nat_lit 3722137538) (nat_lit 0) D2M8K2.t12457 from rfl, allE_node, rows12456, irow12451, rows12457]
  all_goals rfl

theorem atot12451 : totK PD2M8K2 D2M8K2.u12451 = [0, 0, 262685663352, 881365013424, 564531479316, 51255825202, 0, 0] := by
  rw [show D2M8K2.u12451 = KTree.node D2M8K2.t12456 (nat_lit 26317904) (nat_lit 3722137538) (nat_lit 0) D2M8K2.t12457 from rfl, totK_node, tot12456, tot12457]
  decide +kernel

theorem arows12452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12452 = true := by
  rw [show D2M8K2.u12452 = KTree.node D2M8K2.t12458 (nat_lit 26321048) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t12459 from rfl, allE_node, rows12458, irow12452, rows12459]
  all_goals rfl

theorem atot12452 : totK PD2M8K2 D2M8K2.u12452 = [0, 0, 415887136984, 963264100648, 383305168733, 18743348488, 0, 0] := by
  rw [show D2M8K2.u12452 = KTree.node D2M8K2.t12458 (nat_lit 26321048) (nat_lit 3491782222) (nat_lit 0) D2M8K2.t12459 from rfl, totK_node, tot12458, tot12459]
  decide +kernel

theorem arows12454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12454 = true := by
  rw [show D2M8K2.u12454 = KTree.node D2M8K2.t12460 (nat_lit 26324483) (nat_lit 2406111553) (nat_lit 0) D2M8K2.t12461 from rfl, allE_node, rows12460, irow12454, rows12461]
  all_goals rfl

theorem atot12454 : totK PD2M8K2 D2M8K2.u12454 = [0, 0, 413446141505, 950512691893, 382425945895, 23145504074, 0, 0] := by
  rw [show D2M8K2.u12454 = KTree.node D2M8K2.t12460 (nat_lit 26324483) (nat_lit 2406111553) (nat_lit 0) D2M8K2.t12461 from rfl, totK_node, tot12460, tot12461]
  decide +kernel

theorem arows12455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12455 = true := by
  rw [show D2M8K2.u12455 = KTree.node D2M8K2.t12462 (nat_lit 26327912) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t12463 from rfl, allE_node, rows12462, irow12455, rows12463]
  all_goals rfl

theorem atot12455 : totK PD2M8K2 D2M8K2.u12455 = [0, 0, 411468290358, 944833143446, 399705204775, 27028037255, 0, 0] := by
  rw [show D2M8K2.u12455 = KTree.node D2M8K2.t12462 (nat_lit 26327912) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t12463 from rfl, totK_node, tot12462, tot12463]
  decide +kernel

theorem arows12459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12459 = true := by
  rw [show D2M8K2.u12459 = KTree.node D2M8K2.t12464 (nat_lit 26329116) (nat_lit 3067151261) (nat_lit 0) D2M8K2.t12465 from rfl, allE_node, rows12464, irow12459, rows12465]
  all_goals rfl

theorem atot12459 : totK PD2M8K2 D2M8K2.u12459 = [0, 0, 178707584483, 775900446828, 683357002694, 101387717326, 1095107716, 0] := by
  rw [show D2M8K2.u12459 = KTree.node D2M8K2.t12464 (nat_lit 26329116) (nat_lit 3067151261) (nat_lit 0) D2M8K2.t12465 from rfl, totK_node, tot12464, tot12465]
  decide +kernel

theorem arows12460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12460 = true := by
  rw [show D2M8K2.u12460 = KTree.node D2M8K2.t12466 (nat_lit 26873994) (nat_lit 3769800760) (nat_lit 0) D2M8K2.t12467 from rfl, allE_node, rows12466, irow12460, rows12467]
  all_goals rfl

theorem atot12460 : totK PD2M8K2 D2M8K2.u12460 = [0, 267847118239, 620919934150, 440769179541, 356789692938, 106002319956, 3882006667, 0] := by
  rw [show D2M8K2.u12460 = KTree.node D2M8K2.t12466 (nat_lit 26873994) (nat_lit 3769800760) (nat_lit 0) D2M8K2.t12467 from rfl, totK_node, tot12466, tot12467]
  decide +kernel

theorem arows12462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12462 = true := by
  rw [show D2M8K2.u12462 = KTree.node D2M8K2.t12468 (nat_lit 26875510) (nat_lit 3527943847) (nat_lit 0) D2M8K2.t12469 from rfl, allE_node, rows12468, irow12462, rows12469]
  all_goals rfl

theorem atot12462 : totK PD2M8K2 D2M8K2.u12462 = [0, 174553809823, 749858175081, 756099392604, 127274759381, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12462 = KTree.node D2M8K2.t12468 (nat_lit 26875510) (nat_lit 3527943847) (nat_lit 0) D2M8K2.t12469 from rfl, totK_node, tot12468, tot12469]
  decide +kernel

theorem arows12463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12463 = true := by
  rw [show D2M8K2.u12463 = KTree.node D2M8K2.t12470 (nat_lit 26881036) (nat_lit 3817458740) (nat_lit 0) D2M8K2.t12471 from rfl, allE_node, rows12470, irow12463, rows12471]
  all_goals rfl

theorem atot12463 : totK PD2M8K2 D2M8K2.u12463 = [0, 271630327075, 849284426184, 629272147330, 64927167357, 0, 0, 0] := by
  rw [show D2M8K2.u12463 = KTree.node D2M8K2.t12470 (nat_lit 26881036) (nat_lit 3817458740) (nat_lit 0) D2M8K2.t12471 from rfl, totK_node, tot12470, tot12471]
  decide +kernel

theorem arows12466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12466 = true := by
  rw [show D2M8K2.u12466 = KTree.node D2M8K2.t12472 (nat_lit 26882564) (nat_lit 3273336226) (nat_lit 0) D2M8K2.t12473 from rfl, allE_node, rows12472, irow12466, rows12473]
  all_goals rfl

theorem atot12466 : totK PD2M8K2 D2M8K2.u12466 = [0, 144979296010, 646762542452, 769201384010, 198335777788, 9587713104, 0, 0] := by
  rw [show D2M8K2.u12466 = KTree.node D2M8K2.t12472 (nat_lit 26882564) (nat_lit 3273336226) (nat_lit 0) D2M8K2.t12473 from rfl, totK_node, tot12472, tot12473]
  decide +kernel

theorem arows12467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12467 = true := by
  rw [show D2M8K2.u12467 = KTree.node D2M8K2.t12474 (nat_lit 26884376) (nat_lit 3491864618) (nat_lit 0) D2M8K2.t12475 from rfl, allE_node, rows12474, irow12467, rows12475]
  all_goals rfl

theorem atot12467 : totK PD2M8K2 D2M8K2.u12467 = [0, 246653216020, 769595442485, 642916265774, 120666827911, 3462014130, 0, 0] := by
  rw [show D2M8K2.u12467 = KTree.node D2M8K2.t12474 (nat_lit 26884376) (nat_lit 3491864618) (nat_lit 0) D2M8K2.t12475 from rfl, totK_node, tot12474, tot12475]
  decide +kernel

theorem arows12469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12469 = true := by
  rw [show D2M8K2.u12469 = KTree.node D2M8K2.t12476 (nat_lit 26885938) (nat_lit 4169091573) (nat_lit 0) D2M8K2.t12477 from rfl, allE_node, rows12476, irow12469, rows12477]
  all_goals rfl

theorem atot12469 : totK PD2M8K2 D2M8K2.u12469 = [0, 170162356382, 706007949134, 747221382736, 150398718067, 2348440009, 0, 0] := by
  rw [show D2M8K2.u12469 = KTree.node D2M8K2.t12476 (nat_lit 26885938) (nat_lit 4169091573) (nat_lit 0) D2M8K2.t12477 from rfl, totK_node, tot12476, tot12477]
  decide +kernel

theorem arows12470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12470 = true := by
  rw [show D2M8K2.u12470 = KTree.node D2M8K2.t12478 (nat_lit 26887763) (nat_lit 2690131565) (nat_lit 0) D2M8K2.t12479 from rfl, allE_node, rows12478, irow12470, rows12479]
  all_goals rfl

theorem atot12470 : totK PD2M8K2 D2M8K2.u12470 = [0, 241797897048, 708746454846, 637110923938, 179521970521, 10902245252, 0, 0] := by
  rw [show D2M8K2.u12470 = KTree.node D2M8K2.t12478 (nat_lit 26887763) (nat_lit 2690131565) (nat_lit 0) D2M8K2.t12479 from rfl, totK_node, tot12478, tot12479]
  decide +kernel

theorem arows12476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12476 = true := by
  rw [show D2M8K2.u12476 = KTree.node D2M8K2.t12480 (nat_lit 26888994) (nat_lit 2357662742) (nat_lit 0) D2M8K2.t12481 from rfl, allE_node, rows12480, irow12476, rows12481]
  all_goals rfl

theorem atot12476 : totK PD2M8K2 D2M8K2.u12476 = [0, 177227747895, 764675052442, 738109204459, 108653121509, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12476 = KTree.node D2M8K2.t12480 (nat_lit 26888994) (nat_lit 2357662742) (nat_lit 0) D2M8K2.t12481 from rfl, totK_node, tot12480, tot12481]
  decide +kernel

theorem arows12477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12477 = true := by
  rw [show D2M8K2.u12477 = KTree.node D2M8K2.t12482 (nat_lit 26891278) (nat_lit 4017857514) (nat_lit 0) D2M8K2.t12483 from rfl, allE_node, rows12482, irow12477, rows12483]
  all_goals rfl

theorem atot12477 : totK PD2M8K2 D2M8K2.u12477 = [0, 239220745891, 758104650692, 657248808630, 127584624117, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12477 = KTree.node D2M8K2.t12482 (nat_lit 26891278) (nat_lit 4017857514) (nat_lit 0) D2M8K2.t12483 from rfl, totK_node, tot12482, tot12483]
  decide +kernel

theorem arows12479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12479 = true := by
  rw [show D2M8K2.u12479 = KTree.node D2M8K2.t12484 (nat_lit 26892870) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t12485 from rfl, allE_node, rows12484, irow12479, rows12485]
  all_goals rfl

theorem atot12479 : totK PD2M8K2 D2M8K2.u12479 = [0, 162867068856, 669716783975, 756695248916, 178573007437, 4967996017, 0, 0] := by
  rw [show D2M8K2.u12479 = KTree.node D2M8K2.t12484 (nat_lit 26892870) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t12485 from rfl, totK_node, tot12484, tot12485]
  decide +kernel

theorem arows12480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12480 = true := by
  rw [show D2M8K2.u12480 = KTree.node D2M8K2.t12486 (nat_lit 26894596) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t12487 from rfl, allE_node, rows12486, irow12480, rows12487]
  all_goals rfl

theorem atot12480 : totK PD2M8K2 D2M8K2.u12480 = [0, 0, 386951056393, 938173211673, 408801315011, 26691696689, 0, 0] := by
  rw [show D2M8K2.u12480 = KTree.node D2M8K2.t12486 (nat_lit 26894596) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t12487 from rfl, totK_node, tot12486, tot12487]
  decide +kernel

theorem arows12483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12483 = true := by
  rw [show D2M8K2.u12483 = KTree.node D2M8K2.t12488 (nat_lit 26896096) (nat_lit 3736252827) (nat_lit 0) D2M8K2.t12489 from rfl, allE_node, rows12488, irow12483, rows12489]
  all_goals rfl

theorem atot12483 : totK PD2M8K2 D2M8K2.u12483 = [0, 0, 228687689064, 784497313630, 623313688413, 108928216624, 1369150432, 0] := by
  rw [show D2M8K2.u12483 = KTree.node D2M8K2.t12488 (nat_lit 26896096) (nat_lit 3736252827) (nat_lit 0) D2M8K2.t12489 from rfl, totK_node, tot12488, tot12489]
  decide +kernel

theorem arows12484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12484 = true := by
  rw [show D2M8K2.u12484 = KTree.node D2M8K2.t12490 (nat_lit 26901635) (nat_lit 2962100531) (nat_lit 0) D2M8K2.t12491 from rfl, allE_node, rows12490, irow12484, rows12491]
  all_goals rfl

theorem atot12484 : totK PD2M8K2 D2M8K2.u12484 = [0, 0, 245819482468, 860808056762, 595605192388, 57422847667, 0, 0] := by
  rw [show D2M8K2.u12484 = KTree.node D2M8K2.t12490 (nat_lit 26901635) (nat_lit 2962100531) (nat_lit 0) D2M8K2.t12491 from rfl, totK_node, tot12490, tot12491]
  decide +kernel

theorem arows12486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12486 = true := by
  rw [show D2M8K2.u12486 = KTree.node D2M8K2.t12492 (nat_lit 26903224) (nat_lit 3344171751) (nat_lit 0) D2M8K2.t12493 from rfl, allE_node, rows12492, irow12486, rows12493]
  all_goals rfl

theorem atot12486 : totK PD2M8K2 D2M8K2.u12486 = [0, 0, 386464810769, 939536104323, 411881764035, 20555118161, 0, 0] := by
  rw [show D2M8K2.u12486 = KTree.node D2M8K2.t12492 (nat_lit 26903224) (nat_lit 3344171751) (nat_lit 0) D2M8K2.t12493 from rfl, totK_node, tot12492, tot12493]
  decide +kernel

theorem arows12487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12487 = true := by
  rw [show D2M8K2.u12487 = KTree.node D2M8K2.t12494 (nat_lit 26906522) (nat_lit 3987152990) (nat_lit 0) D2M8K2.t12495 from rfl, allE_node, rows12494, irow12487, rows12495]
  all_goals rfl

theorem atot12487 : totK PD2M8K2 D2M8K2.u12487 = [0, 0, 354194231500, 950132692527, 435038080878, 22498016149, 0, 0] := by
  rw [show D2M8K2.u12487 = KTree.node D2M8K2.t12494 (nat_lit 26906522) (nat_lit 3987152990) (nat_lit 0) D2M8K2.t12495 from rfl, totK_node, tot12494, tot12495]
  decide +kernel

theorem arows12491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12491 = true := by
  rw [show D2M8K2.u12491 = KTree.node D2M8K2.t12496 (nat_lit 26909547) (nat_lit 1618030211) (nat_lit 0) D2M8K2.t12497 from rfl, allE_node, rows12496, irow12491, rows12497]
  all_goals rfl

theorem atot12491 : totK PD2M8K2 D2M8K2.u12491 = [0, 0, 380202978547, 940074744878, 428363784529, 23530719713, 0, 0] := by
  rw [show D2M8K2.u12491 = KTree.node D2M8K2.t12496 (nat_lit 26909547) (nat_lit 1618030211) (nat_lit 0) D2M8K2.t12497 from rfl, totK_node, tot12496, tot12497]
  decide +kernel

theorem arows12492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12492 = true := by
  rw [show D2M8K2.u12492 = KTree.node D2M8K2.t12498 (nat_lit 26912954) (nat_lit 3948304266) (nat_lit 0) D2M8K2.t12499 from rfl, allE_node, rows12498, irow12492, rows12499]
  all_goals rfl

theorem atot12492 : totK PD2M8K2 D2M8K2.u12492 = [0, 90905995700, 462353420621, 826241168824, 362714283996, 21338389516, 0, 0] := by
  rw [show D2M8K2.u12492 = KTree.node D2M8K2.t12498 (nat_lit 26912954) (nat_lit 3948304266) (nat_lit 0) D2M8K2.t12499 from rfl, totK_node, tot12498, tot12499]
  decide +kernel

theorem arows12494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12494 = true := by
  rw [show D2M8K2.u12494 = KTree.node D2M8K2.t12500 (nat_lit 26957964) (nat_lit 3569228782) (nat_lit 0) D2M8K2.t12501 from rfl, allE_node, rows12500, irow12494, rows12501]
  all_goals rfl

theorem atot12494 : totK PD2M8K2 D2M8K2.u12494 = [0, 328113308497, 910611800074, 508411392906, 36064414159, 0, 0, 0] := by
  rw [show D2M8K2.u12494 = KTree.node D2M8K2.t12500 (nat_lit 26957964) (nat_lit 3569228782) (nat_lit 0) D2M8K2.t12501 from rfl, totK_node, tot12500, tot12501]
  decide +kernel

theorem arows12495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12495 = true := by
  rw [show D2M8K2.u12495 = KTree.node D2M8K2.t12502 (nat_lit 26959755) (nat_lit 2578388487) (nat_lit 0) D2M8K2.t12503 from rfl, allE_node, rows12502, irow12495, rows12503]
  all_goals rfl

theorem atot12495 : totK PD2M8K2 D2M8K2.u12495 = [0, 142288836322, 695824494961, 837853959455, 147370680466, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12495 = KTree.node D2M8K2.t12502 (nat_lit 26959755) (nat_lit 2578388487) (nat_lit 0) D2M8K2.t12503 from rfl, totK_node, tot12502, tot12503]
  decide +kernel

theorem arows12498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12498 = true := by
  rw [show D2M8K2.u12498 = KTree.node D2M8K2.t12504 (nat_lit 26961847) (nat_lit 1049829528) (nat_lit 128) D2M8K2.t12505 from rfl, allE_node, rows12504, irow12498, rows12505]
  all_goals rfl

theorem atot12498 : totK PD2M8K2 D2M8K2.u12498 = [0, 188655335925, 717217171726, 700278592737, 207284024440, 11701455490, 0, 0] := by
  rw [show D2M8K2.u12498 = KTree.node D2M8K2.t12504 (nat_lit 26961847) (nat_lit 1049829528) (nat_lit 128) D2M8K2.t12505 from rfl, totK_node, tot12504, tot12505]
  decide +kernel

theorem arows12499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12499 = true := by
  rw [show D2M8K2.u12499 = KTree.node D2M8K2.t12506 (nat_lit 26963805) (nat_lit 1528811126) (nat_lit 0) D2M8K2.t12507 from rfl, allE_node, rows12506, irow12499, rows12507]
  all_goals rfl

theorem atot12499 : totK PD2M8K2 D2M8K2.u12499 = [0, 245666187991, 689566230367, 671128461084, 206865427536, 3707914794, 0, 0] := by
  rw [show D2M8K2.u12499 = KTree.node D2M8K2.t12506 (nat_lit 26963805) (nat_lit 1528811126) (nat_lit 0) D2M8K2.t12507 from rfl, totK_node, tot12506, tot12507]
  decide +kernel

theorem arows12501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12501 = true := by
  rw [show D2M8K2.u12501 = KTree.node D2M8K2.t12508 (nat_lit 26965284) (nat_lit 3268934062) (nat_lit 0) D2M8K2.t12509 from rfl, allE_node, rows12508, irow12501, rows12509]
  all_goals rfl

theorem atot12501 : totK PD2M8K2 D2M8K2.u12501 = [0, 191837688753, 779650973512, 714846176284, 109508562672, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12501 = KTree.node D2M8K2.t12508 (nat_lit 26965284) (nat_lit 3268934062) (nat_lit 0) D2M8K2.t12509 from rfl, totK_node, tot12508, tot12509]
  decide +kernel

theorem arows12502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12502 = true := by
  rw [show D2M8K2.u12502 = KTree.node D2M8K2.t12510 (nat_lit 26966941) (nat_lit 1153172798) (nat_lit 0) D2M8K2.t12511 from rfl, allE_node, rows12510, irow12502, rows12511]
  all_goals rfl

theorem atot12502 : totK PD2M8K2 D2M8K2.u12502 = [0, 164975251400, 641825513877, 743369074288, 220735194707, 11885407614, 0, 0] := by
  rw [show D2M8K2.u12502 = KTree.node D2M8K2.t12510 (nat_lit 26966941) (nat_lit 1153172798) (nat_lit 0) D2M8K2.t12511 from rfl, totK_node, tot12510, tot12511]
  decide +kernel

theorem arows12507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12507 = true := by
  rw [show D2M8K2.u12507 = KTree.node D2M8K2.t12512 (nat_lit 26971814) (nat_lit 4136063774) (nat_lit 0) D2M8K2.t12513 from rfl, allE_node, rows12512, irow12507, rows12513]
  all_goals rfl

theorem atot12507 : totK PD2M8K2 D2M8K2.u12507 = [0, 247189380422, 792367012512, 653807279447, 98367699326, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12507 = KTree.node D2M8K2.t12512 (nat_lit 26971814) (nat_lit 4136063774) (nat_lit 0) D2M8K2.t12513 from rfl, totK_node, tot12512, tot12513]
  decide +kernel

theorem arows12508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12508 = true := by
  rw [show D2M8K2.u12508 = KTree.node D2M8K2.t12514 (nat_lit 26974096) (nat_lit 3375009103) (nat_lit 0) D2M8K2.t12515 from rfl, allE_node, rows12514, irow12508, rows12515]
  all_goals rfl

theorem atot12508 : totK PD2M8K2 D2M8K2.u12508 = [0, 221059119319, 738475514725, 703832038298, 144552595925, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12508 = KTree.node D2M8K2.t12514 (nat_lit 26974096) (nat_lit 3375009103) (nat_lit 0) D2M8K2.t12515 from rfl, totK_node, tot12514, tot12515]
  decide +kernel

theorem arows12510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12510 = true := by
  rw [show D2M8K2.u12510 = KTree.node D2M8K2.t12516 (nat_lit 26975736) (nat_lit 3370835391) (nat_lit 0) D2M8K2.t12517 from rfl, allE_node, rows12516, irow12510, rows12517]
  all_goals rfl

theorem atot12510 : totK PD2M8K2 D2M8K2.u12510 = [0, 162053559089, 734392580457, 757331755402, 137559477409, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12510 = KTree.node D2M8K2.t12516 (nat_lit 26975736) (nat_lit 3370835391) (nat_lit 0) D2M8K2.t12517 from rfl, totK_node, tot12516, tot12517]
  decide +kernel

theorem arows12511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12511 = true := by
  rw [show D2M8K2.u12511 = KTree.node D2M8K2.t12518 (nat_lit 26977630) (nat_lit 3687608658) (nat_lit 0) D2M8K2.t12519 from rfl, allE_node, rows12518, irow12511, rows12519]
  all_goals rfl

theorem atot12511 : totK PD2M8K2 D2M8K2.u12511 = [0, 0, 390796969635, 960033402519, 400374976281, 22521706927, 0, 0] := by
  rw [show D2M8K2.u12511 = KTree.node D2M8K2.t12518 (nat_lit 26977630) (nat_lit 3687608658) (nat_lit 0) D2M8K2.t12519 from rfl, totK_node, tot12518, tot12519]
  decide +kernel

theorem arows12514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12514 = true := by
  rw [show D2M8K2.u12514 = KTree.node D2M8K2.t12520 (nat_lit 26979201) (nat_lit 897800355) (nat_lit 0) D2M8K2.t12521 from rfl, allE_node, rows12520, irow12514, rows12521]
  all_goals rfl

theorem atot12514 : totK PD2M8K2 D2M8K2.u12514 = [0, 0, 168403117094, 761183571384, 683938628515, 92534763348, 1206465782, 0] := by
  rw [show D2M8K2.u12514 = KTree.node D2M8K2.t12520 (nat_lit 26979201) (nat_lit 897800355) (nat_lit 0) D2M8K2.t12521 from rfl, totK_node, tot12520, tot12521]
  decide +kernel

theorem arows12515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12515 = true := by
  rw [show D2M8K2.u12515 = KTree.node D2M8K2.t12522 (nat_lit 26981636) (nat_lit 3359499841) (nat_lit 0) D2M8K2.t12523 from rfl, allE_node, rows12522, irow12515, rows12523]
  all_goals rfl

theorem atot12515 : totK PD2M8K2 D2M8K2.u12515 = [0, 0, 329844453000, 919190837027, 518117776060, 39237374476, 0, 0] := by
  rw [show D2M8K2.u12515 = KTree.node D2M8K2.t12522 (nat_lit 26981636) (nat_lit 3359499841) (nat_lit 0) D2M8K2.t12523 from rfl, totK_node, tot12522, tot12523]
  decide +kernel

theorem arows12517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12517 = true := by
  rw [show D2M8K2.u12517 = KTree.node D2M8K2.t12524 (nat_lit 26985007) (nat_lit 1203090462) (nat_lit 0) D2M8K2.t12525 from rfl, allE_node, rows12524, irow12517, rows12525]
  all_goals rfl

theorem atot12517 : totK PD2M8K2 D2M8K2.u12517 = [0, 0, 366812020627, 952170235518, 454052978313, 25937187964, 0, 0] := by
  rw [show D2M8K2.u12517 = KTree.node D2M8K2.t12524 (nat_lit 26985007) (nat_lit 1203090462) (nat_lit 0) D2M8K2.t12525 from rfl, totK_node, tot12524, tot12525]
  decide +kernel

theorem arows12518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12518 = true := by
  rw [show D2M8K2.u12518 = KTree.node D2M8K2.t12526 (nat_lit 26986564) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t12527 from rfl, allE_node, rows12526, irow12518, rows12527]
  all_goals rfl

theorem atot12518 : totK PD2M8K2 D2M8K2.u12518 = [0, 0, 68542036366, 555694115055, 821062010247, 251521352195, 13016197374, 0] := by
  rw [show D2M8K2.u12518 = KTree.node D2M8K2.t12526 (nat_lit 26986564) (nat_lit 3798767105) (nat_lit 0) D2M8K2.t12527 from rfl, totK_node, tot12526, tot12527]
  decide +kernel

theorem arows12522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12522 = true := by
  rw [show D2M8K2.u12522 = KTree.node D2M8K2.t12528 (nat_lit 26991891) (nat_lit 3686400846) (nat_lit 0) D2M8K2.t12529 from rfl, allE_node, rows12528, irow12522, rows12529]
  all_goals rfl

theorem atot12522 : totK PD2M8K2 D2M8K2.u12522 = [0, 0, 355453481233, 927613863276, 475224432801, 32488145247, 0, 0] := by
  rw [show D2M8K2.u12522 = KTree.node D2M8K2.t12528 (nat_lit 26991891) (nat_lit 3686400846) (nat_lit 0) D2M8K2.t12529 from rfl, totK_node, tot12528, tot12529]
  decide +kernel

theorem arows12523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12523 = true := by
  rw [show D2M8K2.u12523 = KTree.node D2M8K2.t12530 (nat_lit 26993676) (nat_lit 3337429149) (nat_lit 0) D2M8K2.t12531 from rfl, allE_node, rows12530, irow12523, rows12531]
  all_goals rfl

theorem atot12523 : totK PD2M8K2 D2M8K2.u12523 = [0, 0, 113658339243, 658673641275, 774066378316, 152576501977, 4574395652, 0] := by
  rw [show D2M8K2.u12523 = KTree.node D2M8K2.t12530 (nat_lit 26993676) (nat_lit 3337429149) (nat_lit 0) D2M8K2.t12531 from rfl, totK_node, tot12530, tot12531]
  decide +kernel

theorem arows12525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12525 = true := by
  rw [show D2M8K2.u12525 = KTree.node D2M8K2.t12532 (nat_lit 26995598) (nat_lit 3054895150) (nat_lit 0) D2M8K2.t12533 from rfl, allE_node, rows12532, irow12525, rows12533]
  all_goals rfl

theorem atot12525 : totK PD2M8K2 D2M8K2.u12525 = [0, 54494369517, 396196288176, 897378349483, 431778418456, 19884808526, 0, 0] := by
  rw [show D2M8K2.u12525 = KTree.node D2M8K2.t12532 (nat_lit 26995598) (nat_lit 3054895150) (nat_lit 0) D2M8K2.t12533 from rfl, totK_node, tot12532, tot12533]
  decide +kernel

theorem arows12526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12526 = true := by
  rw [show D2M8K2.u12526 = KTree.node D2M8K2.t12534 (nat_lit 26999290) (nat_lit 3802535427) (nat_lit 0) D2M8K2.t12535 from rfl, allE_node, rows12534, irow12526, rows12535]
  all_goals rfl

theorem atot12526 : totK PD2M8K2 D2M8K2.u12526 = [0, 364557976856, 945415254900, 450603829685, 23644192949, 0, 0, 0] := by
  rw [show D2M8K2.u12526 = KTree.node D2M8K2.t12534 (nat_lit 26999290) (nat_lit 3802535427) (nat_lit 0) D2M8K2.t12535 from rfl, totK_node, tot12534, tot12535]
  decide +kernel

theorem arows12529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12529 = true := by
  rw [show D2M8K2.u12529 = KTree.node D2M8K2.t12536 (nat_lit 27000980) (nat_lit 3523624394) (nat_lit 0) D2M8K2.t12537 from rfl, allE_node, rows12536, irow12529, rows12537]
  all_goals rfl

theorem atot12529 : totK PD2M8K2 D2M8K2.u12529 = [0, 89157145599, 667029431264, 898460858639, 159772127420, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12529 = KTree.node D2M8K2.t12536 (nat_lit 27000980) (nat_lit 3523624394) (nat_lit 0) D2M8K2.t12537 from rfl, totK_node, tot12536, tot12537]
  decide +kernel

theorem arows12530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12530 = true := by
  rw [show D2M8K2.u12530 = KTree.node D2M8K2.t12538 (nat_lit 27003174) (nat_lit 3719043872) (nat_lit 0) D2M8K2.t12539 from rfl, allE_node, rows12538, irow12530, rows12539]
  all_goals rfl

theorem atot12530 : totK PD2M8K2 D2M8K2.u12530 = [0, 241927735241, 787819035426, 639517212597, 160968608851, 9977052014, 0, 0] := by
  rw [show D2M8K2.u12530 = KTree.node D2M8K2.t12538 (nat_lit 27003174) (nat_lit 3719043872) (nat_lit 0) D2M8K2.t12539 from rfl, totK_node, tot12538, tot12539]
  decide +kernel

theorem arows12532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12532 = true := by
  rw [show D2M8K2.u12532 = KTree.node D2M8K2.t12540 (nat_lit 27005115) (nat_lit 3464517900) (nat_lit 0) D2M8K2.t12541 from rfl, allE_node, rows12540, irow12532, rows12541]
  all_goals rfl

theorem atot12532 : totK PD2M8K2 D2M8K2.u12532 = [0, 171270522578, 626394769743, 754953824123, 252466989930, 6618102278, 0, 0] := by
  rw [show D2M8K2.u12532 = KTree.node D2M8K2.t12540 (nat_lit 27005115) (nat_lit 3464517900) (nat_lit 0) D2M8K2.t12541 from rfl, totK_node, tot12540, tot12541]
  decide +kernel

theorem arows12533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12533 = true := by
  rw [show D2M8K2.u12533 = KTree.node D2M8K2.t12542 (nat_lit 27010089) (nat_lit 1528962342) (nat_lit 0) D2M8K2.t12543 from rfl, allE_node, rows12542, irow12533, rows12543]
  all_goals rfl

theorem atot12533 : totK PD2M8K2 D2M8K2.u12533 = [0, 266413396601, 804921161398, 626563431156, 102817362695, 1198073392, 0, 0] := by
  rw [show D2M8K2.u12533 = KTree.node D2M8K2.t12542 (nat_lit 27010089) (nat_lit 1528962342) (nat_lit 0) D2M8K2.t12543 from rfl, totK_node, tot12542, tot12543]
  decide +kernel

theorem arows12541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12541 = true := by
  rw [show D2M8K2.u12541 = KTree.node D2M8K2.t12544 (nat_lit 27011721) (nat_lit 1611784643) (nat_lit 0) D2M8K2.t12545 from rfl, allE_node, rows12544, irow12541, rows12545]
  all_goals rfl

theorem atot12541 : totK PD2M8K2 D2M8K2.u12541 = [0, 153876230903, 632094721854, 761100946414, 226934081194, 12052611869, 0, 0] := by
  rw [show D2M8K2.u12541 = KTree.node D2M8K2.t12544 (nat_lit 27011721) (nat_lit 1611784643) (nat_lit 0) D2M8K2.t12545 from rfl, totK_node, tot12544, tot12545]
  decide +kernel

theorem arows12542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12542 = true := by
  rw [show D2M8K2.u12542 = KTree.node D2M8K2.t12546 (nat_lit 27013132) (nat_lit 2810802282) (nat_lit 0) D2M8K2.t12547 from rfl, allE_node, rows12546, irow12542, rows12547]
  all_goals rfl

theorem atot12542 : totK PD2M8K2 D2M8K2.u12542 = [0, 258343405264, 809955415107, 626708332541, 89171516012, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12542 = KTree.node D2M8K2.t12546 (nat_lit 27013132) (nat_lit 2810802282) (nat_lit 0) D2M8K2.t12547 from rfl, totK_node, tot12546, tot12547]
  decide +kernel

theorem arows12544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12544 = true := by
  rw [show D2M8K2.u12544 = KTree.node D2M8K2.t12548 (nat_lit 27015088) (nat_lit 3369472898) (nat_lit 0) D2M8K2.t12549 from rfl, allE_node, rows12548, irow12544, rows12549]
  all_goals rfl

theorem atot12544 : totK PD2M8K2 D2M8K2.u12544 = [0, 151806946431, 701757677807, 794134406362, 167116937480, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12544 = KTree.node D2M8K2.t12548 (nat_lit 27015088) (nat_lit 3369472898) (nat_lit 0) D2M8K2.t12549 from rfl, totK_node, tot12548, tot12549]
  decide +kernel

theorem arows12545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12545 = true := by
  rw [show D2M8K2.u12545 = KTree.node D2M8K2.t12550 (nat_lit 27017067) (nat_lit 3626136584) (nat_lit 0) D2M8K2.t12551 from rfl, allE_node, rows12550, irow12545, rows12551]
  all_goals rfl

theorem atot12545 : totK PD2M8K2 D2M8K2.u12545 = [0, 231402759198, 762934610712, 674175250458, 120940082095, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12545 = KTree.node D2M8K2.t12550 (nat_lit 27017067) (nat_lit 3626136584) (nat_lit 0) D2M8K2.t12551 from rfl, totK_node, tot12550, tot12551]
  decide +kernel

theorem arows12548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12548 = true := by
  rw [show D2M8K2.u12548 = KTree.node D2M8K2.t12552 (nat_lit 27018949) (nat_lit 1032721676) (nat_lit 0) D2M8K2.t12553 from rfl, allE_node, rows12552, irow12548, rows12553]
  all_goals rfl

theorem atot12548 : totK PD2M8K2 D2M8K2.u12548 = [0, 0, 422149176758, 981273555290, 361246804944, 15266090693, 0, 0] := by
  rw [show D2M8K2.u12548 = KTree.node D2M8K2.t12552 (nat_lit 27018949) (nat_lit 1032721676) (nat_lit 0) D2M8K2.t12553 from rfl, totK_node, tot12552, tot12553]
  decide +kernel

theorem arows12549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12549 = true := by
  rw [show D2M8K2.u12549 = KTree.node D2M8K2.t12554 (nat_lit 27020531) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t12555 from rfl, allE_node, rows12554, irow12549, rows12555]
  all_goals rfl

theorem atot12549 : totK PD2M8K2 D2M8K2.u12549 = [0, 0, 208387816234, 783082382769, 639526086431, 87741709192, 1239866073, 0] := by
  rw [show D2M8K2.u12549 = KTree.node D2M8K2.t12554 (nat_lit 27020531) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t12555 from rfl, totK_node, tot12554, tot12555]
  decide +kernel

theorem arows12551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12551 = true := by
  rw [show D2M8K2.u12551 = KTree.node D2M8K2.t12556 (nat_lit 27022979) (nat_lit 2734245834) (nat_lit 0) D2M8K2.t12557 from rfl, allE_node, rows12556, irow12551, rows12557]
  all_goals rfl

theorem atot12551 : totK PD2M8K2 D2M8K2.u12551 = [0, 0, 264226906344, 880102149056, 612144388993, 53477790511, 0, 0] := by
  rw [show D2M8K2.u12551 = KTree.node D2M8K2.t12556 (nat_lit 27022979) (nat_lit 2734245834) (nat_lit 0) D2M8K2.t12557 from rfl, totK_node, tot12556, tot12557]
  decide +kernel

theorem arows12552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12552 = true := by
  rw [show D2M8K2.u12552 = KTree.node D2M8K2.t12558 (nat_lit 27029784) (nat_lit 2831027896) (nat_lit 0) D2M8K2.t12559 from rfl, allE_node, rows12558, irow12552, rows12559]
  all_goals rfl

theorem atot12552 : totK PD2M8K2 D2M8K2.u12552 = [0, 0, 405528301974, 959638779159, 431989470455, 23887885705, 0, 0] := by
  rw [show D2M8K2.u12552 = KTree.node D2M8K2.t12558 (nat_lit 27029784) (nat_lit 2831027896) (nat_lit 0) D2M8K2.t12559 from rfl, totK_node, tot12558, tot12559]
  decide +kernel

theorem arows12556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12556 = true := by
  rw [show D2M8K2.u12556 = KTree.node D2M8K2.t12560 (nat_lit 27031264) (nat_lit 1501050877) (nat_lit 0) D2M8K2.t12561 from rfl, allE_node, rows12560, irow12556, rows12561]
  all_goals rfl

theorem atot12556 : totK PD2M8K2 D2M8K2.u12556 = [0, 0, 89770953565, 644567508892, 794185204958, 197901833682, 9633262574, 0] := by
  rw [show D2M8K2.u12556 = KTree.node D2M8K2.t12560 (nat_lit 27031264) (nat_lit 1501050877) (nat_lit 0) D2M8K2.t12561 from rfl, totK_node, tot12560, tot12561]
  decide +kernel

theorem arows12557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12557 = true := by
  rw [show D2M8K2.u12557 = KTree.node D2M8K2.t12562 (nat_lit 27033203) (nat_lit 2450516263) (nat_lit 0) D2M8K2.t12563 from rfl, allE_node, rows12562, irow12557, rows12563]
  all_goals rfl

theorem atot12557 : totK PD2M8K2 D2M8K2.u12557 = [0, 0, 319763103064, 844751120369, 508901445324, 84788122291, 3472187823, 0] := by
  rw [show D2M8K2.u12557 = KTree.node D2M8K2.t12562 (nat_lit 27033203) (nat_lit 2450516263) (nat_lit 0) D2M8K2.t12563 from rfl, totK_node, tot12562, tot12563]
  decide +kernel

theorem arows12559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12559 = true := by
  rw [show D2M8K2.u12559 = KTree.node D2M8K2.t12564 (nat_lit 27034805) (nat_lit 1157390258) (nat_lit 0) D2M8K2.t12565 from rfl, allE_node, rows12564, irow12559, rows12565]
  all_goals rfl

theorem atot12559 : totK PD2M8K2 D2M8K2.u12559 = [0, 0, 90563211903, 691675555986, 815489695827, 130972837323, 2074792727, 0] := by
  rw [show D2M8K2.u12559 = KTree.node D2M8K2.t12564 (nat_lit 27034805) (nat_lit 1157390258) (nat_lit 0) D2M8K2.t12565 from rfl, totK_node, tot12564, tot12565]
  decide +kernel

theorem arows12560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12560 = true := by
  rw [show D2M8K2.u12560 = KTree.node D2M8K2.t12566 (nat_lit 27036984) (nat_lit 3501106790) (nat_lit 0) D2M8K2.t12567 from rfl, allE_node, rows12566, irow12560, rows12567]
  all_goals rfl

theorem atot12560 : totK PD2M8K2 D2M8K2.u12560 = [0, 0, 381700370573, 924777100333, 432479420801, 46754983351, 2645825719, 0] := by
  rw [show D2M8K2.u12560 = KTree.node D2M8K2.t12566 (nat_lit 27036984) (nat_lit 3501106790) (nat_lit 0) D2M8K2.t12567 from rfl, totK_node, tot12566, tot12567]
  decide +kernel

theorem arows12563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12563 = true := by
  rw [show D2M8K2.u12563 = KTree.node D2M8K2.t12568 (nat_lit 27040566) (nat_lit 2724407266) (nat_lit 0) D2M8K2.t12569 from rfl, allE_node, rows12568, irow12563, rows12569]
  all_goals rfl

theorem atot12563 : totK PD2M8K2 D2M8K2.u12563 = [0, 350567134047, 892520997554, 467161437660, 81262485481, 7923020108, 0, 0] := by
  rw [show D2M8K2.u12563 = KTree.node D2M8K2.t12568 (nat_lit 27040566) (nat_lit 2724407266) (nat_lit 0) D2M8K2.t12569 from rfl, totK_node, tot12568, tot12569]
  decide +kernel

theorem arows12564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12564 = true := by
  rw [show D2M8K2.u12564 = KTree.node D2M8K2.t12570 (nat_lit 27042108) (nat_lit 3224907551) (nat_lit 0) D2M8K2.t12571 from rfl, allE_node, rows12570, irow12564, rows12571]
  all_goals rfl

theorem atot12564 : totK PD2M8K2 D2M8K2.u12564 = [0, 119561506695, 665346225296, 860028195977, 152126405583, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12564 = KTree.node D2M8K2.t12570 (nat_lit 27042108) (nat_lit 3224907551) (nat_lit 0) D2M8K2.t12571 from rfl, totK_node, tot12570, tot12571]
  decide +kernel

theorem arows12566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12566 = true := by
  rw [show D2M8K2.u12566 = KTree.node D2M8K2.t12572 (nat_lit 27044161) (nat_lit 1369606179) (nat_lit 0) D2M8K2.t12573 from rfl, allE_node, rows12572, irow12566, rows12573]
  all_goals rfl

theorem atot12566 : totK PD2M8K2 D2M8K2.u12566 = [0, 293636651748, 904006964400, 574157111367, 57861097601, 0, 0, 0] := by
  rw [show D2M8K2.u12566 = KTree.node D2M8K2.t12572 (nat_lit 27044161) (nat_lit 1369606179) (nat_lit 0) D2M8K2.t12573 from rfl, totK_node, tot12572, tot12573]
  decide +kernel

theorem arows12567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12567 = true := by
  rw [show D2M8K2.u12567 = KTree.node D2M8K2.t12574 (nat_lit 27045966) (nat_lit 3933033034) (nat_lit 0) D2M8K2.t12575 from rfl, allE_node, rows12574, irow12567, rows12575]
  all_goals rfl

theorem atot12567 : totK PD2M8K2 D2M8K2.u12567 = [0, 85167078157, 468567585343, 822275329481, 389137566038, 24128189171, 0, 0] := by
  rw [show D2M8K2.u12567 = KTree.node D2M8K2.t12574 (nat_lit 27045966) (nat_lit 3933033034) (nat_lit 0) D2M8K2.t12575 from rfl, totK_node, tot12574, tot12575]
  decide +kernel

theorem arows12572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12572 = true := by
  rw [show D2M8K2.u12572 = KTree.node D2M8K2.t12576 (nat_lit 27047503) (nat_lit 945156502) (nat_lit 0) D2M8K2.t12577 from rfl, allE_node, rows12576, irow12572, rows12577]
  all_goals rfl

theorem atot12572 : totK PD2M8K2 D2M8K2.u12572 = [0, 326693651588, 891579907958, 540653511625, 48887259090, 0, 0, 0] := by
  rw [show D2M8K2.u12572 = KTree.node D2M8K2.t12576 (nat_lit 27047503) (nat_lit 945156502) (nat_lit 0) D2M8K2.t12577 from rfl, totK_node, tot12576, tot12577]
  decide +kernel

theorem arows12573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12573 = true := by
  rw [show D2M8K2.u12573 = KTree.node D2M8K2.t12578 (nat_lit 27049230) (nat_lit 2174753614) (nat_lit 0) D2M8K2.t12579 from rfl, allE_node, rows12578, irow12573, rows12579]
  all_goals rfl

theorem atot12573 : totK PD2M8K2 D2M8K2.u12573 = [0, 85190975889, 524284904997, 861070288418, 275986078555, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12573 = KTree.node D2M8K2.t12578 (nat_lit 27049230) (nat_lit 2174753614) (nat_lit 0) D2M8K2.t12579 from rfl, totK_node, tot12578, tot12579]
  decide +kernel

theorem arows12575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12575 = true := by
  rw [show D2M8K2.u12575 = KTree.node D2M8K2.t12580 (nat_lit 27051217) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t12581 from rfl, allE_node, rows12580, irow12575, rows12581]
  all_goals rfl

theorem atot12575 : totK PD2M8K2 D2M8K2.u12575 = [0, 326890713627, 911254144396, 529950940021, 42893551975, 0, 0, 0] := by
  rw [show D2M8K2.u12575 = KTree.node D2M8K2.t12580 (nat_lit 27051217) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t12581 from rfl, totK_node, tot12580, tot12581]
  decide +kernel

theorem arows12576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12576 = true := by
  rw [show D2M8K2.u12576 = KTree.node D2M8K2.t12582 (nat_lit 27052939) (nat_lit 2224574032) (nat_lit 0) D2M8K2.t12583 from rfl, allE_node, rows12582, irow12576, rows12583]
  all_goals rfl

theorem atot12576 : totK PD2M8K2 D2M8K2.u12576 = [0, 86654048599, 509985601020, 864458318627, 292105332955, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12576 = KTree.node D2M8K2.t12582 (nat_lit 27052939) (nat_lit 2224574032) (nat_lit 0) D2M8K2.t12583 from rfl, totK_node, tot12582, tot12583]
  decide +kernel

theorem arows12579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12579 = true := by
  rw [show D2M8K2.u12579 = KTree.node D2M8K2.t12584 (nat_lit 27054308) (nat_lit 2827845027) (nat_lit 0) D2M8K2.t12585 from rfl, allE_node, rows12584, irow12579, rows12585]
  all_goals rfl

theorem atot12579 : totK PD2M8K2 D2M8K2.u12579 = [0, 352446817612, 928364516711, 508709238180, 39368625390, 0, 0, 0] := by
  rw [show D2M8K2.u12579 = KTree.node D2M8K2.t12584 (nat_lit 27054308) (nat_lit 2827845027) (nat_lit 0) D2M8K2.t12585 from rfl, totK_node, tot12584, tot12585]
  decide +kernel

theorem arows12580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12580 = true := by
  rw [show D2M8K2.u12580 = KTree.node D2M8K2.t12586 (nat_lit 27055993) (nat_lit 1390418125) (nat_lit 0) D2M8K2.t12587 from rfl, allE_node, rows12586, irow12580, rows12587]
  all_goals rfl

theorem atot12580 : totK PD2M8K2 D2M8K2.u12580 = [0, 0, 578236839564, 1003901852865, 219968162423, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12580 = KTree.node D2M8K2.t12586 (nat_lit 27055993) (nat_lit 1390418125) (nat_lit 0) D2M8K2.t12587 from rfl, totK_node, tot12586, tot12587]
  decide +kernel

theorem arows12582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12582 = true := by
  rw [show D2M8K2.u12582 = KTree.node D2M8K2.t12588 (nat_lit 27061514) (nat_lit 3736327406) (nat_lit 0) D2M8K2.t12589 from rfl, allE_node, rows12588, irow12582, rows12589]
  all_goals rfl

theorem atot12582 : totK PD2M8K2 D2M8K2.u12582 = [0, 0, 329084385323, 956612484123, 450390530094, 23418410187, 0, 0] := by
  rw [show D2M8K2.u12582 = KTree.node D2M8K2.t12588 (nat_lit 27061514) (nat_lit 3736327406) (nat_lit 0) D2M8K2.t12589 from rfl, totK_node, tot12588, tot12589]
  decide +kernel

theorem arows12583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12583 = true := by
  rw [show D2M8K2.u12583 = KTree.node D2M8K2.t12590 (nat_lit 27063450) (nat_lit 3451679299) (nat_lit 0) D2M8K2.t12591 from rfl, allE_node, rows12590, irow12583, rows12591]
  all_goals rfl

theorem atot12583 : totK PD2M8K2 D2M8K2.u12583 = [0, 0, 173438096905, 761328324703, 724599044613, 102844239087, 1138244013, 0] := by
  rw [show D2M8K2.u12583 = KTree.node D2M8K2.t12590 (nat_lit 27063450) (nat_lit 3451679299) (nat_lit 0) D2M8K2.t12591 from rfl, totK_node, tot12590, tot12591]
  decide +kernel

theorem arows12587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12587 = true := by
  rw [show D2M8K2.u12587 = KTree.node D2M8K2.t12592 (nat_lit 27065328) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t12593 from rfl, allE_node, rows12592, irow12587, rows12593]
  all_goals rfl

theorem atot12587 : totK PD2M8K2 D2M8K2.u12587 = [0, 0, 362580437567, 956361523798, 448207799561, 28485904727, 0, 0] := by
  rw [show D2M8K2.u12587 = KTree.node D2M8K2.t12592 (nat_lit 27065328) (nat_lit 3290801189) (nat_lit 0) D2M8K2.t12593 from rfl, totK_node, tot12592, tot12593]
  decide +kernel

theorem arows12588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12588 = true := by
  rw [show D2M8K2.u12588 = KTree.node D2M8K2.t12594 (nat_lit 27068881) (nat_lit 1468849511) (nat_lit 0) D2M8K2.t12595 from rfl, allE_node, rows12594, irow12588, rows12595]
  all_goals rfl

theorem atot12588 : totK PD2M8K2 D2M8K2.u12588 = [0, 0, 381550561766, 949543175824, 419304976410, 21541056324, 0, 0] := by
  rw [show D2M8K2.u12588 = KTree.node D2M8K2.t12594 (nat_lit 27068881) (nat_lit 1468849511) (nat_lit 0) D2M8K2.t12595 from rfl, totK_node, tot12594, tot12595]
  decide +kernel

theorem arows12590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12590 = true := by
  rw [show D2M8K2.u12590 = KTree.node D2M8K2.t12596 (nat_lit 27072192) (nat_lit 3146319992) (nat_lit 0) D2M8K2.t12597 from rfl, allE_node, rows12596, irow12590, rows12597]
  all_goals rfl

theorem atot12590 : totK PD2M8K2 D2M8K2.u12590 = [0, 0, 368489474655, 941208641794, 450885877195, 21810364108, 0, 0] := by
  rw [show D2M8K2.u12590 = KTree.node D2M8K2.t12596 (nat_lit 27072192) (nat_lit 3146319992) (nat_lit 0) D2M8K2.t12597 from rfl, totK_node, tot12596, tot12597]
  decide +kernel

theorem arows12591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12591 = true := by
  rw [show D2M8K2.u12591 = KTree.node D2M8K2.t12598 (nat_lit 27075240) (nat_lit 3557993722) (nat_lit 0) D2M8K2.t12599 from rfl, allE_node, rows12598, irow12591, rows12599]
  all_goals rfl

theorem atot12591 : totK PD2M8K2 D2M8K2.u12591 = [0, 0, 313610753254, 901942582895, 522355150012, 44379446066, 0, 0] := by
  rw [show D2M8K2.u12591 = KTree.node D2M8K2.t12598 (nat_lit 27075240) (nat_lit 3557993722) (nat_lit 0) D2M8K2.t12599 from rfl, totK_node, tot12598, tot12599]
  decide +kernel

theorem arows12594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12594 = true := by
  rw [show D2M8K2.u12594 = KTree.node D2M8K2.t12600 (nat_lit 27077204) (nat_lit 3284668582) (nat_lit 0) D2M8K2.t12601 from rfl, allE_node, rows12600, irow12594, rows12601]
  all_goals rfl

theorem atot12594 : totK PD2M8K2 D2M8K2.u12594 = [0, 141777946573, 295910850972, 466233282010, 674271296786, 177535119139, 4977114383, 0] := by
  rw [show D2M8K2.u12594 = KTree.node D2M8K2.t12600 (nat_lit 27077204) (nat_lit 3284668582) (nat_lit 0) D2M8K2.t12601 from rfl, totK_node, tot12600, tot12601]
  decide +kernel

theorem arows12595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12595 = true := by
  rw [show D2M8K2.u12595 = KTree.node D2M8K2.t12602 (nat_lit 27082466) (nat_lit 3101103175) (nat_lit 0) D2M8K2.t12603 from rfl, allE_node, rows12602, irow12595, rows12603]
  all_goals rfl

theorem atot12595 : totK PD2M8K2 D2M8K2.u12595 = [0, 279549890402, 869229636883, 579027738340, 55368321461, 0, 0, 0] := by
  rw [show D2M8K2.u12595 = KTree.node D2M8K2.t12602 (nat_lit 27082466) (nat_lit 3101103175) (nat_lit 0) D2M8K2.t12603 from rfl, totK_node, tot12602, tot12603]
  decide +kernel

theorem arows12597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12597 = true := by
  rw [show D2M8K2.u12597 = KTree.node D2M8K2.t12604 (nat_lit 27084441) (nat_lit 1520034149) (nat_lit 0) D2M8K2.t12605 from rfl, allE_node, rows12604, irow12597, rows12605]
  all_goals rfl

theorem atot12597 : totK PD2M8K2 D2M8K2.u12597 = [0, 154567988930, 723407729190, 799682506958, 133204157845, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12597 = KTree.node D2M8K2.t12604 (nat_lit 27084441) (nat_lit 1520034149) (nat_lit 0) D2M8K2.t12605 from rfl, totK_node, tot12604, tot12605]
  decide +kernel

theorem arows12598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12598 = true := by
  rw [show D2M8K2.u12598 = KTree.node D2M8K2.t12606 (nat_lit 27089619) (nat_lit 3634743472) (nat_lit 0) D2M8K2.t12607 from rfl, allE_node, rows12606, irow12598, rows12607]
  all_goals rfl

theorem atot12598 : totK PD2M8K2 D2M8K2.u12598 = [0, 246733434984, 783156226519, 654611476536, 105809918851, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12598 = KTree.node D2M8K2.t12606 (nat_lit 27089619) (nat_lit 3634743472) (nat_lit 0) D2M8K2.t12607 from rfl, totK_node, tot12606, tot12607]
  decide +kernel

theorem arows12604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12604 = true := by
  rw [show D2M8K2.u12604 = KTree.node D2M8K2.t12608 (nat_lit 27091642) (nat_lit 3785945449) (nat_lit 0) D2M8K2.t12609 from rfl, allE_node, rows12608, irow12604, rows12609]
  all_goals rfl

theorem atot12604 : totK PD2M8K2 D2M8K2.u12604 = [0, 226967627943, 741440299798, 696998495074, 145397716406, 4234510686, 0, 0] := by
  rw [show D2M8K2.u12604 = KTree.node D2M8K2.t12608 (nat_lit 27091642) (nat_lit 3785945449) (nat_lit 0) D2M8K2.t12609 from rfl, totK_node, tot12608, tot12609]
  decide +kernel

theorem arows12605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12605 = true := by
  rw [show D2M8K2.u12605 = KTree.node D2M8K2.t12610 (nat_lit 27093198) (nat_lit 3851888000) (nat_lit 0) D2M8K2.t12611 from rfl, allE_node, rows12610, irow12605, rows12611]
  all_goals rfl

theorem atot12605 : totK PD2M8K2 D2M8K2.u12605 = [0, 174584958464, 756218662306, 735258556589, 125861543849, 1198073392, 0, 0] := by
  rw [show D2M8K2.u12605 = KTree.node D2M8K2.t12610 (nat_lit 27093198) (nat_lit 3851888000) (nat_lit 0) D2M8K2.t12611 from rfl, totK_node, tot12610, tot12611]
  decide +kernel

theorem arows12607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12607 = true := by
  rw [show D2M8K2.u12607 = KTree.node D2M8K2.t12612 (nat_lit 27098640) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t12613 from rfl, allE_node, rows12612, irow12607, rows12613]
  all_goals rfl

theorem atot12607 : totK PD2M8K2 D2M8K2.u12607 = [0, 247757144055, 772410144200, 656762018393, 134371425126, 4257574148, 0, 0] := by
  rw [show D2M8K2.u12607 = KTree.node D2M8K2.t12612 (nat_lit 27098640) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t12613 from rfl, totK_node, tot12612, tot12613]
  decide +kernel

theorem arows12608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12608 = true := by
  rw [show D2M8K2.u12608 = KTree.node D2M8K2.t12614 (nat_lit 27100150) (nat_lit 3531214641) (nat_lit 0) D2M8K2.t12615 from rfl, allE_node, rows12614, irow12608, rows12615]
  all_goals rfl

theorem atot12608 : totK PD2M8K2 D2M8K2.u12608 = [0, 180075851965, 736358487139, 752857210867, 135657295868, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12608 = KTree.node D2M8K2.t12614 (nat_lit 27100150) (nat_lit 3531214641) (nat_lit 0) D2M8K2.t12615 from rfl, totK_node, tot12614, tot12615]
  decide +kernel

theorem arows12611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12611 = true := by
  rw [show D2M8K2.u12611 = KTree.node D2M8K2.t12616 (nat_lit 27101837) (nat_lit 1518107584) (nat_lit 0) D2M8K2.t12617 from rfl, allE_node, rows12616, irow12611, rows12617]
  all_goals rfl

theorem atot12611 : totK PD2M8K2 D2M8K2.u12611 = [0, 0, 358700161133, 957706121991, 426755155514, 23301045897, 0, 0] := by
  rw [show D2M8K2.u12611 = KTree.node D2M8K2.t12616 (nat_lit 27101837) (nat_lit 1518107584) (nat_lit 0) D2M8K2.t12617 from rfl, totK_node, tot12616, tot12617]
  decide +kernel

theorem arows12612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12612 = true := by
  rw [show D2M8K2.u12612 = KTree.node D2M8K2.t12618 (nat_lit 27103438) (nat_lit 4003979360) (nat_lit 0) D2M8K2.t12619 from rfl, allE_node, rows12618, irow12612, rows12619]
  all_goals rfl

theorem atot12612 : totK PD2M8K2 D2M8K2.u12612 = [0, 0, 243728036388, 804087158431, 600412642620, 87921889764, 1310285577, 0] := by
  rw [show D2M8K2.u12612 = KTree.node D2M8K2.t12618 (nat_lit 27103438) (nat_lit 4003979360) (nat_lit 0) D2M8K2.t12619 from rfl, totK_node, tot12618, tot12619]
  decide +kernel

theorem arows12614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12614 = true := by
  rw [show D2M8K2.u12614 = KTree.node D2M8K2.t12620 (nat_lit 27109003) (nat_lit 1539301631) (nat_lit 0) D2M8K2.t12621 from rfl, allE_node, rows12620, irow12614, rows12621]
  all_goals rfl

theorem atot12614 : totK PD2M8K2 D2M8K2.u12614 = [0, 0, 244841901270, 860459998073, 623249484716, 46563353139, 0, 0] := by
  rw [show D2M8K2.u12614 = KTree.node D2M8K2.t12620 (nat_lit 27109003) (nat_lit 1539301631) (nat_lit 0) D2M8K2.t12621 from rfl, totK_node, tot12620, tot12621]
  decide +kernel

theorem arows12615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12615 = true := by
  rw [show D2M8K2.u12615 = KTree.node D2M8K2.t12622 (nat_lit 27112394) (nat_lit 3395774114) (nat_lit 0) D2M8K2.t12623 from rfl, allE_node, rows12622, irow12615, rows12623]
  all_goals rfl

theorem atot12615 : totK PD2M8K2 D2M8K2.u12615 = [0, 0, 399848257845, 958252549107, 412395930787, 20582564690, 0, 0] := by
  rw [show D2M8K2.u12615 = KTree.node D2M8K2.t12622 (nat_lit 27112394) (nat_lit 3395774114) (nat_lit 0) D2M8K2.t12623 from rfl, totK_node, tot12622, tot12623]
  decide +kernel

theorem arows12619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12619 = true := by
  rw [show D2M8K2.u12619 = KTree.node D2M8K2.t12624 (nat_lit 27114026) (nat_lit 4051237869) (nat_lit 0) D2M8K2.t12625 from rfl, allE_node, rows12624, irow12619, rows12625]
  all_goals rfl

theorem atot12619 : totK PD2M8K2 D2M8K2.u12619 = [0, 0, 350425352261, 931152676705, 483205324877, 30161368593, 0, 0] := by
  rw [show D2M8K2.u12619 = KTree.node D2M8K2.t12624 (nat_lit 27114026) (nat_lit 4051237869) (nat_lit 0) D2M8K2.t12625 from rfl, totK_node, tot12624, tot12625]
  decide +kernel

theorem arows12620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12620 = true := by
  rw [show D2M8K2.u12620 = KTree.node D2M8K2.t12626 (nat_lit 27120751) (nat_lit 2419841192) (nat_lit 0) D2M8K2.t12627 from rfl, allE_node, rows12626, irow12620, rows12627]
  all_goals rfl

theorem atot12620 : totK PD2M8K2 D2M8K2.u12620 = [0, 0, 390902499944, 966224262275, 433915160129, 23389354585, 0, 0] := by
  rw [show D2M8K2.u12620 = KTree.node D2M8K2.t12626 (nat_lit 27120751) (nat_lit 2419841192) (nat_lit 0) D2M8K2.t12627 from rfl, totK_node, tot12626, tot12627]
  decide +kernel

theorem arows12622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12622 = true := by
  rw [show D2M8K2.u12622 = KTree.node D2M8K2.t12628 (nat_lit 27123948) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t12629 from rfl, allE_node, rows12628, irow12622, rows12629]
  all_goals rfl

theorem atot12622 : totK PD2M8K2 D2M8K2.u12622 = [0, 0, 277601318702, 866536096602, 584164018732, 55392456700, 0, 0] := by
  rw [show D2M8K2.u12622 = KTree.node D2M8K2.t12628 (nat_lit 27123948) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t12629 from rfl, totK_node, tot12628, tot12629]
  decide +kernel

theorem arows12623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12623 = true := by
  rw [show D2M8K2.u12623 = KTree.node D2M8K2.t12630 (nat_lit 27125890) (nat_lit 4024406552) (nat_lit 0) D2M8K2.t12631 from rfl, allE_node, rows12630, irow12623, rows12631]
  all_goals rfl

theorem atot12623 : totK PD2M8K2 D2M8K2.u12623 = [0, 0, 180029667328, 732601080257, 758382940551, 121580378243, 1369150432, 0] := by
  rw [show D2M8K2.u12623 = KTree.node D2M8K2.t12630 (nat_lit 27125890) (nat_lit 4024406552) (nat_lit 0) D2M8K2.t12631 from rfl, totK_node, tot12630, tot12631]
  decide +kernel

theorem arows12626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12626 = true := by
  rw [show D2M8K2.u12626 = KTree.node D2M8K2.t12632 (nat_lit 27131092) (nat_lit 4038823285) (nat_lit 0) D2M8K2.t12633 from rfl, allE_node, rows12632, irow12626, rows12633]
  all_goals rfl

theorem atot12626 : totK PD2M8K2 D2M8K2.u12626 = [0, 0, 224971035113, 793749743490, 646793262193, 89397456326, 1164319620, 0] := by
  rw [show D2M8K2.u12626 = KTree.node D2M8K2.t12632 (nat_lit 27131092) (nat_lit 4038823285) (nat_lit 0) D2M8K2.t12633 from rfl, totK_node, tot12632, tot12633]
  decide +kernel

theorem arows12627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12627 = true := by
  rw [show D2M8K2.u12627 = KTree.node D2M8K2.t12634 (nat_lit 27132858) (nat_lit 3041915427) (nat_lit 8) D2M8K2.t12635 from rfl, allE_node, rows12634, irow12627, rows12635]
  all_goals rfl

theorem atot12627 : totK PD2M8K2 D2M8K2.u12627 = [0, 0, 221376211258, 675401579672, 660005767336, 173834085845, 11727338389, 0] := by
  rw [show D2M8K2.u12627 = KTree.node D2M8K2.t12634 (nat_lit 27132858) (nat_lit 3041915427) (nat_lit 8) D2M8K2.t12635 from rfl, totK_node, tot12634, tot12635]
  decide +kernel

theorem arows12629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12629 = true := by
  rw [show D2M8K2.u12629 = KTree.node D2M8K2.t12636 (nat_lit 27134629) (nat_lit 1359356173) (nat_lit 0) D2M8K2.t12637 from rfl, allE_node, rows12636, irow12629, rows12637]
  all_goals rfl

theorem atot12629 : totK PD2M8K2 D2M8K2.u12629 = [0, 0, 187540238935, 774940231890, 694999640679, 99879160409, 1198073392, 0] := by
  rw [show D2M8K2.u12629 = KTree.node D2M8K2.t12636 (nat_lit 27134629) (nat_lit 1359356173) (nat_lit 0) D2M8K2.t12637 from rfl, totK_node, tot12636, tot12637]
  decide +kernel

theorem arows12630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12630 = true := by
  rw [show D2M8K2.u12630 = KTree.node D2M8K2.t12638 (nat_lit 27136561) (nat_lit 1510266876) (nat_lit 0) D2M8K2.t12639 from rfl, allE_node, rows12638, irow12630, rows12639]
  all_goals rfl

theorem atot12630 : totK PD2M8K2 D2M8K2.u12630 = [0, 0, 223293557169, 678030851074, 640615044955, 173900878647, 11894306413, 0] := by
  rw [show D2M8K2.u12630 = KTree.node D2M8K2.t12638 (nat_lit 27136561) (nat_lit 1510266876) (nat_lit 0) D2M8K2.t12639 from rfl, totK_node, tot12638, tot12639]
  decide +kernel

theorem arows12635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12635 = true := by
  rw [show D2M8K2.u12635 = KTree.node D2M8K2.t12640 (nat_lit 27137772) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t12641 from rfl, allE_node, rows12640, irow12635, rows12641]
  all_goals rfl

theorem atot12635 : totK PD2M8K2 D2M8K2.u12635 = [0, 0, 187149259026, 761781641183, 705285482831, 95372068551, 1096505104, 0] := by
  rw [show D2M8K2.u12635 = KTree.node D2M8K2.t12640 (nat_lit 27137772) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t12641 from rfl, totK_node, tot12640, tot12641]
  decide +kernel

theorem arows12636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12636 = true := by
  rw [show D2M8K2.u12636 = KTree.node D2M8K2.t12642 (nat_lit 27140092) (nat_lit 3843440653) (nat_lit 0) D2M8K2.t12643 from rfl, allE_node, rows12642, irow12636, rows12643]
  all_goals rfl

theorem atot12636 : totK PD2M8K2 D2M8K2.u12636 = [0, 0, 275257972445, 772757250314, 606143518120, 107975309807, 3838026431, 0] := by
  rw [show D2M8K2.u12636 = KTree.node D2M8K2.t12642 (nat_lit 27140092) (nat_lit 3843440653) (nat_lit 0) D2M8K2.t12643 from rfl, totK_node, tot12642, tot12643]
  decide +kernel

theorem arows12638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12638 = true := by
  rw [show D2M8K2.u12638 = KTree.node D2M8K2.t12644 (nat_lit 27141808) (nat_lit 3090916299) (nat_lit 0) D2M8K2.t12645 from rfl, allE_node, rows12644, irow12638, rows12645]
  all_goals rfl

theorem atot12638 : totK PD2M8K2 D2M8K2.u12638 = [0, 0, 116791540598, 747401569791, 798245889758, 122544888930, 1268739303, 0] := by
  rw [show D2M8K2.u12638 = KTree.node D2M8K2.t12644 (nat_lit 27141808) (nat_lit 3090916299) (nat_lit 0) D2M8K2.t12645 from rfl, totK_node, tot12644, tot12645]
  decide +kernel

theorem arows12639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12639 = true := by
  rw [show D2M8K2.u12639 = KTree.node D2M8K2.t12646 (nat_lit 27144333) (nat_lit 1255382991) (nat_lit 0) D2M8K2.t12647 from rfl, allE_node, rows12646, irow12639, rows12647]
  all_goals rfl

theorem atot12639 : totK PD2M8K2 D2M8K2.u12639 = [0, 0, 0, 407145616453, 948208280464, 371763162783, 21817061227, 0] := by
  rw [show D2M8K2.u12639 = KTree.node D2M8K2.t12646 (nat_lit 27144333) (nat_lit 1255382991) (nat_lit 0) D2M8K2.t12647 from rfl, totK_node, tot12646, tot12647]
  decide +kernel

theorem arows12642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12642 = true := by
  rw [show D2M8K2.u12642 = KTree.node D2M8K2.t12648 (nat_lit 27146130) (nat_lit 3255505874) (nat_lit 0) D2M8K2.t12649 from rfl, allE_node, rows12648, irow12642, rows12649]
  all_goals rfl

theorem atot12642 : totK PD2M8K2 D2M8K2.u12642 = [0, 0, 0, 164374285716, 807828699046, 662307654869, 90745192982, 1369150432] := by
  rw [show D2M8K2.u12642 = KTree.node D2M8K2.t12648 (nat_lit 27146130) (nat_lit 3255505874) (nat_lit 0) D2M8K2.t12649 from rfl, totK_node, tot12648, tot12649]
  decide +kernel

theorem arows12643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12643 = true := by
  rw [show D2M8K2.u12643 = KTree.node D2M8K2.t12650 (nat_lit 27151818) (nat_lit 729177428) (nat_lit 2176) D2M8K2.t12651 from rfl, allE_node, rows12650, irow12643, rows12651]
  all_goals rfl

theorem atot12643 : totK PD2M8K2 D2M8K2.u12643 = [0, 0, 0, 496441024872, 972333483963, 286419351838, 13452247108, 0] := by
  rw [show D2M8K2.u12643 = KTree.node D2M8K2.t12650 (nat_lit 27151818) (nat_lit 729177428) (nat_lit 2176) D2M8K2.t12651 from rfl, totK_node, tot12650, tot12651]
  decide +kernel

theorem arows12645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12645 = true := by
  rw [show D2M8K2.u12645 = KTree.node D2M8K2.t12652 (nat_lit 27157342) (nat_lit 3308177036) (nat_lit 0) D2M8K2.t12653 from rfl, allE_node, rows12652, irow12645, rows12653]
  all_goals rfl

theorem atot12645 : totK PD2M8K2 D2M8K2.u12645 = [0, 0, 0, 422679368088, 935964400149, 341851768137, 21768253790, 0] := by
  rw [show D2M8K2.u12645 = KTree.node D2M8K2.t12652 (nat_lit 27157342) (nat_lit 3308177036) (nat_lit 0) D2M8K2.t12653 from rfl, totK_node, tot12652, tot12653]
  decide +kernel

theorem arows12646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12646 = true := by
  rw [show D2M8K2.u12646 = KTree.node D2M8K2.t12654 (nat_lit 27160795) (nat_lit 2216827072) (nat_lit 0) D2M8K2.t12655 from rfl, allE_node, rows12654, irow12646, rows12655]
  all_goals rfl

theorem atot12646 : totK PD2M8K2 D2M8K2.u12646 = [0, 0, 0, 509237308657, 967926460449, 280260627366, 13612167972, 0] := by
  rw [show D2M8K2.u12646 = KTree.node D2M8K2.t12654 (nat_lit 27160795) (nat_lit 2216827072) (nat_lit 0) D2M8K2.t12655 from rfl, totK_node, tot12654, tot12655]
  decide +kernel

theorem arows12650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12650 = true := by
  rw [show D2M8K2.u12650 = KTree.node D2M8K2.t12656 (nat_lit 27206501) (nat_lit 2065902022) (nat_lit 0) D2M8K2.t12657 from rfl, allE_node, rows12656, irow12650, rows12657]
  all_goals rfl

theorem atot12650 : totK PD2M8K2 D2M8K2.u12650 = [0, 0, 382804451125, 931862940083, 430250371448, 29635495010, 0, 0] := by
  rw [show D2M8K2.u12650 = KTree.node D2M8K2.t12656 (nat_lit 27206501) (nat_lit 2065902022) (nat_lit 0) D2M8K2.t12657 from rfl, totK_node, tot12656, tot12657]
  decide +kernel

theorem arows12651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12651 = true := by
  rw [show D2M8K2.u12651 = KTree.node D2M8K2.t12658 (nat_lit 27208067) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t12659 from rfl, allE_node, rows12658, irow12651, rows12659]
  all_goals rfl

theorem atot12651 : totK PD2M8K2 D2M8K2.u12651 = [0, 0, 118146957325, 686056031374, 827396185364, 134602830392, 1369150432, 0] := by
  rw [show D2M8K2.u12651 = KTree.node D2M8K2.t12658 (nat_lit 27208067) (nat_lit 2947981234) (nat_lit 0) D2M8K2.t12659 from rfl, totK_node, tot12658, tot12659]
  decide +kernel

theorem arows12653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12653 = true := by
  rw [show D2M8K2.u12653 = KTree.node D2M8K2.t12660 (nat_lit 27210415) (nat_lit 1987986177) (nat_lit 0) D2M8K2.t12661 from rfl, allE_node, rows12660, irow12653, rows12661]
  all_goals rfl

theorem atot12653 : totK PD2M8K2 D2M8K2.u12653 = [0, 0, 357914267981, 953875247838, 489127586617, 27674338237, 0, 0] := by
  rw [show D2M8K2.u12653 = KTree.node D2M8K2.t12660 (nat_lit 27210415) (nat_lit 1987986177) (nat_lit 0) D2M8K2.t12661 from rfl, totK_node, tot12660, tot12661]
  decide +kernel

theorem arows12654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12654 = true := by
  rw [show D2M8K2.u12654 = KTree.node D2M8K2.t12662 (nat_lit 27213729) (nat_lit 1850755050) (nat_lit 0) D2M8K2.t12663 from rfl, allE_node, rows12662, irow12654, rows12663]
  all_goals rfl

theorem atot12654 : totK PD2M8K2 D2M8K2.u12654 = [0, 0, 318309646710, 898825195176, 544495835837, 43174709497, 0, 0] := by
  rw [show D2M8K2.u12654 = KTree.node D2M8K2.t12662 (nat_lit 27213729) (nat_lit 1850755050) (nat_lit 0) D2M8K2.t12663 from rfl, totK_node, tot12662, tot12663]
  decide +kernel

theorem arows12657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12657 = true := by
  rw [show D2M8K2.u12657 = KTree.node D2M8K2.t12664 (nat_lit 27215435) (nat_lit 2082816059) (nat_lit 0) D2M8K2.t12665 from rfl, allE_node, rows12664, irow12657, rows12665]
  all_goals rfl

theorem atot12657 : totK PD2M8K2 D2M8K2.u12657 = [0, 0, 84538960942, 565458558314, 837082162056, 250954252921, 13049727234, 0] := by
  rw [show D2M8K2.u12657 = KTree.node D2M8K2.t12664 (nat_lit 27215435) (nat_lit 2082816059) (nat_lit 0) D2M8K2.t12665 from rfl, totK_node, tot12664, tot12665]
  decide +kernel

theorem arows12658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12658 = true := by
  rw [show D2M8K2.u12658 = KTree.node D2M8K2.t12666 (nat_lit 27220299) (nat_lit 3246642149) (nat_lit 0) D2M8K2.t12667 from rfl, allE_node, rows12666, irow12658, rows12667]
  all_goals rfl

theorem atot12658 : totK PD2M8K2 D2M8K2.u12658 = [0, 0, 325593991697, 901968521686, 527305928264, 41288352379, 0, 0] := by
  rw [show D2M8K2.u12658 = KTree.node D2M8K2.t12666 (nat_lit 27220299) (nat_lit 3246642149) (nat_lit 0) D2M8K2.t12667 from rfl, totK_node, tot12666, tot12667]
  decide +kernel

theorem arows12660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12660 = true := by
  rw [show D2M8K2.u12660 = KTree.node D2M8K2.t12668 (nat_lit 27222362) (nat_lit 4217839901) (nat_lit 0) D2M8K2.t12669 from rfl, allE_node, rows12668, irow12660, rows12669]
  all_goals rfl

theorem atot12660 : totK PD2M8K2 D2M8K2.u12660 = [0, 0, 150612604471, 652091086101, 790760179762, 172357236512, 4917269347, 0] := by
  rw [show D2M8K2.u12660 = KTree.node D2M8K2.t12668 (nat_lit 27222362) (nat_lit 4217839901) (nat_lit 0) D2M8K2.t12669 from rfl, totK_node, tot12668, tot12669]
  decide +kernel

theorem arows12661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12661 = true := by
  rw [show D2M8K2.u12661 = KTree.node D2M8K2.t12670 (nat_lit 27224443) (nat_lit 1901264630) (nat_lit 512) D2M8K2.t12671 from rfl, allE_node, rows12670, irow12661, rows12671]
  all_goals rfl

theorem atot12661 : totK PD2M8K2 D2M8K2.u12661 = [0, 0, 388178022635, 935479331698, 449469727263, 27273988766, 0, 0] := by
  rw [show D2M8K2.u12661 = KTree.node D2M8K2.t12670 (nat_lit 27224443) (nat_lit 1901264630) (nat_lit 512) D2M8K2.t12671 from rfl, totK_node, tot12670, tot12671]
  decide +kernel

theorem arows12668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12668 = true := by
  rw [show D2M8K2.u12668 = KTree.node D2M8K2.t12672 (nat_lit 27248479) (nat_lit 2391233226) (nat_lit 0) D2M8K2.t12673 from rfl, allE_node, rows12672, irow12668, rows12673]
  all_goals rfl

theorem atot12668 : totK PD2M8K2 D2M8K2.u12668 = [0, 0, 254851173527, 785455767826, 613016389976, 101185503721, 1369150432, 0] := by
  rw [show D2M8K2.u12668 = KTree.node D2M8K2.t12672 (nat_lit 27248479) (nat_lit 2391233226) (nat_lit 0) D2M8K2.t12673 from rfl, totK_node, tot12672, tot12673]
  decide +kernel

theorem arows12669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12669 = true := by
  rw [show D2M8K2.u12669 = KTree.node D2M8K2.t12674 (nat_lit 27250893) (nat_lit 1494925353) (nat_lit 0) D2M8K2.t12675 from rfl, allE_node, rows12674, irow12669, rows12675]
  all_goals rfl

theorem atot12669 : totK PD2M8K2 D2M8K2.u12669 = [0, 0, 210002947152, 807548558841, 724953922982, 71907340910, 0, 0] := by
  rw [show D2M8K2.u12669 = KTree.node D2M8K2.t12674 (nat_lit 27250893) (nat_lit 1494925353) (nat_lit 0) D2M8K2.t12675 from rfl, totK_node, tot12674, tot12675]
  decide +kernel

theorem arows12671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12671 = true := by
  rw [show D2M8K2.u12671 = KTree.node D2M8K2.t12676 (nat_lit 27257625) (nat_lit 1733201725) (nat_lit 0) D2M8K2.t12677 from rfl, allE_node, rows12676, irow12671, rows12677]
  all_goals rfl

theorem atot12671 : totK PD2M8K2 D2M8K2.u12671 = [0, 0, 383872149971, 960353348869, 461843523710, 24608581089, 0, 0] := by
  rw [show D2M8K2.u12671 = KTree.node D2M8K2.t12676 (nat_lit 27257625) (nat_lit 1733201725) (nat_lit 0) D2M8K2.t12677 from rfl, totK_node, tot12676, tot12677]
  decide +kernel

theorem arows12672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12672 = true := by
  rw [show D2M8K2.u12672 = KTree.node D2M8K2.t12678 (nat_lit 27259130) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t12679 from rfl, allE_node, rows12678, irow12672, rows12679]
  all_goals rfl

theorem atot12672 : totK PD2M8K2 D2M8K2.u12672 = [0, 0, 171618738591, 755603633027, 747530889646, 117166369306, 1178750802, 0] := by
  rw [show D2M8K2.u12672 = KTree.node D2M8K2.t12678 (nat_lit 27259130) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t12679 from rfl, totK_node, tot12678, tot12679]
  decide +kernel

theorem arows12675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12675 = true := by
  rw [show D2M8K2.u12675 = KTree.node D2M8K2.t12680 (nat_lit 27261026) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t12681 from rfl, allE_node, rows12680, irow12675, rows12681]
  all_goals rfl

theorem atot12675 : totK PD2M8K2 D2M8K2.u12675 = [0, 0, 231176685989, 710555922563, 634697321078, 177458605309, 11991925116, 0] := by
  rw [show D2M8K2.u12675 = KTree.node D2M8K2.t12680 (nat_lit 27261026) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t12681 from rfl, totK_node, tot12680, tot12681]
  decide +kernel

theorem arows12676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12676 = true := by
  rw [show D2M8K2.u12676 = KTree.node D2M8K2.t12682 (nat_lit 27262283) (nat_lit 1251902287) (nat_lit 0) D2M8K2.t12683 from rfl, allE_node, rows12682, irow12676, rows12683]
  all_goals rfl

theorem atot12676 : totK PD2M8K2 D2M8K2.u12676 = [0, 0, 179009229301, 763093703841, 733435946447, 101843089338, 1096505104, 0] := by
  rw [show D2M8K2.u12676 = KTree.node D2M8K2.t12682 (nat_lit 27262283) (nat_lit 1251902287) (nat_lit 0) D2M8K2.t12683 from rfl, totK_node, tot12682, tot12683]
  decide +kernel

theorem arows12678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12678 = true := by
  rw [show D2M8K2.u12678 = KTree.node D2M8K2.t12684 (nat_lit 27264633) (nat_lit 1816676103) (nat_lit 0) D2M8K2.t12685 from rfl, allE_node, rows12684, irow12678, rows12685]
  all_goals rfl

theorem atot12678 : totK PD2M8K2 D2M8K2.u12678 = [0, 0, 291374568197, 798086361394, 599727746673, 110561535135, 3821179711, 0] := by
  rw [show D2M8K2.u12678 = KTree.node D2M8K2.t12684 (nat_lit 27264633) (nat_lit 1816676103) (nat_lit 0) D2M8K2.t12685 from rfl, totK_node, tot12684, tot12685]
  decide +kernel

theorem arows12679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12679 = true := by
  rw [show D2M8K2.u12679 = KTree.node D2M8K2.t12686 (nat_lit 27289179) (nat_lit 3422720720) (nat_lit 0) D2M8K2.t12687 from rfl, allE_node, rows12686, irow12679, rows12687]
  all_goals rfl

theorem atot12679 : totK PD2M8K2 D2M8K2.u12679 = [0, 0, 379972630089, 929534185673, 444132054047, 27669170491, 0, 0] := by
  rw [show D2M8K2.u12679 = KTree.node D2M8K2.t12686 (nat_lit 27289179) (nat_lit 3422720720) (nat_lit 0) D2M8K2.t12687 from rfl, totK_node, tot12686, tot12687]
  decide +kernel

theorem arows12683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12683 = true := by
  rw [show D2M8K2.u12683 = KTree.node D2M8K2.t12688 (nat_lit 27290425) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t12689 from rfl, allE_node, rows12688, irow12683, rows12689]
  all_goals rfl

theorem atot12683 : totK PD2M8K2 D2M8K2.u12683 = [0, 0, 121679063083, 692529412583, 804681363417, 126074977992, 1369150432, 0] := by
  rw [show D2M8K2.u12683 = KTree.node D2M8K2.t12688 (nat_lit 27290425) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t12689 from rfl, totK_node, tot12688, tot12689]
  decide +kernel

theorem arows12684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12684 = true := by
  rw [show D2M8K2.u12684 = KTree.node D2M8K2.t12690 (nat_lit 27292780) (nat_lit 3936016957) (nat_lit 0) D2M8K2.t12691 from rfl, allE_node, rows12690, irow12684, rows12691]
  all_goals rfl

theorem atot12684 : totK PD2M8K2 D2M8K2.u12684 = [0, 0, 342405846375, 899463745806, 523016267298, 41498074614, 0, 0] := by
  rw [show D2M8K2.u12684 = KTree.node D2M8K2.t12690 (nat_lit 27292780) (nat_lit 3936016957) (nat_lit 0) D2M8K2.t12691 from rfl, totK_node, tot12690, tot12691]
  decide +kernel

theorem arows12686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12686 = true := by
  rw [show D2M8K2.u12686 = KTree.node D2M8K2.t12692 (nat_lit 27295021) (nat_lit 1103305558) (nat_lit 0) D2M8K2.t12693 from rfl, allE_node, rows12692, irow12686, rows12693]
  all_goals rfl

theorem atot12686 : totK PD2M8K2 D2M8K2.u12686 = [0, 0, 163675580057, 745824939871, 762476078714, 137632854178, 1409560813, 0] := by
  rw [show D2M8K2.u12686 = KTree.node D2M8K2.t12692 (nat_lit 27295021) (nat_lit 1103305558) (nat_lit 0) D2M8K2.t12693 from rfl, totK_node, tot12692, tot12693]
  decide +kernel

theorem arows12687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12687 = true := by
  rw [show D2M8K2.u12687 = KTree.node D2M8K2.t12694 (nat_lit 27296882) (nat_lit 4002422937) (nat_lit 0) D2M8K2.t12695 from rfl, allE_node, rows12694, irow12687, rows12695]
  all_goals rfl

theorem atot12687 : totK PD2M8K2 D2M8K2.u12687 = [0, 0, 243918017985, 790811464266, 647576771834, 86099795156, 1164319620, 0] := by
  rw [show D2M8K2.u12687 = KTree.node D2M8K2.t12694 (nat_lit 27296882) (nat_lit 4002422937) (nat_lit 0) D2M8K2.t12695 from rfl, totK_node, tot12694, tot12695]
  decide +kernel

theorem arows12690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12690 = true := by
  rw [show D2M8K2.u12690 = KTree.node D2M8K2.t12696 (nat_lit 27298724) (nat_lit 2765612718) (nat_lit 0) D2M8K2.t12697 from rfl, allE_node, rows12696, irow12690, rows12697]
  all_goals rfl

theorem atot12690 : totK PD2M8K2 D2M8K2.u12690 = [0, 0, 185648347603, 669967153438, 707719368947, 186536548501, 11819130176, 0] := by
  rw [show D2M8K2.u12690 = KTree.node D2M8K2.t12696 (nat_lit 27298724) (nat_lit 2765612718) (nat_lit 0) D2M8K2.t12697 from rfl, totK_node, tot12696, tot12697]
  decide +kernel

theorem arows12691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12691 = true := by
  rw [show D2M8K2.u12691 = KTree.node D2M8K2.t12698 (nat_lit 27300465) (nat_lit 1624208752) (nat_lit 0) D2M8K2.t12699 from rfl, allE_node, rows12698, irow12691, rows12699]
  all_goals rfl

theorem atot12691 : totK PD2M8K2 D2M8K2.u12691 = [0, 0, 219243455103, 778844359367, 683241215629, 97880430413, 1198073392, 0] := by
  rw [show D2M8K2.u12691 = KTree.node D2M8K2.t12698 (nat_lit 27300465) (nat_lit 1624208752) (nat_lit 0) D2M8K2.t12699 from rfl, totK_node, tot12698, tot12699]
  decide +kernel

theorem arows12693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12693 = true := by
  rw [show D2M8K2.u12693 = KTree.node D2M8K2.t12700 (nat_lit 27302470) (nat_lit 3358484767) (nat_lit 0) D2M8K2.t12701 from rfl, allE_node, rows12700, irow12693, rows12701]
  all_goals rfl

theorem atot12693 : totK PD2M8K2 D2M8K2.u12693 = [0, 0, 226550506741, 699967455340, 659773363966, 181618634069, 11986244008, 0] := by
  rw [show D2M8K2.u12693 = KTree.node D2M8K2.t12700 (nat_lit 27302470) (nat_lit 3358484767) (nat_lit 0) D2M8K2.t12701 from rfl, totK_node, tot12700, tot12701]
  decide +kernel

theorem arows12694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12694 = true := by
  rw [show D2M8K2.u12694 = KTree.node D2M8K2.t12702 (nat_lit 27303634) (nat_lit 3087864335) (nat_lit 0) D2M8K2.t12703 from rfl, allE_node, rows12702, irow12694, rows12703]
  all_goals rfl

theorem atot12694 : totK PD2M8K2 D2M8K2.u12694 = [0, 0, 210022707060, 794126588089, 690046092361, 94961872293, 1096505104, 0] := by
  rw [show D2M8K2.u12694 = KTree.node D2M8K2.t12702 (nat_lit 27303634) (nat_lit 3087864335) (nat_lit 0) D2M8K2.t12703 from rfl, totK_node, tot12702, tot12703]
  decide +kernel

theorem arows12699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12699 = true := by
  rw [show D2M8K2.u12699 = KTree.node D2M8K2.t12704 (nat_lit 27330117) (nat_lit 1493138657) (nat_lit 0) D2M8K2.t12705 from rfl, allE_node, rows12704, irow12699, rows12705]
  all_goals rfl

theorem atot12699 : totK PD2M8K2 D2M8K2.u12699 = [0, 0, 239752153462, 757020547537, 655157447122, 130093932753, 3884009855, 0] := by
  rw [show D2M8K2.u12699 = KTree.node D2M8K2.t12704 (nat_lit 27330117) (nat_lit 1493138657) (nat_lit 0) D2M8K2.t12705 from rfl, totK_node, tot12704, tot12705]
  decide +kernel

theorem arows12700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12700 = true := by
  rw [show D2M8K2.u12700 = KTree.node D2M8K2.t12706 (nat_lit 27331666) (nat_lit 4056959791) (nat_lit 0) D2M8K2.t12707 from rfl, allE_node, rows12706, irow12700, rows12707]
  all_goals rfl

theorem atot12700 : totK PD2M8K2 D2M8K2.u12700 = [0, 0, 175585308140, 754696227277, 704710943850, 110017200386, 1369150432, 0] := by
  rw [show D2M8K2.u12700 = KTree.node D2M8K2.t12706 (nat_lit 27331666) (nat_lit 4056959791) (nat_lit 0) D2M8K2.t12707 from rfl, totK_node, tot12706, tot12707]
  decide +kernel

theorem arows12702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12702 = true := by
  rw [show D2M8K2.u12702 = KTree.node D2M8K2.t12708 (nat_lit 27337292) (nat_lit 3456330711) (nat_lit 0) D2M8K2.t12709 from rfl, allE_node, rows12708, irow12702, rows12709]
  all_goals rfl

theorem atot12702 : totK PD2M8K2 D2M8K2.u12702 = [0, 0, 311246928839, 866547483369, 567573447457, 48548918081, 0, 0] := by
  rw [show D2M8K2.u12702 = KTree.node D2M8K2.t12708 (nat_lit 27337292) (nat_lit 3456330711) (nat_lit 0) D2M8K2.t12709 from rfl, totK_node, tot12708, tot12709]
  decide +kernel

theorem arows12703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12703 = true := by
  rw [show D2M8K2.u12703 = KTree.node D2M8K2.t12710 (nat_lit 27340779) (nat_lit 3704293716) (nat_lit 0) D2M8K2.t12711 from rfl, allE_node, rows12710, irow12703, rows12711]
  all_goals rfl

theorem atot12703 : totK PD2M8K2 D2M8K2.u12703 = [0, 0, 399670962108, 951605063644, 437895234557, 26341843418, 0, 0] := by
  rw [show D2M8K2.u12703 = KTree.node D2M8K2.t12710 (nat_lit 27340779) (nat_lit 3704293716) (nat_lit 0) D2M8K2.t12711 from rfl, totK_node, tot12710, tot12711]
  decide +kernel

theorem arows12706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12706 = true := by
  rw [show D2M8K2.u12706 = KTree.node D2M8K2.t12712 (nat_lit 27347675) (nat_lit 2859965586) (nat_lit 0) D2M8K2.t12713 from rfl, allE_node, rows12712, irow12706, rows12713]
  all_goals rfl

theorem atot12706 : totK PD2M8K2 D2M8K2.u12706 = [0, 0, 398420713699, 952270091878, 449229848906, 27250835840, 0, 0] := by
  rw [show D2M8K2.u12706 = KTree.node D2M8K2.t12712 (nat_lit 27347675) (nat_lit 2859965586) (nat_lit 0) D2M8K2.t12713 from rfl, totK_node, tot12712, tot12713]
  decide +kernel

theorem arows12707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12707 = true := by
  rw [show D2M8K2.u12707 = KTree.node D2M8K2.t12714 (nat_lit 27416846) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t12715 from rfl, allE_node, rows12714, irow12707, rows12715]
  all_goals rfl

theorem atot12707 : totK PD2M8K2 D2M8K2.u12707 = [0, 242922008643, 668421290254, 670773244151, 257114308798, 17949411884, 0, 0] := by
  rw [show D2M8K2.u12707 = KTree.node D2M8K2.t12714 (nat_lit 27416846) (nat_lit 3885436770) (nat_lit 0) D2M8K2.t12715 from rfl, totK_node, tot12714, tot12715]
  decide +kernel

theorem arows12709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12709 = true := by
  rw [show D2M8K2.u12709 = KTree.node D2M8K2.t12716 (nat_lit 27418014) (nat_lit 3908975553) (nat_lit 0) D2M8K2.t12717 from rfl, allE_node, rows12716, irow12709, rows12717]
  all_goals rfl

theorem atot12709 : totK PD2M8K2 D2M8K2.u12709 = [0, 206497042769, 744047239820, 661290365901, 205394564749, 21400436502, 0, 0] := by
  rw [show D2M8K2.u12709 = KTree.node D2M8K2.t12716 (nat_lit 27418014) (nat_lit 3908975553) (nat_lit 0) D2M8K2.t12717 from rfl, totK_node, tot12716, tot12717]
  decide +kernel

theorem arows12710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12710 = true := by
  rw [show D2M8K2.u12710 = KTree.node D2M8K2.t12718 (nat_lit 27419437) (nat_lit 1087511909) (nat_lit 0) D2M8K2.t12719 from rfl, allE_node, rows12718, irow12710, rows12719]
  all_goals rfl

theorem atot12710 : totK PD2M8K2 D2M8K2.u12710 = [0, 65806493344, 461035827830, 866091112952, 380557140367, 16208961603, 0, 0] := by
  rw [show D2M8K2.u12710 = KTree.node D2M8K2.t12718 (nat_lit 27419437) (nat_lit 1087511909) (nat_lit 0) D2M8K2.t12719 from rfl, totK_node, tot12718, tot12719]
  decide +kernel

theorem arows12714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12714 = true := by
  rw [show D2M8K2.u12714 = KTree.node D2M8K2.t12720 (nat_lit 27420736) (nat_lit 3289551508) (nat_lit 0) D2M8K2.t12721 from rfl, allE_node, rows12720, irow12714, rows12721]
  all_goals rfl

theorem atot12714 : totK PD2M8K2 D2M8K2.u12714 = [0, 354340264648, 910962594511, 521693150983, 42893781545, 0, 0, 0] := by
  rw [show D2M8K2.u12714 = KTree.node D2M8K2.t12720 (nat_lit 27420736) (nat_lit 3289551508) (nat_lit 0) D2M8K2.t12721 from rfl, totK_node, tot12720, tot12721]
  decide +kernel

theorem arows12715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12715 = true := by
  rw [show D2M8K2.u12715 = KTree.node D2M8K2.t12722 (nat_lit 27422422) (nat_lit 2930599450) (nat_lit 0) D2M8K2.t12723 from rfl, allE_node, rows12722, irow12715, rows12723]
  all_goals rfl

theorem atot12715 : totK PD2M8K2 D2M8K2.u12715 = [0, 65882149240, 522542046765, 897277188641, 273373680994, 11837410003, 0, 0] := by
  rw [show D2M8K2.u12715 = KTree.node D2M8K2.t12722 (nat_lit 27422422) (nat_lit 2930599450) (nat_lit 0) D2M8K2.t12723 from rfl, totK_node, tot12722, tot12723]
  decide +kernel

theorem arows12717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12717 = true := by
  rw [show D2M8K2.u12717 = KTree.node D2M8K2.t12724 (nat_lit 27424395) (nat_lit 3730017686) (nat_lit 0) D2M8K2.t12725 from rfl, allE_node, rows12724, irow12717, rows12725]
  all_goals rfl

theorem atot12717 : totK PD2M8K2 D2M8K2.u12717 = [0, 354488597387, 936311467746, 499339466164, 36870967278, 0, 0, 0] := by
  rw [show D2M8K2.u12717 = KTree.node D2M8K2.t12724 (nat_lit 27424395) (nat_lit 3730017686) (nat_lit 0) D2M8K2.t12725 from rfl, totK_node, tot12724, tot12725]
  decide +kernel

theorem arows12718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12718 = true := by
  rw [show D2M8K2.u12718 = KTree.node D2M8K2.t12726 (nat_lit 27426095) (nat_lit 2581241356) (nat_lit 0) D2M8K2.t12727 from rfl, allE_node, rows12726, irow12718, rows12727]
  all_goals rfl

theorem atot12718 : totK PD2M8K2 D2M8K2.u12718 = [0, 31608431453, 486705782829, 949134126433, 292466490317, 12003981235, 0, 0] := by
  rw [show D2M8K2.u12718 = KTree.node D2M8K2.t12726 (nat_lit 27426095) (nat_lit 2581241356) (nat_lit 0) D2M8K2.t12727 from rfl, totK_node, tot12726, tot12727]
  decide +kernel

theorem arows12721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12721 = true := by
  rw [show D2M8K2.u12721 = KTree.node D2M8K2.t12728 (nat_lit 27427497) (nat_lit 1907412261) (nat_lit 0) D2M8K2.t12729 from rfl, allE_node, rows12728, irow12721, rows12729]
  all_goals rfl

theorem atot12721 : totK PD2M8K2 D2M8K2.u12721 = [0, 373903368963, 926917385872, 485679213892, 40449960951, 0, 0, 0] := by
  rw [show D2M8K2.u12721 = KTree.node D2M8K2.t12728 (nat_lit 27427497) (nat_lit 1907412261) (nat_lit 0) D2M8K2.t12729 from rfl, totK_node, tot12728, tot12729]
  decide +kernel

theorem arows12722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12722 = true := by
  rw [show D2M8K2.u12722 = KTree.node D2M8K2.t12730 (nat_lit 27429222) (nat_lit 2903037366) (nat_lit 0) D2M8K2.t12731 from rfl, allE_node, rows12730, irow12722, rows12731]
  all_goals rfl

theorem atot12722 : totK PD2M8K2 D2M8K2.u12722 = [0, 63594746704, 635329283248, 903551389964, 191589984861, 3867150671, 0, 0] := by
  rw [show D2M8K2.u12722 = KTree.node D2M8K2.t12730 (nat_lit 27429222) (nat_lit 2903037366) (nat_lit 0) D2M8K2.t12731 from rfl, totK_node, tot12730, tot12731]
  decide +kernel

theorem arows12724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12724 = true := by
  rw [show D2M8K2.u12724 = KTree.node D2M8K2.t12732 (nat_lit 27431060) (nat_lit 3052992090) (nat_lit 0) D2M8K2.t12733 from rfl, allE_node, rows12732, irow12724, rows12733]
  all_goals rfl

theorem atot12724 : totK PD2M8K2 D2M8K2.u12724 = [0, 354625091026, 918962351754, 508220280717, 41654719951, 0, 0, 0] := by
  rw [show D2M8K2.u12724 = KTree.node D2M8K2.t12732 (nat_lit 27431060) (nat_lit 3052992090) (nat_lit 0) D2M8K2.t12733 from rfl, totK_node, tot12732, tot12733]
  decide +kernel

theorem arows12725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12725 = true := by
  rw [show D2M8K2.u12725 = KTree.node D2M8K2.t12734 (nat_lit 27432779) (nat_lit 2383793899) (nat_lit 0) D2M8K2.t12735 from rfl, allE_node, rows12734, irow12725, rows12735]
  all_goals rfl

theorem atot12725 : totK PD2M8K2 D2M8K2.u12725 = [0, 0, 430364900201, 967493280410, 351512454977, 9478845344, 0, 0] := by
  rw [show D2M8K2.u12725 = KTree.node D2M8K2.t12734 (nat_lit 27432779) (nat_lit 2383793899) (nat_lit 0) D2M8K2.t12735 from rfl, totK_node, tot12734, tot12735]
  decide +kernel

theorem arows12731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12731 = true := by
  rw [show D2M8K2.u12731 = KTree.node D2M8K2.t12736 (nat_lit 27438001) (nat_lit 1283547754) (nat_lit 0) D2M8K2.t12737 from rfl, allE_node, rows12736, irow12731, rows12737]
  all_goals rfl

theorem atot12731 : totK PD2M8K2 D2M8K2.u12731 = [0, 0, 359203217740, 927249098924, 521724484347, 42633778887, 0, 0] := by
  rw [show D2M8K2.u12731 = KTree.node D2M8K2.t12736 (nat_lit 27438001) (nat_lit 1283547754) (nat_lit 0) D2M8K2.t12737 from rfl, totK_node, tot12736, tot12737]
  decide +kernel

theorem arows12732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12732 = true := by
  rw [show D2M8K2.u12732 = KTree.node D2M8K2.t12738 (nat_lit 27439454) (nat_lit 3825179408) (nat_lit 0) D2M8K2.t12739 from rfl, allE_node, rows12738, irow12732, rows12739]
  all_goals rfl

theorem atot12732 : totK PD2M8K2 D2M8K2.u12732 = [0, 0, 88693638382, 509046794721, 823688689723, 358649209362, 29044448997, 0] := by
  rw [show D2M8K2.u12732 = KTree.node D2M8K2.t12738 (nat_lit 27439454) (nat_lit 3825179408) (nat_lit 0) D2M8K2.t12739 from rfl, totK_node, tot12738, tot12739]
  decide +kernel

theorem arows12734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12734 = true := by
  rw [show D2M8K2.u12734 = KTree.node D2M8K2.t12740 (nat_lit 27440756) (nat_lit 3538282958) (nat_lit 0) D2M8K2.t12741 from rfl, allE_node, rows12740, irow12734, rows12741]
  all_goals rfl

theorem atot12734 : totK PD2M8K2 D2M8K2.u12734 = [0, 0, 247432336922, 702102897269, 653718886232, 205762204984, 7877424857, 0] := by
  rw [show D2M8K2.u12734 = KTree.node D2M8K2.t12740 (nat_lit 27440756) (nat_lit 3538282958) (nat_lit 0) D2M8K2.t12741 from rfl, totK_node, tot12740, tot12741]
  decide +kernel

theorem arows12735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12735 = true := by
  rw [show D2M8K2.u12735 = KTree.node D2M8K2.t12742 (nat_lit 27442254) (nat_lit 3602804972) (nat_lit 0) D2M8K2.t12743 from rfl, allE_node, rows12742, irow12735, rows12743]
  all_goals rfl

theorem atot12735 : totK PD2M8K2 D2M8K2.u12735 = [0, 0, 170791424039, 765738553865, 732532144742, 115714875241, 2909416399, 0] := by
  rw [show D2M8K2.u12735 = KTree.node D2M8K2.t12742 (nat_lit 27442254) (nat_lit 3602804972) (nat_lit 0) D2M8K2.t12743 from rfl, totK_node, tot12742, tot12743]
  decide +kernel

theorem arows12738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12738 = true := by
  rw [show D2M8K2.u12738 = KTree.node D2M8K2.t12744 (nat_lit 27444345) (nat_lit 1853268785) (nat_lit 0) D2M8K2.t12745 from rfl, allE_node, rows12744, irow12738, rows12745]
  all_goals rfl

theorem atot12738 : totK PD2M8K2 D2M8K2.u12738 = [0, 0, 247591814487, 771324003166, 657739282921, 129645137903, 2250452236, 0] := by
  rw [show D2M8K2.u12738 = KTree.node D2M8K2.t12744 (nat_lit 27444345) (nat_lit 1853268785) (nat_lit 0) D2M8K2.t12745 from rfl, totK_node, tot12744, tot12745]
  decide +kernel

theorem arows12739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12739 = true := by
  rw [show D2M8K2.u12739 = KTree.node D2M8K2.t12746 (nat_lit 27445812) (nat_lit 3068570126) (nat_lit 0) D2M8K2.t12747 from rfl, allE_node, rows12746, irow12739, rows12747]
  all_goals rfl

theorem atot12739 : totK PD2M8K2 D2M8K2.u12739 = [0, 0, 170862476745, 741295592631, 723590308198, 140437845557, 4031931762, 0] := by
  rw [show D2M8K2.u12739 = KTree.node D2M8K2.t12746 (nat_lit 27445812) (nat_lit 3068570126) (nat_lit 0) D2M8K2.t12747 from rfl, totK_node, tot12746, tot12747]
  decide +kernel

theorem arows12741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12741 = true := by
  rw [show D2M8K2.u12741 = KTree.node D2M8K2.t12748 (nat_lit 27447909) (nat_lit 1495181049) (nat_lit 0) D2M8K2.t12749 from rfl, allE_node, rows12748, irow12741, rows12749]
  all_goals rfl

theorem atot12741 : totK PD2M8K2 D2M8K2.u12741 = [0, 0, 276111737723, 795273849001, 621601148674, 107268970793, 1186940923, 0] := by
  rw [show D2M8K2.u12741 = KTree.node D2M8K2.t12748 (nat_lit 27447909) (nat_lit 1495181049) (nat_lit 0) D2M8K2.t12749 from rfl, totK_node, tot12748, tot12749]
  decide +kernel

theorem arows12742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12742 = true := by
  rw [show D2M8K2.u12742 = KTree.node D2M8K2.t12750 (nat_lit 27449372) (nat_lit 3002968983) (nat_lit 0) D2M8K2.t12751 from rfl, allE_node, rows12750, irow12742, rows12751]
  all_goals rfl

theorem atot12742 : totK PD2M8K2 D2M8K2.u12742 = [0, 0, 143160765898, 786813852775, 791929863958, 86104112046, 0, 0] := by
  rw [show D2M8K2.u12742 = KTree.node D2M8K2.t12750 (nat_lit 27449372) (nat_lit 3002968983) (nat_lit 0) D2M8K2.t12751 from rfl, totK_node, tot12750, tot12751]
  decide +kernel

theorem arows12746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12746 = true := by
  rw [show D2M8K2.u12746 = KTree.node D2M8K2.t12752 (nat_lit 27451561) (nat_lit 1240513621) (nat_lit 0) D2M8K2.t12753 from rfl, allE_node, rows12752, irow12746, rows12753]
  all_goals rfl

theorem atot12746 : totK PD2M8K2 D2M8K2.u12746 = [0, 0, 316149806717, 841485912381, 566598424701, 95372954468, 1415142070, 0] := by
  rw [show D2M8K2.u12746 = KTree.node D2M8K2.t12752 (nat_lit 27451561) (nat_lit 1240513621) (nat_lit 0) D2M8K2.t12753 from rfl, totK_node, tot12752, tot12753]
  decide +kernel

theorem arows12747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12747 = true := by
  rw [show D2M8K2.u12747 = KTree.node D2M8K2.t12754 (nat_lit 27453372) (nat_lit 3025922233) (nat_lit 0) D2M8K2.t12755 from rfl, allE_node, rows12754, irow12747, rows12755]
  all_goals rfl

theorem atot12747 : totK PD2M8K2 D2M8K2.u12747 = [0, 0, 84786226771, 626300431744, 884952250256, 200524651412, 2484078857, 0] := by
  rw [show D2M8K2.u12747 = KTree.node D2M8K2.t12754 (nat_lit 27453372) (nat_lit 3025922233) (nat_lit 0) D2M8K2.t12755 from rfl, totK_node, tot12754, tot12755]
  decide +kernel

theorem arows12749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12749 = true := by
  rw [show D2M8K2.u12749 = KTree.node D2M8K2.t12756 (nat_lit 27455289) (nat_lit 1870966113) (nat_lit 0) D2M8K2.t12757 from rfl, allE_node, rows12756, irow12749, rows12757]
  all_goals rfl

theorem atot12749 : totK PD2M8K2 D2M8K2.u12749 = [0, 324875230463, 877056711472, 440404609758, 69535501654, 64886976868, 6818291842, 0] := by
  rw [show D2M8K2.u12749 = KTree.node D2M8K2.t12756 (nat_lit 27455289) (nat_lit 1870966113) (nat_lit 0) D2M8K2.t12757 from rfl, totK_node, tot12756, tot12757]
  decide +kernel

theorem arows12750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12750 = true := by
  rw [show D2M8K2.u12750 = KTree.node D2M8K2.t12758 (nat_lit 27458236) (nat_lit 3930389489) (nat_lit 0) D2M8K2.t12759 from rfl, allE_node, rows12758, irow12750, rows12759]
  all_goals rfl

theorem atot12750 : totK PD2M8K2 D2M8K2.u12750 = [0, 183106467492, 723965354977, 783326273074, 136823647537, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12750 = KTree.node D2M8K2.t12758 (nat_lit 27458236) (nat_lit 3930389489) (nat_lit 0) D2M8K2.t12759 from rfl, totK_node, tot12758, tot12759]
  decide +kernel

theorem arows12753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12753 = true := by
  rw [show D2M8K2.u12753 = KTree.node D2M8K2.t12760 (nat_lit 27459410) (nat_lit 4049472801) (nat_lit 0) D2M8K2.t12761 from rfl, allE_node, rows12760, irow12753, rows12761]
  all_goals rfl

theorem atot12753 : totK PD2M8K2 D2M8K2.u12753 = [0, 245808924928, 758673636335, 596524170678, 189857854674, 21395095148, 0, 0] := by
  rw [show D2M8K2.u12753 = KTree.node D2M8K2.t12760 (nat_lit 27459410) (nat_lit 4049472801) (nat_lit 0) D2M8K2.t12761 from rfl, totK_node, tot12760, tot12761]
  decide +kernel

theorem arows12754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12754 = true := by
  rw [show D2M8K2.u12754 = KTree.node D2M8K2.t12762 (nat_lit 27460882) (nat_lit 2716928483) (nat_lit 0) D2M8K2.t12763 from rfl, allE_node, rows12762, irow12754, rows12763]
  all_goals rfl

theorem atot12754 : totK PD2M8K2 D2M8K2.u12754 = [0, 81767663791, 455384814104, 850546424866, 388012405093, 16202021669, 0, 0] := by
  rw [show D2M8K2.u12754 = KTree.node D2M8K2.t12762 (nat_lit 27460882) (nat_lit 2716928483) (nat_lit 0) D2M8K2.t12763 from rfl, totK_node, tot12762, tot12763]
  decide +kernel

theorem arows12756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12756 = true := by
  rw [show D2M8K2.u12756 = KTree.node D2M8K2.t12764 (nat_lit 27462114) (nat_lit 1408261976) (nat_lit 0) D2M8K2.t12765 from rfl, allE_node, rows12764, irow12756, rows12765]
  all_goals rfl

theorem atot12756 : totK PD2M8K2 D2M8K2.u12756 = [0, 356748833854, 939225125844, 501012937625, 36834395031, 0, 0, 0] := by
  rw [show D2M8K2.u12756 = KTree.node D2M8K2.t12764 (nat_lit 27462114) (nat_lit 1408261976) (nat_lit 0) D2M8K2.t12765 from rfl, totK_node, tot12764, tot12765]
  decide +kernel

theorem arows12757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12757 = true := by
  rw [show D2M8K2.u12757 = KTree.node D2M8K2.t12766 (nat_lit 27463783) (nat_lit 1508665195) (nat_lit 0) D2M8K2.t12767 from rfl, allE_node, rows12766, irow12757, rows12767]
  all_goals rfl

theorem atot12757 : totK PD2M8K2 D2M8K2.u12757 = [0, 0, 476935273967, 981574044736, 300904834030, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12757 = KTree.node D2M8K2.t12766 (nat_lit 27463783) (nat_lit 1508665195) (nat_lit 0) D2M8K2.t12767 from rfl, totK_node, tot12766, tot12767]
  decide +kernel

theorem arows12762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12762 = true := by
  rw [show D2M8K2.u12762 = KTree.node D2M8K2.t12768 (nat_lit 27468893) (nat_lit 2324370134) (nat_lit 0) D2M8K2.t12769 from rfl, allE_node, rows12768, irow12762, rows12769]
  all_goals rfl

theorem atot12762 : totK PD2M8K2 D2M8K2.u12762 = [0, 388494179903, 915935637772, 473469328374, 43107507348, 0, 0, 0] := by
  rw [show D2M8K2.u12762 = KTree.node D2M8K2.t12768 (nat_lit 27468893) (nat_lit 2324370134) (nat_lit 0) D2M8K2.t12769 from rfl, totK_node, tot12768, tot12769]
  decide +kernel

theorem arows12763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12763 = true := by
  rw [show D2M8K2.u12763 = KTree.node D2M8K2.t12770 (nat_lit 27470624) (nat_lit 3762414333) (nat_lit 0) D2M8K2.t12771 from rfl, allE_node, rows12770, irow12763, rows12771]
  all_goals rfl

theorem atot12763 : totK PD2M8K2 D2M8K2.u12763 = [0, 74936445204, 617484930555, 885998662883, 205541598761, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12763 = KTree.node D2M8K2.t12770 (nat_lit 27470624) (nat_lit 3762414333) (nat_lit 0) D2M8K2.t12771 from rfl, totK_node, tot12770, tot12771]
  decide +kernel

theorem arows12765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12765 = true := by
  rw [show D2M8K2.u12765 = KTree.node D2M8K2.t12772 (nat_lit 27472468) (nat_lit 3757874428) (nat_lit 0) D2M8K2.t12773 from rfl, allE_node, rows12772, irow12765, rows12773]
  all_goals rfl

theorem atot12765 : totK PD2M8K2 D2M8K2.u12765 = [0, 336929329165, 922485010735, 527652196395, 42459230315, 0, 0, 0] := by
  rw [show D2M8K2.u12765 = KTree.node D2M8K2.t12772 (nat_lit 27472468) (nat_lit 3757874428) (nat_lit 0) D2M8K2.t12773 from rfl, totK_node, tot12772, tot12773]
  decide +kernel

theorem arows12766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12766 = true := by
  rw [show D2M8K2.u12766 = KTree.node D2M8K2.t12774 (nat_lit 27474251) (nat_lit 2383793899) (nat_lit 0) D2M8K2.t12775 from rfl, allE_node, rows12774, irow12766, rows12775]
  all_goals rfl

theorem atot12766 : totK PD2M8K2 D2M8K2.u12766 = [0, 0, 429308648203, 960775695683, 370424236618, 18232212537, 0, 0] := by
  rw [show D2M8K2.u12766 = KTree.node D2M8K2.t12774 (nat_lit 27474251) (nat_lit 2383793899) (nat_lit 0) D2M8K2.t12775 from rfl, totK_node, tot12774, tot12775]
  decide +kernel

theorem arows12769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12769 = true := by
  rw [show D2M8K2.u12769 = KTree.node D2M8K2.t12776 (nat_lit 27476450) (nat_lit 3741490392) (nat_lit 0) D2M8K2.t12777 from rfl, allE_node, rows12776, irow12769, rows12777]
  all_goals rfl

theorem atot12769 : totK PD2M8K2 D2M8K2.u12769 = [0, 0, 372323390795, 947221170519, 440151505886, 30867662800, 0, 0] := by
  rw [show D2M8K2.u12769 = KTree.node D2M8K2.t12776 (nat_lit 27476450) (nat_lit 3741490392) (nat_lit 0) D2M8K2.t12777 from rfl, totK_node, tot12776, tot12777]
  decide +kernel

theorem arows12770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12770 = true := by
  rw [show D2M8K2.u12770 = KTree.node D2M8K2.t12778 (nat_lit 27479789) (nat_lit 1544242199) (nat_lit 0) D2M8K2.t12779 from rfl, allE_node, rows12778, irow12770, rows12779]
  all_goals rfl

theorem atot12770 : totK PD2M8K2 D2M8K2.u12770 = [0, 0, 352527395308, 931115392320, 497018133014, 32699640026, 0, 0] := by
  rw [show D2M8K2.u12770 = KTree.node D2M8K2.t12778 (nat_lit 27479789) (nat_lit 1544242199) (nat_lit 0) D2M8K2.t12779 from rfl, totK_node, tot12778, tot12779]
  decide +kernel

theorem arows12772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12772 = true := by
  rw [show D2M8K2.u12772 = KTree.node D2M8K2.t12780 (nat_lit 27482740) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t12781 from rfl, allE_node, rows12780, irow12772, rows12781]
  all_goals rfl

theorem atot12772 : totK PD2M8K2 D2M8K2.u12772 = [0, 0, 386389138099, 949134763841, 446411639285, 28288117611, 0, 0] := by
  rw [show D2M8K2.u12772 = KTree.node D2M8K2.t12780 (nat_lit 27482740) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t12781 from rfl, totK_node, tot12780, tot12781]
  decide +kernel

theorem arows12773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12773 = true := by
  rw [show D2M8K2.u12773 = KTree.node D2M8K2.t12782 (nat_lit 27484446) (nat_lit 2432362848) (nat_lit 0) D2M8K2.t12783 from rfl, allE_node, rows12782, irow12773, rows12783]
  all_goals rfl

theorem atot12773 : totK PD2M8K2 D2M8K2.u12773 = [0, 0, 30011752942, 528241100319, 876821579258, 270680882928, 13016197374, 0] := by
  rw [show D2M8K2.u12773 = KTree.node D2M8K2.t12782 (nat_lit 27484446) (nat_lit 2432362848) (nat_lit 0) D2M8K2.t12783 from rfl, totK_node, tot12782, tot12783]
  decide +kernel

theorem arows12777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12777 = true := by
  rw [show D2M8K2.u12777 = KTree.node D2M8K2.t12784 (nat_lit 27489611) (nat_lit 2518730206) (nat_lit 0) D2M8K2.t12785 from rfl, allE_node, rows12784, irow12777, rows12785]
  all_goals rfl

theorem atot12777 : totK PD2M8K2 D2M8K2.u12777 = [0, 0, 393504539332, 947778208810, 444533572482, 29002121745, 0, 0] := by
  rw [show D2M8K2.u12777 = KTree.node D2M8K2.t12784 (nat_lit 27489611) (nat_lit 2518730206) (nat_lit 0) D2M8K2.t12785 from rfl, totK_node, tot12784, tot12785]
  decide +kernel

theorem arows12778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12778 = true := by
  rw [show D2M8K2.u12778 = KTree.node D2M8K2.t12786 (nat_lit 27491431) (nat_lit 1883380864) (nat_lit 0) D2M8K2.t12787 from rfl, allE_node, rows12786, irow12778, rows12787]
  all_goals rfl

theorem atot12778 : totK PD2M8K2 D2M8K2.u12778 = [0, 0, 103148523404, 696594299528, 771090324533, 150370805458, 4574395652, 0] := by
  rw [show D2M8K2.u12778 = KTree.node D2M8K2.t12786 (nat_lit 27491431) (nat_lit 1883380864) (nat_lit 0) D2M8K2.t12787 from rfl, totK_node, tot12786, tot12787]
  decide +kernel

theorem arows12780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12780 = true := by
  rw [show D2M8K2.u12780 = KTree.node D2M8K2.t12788 (nat_lit 27493382) (nat_lit 4100432831) (nat_lit 0) D2M8K2.t12789 from rfl, allE_node, rows12788, irow12780, rows12789]
  all_goals rfl

theorem atot12780 : totK PD2M8K2 D2M8K2.u12780 = [0, 74725294189, 406811436172, 827020761536, 469116618715, 38988789474, 0, 0] := by
  rw [show D2M8K2.u12780 = KTree.node D2M8K2.t12788 (nat_lit 27493382) (nat_lit 4100432831) (nat_lit 0) D2M8K2.t12789 from rfl, totK_node, tot12788, tot12789]
  decide +kernel

theorem arows12781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12781 = true := by
  rw [show D2M8K2.u12781 = KTree.node D2M8K2.t12790 (nat_lit 27497254) (nat_lit 1212599255) (nat_lit 0) D2M8K2.t12791 from rfl, allE_node, rows12790, irow12781, rows12791]
  all_goals rfl

theorem atot12781 : totK PD2M8K2 D2M8K2.u12781 = [0, 250286109675, 838339946081, 610812661305, 86976200024, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12781 = KTree.node D2M8K2.t12790 (nat_lit 27497254) (nat_lit 1212599255) (nat_lit 0) D2M8K2.t12791 from rfl, totK_node, tot12790, tot12791]
  decide +kernel

theorem arows12784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12784 = true := by
  rw [show D2M8K2.u12784 = KTree.node D2M8K2.t12792 (nat_lit 27499880) (nat_lit 3628393285) (nat_lit 0) D2M8K2.t12793 from rfl, allE_node, rows12792, irow12784, rows12793]
  all_goals rfl

theorem atot12784 : totK PD2M8K2 D2M8K2.u12784 = [0, 255834454894, 831541768765, 682143965370, 79499947304, 0, 0, 0] := by
  rw [show D2M8K2.u12784 = KTree.node D2M8K2.t12792 (nat_lit 27499880) (nat_lit 3628393285) (nat_lit 0) D2M8K2.t12793 from rfl, totK_node, tot12792, tot12793]
  decide +kernel

theorem arows12785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12785 = true := by
  rw [show D2M8K2.u12785 = KTree.node D2M8K2.t12794 (nat_lit 27501101) (nat_lit 2087930190) (nat_lit 0) D2M8K2.t12795 from rfl, allE_node, rows12794, irow12785, rows12795]
  all_goals rfl

theorem atot12785 : totK PD2M8K2 D2M8K2.u12785 = [0, 173125932643, 638642845968, 690518994500, 274639785643, 25364689049, 0, 0] := by
  rw [show D2M8K2.u12785 = KTree.node D2M8K2.t12794 (nat_lit 27501101) (nat_lit 2087930190) (nat_lit 0) D2M8K2.t12795 from rfl, totK_node, tot12794, tot12795]
  decide +kernel

theorem arows12787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12787 = true := by
  rw [show D2M8K2.u12787 = KTree.node D2M8K2.t12796 (nat_lit 27502610) (nat_lit 4015269650) (nat_lit 0) D2M8K2.t12797 from rfl, allE_node, rows12796, irow12787, rows12797]
  all_goals rfl

theorem atot12787 : totK PD2M8K2 D2M8K2.u12787 = [0, 155984292415, 578958212059, 758073217900, 297325857207, 12230400950, 0, 0] := by
  rw [show D2M8K2.u12787 = KTree.node D2M8K2.t12796 (nat_lit 27502610) (nat_lit 4015269650) (nat_lit 0) D2M8K2.t12797 from rfl, totK_node, tot12796, tot12797]
  decide +kernel

theorem arows12788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12788 = true := by
  rw [show D2M8K2.u12788 = KTree.node D2M8K2.t12798 (nat_lit 27507536) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t12799 from rfl, allE_node, rows12798, irow12788, rows12799]
  all_goals rfl

theorem atot12788 : totK PD2M8K2 D2M8K2.u12788 = [0, 282719729032, 878126214051, 603126688689, 57397819062, 0, 0, 0] := by
  rw [show D2M8K2.u12788 = KTree.node D2M8K2.t12798 (nat_lit 27507536) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t12799 from rfl, totK_node, tot12798, tot12799]
  decide +kernel

theorem arows12797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12797 = true := by
  rw [show D2M8K2.u12797 = KTree.node D2M8K2.t12800 (nat_lit 27509210) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t12801 from rfl, allE_node, rows12800, irow12797, rows12801]
  all_goals rfl

theorem atot12797 : totK PD2M8K2 D2M8K2.u12797 = [0, 77658537643, 522029630723, 874419141577, 292780676659, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12797 = KTree.node D2M8K2.t12800 (nat_lit 27509210) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t12801 from rfl, totK_node, tot12800, tot12801]
  decide +kernel

theorem arows12798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12798 = true := by
  rw [show D2M8K2.u12798 = KTree.node D2M8K2.t12802 (nat_lit 27510629) (nat_lit 1821814398) (nat_lit 0) D2M8K2.t12803 from rfl, allE_node, rows12802, irow12798, rows12803]
  all_goals rfl

theorem atot12798 : totK PD2M8K2 D2M8K2.u12798 = [0, 336129503034, 914407807363, 528304921458, 44247086111, 0, 0, 0] := by
  rw [show D2M8K2.u12798 = KTree.node D2M8K2.t12802 (nat_lit 27510629) (nat_lit 1821814398) (nat_lit 0) D2M8K2.t12803 from rfl, totK_node, tot12802, tot12803]
  decide +kernel

theorem arows12800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12800 = true := by
  rw [show D2M8K2.u12800 = KTree.node D2M8K2.t12804 (nat_lit 27512468) (nat_lit 3667981016) (nat_lit 0) D2M8K2.t12805 from rfl, allE_node, rows12804, irow12800, rows12805]
  all_goals rfl

theorem atot12800 : totK PD2M8K2 D2M8K2.u12800 = [0, 119263646302, 628981389280, 844441345306, 201580397406, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12800 = KTree.node D2M8K2.t12804 (nat_lit 27512468) (nat_lit 3667981016) (nat_lit 0) D2M8K2.t12805 from rfl, totK_node, tot12804, tot12805]
  decide +kernel

theorem arows12801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12801 = true := by
  rw [show D2M8K2.u12801 = KTree.node D2M8K2.t12806 (nat_lit 27514251) (nat_lit 3723494530) (nat_lit 0) D2M8K2.t12807 from rfl, allE_node, rows12806, irow12801, rows12807]
  all_goals rfl

theorem atot12801 : totK PD2M8K2 D2M8K2.u12801 = [0, 267469010271, 814334087194, 633955318507, 96614124185, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12801 = KTree.node D2M8K2.t12806 (nat_lit 27514251) (nat_lit 3723494530) (nat_lit 0) D2M8K2.t12807 from rfl, totK_node, tot12806, tot12807]
  decide +kernel

theorem arows12804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12804 = true := by
  rw [show D2M8K2.u12804 = KTree.node D2M8K2.t12808 (nat_lit 27516078) (nat_lit 3888769375) (nat_lit 0) D2M8K2.t12809 from rfl, allE_node, rows12808, irow12804, rows12809]
  all_goals rfl

theorem atot12804 : totK PD2M8K2 D2M8K2.u12804 = [0, 0, 423984955112, 958038411837, 383874544804, 18403315207, 0, 0] := by
  rw [show D2M8K2.u12804 = KTree.node D2M8K2.t12808 (nat_lit 27516078) (nat_lit 3888769375) (nat_lit 0) D2M8K2.t12809 from rfl, totK_node, tot12808, tot12809]
  decide +kernel

theorem arows12805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12805 = true := by
  rw [show D2M8K2.u12805 = KTree.node D2M8K2.t12810 (nat_lit 27518192) (nat_lit 2902124967) (nat_lit 0) D2M8K2.t12811 from rfl, allE_node, rows12810, irow12805, rows12811]
  all_goals rfl

theorem atot12805 : totK PD2M8K2 D2M8K2.u12805 = [0, 0, 382209059763, 929548487650, 471378676790, 38197885173, 0, 0] := by
  rw [show D2M8K2.u12805 = KTree.node D2M8K2.t12810 (nat_lit 27518192) (nat_lit 2902124967) (nat_lit 0) D2M8K2.t12811 from rfl, totK_node, tot12810, tot12811]
  decide +kernel

theorem arows12807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12807 = true := by
  rw [show D2M8K2.u12807 = KTree.node D2M8K2.t12812 (nat_lit 27521472) (nat_lit 2259995937) (nat_lit 0) D2M8K2.t12813 from rfl, allE_node, rows12812, irow12807, rows12813]
  all_goals rfl

theorem atot12807 : totK PD2M8K2 D2M8K2.u12807 = [0, 0, 343287004371, 951798360587, 474716977478, 26633471598, 0, 0] := by
  rw [show D2M8K2.u12807 = KTree.node D2M8K2.t12812 (nat_lit 27521472) (nat_lit 2259995937) (nat_lit 0) D2M8K2.t12813 from rfl, totK_node, tot12812, tot12813]
  decide +kernel

theorem arows12808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12808 = true := by
  rw [show D2M8K2.u12808 = KTree.node D2M8K2.t12814 (nat_lit 27528150) (nat_lit 3867271593) (nat_lit 0) D2M8K2.t12815 from rfl, allE_node, rows12814, irow12808, rows12815]
  all_goals rfl

theorem atot12808 : totK PD2M8K2 D2M8K2.u12808 = [0, 0, 355782120981, 923818895452, 502817417798, 36212595015, 0, 0] := by
  rw [show D2M8K2.u12808 = KTree.node D2M8K2.t12814 (nat_lit 27528150) (nat_lit 3867271593) (nat_lit 0) D2M8K2.t12815 from rfl, totK_node, tot12814, tot12815]
  decide +kernel

theorem arows12812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12812 = true := by
  rw [show D2M8K2.u12812 = KTree.node D2M8K2.t12816 (nat_lit 27529851) (nat_lit 2960180127) (nat_lit 0) D2M8K2.t12817 from rfl, allE_node, rows12816, irow12812, rows12817]
  all_goals rfl

theorem atot12812 : totK PD2M8K2 D2M8K2.u12812 = [0, 0, 66967892138, 524879430834, 854119986419, 277453381182, 13105450397, 0] := by
  rw [show D2M8K2.u12812 = KTree.node D2M8K2.t12816 (nat_lit 27529851) (nat_lit 2960180127) (nat_lit 0) D2M8K2.t12817 from rfl, totK_node, tot12816, tot12817]
  decide +kernel

theorem arows12813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12813 = true := by
  rw [show D2M8K2.u12813 = KTree.node D2M8K2.t12818 (nat_lit 27531324) (nat_lit 2458540614) (nat_lit 2048) D2M8K2.t12819 from rfl, allE_node, rows12818, irow12813, rows12819]
  all_goals rfl

theorem atot12813 : totK PD2M8K2 D2M8K2.u12813 = [0, 0, 342243243364, 963944667567, 474748818962, 26039154446, 0, 0] := by
  rw [show D2M8K2.u12813 = KTree.node D2M8K2.t12818 (nat_lit 27531324) (nat_lit 2458540614) (nat_lit 2048) D2M8K2.t12819 from rfl, totK_node, tot12818, tot12819]
  decide +kernel

theorem arows12815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12815 = true := by
  rw [show D2M8K2.u12815 = KTree.node D2M8K2.t12820 (nat_lit 27533408) (nat_lit 3838293110) (nat_lit 0) D2M8K2.t12821 from rfl, allE_node, rows12820, irow12815, rows12821]
  all_goals rfl

theorem atot12815 : totK PD2M8K2 D2M8K2.u12815 = [0, 0, 152604957350, 700007524043, 737876766774, 153601997377, 4720618446, 0] := by
  rw [show D2M8K2.u12815 = KTree.node D2M8K2.t12820 (nat_lit 27533408) (nat_lit 3838293110) (nat_lit 0) D2M8K2.t12821 from rfl, totK_node, tot12820, tot12821]
  decide +kernel

theorem arows12816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12816 = true := by
  rw [show D2M8K2.u12816 = KTree.node D2M8K2.t12822 (nat_lit 27535091) (nat_lit 2946963925) (nat_lit 0) D2M8K2.t12823 from rfl, allE_node, rows12822, irow12816, rows12823]
  all_goals rfl

theorem atot12816 : totK PD2M8K2 D2M8K2.u12816 = [0, 104114512826, 468235849157, 743555991539, 446841027000, 41583071754, 0, 0] := by
  rw [show D2M8K2.u12816 = KTree.node D2M8K2.t12822 (nat_lit 27535091) (nat_lit 2946963925) (nat_lit 0) D2M8K2.t12823 from rfl, totK_node, tot12822, tot12823]
  decide +kernel

theorem arows12819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12819 = true := by
  rw [show D2M8K2.u12819 = KTree.node D2M8K2.t12824 (nat_lit 27538613) (nat_lit 2373749623) (nat_lit 0) D2M8K2.t12825 from rfl, allE_node, rows12824, irow12819, rows12825]
  all_goals rfl

theorem atot12819 : totK PD2M8K2 D2M8K2.u12819 = [0, 236315663464, 792535800641, 646389665277, 103227935145, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12819 = KTree.node D2M8K2.t12824 (nat_lit 27538613) (nat_lit 2373749623) (nat_lit 0) D2M8K2.t12825 from rfl, totK_node, tot12824, tot12825]
  decide +kernel

theorem arows12820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12820 = true := by
  rw [show D2M8K2.u12820 = KTree.node D2M8K2.t12826 (nat_lit 27541410) (nat_lit 3299736308) (nat_lit 0) D2M8K2.t12827 from rfl, allE_node, rows12826, irow12820, rows12827]
  all_goals rfl

theorem atot12820 : totK PD2M8K2 D2M8K2.u12820 = [0, 268187714162, 841777260095, 655316833028, 69238992138, 0, 0, 0] := by
  rw [show D2M8K2.u12820 = KTree.node D2M8K2.t12826 (nat_lit 27541410) (nat_lit 3299736308) (nat_lit 0) D2M8K2.t12827 from rfl, totK_node, tot12826, tot12827]
  decide +kernel

theorem arows12822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12822 = true := by
  rw [show D2M8K2.u12822 = KTree.node D2M8K2.t12828 (nat_lit 27542938) (nat_lit 3856239378) (nat_lit 0) D2M8K2.t12829 from rfl, allE_node, rows12828, irow12822, rows12829]
  all_goals rfl

theorem atot12822 : totK PD2M8K2 D2M8K2.u12822 = [0, 162037142227, 644684614705, 714004650964, 278675355053, 25370006417, 0, 0] := by
  rw [show D2M8K2.u12822 = KTree.node D2M8K2.t12828 (nat_lit 27542938) (nat_lit 3856239378) (nat_lit 0) D2M8K2.t12829 from rfl, totK_node, tot12828, tot12829]
  decide +kernel

theorem arows12823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12823 = true := by
  rw [show D2M8K2.u12823 = KTree.node D2M8K2.t12830 (nat_lit 27544153) (nat_lit 739533641) (nat_lit 0) D2M8K2.t12831 from rfl, allE_node, rows12830, irow12823, rows12831]
  all_goals rfl

theorem atot12823 : totK PD2M8K2 D2M8K2.u12823 = [0, 166517582303, 587809481452, 739631012171, 304061039539, 12231701805, 0, 0] := by
  rw [show D2M8K2.u12823 = KTree.node D2M8K2.t12830 (nat_lit 27544153) (nat_lit 739533641) (nat_lit 0) D2M8K2.t12831 from rfl, totK_node, tot12830, tot12831]
  decide +kernel

theorem arows12828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12828 = true := by
  rw [show D2M8K2.u12828 = KTree.node D2M8K2.t12832 (nat_lit 27545643) (nat_lit 3717246024) (nat_lit 0) D2M8K2.t12833 from rfl, allE_node, rows12832, irow12828, rows12833]
  all_goals rfl

theorem atot12828 : totK PD2M8K2 D2M8K2.u12828 = [0, 247303354139, 792388139834, 649827215193, 99733547004, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12828 = KTree.node D2M8K2.t12832 (nat_lit 27545643) (nat_lit 3717246024) (nat_lit 0) D2M8K2.t12833 from rfl, totK_node, tot12832, tot12833]
  decide +kernel

theorem arows12829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12829 = true := by
  rw [show D2M8K2.u12829 = KTree.node D2M8K2.t12834 (nat_lit 27547376) (nat_lit 3691776655) (nat_lit 0) D2M8K2.t12835 from rfl, allE_node, rows12834, irow12829, rows12835]
  all_goals rfl

theorem atot12829 : totK PD2M8K2 D2M8K2.u12829 = [0, 166594156294, 636944761389, 749199919815, 218390968794, 11885407614, 0, 0] := by
  rw [show D2M8K2.u12829 = KTree.node D2M8K2.t12834 (nat_lit 27547376) (nat_lit 3691776655) (nat_lit 0) D2M8K2.t12835 from rfl, totK_node, tot12834, tot12835]
  decide +kernel

theorem arows12831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12831 = true := by
  rw [show D2M8K2.u12831 = KTree.node D2M8K2.t12836 (nat_lit 27549031) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t12837 from rfl, allE_node, rows12836, irow12831, rows12837]
  all_goals rfl

theorem atot12831 : totK PD2M8K2 D2M8K2.u12831 = [0, 247452901701, 793418446810, 651280369665, 99827466760, 1198073392, 0, 0] := by
  rw [show D2M8K2.u12831 = KTree.node D2M8K2.t12836 (nat_lit 27549031) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t12837 from rfl, totK_node, tot12836, tot12837]
  decide +kernel

theorem arows12832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12832 = true := by
  rw [show D2M8K2.u12832 = KTree.node D2M8K2.t12838 (nat_lit 27550759) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t12839 from rfl, allE_node, rows12838, irow12832, rows12839]
  all_goals rfl

theorem atot12832 : totK PD2M8K2 D2M8K2.u12832 = [0, 138591533057, 616766287513, 786037055349, 238641264484, 12052611869, 0, 0] := by
  rw [show D2M8K2.u12832 = KTree.node D2M8K2.t12838 (nat_lit 27550759) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t12839 from rfl, totK_node, tot12838, tot12839]
  decide +kernel

theorem arows12835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12835 = true := by
  rw [show D2M8K2.u12835 = KTree.node D2M8K2.t12840 (nat_lit 27552178) (nat_lit 3692539227) (nat_lit 0) D2M8K2.t12841 from rfl, allE_node, rows12840, irow12835, rows12841]
  all_goals rfl

theorem atot12835 : totK PD2M8K2 D2M8K2.u12835 = [0, 301076925428, 898873262469, 574296408265, 53977851311, 0, 0, 0] := by
  rw [show D2M8K2.u12835 = KTree.node D2M8K2.t12840 (nat_lit 27552178) (nat_lit 3692539227) (nat_lit 0) D2M8K2.t12841 from rfl, totK_node, tot12840, tot12841]
  decide +kernel

theorem arows12836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12836 = true := by
  rw [show D2M8K2.u12836 = KTree.node D2M8K2.t12842 (nat_lit 27554117) (nat_lit 2280755039) (nat_lit 0) D2M8K2.t12843 from rfl, allE_node, rows12842, irow12836, rows12843]
  all_goals rfl

theorem atot12836 : totK PD2M8K2 D2M8K2.u12836 = [0, 0, 497768980059, 1022161251747, 277701520793, 6350335412, 0, 0] := by
  rw [show D2M8K2.u12836 = KTree.node D2M8K2.t12842 (nat_lit 27554117) (nat_lit 2280755039) (nat_lit 0) D2M8K2.t12843 from rfl, totK_node, tot12842, tot12843]
  decide +kernel

theorem arows12838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12838 = true := by
  rw [show D2M8K2.u12838 = KTree.node D2M8K2.t12844 (nat_lit 27559387) (nat_lit 2224327604) (nat_lit 0) D2M8K2.t12845 from rfl, allE_node, rows12844, irow12838, rows12845]
  all_goals rfl

theorem atot12838 : totK PD2M8K2 D2M8K2.u12838 = [0, 0, 365073545249, 911882026339, 475633088079, 42723698618, 0, 0] := by
  rw [show D2M8K2.u12838 = KTree.node D2M8K2.t12844 (nat_lit 27559387) (nat_lit 2224327604) (nat_lit 0) D2M8K2.t12845 from rfl, totK_node, tot12844, tot12845]
  decide +kernel

theorem arows12839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12839 = true := by
  rw [show D2M8K2.u12839 = KTree.node D2M8K2.t12846 (nat_lit 27562861) (nat_lit 1108564402) (nat_lit 0) D2M8K2.t12847 from rfl, allE_node, rows12846, irow12839, rows12847]
  all_goals rfl

theorem atot12839 : totK PD2M8K2 D2M8K2.u12839 = [0, 0, 343945374609, 959547646249, 454883396650, 25702417828, 0, 0] := by
  rw [show D2M8K2.u12839 = KTree.node D2M8K2.t12846 (nat_lit 27562861) (nat_lit 1108564402) (nat_lit 0) D2M8K2.t12847 from rfl, totK_node, tot12846, tot12847]
  decide +kernel

theorem arows12843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12843 = true := by
  rw [show D2M8K2.u12843 = KTree.node D2M8K2.t12848 (nat_lit 27566212) (nat_lit 3756330783) (nat_lit 0) D2M8K2.t12849 from rfl, allE_node, rows12848, irow12843, rows12849]
  all_goals rfl

theorem atot12843 : totK PD2M8K2 D2M8K2.u12843 = [0, 0, 399944575339, 952111185902, 435945958508, 24759104640, 0, 0] := by
  rw [show D2M8K2.u12843 = KTree.node D2M8K2.t12848 (nat_lit 27566212) (nat_lit 3756330783) (nat_lit 0) D2M8K2.t12849 from rfl, totK_node, tot12848, tot12849]
  decide +kernel

theorem arows12844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12844 = true := by
  rw [show D2M8K2.u12844 = KTree.node D2M8K2.t12850 (nat_lit 27569530) (nat_lit 3540320949) (nat_lit 0) D2M8K2.t12851 from rfl, allE_node, rows12850, irow12844, rows12851]
  all_goals rfl

theorem atot12844 : totK PD2M8K2 D2M8K2.u12844 = [0, 0, 349058144317, 948379496526, 477744156379, 26135344416, 0, 0] := by
  rw [show D2M8K2.u12844 = KTree.node D2M8K2.t12850 (nat_lit 27569530) (nat_lit 3540320949) (nat_lit 0) D2M8K2.t12851 from rfl, totK_node, tot12850, tot12851]
  decide +kernel

theorem arows12846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12846 = true := by
  rw [show D2M8K2.u12846 = KTree.node D2M8K2.t12852 (nat_lit 27572574) (nat_lit 3216350317) (nat_lit 0) D2M8K2.t12853 from rfl, allE_node, rows12852, irow12846, rows12853]
  all_goals rfl

theorem atot12846 : totK PD2M8K2 D2M8K2.u12846 = [0, 0, 382428393612, 933588828444, 449727584199, 32547243808, 0, 0] := by
  rw [show D2M8K2.u12846 = KTree.node D2M8K2.t12852 (nat_lit 27572574) (nat_lit 3216350317) (nat_lit 0) D2M8K2.t12853 from rfl, totK_node, tot12852, tot12853]
  decide +kernel

theorem arows12847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12847 = true := by
  rw [show D2M8K2.u12847 = KTree.node D2M8K2.t12854 (nat_lit 27574277) (nat_lit 2327739443) (nat_lit 0) D2M8K2.t12855 from rfl, allE_node, rows12854, irow12847, rows12855]
  all_goals rfl

theorem atot12847 : totK PD2M8K2 D2M8K2.u12847 = [0, 22713249043, 89911278446, 618292807485, 822580354102, 191084932987, 4977114383, 0] := by
  rw [show D2M8K2.u12847 = KTree.node D2M8K2.t12854 (nat_lit 27574277) (nat_lit 2327739443) (nat_lit 0) D2M8K2.t12855 from rfl, totK_node, tot12854, tot12855]
  decide +kernel

theorem arows12850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12850 = true := by
  rw [show D2M8K2.u12850 = KTree.node D2M8K2.t12856 (nat_lit 27583213) (nat_lit 1126296431) (nat_lit 0) D2M8K2.t12857 from rfl, allE_node, rows12856, irow12850, rows12857]
  all_goals rfl

theorem atot12850 : totK PD2M8K2 D2M8K2.u12850 = [0, 372660213517, 929462480063, 485114841991, 40443072092, 0, 0, 0] := by
  rw [show D2M8K2.u12850 = KTree.node D2M8K2.t12856 (nat_lit 27583213) (nat_lit 1126296431) (nat_lit 0) D2M8K2.t12857 from rfl, totK_node, tot12856, tot12857]
  decide +kernel

theorem arows12851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12851 = true := by
  rw [show D2M8K2.u12851 = KTree.node D2M8K2.t12858 (nat_lit 27584687) (nat_lit 2124004481) (nat_lit 0) D2M8K2.t12859 from rfl, allE_node, rows12858, irow12851, rows12859]
  all_goals rfl

theorem atot12851 : totK PD2M8K2 D2M8K2.u12851 = [0, 26464483550, 471939491998, 890167593312, 390679361245, 29375735501, 0, 0] := by
  rw [show D2M8K2.u12851 = KTree.node D2M8K2.t12858 (nat_lit 27584687) (nat_lit 2124004481) (nat_lit 0) D2M8K2.t12859 from rfl, totK_node, tot12858, tot12859]
  decide +kernel

theorem arows12853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12853 = true := by
  rw [show D2M8K2.u12853 = KTree.node D2M8K2.t12860 (nat_lit 27586067) (nat_lit 2901651725) (nat_lit 0) D2M8K2.t12861 from rfl, allE_node, rows12860, irow12853, rows12861]
  all_goals rfl

theorem atot12853 : totK PD2M8K2 D2M8K2.u12853 = [0, 247194791840, 712323171883, 650241598946, 201167487410, 8213711289, 0, 0] := by
  rw [show D2M8K2.u12853 = KTree.node D2M8K2.t12860 (nat_lit 27586067) (nat_lit 2901651725) (nat_lit 0) D2M8K2.t12861 from rfl, totK_node, tot12860, tot12861]
  decide +kernel

theorem arows12854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12854 = true := by
  rw [show D2M8K2.u12854 = KTree.node D2M8K2.t12862 (nat_lit 27587588) (nat_lit 3141659001) (nat_lit 0) D2M8K2.t12863 from rfl, allE_node, rows12862, irow12854, rows12863]
  all_goals rfl

theorem atot12854 : totK PD2M8K2 D2M8K2.u12854 = [0, 156264529942, 668002396832, 759177802224, 203744675009, 8192599454, 0, 0] := by
  rw [show D2M8K2.u12854 = KTree.node D2M8K2.t12862 (nat_lit 27587588) (nat_lit 3141659001) (nat_lit 0) D2M8K2.t12863 from rfl, totK_node, tot12862, tot12863]
  decide +kernel

theorem arows12860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12860 = true := by
  rw [show D2M8K2.u12860 = KTree.node D2M8K2.t12864 (nat_lit 27589583) (nat_lit 2147245901) (nat_lit 0) D2M8K2.t12865 from rfl, allE_node, rows12864, irow12860, rows12865]
  all_goals rfl

theorem atot12860 : totK PD2M8K2 D2M8K2.u12860 = [0, 258287677693, 788523172105, 657356178267, 111711820449, 1288020181, 0, 0] := by
  rw [show D2M8K2.u12860 = KTree.node D2M8K2.t12864 (nat_lit 27589583) (nat_lit 2147245901) (nat_lit 0) D2M8K2.t12865 from rfl, totK_node, tot12864, tot12865]
  decide +kernel

theorem arows12861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12861 = true := by
  rw [show D2M8K2.u12861 = KTree.node D2M8K2.t12866 (nat_lit 27591099) (nat_lit 2926314110) (nat_lit 0) D2M8K2.t12867 from rfl, allE_node, rows12866, irow12861, rows12867]
  all_goals rfl

theorem atot12861 : totK PD2M8K2 D2M8K2.u12861 = [0, 143158187961, 665737468023, 770961190985, 209509658931, 8265692893, 0, 0] := by
  rw [show D2M8K2.u12861 = KTree.node D2M8K2.t12866 (nat_lit 27591099) (nat_lit 2926314110) (nat_lit 0) D2M8K2.t12867 from rfl, totK_node, tot12866, tot12867]
  decide +kernel

theorem arows12863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12863 = true := by
  rw [show D2M8K2.u12863 = KTree.node D2M8K2.t12868 (nat_lit 27596507) (nat_lit 2859965586) (nat_lit 0) D2M8K2.t12869 from rfl, allE_node, rows12868, irow12863, rows12869]
  all_goals rfl

theorem atot12863 : totK PD2M8K2 D2M8K2.u12863 = [0, 276587717093, 798823633611, 632668031128, 111991848666, 1334241821, 0, 0] := by
  rw [show D2M8K2.u12863 = KTree.node D2M8K2.t12868 (nat_lit 27596507) (nat_lit 2859965586) (nat_lit 0) D2M8K2.t12869 from rfl, totK_node, tot12868, tot12869]
  decide +kernel

theorem arows12864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12864 = true := by
  rw [show D2M8K2.u12864 = KTree.node D2M8K2.t12870 (nat_lit 27597938) (nat_lit 3243273556) (nat_lit 0) D2M8K2.t12871 from rfl, allE_node, rows12870, irow12864, rows12871]
  all_goals rfl

theorem atot12864 : totK PD2M8K2 D2M8K2.u12864 = [0, 148990985574, 677524948519, 783350852547, 188248826559, 4967996017, 0, 0] := by
  rw [show D2M8K2.u12864 = KTree.node D2M8K2.t12870 (nat_lit 27597938) (nat_lit 3243273556) (nat_lit 0) D2M8K2.t12871 from rfl, totK_node, tot12870, tot12871]
  decide +kernel

theorem arows12867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12867 = true := by
  rw [show D2M8K2.u12867 = KTree.node D2M8K2.t12872 (nat_lit 27603386) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t12873 from rfl, allE_node, rows12872, irow12867, rows12873]
  all_goals rfl

theorem atot12867 : totK PD2M8K2 D2M8K2.u12867 = [0, 0, 358808626188, 905840067587, 498657507322, 44292591756, 0, 0] := by
  rw [show D2M8K2.u12867 = KTree.node D2M8K2.t12872 (nat_lit 27603386) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t12873 from rfl, totK_node, tot12872, tot12873]
  decide +kernel

theorem arows12868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12868 = true := by
  rw [show D2M8K2.u12868 = KTree.node D2M8K2.t12874 (nat_lit 27604574) (nat_lit 3889182706) (nat_lit 0) D2M8K2.t12875 from rfl, allE_node, rows12874, irow12868, rows12875]
  all_goals rfl

theorem atot12868 : totK PD2M8K2 D2M8K2.u12868 = [0, 0, 404057017137, 976456960584, 435999068535, 19650945882, 0, 0] := by
  rw [show D2M8K2.u12868 = KTree.node D2M8K2.t12874 (nat_lit 27604574) (nat_lit 3889182706) (nat_lit 0) D2M8K2.t12875 from rfl, totK_node, tot12874, tot12875]
  decide +kernel

theorem arows12870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12870 = true := by
  rw [show D2M8K2.u12870 = KTree.node D2M8K2.t12876 (nat_lit 27607859) (nat_lit 2005964993) (nat_lit 0) D2M8K2.t12877 from rfl, allE_node, rows12876, irow12870, rows12877]
  all_goals rfl

theorem atot12870 : totK PD2M8K2 D2M8K2.u12870 = [0, 0, 246679927452, 866420185463, 636367810958, 57500133410, 0, 0] := by
  rw [show D2M8K2.u12870 = KTree.node D2M8K2.t12876 (nat_lit 27607859) (nat_lit 2005964993) (nat_lit 0) D2M8K2.t12877 from rfl, totK_node, tot12876, tot12877]
  decide +kernel

theorem arows12871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12871 = true := by
  rw [show D2M8K2.u12871 = KTree.node D2M8K2.t12878 (nat_lit 27610118) (nat_lit 3334739211) (nat_lit 0) D2M8K2.t12879 from rfl, allE_node, rows12878, irow12871, rows12879]
  all_goals rfl

theorem atot12871 : totK PD2M8K2 D2M8K2.u12871 = [0, 0, 246573870743, 777149339340, 658306848658, 111908666686, 1435164049, 0] := by
  rw [show D2M8K2.u12871 = KTree.node D2M8K2.t12878 (nat_lit 27610118) (nat_lit 3334739211) (nat_lit 0) D2M8K2.t12879 from rfl, totK_node, tot12878, tot12879]
  decide +kernel

theorem arows12875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12875 = true := by
  rw [show D2M8K2.u12875 = KTree.node D2M8K2.t12880 (nat_lit 27611695) (nat_lit 2186808104) (nat_lit 0) D2M8K2.t12881 from rfl, allE_node, rows12880, irow12875, rows12881]
  all_goals rfl

theorem atot12875 : totK PD2M8K2 D2M8K2.u12875 = [0, 0, 155928167669, 786212889053, 728998730486, 110473933382, 1444560764, 0] := by
  rw [show D2M8K2.u12875 = KTree.node D2M8K2.t12880 (nat_lit 27611695) (nat_lit 2186808104) (nat_lit 0) D2M8K2.t12881 from rfl, totK_node, tot12880, tot12881]
  decide +kernel

theorem arows12876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12876 = true := by
  rw [show D2M8K2.u12876 = KTree.node D2M8K2.t12882 (nat_lit 27617414) (nat_lit 3885612275) (nat_lit 0) D2M8K2.t12883 from rfl, allE_node, rows12882, irow12876, rows12883]
  all_goals rfl

theorem atot12876 : totK PD2M8K2 D2M8K2.u12876 = [0, 0, 334422623409, 904832003836, 537021278649, 48577465897, 0, 0] := by
  rw [show D2M8K2.u12876 = KTree.node D2M8K2.t12882 (nat_lit 27617414) (nat_lit 3885612275) (nat_lit 0) D2M8K2.t12883 from rfl, totK_node, tot12882, tot12883]
  decide +kernel

theorem arows12878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12878 = true := by
  rw [show D2M8K2.u12878 = KTree.node D2M8K2.t12884 (nat_lit 27619227) (nat_lit 3724451651) (nat_lit 0) D2M8K2.t12885 from rfl, allE_node, rows12884, irow12878, rows12885]
  all_goals rfl

theorem atot12878 : totK PD2M8K2 D2M8K2.u12878 = [0, 0, 93237485209, 673364671972, 857903723652, 172701267905, 2679002914, 0] := by
  rw [show D2M8K2.u12878 = KTree.node D2M8K2.t12884 (nat_lit 27619227) (nat_lit 3724451651) (nat_lit 0) D2M8K2.t12885 from rfl, totK_node, tot12884, tot12885]
  decide +kernel

theorem arows12879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12879 = true := by
  rw [show D2M8K2.u12879 = KTree.node D2M8K2.t12886 (nat_lit 27869933) (nat_lit 2053572230) (nat_lit 0) D2M8K2.t12887 from rfl, allE_node, rows12886, irow12879, rows12887]
  all_goals rfl

theorem atot12879 : totK PD2M8K2 D2M8K2.u12879 = [0, 347773466219, 853354629924, 373830832833, 109386550362, 90857185904, 7618107313, 0] := by
  rw [show D2M8K2.u12879 = KTree.node D2M8K2.t12886 (nat_lit 27869933) (nat_lit 2053572230) (nat_lit 0) D2M8K2.t12887 from rfl, totK_node, tot12886, tot12887]
  decide +kernel

theorem arows12882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12882 = true := by
  rw [show D2M8K2.u12882 = KTree.node D2M8K2.t12888 (nat_lit 27871180) (nat_lit 3453424231) (nat_lit 0) D2M8K2.t12889 from rfl, allE_node, rows12888, irow12882, rows12889]
  all_goals rfl

theorem atot12882 : totK PD2M8K2 D2M8K2.u12882 = [0, 85371767328, 668610236662, 888953240479, 150808840006, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12882 = KTree.node D2M8K2.t12888 (nat_lit 27871180) (nat_lit 3453424231) (nat_lit 0) D2M8K2.t12889 from rfl, totK_node, tot12888, tot12889]
  decide +kernel

theorem arows12883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12883 = true := by
  rw [show D2M8K2.u12883 = KTree.node D2M8K2.t12890 (nat_lit 27876706) (nat_lit 3920247055) (nat_lit 0) D2M8K2.t12891 from rfl, allE_node, rows12890, irow12883, rows12891]
  all_goals rfl

theorem atot12883 : totK PD2M8K2 D2M8K2.u12883 = [0, 376226297450, 921173071398, 471354050367, 39414343579, 0, 0, 0] := by
  rw [show D2M8K2.u12883 = KTree.node D2M8K2.t12890 (nat_lit 27876706) (nat_lit 3920247055) (nat_lit 0) D2M8K2.t12891 from rfl, totK_node, tot12890, tot12891]
  decide +kernel

theorem arows12885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12885 = true := by
  rw [show D2M8K2.u12885 = KTree.node D2M8K2.t12892 (nat_lit 27878246) (nat_lit 3983169320) (nat_lit 0) D2M8K2.t12893 from rfl, allE_node, rows12892, irow12885, rows12893]
  all_goals rfl

theorem atot12885 : totK PD2M8K2 D2M8K2.u12885 = [0, 47142334795, 519427184869, 913037795614, 278564743262, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12885 = KTree.node D2M8K2.t12892 (nat_lit 27878246) (nat_lit 3983169320) (nat_lit 0) D2M8K2.t12893 from rfl, totK_node, tot12892, tot12893]
  decide +kernel

theorem arows12886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12886 = true := by
  rw [show D2M8K2.u12886 = KTree.node D2M8K2.t12894 (nat_lit 27880639) (nat_lit 2440169442) (nat_lit 0) D2M8K2.t12895 from rfl, allE_node, rows12894, irow12886, rows12895]
  all_goals rfl

theorem atot12886 : totK PD2M8K2 D2M8K2.u12886 = [0, 324899293396, 925042980923, 505424858512, 38166809546, 0, 0, 0] := by
  rw [show D2M8K2.u12886 = KTree.node D2M8K2.t12894 (nat_lit 27880639) (nat_lit 2440169442) (nat_lit 0) D2M8K2.t12895 from rfl, totK_node, tot12894, tot12895]
  decide +kernel

theorem arows12891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12891 = true := by
  rw [show D2M8K2.u12891 = KTree.node D2M8K2.t12896 (nat_lit 27882533) (nat_lit 2176664214) (nat_lit 0) D2M8K2.t12897 from rfl, allE_node, rows12896, irow12891, rows12897]
  all_goals rfl

theorem atot12891 : totK PD2M8K2 D2M8K2.u12891 = [0, 137857439953, 575312491054, 779984519384, 256443219594, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12891 = KTree.node D2M8K2.t12896 (nat_lit 27882533) (nat_lit 2176664214) (nat_lit 0) D2M8K2.t12897 from rfl, totK_node, tot12896, tot12897]
  decide +kernel

theorem arows12892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12892 = true := by
  rw [show D2M8K2.u12892 = KTree.node D2M8K2.t12898 (nat_lit 27884011) (nat_lit 1605046389) (nat_lit 0) D2M8K2.t12899 from rfl, allE_node, rows12898, irow12892, rows12899]
  all_goals rfl

theorem atot12892 : totK PD2M8K2 D2M8K2.u12892 = [0, 273789053441, 842817566642, 589936620903, 75104663898, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12892 = KTree.node D2M8K2.t12898 (nat_lit 27884011) (nat_lit 1605046389) (nat_lit 0) D2M8K2.t12899 from rfl, totK_node, tot12898, tot12899]
  decide +kernel

theorem arows12894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12894 = true := by
  rw [show D2M8K2.u12894 = KTree.node D2M8K2.t12900 (nat_lit 27885980) (nat_lit 3396117572) (nat_lit 0) D2M8K2.t12901 from rfl, allE_node, rows12900, irow12894, rows12901]
  all_goals rfl

theorem atot12894 : totK PD2M8K2 D2M8K2.u12894 = [0, 141545560730, 679214814746, 805323380990, 175718862976, 3884009855, 0, 0] := by
  rw [show D2M8K2.u12894 = KTree.node D2M8K2.t12900 (nat_lit 27885980) (nat_lit 3396117572) (nat_lit 0) D2M8K2.t12901 from rfl, totK_node, tot12900, tot12901]
  decide +kernel

theorem arows12895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12895 = true := by
  rw [show D2M8K2.u12895 = KTree.node D2M8K2.t12902 (nat_lit 27887963) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t12903 from rfl, allE_node, rows12902, irow12895, rows12903]
  all_goals rfl

theorem atot12895 : totK PD2M8K2 D2M8K2.u12895 = [0, 241171574505, 765137896170, 659803107932, 119862985167, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12895 = KTree.node D2M8K2.t12902 (nat_lit 27887963) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t12903 from rfl, totK_node, tot12902, tot12903]
  decide +kernel

theorem arows12898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12898 = true := by
  rw [show D2M8K2.u12898 = KTree.node D2M8K2.t12904 (nat_lit 27889832) (nat_lit 2238482836) (nat_lit 0) D2M8K2.t12905 from rfl, allE_node, rows12904, irow12898, rows12905]
  all_goals rfl

theorem atot12898 : totK PD2M8K2 D2M8K2.u12898 = [0, 0, 408652507060, 969029652417, 381481647852, 20894433220, 0, 0] := by
  rw [show D2M8K2.u12898 = KTree.node D2M8K2.t12904 (nat_lit 27889832) (nat_lit 2238482836) (nat_lit 0) D2M8K2.t12905 from rfl, totK_node, tot12904, tot12905]
  decide +kernel

theorem arows12899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12899 = true := by
  rw [show D2M8K2.u12899 = KTree.node D2M8K2.t12906 (nat_lit 27891373) (nat_lit 1386666610) (nat_lit 0) D2M8K2.t12907 from rfl, allE_node, rows12906, irow12899, rows12907]
  all_goals rfl

theorem atot12899 : totK PD2M8K2 D2M8K2.u12899 = [0, 0, 252249633341, 792342984444, 581682280122, 94973254361, 1369150432, 0] := by
  rw [show D2M8K2.u12899 = KTree.node D2M8K2.t12906 (nat_lit 27891373) (nat_lit 1386666610) (nat_lit 0) D2M8K2.t12907 from rfl, totK_node, tot12906, tot12907]
  decide +kernel

theorem arows12901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12901 = true := by
  rw [show D2M8K2.u12901 = KTree.node D2M8K2.t12908 (nat_lit 27896959) (nat_lit 2158041280) (nat_lit 0) D2M8K2.t12909 from rfl, allE_node, rows12908, irow12901, rows12909]
  all_goals rfl

theorem atot12901 : totK PD2M8K2 D2M8K2.u12901 = [0, 0, 251783225937, 884264266173, 578034721867, 48376169181, 0, 0] := by
  rw [show D2M8K2.u12901 = KTree.node D2M8K2.t12908 (nat_lit 27896959) (nat_lit 2158041280) (nat_lit 0) D2M8K2.t12909 from rfl, totK_node, tot12908, tot12909]
  decide +kernel

theorem arows12902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12902 = true := by
  rw [show D2M8K2.u12902 = KTree.node D2M8K2.t12910 (nat_lit 27898539) (nat_lit 2882628734) (nat_lit 128) D2M8K2.t12911 from rfl, allE_node, rows12910, irow12902, rows12911]
  all_goals rfl

theorem atot12902 : totK PD2M8K2 D2M8K2.u12902 = [0, 0, 360989349889, 922223389918, 440863916024, 28612850475, 0, 0] := by
  rw [show D2M8K2.u12902 = KTree.node D2M8K2.t12910 (nat_lit 27898539) (nat_lit 2882628734) (nat_lit 128) D2M8K2.t12911 from rfl, totK_node, tot12910, tot12911]
  decide +kernel

theorem arows12906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12906 = true := by
  rw [show D2M8K2.u12906 = KTree.node D2M8K2.t12912 (nat_lit 27903887) (nat_lit 2341598122) (nat_lit 128) D2M8K2.t12913 from rfl, allE_node, rows12912, irow12906, rows12913]
  all_goals rfl

theorem atot12906 : totK PD2M8K2 D2M8K2.u12906 = [0, 0, 375549785805, 969903100896, 414962217259, 16122303122, 0, 0] := by
  rw [show D2M8K2.u12906 = KTree.node D2M8K2.t12912 (nat_lit 27903887) (nat_lit 2341598122) (nat_lit 128) D2M8K2.t12913 from rfl, totK_node, tot12912, tot12913]
  decide +kernel

theorem arows12907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12907 = true := by
  rw [show D2M8K2.u12907 = KTree.node D2M8K2.t12914 (nat_lit 27907257) (nat_lit 1687911879) (nat_lit 0) D2M8K2.t12915 from rfl, allE_node, rows12914, irow12907, rows12915]
  all_goals rfl

theorem atot12907 : totK PD2M8K2 D2M8K2.u12907 = [0, 0, 396413197379, 959622421619, 404450625429, 16190983897, 0, 0] := by
  rw [show D2M8K2.u12907 = KTree.node D2M8K2.t12914 (nat_lit 27907257) (nat_lit 1687911879) (nat_lit 0) D2M8K2.t12915 from rfl, totK_node, tot12914, tot12915]
  decide +kernel

theorem arows12909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12909 = true := by
  rw [show D2M8K2.u12909 = KTree.node D2M8K2.t12916 (nat_lit 27914448) (nat_lit 2759477432) (nat_lit 0) D2M8K2.t12917 from rfl, allE_node, rows12916, irow12909, rows12917]
  all_goals rfl

theorem atot12909 : totK PD2M8K2 D2M8K2.u12909 = [0, 193597321667, 632033377720, 735952378885, 253906015035, 12993903218, 0, 0] := by
  rw [show D2M8K2.u12909 = KTree.node D2M8K2.t12916 (nat_lit 27914448) (nat_lit 2759477432) (nat_lit 0) D2M8K2.t12917 from rfl, totK_node, tot12916, tot12917]
  decide +kernel

theorem arows12910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12910 = true := by
  rw [show D2M8K2.u12910 = KTree.node D2M8K2.t12918 (nat_lit 27915601) (nat_lit 1348547155) (nat_lit 0) D2M8K2.t12919 from rfl, allE_node, rows12918, irow12910, rows12919]
  all_goals rfl

theorem atot12910 : totK PD2M8K2 D2M8K2.u12910 = [0, 248948718730, 763412320992, 598496143480, 188774386336, 21400436502, 0, 0] := by
  rw [show D2M8K2.u12910 = KTree.node D2M8K2.t12918 (nat_lit 27915601) (nat_lit 1348547155) (nat_lit 0) D2M8K2.t12919 from rfl, totK_node, tot12918, tot12919]
  decide +kernel

theorem arows12913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12913 = true := by
  rw [show D2M8K2.u12913 = KTree.node D2M8K2.t12920 (nat_lit 27917056) (nat_lit 3720691378) (nat_lit 0) D2M8K2.t12921 from rfl, allE_node, rows12920, irow12913, rows12921]
  all_goals rfl

theorem atot12913 : totK PD2M8K2 D2M8K2.u12913 = [0, 70538324455, 449721141396, 876927627410, 389708838439, 16208961603, 0, 0] := by
  rw [show D2M8K2.u12913 = KTree.node D2M8K2.t12920 (nat_lit 27917056) (nat_lit 3720691378) (nat_lit 0) D2M8K2.t12921 from rfl, totK_node, tot12920, tot12921]
  decide +kernel

theorem arows12914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12914 = true := by
  rw [show D2M8K2.u12914 = KTree.node D2M8K2.t12922 (nat_lit 27918314) (nat_lit 4191348247) (nat_lit 0) D2M8K2.t12923 from rfl, allE_node, rows12922, irow12914, rows12923]
  all_goals rfl

theorem atot12914 : totK PD2M8K2 D2M8K2.u12914 = [0, 354477245975, 931927634548, 503874629038, 36982387124, 0, 0, 0] := by
  rw [show D2M8K2.u12914 = KTree.node D2M8K2.t12922 (nat_lit 27918314) (nat_lit 4191348247) (nat_lit 0) D2M8K2.t12923 from rfl, totK_node, tot12922, tot12923]
  decide +kernel

theorem arows12916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12916 = true := by
  rw [show D2M8K2.u12916 = KTree.node D2M8K2.t12924 (nat_lit 27920002) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t12925 from rfl, allE_node, rows12924, irow12916, rows12925]
  all_goals rfl

theorem atot12916 : totK PD2M8K2 D2M8K2.u12916 = [0, 19810472444, 482455693488, 965110867257, 298655480640, 13036865798, 0, 0] := by
  rw [show D2M8K2.u12916 = KTree.node D2M8K2.t12924 (nat_lit 27920002) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t12925 from rfl, totK_node, tot12924, tot12925]
  decide +kernel

theorem arows12917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12917 = true := by
  rw [show D2M8K2.u12917 = KTree.node D2M8K2.t12926 (nat_lit 27922203) (nat_lit 3748895556) (nat_lit 0) D2M8K2.t12927 from rfl, allE_node, rows12926, irow12917, rows12927]
  all_goals rfl

theorem atot12917 : totK PD2M8K2 D2M8K2.u12917 = [0, 311615555352, 904153821781, 574390603175, 59927736867, 0, 0, 0] := by
  rw [show D2M8K2.u12917 = KTree.node D2M8K2.t12926 (nat_lit 27922203) (nat_lit 3748895556) (nat_lit 0) D2M8K2.t12927 from rfl, totK_node, tot12926, tot12927]
  decide +kernel

theorem arows12924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12924 = true := by
  rw [show D2M8K2.u12924 = KTree.node D2M8K2.t12928 (nat_lit 27924252) (nat_lit 2030951327) (nat_lit 0) D2M8K2.t12929 from rfl, allE_node, rows12928, irow12924, rows12929]
  all_goals rfl

theorem atot12924 : totK PD2M8K2 D2M8K2.u12924 = [0, 156964551489, 654634494145, 785766352020, 209084281032, 9849381256, 0, 0] := by
  rw [show D2M8K2.u12924 = KTree.node D2M8K2.t12928 (nat_lit 27924252) (nat_lit 2030951327) (nat_lit 0) D2M8K2.t12929 from rfl, totK_node, tot12928, tot12929]
  decide +kernel

theorem arows12925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12925 = true := by
  rw [show D2M8K2.u12925 = KTree.node D2M8K2.t12930 (nat_lit 27925660) (nat_lit 3845805815) (nat_lit 0) D2M8K2.t12931 from rfl, allE_node, rows12930, irow12925, rows12931]
  all_goals rfl

theorem atot12925 : totK PD2M8K2 D2M8K2.u12925 = [0, 257302096101, 814108531030, 635677729013, 96740383187, 1096156699, 0, 0] := by
  rw [show D2M8K2.u12925 = KTree.node D2M8K2.t12930 (nat_lit 27925660) (nat_lit 3845805815) (nat_lit 0) D2M8K2.t12931 from rfl, totK_node, tot12930, tot12931]
  decide +kernel

theorem arows12927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12927 = true := by
  rw [show D2M8K2.u12927 = KTree.node D2M8K2.t12932 (nat_lit 27927948) (nat_lit 3589570064) (nat_lit 0) D2M8K2.t12933 from rfl, allE_node, rows12932, irow12927, rows12933]
  all_goals rfl

theorem atot12927 : totK PD2M8K2 D2M8K2.u12927 = [0, 214121091928, 730291754269, 731190931725, 149478874938, 3880716147, 0, 0] := by
  rw [show D2M8K2.u12927 = KTree.node D2M8K2.t12932 (nat_lit 27927948) (nat_lit 3589570064) (nat_lit 0) D2M8K2.t12933 from rfl, totK_node, tot12932, tot12933]
  decide +kernel

theorem arows12928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12928 = true := by
  rw [show D2M8K2.u12928 = KTree.node D2M8K2.t12934 (nat_lit 27929571) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t12935 from rfl, allE_node, rows12934, irow12928, rows12935]
  all_goals rfl

theorem atot12928 : totK PD2M8K2 D2M8K2.u12928 = [0, 172942879662, 749730621499, 751606256798, 132369328133, 1267860612, 0, 0] := by
  rw [show D2M8K2.u12928 = KTree.node D2M8K2.t12934 (nat_lit 27929571) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t12935 from rfl, totK_node, tot12934, tot12935]
  decide +kernel

theorem arows12931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12931 = true := by
  rw [show D2M8K2.u12931 = KTree.node D2M8K2.t12936 (nat_lit 27935162) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t12937 from rfl, allE_node, rows12936, irow12931, rows12937]
  all_goals rfl

theorem atot12931 : totK PD2M8K2 D2M8K2.u12931 = [0, 0, 339607304122, 911830894847, 519503904203, 44066526921, 0, 0] := by
  rw [show D2M8K2.u12931 = KTree.node D2M8K2.t12936 (nat_lit 27935162) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t12937 from rfl, totK_node, tot12936, tot12937]
  decide +kernel

theorem arows12932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12932 = true := by
  rw [show D2M8K2.u12932 = KTree.node D2M8K2.t12938 (nat_lit 27936320) (nat_lit 3295161593) (nat_lit 0) D2M8K2.t12939 from rfl, allE_node, rows12938, irow12932, rows12939]
  all_goals rfl

theorem atot12932 : totK PD2M8K2 D2M8K2.u12932 = [0, 0, 258729704118, 800767125234, 612746472158, 144778227799, 9929822194, 0] := by
  rw [show D2M8K2.u12932 = KTree.node D2M8K2.t12938 (nat_lit 27936320) (nat_lit 3295161593) (nat_lit 0) D2M8K2.t12939 from rfl, totK_node, tot12938, tot12939]
  decide +kernel

theorem arows12934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12934 = true := by
  rw [show D2M8K2.u12934 = KTree.node D2M8K2.t12940 (nat_lit 27937982) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t12941 from rfl, allE_node, rows12940, irow12934, rows12941]
  all_goals rfl

theorem atot12934 : totK PD2M8K2 D2M8K2.u12934 = [0, 0, 160253043472, 679763617448, 756247293696, 213418740140, 5159287072, 0] := by
  rw [show D2M8K2.u12934 = KTree.node D2M8K2.t12940 (nat_lit 27937982) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t12941 from rfl, totK_node, tot12940, tot12941]
  decide +kernel

theorem arows12935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12935 = true := by
  rw [show D2M8K2.u12935 = KTree.node D2M8K2.t12942 (nat_lit 27939658) (nat_lit 3247204777) (nat_lit 0) D2M8K2.t12943 from rfl, allE_node, rows12942, irow12935, rows12943]
  all_goals rfl

theorem atot12935 : totK PD2M8K2 D2M8K2.u12935 = [0, 0, 263174248957, 864875997538, 621195662652, 52516977350, 0, 0] := by
  rw [show D2M8K2.u12935 = KTree.node D2M8K2.t12942 (nat_lit 27939658) (nat_lit 3247204777) (nat_lit 0) D2M8K2.t12943 from rfl, totK_node, tot12942, tot12943]
  decide +kernel

theorem arows12939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12939 = true := by
  rw [show D2M8K2.u12939 = KTree.node D2M8K2.t12944 (nat_lit 27941531) (nat_lit 2896017201) (nat_lit 0) D2M8K2.t12945 from rfl, allE_node, rows12944, irow12939, rows12945]
  all_goals rfl

theorem atot12939 : totK PD2M8K2 D2M8K2.u12939 = [0, 0, 177605389916, 677927868967, 770445444446, 189297854302, 5159868635, 0] := by
  rw [show D2M8K2.u12939 = KTree.node D2M8K2.t12944 (nat_lit 27941531) (nat_lit 2896017201) (nat_lit 0) D2M8K2.t12945 from rfl, totK_node, tot12944, tot12945]
  decide +kernel

theorem arows12940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12940 = true := by
  rw [show D2M8K2.u12940 = KTree.node D2M8K2.t12946 (nat_lit 27945274) (nat_lit 2772686203) (nat_lit 0) D2M8K2.t12947 from rfl, allE_node, rows12946, irow12940, rows12947]
  all_goals rfl

theorem atot12940 : totK PD2M8K2 D2M8K2.u12940 = [0, 0, 377288353811, 921842209523, 481337901326, 39210016326, 0, 0] := by
  rw [show D2M8K2.u12940 = KTree.node D2M8K2.t12946 (nat_lit 27945274) (nat_lit 2772686203) (nat_lit 0) D2M8K2.t12947 from rfl, totK_node, tot12946, tot12947]
  decide +kernel

theorem arows12942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12942 = true := by
  rw [show D2M8K2.u12942 = KTree.node D2M8K2.t12948 (nat_lit 27946482) (nat_lit 3444910579) (nat_lit 0) D2M8K2.t12949 from rfl, allE_node, rows12948, irow12942, rows12949]
  all_goals rfl

theorem atot12942 : totK PD2M8K2 D2M8K2.u12942 = [0, 0, 185079162298, 831138204117, 717237679068, 67352255335, 0, 0] := by
  rw [show D2M8K2.u12942 = KTree.node D2M8K2.t12948 (nat_lit 27946482) (nat_lit 3444910579) (nat_lit 0) D2M8K2.t12949 from rfl, totK_node, tot12948, tot12949]
  decide +kernel

theorem arows12943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12943 = true := by
  rw [show D2M8K2.u12943 = KTree.node D2M8K2.t12950 (nat_lit 27949050) (nat_lit 3904249591) (nat_lit 0) D2M8K2.t12951 from rfl, allE_node, rows12950, irow12943, rows12951]
  all_goals rfl

theorem atot12943 : totK PD2M8K2 D2M8K2.u12943 = [0, 0, 284284854142, 803318850655, 619682583826, 112956707087, 1415142070, 0] := by
  rw [show D2M8K2.u12943 = KTree.node D2M8K2.t12950 (nat_lit 27949050) (nat_lit 3904249591) (nat_lit 0) D2M8K2.t12951 from rfl, totK_node, tot12950, tot12951]
  decide +kernel

theorem arows12946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12946 = true := by
  rw [show D2M8K2.u12946 = KTree.node D2M8K2.t12952 (nat_lit 27952276) (nat_lit 3678569512) (nat_lit 0) D2M8K2.t12953 from rfl, allE_node, rows12952, irow12946, rows12953]
  all_goals rfl

theorem atot12946 : totK PD2M8K2 D2M8K2.u12946 = [0, 243766864263, 704104576386, 601176032637, 227557085611, 16217208973, 0, 0] := by
  rw [show D2M8K2.u12946 = KTree.node D2M8K2.t12952 (nat_lit 27952276) (nat_lit 3678569512) (nat_lit 0) D2M8K2.t12953 from rfl, totK_node, tot12952, tot12953]
  decide +kernel

theorem arows12947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12947 = true := by
  rw [show D2M8K2.u12947 = KTree.node D2M8K2.t12954 (nat_lit 27953856) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t12955 from rfl, allE_node, rows12954, irow12947, rows12955]
  all_goals rfl

theorem atot12947 : totK PD2M8K2 D2M8K2.u12947 = [0, 169434610987, 729668265050, 748465254353, 122920810090, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12947 = KTree.node D2M8K2.t12954 (nat_lit 27953856) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t12955 from rfl, totK_node, tot12954, tot12955]
  decide +kernel

theorem arows12949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12949 = true := by
  rw [show D2M8K2.u12949 = KTree.node D2M8K2.t12956 (nat_lit 27956176) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t12957 from rfl, allE_node, rows12956, irow12949, rows12957]
  all_goals rfl

theorem atot12949 : totK PD2M8K2 D2M8K2.u12949 = [0, 308542917375, 857157283975, 603345166358, 64676639581, 0, 0, 0] := by
  rw [show D2M8K2.u12949 = KTree.node D2M8K2.t12956 (nat_lit 27956176) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t12957 from rfl, totK_node, tot12956, tot12957]
  decide +kernel

theorem arows12950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12950 = true := by
  rw [show D2M8K2.u12950 = KTree.node D2M8K2.t12958 (nat_lit 27957708) (nat_lit 2490883858) (nat_lit 0) D2M8K2.t12959 from rfl, allE_node, rows12958, irow12950, rows12959]
  all_goals rfl

theorem atot12950 : totK PD2M8K2 D2M8K2.u12950 = [0, 111385534382, 608063803725, 767304665608, 296204703215, 25111704080, 0, 0] := by
  rw [show D2M8K2.u12950 = KTree.node D2M8K2.t12958 (nat_lit 27957708) (nat_lit 2490883858) (nat_lit 0) D2M8K2.t12959 from rfl, totK_node, tot12958, tot12959]
  decide +kernel

theorem arows12955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12955 = true := by
  rw [show D2M8K2.u12955 = KTree.node D2M8K2.t12960 (nat_lit 27958971) (nat_lit 3458939806) (nat_lit 0) D2M8K2.t12961 from rfl, allE_node, rows12960, irow12955, rows12961]
  all_goals rfl

theorem atot12955 : totK PD2M8K2 D2M8K2.u12955 = [0, 176559373540, 606693376851, 730232496908, 281567604067, 10780570030, 0, 0] := by
  rw [show D2M8K2.u12955 = KTree.node D2M8K2.t12960 (nat_lit 27958971) (nat_lit 3458939806) (nat_lit 0) D2M8K2.t12961 from rfl, totK_node, tot12960, tot12961]
  decide +kernel

theorem arows12956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12956 = true := by
  rw [show D2M8K2.u12956 = KTree.node D2M8K2.t12962 (nat_lit 27960441) (nat_lit 1902207435) (nat_lit 0) D2M8K2.t12963 from rfl, allE_node, rows12962, irow12956, rows12963]
  all_goals rfl

theorem atot12956 : totK PD2M8K2 D2M8K2.u12956 = [0, 269367214776, 812104288432, 628879708875, 100627262375, 1164319620, 0, 0] := by
  rw [show D2M8K2.u12956 = KTree.node D2M8K2.t12962 (nat_lit 27960441) (nat_lit 1902207435) (nat_lit 0) D2M8K2.t12963 from rfl, totK_node, tot12962, tot12963]
  decide +kernel

theorem arows12958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12958 = true := by
  rw [show D2M8K2.u12958 = KTree.node D2M8K2.t12964 (nat_lit 27962084) (nat_lit 2794102258) (nat_lit 0) D2M8K2.t12965 from rfl, allE_node, rows12964, irow12958, rows12965]
  all_goals rfl

theorem atot12958 : totK PD2M8K2 D2M8K2.u12958 = [0, 138856288286, 630953685673, 789761115791, 224338324585, 11885407614, 0, 0] := by
  rw [show D2M8K2.u12958 = KTree.node D2M8K2.t12964 (nat_lit 27962084) (nat_lit 2794102258) (nat_lit 0) D2M8K2.t12965 from rfl, totK_node, tot12964, tot12965]
  decide +kernel

theorem arows12959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12959 = true := by
  rw [show D2M8K2.u12959 = KTree.node D2M8K2.t12966 (nat_lit 27966902) (nat_lit 3795248189) (nat_lit 0) D2M8K2.t12967 from rfl, allE_node, rows12966, irow12959, rows12967]
  all_goals rfl

theorem atot12959 : totK PD2M8K2 D2M8K2.u12959 = [0, 281381590943, 858355439579, 602305208897, 63564381280, 0, 0, 0] := by
  rw [show D2M8K2.u12959 = KTree.node D2M8K2.t12966 (nat_lit 27966902) (nat_lit 3795248189) (nat_lit 0) D2M8K2.t12967 from rfl, totK_node, tot12966, tot12967]
  decide +kernel

theorem arows12962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12962 = true := by
  rw [show D2M8K2.u12962 = KTree.node D2M8K2.t12968 (nat_lit 27968896) (nat_lit 3579397313) (nat_lit 0) D2M8K2.t12969 from rfl, allE_node, rows12968, irow12962, rows12969]
  all_goals rfl

theorem atot12962 : totK PD2M8K2 D2M8K2.u12962 = [0, 171051348884, 673400891837, 768527085074, 180526693875, 4980514959, 0, 0] := by
  rw [show D2M8K2.u12962 = KTree.node D2M8K2.t12968 (nat_lit 27968896) (nat_lit 3579397313) (nat_lit 0) D2M8K2.t12969 from rfl, totK_node, tot12968, tot12969]
  decide +kernel

theorem arows12963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12963 = true := by
  rw [show D2M8K2.u12963 = KTree.node D2M8K2.t12970 (nat_lit 27970446) (nat_lit 3325932858) (nat_lit 0) D2M8K2.t12971 from rfl, allE_node, rows12970, irow12963, rows12971]
  all_goals rfl

theorem atot12963 : totK PD2M8K2 D2M8K2.u12963 = [0, 232904275417, 775769882807, 669347488902, 108610660108, 1268739303, 0, 0] := by
  rw [show D2M8K2.u12963 = KTree.node D2M8K2.t12970 (nat_lit 27970446) (nat_lit 3325932858) (nat_lit 0) D2M8K2.t12971 from rfl, totK_node, tot12970, tot12971]
  decide +kernel

theorem arows12965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12965 = true := by
  rw [show D2M8K2.u12965 = KTree.node D2M8K2.t12972 (nat_lit 27972576) (nat_lit 3701693887) (nat_lit 0) D2M8K2.t12973 from rfl, allE_node, rows12972, irow12965, rows12973]
  all_goals rfl

theorem atot12965 : totK PD2M8K2 D2M8K2.u12965 = [0, 0, 422325690376, 953791088406, 377330109053, 17650709493, 0, 0] := by
  rw [show D2M8K2.u12965 = KTree.node D2M8K2.t12972 (nat_lit 27972576) (nat_lit 3701693887) (nat_lit 0) D2M8K2.t12973 from rfl, totK_node, tot12972, tot12973]
  decide +kernel

theorem arows12966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12966 = true := by
  rw [show D2M8K2.u12966 = KTree.node D2M8K2.t12974 (nat_lit 27974109) (nat_lit 1565971258) (nat_lit 0) D2M8K2.t12975 from rfl, allE_node, rows12974, irow12966, rows12975]
  all_goals rfl

theorem atot12966 : totK PD2M8K2 D2M8K2.u12966 = [0, 0, 302774284327, 886880797993, 499405189871, 38811442079, 0, 0] := by
  rw [show D2M8K2.u12966 = KTree.node D2M8K2.t12974 (nat_lit 27974109) (nat_lit 1565971258) (nat_lit 0) D2M8K2.t12975 from rfl, totK_node, tot12974, tot12975]
  decide +kernel

theorem arows12970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12970 = true := by
  rw [show D2M8K2.u12970 = KTree.node D2M8K2.t12976 (nat_lit 27976168) (nat_lit 3500279117) (nat_lit 0) D2M8K2.t12977 from rfl, allE_node, rows12976, irow12970, rows12977]
  all_goals rfl

theorem atot12970 : totK PD2M8K2 D2M8K2.u12970 = [0, 0, 182442894580, 760922961993, 725990698313, 107483691854, 1206465782, 0] := by
  rw [show D2M8K2.u12970 = KTree.node D2M8K2.t12976 (nat_lit 27976168) (nat_lit 3500279117) (nat_lit 0) D2M8K2.t12977 from rfl, totK_node, tot12976, tot12977]
  decide +kernel

theorem arows12971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12971 = true := by
  rw [show D2M8K2.u12971 = KTree.node D2M8K2.t12978 (nat_lit 27977835) (nat_lit 3631582253) (nat_lit 0) D2M8K2.t12979 from rfl, allE_node, rows12978, irow12971, rows12979]
  all_goals rfl

theorem atot12971 : totK PD2M8K2 D2M8K2.u12971 = [0, 0, 415236777888, 976644269456, 392498189614, 15720163340, 0, 0] := by
  rw [show D2M8K2.u12971 = KTree.node D2M8K2.t12978 (nat_lit 27977835) (nat_lit 3631582253) (nat_lit 0) D2M8K2.t12979 from rfl, totK_node, tot12978, tot12979]
  decide +kernel

theorem arows12973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12973 = true := by
  rw [show D2M8K2.u12973 = KTree.node D2M8K2.t12980 (nat_lit 27981033) (nat_lit 1918752217) (nat_lit 0) D2M8K2.t12981 from rfl, allE_node, rows12980, irow12973, rows12981]
  all_goals rfl

theorem atot12973 : totK PD2M8K2 D2M8K2.u12973 = [0, 0, 268028359721, 865483633008, 594924309632, 66797411559, 1162935789, 0] := by
  rw [show D2M8K2.u12973 = KTree.node D2M8K2.t12980 (nat_lit 27981033) (nat_lit 1918752217) (nat_lit 0) D2M8K2.t12981 from rfl, totK_node, tot12980, tot12981]
  decide +kernel

theorem arows12974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12974 = true := by
  rw [show D2M8K2.u12974 = KTree.node D2M8K2.t12982 (nat_lit 27982728) (nat_lit 3131227714) (nat_lit 0) D2M8K2.t12983 from rfl, allE_node, rows12982, irow12974, rows12983]
  all_goals rfl

theorem atot12974 : totK PD2M8K2 D2M8K2.u12974 = [0, 0, 103178256370, 589187386866, 794948336067, 239076123090, 11853261585, 0] := by
  rw [show D2M8K2.u12974 = KTree.node D2M8K2.t12982 (nat_lit 27982728) (nat_lit 3131227714) (nat_lit 0) D2M8K2.t12983 from rfl, totK_node, tot12982, tot12983]
  decide +kernel

theorem arows12977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12977 = true := by
  rw [show D2M8K2.u12977 = KTree.node D2M8K2.t12984 (nat_lit 27987595) (nat_lit 1717046645) (nat_lit 0) D2M8K2.t12985 from rfl, allE_node, rows12984, irow12977, rows12985]
  all_goals rfl

theorem atot12977 : totK PD2M8K2 D2M8K2.u12977 = [0, 0, 314709741183, 900945826733, 526159367680, 38371803404, 0, 0] := by
  rw [show D2M8K2.u12977 = KTree.node D2M8K2.t12984 (nat_lit 27987595) (nat_lit 1717046645) (nat_lit 0) D2M8K2.t12985 from rfl, totK_node, tot12984, tot12985]
  decide +kernel

theorem arows12978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12978 = true := by
  rw [show D2M8K2.u12978 = KTree.node D2M8K2.t12986 (nat_lit 27989676) (nat_lit 3141727451) (nat_lit 0) D2M8K2.t12987 from rfl, allE_node, rows12986, irow12978, rows12987]
  all_goals rfl

theorem atot12978 : totK PD2M8K2 D2M8K2.u12978 = [0, 0, 170308802673, 705181671255, 706525654659, 145372499749, 4574395652, 0] := by
  rw [show D2M8K2.u12978 = KTree.node D2M8K2.t12986 (nat_lit 27989676) (nat_lit 3141727451) (nat_lit 0) D2M8K2.t12987 from rfl, totK_node, tot12986, tot12987]
  decide +kernel

theorem arows12980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12980 = true := by
  rw [show D2M8K2.u12980 = KTree.node D2M8K2.t12988 (nat_lit 27991633) (nat_lit 1484812046) (nat_lit 0) D2M8K2.t12989 from rfl, allE_node, rows12988, irow12980, rows12989]
  all_goals rfl

theorem atot12980 : totK PD2M8K2 D2M8K2.u12980 = [0, 145194857232, 542202459137, 740492427322, 353976793981, 21651140660, 0, 0] := by
  rw [show D2M8K2.u12980 = KTree.node D2M8K2.t12988 (nat_lit 27991633) (nat_lit 1484812046) (nat_lit 0) D2M8K2.t12989 from rfl, totK_node, tot12988, tot12989]
  decide +kernel

theorem arows12981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12981 = true := by
  rw [show D2M8K2.u12981 = KTree.node D2M8K2.t12990 (nat_lit 28036327) (nat_lit 2364124358) (nat_lit 0) D2M8K2.t12991 from rfl, allE_node, rows12990, irow12981, rows12991]
  all_goals rfl

theorem atot12981 : totK PD2M8K2 D2M8K2.u12981 = [0, 258139383882, 811322187556, 592628730711, 88979451878, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12981 = KTree.node D2M8K2.t12990 (nat_lit 28036327) (nat_lit 2364124358) (nat_lit 0) D2M8K2.t12991 from rfl, totK_node, tot12990, tot12991]
  decide +kernel

theorem arows12987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12987 = true := by
  rw [show D2M8K2.u12987 = KTree.node D2M8K2.t12992 (nat_lit 28038374) (nat_lit 2696462439) (nat_lit 0) D2M8K2.t12993 from rfl, allE_node, rows12992, irow12987, rows12993]
  all_goals rfl

theorem atot12987 : totK PD2M8K2 D2M8K2.u12987 = [0, 180520054459, 757451241260, 779559455983, 105163406379, 0, 0, 0] := by
  rw [show D2M8K2.u12987 = KTree.node D2M8K2.t12992 (nat_lit 28038374) (nat_lit 2696462439) (nat_lit 0) D2M8K2.t12993 from rfl, totK_node, tot12992, tot12993]
  decide +kernel

theorem arows12988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12988 = true := by
  rw [show D2M8K2.u12988 = KTree.node D2M8K2.t12994 (nat_lit 28040008) (nat_lit 3813729919) (nat_lit 0) D2M8K2.t12995 from rfl, allE_node, rows12994, irow12988, rows12995]
  all_goals rfl

theorem atot12988 : totK PD2M8K2 D2M8K2.u12988 = [0, 237807220017, 758719171321, 612688746204, 189596045131, 21156593246, 0, 0] := by
  rw [show D2M8K2.u12988 = KTree.node D2M8K2.t12994 (nat_lit 28040008) (nat_lit 3813729919) (nat_lit 0) D2M8K2.t12995 from rfl, totK_node, tot12994, tot12995]
  decide +kernel

theorem arows12990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12990 = true := by
  rw [show D2M8K2.u12990 = KTree.node D2M8K2.t12996 (nat_lit 28041493) (nat_lit 1140778677) (nat_lit 0) D2M8K2.t12997 from rfl, allE_node, rows12996, irow12990, rows12997]
  all_goals rfl

theorem atot12990 : totK PD2M8K2 D2M8K2.u12990 = [0, 84808482832, 469510674371, 847965540981, 381410263444, 14828424711, 0, 0] := by
  rw [show D2M8K2.u12990 = KTree.node D2M8K2.t12996 (nat_lit 28041493) (nat_lit 1140778677) (nat_lit 0) D2M8K2.t12997 from rfl, totK_node, tot12996, tot12997]
  decide +kernel

theorem arows12991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12991 = true := by
  rw [show D2M8K2.u12991 = KTree.node D2M8K2.t12998 (nat_lit 28042763) (nat_lit 2407717699) (nat_lit 0) D2M8K2.t12999 from rfl, allE_node, rows12998, irow12991, rows12999]
  all_goals rfl

theorem atot12991 : totK PD2M8K2 D2M8K2.u12991 = [0, 340904620270, 918750865190, 518032070537, 44459917402, 0, 0, 0] := by
  rw [show D2M8K2.u12991 = KTree.node D2M8K2.t12998 (nat_lit 28042763) (nat_lit 2407717699) (nat_lit 0) D2M8K2.t12999 from rfl, totK_node, tot12998, tot12999]
  decide +kernel

theorem arows12994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12994 = true := by
  rw [show D2M8K2.u12994 = KTree.node D2M8K2.t13000 (nat_lit 28044461) (nat_lit 1939309492) (nat_lit 0) D2M8K2.t13001 from rfl, allE_node, rows13000, irow12994, rows13001]
  all_goals rfl

theorem atot12994 : totK PD2M8K2 D2M8K2.u12994 = [0, 67923955290, 501227062871, 907131737524, 289508424651, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12994 = KTree.node D2M8K2.t13000 (nat_lit 28044461) (nat_lit 1939309492) (nat_lit 0) D2M8K2.t13001 from rfl, totK_node, tot13000, tot13001]
  decide +kernel

theorem arows12995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12995 = true := by
  rw [show D2M8K2.u12995 = KTree.node D2M8K2.t13002 (nat_lit 28046453) (nat_lit 1085394923) (nat_lit 0) D2M8K2.t13003 from rfl, allE_node, rows13002, irow12995, rows13003]
  all_goals rfl

theorem atot12995 : totK PD2M8K2 D2M8K2.u12995 = [0, 275426879934, 864944317748, 582157308865, 71871277227, 1198073392, 0, 0] := by
  rw [show D2M8K2.u12995 = KTree.node D2M8K2.t13002 (nat_lit 28046453) (nat_lit 1085394923) (nat_lit 0) D2M8K2.t13003 from rfl, totK_node, tot13002, tot13003]
  decide +kernel

theorem arows12997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12997 = true := by
  rw [show D2M8K2.u12997 = KTree.node D2M8K2.t13004 (nat_lit 28048417) (nat_lit 1469764860) (nat_lit 0) D2M8K2.t13005 from rfl, allE_node, rows13004, irow12997, rows13005]
  all_goals rfl

theorem atot12997 : totK PD2M8K2 D2M8K2.u12997 = [0, 174534810133, 639271471628, 741067353509, 231493968736, 12052611869, 0, 0] := by
  rw [show D2M8K2.u12997 = KTree.node D2M8K2.t13004 (nat_lit 28048417) (nat_lit 1469764860) (nat_lit 0) D2M8K2.t13005 from rfl, totK_node, tot13004, tot13005]
  decide +kernel

theorem arows12998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12998 = true := by
  rw [show D2M8K2.u12998 = KTree.node D2M8K2.t13006 (nat_lit 28049933) (nat_lit 1634528915) (nat_lit 0) D2M8K2.t13007 from rfl, allE_node, rows13006, irow12998, rows13007]
  all_goals rfl

theorem atot12998 : totK PD2M8K2 D2M8K2.u12998 = [0, 264859864349, 824619126931, 628973318548, 82721080887, 1096505104, 0, 0] := by
  rw [show D2M8K2.u12998 = KTree.node D2M8K2.t13006 (nat_lit 28049933) (nat_lit 1634528915) (nat_lit 0) D2M8K2.t13007 from rfl, totK_node, tot13006, tot13007]
  decide +kernel

theorem arows13002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13002 = true := by
  rw [show D2M8K2.u13002 = KTree.node D2M8K2.t13008 (nat_lit 28051866) (nat_lit 3677914707) (nat_lit 0) D2M8K2.t13009 from rfl, allE_node, rows13008, irow13002, rows13009]
  all_goals rfl

theorem atot13002 : totK PD2M8K2 D2M8K2.u13002 = [0, 0, 525241228234, 1023323428781, 264178561607, 5253830308, 0, 0] := by
  rw [show D2M8K2.u13002 = KTree.node D2M8K2.t13008 (nat_lit 28051866) (nat_lit 3677914707) (nat_lit 0) D2M8K2.t13009 from rfl, totK_node, tot13008, tot13009]
  decide +kernel

theorem arows13003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13003 = true := by
  rw [show D2M8K2.u13003 = KTree.node D2M8K2.t13010 (nat_lit 28057177) (nat_lit 1413477595) (nat_lit 0) D2M8K2.t13011 from rfl, allE_node, rows13010, irow13003, rows13011]
  all_goals rfl

theorem atot13003 : totK PD2M8K2 D2M8K2.u13003 = [0, 0, 229982905472, 798118336809, 595605893984, 82847412909, 1138244013, 0] := by
  rw [show D2M8K2.u13003 = KTree.node D2M8K2.t13010 (nat_lit 28057177) (nat_lit 1413477595) (nat_lit 0) D2M8K2.t13011 from rfl, totK_node, tot13010, tot13011]
  decide +kernel

theorem arows13005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13005 = true := by
  rw [show D2M8K2.u13005 = KTree.node D2M8K2.t13012 (nat_lit 28059754) (nat_lit 3790371784) (nat_lit 0) D2M8K2.t13013 from rfl, allE_node, rows13012, irow13005, rows13013]
  all_goals rfl

theorem atot13005 : totK PD2M8K2 D2M8K2.u13005 = [0, 0, 260562340739, 873246257099, 605969444959, 59205343999, 0, 0] := by
  rw [show D2M8K2.u13005 = KTree.node D2M8K2.t13012 (nat_lit 28059754) (nat_lit 3790371784) (nat_lit 0) D2M8K2.t13013 from rfl, totK_node, tot13012, tot13013]
  decide +kernel

theorem arows13006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13006 = true := by
  rw [show D2M8K2.u13006 = KTree.node D2M8K2.t13014 (nat_lit 28062799) (nat_lit 2188597588) (nat_lit 0) D2M8K2.t13015 from rfl, allE_node, rows13014, irow13006, rows13015]
  all_goals rfl

theorem atot13006 : totK PD2M8K2 D2M8K2.u13006 = [0, 0, 403429756924, 970665093827, 422565901785, 19083095162, 0, 0] := by
  rw [show D2M8K2.u13006 = KTree.node D2M8K2.t13014 (nat_lit 28062799) (nat_lit 2188597588) (nat_lit 0) D2M8K2.t13015 from rfl, totK_node, tot13014, tot13015]
  decide +kernel

theorem arows13009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13009 = true := by
  rw [show D2M8K2.u13009 = KTree.node D2M8K2.t13016 (nat_lit 28064310) (nat_lit 2400928313) (nat_lit 0) D2M8K2.t13017 from rfl, allE_node, rows13016, irow13009, rows13017]
  all_goals rfl

theorem atot13009 : totK PD2M8K2 D2M8K2.u13009 = [0, 0, 343140828338, 947654827091, 467595963757, 25790587952, 0, 0] := by
  rw [show D2M8K2.u13009 = KTree.node D2M8K2.t13016 (nat_lit 28064310) (nat_lit 2400928313) (nat_lit 0) D2M8K2.t13017 from rfl, totK_node, tot13016, tot13017]
  decide +kernel

theorem arows13010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13010 = true := by
  rw [show D2M8K2.u13010 = KTree.node D2M8K2.t13018 (nat_lit 28069642) (nat_lit 3530658062) (nat_lit 0) D2M8K2.t13019 from rfl, allE_node, rows13018, irow13010, rows13019]
  all_goals rfl

theorem atot13010 : totK PD2M8K2 D2M8K2.u13010 = [0, 0, 385562548396, 941424748051, 442952435809, 29689546679, 0, 0] := by
  rw [show D2M8K2.u13010 = KTree.node D2M8K2.t13018 (nat_lit 28069642) (nat_lit 3530658062) (nat_lit 0) D2M8K2.t13019 from rfl, totK_node, tot13018, tot13019]
  decide +kernel

theorem arows13012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13012 = true := by
  rw [show D2M8K2.u13012 = KTree.node D2M8K2.t13020 (nat_lit 28070842) (nat_lit 3029288444) (nat_lit 0) D2M8K2.t13021 from rfl, allE_node, rows13020, irow13012, rows13021]
  all_goals rfl

theorem atot13012 : totK PD2M8K2 D2M8K2.u13012 = [0, 0, 227800770674, 807610409172, 629032454107, 90385737345, 1095107716, 0] := by
  rw [show D2M8K2.u13012 = KTree.node D2M8K2.t13020 (nat_lit 28070842) (nat_lit 3029288444) (nat_lit 0) D2M8K2.t13021 from rfl, totK_node, tot13020, tot13021]
  decide +kernel

theorem arows13013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13013 = true := by
  rw [show D2M8K2.u13013 = KTree.node D2M8K2.t13022 (nat_lit 28076608) (nat_lit 3732717001) (nat_lit 0) D2M8K2.t13023 from rfl, allE_node, rows13022, irow13013, rows13023]
  all_goals rfl

theorem atot13013 : totK PD2M8K2 D2M8K2.u13013 = [0, 234545227448, 527213311049, 445177076196, 441384825353, 118532399241, 3882006667, 0] := by
  rw [show D2M8K2.u13013 = KTree.node D2M8K2.t13022 (nat_lit 28076608) (nat_lit 3732717001) (nat_lit 0) D2M8K2.t13023 from rfl, totK_node, tot13022, tot13023]
  decide +kernel

theorem arows13018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13018 = true := by
  rw [show D2M8K2.u13018 = KTree.node D2M8K2.t13024 (nat_lit 28078214) (nat_lit 2390351636) (nat_lit 0) D2M8K2.t13025 from rfl, allE_node, rows13024, irow13018, rows13025]
  all_goals rfl

theorem atot13018 : totK PD2M8K2 D2M8K2.u13018 = [0, 161764526861, 737734010763, 754600118698, 120745517857, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13018 = KTree.node D2M8K2.t13024 (nat_lit 28078214) (nat_lit 2390351636) (nat_lit 0) D2M8K2.t13025 from rfl, totK_node, tot13024, tot13025]
  decide +kernel

theorem arows13019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13019 = true := by
  rw [show D2M8K2.u13019 = KTree.node D2M8K2.t13026 (nat_lit 28080584) (nat_lit 2841016251) (nat_lit 0) D2M8K2.t13027 from rfl, allE_node, rows13026, irow13019, rows13027]
  all_goals rfl

theorem atot13019 : totK PD2M8K2 D2M8K2.u13019 = [0, 301386758286, 856307959279, 616341559764, 63634135253, 0, 0, 0] := by
  rw [show D2M8K2.u13019 = KTree.node D2M8K2.t13026 (nat_lit 28080584) (nat_lit 2841016251) (nat_lit 0) D2M8K2.t13027 from rfl, totK_node, tot13026, tot13027]
  decide +kernel

theorem arows13021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13021 = true := by
  rw [show D2M8K2.u13021 = KTree.node D2M8K2.t13028 (nat_lit 28082187) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t13029 from rfl, allE_node, rows13028, irow13021, rows13029]
  all_goals rfl

theorem atot13021 : totK PD2M8K2 D2M8K2.u13021 = [0, 106842647937, 577713677170, 793017111274, 318463974723, 23828799420, 0, 0] := by
  rw [show D2M8K2.u13021 = KTree.node D2M8K2.t13028 (nat_lit 28082187) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t13029 from rfl, totK_node, tot13028, tot13029]
  decide +kernel

theorem arows13022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13022 = true := by
  rw [show D2M8K2.u13022 = KTree.node D2M8K2.t13030 (nat_lit 28083525) (nat_lit 1500051849) (nat_lit 0) D2M8K2.t13031 from rfl, allE_node, rows13030, irow13022, rows13031]
  all_goals rfl

theorem atot13022 : totK PD2M8K2 D2M8K2.u13022 = [0, 220545319089, 662674721797, 684151349650, 234899692008, 9749326875, 0, 0] := by
  rw [show D2M8K2.u13022 = KTree.node D2M8K2.t13030 (nat_lit 28083525) (nat_lit 1500051849) (nat_lit 0) D2M8K2.t13031 from rfl, totK_node, tot13030, tot13031]
  decide +kernel

theorem arows13025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13025 = true := by
  rw [show D2M8K2.u13025 = KTree.node D2M8K2.t13032 (nat_lit 28085028) (nat_lit 3268934062) (nat_lit 0) D2M8K2.t13033 from rfl, allE_node, rows13032, irow13025, rows13033]
  all_goals rfl

theorem atot13025 : totK PD2M8K2 D2M8K2.u13025 = [0, 204923444032, 775586315026, 707397165602, 112487891059, 1164319620, 0, 0] := by
  rw [show D2M8K2.u13025 = KTree.node D2M8K2.t13032 (nat_lit 28085028) (nat_lit 3268934062) (nat_lit 0) D2M8K2.t13033 from rfl, totK_node, tot13032, tot13033]
  decide +kernel

theorem arows13026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13026 = true := by
  rw [show D2M8K2.u13026 = KTree.node D2M8K2.t13034 (nat_lit 28086709) (nat_lit 1150281795) (nat_lit 0) D2M8K2.t13035 from rfl, allE_node, rows13034, irow13026, rows13035]
  all_goals rfl

theorem atot13026 : totK PD2M8K2 D2M8K2.u13026 = [0, 173197134760, 657870437013, 729811720583, 217726576982, 11879463720, 0, 0] := by
  rw [show D2M8K2.u13026 = KTree.node D2M8K2.t13034 (nat_lit 28086709) (nat_lit 1150281795) (nat_lit 0) D2M8K2.t13035 from rfl, totK_node, tot13034, tot13035]
  decide +kernel

theorem arows13028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13028 = true := by
  rw [show D2M8K2.u13028 = KTree.node D2M8K2.t13036 (nat_lit 28095299) (nat_lit 2905336933) (nat_lit 0) D2M8K2.t13037 from rfl, allE_node, rows13036, irow13028, rows13037]
  all_goals rfl

theorem atot13028 : totK PD2M8K2 D2M8K2.u13028 = [0, 254786597985, 790335607777, 652803883444, 115282014227, 1268739303, 0, 0] := by
  rw [show D2M8K2.u13028 = KTree.node D2M8K2.t13036 (nat_lit 28095299) (nat_lit 2905336933) (nat_lit 0) D2M8K2.t13037 from rfl, totK_node, tot13036, tot13037]
  decide +kernel

theorem arows13029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13029 = true := by
  rw [show D2M8K2.u13029 = KTree.node D2M8K2.t13038 (nat_lit 28096998) (nat_lit 3754526149) (nat_lit 0) D2M8K2.t13039 from rfl, allE_node, rows13038, irow13029, rows13039]
  all_goals rfl

theorem atot13029 : totK PD2M8K2 D2M8K2.u13029 = [0, 0, 404045152740, 951315340227, 398641915522, 22149860293, 0, 0] := by
  rw [show D2M8K2.u13029 = KTree.node D2M8K2.t13038 (nat_lit 28096998) (nat_lit 3754526149) (nat_lit 0) D2M8K2.t13039 from rfl, totK_node, tot13038, tot13039]
  decide +kernel

theorem arows13033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13033 = true := by
  rw [show D2M8K2.u13033 = KTree.node D2M8K2.t13040 (nat_lit 28098598) (nat_lit 1260775280) (nat_lit 0) D2M8K2.t13041 from rfl, allE_node, rows13040, irow13033, rows13041]
  all_goals rfl

theorem atot13033 : totK PD2M8K2 D2M8K2.u13033 = [0, 0, 287880903054, 853169689133, 538770687112, 66587724526, 1310285577, 0] := by
  rw [show D2M8K2.u13033 = KTree.node D2M8K2.t13040 (nat_lit 28098598) (nat_lit 1260775280) (nat_lit 0) D2M8K2.t13041 from rfl, totK_node, tot13040, tot13041]
  decide +kernel

theorem arows13034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13034 = true := by
  rw [show D2M8K2.u13034 = KTree.node D2M8K2.t13042 (nat_lit 28101136) (nat_lit 3303686054) (nat_lit 0) D2M8K2.t13043 from rfl, allE_node, rows13042, irow13034, rows13043]
  all_goals rfl

theorem atot13034 : totK PD2M8K2 D2M8K2.u13034 = [0, 0, 249466716547, 845963041719, 661177058024, 55586324095, 0, 0] := by
  rw [show D2M8K2.u13034 = KTree.node D2M8K2.t13042 (nat_lit 28101136) (nat_lit 3303686054) (nat_lit 0) D2M8K2.t13043 from rfl, totK_node, tot13042, tot13043]
  decide +kernel

theorem arows13036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13036 = true := by
  rw [show D2M8K2.u13036 = KTree.node D2M8K2.t13044 (nat_lit 28102451) (nat_lit 2976141119) (nat_lit 0) D2M8K2.t13045 from rfl, allE_node, rows13044, irow13036, rows13045]
  all_goals rfl

theorem atot13036 : totK PD2M8K2 D2M8K2.u13036 = [0, 0, 346612191744, 936692276964, 498850053484, 34053254439, 0, 0] := by
  rw [show D2M8K2.u13036 = KTree.node D2M8K2.t13044 (nat_lit 28102451) (nat_lit 2976141119) (nat_lit 0) D2M8K2.t13045 from rfl, totK_node, tot13044, tot13045]
  decide +kernel

theorem arows13037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13037 = true := by
  rw [show D2M8K2.u13037 = KTree.node D2M8K2.t13046 (nat_lit 28105694) (nat_lit 3871483797) (nat_lit 0) D2M8K2.t13047 from rfl, allE_node, rows13046, irow13037, rows13047]
  all_goals rfl

theorem atot13037 : totK PD2M8K2 D2M8K2.u13037 = [0, 0, 234492525279, 821051206425, 640387550642, 82120135423, 1075657031, 0] := by
  rw [show D2M8K2.u13037 = KTree.node D2M8K2.t13046 (nat_lit 28105694) (nat_lit 3871483797) (nat_lit 0) D2M8K2.t13047 from rfl, totK_node, tot13046, tot13047]
  decide +kernel

theorem arows13040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13040 = true := by
  rw [show D2M8K2.u13040 = KTree.node D2M8K2.t13048 (nat_lit 28114680) (nat_lit 3631534234) (nat_lit 0) D2M8K2.t13049 from rfl, allE_node, rows13048, irow13040, rows13049]
  all_goals rfl

theorem atot13040 : totK PD2M8K2 D2M8K2.u13040 = [0, 0, 260689589179, 774855604786, 625187863727, 119911014041, 3804183361, 0] := by
  rw [show D2M8K2.u13040 = KTree.node D2M8K2.t13048 (nat_lit 28114680) (nat_lit 3631534234) (nat_lit 0) D2M8K2.t13049 from rfl, totK_node, tot13048, tot13049]
  decide +kernel

theorem arows13041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13041 = true := by
  rw [show D2M8K2.u13041 = KTree.node D2M8K2.t13050 (nat_lit 28116201) (nat_lit 1135712977) (nat_lit 512) D2M8K2.t13051 from rfl, allE_node, rows13050, irow13041, rows13051]
  all_goals rfl

theorem atot13041 : totK PD2M8K2 D2M8K2.u13041 = [0, 173576733255, 587404144052, 693585547390, 327088142257, 23220082334, 0, 0] := by
  rw [show D2M8K2.u13041 = KTree.node D2M8K2.t13050 (nat_lit 28116201) (nat_lit 1135712977) (nat_lit 512) D2M8K2.t13051 from rfl, totK_node, tot13050, tot13051]
  decide +kernel

theorem arows13043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13043 = true := by
  rw [show D2M8K2.u13043 = KTree.node D2M8K2.t13052 (nat_lit 28368292) (nat_lit 3764267211) (nat_lit 0) D2M8K2.t13053 from rfl, allE_node, rows13052, irow13043, rows13053]
  all_goals rfl

theorem atot13043 : totK PD2M8K2 D2M8K2.u13043 = [0, 259588481021, 795885482783, 626746232786, 104871526412, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13043 = KTree.node D2M8K2.t13052 (nat_lit 28368292) (nat_lit 3764267211) (nat_lit 0) D2M8K2.t13053 from rfl, totK_node, tot13052, tot13053]
  decide +kernel

theorem arows13044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13044 = true := by
  rw [show D2M8K2.u13044 = KTree.node D2M8K2.t13054 (nat_lit 28373776) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t13055 from rfl, allE_node, rows13054, irow13044, rows13055]
  all_goals rfl

theorem atot13044 : totK PD2M8K2 D2M8K2.u13044 = [0, 220558954604, 810991588803, 692211157614, 75137295688, 0, 0, 0] := by
  rw [show D2M8K2.u13044 = KTree.node D2M8K2.t13054 (nat_lit 28373776) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t13055 from rfl, totK_node, tot13054, tot13055]
  decide +kernel

theorem arows13052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13052 = true := by
  rw [show D2M8K2.u13052 = KTree.node D2M8K2.t13056 (nat_lit 28375712) (nat_lit 3206446359) (nat_lit 0) D2M8K2.t13057 from rfl, allE_node, rows13056, irow13052, rows13057]
  all_goals rfl

theorem atot13052 : totK PD2M8K2 D2M8K2.u13052 = [0, 101069471148, 596689323234, 795204544423, 241876256705, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13052 = KTree.node D2M8K2.t13056 (nat_lit 28375712) (nat_lit 3206446359) (nat_lit 0) D2M8K2.t13057 from rfl, totK_node, tot13056, tot13057]
  decide +kernel

theorem arows13053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13053 = true := by
  rw [show D2M8K2.u13053 = KTree.node D2M8K2.t13058 (nat_lit 28377771) (nat_lit 3637240426) (nat_lit 0) D2M8K2.t13059 from rfl, allE_node, rows13058, irow13053, rows13059]
  all_goals rfl

theorem atot13053 : totK PD2M8K2 D2M8K2.u13053 = [0, 338327029539, 914896584655, 518034969167, 43681929192, 0, 0, 0] := by
  rw [show D2M8K2.u13053 = KTree.node D2M8K2.t13058 (nat_lit 28377771) (nat_lit 3637240426) (nat_lit 0) D2M8K2.t13059 from rfl, totK_node, tot13058, tot13059]
  decide +kernel

theorem arows13055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13055 = true := by
  rw [show D2M8K2.u13055 = KTree.node D2M8K2.t13060 (nat_lit 28379311) (nat_lit 2428327644) (nat_lit 0) D2M8K2.t13061 from rfl, allE_node, rows13060, irow13055, rows13061]
  all_goals rfl

theorem atot13055 : totK PD2M8K2 D2M8K2.u13055 = [0, 85228556775, 554808397479, 866950066052, 257390465855, 10680993762, 0, 0] := by
  rw [show D2M8K2.u13055 = KTree.node D2M8K2.t13060 (nat_lit 28379311) (nat_lit 2428327644) (nat_lit 0) D2M8K2.t13061 from rfl, totK_node, tot13060, tot13061]
  decide +kernel

theorem arows13056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13056 = true := by
  rw [show D2M8K2.u13056 = KTree.node D2M8K2.t13062 (nat_lit 28381077) (nat_lit 1731954956) (nat_lit 0) D2M8K2.t13063 from rfl, allE_node, rows13062, irow13056, rows13063]
  all_goals rfl

theorem atot13056 : totK PD2M8K2 D2M8K2.u13056 = [0, 320833236977, 847612369622, 536371841541, 83672129596, 2569691499, 0, 0] := by
  rw [show D2M8K2.u13056 = KTree.node D2M8K2.t13062 (nat_lit 28381077) (nat_lit 1731954956) (nat_lit 0) D2M8K2.t13063 from rfl, totK_node, tot13062, tot13063]
  decide +kernel

theorem arows13059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13059 = true := by
  rw [show D2M8K2.u13059 = KTree.node D2M8K2.t13064 (nat_lit 28382665) (nat_lit 1366524599) (nat_lit 0) D2M8K2.t13065 from rfl, allE_node, rows13064, irow13059, rows13065]
  all_goals rfl

theorem atot13059 : totK PD2M8K2 D2M8K2.u13059 = [0, 90840904916, 687901891073, 872672117993, 144479869635, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13059 = KTree.node D2M8K2.t13064 (nat_lit 28382665) (nat_lit 1366524599) (nat_lit 0) D2M8K2.t13065 from rfl, totK_node, tot13064, tot13065]
  decide +kernel

theorem arows13060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13060 = true := by
  rw [show D2M8K2.u13060 = KTree.node D2M8K2.t13066 (nat_lit 28384720) (nat_lit 3414140836) (nat_lit 0) D2M8K2.t13067 from rfl, allE_node, rows13066, irow13060, rows13067]
  all_goals rfl

theorem atot13060 : totK PD2M8K2 D2M8K2.u13060 = [0, 363101264539, 848883245344, 476588433380, 98560718352, 3884009855, 0, 0] := by
  rw [show D2M8K2.u13060 = KTree.node D2M8K2.t13066 (nat_lit 28384720) (nat_lit 3414140836) (nat_lit 0) D2M8K2.t13067 from rfl, totK_node, tot13066, tot13067]
  decide +kernel

theorem arows13062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13062 = true := by
  rw [show D2M8K2.u13062 = KTree.node D2M8K2.t13068 (nat_lit 28386493) (nat_lit 1217259329) (nat_lit 0) D2M8K2.t13069 from rfl, allE_node, rows13068, irow13062, rows13069]
  all_goals rfl

theorem atot13062 : totK PD2M8K2 D2M8K2.u13062 = [0, 19692840307, 507423891477, 954681253908, 287622468731, 8771088775, 0, 0] := by
  rw [show D2M8K2.u13062 = KTree.node D2M8K2.t13068 (nat_lit 28386493) (nat_lit 1217259329) (nat_lit 0) D2M8K2.t13069 from rfl, totK_node, tot13068, tot13069]
  decide +kernel

theorem arows13063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13063 = true := by
  rw [show D2M8K2.u13063 = KTree.node D2M8K2.t13070 (nat_lit 28388468) (nat_lit 3218310378) (nat_lit 0) D2M8K2.t13071 from rfl, allE_node, rows13070, irow13063, rows13071]
  all_goals rfl

theorem atot13063 : totK PD2M8K2 D2M8K2.u13063 = [0, 0, 381151514692, 929714556417, 411708378346, 27061787355, 0, 0] := by
  rw [show D2M8K2.u13063 = KTree.node D2M8K2.t13070 (nat_lit 28388468) (nat_lit 3218310378) (nat_lit 0) D2M8K2.t13071 from rfl, totK_node, tot13070, tot13071]
  decide +kernel

theorem arows13067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13067 = true := by
  rw [show D2M8K2.u13067 = KTree.node D2M8K2.t13072 (nat_lit 28390014) (nat_lit 2328123959) (nat_lit 0) D2M8K2.t13073 from rfl, allE_node, rows13072, irow13067, rows13073]
  all_goals rfl

theorem atot13067 : totK PD2M8K2 D2M8K2.u13067 = [0, 0, 134110583657, 734107092111, 738370346693, 121997866151, 1369150432, 0] := by
  rw [show D2M8K2.u13067 = KTree.node D2M8K2.t13072 (nat_lit 28390014) (nat_lit 2328123959) (nat_lit 0) D2M8K2.t13073 from rfl, totK_node, tot13072, tot13073]
  decide +kernel

theorem arows13068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13068 = true := by
  rw [show D2M8K2.u13068 = KTree.node D2M8K2.t13074 (nat_lit 28395888) (nat_lit 3372027654) (nat_lit 0) D2M8K2.t13075 from rfl, allE_node, rows13074, irow13068, rows13075]
  all_goals rfl

theorem atot13068 : totK PD2M8K2 D2M8K2.u13068 = [0, 0, 380033306828, 974557112309, 407248403481, 14821550631, 0, 0] := by
  rw [show D2M8K2.u13068 = KTree.node D2M8K2.t13074 (nat_lit 28395888) (nat_lit 3372027654) (nat_lit 0) D2M8K2.t13075 from rfl, totK_node, tot13074, tot13075]
  decide +kernel

theorem arows13070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13070 = true := by
  rw [show D2M8K2.u13070 = KTree.node D2M8K2.t13076 (nat_lit 28399253) (nat_lit 2048863643) (nat_lit 0) D2M8K2.t13077 from rfl, allE_node, rows13076, irow13070, rows13077]
  all_goals rfl

theorem atot13070 : totK PD2M8K2 D2M8K2.u13070 = [0, 0, 364029428301, 928403617198, 456143455676, 26644536935, 0, 0] := by
  rw [show D2M8K2.u13070 = KTree.node D2M8K2.t13076 (nat_lit 28399253) (nat_lit 2048863643) (nat_lit 0) D2M8K2.t13077 from rfl, totK_node, tot13076, tot13077]
  decide +kernel

theorem arows13071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13071 = true := by
  rw [show D2M8K2.u13071 = KTree.node D2M8K2.t13078 (nat_lit 28402316) (nat_lit 3697621938) (nat_lit 0) D2M8K2.t13079 from rfl, allE_node, rows13078, irow13071, rows13079]
  all_goals rfl

theorem atot13071 : totK PD2M8K2 D2M8K2.u13071 = [0, 0, 377586901512, 944794379254, 421630878577, 22161131776, 0, 0] := by
  rw [show D2M8K2.u13071 = KTree.node D2M8K2.t13078 (nat_lit 28402316) (nat_lit 3697621938) (nat_lit 0) D2M8K2.t13079 from rfl, totK_node, tot13078, tot13079]
  decide +kernel

theorem arows13074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13074 = true := by
  rw [show D2M8K2.u13074 = KTree.node D2M8K2.t13080 (nat_lit 28405772) (nat_lit 2859369784) (nat_lit 0) D2M8K2.t13081 from rfl, allE_node, rows13080, irow13074, rows13081]
  all_goals rfl

theorem atot13074 : totK PD2M8K2 D2M8K2.u13074 = [0, 49430535357, 395528570651, 919022270250, 423651261763, 16826381184, 0, 0] := by
  rw [show D2M8K2.u13074 = KTree.node D2M8K2.t13080 (nat_lit 28405772) (nat_lit 2859369784) (nat_lit 0) D2M8K2.t13081 from rfl, totK_node, tot13080, tot13081]
  decide +kernel

theorem arows13075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13075 = true := by
  rw [show D2M8K2.u13075 = KTree.node D2M8K2.t13082 (nat_lit 28412718) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t13083 from rfl, allE_node, rows13082, irow13075, rows13083]
  all_goals rfl

theorem atot13075 : totK PD2M8K2 D2M8K2.u13075 = [0, 366689676785, 927935762033, 499661092976, 40934385617, 0, 0, 0] := by
  rw [show D2M8K2.u13075 = KTree.node D2M8K2.t13082 (nat_lit 28412718) (nat_lit 4079301544) (nat_lit 0) D2M8K2.t13083 from rfl, totK_node, tot13082, tot13083]
  decide +kernel

theorem arows13077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13077 = true := by
  rw [show D2M8K2.u13077 = KTree.node D2M8K2.t13084 (nat_lit 28414136) (nat_lit 3739627535) (nat_lit 0) D2M8K2.t13085 from rfl, allE_node, rows13084, irow13077, rows13085]
  all_goals rfl

theorem atot13077 : totK PD2M8K2 D2M8K2.u13077 = [0, 23480092369, 474181404430, 900801887237, 392000458349, 29394892645, 0, 0] := by
  rw [show D2M8K2.u13077 = KTree.node D2M8K2.t13084 (nat_lit 28414136) (nat_lit 3739627535) (nat_lit 0) D2M8K2.t13085 from rfl, totK_node, tot13084, tot13085]
  decide +kernel

theorem arows13078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13078 = true := by
  rw [show D2M8K2.u13078 = KTree.node D2M8K2.t13086 (nat_lit 28415699) (nat_lit 2728480072) (nat_lit 0) D2M8K2.t13087 from rfl, allE_node, rows13086, irow13078, rows13087]
  all_goals rfl

theorem atot13078 : totK PD2M8K2 D2M8K2.u13078 = [0, 261358537408, 712312777215, 640979895222, 205031255636, 8214505460, 0, 0] := by
  rw [show D2M8K2.u13078 = KTree.node D2M8K2.t13086 (nat_lit 28415699) (nat_lit 2728480072) (nat_lit 0) D2M8K2.t13087 from rfl, totK_node, tot13086, tot13087]
  decide +kernel

theorem arows13083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13083 = true := by
  rw [show D2M8K2.u13083 = KTree.node D2M8K2.t13088 (nat_lit 28417656) (nat_lit 2743662572) (nat_lit 0) D2M8K2.t13089 from rfl, allE_node, rows13088, irow13083, rows13089]
  all_goals rfl

theorem atot13083 : totK PD2M8K2 D2M8K2.u13083 = [0, 123320957527, 636379395901, 841028294371, 211149087940, 9718818700, 0, 0] := by
  rw [show D2M8K2.u13083 = KTree.node D2M8K2.t13088 (nat_lit 28417656) (nat_lit 2743662572) (nat_lit 0) D2M8K2.t13089 from rfl, totK_node, tot13088, tot13089]
  decide +kernel

theorem arows13084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13084 = true := by
  rw [show D2M8K2.u13084 = KTree.node D2M8K2.t13090 (nat_lit 28419677) (nat_lit 1557002042) (nat_lit 0) D2M8K2.t13091 from rfl, allE_node, rows13090, irow13084, rows13091]
  all_goals rfl

theorem atot13084 : totK PD2M8K2 D2M8K2.u13084 = [0, 371840917896, 941357369822, 480099715611, 35869813831, 0, 0, 0] := by
  rw [show D2M8K2.u13084 = KTree.node D2M8K2.t13090 (nat_lit 28419677) (nat_lit 1557002042) (nat_lit 0) D2M8K2.t13091 from rfl, totK_node, tot13090, tot13091]
  decide +kernel

theorem arows13086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13086 = true := by
  rw [show D2M8K2.u13086 = KTree.node D2M8K2.t13092 (nat_lit 28421366) (nat_lit 3930608647) (nat_lit 0) D2M8K2.t13093 from rfl, allE_node, rows13092, irow13086, rows13093]
  all_goals rfl

theorem atot13086 : totK PD2M8K2 D2M8K2.u13086 = [0, 0, 485338380985, 969633047023, 302283947842, 13237669976, 0, 0] := by
  rw [show D2M8K2.u13086 = KTree.node D2M8K2.t13092 (nat_lit 28421366) (nat_lit 3930608647) (nat_lit 0) D2M8K2.t13093 from rfl, totK_node, tot13092, tot13093]
  decide +kernel

theorem arows13087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13087 = true := by
  rw [show D2M8K2.u13087 = KTree.node D2M8K2.t13094 (nat_lit 28422753) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t13095 from rfl, allE_node, rows13094, irow13087, rows13095]
  all_goals rfl

theorem atot13087 : totK PD2M8K2 D2M8K2.u13087 = [0, 373955421059, 909787716217, 501707184732, 47692869876, 0, 0, 0] := by
  rw [show D2M8K2.u13087 = KTree.node D2M8K2.t13094 (nat_lit 28422753) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t13095 from rfl, totK_node, tot13094, tot13095]
  decide +kernel

theorem arows13090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13090 = true := by
  rw [show D2M8K2.u13090 = KTree.node D2M8K2.t13096 (nat_lit 28424482) (nat_lit 3604444673) (nat_lit 0) D2M8K2.t13097 from rfl, allE_node, rows13096, irow13090, rows13097]
  all_goals rfl

theorem atot13090 : totK PD2M8K2 D2M8K2.u13090 = [0, 78501087505, 630695768952, 885199981495, 203856436315, 4976872846, 0, 0] := by
  rw [show D2M8K2.u13090 = KTree.node D2M8K2.t13096 (nat_lit 28424482) (nat_lit 3604444673) (nat_lit 0) D2M8K2.t13097 from rfl, totK_node, tot13096, tot13097]
  decide +kernel

theorem arows13091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13091 = true := by
  rw [show D2M8K2.u13091 = KTree.node D2M8K2.t13098 (nat_lit 28426390) (nat_lit 2988145152) (nat_lit 0) D2M8K2.t13099 from rfl, allE_node, rows13098, irow13091, rows13099]
  all_goals rfl

theorem atot13091 : totK PD2M8K2 D2M8K2.u13091 = [0, 348993723264, 923391039491, 520922186607, 41194588071, 0, 0, 0] := by
  rw [show D2M8K2.u13091 = KTree.node D2M8K2.t13098 (nat_lit 28426390) (nat_lit 2988145152) (nat_lit 0) D2M8K2.t13099 from rfl, totK_node, tot13098, tot13099]
  decide +kernel

theorem arows13093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13093 = true := by
  rw [show D2M8K2.u13093 = KTree.node D2M8K2.t13100 (nat_lit 28428218) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t13101 from rfl, allE_node, rows13100, irow13093, rows13101]
  all_goals rfl

theorem atot13093 : totK PD2M8K2 D2M8K2.u13093 = [0, 0, 435619027491, 964241726209, 375016073606, 18292826089, 0, 0] := by
  rw [show D2M8K2.u13093 = KTree.node D2M8K2.t13100 (nat_lit 28428218) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t13101 from rfl, totK_node, tot13100, tot13101]
  decide +kernel

theorem arows13094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13094 = true := by
  rw [show D2M8K2.u13094 = KTree.node D2M8K2.t13102 (nat_lit 28433409) (nat_lit 1816237343) (nat_lit 0) D2M8K2.t13103 from rfl, allE_node, rows13102, irow13094, rows13103]
  all_goals rfl

theorem atot13094 : totK PD2M8K2 D2M8K2.u13094 = [0, 0, 373039295103, 931622915086, 494111146174, 37426930736, 0, 0] := by
  rw [show D2M8K2.u13094 = KTree.node D2M8K2.t13102 (nat_lit 28433409) (nat_lit 1816237343) (nat_lit 0) D2M8K2.t13103 from rfl, totK_node, tot13102, tot13103]
  decide +kernel

theorem arows13098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13098 = true := by
  rw [show D2M8K2.u13098 = KTree.node D2M8K2.t13104 (nat_lit 28434914) (nat_lit 4026169506) (nat_lit 0) D2M8K2.t13105 from rfl, allE_node, rows13104, irow13098, rows13105]
  all_goals rfl

theorem atot13098 : totK PD2M8K2 D2M8K2.u13098 = [0, 0, 37647871296, 536929961379, 908759627293, 320133031050, 15177715065, 0] := by
  rw [show D2M8K2.u13098 = KTree.node D2M8K2.t13104 (nat_lit 28434914) (nat_lit 4026169506) (nat_lit 0) D2M8K2.t13105 from rfl, totK_node, tot13104, tot13105]
  decide +kernel

theorem arows13099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13099 = true := by
  rw [show D2M8K2.u13099 = KTree.node D2M8K2.t13106 (nat_lit 28436718) (nat_lit 3185332478) (nat_lit 0) D2M8K2.t13107 from rfl, allE_node, rows13106, irow13099, rows13107]
  all_goals rfl

theorem atot13099 : totK PD2M8K2 D2M8K2.u13099 = [0, 0, 344356381778, 911697474220, 533889143407, 52212905670, 0, 0] := by
  rw [show D2M8K2.u13099 = KTree.node D2M8K2.t13106 (nat_lit 28436718) (nat_lit 3185332478) (nat_lit 0) D2M8K2.t13107 from rfl, totK_node, tot13106, tot13107]
  decide +kernel

theorem arows13101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13101 = true := by
  rw [show D2M8K2.u13101 = KTree.node D2M8K2.t13108 (nat_lit 28440368) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t13109 from rfl, allE_node, rows13108, irow13101, rows13109]
  all_goals rfl

theorem atot13101 : totK PD2M8K2 D2M8K2.u13101 = [0, 0, 379422852904, 939760923395, 464092885889, 35288462285, 0, 0] := by
  rw [show D2M8K2.u13101 = KTree.node D2M8K2.t13108 (nat_lit 28440368) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t13109 from rfl, totK_node, tot13108, tot13109]
  decide +kernel

theorem arows13102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13102 = true := by
  rw [show D2M8K2.u13102 = KTree.node D2M8K2.t13110 (nat_lit 28442148) (nat_lit 2938302417) (nat_lit 0) D2M8K2.t13111 from rfl, allE_node, rows13110, irow13102, rows13111]
  all_goals rfl

theorem atot13102 : totK PD2M8K2 D2M8K2.u13102 = [0, 0, 75724581091, 622823579355, 876284764020, 203025828268, 5218872685, 0] := by
  rw [show D2M8K2.u13102 = KTree.node D2M8K2.t13110 (nat_lit 28442148) (nat_lit 2938302417) (nat_lit 0) D2M8K2.t13111 from rfl, totK_node, tot13110, tot13111]
  decide +kernel

theorem arows13105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13105 = true := by
  rw [show D2M8K2.u13105 = KTree.node D2M8K2.t13112 (nat_lit 28443616) (nat_lit 3219395937) (nat_lit 0) D2M8K2.t13113 from rfl, allE_node, rows13112, irow13105, rows13113]
  all_goals rfl

theorem atot13105 : totK PD2M8K2 D2M8K2.u13105 = [0, 0, 360985664420, 922127095447, 492733334294, 40815855033, 0, 0] := by
  rw [show D2M8K2.u13105 = KTree.node D2M8K2.t13112 (nat_lit 28443616) (nat_lit 3219395937) (nat_lit 0) D2M8K2.t13113 from rfl, totK_node, tot13112, tot13113]
  decide +kernel

theorem arows13106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13106 = true := by
  rw [show D2M8K2.u13106 = KTree.node D2M8K2.t13114 (nat_lit 28445584) (nat_lit 2753396641) (nat_lit 0) D2M8K2.t13115 from rfl, allE_node, rows13114, irow13106, rows13115]
  all_goals rfl

theorem atot13106 : totK PD2M8K2 D2M8K2.u13106 = [0, 0, 138293598013, 720167402640, 813625287521, 136323824919, 1415142070, 0] := by
  rw [show D2M8K2.u13106 = KTree.node D2M8K2.t13114 (nat_lit 28445584) (nat_lit 2753396641) (nat_lit 0) D2M8K2.t13115 from rfl, totK_node, tot13114, tot13115]
  decide +kernel

theorem arows13108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13108 = true := by
  rw [show D2M8K2.u13108 = KTree.node D2M8K2.t13116 (nat_lit 28447417) (nat_lit 1409452706) (nat_lit 0) D2M8K2.t13117 from rfl, allE_node, rows13116, irow13108, rows13117]
  all_goals rfl

theorem atot13108 : totK PD2M8K2 D2M8K2.u13108 = [0, 90526249043, 414809443050, 790834628596, 486652356314, 44759941450, 0, 0] := by
  rw [show D2M8K2.u13108 = KTree.node D2M8K2.t13116 (nat_lit 28447417) (nat_lit 1409452706) (nat_lit 0) D2M8K2.t13117 from rfl, totK_node, tot13116, tot13117]
  decide +kernel

theorem arows13109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13109 = true := by
  rw [show D2M8K2.u13109 = KTree.node D2M8K2.t13118 (nat_lit 28492428) (nat_lit 3569228782) (nat_lit 0) D2M8K2.t13119 from rfl, allE_node, rows13118, irow13109, rows13119]
  all_goals rfl

theorem atot13109 : totK PD2M8K2 D2M8K2.u13109 = [0, 322738355064, 906038164425, 505214080234, 34141949929, 0, 0, 0] := by
  rw [show D2M8K2.u13109 = KTree.node D2M8K2.t13118 (nat_lit 28492428) (nat_lit 3569228782) (nat_lit 0) D2M8K2.t13119 from rfl, totK_node, tot13118, tot13119]
  decide +kernel

theorem arows13115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13115 = true := by
  rw [show D2M8K2.u13115 = KTree.node D2M8K2.t13120 (nat_lit 28494227) (nat_lit 2146287306) (nat_lit 0) D2M8K2.t13121 from rfl, allE_node, rows13120, irow13115, rows13121]
  all_goals rfl

theorem atot13115 : totK PD2M8K2 D2M8K2.u13115 = [0, 127552667007, 670092416928, 864167010316, 155008859727, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13115 = KTree.node D2M8K2.t13120 (nat_lit 28494227) (nat_lit 2146287306) (nat_lit 0) D2M8K2.t13121 from rfl, totK_node, tot13120, tot13121]
  decide +kernel

theorem arows13116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13116 = true := by
  rw [show D2M8K2.u13116 = KTree.node D2M8K2.t13122 (nat_lit 28495976) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t13123 from rfl, allE_node, rows13122, irow13116, rows13123]
  all_goals rfl

theorem atot13116 : totK PD2M8K2 D2M8K2.u13116 = [0, 296145858214, 890593417333, 567255976673, 54524270437, 0, 0, 0] := by
  rw [show D2M8K2.u13116 = KTree.node D2M8K2.t13122 (nat_lit 28495976) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t13123 from rfl, totK_node, tot13122, tot13123]
  decide +kernel

theorem arows13118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13118 = true := by
  rw [show D2M8K2.u13118 = KTree.node D2M8K2.t13124 (nat_lit 28497537) (nat_lit 1755358248) (nat_lit 0) D2M8K2.t13125 from rfl, allE_node, rows13124, irow13118, rows13125]
  all_goals rfl

theorem atot13118 : totK PD2M8K2 D2M8K2.u13118 = [0, 0, 329404849504, 927313761536, 505934881532, 31706270301, 0, 0] := by
  rw [show D2M8K2.u13118 = KTree.node D2M8K2.t13124 (nat_lit 28497537) (nat_lit 1755358248) (nat_lit 0) D2M8K2.t13125 from rfl, totK_node, tot13124, tot13125]
  decide +kernel

theorem arows13119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13119 = true := by
  rw [show D2M8K2.u13119 = KTree.node D2M8K2.t13126 (nat_lit 28502500) (nat_lit 2724652133) (nat_lit 0) D2M8K2.t13127 from rfl, allE_node, rows13126, irow13119, rows13127]
  all_goals rfl

theorem atot13119 : totK PD2M8K2 D2M8K2.u13119 = [0, 375257125037, 938318273764, 474341486042, 45914736946, 4185297743, 0, 0] := by
  rw [show D2M8K2.u13119 = KTree.node D2M8K2.t13126 (nat_lit 28502500) (nat_lit 2724652133) (nat_lit 0) D2M8K2.t13127 from rfl, totK_node, tot13126, tot13127]
  decide +kernel

theorem arows13122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13122 = true := by
  rw [show D2M8K2.u13122 = KTree.node D2M8K2.t13128 (nat_lit 28503729) (nat_lit 1805756758) (nat_lit 0) D2M8K2.t13129 from rfl, allE_node, rows13128, irow13122, rows13129]
  all_goals rfl

theorem atot13122 : totK PD2M8K2 D2M8K2.u13122 = [0, 70799043915, 555340535492, 901723860699, 261175308525, 10680993762, 0, 0] := by
  rw [show D2M8K2.u13122 = KTree.node D2M8K2.t13128 (nat_lit 28503729) (nat_lit 1805756758) (nat_lit 0) D2M8K2.t13129 from rfl, totK_node, tot13128, tot13129]
  decide +kernel

theorem arows13123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13123 = true := by
  rw [show D2M8K2.u13123 = KTree.node D2M8K2.t13130 (nat_lit 28505490) (nat_lit 3415873317) (nat_lit 0) D2M8K2.t13131 from rfl, allE_node, rows13130, irow13123, rows13131]
  all_goals rfl

theorem atot13123 : totK PD2M8K2 D2M8K2.u13123 = [0, 328878323951, 852386950947, 538212470751, 87331682521, 2569691499, 0, 0] := by
  rw [show D2M8K2.u13123 = KTree.node D2M8K2.t13130 (nat_lit 28505490) (nat_lit 3415873317) (nat_lit 0) D2M8K2.t13131 from rfl, totK_node, tot13130, tot13131]
  decide +kernel

theorem arows13125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13125 = true := by
  rw [show D2M8K2.u13125 = KTree.node D2M8K2.t13132 (nat_lit 28507033) (nat_lit 1412217548) (nat_lit 0) D2M8K2.t13133 from rfl, allE_node, rows13132, irow13125, rows13133]
  all_goals rfl

theorem atot13125 : totK PD2M8K2 D2M8K2.u13125 = [0, 91400987495, 702196715206, 871894473654, 138989264163, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13125 = KTree.node D2M8K2.t13132 (nat_lit 28507033) (nat_lit 1412217548) (nat_lit 0) D2M8K2.t13133 from rfl, totK_node, tot13132, tot13133]
  decide +kernel

theorem arows13126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13126 = true := by
  rw [show D2M8K2.u13126 = KTree.node D2M8K2.t13134 (nat_lit 28509015) (nat_lit 3625545066) (nat_lit 0) D2M8K2.t13135 from rfl, allE_node, rows13134, irow13126, rows13135]
  all_goals rfl

theorem atot13126 : totK PD2M8K2 D2M8K2.u13126 = [0, 316194754444, 822773995451, 546049155313, 107662819451, 3884009855, 0, 0] := by
  rw [show D2M8K2.u13126 = KTree.node D2M8K2.t13134 (nat_lit 28509015) (nat_lit 3625545066) (nat_lit 0) D2M8K2.t13135 from rfl, totK_node, tot13134, tot13135]
  decide +kernel

theorem arows13130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13130 = true := by
  rw [show D2M8K2.u13130 = KTree.node D2M8K2.t13136 (nat_lit 28510606) (nat_lit 3993191833) (nat_lit 0) D2M8K2.t13137 from rfl, allE_node, rows13136, irow13130, rows13137]
  all_goals rfl

theorem atot13130 : totK PD2M8K2 D2M8K2.u13130 = [0, 87861870204, 565878235767, 868294198970, 245556377506, 6046211669, 0, 0] := by
  rw [show D2M8K2.u13130 = KTree.node D2M8K2.t13136 (nat_lit 28510606) (nat_lit 3993191833) (nat_lit 0) D2M8K2.t13137 from rfl, totK_node, tot13136, tot13137]
  decide +kernel

theorem arows13131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13131 = true := by
  rw [show D2M8K2.u13131 = KTree.node D2M8K2.t13138 (nat_lit 28512641) (nat_lit 2210742470) (nat_lit 0) D2M8K2.t13139 from rfl, allE_node, rows13138, irow13131, rows13139]
  all_goals rfl

theorem atot13131 : totK PD2M8K2 D2M8K2.u13131 = [0, 0, 392456860906, 942885971057, 402240127373, 22603622741, 0, 0] := by
  rw [show D2M8K2.u13131 = KTree.node D2M8K2.t13138 (nat_lit 28512641) (nat_lit 2210742470) (nat_lit 0) D2M8K2.t13139 from rfl, totK_node, tot13138, tot13139]
  decide +kernel

theorem arows13133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13133 = true := by
  rw [show D2M8K2.u13133 = KTree.node D2M8K2.t13140 (nat_lit 28513929) (nat_lit 1110087353) (nat_lit 0) D2M8K2.t13141 from rfl, allE_node, rows13140, irow13133, rows13141]
  all_goals rfl

theorem atot13133 : totK PD2M8K2 D2M8K2.u13133 = [0, 0, 104345005500, 718500123305, 795140692318, 109655992587, 1239866073, 0] := by
  rw [show D2M8K2.u13133 = KTree.node D2M8K2.t13140 (nat_lit 28513929) (nat_lit 1110087353) (nat_lit 0) D2M8K2.t13141 from rfl, totK_node, tot13140, tot13141]
  decide +kernel

theorem arows13134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13134 = true := by
  rw [show D2M8K2.u13134 = KTree.node D2M8K2.t13142 (nat_lit 28516402) (nat_lit 3942439521) (nat_lit 0) D2M8K2.t13143 from rfl, allE_node, rows13142, irow13134, rows13143]
  all_goals rfl

theorem atot13134 : totK PD2M8K2 D2M8K2.u13134 = [0, 0, 382986118260, 943952763015, 460813438005, 34162227498, 0, 0] := by
  rw [show D2M8K2.u13134 = KTree.node D2M8K2.t13142 (nat_lit 28516402) (nat_lit 3942439521) (nat_lit 0) D2M8K2.t13143 from rfl, totK_node, tot13142, tot13143]
  decide +kernel

theorem arows13137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13137 = true := by
  rw [show D2M8K2.u13137 = KTree.node D2M8K2.t13144 (nat_lit 28522827) (nat_lit 3773231236) (nat_lit 0) D2M8K2.t13145 from rfl, allE_node, rows13144, irow13137, rows13145]
  all_goals rfl

theorem atot13137 : totK PD2M8K2 D2M8K2.u13137 = [0, 0, 375179997377, 922523408918, 491298819721, 37713597085, 0, 0] := by
  rw [show D2M8K2.u13137 = KTree.node D2M8K2.t13144 (nat_lit 28522827) (nat_lit 3773231236) (nat_lit 0) D2M8K2.t13145 from rfl, totK_node, tot13144, tot13145]
  decide +kernel

theorem arows13138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13138 = true := by
  rw [show D2M8K2.u13138 = KTree.node D2M8K2.t13146 (nat_lit 28524252) (nat_lit 3156656087) (nat_lit 0) D2M8K2.t13147 from rfl, allE_node, rows13146, irow13138, rows13147]
  all_goals rfl

theorem atot13138 : totK PD2M8K2 D2M8K2.u13138 = [0, 0, 87965710978, 634046989482, 813559719208, 207621169296, 9633262574, 0] := by
  rw [show D2M8K2.u13138 = KTree.node D2M8K2.t13146 (nat_lit 28524252) (nat_lit 3156656087) (nat_lit 0) D2M8K2.t13147 from rfl, totK_node, tot13146, tot13147]
  decide +kernel

theorem arows13140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13140 = true := by
  rw [show D2M8K2.u13140 = KTree.node D2M8K2.t13148 (nat_lit 28526156) (nat_lit 3765816030) (nat_lit 0) D2M8K2.t13149 from rfl, allE_node, rows13148, irow13140, rows13149]
  all_goals rfl

theorem atot13140 : totK PD2M8K2 D2M8K2.u13140 = [0, 0, 312084892076, 825038065542, 542016464739, 94532520532, 3472187823, 0] := by
  rw [show D2M8K2.u13140 = KTree.node D2M8K2.t13148 (nat_lit 28526156) (nat_lit 3765816030) (nat_lit 0) D2M8K2.t13149 from rfl, totK_node, tot13148, tot13149]
  decide +kernel

theorem arows13141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13141 = true := by
  rw [show D2M8K2.u13141 = KTree.node D2M8K2.t13150 (nat_lit 28527690) (nat_lit 3233158479) (nat_lit 0) D2M8K2.t13151 from rfl, allE_node, rows13150, irow13141, rows13151]
  all_goals rfl

theorem atot13141 : totK PD2M8K2 D2M8K2.u13141 = [0, 0, 106144867291, 747997437987, 786780415169, 103520065299, 1053411165, 0] := by
  rw [show D2M8K2.u13141 = KTree.node D2M8K2.t13150 (nat_lit 28527690) (nat_lit 3233158479) (nat_lit 0) D2M8K2.t13151 from rfl, totK_node, tot13150, tot13151]
  decide +kernel

theorem arows13146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13146 = true := by
  rw [show D2M8K2.u13146 = KTree.node D2M8K2.t13152 (nat_lit 28529771) (nat_lit 2728640004) (nat_lit 0) D2M8K2.t13153 from rfl, allE_node, rows13152, irow13146, rows13153]
  all_goals rfl

theorem atot13146 : totK PD2M8K2 D2M8K2.u13146 = [0, 0, 340661026832, 832650243450, 507868423133, 87676877866, 3667207281, 0] := by
  rw [show D2M8K2.u13146 = KTree.node D2M8K2.t13152 (nat_lit 28529771) (nat_lit 2728640004) (nat_lit 0) D2M8K2.t13153 from rfl, totK_node, tot13152, tot13153]
  decide +kernel

theorem arows13147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13147 = true := by
  rw [show D2M8K2.u13147 = KTree.node D2M8K2.t13154 (nat_lit 28533361) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t13155 from rfl, allE_node, rows13154, irow13147, rows13155]
  all_goals rfl

theorem atot13147 : totK PD2M8K2 D2M8K2.u13147 = [0, 308168605862, 787625497062, 521480959892, 155911503684, 11723623870, 0, 0] := by
  rw [show D2M8K2.u13147 = KTree.node D2M8K2.t13154 (nat_lit 28533361) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t13155 from rfl, totK_node, tot13154, tot13155]
  decide +kernel

theorem arows13149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13149 = true := by
  rw [show D2M8K2.u13149 = KTree.node D2M8K2.t13156 (nat_lit 28534618) (nat_lit 3635926283) (nat_lit 0) D2M8K2.t13157 from rfl, allE_node, rows13156, irow13149, rows13157]
  all_goals rfl

theorem atot13149 : totK PD2M8K2 D2M8K2.u13149 = [0, 95189083643, 686544123112, 845216209401, 140793171097, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13149 = KTree.node D2M8K2.t13156 (nat_lit 28534618) (nat_lit 3635926283) (nat_lit 0) D2M8K2.t13157 from rfl, totK_node, tot13156, tot13157]
  decide +kernel

theorem arows13150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13150 = true := by
  rw [show D2M8K2.u13150 = KTree.node D2M8K2.t13158 (nat_lit 28536974) (nat_lit 3068200444) (nat_lit 0) D2M8K2.t13159 from rfl, allE_node, rows13158, irow13150, rows13159]
  all_goals rfl

theorem atot13150 : totK PD2M8K2 D2M8K2.u13150 = [0, 349404024988, 910075113749, 525750540570, 48237326211, 0, 0, 0] := by
  rw [show D2M8K2.u13150 = KTree.node D2M8K2.t13158 (nat_lit 28536974) (nat_lit 3068200444) (nat_lit 0) D2M8K2.t13159 from rfl, totK_node, tot13158, tot13159]
  decide +kernel

theorem arows13153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13153 = true := by
  rw [show D2M8K2.u13153 = KTree.node D2M8K2.t13160 (nat_lit 28538497) (nat_lit 1452376532) (nat_lit 0) D2M8K2.t13161 from rfl, allE_node, rows13160, irow13153, rows13161]
  all_goals rfl

theorem atot13153 : totK PD2M8K2 D2M8K2.u13153 = [0, 68965578832, 488304488041, 847876036837, 381797979690, 29149246332, 0, 0] := by
  rw [show D2M8K2.u13153 = KTree.node D2M8K2.t13160 (nat_lit 28538497) (nat_lit 1452376532) (nat_lit 0) D2M8K2.t13161 from rfl, totK_node, tot13160, tot13161]
  decide +kernel

theorem arows13154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13154 = true := by
  rw [show D2M8K2.u13154 = KTree.node D2M8K2.t13162 (nat_lit 28539808) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t13163 from rfl, allE_node, rows13162, irow13154, rows13163]
  all_goals rfl

theorem atot13154 : totK PD2M8K2 D2M8K2.u13154 = [0, 254838890895, 726574138625, 626415784615, 193504369062, 6825134885, 0, 0] := by
  rw [show D2M8K2.u13154 = KTree.node D2M8K2.t13162 (nat_lit 28539808) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t13163 from rfl, totK_node, tot13162, tot13163]
  decide +kernel

theorem arows13156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13156 = true := by
  rw [show D2M8K2.u13156 = KTree.node D2M8K2.t13164 (nat_lit 28541709) (nat_lit 1476459923) (nat_lit 0) D2M8K2.t13165 from rfl, allE_node, rows13164, irow13156, rows13165]
  all_goals rfl

theorem atot13156 : totK PD2M8K2 D2M8K2.u13156 = [0, 88397418417, 596338112940, 853047246366, 228096312705, 10568566766, 0, 0] := by
  rw [show D2M8K2.u13156 = KTree.node D2M8K2.t13164 (nat_lit 28541709) (nat_lit 1476459923) (nat_lit 0) D2M8K2.t13165 from rfl, totK_node, tot13164, tot13165]
  decide +kernel

theorem arows13157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13157 = true := by
  rw [show D2M8K2.u13157 = KTree.node D2M8K2.t13166 (nat_lit 28543640) (nat_lit 3875261842) (nat_lit 0) D2M8K2.t13167 from rfl, allE_node, rows13166, irow13157, rows13167]
  all_goals rfl

theorem atot13157 : totK PD2M8K2 D2M8K2.u13157 = [0, 353993468950, 894478281428, 498033049374, 66797379228, 2481160468, 0, 0] := by
  rw [show D2M8K2.u13157 = KTree.node D2M8K2.t13166 (nat_lit 28543640) (nat_lit 3875261842) (nat_lit 0) D2M8K2.t13167 from rfl, totK_node, tot13166, tot13167]
  decide +kernel

theorem arows13161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13161 = true := by
  rw [show D2M8K2.u13161 = KTree.node D2M8K2.t13168 (nat_lit 28545201) (nat_lit 1805756758) (nat_lit 0) D2M8K2.t13169 from rfl, allE_node, rows13168, irow13161, rows13169]
  all_goals rfl

theorem atot13161 : totK PD2M8K2 D2M8K2.u13161 = [0, 71891312889, 543663815552, 891394934864, 261461395249, 10680993762, 0, 0] := by
  rw [show D2M8K2.u13161 = KTree.node D2M8K2.t13168 (nat_lit 28545201) (nat_lit 1805756758) (nat_lit 0) D2M8K2.t13169 from rfl, totK_node, tot13168, tot13169]
  decide +kernel

theorem arows13162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13162 = true := by
  rw [show D2M8K2.u13162 = KTree.node D2M8K2.t13170 (nat_lit 28546986) (nat_lit 3660937937) (nat_lit 0) D2M8K2.t13171 from rfl, allE_node, rows13170, irow13162, rows13171]
  all_goals rfl

theorem atot13162 : totK PD2M8K2 D2M8K2.u13162 = [0, 346683176451, 868361793174, 520842783409, 84593736971, 2569691499, 0, 0] := by
  rw [show D2M8K2.u13162 = KTree.node D2M8K2.t13170 (nat_lit 28546986) (nat_lit 3660937937) (nat_lit 0) D2M8K2.t13171 from rfl, totK_node, tot13170, tot13171]
  decide +kernel

theorem arows13164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13164 = true := by
  rw [show D2M8K2.u13164 = KTree.node D2M8K2.t13172 (nat_lit 28548480) (nat_lit 3458864538) (nat_lit 0) D2M8K2.t13173 from rfl, allE_node, rows13172, irow13164, rows13173]
  all_goals rfl

theorem atot13164 : totK PD2M8K2 D2M8K2.u13164 = [0, 92722817510, 719553413358, 873676536218, 136113364990, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13164 = KTree.node D2M8K2.t13172 (nat_lit 28548480) (nat_lit 3458864538) (nat_lit 0) D2M8K2.t13173 from rfl, totK_node, tot13172, tot13173]
  decide +kernel

theorem arows13165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13165 = true := by
  rw [show D2M8K2.u13165 = KTree.node D2M8K2.t13174 (nat_lit 28554180) (nat_lit 3216656488) (nat_lit 0) D2M8K2.t13175 from rfl, allE_node, rows13174, irow13165, rows13175]
  all_goals rfl

theorem atot13165 : totK PD2M8K2 D2M8K2.u13165 = [0, 0, 380122948895, 951560795051, 401797494822, 22145572651, 0, 0] := by
  rw [show D2M8K2.u13165 = KTree.node D2M8K2.t13174 (nat_lit 28554180) (nat_lit 3216656488) (nat_lit 0) D2M8K2.t13175 from rfl, totK_node, tot13174, tot13175]
  decide +kernel

theorem arows13168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13168 = true := by
  rw [show D2M8K2.u13168 = KTree.node D2M8K2.t13176 (nat_lit 28555835) (nat_lit 1810223483) (nat_lit 2176) D2M8K2.t13177 from rfl, allE_node, rows13176, irow13168, rows13177]
  all_goals rfl

theorem atot13168 : totK PD2M8K2 D2M8K2.u13168 = [0, 0, 158093932695, 776683812016, 701267386670, 91765004196, 1138244013, 0] := by
  rw [show D2M8K2.u13168 = KTree.node D2M8K2.t13176 (nat_lit 28555835) (nat_lit 1810223483) (nat_lit 2176) D2M8K2.t13177 from rfl, totK_node, tot13176, tot13177]
  decide +kernel

theorem arows13169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13169 = true := by
  rw [show D2M8K2.u13169 = KTree.node D2M8K2.t13178 (nat_lit 28557965) (nat_lit 1663964508) (nat_lit 0) D2M8K2.t13179 from rfl, allE_node, rows13178, irow13169, rows13179]
  all_goals rfl

theorem atot13169 : totK PD2M8K2 D2M8K2.u13169 = [0, 0, 342859274481, 929009203833, 504121639053, 40339586226, 0, 0] := by
  rw [show D2M8K2.u13169 = KTree.node D2M8K2.t13178 (nat_lit 28557965) (nat_lit 1663964508) (nat_lit 0) D2M8K2.t13179 from rfl, totK_node, tot13178, tot13179]
  decide +kernel

theorem arows13171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13171 = true := by
  rw [show D2M8K2.u13171 = KTree.node D2M8K2.t13180 (nat_lit 28561028) (nat_lit 3374714680) (nat_lit 0) D2M8K2.t13181 from rfl, allE_node, rows13180, irow13171, rows13181]
  all_goals rfl

theorem atot13171 : totK PD2M8K2 D2M8K2.u13171 = [0, 0, 397514179558, 952011722796, 418391983274, 23422307148, 0, 0] := by
  rw [show D2M8K2.u13171 = KTree.node D2M8K2.t13180 (nat_lit 28561028) (nat_lit 3374714680) (nat_lit 0) D2M8K2.t13181 from rfl, totK_node, tot13180, tot13181]
  decide +kernel

theorem arows13172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13172 = true := by
  rw [show D2M8K2.u13172 = KTree.node D2M8K2.t13182 (nat_lit 28564856) (nat_lit 3489231784) (nat_lit 0) D2M8K2.t13183 from rfl, allE_node, rows13182, irow13172, rows13183]
  all_goals rfl

theorem atot13172 : totK PD2M8K2 D2M8K2.u13172 = [0, 0, 347803250034, 957160210934, 477735734649, 24663448840, 0, 0] := by
  rw [show D2M8K2.u13172 = KTree.node D2M8K2.t13182 (nat_lit 28564856) (nat_lit 3489231784) (nat_lit 0) D2M8K2.t13183 from rfl, totK_node, tot13182, tot13183]
  decide +kernel

theorem arows13179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13179 = true := by
  rw [show D2M8K2.u13179 = KTree.node D2M8K2.t13184 (nat_lit 28567876) (nat_lit 3836880707) (nat_lit 0) D2M8K2.t13185 from rfl, allE_node, rows13184, irow13179, rows13185]
  all_goals rfl

theorem atot13179 : totK PD2M8K2 D2M8K2.u13179 = [0, 0, 370323956439, 923884319768, 458220666670, 35187629387, 0, 0] := by
  rw [show D2M8K2.u13179 = KTree.node D2M8K2.t13184 (nat_lit 28567876) (nat_lit 3836880707) (nat_lit 0) D2M8K2.t13185 from rfl, totK_node, tot13184, tot13185]
  decide +kernel

theorem arows13180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13180 = true := by
  rw [show D2M8K2.u13180 = KTree.node D2M8K2.t13186 (nat_lit 28569414) (nat_lit 3717644314) (nat_lit 0) D2M8K2.t13187 from rfl, allE_node, rows13186, irow13180, rows13187]
  all_goals rfl

theorem atot13180 : totK PD2M8K2 D2M8K2.u13180 = [0, 7559944729, 70740391001, 625085940614, 841599084843, 192215148162, 4977114383, 0] := by
  rw [show D2M8K2.u13180 = KTree.node D2M8K2.t13186 (nat_lit 28569414) (nat_lit 3717644314) (nat_lit 0) D2M8K2.t13187 from rfl, totK_node, tot13186, tot13187]
  decide +kernel

theorem arows13182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13182 = true := by
  rw [show D2M8K2.u13182 = KTree.node D2M8K2.t13188 (nat_lit 28575189) (nat_lit 1718085784) (nat_lit 0) D2M8K2.t13189 from rfl, allE_node, rows13188, irow13182, rows13189]
  all_goals rfl

theorem atot13182 : totK PD2M8K2 D2M8K2.u13182 = [0, 384994841356, 958432467239, 421868359817, 19403983580, 0, 0, 0] := by
  rw [show D2M8K2.u13182 = KTree.node D2M8K2.t13188 (nat_lit 28575189) (nat_lit 1718085784) (nat_lit 0) D2M8K2.t13189 from rfl, totK_node, tot13188, tot13189]
  decide +kernel

theorem arows13183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13183 = true := by
  rw [show D2M8K2.u13183 = KTree.node D2M8K2.t13190 (nat_lit 28576924) (nat_lit 2867400742) (nat_lit 0) D2M8K2.t13191 from rfl, allE_node, rows13190, irow13183, rows13191]
  all_goals rfl

theorem atot13183 : totK PD2M8K2 D2M8K2.u13183 = [0, 92635576531, 656304016332, 896076912064, 156539392328, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13183 = KTree.node D2M8K2.t13190 (nat_lit 28576924) (nat_lit 2867400742) (nat_lit 0) D2M8K2.t13191 from rfl, totK_node, tot13190, tot13191]
  decide +kernel

theorem arows13186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13186 = true := by
  rw [show D2M8K2.u13186 = KTree.node D2M8K2.t13192 (nat_lit 28578873) (nat_lit 1579628315) (nat_lit 2) D2M8K2.t13193 from rfl, allE_node, rows13192, irow13186, rows13193]
  all_goals rfl

theorem atot13186 : totK PD2M8K2 D2M8K2.u13186 = [0, 315653237186, 905996352286, 555267909365, 55693995623, 0, 0, 0] := by
  rw [show D2M8K2.u13186 = KTree.node D2M8K2.t13192 (nat_lit 28578873) (nat_lit 1579628315) (nat_lit 2) D2M8K2.t13193 from rfl, totK_node, tot13192, tot13193]
  decide +kernel

theorem arows13187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13187 = true := by
  rw [show D2M8K2.u13187 = KTree.node D2M8K2.t13194 (nat_lit 28580430) (nat_lit 3933033034) (nat_lit 0) D2M8K2.t13195 from rfl, allE_node, rows13194, irow13187, rows13195]
  all_goals rfl

theorem atot13187 : totK PD2M8K2 D2M8K2.u13187 = [0, 14517969929, 339797787921, 924941590715, 495921339195, 33655171283, 0, 0] := by
  rw [show D2M8K2.u13187 = KTree.node D2M8K2.t13194 (nat_lit 28580430) (nat_lit 3933033034) (nat_lit 0) D2M8K2.t13195 from rfl, totK_node, tot13194, tot13195]
  decide +kernel

theorem arows13189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13189 = true := by
  rw [show D2M8K2.u13189 = KTree.node D2M8K2.t13196 (nat_lit 28585467) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t13197 from rfl, allE_node, rows13196, irow13189, rows13197]
  all_goals rfl

theorem atot13189 : totK PD2M8K2 D2M8K2.u13189 = [0, 380505469814, 936542619899, 466304993032, 35243277195, 0, 0, 0] := by
  rw [show D2M8K2.u13189 = KTree.node D2M8K2.t13196 (nat_lit 28585467) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t13197 from rfl, totK_node, tot13196, tot13197]
  decide +kernel

theorem arows13190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13190 = true := by
  rw [show D2M8K2.u13190 = KTree.node D2M8K2.t13198 (nat_lit 28586724) (nat_lit 2675032659) (nat_lit 0) D2M8K2.t13199 from rfl, allE_node, rows13198, irow13190, rows13199]
  all_goals rfl

theorem atot13190 : totK PD2M8K2 D2M8K2.u13190 = [0, 30623113973, 514277117184, 928424220934, 290932468204, 13243784863, 0, 0] := by
  rw [show D2M8K2.u13190 = KTree.node D2M8K2.t13198 (nat_lit 28586724) (nat_lit 2675032659) (nat_lit 0) D2M8K2.t13199 from rfl, totK_node, tot13198, tot13199]
  decide +kernel

end QECKChecks.D2M8K2
