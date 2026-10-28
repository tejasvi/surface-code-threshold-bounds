import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A25

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows7706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7706 = true := by
  rw [show D2M8K2.u7706 = KTree.node D2M8K2.u7690 (nat_lit 16235329) (nat_lit 1377211629) (nat_lit 0) D2M8K2.u7705 from rfl, allE_node, arows7690, irow7706, arows7705]
  all_goals rfl

theorem atot7706 : totK PD2M8K2 D2M8K2.u7706 = [0, 0, 3626675001277, 12274880712092, 10822286435126, 2191616186837, 89386367044, 0] := by
  rw [show D2M8K2.u7706 = KTree.node D2M8K2.u7690 (nat_lit 16235329) (nat_lit 1377211629) (nat_lit 0) D2M8K2.u7705 from rfl, totK_node, atot7690, atot7705]
  decide +kernel

theorem arows7737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7737 = true := by
  rw [show D2M8K2.u7737 = KTree.node D2M8K2.u7721 (nat_lit 16292453) (nat_lit 1960983630) (nat_lit 0) D2M8K2.u7736 from rfl, allE_node, arows7721, irow7737, arows7736]
  all_goals rfl

theorem atot7737 : totK PD2M8K2 D2M8K2.u7737 = [0, 0, 1709920264582, 8230431717944, 12157071034607, 5538600871422, 698602565794, 18797058808] := by
  rw [show D2M8K2.u7737 = KTree.node D2M8K2.u7721 (nat_lit 16292453) (nat_lit 1960983630) (nat_lit 0) D2M8K2.u7736 from rfl, totK_node, atot7721, atot7736]
  decide +kernel

theorem arows7769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7769 = true := by
  rw [show D2M8K2.u7769 = KTree.node D2M8K2.u7753 (nat_lit 16375162) (nat_lit 3663530683) (nat_lit 0) D2M8K2.u7768 from rfl, allE_node, arows7753, irow7769, arows7768]
  all_goals rfl

theorem atot7769 : totK PD2M8K2 D2M8K2.u7769 = [0, 0, 2370179749297, 9903654469606, 11820688630923, 3947051038266, 340127572348, 5883117146] := by
  rw [show D2M8K2.u7769 = KTree.node D2M8K2.u7753 (nat_lit 16375162) (nat_lit 3663530683) (nat_lit 0) D2M8K2.u7768 from rfl, totK_node, atot7753, atot7768]
  decide +kernel

theorem arows7800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7800 = true := by
  rw [show D2M8K2.u7800 = KTree.node D2M8K2.u7784 (nat_lit 16934729) (nat_lit 1796861979) (nat_lit 0) D2M8K2.u7799 from rfl, allE_node, arows7784, irow7800, arows7799]
  all_goals rfl

theorem atot7800 : totK PD2M8K2 D2M8K2.u7800 = [0, 1973854997411, 8859389434445, 12101821802524, 5045282049575, 576580245559, 15318603796, 0] := by
  rw [show D2M8K2.u7800 = KTree.node D2M8K2.u7784 (nat_lit 16934729) (nat_lit 1796861979) (nat_lit 0) D2M8K2.u7799 from rfl, totK_node, atot7784, atot7799]
  decide +kernel

theorem arows7833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7833 = true := by
  rw [show D2M8K2.u7833 = KTree.node D2M8K2.u7817 (nat_lit 16976440) (nat_lit 3510766282) (nat_lit 0) D2M8K2.u7832 from rfl, allE_node, arows7817, irow7833, arows7832]
  all_goals rfl

theorem atot7833 : totK PD2M8K2 D2M8K2.u7833 = [0, 1998065620822, 8723428572770, 12054371367749, 5526312487875, 748192885605, 20248977901, 0] := by
  rw [show D2M8K2.u7833 = KTree.node D2M8K2.u7817 (nat_lit 16976440) (nat_lit 3510766282) (nat_lit 0) D2M8K2.u7832 from rfl, totK_node, atot7817, atot7832]
  decide +kernel

theorem arows7864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7864 = true := by
  rw [show D2M8K2.u7864 = KTree.node D2M8K2.u7848 (nat_lit 17011628) (nat_lit 3773568839) (nat_lit 0) D2M8K2.u7863 from rfl, allE_node, arows7848, irow7864, arows7863]
  all_goals rfl

theorem atot7864 : totK PD2M8K2 D2M8K2.u7864 = [0, 2036458072821, 8960452964036, 12236803000245, 5210493562174, 461057937291, 2621607852, 0] := by
  rw [show D2M8K2.u7864 = KTree.node D2M8K2.u7848 (nat_lit 17011628) (nat_lit 3773568839) (nat_lit 0) D2M8K2.u7863 from rfl, totK_node, atot7848, atot7863]
  decide +kernel

theorem arows7896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7896 = true := by
  rw [show D2M8K2.u7896 = KTree.node D2M8K2.u7880 (nat_lit 17050869) (nat_lit 1724547134) (nat_lit 0) D2M8K2.u7895 from rfl, allE_node, arows7880, irow7896, arows7895]
  all_goals rfl

theorem atot7896 : totK PD2M8K2 D2M8K2.u7896 = [0, 1651943885261, 8064867537673, 12354237979307, 5903841660087, 695402634454, 18830459099, 0] := by
  rw [show D2M8K2.u7896 = KTree.node D2M8K2.u7880 (nat_lit 17050869) (nat_lit 1724547134) (nat_lit 0) D2M8K2.u7895 from rfl, totK_node, atot7880, atot7895]
  decide +kernel

theorem arows7927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7927 = true := by
  rw [show D2M8K2.u7927 = KTree.node D2M8K2.u7911 (nat_lit 17095500) (nat_lit 2447749105) (nat_lit 0) D2M8K2.u7926 from rfl, allE_node, arows7911, irow7927, arows7926]
  all_goals rfl

theorem atot7927 : totK PD2M8K2 D2M8K2.u7927 = [0, 2102333489562, 9081119546979, 12143977197807, 4824447399067, 426540345885, 5858862459, 0] := by
  rw [show D2M8K2.u7927 = KTree.node D2M8K2.u7911 (nat_lit 17095500) (nat_lit 2447749105) (nat_lit 0) D2M8K2.u7926 from rfl, totK_node, atot7911, atot7926]
  decide +kernel

theorem arows7961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7961 = true := by
  rw [show D2M8K2.u7961 = KTree.node D2M8K2.u7945 (nat_lit 17180766) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u7960 from rfl, allE_node, arows7945, irow7961, arows7960]
  all_goals rfl

theorem atot7961 : totK PD2M8K2 D2M8K2.u7961 = [0, 0, 3011340670890, 11388451457489, 11160877624181, 2553059046680, 130269716058, 1209030869] := by
  rw [show D2M8K2.u7961 = KTree.node D2M8K2.u7945 (nat_lit 17180766) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u7960 from rfl, totK_node, atot7945, atot7960]
  decide +kernel

theorem arows7992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7992 = true := by
  rw [show D2M8K2.u7992 = KTree.node D2M8K2.u7976 (nat_lit 17228584) (nat_lit 3790668661) (nat_lit 0) D2M8K2.u7991 from rfl, allE_node, arows7976, irow7992, arows7991]
  all_goals rfl

theorem atot7992 : totK PD2M8K2 D2M8K2.u7992 = [0, 0, 3665104689735, 12302535449940, 10867485790137, 2100953644919, 73016687287, 0] := by
  rw [show D2M8K2.u7992 = KTree.node D2M8K2.u7976 (nat_lit 17228584) (nat_lit 3790668661) (nat_lit 0) D2M8K2.u7991 from rfl, totK_node, atot7976, atot7991]
  decide +kernel

theorem arows8024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8024 = true := by
  rw [show D2M8K2.u8024 = KTree.node D2M8K2.u8008 (nat_lit 17336076) (nat_lit 3039064465) (nat_lit 0) D2M8K2.u8023 from rfl, allE_node, arows8008, irow8024, arows8023]
  all_goals rfl

theorem atot8024 : totK PD2M8K2 D2M8K2.u8024 = [0, 0, 3968698384653, 12773199960916, 10191315884096, 1654221908816, 49071934279, 0] := by
  rw [show D2M8K2.u8024 = KTree.node D2M8K2.u8008 (nat_lit 17336076) (nat_lit 3039064465) (nat_lit 0) D2M8K2.u8023 from rfl, totK_node, atot8008, atot8023]
  decide +kernel

theorem arows8055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8055 = true := by
  rw [show D2M8K2.u8055 = KTree.node D2M8K2.u8039 (nat_lit 17419501) (nat_lit 1128289678) (nat_lit 0) D2M8K2.u8054 from rfl, allE_node, arows8039, irow8055, arows8054]
  all_goals rfl

theorem atot8055 : totK PD2M8K2 D2M8K2.u8055 = [0, 1978604257116, 6868903636481, 8748499941935, 7428811787100, 3048144775746, 312110578983, 6115358396] := by
  rw [show D2M8K2.u8055 = KTree.node D2M8K2.u8039 (nat_lit 17419501) (nat_lit 1128289678) (nat_lit 0) D2M8K2.u8054 from rfl, totK_node, atot8039, atot8054]
  decide +kernel

theorem arows8088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8088 = true := by
  rw [show D2M8K2.u8088 = KTree.node D2M8K2.u8072 (nat_lit 17465354) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u8087 from rfl, allE_node, arows8072, irow8088, arows8087]
  all_goals rfl

theorem atot8088 : totK PD2M8K2 D2M8K2.u8088 = [0, 2003498705682, 9128595388810, 12652964647838, 4762652510597, 321031114859, 1369150432, 0] := by
  rw [show D2M8K2.u8088 = KTree.node D2M8K2.u8072 (nat_lit 17465354) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u8087 from rfl, totK_node, atot8072, atot8087]
  decide +kernel

theorem arows8119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8119 = true := by
  rw [show D2M8K2.u8119 = KTree.node D2M8K2.u8103 (nat_lit 17497406) (nat_lit 2549702911) (nat_lit 128) D2M8K2.u8118 from rfl, allE_node, arows8103, irow8119, arows8118]
  all_goals rfl

theorem atot8119 : totK PD2M8K2 D2M8K2.u8119 = [0, 1268633329011, 6578827722010, 11785459058271, 7879282062938, 1482315913217, 50450299231, 0] := by
  rw [show D2M8K2.u8119 = KTree.node D2M8K2.u8103 (nat_lit 17497406) (nat_lit 2549702911) (nat_lit 128) D2M8K2.u8118 from rfl, totK_node, atot8103, atot8118]
  decide +kernel

theorem arows8151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8151 = true := by
  rw [show D2M8K2.u8151 = KTree.node D2M8K2.u8135 (nat_lit 17530354) (nat_lit 3965371130) (nat_lit 0) D2M8K2.u8150 from rfl, allE_node, arows8135, irow8151, arows8150]
  all_goals rfl

theorem atot8151 : totK PD2M8K2 D2M8K2.u8151 = [0, 1912847478495, 8600097223286, 12232213095448, 5463780211048, 601880882792, 14222663156, 0] := by
  rw [show D2M8K2.u8151 = KTree.node D2M8K2.u8135 (nat_lit 17530354) (nat_lit 3965371130) (nat_lit 0) D2M8K2.u8150 from rfl, totK_node, atot8135, atot8150]
  decide +kernel

theorem arows8182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8182 = true := by
  rw [show D2M8K2.u8182 = KTree.node D2M8K2.u8166 (nat_lit 17576954) (nat_lit 4202520523) (nat_lit 0) D2M8K2.u8181 from rfl, allE_node, arows8166, irow8182, arows8181]
  all_goals rfl

theorem atot8182 : totK PD2M8K2 D2M8K2.u8182 = [0, 1948283720596, 8787639172873, 12310369335687, 5293228294197, 481101557696, 6665697270, 0] := by
  rw [show D2M8K2.u8182 = KTree.node D2M8K2.u8166 (nat_lit 17576954) (nat_lit 4202520523) (nat_lit 0) D2M8K2.u8181 from rfl, totK_node, atot8166, atot8181]
  decide +kernel

theorem arows8221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8221 = true := by
  rw [show D2M8K2.u8221 = KTree.node D2M8K2.u8205 (nat_lit 17655075) (nat_lit 1224608512) (nat_lit 0) D2M8K2.u8220 from rfl, allE_node, arows8205, irow8221, arows8220]
  all_goals rfl

theorem atot8221 : totK PD2M8K2 D2M8K2.u8221 = [842186864805, 3373131598765, 6778468049507, 10098570325386, 6558276465172, 1037513494114, 32872698681, 0] := by
  rw [show D2M8K2.u8221 = KTree.node D2M8K2.u8205 (nat_lit 17655075) (nat_lit 1224608512) (nat_lit 0) D2M8K2.u8220 from rfl, totK_node, atot8205, atot8220]
  decide +kernel

theorem arows8252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8252 = true := by
  rw [show D2M8K2.u8252 = KTree.node D2M8K2.u8236 (nat_lit 17938283) (nat_lit 2864001406) (nat_lit 0) D2M8K2.u8251 from rfl, allE_node, arows8236, irow8252, arows8251]
  all_goals rfl

theorem atot8252 : totK PD2M8K2 D2M8K2.u8252 = [2014305670632, 9172654375115, 12409416432403, 4610464712950, 324443801371, 1369150432, 0, 0] := by
  rw [show D2M8K2.u8252 = KTree.node D2M8K2.u8236 (nat_lit 17938283) (nat_lit 2864001406) (nat_lit 0) D2M8K2.u8251 from rfl, totK_node, atot8236, atot8251]
  decide +kernel

theorem arows8284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8284 = true := by
  rw [show D2M8K2.u8284 = KTree.node D2M8K2.u8268 (nat_lit 18028086) (nat_lit 3309404455) (nat_lit 0) D2M8K2.u8283 from rfl, allE_node, arows8268, irow8284, arows8283]
  all_goals rfl

theorem atot8284 : totK PD2M8K2 D2M8K2.u8284 = [1825986594174, 8214182404098, 12012430936295, 5817130986238, 721971025153, 18797058808, 0, 0] := by
  rw [show D2M8K2.u8284 = KTree.node D2M8K2.u8268 (nat_lit 18028086) (nat_lit 3309404455) (nat_lit 0) D2M8K2.u8283 from rfl, totK_node, atot8268, atot8283]
  decide +kernel

theorem arows8315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8315 = true := by
  rw [show D2M8K2.u8315 = KTree.node D2M8K2.u8299 (nat_lit 18065449) (nat_lit 1444693573) (nat_lit 0) D2M8K2.u8314 from rfl, allE_node, arows8299, irow8315, arows8314]
  all_goals rfl

theorem atot8315 : totK PD2M8K2 D2M8K2.u8315 = [1673553266984, 8025847850969, 12186260542759, 6054684931231, 756383215255, 19065934916, 0, 0] := by
  rw [show D2M8K2.u8315 = KTree.node D2M8K2.u8299 (nat_lit 18065449) (nat_lit 1444693573) (nat_lit 0) D2M8K2.u8314 from rfl, totK_node, atot8299, atot8314]
  decide +kernel

theorem arows8348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8348 = true := by
  rw [show D2M8K2.u8348 = KTree.node D2M8K2.u8332 (nat_lit 18103554) (nat_lit 3257192735) (nat_lit 0) D2M8K2.u8347 from rfl, allE_node, arows8332, irow8348, arows8347]
  all_goals rfl

theorem atot8348 : totK PD2M8K2 D2M8K2.u8348 = [1841226873467, 8643950797835, 12388559044684, 5239642254629, 492955828873, 6115358396, 0, 0] := by
  rw [show D2M8K2.u8348 = KTree.node D2M8K2.u8332 (nat_lit 18103554) (nat_lit 3257192735) (nat_lit 0) D2M8K2.u8347 from rfl, totK_node, atot8332, atot8347]
  decide +kernel

theorem arows8379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8379 = true := by
  rw [show D2M8K2.u8379 = KTree.node D2M8K2.u8363 (nat_lit 18143921) (nat_lit 1495929162) (nat_lit 0) D2M8K2.u8378 from rfl, allE_node, arows8363, irow8379, arows8378]
  all_goals rfl

theorem atot8379 : totK PD2M8K2 D2M8K2.u8379 = [1549751495390, 7563605587621, 12191620504020, 6697095460489, 813173318997, 12363669215, 0, 0] := by
  rw [show D2M8K2.u8379 = KTree.node D2M8K2.u8363 (nat_lit 18143921) (nat_lit 1495929162) (nat_lit 0) D2M8K2.u8378 from rfl, totK_node, atot8363, atot8378]
  decide +kernel

theorem arows8411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8411 = true := by
  rw [show D2M8K2.u8411 = KTree.node D2M8K2.u8395 (nat_lit 18180552) (nat_lit 3423636580) (nat_lit 0) D2M8K2.u8410 from rfl, allE_node, arows8395, irow8411, arows8410]
  all_goals rfl

theorem atot8411 : totK PD2M8K2 D2M8K2.u8411 = [0, 2087401900248, 9488445329089, 12359702041671, 4022126893830, 306636428551, 1369150432, 0] := by
  rw [show D2M8K2.u8411 = KTree.node D2M8K2.u8395 (nat_lit 18180552) (nat_lit 3423636580) (nat_lit 0) D2M8K2.u8410 from rfl, totK_node, atot8395, atot8410]
  decide +kernel

theorem arows8442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8442 = true := by
  rw [show D2M8K2.u8442 = KTree.node D2M8K2.u8426 (nat_lit 18267369) (nat_lit 1843418040) (nat_lit 0) D2M8K2.u8441 from rfl, allE_node, arows8426, irow8442, arows8441]
  all_goals rfl

theorem atot8442 : totK PD2M8K2 D2M8K2.u8442 = [0, 3258868718937, 11789543893735, 11332733880061, 2296191451978, 76130314806, 0, 0] := by
  rw [show D2M8K2.u8442 = KTree.node D2M8K2.u8426 (nat_lit 18267369) (nat_lit 1843418040) (nat_lit 0) D2M8K2.u8441 from rfl, totK_node, atot8426, atot8441]
  decide +kernel

theorem arows8476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8476 = true := by
  rw [show D2M8K2.u8476 = KTree.node D2M8K2.u8460 (nat_lit 18342072) (nat_lit 3424934041) (nat_lit 0) D2M8K2.u8475 from rfl, allE_node, arows8460, irow8476, arows8475]
  all_goals rfl

theorem atot8476 : totK PD2M8K2 D2M8K2.u8476 = [0, 3520500647181, 12112542904084, 11009595017746, 2100131484666, 61338204198, 0, 0] := by
  rw [show D2M8K2.u8476 = KTree.node D2M8K2.u8460 (nat_lit 18342072) (nat_lit 3424934041) (nat_lit 0) D2M8K2.u8475 from rfl, totK_node, atot8460, atot8475]
  decide +kernel

theorem arows8507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8507 = true := by
  rw [show D2M8K2.u8507 = KTree.node D2M8K2.u8491 (nat_lit 18462768) (nat_lit 3304321226) (nat_lit 0) D2M8K2.u8506 from rfl, allE_node, arows8491, irow8507, arows8506]
  all_goals rfl

theorem atot8507 : totK PD2M8K2 D2M8K2.u8507 = [2117734323592, 8570633824029, 11370799991131, 5899431743881, 999001152915, 32229130377, 0, 0] := by
  rw [show D2M8K2.u8507 = KTree.node D2M8K2.u8491 (nat_lit 18462768) (nat_lit 3304321226) (nat_lit 0) D2M8K2.u8506 from rfl, totK_node, atot8491, atot8506]
  decide +kernel

theorem arows8539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8539 = true := by
  rw [show D2M8K2.u8539 = KTree.node D2M8K2.u8523 (nat_lit 18493481) (nat_lit 1606177362) (nat_lit 0) D2M8K2.u8538 from rfl, allE_node, arows8523, irow8539, arows8538]
  all_goals rfl

theorem atot8539 : totK PD2M8K2 D2M8K2.u8539 = [1256250740985, 6404233065265, 11554408689133, 8035253951623, 1602436727774, 58018127943, 0, 0] := by
  rw [show D2M8K2.u8539 = KTree.node D2M8K2.u8523 (nat_lit 18493481) (nat_lit 1606177362) (nat_lit 0) D2M8K2.u8538 from rfl, totK_node, atot8523, atot8538]
  decide +kernel

theorem arows8570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8570 = true := by
  rw [show D2M8K2.u8570 = KTree.node D2M8K2.u8554 (nat_lit 18535628) (nat_lit 1531578613) (nat_lit 0) D2M8K2.u8569 from rfl, allE_node, arows8554, irow8570, arows8569]
  all_goals rfl

theorem atot8570 : totK PD2M8K2 D2M8K2.u8570 = [2031355214467, 8796023634929, 12025135069600, 5381664619572, 646283957367, 17590593026, 0, 0] := by
  rw [show D2M8K2.u8570 = KTree.node D2M8K2.u8554 (nat_lit 18535628) (nat_lit 1531578613) (nat_lit 0) D2M8K2.u8569 from rfl, totK_node, atot8554, atot8569]
  decide +kernel

theorem arows8603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8603 = true := by
  rw [show D2M8K2.u8603 = KTree.node D2M8K2.u8587 (nat_lit 18573661) (nat_lit 1023417417) (nat_lit 0) D2M8K2.u8602 from rfl, allE_node, arows8587, irow8603, arows8602]
  all_goals rfl

theorem atot8603 : totK PD2M8K2 D2M8K2.u8603 = [1630550614751, 7784714611484, 12183026946146, 6355135561764, 791246881156, 19065934916, 0, 0] := by
  rw [show D2M8K2.u8603 = KTree.node D2M8K2.u8587 (nat_lit 18573661) (nat_lit 1023417417) (nat_lit 0) D2M8K2.u8602 from rfl, totK_node, atot8587, atot8602]
  decide +kernel

theorem arows8634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8634 = true := by
  rw [show D2M8K2.u8634 = KTree.node D2M8K2.u8618 (nat_lit 18611446) (nat_lit 3225532701) (nat_lit 0) D2M8K2.u8633 from rfl, allE_node, arows8618, irow8634, arows8633]
  all_goals rfl

theorem atot8634 : totK PD2M8K2 D2M8K2.u8634 = [1915723616619, 8797668540893, 12380401368725, 5246026136309, 492277257258, 6115358396, 0, 0] := by
  rw [show D2M8K2.u8634 = KTree.node D2M8K2.u8618 (nat_lit 18611446) (nat_lit 3225532701) (nat_lit 0) D2M8K2.u8633 from rfl, totK_node, atot8618, atot8633]
  decide +kernel

theorem arows8666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8666 = true := by
  rw [show D2M8K2.u8666 = KTree.node D2M8K2.u8650 (nat_lit 18649790) (nat_lit 3709854245) (nat_lit 0) D2M8K2.u8665 from rfl, allE_node, arows8650, irow8666, arows8665]
  all_goals rfl

theorem atot8666 : totK PD2M8K2 D2M8K2.u8666 = [857731848908, 5803062016975, 12027383786083, 8494845106272, 1685360764597, 70482096786, 0, 0] := by
  rw [show D2M8K2.u8666 = KTree.node D2M8K2.u8650 (nat_lit 18649790) (nat_lit 3709854245) (nat_lit 0) D2M8K2.u8665 from rfl, totK_node, atot8650, atot8665]
  decide +kernel

theorem arows8697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8697 = true := by
  rw [show D2M8K2.u8697 = KTree.node D2M8K2.u8681 (nat_lit 18728633) (nat_lit 1182911004) (nat_lit 0) D2M8K2.u8696 from rfl, allE_node, arows8681, irow8697, arows8696]
  all_goals rfl

theorem atot8697 : totK PD2M8K2 D2M8K2.u8697 = [0, 1499167729953, 7373951454025, 11729417630961, 6853709482902, 1216459630965, 48508304344, 0] := by
  rw [show D2M8K2.u8697 = KTree.node D2M8K2.u8681 (nat_lit 18728633) (nat_lit 1182911004) (nat_lit 0) D2M8K2.u8696 from rfl, totK_node, atot8681, atot8696]
  decide +kernel

theorem arows8732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8732 = true := by
  rw [show D2M8K2.u8732 = KTree.node D2M8K2.u8716 (nat_lit 18762297) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u8731 from rfl, allE_node, arows8716, irow8732, arows8731]
  all_goals rfl

theorem atot8732 : totK PD2M8K2 D2M8K2.u8732 = [0, 1694558173554, 7864385812125, 12079501600997, 6290319000627, 790625194120, 15685616753, 0] := by
  rw [show D2M8K2.u8732 = KTree.node D2M8K2.u8716 (nat_lit 18762297) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u8731 from rfl, totK_node, atot8716, atot8731]
  decide +kernel

theorem arows8763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8763 = true := by
  rw [show D2M8K2.u8763 = KTree.node D2M8K2.u8747 (nat_lit 18804238) (nat_lit 4017857514) (nat_lit 0) D2M8K2.u8762 from rfl, allE_node, arows8747, irow8763, arows8762]
  all_goals rfl

theorem atot8763 : totK PD2M8K2 D2M8K2.u8763 = [0, 2010231624009, 9007923039884, 12187160372558, 5105537160483, 490281847145, 6624648996, 0] := by
  rw [show D2M8K2.u8763 = KTree.node D2M8K2.u8747 (nat_lit 18804238) (nat_lit 4017857514) (nat_lit 0) D2M8K2.u8762 from rfl, totK_node, atot8747, atot8762]
  decide +kernel

theorem arows8795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8795 = true := by
  rw [show D2M8K2.u8795 = KTree.node D2M8K2.u8779 (nat_lit 18841418) (nat_lit 4129028225) (nat_lit 0) D2M8K2.u8794 from rfl, allE_node, arows8779, irow8795, arows8794]
  all_goals rfl

theorem atot8795 : totK PD2M8K2 D2M8K2.u8795 = [0, 1987484463283, 9262166280692, 12642118752917, 4544450627892, 254683002250, 0, 0] := by
  rw [show D2M8K2.u8795 = KTree.node D2M8K2.u8779 (nat_lit 18841418) (nat_lit 4129028225) (nat_lit 0) D2M8K2.u8794 from rfl, totK_node, atot8779, atot8794]
  decide +kernel

theorem arows8826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8826 = true := by
  rw [show D2M8K2.u8826 = KTree.node D2M8K2.u8810 (nat_lit 18883302) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u8825 from rfl, allE_node, arows8810, irow8826, arows8825]
  all_goals rfl

theorem atot8826 : totK PD2M8K2 D2M8K2.u8826 = [0, 1999337774884, 8860706651006, 12169483459496, 5377822566161, 521837014276, 4085914357, 0] := by
  rw [show D2M8K2.u8826 = KTree.node D2M8K2.u8810 (nat_lit 18883302) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u8825 from rfl, totK_node, atot8810, atot8825]
  decide +kernel

theorem arows8859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8859 = true := by
  rw [show D2M8K2.u8859 = KTree.node D2M8K2.u8843 (nat_lit 19423748) (nat_lit 2876035827) (nat_lit 0) D2M8K2.u8858 from rfl, allE_node, arows8843, irow8859, arows8858]
  all_goals rfl

theorem atot8859 : totK PD2M8K2 D2M8K2.u8859 = [2005808282881, 8607980338512, 11211799160414, 4929850218260, 1480276322672, 276969942314, 9533751846, 0] := by
  rw [show D2M8K2.u8859 = KTree.node D2M8K2.u8843 (nat_lit 19423748) (nat_lit 2876035827) (nat_lit 0) D2M8K2.u8858 from rfl, totK_node, atot8843, atot8858]
  decide +kernel

theorem arows8890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8890 = true := by
  rw [show D2M8K2.u8890 = KTree.node D2M8K2.u8874 (nat_lit 19464819) (nat_lit 3654597354) (nat_lit 0) D2M8K2.u8889 from rfl, allE_node, arows8874, irow8890, arows8889]
  all_goals rfl

theorem atot8890 : totK PD2M8K2 D2M8K2.u8890 = [2029071634983, 8671316173087, 11772110393593, 5621300312544, 948863421883, 42081742489, 0, 0] := by
  rw [show D2M8K2.u8890 = KTree.node D2M8K2.u8874 (nat_lit 19464819) (nat_lit 3654597354) (nat_lit 0) D2M8K2.u8889 from rfl, totK_node, atot8874, atot8889]
  decide +kernel

theorem arows8922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8922 = true := by
  rw [show D2M8K2.u8922 = KTree.node D2M8K2.u8906 (nat_lit 19537994) (nat_lit 4048780173) (nat_lit 0) D2M8K2.u8921 from rfl, allE_node, arows8906, irow8922, arows8921]
  all_goals rfl

theorem atot8922 : totK PD2M8K2 D2M8K2.u8922 = [2133325745332, 8767315153325, 11600471299510, 5634402249861, 809944385811, 15936385454, 0, 0] := by
  rw [show D2M8K2.u8922 = KTree.node D2M8K2.u8906 (nat_lit 19537994) (nat_lit 4048780173) (nat_lit 0) D2M8K2.u8921 from rfl, totK_node, atot8906, atot8921]
  decide +kernel

theorem arows8953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8953 = true := by
  rw [show D2M8K2.u8953 = KTree.node D2M8K2.u8937 (nat_lit 19574856) (nat_lit 3630915925) (nat_lit 0) D2M8K2.u8952 from rfl, allE_node, arows8937, irow8953, arows8952]
  all_goals rfl

theorem atot8953 : totK PD2M8K2 D2M8K2.u8953 = [1659510064435, 7791322791120, 12103072835633, 6316807120534, 783916926036, 19065934916, 0, 0] := by
  rw [show D2M8K2.u8953 = KTree.node D2M8K2.u8937 (nat_lit 19574856) (nat_lit 3630915925) (nat_lit 0) D2M8K2.u8952 from rfl, totK_node, atot8937, atot8952]
  decide +kernel

theorem arows8987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8987 = true := by
  rw [show D2M8K2.u8987 = KTree.node D2M8K2.u8971 (nat_lit 19611217) (nat_lit 1497555566) (nat_lit 0) D2M8K2.u8986 from rfl, allE_node, arows8971, irow8987, arows8986]
  all_goals rfl

theorem atot8987 : totK PD2M8K2 D2M8K2.u8987 = [1932691287706, 8849403953308, 12365235988329, 5168481444815, 484576769066, 6115358396, 0, 0] := by
  rw [show D2M8K2.u8987 = KTree.node D2M8K2.u8971 (nat_lit 19611217) (nat_lit 1497555566) (nat_lit 0) D2M8K2.u8986 from rfl, totK_node, atot8971, atot8986]
  decide +kernel

theorem arows9018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9018 = true := by
  rw [show D2M8K2.u9018 = KTree.node D2M8K2.u9002 (nat_lit 19648610) (nat_lit 3994438034) (nat_lit 0) D2M8K2.u9017 from rfl, allE_node, arows9002, irow9018, arows9017]
  all_goals rfl

theorem atot9018 : totK PD2M8K2 D2M8K2.u9018 = [441860355822, 4938177957647, 12622805832031, 9262586437156, 1419551531841, 36604242125, 0, 0] := by
  rw [show D2M8K2.u9018 = KTree.node D2M8K2.u9002 (nat_lit 19648610) (nat_lit 3994438034) (nat_lit 0) D2M8K2.u9017 from rfl, totK_node, atot9002, atot9017]
  decide +kernel

theorem arows9050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9050 = true := by
  rw [show D2M8K2.u9050 = KTree.node D2M8K2.u9034 (nat_lit 19690132) (nat_lit 3190465814) (nat_lit 0) D2M8K2.u9049 from rfl, allE_node, arows9034, irow9050, arows9049]
  all_goals rfl

theorem atot9050 : totK PD2M8K2 D2M8K2.u9050 = [0, 2020274379916, 9328971134325, 12661529154950, 4309982303254, 260424761048, 1310517177, 0] := by
  rw [show D2M8K2.u9050 = KTree.node D2M8K2.u9034 (nat_lit 19690132) (nat_lit 3190465814) (nat_lit 0) D2M8K2.u9049 from rfl, totK_node, atot9034, atot9049]
  decide +kernel

theorem arows9081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9081 = true := by
  rw [show D2M8K2.u9081 = KTree.node D2M8K2.u9065 (nat_lit 19788370) (nat_lit 3908507366) (nat_lit 0) D2M8K2.u9080 from rfl, allE_node, arows9065, irow9081, arows9080]
  all_goals rfl

theorem atot9081 : totK PD2M8K2 D2M8K2.u9081 = [0, 2955931208760, 11087254374619, 11629782205552, 2968362185409, 128117596158, 0, 0] := by
  rw [show D2M8K2.u9081 = KTree.node D2M8K2.u9065 (nat_lit 19788370) (nat_lit 3908507366) (nat_lit 0) D2M8K2.u9080 from rfl, totK_node, atot9065, atot9080]
  decide +kernel

theorem arows9114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9114 = true := by
  rw [show D2M8K2.u9114 = KTree.node D2M8K2.u9098 (nat_lit 19826309) (nat_lit 1990427199) (nat_lit 0) D2M8K2.u9113 from rfl, allE_node, arows9098, irow9114, arows9113]
  all_goals rfl

theorem atot9114 : totK PD2M8K2 D2M8K2.u9114 = [0, 2008995320699, 8823779067794, 11867976421731, 5162160417785, 667503980118, 18953862985, 0] := by
  rw [show D2M8K2.u9114 = KTree.node D2M8K2.u9098 (nat_lit 19826309) (nat_lit 1990427199) (nat_lit 0) D2M8K2.u9113 from rfl, totK_node, atot9098, atot9113]
  decide +kernel

theorem arows9145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9145 = true := by
  rw [show D2M8K2.u9145 = KTree.node D2M8K2.u9129 (nat_lit 19868348) (nat_lit 2523423938) (nat_lit 0) D2M8K2.u9144 from rfl, allE_node, arows9129, irow9145, arows9144]
  all_goals rfl

theorem atot9145 : totK PD2M8K2 D2M8K2.u9145 = [0, 2019200917362, 9064939309019, 12315905265182, 4695686262444, 381801740878, 6052528252, 0] := by
  rw [show D2M8K2.u9145 = KTree.node D2M8K2.u9129 (nat_lit 19868348) (nat_lit 2523423938) (nat_lit 0) D2M8K2.u9144 from rfl, totK_node, atot9129, atot9144]
  decide +kernel

theorem arows9177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9177 = true := by
  rw [show D2M8K2.u9177 = KTree.node D2M8K2.u9161 (nat_lit 19923424) (nat_lit 2244071918) (nat_lit 0) D2M8K2.u9176 from rfl, allE_node, arows9161, irow9177, arows9176]
  all_goals rfl

theorem atot9177 : totK PD2M8K2 D2M8K2.u9177 = [2068225548152, 9114095213469, 12197077385111, 4693381184756, 451281325539, 14707189545, 0, 0] := by
  rw [show D2M8K2.u9177 = KTree.node D2M8K2.u9161 (nat_lit 19923424) (nat_lit 2244071918) (nat_lit 0) D2M8K2.u9176 from rfl, totK_node, atot9161, atot9176]
  decide +kernel

theorem arows9208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9208 = true := by
  rw [show D2M8K2.u9208 = KTree.node D2M8K2.u9192 (nat_lit 19964774) (nat_lit 4109909736) (nat_lit 0) D2M8K2.u9207 from rfl, allE_node, arows9192, irow9208, arows9207]
  all_goals rfl

theorem atot9208 : totK PD2M8K2 D2M8K2.u9208 = [1903830430307, 8209409875063, 11546907491798, 6164016930924, 1146056548582, 47300615174, 0, 0] := by
  rw [show D2M8K2.u9208 = KTree.node D2M8K2.u9192 (nat_lit 19964774) (nat_lit 4109909736) (nat_lit 0) D2M8K2.u9207 from rfl, totK_node, atot9192, atot9207]
  decide +kernel

theorem arows9244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9244 = true := by
  rw [show D2M8K2.u9244 = KTree.node D2M8K2.u9228 (nat_lit 19996876) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u9243 from rfl, allE_node, arows9228, irow9244, arows9243]
  all_goals rfl

theorem atot9244 : totK PD2M8K2 D2M8K2.u9244 = [1651658917354, 7840020884376, 12054954345414, 6390348077861, 839618692083, 13086914340, 0, 0] := by
  rw [show D2M8K2.u9244 = KTree.node D2M8K2.u9228 (nat_lit 19996876) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u9243 from rfl, totK_node, atot9228, atot9243]
  decide +kernel

theorem arows9275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9275 = true := by
  rw [show D2M8K2.u9275 = KTree.node D2M8K2.u9259 (nat_lit 20043417) (nat_lit 1534580032) (nat_lit 0) D2M8K2.u9274 from rfl, allE_node, arows9259, irow9275, arows9274]
  all_goals rfl

theorem atot9275 : totK PD2M8K2 D2M8K2.u9275 = [2036865665311, 8753001022027, 11938956228606, 5404039588088, 639287421388, 17667523310, 0, 0] := by
  rw [show D2M8K2.u9275 = KTree.node D2M8K2.u9259 (nat_lit 20043417) (nat_lit 1534580032) (nat_lit 0) D2M8K2.u9274 from rfl, totK_node, atot9259, atot9274]
  decide +kernel

theorem arows9307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9307 = true := by
  rw [show D2M8K2.u9307 = KTree.node D2M8K2.u9291 (nat_lit 20078737) (nat_lit 1231793523) (nat_lit 0) D2M8K2.u9306 from rfl, allE_node, arows9291, irow9307, arows9306]
  all_goals rfl

theorem atot9307 : totK PD2M8K2 D2M8K2.u9307 = [2102355608136, 8811334544879, 11707499472338, 5288174706919, 679064560983, 18964312856, 0, 0] := by
  rw [show D2M8K2.u9307 = KTree.node D2M8K2.u9291 (nat_lit 20078737) (nat_lit 1231793523) (nat_lit 0) D2M8K2.u9306 from rfl, totK_node, atot9291, atot9306]
  decide +kernel

theorem arows9338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9338 = true := by
  rw [show D2M8K2.u9338 = KTree.node D2M8K2.u9322 (nat_lit 20162950) (nat_lit 3806958359) (nat_lit 0) D2M8K2.u9337 from rfl, allE_node, arows9322, irow9338, arows9337]
  all_goals rfl

theorem atot9338 : totK PD2M8K2 D2M8K2.u9338 = [0, 3651654565454, 12310676437936, 10511239504451, 1972954497922, 67774614714, 0, 0] := by
  rw [show D2M8K2.u9338 = KTree.node D2M8K2.u9322 (nat_lit 20162950) (nat_lit 3806958359) (nat_lit 0) D2M8K2.u9337 from rfl, totK_node, atot9322, atot9337]
  decide +kernel

theorem arows9371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9371 = true := by
  rw [show D2M8K2.u9371 = KTree.node D2M8K2.u9355 (nat_lit 20206772) (nat_lit 3694315474) (nat_lit 0) D2M8K2.u9370 from rfl, allE_node, arows9355, irow9371, arows9370]
  all_goals rfl

theorem atot9371 : totK PD2M8K2 D2M8K2.u9371 = [0, 2569557316493, 10466678685668, 12043787958630, 3477855917777, 207441307894, 1209030869, 0] := by
  rw [show D2M8K2.u9371 = KTree.node D2M8K2.u9355 (nat_lit 20206772) (nat_lit 3694315474) (nat_lit 0) D2M8K2.u9370 from rfl, totK_node, atot9355, atot9370]
  decide +kernel

theorem arows9402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9402 = true := by
  rw [show D2M8K2.u9402 = KTree.node D2M8K2.u9386 (nat_lit 20284304) (nat_lit 3683952886) (nat_lit 0) D2M8K2.u9401 from rfl, allE_node, arows9386, irow9402, arows9401]
  all_goals rfl

theorem atot9402 : totK PD2M8K2 D2M8K2.u9402 = [0, 3425668970141, 11956776553131, 11157941644824, 2318772225659, 72506826507, 0, 0] := by
  rw [show D2M8K2.u9402 = KTree.node D2M8K2.u9386 (nat_lit 20284304) (nat_lit 3683952886) (nat_lit 0) D2M8K2.u9401 from rfl, totK_node, atot9386, atot9401]
  decide +kernel

theorem arows9434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9434 = true := by
  rw [show D2M8K2.u9434 = KTree.node D2M8K2.u9418 (nat_lit 20335945) (nat_lit 1374330533) (nat_lit 0) D2M8K2.u9433 from rfl, allE_node, arows9418, irow9434, arows9433]
  all_goals rfl

theorem atot9434 : totK PD2M8K2 D2M8K2.u9434 = [18947402031, 1789362678465, 8747361508359, 12532689853751, 4846282262216, 463630773415, 6115358396, 0] := by
  rw [show D2M8K2.u9434 = KTree.node D2M8K2.u9418 (nat_lit 20335945) (nat_lit 1374330533) (nat_lit 0) D2M8K2.u9433 from rfl, totK_node, atot9418, atot9433]
  decide +kernel

theorem arows9465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9465 = true := by
  rw [show D2M8K2.u9465 = KTree.node D2M8K2.u9449 (nat_lit 20422272) (nat_lit 3402447142) (nat_lit 0) D2M8K2.u9464 from rfl, allE_node, arows9449, irow9465, arows9464]
  all_goals rfl

theorem atot9465 : totK PD2M8K2 D2M8K2.u9465 = [2105196775267, 9281725286557, 12328390264930, 4552944455927, 322870938561, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9465 = KTree.node D2M8K2.u9449 (nat_lit 20422272) (nat_lit 3402447142) (nat_lit 0) D2M8K2.u9464 from rfl, totK_node, atot9449, atot9464]
  decide +kernel

theorem arows9499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9499 = true := by
  rw [show D2M8K2.u9499 = KTree.node D2M8K2.u9483 (nat_lit 20463597) (nat_lit 1403306970) (nat_lit 0) D2M8K2.u9498 from rfl, allE_node, arows9483, irow9499, arows9498]
  all_goals rfl

theorem atot9499 : totK PD2M8K2 D2M8K2.u9499 = [1858083019319, 8166152557761, 11629767692840, 6231644190071, 1161026430328, 47300615174, 0, 0] := by
  rw [show D2M8K2.u9499 = KTree.node D2M8K2.u9483 (nat_lit 20463597) (nat_lit 1403306970) (nat_lit 0) D2M8K2.u9498 from rfl, totK_node, atot9483, atot9498]
  decide +kernel

theorem arows9530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9530 = true := by
  rw [show D2M8K2.u9530 = KTree.node D2M8K2.u9514 (nat_lit 20494786) (nat_lit 4122712912) (nat_lit 0) D2M8K2.u9529 from rfl, allE_node, arows9514, irow9530, arows9529]
  all_goals rfl

theorem atot9530 : totK PD2M8K2 D2M8K2.u9530 = [1657709877627, 7793456021790, 12108020913843, 6448953566147, 835983824761, 13086914340, 0, 0] := by
  rw [show D2M8K2.u9530 = KTree.node D2M8K2.u9514 (nat_lit 20494786) (nat_lit 4122712912) (nat_lit 0) D2M8K2.u9529 from rfl, totK_node, atot9514, atot9529]
  decide +kernel

theorem arows9562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9562 = true := by
  rw [show D2M8K2.u9562 = KTree.node D2M8K2.u9546 (nat_lit 20542472) (nat_lit 3643078003) (nat_lit 0) D2M8K2.u9561 from rfl, allE_node, arows9546, irow9562, arows9561]
  all_goals rfl

theorem atot9562 : totK PD2M8K2 D2M8K2.u9562 = [2040138544570, 8948518861283, 12176093623144, 5206464969178, 535945559741, 13093127658, 0, 0] := by
  rw [show D2M8K2.u9562 = KTree.node D2M8K2.u9546 (nat_lit 20542472) (nat_lit 3643078003) (nat_lit 0) D2M8K2.u9561 from rfl, totK_node, atot9546, atot9561]
  decide +kernel

theorem arows9593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9593 = true := by
  rw [show D2M8K2.u9593 = KTree.node D2M8K2.u9577 (nat_lit 20618836) (nat_lit 4041295213) (nat_lit 0) D2M8K2.u9592 from rfl, allE_node, arows9577, irow9593, arows9592]
  all_goals rfl

theorem atot9593 : totK PD2M8K2 D2M8K2.u9593 = [2111932675973, 8772203793334, 11684973095006, 5463415980933, 702945623644, 19136354420, 0, 0] := by
  rw [show D2M8K2.u9593 = KTree.node D2M8K2.u9577 (nat_lit 20618836) (nat_lit 4041295213) (nat_lit 0) D2M8K2.u9592 from rfl, totK_node, atot9577, atot9592]
  decide +kernel

theorem arows9626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9626 = true := by
  rw [show D2M8K2.u9626 = KTree.node D2M8K2.u9610 (nat_lit 20654502) (nat_lit 3775869734) (nat_lit 0) D2M8K2.u9625 from rfl, allE_node, arows9610, irow9626, arows9625]
  all_goals rfl

theorem atot9626 : totK PD2M8K2 D2M8K2.u9626 = [0, 3594422542479, 12346111053380, 10754298923546, 1913677449663, 49331749000, 0, 0] := by
  rw [show D2M8K2.u9626 = KTree.node D2M8K2.u9610 (nat_lit 20654502) (nat_lit 3775869734) (nat_lit 0) D2M8K2.u9625 from rfl, totK_node, atot9610, atot9625]
  decide +kernel

theorem arows9657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9657 = true := by
  rw [show D2M8K2.u9657 = KTree.node D2M8K2.u9641 (nat_lit 20700606) (nat_lit 3971616199) (nat_lit 0) D2M8K2.u9656 from rfl, allE_node, arows9641, irow9657, arows9656]
  all_goals rfl

theorem atot9657 : totK PD2M8K2 D2M8K2.u9657 = [0, 2002731558746, 9131608801957, 12674729096550, 4609169082678, 276596127864, 1369150432, 0] := by
  rw [show D2M8K2.u9657 = KTree.node D2M8K2.u9641 (nat_lit 20700606) (nat_lit 3971616199) (nat_lit 0) D2M8K2.u9656 from rfl, totK_node, atot9641, atot9656]
  decide +kernel

theorem arows9689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9689 = true := by
  rw [show D2M8K2.u9689 = KTree.node D2M8K2.u9673 (nat_lit 20755714) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u9688 from rfl, allE_node, arows9673, irow9689, arows9688]
  all_goals rfl

theorem atot9689 : totK PD2M8K2 D2M8K2.u9689 = [0, 2152754201055, 9185115610234, 12074268119298, 4788208381129, 425093704455, 6301476269, 0] := by
  rw [show D2M8K2.u9689 = KTree.node D2M8K2.u9673 (nat_lit 20755714) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u9688 from rfl, totK_node, atot9673, atot9688]
  decide +kernel

theorem arows9720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9720 = true := by
  rw [show D2M8K2.u9720 = KTree.node D2M8K2.u9704 (nat_lit 20798080) (nat_lit 2867222864) (nat_lit 0) D2M8K2.u9719 from rfl, allE_node, arows9704, irow9720, arows9719]
  all_goals rfl

theorem atot9720 : totK PD2M8K2 D2M8K2.u9720 = [0, 1950887146295, 9027961075282, 12327096220089, 4915337751386, 426380864269, 6363931553, 0] := by
  rw [show D2M8K2.u9720 = KTree.node D2M8K2.u9704 (nat_lit 20798080) (nat_lit 2867222864) (nat_lit 0) D2M8K2.u9719 from rfl, totK_node, atot9704, atot9719]
  decide +kernel

theorem arows9755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9755 = true := by
  rw [show D2M8K2.u9755 = KTree.node D2M8K2.u9739 (nat_lit 20879758) (nat_lit 3993191833) (nat_lit 0) D2M8K2.u9754 from rfl, allE_node, arows9739, irow9755, arows9754]
  all_goals rfl

theorem atot9755 : totK PD2M8K2 D2M8K2.u9755 = [0, 1696578666752, 8090652181864, 12296489016658, 5822393917548, 629643198346, 10913788937, 0] := by
  rw [show D2M8K2.u9755 = KTree.node D2M8K2.u9739 (nat_lit 20879758) (nat_lit 3993191833) (nat_lit 0) D2M8K2.u9754 from rfl, totK_node, atot9739, atot9754]
  decide +kernel

theorem arows9786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9786 = true := by
  rw [show D2M8K2.u9786 = KTree.node D2M8K2.u9770 (nat_lit 20916402) (nat_lit 2794511873) (nat_lit 0) D2M8K2.u9785 from rfl, allE_node, arows9770, irow9786, arows9785]
  all_goals rfl

theorem atot9786 : totK PD2M8K2 D2M8K2.u9786 = [0, 2097017426243, 8984363722796, 11836125084416, 4898890062827, 656516904378, 23120318498, 0] := by
  rw [show D2M8K2.u9786 = KTree.node D2M8K2.u9770 (nat_lit 20916402) (nat_lit 2794511873) (nat_lit 0) D2M8K2.u9785 from rfl, totK_node, atot9770, atot9785]
  decide +kernel

theorem arows9818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9818 = true := by
  rw [show D2M8K2.u9818 = KTree.node D2M8K2.u9802 (nat_lit 21002475) (nat_lit 3636872964) (nat_lit 0) D2M8K2.u9817 from rfl, allE_node, arows9802, irow9818, arows9817]
  all_goals rfl

theorem atot9818 : totK PD2M8K2 D2M8K2.u9818 = [0, 2069654279492, 9316061517296, 12482961592643, 4438448417721, 273989471063, 1206465782, 0] := by
  rw [show D2M8K2.u9818 = KTree.node D2M8K2.u9802 (nat_lit 21002475) (nat_lit 3636872964) (nat_lit 0) D2M8K2.u9817 from rfl, totK_node, atot9802, atot9817]
  decide +kernel

theorem arows9849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9849 = true := by
  rw [show D2M8K2.u9849 = KTree.node D2M8K2.u9833 (nat_lit 21045685) (nat_lit 1068448507) (nat_lit 0) D2M8K2.u9848 from rfl, allE_node, arows9833, irow9849, arows9848]
  all_goals rfl

theorem atot9849 : totK PD2M8K2 D2M8K2.u9849 = [0, 1613359424907, 7933798990515, 12359206441169, 6097570442718, 740345907573, 19065934916, 0] := by
  rw [show D2M8K2.u9849 = KTree.node D2M8K2.u9833 (nat_lit 21045685) (nat_lit 1068448507) (nat_lit 0) D2M8K2.u9848 from rfl, totK_node, atot9833, atot9848]
  decide +kernel

theorem arows9882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9882 = true := by
  rw [show D2M8K2.u9882 = KTree.node D2M8K2.u9866 (nat_lit 21081436) (nat_lit 3169166271) (nat_lit 0) D2M8K2.u9881 from rfl, allE_node, arows9866, irow9882, arows9881]
  all_goals rfl

theorem atot9882 : totK PD2M8K2 D2M8K2.u9882 = [0, 1977912478543, 9149950976847, 12616612307003, 4619709187673, 292217317202, 1138244013, 0] := by
  rw [show D2M8K2.u9882 = KTree.node D2M8K2.u9866 (nat_lit 21081436) (nat_lit 3169166271) (nat_lit 0) D2M8K2.u9881 from rfl, totK_node, atot9866, atot9881]
  decide +kernel

theorem arows9913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9913 = true := by
  rw [show D2M8K2.u9913 = KTree.node D2M8K2.u9897 (nat_lit 21122653) (nat_lit 1011557657) (nat_lit 0) D2M8K2.u9912 from rfl, allE_node, arows9897, irow9913, arows9912]
  all_goals rfl

theorem atot9913 : totK PD2M8K2 D2M8K2.u9913 = [0, 1989067156267, 8624066118707, 12022732623289, 5554699863845, 615266303767, 11218804606, 0] := by
  rw [show D2M8K2.u9913 = KTree.node D2M8K2.u9897 (nat_lit 21122653) (nat_lit 1011557657) (nat_lit 0) D2M8K2.u9912 from rfl, totK_node, atot9897, atot9912]
  decide +kernel

theorem arows9945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9945 = true := by
  rw [show D2M8K2.u9945 = KTree.node D2M8K2.u9929 (nat_lit 21164784) (nat_lit 3583200308) (nat_lit 0) D2M8K2.u9944 from rfl, allE_node, arows9929, irow9945, arows9944]
  all_goals rfl

theorem atot9945 : totK PD2M8K2 D2M8K2.u9945 = [0, 0, 2514023577144, 10443604653443, 11964540752500, 3221014830385, 207172192423, 1369150432] := by
  rw [show D2M8K2.u9945 = KTree.node D2M8K2.u9929 (nat_lit 21164784) (nat_lit 3583200308) (nat_lit 0) D2M8K2.u9944 from rfl, totK_node, atot9929, atot9944]
  decide +kernel

theorem arows9976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9976 = true := by
  rw [show D2M8K2.u9976 = KTree.node D2M8K2.u9960 (nat_lit 21276174) (nat_lit 3938733786) (nat_lit 0) D2M8K2.u9975 from rfl, allE_node, arows9960, irow9976, arows9975]
  all_goals rfl

theorem atot9976 : totK PD2M8K2 D2M8K2.u9976 = [0, 0, 3661522400047, 12517672717389, 10812466989425, 1738678471263, 46533176475, 0] := by
  rw [show D2M8K2.u9976 = KTree.node D2M8K2.u9960 (nat_lit 21276174) (nat_lit 3938733786) (nat_lit 0) D2M8K2.u9975 from rfl, totK_node, atot9960, atot9975]
  decide +kernel

theorem arows10010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10010 = true := by
  rw [show D2M8K2.u10010 = KTree.node D2M8K2.u9994 (nat_lit 21330813) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u10009 from rfl, allE_node, arows9994, irow10010, arows10009]
  all_goals rfl

theorem atot10010 : totK PD2M8K2 D2M8K2.u10010 = [0, 0, 3771151031354, 12674073231340, 10654004168775, 1660936097550, 42385061453, 0] := by
  rw [show D2M8K2.u10010 = KTree.node D2M8K2.u9994 (nat_lit 21330813) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u10009 from rfl, totK_node, atot9994, atot10009]
  decide +kernel

theorem arows10041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10041 = true := by
  rw [show D2M8K2.u10041 = KTree.node D2M8K2.u10025 (nat_lit 21454940) (nat_lit 3344067707) (nat_lit 0) D2M8K2.u10040 from rfl, allE_node, arows10025, irow10041, arows10040]
  all_goals rfl

theorem atot10041 : totK PD2M8K2 D2M8K2.u10041 = [0, 2117734323592, 8576479170955, 11375841096865, 5793736363886, 1114223969913, 54862173305, 0] := by
  rw [show D2M8K2.u10041 = KTree.node D2M8K2.u10025 (nat_lit 21454940) (nat_lit 3344067707) (nat_lit 0) D2M8K2.u10040 from rfl, totK_node, atot10025, atot10040]
  decide +kernel

theorem arows10073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10073 = true := by
  rw [show D2M8K2.u10073 = KTree.node D2M8K2.u10057 (nat_lit 21488782) (nat_lit 2977768187) (nat_lit 0) D2M8K2.u10072 from rfl, allE_node, arows10057, irow10073, arows10072]
  all_goals rfl

theorem atot10073 : totK PD2M8K2 D2M8K2.u10073 = [0, 1662027715281, 7763771354341, 11980568451432, 6638951883050, 945909285773, 17086344800, 0] := by
  rw [show D2M8K2.u10073 = KTree.node D2M8K2.u10057 (nat_lit 21488782) (nat_lit 2977768187) (nat_lit 0) D2M8K2.u10072 from rfl, totK_node, atot10057, atot10072]
  decide +kernel

theorem arows10104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10104 = true := by
  rw [show D2M8K2.u10104 = KTree.node D2M8K2.u10088 (nat_lit 21530675) (nat_lit 2895302561) (nat_lit 0) D2M8K2.u10103 from rfl, allE_node, arows10088, irow10104, arows10103]
  all_goals rfl

theorem atot10104 : totK PD2M8K2 D2M8K2.u10104 = [0, 2042762082282, 8765595379497, 12048165111054, 5437753962265, 574866346111, 8287982345, 0] := by
  rw [show D2M8K2.u10104 = KTree.node D2M8K2.u10088 (nat_lit 21530675) (nat_lit 2895302561) (nat_lit 0) D2M8K2.u10103 from rfl, totK_node, atot10088, atot10103]
  decide +kernel

theorem arows10137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10137 = true := by
  rw [show D2M8K2.u10137 = KTree.node D2M8K2.u10121 (nat_lit 21569725) (nat_lit 964728298) (nat_lit 0) D2M8K2.u10136 from rfl, allE_node, arows10121, irow10137, arows10136]
  all_goals rfl

theorem atot10137 : totK PD2M8K2 D2M8K2.u10137 = [0, 1987484463283, 8757426639113, 11997017578742, 5401712923889, 653173224523, 17826068843, 0] := by
  rw [show D2M8K2.u10137 = KTree.node D2M8K2.u10121 (nat_lit 21569725) (nat_lit 964728298) (nat_lit 0) D2M8K2.u10136 from rfl, totK_node, atot10121, atot10136]
  decide +kernel

theorem arows10168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10168 = true := by
  rw [show D2M8K2.u10168 = KTree.node D2M8K2.u10152 (nat_lit 21611377) (nat_lit 1401464946) (nat_lit 0) D2M8K2.u10167 from rfl, allE_node, arows10152, irow10168, arows10167]
  all_goals rfl

theorem atot10168 : totK PD2M8K2 D2M8K2.u10168 = [0, 1999337774884, 9075103448436, 12493137382360, 4927252194277, 421328485983, 4977114383, 0] := by
  rw [show D2M8K2.u10168 = KTree.node D2M8K2.u10152 (nat_lit 21611377) (nat_lit 1401464946) (nat_lit 0) D2M8K2.u10167 from rfl, totK_node, atot10152, atot10167]
  decide +kernel

theorem arows10200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10200 = true := by
  rw [show D2M8K2.u10200 = KTree.node D2M8K2.u10184 (nat_lit 21648125) (nat_lit 2107667347) (nat_lit 0) D2M8K2.u10199 from rfl, allE_node, arows10184, irow10200, arows10199]
  all_goals rfl

theorem atot10200 : totK PD2M8K2 D2M8K2.u10200 = [0, 1749318396885, 7917005576151, 11754147197203, 6410007892681, 942971245884, 25761178333, 0] := by
  rw [show D2M8K2.u10200 = KTree.node D2M8K2.u10184 (nat_lit 21648125) (nat_lit 2107667347) (nat_lit 0) D2M8K2.u10199 from rfl, totK_node, atot10184, atot10199]
  decide +kernel

theorem arows10231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10231 = true := by
  rw [show D2M8K2.u10231 = KTree.node D2M8K2.u10215 (nat_lit 22440310) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u10230 from rfl, allE_node, arows10215, irow10231, arows10230]
  all_goals rfl

theorem atot10231 : totK PD2M8K2 D2M8K2.u10231 = [0, 1966889767749, 9060676188626, 12704170828951, 4744008086846, 303857214473, 1369150432, 0] := by
  rw [show D2M8K2.u10231 = KTree.node D2M8K2.u10215 (nat_lit 22440310) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u10230 from rfl, totK_node, atot10215, atot10230]
  decide +kernel

theorem arows10268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10268 = true := by
  rw [show D2M8K2.u10268 = KTree.node D2M8K2.u10252 (nat_lit 22471370) (nat_lit 4267280952) (nat_lit 0) D2M8K2.u10267 from rfl, allE_node, arows10252, irow10268, arows10267]
  all_goals rfl

theorem atot10268 : totK PD2M8K2 D2M8K2.u10268 = [0, 1338564870512, 6650039561949, 11695954016391, 7866396165659, 1421607209783, 45026643442, 0] := by
  rw [show D2M8K2.u10268 = KTree.node D2M8K2.u10252 (nat_lit 22471370) (nat_lit 4267280952) (nat_lit 0) D2M8K2.u10267 from rfl, totK_node, atot10252, atot10267]
  decide +kernel

theorem arows10299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10299 = true := by
  rw [show D2M8K2.u10299 = KTree.node D2M8K2.u10283 (nat_lit 22544090) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u10298 from rfl, allE_node, arows10283, irow10299, arows10298]
  all_goals rfl

theorem atot10299 : totK PD2M8K2 D2M8K2.u10299 = [0, 1612564422261, 7941168264807, 12284380087536, 6093271382529, 754125383911, 19065934916, 0] := by
  rw [show D2M8K2.u10299 = KTree.node D2M8K2.u10283 (nat_lit 22544090) (nat_lit 4242461733) (nat_lit 0) D2M8K2.u10298 from rfl, totK_node, atot10283, atot10298]
  decide +kernel

theorem arows10331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10331 = true := by
  rw [show D2M8K2.u10331 = KTree.node D2M8K2.u10315 (nat_lit 22582089) (nat_lit 1820735469) (nat_lit 0) D2M8K2.u10330 from rfl, allE_node, arows10315, irow10331, arows10330]
  all_goals rfl

theorem atot10331 : totK PD2M8K2 D2M8K2.u10331 = [0, 1920184716866, 8793027357648, 12367834986333, 5131297458818, 441501581182, 6115358396, 0] := by
  rw [show D2M8K2.u10331 = KTree.node D2M8K2.u10315 (nat_lit 22582089) (nat_lit 1820735469) (nat_lit 0) D2M8K2.u10330 from rfl, totK_node, atot10315, atot10330]
  decide +kernel

theorem arows10362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10362 = true := by
  rw [show D2M8K2.u10362 = KTree.node D2M8K2.u10346 (nat_lit 22622017) (nat_lit 1393479757) (nat_lit 0) D2M8K2.u10361 from rfl, allE_node, arows10346, irow10362, arows10361]
  all_goals rfl

theorem atot10362 : totK PD2M8K2 D2M8K2.u10362 = [0, 1614745196886, 7966379851687, 12548237998076, 6229363669780, 602431129381, 7317347254, 0] := by
  rw [show D2M8K2.u10362 = KTree.node D2M8K2.u10346 (nat_lit 22622017) (nat_lit 1393479757) (nat_lit 0) D2M8K2.u10361 from rfl, totK_node, atot10346, atot10361]
  decide +kernel

theorem arows10395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10395 = true := by
  rw [show D2M8K2.u10395 = KTree.node D2M8K2.u10379 (nat_lit 22660524) (nat_lit 3152783054) (nat_lit 0) D2M8K2.u10394 from rfl, allE_node, arows10379, irow10395, arows10394]
  all_goals rfl

theorem atot10395 : totK PD2M8K2 D2M8K2.u10395 = [0, 0, 2210250888185, 9898903572800, 12332733334931, 3681543844063, 227598317841, 1310517177] := by
  rw [show D2M8K2.u10395 = KTree.node D2M8K2.u10379 (nat_lit 22660524) (nat_lit 3152783054) (nat_lit 0) D2M8K2.u10394 from rfl, totK_node, atot10379, atot10394]
  decide +kernel

theorem arows10426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10426 = true := by
  rw [show D2M8K2.u10426 = KTree.node D2M8K2.u10410 (nat_lit 22705764) (nat_lit 3251650857) (nat_lit 0) D2M8K2.u10425 from rfl, allE_node, arows10410, irow10426, arows10425]
  all_goals rfl

theorem atot10426 : totK PD2M8K2 D2M8K2.u10426 = [0, 0, 3510832024673, 12177655183853, 10969421103018, 2276639681052, 91661518829, 0] := by
  rw [show D2M8K2.u10426 = KTree.node D2M8K2.u10410 (nat_lit 22705764) (nat_lit 3251650857) (nat_lit 0) D2M8K2.u10425 from rfl, totK_node, atot10410, atot10425]
  decide +kernel

theorem arows10458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10458 = true := by
  rw [show D2M8K2.u10458 = KTree.node D2M8K2.u10442 (nat_lit 22803897) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u10457 from rfl, allE_node, arows10442, irow10458, arows10457]
  all_goals rfl

theorem atot10458 : totK PD2M8K2 D2M8K2.u10458 = [0, 0, 1916625394188, 8546136654677, 11835132760952, 5392805298863, 695183070793, 18953862985] := by
  rw [show D2M8K2.u10458 = KTree.node D2M8K2.u10442 (nat_lit 22803897) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u10457 from rfl, totK_node, atot10442, atot10457]
  decide +kernel

theorem arows10489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10489 = true := by
  rw [show D2M8K2.u10489 = KTree.node D2M8K2.u10473 (nat_lit 22845110) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u10488 from rfl, allE_node, arows10473, irow10489, arows10488]
  all_goals rfl

theorem atot10489 : totK PD2M8K2 D2M8K2.u10489 = [0, 0, 2258051063559, 9640236059681, 12049536121105, 4181377761841, 353091565374, 6052528252] := by
  rw [show D2M8K2.u10489 = KTree.node D2M8K2.u10473 (nat_lit 22845110) (nat_lit 3946446048) (nat_lit 0) D2M8K2.u10488 from rfl, totK_node, atot10473, atot10488]
  decide +kernel

theorem arows10523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10523 = true := by
  rw [show D2M8K2.u10523 = KTree.node D2M8K2.u10507 (nat_lit 22906886) (nat_lit 3862859138) (nat_lit 0) D2M8K2.u10522 from rfl, allE_node, arows10507, irow10523, arows10522]
  all_goals rfl

theorem atot10523 : totK PD2M8K2 D2M8K2.u10523 = [0, 1973920194057, 8811466517111, 12062950095224, 5092312952400, 597390581342, 15707817927, 0] := by
  rw [show D2M8K2.u10523 = KTree.node D2M8K2.u10507 (nat_lit 22906886) (nat_lit 3862859138) (nat_lit 0) D2M8K2.u10522 from rfl, totK_node, atot10507, atot10522]
  decide +kernel

theorem arows10554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10554 = true := by
  rw [show D2M8K2.u10554 = KTree.node D2M8K2.u10538 (nat_lit 22948592) (nat_lit 3691258453) (nat_lit 0) D2M8K2.u10553 from rfl, allE_node, arows10538, irow10554, arows10553]
  all_goals rfl

theorem atot10554 : totK PD2M8K2 D2M8K2.u10554 = [0, 1998135784402, 8773806853819, 12142928384704, 5485838795121, 713340856825, 19209646827, 0] := by
  rw [show D2M8K2.u10554 = KTree.node D2M8K2.u10538 (nat_lit 22948592) (nat_lit 3691258453) (nat_lit 0) D2M8K2.u10553 from rfl, totK_node, atot10538, atot10553]
  decide +kernel

theorem arows10586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10586 = true := by
  rw [show D2M8K2.u10586 = KTree.node D2M8K2.u10570 (nat_lit 22984240) (nat_lit 3354497016) (nat_lit 0) D2M8K2.u10585 from rfl, allE_node, arows10570, irow10586, arows10585]
  all_goals rfl

theorem atot10586 : totK PD2M8K2 D2M8K2.u10586 = [0, 1651658917354, 8257804859273, 12607397387426, 5726308790833, 534099137440, 4830149413, 0] := by
  rw [show D2M8K2.u10586 = KTree.node D2M8K2.u10570 (nat_lit 22984240) (nat_lit 3354497016) (nat_lit 0) D2M8K2.u10585 from rfl, totK_node, atot10570, atot10585]
  decide +kernel

theorem arows10617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10617 = true := by
  rw [show D2M8K2.u10617 = KTree.node D2M8K2.u10601 (nat_lit 23032628) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u10616 from rfl, allE_node, arows10601, irow10617, arows10616]
  all_goals rfl

theorem atot10617 : totK PD2M8K2 D2M8K2.u10617 = [0, 2036865665311, 8741824026132, 11930060010396, 5420766095016, 657799631198, 17898111484, 0] := by
  rw [show D2M8K2.u10617 = KTree.node D2M8K2.u10601 (nat_lit 23032628) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u10616 from rfl, totK_node, atot10601, atot10616]
  decide +kernel

theorem arows10650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10650 = true := by
  rw [show D2M8K2.u10650 = KTree.node D2M8K2.u10634 (nat_lit 23067760) (nat_lit 3445111236) (nat_lit 0) D2M8K2.u10649 from rfl, allE_node, arows10634, irow10650, arows10649]
  all_goals rfl

theorem atot10650 : totK PD2M8K2 D2M8K2.u10650 = [0, 2102355608136, 9077187694242, 12118915180044, 4890583021688, 442309049284, 5858862459, 0] := by
  rw [show D2M8K2.u10650 = KTree.node D2M8K2.u10634 (nat_lit 23067760) (nat_lit 3445111236) (nat_lit 0) D2M8K2.u10649 from rfl, totK_node, atot10634, atot10649]
  decide +kernel

theorem arows10681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10681 = true := by
  rw [show D2M8K2.u10681 = KTree.node D2M8K2.u10665 (nat_lit 23153244) (nat_lit 3108171929) (nat_lit 0) D2M8K2.u10680 from rfl, allE_node, arows10665, irow10681, arows10680]
  all_goals rfl

theorem atot10681 : totK PD2M8K2 D2M8K2.u10681 = [0, 0, 2963086874887, 11308182972028, 11287989046517, 2591522951177, 133630773038, 1209030869] := by
  rw [show D2M8K2.u10681 = KTree.node D2M8K2.u10665 (nat_lit 23153244) (nat_lit 3108171929) (nat_lit 0) D2M8K2.u10680 from rfl, totK_node, atot10665, atot10680]
  decide +kernel

theorem arows10713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10713 = true := by
  rw [show D2M8K2.u10713 = KTree.node D2M8K2.u10697 (nat_lit 23199793) (nat_lit 1377641046) (nat_lit 0) D2M8K2.u10712 from rfl, allE_node, arows10697, irow10713, arows10712]
  all_goals rfl

theorem atot10713 : totK PD2M8K2 D2M8K2.u10713 = [0, 0, 3959001386730, 12754690753535, 10387712793218, 1786252390816, 55205486817, 0] := by
  rw [show D2M8K2.u10713 = KTree.node D2M8K2.u10697 (nat_lit 23199793) (nat_lit 1377641046) (nat_lit 0) D2M8K2.u10712 from rfl, totK_node, atot10697, atot10712]
  decide +kernel

theorem arows10744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10744 = true := by
  rw [show D2M8K2.u10744 = KTree.node D2M8K2.u10728 (nat_lit 23284927) (nat_lit 2199441423) (nat_lit 0) D2M8K2.u10743 from rfl, allE_node, arows10728, irow10744, arows10743]
  all_goals rfl

theorem atot10744 : totK PD2M8K2 D2M8K2.u10744 = [0, 0, 3335070188634, 11966515250092, 11202315063039, 2151383446733, 71044863677, 0] := by
  rw [show D2M8K2.u10744 = KTree.node D2M8K2.u10728 (nat_lit 23284927) (nat_lit 2199441423) (nat_lit 0) D2M8K2.u10743 from rfl, totK_node, atot10728, atot10743]
  decide +kernel

theorem arows10779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10779 = true := by
  rw [show D2M8K2.u10779 = KTree.node D2M8K2.u10763 (nat_lit 23344422) (nat_lit 3818243344) (nat_lit 0) D2M8K2.u10778 from rfl, allE_node, arows10763, irow10779, arows10778]
  all_goals rfl

theorem atot10779 : totK PD2M8K2 D2M8K2.u10779 = [0, 1713929917221, 6330805821321, 8854908628752, 7942096598077, 3239101363664, 329558097425, 6115358396] := by
  rw [show D2M8K2.u10779 = KTree.node D2M8K2.u10763 (nat_lit 23344422) (nat_lit 3818243344) (nat_lit 0) D2M8K2.u10778 from rfl, totK_node, atot10763, atot10778]
  decide +kernel

theorem arows10810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10810 = true := by
  rw [show D2M8K2.u10810 = KTree.node D2M8K2.u10794 (nat_lit 23435654) (nat_lit 3911505399) (nat_lit 0) D2M8K2.u10809 from rfl, allE_node, arows10794, irow10810, arows10809]
  all_goals rfl

theorem atot10810 : totK PD2M8K2 D2M8K2.u10810 = [0, 2002704021271, 9114072609701, 12653176029314, 4783337693741, 323792728550, 1369150432, 0] := by
  rw [show D2M8K2.u10810 = KTree.node D2M8K2.u10794 (nat_lit 23435654) (nat_lit 3911505399) (nat_lit 0) D2M8K2.u10809 from rfl, totK_node, atot10794, atot10809]
  decide +kernel

theorem arows10842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10842 = true := by
  rw [show D2M8K2.u10842 = KTree.node D2M8K2.u10826 (nat_lit 23466789) (nat_lit 1406107179) (nat_lit 0) D2M8K2.u10841 from rfl, allE_node, arows10826, irow10842, arows10841]
  all_goals rfl

theorem atot10842 : totK PD2M8K2 D2M8K2.u10842 = [0, 1370038617928, 6700114320965, 11646246565451, 7799402673020, 1479627023945, 50576159417, 0] := by
  rw [show D2M8K2.u10842 = KTree.node D2M8K2.u10826 (nat_lit 23466789) (nat_lit 1406107179) (nat_lit 0) D2M8K2.u10841 from rfl, totK_node, atot10826, atot10841]
  decide +kernel

theorem arows10873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10873 = true := by
  rw [show D2M8K2.u10873 = KTree.node D2M8K2.u10857 (nat_lit 23504000) (nat_lit 2117396566) (nat_lit 512) D2M8K2.u10872 from rfl, allE_node, arows10857, irow10873, arows10872]
  all_goals rfl

theorem atot10873 : totK PD2M8K2 D2M8K2.u10873 = [0, 2002360983908, 8914316910276, 12301285704538, 5192797325650, 471016962800, 6601594569, 0] := by
  rw [show D2M8K2.u10873 = KTree.node D2M8K2.u10857 (nat_lit 23504000) (nat_lit 2117396566) (nat_lit 512) D2M8K2.u10872 from rfl, totK_node, atot10857, atot10872]
  decide +kernel

theorem arows10906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10906 = true := by
  rw [show D2M8K2.u10906 = KTree.node D2M8K2.u10890 (nat_lit 23548595) (nat_lit 2337647797) (nat_lit 0) D2M8K2.u10905 from rfl, allE_node, arows10890, irow10906, arows10905]
  all_goals rfl

theorem atot10906 : totK PD2M8K2 D2M8K2.u10906 = [0, 1703251355743, 8017112184499, 12124447558112, 6131015644538, 768461109551, 19065934916, 0] := by
  rw [show D2M8K2.u10906 = KTree.node D2M8K2.u10890 (nat_lit 23548595) (nat_lit 2337647797) (nat_lit 0) D2M8K2.u10905 from rfl, totK_node, atot10890, atot10905]
  decide +kernel

theorem arows10937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10937 = true := by
  rw [show D2M8K2.u10937 = KTree.node D2M8K2.u10921 (nat_lit 23622746) (nat_lit 4057403736) (nat_lit 0) D2M8K2.u10936 from rfl, allE_node, arows10921, irow10937, arows10936]
  all_goals rfl

theorem atot10937 : totK PD2M8K2 D2M8K2.u10937 = [442400928062, 2266269326406, 6783527178398, 11284933801303, 6894055928273, 1051906140744, 32872698681, 0] := by
  rw [show D2M8K2.u10937 = KTree.node D2M8K2.u10921 (nat_lit 23622746) (nat_lit 4057403736) (nat_lit 0) D2M8K2.u10936 from rfl, totK_node, atot10921, atot10936]
  decide +kernel

theorem arows10969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10969 = true := by
  rw [show D2M8K2.u10969 = KTree.node D2M8K2.u10953 (nat_lit 23907487) (nat_lit 992604370) (nat_lit 0) D2M8K2.u10968 from rfl, allE_node, arows10953, irow10969, arows10968]
  all_goals rfl

theorem atot10969 : totK PD2M8K2 D2M8K2.u10969 = [2038665478346, 9170579184171, 12377782565488, 4584362570459, 324238970559, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10969 = KTree.node D2M8K2.u10953 (nat_lit 23907487) (nat_lit 992604370) (nat_lit 0) D2M8K2.u10968 from rfl, totK_node, atot10953, atot10968]
  decide +kernel

theorem arows11000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11000 = true := by
  rw [show D2M8K2.u11000 = KTree.node D2M8K2.u10984 (nat_lit 23989977) (nat_lit 1256586072) (nat_lit 0) D2M8K2.u10999 from rfl, allE_node, arows10984, irow11000, arows10999]
  all_goals rfl

theorem atot11000 : totK PD2M8K2 D2M8K2.u11000 = [1598617840249, 7956659500581, 12308163971360, 6002568597643, 740715962653, 18797058808, 0, 0] := by
  rw [show D2M8K2.u11000 = KTree.node D2M8K2.u10984 (nat_lit 23989977) (nat_lit 1256586072) (nat_lit 0) D2M8K2.u10999 from rfl, totK_node, atot10984, atot10999]
  decide +kernel

theorem arows11034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11034 = true := by
  rw [show D2M8K2.u11034 = KTree.node D2M8K2.u11018 (nat_lit 24028999) (nat_lit 2327385968) (nat_lit 0) D2M8K2.u11033 from rfl, allE_node, arows11018, irow11034, arows11033]
  all_goals rfl

theorem atot11034 : totK PD2M8K2 D2M8K2.u11034 = [1983250488188, 8748615147176, 12050626373737, 5342218640530, 603395231737, 14345316470, 0, 0] := by
  rw [show D2M8K2.u11034 = KTree.node D2M8K2.u11018 (nat_lit 24028999) (nat_lit 2327385968) (nat_lit 0) D2M8K2.u11033 from rfl, totK_node, atot11018, atot11033]
  decide +kernel

theorem arows11065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11065 = true := by
  rw [show D2M8K2.u11065 = KTree.node D2M8K2.u11049 (nat_lit 24064466) (nat_lit 4000871149) (nat_lit 0) D2M8K2.u11064 from rfl, allE_node, arows11049, irow11065, arows11064]
  all_goals rfl

theorem atot11065 : totK PD2M8K2 D2M8K2.u11065 = [2030540531638, 8960956594686, 12246537442884, 5047515611821, 455665757895, 5858862459, 0, 0] := by
  rw [show D2M8K2.u11065 = KTree.node D2M8K2.u11049 (nat_lit 24064466) (nat_lit 4000871149) (nat_lit 0) D2M8K2.u11064 from rfl, totK_node, atot11049, atot11064]
  decide +kernel

theorem arows11097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11097 = true := by
  rw [show D2M8K2.u11097 = KTree.node D2M8K2.u11081 (nat_lit 24108236) (nat_lit 3437260527) (nat_lit 0) D2M8K2.u11096 from rfl, allE_node, arows11081, irow11097, arows11096]
  all_goals rfl

theorem atot11097 : totK PD2M8K2 D2M8K2.u11097 = [1652014843316, 7772000119234, 12003197952461, 6362406349849, 801611087859, 13328224767, 0, 0] := by
  rw [show D2M8K2.u11097 = KTree.node D2M8K2.u11081 (nat_lit 24108236) (nat_lit 3437260527) (nat_lit 0) D2M8K2.u11096 from rfl, totK_node, atot11081, atot11096]
  decide +kernel

theorem arows11128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11128 = true := by
  rw [show D2M8K2.u11128 = KTree.node D2M8K2.u11112 (nat_lit 24149801) (nat_lit 858945031) (nat_lit 0) D2M8K2.u11127 from rfl, allE_node, arows11112, irow11128, arows11127]
  all_goals rfl

theorem atot11128 : totK PD2M8K2 D2M8K2.u11128 = [0, 2512289254370, 10181116053532, 11804557687095, 3555260275779, 273910657020, 1369150432, 0] := by
  rw [show D2M8K2.u11128 = KTree.node D2M8K2.u11112 (nat_lit 24149801) (nat_lit 858945031) (nat_lit 0) D2M8K2.u11127 from rfl, totK_node, atot11112, atot11127]
  decide +kernel

theorem arows11161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11161 = true := by
  rw [show D2M8K2.u11161 = KTree.node D2M8K2.u11145 (nat_lit 24233521) (nat_lit 1510266876) (nat_lit 0) D2M8K2.u11160 from rfl, allE_node, arows11145, irow11161, arows11160]
  all_goals rfl

theorem atot11161 : totK PD2M8K2 D2M8K2.u11161 = [0, 3001680154831, 11277092534903, 11659512658511, 2672525196965, 101735861280, 0, 0] := by
  rw [show D2M8K2.u11161 = KTree.node D2M8K2.u11145 (nat_lit 24233521) (nat_lit 1510266876) (nat_lit 0) D2M8K2.u11160 from rfl, totK_node, atot11145, atot11160]
  decide +kernel

theorem arows11192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11192 = true := by
  rw [show D2M8K2.u11192 = KTree.node D2M8K2.u11176 (nat_lit 24307374) (nat_lit 3846508441) (nat_lit 0) D2M8K2.u11191 from rfl, allE_node, arows11176, irow11192, arows11191]
  all_goals rfl

theorem atot11192 : totK PD2M8K2 D2M8K2.u11192 = [0, 3400110429768, 12018077520020, 11135578115071, 2127249307408, 65730020013, 0, 0] := by
  rw [show D2M8K2.u11192 = KTree.node D2M8K2.u11176 (nat_lit 24307374) (nat_lit 3846508441) (nat_lit 0) D2M8K2.u11191 from rfl, totK_node, atot11176, atot11191]
  decide +kernel

theorem arows11224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11224 = true := by
  rw [show D2M8K2.u11224 = KTree.node D2M8K2.u11208 (nat_lit 24432680) (nat_lit 3545211341) (nat_lit 0) D2M8K2.u11223 from rfl, allE_node, arows11208, irow11224, arows11223]
  all_goals rfl

theorem atot11224 : totK PD2M8K2 D2M8K2.u11224 = [2041937521767, 8145032841228, 11210317546735, 6398662517853, 1113193292852, 33598280809, 0, 0] := by
  rw [show D2M8K2.u11224 = KTree.node D2M8K2.u11208 (nat_lit 24432680) (nat_lit 3545211341) (nat_lit 0) D2M8K2.u11223 from rfl, totK_node, atot11208, atot11223]
  decide +kernel

theorem arows11255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11255 = true := by
  rw [show D2M8K2.u11255 = KTree.node D2M8K2.u11239 (nat_lit 24462182) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u11254 from rfl, allE_node, arows11239, irow11255, arows11254]
  all_goals rfl

theorem atot11255 : totK PD2M8K2 D2M8K2.u11255 = [1162574705268, 6201907725586, 11614990954453, 8252288819339, 1631308991824, 58018127943, 0, 0] := by
  rw [show D2M8K2.u11255 = KTree.node D2M8K2.u11239 (nat_lit 24462182) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u11254 from rfl, totK_node, atot11239, atot11254]
  decide +kernel

theorem arows11291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11291 = true := by
  rw [show D2M8K2.u11291 = KTree.node D2M8K2.u11275 (nat_lit 24496320) (nat_lit 3565159046) (nat_lit 0) D2M8K2.u11290 from rfl, allE_node, arows11275, irow11291, arows11290]
  all_goals rfl

theorem atot11291 : totK PD2M8K2 D2M8K2.u11291 = [1656329259307, 8059656208096, 12214954034162, 6032609493252, 756090339453, 18797058808, 0, 0] := by
  rw [show D2M8K2.u11291 = KTree.node D2M8K2.u11275 (nat_lit 24496320) (nat_lit 3565159046) (nat_lit 0) D2M8K2.u11290 from rfl, totK_node, atot11275, atot11290]
  decide +kernel

theorem arows11322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11322 = true := by
  rw [show D2M8K2.u11322 = KTree.node D2M8K2.u11306 (nat_lit 24533643) (nat_lit 2992324229) (nat_lit 0) D2M8K2.u11321 from rfl, allE_node, arows11306, irow11322, arows11321]
  all_goals rfl

theorem atot11322 : totK PD2M8K2 D2M8K2.u11322 = [1673192223136, 7990312257601, 12200763414891, 6137007436749, 764987782214, 19065934916, 0, 0] := by
  rw [show D2M8K2.u11322 = KTree.node D2M8K2.u11306 (nat_lit 24533643) (nat_lit 2992324229) (nat_lit 0) D2M8K2.u11321 from rfl, totK_node, atot11306, atot11321]
  decide +kernel

theorem arows11354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11354 = true := by
  rw [show D2M8K2.u11354 = KTree.node D2M8K2.u11338 (nat_lit 24567879) (nat_lit 2440785571) (nat_lit 0) D2M8K2.u11353 from rfl, allE_node, arows11338, irow11354, arows11353]
  all_goals rfl

theorem atot11354 : totK PD2M8K2 D2M8K2.u11354 = [1944303038449, 8705981496770, 12332467368058, 5342902810044, 502845922348, 6115358396, 0, 0] := by
  rw [show D2M8K2.u11354 = KTree.node D2M8K2.u11338 (nat_lit 24567879) (nat_lit 2440785571) (nat_lit 0) D2M8K2.u11353 from rfl, totK_node, atot11338, atot11353]
  decide +kernel

theorem arows11385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11385 = true := by
  rw [show D2M8K2.u11385 = KTree.node D2M8K2.u11369 (nat_lit 24617693) (nat_lit 2328645645) (nat_lit 0) D2M8K2.u11384 from rfl, allE_node, arows11369, irow11385, arows11384]
  all_goals rfl

theorem atot11385 : totK PD2M8K2 D2M8K2.u11385 = [1326121685222, 7242925228453, 12343294621054, 6958022729171, 1027081178206, 31562413104, 0, 0] := by
  rw [show D2M8K2.u11385 = KTree.node D2M8K2.u11369 (nat_lit 24617693) (nat_lit 2328645645) (nat_lit 0) D2M8K2.u11384 from rfl, totK_node, atot11369, atot11384]
  decide +kernel

theorem arows11418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11418 = true := by
  rw [show D2M8K2.u11418 = KTree.node D2M8K2.u11402 (nat_lit 24694148) (nat_lit 2222174867) (nat_lit 0) D2M8K2.u11417 from rfl, allE_node, arows11402, irow11418, arows11417]
  all_goals rfl

theorem atot11418 : totK PD2M8K2 D2M8K2.u11418 = [0, 1668324019370, 7830469129067, 11754536714736, 6356411652201, 1117537722631, 47116249314, 0] := by
  rw [show D2M8K2.u11418 = KTree.node D2M8K2.u11402 (nat_lit 24694148) (nat_lit 2222174867) (nat_lit 0) D2M8K2.u11417 from rfl, totK_node, atot11402, atot11417]
  decide +kernel

theorem arows11449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11449 = true := by
  rw [show D2M8K2.u11449 = KTree.node D2M8K2.u11433 (nat_lit 24725573) (nat_lit 2352245897) (nat_lit 0) D2M8K2.u11448 from rfl, allE_node, arows11433, irow11449, arows11448]
  all_goals rfl

theorem atot11449 : totK PD2M8K2 D2M8K2.u11449 = [0, 1992667074800, 8800610855186, 12074060481367, 5292974194619, 579027844130, 10531122277, 0] := by
  rw [show D2M8K2.u11449 = KTree.node D2M8K2.u11433 (nat_lit 24725573) (nat_lit 2352245897) (nat_lit 0) D2M8K2.u11448 from rfl, totK_node, atot11433, atot11448]
  decide +kernel

theorem arows11481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11481 = true := by
  rw [show D2M8K2.u11481 = KTree.node D2M8K2.u11465 (nat_lit 24769666) (nat_lit 3923195380) (nat_lit 0) D2M8K2.u11480 from rfl, allE_node, arows11465, irow11481, arows11480]
  all_goals rfl

theorem atot11481 : totK PD2M8K2 D2M8K2.u11481 = [0, 1993196510098, 8909630004368, 12197105190123, 5160798615758, 494694437416, 6546549506, 0] := by
  rw [show D2M8K2.u11481 = KTree.node D2M8K2.u11465 (nat_lit 24769666) (nat_lit 3923195380) (nat_lit 0) D2M8K2.u11480 from rfl, totK_node, atot11465, atot11480]
  decide +kernel

theorem arows11512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11512 = true := by
  rw [show D2M8K2.u11512 = KTree.node D2M8K2.u11496 (nat_lit 24807058) (nat_lit 4038603163) (nat_lit 0) D2M8K2.u11511 from rfl, allE_node, arows11496, irow11512, arows11511]
  all_goals rfl

theorem atot11512 : totK PD2M8K2 D2M8K2.u11512 = [0, 2038191485601, 8952220408136, 12160631396739, 5066386897871, 479085047982, 6624648996, 0] := by
  rw [show D2M8K2.u11512 = KTree.node D2M8K2.u11496 (nat_lit 24807058) (nat_lit 4038603163) (nat_lit 0) D2M8K2.u11511 from rfl, totK_node, atot11496, atot11511]
  decide +kernel

theorem arows11546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11546 = true := by
  rw [show D2M8K2.u11546 = KTree.node D2M8K2.u11530 (nat_lit 24850735) (nat_lit 2325511650) (nat_lit 0) D2M8K2.u11545 from rfl, allE_node, arows11530, irow11546, arows11545]
  all_goals rfl

theorem atot11546 : totK PD2M8K2 D2M8K2.u11546 = [0, 1666200742509, 8254159832511, 12675836773070, 5775102733105, 486040158247, 2753446244, 0] := by
  rw [show D2M8K2.u11546 = KTree.node D2M8K2.u11530 (nat_lit 24850735) (nat_lit 2325511650) (nat_lit 0) D2M8K2.u11545 from rfl, totK_node, atot11530, atot11545]
  decide +kernel

theorem arows11577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11577 = true := by
  rw [show D2M8K2.u11577 = KTree.node D2M8K2.u11561 (nat_lit 24894870) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u11576 from rfl, allE_node, arows11561, irow11577, arows11576]
  all_goals rfl

theorem atot11577 : totK PD2M8K2 D2M8K2.u11577 = [1975776787817, 7851454581766, 9916783209465, 5660372685826, 2670393354811, 430702926894, 10866219959, 0] := by
  rw [show D2M8K2.u11577 = KTree.node D2M8K2.u11561 (nat_lit 24894870) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u11576 from rfl, totK_node, atot11561, atot11576]
  decide +kernel

theorem arows11609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11609 = true := by
  rw [show D2M8K2.u11609 = KTree.node D2M8K2.u11593 (nat_lit 24936131) (nat_lit 2693220863) (nat_lit 0) D2M8K2.u11608 from rfl, allE_node, arows11593, irow11609, arows11608]
  all_goals rfl

theorem atot11609 : totK PD2M8K2 D2M8K2.u11609 = [2000318257803, 8886394084300, 12096386884029, 5205898485098, 767779867285, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11609 = KTree.node D2M8K2.u11593 (nat_lit 24936131) (nat_lit 2693220863) (nat_lit 0) D2M8K2.u11608 from rfl, totK_node, atot11593, atot11608]
  decide +kernel

theorem arows11640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11640 = true := by
  rw [show D2M8K2.u11640 = KTree.node D2M8K2.u11624 (nat_lit 24967962) (nat_lit 3484365061) (nat_lit 0) D2M8K2.u11639 from rfl, allE_node, arows11624, irow11640, arows11639]
  all_goals rfl

theorem atot11640 : totK PD2M8K2 D2M8K2.u11640 = [2052235371532, 8251075656236, 11311585223440, 6286686385049, 1016230423551, 21096254089, 0, 0] := by
  rw [show D2M8K2.u11640 = KTree.node D2M8K2.u11624 (nat_lit 24967962) (nat_lit 3484365061) (nat_lit 0) D2M8K2.u11639 from rfl, totK_node, atot11624, atot11639]
  decide +kernel

theorem arows11673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11673 = true := by
  rw [show D2M8K2.u11673 = KTree.node D2M8K2.u11657 (nat_lit 25003757) (nat_lit 1673353523) (nat_lit 0) D2M8K2.u11672 from rfl, allE_node, arows11657, irow11673, arows11672]
  all_goals rfl

theorem atot11673 : totK PD2M8K2 D2M8K2.u11673 = [1560730111018, 7697179141486, 12274001420330, 6287379826767, 764104520762, 18797058808, 0, 0] := by
  rw [show D2M8K2.u11673 = KTree.node D2M8K2.u11657 (nat_lit 25003757) (nat_lit 1673353523) (nat_lit 0) D2M8K2.u11672 from rfl, totK_node, atot11657, atot11672]
  decide +kernel

theorem arows11704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11704 = true := by
  rw [show D2M8K2.u11704 = KTree.node D2M8K2.u11688 (nat_lit 25081585) (nat_lit 1406327514) (nat_lit 0) D2M8K2.u11703 from rfl, allE_node, arows11688, irow11704, arows11703]
  all_goals rfl

theorem atot11704 : totK PD2M8K2 D2M8K2.u11704 = [1757813312456, 8539679437882, 12546988751902, 5398590602298, 502902852080, 6115358396, 0, 0] := by
  rw [show D2M8K2.u11704 = KTree.node D2M8K2.u11688 (nat_lit 25081585) (nat_lit 1406327514) (nat_lit 0) D2M8K2.u11703 from rfl, totK_node, atot11688, atot11703]
  decide +kernel

theorem arows11736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11736 = true := by
  rw [show D2M8K2.u11736 = KTree.node D2M8K2.u11720 (nat_lit 25129664) (nat_lit 3012977573) (nat_lit 0) D2M8K2.u11735 from rfl, allE_node, arows11720, irow11736, arows11735]
  all_goals rfl

theorem atot11736 : totK PD2M8K2 D2M8K2.u11736 = [427983732745, 4837712277144, 12443006590370, 9373902919249, 1523743843173, 44654750197, 0, 0] := by
  rw [show D2M8K2.u11736 = KTree.node D2M8K2.u11720 (nat_lit 25129664) (nat_lit 3012977573) (nat_lit 0) D2M8K2.u11735 from rfl, totK_node, atot11720, atot11735]
  decide +kernel

theorem arows11767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11767 = true := by
  rw [show D2M8K2.u11767 = KTree.node D2M8K2.u11751 (nat_lit 25177307) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u11766 from rfl, allE_node, arows11751, irow11767, arows11766]
  all_goals rfl

theorem atot11767 : totK PD2M8K2 D2M8K2.u11767 = [0, 2083545171736, 9548647446794, 12623422725560, 4136808571318, 251296746508, 1275377855, 0] := by
  rw [show D2M8K2.u11767 = KTree.node D2M8K2.u11751 (nat_lit 25177307) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u11766 from rfl, totK_node, atot11751, atot11766]
  decide +kernel

theorem arows11802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11802 = true := by
  rw [show D2M8K2.u11802 = KTree.node D2M8K2.u11786 (nat_lit 25225183) (nat_lit 2079551004) (nat_lit 0) D2M8K2.u11801 from rfl, allE_node, arows11786, irow11802, arows11801]
  all_goals rfl

theorem atot11802 : totK PD2M8K2 D2M8K2.u11802 = [0, 2397754309302, 9912461586357, 12065230535885, 3993002322445, 268256200894, 1206465782, 0] := by
  rw [show D2M8K2.u11802 = KTree.node D2M8K2.u11786 (nat_lit 25225183) (nat_lit 2079551004) (nat_lit 0) D2M8K2.u11801 from rfl, totK_node, atot11786, atot11801]
  decide +kernel

theorem arows11833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11833 = true := by
  rw [show D2M8K2.u11833 = KTree.node D2M8K2.u11817 (nat_lit 25305398) (nat_lit 3920759378) (nat_lit 0) D2M8K2.u11832 from rfl, allE_node, arows11817, irow11833, arows11832]
  all_goals rfl

theorem atot11833 : totK PD2M8K2 D2M8K2.u11833 = [0, 2029484991902, 8966866973152, 11946606674855, 4877329312956, 602999853546, 18694047957, 0] := by
  rw [show D2M8K2.u11833 = KTree.node D2M8K2.u11817 (nat_lit 25305398) (nat_lit 3920759378) (nat_lit 0) D2M8K2.u11832 from rfl, totK_node, atot11817, atot11832]
  decide +kernel

theorem arows11865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11865 = true := by
  rw [show D2M8K2.u11865 = KTree.node D2M8K2.u11849 (nat_lit 25347122) (nat_lit 3899463463) (nat_lit 0) D2M8K2.u11864 from rfl, allE_node, arows11849, irow11865, arows11864]
  all_goals rfl

theorem atot11865 : totK PD2M8K2 D2M8K2.u11865 = [1107237586083, 5201879835495, 9789072255774, 9132862603400, 3120335517813, 269989918758, 4779662215, 0] := by
  rw [show D2M8K2.u11865 = KTree.node D2M8K2.u11849 (nat_lit 25347122) (nat_lit 3899463463) (nat_lit 0) D2M8K2.u11864 from rfl, totK_node, atot11849, atot11864]
  decide +kernel

theorem arows11896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11896 = true := by
  rw [show D2M8K2.u11896 = KTree.node D2M8K2.u11880 (nat_lit 25412104) (nat_lit 3412863596) (nat_lit 0) D2M8K2.u11895 from rfl, allE_node, arows11880, irow11896, arows11895]
  all_goals rfl

theorem atot11896 : totK PD2M8K2 D2M8K2.u11896 = [1966658366431, 8939649157831, 12538478448785, 4903599753309, 355150091045, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11896 = KTree.node D2M8K2.u11880 (nat_lit 25412104) (nat_lit 3412863596) (nat_lit 0) D2M8K2.u11895 from rfl, totK_node, atot11880, atot11895]
  decide +kernel

theorem arows11929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11929 = true := by
  rw [show D2M8K2.u11929 = KTree.node D2M8K2.u11913 (nat_lit 25450685) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u11928 from rfl, allE_node, arows11913, irow11929, arows11928]
  all_goals rfl

theorem atot11929 : totK PD2M8K2 D2M8K2.u11929 = [1315881643474, 6644577661180, 11493842404471, 7832112723454, 1597436352679, 58018127943, 0, 0] := by
  rw [show D2M8K2.u11929 = KTree.node D2M8K2.u11913 (nat_lit 25450685) (nat_lit 2326292714) (nat_lit 0) D2M8K2.u11928 from rfl, totK_node, atot11913, atot11928]
  decide +kernel

theorem arows11960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11960 = true := by
  rw [show D2M8K2.u11960 = KTree.node D2M8K2.u11944 (nat_lit 25523603) (nat_lit 2739261758) (nat_lit 0) D2M8K2.u11959 from rfl, allE_node, arows11944, irow11960, arows11959]
  all_goals rfl

theorem atot11960 : totK PD2M8K2 D2M8K2.u11960 = [1694090630267, 8149222031029, 12319040985741, 5884304028752, 673465092880, 15398727635, 0, 0] := by
  rw [show D2M8K2.u11960 = KTree.node D2M8K2.u11944 (nat_lit 25523603) (nat_lit 2739261758) (nat_lit 0) D2M8K2.u11959 from rfl, totK_node, atot11944, atot11959]
  decide +kernel

theorem arows11992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11992 = true := by
  rw [show D2M8K2.u11992 = KTree.node D2M8K2.u11976 (nat_lit 25558324) (nat_lit 3620226531) (nat_lit 0) D2M8K2.u11991 from rfl, allE_node, arows11976, irow11992, arows11991]
  all_goals rfl

theorem atot11992 : totK PD2M8K2 D2M8K2.u11992 = [2033977454397, 9140248579133, 12381394025188, 4842979004488, 393118672302, 4805451294, 0, 0] := by
  rw [show D2M8K2.u11992 = KTree.node D2M8K2.u11976 (nat_lit 25558324) (nat_lit 3620226531) (nat_lit 0) D2M8K2.u11991 from rfl, totK_node, atot11976, atot11991]
  decide +kernel

theorem arows12023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12023 = true := by
  rw [show D2M8K2.u12023 = KTree.node D2M8K2.u12007 (nat_lit 25601503) (nat_lit 2341993973) (nat_lit 0) D2M8K2.u12022 from rfl, allE_node, arows12007, irow12023, arows12022]
  all_goals rfl

theorem atot12023 : totK PD2M8K2 D2M8K2.u12023 = [1658316920461, 7913528394609, 12223940728767, 6254685744959, 722635736400, 11218804606, 0, 0] := by
  rw [show D2M8K2.u12023 = KTree.node D2M8K2.u12007 (nat_lit 25601503) (nat_lit 2341993973) (nat_lit 0) D2M8K2.u12022 from rfl, totK_node, atot12007, atot12022]
  decide +kernel

theorem arows12057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12057 = true := by
  rw [show D2M8K2.u12057 = KTree.node D2M8K2.u12041 (nat_lit 25644921) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u12056 from rfl, allE_node, arows12041, irow12057, arows12056]
  all_goals rfl

theorem atot12057 : totK PD2M8K2 D2M8K2.u12057 = [0, 2122446244173, 9691801959445, 12415991005346, 3877445598146, 226963635683, 1310517177, 0] := by
  rw [show D2M8K2.u12057 = KTree.node D2M8K2.u12041 (nat_lit 25644921) (nat_lit 1903903263) (nat_lit 0) D2M8K2.u12056 from rfl, totK_node, atot12041, atot12056]
  decide +kernel

theorem arows12088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12088 = true := by
  rw [show D2M8K2.u12088 = KTree.node D2M8K2.u12072 (nat_lit 25687906) (nat_lit 3208673382) (nat_lit 0) D2M8K2.u12087 from rfl, allE_node, arows12072, irow12088, arows12087]
  all_goals rfl

theorem atot12088 : totK PD2M8K2 D2M8K2.u12088 = [0, 3278366477456, 11545580289906, 11257637310135, 2779333047757, 119342414793, 0, 0] := by
  rw [show D2M8K2.u12088 = KTree.node D2M8K2.u12072 (nat_lit 25687906) (nat_lit 3208673382) (nat_lit 0) D2M8K2.u12087 from rfl, totK_node, atot12072, atot12087]
  decide +kernel

theorem arows12120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12120 = true := by
  rw [show D2M8K2.u12120 = KTree.node D2M8K2.u12104 (nat_lit 25786336) (nat_lit 1726767959) (nat_lit 0) D2M8K2.u12119 from rfl, allE_node, arows12104, irow12120, arows12119]
  all_goals rfl

theorem atot12120 : totK PD2M8K2 D2M8K2.u12120 = [0, 1646665077031, 8063758175642, 12236152540583, 5722767886140, 712458993493, 18953862985, 0] := by
  rw [show D2M8K2.u12120 = KTree.node D2M8K2.u12104 (nat_lit 25786336) (nat_lit 1726767959) (nat_lit 0) D2M8K2.u12119 from rfl, totK_node, atot12104, atot12119]
  decide +kernel

theorem arows12151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12151 = true := by
  rw [show D2M8K2.u12151 = KTree.node D2M8K2.u12135 (nat_lit 25820915) (nat_lit 2416712695) (nat_lit 0) D2M8K2.u12150 from rfl, allE_node, arows12135, irow12151, arows12150]
  all_goals rfl

theorem atot12151 : totK PD2M8K2 D2M8K2.u12151 = [0, 2010198736222, 9188805747949, 12353224706628, 4562014690608, 371946196802, 6052528252, 0] := by
  rw [show D2M8K2.u12151 = KTree.node D2M8K2.u12135 (nat_lit 25820915) (nat_lit 2416712695) (nat_lit 0) D2M8K2.u12150 from rfl, totK_node, atot12135, atot12150]
  decide +kernel

theorem arows12184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12184 = true := by
  rw [show D2M8K2.u12184 = KTree.node D2M8K2.u12168 (nat_lit 25888342) (nat_lit 2480157904) (nat_lit 0) D2M8K2.u12183 from rfl, allE_node, arows12168, irow12184, arows12183]
  all_goals rfl

theorem atot12184 : totK PD2M8K2 D2M8K2.u12184 = [2003940924109, 8423425886388, 11355038237025, 5734142719489, 1059020577173, 42153930608, 0, 0] := by
  rw [show D2M8K2.u12184 = KTree.node D2M8K2.u12168 (nat_lit 25888342) (nat_lit 2480157904) (nat_lit 0) D2M8K2.u12183 from rfl, totK_node, atot12168, atot12183]
  decide +kernel

theorem arows12215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12215 = true := by
  rw [show D2M8K2.u12215 = KTree.node D2M8K2.u12199 (nat_lit 25929029) (nat_lit 2315076869) (nat_lit 0) D2M8K2.u12214 from rfl, allE_node, arows12199, irow12215, arows12214]
  all_goals rfl

theorem atot12215 : totK PD2M8K2 D2M8K2.u12215 = [2026914572400, 9196839665620, 12551124023725, 4748461754635, 417552936359, 21385604922, 0, 0] := by
  rw [show D2M8K2.u12215 = KTree.node D2M8K2.u12199 (nat_lit 25929029) (nat_lit 2315076869) (nat_lit 0) D2M8K2.u12214 from rfl, totK_node, atot12199, atot12214]
  decide +kernel

theorem arows12247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12247 = true := by
  rw [show D2M8K2.u12247 = KTree.node D2M8K2.u12231 (nat_lit 25961242) (nat_lit 4021842791) (nat_lit 0) D2M8K2.u12246 from rfl, allE_node, arows12231, irow12247, arows12246]
  all_goals rfl

theorem atot12247 : totK PD2M8K2 D2M8K2.u12247 = [1689069297834, 7378849837630, 11246254565700, 7166927088627, 1381072757461, 36632523021, 0, 0] := by
  rw [show D2M8K2.u12247 = KTree.node D2M8K2.u12231 (nat_lit 25961242) (nat_lit 4021842791) (nat_lit 0) D2M8K2.u12246 from rfl, totK_node, atot12231, atot12246]
  decide +kernel

theorem arows12278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12278 = true := by
  rw [show D2M8K2.u12278 = KTree.node D2M8K2.u12262 (nat_lit 25997234) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u12277 from rfl, allE_node, arows12262, irow12278, arows12277]
  all_goals rfl

theorem atot12278 : totK PD2M8K2 D2M8K2.u12278 = [1590673508962, 7810993196204, 12270318132181, 6201019565317, 760709942803, 18797058808, 0, 0] := by
  rw [show D2M8K2.u12278 = KTree.node D2M8K2.u12262 (nat_lit 25997234) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u12277 from rfl, totK_node, atot12262, atot12277]
  decide +kernel

theorem arows12316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12316 = true := by
  rw [show D2M8K2.u12316 = KTree.node D2M8K2.u12300 (nat_lit 26035977) (nat_lit 1110321614) (nat_lit 0) D2M8K2.u12315 from rfl, allE_node, arows12300, irow12316, arows12315]
  all_goals rfl

theorem atot12316 : totK PD2M8K2 D2M8K2.u12316 = [1720252757066, 7991672104143, 12070406503578, 6151856743730, 771555077402, 19065934916, 0, 0] := by
  rw [show D2M8K2.u12316 = KTree.node D2M8K2.u12300 (nat_lit 26035977) (nat_lit 1110321614) (nat_lit 0) D2M8K2.u12315 from rfl, totK_node, atot12300, atot12315]
  decide +kernel

theorem arows12347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12347 = true := by
  rw [show D2M8K2.u12347 = KTree.node D2M8K2.u12331 (nat_lit 26069306) (nat_lit 4021268430) (nat_lit 0) D2M8K2.u12346 from rfl, allE_node, arows12331, irow12347, arows12346]
  all_goals rfl

theorem atot12347 : totK PD2M8K2 D2M8K2.u12347 = [1160434894226, 7252811329494, 13044994244258, 6602000982036, 670320216771, 7484508828, 0, 0] := by
  rw [show D2M8K2.u12347 = KTree.node D2M8K2.u12331 (nat_lit 26069306) (nat_lit 4021268430) (nat_lit 0) D2M8K2.u12346 from rfl, totK_node, atot12331, atot12346]
  decide +kernel

theorem arows12379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12379 = true := by
  rw [show D2M8K2.u12379 = KTree.node D2M8K2.u12363 (nat_lit 26151338) (nat_lit 2511859258) (nat_lit 0) D2M8K2.u12378 from rfl, allE_node, arows12363, irow12379, arows12378]
  all_goals rfl

theorem atot12379 : totK PD2M8K2 D2M8K2.u12379 = [0, 2076344481860, 9680561106131, 12571179054856, 3924939910965, 243170730532, 1209030869, 0] := by
  rw [show D2M8K2.u12379 = KTree.node D2M8K2.u12363 (nat_lit 26151338) (nat_lit 2511859258) (nat_lit 0) D2M8K2.u12378 from rfl, totK_node, atot12363, atot12378]
  decide +kernel

theorem arows12410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12410 = true := by
  rw [show D2M8K2.u12410 = KTree.node D2M8K2.u12394 (nat_lit 26215005) (nat_lit 1556821885) (nat_lit 0) D2M8K2.u12409 from rfl, allE_node, arows12394, irow12410, arows12409]
  all_goals rfl

theorem atot12410 : totK PD2M8K2 D2M8K2.u12410 = [0, 3515396483763, 12124693713338, 11030403866921, 2173966669282, 64886825524, 0, 0] := by
  rw [show D2M8K2.u12410 = KTree.node D2M8K2.u12394 (nat_lit 26215005) (nat_lit 1556821885) (nat_lit 0) D2M8K2.u12409 from rfl, totK_node, atot12394, atot12409]
  decide +kernel

theorem arows12443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12443 = true := by
  rw [show D2M8K2.u12443 = KTree.node D2M8K2.u12427 (nat_lit 26271000) (nat_lit 3526195808) (nat_lit 0) D2M8K2.u12442 from rfl, allE_node, arows12427, irow12443, arows12442]
  all_goals rfl

theorem atot12443 : totK PD2M8K2 D2M8K2.u12443 = [0, 3282222605960, 11783424117690, 11334990654242, 2363811459070, 78572372441, 0, 0] := by
  rw [show D2M8K2.u12443 = KTree.node D2M8K2.u12427 (nat_lit 26271000) (nat_lit 3526195808) (nat_lit 0) D2M8K2.u12442 from rfl, totK_node, atot12427, atot12442]
  decide +kernel

theorem arows12474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12474 = true := by
  rw [show D2M8K2.u12474 = KTree.node D2M8K2.u12458 (nat_lit 26328520) (nat_lit 3794656059) (nat_lit 0) D2M8K2.u12473 from rfl, allE_node, arows12458, irow12474, arows12473]
  all_goals rfl

theorem atot12474 : totK PD2M8K2 D2M8K2.u12474 = [0, 1961740274118, 9020528148698, 12362936110092, 4700860374188, 452190558943, 6115358396, 0] := by
  rw [show D2M8K2.u12474 = KTree.node D2M8K2.u12458 (nat_lit 26328520) (nat_lit 3794656059) (nat_lit 0) D2M8K2.u12473 from rfl, totK_node, atot12458, atot12473]
  decide +kernel

theorem arows12506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12506 = true := by
  rw [show D2M8K2.u12506 = KTree.node D2M8K2.u12490 (nat_lit 26908931) (nat_lit 1549271017) (nat_lit 0) D2M8K2.u12505 from rfl, allE_node, arows12490, irow12506, arows12505]
  all_goals rfl

theorem atot12506 : totK PD2M8K2 D2M8K2.u12506 = [0, 1931758167230, 9084561134283, 12586368809616, 4614374888644, 321836668178, 1369150432, 0] := by
  rw [show D2M8K2.u12506 = KTree.node D2M8K2.u12490 (nat_lit 26908931) (nat_lit 1549271017) (nat_lit 0) D2M8K2.u12505 from rfl, totK_node, atot12490, atot12505]
  decide +kernel

theorem arows12537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12537 = true := by
  rw [show D2M8K2.u12537 = KTree.node D2M8K2.u12521 (nat_lit 26987625) (nat_lit 1426804665) (nat_lit 0) D2M8K2.u12536 from rfl, allE_node, arows12521, irow12537, arows12536]
  all_goals rfl

theorem atot12537 : totK PD2M8K2 D2M8K2.u12537 = [0, 1818123205222, 8292259442288, 12139563651681, 5650002788586, 662113473038, 18797058808, 0] := by
  rw [show D2M8K2.u12537 = KTree.node D2M8K2.u12521 (nat_lit 26987625) (nat_lit 1426804665) (nat_lit 0) D2M8K2.u12536 from rfl, totK_node, atot12521, atot12536]
  decide +kernel

theorem arows12571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12571 = true := by
  rw [show D2M8K2.u12571 = KTree.node D2M8K2.u12555 (nat_lit 27030630) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u12570 from rfl, allE_node, arows12555, irow12571, arows12570]
  all_goals rfl

theorem atot12571 : totK PD2M8K2 D2M8K2.u12571 = [0, 1648093666119, 8038651963262, 12303009019657, 5886700103914, 694015610164, 19065934916, 0] := by
  rw [show D2M8K2.u12571 = KTree.node D2M8K2.u12555 (nat_lit 27030630) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u12570 from rfl, totK_node, atot12555, atot12570]
  decide +kernel

theorem arows12602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12602 = true := by
  rw [show D2M8K2.u12602 = KTree.node D2M8K2.u12586 (nat_lit 27064667) (nat_lit 1550262871) (nat_lit 0) D2M8K2.u12601 from rfl, allE_node, arows12586, irow12602, arows12601]
  all_goals rfl

theorem atot12602 : totK PD2M8K2 D2M8K2.u12602 = [0, 2000505468204, 8958287237824, 12285476721889, 4909615848077, 456755401573, 6115358396, 0] := by
  rw [show D2M8K2.u12602 = KTree.node D2M8K2.u12586 (nat_lit 27064667) (nat_lit 1550262871) (nat_lit 0) D2M8K2.u12601 from rfl, totK_node, atot12586, atot12601]
  decide +kernel

theorem arows12634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12634 = true := by
  rw [show D2M8K2.u12634 = KTree.node D2M8K2.u12618 (nat_lit 27113335) (nat_lit 2359819404) (nat_lit 0) D2M8K2.u12633 from rfl, allE_node, arows12618, irow12634, arows12633]
  all_goals rfl

theorem atot12634 : totK PD2M8K2 D2M8K2.u12634 = [0, 829385582427, 6316646420576, 12858585137524, 7515849666039, 958421468702, 28663473823, 0] := by
  rw [show D2M8K2.u12634 = KTree.node D2M8K2.u12618 (nat_lit 27113335) (nat_lit 2359819404) (nat_lit 0) D2M8K2.u12633 from rfl, totK_node, atot12618, atot12633]
  decide +kernel

theorem arows12665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12665 = true := by
  rw [show D2M8K2.u12665 = KTree.node D2M8K2.u12649 (nat_lit 27162238) (nat_lit 3922075906) (nat_lit 0) D2M8K2.u12664 from rfl, allE_node, arows12649, irow12665, arows12664]
  all_goals rfl

theorem atot12665 : totK PD2M8K2 D2M8K2.u12665 = [0, 0, 2708028632202, 10824472604088, 11652864734341, 2999266947439, 186934340930, 1369150432] := by
  rw [show D2M8K2.u12665 = KTree.node D2M8K2.u12649 (nat_lit 27162238) (nat_lit 3922075906) (nat_lit 0) D2M8K2.u12664 from rfl, totK_node, atot12649, atot12664]
  decide +kernel

theorem arows12698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12698 = true := by
  rw [show D2M8K2.u12698 = KTree.node D2M8K2.u12682 (nat_lit 27289770) (nat_lit 3659780061) (nat_lit 0) D2M8K2.u12697 from rfl, allE_node, arows12682, irow12698, arows12697]
  all_goals rfl

theorem atot12698 : totK PD2M8K2 D2M8K2.u12698 = [0, 0, 3817951819647, 12609159316624, 10447237398217, 1688800197455, 49500494710, 0] := by
  rw [show D2M8K2.u12698 = KTree.node D2M8K2.u12682 (nat_lit 27289770) (nat_lit 3659780061) (nat_lit 0) D2M8K2.u12697 from rfl, totK_node, atot12682, atot12697]
  decide +kernel

theorem arows12729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12729 = true := by
  rw [show D2M8K2.u12729 = KTree.node D2M8K2.u12713 (nat_lit 27420178) (nat_lit 4036939643) (nat_lit 0) D2M8K2.u12728 from rfl, allE_node, arows12713, irow12729, arows12728]
  all_goals rfl

theorem atot12729 : totK PD2M8K2 D2M8K2.u12729 = [0, 2117743070782, 9183530332009, 12223929499984, 4934000346279, 434998927720, 5253160287, 0] := by
  rw [show D2M8K2.u12729 = KTree.node D2M8K2.u12713 (nat_lit 27420178) (nat_lit 4036939643) (nat_lit 0) D2M8K2.u12728 from rfl, totK_node, atot12713, atot12728]
  decide +kernel

theorem arows12761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12761 = true := by
  rw [show D2M8K2.u12761 = KTree.node D2M8K2.u12745 (nat_lit 27450505) (nat_lit 1414809158) (nat_lit 0) D2M8K2.u12760 from rfl, allE_node, arows12745, irow12761, arows12760]
  all_goals rfl

theorem atot12761 : totK PD2M8K2 D2M8K2.u12761 = [0, 1192307120528, 6343243496506, 11637637995873, 8118284099960, 1601406921669, 58018127943, 0] := by
  rw [show D2M8K2.u12761 = KTree.node D2M8K2.u12745 (nat_lit 27450505) (nat_lit 1414809158) (nat_lit 0) D2M8K2.u12760 from rfl, totK_node, atot12745, atot12760]
  decide +kernel

theorem arows12792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12792 = true := by
  rw [show D2M8K2.u12792 = KTree.node D2M8K2.u12776 (nat_lit 27485341) (nat_lit 1142153936) (nat_lit 0) D2M8K2.u12791 from rfl, allE_node, arows12776, irow12792, arows12791]
  all_goals rfl

theorem atot12792 : totK PD2M8K2 D2M8K2.u12792 = [0, 1993035767120, 8712904171356, 12038298252912, 5403212167559, 644217141905, 17590593026, 0] := by
  rw [show D2M8K2.u12792 = KTree.node D2M8K2.u12776 (nat_lit 27485341) (nat_lit 1142153936) (nat_lit 0) D2M8K2.u12791 from rfl, totK_node, atot12776, atot12791]
  decide +kernel

theorem arows12827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12827 = true := by
  rw [show D2M8K2.u12827 = KTree.node D2M8K2.u12811 (nat_lit 27528758) (nat_lit 3052681437) (nat_lit 0) D2M8K2.u12826 from rfl, allE_node, arows12811, irow12827, arows12826]
  all_goals rfl

theorem atot12827 : totK PD2M8K2 D2M8K2.u12827 = [0, 1737693312232, 8298648367340, 12345199059587, 5746353856239, 676595669929, 17826068843, 0] := by
  rw [show D2M8K2.u12827 = KTree.node D2M8K2.u12811 (nat_lit 27528758) (nat_lit 3052681437) (nat_lit 0) D2M8K2.u12826 from rfl, totK_node, atot12811, atot12826]
  decide +kernel

theorem arows12858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12858 = true := by
  rw [show D2M8K2.u12858 = KTree.node D2M8K2.u12842 (nat_lit 27565330) (nat_lit 3256376426) (nat_lit 0) D2M8K2.u12857 from rfl, allE_node, arows12842, irow12858, arows12857]
  all_goals rfl

theorem atot12858 : totK PD2M8K2 D2M8K2.u12858 = [0, 1934480863883, 8975288782459, 12555342388392, 4944430369767, 421385536448, 4977114383, 0] := by
  rw [show D2M8K2.u12858 = KTree.node D2M8K2.u12842 (nat_lit 27565330) (nat_lit 3256376426) (nat_lit 0) D2M8K2.u12857 from rfl, totK_node, atot12842, atot12857]
  decide +kernel

theorem arows12890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12890 = true := by
  rw [show D2M8K2.u12890 = KTree.node D2M8K2.u12874 (nat_lit 27611004) (nat_lit 3174028253) (nat_lit 0) D2M8K2.u12889 from rfl, allE_node, arows12874, irow12890, arows12889]
  all_goals rfl

theorem atot12890 : totK PD2M8K2 D2M8K2.u12890 = [0, 2014151908433, 8667083450313, 11899942833814, 5605051314581, 687514697213, 13176835040, 0] := by
  rw [show D2M8K2.u12890 = KTree.node D2M8K2.u12874 (nat_lit 27611004) (nat_lit 3174028253) (nat_lit 0) D2M8K2.u12889 from rfl, totK_node, atot12874, atot12889]
  decide +kernel

theorem arows12921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12921 = true := by
  rw [show D2M8K2.u12921 = KTree.node D2M8K2.u12905 (nat_lit 27901458) (nat_lit 3378061122) (nat_lit 0) D2M8K2.u12920 from rfl, allE_node, arows12905, irow12921, arows12920]
  all_goals rfl

theorem atot12921 : totK PD2M8K2 D2M8K2.u12921 = [0, 1993351267252, 9091256544675, 12594568529520, 4670873092670, 308310100900, 1369150432, 0] := by
  rw [show D2M8K2.u12921 = KTree.node D2M8K2.u12905 (nat_lit 27901458) (nat_lit 3378061122) (nat_lit 0) D2M8K2.u12920 from rfl, totK_node, atot12905, atot12920]
  decide +kernel

theorem arows12954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12954 = true := by
  rw [show D2M8K2.u12954 = KTree.node D2M8K2.u12938 (nat_lit 27940458) (nat_lit 2743937354) (nat_lit 130) D2M8K2.u12953 from rfl, allE_node, arows12938, irow12954, arows12953]
  all_goals rfl

theorem atot12954 : totK PD2M8K2 D2M8K2.u12954 = [0, 1638149173016, 7903115696106, 12126882628529, 6410758231886, 925019339344, 21664119971, 0] := by
  rw [show D2M8K2.u12954 = KTree.node D2M8K2.u12938 (nat_lit 27940458) (nat_lit 2743937354) (nat_lit 130) D2M8K2.u12953 from rfl, totK_node, atot12938, atot12953]
  decide +kernel

theorem arows12985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12985 = true := by
  rw [show D2M8K2.u12985 = KTree.node D2M8K2.u12969 (nat_lit 27974740) (nat_lit 3496796485) (nat_lit 0) D2M8K2.u12984 from rfl, allE_node, arows12969, irow12985, arows12984]
  all_goals rfl

theorem atot12985 : totK PD2M8K2 D2M8K2.u12985 = [0, 1677166430233, 7901220555562, 12175159679723, 6033864677223, 726582305124, 18797058808, 0] := by
  rw [show D2M8K2.u12985 = KTree.node D2M8K2.u12969 (nat_lit 27974740) (nat_lit 3496796485) (nat_lit 0) D2M8K2.u12984 from rfl, totK_node, atot12969, atot12984]
  decide +kernel

theorem arows13017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13017 = true := by
  rw [show D2M8K2.u13017 = KTree.node D2M8K2.u13001 (nat_lit 28050871) (nat_lit 2069271054) (nat_lit 0) D2M8K2.u13016 from rfl, allE_node, arows13001, irow13017, arows13016]
  all_goals rfl

theorem atot13017 : totK PD2M8K2 D2M8K2.u13017 = [0, 1861331114732, 8643269539213, 12443717473587, 5281660855332, 494169889151, 6115358396, 0] := by
  rw [show D2M8K2.u13017 = KTree.node D2M8K2.u13001 (nat_lit 28050871) (nat_lit 2069271054) (nat_lit 0) D2M8K2.u13016 from rfl, totK_node, atot13001, atot13016]
  decide +kernel

theorem arows13048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13048 = true := by
  rw [show D2M8K2.u13048 = KTree.node D2M8K2.u13032 (nat_lit 28097872) (nat_lit 3423385323) (nat_lit 0) D2M8K2.u13047 from rfl, allE_node, arows13032, irow13048, arows13047]
  all_goals rfl

theorem atot13048 : totK PD2M8K2 D2M8K2.u13048 = [0, 2077170597830, 9049470721503, 12155028239634, 5058660125370, 454257344953, 6190125969, 0] := by
  rw [show D2M8K2.u13048 = KTree.node D2M8K2.u13032 (nat_lit 28097872) (nat_lit 3423385323) (nat_lit 0) D2M8K2.u13047 from rfl, totK_node, atot13032, atot13047]
  decide +kernel

theorem arows13082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13082 = true := by
  rw [show D2M8K2.u13082 = KTree.node D2M8K2.u13066 (nat_lit 28389074) (nat_lit 2508298130) (nat_lit 0) D2M8K2.u13081 from rfl, allE_node, arows13066, irow13082, arows13081]
  all_goals rfl

theorem atot13082 : totK PD2M8K2 D2M8K2.u13082 = [0, 2023022516822, 9123154694942, 12515617713928, 4654002662204, 308544217725, 1369150432, 0] := by
  rw [show D2M8K2.u13082 = KTree.node D2M8K2.u13066 (nat_lit 28389074) (nat_lit 2508298130) (nat_lit 0) D2M8K2.u13081 from rfl, totK_node, atot13066, atot13081]
  decide +kernel

theorem arows13113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13113 = true := by
  rw [show D2M8K2.u13113 = KTree.node D2M8K2.u13097 (nat_lit 28434013) (nat_lit 625157337) (nat_lit 0) D2M8K2.u13112 from rfl, allE_node, arows13097, irow13113, arows13112]
  all_goals rfl

theorem atot13113 : totK PD2M8K2 D2M8K2.u13113 = [0, 1709876711358, 8016496746046, 12049365591183, 6324667362871, 917974043075, 21811729820, 0] := by
  rw [show D2M8K2.u13113 = KTree.node D2M8K2.u13097 (nat_lit 28434013) (nat_lit 625157337) (nat_lit 0) D2M8K2.u13112 from rfl, totK_node, atot13097, atot13112]
  decide +kernel

theorem arows13145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13145 = true := by
  rw [show D2M8K2.u13145 = KTree.node D2M8K2.u13129 (nat_lit 28509985) (nat_lit 1557828645) (nat_lit 0) D2M8K2.u13144 from rfl, allE_node, arows13129, irow13145, arows13144]
  all_goals rfl

theorem atot13145 : totK PD2M8K2 D2M8K2.u13145 = [0, 1694090630267, 8100581818619, 12316381105252, 5901806005465, 671347325403, 15398727635, 0] := by
  rw [show D2M8K2.u13145 = KTree.node D2M8K2.u13129 (nat_lit 28509985) (nat_lit 1557828645) (nat_lit 0) D2M8K2.u13144 from rfl, totK_node, atot13129, atot13144]
  decide +kernel

theorem arows13176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13176 = true := by
  rw [show D2M8K2.u13176 = KTree.node D2M8K2.u13160 (nat_lit 28544500) (nat_lit 3545287213) (nat_lit 0) D2M8K2.u13175 from rfl, allE_node, arows13160, irow13176, arows13175]
  all_goals rfl

theorem atot13176 : totK PD2M8K2 D2M8K2.u13176 = [0, 2033977454397, 9204672656194, 12419300612201, 4711179774174, 367558153357, 4805451294, 0] := by
  rw [show D2M8K2.u13176 = KTree.node D2M8K2.u13160 (nat_lit 28544500) (nat_lit 3545287213) (nat_lit 0) D2M8K2.u13175 from rfl, totK_node, atot13160, atot13175]
  decide +kernel

theorem arows13209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13209 = true := by
  rw [show D2M8K2.u13209 = KTree.node D2M8K2.u13193 (nat_lit 28587789) (nat_lit 1160965563) (nat_lit 0) D2M8K2.u13208 from rfl, allE_node, arows13193, irow13209, arows13208]
  all_goals rfl

theorem atot13209 : totK PD2M8K2 D2M8K2.u13209 = [0, 1658316920461, 7978915765035, 12319622986247, 6127623492268, 676189901939, 11218804606, 0] := by
  rw [show D2M8K2.u13209 = KTree.node D2M8K2.u13193 (nat_lit 28587789) (nat_lit 1160965563) (nat_lit 0) D2M8K2.u13208 from rfl, totK_node, atot13193, atot13208]
  decide +kernel

theorem arows13240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13240 = true := by
  rw [show D2M8K2.u13240 = KTree.node D2M8K2.u13224 (nat_lit 28881361) (nat_lit 1454138027) (nat_lit 0) D2M8K2.u13239 from rfl, allE_node, arows13224, irow13240, arows13239]
  all_goals rfl

theorem atot13240 : totK PD2M8K2 D2M8K2.u13240 = [0, 2131175653011, 9382713057507, 12375323639886, 4312924795348, 271439997348, 1369150432, 0] := by
  rw [show D2M8K2.u13240 = KTree.node D2M8K2.u13224 (nat_lit 28881361) (nat_lit 1454138027) (nat_lit 0) D2M8K2.u13239 from rfl, totK_node, atot13224, atot13239]
  decide +kernel

theorem arows13272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13272 = true := by
  rw [show D2M8K2.u13272 = KTree.node D2M8K2.u13256 (nat_lit 28922771) (nat_lit 1916060884) (nat_lit 0) D2M8K2.u13271 from rfl, allE_node, arows13256, irow13272, arows13271]
  all_goals rfl

theorem atot13272 : totK PD2M8K2 D2M8K2.u13272 = [0, 1899679843498, 8293462106799, 11767782847480, 5991014660152, 957029481194, 34105821913, 0] := by
  rw [show D2M8K2.u13272 = KTree.node D2M8K2.u13256 (nat_lit 28922771) (nat_lit 1916060884) (nat_lit 0) D2M8K2.u13271 from rfl, totK_node, atot13256, atot13271]
  decide +kernel

theorem arows13303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13303 = true := by
  rw [show D2M8K2.u13303 = KTree.node D2M8K2.u13287 (nat_lit 28956226) (nat_lit 4087583925) (nat_lit 0) D2M8K2.u13302 from rfl, allE_node, arows13287, irow13303, arows13302]
  all_goals rfl

theorem atot13303 : totK PD2M8K2 D2M8K2.u13303 = [0, 2015197058602, 8924073565068, 12244301102486, 5180353456231, 442994042676, 2621607852, 0] := by
  rw [show D2M8K2.u13303 = KTree.node D2M8K2.u13287 (nat_lit 28956226) (nat_lit 4087583925) (nat_lit 0) D2M8K2.u13302 from rfl, totK_node, atot13287, atot13302]
  decide +kernel

theorem arows13339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13339 = true := by
  rw [show D2M8K2.u13339 = KTree.node D2M8K2.u13323 (nat_lit 28995642) (nat_lit 3894365716) (nat_lit 0) D2M8K2.u13338 from rfl, allE_node, arows13323, irow13339, arows13338]
  all_goals rfl

theorem atot13339 : totK PD2M8K2 D2M8K2.u13339 = [0, 2015680103480, 8605688023034, 11858038916286, 5447746837963, 642664493454, 18830459099, 0] := by
  rw [show D2M8K2.u13339 = KTree.node D2M8K2.u13323 (nat_lit 28995642) (nat_lit 3894365716) (nat_lit 0) D2M8K2.u13338 from rfl, totK_node, atot13323, atot13338]
  decide +kernel

theorem arows13370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13370 = true := by
  rw [show D2M8K2.u13370 = KTree.node D2M8K2.u13354 (nat_lit 29034857) (nat_lit 990407664) (nat_lit 0) D2M8K2.u13369 from rfl, allE_node, arows13354, irow13370, arows13369]
  all_goals rfl

theorem atot13370 : totK PD2M8K2 D2M8K2.u13370 = [0, 2129553296006, 9085352219597, 11955546122746, 5000276683073, 572510123529, 17826068843, 0] := by
  rw [show D2M8K2.u13370 = KTree.node D2M8K2.u13354 (nat_lit 29034857) (nat_lit 990407664) (nat_lit 0) D2M8K2.u13369 from rfl, totK_node, atot13354, atot13369]
  decide +kernel

theorem arows13402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13402 = true := by
  rw [show D2M8K2.u13402 = KTree.node D2M8K2.u13386 (nat_lit 29114904) (nat_lit 3603225515) (nat_lit 0) D2M8K2.u13401 from rfl, allE_node, arows13386, irow13402, arows13401]
  all_goals rfl

theorem atot13402 : totK PD2M8K2 D2M8K2.u13402 = [0, 0, 4021749842409, 13102277420888, 9778042869834, 1434098064709, 39901530286, 0] := by
  rw [show D2M8K2.u13402 = KTree.node D2M8K2.u13386 (nat_lit 29114904) (nat_lit 3603225515) (nat_lit 0) D2M8K2.u13401 from rfl, totK_node, atot13386, atot13401]
  decide +kernel

theorem arows13433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13433 = true := by
  rw [show D2M8K2.u13433 = KTree.node D2M8K2.u13417 (nat_lit 29162948) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u13432 from rfl, allE_node, arows13417, irow13433, arows13432]
  all_goals rfl

theorem atot13433 : totK PD2M8K2 D2M8K2.u13433 = [0, 0, 2672667851984, 10660179890700, 11843130659244, 3245721980722, 209268027755, 1209030869] := by
  rw [show D2M8K2.u13433 = KTree.node D2M8K2.u13417 (nat_lit 29162948) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u13432 from rfl, totK_node, atot13417, atot13432]
  decide +kernel

theorem arows13466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13466 = true := by
  rw [show D2M8K2.u13466 = KTree.node D2M8K2.u13450 (nat_lit 29241564) (nat_lit 1480261109) (nat_lit 2048) D2M8K2.u13465 from rfl, allE_node, arows13450, irow13466, arows13465]
  all_goals rfl

theorem atot13466 : totK PD2M8K2 D2M8K2.u13466 = [0, 0, 3766989162309, 12513203929461, 10435841974473, 1929047607739, 67572272192, 0] := by
  rw [show D2M8K2.u13466 = KTree.node D2M8K2.u13450 (nat_lit 29241564) (nat_lit 1480261109) (nat_lit 2048) D2M8K2.u13465 from rfl, totK_node, atot13450, atot13465]
  decide +kernel

theorem arows13497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13497 = true := by
  rw [show D2M8K2.u13497 = KTree.node D2M8K2.u13481 (nat_lit 29294387) (nat_lit 1982421169) (nat_lit 0) D2M8K2.u13496 from rfl, allE_node, arows13481, irow13497, arows13496]
  all_goals rfl

theorem atot13497 : totK PD2M8K2 D2M8K2.u13497 = [186677387228, 459373490871, 1898978854949, 8422857710200, 12155780511927, 4764499716984, 462046563768, 6115358396] := by
  rw [show D2M8K2.u13497 = KTree.node D2M8K2.u13481 (nat_lit 29294387) (nat_lit 1982421169) (nat_lit 0) D2M8K2.u13496 from rfl, totK_node, atot13481, atot13496]
  decide +kernel

theorem arows13529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13529 = true := by
  rw [show D2M8K2.u13529 = KTree.node D2M8K2.u13513 (nat_lit 29877808) (nat_lit 3429922328) (nat_lit 0) D2M8K2.u13528 from rfl, allE_node, arows13513, irow13529, arows13528]
  all_goals rfl

theorem atot13529 : totK PD2M8K2 D2M8K2.u13529 = [1910473496241, 9066801106026, 12600541620410, 4639743755591, 316987014630, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13529 = KTree.node D2M8K2.u13513 (nat_lit 29877808) (nat_lit 3429922328) (nat_lit 0) D2M8K2.u13528 from rfl, totK_node, atot13513, atot13528]
  decide +kernel

theorem arows13560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13560 = true := by
  rw [show D2M8K2.u13560 = KTree.node D2M8K2.u13544 (nat_lit 29960485) (nat_lit 1189376891) (nat_lit 0) D2M8K2.u13559 from rfl, allE_node, arows13544, irow13560, arows13559]
  all_goals rfl

theorem atot13560 : totK PD2M8K2 D2M8K2.u13560 = [1983586845702, 8607728870854, 11934502335335, 5480269730888, 648094787290, 15244263794, 0, 0] := by
  rw [show D2M8K2.u13560 = KTree.node D2M8K2.u13544 (nat_lit 29960485) (nat_lit 1189376891) (nat_lit 0) D2M8K2.u13559 from rfl, totK_node, atot13544, atot13559]
  decide +kernel

theorem arows13594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13594 = true := by
  rw [show D2M8K2.u13594 = KTree.node D2M8K2.u13578 (nat_lit 29999043) (nat_lit 3644688201) (nat_lit 0) D2M8K2.u13593 from rfl, allE_node, arows13578, irow13594, arows13593]
  all_goals rfl

theorem atot13594 : totK PD2M8K2 D2M8K2.u13594 = [1984109884308, 8652852619086, 11943780236550, 5488284434525, 672093443690, 17898111484, 0, 0] := by
  rw [show D2M8K2.u13594 = KTree.node D2M8K2.u13578 (nat_lit 29999043) (nat_lit 3644688201) (nat_lit 0) D2M8K2.u13593 from rfl, totK_node, atot13578, atot13593]
  decide +kernel

theorem arows13625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13625 = true := by
  rw [show D2M8K2.u13625 = KTree.node D2M8K2.u13609 (nat_lit 30037883) (nat_lit 2093914618) (nat_lit 0) D2M8K2.u13624 from rfl, allE_node, arows13609, irow13625, arows13624]
  all_goals rfl

theorem atot13625 : totK PD2M8K2 D2M8K2.u13625 = [1644711138228, 8257049936803, 12531977309619, 5577559619228, 508780145738, 6953970175, 0, 0] := by
  rw [show D2M8K2.u13625 = KTree.node D2M8K2.u13609 (nat_lit 30037883) (nat_lit 2093914618) (nat_lit 0) D2M8K2.u13624 from rfl, totK_node, atot13609, atot13624]
  decide +kernel

theorem arows13657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13657 = true := by
  rw [show D2M8K2.u13657 = KTree.node D2M8K2.u13641 (nat_lit 30080204) (nat_lit 3437260527) (nat_lit 0) D2M8K2.u13656 from rfl, allE_node, arows13641, irow13657, arows13656]
  all_goals rfl

theorem atot13657 : totK PD2M8K2 D2M8K2.u13657 = [2038998152306, 8660647986236, 11874171764595, 5670247681731, 655257595276, 10072132636, 0, 0] := by
  rw [show D2M8K2.u13657 = KTree.node D2M8K2.u13641 (nat_lit 30080204) (nat_lit 3437260527) (nat_lit 0) D2M8K2.u13656 from rfl, totK_node, atot13641, atot13656]
  decide +kernel

theorem arows13688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13688 = true := by
  rw [show D2M8K2.u13688 = KTree.node D2M8K2.u13672 (nat_lit 30119931) (nat_lit 3552568136) (nat_lit 0) D2M8K2.u13687 from rfl, allE_node, arows13672, irow13688, arows13687]
  all_goals rfl

theorem atot13688 : totK PD2M8K2 D2M8K2.u13688 = [0, 2719287296666, 10595608490402, 11575577623203, 3265348239354, 247747554896, 1369150432, 0] := by
  rw [show D2M8K2.u13688 = KTree.node D2M8K2.u13672 (nat_lit 30119931) (nat_lit 3552568136) (nat_lit 0) D2M8K2.u13687 from rfl, totK_node, atot13672, atot13687]
  decide +kernel

theorem arows13721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13721 = true := by
  rw [show D2M8K2.u13721 = KTree.node D2M8K2.u13705 (nat_lit 30200010) (nat_lit 3317858464) (nat_lit 0) D2M8K2.u13720 from rfl, allE_node, arows13705, irow13721, arows13720]
  all_goals rfl

theorem atot13721 : totK PD2M8K2 D2M8K2.u13721 = [0, 2729675541039, 10900580069114, 11973591021563, 2928378240579, 125791679310, 0, 0] := by
  rw [show D2M8K2.u13721 = KTree.node D2M8K2.u13705 (nat_lit 30200010) (nat_lit 3317858464) (nat_lit 0) D2M8K2.u13720 from rfl, totK_node, atot13705, atot13720]
  decide +kernel

theorem arows13752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13752 = true := by
  rw [show D2M8K2.u13752 = KTree.node D2M8K2.u13736 (nat_lit 30277261) (nat_lit 1111001889) (nat_lit 0) D2M8K2.u13751 from rfl, allE_node, arows13736, irow13752, arows13751]
  all_goals rfl

theorem atot13752 : totK PD2M8K2 D2M8K2.u13752 = [0, 3291790544044, 11816406542525, 11243477501118, 2237244516900, 71038417224, 0, 0] := by
  rw [show D2M8K2.u13752 = KTree.node D2M8K2.u13736 (nat_lit 30277261) (nat_lit 1111001889) (nat_lit 0) D2M8K2.u13751 from rfl, totK_node, atot13736, atot13751]
  decide +kernel

theorem arows13784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13784 = true := by
  rw [show D2M8K2.u13784 = KTree.node D2M8K2.u13768 (nat_lit 30402800) (nat_lit 3731953676) (nat_lit 0) D2M8K2.u13783 from rfl, allE_node, arows13768, irow13784, arows13783]
  all_goals rfl

theorem atot13784 : totK PD2M8K2 D2M8K2.u13784 = [1691835200920, 7455472672966, 11401607581868, 7125719314898, 1332728523061, 41804758000, 0, 0] := by
  rw [show D2M8K2.u13784 = KTree.node D2M8K2.u13768 (nat_lit 30402800) (nat_lit 3731953676) (nat_lit 0) D2M8K2.u13783 from rfl, totK_node, atot13768, atot13783]
  decide +kernel

theorem arows13815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13815 = true := by
  rw [show D2M8K2.u13815 = KTree.node D2M8K2.u13799 (nat_lit 30431672) (nat_lit 1862505435) (nat_lit 0) D2M8K2.u13814 from rfl, allE_node, arows13799, irow13815, arows13814]
  all_goals rfl

theorem atot13815 : totK PD2M8K2 D2M8K2.u13815 = [1180280341265, 6322925458084, 11641542795415, 8128474820974, 1624006886787, 58018127943, 0, 0] := by
  rw [show D2M8K2.u13815 = KTree.node D2M8K2.u13799 (nat_lit 30431672) (nat_lit 1862505435) (nat_lit 0) D2M8K2.u13814 from rfl, totK_node, atot13799, atot13814]
  decide +kernel

theorem arows13850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13850 = true := by
  rw [show D2M8K2.u13850 = KTree.node D2M8K2.u13834 (nat_lit 30464420) (nat_lit 2534902590) (nat_lit 0) D2M8K2.u13849 from rfl, allE_node, arows13834, irow13850, arows13849]
  all_goals rfl

theorem atot13850 : totK PD2M8K2 D2M8K2.u13850 = [1730953917080, 8091751516873, 12216116966722, 5985596177035, 737008703692, 18797058808, 0, 0] := by
  rw [show D2M8K2.u13850 = KTree.node D2M8K2.u13834 (nat_lit 30464420) (nat_lit 2534902590) (nat_lit 0) D2M8K2.u13849 from rfl, totK_node, atot13834, atot13849]
  decide +kernel

theorem arows13881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13881 = true := by
  rw [show D2M8K2.u13881 = KTree.node D2M8K2.u13865 (nat_lit 30502570) (nat_lit 3968985432) (nat_lit 0) D2M8K2.u13880 from rfl, allE_node, arows13865, irow13881, arows13880]
  all_goals rfl

theorem atot13881 : totK PD2M8K2 D2M8K2.u13881 = [1661324985610, 7890751035499, 12225953128568, 6264870678159, 781761456033, 19065934916, 0, 0] := by
  rw [show D2M8K2.u13881 = KTree.node D2M8K2.u13865 (nat_lit 30502570) (nat_lit 3968985432) (nat_lit 0) D2M8K2.u13880 from rfl, totK_node, atot13865, atot13880]
  decide +kernel

theorem arows13913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13913 = true := by
  rw [show D2M8K2.u13913 = KTree.node D2M8K2.u13897 (nat_lit 30547931) (nat_lit 2765552662) (nat_lit 0) D2M8K2.u13912 from rfl, allE_node, arows13897, irow13913, arows13912]
  all_goals rfl

theorem atot13913 : totK PD2M8K2 D2M8K2.u13913 = [2272899070829, 9592044327409, 12111811866768, 4554195965041, 393142893870, 4977114383, 0, 0] := by
  rw [show D2M8K2.u13913 = KTree.node D2M8K2.u13897 (nat_lit 30547931) (nat_lit 2765552662) (nat_lit 0) D2M8K2.u13912 from rfl, totK_node, atot13897, atot13912]
  decide +kernel

theorem arows13944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13944 = true := by
  rw [show D2M8K2.u13944 = KTree.node D2M8K2.u13928 (nat_lit 30586587) (nat_lit 3315021601) (nat_lit 0) D2M8K2.u13943 from rfl, allE_node, arows13928, irow13944, arows13943]
  all_goals rfl

theorem atot13944 : totK PD2M8K2 D2M8K2.u13944 = [1273419804210, 6964703433588, 12362153503751, 7281086102140, 992428942252, 19545957871, 0, 0] := by
  rw [show D2M8K2.u13944 = KTree.node D2M8K2.u13928 (nat_lit 30586587) (nat_lit 3315021601) (nat_lit 0) D2M8K2.u13943 from rfl, totK_node, atot13928, atot13943]
  decide +kernel

theorem arows13977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13977 = true := by
  rw [show D2M8K2.u13977 = KTree.node D2M8K2.u13961 (nat_lit 30663742) (nat_lit 3559765751) (nat_lit 0) D2M8K2.u13976 from rfl, allE_node, arows13961, irow13977, arows13976]
  all_goals rfl

theorem atot13977 : totK PD2M8K2 D2M8K2.u13977 = [0, 2117768858604, 8783554073117, 11552196927611, 5458142220859, 913863525078, 41989737272, 0] := by
  rw [show D2M8K2.u13977 = KTree.node D2M8K2.u13961 (nat_lit 30663742) (nat_lit 3559765751) (nat_lit 0) D2M8K2.u13976 from rfl, totK_node, atot13961, atot13976]
  decide +kernel

theorem arows14008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14008 = true := by
  rw [show D2M8K2.u14008 = KTree.node D2M8K2.u13992 (nat_lit 30695577) (nat_lit 1812770759) (nat_lit 0) D2M8K2.u14007 from rfl, allE_node, arows13992, irow14008, arows14007]
  all_goals rfl

theorem atot14008 : totK PD2M8K2 D2M8K2.u14008 = [0, 1993496677444, 8519720966670, 11734529257041, 5719575359046, 758457382019, 15657634319, 0] := by
  rw [show D2M8K2.u14008 = KTree.node D2M8K2.u13992 (nat_lit 30695577) (nat_lit 1812770759) (nat_lit 0) D2M8K2.u14007 from rfl, totK_node, atot13992, atot14007]
  decide +kernel

theorem arows14040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14040 = true := by
  rw [show D2M8K2.u14040 = KTree.node D2M8K2.u14024 (nat_lit 30736471) (nat_lit 2188946791) (nat_lit 0) D2M8K2.u14039 from rfl, allE_node, arows14024, irow14040, arows14039]
  all_goals rfl

theorem atot14040 : totK PD2M8K2 D2M8K2.u14040 = [0, 1994043766943, 8953774263550, 12210270206863, 5121514364576, 489768097040, 6546549506, 0] := by
  rw [show D2M8K2.u14040 = KTree.node D2M8K2.u14024 (nat_lit 30736471) (nat_lit 2188946791) (nat_lit 0) D2M8K2.u14039 from rfl, totK_node, atot14024, atot14039]
  decide +kernel

theorem arows14071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14071 = true := by
  rw [show D2M8K2.u14071 = KTree.node D2M8K2.u14055 (nat_lit 30779298) (nat_lit 2096129509) (nat_lit 0) D2M8K2.u14070 from rfl, allE_node, arows14055, irow14071, arows14070]
  all_goals rfl

theorem atot14071 : totK PD2M8K2 D2M8K2.u14071 = [0, 1658284530265, 8228097780081, 12511917349962, 5796136384406, 547552947822, 6624648996, 0] := by
  rw [show D2M8K2.u14071 = KTree.node D2M8K2.u14055 (nat_lit 30779298) (nat_lit 2096129509) (nat_lit 0) D2M8K2.u14070 from rfl, totK_node, atot14055, atot14070]
  decide +kernel

theorem arows14105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14105 = true := by
  rw [show D2M8K2.u14105 = KTree.node D2M8K2.u14089 (nat_lit 30822336) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u14104 from rfl, allE_node, arows14089, irow14105, arows14104]
  all_goals rfl

theorem atot14105 : totK PD2M8K2 D2M8K2.u14105 = [0, 2047119486658, 9275681175826, 12464412676004, 4779175208250, 353349196798, 1429815836, 0] := by
  rw [show D2M8K2.u14105 = KTree.node D2M8K2.u14089 (nat_lit 30822336) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u14104 from rfl, totK_node, atot14089, atot14104]
  decide +kernel

theorem arows14136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14136 = true := by
  rw [show D2M8K2.u14136 = KTree.node D2M8K2.u14120 (nat_lit 30864625) (nat_lit 1353320213) (nat_lit 0) D2M8K2.u14135 from rfl, allE_node, arows14120, irow14136, arows14135]
  all_goals rfl

theorem atot14136 : totK PD2M8K2 D2M8K2.u14136 = [1976552160701, 7522340805684, 9173030721548, 5965469786318, 3369041449697, 539356146172, 12189850367, 0] := by
  rw [show D2M8K2.u14136 = KTree.node D2M8K2.u14120 (nat_lit 30864625) (nat_lit 1353320213) (nat_lit 0) D2M8K2.u14135 from rfl, totK_node, atot14120, atot14135]
  decide +kernel

theorem arows14168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14168 = true := by
  rw [show D2M8K2.u14168 = KTree.node D2M8K2.u14152 (nat_lit 30905909) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u14167 from rfl, allE_node, arows14152, irow14168, arows14167]
  all_goals rfl

theorem atot14168 : totK PD2M8K2 D2M8K2.u14168 = [2001094274040, 9032303730992, 12406205188274, 4990461886429, 551435047303, 26904681413, 0, 0] := by
  rw [show D2M8K2.u14168 = KTree.node D2M8K2.u14152 (nat_lit 30905909) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u14167 from rfl, totK_node, atot14152, atot14167]
  decide +kernel

theorem arows14199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14199 = true := by
  rw [show D2M8K2.u14199 = KTree.node D2M8K2.u14183 (nat_lit 30938701) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u14198 from rfl, allE_node, arows14183, irow14199, arows14198]
  all_goals rfl

theorem atot14199 : totK PD2M8K2 D2M8K2.u14199 = [1690036004246, 7533589862666, 11456847603041, 6925778352812, 1253791986912, 30065390301, 0, 0] := by
  rw [show D2M8K2.u14199 = KTree.node D2M8K2.u14183 (nat_lit 30938701) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u14198 from rfl, totK_node, atot14183, atot14198]
  decide +kernel

theorem arows14232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14232 = true := by
  rw [show D2M8K2.u14232 = KTree.node D2M8K2.u14216 (nat_lit 30973692) (nat_lit 2921944799) (nat_lit 0) D2M8K2.u14231 from rfl, allE_node, arows14216, irow14232, arows14231]
  all_goals rfl

theorem atot14232 : totK PD2M8K2 D2M8K2.u14232 = [1640341136195, 7842518693738, 12143463485158, 6233100684004, 766492662634, 18797058808, 0, 0] := by
  rw [show D2M8K2.u14232 = KTree.node D2M8K2.u14216 (nat_lit 30973692) (nat_lit 2921944799) (nat_lit 0) D2M8K2.u14231 from rfl, totK_node, atot14216, atot14231]
  decide +kernel

theorem arows14263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14263 = true := by
  rw [show D2M8K2.u14263 = KTree.node D2M8K2.u14247 (nat_lit 31058608) (nat_lit 3378751486) (nat_lit 0) D2M8K2.u14262 from rfl, allE_node, arows14247, irow14263, arows14262]
  all_goals rfl

theorem atot14263 : totK PD2M8K2 D2M8K2.u14263 = [2042385929962, 8982147217552, 12239063917463, 5028773537152, 479014155406, 6115358396, 0, 0] := by
  rw [show D2M8K2.u14263 = KTree.node D2M8K2.u14247 (nat_lit 31058608) (nat_lit 3378751486) (nat_lit 0) D2M8K2.u14262 from rfl, totK_node, atot14247, atot14262]
  decide +kernel

theorem arows14295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14295 = true := by
  rw [show D2M8K2.u14295 = KTree.node D2M8K2.u14279 (nat_lit 31095268) (nat_lit 3839101480) (nat_lit 0) D2M8K2.u14294 from rfl, allE_node, arows14279, irow14295, arows14294]
  all_goals rfl

theorem atot14295 : totK PD2M8K2 D2M8K2.u14295 = [424455604040, 4778471016263, 12363169042425, 9532965823463, 1613148202054, 48489649739, 0, 0] := by
  rw [show D2M8K2.u14295 = KTree.node D2M8K2.u14279 (nat_lit 31095268) (nat_lit 3839101480) (nat_lit 0) D2M8K2.u14294 from rfl, totK_node, atot14279, atot14294]
  decide +kernel

theorem arows14326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14326 = true := by
  rw [show D2M8K2.u14326 = KTree.node D2M8K2.u14310 (nat_lit 31139019) (nat_lit 2642041806) (nat_lit 0) D2M8K2.u14325 from rfl, allE_node, arows14310, irow14326, arows14325]
  all_goals rfl

theorem atot14326 : totK PD2M8K2 D2M8K2.u14326 = [0, 2132490723601, 9634169239525, 12553352085591, 4079656588159, 248512535465, 1275377855, 0] := by
  rw [show D2M8K2.u14326 = KTree.node D2M8K2.u14310 (nat_lit 31139019) (nat_lit 2642041806) (nat_lit 0) D2M8K2.u14325 from rfl, totK_node, atot14310, atot14325]
  decide +kernel

theorem arows14363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14363 = true := by
  rw [show D2M8K2.u14363 = KTree.node D2M8K2.u14347 (nat_lit 31194415) (nat_lit 1986599626) (nat_lit 0) D2M8K2.u14362 from rfl, allE_node, arows14347, irow14363, arows14362]
  all_goals rfl

theorem atot14363 : totK PD2M8K2 D2M8K2.u14363 = [0, 2762664318428, 10642653481713, 11681830917589, 3401078135709, 218450492461, 1206465782, 0] := by
  rw [show D2M8K2.u14363 = KTree.node D2M8K2.u14347 (nat_lit 31194415) (nat_lit 1986599626) (nat_lit 0) D2M8K2.u14362 from rfl, totK_node, atot14347, atot14362]
  decide +kernel

theorem arows14394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14394 = true := by
  rw [show D2M8K2.u14394 = KTree.node D2M8K2.u14378 (nat_lit 31274825) (nat_lit 1778825351) (nat_lit 0) D2M8K2.u14393 from rfl, allE_node, arows14378, irow14394, arows14393]
  all_goals rfl

theorem atot14394 : totK PD2M8K2 D2M8K2.u14394 = [0, 1647925314252, 8197026117596, 12340141517787, 5515551864401, 660254659942, 18694047957, 0] := by
  rw [show D2M8K2.u14394 = KTree.node D2M8K2.u14378 (nat_lit 31274825) (nat_lit 1778825351) (nat_lit 0) D2M8K2.u14393 from rfl, totK_node, atot14378, atot14393]
  decide +kernel

theorem arows14426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14426 = true := by
  rw [show D2M8K2.u14426 = KTree.node D2M8K2.u14410 (nat_lit 31320268) (nat_lit 3736817080) (nat_lit 0) D2M8K2.u14425 from rfl, allE_node, arows14410, irow14426, arows14425]
  all_goals rfl

theorem atot14426 : totK PD2M8K2 D2M8K2.u14426 = [758382914429, 4669080807702, 10258573422004, 9645220822552, 3122214122271, 261946989116, 4779662215, 0] := by
  rw [show D2M8K2.u14426 = KTree.node D2M8K2.u14410 (nat_lit 31320268) (nat_lit 3736817080) (nat_lit 0) D2M8K2.u14425 from rfl, totK_node, atot14410, atot14425]
  decide +kernel

theorem arows14457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14457 = true := by
  rw [show D2M8K2.u14457 = KTree.node D2M8K2.u14441 (nat_lit 31376860) (nat_lit 3861144248) (nat_lit 0) D2M8K2.u14456 from rfl, allE_node, arows14441, irow14457, arows14456]
  all_goals rfl

theorem atot14457 : totK PD2M8K2 D2M8K2.u14457 = [1992671274727, 9026299294183, 12492099309357, 4868913201393, 352983541647, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14457 = KTree.node D2M8K2.u14441 (nat_lit 31376860) (nat_lit 3861144248) (nat_lit 0) D2M8K2.u14456 from rfl, totK_node, atot14441, atot14456]
  decide +kernel

theorem arows14490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14490 = true := by
  rw [show D2M8K2.u14490 = KTree.node D2M8K2.u14474 (nat_lit 31421121) (nat_lit 1777597893) (nat_lit 0) D2M8K2.u14489 from rfl, allE_node, arows14474, irow14490, arows14489]
  all_goals rfl

theorem atot14490 : totK PD2M8K2 D2M8K2.u14490 = [1298941311935, 6556148451113, 11606230451596, 7899975426869, 1599091186457, 58018127943, 0, 0] := by
  rw [show D2M8K2.u14490 = KTree.node D2M8K2.u14474 (nat_lit 31421121) (nat_lit 1777597893) (nat_lit 0) D2M8K2.u14489 from rfl, totK_node, atot14474, atot14489]
  decide +kernel

theorem arows14521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14521 = true := by
  rw [show D2M8K2.u14521 = KTree.node D2M8K2.u14505 (nat_lit 31494031) (nat_lit 2426140697) (nat_lit 0) D2M8K2.u14520 from rfl, allE_node, arows14505, irow14521, arows14520]
  all_goals rfl

theorem atot14521 : totK PD2M8K2 D2M8K2.u14521 = [2035342497047, 8894179593297, 12001009191741, 5203974955838, 582909483988, 14345316470, 0, 0] := by
  rw [show D2M8K2.u14521 = KTree.node D2M8K2.u14505 (nat_lit 31494031) (nat_lit 2426140697) (nat_lit 0) D2M8K2.u14520 from rfl, totK_node, atot14505, atot14520]
  decide +kernel

theorem arows14553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14553 = true := by
  rw [show D2M8K2.u14553 = KTree.node D2M8K2.u14537 (nat_lit 31531778) (nat_lit 3999014965) (nat_lit 0) D2M8K2.u14552 from rfl, allE_node, arows14537, irow14553, arows14552]
  all_goals rfl

theorem atot14553 : totK PD2M8K2 D2M8K2.u14553 = [1651660593053, 8103290839984, 12447051001294, 5874152360956, 578177004494, 6953970175, 0, 0] := by
  rw [show D2M8K2.u14553 = KTree.node D2M8K2.u14537 (nat_lit 31531778) (nat_lit 3999014965) (nat_lit 0) D2M8K2.u14552 from rfl, totK_node, atot14537, atot14552]
  decide +kernel

theorem arows14584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14584 = true := by
  rw [show D2M8K2.u14584 = KTree.node D2M8K2.u14568 (nat_lit 31573614) (nat_lit 3746194052) (nat_lit 0) D2M8K2.u14583 from rfl, allE_node, arows14568, irow14584, arows14583]
  all_goals rfl

theorem atot14584 : totK PD2M8K2 D2M8K2.u14584 = [2042848924932, 8838642175088, 12043691011640, 5452770294636, 600632138603, 10072132636, 0, 0] := by
  rw [show D2M8K2.u14584 = KTree.node D2M8K2.u14568 (nat_lit 31573614) (nat_lit 3746194052) (nat_lit 0) D2M8K2.u14583 from rfl, totK_node, atot14568, atot14583]
  decide +kernel

theorem arows14618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14618 = true := by
  rw [show D2M8K2.u14618 = KTree.node D2M8K2.u14602 (nat_lit 31614650) (nat_lit 4170378179) (nat_lit 0) D2M8K2.u14617 from rfl, allE_node, arows14602, irow14618, arows14617]
  all_goals rfl

theorem atot14618 : totK PD2M8K2 D2M8K2.u14618 = [0, 2447518750343, 10276568065792, 12023080611587, 3481072661961, 205618678570, 1310517177, 0] := by
  rw [show D2M8K2.u14618 = KTree.node D2M8K2.u14602 (nat_lit 31614650) (nat_lit 4170378179) (nat_lit 0) D2M8K2.u14617 from rfl, totK_node, atot14602, atot14617]
  decide +kernel

theorem arows14649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14649 = true := by
  rw [show D2M8K2.u14649 = KTree.node D2M8K2.u14633 (nat_lit 31656811) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u14648 from rfl, allE_node, arows14633, irow14649, arows14648]
  all_goals rfl

theorem atot14649 : totK PD2M8K2 D2M8K2.u14649 = [0, 2835237889630, 10885918311108, 11839535425069, 3199251860010, 139272848535, 0, 0] := by
  rw [show D2M8K2.u14649 = KTree.node D2M8K2.u14633 (nat_lit 31656811) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u14648 from rfl, totK_node, atot14633, atot14648]
  decide +kernel

theorem arows14681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14681 = true := by
  rw [show D2M8K2.u14681 = KTree.node D2M8K2.u14665 (nat_lit 31750599) (nat_lit 3639394546) (nat_lit 0) D2M8K2.u14680 from rfl, allE_node, arows14665, irow14681, arows14680]
  all_goals rfl

theorem atot14681 : totK PD2M8K2 D2M8K2.u14681 = [0, 1810053120087, 8280814682094, 12038964987326, 5548915796299, 703738588837, 18953862985, 0] := by
  rw [show D2M8K2.u14681 = KTree.node D2M8K2.u14665 (nat_lit 31750599) (nat_lit 3639394546) (nat_lit 0) D2M8K2.u14680 from rfl, totK_node, atot14665, atot14680]
  decide +kernel

theorem arows14712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14712 = true := by
  rw [show D2M8K2.u14712 = KTree.node D2M8K2.u14696 (nat_lit 31792956) (nat_lit 2330901154) (nat_lit 0) D2M8K2.u14711 from rfl, allE_node, arows14696, irow14712, arows14711]
  all_goals rfl

theorem atot14712 : totK PD2M8K2 D2M8K2.u14712 = [0, 2193437731514, 9372922508302, 12075322152357, 4561175564946, 379562827505, 6052528252, 0] := by
  rw [show D2M8K2.u14712 = KTree.node D2M8K2.u14696 (nat_lit 31792956) (nat_lit 2330901154) (nat_lit 0) D2M8K2.u14711 from rfl, totK_node, atot14696, atot14711]
  decide +kernel

theorem arows14745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14745 = true := by
  rw [show D2M8K2.u14745 = KTree.node D2M8K2.u14729 (nat_lit 32356328) (nat_lit 3943017048) (nat_lit 0) D2M8K2.u14744 from rfl, allE_node, arows14729, irow14745, arows14744]
  all_goals rfl

theorem atot14745 : totK PD2M8K2 D2M8K2.u14745 = [2007681859162, 8441552770296, 11359521514127, 5829602026565, 1068984120021, 40338621816, 0, 0] := by
  rw [show D2M8K2.u14745 = KTree.node D2M8K2.u14729 (nat_lit 32356328) (nat_lit 3943017048) (nat_lit 0) D2M8K2.u14744 from rfl, totK_node, atot14729, atot14744]
  decide +kernel

theorem arows14776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14776 = true := by
  rw [show D2M8K2.u14776 = KTree.node D2M8K2.u14760 (nat_lit 32397101) (nat_lit 2187426488) (nat_lit 0) D2M8K2.u14775 from rfl, allE_node, arows14760, irow14776, arows14775]
  all_goals rfl

theorem atot14776 : totK PD2M8K2 D2M8K2.u14776 = [2031190622891, 9138617031058, 12518126730802, 4881538890638, 364209680803, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14776 = KTree.node D2M8K2.u14760 (nat_lit 32397101) (nat_lit 2187426488) (nat_lit 0) D2M8K2.u14775 from rfl, totK_node, atot14760, atot14775]
  decide +kernel

theorem arows14808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14808 = true := by
  rw [show D2M8K2.u14808 = KTree.node D2M8K2.u14792 (nat_lit 32429094) (nat_lit 3739187072) (nat_lit 0) D2M8K2.u14807 from rfl, allE_node, arows14792, irow14808, arows14807]
  all_goals rfl

theorem atot14808 : totK PD2M8K2 D2M8K2.u14808 = [1517608550593, 6830892689730, 11286367375088, 7685632077762, 1578523164001, 58018127943, 0, 0] := by
  rw [show D2M8K2.u14808 = KTree.node D2M8K2.u14792 (nat_lit 32429094) (nat_lit 3739187072) (nat_lit 0) D2M8K2.u14807 from rfl, totK_node, atot14792, atot14807]
  decide +kernel

theorem arows14839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14839 = true := by
  rw [show D2M8K2.u14839 = KTree.node D2M8K2.u14823 (nat_lit 32461929) (nat_lit 1426804665) (nat_lit 0) D2M8K2.u14838 from rfl, allE_node, arows14823, irow14839, arows14838]
  all_goals rfl

theorem atot14839 : totK PD2M8K2 D2M8K2.u14839 = [1766587827691, 8105829567580, 12069839031593, 6023930313180, 747124700504, 18797058808, 0, 0] := by
  rw [show D2M8K2.u14839 = KTree.node D2M8K2.u14823 (nat_lit 32461929) (nat_lit 1426804665) (nat_lit 0) D2M8K2.u14838 from rfl, totK_node, atot14823, atot14838]
  decide +kernel

theorem arows14874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14874 = true := by
  rw [show D2M8K2.u14874 = KTree.node D2M8K2.u14858 (nat_lit 32504069) (nat_lit 1908797021) (nat_lit 0) D2M8K2.u14873 from rfl, allE_node, arows14858, irow14874, arows14873]
  all_goals rfl

theorem atot14874 : totK PD2M8K2 D2M8K2.u14874 = [1597260912698, 7959300109699, 12297396497225, 6130683981612, 766071666461, 19065934916, 0, 0] := by
  rw [show D2M8K2.u14874 = KTree.node D2M8K2.u14858 (nat_lit 32504069) (nat_lit 1908797021) (nat_lit 0) D2M8K2.u14873 from rfl, totK_node, atot14858, atot14873]
  decide +kernel

theorem arows14905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14905 = true := by
  rw [show D2M8K2.u14905 = KTree.node D2M8K2.u14889 (nat_lit 32577744) (nat_lit 3547789339) (nat_lit 0) D2M8K2.u14904 from rfl, allE_node, arows14889, irow14905, arows14904]
  all_goals rfl

theorem atot14905 : totK PD2M8K2 D2M8K2.u14905 = [1292464131673, 6972357598027, 12336598840565, 7247541060530, 974748131608, 19545957871, 0, 0] := by
  rw [show D2M8K2.u14905 = KTree.node D2M8K2.u14889 (nat_lit 32577744) (nat_lit 3547789339) (nat_lit 0) D2M8K2.u14904 from rfl, totK_node, atot14889, atot14904]
  decide +kernel

theorem arows14937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14937 = true := by
  rw [show D2M8K2.u14937 = KTree.node D2M8K2.u14921 (nat_lit 32615093) (nat_lit 2304042884) (nat_lit 0) D2M8K2.u14936 from rfl, allE_node, arows14921, irow14937, arows14936]
  all_goals rfl

theorem atot14937 : totK PD2M8K2 D2M8K2.u14937 = [0, 2190285725155, 9571112618190, 12358352736366, 4090864593731, 241913761138, 1369150432, 0] := by
  rw [show D2M8K2.u14937 = KTree.node D2M8K2.u14921 (nat_lit 32615093) (nat_lit 2304042884) (nat_lit 0) D2M8K2.u14936 from rfl, totK_node, atot14921, atot14936]
  decide +kernel

theorem arows14968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14968 = true := by
  rw [show D2M8K2.u14968 = KTree.node D2M8K2.u14952 (nat_lit 32656469) (nat_lit 2225338828) (nat_lit 0) D2M8K2.u14967 from rfl, allE_node, arows14952, irow14968, arows14967]
  all_goals rfl

theorem atot14968 : totK PD2M8K2 D2M8K2.u14968 = [0, 3191530801594, 11387632369375, 11350355173769, 2889727763608, 126291503606, 0, 0] := by
  rw [show D2M8K2.u14968 = KTree.node D2M8K2.u14952 (nat_lit 32656469) (nat_lit 2225338828) (nat_lit 0) D2M8K2.u14967 from rfl, totK_node, atot14952, atot14967]
  decide +kernel

theorem arows15001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15001 = true := by
  rw [show D2M8K2.u15001 = KTree.node D2M8K2.u14985 (nat_lit 32710827) (nat_lit 2442323262) (nat_lit 0) D2M8K2.u15000 from rfl, allE_node, arows14985, irow15001, arows15000]
  all_goals rfl

theorem atot15001 : totK PD2M8K2 D2M8K2.u15001 = [0, 1937348264828, 8939776026064, 12347329749101, 4917714461988, 423899628351, 6301476269, 0] := by
  rw [show D2M8K2.u15001 = KTree.node D2M8K2.u14985 (nat_lit 32710827) (nat_lit 2442323262) (nat_lit 0) D2M8K2.u15000 from rfl, totK_node, atot14985, atot15000]
  decide +kernel

theorem arows15032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15032 = true := by
  rw [show D2M8K2.u15032 = KTree.node D2M8K2.u15016 (nat_lit 32755258) (nat_lit 3445479231) (nat_lit 0) D2M8K2.u15031 from rfl, allE_node, arows15016, irow15032, arows15031]
  all_goals rfl

theorem atot15032 : totK PD2M8K2 D2M8K2.u15032 = [0, 2016980526712, 9099931148692, 12267987751684, 4827688689978, 418404187034, 6363931553, 0] := by
  rw [show D2M8K2.u15032 = KTree.node D2M8K2.u15016 (nat_lit 32755258) (nat_lit 3445479231) (nat_lit 0) D2M8K2.u15031 from rfl, totK_node, atot15016, atot15031]
  decide +kernel

theorem arows15064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15064 = true := by
  rw [show D2M8K2.u15064 = KTree.node D2M8K2.u15048 (nat_lit 32832719) (nat_lit 2765317775) (nat_lit 0) D2M8K2.u15063 from rfl, allE_node, arows15048, irow15064, arows15063]
  all_goals rfl

theorem atot15064 : totK PD2M8K2 D2M8K2.u15064 = [0, 1622805746891, 7607834020049, 11874534847548, 6434684071599, 979890817427, 32664957003, 0] := by
  rw [show D2M8K2.u15064 = KTree.node D2M8K2.u15048 (nat_lit 32832719) (nat_lit 2765317775) (nat_lit 0) D2M8K2.u15063 from rfl, totK_node, atot15048, atot15063]
  decide +kernel

theorem arows15095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15095 = true := by
  rw [show D2M8K2.u15095 = KTree.node D2M8K2.u15079 (nat_lit 32867540) (nat_lit 3635762819) (nat_lit 0) D2M8K2.u15094 from rfl, allE_node, arows15079, irow15095, arows15094]
  all_goals rfl

theorem atot15095 : totK PD2M8K2 D2M8K2.u15095 = [0, 1925859434549, 9061251983868, 12598367309257, 4574529414746, 318977033891, 1369150432, 0] := by
  rw [show D2M8K2.u15095 = KTree.node D2M8K2.u15079 (nat_lit 32867540) (nat_lit 3635762819) (nat_lit 0) D2M8K2.u15094 from rfl, totK_node, atot15079, atot15094]
  decide +kernel

theorem arows15129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15129 = true := by
  rw [show D2M8K2.u15129 = KTree.node D2M8K2.u15113 (nat_lit 32950375) (nat_lit 2383858899) (nat_lit 0) D2M8K2.u15128 from rfl, allE_node, arows15113, irow15129, arows15128]
  all_goals rfl

theorem atot15129 : totK PD2M8K2 D2M8K2.u15129 = [0, 1816813455696, 8598512751087, 12435012945737, 5363691822829, 502710622712, 6601594569, 0] := by
  rw [show D2M8K2.u15129 = KTree.node D2M8K2.u15113 (nat_lit 32950375) (nat_lit 2383858899) (nat_lit 0) D2M8K2.u15128 from rfl, totK_node, atot15113, atot15128]
  decide +kernel

theorem arows15160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15160 = true := by
  rw [show D2M8K2.u15160 = KTree.node D2M8K2.u15144 (nat_lit 32990922) (nat_lit 3360193961) (nat_lit 0) D2M8K2.u15159 from rfl, allE_node, arows15144, irow15160, arows15159]
  all_goals rfl

theorem atot15160 : totK PD2M8K2 D2M8K2.u15160 = [0, 1985588590772, 8729450549096, 12219296163607, 5381227218157, 513098577524, 6665697270, 0] := by
  rw [show D2M8K2.u15160 = KTree.node D2M8K2.u15144 (nat_lit 32990922) (nat_lit 3360193961) (nat_lit 0) D2M8K2.u15159 from rfl, totK_node, atot15144, atot15159]
  decide +kernel

theorem arows15192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15192 = true := by
  rw [show D2M8K2.u15192 = KTree.node D2M8K2.u15176 (nat_lit 33035056) (nat_lit 2388312848) (nat_lit 0) D2M8K2.u15191 from rfl, allE_node, arows15176, irow15192, arows15191]
  all_goals rfl

theorem atot15192 : totK PD2M8K2 D2M8K2.u15192 = [0, 2252102573292, 9756861320734, 12414634051767, 4044687205742, 241857263117, 1138244013, 0] := by
  rw [show D2M8K2.u15192 = KTree.node D2M8K2.u15176 (nat_lit 33035056) (nat_lit 2388312848) (nat_lit 0) D2M8K2.u15191 from rfl, totK_node, atot15176, atot15191]
  decide +kernel

theorem arows15223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15223 = true := by
  rw [show D2M8K2.u15223 = KTree.node D2M8K2.u15207 (nat_lit 33078343) (nat_lit 2373002800) (nat_lit 0) D2M8K2.u15222 from rfl, allE_node, arows15207, irow15223, arows15222]
  all_goals rfl

theorem atot15223 : totK PD2M8K2 D2M8K2.u15223 = [0, 1010969223297, 6336782907735, 12432834057063, 7825337626200, 1161601805894, 34241849113, 0] := by
  rw [show D2M8K2.u15223 = KTree.node D2M8K2.u15207 (nat_lit 33078343) (nat_lit 2373002800) (nat_lit 0) D2M8K2.u15222 from rfl, totK_node, atot15207, atot15222]
  decide +kernel

theorem arows15256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15256 = true := by
  rw [show D2M8K2.u15256 = KTree.node D2M8K2.u15240 (nat_lit 33115412) (nat_lit 3255924874) (nat_lit 0) D2M8K2.u15255 from rfl, allE_node, arows15240, irow15256, arows15255]
  all_goals rfl

theorem atot15256 : totK PD2M8K2 D2M8K2.u15256 = [0, 0, 2242647616313, 9968491704867, 12474415698464, 3492667541690, 222517737428, 1369150432] := by
  rw [show D2M8K2.u15256 = KTree.node D2M8K2.u15240 (nat_lit 33115412) (nat_lit 3255924874) (nat_lit 0) D2M8K2.u15255 from rfl, totK_node, atot15240, atot15255]
  decide +kernel

theorem arows15287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15287 = true := by
  rw [show D2M8K2.u15287 = KTree.node D2M8K2.u15271 (nat_lit 33221064) (nat_lit 3583817864) (nat_lit 0) D2M8K2.u15286 from rfl, allE_node, arows15271, irow15287, arows15286]
  all_goals rfl

theorem atot15287 : totK PD2M8K2 D2M8K2.u15287 = [0, 0, 3541156058578, 12488906983034, 11103379322938, 1800851230432, 44859635443, 0] := by
  rw [show D2M8K2.u15287 = KTree.node D2M8K2.u15271 (nat_lit 33221064) (nat_lit 3583817864) (nat_lit 0) D2M8K2.u15286 from rfl, totK_node, atot15271, atot15286]
  decide +kernel

theorem arows15319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15319 = true := by
  rw [show D2M8K2.u15319 = KTree.node D2M8K2.u15303 (nat_lit 33303864) (nat_lit 3640629068) (nat_lit 0) D2M8K2.u15318 from rfl, allE_node, arows15303, irow15319, arows15318]
  all_goals rfl

theorem atot15319 : totK PD2M8K2 D2M8K2.u15319 = [0, 0, 3498676990498, 12541287521037, 11202098003278, 1659597792364, 30987500609, 0] := by
  rw [show D2M8K2.u15319 = KTree.node D2M8K2.u15303 (nat_lit 33303864) (nat_lit 3640629068) (nat_lit 0) D2M8K2.u15318 from rfl, totK_node, atot15303, atot15318]
  decide +kernel

theorem arows15350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15350 = true := by
  rw [show D2M8K2.u15350 = KTree.node D2M8K2.u15334 (nat_lit 33400109) (nat_lit 2023480268) (nat_lit 0) D2M8K2.u15349 from rfl, allE_node, arows15334, irow15350, arows15349]
  all_goals rfl

theorem atot15350 : totK PD2M8K2 D2M8K2.u15350 = [0, 2117768858604, 8660841124037, 11371438552106, 5690028259241, 1129888720742, 59096198860, 0] := by
  rw [show D2M8K2.u15350 = KTree.node D2M8K2.u15334 (nat_lit 33400109) (nat_lit 2023480268) (nat_lit 0) D2M8K2.u15349 from rfl, totK_node, atot15334, atot15349]
  decide +kernel

theorem arows15386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15386 = true := by
  rw [show D2M8K2.u15386 = KTree.node D2M8K2.u15370 (nat_lit 33432173) (nat_lit 2043094069) (nat_lit 0) D2M8K2.u15385 from rfl, allE_node, arows15370, irow15386, arows15385]
  all_goals rfl

theorem atot15386 : totK PD2M8K2 D2M8K2.u15386 = [0, 1993496677444, 8409037746226, 11675977198460, 5968572200990, 851450797141, 17142851236, 0] := by
  rw [show D2M8K2.u15386 = KTree.node D2M8K2.u15370 (nat_lit 33432173) (nat_lit 2043094069) (nat_lit 0) D2M8K2.u15385 from rfl, totK_node, atot15370, atot15385]
  decide +kernel

theorem arows15417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15417 = true := by
  rw [show D2M8K2.u15417 = KTree.node D2M8K2.u15401 (nat_lit 33471914) (nat_lit 4124048370) (nat_lit 0) D2M8K2.u15416 from rfl, allE_node, arows15401, irow15417, arows15416]
  all_goals rfl

theorem atot15417 : totK PD2M8K2 D2M8K2.u15417 = [0, 1994043766943, 8759981973314, 12122623895049, 5474228539010, 597099876699, 10797810883, 0] := by
  rw [show D2M8K2.u15417 = KTree.node D2M8K2.u15401 (nat_lit 33471914) (nat_lit 4124048370) (nat_lit 0) D2M8K2.u15416 from rfl, totK_node, atot15401, atot15416]
  decide +kernel

theorem arows15449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15449 = true := by
  rw [show D2M8K2.u15449 = KTree.node D2M8K2.u15433 (nat_lit 33513578) (nat_lit 4204973949) (nat_lit 0) D2M8K2.u15448 from rfl, allE_node, arows15433, irow15449, arows15448]
  all_goals rfl

theorem atot15449 : totK PD2M8K2 D2M8K2.u15449 = [0, 1658284530265, 8033727426106, 12287474193401, 6214650637264, 726836593270, 12143333308, 0] := by
  rw [show D2M8K2.u15449 = KTree.node D2M8K2.u15433 (nat_lit 33513578) (nat_lit 4204973949) (nat_lit 0) D2M8K2.u15448 from rfl, totK_node, atot15433, atot15448]
  decide +kernel

theorem arows15480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15480 = true := by
  rw [show D2M8K2.u15480 = KTree.node D2M8K2.u15464 (nat_lit 33556822) (nat_lit 2951961772) (nat_lit 0) D2M8K2.u15479 from rfl, allE_node, arows15464, irow15480, arows15479]
  all_goals rfl

theorem atot15480 : totK PD2M8K2 D2M8K2.u15480 = [0, 2047119486658, 9142611800071, 12555220290734, 4885800181757, 351633474714, 1493059870, 0] := by
  rw [show D2M8K2.u15480 = KTree.node D2M8K2.u15464 (nat_lit 33556822) (nat_lit 2951961772) (nat_lit 0) D2M8K2.u15479 from rfl, totK_node, atot15464, atot15479]
  decide +kernel

theorem arows15513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15513 = true := by
  rw [show D2M8K2.u15513 = KTree.node D2M8K2.u15497 (nat_lit 33841838) (nat_lit 3418036823) (nat_lit 0) D2M8K2.u15512 from rfl, allE_node, arows15497, irow15513, arows15512]
  all_goals rfl

theorem atot15513 : totK PD2M8K2 D2M8K2.u15513 = [0, 1976552160701, 8194981669121, 11356131910993, 6196671297158, 1005275064589, 32872698681, 0] := by
  rw [show D2M8K2.u15513 = KTree.node D2M8K2.u15497 (nat_lit 33841838) (nat_lit 3418036823) (nat_lit 0) D2M8K2.u15512 from rfl, totK_node, atot15497, atot15512]
  decide +kernel

theorem arows15544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15544 = true := by
  rw [show D2M8K2.u15544 = KTree.node D2M8K2.u15528 (nat_lit 33887405) (nat_lit 2025995828) (nat_lit 0) D2M8K2.u15543 from rfl, allE_node, arows15528, irow15544, arows15543]
  all_goals rfl

theorem atot15544 : totK PD2M8K2 D2M8K2.u15544 = [0, 2001094274040, 9155879801406, 12645362725136, 4748219770708, 323031976766, 1369150432, 0] := by
  rw [show D2M8K2.u15544 = KTree.node D2M8K2.u15528 (nat_lit 33887405) (nat_lit 2025995828) (nat_lit 0) D2M8K2.u15543 from rfl, totK_node, atot15528, atot15543]
  decide +kernel

theorem arows15576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15576 = true := by
  rw [show D2M8K2.u15576 = KTree.node D2M8K2.u15560 (nat_lit 33919256) (nat_lit 3732255902) (nat_lit 0) D2M8K2.u15575 from rfl, allE_node, arows15560, irow15576, arows15575]
  all_goals rfl

theorem atot15576 : totK PD2M8K2 D2M8K2.u15576 = [0, 1282600422507, 6632835610864, 11724151084633, 7868832289680, 1478300653241, 50450299231, 0] := by
  rw [show D2M8K2.u15576 = KTree.node D2M8K2.u15560 (nat_lit 33919256) (nat_lit 3732255902) (nat_lit 0) D2M8K2.u15575 from rfl, totK_node, atot15560, atot15575]
  decide +kernel

theorem arows15607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15607 = true := by
  rw [show D2M8K2.u15607 = KTree.node D2M8K2.u15591 (nat_lit 33951960) (nat_lit 3552817002) (nat_lit 0) D2M8K2.u15606 from rfl, allE_node, arows15591, irow15607, arows15606]
  all_goals rfl

theorem atot15607 : totK PD2M8K2 D2M8K2.u15607 = [0, 1626636878246, 7937547928235, 12250730788898, 6001817788001, 745859776281, 18797058808, 0] := by
  rw [show D2M8K2.u15607 = KTree.node D2M8K2.u15591 (nat_lit 33951960) (nat_lit 3552817002) (nat_lit 0) D2M8K2.u15606 from rfl, totK_node, atot15591, atot15606]
  decide +kernel

theorem arows15641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15641 = true := by
  rw [show D2M8K2.u15641 = KTree.node D2M8K2.u15625 (nat_lit 34035386) (nat_lit 3974136014) (nat_lit 0) D2M8K2.u15640 from rfl, allE_node, arows15625, irow15641, arows15640]
  all_goals rfl

theorem atot15641 : totK PD2M8K2 D2M8K2.u15641 = [0, 2103099043256, 9160423846683, 12289863328321, 4809082645142, 396439138298, 6115358396, 0] := by
  rw [show D2M8K2.u15641 = KTree.node D2M8K2.u15625 (nat_lit 34035386) (nat_lit 3974136014) (nat_lit 0) D2M8K2.u15640 from rfl, totK_node, atot15625, atot15640]
  decide +kernel

theorem arows15672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15672 = true := by
  rw [show D2M8K2.u15672 = KTree.node D2M8K2.u15656 (nat_lit 34076792) (nat_lit 3721344083) (nat_lit 0) D2M8K2.u15671 from rfl, allE_node, arows15656, irow15672, arows15671]
  all_goals rfl

theorem atot15672 : totK PD2M8K2 D2M8K2.u15672 = [0, 788562694442, 5878708352633, 12566696209704, 8326936375671, 1232591245730, 34241849113, 0] := by
  rw [show D2M8K2.u15672 = KTree.node D2M8K2.u15656 (nat_lit 34076792) (nat_lit 3721344083) (nat_lit 0) D2M8K2.u15671 from rfl, totK_node, atot15656, atot15671]
  decide +kernel

theorem arows15704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15704 = true := by
  rw [show D2M8K2.u15704 = KTree.node D2M8K2.u15688 (nat_lit 34117982) (nat_lit 3852639362) (nat_lit 0) D2M8K2.u15703 from rfl, allE_node, arows15688, irow15704, arows15703]
  all_goals rfl

theorem atot15704 : totK PD2M8K2 D2M8K2.u15704 = [0, 0, 2502661781933, 10490443515411, 12247590657515, 3323286032806, 168620717466, 1275377855] := by
  rw [show D2M8K2.u15704 = KTree.node D2M8K2.u15688 (nat_lit 34117982) (nat_lit 3852639362) (nat_lit 0) D2M8K2.u15703 from rfl, totK_node, atot15688, atot15703]
  decide +kernel

theorem arows15735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15735 = true := by
  rw [show D2M8K2.u15735 = KTree.node D2M8K2.u15719 (nat_lit 34181976) (nat_lit 2667763121) (nat_lit 0) D2M8K2.u15734 from rfl, allE_node, arows15719, irow15735, arows15734]
  all_goals rfl

theorem atot15735 : totK PD2M8K2 D2M8K2.u15735 = [0, 0, 2783411924231, 10751557374207, 11700775464655, 3318661106080, 194290810814, 1206465782] := by
  rw [show D2M8K2.u15735 = KTree.node D2M8K2.u15719 (nat_lit 34181976) (nat_lit 2667763121) (nat_lit 0) D2M8K2.u15734 from rfl, totK_node, atot15719, atot15734]
  decide +kernel

theorem arows15768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15768 = true := by
  rw [show D2M8K2.u15768 = KTree.node D2M8K2.u15752 (nat_lit 34270782) (nat_lit 4054141798) (nat_lit 0) D2M8K2.u15767 from rfl, allE_node, arows15752, irow15768, arows15767]
  all_goals rfl

theorem atot15768 : totK PD2M8K2 D2M8K2.u15768 = [0, 0, 3230091306877, 11462984918000, 10965894082172, 2846528959016, 252153671653, 5395128787] := by
  rw [show D2M8K2.u15768 = KTree.node D2M8K2.u15752 (nat_lit 34270782) (nat_lit 4054141798) (nat_lit 0) D2M8K2.u15767 from rfl, totK_node, atot15752, atot15767]
  decide +kernel

theorem arows15799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15799 = true := by
  rw [show D2M8K2.u15799 = KTree.node D2M8K2.u15783 (nat_lit 34352358) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u15798 from rfl, allE_node, arows15783, irow15799, arows15798]
  all_goals rfl

theorem atot15799 : totK PD2M8K2 D2M8K2.u15799 = [0, 1976745319685, 8683292720648, 11817616952855, 5356581054822, 784621510864, 27382469208, 0] := by
  rw [show D2M8K2.u15799 = KTree.node D2M8K2.u15783 (nat_lit 34352358) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u15798 from rfl, totK_node, atot15783, atot15798]
  decide +kernel

theorem arows15831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15831 = true := by
  rw [show D2M8K2.u15831 = KTree.node D2M8K2.u15815 (nat_lit 34393840) (nat_lit 2383035646) (nat_lit 0) D2M8K2.u15830 from rfl, allE_node, arows15815, irow15831, arows15830]
  all_goals rfl

theorem atot15831 : totK PD2M8K2 D2M8K2.u15831 = [0, 2001317120088, 8711867543252, 12015965333758, 5550337810394, 839007017335, 34639773963, 0] := by
  rw [show D2M8K2.u15831 = KTree.node D2M8K2.u15815 (nat_lit 34393840) (nat_lit 2383035646) (nat_lit 0) D2M8K2.u15830 from rfl, totK_node, atot15815, atot15830]
  decide +kernel

theorem arows15862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15862 = true := by
  rw [show D2M8K2.u15862 = KTree.node D2M8K2.u15846 (nat_lit 34467822) (nat_lit 3933810565) (nat_lit 0) D2M8K2.u15861 from rfl, allE_node, arows15846, irow15862, arows15861]
  all_goals rfl

theorem atot15862 : totK PD2M8K2 D2M8K2.u15862 = [0, 2107275558365, 8735992792677, 11635259387838, 5640411249066, 794424880713, 15936385454, 0] := by
  rw [show D2M8K2.u15862 = KTree.node D2M8K2.u15846 (nat_lit 34467822) (nat_lit 3933810565) (nat_lit 0) D2M8K2.u15861 from rfl, totK_node, atot15846, atot15861]
  decide +kernel

theorem arows15897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15897 = true := by
  rw [show D2M8K2.u15897 = KTree.node D2M8K2.u15881 (nat_lit 34504837) (nat_lit 1377495917) (nat_lit 0) D2M8K2.u15896 from rfl, allE_node, arows15881, irow15897, arows15896]
  all_goals rfl

theorem atot15897 : totK PD2M8K2 D2M8K2.u15897 = [0, 1651660593053, 7995208922099, 12223389097912, 6045980545317, 748083615236, 19065934916, 0] := by
  rw [show D2M8K2.u15897 = KTree.node D2M8K2.u15881 (nat_lit 34504837) (nat_lit 1377495917) (nat_lit 0) D2M8K2.u15896 from rfl, totK_node, atot15881, atot15896]
  decide +kernel

theorem arows15928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15928 = true := by
  rw [show D2M8K2.u15928 = KTree.node D2M8K2.u15912 (nat_lit 34550812) (nat_lit 3710354490) (nat_lit 0) D2M8K2.u15927 from rfl, allE_node, arows15912, irow15928, arows15927]
  all_goals rfl

theorem atot15928 : totK PD2M8K2 D2M8K2.u15928 = [0, 2042848924932, 8961904283704, 12339725148104, 5061461249712, 429888099281, 6115358396, 0] := by
  rw [show D2M8K2.u15928 = KTree.node D2M8K2.u15912 (nat_lit 34550812) (nat_lit 3710354490) (nat_lit 0) D2M8K2.u15927 from rfl, totK_node, atot15912, atot15927]
  decide +kernel

theorem arows15960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15960 = true := by
  rw [show D2M8K2.u15960 = KTree.node D2M8K2.u15944 (nat_lit 34587390) (nat_lit 3841238990) (nat_lit 0) D2M8K2.u15959 from rfl, allE_node, arows15944, irow15960, arows15959]
  all_goals rfl

theorem atot15960 : totK PD2M8K2 D2M8K2.u15960 = [0, 0, 3814666024432, 12719322379760, 10504739967969, 1631012443772, 41958321377, 0] := by
  rw [show D2M8K2.u15960 = KTree.node D2M8K2.u15944 (nat_lit 34587390) (nat_lit 3841238990) (nat_lit 0) D2M8K2.u15959 from rfl, totK_node, atot15944, atot15959]
  decide +kernel

theorem arows15991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15991 = true := by
  rw [show D2M8K2.u15991 = KTree.node D2M8K2.u15975 (nat_lit 34635565) (nat_lit 860573647) (nat_lit 2) D2M8K2.u15990 from rfl, allE_node, arows15975, irow15991, arows15990]
  all_goals rfl

theorem atot15991 : totK PD2M8K2 D2M8K2.u15991 = [0, 0, 2615158559146, 10500151222351, 12116882033686, 3455490537522, 179224860464, 1310517177] := by
  rw [show D2M8K2.u15991 = KTree.node D2M8K2.u15975 (nat_lit 34635565) (nat_lit 860573647) (nat_lit 2) D2M8K2.u15990 from rfl, totK_node, atot15975, atot15990]
  decide +kernel

theorem arows16024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16024 = true := by
  rw [show D2M8K2.u16024 = KTree.node D2M8K2.u16008 (nat_lit 34733743) (nat_lit 2447444894) (nat_lit 0) D2M8K2.u16023 from rfl, allE_node, arows16008, irow16024, arows16023]
  all_goals rfl

theorem atot16024 : totK PD2M8K2 D2M8K2.u16024 = [0, 0, 2136155924557, 9422030322707, 12162346713668, 4474826947162, 400944969224, 6643327963] := by
  rw [show D2M8K2.u16024 = KTree.node D2M8K2.u16008 (nat_lit 34733743) (nat_lit 2447444894) (nat_lit 0) D2M8K2.u16023 from rfl, totK_node, atot16008, atot16023]
  decide +kernel

theorem arows16055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16055 = true := by
  rw [show D2M8K2.u16055 = KTree.node D2M8K2.u16039 (nat_lit 34803661) (nat_lit 1389735202) (nat_lit 0) D2M8K2.u16054 from rfl, allE_node, arows16039, irow16055, arows16054]
  all_goals rfl

theorem atot16055 : totK PD2M8K2 D2M8K2.u16055 = [0, 847096328040, 5608137943206, 11871324728830, 8872437810597, 1702626699121, 58695292366, 0] := by
  rw [show D2M8K2.u16055 = KTree.node D2M8K2.u16039 (nat_lit 34803661) (nat_lit 1389735202) (nat_lit 0) D2M8K2.u16054 from rfl, totK_node, atot16039, atot16054]
  decide +kernel

theorem arows16087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16087 = true := by
  rw [show D2M8K2.u16087 = KTree.node D2M8K2.u16071 (nat_lit 35357289) (nat_lit 1879737813) (nat_lit 0) D2M8K2.u16086 from rfl, allE_node, arows16071, irow16087, arows16086]
  all_goals rfl

theorem atot16087 : totK PD2M8K2 D2M8K2.u16087 = [0, 2019582649184, 9084444878411, 12562410280022, 4741786651062, 305385688318, 1369150432, 0] := by
  rw [show D2M8K2.u16087 = KTree.node D2M8K2.u16071 (nat_lit 35357289) (nat_lit 1879737813) (nat_lit 0) D2M8K2.u16086 from rfl, totK_node, atot16071, atot16086]
  decide +kernel

theorem arows16118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16118 = true := by
  rw [show D2M8K2.u16118 = KTree.node D2M8K2.u16102 (nat_lit 35401893) (nat_lit 1383261414) (nat_lit 0) D2M8K2.u16117 from rfl, allE_node, arows16102, irow16118, arows16117]
  all_goals rfl

theorem atot16118 : totK PD2M8K2 D2M8K2.u16118 = [0, 1172193504829, 6714030989918, 12176125906524, 7699489174435, 1308229909631, 37477867745, 0] := by
  rw [show D2M8K2.u16118 = KTree.node D2M8K2.u16102 (nat_lit 35401893) (nat_lit 1383261414) (nat_lit 0) D2M8K2.u16117 from rfl, totK_node, atot16102, atot16117]
  decide +kernel

theorem arows16152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16152 = true := by
  rw [show D2M8K2.u16152 = KTree.node D2M8K2.u16136 (nat_lit 35434416) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u16151 from rfl, allE_node, arows16136, irow16152, arows16151]
  all_goals rfl

theorem atot16152 : totK PD2M8K2 D2M8K2.u16152 = [0, 2018243269309, 8759396632085, 11980682044660, 5353650962024, 657056723794, 18072244084, 0] := by
  rw [show D2M8K2.u16152 = KTree.node D2M8K2.u16136 (nat_lit 35434416) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u16151 from rfl, totK_node, atot16136, atot16151]
  decide +kernel

theorem arows16183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16183 = true := by
  rw [show D2M8K2.u16183 = KTree.node D2M8K2.u16167 (nat_lit 35472516) (nat_lit 3267741289) (nat_lit 0) D2M8K2.u16182 from rfl, allE_node, arows16167, irow16183, arows16182]
  all_goals rfl

theorem atot16183 : totK PD2M8K2 D2M8K2.u16183 = [0, 2018750390566, 8869845803346, 12220483940203, 5301937816444, 458700188243, 3432551270, 0] := by
  rw [show D2M8K2.u16183 = KTree.node D2M8K2.u16167 (nat_lit 35472516) (nat_lit 3267741289) (nat_lit 0) D2M8K2.u16182 from rfl, totK_node, atot16167, atot16182]
  decide +kernel

theorem arows16215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16215 = true := by
  rw [show D2M8K2.u16215 = KTree.node D2M8K2.u16199 (nat_lit 35549613) (nat_lit 1424888993) (nat_lit 0) D2M8K2.u16214 from rfl, allE_node, arows16199, irow16215, arows16214]
  all_goals rfl

theorem atot16215 : totK PD2M8K2 D2M8K2.u16215 = [0, 2136927762780, 8982856739820, 11956777185367, 5259467613413, 537097669488, 10046265537, 0] := by
  rw [show D2M8K2.u16215 = KTree.node D2M8K2.u16199 (nat_lit 35549613) (nat_lit 1424888993) (nat_lit 0) D2M8K2.u16214 from rfl, totK_node, atot16199, atot16214]
  decide +kernel

theorem arows16246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16246 = true := by
  rw [show D2M8K2.u16246 = KTree.node D2M8K2.u16230 (nat_lit 35584898) (nat_lit 2628092425) (nat_lit 0) D2M8K2.u16245 from rfl, allE_node, arows16230, irow16246, arows16245]
  all_goals rfl

theorem atot16246 : totK PD2M8K2 D2M8K2.u16246 = [0, 0, 3503256729569, 12255546481460, 10863357091668, 1981143070286, 66346205371, 0] := by
  rw [show D2M8K2.u16246 = KTree.node D2M8K2.u16230 (nat_lit 35584898) (nat_lit 2628092425) (nat_lit 0) D2M8K2.u16245 from rfl, totK_node, atot16230, atot16245]
  decide +kernel

theorem arows16279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16279 = true := by
  rw [show D2M8K2.u16279 = KTree.node D2M8K2.u16263 (nat_lit 35631494) (nat_lit 3315506828) (nat_lit 0) D2M8K2.u16278 from rfl, allE_node, arows16263, irow16279, arows16278]
  all_goals rfl

theorem atot16279 : totK PD2M8K2 D2M8K2.u16279 = [0, 0, 2433769005611, 10027577448726, 12143932491154, 3932103105192, 246043241503, 1369150432] := by
  rw [show D2M8K2.u16279 = KTree.node D2M8K2.u16263 (nat_lit 35631494) (nat_lit 3315506828) (nat_lit 0) D2M8K2.u16278 from rfl, totK_node, atot16263, atot16278]
  decide +kernel

theorem arows16310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16310 = true := by
  rw [show D2M8K2.u16310 = KTree.node D2M8K2.u16294 (nat_lit 35687278) (nat_lit 3778510033) (nat_lit 0) D2M8K2.u16309 from rfl, allE_node, arows16294, irow16310, arows16309]
  all_goals rfl

theorem atot16310 : totK PD2M8K2 D2M8K2.u16310 = [0, 0, 2208806345158, 9575853780907, 12164175065730, 4338261859666, 371638128318, 6301476269] := by
  rw [show D2M8K2.u16310 = KTree.node D2M8K2.u16294 (nat_lit 35687278) (nat_lit 3778510033) (nat_lit 0) D2M8K2.u16309 from rfl, totK_node, atot16294, atot16309]
  decide +kernel

theorem arows16342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16342 = true := by
  rw [show D2M8K2.u16342 = KTree.node D2M8K2.u16326 (nat_lit 35729730) (nat_lit 3015955748) (nat_lit 0) D2M8K2.u16341 from rfl, allE_node, arows16326, irow16342, arows16341]
  all_goals rfl

theorem atot16342 : totK PD2M8K2 D2M8K2.u16342 = [0, 0, 2253150022140, 9683767767723, 12034780652318, 4343073083773, 376694559304, 6363931553] := by
  rw [show D2M8K2.u16342 = KTree.node D2M8K2.u16326 (nat_lit 35729730) (nat_lit 3015955748) (nat_lit 0) D2M8K2.u16341 from rfl, totK_node, atot16326, atot16341]
  decide +kernel

theorem arows16373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16373 = true := by
  rw [show D2M8K2.u16373 = KTree.node D2M8K2.u16357 (nat_lit 35812200) (nat_lit 3443070030) (nat_lit 0) D2M8K2.u16372 from rfl, allE_node, arows16357, irow16373, arows16372]
  all_goals rfl

theorem atot16373 : totK PD2M8K2 D2M8K2.u16373 = [0, 0, 1288971957659, 7077062601880, 12264661152501, 6801436037690, 1005851697596, 32664957003] := by
  rw [show D2M8K2.u16373 = KTree.node D2M8K2.u16357 (nat_lit 35812200) (nat_lit 3443070030) (nat_lit 0) D2M8K2.u16372 from rfl, totK_node, atot16357, atot16372]
  decide +kernel

theorem arows62 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u62 = true := by
  rw [show D2M8K2.u62 = KTree.node D2M8K2.u30 (nat_lit 38709) (nat_lit 1620045827) (nat_lit 0) D2M8K2.u61 from rfl, allE_node, arows30, irow62, arows61]
  all_goals rfl

theorem atot62 : totK PD2M8K2 D2M8K2.u62 = [4139289329579, 18262090912351, 24483643551620, 9645918260117, 886403162661, 15591813588, 0, 0] := by
  rw [show D2M8K2.u62 = KTree.node D2M8K2.u30 (nat_lit 38709) (nat_lit 1620045827) (nat_lit 0) D2M8K2.u61 from rfl, totK_node, atot30, atot61]
  decide +kernel

theorem arows125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u125 = true := by
  rw [show D2M8K2.u125 = KTree.node D2M8K2.u93 (nat_lit 157139) (nat_lit 2871671772) (nat_lit 0) D2M8K2.u124 from rfl, allE_node, arows93, irow125, arows124]
  all_goals rfl

theorem atot125 : totK PD2M8K2 D2M8K2.u125 = [4022317113911, 17481800307185, 23963550585082, 10668375362005, 1179336590086, 24778574581, 0, 0] := by
  rw [show D2M8K2.u125 = KTree.node D2M8K2.u93 (nat_lit 157139) (nat_lit 2871671772) (nat_lit 0) D2M8K2.u124 from rfl, totK_node, atot93, atot124]
  decide +kernel

theorem arows189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u189 = true := by
  rw [show D2M8K2.u189 = KTree.node D2M8K2.u157 (nat_lit 230464) (nat_lit 3751396352) (nat_lit 0) D2M8K2.u188 from rfl, allE_node, arows157, irow189, arows188]
  all_goals rfl

theorem atot189 : totK PD2M8K2 D2M8K2.u189 = [2019269348258, 12523439456269, 24520612350488, 15860071766213, 2396090339809, 70137532845, 0, 0] := by
  rw [show D2M8K2.u189 = KTree.node D2M8K2.u157 (nat_lit 230464) (nat_lit 3751396352) (nat_lit 0) D2M8K2.u188 from rfl, totK_node, atot157, atot188]
  decide +kernel

theorem arows252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u252 = true := by
  rw [show D2M8K2.u252 = KTree.node D2M8K2.u220 (nat_lit 350726) (nat_lit 2562015365) (nat_lit 0) D2M8K2.u251 from rfl, allE_node, arows220, irow252, arows251]
  all_goals rfl

theorem atot252 : totK PD2M8K2 D2M8K2.u252 = [0, 5400064274339, 21401192486796, 23784245182707, 6300549545564, 367482936959, 1369150432, 0] := by
  rw [show D2M8K2.u252 = KTree.node D2M8K2.u220 (nat_lit 350726) (nat_lit 2562015365) (nat_lit 0) D2M8K2.u251 from rfl, totK_node, atot220, atot251]
  decide +kernel

theorem arows317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u317 = true := by
  rw [show D2M8K2.u317 = KTree.node D2M8K2.u285 (nat_lit 1002866) (nat_lit 4030184258) (nat_lit 0) D2M8K2.u316 from rfl, allE_node, arows285, irow317, arows316]
  all_goals rfl

theorem atot317 : totK PD2M8K2 D2M8K2.u317 = [2531169229408, 13626781284176, 24170908587329, 14862802527104, 2338895505851, 62707891223, 0, 0] := by
  rw [show D2M8K2.u317 = KTree.node D2M8K2.u285 (nat_lit 1002866) (nat_lit 4030184258) (nat_lit 0) D2M8K2.u316 from rfl, totK_node, atot285, atot316]
  decide +kernel

theorem arows380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u380 = true := by
  rw [show D2M8K2.u380 = KTree.node D2M8K2.u348 (nat_lit 1082137) (nat_lit 1176117592) (nat_lit 0) D2M8K2.u379 from rfl, allE_node, arows348, irow380, arows379]
  all_goals rfl

theorem atot380 : totK PD2M8K2 D2M8K2.u380 = [3268065192031, 15388673255060, 23689844141817, 12977914504698, 2107724514532, 71596314066, 0, 0] := by
  rw [show D2M8K2.u380 = KTree.node D2M8K2.u348 (nat_lit 1082137) (nat_lit 1176117592) (nat_lit 0) D2M8K2.u379 from rfl, totK_node, atot348, atot379]
  decide +kernel

theorem arows444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u444 = true := by
  rw [show D2M8K2.u444 = KTree.node D2M8K2.u412 (nat_lit 1197029) (nat_lit 2326679395) (nat_lit 0) D2M8K2.u443 from rfl, allE_node, arows412, irow444, arows443]
  all_goals rfl

theorem atot444 : totK PD2M8K2 D2M8K2.u444 = [3974952489386, 17609658257420, 24373483866137, 10532418816763, 1006758164940, 12305484365, 0, 0] := by
  rw [show D2M8K2.u444 = KTree.node D2M8K2.u412 (nat_lit 1197029) (nat_lit 2326679395) (nat_lit 0) D2M8K2.u443 from rfl, totK_node, atot412, atot443]
  decide +kernel

theorem arows507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u507 = true := by
  rw [show D2M8K2.u507 = KTree.node D2M8K2.u475 (nat_lit 1276222) (nat_lit 3868888697) (nat_lit 0) D2M8K2.u506 from rfl, allE_node, arows475, irow507, arows506]
  all_goals rfl

theorem atot507 : totK PD2M8K2 D2M8K2.u507 = [0, 5567574139314, 21579856862195, 23529841473267, 6373340175415, 333632639771, 1275377855, 0] := by
  rw [show D2M8K2.u507 = KTree.node D2M8K2.u475 (nat_lit 1276222) (nat_lit 3868888697) (nat_lit 0) D2M8K2.u506 from rfl, totK_node, atot475, atot506]
  decide +kernel

theorem arows573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u573 = true := by
  rw [show D2M8K2.u573 = KTree.node D2M8K2.u541 (nat_lit 1416486) (nat_lit 3804786856) (nat_lit 0) D2M8K2.u572 from rfl, allE_node, arows541, irow573, arows572]
  all_goals rfl

theorem atot573 : totK PD2M8K2 D2M8K2.u573 = [0, 3694321870900, 17342386875992, 24578902857445, 10103231185424, 1065300973307, 24680175954, 0] := by
  rw [show D2M8K2.u573 = KTree.node D2M8K2.u541 (nat_lit 1416486) (nat_lit 3804786856) (nat_lit 0) D2M8K2.u572 from rfl, totK_node, atot541, atot572]
  decide +kernel

theorem arows636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u636 = true := by
  rw [show D2M8K2.u636 = KTree.node D2M8K2.u604 (nat_lit 1514665) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u635 from rfl, allE_node, arows604, irow636, arows635]
  all_goals rfl

theorem atot636 : totK PD2M8K2 D2M8K2.u636 = [3692611367677, 16682719211331, 23906350949387, 11587493563921, 1742485347427, 67208663628, 0, 0] := by
  rw [show D2M8K2.u636 = KTree.node D2M8K2.u604 (nat_lit 1514665) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u635 from rfl, totK_node, atot604, atot635]
  decide +kernel

theorem arows700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u700 = true := by
  rw [show D2M8K2.u700 = KTree.node D2M8K2.u668 (nat_lit 1637146) (nat_lit 3709670711) (nat_lit 0) D2M8K2.u699 from rfl, allE_node, arows668, irow700, arows699]
  all_goals rfl

theorem atot700 : totK PD2M8K2 D2M8K2.u700 = [3653572101923, 16162663473797, 23525067804821, 12298913083447, 1780675666063, 42879745227, 0, 0] := by
  rw [show D2M8K2.u700 = KTree.node D2M8K2.u668 (nat_lit 1637146) (nat_lit 3709670711) (nat_lit 0) D2M8K2.u699 from rfl, totK_node, atot668, atot699]
  decide +kernel

theorem arows763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u763 = true := by
  rw [show D2M8K2.u763 = KTree.node D2M8K2.u731 (nat_lit 1712672) (nat_lit 3442412345) (nat_lit 0) D2M8K2.u762 from rfl, allE_node, arows731, irow763, arows762]
  all_goals rfl

theorem atot763 : totK PD2M8K2 D2M8K2.u763 = [2429303064203, 13934175250077, 24977748080315, 14265800645991, 1869807606119, 41521527129, 0, 0] := by
  rw [show D2M8K2.u763 = KTree.node D2M8K2.u731 (nat_lit 1712672) (nat_lit 3442412345) (nat_lit 0) D2M8K2.u762 from rfl, totK_node, atot731, atot762]
  decide +kernel

theorem arows828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u828 = true := by
  rw [show D2M8K2.u828 = KTree.node D2M8K2.u796 (nat_lit 1798312) (nat_lit 3801706377) (nat_lit 0) D2M8K2.u827 from rfl, allE_node, arows796, irow828, arows827]
  all_goals rfl

theorem atot828 : totK PD2M8K2 D2M8K2.u828 = [0, 4595412649113, 19650857029413, 24495471270228, 7949522247644, 493992259854, 2528013943, 0] := by
  rw [show D2M8K2.u828 = KTree.node D2M8K2.u796 (nat_lit 1798312) (nat_lit 3801706377) (nat_lit 0) D2M8K2.u827 from rfl, totK_node, atot796, atot827]
  decide +kernel

theorem arows891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u891 = true := by
  rw [show D2M8K2.u891 = KTree.node D2M8K2.u859 (nat_lit 1931695) (nat_lit 2376504823) (nat_lit 0) D2M8K2.u890 from rfl, allE_node, arows859, irow891, arows890]
  all_goals rfl

theorem atot891 : totK PD2M8K2 D2M8K2.u891 = [437191058986, 5238516640705, 18165793384406, 23113758089168, 9121820551201, 953021518692, 23788894471, 0] := by
  rw [show D2M8K2.u891 = KTree.node D2M8K2.u859 (nat_lit 1931695) (nat_lit 2376504823) (nat_lit 0) D2M8K2.u890 from rfl, totK_node, atot859, atot890]
  decide +kernel

theorem arows955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u955 = true := by
  rw [show D2M8K2.u955 = KTree.node D2M8K2.u923 (nat_lit 2037984) (nat_lit 3114872755) (nat_lit 0) D2M8K2.u954 from rfl, allE_node, arows923, irow955, arows954]
  all_goals rfl

theorem atot955 : totK PD2M8K2 D2M8K2.u955 = [3659698560063, 16630929161132, 23997382183501, 11587985552075, 1632663134303, 50084907676, 0, 0] := by
  rw [show D2M8K2.u955 = KTree.node D2M8K2.u923 (nat_lit 2037984) (nat_lit 3114872755) (nat_lit 0) D2M8K2.u954 from rfl, totK_node, atot923, atot954]
  decide +kernel

theorem arows1018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1018 = true := by
  rw [show D2M8K2.u1018 = KTree.node D2M8K2.u986 (nat_lit 2113128) (nat_lit 3401736653) (nat_lit 0) D2M8K2.u1017 from rfl, allE_node, arows986, irow1018, arows1017]
  all_goals rfl

theorem atot1018 : totK PD2M8K2 D2M8K2.u1018 = [3560960190194, 16595449245051, 24399775702344, 11461207819991, 1349997573082, 33142375278, 0, 0] := by
  rw [show D2M8K2.u1018 = KTree.node D2M8K2.u986 (nat_lit 2113128) (nat_lit 3401736653) (nat_lit 0) D2M8K2.u1017 from rfl, totK_node, atot986, atot1017]
  decide +kernel

theorem arows1085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1085 = true := by
  rw [show D2M8K2.u1085 = KTree.node D2M8K2.u1053 (nat_lit 2187756) (nat_lit 3199526130) (nat_lit 0) D2M8K2.u1084 from rfl, allE_node, arows1053, irow1085, arows1084]
  all_goals rfl

theorem atot1085 : totK PD2M8K2 D2M8K2.u1085 = [2102405875695, 11903915624820, 23050601939186, 16465963490287, 3402739718971, 181315064912, 1209030869, 0] := by
  rw [show D2M8K2.u1085 = KTree.node D2M8K2.u1053 (nat_lit 2187756) (nat_lit 3199526130) (nat_lit 0) D2M8K2.u1084 from rfl, totK_node, atot1053, atot1084]
  decide +kernel

theorem arows1148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1148 = true := by
  rw [show D2M8K2.u1148 = KTree.node D2M8K2.u1116 (nat_lit 2336802) (nat_lit 3255006332) (nat_lit 0) D2M8K2.u1147 from rfl, allE_node, arows1116, irow1148, arows1147]
  all_goals rfl

theorem atot1148 : totK PD2M8K2 D2M8K2.u1148 = [0, 6436232221439, 23321329759227, 22676661585499, 5031492793648, 188323891243, 0, 0] := by
  rw [show D2M8K2.u1148 = KTree.node D2M8K2.u1116 (nat_lit 2336802) (nat_lit 3255006332) (nat_lit 0) D2M8K2.u1147 from rfl, totK_node, atot1116, atot1147]
  decide +kernel

theorem arows1212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1212 = true := by
  rw [show D2M8K2.u1212 = KTree.node D2M8K2.u1180 (nat_lit 2496484) (nat_lit 3825369563) (nat_lit 0) D2M8K2.u1211 from rfl, allE_node, arows1180, irow1212, arows1211]
  all_goals rfl

theorem atot1212 : totK PD2M8K2 D2M8K2.u1212 = [2618826317765, 12391080252472, 21078128208236, 15849709691660, 4806099144675, 445355703509, 6115358396, 0] := by
  rw [show D2M8K2.u1212 = KTree.node D2M8K2.u1180 (nat_lit 2496484) (nat_lit 3825369563) (nat_lit 0) D2M8K2.u1211 from rfl, totK_node, atot1180, atot1211]
  decide +kernel

theorem arows1275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1275 = true := by
  rw [show D2M8K2.u1275 = KTree.node D2M8K2.u1243 (nat_lit 2575222) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u1274 from rfl, allE_node, arows1243, irow1275, arows1274]
  all_goals rfl

theorem atot1275 : totK PD2M8K2 D2M8K2.u1275 = [3314367209178, 15321141397519, 23574163927433, 13131200404065, 2194914065622, 75400044681, 0, 0] := by
  rw [show D2M8K2.u1275 = KTree.node D2M8K2.u1243 (nat_lit 2575222) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u1274 from rfl, totK_node, atot1243, atot1274]
  decide +kernel

theorem arows1340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1340 = true := by
  rw [show D2M8K2.u1340 = KTree.node D2M8K2.u1308 (nat_lit 2651089) (nat_lit 1024509920) (nat_lit 0) D2M8K2.u1339 from rfl, allE_node, arows1308, irow1340, arows1339]
  all_goals rfl

theorem atot1340 : totK PD2M8K2 D2M8K2.u1340 = [3856492171129, 17259406848773, 24254680383295, 11024815456932, 1172277121899, 21451877524, 0, 0] := by
  rw [show D2M8K2.u1340 = KTree.node D2M8K2.u1308 (nat_lit 2651089) (nat_lit 1024509920) (nat_lit 0) D2M8K2.u1339 from rfl, totK_node, atot1308, atot1339]
  decide +kernel

theorem arows1403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1403 = true := by
  rw [show D2M8K2.u1403 = KTree.node D2M8K2.u1371 (nat_lit 2765068) (nat_lit 3805558280) (nat_lit 0) D2M8K2.u1402 from rfl, allE_node, arows1371, irow1403, arows1402]
  all_goals rfl

theorem atot1403 : totK PD2M8K2 D2M8K2.u1403 = [0, 5358186289991, 21038007378373, 23703452673629, 6893897559716, 362812225517, 1369150432, 0] := by
  rw [show D2M8K2.u1403 = KTree.node D2M8K2.u1371 (nat_lit 2765068) (nat_lit 3805558280) (nat_lit 0) D2M8K2.u1402 from rfl, totK_node, atot1371, atot1402]
  decide +kernel

theorem arows1467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1467 = true := by
  rw [show D2M8K2.u1467 = KTree.node D2M8K2.u1435 (nat_lit 2867719) (nat_lit 2381626949) (nat_lit 0) D2M8K2.u1466 from rfl, allE_node, arows1435, irow1467, arows1466]
  all_goals rfl

theorem atot1467 : totK PD2M8K2 D2M8K2.u1467 = [0, 4002406384981, 18045261936058, 24571728994372, 9719663572873, 844132318506, 12665407822, 0] := by
  rw [show D2M8K2.u1467 = KTree.node D2M8K2.u1435 (nat_lit 2867719) (nat_lit 2381626949) (nat_lit 0) D2M8K2.u1466 from rfl, totK_node, atot1435, atot1466]
  decide +kernel

theorem arows1530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1530 = true := by
  rw [show D2M8K2.u1530 = KTree.node D2M8K2.u1498 (nat_lit 2986249) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u1529 from rfl, allE_node, arows1498, irow1530, arows1529]
  all_goals rfl

theorem atot1530 : totK PD2M8K2 D2M8K2.u1530 = [0, 3410718635836, 16424391524189, 24639115542662, 11218330898672, 1305990989971, 34034107435, 0] := by
  rw [show D2M8K2.u1530 = KTree.node D2M8K2.u1498 (nat_lit 2986249) (nat_lit 1508690721) (nat_lit 0) D2M8K2.u1529 from rfl, totK_node, atot1498, atot1529]
  decide +kernel

theorem arows1596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1596 = true := by
  rw [show D2M8K2.u1596 = KTree.node D2M8K2.u1564 (nat_lit 3104901) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u1595 from rfl, allE_node, arows1564, irow1596, arows1595]
  all_goals rfl

theorem atot1596 : totK PD2M8K2 D2M8K2.u1596 = [0, 4027454880231, 17596406429221, 24166814698165, 10293891588843, 1063933481299, 28219063037, 0] := by
  rw [show D2M8K2.u1596 = KTree.node D2M8K2.u1564 (nat_lit 3104901) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u1595 from rfl, totK_node, atot1564, atot1595]
  decide +kernel

theorem arows1659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1659 = true := by
  rw [show D2M8K2.u1659 = KTree.node D2M8K2.u1627 (nat_lit 3180143) (nat_lit 1820705409) (nat_lit 128) D2M8K2.u1658 from rfl, allE_node, arows1627, irow1659, arows1658]
  all_goals rfl

theorem atot1659 : totK PD2M8K2 D2M8K2.u1659 = [0, 4027617773463, 17764878016236, 24356509660527, 10025994517832, 901473531724, 15618450242, 0] := by
  rw [show D2M8K2.u1659 = KTree.node D2M8K2.u1627 (nat_lit 3180143) (nat_lit 1820705409) (nat_lit 128) D2M8K2.u1658 from rfl, totK_node, atot1627, atot1658]
  decide +kernel

theorem arows1723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1723 = true := by
  rw [show D2M8K2.u1723 = KTree.node D2M8K2.u1691 (nat_lit 3255347) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u1722 from rfl, allE_node, arows1691, irow1723, arows1722]
  all_goals rfl

theorem atot1723 : totK PD2M8K2 D2M8K2.u1723 = [0, 0, 5867233419778, 22024341599880, 22439978096099, 5791903280232, 373134725533, 1369150432] := by
  rw [show D2M8K2.u1723 = KTree.node D2M8K2.u1691 (nat_lit 3255347) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u1722 from rfl, totK_node, atot1691, atot1722]
  decide +kernel

theorem arows1786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1786 = true := by
  rw [show D2M8K2.u1786 = KTree.node D2M8K2.u1754 (nat_lit 3442786) (nat_lit 3878378429) (nat_lit 0) D2M8K2.u1785 from rfl, allE_node, arows1754, irow1786, arows1785]
  all_goals rfl

theorem atot1786 : totK PD2M8K2 D2M8K2.u1786 = [0, 1636922335308, 11323905481462, 24222163584183, 17069650993000, 2799704022929, 97918740009, 0] := by
  rw [show D2M8K2.u1786 = KTree.node D2M8K2.u1754 (nat_lit 3442786) (nat_lit 3878378429) (nat_lit 0) D2M8K2.u1785 from rfl, totK_node, atot1754, atot1785]
  decide +kernel

theorem arows1851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1851 = true := by
  rw [show D2M8K2.u1851 = KTree.node D2M8K2.u1819 (nat_lit 4042174) (nat_lit 3857547598) (nat_lit 0) D2M8K2.u1850 from rfl, allE_node, arows1819, irow1851, arows1850]
  all_goals rfl

theorem atot1851 : totK PD2M8K2 D2M8K2.u1851 = [0, 4162312086131, 18129532450126, 24508783573955, 9930998064353, 847026725745, 7944161137, 0] := by
  rw [show D2M8K2.u1851 = KTree.node D2M8K2.u1819 (nat_lit 4042174) (nat_lit 3857547598) (nat_lit 0) D2M8K2.u1850 from rfl, totK_node, atot1819, atot1850]
  decide +kernel

theorem arows1914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1914 = true := by
  rw [show D2M8K2.u1914 = KTree.node D2M8K2.u1882 (nat_lit 4159539) (nat_lit 1097298499) (nat_lit 0) D2M8K2.u1913 from rfl, allE_node, arows1882, irow1914, arows1913]
  all_goals rfl

theorem atot1914 : totK PD2M8K2 D2M8K2.u1914 = [0, 3508178713575, 16544014748996, 24649918245922, 11230924318287, 1184567339954, 24912417204, 0] := by
  rw [show D2M8K2.u1914 = KTree.node D2M8K2.u1882 (nat_lit 4159539) (nat_lit 1097298499) (nat_lit 0) D2M8K2.u1913 from rfl, totK_node, atot1882, atot1913]
  decide +kernel

theorem arows1978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1978 = true := by
  rw [show D2M8K2.u1978 = KTree.node D2M8K2.u1946 (nat_lit 4492058) (nat_lit 3941683781) (nat_lit 0) D2M8K2.u1977 from rfl, allE_node, arows1946, irow1978, arows1977]
  all_goals rfl

theorem atot1978 : totK PD2M8K2 D2M8K2.u1978 = [0, 3660042995213, 17046060446050, 24688388052918, 10908477235794, 1098601276780, 21345770449, 0] := by
  rw [show D2M8K2.u1978 = KTree.node D2M8K2.u1946 (nat_lit 4492058) (nat_lit 3941683781) (nat_lit 0) D2M8K2.u1977 from rfl, totK_node, atot1946, atot1977]
  decide +kernel

theorem arows2041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2041 = true := by
  rw [show D2M8K2.u2041 = KTree.node D2M8K2.u2009 (nat_lit 4618053) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u2040 from rfl, allE_node, arows2009, irow2041, arows2040]
  all_goals rfl

theorem atot2041 : totK PD2M8K2 D2M8K2.u2041 = [0, 3638388553773, 16751393693172, 24364621852528, 11475556953919, 1267629326318, 25699949671, 0] := by
  rw [show D2M8K2.u2041 = KTree.node D2M8K2.u2009 (nat_lit 4618053) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u2040 from rfl, totK_node, atot2009, atot2040]
  decide +kernel

theorem arows2109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2109 = true := by
  rw [show D2M8K2.u2109 = KTree.node D2M8K2.u2077 (nat_lit 4693611) (nat_lit 3688397007) (nat_lit 0) D2M8K2.u2108 from rfl, allE_node, arows2077, irow2109, arows2108]
  all_goals rfl

theorem atot2109 : totK PD2M8K2 D2M8K2.u2109 = [0, 3677352512586, 16934487584290, 24532638597643, 11099629959089, 1191971626577, 26209352523, 0] := by
  rw [show D2M8K2.u2109 = KTree.node D2M8K2.u2077 (nat_lit 4693611) (nat_lit 3688397007) (nat_lit 0) D2M8K2.u2108 from rfl, totK_node, atot2077, atot2108]
  decide +kernel

theorem arows2172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2172 = true := by
  rw [show D2M8K2.u2172 = KTree.node D2M8K2.u2140 (nat_lit 5025553) (nat_lit 1100305286) (nat_lit 0) D2M8K2.u2171 from rfl, allE_node, arows2140, irow2172, arows2171]
  all_goals rfl

theorem atot2172 : totK PD2M8K2 D2M8K2.u2172 = [0, 4181127306637, 18510383922013, 24692649066564, 9337075571295, 685029234416, 2784292502, 0] := by
  rw [show D2M8K2.u2172 = KTree.node D2M8K2.u2140 (nat_lit 5025553) (nat_lit 1100305286) (nat_lit 0) D2M8K2.u2171 from rfl, totK_node, atot2140, atot2171]
  decide +kernel

theorem arows2236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2236 = true := by
  rw [show D2M8K2.u2236 = KTree.node D2M8K2.u2204 (nat_lit 5111507) (nat_lit 2858976552) (nat_lit 0) D2M8K2.u2235 from rfl, allE_node, arows2204, irow2236, arows2235]
  all_goals rfl

theorem atot2236 : totK PD2M8K2 D2M8K2.u2236 = [0, 3506692764170, 16340366728079, 24373768876211, 11526217801989, 1362063816053, 37862993724, 0] := by
  rw [show D2M8K2.u2236 = KTree.node D2M8K2.u2204 (nat_lit 5111507) (nat_lit 2858976552) (nat_lit 0) D2M8K2.u2235 from rfl, totK_node, atot2204, atot2235]
  decide +kernel

theorem arows2299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2299 = true := by
  rw [show D2M8K2.u2299 = KTree.node D2M8K2.u2267 (nat_lit 5476668) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u2298 from rfl, allE_node, arows2267, irow2299, arows2298]
  all_goals rfl

theorem atot2299 : totK PD2M8K2 D2M8K2.u2299 = [0, 3794852640118, 17691462129683, 24923219372427, 9955200028623, 825336631804, 7484508828, 0] := by
  rw [show D2M8K2.u2299 = KTree.node D2M8K2.u2267 (nat_lit 5476668) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u2298 from rfl, totK_node, atot2267, atot2298]
  decide +kernel

theorem arows2364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2364 = true := by
  rw [show D2M8K2.u2364 = KTree.node D2M8K2.u2332 (nat_lit 5561609) (nat_lit 1657900937) (nat_lit 0) D2M8K2.u2363 from rfl, allE_node, arows2332, irow2364, arows2363]
  all_goals rfl

theorem atot2364 : totK PD2M8K2 D2M8K2.u2364 = [0, 3635637948877, 16849192112709, 24634857716038, 11383662782272, 1207434239772, 19009380153, 0] := by
  rw [show D2M8K2.u2364 = KTree.node D2M8K2.u2332 (nat_lit 5561609) (nat_lit 1657900937) (nat_lit 0) D2M8K2.u2363 from rfl, totK_node, atot2332, atot2363]
  decide +kernel

theorem arows2427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2427 = true := by
  rw [show D2M8K2.u2427 = KTree.node D2M8K2.u2395 (nat_lit 5683400) (nat_lit 3553519028) (nat_lit 0) D2M8K2.u2426 from rfl, allE_node, arows2395, irow2427, arows2426]
  all_goals rfl

theorem atot2427 : totK PD2M8K2 D2M8K2.u2427 = [0, 3691676416270, 16790750276130, 24494884206617, 11416532769568, 1139547191238, 17787227885, 0] := by
  rw [show D2M8K2.u2427 = KTree.node D2M8K2.u2395 (nat_lit 5683400) (nat_lit 3553519028) (nat_lit 0) D2M8K2.u2426 from rfl, totK_node, atot2395, atot2426]
  decide +kernel

theorem arows2491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2491 = true := by
  rw [show D2M8K2.u2491 = KTree.node D2M8K2.u2459 (nat_lit 6539473) (nat_lit 1435094248) (nat_lit 0) D2M8K2.u2490 from rfl, allE_node, arows2459, irow2491, arows2490]
  all_goals rfl

theorem atot2491 : totK PD2M8K2 D2M8K2.u2491 = [4095529399505, 16330754357304, 21687874647793, 12091675164978, 3322041824147, 479005349626, 21751168066, 0] := by
  rw [show D2M8K2.u2491 = KTree.node D2M8K2.u2459 (nat_lit 6539473) (nat_lit 1435094248) (nat_lit 0) D2M8K2.u2490 from rfl, totK_node, atot2459, atot2490]
  decide +kernel

theorem arows2554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2554 = true := by
  rw [show D2M8K2.u2554 = KTree.node D2M8K2.u2522 (nat_lit 6609661) (nat_lit 1041469472) (nat_lit 0) D2M8K2.u2553 from rfl, allE_node, arows2522, irow2554, arows2553]
  all_goals rfl

theorem atot2554 : totK PD2M8K2 D2M8K2.u2554 = [3249006127965, 15826430598854, 24494146446876, 12379785484185, 1533168692104, 37862993724, 0, 0] := by
  rw [show D2M8K2.u2554 = KTree.node D2M8K2.u2522 (nat_lit 6609661) (nat_lit 1041469472) (nat_lit 0) D2M8K2.u2553 from rfl, totK_node, atot2522, atot2553]
  decide +kernel

theorem arows2620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2620 = true := by
  rw [show D2M8K2.u2620 = KTree.node D2M8K2.u2588 (nat_lit 6685386) (nat_lit 3600559107) (nat_lit 0) D2M8K2.u2619 from rfl, allE_node, arows2588, irow2620, arows2619]
  all_goals rfl

theorem atot2620 : totK PD2M8K2 D2M8K2.u2620 = [2878068400688, 14879017033324, 24533402302779, 13350909091711, 1970518159183, 68382949722, 0, 0] := by
  rw [show D2M8K2.u2620 = KTree.node D2M8K2.u2588 (nat_lit 6685386) (nat_lit 3600559107) (nat_lit 0) D2M8K2.u2619 from rfl, totK_node, atot2588, atot2619]
  decide +kernel

theorem arows2683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2683 = true := by
  rw [show D2M8K2.u2683 = KTree.node D2M8K2.u2651 (nat_lit 6795906) (nat_lit 2904283101) (nat_lit 0) D2M8K2.u2682 from rfl, allE_node, arows2651, irow2683, arows2682]
  all_goals rfl

theorem atot2683 : totK PD2M8K2 D2M8K2.u2683 = [0, 3712430816758, 16655579956098, 23755387772174, 11711473793235, 1704308504147, 57647371591, 0] := by
  rw [show D2M8K2.u2683 = KTree.node D2M8K2.u2651 (nat_lit 6795906) (nat_lit 2904283101) (nat_lit 0) D2M8K2.u2682 from rfl, totK_node, atot2651, atot2682]
  decide +kernel

theorem arows2747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2747 = true := by
  rw [show D2M8K2.u2747 = KTree.node D2M8K2.u2715 (nat_lit 6875302) (nat_lit 1098454926) (nat_lit 0) D2M8K2.u2746 from rfl, allE_node, arows2715, irow2747, arows2746]
  all_goals rfl

theorem atot2747 : totK PD2M8K2 D2M8K2.u2747 = [0, 4036894483938, 17997204246681, 24357500132648, 10020936948448, 946468888886, 13171198502, 0] := by
  rw [show D2M8K2.u2747 = KTree.node D2M8K2.u2715 (nat_lit 6875302) (nat_lit 1098454926) (nat_lit 0) D2M8K2.u2746 from rfl, totK_node, atot2715, atot2746]
  decide +kernel

theorem arows2810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2810 = true := by
  rw [show D2M8K2.u2810 = KTree.node D2M8K2.u2778 (nat_lit 6953934) (nat_lit 3687018877) (nat_lit 0) D2M8K2.u2809 from rfl, allE_node, arows2778, irow2810, arows2809]
  all_goals rfl

theorem atot2810 : totK PD2M8K2 D2M8K2.u2810 = [1647549989118, 8714747279241, 18414866121788, 19259011798846, 8513635347403, 914847074964, 13619666203, 0] := by
  rw [show D2M8K2.u2810 = KTree.node D2M8K2.u2778 (nat_lit 6953934) (nat_lit 3687018877) (nat_lit 0) D2M8K2.u2809 from rfl, totK_node, atot2778, atot2809]
  decide +kernel

theorem arows2875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2875 = true := by
  rw [show D2M8K2.u2875 = KTree.node D2M8K2.u2843 (nat_lit 7038029) (nat_lit 2188079480) (nat_lit 0) D2M8K2.u2874 from rfl, allE_node, arows2843, irow2875, arows2874]
  all_goals rfl

theorem atot2875 : totK PD2M8K2 D2M8K2.u2875 = [4155261567927, 17315147959761, 23316287066216, 11408247702663, 1778468609248, 58018127943, 0, 0] := by
  rw [show D2M8K2.u2875 = KTree.node D2M8K2.u2843 (nat_lit 7038029) (nat_lit 2188079480) (nat_lit 0) D2M8K2.u2874 from rfl, totK_node, atot2843, atot2874]
  decide +kernel

theorem arows2938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2938 = true := by
  rw [show D2M8K2.u2938 = KTree.node D2M8K2.u2906 (nat_lit 7145651) (nat_lit 2610737141) (nat_lit 0) D2M8K2.u2937 from rfl, allE_node, arows2906, irow2938, arows2937]
  all_goals rfl

theorem atot2938 : totK PD2M8K2 D2M8K2.u2938 = [3449003366098, 16394502527934, 24645325681780, 11617443091524, 1271612587188, 24912417204, 0, 0] := by
  rw [show D2M8K2.u2938 = KTree.node D2M8K2.u2906 (nat_lit 7145651) (nat_lit 2610737141) (nat_lit 0) D2M8K2.u2937 from rfl, totK_node, atot2906, atot2937]
  decide +kernel

theorem arows3002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3002 = true := by
  rw [show D2M8K2.u3002 = KTree.node D2M8K2.u2970 (nat_lit 7230410) (nat_lit 4242385292) (nat_lit 0) D2M8K2.u3001 from rfl, allE_node, arows2970, irow3002, arows3001]
  all_goals rfl

theorem atot3002 : totK PD2M8K2 D2M8K2.u3002 = [529390851355, 7404741174581, 22240666970857, 21520179807135, 5504029243288, 293356877127, 1275377855, 0] := by
  rw [show D2M8K2.u3002 = KTree.node D2M8K2.u2970 (nat_lit 7230410) (nat_lit 4242385292) (nat_lit 0) D2M8K2.u3001 from rfl, totK_node, atot2970, atot3001]
  decide +kernel

theorem arows3065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3065 = true := by
  rw [show D2M8K2.u3065 = KTree.node D2M8K2.u3033 (nat_lit 7327884) (nat_lit 3532810312) (nat_lit 0) D2M8K2.u3064 from rfl, allE_node, arows3033, irow3065, arows3064]
  all_goals rfl

theorem atot3065 : totK PD2M8K2 D2M8K2.u3065 = [0, 4502183176728, 18954474023852, 23895938302097, 8855218207448, 873856195433, 19900513739, 0] := by
  rw [show D2M8K2.u3065 = KTree.node D2M8K2.u3033 (nat_lit 7327884) (nat_lit 3532810312) (nat_lit 0) D2M8K2.u3064 from rfl, totK_node, atot3033, atot3064]
  decide +kernel

theorem arows3132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3132 = true := by
  rw [show D2M8K2.u3132 = KTree.node D2M8K2.u3100 (nat_lit 7476515) (nat_lit 1746665908) (nat_lit 0) D2M8K2.u3131 from rfl, allE_node, arows3100, irow3132, arows3131]
  all_goals rfl

theorem atot3132 : totK PD2M8K2 D2M8K2.u3132 = [2866755110009, 13511392758712, 22192334335136, 14930774839375, 3754842204107, 277868584124, 4779662215, 0] := by
  rw [show D2M8K2.u3132 = KTree.node D2M8K2.u3100 (nat_lit 7476515) (nat_lit 1746665908) (nat_lit 0) D2M8K2.u3131 from rfl, totK_node, atot3100, atot3131]
  decide +kernel

theorem arows3195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3195 = true := by
  rw [show D2M8K2.u3195 = KTree.node D2M8K2.u3163 (nat_lit 7591816) (nat_lit 3012765568) (nat_lit 0) D2M8K2.u3194 from rfl, allE_node, arows3163, irow3195, arows3194]
  all_goals rfl

theorem atot3195 : totK PD2M8K2 D2M8K2.u3195 = [2936955391941, 14558002691552, 23772672378066, 13983520322134, 2357785158771, 77084062859, 0, 0] := by
  rw [show D2M8K2.u3195 = KTree.node D2M8K2.u3163 (nat_lit 7591816) (nat_lit 3012765568) (nat_lit 0) D2M8K2.u3194 from rfl, totK_node, atot3163, atot3194]
  decide +kernel

theorem arows3259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3259 = true := by
  rw [show D2M8K2.u3259 = KTree.node D2M8K2.u3227 (nat_lit 7665902) (nat_lit 3625837239) (nat_lit 0) D2M8K2.u3258 from rfl, allE_node, arows3227, irow3259, arows3258]
  all_goals rfl

theorem atot3259 : totK PD2M8K2 D2M8K2.u3259 = [3978808262243, 17683424184913, 24465291248639, 10564639644568, 1010640513203, 12305484365, 0, 0] := by
  rw [show D2M8K2.u3259 = KTree.node D2M8K2.u3227 (nat_lit 7665902) (nat_lit 3625837239) (nat_lit 0) D2M8K2.u3258 from rfl, totK_node, atot3227, atot3258]
  decide +kernel

theorem arows3322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3322 = true := by
  rw [show D2M8K2.u3322 = KTree.node D2M8K2.u3290 (nat_lit 7752140) (nat_lit 3102400415) (nat_lit 0) D2M8K2.u3321 from rfl, allE_node, arows3290, irow3322, arows3321]
  all_goals rfl

theorem atot3322 : totK PD2M8K2 D2M8K2.u3322 = [0, 5747678667061, 21665821196722, 23255291614989, 6463536720527, 345277620929, 1310517177, 0] := by
  rw [show D2M8K2.u3322 = KTree.node D2M8K2.u3290 (nat_lit 7752140) (nat_lit 3102400415) (nat_lit 0) D2M8K2.u3321 from rfl, totK_node, atot3290, atot3321]
  decide +kernel

theorem arows3387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3387 = true := by
  rw [show D2M8K2.u3387 = KTree.node D2M8K2.u3355 (nat_lit 7885541) (nat_lit 2338578389) (nat_lit 0) D2M8K2.u3386 from rfl, allE_node, arows3355, irow3387, arows3386]
  all_goals rfl

theorem atot3387 : totK PD2M8K2 D2M8K2.u3387 = [0, 3618278974270, 17293043809177, 24615067879342, 10246655271939, 1083144047056, 25006391237, 0] := by
  rw [show D2M8K2.u3387 = KTree.node D2M8K2.u3355 (nat_lit 7885541) (nat_lit 2338578389) (nat_lit 0) D2M8K2.u3386 from rfl, totK_node, atot3355, atot3386]
  decide +kernel

theorem arows3450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3450 = true := by
  rw [show D2M8K2.u3450 = KTree.node D2M8K2.u3418 (nat_lit 7990368) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u3449 from rfl, allE_node, arows3418, irow3450, arows3449]
  all_goals rfl

theorem atot3450 : totK PD2M8K2 D2M8K2.u3450 = [3690298243741, 16464562544373, 23432472165527, 11914762971832, 2119134320739, 86707828971, 0, 0] := by
  rw [show D2M8K2.u3450 = KTree.node D2M8K2.u3418 (nat_lit 7990368) (nat_lit 3592768262) (nat_lit 0) D2M8K2.u3449 from rfl, totK_node, atot3418, atot3449]
  decide +kernel

theorem arows3514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3514 = true := by
  rw [show D2M8K2.u3514 = KTree.node D2M8K2.u3482 (nat_lit 8063544) (nat_lit 3543146485) (nat_lit 0) D2M8K2.u3513 from rfl, allE_node, arows3482, irow3514, arows3513]
  all_goals rfl

theorem atot3514 : totK PD2M8K2 D2M8K2.u3514 = [3624754123544, 15920904048143, 23553640419968, 12741880385833, 1811637123741, 39893312897, 0, 0] := by
  rw [show D2M8K2.u3514 = KTree.node D2M8K2.u3482 (nat_lit 8063544) (nat_lit 3543146485) (nat_lit 0) D2M8K2.u3513 from rfl, totK_node, atot3482, atot3513]
  decide +kernel

theorem arows3577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3577 = true := by
  rw [show D2M8K2.u3577 = KTree.node D2M8K2.u3545 (nat_lit 8137770) (nat_lit 3056830631) (nat_lit 0) D2M8K2.u3576 from rfl, allE_node, arows3545, irow3577, arows3576]
  all_goals rfl

theorem atot3577 : totK PD2M8K2 D2M8K2.u3577 = [2451635820495, 14277256196253, 25093335507373, 13705596161997, 1724860255441, 39533893540, 0, 0] := by
  rw [show D2M8K2.u3577 = KTree.node D2M8K2.u3545 (nat_lit 8137770) (nat_lit 3056830631) (nat_lit 0) D2M8K2.u3576 from rfl, totK_node, atot3545, atot3576]
  decide +kernel

theorem arows3643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3643 = true := by
  rw [show D2M8K2.u3643 = KTree.node D2M8K2.u3611 (nat_lit 8269475) (nat_lit 2660779450) (nat_lit 0) D2M8K2.u3642 from rfl, allE_node, arows3611, irow3643, arows3642]
  all_goals rfl

theorem atot3643 : totK PD2M8K2 D2M8K2.u3643 = [0, 5740027729266, 21959127536863, 23551657651070, 6126277248172, 308812628870, 1209030869, 0] := by
  rw [show D2M8K2.u3643 = KTree.node D2M8K2.u3611 (nat_lit 8269475) (nat_lit 2660779450) (nat_lit 0) D2M8K2.u3642 from rfl, totK_node, atot3611, atot3642]
  decide +kernel

theorem arows3706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3706 = true := by
  rw [show D2M8K2.u3706 = KTree.node D2M8K2.u3674 (nat_lit 8399665) (nat_lit 1538198295) (nat_lit 0) D2M8K2.u3705 from rfl, allE_node, arows3674, irow3706, arows3705]
  all_goals rfl

theorem atot3706 : totK PD2M8K2 D2M8K2.u3706 = [1651197789013, 9427462905593, 20539111678752, 19123701649897, 5860710246635, 488085669039, 6115358396, 0] := by
  rw [show D2M8K2.u3706 = KTree.node D2M8K2.u3674 (nat_lit 8399665) (nat_lit 1538198295) (nat_lit 0) D2M8K2.u3705 from rfl, totK_node, atot3674, atot3705]
  decide +kernel

theorem arows3770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3770 = true := by
  rw [show D2M8K2.u3770 = KTree.node D2M8K2.u3738 (nat_lit 8529961) (nat_lit 1179661664) (nat_lit 0) D2M8K2.u3769 from rfl, allE_node, arows3738, irow3770, arows3769]
  all_goals rfl

theorem atot3770 : totK PD2M8K2 D2M8K2.u3770 = [4041817071895, 17158845444389, 23514970615481, 11569104161068, 1791270066566, 58018127943, 0, 0] := by
  rw [show D2M8K2.u3770 = KTree.node D2M8K2.u3738 (nat_lit 8529961) (nat_lit 1179661664) (nat_lit 0) D2M8K2.u3769 from rfl, totK_node, atot3738, atot3769]
  decide +kernel

theorem arows3833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3833 = true := by
  rw [show D2M8K2.u3833 = KTree.node D2M8K2.u3801 (nat_lit 8601494) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u3832 from rfl, allE_node, arows3801, irow3833, arows3832]
  all_goals rfl

theorem atot3833 : totK PD2M8K2 D2M8K2.u3833 = [3237240397021, 15787396953853, 24535795958113, 12409947030493, 1534321096314, 37862993724, 0, 0] := by
  rw [show D2M8K2.u3833 = KTree.node D2M8K2.u3801 (nat_lit 8601494) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u3832 from rfl, totK_node, atot3801, atot3832]
  decide +kernel

theorem arows3898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3898 = true := by
  rw [show D2M8K2.u3898 = KTree.node D2M8K2.u3866 (nat_lit 8717189) (nat_lit 2311055063) (nat_lit 0) D2M8K2.u3897 from rfl, allE_node, arows3866, irow3898, arows3897]
  all_goals rfl

theorem atot3898 : totK PD2M8K2 D2M8K2.u3898 = [867070346516, 8172721416871, 21917906181404, 20599413999604, 5563922954088, 302152320751, 1369150432, 0] := by
  rw [show D2M8K2.u3898 = KTree.node D2M8K2.u3866 (nat_lit 8717189) (nat_lit 2311055063) (nat_lit 0) D2M8K2.u3897 from rfl, totK_node, atot3866, atot3897]
  decide +kernel

theorem arows3961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3961 = true := by
  rw [show D2M8K2.u3961 = KTree.node D2M8K2.u3929 (nat_lit 8816592) (nat_lit 2780830143) (nat_lit 0) D2M8K2.u3960 from rfl, allE_node, arows3929, irow3961, arows3960]
  all_goals rfl

theorem atot3961 : totK PD2M8K2 D2M8K2.u3961 = [0, 4755421976844, 19608921761108, 24060377974848, 8383507792202, 615114848297, 7501842248, 0] := by
  rw [show D2M8K2.u3961 = KTree.node D2M8K2.u3929 (nat_lit 8816592) (nat_lit 2780830143) (nat_lit 0) D2M8K2.u3960 from rfl, totK_node, atot3929, atot3960]
  decide +kernel

theorem arows4025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4025 = true := by
  rw [show D2M8K2.u4025 = KTree.node D2M8K2.u3993 (nat_lit 8938746) (nat_lit 3893305560) (nat_lit 0) D2M8K2.u4024 from rfl, allE_node, arows3993, irow4025, arows4024]
  all_goals rfl

theorem atot4025 : totK PD2M8K2 D2M8K2.u4025 = [0, 3827434933032, 17189618632458, 24069452983983, 10896300847643, 1345941502139, 37828522577, 0] := by
  rw [show D2M8K2.u4025 = KTree.node D2M8K2.u3993 (nat_lit 8938746) (nat_lit 3893305560) (nat_lit 0) D2M8K2.u4024 from rfl, totK_node, atot3993, atot4024]
  decide +kernel

theorem arows4088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4088 = true := by
  rw [show D2M8K2.u4088 = KTree.node D2M8K2.u4056 (nat_lit 9544993) (nat_lit 1373303054) (nat_lit 0) D2M8K2.u4087 from rfl, allE_node, arows4056, irow4088, arows4087]
  all_goals rfl

theorem atot4088 : totK PD2M8K2 D2M8K2.u4088 = [0, 3010395824285, 14641507952410, 23885301519926, 14009126562427, 2255515033885, 69430655237, 0] := by
  rw [show D2M8K2.u4088 = KTree.node D2M8K2.u4056 (nat_lit 9544993) (nat_lit 1373303054) (nat_lit 0) D2M8K2.u4087 from rfl, totK_node, atot4056, atot4087]
  decide +kernel

theorem arows4157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4157 = true := by
  rw [show D2M8K2.u4157 = KTree.node D2M8K2.u4125 (nat_lit 9622446) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u4156 from rfl, allE_node, arows4125, irow4157, arows4156]
  all_goals rfl

theorem atot4157 : totK PD2M8K2 D2M8K2.u4157 = [0, 3501676935231, 16722215610159, 24878506564699, 11437195407347, 1134588890798, 14139149514, 0] := by
  rw [show D2M8K2.u4157 = KTree.node D2M8K2.u4125 (nat_lit 9622446) (nat_lit 4071740195) (nat_lit 0) D2M8K2.u4156 from rfl, totK_node, atot4125, atot4156]
  decide +kernel

theorem arows4220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4220 = true := by
  rw [show D2M8K2.u4220 = KTree.node D2M8K2.u4188 (nat_lit 9696843) (nat_lit 2384468759) (nat_lit 0) D2M8K2.u4219 from rfl, allE_node, arows4188, irow4220, arows4219]
  all_goals rfl

theorem atot4220 : totK PD2M8K2 D2M8K2.u4220 = [0, 1995489986565, 11349702151516, 22162745023366, 16966306976593, 4792153632207, 693503154280, 36921873854] := by
  rw [show D2M8K2.u4220 = KTree.node D2M8K2.u4188 (nat_lit 9696843) (nat_lit 2384468759) (nat_lit 0) D2M8K2.u4219 from rfl, totK_node, atot4188, atot4219]
  decide +kernel

theorem arows4284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4284 = true := by
  rw [show D2M8K2.u4284 = KTree.node D2M8K2.u4252 (nat_lit 9806738) (nat_lit 4104333089) (nat_lit 0) D2M8K2.u4283 from rfl, allE_node, arows4252, irow4284, arows4283]
  all_goals rfl

theorem atot4284 : totK PD2M8K2 D2M8K2.u4284 = [0, 0, 4034986554361, 17258780000949, 23653430053585, 11214068274221, 1368991340052, 27272047243] := by
  rw [show D2M8K2.u4284 = KTree.node D2M8K2.u4252 (nat_lit 9806738) (nat_lit 4104333089) (nat_lit 0) D2M8K2.u4283 from rfl, totK_node, atot4252, atot4283]
  decide +kernel

theorem arows4347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4347 = true := by
  rw [show D2M8K2.u4347 = KTree.node D2M8K2.u4315 (nat_lit 9885973) (nat_lit 1215979211) (nat_lit 0) D2M8K2.u4346 from rfl, allE_node, arows4315, irow4347, arows4346]
  all_goals rfl

theorem atot4347 : totK PD2M8K2 D2M8K2.u4347 = [0, 0, 4035136786716, 18381399064790, 24891359368143, 9578123858656, 749539514654, 8054464832] := by
  rw [show D2M8K2.u4347 = KTree.node D2M8K2.u4315 (nat_lit 9885973) (nat_lit 1215979211) (nat_lit 0) D2M8K2.u4346 from rfl, totK_node, atot4315, atot4346]
  decide +kernel

theorem arows4412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4412 = true := by
  rw [show D2M8K2.u4412 = KTree.node D2M8K2.u4380 (nat_lit 9975577) (nat_lit 1516127035) (nat_lit 0) D2M8K2.u4411 from rfl, allE_node, arows4380, irow4412, arows4411]
  all_goals rfl

theorem atot4412 : totK PD2M8K2 D2M8K2.u4412 = [0, 3695682846758, 15234096919634, 20807770639874, 12477380705922, 4912778847632, 601912489888, 12189850367] := by
  rw [show D2M8K2.u4412 = KTree.node D2M8K2.u4380 (nat_lit 9975577) (nat_lit 1516127035) (nat_lit 0) D2M8K2.u4411 from rfl, totK_node, atot4380, atot4411]
  decide +kernel

theorem arows4475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4475 = true := by
  rw [show D2M8K2.u4475 = KTree.node D2M8K2.u4443 (nat_lit 10052673) (nat_lit 1825578435) (nat_lit 0) D2M8K2.u4474 from rfl, allE_node, arows4443, irow4475, arows4474]
  all_goals rfl

theorem atot4475 : totK PD2M8K2 D2M8K2.u4475 = [0, 3327383759999, 15306697409364, 23593847047964, 13288124306980, 2052804195243, 51623628652, 0] := by
  rw [show D2M8K2.u4475 = KTree.node D2M8K2.u4443 (nat_lit 10052673) (nat_lit 1825578435) (nat_lit 0) D2M8K2.u4474 from rfl, totK_node, atot4443, atot4474]
  decide +kernel

theorem arows4539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4539 = true := by
  rw [show D2M8K2.u4539 = KTree.node D2M8K2.u4507 (nat_lit 10169289) (nat_lit 1782739114) (nat_lit 0) D2M8K2.u4538 from rfl, allE_node, arows4507, irow4539, arows4538]
  all_goals rfl

theorem atot4539 : totK PD2M8K2 D2M8K2.u4539 = [0, 2758139167741, 14834293839324, 25042056918046, 13354111576959, 1614296889151, 33133348202, 0] := by
  rw [show D2M8K2.u4539 = KTree.node D2M8K2.u4507 (nat_lit 10169289) (nat_lit 1782739114) (nat_lit 0) D2M8K2.u4538 from rfl, totK_node, atot4507, atot4538]
  decide +kernel

theorem arows4602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4602 = true := by
  rw [show D2M8K2.u4602 = KTree.node D2M8K2.u4570 (nat_lit 10289860) (nat_lit 3972303320) (nat_lit 0) D2M8K2.u4601 from rfl, allE_node, arows4570, irow4602, arows4601]
  all_goals rfl

theorem atot4602 : totK PD2M8K2 D2M8K2.u4602 = [0, 0, 5417050660068, 21101517346216, 23442935759988, 7047592333017, 536629574311, 7048116272] := by
  rw [show D2M8K2.u4602 = KTree.node D2M8K2.u4570 (nat_lit 10289860) (nat_lit 3972303320) (nat_lit 0) D2M8K2.u4601 from rfl, totK_node, atot4570, atot4601]
  decide +kernel

theorem arows4668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4668 = true := by
  rw [show D2M8K2.u4668 = KTree.node D2M8K2.u4636 (nat_lit 10416235) (nat_lit 1595479620) (nat_lit 0) D2M8K2.u4667 from rfl, allE_node, arows4636, irow4668, arows4667]
  all_goals rfl

theorem atot4668 : totK PD2M8K2 D2M8K2.u4668 = [0, 1647845184997, 10071033559150, 21895104846518, 18810925835992, 4928049383236, 263337742252, 1394496256] := by
  rw [show D2M8K2.u4668 = KTree.node D2M8K2.u4636 (nat_lit 10416235) (nat_lit 1595479620) (nat_lit 0) D2M8K2.u4667 from rfl, totK_node, atot4636, atot4667]
  decide +kernel

theorem arows4731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4731 = true := by
  rw [show D2M8K2.u4731 = KTree.node D2M8K2.u4699 (nat_lit 10521648) (nat_lit 2959553890) (nat_lit 0) D2M8K2.u4730 from rfl, allE_node, arows4699, irow4731, arows4730]
  all_goals rfl

theorem atot4731 : totK PD2M8K2 D2M8K2.u4731 = [0, 4155865316953, 17362577471033, 23434765308414, 11365266551296, 1746277549096, 58018127943, 0] := by
  rw [show D2M8K2.u4731 = KTree.node D2M8K2.u4699 (nat_lit 10521648) (nat_lit 2959553890) (nat_lit 0) D2M8K2.u4730 from rfl, totK_node, atot4699, atot4730]
  decide +kernel

theorem arows4795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4795 = true := by
  rw [show D2M8K2.u4795 = KTree.node D2M8K2.u4763 (nat_lit 10629308) (nat_lit 3290411903) (nat_lit 0) D2M8K2.u4794 from rfl, allE_node, arows4763, irow4795, arows4794]
  all_goals rfl

theorem atot4795 : totK PD2M8K2 D2M8K2.u4795 = [0, 3538520248134, 16553381524726, 24585447310887, 11551101750611, 1272833244013, 25181293312, 0] := by
  rw [show D2M8K2.u4795 = KTree.node D2M8K2.u4763 (nat_lit 10629308) (nat_lit 3290411903) (nat_lit 0) D2M8K2.u4794 from rfl, totK_node, atot4763, atot4794]
  decide +kernel

theorem arows4858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4858 = true := by
  rw [show D2M8K2.u4858 = KTree.node D2M8K2.u4826 (nat_lit 10715944) (nat_lit 3451968748) (nat_lit 0) D2M8K2.u4857 from rfl, allE_node, arows4826, irow4858, arows4857]
  all_goals rfl

theorem atot4858 : totK PD2M8K2 D2M8K2.u4858 = [0, 440288014109, 8822093247719, 24898997397182, 19797169154840, 3748609752024, 128044240138, 0] := by
  rw [show D2M8K2.u4858 = KTree.node D2M8K2.u4826 (nat_lit 10715944) (nat_lit 3451968748) (nat_lit 0) D2M8K2.u4857 from rfl, totK_node, atot4826, atot4857]
  decide +kernel

theorem arows4923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4923 = true := by
  rw [show D2M8K2.u4923 = KTree.node D2M8K2.u4891 (nat_lit 10872939) (nat_lit 3687752868) (nat_lit 0) D2M8K2.u4922 from rfl, allE_node, arows4891, irow4923, arows4922]
  all_goals rfl

theorem atot4923 : totK PD2M8K2 D2M8K2.u4923 = [0, 0, 4297737178035, 19067719614329, 24665540349866, 8664739788434, 687009443550, 8535762846] := by
  rw [show D2M8K2.u4923 = KTree.node D2M8K2.u4891 (nat_lit 10872939) (nat_lit 3687752868) (nat_lit 0) D2M8K2.u4922 from rfl, totK_node, atot4891, atot4922]
  decide +kernel

theorem arows4986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4986 = true := by
  rw [show D2M8K2.u4986 = KTree.node D2M8K2.u4954 (nat_lit 10983997) (nat_lit 983898430) (nat_lit 0) D2M8K2.u4985 from rfl, allE_node, arows4954, irow4986, arows4985]
  all_goals rfl

theorem atot4986 : totK PD2M8K2 D2M8K2.u4986 = [0, 3690298243741, 16654406832263, 23875047454466, 11612944126813, 1879678722907, 71303664461, 0] := by
  rw [show D2M8K2.u4986 = KTree.node D2M8K2.u4954 (nat_lit 10983997) (nat_lit 983898430) (nat_lit 0) D2M8K2.u4985 from rfl, totK_node, atot4954, atot4985]
  decide +kernel

theorem arows5050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5050 = true := by
  rw [show D2M8K2.u5050 = KTree.node D2M8K2.u5018 (nat_lit 11056091) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u5049 from rfl, allE_node, arows5018, irow5050, arows5049]
  all_goals rfl

theorem atot5050 : totK PD2M8K2 D2M8K2.u5050 = [0, 3974097099713, 17049300774532, 23650719529887, 11478964657837, 1518615342238, 34733444262, 0] := by
  rw [show D2M8K2.u5050 = KTree.node D2M8K2.u5018 (nat_lit 11056091) (nat_lit 2842696641) (nat_lit 0) D2M8K2.u5049 from rfl, totK_node, atot5018, atot5049]
  decide +kernel

theorem arows5113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5113 = true := by
  rw [show D2M8K2.u5113 = KTree.node D2M8K2.u5081 (nat_lit 11128746) (nat_lit 3660937937) (nat_lit 0) D2M8K2.u5112 from rfl, allE_node, arows5081, irow5113, arows5112]
  all_goals rfl

theorem atot5113 : totK PD2M8K2 D2M8K2.u5113 = [0, 2102292844326, 13148929873009, 25313911204008, 14968261236920, 1730672616216, 30009341860, 0] := by
  rw [show D2M8K2.u5113 = KTree.node D2M8K2.u5081 (nat_lit 11128746) (nat_lit 3660937937) (nat_lit 0) D2M8K2.u5112 from rfl, totK_node, atot5081, atot5112]
  decide +kernel

theorem arows5180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5180 = true := by
  rw [show D2M8K2.u5180 = KTree.node D2M8K2.u5148 (nat_lit 11294688) (nat_lit 2672641451) (nat_lit 0) D2M8K2.u5179 from rfl, allE_node, arows5148, irow5180, arows5179]
  all_goals rfl

theorem atot5180 : totK PD2M8K2 D2M8K2.u5180 = [0, 0, 6737624475046, 23961723287948, 22502567991441, 4681300259825, 163411016759, 0] := by
  rw [show D2M8K2.u5180 = KTree.node D2M8K2.u5148 (nat_lit 11294688) (nat_lit 2672641451) (nat_lit 0) D2M8K2.u5179 from rfl, totK_node, atot5148, atot5179]
  decide +kernel

theorem arows5243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5243 = true := by
  rw [show D2M8K2.u5243 = KTree.node D2M8K2.u5211 (nat_lit 11456435) (nat_lit 2883648932) (nat_lit 0) D2M8K2.u5242 from rfl, allE_node, arows5211, irow5243, arows5242]
  all_goals rfl

theorem atot5243 : totK PD2M8K2 D2M8K2.u5243 = [0, 3030482235072, 13586934727000, 21689395860654, 14939121585725, 3991990242455, 287697609718, 1493059870] := by
  rw [show D2M8K2.u5243 = KTree.node D2M8K2.u5211 (nat_lit 11456435) (nat_lit 2883648932) (nat_lit 0) D2M8K2.u5242 from rfl, totK_node, atot5211, atot5242]
  decide +kernel

theorem arows5307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5307 = true := by
  rw [show D2M8K2.u5307 = KTree.node D2M8K2.u5275 (nat_lit 11534242) (nat_lit 4194847968) (nat_lit 0) D2M8K2.u5306 from rfl, allE_node, arows5275, irow5307, arows5306]
  all_goals rfl

theorem atot5307 : totK PD2M8K2 D2M8K2.u5307 = [0, 3041447087876, 14865809409490, 23893308645954, 13822603045327, 2252725975028, 70022404608, 0] := by
  rw [show D2M8K2.u5307 = KTree.node D2M8K2.u5275 (nat_lit 11534242) (nat_lit 4194847968) (nat_lit 0) D2M8K2.u5306 from rfl, totK_node, atot5275, atot5306]
  decide +kernel

theorem arows5370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5370 = true := by
  rw [show D2M8K2.u5370 = KTree.node D2M8K2.u5338 (nat_lit 11654248) (nat_lit 3862351557) (nat_lit 0) D2M8K2.u5369 from rfl, allE_node, arows5338, irow5370, arows5369]
  all_goals rfl

theorem atot5370 : totK PD2M8K2 D2M8K2.u5370 = [0, 3725396281497, 16930113155489, 24450229473547, 11454663915297, 1206551693260, 18333459277, 0] := by
  rw [show D2M8K2.u5370 = KTree.node D2M8K2.u5338 (nat_lit 11654248) (nat_lit 3862351557) (nat_lit 0) D2M8K2.u5369 from rfl, totK_node, atot5338, atot5369]
  decide +kernel

theorem arows5435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5435 = true := by
  rw [show D2M8K2.u5435 = KTree.node D2M8K2.u5403 (nat_lit 11753502) (nat_lit 3860568084) (nat_lit 0) D2M8K2.u5434 from rfl, allE_node, arows5403, irow5435, arows5434]
  all_goals rfl

theorem atot5435 : totK PD2M8K2 D2M8K2.u5435 = [0, 0, 6191475990701, 22370506210814, 22790165051388, 6114050889351, 324776771499, 1501162176] := by
  rw [show D2M8K2.u5435 = KTree.node D2M8K2.u5403 (nat_lit 11753502) (nat_lit 3860568084) (nat_lit 0) D2M8K2.u5434 from rfl, totK_node, atot5403, atot5434]
  decide +kernel

theorem arows5498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5498 = true := by
  rw [show D2M8K2.u5498 = KTree.node D2M8K2.u5466 (nat_lit 11904133) (nat_lit 1083933490) (nat_lit 0) D2M8K2.u5497 from rfl, allE_node, arows5466, irow5498, arows5497]
  all_goals rfl

theorem atot5498 : totK PD2M8K2 D2M8K2.u5498 = [0, 0, 4077180317279, 18412740662724, 24953512117117, 9456156759764, 693738758779, 4333001713] := by
  rw [show D2M8K2.u5498 = KTree.node D2M8K2.u5466 (nat_lit 11904133) (nat_lit 1083933490) (nat_lit 0) D2M8K2.u5497 from rfl, totK_node, atot5466, atot5497]
  decide +kernel

theorem arows5562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5562 = true := by
  rw [show D2M8K2.u5562 = KTree.node D2M8K2.u5530 (nat_lit 11979909) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u5561 from rfl, allE_node, arows5530, irow5562, arows5561]
  all_goals rfl

theorem atot5562 : totK PD2M8K2 D2M8K2.u5562 = [4131452540696, 17997649082145, 23846126243141, 9364126729887, 1120020247063, 633251217702, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5562 = KTree.node D2M8K2.u5530 (nat_lit 11979909) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u5561 from rfl, totK_node, atot5530, atot5561]
  decide +kernel

theorem arows5625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5625 = true := by
  rw [show D2M8K2.u5625 = KTree.node D2M8K2.u5593 (nat_lit 12104968) (nat_lit 2536439163) (nat_lit 0) D2M8K2.u5624 from rfl, allE_node, arows5593, irow5625, arows5624]
  all_goals rfl

theorem atot5625 : totK PD2M8K2 D2M8K2.u5625 = [3626292886699, 16826625490915, 24411100327242, 11105240945235, 1195062588623, 24778574581, 0, 0] := by
  rw [show D2M8K2.u5625 = KTree.node D2M8K2.u5593 (nat_lit 12104968) (nat_lit 2536439163) (nat_lit 0) D2M8K2.u5624 from rfl, totK_node, atot5593, atot5624]
  decide +kernel

theorem arows5691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5691 = true := by
  rw [show D2M8K2.u5691 = KTree.node D2M8K2.u5659 (nat_lit 12180834) (nat_lit 1238914651) (nat_lit 0) D2M8K2.u5690 from rfl, allE_node, arows5659, irow5691, arows5690]
  all_goals rfl

theorem atot5691 : totK PD2M8K2 D2M8K2.u5691 = [1988996583632, 11582089531704, 23112007400482, 16990859311206, 3360460646673, 173896123117, 1369150432, 0] := by
  rw [show D2M8K2.u5691 = KTree.node D2M8K2.u5659 (nat_lit 12180834) (nat_lit 1238914651) (nat_lit 0) D2M8K2.u5690 from rfl, totK_node, atot5659, atot5690]
  decide +kernel

theorem arows5754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5754 = true := by
  rw [show D2M8K2.u5754 = KTree.node D2M8K2.u5722 (nat_lit 12320442) (nat_lit 3833466974) (nat_lit 0) D2M8K2.u5753 from rfl, allE_node, arows5722, irow5754, arows5753]
  all_goals rfl

theorem atot5754 : totK PD2M8K2 D2M8K2.u5754 = [0, 5924780701508, 22332377105992, 23178475956577, 5578280892358, 276540371454, 0, 0] := by
  rw [show D2M8K2.u5754 = KTree.node D2M8K2.u5722 (nat_lit 12320442) (nat_lit 3833466974) (nat_lit 0) D2M8K2.u5753 from rfl, totK_node, atot5722, atot5753]
  decide +kernel

theorem arows5818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5818 = true := by
  rw [show D2M8K2.u5818 = KTree.node D2M8K2.u5786 (nat_lit 12497717) (nat_lit 2313285176) (nat_lit 0) D2M8K2.u5817 from rfl, allE_node, arows5786, irow5818, arows5817]
  all_goals rfl

theorem atot5818 : totK PD2M8K2 D2M8K2.u5818 = [2801581853159, 13374064730980, 22884333569661, 15704223275141, 3067368138126, 101192036375, 0, 0] := by
  rw [show D2M8K2.u5818 = KTree.node D2M8K2.u5786 (nat_lit 12497717) (nat_lit 2313285176) (nat_lit 0) D2M8K2.u5817 from rfl, totK_node, atot5786, atot5817]
  decide +kernel

theorem arows5881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5881 = true := by
  rw [show D2M8K2.u5881 = KTree.node D2M8K2.u5849 (nat_lit 12570437) (nat_lit 1923317089) (nat_lit 0) D2M8K2.u5880 from rfl, allE_node, arows5849, irow5881, arows5880]
  all_goals rfl

theorem atot5881 : totK PD2M8K2 D2M8K2.u5881 = [3531628579695, 16478065231497, 24403408359449, 11781089348379, 1436258762186, 36623127651, 0, 0] := by
  rw [show D2M8K2.u5881 = KTree.node D2M8K2.u5849 (nat_lit 12570437) (nat_lit 1923317089) (nat_lit 0) D2M8K2.u5880 from rfl, totK_node, atot5849, atot5880]
  decide +kernel

theorem arows5946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5946 = true := by
  rw [show D2M8K2.u5946 = KTree.node D2M8K2.u5914 (nat_lit 12652756) (nat_lit 4030790800) (nat_lit 0) D2M8K2.u5945 from rfl, allE_node, arows5914, irow5946, arows5945]
  all_goals rfl

theorem atot5946 : totK PD2M8K2 D2M8K2.u5946 = [3472343576529, 16543987321581, 24775463878082, 11703962927699, 1224268544030, 17236889011, 0, 0] := by
  rw [show D2M8K2.u5946 = KTree.node D2M8K2.u5914 (nat_lit 12652756) (nat_lit 4030790800) (nat_lit 0) D2M8K2.u5945 from rfl, totK_node, atot5914, atot5945]
  decide +kernel

theorem arows6009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6009 = true := by
  rw [show D2M8K2.u6009 = KTree.node D2M8K2.u5977 (nat_lit 12763147) (nat_lit 1609007211) (nat_lit 0) D2M8K2.u6008 from rfl, allE_node, arows5977, irow6009, arows6008]
  all_goals rfl

theorem atot6009 : totK PD2M8K2 D2M8K2.u6009 = [0, 4160055232832, 17487188224478, 23258256166569, 10975175559116, 1645957484653, 57647371591, 0] := by
  rw [show D2M8K2.u6009 = KTree.node D2M8K2.u5977 (nat_lit 12763147) (nat_lit 1609007211) (nat_lit 0) D2M8K2.u6008 from rfl, totK_node, atot5977, atot6008]
  decide +kernel

theorem arows6073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6073 = true := by
  rw [show D2M8K2.u6073 = KTree.node D2M8K2.u6041 (nat_lit 12846051) (nat_lit 2731630620) (nat_lit 0) D2M8K2.u6072 from rfl, allE_node, arows6041, irow6073, arows6072]
  all_goals rfl

theorem atot6073 : totK PD2M8K2 D2M8K2.u6073 = [0, 3649765939535, 17081197185351, 24716590782154, 10941206488065, 1041566705711, 13171198502, 0] := by
  rw [show D2M8K2.u6073 = KTree.node D2M8K2.u6041 (nat_lit 12846051) (nat_lit 2731630620) (nat_lit 0) D2M8K2.u6072 from rfl, totK_node, atot6041, atot6072]
  decide +kernel

theorem arows6136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6136 = true := by
  rw [show D2M8K2.u6136 = KTree.node D2M8K2.u6104 (nat_lit 12923516) (nat_lit 2585743037) (nat_lit 0) D2M8K2.u6135 from rfl, allE_node, arows6104, irow6136, arows6135]
  all_goals rfl

theorem atot6136 : totK PD2M8K2 D2M8K2.u6136 = [2005649722024, 9386736039695, 17905886253260, 18700714919878, 8595928030461, 924115566970, 13619666203, 0] := by
  rw [show D2M8K2.u6136 = KTree.node D2M8K2.u6104 (nat_lit 12923516) (nat_lit 2585743037) (nat_lit 0) D2M8K2.u6135 from rfl, totK_node, atot6104, atot6135]
  decide +kernel

theorem arows6204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6204 = true := by
  rw [show D2M8K2.u6204 = KTree.node D2M8K2.u6172 (nat_lit 13005646) (nat_lit 4004602945) (nat_lit 0) D2M8K2.u6203 from rfl, allE_node, arows6172, irow6204, arows6203]
  all_goals rfl

theorem atot6204 : totK PD2M8K2 D2M8K2.u6204 = [3454408949353, 15845000477323, 23903333537045, 12659210601759, 1947077240945, 59387278375, 0, 0] := by
  rw [show D2M8K2.u6204 = KTree.node D2M8K2.u6172 (nat_lit 13005646) (nat_lit 4004602945) (nat_lit 0) D2M8K2.u6203 from rfl, totK_node, atot6172, atot6203]
  decide +kernel

theorem arows6267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6267 = true := by
  rw [show D2M8K2.u6267 = KTree.node D2M8K2.u6235 (nat_lit 13112043) (nat_lit 3482221614) (nat_lit 0) D2M8K2.u6266 from rfl, allE_node, arows6235, irow6267, arows6266]
  all_goals rfl

theorem atot6267 : totK PD2M8K2 D2M8K2.u6267 = [3545683083409, 16685591344939, 24552713550317, 11328165604412, 1247947131502, 24912417204, 0, 0] := by
  rw [show D2M8K2.u6267 = KTree.node D2M8K2.u6235 (nat_lit 13112043) (nat_lit 3482221614) (nat_lit 0) D2M8K2.u6266 from rfl, totK_node, atot6235, atot6266]
  decide +kernel

theorem arows6331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6331 = true := by
  rw [show D2M8K2.u6331 = KTree.node D2M8K2.u6299 (nat_lit 13189264) (nat_lit 3342749478) (nat_lit 0) D2M8K2.u6330 from rfl, allE_node, arows6299, irow6331, arows6330]
  all_goals rfl

theorem atot6331 : totK PD2M8K2 D2M8K2.u6331 = [1195523425885, 8955623051069, 22125667397902, 19830317616149, 4933614479513, 267564329344, 1275377855, 0] := by
  rw [show D2M8K2.u6331 = KTree.node D2M8K2.u6299 (nat_lit 13189264) (nat_lit 3342749478) (nat_lit 0) D2M8K2.u6330 from rfl, totK_node, atot6299, atot6330]
  decide +kernel

theorem arows6394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6394 = true := by
  rw [show D2M8K2.u6394 = KTree.node D2M8K2.u6362 (nat_lit 13287568) (nat_lit 2767715103) (nat_lit 0) D2M8K2.u6393 from rfl, allE_node, arows6362, irow6394, arows6393]
  all_goals rfl

theorem atot6394 : totK PD2M8K2 D2M8K2.u6394 = [0, 4982443688084, 19908615096076, 23549764927182, 8151165761601, 792681587545, 18797058808, 0] := by
  rw [show D2M8K2.u6394 = KTree.node D2M8K2.u6362 (nat_lit 13287568) (nat_lit 2767715103) (nat_lit 0) D2M8K2.u6393 from rfl, totK_node, atot6362, atot6393]
  decide +kernel

theorem arows6459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6459 = true := by
  rw [show D2M8K2.u6459 = KTree.node D2M8K2.u6427 (nat_lit 13406236) (nat_lit 3637242284) (nat_lit 0) D2M8K2.u6458 from rfl, allE_node, arows6427, irow6459, arows6458]
  all_goals rfl

theorem atot6459 : totK PD2M8K2 D2M8K2.u6459 = [1973854997411, 10586563245754, 20969082456071, 17867981025334, 5295557651660, 388481047872, 5883117146, 0] := by
  rw [show D2M8K2.u6459 = KTree.node D2M8K2.u6427 (nat_lit 13406236) (nat_lit 3637242284) (nat_lit 0) D2M8K2.u6458 from rfl, totK_node, atot6427, atot6458]
  decide +kernel

theorem arows6522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6522 = true := by
  rw [show D2M8K2.u6522 = KTree.node D2M8K2.u6490 (nat_lit 14004265) (nat_lit 1070050383) (nat_lit 0) D2M8K2.u6521 from rfl, allE_node, arows6490, irow6522, arows6521]
  all_goals rfl

theorem atot6522 : totK PD2M8K2 D2M8K2.u6522 = [4034523693643, 17079075550102, 23427531317541, 11565964675101, 1787419989412, 58018127943, 0, 0] := by
  rw [show D2M8K2.u6522 = KTree.node D2M8K2.u6490 (nat_lit 14004265) (nat_lit 1070050383) (nat_lit 0) D2M8K2.u6521 from rfl, totK_node, atot6490, atot6521]
  decide +kernel

theorem arows6586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6586 = true := by
  rw [show D2M8K2.u6586 = KTree.node D2M8K2.u6554 (nat_lit 14074618) (nat_lit 2599852975) (nat_lit 0) D2M8K2.u6585 from rfl, allE_node, arows6554, irow6586, arows6585]
  all_goals rfl

theorem atot6586 : totK PD2M8K2 D2M8K2.u6586 = [3396477191237, 16032647862242, 24196374973259, 12070074559578, 1502364228587, 37862993724, 0, 0] := by
  rw [show D2M8K2.u6586 = KTree.node D2M8K2.u6554 (nat_lit 14074618) (nat_lit 2599852975) (nat_lit 0) D2M8K2.u6585 from rfl, totK_node, atot6554, atot6585]
  decide +kernel

theorem arows6649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6649 = true := by
  rw [show D2M8K2.u6649 = KTree.node D2M8K2.u6617 (nat_lit 14199142) (nat_lit 1270123041) (nat_lit 0) D2M8K2.u6648 from rfl, allE_node, arows6617, irow6649, arows6648]
  all_goals rfl

theorem atot6649 : totK PD2M8K2 D2M8K2.u6649 = [357800183586, 7337174776463, 22956143122829, 21251910141512, 5081597022486, 266576228759, 1209030869, 0] := by
  rw [show D2M8K2.u6649 = KTree.node D2M8K2.u6617 (nat_lit 14199142) (nat_lit 1270123041) (nat_lit 0) D2M8K2.u6648 from rfl, totK_node, atot6617, atot6648]
  decide +kernel

theorem arows6715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6715 = true := by
  rw [show D2M8K2.u6715 = KTree.node D2M8K2.u6683 (nat_lit 14320892) (nat_lit 3364820716) (nat_lit 0) D2M8K2.u6714 from rfl, allE_node, arows6683, irow6715, arows6714]
  all_goals rfl

theorem atot6715 : totK PD2M8K2 D2M8K2.u6715 = [0, 5859870255183, 22155639251677, 23267113118925, 5865615715763, 295701435919, 1138244013, 0] := by
  rw [show D2M8K2.u6715 = KTree.node D2M8K2.u6683 (nat_lit 14320892) (nat_lit 3364820716) (nat_lit 0) D2M8K2.u6714 from rfl, totK_node, atot6683, atot6714]
  decide +kernel

theorem arows6778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6778 = true := by
  rw [show D2M8K2.u6778 = KTree.node D2M8K2.u6746 (nat_lit 14463516) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u6777 from rfl, allE_node, arows6746, irow6778, arows6777]
  all_goals rfl

theorem atot6778 : totK PD2M8K2 D2M8K2.u6778 = [3982102962798, 16824220187095, 22479468668145, 11164931719209, 2768087675443, 289714238634, 4977114383, 0] := by
  rw [show D2M8K2.u6778 = KTree.node D2M8K2.u6746 (nat_lit 14463516) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u6777 from rfl, totK_node, atot6746, atot6777]
  decide +kernel

theorem arows6842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6842 = true := by
  rw [show D2M8K2.u6842 = KTree.node D2M8K2.u6810 (nat_lit 14534608) (nat_lit 3303315757) (nat_lit 0) D2M8K2.u6841 from rfl, allE_node, arows6810, irow6842, arows6841]
  all_goals rfl

theorem atot6842 : totK PD2M8K2 D2M8K2.u6842 = [3697746283978, 16206464384982, 23629413697130, 12459156238852, 1775232816774, 39893312897, 0, 0] := by
  rw [show D2M8K2.u6842 = KTree.node D2M8K2.u6810 (nat_lit 14534608) (nat_lit 3303315757) (nat_lit 0) D2M8K2.u6841 from rfl, totK_node, atot6810, atot6841]
  decide +kernel

theorem arows6905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6905 = true := by
  rw [show D2M8K2.u6905 = KTree.node D2M8K2.u6873 (nat_lit 14658009) (nat_lit 980213353) (nat_lit 0) D2M8K2.u6904 from rfl, allE_node, arows6873, irow6905, arows6904]
  all_goals rfl

theorem atot6905 : totK PD2M8K2 D2M8K2.u6905 = [2111905449398, 12803178074879, 24566375790403, 15594115101897, 2324617480430, 58988913241, 0, 0] := by
  rw [show D2M8K2.u6905 = KTree.node D2M8K2.u6873 (nat_lit 14658009) (nat_lit 980213353) (nat_lit 0) D2M8K2.u6904 from rfl, totK_node, atot6873, atot6904]
  decide +kernel

theorem arows6970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6970 = true := by
  rw [show D2M8K2.u6970 = KTree.node D2M8K2.u6938 (nat_lit 14736881) (nat_lit 1736990360) (nat_lit 0) D2M8K2.u6969 from rfl, allE_node, arows6938, irow6970, arows6969]
  all_goals rfl

theorem atot6970 : totK PD2M8K2 D2M8K2.u6970 = [0, 4774565851867, 19806481074875, 24326696213427, 8024127469746, 472648899203, 2535870848, 0] := by
  rw [show D2M8K2.u6970 = KTree.node D2M8K2.u6938 (nat_lit 14736881) (nat_lit 1736990360) (nat_lit 0) D2M8K2.u6969 from rfl, totK_node, atot6938, atot6969]
  decide +kernel

theorem arows7033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7033 = true := by
  rw [show D2M8K2.u7033 = KTree.node D2M8K2.u7001 (nat_lit 14838562) (nat_lit 3591470567) (nat_lit 0) D2M8K2.u7032 from rfl, allE_node, arows7001, irow7033, arows7032]
  all_goals rfl

theorem atot7033 : totK PD2M8K2 D2M8K2.u7033 = [0, 3766738106497, 17469440555102, 24753102133195, 10296152122038, 915933748633, 12787178760, 0] := by
  rw [show D2M8K2.u7033 = KTree.node D2M8K2.u7001 (nat_lit 14838562) (nat_lit 3591470567) (nat_lit 0) D2M8K2.u7032 from rfl, totK_node, atot7001, atot7032]
  decide +kernel

theorem arows7097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7097 = true := by
  rw [show D2M8K2.u7097 = KTree.node D2M8K2.u7065 (nat_lit 14952176) (nat_lit 2764404734) (nat_lit 0) D2M8K2.u7096 from rfl, allE_node, arows7065, irow7097, arows7096]
  all_goals rfl

theorem atot7097 : totK PD2M8K2 D2M8K2.u7097 = [0, 4131452540696, 17921657276373, 23985884641840, 9903600253706, 1156845066419, 32745616081, 0] := by
  rw [show D2M8K2.u7097 = KTree.node D2M8K2.u7065 (nat_lit 14952176) (nat_lit 2764404734) (nat_lit 0) D2M8K2.u7096 from rfl, totK_node, atot7065, atot7096]
  decide +kernel

theorem arows7160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7160 = true := by
  rw [show D2M8K2.u7160 = KTree.node D2M8K2.u7128 (nat_lit 15076932) (nat_lit 3269347075) (nat_lit 0) D2M8K2.u7159 from rfl, allE_node, arows7128, irow7160, arows7159]
  all_goals rfl

theorem atot7160 : totK PD2M8K2 D2M8K2.u7160 = [0, 3626292886699, 17001691719245, 24724057807645, 10731404705714, 1073005809976, 21175168894, 0] := by
  rw [show D2M8K2.u7160 = KTree.node D2M8K2.u7128 (nat_lit 15076932) (nat_lit 3269347075) (nat_lit 0) D2M8K2.u7159 from rfl, totK_node, atot7128, atot7159]
  decide +kernel

theorem arows7227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7227 = true := by
  rw [show D2M8K2.u7227 = KTree.node D2M8K2.u7195 (nat_lit 15162261) (nat_lit 1128901359) (nat_lit 0) D2M8K2.u7226 from rfl, allE_node, arows7195, irow7227, arows7226]
  all_goals rfl

theorem atot7227 : totK PD2M8K2 D2M8K2.u7227 = [0, 1988996583632, 12286429736496, 24378166135238, 15984659656161, 2506660121526, 77571812180, 0] := by
  rw [show D2M8K2.u7227 = KTree.node D2M8K2.u7195 (nat_lit 15162261) (nat_lit 1128901359) (nat_lit 0) D2M8K2.u7226 from rfl, totK_node, atot7195, atot7226]
  decide +kernel

theorem arows7290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7290 = true := by
  rw [show D2M8K2.u7290 = KTree.node D2M8K2.u7258 (nat_lit 15314562) (nat_lit 3311549997) (nat_lit 0) D2M8K2.u7289 from rfl, allE_node, arows7258, irow7290, arows7289]
  all_goals rfl

theorem atot7290 : totK PD2M8K2 D2M8K2.u7290 = [0, 0, 6786314804302, 23959539710074, 21894608199638, 4353982399425, 217712456750, 1369150432] := by
  rw [show D2M8K2.u7290 = KTree.node D2M8K2.u7258 (nat_lit 15314562) (nat_lit 3311549997) (nat_lit 0) D2M8K2.u7289 from rfl, totK_node, atot7258, atot7289]
  decide +kernel

theorem arows7354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7354 = true := by
  rw [show D2M8K2.u7354 = KTree.node D2M8K2.u7322 (nat_lit 15495694) (nat_lit 3963947503) (nat_lit 0) D2M8K2.u7353 from rfl, allE_node, arows7322, irow7354, arows7353]
  all_goals rfl

theorem atot7354 : totK PD2M8K2 D2M8K2.u7354 = [0, 3742939307385, 16086964222213, 23118232917622, 12799916744439, 2208362301877, 77020877379, 0] := by
  rw [show D2M8K2.u7354 = KTree.node D2M8K2.u7322 (nat_lit 15495694) (nat_lit 3963947503) (nat_lit 0) D2M8K2.u7353 from rfl, totK_node, atot7322, atot7353]
  decide +kernel

theorem arows7417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7417 = true := by
  rw [show D2M8K2.u7417 = KTree.node D2M8K2.u7385 (nat_lit 15569544) (nat_lit 3605856933) (nat_lit 0) D2M8K2.u7416 from rfl, allE_node, arows7385, irow7417, arows7416]
  all_goals rfl

theorem atot7417 : totK PD2M8K2 D2M8K2.u7417 = [0, 3801195702786, 17199023780319, 24463530540962, 11038471344529, 1196193552937, 24723801900, 0] := by
  rw [show D2M8K2.u7417 = KTree.node D2M8K2.u7385 (nat_lit 15569544) (nat_lit 3605856933) (nat_lit 0) D2M8K2.u7416 from rfl, totK_node, atot7385, atot7416]
  decide +kernel

theorem arows7482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7482 = true := by
  rw [show D2M8K2.u7482 = KTree.node D2M8K2.u7450 (nat_lit 15652954) (nat_lit 3808469700) (nat_lit 0) D2M8K2.u7481 from rfl, allE_node, arows7450, irow7482, arows7481]
  all_goals rfl

theorem atot7482 : totK PD2M8K2 D2M8K2.u7482 = [0, 3690305895761, 16914493154656, 24389295056980, 11351547398233, 1357894545105, 30625953757, 0] := by
  rw [show D2M8K2.u7482 = KTree.node D2M8K2.u7450 (nat_lit 15652954) (nat_lit 3808469700) (nat_lit 0) D2M8K2.u7481 from rfl, totK_node, atot7450, atot7481]
  decide +kernel

theorem arows7545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7545 = true := by
  rw [show D2M8K2.u7545 = KTree.node D2M8K2.u7513 (nat_lit 15981090) (nat_lit 3306351170) (nat_lit 0) D2M8K2.u7544 from rfl, allE_node, arows7513, irow7545, arows7544]
  all_goals rfl

theorem atot7545 : totK PD2M8K2 D2M8K2.u7545 = [0, 3452376752483, 16402696175285, 24557182594198, 11768920243480, 1500396784105, 37736554897, 0] := by
  rw [show D2M8K2.u7545 = KTree.node D2M8K2.u7513 (nat_lit 15981090) (nat_lit 3306351170) (nat_lit 0) D2M8K2.u7544 from rfl, totK_node, atot7513, atot7544]
  decide +kernel

theorem arows7609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7609 = true := by
  rw [show D2M8K2.u7609 = KTree.node D2M8K2.u7577 (nat_lit 16092742) (nat_lit 3473097264) (nat_lit 0) D2M8K2.u7608 from rfl, allE_node, arows7577, irow7609, arows7608]
  all_goals rfl

theorem atot7609 : totK PD2M8K2 D2M8K2.u7609 = [0, 3553972642518, 16687542247202, 24695765929300, 11192386652069, 1167302210305, 24912417204, 0] := by
  rw [show D2M8K2.u7609 = KTree.node D2M8K2.u7577 (nat_lit 16092742) (nat_lit 3473097264) (nat_lit 0) D2M8K2.u7608 from rfl, totK_node, atot7577, atot7608]
  decide +kernel

theorem arows7672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7672 = true := by
  rw [show D2M8K2.u7672 = KTree.node D2M8K2.u7640 (nat_lit 16171637) (nat_lit 1131443647) (nat_lit 0) D2M8K2.u7671 from rfl, allE_node, arows7640, irow7672, arows7671]
  all_goals rfl

theorem atot7672 : totK PD2M8K2 D2M8K2.u7672 = [0, 1769564901391, 10698731678038, 22497535968544, 17904590013694, 4111503502241, 229294462313, 1275377855] := by
  rw [show D2M8K2.u7672 = KTree.node D2M8K2.u7640 (nat_lit 16171637) (nat_lit 1131443647) (nat_lit 0) D2M8K2.u7671 from rfl, totK_node, atot7640, atot7671]
  decide +kernel

theorem arows7738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7738 = true := by
  rw [show D2M8K2.u7738 = KTree.node D2M8K2.u7706 (nat_lit 16273168) (nat_lit 3385930378) (nat_lit 0) D2M8K2.u7737 from rfl, allE_node, arows7706, irow7738, arows7737]
  all_goals rfl

theorem atot7738 : totK PD2M8K2 D2M8K2.u7738 = [0, 0, 5336595265859, 20505312430036, 22982743400111, 7730217058259, 787988932838, 18797058808] := by
  rw [show D2M8K2.u7738 = KTree.node D2M8K2.u7706 (nat_lit 16273168) (nat_lit 3385930378) (nat_lit 0) D2M8K2.u7737 from rfl, totK_node, atot7706, atot7737]
  decide +kernel

theorem arows7801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7801 = true := by
  rw [show D2M8K2.u7801 = KTree.node D2M8K2.u7769 (nat_lit 16398944) (nat_lit 2980273920) (nat_lit 0) D2M8K2.u7800 from rfl, allE_node, arows7769, irow7801, arows7800]
  all_goals rfl

theorem atot7801 : totK PD2M8K2 D2M8K2.u7801 = [0, 1973854997411, 11229569183742, 22008456546050, 16865970680498, 4523631283825, 355446176144, 5883117146] := by
  rw [show D2M8K2.u7801 = KTree.node D2M8K2.u7769 (nat_lit 16398944) (nat_lit 2980273920) (nat_lit 0) D2M8K2.u7800 from rfl, totK_node, atot7769, atot7800]
  decide +kernel

theorem arows7865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7865 = true := by
  rw [show D2M8K2.u7865 = KTree.node D2M8K2.u7833 (nat_lit 16994398) (nat_lit 3241561619) (nat_lit 0) D2M8K2.u7864 from rfl, allE_node, arows7833, irow7865, arows7864]
  all_goals rfl

theorem atot7865 : totK PD2M8K2 D2M8K2.u7865 = [0, 4034523693643, 17683881536806, 24294415929613, 10736806050049, 1209250822896, 22870585753, 0] := by
  rw [show D2M8K2.u7865 = KTree.node D2M8K2.u7833 (nat_lit 16994398) (nat_lit 3241561619) (nat_lit 0) D2M8K2.u7864 from rfl, totK_node, atot7833, atot7864]
  decide +kernel

theorem arows7928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7928 = true := by
  rw [show D2M8K2.u7928 = KTree.node D2M8K2.u7896 (nat_lit 17077137) (nat_lit 1577325410) (nat_lit 0) D2M8K2.u7927 from rfl, allE_node, arows7896, irow7928, arows7927]
  all_goals rfl

theorem atot7928 : totK PD2M8K2 D2M8K2.u7928 = [0, 3754277374823, 17145987084652, 24498215177114, 10729866384564, 1121942980339, 24689321558, 0] := by
  rw [show D2M8K2.u7928 = KTree.node D2M8K2.u7896 (nat_lit 17077137) (nat_lit 1577325410) (nat_lit 0) D2M8K2.u7927 from rfl, totK_node, atot7896, atot7927]
  decide +kernel

theorem arows7993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7993 = true := by
  rw [show D2M8K2.u7993 = KTree.node D2M8K2.u7961 (nat_lit 17204577) (nat_lit 1818646111) (nat_lit 0) D2M8K2.u7992 from rfl, allE_node, arows7961, irow7993, arows7992]
  all_goals rfl

theorem atot7993 : totK PD2M8K2 D2M8K2.u7993 = [0, 0, 6676445360625, 23690986907429, 22030182060429, 4654012691599, 203286403345, 1209030869] := by
  rw [show D2M8K2.u7993 = KTree.node D2M8K2.u7961 (nat_lit 17204577) (nat_lit 1818646111) (nat_lit 0) D2M8K2.u7992 from rfl, totK_node, atot7961, atot7992]
  decide +kernel

theorem arows8056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8056 = true := by
  rw [show D2M8K2.u8056 = KTree.node D2M8K2.u8024 (nat_lit 17350137) (nat_lit 1738210891) (nat_lit 0) D2M8K2.u8055 from rfl, allE_node, arows8024, irow8056, arows8055]
  all_goals rfl

theorem atot8056 : totK PD2M8K2 D2M8K2.u8056 = [0, 1978604257116, 10837602021134, 21521699902851, 17621865882087, 4702366684562, 361182513262, 6115358396] := by
  rw [show D2M8K2.u8056 = KTree.node D2M8K2.u8024 (nat_lit 17350137) (nat_lit 1738210891) (nat_lit 0) D2M8K2.u8055 from rfl, totK_node, atot8024, atot8055]
  decide +kernel

theorem arows8120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8120 = true := by
  rw [show D2M8K2.u8120 = KTree.node D2M8K2.u8088 (nat_lit 17479352) (nat_lit 3487364402) (nat_lit 0) D2M8K2.u8119 from rfl, allE_node, arows8088, irow8120, arows8119]
  all_goals rfl

theorem atot8120 : totK PD2M8K2 D2M8K2.u8120 = [0, 3272132034693, 15710910475222, 24438423706109, 12641934573535, 1803347028076, 51819449663, 0] := by
  rw [show D2M8K2.u8120 = KTree.node D2M8K2.u8088 (nat_lit 17479352) (nat_lit 3487364402) (nat_lit 0) D2M8K2.u8119 from rfl, totK_node, atot8088, atot8119]
  decide +kernel

theorem arows8183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8183 = true := by
  rw [show D2M8K2.u8183 = KTree.node D2M8K2.u8151 (nat_lit 17554392) (nat_lit 3394814948) (nat_lit 0) D2M8K2.u8182 from rfl, allE_node, arows8151, irow8183, arows8182]
  all_goals rfl

theorem atot8183 : totK PD2M8K2 D2M8K2.u8183 = [0, 3861131199091, 17391131211107, 24542582431135, 10757008505245, 1082982440488, 20888360426, 0] := by
  rw [show D2M8K2.u8183 = KTree.node D2M8K2.u8151 (nat_lit 17554392) (nat_lit 3394814948) (nat_lit 0) D2M8K2.u8182 from rfl, totK_node, atot8151, atot8182]
  decide +kernel

theorem arows8253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8253 = true := by
  rw [show D2M8K2.u8253 = KTree.node D2M8K2.u8221 (nat_lit 17924930) (nat_lit 3203661312) (nat_lit 0) D2M8K2.u8252 from rfl, allE_node, arows8221, irow8253, arows8252]
  all_goals rfl

theorem atot8253 : totK PD2M8K2 D2M8K2.u8253 = [2856492535437, 12548989635192, 19187884481910, 14709035038336, 6882720266543, 1038882644546, 32872698681, 0] := by
  rw [show D2M8K2.u8253 = KTree.node D2M8K2.u8221 (nat_lit 17924930) (nat_lit 3203661312) (nat_lit 0) D2M8K2.u8252 from rfl, totK_node, atot8221, atot8252]
  decide +kernel

theorem arows8316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8316 = true := by
  rw [show D2M8K2.u8316 = KTree.node D2M8K2.u8284 (nat_lit 18051103) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u8315 from rfl, allE_node, arows8284, irow8316, arows8315]
  all_goals rfl

theorem atot8316 : totK PD2M8K2 D2M8K2.u8316 = [3499539861158, 16242345573412, 24198691479054, 11871815917469, 1478354240408, 37862993724, 0, 0] := by
  rw [show D2M8K2.u8316 = KTree.node D2M8K2.u8284 (nat_lit 18051103) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u8315 from rfl, totK_node, atot8284, atot8315]
  decide +kernel

theorem arows8380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8380 = true := by
  rw [show D2M8K2.u8380 = KTree.node D2M8K2.u8348 (nat_lit 18127043) (nat_lit 2870342021) (nat_lit 0) D2M8K2.u8379 from rfl, allE_node, arows8348, irow8380, arows8379]
  all_goals rfl

theorem atot8380 : totK PD2M8K2 D2M8K2.u8380 = [3390978368857, 16210426727477, 24580179548704, 11936737715118, 1306129147870, 18479027611, 0, 0] := by
  rw [show D2M8K2.u8380 = KTree.node D2M8K2.u8348 (nat_lit 18127043) (nat_lit 2870342021) (nat_lit 0) D2M8K2.u8379 from rfl, totK_node, atot8348, atot8379]
  decide +kernel

theorem arows8443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8443 = true := by
  rw [show D2M8K2.u8443 = KTree.node D2M8K2.u8411 (nat_lit 18203356) (nat_lit 3927371815) (nat_lit 0) D2M8K2.u8442 from rfl, allE_node, arows8411, irow8443, arows8442]
  all_goals rfl

theorem atot8443 : totK PD2M8K2 D2M8K2.u8443 = [0, 5346270619185, 21281916594639, 23692435921732, 6318318345808, 382766743357, 1369150432, 0] := by
  rw [show D2M8K2.u8443 = KTree.node D2M8K2.u8411 (nat_lit 18203356) (nat_lit 3927371815) (nat_lit 0) D2M8K2.u8442 from rfl, totK_node, atot8411, atot8442]
  decide +kernel

theorem arows8508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8508 = true := by
  rw [show D2M8K2.u8508 = KTree.node D2M8K2.u8476 (nat_lit 18380731) (nat_lit 1498448094) (nat_lit 0) D2M8K2.u8507 from rfl, allE_node, arows8476, irow8508, arows8507]
  all_goals rfl

theorem atot8508 : totK PD2M8K2 D2M8K2.u8508 = [2117734323592, 12091134471210, 23483342895215, 16909026761627, 3100631085675, 93567334575, 0, 0] := by
  rw [show D2M8K2.u8508 = KTree.node D2M8K2.u8476 (nat_lit 18380731) (nat_lit 1498448094) (nat_lit 0) D2M8K2.u8507 from rfl, totK_node, atot8476, atot8507]
  decide +kernel

theorem arows8571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8571 = true := by
  rw [show D2M8K2.u8571 = KTree.node D2M8K2.u8539 (nat_lit 18513388) (nat_lit 3511499415) (nat_lit 0) D2M8K2.u8570 from rfl, allE_node, arows8539, irow8571, arows8570]
  all_goals rfl

theorem atot8571 : totK PD2M8K2 D2M8K2.u8571 = [3287605955452, 15200256700194, 23583055258148, 13416918571195, 2248720685141, 75608720969, 0, 0] := by
  rw [show D2M8K2.u8571 = KTree.node D2M8K2.u8539 (nat_lit 18513388) (nat_lit 3511499415) (nat_lit 0) D2M8K2.u8570 from rfl, totK_node, atot8539, atot8570]
  decide +kernel

theorem arows8635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8635 = true := by
  rw [show D2M8K2.u8635 = KTree.node D2M8K2.u8603 (nat_lit 18589980) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u8634 from rfl, allE_node, arows8603, irow8635, arows8634]
  all_goals rfl

theorem atot8635 : totK PD2M8K2 D2M8K2.u8635 = [3546274231370, 16582383152377, 24566938089218, 11601161698073, 1283524138414, 25181293312, 0, 0] := by
  rw [show D2M8K2.u8635 = KTree.node D2M8K2.u8603 (nat_lit 18589980) (nat_lit 3509774347) (nat_lit 0) D2M8K2.u8634 from rfl, totK_node, atot8603, atot8634]
  decide +kernel

theorem arows8698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8698 = true := by
  rw [show D2M8K2.u8698 = KTree.node D2M8K2.u8666 (nat_lit 18711390) (nat_lit 3266331654) (nat_lit 0) D2M8K2.u8697 from rfl, allE_node, arows8666, irow8698, arows8697]
  all_goals rfl

theorem atot8698 : totK PD2M8K2 D2M8K2.u8698 = [857731848908, 7305496078582, 19401335240108, 20224262737233, 8539070247499, 1286941727751, 48508304344, 0] := by
  rw [show D2M8K2.u8698 = KTree.node D2M8K2.u8666 (nat_lit 18711390) (nat_lit 3266331654) (nat_lit 0) D2M8K2.u8697 from rfl, totK_node, atot8666, atot8697]
  decide +kernel

theorem arows8764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8764 = true := by
  rw [show D2M8K2.u8764 = KTree.node D2M8K2.u8732 (nat_lit 18786876) (nat_lit 3255558676) (nat_lit 0) D2M8K2.u8763 from rfl, allE_node, arows8732, irow8764, arows8763]
  all_goals rfl

theorem atot8764 : totK PD2M8K2 D2M8K2.u8764 = [0, 3704789797563, 16875564410685, 24266661973555, 11395856161110, 1280907041265, 22310265749, 0] := by
  rw [show D2M8K2.u8764 = KTree.node D2M8K2.u8732 (nat_lit 18786876) (nat_lit 3255558676) (nat_lit 0) D2M8K2.u8763 from rfl, totK_node, atot8732, atot8763]
  decide +kernel

theorem arows8827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8827 = true := by
  rw [show D2M8K2.u8827 = KTree.node D2M8K2.u8795 (nat_lit 18865193) (nat_lit 1674285303) (nat_lit 0) D2M8K2.u8826 from rfl, allE_node, arows8795, irow8827, arows8826]
  all_goals rfl

theorem atot8827 : totK PD2M8K2 D2M8K2.u8827 = [0, 3986822238167, 18122872931698, 24811602212413, 9922273194053, 778194301829, 4085914357, 0] := by
  rw [show D2M8K2.u8827 = KTree.node D2M8K2.u8795 (nat_lit 18865193) (nat_lit 1674285303) (nat_lit 0) D2M8K2.u8826 from rfl, totK_node, atot8795, atot8826]
  decide +kernel

theorem arows8891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8891 = true := by
  rw [show D2M8K2.u8891 = KTree.node D2M8K2.u8859 (nat_lit 19444565) (nat_lit 1484006826) (nat_lit 0) D2M8K2.u8890 from rfl, allE_node, arows8859, irow8891, arows8890]
  all_goals rfl

theorem atot8891 : totK PD2M8K2 D2M8K2.u8891 = [4034879917864, 17279296511599, 22983909554007, 10552634537630, 2429139744555, 319051684803, 9533751846, 0] := by
  rw [show D2M8K2.u8891 = KTree.node D2M8K2.u8859 (nat_lit 19444565) (nat_lit 1484006826) (nat_lit 0) D2M8K2.u8890 from rfl, totK_node, atot8859, atot8890]
  decide +kernel

theorem arows8954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8954 = true := by
  rw [show D2M8K2.u8954 = KTree.node D2M8K2.u8922 (nat_lit 19554192) (nat_lit 3743040523) (nat_lit 0) D2M8K2.u8953 from rfl, allE_node, arows8922, irow8954, arows8953]
  all_goals rfl

theorem atot8954 : totK PD2M8K2 D2M8K2.u8954 = [3792835809767, 16558637944445, 23707287175666, 11951209370395, 1593861311847, 35002320370, 0, 0] := by
  rw [show D2M8K2.u8954 = KTree.node D2M8K2.u8922 (nat_lit 19554192) (nat_lit 3743040523) (nat_lit 0) D2M8K2.u8953 from rfl, totK_node, atot8922, atot8953]
  decide +kernel

theorem arows9019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9019 = true := by
  rw [show D2M8K2.u9019 = KTree.node D2M8K2.u8987 (nat_lit 19629341) (nat_lit 1569048232) (nat_lit 0) D2M8K2.u9018 from rfl, allE_node, arows8987, irow9019, arows9018]
  all_goals rfl

theorem atot9019 : totK PD2M8K2 D2M8K2.u9019 = [2374551643528, 13787581910955, 24989610868592, 14431067881971, 1904128300907, 42719600521, 0, 0] := by
  rw [show D2M8K2.u9019 = KTree.node D2M8K2.u8987 (nat_lit 19629341) (nat_lit 1569048232) (nat_lit 0) D2M8K2.u9018 from rfl, totK_node, atot8987, atot9018]
  decide +kernel

theorem arows9082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9082 = true := by
  rw [show D2M8K2.u9082 = KTree.node D2M8K2.u9050 (nat_lit 19712409) (nat_lit 1818964075) (nat_lit 0) D2M8K2.u9081 from rfl, allE_node, arows9050, irow9082, arows9081]
  all_goals rfl

theorem atot9082 : totK PD2M8K2 D2M8K2.u9082 = [0, 4976205588676, 20416225508944, 24291311360502, 7280163452738, 388542357206, 1310517177, 0] := by
  rw [show D2M8K2.u9082 = KTree.node D2M8K2.u9050 (nat_lit 19712409) (nat_lit 1818964075) (nat_lit 0) D2M8K2.u9081 from rfl, totK_node, atot9050, atot9081]
  decide +kernel

theorem arows9146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9146 = true := by
  rw [show D2M8K2.u9146 = KTree.node D2M8K2.u9114 (nat_lit 19844362) (nat_lit 3879617763) (nat_lit 0) D2M8K2.u9145 from rfl, allE_node, arows9114, irow9146, arows9145]
  all_goals rfl

theorem atot9146 : totK PD2M8K2 D2M8K2.u9146 = [0, 4028196238061, 17892597994576, 24183881686913, 9857846680229, 1049305720996, 25006391237, 0] := by
  rw [show D2M8K2.u9146 = KTree.node D2M8K2.u9114 (nat_lit 19844362) (nat_lit 3879617763) (nat_lit 0) D2M8K2.u9145 from rfl, totK_node, atot9114, atot9145]
  decide +kernel

theorem arows9209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9209 = true := by
  rw [show D2M8K2.u9209 = KTree.node D2M8K2.u9177 (nat_lit 19951947) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u9208 from rfl, allE_node, arows9177, irow9209, arows9208]
  all_goals rfl

theorem atot9209 : totK PD2M8K2 D2M8K2.u9209 = [3972055978459, 17323505088532, 23747761118630, 10857398115680, 1597337874121, 62007804719, 0, 0] := by
  rw [show D2M8K2.u9209 = KTree.node D2M8K2.u9177 (nat_lit 19951947) (nat_lit 3776241721) (nat_lit 0) D2M8K2.u9208 from rfl, totK_node, atot9177, atot9208]
  decide +kernel

theorem arows9276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9276 = true := by
  rw [show D2M8K2.u9276 = KTree.node D2M8K2.u9244 (nat_lit 20019463) (nat_lit 1440514849) (nat_lit 0) D2M8K2.u9275 from rfl, allE_node, arows9244, irow9276, arows9275]
  all_goals rfl

theorem atot9276 : totK PD2M8K2 D2M8K2.u9276 = [3688524582665, 16593021906403, 23993910574020, 11795828180798, 1478906113471, 30754437650, 0, 0] := by
  rw [show D2M8K2.u9276 = KTree.node D2M8K2.u9244 (nat_lit 20019463) (nat_lit 1440514849) (nat_lit 0) D2M8K2.u9275 from rfl, totK_node, atot9244, atot9275]
  decide +kernel

theorem arows9339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9339 = true := by
  rw [show D2M8K2.u9339 = KTree.node D2M8K2.u9307 (nat_lit 20095802) (nat_lit 3993500260) (nat_lit 0) D2M8K2.u9338 from rfl, allE_node, arows9307, irow9339, arows9338]
  all_goals rfl

theorem atot9339 : totK PD2M8K2 D2M8K2.u9339 = [2102355608136, 12462989110333, 24022169410534, 15799414211370, 2652019058905, 86738927570, 0, 0] := by
  rw [show D2M8K2.u9339 = KTree.node D2M8K2.u9307 (nat_lit 20095802) (nat_lit 3993500260) (nat_lit 0) D2M8K2.u9338 from rfl, totK_node, atot9307, atot9338]
  decide +kernel

theorem arows9403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9403 = true := by
  rw [show D2M8K2.u9403 = KTree.node D2M8K2.u9371 (nat_lit 20242635) (nat_lit 3467781381) (nat_lit 0) D2M8K2.u9402 from rfl, allE_node, arows9371, irow9403, arows9402]
  all_goals rfl

theorem atot9403 : totK PD2M8K2 D2M8K2.u9403 = [0, 5995226286634, 22423455238799, 23205197384835, 5796628143436, 279948134401, 1209030869, 0] := by
  rw [show D2M8K2.u9403 = KTree.node D2M8K2.u9371 (nat_lit 20242635) (nat_lit 3467781381) (nat_lit 0) D2M8K2.u9402 from rfl, totK_node, atot9371, atot9402]
  decide +kernel

theorem arows9466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9466 = true := by
  rw [show D2M8K2.u9466 = KTree.node D2M8K2.u9434 (nat_lit 20404237) (nat_lit 1391987541) (nat_lit 0) D2M8K2.u9465 from rfl, allE_node, arows9434, irow9466, arows9465]
  all_goals rfl

theorem atot9466 : totK PD2M8K2 D2M8K2.u9466 = [2124144177298, 11071087965022, 21077143760830, 17085634309678, 5169153200777, 464999923847, 6115358396, 0] := by
  rw [show D2M8K2.u9466 = KTree.node D2M8K2.u9434 (nat_lit 20404237) (nat_lit 1391987541) (nat_lit 0) D2M8K2.u9465 from rfl, totK_node, atot9434, atot9465]
  decide +kernel

theorem arows9531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9531 = true := by
  rw [show D2M8K2.u9531 = KTree.node D2M8K2.u9499 (nat_lit 20480744) (nat_lit 3683002312) (nat_lit 0) D2M8K2.u9530 from rfl, allE_node, arows9499, irow9531, arows9530]
  all_goals rfl

theorem atot9531 : totK PD2M8K2 D2M8K2.u9531 = [3515792896946, 15959608579551, 23741471608995, 12680597756218, 1997010255089, 60387529514, 0, 0] := by
  rw [show D2M8K2.u9531 = KTree.node D2M8K2.u9499 (nat_lit 20480744) (nat_lit 3683002312) (nat_lit 0) D2M8K2.u9530 from rfl, totK_node, atot9499, atot9530]
  decide +kernel

theorem arows9594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9594 = true := by
  rw [show D2M8K2.u9594 = KTree.node D2M8K2.u9562 (nat_lit 20561572) (nat_lit 2830660881) (nat_lit 0) D2M8K2.u9593 from rfl, allE_node, arows9562, irow9594, arows9593]
  all_goals rfl

theorem atot9594 : totK PD2M8K2 D2M8K2.u9594 = [4152071220543, 17720722654617, 23863897379031, 10669880950111, 1238891183385, 32229482078, 0, 0] := by
  rw [show D2M8K2.u9594 = KTree.node D2M8K2.u9562 (nat_lit 20561572) (nat_lit 2830660881) (nat_lit 0) D2M8K2.u9593 from rfl, totK_node, atot9562, atot9593]
  decide +kernel

theorem arows9658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9658 = true := by
  rw [show D2M8K2.u9658 = KTree.node D2M8K2.u9626 (nat_lit 20673044) (nat_lit 2929684814) (nat_lit 0) D2M8K2.u9657 from rfl, allE_node, arows9626, irow9658, arows9657]
  all_goals rfl

theorem atot9658 : totK PD2M8K2 D2M8K2.u9658 = [0, 5597154101225, 21477719855337, 23431957704910, 6522846532341, 325927876864, 1369150432, 0] := by
  rw [show D2M8K2.u9658 = KTree.node D2M8K2.u9626 (nat_lit 20673044) (nat_lit 2929684814) (nat_lit 0) D2M8K2.u9657 from rfl, totK_node, atot9626, atot9657]
  decide +kernel

theorem arows9721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9721 = true := by
  rw [show D2M8K2.u9721 = KTree.node D2M8K2.u9689 (nat_lit 20781346) (nat_lit 4158981226) (nat_lit 0) D2M8K2.u9720 from rfl, allE_node, arows9689, irow9721, arows9720]
  all_goals rfl

theorem atot9721 : totK PD2M8K2 D2M8K2.u9721 = [0, 4107800328576, 18213076685516, 24401364339387, 9703546132515, 851474568724, 12665407822, 0] := by
  rw [show D2M8K2.u9721 = KTree.node D2M8K2.u9689 (nat_lit 20781346) (nat_lit 4158981226) (nat_lit 0) D2M8K2.u9720 from rfl, totK_node, atot9689, atot9720]
  decide +kernel

theorem arows9787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9787 = true := by
  rw [show D2M8K2.u9787 = KTree.node D2M8K2.u9755 (nat_lit 20899338) (nat_lit 3898492010) (nat_lit 0) D2M8K2.u9786 from rfl, allE_node, arows9755, irow9787, arows9786]
  all_goals rfl

theorem atot9787 : totK PD2M8K2 D2M8K2.u9787 = [0, 3793596092995, 17075015904660, 24136512593084, 10721283980375, 1286160102724, 34034107435, 0] := by
  rw [show D2M8K2.u9787 = KTree.node D2M8K2.u9755 (nat_lit 20899338) (nat_lit 3898492010) (nat_lit 0) D2M8K2.u9786 from rfl, totK_node, atot9755, atot9786]
  decide +kernel

theorem arows9850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9850 = true := by
  rw [show D2M8K2.u9850 = KTree.node D2M8K2.u9818 (nat_lit 21028153) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u9849 from rfl, allE_node, arows9818, irow9850, arows9849]
  all_goals rfl

theorem atot9850 : totK PD2M8K2 D2M8K2.u9850 = [0, 3683013704399, 17249860507811, 24843695113996, 10536018860439, 1014335378636, 20272400698, 0] := by
  rw [show D2M8K2.u9850 = KTree.node D2M8K2.u9818 (nat_lit 21028153) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u9849 from rfl, totK_node, atot9818, atot9849]
  decide +kernel

theorem arows9914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9914 = true := by
  rw [show D2M8K2.u9914 = KTree.node D2M8K2.u9882 (nat_lit 21104194) (nat_lit 2875146467) (nat_lit 0) D2M8K2.u9913 from rfl, allE_node, arows9882, irow9914, arows9913]
  all_goals rfl

theorem atot9914 : totK PD2M8K2 D2M8K2.u9914 = [0, 3966979634810, 17774017095554, 24642220076759, 10174409051518, 907483620969, 12357048619, 0] := by
  rw [show D2M8K2.u9914 = KTree.node D2M8K2.u9882 (nat_lit 21104194) (nat_lit 2875146467) (nat_lit 0) D2M8K2.u9913 from rfl, totK_node, atot9882, atot9913]
  decide +kernel

theorem arows9977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9977 = true := by
  rw [show D2M8K2.u9977 = KTree.node D2M8K2.u9945 (nat_lit 21186442) (nat_lit 2879695581) (nat_lit 0) D2M8K2.u9976 from rfl, allE_node, arows9945, irow9977, arows9976]
  all_goals rfl

theorem atot9977 : totK PD2M8K2 D2M8K2.u9977 = [0, 0, 6175545977191, 22964157066413, 22777007741925, 4959693301648, 253705368898, 1369150432] := by
  rw [show D2M8K2.u9977 = KTree.node D2M8K2.u9945 (nat_lit 21186442) (nat_lit 2879695581) (nat_lit 0) D2M8K2.u9976 from rfl, totK_node, atot9945, atot9976]
  decide +kernel

theorem arows10042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10042 = true := by
  rw [show D2M8K2.u10042 = KTree.node D2M8K2.u10010 (nat_lit 21376130) (nat_lit 4031739329) (nat_lit 0) D2M8K2.u10041 from rfl, allE_node, arows10010, irow10042, arows10041]
  all_goals rfl

theorem atot10042 : totK PD2M8K2 D2M8K2.u10042 = [0, 2117734323592, 12347630202309, 24053946067534, 16447740532661, 2775160067463, 97247234758, 0] := by
  rw [show D2M8K2.u10042 = KTree.node D2M8K2.u10010 (nat_lit 21376130) (nat_lit 4031739329) (nat_lit 0) D2M8K2.u10041 from rfl, totK_node, atot10010, atot10041]
  decide +kernel

theorem arows10105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10105 = true := by
  rw [show D2M8K2.u10105 = KTree.node D2M8K2.u10073 (nat_lit 21510706) (nat_lit 4121252693) (nat_lit 0) D2M8K2.u10104 from rfl, allE_node, arows10073, irow10105, arows10104]
  all_goals rfl

theorem atot10105 : totK PD2M8K2 D2M8K2.u10105 = [0, 3704789797563, 16529366733838, 24032854815179, 12076705845315, 1520775631884, 25374327145, 0] := by
  rw [show D2M8K2.u10105 = KTree.node D2M8K2.u10073 (nat_lit 21510706) (nat_lit 4121252693) (nat_lit 0) D2M8K2.u10104 from rfl, totK_node, atot10073, atot10104]
  decide +kernel

theorem arows10169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10169 = true := by
  rw [show D2M8K2.u10169 = KTree.node D2M8K2.u10137 (nat_lit 21586765) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u10168 from rfl, allE_node, arows10137, irow10169, arows10168]
  all_goals rfl

theorem atot10169 : totK PD2M8K2 D2M8K2.u10169 = [0, 3986822238167, 17832530087549, 24490154961102, 10330351391470, 1074501710506, 22803183226, 0] := by
  rw [show D2M8K2.u10169 = KTree.node D2M8K2.u10137 (nat_lit 21586765) (nat_lit 1386273304) (nat_lit 0) D2M8K2.u10168 from rfl, totK_node, atot10137, atot10168]
  decide +kernel

theorem arows10232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10232 = true := by
  rw [show D2M8K2.u10232 = KTree.node D2M8K2.u10200 (nat_lit 22412650) (nat_lit 3935621357) (nat_lit 0) D2M8K2.u10231 from rfl, allE_node, arows10200, irow10232, arows10231]
  all_goals rfl

theorem atot10232 : totK PD2M8K2 D2M8K2.u10232 = [0, 3716208164634, 16981617386134, 24458318026154, 11154015979527, 1246828460357, 27130328765, 0] := by
  rw [show D2M8K2.u10232 = KTree.node D2M8K2.u10200 (nat_lit 22412650) (nat_lit 3935621357) (nat_lit 0) D2M8K2.u10231 from rfl, totK_node, atot10200, atot10231]
  decide +kernel

theorem arows10300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10300 = true := by
  rw [show D2M8K2.u10300 = KTree.node D2M8K2.u10268 (nat_lit 22530088) (nat_lit 3495518375) (nat_lit 0) D2M8K2.u10299 from rfl, allE_node, arows10268, irow10300, arows10299]
  all_goals rfl

theorem atot10300 : totK PD2M8K2 D2M8K2.u10300 = [0, 2951129292773, 14594703345131, 23980334103927, 13959667548188, 2175732593694, 64092578358, 0] := by
  rw [show D2M8K2.u10300 = KTree.node D2M8K2.u10268 (nat_lit 22530088) (nat_lit 3495518375) (nat_lit 0) D2M8K2.u10299 from rfl, totK_node, atot10268, atot10299]
  decide +kernel

theorem arows10363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10363 = true := by
  rw [show D2M8K2.u10363 = KTree.node D2M8K2.u10331 (nat_lit 22604911) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u10362 from rfl, allE_node, arows10331, irow10363, arows10362]
  all_goals rfl

theorem atot10363 : totK PD2M8K2 D2M8K2.u10363 = [0, 3534929913752, 16759407209335, 24918519334107, 11360661128598, 1043932710563, 13432705650, 0] := by
  rw [show D2M8K2.u10363 = KTree.node D2M8K2.u10331 (nat_lit 22604911) (nat_lit 2446349698) (nat_lit 0) D2M8K2.u10362 from rfl, totK_node, atot10331, atot10362]
  decide +kernel

theorem arows10427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10427 = true := by
  rw [show D2M8K2.u10427 = KTree.node D2M8K2.u10395 (nat_lit 22689551) (nat_lit 2143130451) (nat_lit 0) D2M8K2.u10426 from rfl, allE_node, arows10395, irow10427, arows10426]
  all_goals rfl

theorem atot10427 : totK PD2M8K2 D2M8K2.u10427 = [0, 0, 5721082912858, 22076558756653, 23304297568400, 5958183525115, 319259836670, 1310517177] := by
  rw [show D2M8K2.u10427 = KTree.node D2M8K2.u10395 (nat_lit 22689551) (nat_lit 2143130451) (nat_lit 0) D2M8K2.u10426 from rfl, totK_node, atot10395, atot10426]
  decide +kernel

theorem arows10490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10490 = true := by
  rw [show D2M8K2.u10490 = KTree.node D2M8K2.u10458 (nat_lit 22821369) (nat_lit 1902210205) (nat_lit 0) D2M8K2.u10489 from rfl, allE_node, arows10458, irow10490, arows10489]
  all_goals rfl

theorem atot10490 : totK PD2M8K2 D2M8K2.u10490 = [0, 0, 4174676457747, 18186372714358, 23886571092262, 9574183060704, 1048274636167, 25006391237] := by
  rw [show D2M8K2.u10490 = KTree.node D2M8K2.u10458 (nat_lit 22821369) (nat_lit 1902210205) (nat_lit 0) D2M8K2.u10489 from rfl, totK_node, atot10458, atot10489]
  decide +kernel

theorem arows10555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10555 = true := by
  rw [show D2M8K2.u10555 = KTree.node D2M8K2.u10523 (nat_lit 22928261) (nat_lit 2301258196) (nat_lit 0) D2M8K2.u10554 from rfl, allE_node, arows10523, irow10555, arows10554]
  all_goals rfl

theorem atot10555 : totK PD2M8K2 D2M8K2.u10555 = [0, 3972055978459, 17585273370930, 24208179738124, 10578151747521, 1310731438167, 34917464754, 0] := by
  rw [show D2M8K2.u10555 = KTree.node D2M8K2.u10523 (nat_lit 22928261) (nat_lit 2301258196) (nat_lit 0) D2M8K2.u10554 from rfl, totK_node, atot10523, atot10554]
  decide +kernel

theorem arows10618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10618 = true := by
  rw [show D2M8K2.u10618 = KTree.node D2M8K2.u10586 (nat_lit 23012139) (nat_lit 3653798956) (nat_lit 0) D2M8K2.u10617 from rfl, allE_node, arows10586, irow10618, arows10617]
  all_goals rfl

theorem atot10618 : totK PD2M8K2 D2M8K2.u10618 = [0, 3688524582665, 16999628885405, 24537457397822, 11150728684805, 1191898768638, 22728260897, 0] := by
  rw [show D2M8K2.u10618 = KTree.node D2M8K2.u10586 (nat_lit 23012139) (nat_lit 3653798956) (nat_lit 0) D2M8K2.u10617 from rfl, totK_node, atot10586, atot10617]
  decide +kernel

theorem arows10682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10682 = true := by
  rw [show D2M8K2.u10682 = KTree.node D2M8K2.u10650 (nat_lit 23086807) (nat_lit 1083621622) (nat_lit 0) D2M8K2.u10681 from rfl, allE_node, arows10650, irow10682, arows10681]
  all_goals rfl

theorem atot10682 : totK PD2M8K2 D2M8K2.u10682 = [0, 2102355608136, 12040274569129, 23427098152072, 16179655689827, 3033832000461, 139489635497, 1209030869] := by
  rw [show D2M8K2.u10682 = KTree.node D2M8K2.u10650 (nat_lit 23086807) (nat_lit 1083621622) (nat_lit 0) D2M8K2.u10681 from rfl, totK_node, atot10650, atot10681]
  decide +kernel

theorem arows10745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10745 = true := by
  rw [show D2M8K2.u10745 = KTree.node D2M8K2.u10713 (nat_lit 23267198) (nat_lit 2936772904) (nat_lit 0) D2M8K2.u10744 from rfl, allE_node, arows10713, irow10745, arows10744]
  all_goals rfl

theorem atot10745 : totK PD2M8K2 D2M8K2.u10745 = [0, 0, 7294071575364, 24721206003627, 21592964629161, 3937635837549, 126250350494, 0] := by
  rw [show D2M8K2.u10745 = KTree.node D2M8K2.u10713 (nat_lit 23267198) (nat_lit 2936772904) (nat_lit 0) D2M8K2.u10744 from rfl, totK_node, atot10713, atot10744]
  decide +kernel

theorem arows10811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10811 = true := by
  rw [show D2M8K2.u10811 = KTree.node D2M8K2.u10779 (nat_lit 23408003) (nat_lit 2746135022) (nat_lit 0) D2M8K2.u10810 from rfl, allE_node, arows10779, irow10811, arows10810]
  all_goals rfl

theorem atot10811 : totK PD2M8K2 D2M8K2.u10811 = [0, 3716633938492, 15444878431022, 21510830793088, 12725434291818, 3562894092214, 330927247857, 6115358396] := by
  rw [show D2M8K2.u10811 = KTree.node D2M8K2.u10779 (nat_lit 23408003) (nat_lit 2746135022) (nat_lit 0) D2M8K2.u10810 from rfl, totK_node, atot10779, atot10810]
  decide +kernel

theorem arows10874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10874 = true := by
  rw [show D2M8K2.u10874 = KTree.node D2M8K2.u10842 (nat_lit 23481254) (nat_lit 4123398383) (nat_lit 0) D2M8K2.u10873 from rfl, allE_node, arows10842, irow10874, arows10873]
  all_goals rfl

theorem atot10874 : totK PD2M8K2 D2M8K2.u10874 = [0, 3372399601836, 15618554629624, 23947532269989, 12992199998670, 1950643986745, 57177753986, 0] := by
  rw [show D2M8K2.u10874 = KTree.node D2M8K2.u10842 (nat_lit 23481254) (nat_lit 4123398383) (nat_lit 0) D2M8K2.u10873 from rfl, totK_node, atot10842, atot10873]
  decide +kernel

theorem arows10938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10938 = true := by
  rw [show D2M8K2.u10938 = KTree.node D2M8K2.u10906 (nat_lit 23605654) (nat_lit 2670541393) (nat_lit 0) D2M8K2.u10937 from rfl, allE_node, arows10906, irow10938, arows10937]
  all_goals rfl

theorem atot10938 : totK PD2M8K2 D2M8K2.u10938 = [442400928062, 3969520682149, 14803309904290, 23409381359415, 13025071572811, 1820367250295, 51938633597, 0] := by
  rw [show D2M8K2.u10938 = KTree.node D2M8K2.u10906 (nat_lit 23605654) (nat_lit 2670541393) (nat_lit 0) D2M8K2.u10937 from rfl, totK_node, atot10906, atot10937]
  decide +kernel

theorem arows11001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11001 = true := by
  rw [show D2M8K2.u11001 = KTree.node D2M8K2.u10969 (nat_lit 23972317) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u11000 from rfl, allE_node, arows10969, irow11001, arows11000]
  all_goals rfl

theorem atot11001 : totK PD2M8K2 D2M8K2.u11001 = [3637283318595, 17127238684752, 24687158555608, 10586931168102, 1064954933212, 20166209240, 0, 0] := by
  rw [show D2M8K2.u11001 = KTree.node D2M8K2.u10969 (nat_lit 23972317) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u11000 from rfl, totK_node, atot10969, atot11000]
  decide +kernel

theorem arows11066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11066 = true := by
  rw [show D2M8K2.u11066 = KTree.node D2M8K2.u11034 (nat_lit 24048073) (nat_lit 1476698829) (nat_lit 0) D2M8K2.u11065 from rfl, allE_node, arows11034, irow11066, arows11065]
  all_goals rfl

theorem atot11066 : totK PD2M8K2 D2M8K2.u11066 = [4013791019826, 17709571741862, 24298640515450, 10389734252351, 1059060989632, 20204178929, 0, 0] := by
  rw [show D2M8K2.u11066 = KTree.node D2M8K2.u11034 (nat_lit 24048073) (nat_lit 1476698829) (nat_lit 0) D2M8K2.u11065 from rfl, totK_node, atot11034, atot11065]
  decide +kernel

theorem arows11129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11129 = true := by
  rw [show D2M8K2.u11129 = KTree.node D2M8K2.u11097 (nat_lit 24129157) (nat_lit 1080539083) (nat_lit 0) D2M8K2.u11128 from rfl, allE_node, arows11097, irow11129, arows11128]
  all_goals rfl

theorem atot11129 : totK PD2M8K2 D2M8K2.u11129 = [1652014843316, 10284289373604, 22184314005993, 18166964036944, 4356871363638, 288319420870, 1369150432, 0] := by
  rw [show D2M8K2.u11129 = KTree.node D2M8K2.u11097 (nat_lit 24129157) (nat_lit 1080539083) (nat_lit 0) D2M8K2.u11128 from rfl, totK_node, atot11097, atot11128]
  decide +kernel

theorem arows11193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11193 = true := by
  rw [show D2M8K2.u11193 = KTree.node D2M8K2.u11161 (nat_lit 24272647) (nat_lit 2358974295) (nat_lit 0) D2M8K2.u11192 from rfl, allE_node, arows11161, irow11193, arows11192]
  all_goals rfl

theorem atot11193 : totK PD2M8K2 D2M8K2.u11193 = [0, 6401790584599, 23297529029218, 22795090773582, 4799774504373, 167465881293, 0, 0] := by
  rw [show D2M8K2.u11193 = KTree.node D2M8K2.u11161 (nat_lit 24272647) (nat_lit 2358974295) (nat_lit 0) D2M8K2.u11192 from rfl, totK_node, atot11161, atot11192]
  decide +kernel

theorem arows11256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11256 = true := by
  rw [show D2M8K2.u11256 = KTree.node D2M8K2.u11224 (nat_lit 24445741) (nat_lit 1184542856) (nat_lit 0) D2M8K2.u11255 from rfl, allE_node, arows11224, irow11256, arows11255]
  all_goals rfl

theorem atot11256 : totK PD2M8K2 D2M8K2.u11256 = [3204512227035, 14346940566814, 22826493044044, 14650951337192, 2744502284676, 91616408752, 0, 0] := by
  rw [show D2M8K2.u11256 = KTree.node D2M8K2.u11224 (nat_lit 24445741) (nat_lit 1184542856) (nat_lit 0) D2M8K2.u11255 from rfl, totK_node, atot11224, atot11255]
  decide +kernel

theorem arows11323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11323 = true := by
  rw [show D2M8K2.u11323 = KTree.node D2M8K2.u11291 (nat_lit 24516072) (nat_lit 3349016598) (nat_lit 0) D2M8K2.u11322 from rfl, allE_node, arows11291, irow11323, arows11322]
  all_goals rfl

theorem atot11323 : totK PD2M8K2 D2M8K2.u11323 = [3329521482443, 16053317482295, 24415717449053, 12169616930001, 1521078121667, 37862993724, 0, 0] := by
  rw [show D2M8K2.u11323 = KTree.node D2M8K2.u11291 (nat_lit 24516072) (nat_lit 3349016598) (nat_lit 0) D2M8K2.u11322 from rfl, totK_node, atot11291, atot11322]
  decide +kernel

theorem arows11386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11386 = true := by
  rw [show D2M8K2.u11386 = KTree.node D2M8K2.u11354 (nat_lit 24597675) (nat_lit 3727771151) (nat_lit 0) D2M8K2.u11385 from rfl, allE_node, arows11354, irow11386, arows11385]
  all_goals rfl

theorem atot11386 : totK PD2M8K2 D2M8K2.u11386 = [3270424723671, 15948906725223, 24679489760263, 12300925539215, 1529927100554, 37677771500, 0, 0] := by
  rw [show D2M8K2.u11386 = KTree.node D2M8K2.u11354 (nat_lit 24597675) (nat_lit 3727771151) (nat_lit 0) D2M8K2.u11385 from rfl, totK_node, atot11354, atot11385]
  decide +kernel

theorem arows11450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11450 = true := by
  rw [show D2M8K2.u11450 = KTree.node D2M8K2.u11418 (nat_lit 24711024) (nat_lit 3460314221) (nat_lit 0) D2M8K2.u11449 from rfl, allE_node, arows11418, irow11450, arows11449]
  all_goals rfl

theorem atot11450 : totK PD2M8K2 D2M8K2.u11450 = [0, 3660991094170, 16634540298474, 23828597196103, 11649385846820, 1696565566761, 57647371591, 0] := by
  rw [show D2M8K2.u11450 = KTree.node D2M8K2.u11418 (nat_lit 24711024) (nat_lit 3460314221) (nat_lit 0) D2M8K2.u11449 from rfl, totK_node, atot11418, atot11449]
  decide +kernel

theorem arows11513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11513 = true := by
  rw [show D2M8K2.u11513 = KTree.node D2M8K2.u11481 (nat_lit 24790782) (nat_lit 3978513910) (nat_lit 0) D2M8K2.u11512 from rfl, allE_node, arows11481, irow11513, arows11512]
  all_goals rfl

theorem atot11513 : totK PD2M8K2 D2M8K2.u11513 = [0, 4031387995699, 17865828926414, 24357736586862, 10227185513629, 973779485398, 13171198502, 0] := by
  rw [show D2M8K2.u11513 = KTree.node D2M8K2.u11481 (nat_lit 24790782) (nat_lit 3978513910) (nat_lit 0) D2M8K2.u11512 from rfl, totK_node, atot11481, atot11512]
  decide +kernel

theorem arows11578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11578 = true := by
  rw [show D2M8K2.u11578 = KTree.node D2M8K2.u11546 (nat_lit 24873303) (nat_lit 3516757189) (nat_lit 0) D2M8K2.u11577 from rfl, allE_node, arows11546, irow11578, arows11577]
  all_goals rfl

theorem atot11578 : totK PD2M8K2 D2M8K2.u11578 = [1975776787817, 9517655324275, 18170943041976, 18336209458896, 8445496087916, 920259842330, 13619666203, 0] := by
  rw [show D2M8K2.u11578 = KTree.node D2M8K2.u11546 (nat_lit 24873303) (nat_lit 3516757189) (nat_lit 0) D2M8K2.u11577 from rfl, totK_node, atot11546, atot11577]
  decide +kernel

theorem arows11641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11641 = true := by
  rw [show D2M8K2.u11641 = KTree.node D2M8K2.u11609 (nat_lit 24952939) (nat_lit 1598885185) (nat_lit 0) D2M8K2.u11640 from rfl, allE_node, arows11609, irow11641, arows11640]
  all_goals rfl

theorem atot11641 : totK PD2M8K2 D2M8K2.u11641 = [4052553629335, 17137469740536, 23407972107469, 11494183755332, 1784010290836, 58018127943, 0, 0] := by
  rw [show D2M8K2.u11641 = KTree.node D2M8K2.u11609 (nat_lit 24952939) (nat_lit 1598885185) (nat_lit 0) D2M8K2.u11640 from rfl, totK_node, atot11609, atot11640]
  decide +kernel

theorem arows11705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11705 = true := by
  rw [show D2M8K2.u11705 = KTree.node D2M8K2.u11673 (nat_lit 25060462) (nat_lit 3306674832) (nat_lit 0) D2M8K2.u11704 from rfl, allE_node, arows11673, irow11705, arows11704]
  all_goals rfl

theorem atot11705 : totK PD2M8K2 D2M8K2.u11705 = [3318543423474, 16240165254200, 24820990172232, 11685970429065, 1267007372842, 24912417204, 0, 0] := by
  rw [show D2M8K2.u11705 = KTree.node D2M8K2.u11673 (nat_lit 25060462) (nat_lit 3306674832) (nat_lit 0) D2M8K2.u11704 from rfl, totK_node, atot11673, atot11704]
  decide +kernel

theorem arows11768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11768 = true := by
  rw [show D2M8K2.u11768 = KTree.node D2M8K2.u11736 (nat_lit 25147807) (nat_lit 2122773314) (nat_lit 0) D2M8K2.u11767 from rfl, allE_node, arows11736, irow11768, arows11767]
  all_goals rfl

theorem atot11768 : totK PD2M8K2 D2M8K2.u11768 = [427983732745, 6921257448880, 21991654037164, 21997325644809, 5662675187805, 295951496705, 1275377855, 0] := by
  rw [show D2M8K2.u11768 = KTree.node D2M8K2.u11736 (nat_lit 25147807) (nat_lit 2122773314) (nat_lit 0) D2M8K2.u11767 from rfl, totK_node, atot11736, atot11767]
  decide +kernel

theorem arows11834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11834 = true := by
  rw [show D2M8K2.u11834 = KTree.node D2M8K2.u11802 (nat_lit 25244456) (nat_lit 3832618542) (nat_lit 0) D2M8K2.u11833 from rfl, allE_node, arows11802, irow11834, arows11833]
  all_goals rfl

theorem atot11834 : totK PD2M8K2 D2M8K2.u11834 = [0, 4427239301204, 18879328559509, 24015669829282, 8870331635401, 871256054440, 19900513739, 0] := by
  rw [show D2M8K2.u11834 = KTree.node D2M8K2.u11802 (nat_lit 25244456) (nat_lit 3832618542) (nat_lit 0) D2M8K2.u11833 from rfl, totK_node, atot11802, atot11833]
  decide +kernel

theorem arows11897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11897 = true := by
  rw [show D2M8K2.u11897 = KTree.node D2M8K2.u11865 (nat_lit 25392679) (nat_lit 2361808614) (nat_lit 0) D2M8K2.u11896 from rfl, allE_node, arows11865, irow11897, arows11896]
  all_goals rfl

theorem atot11897 : totK PD2M8K2 D2M8K2.u11897 = [3073895952514, 14143890801940, 22327550704559, 14036462356709, 3475485608858, 271359069190, 4779662215, 0] := by
  rw [show D2M8K2.u11897 = KTree.node D2M8K2.u11865 (nat_lit 25392679) (nat_lit 2361808614) (nat_lit 0) D2M8K2.u11896 from rfl, totK_node, atot11865, atot11896]
  decide +kernel

theorem arows11961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11961 = true := by
  rw [show D2M8K2.u11961 = KTree.node D2M8K2.u11929 (nat_lit 25506984) (nat_lit 3445181887) (nat_lit 0) D2M8K2.u11960 from rfl, allE_node, arows11929, irow11961, arows11960]
  all_goals rfl

theorem atot11961 : totK PD2M8K2 D2M8K2.u11961 = [3009972273741, 14797244874096, 23812883390212, 13716416752206, 2270901445559, 73416855578, 0, 0] := by
  rw [show D2M8K2.u11961 = KTree.node D2M8K2.u11929 (nat_lit 25506984) (nat_lit 3445181887) (nat_lit 0) D2M8K2.u11960 from rfl, totK_node, atot11929, atot11960]
  decide +kernel

theorem arows12024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12024 = true := by
  rw [show D2M8K2.u12024 = KTree.node D2M8K2.u11992 (nat_lit 25579296) (nat_lit 3667768859) (nat_lit 0) D2M8K2.u12023 from rfl, allE_node, arows11992, irow12024, arows12023]
  all_goals rfl

theorem atot12024 : totK PD2M8K2 D2M8K2.u12024 = [3692294374858, 17057444742601, 24605334753955, 11097664749447, 1115754408702, 16024255900, 0, 0] := by
  rw [show D2M8K2.u12024 = KTree.node D2M8K2.u11992 (nat_lit 25579296) (nat_lit 3667768859) (nat_lit 0) D2M8K2.u12023 from rfl, totK_node, atot11992, atot12023]
  decide +kernel

theorem arows12089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12089 = true := by
  rw [show D2M8K2.u12089 = KTree.node D2M8K2.u12057 (nat_lit 25668824) (nat_lit 3674377383) (nat_lit 0) D2M8K2.u12088 from rfl, allE_node, arows12057, irow12089, arows12088]
  all_goals rfl

theorem atot12089 : totK PD2M8K2 D2M8K2.u12089 = [0, 5400812721629, 21237382249351, 23677302692864, 6656778645903, 346306050476, 1310517177, 0] := by
  rw [show D2M8K2.u12089 = KTree.node D2M8K2.u12057 (nat_lit 25668824) (nat_lit 3674377383) (nat_lit 0) D2M8K2.u12088 from rfl, totK_node, atot12057, atot12088]
  decide +kernel

theorem arows12152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12152 = true := by
  rw [show D2M8K2.u12152 = KTree.node D2M8K2.u12120 (nat_lit 25802236) (nat_lit 3720532539) (nat_lit 0) D2M8K2.u12151 from rfl, allE_node, arows12120, irow12152, arows12151]
  all_goals rfl

theorem atot12152 : totK PD2M8K2 D2M8K2.u12152 = [0, 3656863813253, 17256284456130, 24589377247211, 10284782576748, 1084405190295, 25006391237, 0] := by
  rw [show D2M8K2.u12152 = KTree.node D2M8K2.u12120 (nat_lit 25802236) (nat_lit 3720532539) (nat_lit 0) D2M8K2.u12151 from rfl, totK_node, atot12120, atot12151]
  decide +kernel

theorem arows12216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12216 = true := by
  rw [show D2M8K2.u12216 = KTree.node D2M8K2.u12184 (nat_lit 25906236) (nat_lit 3251093975) (nat_lit 0) D2M8K2.u12215 from rfl, allE_node, arows12184, irow12216, arows12215]
  all_goals rfl

theorem atot12216 : totK PD2M8K2 D2M8K2.u12216 = [4030855496509, 17620265552008, 23909413354725, 10482604474124, 1476573513532, 63539535530, 0, 0] := by
  rw [show D2M8K2.u12216 = KTree.node D2M8K2.u12184 (nat_lit 25906236) (nat_lit 3251093975) (nat_lit 0) D2M8K2.u12215 from rfl, totK_node, atot12184, atot12215]
  decide +kernel

theorem arows12279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12279 = true := by
  rw [show D2M8K2.u12279 = KTree.node D2M8K2.u12247 (nat_lit 25977658) (nat_lit 3748821437) (nat_lit 0) D2M8K2.u12278 from rfl, allE_node, arows12247, irow12279, arows12278]
  all_goals rfl

theorem atot12279 : totK PD2M8K2 D2M8K2.u12279 = [3279742806796, 15193591855271, 23516572697881, 13367946653944, 2141782700264, 55429581829, 0, 0] := by
  rw [show D2M8K2.u12279 = KTree.node D2M8K2.u12247 (nat_lit 25977658) (nat_lit 3748821437) (nat_lit 0) D2M8K2.u12278 from rfl, totK_node, atot12247, atot12278]
  decide +kernel

theorem arows12348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12348 = true := by
  rw [show D2M8K2.u12348 = KTree.node D2M8K2.u12316 (nat_lit 26051691) (nat_lit 3687752868) (nat_lit 0) D2M8K2.u12347 from rfl, allE_node, arows12316, irow12348, arows12347]
  all_goals rfl

theorem atot12348 : totK PD2M8K2 D2M8K2.u12348 = [2880687651292, 15248171186505, 25115400747836, 12753857725766, 1441875294173, 26550443744, 0, 0] := by
  rw [show D2M8K2.u12348 = KTree.node D2M8K2.u12316 (nat_lit 26051691) (nat_lit 3687752868) (nat_lit 0) D2M8K2.u12347 from rfl, totK_node, atot12316, atot12347]
  decide +kernel

theorem arows12411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12411 = true := by
  rw [show D2M8K2.u12411 = KTree.node D2M8K2.u12379 (nat_lit 26179464) (nat_lit 3402052201) (nat_lit 0) D2M8K2.u12410 from rfl, allE_node, arows12379, irow12411, arows12410]
  all_goals rfl

theorem atot12411 : totK PD2M8K2 D2M8K2.u12411 = [0, 5591740965623, 21808656871670, 23601582921777, 6098906580247, 308057556056, 1209030869, 0] := by
  rw [show D2M8K2.u12411 = KTree.node D2M8K2.u12379 (nat_lit 26179464) (nat_lit 3402052201) (nat_lit 0) D2M8K2.u12410 from rfl, totK_node, atot12379, atot12410]
  decide +kernel

theorem arows12475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12475 = true := by
  rw [show D2M8K2.u12475 = KTree.node D2M8K2.u12443 (nat_lit 26305697) (nat_lit 1657967269) (nat_lit 0) D2M8K2.u12474 from rfl, allE_node, arows12443, irow12475, arows12474]
  all_goals rfl

theorem atot12475 : totK PD2M8K2 D2M8K2.u12475 = [0, 5243962880078, 20803952266388, 23697926764334, 7066329800527, 530762931384, 6115358396, 0] := by
  rw [show D2M8K2.u12475 = KTree.node D2M8K2.u12443 (nat_lit 26305697) (nat_lit 1657967269) (nat_lit 0) D2M8K2.u12474 from rfl, totK_node, atot12443, atot12474]
  decide +kernel

theorem arows12538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12538 = true := by
  rw [show D2M8K2.u12538 = KTree.node D2M8K2.u12506 (nat_lit 26971168) (nat_lit 3295303898) (nat_lit 0) D2M8K2.u12537 from rfl, allE_node, arows12506, irow12538, arows12537]
  all_goals rfl

theorem atot12538 : totK PD2M8K2 D2M8K2.u12538 = [0, 3749881372452, 17376820576571, 24729227765195, 10264377677230, 983950141216, 20166209240, 0] := by
  rw [show D2M8K2.u12538 = KTree.node D2M8K2.u12506 (nat_lit 26971168) (nat_lit 3295303898) (nat_lit 0) D2M8K2.u12537 from rfl, totK_node, atot12506, atot12537]
  decide +kernel

theorem arows12603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12603 = true := by
  rw [show D2M8K2.u12603 = KTree.node D2M8K2.u12571 (nat_lit 27046925) (nat_lit 1831930124) (nat_lit 0) D2M8K2.u12602 from rfl, allE_node, arows12571, irow12603, arows12602]
  all_goals rfl

theorem atot12603 : totK PD2M8K2 D2M8K2.u12603 = [0, 3648599134323, 16996939201086, 24590317671670, 10796315951991, 1150771011737, 25181293312, 0] := by
  rw [show D2M8K2.u12603 = KTree.node D2M8K2.u12571 (nat_lit 27046925) (nat_lit 1831930124) (nat_lit 0) D2M8K2.u12602 from rfl, totK_node, atot12571, atot12602]
  decide +kernel

theorem arows12666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12666 = true := by
  rw [show D2M8K2.u12666 = KTree.node D2M8K2.u12634 (nat_lit 27137205) (nat_lit 1736237503) (nat_lit 0) D2M8K2.u12665 from rfl, allE_node, arows12634, irow12666, arows12665]
  all_goals rfl

theorem atot12666 : totK PD2M8K2 D2M8K2.u12666 = [0, 829385582427, 9024675052778, 23683057741612, 19170450637883, 3957688416141, 215597814753, 1369150432] := by
  rw [show D2M8K2.u12666 = KTree.node D2M8K2.u12634 (nat_lit 27137205) (nat_lit 1736237503) (nat_lit 0) D2M8K2.u12665 from rfl, totK_node, atot12634, atot12665]
  decide +kernel

theorem arows12730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12730 = true := by
  rw [show D2M8K2.u12730 = KTree.node D2M8K2.u12698 (nat_lit 27304738) (nat_lit 3361631648) (nat_lit 0) D2M8K2.u12729 from rfl, allE_node, arows12698, irow12730, arows12729]
  all_goals rfl

theorem atot12730 : totK PD2M8K2 D2M8K2.u12730 = [0, 2117743070782, 13001482151656, 24836450448256, 15381237744496, 2123799125175, 54753654997, 0] := by
  rw [show D2M8K2.u12730 = KTree.node D2M8K2.u12698 (nat_lit 27304738) (nat_lit 3361631648) (nat_lit 0) D2M8K2.u12729 from rfl, totK_node, atot12698, atot12729]
  decide +kernel

theorem arows12793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12793 = true := by
  rw [show D2M8K2.u12793 = KTree.node D2M8K2.u12761 (nat_lit 27464686) (nat_lit 4049948875) (nat_lit 0) D2M8K2.u12792 from rfl, allE_node, arows12761, irow12793, arows12792]
  all_goals rfl

theorem atot12793 : totK PD2M8K2 D2M8K2.u12793 = [0, 3185342887648, 15056147667862, 23679986197660, 13521496267519, 2245624063574, 75608720969, 0] := by
  rw [show D2M8K2.u12793 = KTree.node D2M8K2.u12761 (nat_lit 27464686) (nat_lit 4049948875) (nat_lit 0) D2M8K2.u12792 from rfl, totK_node, atot12761, atot12792]
  decide +kernel

theorem arows12859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12859 = true := by
  rw [show D2M8K2.u12859 = KTree.node D2M8K2.u12827 (nat_lit 27544809) (nat_lit 1810823113) (nat_lit 0) D2M8K2.u12858 from rfl, allE_node, arows12827, irow12859, arows12858]
  all_goals rfl

theorem atot12859 : totK PD2M8K2 D2M8K2.u12859 = [0, 3672174176115, 17273937149799, 24902352271092, 10690784226006, 1097981206377, 22803183226, 0] := by
  rw [show D2M8K2.u12859 = KTree.node D2M8K2.u12827 (nat_lit 27544809) (nat_lit 1810823113) (nat_lit 0) D2M8K2.u12858 from rfl, totK_node, atot12827, atot12858]
  decide +kernel

theorem arows12922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12922 = true := by
  rw [show D2M8K2.u12922 = KTree.node D2M8K2.u12890 (nat_lit 27881353) (nat_lit 1516325822) (nat_lit 0) D2M8K2.u12921 from rfl, allE_node, arows12890, irow12922, arows12921]
  all_goals rfl

theorem atot12922 : totK PD2M8K2 D2M8K2.u12922 = [0, 4007503175685, 17758339994988, 24496027689156, 10275924407251, 995824798113, 14545985472, 0] := by
  rw [show D2M8K2.u12922 = KTree.node D2M8K2.u12890 (nat_lit 27881353) (nat_lit 1516325822) (nat_lit 0) D2M8K2.u12921 from rfl, totK_node, atot12890, atot12921]
  decide +kernel

theorem arows12986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12986 = true := by
  rw [show D2M8K2.u12986 = KTree.node D2M8K2.u12954 (nat_lit 27958307) (nat_lit 2939083501) (nat_lit 0) D2M8K2.u12985 from rfl, allE_node, arows12954, irow12986, arows12985]
  all_goals rfl

theorem atot12986 : totK PD2M8K2 D2M8K2.u12986 = [0, 3315315603249, 15804336251668, 24304981391753, 12444622909109, 1651601644468, 40461178779, 0] := by
  rw [show D2M8K2.u12986 = KTree.node D2M8K2.u12954 (nat_lit 27958307) (nat_lit 2939083501) (nat_lit 0) D2M8K2.u12985 from rfl, totK_node, atot12954, atot12985]
  decide +kernel

theorem arows13049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13049 = true := by
  rw [show D2M8K2.u13049 = KTree.node D2M8K2.u13017 (nat_lit 28077533) (nat_lit 1733081943) (nat_lit 0) D2M8K2.u13048 from rfl, allE_node, arows13017, irow13049, arows13048]
  all_goals rfl

theorem atot13049 : totK PD2M8K2 D2M8K2.u13049 = [0, 3938501712562, 17694473342659, 24598745713221, 10340320980702, 948427234104, 12305484365, 0] := by
  rw [show D2M8K2.u13049 = KTree.node D2M8K2.u13017 (nat_lit 28077533) (nat_lit 1733081943) (nat_lit 0) D2M8K2.u13048 from rfl, totK_node, atot13017, atot13048]
  decide +kernel

theorem arows13114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13114 = true := by
  rw [show D2M8K2.u13114 = KTree.node D2M8K2.u13082 (nat_lit 28416558) (nat_lit 3595781564) (nat_lit 0) D2M8K2.u13113 from rfl, allE_node, arows13082, irow13114, arows13113]
  all_goals rfl

theorem atot13114 : totK PD2M8K2 D2M8K2.u13114 = [0, 3732899228180, 17143247222552, 24564983305111, 10978670025075, 1226518260800, 23180880252, 0] := by
  rw [show D2M8K2.u13114 = KTree.node D2M8K2.u13082 (nat_lit 28416558) (nat_lit 3595781564) (nat_lit 0) D2M8K2.u13113 from rfl, totK_node, atot13082, atot13113]
  decide +kernel

theorem arows13177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13177 = true := by
  rw [show D2M8K2.u13177 = KTree.node D2M8K2.u13145 (nat_lit 28528806) (nat_lit 3809073837) (nat_lit 0) D2M8K2.u13176 from rfl, allE_node, arows13145, irow13177, arows13176]
  all_goals rfl

theorem atot13177 : totK PD2M8K2 D2M8K2.u13177 = [0, 3728068084664, 17305254474813, 24739490791290, 10612985779639, 1038905478760, 20204178929, 0] := by
  rw [show D2M8K2.u13177 = KTree.node D2M8K2.u13145 (nat_lit 28528806) (nat_lit 3809073837) (nat_lit 0) D2M8K2.u13176 from rfl, totK_node, atot13145, atot13176]
  decide +kernel

theorem arows13241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13241 = true := by
  rw [show D2M8K2.u13241 = KTree.node D2M8K2.u13209 (nat_lit 28613788) (nat_lit 3920975462) (nat_lit 0) D2M8K2.u13240 from rfl, allE_node, arows13209, irow13241, arows13240]
  all_goals rfl

theorem atot13241 : totK PD2M8K2 D2M8K2.u13241 = [0, 3789492573472, 17365549798004, 24694946626133, 10440548287616, 947629899287, 12587955038, 0] := by
  rw [show D2M8K2.u13241 = KTree.node D2M8K2.u13209 (nat_lit 28613788) (nat_lit 3920975462) (nat_lit 0) D2M8K2.u13240 from rfl, totK_node, atot13209, atot13240]
  decide +kernel

theorem arows13304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13304 = true := by
  rw [show D2M8K2.u13304 = KTree.node D2M8K2.u13272 (nat_lit 28940884) (nat_lit 4008381168) (nat_lit 0) D2M8K2.u13303 from rfl, allE_node, arows13272, irow13304, arows13303]
  all_goals rfl

theorem atot13304 : totK PD2M8K2 D2M8K2.u13304 = [0, 3914876902100, 17221544053035, 24012083949966, 11171368116383, 1400023523870, 36727429765, 0] := by
  rw [show D2M8K2.u13304 = KTree.node D2M8K2.u13272 (nat_lit 28940884) (nat_lit 4008381168) (nat_lit 0) D2M8K2.u13303 from rfl, totK_node, atot13272, atot13303]
  decide +kernel

theorem arows13371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13371 = true := by
  rw [show D2M8K2.u13371 = KTree.node D2M8K2.u13339 (nat_lit 29013905) (nat_lit 1779401491) (nat_lit 0) D2M8K2.u13370 from rfl, allE_node, arows13339, irow13371, arows13370]
  all_goals rfl

theorem atot13371 : totK PD2M8K2 D2M8K2.u13371 = [0, 4145233399486, 17691040242631, 23813585039032, 10448023521036, 1216954018474, 36656527942, 0] := by
  rw [show D2M8K2.u13371 = KTree.node D2M8K2.u13339 (nat_lit 29013905) (nat_lit 1779401491) (nat_lit 0) D2M8K2.u13370 from rfl, totK_node, atot13339, atot13370]
  decide +kernel

theorem arows13434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13434 = true := by
  rw [show D2M8K2.u13434 = KTree.node D2M8K2.u13402 (nat_lit 29134142) (nat_lit 2681731166) (nat_lit 0) D2M8K2.u13433 from rfl, allE_node, arows13402, irow13434, arows13433]
  all_goals rfl

theorem atot13434 : totK PD2M8K2 D2M8K2.u13434 = [0, 0, 6694417694393, 23762457311588, 21623855260244, 4679820045431, 249169558041, 1209030869] := by
  rw [show D2M8K2.u13434 = KTree.node D2M8K2.u13402 (nat_lit 29134142) (nat_lit 2681731166) (nat_lit 0) D2M8K2.u13433 from rfl, totK_node, atot13402, atot13433]
  decide +kernel

theorem arows13498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13498 = true := by
  rw [show D2M8K2.u13498 = KTree.node D2M8K2.u13466 (nat_lit 29281030) (nat_lit 3199819959) (nat_lit 0) D2M8K2.u13497 from rfl, allE_node, arows13466, irow13498, arows13497]
  all_goals rfl

theorem atot13498 : totK PD2M8K2 D2M8K2.u13498 = [186677387228, 459373490871, 5665968017258, 20936061639661, 22594822306359, 6693547324723, 529618835960, 6115358396] := by
  rw [show D2M8K2.u13498 = KTree.node D2M8K2.u13466 (nat_lit 29281030) (nat_lit 3199819959) (nat_lit 0) D2M8K2.u13497 from rfl, totK_node, atot13466, atot13497]
  decide +kernel

theorem arows13561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13561 = true := by
  rw [show D2M8K2.u13561 = KTree.node D2M8K2.u13529 (nat_lit 29899526) (nat_lit 2525692104) (nat_lit 0) D2M8K2.u13560 from rfl, allE_node, arows13529, irow13561, arows13560]
  all_goals rfl

theorem atot13561 : totK PD2M8K2 D2M8K2.u13561 = [3894060341943, 17674529976880, 24535043955745, 10122539178583, 965081801920, 16613414226, 0, 0] := by
  rw [show D2M8K2.u13561 = KTree.node D2M8K2.u13529 (nat_lit 29899526) (nat_lit 2525692104) (nat_lit 0) D2M8K2.u13560 from rfl, totK_node, atot13529, atot13560]
  decide +kernel

theorem arows13626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13626 = true := by
  rw [show D2M8K2.u13626 = KTree.node D2M8K2.u13594 (nat_lit 30018541) (nat_lit 1285768494) (nat_lit 0) D2M8K2.u13625 from rfl, allE_node, arows13594, irow13626, arows13625]
  all_goals rfl

theorem atot13626 : totK PD2M8K2 D2M8K2.u13626 = [3628821022536, 16909902555889, 24475757546169, 11065844053753, 1182159357922, 24852081659, 0, 0] := by
  rw [show D2M8K2.u13626 = KTree.node D2M8K2.u13594 (nat_lit 30018541) (nat_lit 1285768494) (nat_lit 0) D2M8K2.u13625 from rfl, totK_node, atot13594, atot13625]
  decide +kernel

theorem arows13689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13689 = true := by
  rw [show D2M8K2.u13689 = KTree.node D2M8K2.u13657 (nat_lit 30099251) (nat_lit 2864044449) (nat_lit 0) D2M8K2.u13688 from rfl, allE_node, arows13657, irow13689, arows13688]
  all_goals rfl

theorem atot13689 : totK PD2M8K2 D2M8K2.u13689 = [2038998152306, 11379935282902, 22472644299446, 17245825304934, 3920605834630, 257819687532, 1369150432, 0] := by
  rw [show D2M8K2.u13689 = KTree.node D2M8K2.u13657 (nat_lit 30099251) (nat_lit 2864044449) (nat_lit 0) D2M8K2.u13688 from rfl, totK_node, atot13657, atot13688]
  decide +kernel

theorem arows13753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13753 = true := by
  rw [show D2M8K2.u13753 = KTree.node D2M8K2.u13721 (nat_lit 30239244) (nat_lit 2795253460) (nat_lit 0) D2M8K2.u13752 from rfl, allE_node, arows13721, irow13753, arows13752]
  all_goals rfl

theorem atot13753 : totK PD2M8K2 D2M8K2.u13753 = [0, 6021466085083, 22716986611639, 23219863776141, 5165622757479, 196830096534, 0, 0] := by
  rw [show D2M8K2.u13753 = KTree.node D2M8K2.u13721 (nat_lit 30239244) (nat_lit 2795253460) (nat_lit 0) D2M8K2.u13752 from rfl, totK_node, atot13721, atot13752]
  decide +kernel

theorem arows13816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13816 = true := by
  rw [show D2M8K2.u13816 = KTree.node D2M8K2.u13784 (nat_lit 30415226) (nat_lit 3922790558) (nat_lit 0) D2M8K2.u13815 from rfl, allE_node, arows13784, irow13816, arows13815]
  all_goals rfl

theorem atot13816 : totK PD2M8K2 D2M8K2.u13816 = [2872115542185, 13782320921608, 23043150377283, 15254194135872, 2956735409848, 99822885943, 0, 0] := by
  rw [show D2M8K2.u13816 = KTree.node D2M8K2.u13784 (nat_lit 30415226) (nat_lit 3922790558) (nat_lit 0) D2M8K2.u13815 from rfl, totK_node, atot13784, atot13815]
  decide +kernel

theorem arows13882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13882 = true := by
  rw [show D2M8K2.u13882 = KTree.node D2M8K2.u13850 (nat_lit 30486127) (nat_lit 1707170592) (nat_lit 0) D2M8K2.u13881 from rfl, allE_node, arows13850, irow13882, arows13881]
  all_goals rfl

theorem atot13882 : totK PD2M8K2 D2M8K2.u13882 = [3392278902690, 15982502552372, 24443777265882, 12250466855194, 1518770159725, 37862993724, 0, 0] := by
  rw [show D2M8K2.u13882 = KTree.node D2M8K2.u13850 (nat_lit 30486127) (nat_lit 1707170592) (nat_lit 0) D2M8K2.u13881 from rfl, totK_node, atot13850, atot13881]
  decide +kernel

theorem arows13945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13945 = true := by
  rw [show D2M8K2.u13945 = KTree.node D2M8K2.u13913 (nat_lit 30570406) (nat_lit 3752079633) (nat_lit 0) D2M8K2.u13944 from rfl, allE_node, arows13913, irow13945, arows13944]
  all_goals rfl

theorem atot13945 : totK PD2M8K2 D2M8K2.u13945 = [3546318875039, 16556747760997, 24477717450152, 11835282067181, 1385571836122, 24523072254, 0, 0] := by
  rw [show D2M8K2.u13945 = KTree.node D2M8K2.u13913 (nat_lit 30570406) (nat_lit 3752079633) (nat_lit 0) D2M8K2.u13944 from rfl, totK_node, atot13913, atot13944]
  decide +kernel

theorem arows14009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14009 = true := by
  rw [show D2M8K2.u14009 = KTree.node D2M8K2.u13977 (nat_lit 30680425) (nat_lit 1457619928) (nat_lit 0) D2M8K2.u14008 from rfl, allE_node, arows13977, irow14009, arows14008]
  all_goals rfl

theorem atot14009 : totK PD2M8K2 D2M8K2.u14009 = [0, 4111265536048, 17303275039787, 23288183804580, 11177717579905, 1672320907097, 57647371591, 0] := by
  rw [show D2M8K2.u14009 = KTree.node D2M8K2.u13977 (nat_lit 30680425) (nat_lit 1457619928) (nat_lit 0) D2M8K2.u14008 from rfl, totK_node, atot13977, atot14008]
  decide +kernel

theorem arows14072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14072 = true := by
  rw [show D2M8K2.u14072 = KTree.node D2M8K2.u14040 (nat_lit 30755625) (nat_lit 1835786192) (nat_lit 0) D2M8K2.u14071 from rfl, allE_node, arows14040, irow14072, arows14071]
  all_goals rfl

theorem atot14072 : totK PD2M8K2 D2M8K2.u14072 = [0, 3652328297208, 17181872043631, 24724023343017, 10917650748982, 1037321044862, 13171198502, 0] := by
  rw [show D2M8K2.u14072 = KTree.node D2M8K2.u14040 (nat_lit 30755625) (nat_lit 1835786192) (nat_lit 0) D2M8K2.u14071 from rfl, totK_node, atot14040, atot14071]
  decide +kernel

theorem arows14137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14137 = true := by
  rw [show D2M8K2.u14137 = KTree.node D2M8K2.u14105 (nat_lit 30843049) (nat_lit 1444519865) (nat_lit 0) D2M8K2.u14136 from rfl, allE_node, arows14105, irow14137, arows14136]
  all_goals rfl

theorem atot14137 : totK PD2M8K2 D2M8K2.u14137 = [1976552160701, 9569460292342, 18448711897374, 18429882462322, 8149661177812, 892705342970, 13619666203, 0] := by
  rw [show D2M8K2.u14137 = KTree.node D2M8K2.u14105 (nat_lit 30843049) (nat_lit 1444519865) (nat_lit 0) D2M8K2.u14136 from rfl, totK_node, atot14105, atot14136]
  decide +kernel

theorem arows14200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14200 = true := by
  rw [show D2M8K2.u14200 = KTree.node D2M8K2.u14168 (nat_lit 30923661) (nat_lit 1048056229) (nat_lit 0) D2M8K2.u14199 from rfl, allE_node, arows14168, irow14200, arows14199]
  all_goals rfl

theorem atot14200 : totK PD2M8K2 D2M8K2.u14200 = [3691130278286, 16565893593658, 23863052791315, 11916240239241, 1805227034215, 58018127943, 0, 0] := by
  rw [show D2M8K2.u14200 = KTree.node D2M8K2.u14168 (nat_lit 30923661) (nat_lit 1048056229) (nat_lit 0) D2M8K2.u14199 from rfl, totK_node, atot14168, atot14199]
  decide +kernel

theorem arows14264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14264 = true := by
  rw [show D2M8K2.u14264 = KTree.node D2M8K2.u14232 (nat_lit 31030886) (nat_lit 4109748624) (nat_lit 0) D2M8K2.u14263 from rfl, allE_node, arows14232, irow14264, arows14263]
  all_goals rfl

theorem atot14264 : totK PD2M8K2 D2M8K2.u14264 = [3682727066157, 16824665911290, 24386637151245, 11261874221156, 1245506818040, 24912417204, 0, 0] := by
  rw [show D2M8K2.u14264 = KTree.node D2M8K2.u14232 (nat_lit 31030886) (nat_lit 4109748624) (nat_lit 0) D2M8K2.u14263 from rfl, totK_node, atot14232, atot14263]
  decide +kernel

theorem arows14327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14327 = true := by
  rw [show D2M8K2.u14327 = KTree.node D2M8K2.u14295 (nat_lit 31116362) (nat_lit 2786397147) (nat_lit 0) D2M8K2.u14326 from rfl, allE_node, arows14295, irow14327, arows14326]
  all_goals rfl

theorem atot14327 : totK PD2M8K2 D2M8K2.u14327 = [424455604040, 6910961739864, 21997338281950, 22089104306201, 5692804790213, 297002185204, 1275377855, 0] := by
  rw [show D2M8K2.u14327 = KTree.node D2M8K2.u14295 (nat_lit 31116362) (nat_lit 2786397147) (nat_lit 0) D2M8K2.u14326 from rfl, totK_node, atot14295, atot14326]
  decide +kernel

theorem arows14395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14395 = true := by
  rw [show D2M8K2.u14395 = KTree.node D2M8K2.u14363 (nat_lit 31212321) (nat_lit 1854144789) (nat_lit 0) D2M8K2.u14394 from rfl, allE_node, arows14363, irow14395, arows14394]
  all_goals rfl

theorem atot14395 : totK PD2M8K2 D2M8K2.u14395 = [0, 4410589632680, 18839679599309, 24023826580165, 8916630000110, 878705152403, 19900513739, 0] := by
  rw [show D2M8K2.u14395 = KTree.node D2M8K2.u14363 (nat_lit 31212321) (nat_lit 1854144789) (nat_lit 0) D2M8K2.u14394 from rfl, totK_node, atot14363, atot14394]
  decide +kernel

theorem arows14458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14458 = true := by
  rw [show D2M8K2.u14458 = KTree.node D2M8K2.u14426 (nat_lit 31362958) (nat_lit 3954473252) (nat_lit 0) D2M8K2.u14457 from rfl, allE_node, arows14426, irow14458, arows14457]
  all_goals rfl

theorem atot14458 : totK PD2M8K2 D2M8K2.u14458 = [2751054189156, 13695380101885, 22754627204613, 14514134023945, 3475197663918, 263316139548, 4779662215, 0] := by
  rw [show D2M8K2.u14458 = KTree.node D2M8K2.u14426 (nat_lit 31362958) (nat_lit 3954473252) (nat_lit 0) D2M8K2.u14457 from rfl, totK_node, atot14426, atot14457]
  decide +kernel

theorem arows14522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14522 = true := by
  rw [show D2M8K2.u14522 = KTree.node D2M8K2.u14490 (nat_lit 31477360) (nat_lit 3275640970) (nat_lit 0) D2M8K2.u14521 from rfl, allE_node, arows14490, irow14522, arows14521]
  all_goals rfl

theorem atot14522 : totK PD2M8K2 D2M8K2.u14522 = [3334283808982, 15453603685380, 23607239643337, 13103950382707, 2182000670445, 72363444413, 0, 0] := by
  rw [show D2M8K2.u14522 = KTree.node D2M8K2.u14490 (nat_lit 31477360) (nat_lit 3275640970) (nat_lit 0) D2M8K2.u14521 from rfl, totK_node, atot14490, atot14521]
  decide +kernel

theorem arows14585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14585 = true := by
  rw [show D2M8K2.u14585 = KTree.node D2M8K2.u14553 (nat_lit 31555915) (nat_lit 1666062191) (nat_lit 0) D2M8K2.u14584 from rfl, allE_node, arows14553, irow14585, arows14584]
  all_goals rfl

theorem atot14585 : totK PD2M8K2 D2M8K2.u14585 = [3694509517985, 16941933015072, 24490742012934, 11326922655592, 1180475205288, 17026102811, 0, 0] := by
  rw [show D2M8K2.u14585 = KTree.node D2M8K2.u14553 (nat_lit 31555915) (nat_lit 1666062191) (nat_lit 0) D2M8K2.u14584 from rfl, totK_node, atot14553, atot14584]
  decide +kernel

theorem arows14650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14650 = true := by
  rw [show D2M8K2.u14650 = KTree.node D2M8K2.u14618 (nat_lit 31634478) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u14649 from rfl, allE_node, arows14618, irow14650, arows14649]
  all_goals rfl

theorem atot14650 : totK PD2M8K2 D2M8K2.u14650 = [0, 5282756639973, 21162486376900, 23866460542698, 6680324521971, 344891527105, 1310517177, 0] := by
  rw [show D2M8K2.u14650 = KTree.node D2M8K2.u14618 (nat_lit 31634478) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u14649 from rfl, totK_node, atot14618, atot14649]
  decide +kernel

theorem arows14713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14713 = true := by
  rw [show D2M8K2.u14713 = KTree.node D2M8K2.u14681 (nat_lit 31771692) (nat_lit 2586701677) (nat_lit 0) D2M8K2.u14712 from rfl, allE_node, arows14681, irow14713, arows14712]
  all_goals rfl

theorem atot14713 : totK PD2M8K2 D2M8K2.u14713 = [0, 4003490851601, 17656323892073, 24114287139683, 10110091361245, 1083301416342, 25006391237, 0] := by
  rw [show D2M8K2.u14713 = KTree.node D2M8K2.u14681 (nat_lit 31771692) (nat_lit 2586701677) (nat_lit 0) D2M8K2.u14712 from rfl, totK_node, atot14681, atot14712]
  decide +kernel

theorem arows14777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14777 = true := by
  rw [show D2M8K2.u14777 = KTree.node D2M8K2.u14745 (nat_lit 32370364) (nat_lit 3703251296) (nat_lit 0) D2M8K2.u14776 from rfl, allE_node, arows14745, irow14777, arows14776]
  all_goals rfl

theorem atot14777 : totK PD2M8K2 D2M8K2.u14777 = [4038872482053, 17583873052650, 23877648244929, 10711140917203, 1433193800824, 41707772248, 0, 0] := by
  rw [show D2M8K2.u14777 = KTree.node D2M8K2.u14745 (nat_lit 32370364) (nat_lit 3703251296) (nat_lit 0) D2M8K2.u14776 from rfl, totK_node, atot14745, atot14776]
  decide +kernel

theorem arows14840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14840 = true := by
  rw [show D2M8K2.u14840 = KTree.node D2M8K2.u14808 (nat_lit 32445658) (nat_lit 3481778363) (nat_lit 0) D2M8K2.u14839 from rfl, allE_node, arows14808, irow14840, arows14839]
  all_goals rfl

theorem atot14840 : totK PD2M8K2 D2M8K2.u14840 = [3284196378284, 14940204035673, 23356206406681, 13709562390942, 2325647864505, 76815186751, 0, 0] := by
  rw [show D2M8K2.u14840 = KTree.node D2M8K2.u14808 (nat_lit 32445658) (nat_lit 3481778363) (nat_lit 0) D2M8K2.u14839 from rfl, totK_node, atot14808, atot14839]
  decide +kernel

theorem arows14906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14906 = true := by
  rw [show D2M8K2.u14906 = KTree.node D2M8K2.u14874 (nat_lit 32561540) (nat_lit 2996813858) (nat_lit 0) D2M8K2.u14905 from rfl, allE_node, arows14874, irow14906, arows14905]
  all_goals rfl

theorem atot14906 : totK PD2M8K2 D2M8K2.u14906 = [2889725044371, 14931657707726, 24633995337790, 13381221856000, 1740819798069, 38611892787, 0, 0] := by
  rw [show D2M8K2.u14906 = KTree.node D2M8K2.u14874 (nat_lit 32561540) (nat_lit 2996813858) (nat_lit 0) D2M8K2.u14905 from rfl, totK_node, atot14874, atot14905]
  decide +kernel

theorem arows14969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14969 = true := by
  rw [show D2M8K2.u14969 = KTree.node D2M8K2.u14937 (nat_lit 32642765) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u14968 from rfl, allE_node, arows14937, irow14969, arows14968]
  all_goals rfl

theorem atot14969 : totK PD2M8K2 D2M8K2.u14969 = [0, 5381816526749, 20958744987565, 23710706180417, 6980592357339, 368205264744, 1369150432, 0] := by
  rw [show D2M8K2.u14969 = KTree.node D2M8K2.u14937 (nat_lit 32642765) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u14968 from rfl, totK_node, atot14937, atot14968]
  decide +kernel

theorem arows15033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15033 = true := by
  rw [show D2M8K2.u15033 = KTree.node D2M8K2.u15001 (nat_lit 32734954) (nat_lit 3976387553) (nat_lit 0) D2M8K2.u15032 from rfl, allE_node, arows15001, irow15033, arows15032]
  all_goals rfl

theorem atot15033 : totK PD2M8K2 D2M8K2.u15033 = [0, 3954328791540, 18043683562309, 24615317500785, 9745403151966, 842303815385, 12665407822, 0] := by
  rw [show D2M8K2.u15033 = KTree.node D2M8K2.u15001 (nat_lit 32734954) (nat_lit 3976387553) (nat_lit 0) D2M8K2.u15032 from rfl, totK_node, atot15001, atot15032]
  decide +kernel

theorem arows15096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15096 = true := by
  rw [show D2M8K2.u15096 = KTree.node D2M8K2.u15064 (nat_lit 32853978) (nat_lit 3689837351) (nat_lit 0) D2M8K2.u15095 from rfl, allE_node, arows15064, irow15096, arows15095]
  all_goals rfl

theorem atot15096 : totK PD2M8K2 D2M8K2.u15096 = [0, 3548665181440, 16672775841268, 24472902156805, 11009213486345, 1298867851318, 34034107435, 0] := by
  rw [show D2M8K2.u15096 = KTree.node D2M8K2.u15064 (nat_lit 32853978) (nat_lit 3689837351) (nat_lit 0) D2M8K2.u15095 from rfl, totK_node, atot15064, atot15095]
  decide +kernel

theorem arows15161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15161 = true := by
  rw [show D2M8K2.u15161 = KTree.node D2M8K2.u15129 (nat_lit 32973409) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u15160 from rfl, allE_node, arows15129, irow15161, arows15160]
  all_goals rfl

theorem atot15161 : totK PD2M8K2 D2M8K2.u15161 = [0, 3802402046468, 17327963300183, 24655871723415, 10744919040986, 1015809200236, 13267291839, 0] := by
  rw [show D2M8K2.u15161 = KTree.node D2M8K2.u15129 (nat_lit 32973409) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u15160 from rfl, totK_node, atot15129, atot15160]
  decide +kernel

theorem arows15224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15224 = true := by
  rw [show D2M8K2.u15224 = KTree.node D2M8K2.u15192 (nat_lit 33060941) (nat_lit 2003906387) (nat_lit 0) D2M8K2.u15223 from rfl, allE_node, arows15192, irow15224, arows15223]
  all_goals rfl

theorem atot15224 : totK PD2M8K2 D2M8K2.u15224 = [0, 3263071796589, 16093644228469, 24849472015217, 11870024831942, 1403459069011, 35380093126, 0] := by
  rw [show D2M8K2.u15224 = KTree.node D2M8K2.u15192 (nat_lit 33060941) (nat_lit 2003906387) (nat_lit 0) D2M8K2.u15223 from rfl, totK_node, atot15192, atot15223]
  decide +kernel

theorem arows15288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15288 = true := by
  rw [show D2M8K2.u15288 = KTree.node D2M8K2.u15256 (nat_lit 33181900) (nat_lit 3917049186) (nat_lit 0) D2M8K2.u15287 from rfl, allE_node, arows15256, irow15288, arows15287]
  all_goals rfl

theorem atot15288 : totK PD2M8K2 D2M8K2.u15288 = [0, 0, 5783803674891, 22461315737087, 23577795021402, 5293518772122, 267377372871, 1369150432] := by
  rw [show D2M8K2.u15288 = KTree.node D2M8K2.u15256 (nat_lit 33181900) (nat_lit 3917049186) (nat_lit 0) D2M8K2.u15287 from rfl, totK_node, atot15256, atot15287]
  decide +kernel

theorem arows15351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15351 = true := by
  rw [show D2M8K2.u15351 = KTree.node D2M8K2.u15319 (nat_lit 33321992) (nat_lit 2666061491) (nat_lit 0) D2M8K2.u15350 from rfl, allE_node, arows15319, irow15351, arows15350]
  all_goals rfl

theorem atot15351 : totK PD2M8K2 D2M8K2.u15351 = [0, 2117768858604, 12159518114535, 23915392134634, 16892126262519, 2789486513106, 90083699469, 0] := by
  rw [show D2M8K2.u15351 = KTree.node D2M8K2.u15319 (nat_lit 33321992) (nat_lit 2666061491) (nat_lit 0) D2M8K2.u15350 from rfl, totK_node, atot15319, atot15350]
  decide +kernel

theorem arows15418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15418 = true := by
  rw [show D2M8K2.u15418 = KTree.node D2M8K2.u15386 (nat_lit 33449484) (nat_lit 3460743785) (nat_lit 0) D2M8K2.u15417 from rfl, allE_node, arows15386, irow15418, arows15417]
  all_goals rfl

theorem atot15418 : totK PD2M8K2 D2M8K2.u15418 = [0, 3987540444387, 17169019719540, 23798601093509, 11446261483785, 1448550673840, 27940662119, 0] := by
  rw [show D2M8K2.u15418 = KTree.node D2M8K2.u15386 (nat_lit 33449484) (nat_lit 3460743785) (nat_lit 0) D2M8K2.u15417 from rfl, totK_node, atot15386, atot15417]
  decide +kernel

theorem arows15481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15481 = true := by
  rw [show D2M8K2.u15481 = KTree.node D2M8K2.u15449 (nat_lit 33534203) (nat_lit 2779017970) (nat_lit 0) D2M8K2.u15480 from rfl, allE_node, arows15449, irow15481, arows15480]
  all_goals rfl

theorem atot15481 : totK PD2M8K2 D2M8K2.u15481 = [0, 3705404016923, 17176339226177, 24845473502105, 11100450819021, 1078470067984, 13636393178, 0] := by
  rw [show D2M8K2.u15481 = KTree.node D2M8K2.u15449 (nat_lit 33534203) (nat_lit 2779017970) (nat_lit 0) D2M8K2.u15480 from rfl, totK_node, atot15449, atot15480]
  decide +kernel

theorem arows15545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15545 = true := by
  rw [show D2M8K2.u15545 = KTree.node D2M8K2.u15513 (nat_lit 33860016) (nat_lit 3691976763) (nat_lit 0) D2M8K2.u15544 from rfl, allE_node, arows15513, irow15545, arows15544]
  all_goals rfl

theorem atot15545 : totK PD2M8K2 D2M8K2.u15545 = [0, 3977646434741, 17354553447290, 24001494636129, 10944891067866, 1328307041355, 34241849113, 0] := by
  rw [show D2M8K2.u15545 = KTree.node D2M8K2.u15513 (nat_lit 33860016) (nat_lit 3691976763) (nat_lit 0) D2M8K2.u15544 from rfl, totK_node, atot15513, atot15544]
  decide +kernel

theorem arows15608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15608 = true := by
  rw [show D2M8K2.u15608 = KTree.node D2M8K2.u15576 (nat_lit 33932845) (nat_lit 1121320289) (nat_lit 0) D2M8K2.u15607 from rfl, allE_node, arows15576, irow15608, arows15607]
  all_goals rfl

theorem atot15608 : totK PD2M8K2 D2M8K2.u15608 = [0, 2909237300753, 14570383539099, 23974881873531, 13871771397970, 2224160429522, 69247358039, 0] := by
  rw [show D2M8K2.u15608 = KTree.node D2M8K2.u15576 (nat_lit 33932845) (nat_lit 1121320289) (nat_lit 0) D2M8K2.u15607 from rfl, totK_node, atot15576, atot15607]
  decide +kernel

theorem arows15673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15673 = true := by
  rw [show D2M8K2.u15673 = KTree.node D2M8K2.u15641 (nat_lit 34057550) (nat_lit 3843686999) (nat_lit 0) D2M8K2.u15672 from rfl, allE_node, arows15641, irow15673, arows15672]
  all_goals rfl

theorem atot15673 : totK PD2M8K2 D2M8K2.u15673 = [0, 2891661737698, 15039132199316, 24860403225024, 13136019020813, 1629030384028, 40357207509, 0] := by
  rw [show D2M8K2.u15673 = KTree.node D2M8K2.u15641 (nat_lit 34057550) (nat_lit 3843686999) (nat_lit 0) D2M8K2.u15672 from rfl, totK_node, atot15641, atot15672]
  decide +kernel

theorem arows15736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15736 = true := by
  rw [show D2M8K2.u15736 = KTree.node D2M8K2.u15704 (nat_lit 34145661) (nat_lit 1334440894) (nat_lit 2) D2M8K2.u15735 from rfl, allE_node, arows15704, irow15736, arows15735]
  all_goals rfl

theorem atot15736 : totK PD2M8K2 D2M8K2.u15736 = [0, 0, 5286073706164, 21242000889618, 23949700563064, 6641947138886, 362911528280, 2481843637] := by
  rw [show D2M8K2.u15736 = KTree.node D2M8K2.u15704 (nat_lit 34145661) (nat_lit 1334440894) (nat_lit 2) D2M8K2.u15735 from rfl, totK_node, atot15704, atot15735]
  decide +kernel

theorem arows15800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15800 = true := by
  rw [show D2M8K2.u15800 = KTree.node D2M8K2.u15768 (nat_lit 34310305) (nat_lit 1549666246) (nat_lit 0) D2M8K2.u15799 from rfl, allE_node, arows15768, irow15800, arows15799]
  all_goals rfl

theorem atot15800 : totK PD2M8K2 D2M8K2.u15800 = [0, 1976745319685, 11913384027525, 23280601870855, 16324024803240, 3631150469880, 279536140861, 5395128787] := by
  rw [show D2M8K2.u15800 = KTree.node D2M8K2.u15768 (nat_lit 34310305) (nat_lit 1549666246) (nat_lit 0) D2M8K2.u15799 from rfl, totK_node, atot15768, atot15799]
  decide +kernel

theorem arows15863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15863 = true := by
  rw [show D2M8K2.u15863 = KTree.node D2M8K2.u15831 (nat_lit 34411666) (nat_lit 4037135596) (nat_lit 0) D2M8K2.u15862 from rfl, allE_node, arows15831, irow15863, arows15862]
  all_goals rfl

theorem atot15863 : totK PD2M8K2 D2M8K2.u15863 = [0, 4108592678453, 17447860335929, 23655261857192, 11190749059460, 1633431898048, 50576159417, 0] := by
  rw [show D2M8K2.u15863 = KTree.node D2M8K2.u15831 (nat_lit 34411666) (nat_lit 4037135596) (nat_lit 0) D2M8K2.u15862 from rfl, totK_node, atot15831, atot15862]
  decide +kernel

theorem arows15929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15929 = true := by
  rw [show D2M8K2.u15929 = KTree.node D2M8K2.u15897 (nat_lit 34526086) (nat_lit 3401867108) (nat_lit 0) D2M8K2.u15928 from rfl, allE_node, arows15897, irow15929, arows15928]
  all_goals rfl

theorem atot15929 : totK PD2M8K2 D2M8K2.u15929 = [0, 3694509517985, 16957113205803, 24566516113124, 11107441795029, 1177971714517, 25181293312, 0] := by
  rw [show D2M8K2.u15929 = KTree.node D2M8K2.u15897 (nat_lit 34526086) (nat_lit 3401867108) (nat_lit 0) D2M8K2.u15928 from rfl, totK_node, atot15897, atot15928]
  decide +kernel

theorem arows15992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15992 = true := by
  rw [show D2M8K2.u15992 = KTree.node D2M8K2.u15960 (nat_lit 34606458) (nat_lit 3909650542) (nat_lit 0) D2M8K2.u15991 from rfl, allE_node, arows15960, irow15992, arows15991]
  all_goals rfl

theorem atot15992 : totK PD2M8K2 D2M8K2.u15992 = [0, 0, 6429824583578, 23223383252653, 22621622001655, 5086502981294, 221183181841, 1310517177] := by
  rw [show D2M8K2.u15992 = KTree.node D2M8K2.u15960 (nat_lit 34606458) (nat_lit 3909650542) (nat_lit 0) D2M8K2.u15991 from rfl, totK_node, atot15960, atot15991]
  decide +kernel

theorem arows16056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16056 = true := by
  rw [show D2M8K2.u16056 = KTree.node D2M8K2.u16024 (nat_lit 34758150) (nat_lit 3580061792) (nat_lit 0) D2M8K2.u16055 from rfl, allE_node, arows16024, irow16056, arows16055]
  all_goals rfl

theorem atot16056 : totK PD2M8K2 D2M8K2.u16056 = [0, 847096328040, 7747873929555, 21293355051537, 21034784524265, 6177453646283, 459640261590, 6643327963] := by
  rw [show D2M8K2.u16056 = KTree.node D2M8K2.u16024 (nat_lit 34758150) (nat_lit 3580061792) (nat_lit 0) D2M8K2.u16055 from rfl, totK_node, atot16024, atot16055]
  decide +kernel

theorem arows16119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16119 = true := by
  rw [show D2M8K2.u16119 = KTree.node D2M8K2.u16087 (nat_lit 35384104) (nat_lit 3829952091) (nat_lit 0) D2M8K2.u16118 from rfl, allE_node, arows16087, irow16119, arows16118]
  all_goals rfl

theorem atot16119 : totK PD2M8K2 D2M8K2.u16119 = [0, 3191776154013, 15802305820420, 24738536186546, 12441275825497, 1613615597949, 38847018177, 0] := by
  rw [show D2M8K2.u16119 = KTree.node D2M8K2.u16087 (nat_lit 35384104) (nat_lit 3829952091) (nat_lit 0) D2M8K2.u16118 from rfl, totK_node, atot16087, atot16118]
  decide +kernel

theorem arows16184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16184 = true := by
  rw [show D2M8K2.u16184 = KTree.node D2M8K2.u16152 (nat_lit 35453432) (nat_lit 3682233856) (nat_lit 0) D2M8K2.u16183 from rfl, allE_node, arows16152, irow16184, arows16183]
  all_goals rfl

theorem atot16184 : totK PD2M8K2 D2M8K2.u16184 = [0, 4036993659875, 17629242435431, 24204848218719, 10655588778468, 1115756912037, 21504795354, 0] := by
  rw [show D2M8K2.u16184 = KTree.node D2M8K2.u16152 (nat_lit 35453432) (nat_lit 3682233856) (nat_lit 0) D2M8K2.u16183 from rfl, totK_node, atot16152, atot16183]
  decide +kernel

theorem arows16247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16247 = true := by
  rw [show D2M8K2.u16247 = KTree.node D2M8K2.u16215 (nat_lit 35566606) (nat_lit 3939038508) (nat_lit 0) D2M8K2.u16246 from rfl, allE_node, arows16215, irow16247, arows16246]
  all_goals rfl

theorem atot16247 : totK PD2M8K2 D2M8K2.u16247 = [0, 2136927762780, 12486113469389, 24216262705335, 16122824705081, 2518240739774, 76392470908, 0] := by
  rw [show D2M8K2.u16247 = KTree.node D2M8K2.u16215 (nat_lit 35566606) (nat_lit 3939038508) (nat_lit 0) D2M8K2.u16246 from rfl, totK_node, atot16215, atot16246]
  decide +kernel

theorem arows16311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16311 = true := by
  rw [show D2M8K2.u16311 = KTree.node D2M8K2.u16279 (nat_lit 35668868) (nat_lit 3352333383) (nat_lit 0) D2M8K2.u16310 from rfl, allE_node, arows16279, irow16311, arows16310]
  all_goals rfl

theorem atot16311 : totK PD2M8K2 D2M8K2.u16311 = [0, 0, 4642575350769, 19603431229633, 24311459890267, 8270364964858, 617681369821, 7670626701] := by
  rw [show D2M8K2.u16311 = KTree.node D2M8K2.u16279 (nat_lit 35668868) (nat_lit 3352333383) (nat_lit 0) D2M8K2.u16310 from rfl, totK_node, atot16279, atot16310]
  decide +kernel

theorem arows16374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16374 = true := by
  rw [show D2M8K2.u16374 = KTree.node D2M8K2.u16342 (nat_lit 35795856) (nat_lit 2698610225) (nat_lit 0) D2M8K2.u16373 from rfl, allE_node, arows16342, irow16374, arows16373]
  all_goals rfl

theorem atot16374 : totK PD2M8K2 D2M8K2.u16374 = [0, 0, 3542121979799, 16763528979828, 24299441804819, 11144509121463, 1382546256900, 39028888556] := by
  rw [show D2M8K2.u16374 = KTree.node D2M8K2.u16342 (nat_lit 35795856) (nat_lit 2698610225) (nat_lit 0) D2M8K2.u16373 from rfl, totK_node, atot16342, atot16373]
  decide +kernel

theorem arows126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u126 = true := by
  rw [show D2M8K2.u126 = KTree.node D2M8K2.u62 (nat_lit 118394) (nat_lit 3323182045) (nat_lit 0) D2M8K2.u125 from rfl, allE_node, arows62, irow126, arows125]
  all_goals rfl

theorem atot126 : totK PD2M8K2 D2M8K2.u126 = [8161606443490, 35747214401581, 48447194136702, 20314293622122, 2065739752747, 40370388169, 0, 0] := by
  rw [show D2M8K2.u126 = KTree.node D2M8K2.u62 (nat_lit 118394) (nat_lit 3323182045) (nat_lit 0) D2M8K2.u125 from rfl, totK_node, atot62, atot125]
  decide +kernel

theorem arows253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u253 = true := by
  rw [show D2M8K2.u253 = KTree.node D2M8K2.u189 (nat_lit 267011) (nat_lit 2831529181) (nat_lit 0) D2M8K2.u252 from rfl, allE_node, arows189, irow253, arows252]
  all_goals rfl

theorem atot253 : totK PD2M8K2 D2M8K2.u253 = [2019269348258, 17923503730608, 45924636366465, 39644316948920, 8696639885373, 437620469804, 1369150432, 0] := by
  rw [show D2M8K2.u253 = KTree.node D2M8K2.u189 (nat_lit 267011) (nat_lit 2831529181) (nat_lit 0) D2M8K2.u252 from rfl, totK_node, atot189, atot252]
  decide +kernel

theorem arows381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u381 = true := by
  rw [show D2M8K2.u381 = KTree.node D2M8K2.u317 (nat_lit 1043845) (nat_lit 1359503336) (nat_lit 0) D2M8K2.u380 from rfl, allE_node, arows317, irow381, arows380]
  all_goals rfl

theorem atot381 : totK PD2M8K2 D2M8K2.u381 = [5799234421439, 29015454539236, 47862112232482, 27840717031802, 4446620020383, 134304205289, 0, 0] := by
  rw [show D2M8K2.u381 = KTree.node D2M8K2.u317 (nat_lit 1043845) (nat_lit 1359503336) (nat_lit 0) D2M8K2.u380 from rfl, totK_node, atot317, atot380]
  decide +kernel

theorem arows508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u508 = true := by
  rw [show D2M8K2.u508 = KTree.node D2M8K2.u444 (nat_lit 1234296) (nat_lit 2702074679) (nat_lit 0) D2M8K2.u507 from rfl, allE_node, arows444, irow508, arows507]
  all_goals rfl

theorem atot508 : totK PD2M8K2 D2M8K2.u508 = [3974952489386, 23177232396734, 45956042803011, 34062260290030, 7380098340355, 345938124136, 1275377855, 0] := by
  rw [show D2M8K2.u508 = KTree.node D2M8K2.u444 (nat_lit 1234296) (nat_lit 2702074679) (nat_lit 0) D2M8K2.u507 from rfl, totK_node, atot444, atot507]
  decide +kernel

theorem arows637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u637 = true := by
  rw [show D2M8K2.u637 = KTree.node D2M8K2.u573 (nat_lit 1458634) (nat_lit 3854234473) (nat_lit 0) D2M8K2.u636 from rfl, allE_node, arows573, irow637, arows636]
  all_goals rfl

theorem atot637 : totK PD2M8K2 D2M8K2.u637 = [3692611367677, 20377041082231, 41252592059852, 36166396421366, 11845716532851, 1132509636935, 24680175954, 0] := by
  rw [show D2M8K2.u637 = KTree.node D2M8K2.u573 (nat_lit 1458634) (nat_lit 3854234473) (nat_lit 0) D2M8K2.u636 from rfl, totK_node, atot573, atot636]
  decide +kernel

theorem arows764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u764 = true := by
  rw [show D2M8K2.u764 = KTree.node D2M8K2.u700 (nat_lit 1672140) (nat_lit 3430419102) (nat_lit 0) D2M8K2.u763 from rfl, allE_node, arows700, irow764, arows763]
  all_goals rfl

theorem atot764 : totK PD2M8K2 D2M8K2.u764 = [6082875166126, 30096838723874, 48506246304238, 26564713729438, 3650483272182, 84401272356, 0, 0] := by
  rw [show D2M8K2.u764 = KTree.node D2M8K2.u700 (nat_lit 1672140) (nat_lit 3430419102) (nat_lit 0) D2M8K2.u763 from rfl, totK_node, atot700, atot763]
  decide +kernel

theorem arows892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u892 = true := by
  rw [show D2M8K2.u892 = KTree.node D2M8K2.u828 (nat_lit 1892047) (nat_lit 2216741076) (nat_lit 0) D2M8K2.u891 from rfl, allE_node, arows828, irow892, arows891]
  all_goals rfl

theorem atot892 : totK PD2M8K2 D2M8K2.u892 = [437191058986, 9833929289818, 37816650413819, 47609229359396, 17073559539921, 1447013778546, 26316908414, 0] := by
  rw [show D2M8K2.u892 = KTree.node D2M8K2.u828 (nat_lit 1892047) (nat_lit 2216741076) (nat_lit 0) D2M8K2.u891 from rfl, totK_node, atot828, atot891]
  decide +kernel

theorem arows1019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1019 = true := by
  rw [show D2M8K2.u1019 = KTree.node D2M8K2.u955 (nat_lit 2075478) (nat_lit 3510286438) (nat_lit 0) D2M8K2.u1018 from rfl, allE_node, arows955, irow1019, arows1018]
  all_goals rfl

theorem atot1019 : totK PD2M8K2 D2M8K2.u1019 = [7220658750257, 33226378406183, 48400668172283, 23049193372066, 2982660707385, 83227282954, 0, 0] := by
  rw [show D2M8K2.u1019 = KTree.node D2M8K2.u955 (nat_lit 2075478) (nat_lit 3510286438) (nat_lit 0) D2M8K2.u1018 from rfl, totK_node, atot955, atot1018]
  decide +kernel

theorem arows1149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1149 = true := by
  rw [show D2M8K2.u1149 = KTree.node D2M8K2.u1085 (nat_lit 2274164) (nat_lit 3666590483) (nat_lit 0) D2M8K2.u1148 from rfl, allE_node, arows1085, irow1149, arows1148]
  all_goals rfl

theorem atot1149 : totK PD2M8K2 D2M8K2.u1149 = [2102405875695, 18340147846259, 46371931698413, 39146291666269, 8434232512619, 369638956155, 1209030869, 0] := by
  rw [show D2M8K2.u1149 = KTree.node D2M8K2.u1085 (nat_lit 2274164) (nat_lit 3666590483) (nat_lit 0) D2M8K2.u1148 from rfl, totK_node, atot1085, atot1148]
  decide +kernel

theorem arows1276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1276 = true := by
  rw [show D2M8K2.u1276 = KTree.node D2M8K2.u1212 (nat_lit 2537194) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u1275 from rfl, allE_node, arows1212, irow1276, arows1275]
  all_goals rfl

theorem atot1276 : totK PD2M8K2 D2M8K2.u1276 = [5933193526943, 27716140918862, 44652292135669, 28980910095725, 7001013210297, 520755748190, 6115358396, 0] := by
  rw [show D2M8K2.u1276 = KTree.node D2M8K2.u1212 (nat_lit 2537194) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u1275 from rfl, totK_node, atot1212, atot1275]
  decide +kernel

theorem arows1404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1404 = true := by
  rw [show D2M8K2.u1404 = KTree.node D2M8K2.u1340 (nat_lit 2725753) (nat_lit 1458770128) (nat_lit 0) D2M8K2.u1403 from rfl, allE_node, arows1340, irow1404, arows1403]
  all_goals rfl

theorem atot1404 : totK PD2M8K2 D2M8K2.u1404 = [3856492171129, 22617593138764, 45292687761668, 34729726900689, 8066174681615, 384264103041, 1369150432, 0] := by
  rw [show D2M8K2.u1404 = KTree.node D2M8K2.u1340 (nat_lit 2725753) (nat_lit 1458770128) (nat_lit 0) D2M8K2.u1403 from rfl, totK_node, atot1340, atot1403]
  decide +kernel

theorem arows1531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1531 = true := by
  rw [show D2M8K2.u1531 = KTree.node D2M8K2.u1467 (nat_lit 2950389) (nat_lit 1184828196) (nat_lit 0) D2M8K2.u1530 from rfl, allE_node, arows1467, irow1531, arows1530]
  all_goals rfl

theorem atot1531 : totK PD2M8K2 D2M8K2.u1531 = [0, 7413125020817, 34469653460247, 49210844537034, 20939179299741, 2150123308477, 46699515257, 0] := by
  rw [show D2M8K2.u1531 = KTree.node D2M8K2.u1467 (nat_lit 2950389) (nat_lit 1184828196) (nat_lit 0) D2M8K2.u1530 from rfl, totK_node, atot1467, atot1530]
  decide +kernel

theorem arows1660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1660 = true := by
  rw [show D2M8K2.u1660 = KTree.node D2M8K2.u1596 (nat_lit 3144357) (nat_lit 1451124418) (nat_lit 0) D2M8K2.u1659 from rfl, allE_node, arows1596, irow1660, arows1659]
  all_goals rfl

theorem atot1660 : totK PD2M8K2 D2M8K2.u1660 = [0, 8055072653694, 35361284445457, 48523324358692, 20319886106675, 1965407013023, 45288637697, 0] := by
  rw [show D2M8K2.u1660 = KTree.node D2M8K2.u1596 (nat_lit 3144357) (nat_lit 1451124418) (nat_lit 0) D2M8K2.u1659 from rfl, totK_node, atot1596, atot1659]
  decide +kernel

theorem arows1787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1787 = true := by
  rw [show D2M8K2.u1787 = KTree.node D2M8K2.u1723 (nat_lit 3361586) (nat_lit 2514055933) (nat_lit 8) D2M8K2.u1786 from rfl, allE_node, arows1723, irow1787, arows1786]
  all_goals rfl

theorem atot1787 : totK PD2M8K2 D2M8K2.u1787 = [0, 1636922335308, 17191138901240, 46249019239996, 39509629089099, 8591607303161, 471053465542, 1369150432] := by
  rw [show D2M8K2.u1787 = KTree.node D2M8K2.u1723 (nat_lit 3361586) (nat_lit 2514055933) (nat_lit 8) D2M8K2.u1786 from rfl, totK_node, atot1723, atot1786]
  decide +kernel

theorem arows1915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1915 = true := by
  rw [show D2M8K2.u1915 = KTree.node D2M8K2.u1851 (nat_lit 4083312) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u1914 from rfl, allE_node, arows1851, irow1915, arows1914]
  all_goals rfl

theorem atot1915 : totK PD2M8K2 D2M8K2.u1915 = [0, 7670490799706, 34677151195400, 49158701819877, 21161922382640, 2031594065699, 32856578341, 0] := by
  rw [show D2M8K2.u1915 = KTree.node D2M8K2.u1851 (nat_lit 4083312) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u1914 from rfl, totK_node, atot1851, atot1914]
  decide +kernel

theorem arows2042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2042 = true := by
  rw [show D2M8K2.u2042 = KTree.node D2M8K2.u1978 (nat_lit 4535366) (nat_lit 3101677560) (nat_lit 0) D2M8K2.u2041 from rfl, allE_node, arows1978, irow2042, arows2041]
  all_goals rfl

theorem atot2042 : totK PD2M8K2 D2M8K2.u2042 = [0, 7298431548986, 33797454139222, 49056111583006, 22384034189713, 2366230603098, 47045720120, 0] := by
  rw [show D2M8K2.u2042 = KTree.node D2M8K2.u1978 (nat_lit 4535366) (nat_lit 3101677560) (nat_lit 0) D2M8K2.u2041 from rfl, totK_node, atot1978, atot2041]
  decide +kernel

theorem arows2173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2173 = true := by
  rw [show D2M8K2.u2173 = KTree.node D2M8K2.u2109 (nat_lit 4984776) (nat_lit 3431858857) (nat_lit 0) D2M8K2.u2172 from rfl, allE_node, arows2109, irow2173, arows2172]
  all_goals rfl

theorem atot2173 : totK PD2M8K2 D2M8K2.u2173 = [0, 7861911678080, 35444871506303, 49225287664207, 20436705530384, 1877000860993, 28993645025, 0] := by
  rw [show D2M8K2.u2173 = KTree.node D2M8K2.u2109 (nat_lit 4984776) (nat_lit 3431858857) (nat_lit 0) D2M8K2.u2172 from rfl, totK_node, atot2109, atot2172]
  decide +kernel

theorem arows2300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2300 = true := by
  rw [show D2M8K2.u2300 = KTree.node D2M8K2.u2236 (nat_lit 5147300) (nat_lit 3114839493) (nat_lit 0) D2M8K2.u2299 from rfl, allE_node, arows2236, irow2300, arows2299]
  all_goals rfl

theorem atot2300 : totK PD2M8K2 D2M8K2.u2300 = [0, 7301545404288, 34031828857762, 49300103088131, 21481417830612, 2187400447857, 45347502552, 0] := by
  rw [show D2M8K2.u2300 = KTree.node D2M8K2.u2236 (nat_lit 5147300) (nat_lit 3114839493) (nat_lit 0) D2M8K2.u2299 from rfl, totK_node, atot2236, atot2299]
  decide +kernel

theorem arows2428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2428 = true := by
  rw [show D2M8K2.u2428 = KTree.node D2M8K2.u2364 (nat_lit 5601970) (nat_lit 3989331968) (nat_lit 0) D2M8K2.u2427 from rfl, allE_node, arows2364, irow2428, arows2427]
  all_goals rfl

theorem atot2428 : totK PD2M8K2 D2M8K2.u2428 = [0, 7327314365147, 33643931720807, 49129741922655, 22800195551840, 2346981431010, 36796608038, 0] := by
  rw [show D2M8K2.u2428 = KTree.node D2M8K2.u2364 (nat_lit 5601970) (nat_lit 3989331968) (nat_lit 0) D2M8K2.u2427 from rfl, totK_node, atot2364, atot2427]
  decide +kernel

theorem arows2555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2555 = true := by
  rw [show D2M8K2.u2555 = KTree.node D2M8K2.u2491 (nat_lit 6571326) (nat_lit 3815872651) (nat_lit 0) D2M8K2.u2554 from rfl, allE_node, arows2491, irow2555, arows2554]
  all_goals rfl

theorem atot2555 : totK PD2M8K2 D2M8K2.u2555 = [7348351400121, 32157184956158, 46182021094669, 24471460649163, 4855210516251, 516868343350, 21751168066, 0] := by
  rw [show D2M8K2.u2555 = KTree.node D2M8K2.u2491 (nat_lit 6571326) (nat_lit 3815872651) (nat_lit 0) D2M8K2.u2554 from rfl, totK_node, atot2491, atot2554]
  decide +kernel

theorem arows2684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2684 = true := by
  rw [show D2M8K2.u2684 = KTree.node D2M8K2.u2620 (nat_lit 6766280) (nat_lit 3668228315) (nat_lit 0) D2M8K2.u2683 from rfl, allE_node, arows2620, irow2684, arows2683]
  all_goals rfl

theorem atot2684 : totK PD2M8K2 D2M8K2.u2684 = [2878068400688, 18591447850082, 41192650487192, 37106296863885, 13681991952418, 1772691453869, 57647371591, 0] := by
  rw [show D2M8K2.u2684 = KTree.node D2M8K2.u2620 (nat_lit 6766280) (nat_lit 3668228315) (nat_lit 0) D2M8K2.u2683 from rfl, totK_node, atot2620, atot2683]
  decide +kernel

theorem arows2811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2811 = true := by
  rw [show D2M8K2.u2811 = KTree.node D2M8K2.u2747 (nat_lit 6912333) (nat_lit 1488703967) (nat_lit 0) D2M8K2.u2810 from rfl, allE_node, arows2747, irow2811, arows2810]
  all_goals rfl

theorem atot2811 : totK PD2M8K2 D2M8K2.u2811 = [1647549989118, 12751641763179, 36412070368469, 43616511931494, 18536060999818, 1861315963850, 26790864705, 0] := by
  rw [show D2M8K2.u2811 = KTree.node D2M8K2.u2747 (nat_lit 6912333) (nat_lit 1488703967) (nat_lit 0) D2M8K2.u2810 from rfl, totK_node, atot2747, atot2810]
  decide +kernel

theorem arows2939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2939 = true := by
  rw [show D2M8K2.u2939 = KTree.node D2M8K2.u2875 (nat_lit 7069570) (nat_lit 4068400611) (nat_lit 0) D2M8K2.u2938 from rfl, allE_node, arows2875, irow2939, arows2938]
  all_goals rfl

theorem atot2939 : totK PD2M8K2 D2M8K2.u2939 = [7604264934025, 33713718888306, 47961612747996, 23025690794187, 3050081196436, 82930545147, 0, 0] := by
  rw [show D2M8K2.u2939 = KTree.node D2M8K2.u2875 (nat_lit 7069570) (nat_lit 4068400611) (nat_lit 0) D2M8K2.u2938 from rfl, totK_node, atot2875, atot2938]
  decide +kernel

theorem arows3066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3066 = true := by
  rw [show D2M8K2.u3066 = KTree.node D2M8K2.u3002 (nat_lit 7274150) (nat_lit 3830427073) (nat_lit 0) D2M8K2.u3065 from rfl, allE_node, arows3002, irow3066, arows3065]
  all_goals rfl

theorem atot3066 : totK PD2M8K2 D2M8K2.u3066 = [529390851355, 11906924351309, 41195140994709, 45419948536305, 14359247450736, 1167213072560, 21175891594, 0] := by
  rw [show D2M8K2.u3066 = KTree.node D2M8K2.u3002 (nat_lit 7274150) (nat_lit 3830427073) (nat_lit 0) D2M8K2.u3065 from rfl, totK_node, atot3002, atot3065]
  decide +kernel

theorem arows3196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3196 = true := by
  rw [show D2M8K2.u3196 = KTree.node D2M8K2.u3132 (nat_lit 7518884) (nat_lit 3179901253) (nat_lit 0) D2M8K2.u3195 from rfl, allE_node, arows3132, irow3196, arows3195]
  all_goals rfl

theorem atot3196 : totK PD2M8K2 D2M8K2.u3196 = [5803710501950, 28069395450264, 45968186614455, 28914295161509, 6112627362878, 354952646983, 4779662215, 0] := by
  rw [show D2M8K2.u3196 = KTree.node D2M8K2.u3132 (nat_lit 7518884) (nat_lit 3179901253) (nat_lit 0) D2M8K2.u3195 from rfl, totK_node, atot3132, atot3195]
  decide +kernel

theorem arows3323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3323 = true := by
  rw [show D2M8K2.u3323 = KTree.node D2M8K2.u3259 (nat_lit 7703548) (nat_lit 3453182119) (nat_lit 0) D2M8K2.u3322 from rfl, allE_node, arows3259, irow3323, arows3322]
  all_goals rfl

theorem atot3323 : totK PD2M8K2 D2M8K2.u3323 = [3978808262243, 23434556034093, 46131112445361, 33819931259557, 7474177233730, 357583105294, 1310517177, 0] := by
  rw [show D2M8K2.u3323 = KTree.node D2M8K2.u3259 (nat_lit 7703548) (nat_lit 3453182119) (nat_lit 0) D2M8K2.u3322 from rfl, totK_node, atot3259, atot3322]
  decide +kernel

theorem arows3451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3451 = true := by
  rw [show D2M8K2.u3451 = KTree.node D2M8K2.u3387 (nat_lit 7927566) (nat_lit 3977210588) (nat_lit 0) D2M8K2.u3450 from rfl, allE_node, arows3387, irow3451, arows3450]
  all_goals rfl

theorem atot3451 : totK PD2M8K2 D2M8K2.u3451 = [3690298243741, 20082841518643, 40729493185292, 36529830851174, 12365789592678, 1169851876027, 25006391237, 0] := by
  rw [show D2M8K2.u3451 = KTree.node D2M8K2.u3387 (nat_lit 7927566) (nat_lit 3977210588) (nat_lit 0) D2M8K2.u3450 from rfl, totK_node, atot3387, atot3450]
  decide +kernel

theorem arows3578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3578 = true := by
  rw [show D2M8K2.u3578 = KTree.node D2M8K2.u3514 (nat_lit 8102109) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u3577 from rfl, allE_node, arows3514, irow3578, arows3577]
  all_goals rfl

theorem atot3578 : totK PD2M8K2 D2M8K2.u3578 = [6076389944039, 30198160244396, 48648546948986, 26447476547830, 3536497379182, 79427206437, 0, 0] := by
  rw [show D2M8K2.u3578 = KTree.node D2M8K2.u3514 (nat_lit 8102109) (nat_lit 1571021645) (nat_lit 0) D2M8K2.u3577 from rfl, totK_node, atot3514, atot3577]
  decide +kernel

theorem arows3707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3707 = true := by
  rw [show D2M8K2.u3707 = KTree.node D2M8K2.u3643 (nat_lit 8347437) (nat_lit 1500648801) (nat_lit 0) D2M8K2.u3706 from rfl, allE_node, arows3643, irow3707, arows3706]
  all_goals rfl

theorem atot3707 : totK PD2M8K2 D2M8K2.u3707 = [1651197789013, 15167490634859, 42498239215615, 42676859949768, 11986987494807, 796898297909, 7324389265, 0] := by
  rw [show D2M8K2.u3707 = KTree.node D2M8K2.u3643 (nat_lit 8347437) (nat_lit 1500648801) (nat_lit 0) D2M8K2.u3706 from rfl, totK_node, atot3643, atot3706]
  decide +kernel

theorem arows3834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3834 = true := by
  rw [show D2M8K2.u3834 = KTree.node D2M8K2.u3770 (nat_lit 8562365) (nat_lit 2158828438) (nat_lit 0) D2M8K2.u3833 from rfl, allE_node, arows3770, irow3834, arows3833]
  all_goals rfl

theorem atot3834 : totK PD2M8K2 D2M8K2.u3834 = [7279057468916, 32946242398242, 48052925402032, 23979051191561, 3325591162880, 95881121667, 0, 0] := by
  rw [show D2M8K2.u3834 = KTree.node D2M8K2.u3770 (nat_lit 8562365) (nat_lit 2158828438) (nat_lit 0) D2M8K2.u3833 from rfl, totK_node, atot3770, atot3833]
  decide +kernel

theorem arows3962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3962 = true := by
  rw [show D2M8K2.u3962 = KTree.node D2M8K2.u3898 (nat_lit 8762802) (nat_lit 3385897543) (nat_lit 0) D2M8K2.u3961 from rfl, allE_node, arows3898, irow3962, arows3961]
  all_goals rfl

theorem atot3962 : totK PD2M8K2 D2M8K2.u3962 = [867070346516, 12928143393715, 41526827942512, 44663177871995, 13947430746290, 917267169048, 8870992680, 0] := by
  rw [show D2M8K2.u3962 = KTree.node D2M8K2.u3898 (nat_lit 8762802) (nat_lit 3385897543) (nat_lit 0) D2M8K2.u3961 from rfl, totK_node, atot3898, atot3961]
  decide +kernel

theorem arows4089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4089 = true := by
  rw [show D2M8K2.u4089 = KTree.node D2M8K2.u4025 (nat_lit 9513627) (nat_lit 3461127377) (nat_lit 0) D2M8K2.u4088 from rfl, allE_node, arows4025, irow4089, arows4088]
  all_goals rfl

theorem atot4089 : totK PD2M8K2 D2M8K2.u4089 = [0, 6837830757317, 31831126584868, 47958215631286, 24905427410070, 3601456536024, 107259177814, 0] := by
  rw [show D2M8K2.u4089 = KTree.node D2M8K2.u4025 (nat_lit 9513627) (nat_lit 3461127377) (nat_lit 0) D2M8K2.u4088 from rfl, totK_node, atot4025, atot4088]
  decide +kernel

theorem arows4221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4221 = true := by
  rw [show D2M8K2.u4221 = KTree.node D2M8K2.u4157 (nat_lit 9663032) (nat_lit 2827197643) (nat_lit 0) D2M8K2.u4220 from rfl, allE_node, arows4157, irow4221, arows4220]
  all_goals rfl

theorem atot4221 : totK PD2M8K2 D2M8K2.u4221 = [0, 5499994119439, 28071917761675, 47041251588065, 28403502383940, 5926742523005, 707642303794, 36921873854] := by
  rw [show D2M8K2.u4221 = KTree.node D2M8K2.u4157 (nat_lit 9663032) (nat_lit 2827197643) (nat_lit 0) D2M8K2.u4220 from rfl, totK_node, atot4157, atot4220]
  decide +kernel

theorem arows4348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4348 = true := by
  rw [show D2M8K2.u4348 = KTree.node D2M8K2.u4284 (nat_lit 9848119) (nat_lit 1042251403) (nat_lit 2) D2M8K2.u4347 from rfl, allE_node, arows4284, irow4348, arows4347]
  all_goals rfl

theorem atot4348 : totK PD2M8K2 D2M8K2.u4348 = [0, 0, 8070123341077, 35640179065739, 48544789421728, 20793234384280, 2118530854706, 35326512075] := by
  rw [show D2M8K2.u4348 = KTree.node D2M8K2.u4284 (nat_lit 9848119) (nat_lit 1042251403) (nat_lit 2) D2M8K2.u4347 from rfl, totK_node, atot4284, atot4347]
  decide +kernel

theorem arows4476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4476 = true := by
  rw [show D2M8K2.u4476 = KTree.node D2M8K2.u4412 (nat_lit 10021543) (nat_lit 2305389841) (nat_lit 0) D2M8K2.u4475 from rfl, allE_node, arows4412, irow4476, arows4475]
  all_goals rfl

theorem atot4476 : totK PD2M8K2 D2M8K2.u4476 = [0, 7023066606757, 30540794328998, 44401617687838, 25767810402743, 6965583042875, 653536118540, 12189850367] := by
  rw [show D2M8K2.u4476 = KTree.node D2M8K2.u4412 (nat_lit 10021543) (nat_lit 2305389841) (nat_lit 0) D2M8K2.u4475 from rfl, totK_node, atot4412, atot4475]
  decide +kernel

theorem arows4603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4603 = true := by
  rw [show D2M8K2.u4603 = KTree.node D2M8K2.u4539 (nat_lit 10210642) (nat_lit 4015353725) (nat_lit 0) D2M8K2.u4602 from rfl, allE_node, arows4539, irow4603, arows4602]
  all_goals rfl

theorem atot4603 : totK PD2M8K2 D2M8K2.u4603 = [0, 2758139167741, 20251344499392, 46147589617987, 36797047336947, 8661889222168, 569762922513, 7048116272] := by
  rw [show D2M8K2.u4603 = KTree.node D2M8K2.u4539 (nat_lit 10210642) (nat_lit 4015353725) (nat_lit 0) D2M8K2.u4602 from rfl, totK_node, atot4539, atot4602]
  decide +kernel

theorem arows4732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4732 = true := by
  rw [show D2M8K2.u4732 = KTree.node D2M8K2.u4668 (nat_lit 10483283) (nat_lit 2266076363) (nat_lit 0) D2M8K2.u4731 from rfl, allE_node, arows4668, irow4732, arows4731]
  all_goals rfl

theorem atot4732 : totK PD2M8K2 D2M8K2.u4732 = [0, 5803710501950, 27433611030183, 45332136231295, 30176192387288, 6674326932332, 321355870195, 1394496256] := by
  rw [show D2M8K2.u4732 = KTree.node D2M8K2.u4668 (nat_lit 10483283) (nat_lit 2266076363) (nat_lit 0) D2M8K2.u4731 from rfl, totK_node, atot4668, atot4731]
  decide +kernel

theorem arows4859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4859 = true := by
  rw [show D2M8K2.u4859 = KTree.node D2M8K2.u4795 (nat_lit 10670274) (nat_lit 3020911170) (nat_lit 0) D2M8K2.u4858 from rfl, allE_node, arows4795, irow4859, arows4858]
  all_goals rfl

theorem atot4859 : totK PD2M8K2 D2M8K2.u4859 = [0, 3978808262243, 25375474772445, 49487465619239, 31348270905451, 5021442996037, 153225533450, 0] := by
  rw [show D2M8K2.u4859 = KTree.node D2M8K2.u4795 (nat_lit 10670274) (nat_lit 3020911170) (nat_lit 0) D2M8K2.u4858 from rfl, totK_node, atot4795, atot4858]
  decide +kernel

theorem arows4987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4987 = true := by
  rw [show D2M8K2.u4987 = KTree.node D2M8K2.u4923 (nat_lit 10918381) (nat_lit 1384173910) (nat_lit 0) D2M8K2.u4986 from rfl, allE_node, arows4923, irow4987, arows4986]
  all_goals rfl

theorem atot4987 : totK PD2M8K2 D2M8K2.u4987 = [0, 3690298243741, 20952144010298, 42942767068795, 36279868650589, 10544418511341, 758313108011, 8535762846] := by
  rw [show D2M8K2.u4987 = KTree.node D2M8K2.u4923 (nat_lit 10918381) (nat_lit 1384173910) (nat_lit 0) D2M8K2.u4986 from rfl, totK_node, atot4923, atot4986]
  decide +kernel

theorem arows5114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5114 = true := by
  rw [show D2M8K2.u5114 = KTree.node D2M8K2.u5050 (nat_lit 11094395) (nat_lit 2275635395) (nat_lit 0) D2M8K2.u5113 from rfl, allE_node, arows5050, irow5114, arows5113]
  all_goals rfl

theorem atot5114 : totK PD2M8K2 D2M8K2.u5114 = [0, 6076389944039, 30198230647541, 48966906369290, 26447225894757, 3249287958454, 64742786122, 0] := by
  rw [show D2M8K2.u5114 = KTree.node D2M8K2.u5050 (nat_lit 11094395) (nat_lit 2275635395) (nat_lit 0) D2M8K2.u5113 from rfl, totK_node, atot5050, atot5113]
  decide +kernel

theorem arows5244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5244 = true := by
  rw [show D2M8K2.u5244 = KTree.node D2M8K2.u5180 (nat_lit 11369692) (nat_lit 3844838750) (nat_lit 0) D2M8K2.u5243 from rfl, allE_node, arows5180, irow5244, arows5243]
  all_goals rfl

theorem atot5244 : totK PD2M8K2 D2M8K2.u5244 = [0, 3030482235072, 20324559202046, 45654963987352, 37441689577166, 8673290502280, 451108626477, 1493059870] := by
  rw [show D2M8K2.u5244 = KTree.node D2M8K2.u5180 (nat_lit 11369692) (nat_lit 3844838750) (nat_lit 0) D2M8K2.u5243 from rfl, totK_node, atot5180, atot5243]
  decide +kernel

theorem arows5371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5371 = true := by
  rw [show D2M8K2.u5371 = KTree.node D2M8K2.u5307 (nat_lit 11573654) (nat_lit 3054272136) (nat_lit 0) D2M8K2.u5370 from rfl, allE_node, arows5307, irow5371, arows5370]
  all_goals rfl

theorem atot5371 : totK PD2M8K2 D2M8K2.u5371 = [0, 6766843369373, 31795922564979, 48346592391637, 25277266960624, 3459277668288, 88355863885, 0] := by
  rw [show D2M8K2.u5371 = KTree.node D2M8K2.u5307 (nat_lit 11573654) (nat_lit 3054272136) (nat_lit 0) D2M8K2.u5370 from rfl, totK_node, atot5307, atot5370]
  decide +kernel

theorem arows5499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5499 = true := by
  rw [show D2M8K2.u5499 = KTree.node D2M8K2.u5435 (nat_lit 11816595) (nat_lit 2638317071) (nat_lit 0) D2M8K2.u5498 from rfl, allE_node, arows5435, irow5499, arows5498]
  all_goals rfl

theorem atot5499 : totK PD2M8K2 D2M8K2.u5499 = [0, 0, 10268656307980, 40783246873538, 47743677168505, 15572845966186, 1018515530278, 5834163889] := by
  rw [show D2M8K2.u5499 = KTree.node D2M8K2.u5435 (nat_lit 11816595) (nat_lit 2638317071) (nat_lit 0) D2M8K2.u5498 from rfl, totK_node, atot5435, atot5498]
  decide +kernel

theorem arows5626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5626 = true := by
  rw [show D2M8K2.u5626 = KTree.node D2M8K2.u5562 (nat_lit 12061510) (nat_lit 3316872278) (nat_lit 0) D2M8K2.u5625 from rfl, allE_node, arows5562, irow5626, arows5625]
  all_goals rfl

theorem atot5626 : totK PD2M8K2 D2M8K2.u5626 = [7757745427395, 34824274573060, 48260543442661, 20469367675122, 2315082835686, 658029792283, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5626 = KTree.node D2M8K2.u5562 (nat_lit 12061510) (nat_lit 3316872278) (nat_lit 0) D2M8K2.u5625 from rfl, totK_node, atot5562, atot5625]
  decide +kernel

theorem arows5755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5755 = true := by
  rw [show D2M8K2.u5755 = KTree.node D2M8K2.u5691 (nat_lit 12215426) (nat_lit 2042451912) (nat_lit 0) D2M8K2.u5754 from rfl, allE_node, arows5691, irow5755, arows5754]
  all_goals rfl

theorem atot5755 : totK PD2M8K2 D2M8K2.u5755 = [1988996583632, 17506870233212, 45444384506474, 40169335267783, 8940783990943, 450436494571, 1369150432, 0] := by
  rw [show D2M8K2.u5755 = KTree.node D2M8K2.u5691 (nat_lit 12215426) (nat_lit 2042451912) (nat_lit 0) D2M8K2.u5754 from rfl, totK_node, atot5691, atot5754]
  decide +kernel

theorem arows5882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5882 = true := by
  rw [show D2M8K2.u5882 = KTree.node D2M8K2.u5818 (nat_lit 12529301) (nat_lit 2168318726) (nat_lit 0) D2M8K2.u5881 from rfl, allE_node, arows5818, irow5882, arows5881]
  all_goals rfl

theorem atot5882 : totK PD2M8K2 D2M8K2.u5882 = [6333210432854, 29852129962477, 47289910247836, 27485312623520, 4503626900312, 137815164026, 0, 0] := by
  rw [show D2M8K2.u5882 = KTree.node D2M8K2.u5818 (nat_lit 12529301) (nat_lit 2168318726) (nat_lit 0) D2M8K2.u5881 from rfl, totK_node, atot5818, atot5881]
  decide +kernel

theorem arows6010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6010 = true := by
  rw [show D2M8K2.u6010 = KTree.node D2M8K2.u5946 (nat_lit 12688699) (nat_lit 1509223917) (nat_lit 0) D2M8K2.u6009 from rfl, allE_node, arows5946, irow6010, arows6009]
  all_goals rfl

theorem atot6010 : totK PD2M8K2 D2M8K2.u6010 = [3472343576529, 20704042554413, 42262652102560, 34962219094268, 12200953327063, 1663194373664, 57647371591, 0] := by
  rw [show D2M8K2.u6010 = KTree.node D2M8K2.u5946 (nat_lit 12688699) (nat_lit 1509223917) (nat_lit 0) D2M8K2.u6009 from rfl, totK_node, atot5946, atot6009]
  decide +kernel

theorem arows6137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6137 = true := by
  rw [show D2M8K2.u6137 = KTree.node D2M8K2.u6073 (nat_lit 12881694) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u6136 from rfl, allE_node, arows6073, irow6137, arows6136]
  all_goals rfl

theorem atot6137 : totK PD2M8K2 D2M8K2.u6137 = [2005649722024, 13036501979230, 34990952484907, 43417305702032, 19537134518526, 1965682272681, 26790864705, 0] := by
  rw [show D2M8K2.u6137 = KTree.node D2M8K2.u6073 (nat_lit 12881694) (nat_lit 3869046296) (nat_lit 0) D2M8K2.u6136 from rfl, totK_node, atot6073, atot6136]
  decide +kernel

theorem arows6268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6268 = true := by
  rw [show D2M8K2.u6268 = KTree.node D2M8K2.u6204 (nat_lit 13036401) (nat_lit 1824404709) (nat_lit 0) D2M8K2.u6267 from rfl, allE_node, arows6204, irow6268, arows6267]
  all_goals rfl

theorem atot6268 : totK PD2M8K2 D2M8K2.u6268 = [7000092032762, 32532416226971, 48456047087362, 23987376206171, 3195024372447, 84299695579, 0, 0] := by
  rw [show D2M8K2.u6268 = KTree.node D2M8K2.u6204 (nat_lit 13036401) (nat_lit 1824404709) (nat_lit 0) D2M8K2.u6267 from rfl, totK_node, atot6204, atot6267]
  decide +kernel

theorem arows6395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6395 = true := by
  rw [show D2M8K2.u6395 = KTree.node D2M8K2.u6331 (nat_lit 13235794) (nat_lit 3908507366) (nat_lit 0) D2M8K2.u6394 from rfl, allE_node, arows6331, irow6395, arows6394]
  all_goals rfl

theorem atot6395 : totK PD2M8K2 D2M8K2.u6395 = [1195523425885, 13938066739153, 42034282493978, 43383991050697, 13084780241114, 1060245916889, 20072436663, 0] := by
  rw [show D2M8K2.u6395 = KTree.node D2M8K2.u6331 (nat_lit 13235794) (nat_lit 3908507366) (nat_lit 0) D2M8K2.u6394 from rfl, totK_node, atot6331, atot6394]
  decide +kernel

theorem arows6523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6523 = true := by
  rw [show D2M8K2.u6523 = KTree.node D2M8K2.u6459 (nat_lit 13963829) (nat_lit 1839966326) (nat_lit 0) D2M8K2.u6522 from rfl, allE_node, arows6459, irow6523, arows6522]
  all_goals rfl

theorem atot6523 : totK PD2M8K2 D2M8K2.u6523 = [6008378691054, 27665638795856, 44396613773612, 29435785666761, 7082977641072, 446499175815, 5883117146, 0] := by
  rw [show D2M8K2.u6523 = KTree.node D2M8K2.u6459 (nat_lit 13963829) (nat_lit 1839966326) (nat_lit 0) D2M8K2.u6522 from rfl, totK_node, atot6459, atot6522]
  decide +kernel

theorem arows6650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6650 = true := by
  rw [show D2M8K2.u6650 = KTree.node D2M8K2.u6586 (nat_lit 14114553) (nat_lit 1871520958) (nat_lit 0) D2M8K2.u6649 from rfl, allE_node, arows6586, irow6650, arows6649]
  all_goals rfl

theorem atot6650 : totK PD2M8K2 D2M8K2.u6650 = [3754277374823, 23369822638705, 47154389617046, 33321984701090, 6583961251073, 304439222483, 1209030869, 0] := by
  rw [show D2M8K2.u6650 = KTree.node D2M8K2.u6586 (nat_lit 14114553) (nat_lit 1871520958) (nat_lit 0) D2M8K2.u6649 from rfl, totK_node, atot6586, atot6649]
  decide +kernel

theorem arows6779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6779 = true := by
  rw [show D2M8K2.u6779 = KTree.node D2M8K2.u6715 (nat_lit 14378160) (nat_lit 3521033207) (nat_lit 0) D2M8K2.u6778 from rfl, allE_node, arows6715, irow6779, arows6778]
  all_goals rfl

theorem atot6779 : totK PD2M8K2 D2M8K2.u6779 = [3982102962798, 22684090442278, 44638628953029, 34432044838134, 8633703391206, 585415674553, 6115358396, 0] := by
  rw [show D2M8K2.u6779 = KTree.node D2M8K2.u6715 (nat_lit 14378160) (nat_lit 3521033207) (nat_lit 0) D2M8K2.u6778 from rfl, totK_node, atot6715, atot6778]
  decide +kernel

theorem arows6906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6906 = true := by
  rw [show D2M8K2.u6906 = KTree.node D2M8K2.u6842 (nat_lit 14576049) (nat_lit 1479885761) (nat_lit 0) D2M8K2.u6905 from rfl, allE_node, arows6842, irow6906, arows6905]
  all_goals rfl

theorem atot6906 : totK PD2M8K2 D2M8K2.u6906 = [5809651733376, 29009642459861, 48197269373294, 28053271340749, 4099850297204, 98882226138, 0, 0] := by
  rw [show D2M8K2.u6906 = KTree.node D2M8K2.u6842 (nat_lit 14576049) (nat_lit 1479885761) (nat_lit 0) D2M8K2.u6905 from rfl, totK_node, atot6842, atot6905]
  decide +kernel

theorem arows7034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7034 = true := by
  rw [show D2M8K2.u7034 = KTree.node D2M8K2.u6970 (nat_lit 14789835) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u7033 from rfl, allE_node, arows6970, irow7034, arows7033]
  all_goals rfl

theorem atot7034 : totK PD2M8K2 D2M8K2.u7034 = [0, 8541303958364, 37275921629977, 49079798346622, 18324019809766, 1388582647836, 15323049608, 0] := by
  rw [show D2M8K2.u7034 = KTree.node D2M8K2.u6970 (nat_lit 14789835) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u7033 from rfl, totK_node, atot6970, atot7033]
  decide +kernel

theorem arows7161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7161 = true := by
  rw [show D2M8K2.u7161 = KTree.node D2M8K2.u7097 (nat_lit 15034866) (nat_lit 3350762892) (nat_lit 0) D2M8K2.u7160 from rfl, allE_node, arows7097, irow7161, arows7160]
  all_goals rfl

theorem atot7161 : totK PD2M8K2 D2M8K2.u7161 = [0, 7757745427395, 34923348995618, 48713293212377, 20635004959420, 2229850876395, 53920784975, 0] := by
  rw [show D2M8K2.u7161 = KTree.node D2M8K2.u7097 (nat_lit 15034866) (nat_lit 3350762892) (nat_lit 0) D2M8K2.u7160 from rfl, totK_node, atot7097, atot7160]
  decide +kernel

theorem arows7291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7291 = true := by
  rw [show D2M8K2.u7291 = KTree.node D2M8K2.u7227 (nat_lit 15201197) (nat_lit 2115381183) (nat_lit 0) D2M8K2.u7290 from rfl, allE_node, arows7227, irow7291, arows7290]
  all_goals rfl

theorem atot7291 : totK PD2M8K2 D2M8K2.u7291 = [0, 1988996583632, 19072744540798, 48337705845312, 37879267855799, 6862757902134, 295284268930, 1369150432] := by
  rw [show D2M8K2.u7291 = KTree.node D2M8K2.u7227 (nat_lit 15201197) (nat_lit 2115381183) (nat_lit 0) D2M8K2.u7290 from rfl, totK_node, atot7227, atot7290]
  decide +kernel

theorem arows7418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7418 = true := by
  rw [show D2M8K2.u7418 = KTree.node D2M8K2.u7354 (nat_lit 15526798) (nat_lit 3785603409) (nat_lit 0) D2M8K2.u7417 from rfl, allE_node, arows7354, irow7418, arows7417]
  all_goals rfl

theorem atot7418 : totK PD2M8K2 D2M8K2.u7418 = [0, 7544135010171, 33285988002532, 47585549061993, 23838388088968, 3404555854814, 101744679279, 0] := by
  rw [show D2M8K2.u7418 = KTree.node D2M8K2.u7354 (nat_lit 15526798) (nat_lit 3785603409) (nat_lit 0) D2M8K2.u7417 from rfl, totK_node, atot7354, atot7417]
  decide +kernel

theorem arows7546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7546 = true := by
  rw [show D2M8K2.u7546 = KTree.node D2M8K2.u7482 (nat_lit 15939781) (nat_lit 1318554817) (nat_lit 0) D2M8K2.u7545 from rfl, allE_node, arows7482, irow7546, arows7545]
  all_goals rfl

theorem atot7546 : totK PD2M8K2 D2M8K2.u7546 = [0, 7142682648244, 33317189329941, 48947796205995, 23120467641713, 2858291329210, 68362508654, 0] := by
  rw [show D2M8K2.u7546 = KTree.node D2M8K2.u7482 (nat_lit 15939781) (nat_lit 1318554817) (nat_lit 0) D2M8K2.u7545 from rfl, totK_node, atot7482, atot7545]
  decide +kernel

theorem arows7673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7673 = true := by
  rw [show D2M8K2.u7673 = KTree.node D2M8K2.u7609 (nat_lit 16133691) (nat_lit 2666739670) (nat_lit 0) D2M8K2.u7672 from rfl, allE_node, arows7609, irow7673, arows7672]
  all_goals rfl

theorem atot7673 : totK PD2M8K2 D2M8K2.u7673 = [0, 5323537543909, 27386273925240, 47195968637514, 29096976665763, 5278805712546, 254206879517, 1275377855] := by
  rw [show D2M8K2.u7673 = KTree.node D2M8K2.u7609 (nat_lit 16133691) (nat_lit 2666739670) (nat_lit 0) D2M8K2.u7672 from rfl, totK_node, atot7609, atot7672]
  decide +kernel

theorem arows7802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7802 = true := by
  rw [show D2M8K2.u7802 = KTree.node D2M8K2.u7738 (nat_lit 16350418) (nat_lit 2678429692) (nat_lit 0) D2M8K2.u7801 from rfl, allE_node, arows7738, irow7802, arows7801]
  all_goals rfl

theorem atot7802 : totK PD2M8K2 D2M8K2.u7802 = [0, 1973854997411, 16568842879293, 42513768976086, 39848714080609, 12253848342084, 1143435108982, 24680175954] := by
  rw [show D2M8K2.u7802 = KTree.node D2M8K2.u7738 (nat_lit 16350418) (nat_lit 2678429692) (nat_lit 0) D2M8K2.u7801 from rfl, totK_node, atot7738, atot7801]
  decide +kernel

theorem arows7929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7929 = true := by
  rw [show D2M8K2.u7929 = KTree.node D2M8K2.u7865 (nat_lit 17031276) (nat_lit 3199421365) (nat_lit 0) D2M8K2.u7928 from rfl, allE_node, arows7865, irow7929, arows7928]
  all_goals rfl

theorem atot7929 : totK PD2M8K2 D2M8K2.u7929 = [0, 7788801068466, 34829868621458, 48795830528092, 21466672434613, 2331193803235, 47559907311, 0] := by
  rw [show D2M8K2.u7929 = KTree.node D2M8K2.u7865 (nat_lit 17031276) (nat_lit 3199421365) (nat_lit 0) D2M8K2.u7928 from rfl, totK_node, atot7865, atot7928]
  decide +kernel

theorem arows8057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8057 = true := by
  rw [show D2M8K2.u8057 = KTree.node D2M8K2.u7993 (nat_lit 17268322) (nat_lit 3788402485) (nat_lit 0) D2M8K2.u8056 from rfl, allE_node, arows7993, irow8057, arows8056]
  all_goals rfl

theorem atot8057 : totK PD2M8K2 D2M8K2.u8057 = [0, 1978604257116, 17514047381759, 45216475212765, 39652047942516, 9356379376161, 564468916607, 7324389265] := by
  rw [show D2M8K2.u8057 = KTree.node D2M8K2.u7993 (nat_lit 17268322) (nat_lit 3788402485) (nat_lit 0) D2M8K2.u8056 from rfl, totK_node, atot7993, atot8056]
  decide +kernel

theorem arows8184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8184 = true := by
  rw [show D2M8K2.u8184 = KTree.node D2M8K2.u8120 (nat_lit 17511009) (nat_lit 1847926262) (nat_lit 0) D2M8K2.u8183 from rfl, allE_node, arows8120, irow8184, arows8183]
  all_goals rfl

theorem atot8184 : totK PD2M8K2 D2M8K2.u8184 = [0, 7133263233784, 33102041686329, 48982854063506, 23398943078780, 2886329468564, 72707810089, 0] := by
  rw [show D2M8K2.u8184 = KTree.node D2M8K2.u8120 (nat_lit 17511009) (nat_lit 1847926262) (nat_lit 0) D2M8K2.u8183 from rfl, totK_node, atot8120, atot8183]
  decide +kernel

theorem arows8317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8317 = true := by
  rw [show D2M8K2.u8317 = KTree.node D2M8K2.u8253 (nat_lit 18007155) (nat_lit 2986366710) (nat_lit 0) D2M8K2.u8316 from rfl, allE_node, arows8253, irow8317, arows8316]
  all_goals rfl

theorem atot8317 : totK PD2M8K2 D2M8K2.u8317 = [6356032396595, 28791335208604, 43389562327674, 26580850955805, 8361074506951, 1076745638270, 32872698681, 0] := by
  rw [show D2M8K2.u8317 = KTree.node D2M8K2.u8253 (nat_lit 18007155) (nat_lit 2986366710) (nat_lit 0) D2M8K2.u8316 from rfl, totK_node, atot8253, atot8316]
  decide +kernel

theorem arows8444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8444 = true := by
  rw [show D2M8K2.u8444 = KTree.node D2M8K2.u8380 (nat_lit 18163419) (nat_lit 3682708789) (nat_lit 0) D2M8K2.u8443 from rfl, allE_node, arows8380, irow8444, arows8443]
  all_goals rfl

theorem atot8444 : totK PD2M8K2 D2M8K2.u8444 = [3390978368857, 21556697346662, 45862096143343, 35632856345639, 7624447493678, 401245770968, 1369150432, 0] := by
  rw [show D2M8K2.u8444 = KTree.node D2M8K2.u8380 (nat_lit 18163419) (nat_lit 3682708789) (nat_lit 0) D2M8K2.u8443 from rfl, totK_node, atot8380, atot8443]
  decide +kernel

theorem arows8572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8572 = true := by
  rw [show D2M8K2.u8572 = KTree.node D2M8K2.u8508 (nat_lit 18479932) (nat_lit 3942085155) (nat_lit 0) D2M8K2.u8571 from rfl, allE_node, arows8508, irow8572, arows8571]
  all_goals rfl

theorem atot8572 : totK PD2M8K2 D2M8K2.u8572 = [5405340279044, 27295333256559, 47066398153363, 30325945332822, 5349351770816, 169176055544, 0, 0] := by
  rw [show D2M8K2.u8572 = KTree.node D2M8K2.u8508 (nat_lit 18479932) (nat_lit 3942085155) (nat_lit 0) D2M8K2.u8571 from rfl, totK_node, atot8508, atot8571]
  decide +kernel

theorem arows8699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8699 = true := by
  rw [show D2M8K2.u8699 = KTree.node D2M8K2.u8635 (nat_lit 18630349) (nat_lit 1189397663) (nat_lit 0) D2M8K2.u8698 from rfl, allE_node, arows8635, irow8699, arows8698]
  all_goals rfl

theorem atot8699 : totK PD2M8K2 D2M8K2.u8699 = [4404006080278, 23887879230959, 43968273329326, 31825424435306, 9823783783576, 1312123021063, 48508304344, 0] := by
  rw [show D2M8K2.u8699 = KTree.node D2M8K2.u8635 (nat_lit 18630349) (nat_lit 1189397663) (nat_lit 0) D2M8K2.u8698 from rfl, totK_node, atot8635, atot8698]
  decide +kernel

theorem arows8828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8828 = true := by
  rw [show D2M8K2.u8828 = KTree.node D2M8K2.u8764 (nat_lit 18825435) (nat_lit 3733231558) (nat_lit 0) D2M8K2.u8827 from rfl, allE_node, arows8764, irow8828, arows8827]
  all_goals rfl

theorem atot8828 : totK PD2M8K2 D2M8K2.u8828 = [0, 7691612035730, 34998437342383, 49081997417526, 21318129355163, 2059101343094, 26396180106, 0] := by
  rw [show D2M8K2.u8828 = KTree.node D2M8K2.u8764 (nat_lit 18825435) (nat_lit 3733231558) (nat_lit 0) D2M8K2.u8827 from rfl, totK_node, atot8764, atot8827]
  decide +kernel

theorem arows8955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8955 = true := by
  rw [show D2M8K2.u8955 = KTree.node D2M8K2.u8891 (nat_lit 19482041) (nat_lit 1121286751) (nat_lit 0) D2M8K2.u8954 from rfl, allE_node, arows8891, irow8955, arows8954]
  all_goals rfl

theorem atot8955 : totK PD2M8K2 D2M8K2.u8955 = [7827715727631, 33837934456044, 46691196729673, 22503843908025, 4024122343153, 354054005173, 9533751846, 0] := by
  rw [show D2M8K2.u8955 = KTree.node D2M8K2.u8891 (nat_lit 19482041) (nat_lit 1121286751) (nat_lit 0) D2M8K2.u8954 from rfl, totK_node, atot8891, atot8954]
  decide +kernel

theorem arows9083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9083 = true := by
  rw [show D2M8K2.u9083 = KTree.node D2M8K2.u9019 (nat_lit 19670024) (nat_lit 3206865775) (nat_lit 0) D2M8K2.u9082 from rfl, allE_node, arows9019, irow9083, arows9082]
  all_goals rfl

theorem atot9083 : totK PD2M8K2 D2M8K2.u9083 = [2374551643528, 18763787499631, 45405836377536, 38725586108248, 9184291753645, 431261957727, 1310517177, 0] := by
  rw [show D2M8K2.u9083 = KTree.node D2M8K2.u9019 (nat_lit 19670024) (nat_lit 3206865775) (nat_lit 0) D2M8K2.u9082 from rfl, totK_node, atot9019, atot9082]
  decide +kernel

theorem arows9210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9210 = true := by
  rw [show D2M8K2.u9210 = KTree.node D2M8K2.u9146 (nat_lit 19885547) (nat_lit 2940743118) (nat_lit 0) D2M8K2.u9209 from rfl, allE_node, arows9146, irow9210, arows9209]
  all_goals rfl

theorem atot9210 : totK PD2M8K2 D2M8K2.u9210 = [3972055978459, 21351701326593, 41640359113206, 35044220545711, 11455184554350, 1111313525715, 25006391237, 0] := by
  rw [show D2M8K2.u9210 = KTree.node D2M8K2.u9146 (nat_lit 19885547) (nat_lit 2940743118) (nat_lit 0) D2M8K2.u9209 from rfl, totK_node, atot9146, atot9209]
  decide +kernel

end QECKChecks.D2M8K2
