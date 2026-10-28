import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A18

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows12830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12830 = true := by
  rw [show D2M8K2.u12830 = KTree.node D2M8K2.u12828 (nat_lit 27546392) (nat_lit 3704549570) (nat_lit 0) D2M8K2.u12829 from rfl, allE_node, arows12828, irow12830, arows12829]
  all_goals rfl

theorem atot12830 : totK PD2M8K2 D2M8K2.u12830 = [0, 413897510433, 1433037450793, 1399027135008, 318124515798, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12830 = KTree.node D2M8K2.u12828 (nat_lit 27546392) (nat_lit 3704549570) (nat_lit 0) D2M8K2.u12829 from rfl, totK_node, atot12828, atot12829]
  decide +kernel

theorem arows12833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12833 = true := by
  rw [show D2M8K2.u12833 = KTree.node D2M8K2.u12831 (nat_lit 27549775) (nat_lit 1806268091) (nat_lit 0) D2M8K2.u12832 from rfl, allE_node, arows12831, irow12833, arows12832]
  all_goals rfl

theorem atot12833 : totK PD2M8K2 D2M8K2.u12833 = [0, 386044434758, 1410184734323, 1437317425014, 340274999335, 13250685261, 0, 0] := by
  rw [show D2M8K2.u12833 = KTree.node D2M8K2.u12831 (nat_lit 27549775) (nat_lit 1806268091) (nat_lit 0) D2M8K2.u12832 from rfl, totK_node, atot12831, atot12832]
  decide +kernel

theorem arows12837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12837 = true := by
  rw [show D2M8K2.u12837 = KTree.node D2M8K2.u12835 (nat_lit 27553062) (nat_lit 3710900557) (nat_lit 0) D2M8K2.u12836 from rfl, allE_node, arows12835, irow12837, arows12836]
  all_goals rfl

theorem atot12837 : totK PD2M8K2 D2M8K2.u12837 = [0, 301076925428, 1400353143085, 1596457660012, 331679372104, 6350335412, 0, 0] := by
  rw [show D2M8K2.u12837 = KTree.node D2M8K2.u12835 (nat_lit 27553062) (nat_lit 3710900557) (nat_lit 0) D2M8K2.u12836 from rfl, totK_node, atot12835, atot12836]
  decide +kernel

theorem arows12840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12840 = true := by
  rw [show D2M8K2.u12840 = KTree.node D2M8K2.u12838 (nat_lit 27562280) (nat_lit 3883430745) (nat_lit 0) D2M8K2.u12839 from rfl, allE_node, arows12838, irow12840, arows12839]
  all_goals rfl

theorem atot12840 : totK PD2M8K2 D2M8K2.u12840 = [0, 0, 712902350603, 1871429672588, 930516484729, 68426116446, 0, 0] := by
  rw [show D2M8K2.u12840 = KTree.node D2M8K2.u12838 (nat_lit 27562280) (nat_lit 3883430745) (nat_lit 0) D2M8K2.u12839 from rfl, totK_node, atot12838, atot12839]
  decide +kernel

theorem arows12845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12845 = true := by
  rw [show D2M8K2.u12845 = KTree.node D2M8K2.u12843 (nat_lit 27568628) (nat_lit 3645906964) (nat_lit 0) D2M8K2.u12844 from rfl, allE_node, arows12843, irow12845, arows12844]
  all_goals rfl

theorem atot12845 : totK PD2M8K2 D2M8K2.u12845 = [0, 0, 749002719656, 1904136589392, 913690114887, 50894449056, 0, 0] := by
  rw [show D2M8K2.u12845 = KTree.node D2M8K2.u12843 (nat_lit 27568628) (nat_lit 3645906964) (nat_lit 0) D2M8K2.u12844 from rfl, totK_node, atot12843, atot12844]
  decide +kernel

theorem arows12848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12848 = true := by
  rw [show D2M8K2.u12848 = KTree.node D2M8K2.u12846 (nat_lit 27573163) (nat_lit 1802348857) (nat_lit 0) D2M8K2.u12847 from rfl, allE_node, arows12846, irow12848, arows12847]
  all_goals rfl

theorem atot12848 : totK PD2M8K2 D2M8K2.u12848 = [0, 22713249043, 472339672058, 1551881635929, 1274110287158, 223632176795, 4977114383, 0] := by
  rw [show D2M8K2.u12848 = KTree.node D2M8K2.u12846 (nat_lit 27573163) (nat_lit 1802348857) (nat_lit 0) D2M8K2.u12847 from rfl, totK_node, atot12846, atot12847]
  decide +kernel

theorem arows12852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12852 = true := by
  rw [show D2M8K2.u12852 = KTree.node D2M8K2.u12850 (nat_lit 27583854) (nat_lit 4025775211) (nat_lit 0) D2M8K2.u12851 from rfl, allE_node, arows12850, irow12852, arows12851]
  all_goals rfl

theorem atot12852 : totK PD2M8K2 D2M8K2.u12852 = [0, 403150472278, 1401401972061, 1375282435303, 431122433337, 29375735501, 0, 0] := by
  rw [show D2M8K2.u12852 = KTree.node D2M8K2.u12850 (nat_lit 27583854) (nat_lit 4025775211) (nat_lit 0) D2M8K2.u12851 from rfl, totK_node, atot12850, atot12851]
  decide +kernel

theorem arows12855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12855 = true := by
  rw [show D2M8K2.u12855 = KTree.node D2M8K2.u12853 (nat_lit 27586624) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u12854 from rfl, allE_node, arows12853, irow12855, arows12854]
  all_goals rfl

theorem atot12855 : totK PD2M8K2 D2M8K2.u12855 = [0, 403459321782, 1380325568715, 1412708952678, 404912162419, 16406310743, 0, 0] := by
  rw [show D2M8K2.u12855 = KTree.node D2M8K2.u12853 (nat_lit 27586624) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u12854 from rfl, totK_node, atot12853, atot12854]
  decide +kernel

theorem arows12862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12862 = true := by
  rw [show D2M8K2.u12862 = KTree.node D2M8K2.u12860 (nat_lit 27590410) (nat_lit 2271910318) (nat_lit 0) D2M8K2.u12861 from rfl, allE_node, arows12860, irow12862, arows12861]
  all_goals rfl

theorem atot12862 : totK PD2M8K2 D2M8K2.u12862 = [0, 403717775972, 1454260640128, 1428317369252, 321221479380, 9553713074, 0, 0] := by
  rw [show D2M8K2.u12862 = KTree.node D2M8K2.u12860 (nat_lit 27590410) (nat_lit 2271910318) (nat_lit 0) D2M8K2.u12861 from rfl, totK_node, atot12860, atot12861]
  decide +kernel

theorem arows12865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12865 = true := by
  rw [show D2M8K2.u12865 = KTree.node D2M8K2.u12863 (nat_lit 27597056) (nat_lit 3442270606) (nat_lit 0) D2M8K2.u12864 from rfl, allE_node, arows12863, irow12865, arows12864]
  all_goals rfl

theorem atot12865 : totK PD2M8K2 D2M8K2.u12865 = [0, 429020973273, 1476348582130, 1416018883675, 300240675225, 6302237838, 0, 0] := by
  rw [show D2M8K2.u12865 = KTree.node D2M8K2.u12863 (nat_lit 27597056) (nat_lit 3442270606) (nat_lit 0) D2M8K2.u12864 from rfl, totK_node, atot12863, atot12864]
  decide +kernel

theorem arows12869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12869 = true := by
  rw [show D2M8K2.u12869 = KTree.node D2M8K2.u12867 (nat_lit 27603912) (nat_lit 3170615684) (nat_lit 0) D2M8K2.u12868 from rfl, allE_node, arows12867, irow12869, arows12868]
  all_goals rfl

theorem atot12869 : totK PD2M8K2 D2M8K2.u12869 = [0, 0, 762865643325, 1885467643855, 934656575857, 63943537638, 0, 0] := by
  rw [show D2M8K2.u12869 = KTree.node D2M8K2.u12867 (nat_lit 27603912) (nat_lit 3170615684) (nat_lit 0) D2M8K2.u12868 from rfl, totK_node, atot12867, atot12868]
  decide +kernel

theorem arows12872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12872 = true := by
  rw [show D2M8K2.u12872 = KTree.node D2M8K2.u12870 (nat_lit 27608845) (nat_lit 1277677813) (nat_lit 0) D2M8K2.u12871 from rfl, allE_node, arows12870, irow12872, arows12871]
  all_goals rfl

theorem atot12872 : totK PD2M8K2 D2M8K2.u12872 = [0, 0, 493253798195, 1643569524803, 1294674659616, 170686477909, 1435164049, 0] := by
  rw [show D2M8K2.u12872 = KTree.node D2M8K2.u12870 (nat_lit 27608845) (nat_lit 1277677813) (nat_lit 0) D2M8K2.u12871 from rfl, totK_node, atot12870, atot12871]
  decide +kernel

theorem arows12877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12877 = true := by
  rw [show D2M8K2.u12877 = KTree.node D2M8K2.u12875 (nat_lit 27613170) (nat_lit 3262518928) (nat_lit 0) D2M8K2.u12876 from rfl, allE_node, arows12875, irow12877, arows12876]
  all_goals rfl

theorem atot12877 : totK PD2M8K2 D2M8K2.u12877 = [0, 0, 490350791078, 1691044892889, 1269282528063, 159051399279, 1444560764, 0] := by
  rw [show D2M8K2.u12877 = KTree.node D2M8K2.u12875 (nat_lit 27613170) (nat_lit 3262518928) (nat_lit 0) D2M8K2.u12876 from rfl, totK_node, atot12875, atot12876]
  decide +kernel

theorem arows12880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12880 = true := by
  rw [show D2M8K2.u12880 = KTree.node D2M8K2.u12878 (nat_lit 27620202) (nat_lit 3797215817) (nat_lit 0) D2M8K2.u12879 from rfl, allE_node, arows12878, irow12880, arows12879]
  all_goals rfl

theorem atot12880 : totK PD2M8K2 D2M8K2.u12880 = [0, 347773466219, 946592115133, 1047195504805, 971087489831, 263558453809, 10297110227, 0] := by
  rw [show D2M8K2.u12880 = KTree.node D2M8K2.u12878 (nat_lit 27620202) (nat_lit 3797215817) (nat_lit 0) D2M8K2.u12879 from rfl, totK_node, atot12878, atot12879]
  decide +kernel

theorem arows12884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12884 = true := by
  rw [show D2M8K2.u12884 = KTree.node D2M8K2.u12882 (nat_lit 27872478) (nat_lit 3894591339) (nat_lit 0) D2M8K2.u12883 from rfl, allE_node, arows12882, irow12884, arows12883]
  all_goals rfl

theorem atot12884 : totK PD2M8K2 D2M8K2.u12884 = [0, 461598064778, 1593677899399, 1360307290846, 190223183585, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12884 = KTree.node D2M8K2.u12882 (nat_lit 27872478) (nat_lit 3894591339) (nat_lit 0) D2M8K2.u12883 from rfl, totK_node, atot12882, atot12883]
  decide +kernel

theorem arows12887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12887 = true := by
  rw [show D2M8K2.u12887 = KTree.node D2M8K2.u12885 (nat_lit 27879291) (nat_lit 3691279300) (nat_lit 0) D2M8K2.u12886 from rfl, allE_node, arows12885, irow12887, arows12886]
  all_goals rfl

theorem atot12887 : totK PD2M8K2 D2M8K2.u12887 = [0, 372041628191, 1444470165792, 1422153933426, 316731552808, 13049727234, 0, 0] := by
  rw [show D2M8K2.u12887 = KTree.node D2M8K2.u12885 (nat_lit 27879291) (nat_lit 3691279300) (nat_lit 0) D2M8K2.u12886 from rfl, totK_node, atot12885, atot12886]
  decide +kernel

theorem arows12893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12893 = true := by
  rw [show D2M8K2.u12893 = KTree.node D2M8K2.u12891 (nat_lit 27883381) (nat_lit 1082743843) (nat_lit 0) D2M8K2.u12892 from rfl, allE_node, arows12891, irow12893, arows12892]
  all_goals rfl

theorem atot12893 : totK PD2M8K2 D2M8K2.u12893 = [0, 411646493394, 1418130057696, 1371003884130, 331547883492, 14347190365, 0, 0] := by
  rw [show D2M8K2.u12893 = KTree.node D2M8K2.u12891 (nat_lit 27883381) (nat_lit 1082743843) (nat_lit 0) D2M8K2.u12892 from rfl, totK_node, atot12891, atot12892]
  decide +kernel

theorem arows12896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12896 = true := by
  rw [show D2M8K2.u12896 = KTree.node D2M8K2.u12894 (nat_lit 27887026) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u12895 from rfl, allE_node, arows12894, irow12896, arows12895]
  all_goals rfl

theorem atot12896 : totK PD2M8K2 D2M8K2.u12896 = [0, 382717135235, 1448496590776, 1465126488922, 295581848143, 5152749158, 0, 0] := by
  rw [show D2M8K2.u12896 = KTree.node D2M8K2.u12894 (nat_lit 27887026) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u12895 from rfl, totK_node, atot12894, atot12895]
  decide +kernel

theorem arows12900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12900 = true := by
  rw [show D2M8K2.u12900 = KTree.node D2M8K2.u12898 (nat_lit 27890750) (nat_lit 1642756821) (nat_lit 0) D2M8K2.u12899 from rfl, allE_node, arows12898, irow12900, arows12899]
  all_goals rfl

theorem atot12900 : totK PD2M8K2 D2M8K2.u12900 = [0, 0, 660902140401, 1761372636861, 964806684795, 115867687581, 1369150432, 0] := by
  rw [show D2M8K2.u12900 = KTree.node D2M8K2.u12898 (nat_lit 27890750) (nat_lit 1642756821) (nat_lit 0) D2M8K2.u12899 from rfl, totK_node, atot12898, atot12899]
  decide +kernel

theorem arows12903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12903 = true := by
  rw [show D2M8K2.u12903 = KTree.node D2M8K2.u12901 (nat_lit 27897614) (nat_lit 3052268572) (nat_lit 0) D2M8K2.u12902 from rfl, allE_node, arows12901, irow12903, arows12902]
  all_goals rfl

theorem atot12903 : totK PD2M8K2 D2M8K2.u12903 = [0, 0, 612772575826, 1806487656091, 1021950906463, 76989019656, 0, 0] := by
  rw [show D2M8K2.u12903 = KTree.node D2M8K2.u12901 (nat_lit 27897614) (nat_lit 3052268572) (nat_lit 0) D2M8K2.u12902 from rfl, totK_node, atot12901, atot12902]
  decide +kernel

theorem arows12908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12908 = true := by
  rw [show D2M8K2.u12908 = KTree.node D2M8K2.u12906 (nat_lit 27904589) (nat_lit 1889139417) (nat_lit 0) D2M8K2.u12907 from rfl, allE_node, arows12906, irow12908, arows12907]
  all_goals rfl

theorem atot12908 : totK PD2M8K2 D2M8K2.u12908 = [0, 0, 771962983184, 1929525522515, 821301982105, 32313287019, 0, 0] := by
  rw [show D2M8K2.u12908 = KTree.node D2M8K2.u12906 (nat_lit 27904589) (nat_lit 1889139417) (nat_lit 0) D2M8K2.u12907 from rfl, totK_node, atot12906, atot12907]
  decide +kernel

theorem arows12911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12911 = true := by
  rw [show D2M8K2.u12911 = KTree.node D2M8K2.u12909 (nat_lit 27914994) (nat_lit 3355619690) (nat_lit 0) D2M8K2.u12910 from rfl, allE_node, arows12909, irow12911, arows12910]
  all_goals rfl

theorem atot12911 : totK PD2M8K2 D2M8K2.u12911 = [0, 442546040397, 1398801318402, 1334448522365, 442680401371, 34394339720, 0, 0] := by
  rw [show D2M8K2.u12911 = KTree.node D2M8K2.u12909 (nat_lit 27914994) (nat_lit 3355619690) (nat_lit 0) D2M8K2.u12910 from rfl, totK_node, atot12909, atot12910]
  decide +kernel

theorem arows12915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12915 = true := by
  rw [show D2M8K2.u12915 = KTree.node D2M8K2.u12913 (nat_lit 27917718) (nat_lit 2784550921) (nat_lit 0) D2M8K2.u12914 from rfl, allE_node, arows12913, irow12915, arows12914]
  all_goals rfl

theorem atot12915 : totK PD2M8K2 D2M8K2.u12915 = [0, 425015570430, 1384433326865, 1380802256448, 426691225563, 16208961603, 0, 0] := by
  rw [show D2M8K2.u12915 = KTree.node D2M8K2.u12913 (nat_lit 27917718) (nat_lit 2784550921) (nat_lit 0) D2M8K2.u12914 from rfl, totK_node, atot12913, atot12914]
  decide +kernel

theorem arows12918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12918 = true := by
  rw [show D2M8K2.u12918 = KTree.node D2M8K2.u12916 (nat_lit 27921356) (nat_lit 3740007784) (nat_lit 0) D2M8K2.u12917 from rfl, allE_node, arows12916, irow12918, arows12917]
  all_goals rfl

theorem atot12918 : totK PD2M8K2 D2M8K2.u12918 = [0, 331426027796, 1390349523053, 1539501470432, 358583217507, 13036865798, 0, 0] := by
  rw [show D2M8K2.u12918 = KTree.node D2M8K2.u12916 (nat_lit 27921356) (nat_lit 3740007784) (nat_lit 0) D2M8K2.u12917 from rfl, totK_node, atot12916, atot12917]
  decide +kernel

theorem arows12926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12926 = true := by
  rw [show D2M8K2.u12926 = KTree.node D2M8K2.u12924 (nat_lit 27925049) (nat_lit 1177676325) (nat_lit 0) D2M8K2.u12925 from rfl, allE_node, arows12924, irow12926, arows12925]
  all_goals rfl

theorem atot12926 : totK PD2M8K2 D2M8K2.u12926 = [0, 414266647590, 1468743025175, 1421444081033, 307002340544, 10945537955, 0, 0] := by
  rw [show D2M8K2.u12926 = KTree.node D2M8K2.u12924 (nat_lit 27925049) (nat_lit 1177676325) (nat_lit 0) D2M8K2.u12925 from rfl, totK_node, atot12924, atot12925]
  decide +kernel

theorem arows12929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12929 = true := by
  rw [show D2M8K2.u12929 = KTree.node D2M8K2.u12927 (nat_lit 27928633) (nat_lit 1462304901) (nat_lit 0) D2M8K2.u12928 from rfl, allE_node, arows12927, irow12929, arows12928]
  all_goals rfl

theorem atot12929 : totK PD2M8K2 D2M8K2.u12929 = [0, 387063971590, 1481484680669, 1482797188523, 281848203071, 5148576759, 0, 0] := by
  rw [show D2M8K2.u12929 = KTree.node D2M8K2.u12927 (nat_lit 27928633) (nat_lit 1462304901) (nat_lit 0) D2M8K2.u12928 from rfl, totK_node, atot12927, atot12928]
  decide +kernel

theorem arows12933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12933 = true := by
  rw [show D2M8K2.u12933 = KTree.node D2M8K2.u12931 (nat_lit 27935684) (nat_lit 3259550594) (nat_lit 0) D2M8K2.u12932 from rfl, allE_node, arows12931, irow12933, arows12932]
  all_goals rfl

theorem atot12933 : totK PD2M8K2 D2M8K2.u12933 = [0, 0, 598337008240, 1712598020081, 1135509926955, 188844754720, 9929822194, 0] := by
  rw [show D2M8K2.u12933 = KTree.node D2M8K2.u12931 (nat_lit 27935684) (nat_lit 3259550594) (nat_lit 0) D2M8K2.u12932 from rfl, totK_node, atot12931, atot12932]
  decide +kernel

theorem arows12936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12936 = true := by
  rw [show D2M8K2.u12936 = KTree.node D2M8K2.u12934 (nat_lit 27938819) (nat_lit 2598698545) (nat_lit 0) D2M8K2.u12935 from rfl, allE_node, arows12934, irow12936, arows12935]
  all_goals rfl

theorem atot12936 : totK PD2M8K2 D2M8K2.u12936 = [0, 0, 423427292429, 1544639614986, 1380041654893, 265935717490, 5159287072, 0] := by
  rw [show D2M8K2.u12936 = KTree.node D2M8K2.u12934 (nat_lit 27938819) (nat_lit 2598698545) (nat_lit 0) D2M8K2.u12935 from rfl, totK_node, atot12934, atot12935]
  decide +kernel

theorem arows12941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12941 = true := by
  rw [show D2M8K2.u12941 = KTree.node D2M8K2.u12939 (nat_lit 27942853) (nat_lit 1188599784) (nat_lit 0) D2M8K2.u12940 from rfl, allE_node, arows12939, irow12941, arows12940]
  all_goals rfl

theorem atot12941 : totK PD2M8K2 D2M8K2.u12941 = [0, 0, 554893743727, 1599770078490, 1251783345772, 229696470412, 5159868635, 0] := by
  rw [show D2M8K2.u12941 = KTree.node D2M8K2.u12939 (nat_lit 27942853) (nat_lit 1188599784) (nat_lit 0) D2M8K2.u12940 from rfl, totK_node, atot12939, atot12940]
  decide +kernel

theorem arows12944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12944 = true := by
  rw [show D2M8K2.u12944 = KTree.node D2M8K2.u12942 (nat_lit 27947853) (nat_lit 1441256101) (nat_lit 0) D2M8K2.u12943 from rfl, allE_node, arows12942, irow12944, arows12943]
  all_goals rfl

theorem atot12944 : totK PD2M8K2 D2M8K2.u12944 = [0, 0, 469364016440, 1634457054772, 1336920262894, 181750218523, 1415142070, 0] := by
  rw [show D2M8K2.u12944 = KTree.node D2M8K2.u12942 (nat_lit 27947853) (nat_lit 1441256101) (nat_lit 0) D2M8K2.u12943 from rfl, totK_node, atot12942, atot12943]
  decide +kernel

theorem arows12948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12948 = true := by
  rw [show D2M8K2.u12948 = KTree.node D2M8K2.u12946 (nat_lit 27953252) (nat_lit 3299040953) (nat_lit 0) D2M8K2.u12947 from rfl, allE_node, arows12946, irow12948, arows12947]
  all_goals rfl

theorem atot12948 : totK PD2M8K2 D2M8K2.u12948 = [0, 413201475250, 1433772841436, 1352940327943, 350477895701, 17586359405, 0, 0] := by
  rw [show D2M8K2.u12948 = KTree.node D2M8K2.u12946 (nat_lit 27953252) (nat_lit 3299040953) (nat_lit 0) D2M8K2.u12947 from rfl, totK_node, atot12946, atot12947]
  decide +kernel

theorem arows12951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12951 = true := by
  rw [show D2M8K2.u12951 = KTree.node D2M8K2.u12949 (nat_lit 27956814) (nat_lit 3688626829) (nat_lit 0) D2M8K2.u12950 from rfl, allE_node, arows12949, irow12951, arows12950]
  all_goals rfl

theorem atot12951 : totK PD2M8K2 D2M8K2.u12951 = [0, 423617078586, 1465221087700, 1370649831966, 360881342796, 25111704080, 0, 0] := by
  rw [show D2M8K2.u12951 = KTree.node D2M8K2.u12949 (nat_lit 27956814) (nat_lit 3688626829) (nat_lit 0) D2M8K2.u12950 from rfl, totK_node, atot12949, atot12950]
  decide +kernel

theorem arows12957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12957 = true := by
  rw [show D2M8K2.u12957 = KTree.node D2M8K2.u12955 (nat_lit 27959586) (nat_lit 3066571516) (nat_lit 0) D2M8K2.u12956 from rfl, allE_node, arows12955, irow12957, arows12956]
  all_goals rfl

theorem atot12957 : totK PD2M8K2 D2M8K2.u12957 = [0, 445926588316, 1418797665283, 1362178777299, 382194866442, 11944889650, 0, 0] := by
  rw [show D2M8K2.u12957 = KTree.node D2M8K2.u12955 (nat_lit 27959586) (nat_lit 3066571516) (nat_lit 0) D2M8K2.u12956 from rfl, totK_node, atot12955, atot12956]
  decide +kernel

theorem arows12960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12960 = true := by
  rw [show D2M8K2.u12960 = KTree.node D2M8K2.u12958 (nat_lit 27966332) (nat_lit 3338486187) (nat_lit 0) D2M8K2.u12959 from rfl, allE_node, arows12958, irow12960, arows12959]
  all_goals rfl

theorem atot12960 : totK PD2M8K2 D2M8K2.u12960 = [0, 420237879229, 1492647611439, 1392066324688, 287902705865, 11885407614, 0, 0] := by
  rw [show D2M8K2.u12960 = KTree.node D2M8K2.u12958 (nat_lit 27966332) (nat_lit 3338486187) (nat_lit 0) D2M8K2.u12959 from rfl, totK_node, atot12958, atot12959]
  decide +kernel

theorem arows12964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12964 = true := by
  rw [show D2M8K2.u12964 = KTree.node D2M8K2.u12962 (nat_lit 27969832) (nat_lit 3790668661) (nat_lit 0) D2M8K2.u12963 from rfl, allE_node, arows12962, irow12964, arows12963]
  all_goals rfl

theorem atot12964 : totK PD2M8K2 D2M8K2.u12964 = [0, 403955624301, 1452961443305, 1437874573976, 289137353983, 6249254262, 0, 0] := by
  rw [show D2M8K2.u12964 = KTree.node D2M8K2.u12962 (nat_lit 27969832) (nat_lit 3790668661) (nat_lit 0) D2M8K2.u12963 from rfl, totK_node, atot12962, atot12963]
  decide +kernel

theorem arows12967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12967 = true := by
  rw [show D2M8K2.u12967 = KTree.node D2M8K2.u12965 (nat_lit 27973451) (nat_lit 2895669219) (nat_lit 0) D2M8K2.u12966 from rfl, allE_node, arows12965, irow12967, arows12966]
  all_goals rfl

theorem atot12967 : totK PD2M8K2 D2M8K2.u12967 = [0, 0, 725099974703, 1843567555618, 876735298924, 56462151572, 0, 0] := by
  rw [show D2M8K2.u12967 = KTree.node D2M8K2.u12965 (nat_lit 27973451) (nat_lit 2895669219) (nat_lit 0) D2M8K2.u12966 from rfl, totK_node, atot12965, atot12966]
  decide +kernel

theorem arows12972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12972 = true := by
  rw [show D2M8K2.u12972 = KTree.node D2M8K2.u12970 (nat_lit 27977152) (nat_lit 3266424284) (nat_lit 0) D2M8K2.u12971 from rfl, allE_node, arows12970, irow12972, arows12971]
  all_goals rfl

theorem atot12972 : totK PD2M8K2 D2M8K2.u12972 = [0, 0, 597679672468, 1737567231449, 1121755312211, 123203855194, 1206465782, 0] := by
  rw [show D2M8K2.u12972 = KTree.node D2M8K2.u12970 (nat_lit 27977152) (nat_lit 3266424284) (nat_lit 0) D2M8K2.u12971 from rfl, totK_node, atot12970, atot12971]
  decide +kernel

theorem arows12975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12975 = true := by
  rw [show D2M8K2.u12975 = KTree.node D2M8K2.u12973 (nat_lit 27981668) (nat_lit 2464030655) (nat_lit 0) D2M8K2.u12974 from rfl, allE_node, arows12973, irow12975, arows12974]
  all_goals rfl

theorem atot12975 : totK PD2M8K2 D2M8K2.u12975 = [0, 0, 371206616091, 1454671019874, 1389872645699, 308337565304, 13016197374, 0] := by
  rw [show D2M8K2.u12975 = KTree.node D2M8K2.u12973 (nat_lit 27981668) (nat_lit 2464030655) (nat_lit 0) D2M8K2.u12974 from rfl, totK_node, atot12973, atot12974]
  decide +kernel

theorem arows12979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12979 = true := by
  rw [show D2M8K2.u12979 = KTree.node D2M8K2.u12977 (nat_lit 27988564) (nat_lit 3315028646) (nat_lit 0) D2M8K2.u12978 from rfl, allE_node, arows12977, irow12979, arows12978]
  all_goals rfl

theorem atot12979 : totK PD2M8K2 D2M8K2.u12979 = [0, 0, 485018543856, 1606127497988, 1236000050985, 183744303153, 4574395652, 0] := by
  rw [show D2M8K2.u12979 = KTree.node D2M8K2.u12977 (nat_lit 27988564) (nat_lit 3315028646) (nat_lit 0) D2M8K2.u12978 from rfl, totK_node, atot12977, atot12978]
  decide +kernel

theorem arows12982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12982 = true := by
  rw [show D2M8K2.u12982 = KTree.node D2M8K2.u12980 (nat_lit 28035746) (nat_lit 3712097273) (nat_lit 0) D2M8K2.u12981 from rfl, allE_node, arows12980, irow12982, arows12981]
  all_goals rfl

theorem atot12982 : totK PD2M8K2 D2M8K2.u12982 = [0, 407046338387, 1353524646693, 1333121158033, 442956245859, 23020291092, 0, 0] := by
  rw [show D2M8K2.u12982 = KTree.node D2M8K2.u12980 (nat_lit 28035746) (nat_lit 3712097273) (nat_lit 0) D2M8K2.u12981 from rfl, totK_node, atot12980, atot12981]
  decide +kernel

theorem arows12989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12989 = true := by
  rw [show D2M8K2.u12989 = KTree.node D2M8K2.u12987 (nat_lit 28039351) (nat_lit 1481295355) (nat_lit 0) D2M8K2.u12988 from rfl, allE_node, arows12987, irow12989, arows12988]
  all_goals rfl

theorem atot12989 : totK PD2M8K2 D2M8K2.u12989 = [0, 418327274476, 1516170412581, 1393729497542, 294759451510, 21156593246, 0, 0] := by
  rw [show D2M8K2.u12989 = KTree.node D2M8K2.u12987 (nat_lit 28039351) (nat_lit 1481295355) (nat_lit 0) D2M8K2.u12988 from rfl, totK_node, atot12987, atot12988]
  decide +kernel

theorem arows12992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12992 = true := by
  rw [show D2M8K2.u12992 = KTree.node D2M8K2.u12990 (nat_lit 28042209) (nat_lit 1707293039) (nat_lit 0) D2M8K2.u12991 from rfl, allE_node, arows12990, irow12992, arows12991]
  all_goals rfl

theorem atot12992 : totK PD2M8K2 D2M8K2.u12992 = [0, 425713103102, 1388261539561, 1367704904557, 425870180846, 14828424711, 0, 0] := by
  rw [show D2M8K2.u12992 = KTree.node D2M8K2.u12990 (nat_lit 28042209) (nat_lit 1707293039) (nat_lit 0) D2M8K2.u12991 from rfl, totK_node, atot12990, atot12991]
  decide +kernel

theorem arows12996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12996 = true := by
  rw [show D2M8K2.u12996 = KTree.node D2M8K2.u12994 (nat_lit 28045548) (nat_lit 3199526130) (nat_lit 0) D2M8K2.u12995 from rfl, allE_node, arows12994, irow12996, arows12995]
  all_goals rfl

theorem atot12996 : totK PD2M8K2 D2M8K2.u12996 = [0, 343350835224, 1369370906749, 1489289046389, 361379701878, 14247800626, 0, 0] := by
  rw [show D2M8K2.u12996 = KTree.node D2M8K2.u12994 (nat_lit 28045548) (nat_lit 3199526130) (nat_lit 0) D2M8K2.u12995 from rfl, totK_node, atot12994, atot12995]
  decide +kernel

theorem arows12999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12999 = true := by
  rw [show D2M8K2.u12999 = KTree.node D2M8K2.u12997 (nat_lit 28049376) (nat_lit 2642391937) (nat_lit 0) D2M8K2.u12998 from rfl, allE_node, arows12997, irow12999, arows12998]
  all_goals rfl

theorem atot12999 : totK PD2M8K2 D2M8K2.u12999 = [0, 439394674482, 1466532990496, 1370040672057, 314215049623, 13149116973, 0, 0] := by
  rw [show D2M8K2.u12999 = KTree.node D2M8K2.u12997 (nat_lit 28049376) (nat_lit 2642391937) (nat_lit 0) D2M8K2.u12998 from rfl, totK_node, atot12997, atot12998]
  decide +kernel

theorem arows13004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13004 = true := by
  rw [show D2M8K2.u13004 = KTree.node D2M8K2.u13002 (nat_lit 28056540) (nat_lit 3155185996) (nat_lit 0) D2M8K2.u13003 from rfl, allE_node, arows13002, irow13004, arows13003]
  all_goals rfl

theorem atot13004 : totK PD2M8K2 D2M8K2.u13004 = [0, 0, 755224133706, 1821441765590, 862939641587, 88101243217, 1138244013, 0] := by
  rw [show D2M8K2.u13004 = KTree.node D2M8K2.u13002 (nat_lit 28056540) (nat_lit 3155185996) (nat_lit 0) D2M8K2.u13003 from rfl, totK_node, atot13002, atot13003]
  decide +kernel

theorem arows13007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13007 = true := by
  rw [show D2M8K2.u13007 = KTree.node D2M8K2.u13005 (nat_lit 28060364) (nat_lit 3154044298) (nat_lit 0) D2M8K2.u13006 from rfl, allE_node, arows13005, irow13007, arows13006]
  all_goals rfl

theorem atot13007 : totK PD2M8K2 D2M8K2.u13007 = [0, 0, 663992097663, 1843911350926, 1031689391042, 78288439161, 0, 0] := by
  rw [show D2M8K2.u13007 = KTree.node D2M8K2.u13005 (nat_lit 28060364) (nat_lit 3154044298) (nat_lit 0) D2M8K2.u13006 from rfl, totK_node, atot13005, atot13006]
  decide +kernel

theorem arows13011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13011 = true := by
  rw [show D2M8K2.u13011 = KTree.node D2M8K2.u13009 (nat_lit 28066722) (nat_lit 3304450853) (nat_lit 0) D2M8K2.u13010 from rfl, allE_node, arows13009, irow13011, arows13010]
  all_goals rfl

theorem atot13011 : totK PD2M8K2 D2M8K2.u13011 = [0, 0, 728703376734, 1889079575142, 913852850419, 55480134631, 0, 0] := by
  rw [show D2M8K2.u13011 = KTree.node D2M8K2.u13009 (nat_lit 28066722) (nat_lit 3304450853) (nat_lit 0) D2M8K2.u13010 from rfl, totK_node, atot13009, atot13010]
  decide +kernel

theorem arows13014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13014 = true := by
  rw [show D2M8K2.u13014 = KTree.node D2M8K2.u13012 (nat_lit 28071946) (nat_lit 3229693309) (nat_lit 0) D2M8K2.u13013 from rfl, allE_node, arows13012, irow13014, arows13013]
  all_goals rfl

theorem atot13014 : totK PD2M8K2 D2M8K2.u13014 = [0, 234545227448, 755014081723, 1256017178677, 1070417279460, 208918136586, 4977114383, 0] := by
  rw [show D2M8K2.u13014 = KTree.node D2M8K2.u13012 (nat_lit 28071946) (nat_lit 3229693309) (nat_lit 0) D2M8K2.u13013 from rfl, totK_node, atot13012, atot13013]
  decide +kernel

theorem arows13020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13020 = true := by
  rw [show D2M8K2.u13020 = KTree.node D2M8K2.u13018 (nat_lit 28079437) (nat_lit 1384954955) (nat_lit 0) D2M8K2.u13019 from rfl, allE_node, arows13018, irow13020, arows13019]
  all_goals rfl

theorem atot13020 : totK PD2M8K2 D2M8K2.u13020 = [0, 463151285147, 1594041970042, 1370941678462, 185764608065, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13020 = KTree.node D2M8K2.u13018 (nat_lit 28079437) (nat_lit 1384954955) (nat_lit 0) D2M8K2.u13019 from rfl, totK_node, atot13018, atot13019]
  decide +kernel

theorem arows13023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13023 = true := by
  rw [show D2M8K2.u13023 = KTree.node D2M8K2.u13021 (nat_lit 28082818) (nat_lit 3842563464) (nat_lit 0) D2M8K2.u13022 from rfl, allE_node, arows13021, irow13023, arows13022]
  all_goals rfl

theorem atot13023 : totK PD2M8K2 D2M8K2.u13023 = [0, 327387967026, 1240388398967, 1481011024388, 553363666731, 33578126295, 0, 0] := by
  rw [show D2M8K2.u13023 = KTree.node D2M8K2.u13021 (nat_lit 28082818) (nat_lit 3842563464) (nat_lit 0) D2M8K2.u13022 from rfl, totK_node, atot13021, atot13022]
  decide +kernel

theorem arows13027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13027 = true := by
  rw [show D2M8K2.u13027 = KTree.node D2M8K2.u13025 (nat_lit 28085788) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u13026 from rfl, allE_node, arows13025, irow13027, arows13026]
  all_goals rfl

theorem atot13027 : totK PD2M8K2 D2M8K2.u13027 = [0, 378120578792, 1437426320176, 1437208886185, 330214468041, 13043783340, 0, 0] := by
  rw [show D2M8K2.u13027 = KTree.node D2M8K2.u13025 (nat_lit 28085788) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u13026 from rfl, totK_node, atot13025, atot13026]
  decide +kernel

theorem arows13030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13030 = true := by
  rw [show D2M8K2.u13030 = KTree.node D2M8K2.u13028 (nat_lit 28095914) (nat_lit 4105473047) (nat_lit 0) D2M8K2.u13029 from rfl, allE_node, arows13028, irow13030, arows13029]
  all_goals rfl

theorem atot13030 : totK PD2M8K2 D2M8K2.u13030 = [0, 254786597985, 1198486233564, 1604119223671, 513923929749, 23418599596, 0, 0] := by
  rw [show D2M8K2.u13030 = KTree.node D2M8K2.u13028 (nat_lit 28095914) (nat_lit 4105473047) (nat_lit 0) D2M8K2.u13029 from rfl, totK_node, atot13028, atot13029]
  decide +kernel

theorem arows13035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13035 = true := by
  rw [show D2M8K2.u13035 = KTree.node D2M8K2.u13033 (nat_lit 28099591) (nat_lit 1857043786) (nat_lit 0) D2M8K2.u13034 from rfl, allE_node, arows13033, irow13035, arows13034]
  all_goals rfl

theorem atot13035 : totK PD2M8K2 D2M8K2.u13035 = [0, 0, 537347619601, 1699132730852, 1201804788922, 122174048621, 1310285577, 0] := by
  rw [show D2M8K2.u13035 = KTree.node D2M8K2.u13033 (nat_lit 28099591) (nat_lit 1857043786) (nat_lit 0) D2M8K2.u13034 from rfl, totK_node, atot13033, atot13034]
  decide +kernel

theorem arows13038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13038 = true := by
  rw [show D2M8K2.u13038 = KTree.node D2M8K2.u13036 (nat_lit 28104780) (nat_lit 3550206895) (nat_lit 0) D2M8K2.u13037 from rfl, allE_node, arows13036, irow13038, arows13037]
  all_goals rfl

theorem atot13038 : totK PD2M8K2 D2M8K2.u13038 = [0, 0, 581104717023, 1761293690284, 1139237604126, 116173389862, 1075657031, 0] := by
  rw [show D2M8K2.u13038 = KTree.node D2M8K2.u13036 (nat_lit 28104780) (nat_lit 3550206895) (nat_lit 0) D2M8K2.u13037 from rfl, totK_node, atot13036, atot13037]
  decide +kernel

theorem arows13042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13042 = true := by
  rw [show D2M8K2.u13042 = KTree.node D2M8K2.u13040 (nat_lit 28115268) (nat_lit 3241439807) (nat_lit 0) D2M8K2.u13041 from rfl, allE_node, arows13040, irow13042, arows13041]
  all_goals rfl

theorem atot13042 : totK PD2M8K2 D2M8K2.u13042 = [0, 173576733255, 848093733231, 1471682591983, 952276005984, 143131096375, 3804183361, 0] := by
  rw [show D2M8K2.u13042 = KTree.node D2M8K2.u13040 (nat_lit 28115268) (nat_lit 3241439807) (nat_lit 0) D2M8K2.u13041 from rfl, totK_node, atot13040, atot13041]
  decide +kernel

theorem arows13045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13045 = true := by
  rw [show D2M8K2.u13045 = KTree.node D2M8K2.u13043 (nat_lit 28369185) (nat_lit 1708947563) (nat_lit 0) D2M8K2.u13044 from rfl, allE_node, arows13043, irow13045, arows13044]
  all_goals rfl

theorem atot13045 : totK PD2M8K2 D2M8K2.u13045 = [0, 480147435625, 1606877071586, 1320666337963, 180008822100, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13045 = KTree.node D2M8K2.u13043 (nat_lit 28369185) (nat_lit 1708947563) (nat_lit 0) D2M8K2.u13044 from rfl, totK_node, atot13043, atot13044]
  decide +kernel

theorem arows13054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13054 = true := by
  rw [show D2M8K2.u13054 = KTree.node D2M8K2.u13052 (nat_lit 28376948) (nat_lit 2381009640) (nat_lit 0) D2M8K2.u13053 from rfl, allE_node, arows13052, irow13054, arows13053]
  all_goals rfl

theorem atot13054 : totK PD2M8K2 D2M8K2.u13054 = [0, 439396500687, 1511585907889, 1315620523230, 285558185897, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13054 = KTree.node D2M8K2.u13052 (nat_lit 28376948) (nat_lit 2381009640) (nat_lit 0) D2M8K2.u13053 from rfl, totK_node, atot13052, atot13053]
  decide +kernel

theorem arows13057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13057 = true := by
  rw [show D2M8K2.u13057 = KTree.node D2M8K2.u13055 (nat_lit 28380312) (nat_lit 3247267020) (nat_lit 0) D2M8K2.u13056 from rfl, allE_node, arows13055, irow13057, arows13056]
  all_goals rfl

theorem atot13057 : totK PD2M8K2 D2M8K2.u13057 = [0, 406061793752, 1402420767101, 1406569174613, 341062595451, 13250685261, 0, 0] := by
  rw [show D2M8K2.u13057 = KTree.node D2M8K2.u13055 (nat_lit 28380312) (nat_lit 3247267020) (nat_lit 0) D2M8K2.u13056 from rfl, totK_node, atot13055, atot13056]
  decide +kernel

theorem arows13061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13061 = true := by
  rw [show D2M8K2.u13061 = KTree.node D2M8K2.u13059 (nat_lit 28383700) (nat_lit 3291258088) (nat_lit 0) D2M8K2.u13060 from rfl, allE_node, arows13059, irow13061, arows13060]
  all_goals rfl

theorem atot13061 : totK PD2M8K2 D2M8K2.u13061 = [0, 453942169455, 1536785136417, 1352551809461, 243040587987, 4980514959, 0, 0] := by
  rw [show D2M8K2.u13061 = KTree.node D2M8K2.u13059 (nat_lit 28383700) (nat_lit 3291258088) (nat_lit 0) D2M8K2.u13060 from rfl, totK_node, atot13059, atot13060]
  decide +kernel

theorem arows13064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13064 = true := by
  rw [show D2M8K2.u13064 = KTree.node D2M8K2.u13062 (nat_lit 28387564) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u13063 from rfl, allE_node, arows13062, irow13064, arows13063]
  all_goals rfl

theorem atot13064 : totK PD2M8K2 D2M8K2.u13064 = [0, 19692840307, 888575406169, 1888167180457, 699330847077, 35832876130, 0, 0] := by
  rw [show D2M8K2.u13064 = KTree.node D2M8K2.u13062 (nat_lit 28387564) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u13063 from rfl, totK_node, atot13062, atot13063]
  decide +kernel

theorem arows13069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13069 = true := by
  rw [show D2M8K2.u13069 = KTree.node D2M8K2.u13067 (nat_lit 28394653) (nat_lit 1369549359) (nat_lit 0) D2M8K2.u13068 from rfl, allE_node, arows13067, irow13069, arows13068]
  all_goals rfl

theorem atot13069 : totK PD2M8K2 D2M8K2.u13069 = [0, 0, 514143890485, 1708664204420, 1145618750174, 138188966141, 1369150432, 0] := by
  rw [show D2M8K2.u13069 = KTree.node D2M8K2.u13067 (nat_lit 28394653) (nat_lit 1369549359) (nat_lit 0) D2M8K2.u13068 from rfl, totK_node, atot13067, atot13068]
  decide +kernel

theorem arows13072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13072 = true := by
  rw [show D2M8K2.u13072 = KTree.node D2M8K2.u13070 (nat_lit 28401608) (nat_lit 3641295092) (nat_lit 0) D2M8K2.u13071 from rfl, allE_node, arows13070, irow13072, arows13071]
  all_goals rfl

theorem atot13072 : totK PD2M8K2 D2M8K2.u13072 = [0, 0, 741616329813, 1876839291544, 877774334253, 48805668711, 0, 0] := by
  rw [show D2M8K2.u13072 = KTree.node D2M8K2.u13070 (nat_lit 28401608) (nat_lit 3641295092) (nat_lit 0) D2M8K2.u13071 from rfl, totK_node, atot13070, atot13071]
  decide +kernel

theorem arows13076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13076 = true := by
  rw [show D2M8K2.u13076 = KTree.node D2M8K2.u13074 (nat_lit 28412143) (nat_lit 2422272469) (nat_lit 0) D2M8K2.u13075 from rfl, allE_node, arows13074, irow13076, arows13075]
  all_goals rfl

theorem atot13076 : totK PD2M8K2 D2M8K2.u13076 = [0, 416120212142, 1325886605153, 1418683363226, 464585647380, 16826381184, 0, 0] := by
  rw [show D2M8K2.u13076 = KTree.node D2M8K2.u13074 (nat_lit 28412143) (nat_lit 2422272469) (nat_lit 0) D2M8K2.u13075 from rfl, totK_node, atot13074, atot13075]
  decide +kernel

theorem arows13079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13079 = true := by
  rw [show D2M8K2.u13079 = KTree.node D2M8K2.u13077 (nat_lit 28414752) (nat_lit 3257669455) (nat_lit 0) D2M8K2.u13078 from rfl, allE_node, arows13077, irow13079, arows13078]
  all_goals rfl

theorem atot13079 : totK PD2M8K2 D2M8K2.u13079 = [0, 284838629777, 1189751851100, 1541781782459, 597031713985, 37609398105, 0, 0] := by
  rw [show D2M8K2.u13079 = KTree.node D2M8K2.u13077 (nat_lit 28414752) (nat_lit 3257669455) (nat_lit 0) D2M8K2.u13078 from rfl, totK_node, atot13077, atot13078]
  decide +kernel

theorem arows13085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13085 = true := by
  rw [show D2M8K2.u13085 = KTree.node D2M8K2.u13083 (nat_lit 28418796) (nat_lit 3159929432) (nat_lit 0) D2M8K2.u13084 from rfl, allE_node, arows13083, irow13085, arows13084]
  all_goals rfl

theorem atot13085 : totK PD2M8K2 D2M8K2.u13085 = [0, 495161875423, 1580896695155, 1321128009982, 247018901771, 9718818700, 0, 0] := by
  rw [show D2M8K2.u13085 = KTree.node D2M8K2.u13083 (nat_lit 28418796) (nat_lit 3159929432) (nat_lit 0) D2M8K2.u13084 from rfl, totK_node, atot13083, atot13084]
  decide +kernel

theorem arows13088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13088 = true := by
  rw [show D2M8K2.u13088 = KTree.node D2M8K2.u13086 (nat_lit 28421977) (nat_lit 1471800791) (nat_lit 0) D2M8K2.u13087 from rfl, allE_node, arows13086, irow13088, arows13087]
  all_goals rfl

theorem atot13088 : totK PD2M8K2 D2M8K2.u13088 = [0, 373955421059, 1395126097202, 1472812032546, 349976817718, 13237669976, 0, 0] := by
  rw [show D2M8K2.u13088 = KTree.node D2M8K2.u13086 (nat_lit 28421977) (nat_lit 1471800791) (nat_lit 0) D2M8K2.u13087 from rfl, totK_node, atot13086, atot13087]
  decide +kernel

theorem arows13092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13092 = true := by
  rw [show D2M8K2.u13092 = KTree.node D2M8K2.u13090 (nat_lit 28425721) (nat_lit 1519186642) (nat_lit 0) D2M8K2.u13091 from rfl, allE_node, arows13090, irow13092, arows13091]
  all_goals rfl

theorem atot13092 : totK PD2M8K2 D2M8K2.u13092 = [0, 427494810769, 1555605995085, 1406122168102, 245051024386, 4976872846, 0, 0] := by
  rw [show D2M8K2.u13092 = KTree.node D2M8K2.u13090 (nat_lit 28425721) (nat_lit 1519186642) (nat_lit 0) D2M8K2.u13091 from rfl, totK_node, atot13090, atot13091]
  decide +kernel

theorem arows13095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13095 = true := by
  rw [show D2M8K2.u13095 = KTree.node D2M8K2.u13093 (nat_lit 28432853) (nat_lit 2380560630) (nat_lit 0) D2M8K2.u13094 from rfl, allE_node, arows13093, irow13095, arows13094]
  all_goals rfl

theorem atot13095 : totK PD2M8K2 D2M8K2.u13095 = [0, 0, 808658322594, 1898245201925, 869127219780, 55719756825, 0, 0] := by
  rw [show D2M8K2.u13095 = KTree.node D2M8K2.u13093 (nat_lit 28432853) (nat_lit 2380560630) (nat_lit 0) D2M8K2.u13094 from rfl, totK_node, atot13093, atot13094]
  decide +kernel

theorem arows13100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13100 = true := by
  rw [show D2M8K2.u13100 = KTree.node D2M8K2.u13098 (nat_lit 28435723) (nat_lit 1761076053) (nat_lit 0) D2M8K2.u13099 from rfl, allE_node, arows13098, irow13100, arows13099]
  all_goals rfl

theorem atot13100 : totK PD2M8K2 D2M8K2.u13100 = [0, 0, 382004253074, 1448627435599, 1442648770700, 374107012773, 15177715065, 0] := by
  rw [show D2M8K2.u13100 = KTree.node D2M8K2.u13098 (nat_lit 28435723) (nat_lit 1761076053) (nat_lit 0) D2M8K2.u13099 from rfl, totK_node, atot13098, atot13099]
  decide +kernel

theorem arows13103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13103 = true := by
  rw [show D2M8K2.u13103 = KTree.node D2M8K2.u13101 (nat_lit 28440944) (nat_lit 3065667167) (nat_lit 0) D2M8K2.u13102 from rfl, allE_node, arows13101, irow13103, arows13102]
  all_goals rfl

theorem atot13103 : totK PD2M8K2 D2M8K2.u13103 = [0, 0, 458213101162, 1562584502750, 1340377649909, 238314290553, 5218872685, 0] := by
  rw [show D2M8K2.u13103 = KTree.node D2M8K2.u13101 (nat_lit 28440944) (nat_lit 3065667167) (nat_lit 0) D2M8K2.u13102 from rfl, totK_node, atot13101, atot13102]
  decide +kernel

theorem arows13107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13107 = true := by
  rw [show D2M8K2.u13107 = KTree.node D2M8K2.u13105 (nat_lit 28444209) (nat_lit 1619108298) (nat_lit 0) D2M8K2.u13106 from rfl, allE_node, arows13105, irow13107, arows13106]
  all_goals rfl

theorem atot13107 : totK PD2M8K2 D2M8K2.u13107 = [0, 0, 499279262433, 1642294498087, 1307977730113, 177139679952, 1415142070, 0] := by
  rw [show D2M8K2.u13107 = KTree.node D2M8K2.u13105 (nat_lit 28444209) (nat_lit 1619108298) (nat_lit 0) D2M8K2.u13106 from rfl, totK_node, atot13105, atot13106]
  decide +kernel

theorem arows13110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13110 = true := by
  rw [show D2M8K2.u13110 = KTree.node D2M8K2.u13108 (nat_lit 28491466) (nat_lit 3772867390) (nat_lit 0) D2M8K2.u13109 from rfl, allE_node, arows13108, irow13110, arows13109]
  all_goals rfl

theorem atot13110 : totK PD2M8K2 D2M8K2.u13110 = [0, 413264604107, 1324620474865, 1296048708830, 520794306243, 44759941450, 0, 0] := by
  rw [show D2M8K2.u13110 = KTree.node D2M8K2.u13108 (nat_lit 28491466) (nat_lit 3772867390) (nat_lit 0) D2M8K2.u13109 from rfl, totK_node, atot13108, atot13109]
  decide +kernel

theorem arows13117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13117 = true := by
  rw [show D2M8K2.u13117 = KTree.node D2M8K2.u13115 (nat_lit 28495365) (nat_lit 1260547425) (nat_lit 2) D2M8K2.u13116 from rfl, allE_node, arows13115, irow13117, arows13116]
  all_goals rfl

theorem atot13117 : totK PD2M8K2 D2M8K2.u13117 = [0, 423698525221, 1560685834261, 1432683534414, 209533130164, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13117 = KTree.node D2M8K2.u13115 (nat_lit 28495365) (nat_lit 1260547425) (nat_lit 2) D2M8K2.u13116 from rfl, totK_node, atot13115, atot13116]
  decide +kernel

theorem arows13120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13120 = true := by
  rw [show D2M8K2.u13120 = KTree.node D2M8K2.u13118 (nat_lit 28498166) (nat_lit 3162133314) (nat_lit 0) D2M8K2.u13119 from rfl, allE_node, arows13118, irow13120, arows13119]
  all_goals rfl

theorem atot13120 : totK PD2M8K2 D2M8K2.u13120 = [0, 375257125037, 1267723123268, 1401655247578, 555011751792, 35891568044, 0, 0] := by
  rw [show D2M8K2.u13120 = KTree.node D2M8K2.u13118 (nat_lit 28498166) (nat_lit 3162133314) (nat_lit 0) D2M8K2.u13119 from rfl, totK_node, atot13118, atot13119]
  decide +kernel

theorem arows13124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13124 = true := by
  rw [show D2M8K2.u13124 = KTree.node D2M8K2.u13122 (nat_lit 28504730) (nat_lit 3666310411) (nat_lit 0) D2M8K2.u13123 from rfl, allE_node, arows13122, irow13124, arows13123]
  all_goals rfl

theorem atot13124 : totK PD2M8K2 D2M8K2.u13124 = [0, 399677367866, 1407727486439, 1443602641861, 348506991046, 13250685261, 0, 0] := by
  rw [show D2M8K2.u13124 = KTree.node D2M8K2.u13122 (nat_lit 28504730) (nat_lit 3666310411) (nat_lit 0) D2M8K2.u13123 from rfl, totK_node, atot13122, atot13123]
  decide +kernel

theorem arows13127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13127 = true := by
  rw [show D2M8K2.u13127 = KTree.node D2M8K2.u13125 (nat_lit 28508054) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u13126 from rfl, allE_node, arows13125, irow13127, arows13126]
  all_goals rfl

theorem atot13127 : totK PD2M8K2 D2M8K2.u13127 = [0, 407595741939, 1524970710657, 1421665917646, 246652083614, 4980514959, 0, 0] := by
  rw [show D2M8K2.u13127 = KTree.node D2M8K2.u13125 (nat_lit 28508054) (nat_lit 3722288679) (nat_lit 0) D2M8K2.u13126 from rfl, totK_node, atot13125, atot13126]
  decide +kernel

theorem arows13132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13132 = true := by
  rw [show D2M8K2.u13132 = KTree.node D2M8K2.u13130 (nat_lit 28511740) (nat_lit 3806893530) (nat_lit 0) D2M8K2.u13131 from rfl, allE_node, arows13130, irow13132, arows13131]
  all_goals rfl

theorem atot13132 : totK PD2M8K2 D2M8K2.u13132 = [0, 87861870204, 962141990203, 1811180170027, 647796504879, 28649834410, 0, 0] := by
  rw [show D2M8K2.u13132 = KTree.node D2M8K2.u13130 (nat_lit 28511740) (nat_lit 3806893530) (nat_lit 0) D2M8K2.u13131 from rfl, totK_node, atot13130, atot13131]
  decide +kernel

theorem arows13135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13135 = true := by
  rw [show D2M8K2.u13135 = KTree.node D2M8K2.u13133 (nat_lit 28515785) (nat_lit 1794947592) (nat_lit 0) D2M8K2.u13134 from rfl, allE_node, arows13133, irow13135, arows13134]
  all_goals rfl

theorem atot13135 : totK PD2M8K2 D2M8K2.u13135 = [0, 0, 487331123760, 1662452886320, 1257749077915, 143818220085, 1239866073, 0] := by
  rw [show D2M8K2.u13135 = KTree.node D2M8K2.u13133 (nat_lit 28515785) (nat_lit 1794947592) (nat_lit 0) D2M8K2.u13134 from rfl, totK_node, atot13133, atot13134]
  decide +kernel

theorem arows13139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13139 = true := by
  rw [show D2M8K2.u13139 = KTree.node D2M8K2.u13137 (nat_lit 28523628) (nat_lit 3167593523) (nat_lit 0) D2M8K2.u13138 from rfl, allE_node, arows13137, irow13139, arows13138]
  all_goals rfl

theorem atot13139 : totK PD2M8K2 D2M8K2.u13139 = [0, 0, 463145708355, 1559737991923, 1304858538929, 245334766381, 9633262574, 0] := by
  rw [show D2M8K2.u13139 = KTree.node D2M8K2.u13137 (nat_lit 28523628) (nat_lit 3167593523) (nat_lit 0) D2M8K2.u13138 from rfl, totK_node, atot13137, atot13138]
  decide +kernel

theorem arows13142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13142 = true := by
  rw [show D2M8K2.u13142 = KTree.node D2M8K2.u13140 (nat_lit 28526796) (nat_lit 3138561861) (nat_lit 0) D2M8K2.u13141 from rfl, allE_node, arows13140, irow13142, arows13141]
  all_goals rfl

theorem atot13142 : totK PD2M8K2 D2M8K2.u13142 = [0, 0, 418229759367, 1576174065390, 1328796879908, 198052585831, 4525598988, 0] := by
  rw [show D2M8K2.u13142 = KTree.node D2M8K2.u13140 (nat_lit 28526796) (nat_lit 3138561861) (nat_lit 0) D2M8K2.u13141 from rfl, totK_node, atot13140, atot13141]
  decide +kernel

theorem arows13148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13148 = true := by
  rw [show D2M8K2.u13148 = KTree.node D2M8K2.u13146 (nat_lit 28530751) (nat_lit 2299740379) (nat_lit 0) D2M8K2.u13147 from rfl, allE_node, arows13146, irow13148, arows13147]
  all_goals rfl

theorem atot13148 : totK PD2M8K2 D2M8K2.u13148 = [0, 308168605862, 1128286523894, 1356430943721, 663779926817, 99400501736, 3667207281, 0] := by
  rw [show D2M8K2.u13148 = KTree.node D2M8K2.u13146 (nat_lit 28530751) (nat_lit 2299740379) (nat_lit 0) D2M8K2.u13147 from rfl, totK_node, atot13146, atot13147]
  decide +kernel

theorem arows13151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13151 = true := by
  rw [show D2M8K2.u13151 = KTree.node D2M8K2.u13149 (nat_lit 28535984) (nat_lit 2603554958) (nat_lit 0) D2M8K2.u13150 from rfl, allE_node, arows13149, irow13151, arows13150]
  all_goals rfl

theorem atot13151 : totK PD2M8K2 D2M8K2.u13151 = [0, 444593108631, 1599222791819, 1370966749971, 189030497308, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13151 = KTree.node D2M8K2.u13149 (nat_lit 28535984) (nat_lit 2603554958) (nat_lit 0) D2M8K2.u13150 from rfl, totK_node, atot13149, atot13150]
  decide +kernel

theorem arows13155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13155 = true := by
  rw [show D2M8K2.u13155 = KTree.node D2M8K2.u13153 (nat_lit 28539128) (nat_lit 3798846925) (nat_lit 0) D2M8K2.u13154 from rfl, allE_node, arows13153, irow13155, arows13154]
  all_goals rfl

theorem atot13155 : totK PD2M8K2 D2M8K2.u13155 = [0, 323804469727, 1218677473591, 1474291821452, 575302348752, 35974381217, 0, 0] := by
  rw [show D2M8K2.u13155 = KTree.node D2M8K2.u13153 (nat_lit 28539128) (nat_lit 3798846925) (nat_lit 0) D2M8K2.u13154 from rfl, totK_node, atot13153, atot13154]
  decide +kernel

theorem arows13158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13158 = true := by
  rw [show D2M8K2.u13158 = KTree.node D2M8K2.u13156 (nat_lit 28542705) (nat_lit 1497272357) (nat_lit 0) D2M8K2.u13157 from rfl, allE_node, arows13156, irow13158, arows13157]
  all_goals rfl

theorem atot13158 : totK PD2M8K2 D2M8K2.u13158 = [0, 442390887367, 1490816394368, 1351080295740, 296390964290, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13158 = KTree.node D2M8K2.u13156 (nat_lit 28542705) (nat_lit 1497272357) (nat_lit 0) D2M8K2.u13157 from rfl, totK_node, atot13156, atot13157]
  decide +kernel

theorem arows13163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13163 = true := by
  rw [show D2M8K2.u13163 = KTree.node D2M8K2.u13161 (nat_lit 28546202) (nat_lit 3666310411) (nat_lit 0) D2M8K2.u13162 from rfl, allE_node, arows13161, irow13163, arows13162]
  all_goals rfl

theorem atot13163 : totK PD2M8K2 D2M8K2.u13163 = [0, 418574489340, 1412025608726, 1415904028684, 346055132220, 13250685261, 0, 0] := by
  rw [show D2M8K2.u13163 = KTree.node D2M8K2.u13161 (nat_lit 28546202) (nat_lit 3666310411) (nat_lit 0) D2M8K2.u13162 from rfl, totK_node, atot13161, atot13162]
  decide +kernel

theorem arows13166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13166 = true := by
  rw [show D2M8K2.u13166 = KTree.node D2M8K2.u13164 (nat_lit 28549497) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u13165 from rfl, allE_node, arows13164, irow13166, arows13165]
  all_goals rfl

theorem atot13166 : totK PD2M8K2 D2M8K2.u13166 = [0, 92722817510, 1099676362253, 1827101778274, 537910859812, 23242077755, 0, 0] := by
  rw [show D2M8K2.u13166 = KTree.node D2M8K2.u13164 (nat_lit 28549497) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u13165 from rfl, totK_node, atot13164, atot13165]
  decide +kernel

theorem arows13170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13170 = true := by
  rw [show D2M8K2.u13170 = KTree.node D2M8K2.u13168 (nat_lit 28557390) (nat_lit 3866013797) (nat_lit 0) D2M8K2.u13169 from rfl, allE_node, arows13168, irow13170, arows13169]
  all_goals rfl

theorem atot13170 : totK PD2M8K2 D2M8K2.u13170 = [0, 0, 500953207176, 1709559029646, 1205389025723, 132104590422, 1138244013, 0] := by
  rw [show D2M8K2.u13170 = KTree.node D2M8K2.u13168 (nat_lit 28557390) (nat_lit 3866013797) (nat_lit 0) D2M8K2.u13169 from rfl, totK_node, atot13168, atot13169]
  decide +kernel

theorem arows13173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13173 = true := by
  rw [show D2M8K2.u13173 = KTree.node D2M8K2.u13171 (nat_lit 28563964) (nat_lit 2412248710) (nat_lit 0) D2M8K2.u13172 from rfl, allE_node, arows13171, irow13173, arows13172]
  all_goals rfl

theorem atot13173 : totK PD2M8K2 D2M8K2.u13173 = [0, 0, 747729678302, 1909171933730, 896127717923, 48085755988, 0, 0] := by
  rw [show D2M8K2.u13173 = KTree.node D2M8K2.u13171 (nat_lit 28563964) (nat_lit 2412248710) (nat_lit 0) D2M8K2.u13172 from rfl, totK_node, atot13171, atot13172]
  decide +kernel

theorem arows13181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13181 = true := by
  rw [show D2M8K2.u13181 = KTree.node D2M8K2.u13179 (nat_lit 28568477) (nat_lit 2292250904) (nat_lit 0) D2M8K2.u13180 from rfl, allE_node, arows13179, irow13181, arows13180]
  all_goals rfl

theorem atot13181 : totK PD2M8K2 D2M8K2.u13181 = [0, 7559944729, 441064347440, 1551262511286, 1299819751513, 227402777549, 4977114383, 0] := by
  rw [show D2M8K2.u13181 = KTree.node D2M8K2.u13179 (nat_lit 28568477) (nat_lit 2292250904) (nat_lit 0) D2M8K2.u13180 from rfl, totK_node, atot13179, atot13180]
  decide +kernel

theorem arows13184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13184 = true := by
  rw [show D2M8K2.u13184 = KTree.node D2M8K2.u13182 (nat_lit 28575844) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u13183 from rfl, allE_node, arows13182, irow13184, arows13183]
  all_goals rfl

theorem atot13184 : totK PD2M8K2 D2M8K2.u13184 = [0, 477630417887, 1618721662557, 1317945271881, 175943375908, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13184 = KTree.node D2M8K2.u13182 (nat_lit 28575844) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u13183 from rfl, totK_node, atot13182, atot13183]
  decide +kernel

theorem arows13188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13188 = true := by
  rw [show D2M8K2.u13188 = KTree.node D2M8K2.u13186 (nat_lit 28579790) (nat_lit 3882570931) (nat_lit 0) D2M8K2.u13187 from rfl, allE_node, arows13186, irow13188, arows13187]
  all_goals rfl

theorem atot13188 : totK PD2M8K2 D2M8K2.u13188 = [0, 330171207115, 1245794140207, 1484092071011, 551615334818, 33655171283, 0, 0] := by
  rw [show D2M8K2.u13188 = KTree.node D2M8K2.u13186 (nat_lit 28579790) (nat_lit 3882570931) (nat_lit 0) D2M8K2.u13187 from rfl, totK_node, atot13186, atot13187]
  decide +kernel

theorem arows13191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13191 = true := by
  rw [show D2M8K2.u13191 = KTree.node D2M8K2.u13189 (nat_lit 28586091) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13190 from rfl, allE_node, arows13189, irow13191, arows13190]
  all_goals rfl

theorem atot13191 : totK PD2M8K2 D2M8K2.u13191 = [0, 411128583787, 1454449070975, 1394729213966, 326175745399, 13243784863, 0, 0] := by
  rw [show D2M8K2.u13191 = KTree.node D2M8K2.u13189 (nat_lit 28586091) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13190 from rfl, totK_node, atot13189, atot13190]
  decide +kernel

theorem arows13196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13196 = true := by
  rw [show D2M8K2.u13196 = KTree.node D2M8K2.u13194 (nat_lit 28592621) (nat_lit 1626674301) (nat_lit 0) D2M8K2.u13195 from rfl, allE_node, arows13194, irow13196, arows13195]
  all_goals rfl

theorem atot13196 : totK PD2M8K2 D2M8K2.u13196 = [0, 428021878965, 1483984716548, 1405484673169, 301963565727, 6033099918, 0, 0] := by
  rw [show D2M8K2.u13196 = KTree.node D2M8K2.u13194 (nat_lit 28592621) (nat_lit 1626674301) (nat_lit 0) D2M8K2.u13195 from rfl, totK_node, atot13194, atot13195]
  decide +kernel

theorem arows13199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13199 = true := by
  rw [show D2M8K2.u13199 = KTree.node D2M8K2.u13197 (nat_lit 28596195) (nat_lit 2762643478) (nat_lit 0) D2M8K2.u13198 from rfl, allE_node, arows13197, irow13199, arows13198]
  all_goals rfl

theorem atot13199 : totK PD2M8K2 D2M8K2.u13199 = [0, 0, 525556871910, 1699239592918, 1193415296425, 115164051965, 1310285577, 0] := by
  rw [show D2M8K2.u13199 = KTree.node D2M8K2.u13197 (nat_lit 28596195) (nat_lit 2762643478) (nat_lit 0) D2M8K2.u13198 from rfl, totK_node, atot13197, atot13198]
  decide +kernel

theorem arows13203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13203 = true := by
  rw [show D2M8K2.u13203 = KTree.node D2M8K2.u13201 (nat_lit 28600034) (nat_lit 3991730768) (nat_lit 0) D2M8K2.u13202 from rfl, allE_node, arows13201, irow13203, arows13202]
  all_goals rfl

theorem atot13203 : totK PD2M8K2 D2M8K2.u13203 = [0, 0, 707735695693, 1848484780188, 1001530609926, 77552743093, 0, 0] := by
  rw [show D2M8K2.u13203 = KTree.node D2M8K2.u13201 (nat_lit 28600034) (nat_lit 3991730768) (nat_lit 0) D2M8K2.u13202 from rfl, totK_node, atot13201, atot13202]
  decide +kernel

theorem arows13206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13206 = true := by
  rw [show D2M8K2.u13206 = KTree.node D2M8K2.u13204 (nat_lit 28612276) (nat_lit 3980353223) (nat_lit 0) D2M8K2.u13205 from rfl, allE_node, arows13204, irow13206, arows13205]
  all_goals rfl

theorem atot13206 : totK PD2M8K2 D2M8K2.u13206 = [0, 0, 496441162787, 1607466076607, 1275998846989, 201769122836, 4931404646, 0] := by
  rw [show D2M8K2.u13206 = KTree.node D2M8K2.u13204 (nat_lit 28612276) (nat_lit 3980353223) (nat_lit 0) D2M8K2.u13205 from rfl, totK_node, atot13204, atot13205]
  decide +kernel

theorem arows13212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13212 = true := by
  rw [show D2M8K2.u13212 = KTree.node D2M8K2.u13210 (nat_lit 28865820) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u13211 from rfl, allE_node, arows13210, irow13212, arows13211]
  all_goals rfl

theorem atot13212 : totK PD2M8K2 D2M8K2.u13212 = [0, 435294558901, 1513954737364, 1355171515404, 289964178987, 15015246194, 0, 0] := by
  rw [show D2M8K2.u13212 = KTree.node D2M8K2.u13210 (nat_lit 28865820) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u13211 from rfl, totK_node, atot13210, atot13211]
  decide +kernel

theorem arows13215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13215 = true := by
  rw [show D2M8K2.u13215 = KTree.node D2M8K2.u13213 (nat_lit 28872902) (nat_lit 3971485324) (nat_lit 0) D2M8K2.u13214 from rfl, allE_node, arows13213, irow13215, arows13214]
  all_goals rfl

theorem atot13215 : totK PD2M8K2 D2M8K2.u13215 = [0, 410614163193, 1432502363740, 1387998623512, 316425977023, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13215 = KTree.node D2M8K2.u13213 (nat_lit 28872902) (nat_lit 3971485324) (nat_lit 0) D2M8K2.u13214 from rfl, totK_node, atot13213, atot13214]
  decide +kernel

theorem arows13219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13219 = true := by
  rw [show D2M8K2.u13219 = KTree.node D2M8K2.u13217 (nat_lit 28876321) (nat_lit 1553244865) (nat_lit 0) D2M8K2.u13218 from rfl, allE_node, arows13217, irow13219, arows13218]
  all_goals rfl

theorem atot13219 : totK PD2M8K2 D2M8K2.u13219 = [0, 410834643430, 1427048839433, 1396878682670, 318215797140, 10680993762, 0, 0] := by
  rw [show D2M8K2.u13219 = KTree.node D2M8K2.u13217 (nat_lit 28876321) (nat_lit 1553244865) (nat_lit 0) D2M8K2.u13218 from rfl, totK_node, atot13217, atot13218]
  decide +kernel

theorem arows13222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13222 = true := by
  rw [show D2M8K2.u13222 = KTree.node D2M8K2.u13220 (nat_lit 28879425) (nat_lit 1782433198) (nat_lit 0) D2M8K2.u13221 from rfl, allE_node, arows13220, irow13222, arows13221]
  all_goals rfl

theorem atot13222 : totK PD2M8K2 D2M8K2.u13222 = [0, 424122565885, 1577340585746, 1400575648271, 205845421972, 3666196603, 0, 0] := by
  rw [show D2M8K2.u13222 = KTree.node D2M8K2.u13220 (nat_lit 28879425) (nat_lit 1782433198) (nat_lit 0) D2M8K2.u13221 from rfl, totK_node, atot13220, atot13221]
  decide +kernel

theorem arows13227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13227 = true := by
  rw [show D2M8K2.u13227 = KTree.node D2M8K2.u13225 (nat_lit 28883593) (nat_lit 1512170416) (nat_lit 0) D2M8K2.u13226 from rfl, allE_node, arows13225, irow13227, arows13226]
  all_goals rfl

theorem atot13227 : totK PD2M8K2 D2M8K2.u13227 = [0, 323074992700, 1299547187360, 1488942245252, 417952450456, 13964570338, 0, 0] := by
  rw [show D2M8K2.u13227 = KTree.node D2M8K2.u13225 (nat_lit 28883593) (nat_lit 1512170416) (nat_lit 0) D2M8K2.u13226 from rfl, totK_node, atot13225, atot13226]
  decide +kernel

theorem arows13230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13230 = true := by
  rw [show D2M8K2.u13230 = KTree.node D2M8K2.u13228 (nat_lit 28887130) (nat_lit 3641657729) (nat_lit 0) D2M8K2.u13229 from rfl, allE_node, arows13228, irow13230, arows13229]
  all_goals rfl

theorem atot13230 : totK PD2M8K2 D2M8K2.u13230 = [0, 0, 483674644285, 1654260857857, 1183105263924, 143279229692, 1369150432, 0] := by
  rw [show D2M8K2.u13230 = KTree.node D2M8K2.u13228 (nat_lit 28887130) (nat_lit 3641657729) (nat_lit 0) D2M8K2.u13229 from rfl, totK_node, atot13228, atot13229]
  decide +kernel

theorem arows13234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13234 = true := by
  rw [show D2M8K2.u13234 = KTree.node D2M8K2.u13232 (nat_lit 28896151) (nat_lit 2328479273) (nat_lit 0) D2M8K2.u13233 from rfl, allE_node, arows13232, irow13234, arows13233]
  all_goals rfl

theorem atot13234 : totK PD2M8K2 D2M8K2.u13234 = [0, 0, 739402146745, 1901746825608, 847917960414, 39146313904, 0, 0] := by
  rw [show D2M8K2.u13234 = KTree.node D2M8K2.u13232 (nat_lit 28896151) (nat_lit 2328479273) (nat_lit 0) D2M8K2.u13233 from rfl, totK_node, atot13232, atot13233]
  decide +kernel

theorem arows13237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13237 = true := by
  rw [show D2M8K2.u13237 = KTree.node D2M8K2.u13235 (nat_lit 28902722) (nat_lit 3042697328) (nat_lit 0) D2M8K2.u13236 from rfl, allE_node, arows13235, irow13237, arows13236]
  all_goals rfl

theorem atot13237 : totK PD2M8K2 D2M8K2.u13237 = [0, 127234728902, 898911907770, 1786246144581, 730160270873, 32637719621, 0, 0] := by
  rw [show D2M8K2.u13237 = KTree.node D2M8K2.u13235 (nat_lit 28902722) (nat_lit 3042697328) (nat_lit 0) D2M8K2.u13236 from rfl, totK_node, atot13235, atot13236]
  decide +kernel

theorem arows13244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13244 = true := by
  rw [show D2M8K2.u13244 = KTree.node D2M8K2.u13242 (nat_lit 28911556) (nat_lit 3772544887) (nat_lit 0) D2M8K2.u13243 from rfl, allE_node, arows13242, irow13244, arows13243]
  all_goals rfl

theorem atot13244 : totK PD2M8K2 D2M8K2.u13244 = [0, 316637552494, 1290376110548, 1509361443138, 507366346325, 30804453458, 0, 0] := by
  rw [show D2M8K2.u13244 = KTree.node D2M8K2.u13242 (nat_lit 28911556) (nat_lit 3772544887) (nat_lit 0) D2M8K2.u13243 from rfl, totK_node, atot13242, atot13243]
  decide +kernel

theorem arows13247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13247 = true := by
  rw [show D2M8K2.u13247 = KTree.node D2M8K2.u13245 (nat_lit 28914301) (nat_lit 1082424169) (nat_lit 0) D2M8K2.u13246 from rfl, allE_node, arows13245, irow13247, arows13246]
  all_goals rfl

theorem atot13247 : totK PD2M8K2 D2M8K2.u13247 = [0, 413774819927, 1393177229192, 1380425485261, 380203515324, 18338216477, 0, 0] := by
  rw [show D2M8K2.u13247 = KTree.node D2M8K2.u13245 (nat_lit 28914301) (nat_lit 1082424169) (nat_lit 0) D2M8K2.u13246 from rfl, totK_node, atot13245, atot13246]
  decide +kernel

theorem arows13251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13251 = true := by
  rw [show D2M8K2.u13251 = KTree.node D2M8K2.u13249 (nat_lit 28917701) (nat_lit 2292692752) (nat_lit 0) D2M8K2.u13250 from rfl, allE_node, arows13249, irow13251, arows13250]
  all_goals rfl

theorem atot13251 : totK PD2M8K2 D2M8K2.u13251 = [0, 414015629082, 1474267701092, 1407304603282, 303723261100, 12174598588, 0, 0] := by
  rw [show D2M8K2.u13251 = KTree.node D2M8K2.u13249 (nat_lit 28917701) (nat_lit 2292692752) (nat_lit 0) D2M8K2.u13250 from rfl, totK_node, atot13249, atot13250]
  decide +kernel

theorem arows13254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13254 = true := by
  rw [show D2M8K2.u13254 = KTree.node D2M8K2.u13252 (nat_lit 28920821) (nat_lit 939249387) (nat_lit 0) D2M8K2.u13253 from rfl, allE_node, arows13252, irow13254, arows13253]
  all_goals rfl

theorem atot13254 : totK PD2M8K2 D2M8K2.u13254 = [0, 425223410355, 1570696877860, 1413650915042, 228580767901, 3662822055, 0, 0] := by
  rw [show D2M8K2.u13254 = KTree.node D2M8K2.u13252 (nat_lit 28920821) (nat_lit 939249387) (nat_lit 0) D2M8K2.u13253 from rfl, totK_node, atot13252, atot13253]
  decide +kernel

theorem arows13259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13259 = true := by
  rw [show D2M8K2.u13259 = KTree.node D2M8K2.u13257 (nat_lit 28924910) (nat_lit 2609194944) (nat_lit 0) D2M8K2.u13258 from rfl, allE_node, arows13257, irow13259, arows13258]
  all_goals rfl

theorem atot13259 : totK PD2M8K2 D2M8K2.u13259 = [0, 330028431640, 1293791281748, 1526516233350, 459428168047, 27291998893, 0, 0] := by
  rw [show D2M8K2.u13259 = KTree.node D2M8K2.u13257 (nat_lit 28924910) (nat_lit 2609194944) (nat_lit 0) D2M8K2.u13258 from rfl, totK_node, atot13257, atot13258]
  decide +kernel

theorem arows13262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13262 = true := by
  rw [show D2M8K2.u13262 = KTree.node D2M8K2.u13260 (nat_lit 28931841) (nat_lit 1403987747) (nat_lit 0) D2M8K2.u13261 from rfl, allE_node, arows13260, irow13262, arows13261]
  all_goals rfl

theorem atot13262 : totK PD2M8K2 D2M8K2.u13262 = [0, 0, 348660325359, 1344133014520, 1474168806359, 426579453111, 23727080593, 0] := by
  rw [show D2M8K2.u13262 = KTree.node D2M8K2.u13260 (nat_lit 28931841) (nat_lit 1403987747) (nat_lit 0) D2M8K2.u13261 from rfl, totK_node, atot13260, atot13261]
  decide +kernel

theorem arows13266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13266 = true := by
  rw [show D2M8K2.u13266 = KTree.node D2M8K2.u13264 (nat_lit 28935100) (nat_lit 3901800563) (nat_lit 0) D2M8K2.u13265 from rfl, allE_node, arows13264, irow13266, arows13265]
  all_goals rfl

theorem atot13266 : totK PD2M8K2 D2M8K2.u13266 = [0, 0, 465508016315, 1573366858409, 1323926749303, 219203207474, 5159868635, 0] := by
  rw [show D2M8K2.u13266 = KTree.node D2M8K2.u13264 (nat_lit 28935100) (nat_lit 3901800563) (nat_lit 0) D2M8K2.u13265 from rfl, totK_node, atot13264, atot13265]
  decide +kernel

theorem arows13269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13269 = true := by
  rw [show D2M8K2.u13269 = KTree.node D2M8K2.u13267 (nat_lit 28938707) (nat_lit 2871729602) (nat_lit 0) D2M8K2.u13268 from rfl, allE_node, arows13267, irow13269, arows13268]
  all_goals rfl

theorem atot13269 : totK PD2M8K2 D2M8K2.u13269 = [0, 0, 456984564685, 1592304085684, 1312048016425, 218974731138, 5218872685, 0] := by
  rw [show D2M8K2.u13269 = KTree.node D2M8K2.u13267 (nat_lit 28938707) (nat_lit 2871729602) (nat_lit 0) D2M8K2.u13268 from rfl, totK_node, atot13267, atot13268]
  decide +kernel

theorem arows13275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13275 = true := by
  rw [show D2M8K2.u13275 = KTree.node D2M8K2.u13273 (nat_lit 28942344) (nat_lit 3475111726) (nat_lit 0) D2M8K2.u13274 from rfl, allE_node, arows13273, irow13275, arows13274]
  all_goals rfl

theorem atot13275 : totK PD2M8K2 D2M8K2.u13275 = [0, 0, 463903660102, 1592001898661, 1390577953050, 198929167321, 1415142070, 0] := by
  rw [show D2M8K2.u13275 = KTree.node D2M8K2.u13273 (nat_lit 28942344) (nat_lit 3475111726) (nat_lit 0) D2M8K2.u13274 from rfl, totK_node, atot13273, atot13274]
  decide +kernel

theorem arows13278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13278 = true := by
  rw [show D2M8K2.u13278 = KTree.node D2M8K2.u13276 (nat_lit 28948286) (nat_lit 2442311913) (nat_lit 0) D2M8K2.u13277 from rfl, allE_node, arows13276, irow13278, arows13277]
  all_goals rfl

theorem atot13278 : totK PD2M8K2 D2M8K2.u13278 = [0, 406592456080, 1382173276147, 1376868190758, 393982775849, 16826295512, 0, 0] := by
  rw [show D2M8K2.u13278 = KTree.node D2M8K2.u13276 (nat_lit 28948286) (nat_lit 2442311913) (nat_lit 0) D2M8K2.u13277 from rfl, totK_node, atot13276, atot13277]
  decide +kernel

theorem arows13282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13282 = true := by
  rw [show D2M8K2.u13282 = KTree.node D2M8K2.u13280 (nat_lit 28951918) (nat_lit 3449555983) (nat_lit 0) D2M8K2.u13281 from rfl, allE_node, arows13280, irow13282, arows13281]
  all_goals rfl

theorem atot13282 : totK PD2M8K2 D2M8K2.u13282 = [0, 417908365244, 1497740449507, 1400840622155, 311691977613, 21155208970, 0, 0] := by
  rw [show D2M8K2.u13282 = KTree.node D2M8K2.u13280 (nat_lit 28951918) (nat_lit 3449555983) (nat_lit 0) D2M8K2.u13281 from rfl, totK_node, atot13280, atot13281]
  decide +kernel

theorem arows13285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13285 = true := by
  rw [show D2M8K2.u13285 = KTree.node D2M8K2.u13283 (nat_lit 28954770) (nat_lit 3094186961) (nat_lit 0) D2M8K2.u13284 from rfl, allE_node, arows13283, irow13285, arows13284]
  all_goals rfl

theorem atot13285 : totK PD2M8K2 D2M8K2.u13285 = [0, 439736597927, 1439961064115, 1341292879843, 386855962885, 14826367994, 0, 0] := by
  rw [show D2M8K2.u13285 = KTree.node D2M8K2.u13283 (nat_lit 28954770) (nat_lit 3094186961) (nat_lit 0) D2M8K2.u13284 from rfl, totK_node, atot13283, atot13284]
  decide +kernel

theorem arows13290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13290 = true := by
  rw [show D2M8K2.u13290 = KTree.node D2M8K2.u13288 (nat_lit 28961505) (nat_lit 1736643975) (nat_lit 0) D2M8K2.u13289 from rfl, allE_node, arows13288, irow13290, arows13289]
  all_goals rfl

theorem atot13290 : totK PD2M8K2 D2M8K2.u13290 = [0, 424831878583, 1454006894107, 1390088464430, 324792084974, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13290 = KTree.node D2M8K2.u13288 (nat_lit 28961505) (nat_lit 1736643975) (nat_lit 0) D2M8K2.u13289 from rfl, totK_node, atot13288, atot13289]
  decide +kernel

theorem arows13293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13293 = true := by
  rw [show D2M8K2.u13293 = KTree.node D2M8K2.u13291 (nat_lit 28965055) (nat_lit 2152900396) (nat_lit 0) D2M8K2.u13292 from rfl, allE_node, arows13291, irow13293, arows13292]
  all_goals rfl

theorem atot13293 : totK PD2M8K2 D2M8K2.u13293 = [0, 326127760768, 1405102749267, 1546432101309, 312858713904, 6249254262, 0, 0] := by
  rw [show D2M8K2.u13293 = KTree.node D2M8K2.u13291 (nat_lit 28965055) (nat_lit 2152900396) (nat_lit 0) D2M8K2.u13292 from rfl, totK_node, atot13291, atot13292]
  decide +kernel

theorem arows13297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13297 = true := by
  rw [show D2M8K2.u13297 = KTree.node D2M8K2.u13295 (nat_lit 28969213) (nat_lit 1182659905) (nat_lit 0) D2M8K2.u13296 from rfl, allE_node, arows13295, irow13297, arows13296]
  all_goals rfl

theorem atot13297 : totK PD2M8K2 D2M8K2.u13297 = [0, 0, 557155133881, 1717548032302, 1077186873803, 102935654513, 1206465782, 0] := by
  rw [show D2M8K2.u13297 = KTree.node D2M8K2.u13295 (nat_lit 28969213) (nat_lit 1182659905) (nat_lit 0) D2M8K2.u13296 from rfl, totK_node, atot13295, atot13296]
  decide +kernel

theorem arows13300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13300 = true := by
  rw [show D2M8K2.u13300 = KTree.node D2M8K2.u13298 (nat_lit 28973026) (nat_lit 2557483303) (nat_lit 0) D2M8K2.u13299 from rfl, allE_node, arows13298, irow13300, arows13299]
  all_goals rfl

theorem atot13300 : totK PD2M8K2 D2M8K2.u13300 = [0, 0, 716095009339, 1871265319788, 979221861203, 69022366870, 0, 0] := by
  rw [show D2M8K2.u13300 = KTree.node D2M8K2.u13298 (nat_lit 28973026) (nat_lit 2557483303) (nat_lit 0) D2M8K2.u13299 from rfl, totK_node, atot13298, atot13299]
  decide +kernel

theorem arows13311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13311 = true := by
  rw [show D2M8K2.u13311 = KTree.node D2M8K2.u13309 (nat_lit 28978013) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u13310 from rfl, allE_node, arows13309, irow13311, arows13310]
  all_goals rfl

theorem atot13311 : totK PD2M8K2 D2M8K2.u13311 = [0, 0, 408036424165, 1489709127883, 1319107772029, 275355659503, 13016197374, 0] := by
  rw [show D2M8K2.u13311 = KTree.node D2M8K2.u13309 (nat_lit 28978013) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u13310 from rfl, totK_node, atot13309, atot13310]
  decide +kernel

theorem arows13314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13314 = true := by
  rw [show D2M8K2.u13314 = KTree.node D2M8K2.u13312 (nat_lit 28984966) (nat_lit 2553798755) (nat_lit 0) D2M8K2.u13313 from rfl, allE_node, arows13312, irow13314, arows13313]
  all_goals rfl

theorem atot13314 : totK PD2M8K2 D2M8K2.u13314 = [0, 0, 471102038500, 1623562943186, 1236454395982, 175727787985, 4574395652, 0] := by
  rw [show D2M8K2.u13314 = KTree.node D2M8K2.u13312 (nat_lit 28984966) (nat_lit 2553798755) (nat_lit 0) D2M8K2.u13313 from rfl, totK_node, atot13312, atot13313]
  decide +kernel

theorem arows13318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13318 = true := by
  rw [show D2M8K2.u13318 = KTree.node D2M8K2.u13316 (nat_lit 28990494) (nat_lit 3899839391) (nat_lit 0) D2M8K2.u13317 from rfl, allE_node, arows13316, irow13318, arows13317]
  all_goals rfl

theorem atot13318 : totK PD2M8K2 D2M8K2.u13318 = [0, 499622693575, 1605018571874, 1283655214176, 184040668551, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13318 = KTree.node D2M8K2.u13316 (nat_lit 28990494) (nat_lit 3899839391) (nat_lit 0) D2M8K2.u13317 from rfl, totK_node, atot13316, atot13317]
  decide +kernel

theorem arows13321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13321 = true := by
  rw [show D2M8K2.u13321 = KTree.node D2M8K2.u13319 (nat_lit 28994428) (nat_lit 3891428098) (nat_lit 0) D2M8K2.u13320 from rfl, allE_node, arows13319, irow13321, arows13320]
  all_goals rfl

theorem atot13321 : totK PD2M8K2 D2M8K2.u13321 = [0, 325018865045, 1305023665138, 1487345101985, 494504100570, 30553880795, 0, 0] := by
  rw [show D2M8K2.u13321 = KTree.node D2M8K2.u13319 (nat_lit 28994428) (nat_lit 3891428098) (nat_lit 0) D2M8K2.u13320 from rfl, totK_node, atot13319, atot13320]
  decide +kernel

theorem arows13326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13326 = true := by
  rw [show D2M8K2.u13326 = KTree.node D2M8K2.u13324 (nat_lit 29000592) (nat_lit 3657878909) (nat_lit 0) D2M8K2.u13325 from rfl, allE_node, arows13324, irow13326, arows13325]
  all_goals rfl

theorem atot13326 : totK PD2M8K2 D2M8K2.u13326 = [0, 439904189574, 1459355028465, 1367251597951, 345648753614, 15084612603, 0, 0] := by
  rw [show D2M8K2.u13326 = KTree.node D2M8K2.u13324 (nat_lit 29000592) (nat_lit 3657878909) (nat_lit 0) D2M8K2.u13325 from rfl, totK_node, atot13324, atot13325]
  decide +kernel

theorem arows13329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13329 = true := by
  rw [show D2M8K2.u13329 = KTree.node D2M8K2.u13327 (nat_lit 29003648) (nat_lit 3765164749) (nat_lit 0) D2M8K2.u13328 from rfl, allE_node, arows13327, irow13329, arows13328]
  all_goals rfl

theorem atot13329 : totK PD2M8K2 D2M8K2.u13329 = [0, 424860175082, 1532184108144, 1409317395927, 245163661531, 4678454933, 0, 0] := by
  rw [show D2M8K2.u13329 = KTree.node D2M8K2.u13327 (nat_lit 29003648) (nat_lit 3765164749) (nat_lit 0) D2M8K2.u13328 from rfl, totK_node, atot13327, atot13328]
  decide +kernel

theorem arows13333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13333 = true := by
  rw [show D2M8K2.u13333 = KTree.node D2M8K2.u13331 (nat_lit 29007734) (nat_lit 3924542569) (nat_lit 0) D2M8K2.u13332 from rfl, allE_node, arows13331, irow13333, arows13332]
  all_goals rfl

theorem atot13333 : totK PD2M8K2 D2M8K2.u13333 = [0, 326274180204, 1345589475386, 1511577256458, 391548016087, 12655098630, 0, 0] := by
  rw [show D2M8K2.u13333 = KTree.node D2M8K2.u13331 (nat_lit 29007734) (nat_lit 3924542569) (nat_lit 0) D2M8K2.u13332 from rfl, totK_node, atot13331, atot13332]
  decide +kernel

theorem arows13336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13336 = true := by
  rw [show D2M8K2.u13336 = KTree.node D2M8K2.u13334 (nat_lit 29011467) (nat_lit 2436195457) (nat_lit 0) D2M8K2.u13335 from rfl, allE_node, arows13334, irow13336, arows13335]
  all_goals rfl

theorem atot13336 : totK PD2M8K2 D2M8K2.u13336 = [0, 0, 476867725491, 1671988854373, 1229809113775, 127239848573, 1239866073, 0] := by
  rw [show D2M8K2.u13336 = KTree.node D2M8K2.u13334 (nat_lit 29011467) (nat_lit 2436195457) (nat_lit 0) D2M8K2.u13335 from rfl, totK_node, atot13334, atot13335]
  decide +kernel

theorem arows13342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13342 = true := by
  rw [show D2M8K2.u13342 = KTree.node D2M8K2.u13340 (nat_lit 29020406) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u13341 from rfl, allE_node, arows13340, irow13342, arows13341]
  all_goals rfl

theorem atot13342 : totK PD2M8K2 D2M8K2.u13342 = [0, 0, 692077474710, 1872129157179, 983527217318, 60466566712, 0, 0] := by
  rw [show D2M8K2.u13342 = KTree.node D2M8K2.u13340 (nat_lit 29020406) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u13341 from rfl, totK_node, atot13340, atot13341]
  decide +kernel

theorem arows13345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13345 = true := by
  rw [show D2M8K2.u13345 = KTree.node D2M8K2.u13343 (nat_lit 29023814) (nat_lit 4180150381) (nat_lit 0) D2M8K2.u13344 from rfl, allE_node, arows13343, irow13345, arows13344]
  all_goals rfl

theorem atot13345 : totK PD2M8K2 D2M8K2.u13345 = [0, 0, 422543073938, 1491887052023, 1318063521098, 277502514097, 13105450397, 0] := by
  rw [show D2M8K2.u13345 = KTree.node D2M8K2.u13343 (nat_lit 29023814) (nat_lit 4180150381) (nat_lit 0) D2M8K2.u13344 from rfl, totK_node, atot13343, atot13344]
  decide +kernel

theorem arows13349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13349 = true := by
  rw [show D2M8K2.u13349 = KTree.node D2M8K2.u13347 (nat_lit 29027421) (nat_lit 1267753642) (nat_lit 0) D2M8K2.u13348 from rfl, allE_node, arows13347, irow13349, arows13348]
  all_goals rfl

theorem atot13349 : totK PD2M8K2 D2M8K2.u13349 = [0, 198027408646, 803521476682, 1365277093330, 1004773174922, 166947248792, 4720618446, 0] := by
  rw [show D2M8K2.u13349 = KTree.node D2M8K2.u13347 (nat_lit 29027421) (nat_lit 1267753642) (nat_lit 0) D2M8K2.u13348 from rfl, totK_node, atot13347, atot13348]
  decide +kernel

theorem arows13352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13352 = true := by
  rw [show D2M8K2.u13352 = KTree.node D2M8K2.u13350 (nat_lit 29032999) (nat_lit 2391034705) (nat_lit 0) D2M8K2.u13351 from rfl, allE_node, arows13350, irow13352, arows13351]
  all_goals rfl

theorem atot13352 : totK PD2M8K2 D2M8K2.u13352 = [0, 481747983067, 1585866635535, 1348396027382, 187351138557, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13352 = KTree.node D2M8K2.u13350 (nat_lit 29032999) (nat_lit 2391034705) (nat_lit 0) D2M8K2.u13351 from rfl, totK_node, atot13350, atot13351]
  decide +kernel

theorem arows13357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13357 = true := by
  rw [show D2M8K2.u13357 = KTree.node D2M8K2.u13355 (nat_lit 29036364) (nat_lit 2433872619) (nat_lit 0) D2M8K2.u13356 from rfl, allE_node, arows13355, irow13357, arows13356]
  all_goals rfl

theorem atot13357 : totK PD2M8K2 D2M8K2.u13357 = [0, 306771166494, 1231382059040, 1484676423566, 572337730395, 34943716042, 0, 0] := by
  rw [show D2M8K2.u13357 = KTree.node D2M8K2.u13355 (nat_lit 29036364) (nat_lit 2433872619) (nat_lit 0) D2M8K2.u13356 from rfl, totK_node, atot13355, atot13356]
  decide +kernel

theorem arows13360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13360 = true := by
  rw [show D2M8K2.u13360 = KTree.node D2M8K2.u13358 (nat_lit 29039196) (nat_lit 3150177418) (nat_lit 0) D2M8K2.u13359 from rfl, allE_node, arows13358, irow13360, arows13359]
  all_goals rfl

theorem atot13360 : totK PD2M8K2 D2M8K2.u13360 = [0, 377075027189, 1416942383797, 1443204379885, 329022476284, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13360 = KTree.node D2M8K2.u13358 (nat_lit 29039196) (nat_lit 3150177418) (nat_lit 0) D2M8K2.u13359 from rfl, totK_node, atot13358, atot13359]
  decide +kernel

theorem arows13364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13364 = true := by
  rw [show D2M8K2.u13364 = KTree.node D2M8K2.u13362 (nat_lit 29042592) (nat_lit 3592802183) (nat_lit 0) D2M8K2.u13363 from rfl, allE_node, arows13362, irow13364, arows13363]
  all_goals rfl

theorem atot13364 : totK PD2M8K2 D2M8K2.u13364 = [0, 403454291491, 1411599532153, 1424417414361, 340701037835, 13250685261, 0, 0] := by
  rw [show D2M8K2.u13364 = KTree.node D2M8K2.u13362 (nat_lit 29042592) (nat_lit 3592802183) (nat_lit 0) D2M8K2.u13363 from rfl, totK_node, atot13362, atot13363]
  decide +kernel

theorem arows13367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13367 = true := by
  rw [show D2M8K2.u13367 = KTree.node D2M8K2.u13365 (nat_lit 29045576) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u13366 from rfl, allE_node, arows13365, irow13367, arows13366]
  all_goals rfl

theorem atot13367 : totK PD2M8K2 D2M8K2.u13367 = [0, 358558880073, 1515443877801, 1518215608017, 263311369308, 4980514959, 0, 0] := by
  rw [show D2M8K2.u13367 = KTree.node D2M8K2.u13365 (nat_lit 29045576) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u13366 from rfl, totK_node, atot13365, atot13366]
  decide +kernel

theorem arows13374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13374 = true := by
  rw [show D2M8K2.u13374 = KTree.node D2M8K2.u13372 (nat_lit 29052915) (nat_lit 1593185258) (nat_lit 0) D2M8K2.u13373 from rfl, allE_node, arows13372, irow13374, arows13373]
  all_goals rfl

theorem atot13374 : totK PD2M8K2 D2M8K2.u13374 = [0, 0, 504501403361, 1692175758528, 1177735226758, 132562483582, 1138244013, 0] := by
  rw [show D2M8K2.u13374 = KTree.node D2M8K2.u13372 (nat_lit 29052915) (nat_lit 1593185258) (nat_lit 0) D2M8K2.u13373 from rfl, totK_node, atot13372, atot13373]
  decide +kernel

theorem arows13377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13377 = true := by
  rw [show D2M8K2.u13377 = KTree.node D2M8K2.u13375 (nat_lit 29058398) (nat_lit 3939444844) (nat_lit 0) D2M8K2.u13376 from rfl, allE_node, arows13375, irow13377, arows13376]
  all_goals rfl

theorem atot13377 : totK PD2M8K2 D2M8K2.u13377 = [0, 0, 748077446787, 1910808900930, 878692976927, 47135731845, 0, 0] := by
  rw [show D2M8K2.u13377 = KTree.node D2M8K2.u13375 (nat_lit 29058398) (nat_lit 3939444844) (nat_lit 0) D2M8K2.u13376 from rfl, totK_node, atot13375, atot13376]
  decide +kernel

theorem arows13381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13381 = true := by
  rw [show D2M8K2.u13381 = KTree.node D2M8K2.u13379 (nat_lit 29064971) (nat_lit 2769914640) (nat_lit 0) D2M8K2.u13380 from rfl, allE_node, arows13379, irow13381, arows13380]
  all_goals rfl

theorem atot13381 : totK PD2M8K2 D2M8K2.u13381 = [0, 0, 725604261000, 1877429162026, 932883801268, 59851078227, 0, 0] := by
  rw [show D2M8K2.u13381 = KTree.node D2M8K2.u13379 (nat_lit 29064971) (nat_lit 2769914640) (nat_lit 0) D2M8K2.u13380 from rfl, totK_node, atot13379, atot13380]
  decide +kernel

theorem arows13384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13384 = true := by
  rw [show D2M8K2.u13384 = KTree.node D2M8K2.u13382 (nat_lit 29113400) (nat_lit 3670420915) (nat_lit 0) D2M8K2.u13383 from rfl, allE_node, arows13382, irow13384, arows13383]
  all_goals rfl

theorem atot13384 : totK PD2M8K2 D2M8K2.u13384 = [0, 0, 464120057031, 1595346132829, 1260575487365, 214601338314, 4977114383, 0] := by
  rw [show D2M8K2.u13384 = KTree.node D2M8K2.u13382 (nat_lit 29113400) (nat_lit 3670420915) (nat_lit 0) D2M8K2.u13383 from rfl, totK_node, atot13382, atot13383]
  decide +kernel

theorem arows13389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13389 = true := by
  rw [show D2M8K2.u13389 = KTree.node D2M8K2.u13387 (nat_lit 29120409) (nat_lit 1733176255) (nat_lit 0) D2M8K2.u13388 from rfl, allE_node, arows13387, irow13389, arows13388]
  all_goals rfl

theorem atot13389 : totK PD2M8K2 D2M8K2.u13389 = [0, 0, 422854213575, 1598769935931, 1369371837894, 164339551419, 1369150432, 0] := by
  rw [show D2M8K2.u13389 = KTree.node D2M8K2.u13387 (nat_lit 29120409) (nat_lit 1733176255) (nat_lit 0) D2M8K2.u13388 from rfl, totK_node, atot13387, atot13388]
  decide +kernel

theorem arows13392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13392 = true := by
  rw [show D2M8K2.u13392 = KTree.node D2M8K2.u13390 (nat_lit 29123987) (nat_lit 2569826151) (nat_lit 32) D2M8K2.u13391 from rfl, allE_node, arows13390, irow13392, arows13391]
  all_goals rfl

theorem atot13392 : totK PD2M8K2 D2M8K2.u13392 = [0, 0, 408429320751, 1467627286387, 1353492834660, 273039695210, 12983449796, 0] := by
  rw [show D2M8K2.u13392 = KTree.node D2M8K2.u13390 (nat_lit 29123987) (nat_lit 2569826151) (nat_lit 32) D2M8K2.u13391 from rfl, totK_node, atot13390, atot13391]
  decide +kernel

theorem arows13396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13396 = true := by
  rw [show D2M8K2.u13396 = KTree.node D2M8K2.u13394 (nat_lit 29127536) (nat_lit 3751103603) (nat_lit 0) D2M8K2.u13395 from rfl, allE_node, arows13394, irow13396, arows13395]
  all_goals rfl

theorem atot13396 : totK PD2M8K2 D2M8K2.u13396 = [0, 0, 419227003156, 1467396621677, 1335078157271, 283873428722, 13184317400, 0] := by
  rw [show D2M8K2.u13396 = KTree.node D2M8K2.u13394 (nat_lit 29127536) (nat_lit 3751103603) (nat_lit 0) D2M8K2.u13395 from rfl, totK_node, atot13394, atot13395]
  decide +kernel

theorem arows13399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13399 = true := by
  rw [show D2M8K2.u13399 = KTree.node D2M8K2.u13397 (nat_lit 29131334) (nat_lit 3105901015) (nat_lit 0) D2M8K2.u13398 from rfl, allE_node, arows13397, irow13399, arows13398]
  all_goals rfl

theorem atot13399 : totK PD2M8K2 D2M8K2.u13399 = [0, 0, 321312386910, 1489037927822, 1459057224902, 258694757390, 6249254262, 0] := by
  rw [show D2M8K2.u13399 = KTree.node D2M8K2.u13397 (nat_lit 29131334) (nat_lit 3105901015) (nat_lit 0) D2M8K2.u13398 from rfl, totK_node, atot13397, atot13398]
  decide +kernel

theorem arows13405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13405 = true := by
  rw [show D2M8K2.u13405 = KTree.node D2M8K2.u13403 (nat_lit 29135682) (nat_lit 2717696056) (nat_lit 0) D2M8K2.u13404 from rfl, allE_node, arows13403, irow13405, arows13404]
  all_goals rfl

theorem atot13405 : totK PD2M8K2 D2M8K2.u13405 = [0, 0, 0, 569780211705, 1748123050684, 992296909472, 110892860290, 1209030869] := by
  rw [show D2M8K2.u13405 = KTree.node D2M8K2.u13403 (nat_lit 29135682) (nat_lit 2717696056) (nat_lit 0) D2M8K2.u13404 from rfl, totK_node, atot13403, atot13404]
  decide +kernel

theorem arows13408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13408 = true := by
  rw [show D2M8K2.u13408 = KTree.node D2M8K2.u13406 (nat_lit 29145482) (nat_lit 4051115475) (nat_lit 0) D2M8K2.u13407 from rfl, allE_node, arows13406, irow13408, arows13407]
  all_goals rfl

theorem atot13408 : totK PD2M8K2 D2M8K2.u13408 = [0, 0, 0, 857432961157, 1920868232979, 691574246728, 34366385524, 0] := by
  rw [show D2M8K2.u13408 = KTree.node D2M8K2.u13406 (nat_lit 29145482) (nat_lit 4051115475) (nat_lit 0) D2M8K2.u13407 from rfl, totK_node, atot13406, atot13407]
  decide +kernel

theorem arows13412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13412 = true := by
  rw [show D2M8K2.u13412 = KTree.node D2M8K2.u13410 (nat_lit 29152923) (nat_lit 3171461236) (nat_lit 0) D2M8K2.u13411 from rfl, allE_node, arows13410, irow13412, arows13411]
  all_goals rfl

theorem atot13412 : totK PD2M8K2 D2M8K2.u13412 = [0, 0, 357932935788, 1408794803973, 1487668456542, 340381465649, 16122459143, 0] := by
  rw [show D2M8K2.u13412 = KTree.node D2M8K2.u13410 (nat_lit 29152923) (nat_lit 3171461236) (nat_lit 0) D2M8K2.u13411 from rfl, totK_node, atot13410, atot13411]
  decide +kernel

theorem arows13415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13415 = true := by
  rw [show D2M8K2.u13415 = KTree.node D2M8K2.u13413 (nat_lit 29161214) (nat_lit 3850045680) (nat_lit 0) D2M8K2.u13414 from rfl, allE_node, arows13413, irow13415, arows13414]
  all_goals rfl

theorem atot13415 : totK PD2M8K2 D2M8K2.u13415 = [0, 0, 385151244548, 1344516148148, 1459653747799, 432423459086, 24128189171, 0] := by
  rw [show D2M8K2.u13415 = KTree.node D2M8K2.u13413 (nat_lit 29161214) (nat_lit 3850045680) (nat_lit 0) D2M8K2.u13414 from rfl, totK_node, atot13413, atot13414]
  decide +kernel

theorem arows13420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13420 = true := by
  rw [show D2M8K2.u13420 = KTree.node D2M8K2.u13418 (nat_lit 29164900) (nat_lit 3763108413) (nat_lit 0) D2M8K2.u13419 from rfl, allE_node, arows13418, irow13420, arows13419]
  all_goals rfl

theorem atot13420 : totK PD2M8K2 D2M8K2.u13420 = [0, 0, 457769821035, 1592818436754, 1322610609017, 219758781889, 9751947372, 0] := by
  rw [show D2M8K2.u13420 = KTree.node D2M8K2.u13418 (nat_lit 29164900) (nat_lit 3763108413) (nat_lit 0) D2M8K2.u13419 from rfl, totK_node, atot13418, atot13419]
  decide +kernel

theorem arows13423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13423 = true := by
  rw [show D2M8K2.u13423 = KTree.node D2M8K2.u13421 (nat_lit 29168737) (nat_lit 1503033362) (nat_lit 0) D2M8K2.u13422 from rfl, allE_node, arows13421, irow13423, arows13422]
  all_goals rfl

theorem atot13423 : totK PD2M8K2 D2M8K2.u13423 = [0, 0, 487795778056, 1588957651314, 1295731027203, 227757696027, 9882685783, 0] := by
  rw [show D2M8K2.u13423 = KTree.node D2M8K2.u13421 (nat_lit 29168737) (nat_lit 1503033362) (nat_lit 0) D2M8K2.u13422 from rfl, totK_node, atot13421, atot13422]
  decide +kernel

theorem arows13427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13427 = true := by
  rw [show D2M8K2.u13427 = KTree.node D2M8K2.u13425 (nat_lit 29172609) (nat_lit 1501194254) (nat_lit 2) D2M8K2.u13426 from rfl, allE_node, arows13425, irow13427, arows13426]
  all_goals rfl

theorem atot13427 : totK PD2M8K2 D2M8K2.u13427 = [0, 0, 506481935886, 1687730670843, 1304062589426, 184233926142, 2813333534, 0] := by
  rw [show D2M8K2.u13427 = KTree.node D2M8K2.u13425 (nat_lit 29172609) (nat_lit 1501194254) (nat_lit 2) D2M8K2.u13426 from rfl, totK_node, atot13425, atot13426]
  decide +kernel

theorem arows13430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13430 = true := by
  rw [show D2M8K2.u13430 = KTree.node D2M8K2.u13428 (nat_lit 29198734) (nat_lit 2814567161) (nat_lit 136) D2M8K2.u13429 from rfl, allE_node, arows13428, irow13430, arows13429]
  all_goals rfl

theorem atot13430 : totK PD2M8K2 D2M8K2.u13430 = [0, 0, 477536136671, 1600101549183, 1298247705419, 155891865259, 1310166938, 0] := by
  rw [show D2M8K2.u13430 = KTree.node D2M8K2.u13428 (nat_lit 29198734) (nat_lit 2814567161) (nat_lit 136) D2M8K2.u13429 from rfl, totK_node, atot13428, atot13429]
  decide +kernel

theorem arows13438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13438 = true := by
  rw [show D2M8K2.u13438 = KTree.node D2M8K2.u13436 (nat_lit 29202637) (nat_lit 1108320336) (nat_lit 0) D2M8K2.u13437 from rfl, allE_node, arows13436, irow13438, arows13437]
  all_goals rfl

theorem atot13438 : totK PD2M8K2 D2M8K2.u13438 = [0, 0, 432802783436, 1506833193652, 1354721156442, 329240523092, 15013989272, 0] := by
  rw [show D2M8K2.u13438 = KTree.node D2M8K2.u13436 (nat_lit 29202637) (nat_lit 1108320336) (nat_lit 0) D2M8K2.u13437 from rfl, totK_node, atot13436, atot13437]
  decide +kernel

theorem arows13441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13441 = true := by
  rw [show D2M8K2.u13441 = KTree.node D2M8K2.u13439 (nat_lit 29205705) (nat_lit 1745220646) (nat_lit 0) D2M8K2.u13440 from rfl, allE_node, arows13439, irow13441, arows13440]
  all_goals rfl

theorem atot13441 : totK PD2M8K2 D2M8K2.u13441 = [0, 0, 430604357377, 1468886626592, 1368746528846, 289792643574, 13049727234, 0] := by
  rw [show D2M8K2.u13441 = KTree.node D2M8K2.u13439 (nat_lit 29205705) (nat_lit 1745220646) (nat_lit 0) D2M8K2.u13440 from rfl, totK_node, atot13439, atot13440]
  decide +kernel

theorem arows13445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13445 = true := by
  rw [show D2M8K2.u13445 = KTree.node D2M8K2.u13443 (nat_lit 29212558) (nat_lit 2696845357) (nat_lit 2176) D2M8K2.u13444 from rfl, allE_node, arows13443, irow13445, arows13444]
  all_goals rfl

theorem atot13445 : totK PD2M8K2 D2M8K2.u13445 = [0, 0, 413816663244, 1539316418482, 1384386183468, 238511868146, 4980514959, 0] := by
  rw [show D2M8K2.u13445 = KTree.node D2M8K2.u13443 (nat_lit 29212558) (nat_lit 2696845357) (nat_lit 2176) D2M8K2.u13444 from rfl, totK_node, atot13443, atot13444]
  decide +kernel

theorem arows13448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13448 = true := by
  rw [show D2M8K2.u13448 = KTree.node D2M8K2.u13446 (nat_lit 29239067) (nat_lit 1249720352) (nat_lit 0) D2M8K2.u13447 from rfl, allE_node, arows13446, irow13448, arows13447]
  all_goals rfl

theorem atot13448 : totK PD2M8K2 D2M8K2.u13448 = [0, 0, 514720082590, 1649201462836, 1222456565659, 136844700535, 1310517177, 0] := by
  rw [show D2M8K2.u13448 = KTree.node D2M8K2.u13446 (nat_lit 29239067) (nat_lit 1249720352) (nat_lit 0) D2M8K2.u13447 from rfl, totK_node, atot13446, atot13447]
  decide +kernel

theorem arows13453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13453 = true := by
  rw [show D2M8K2.u13453 = KTree.node D2M8K2.u13451 (nat_lit 29242827) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u13452 from rfl, allE_node, arows13451, irow13453, arows13452]
  all_goals rfl

theorem atot13453 : totK PD2M8K2 D2M8K2.u13453 = [0, 0, 442750062884, 1494608211430, 1360610575339, 334840211637, 15066332673, 0] := by
  rw [show D2M8K2.u13453 = KTree.node D2M8K2.u13451 (nat_lit 29242827) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u13452 from rfl, totK_node, atot13451, atot13452]
  decide +kernel

theorem arows13456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13456 = true := by
  rw [show D2M8K2.u13456 = KTree.node D2M8K2.u13454 (nat_lit 29249712) (nat_lit 3678685636) (nat_lit 0) D2M8K2.u13455 from rfl, allE_node, arows13454, irow13456, arows13455]
  all_goals rfl

theorem atot13456 : totK PD2M8K2 D2M8K2.u13456 = [0, 0, 370867354868, 1463770670326, 1441284899467, 301425729831, 13170675918, 0] := by
  rw [show D2M8K2.u13456 = KTree.node D2M8K2.u13454 (nat_lit 29249712) (nat_lit 3678685636) (nat_lit 0) D2M8K2.u13455 from rfl, totK_node, atot13454, atot13455]
  decide +kernel

theorem arows13460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13460 = true := by
  rw [show D2M8K2.u13460 = KTree.node D2M8K2.u13458 (nat_lit 29252794) (nat_lit 2244613949) (nat_lit 0) D2M8K2.u13459 from rfl, allE_node, arows13458, irow13460, arows13459]
  all_goals rfl

theorem atot13460 : totK PD2M8K2 D2M8K2.u13460 = [0, 0, 449599160222, 1525838617311, 1362793460031, 238168411657, 4980514959, 0] := by
  rw [show D2M8K2.u13460 = KTree.node D2M8K2.u13458 (nat_lit 29252794) (nat_lit 2244613949) (nat_lit 0) D2M8K2.u13459 from rfl, totK_node, atot13458, atot13459]
  decide +kernel

theorem arows13463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13463 = true := by
  rw [show D2M8K2.u13463 = KTree.node D2M8K2.u13461 (nat_lit 29279448) (nat_lit 3601261849) (nat_lit 0) D2M8K2.u13462 from rfl, allE_node, arows13461, irow13463, arows13462]
  all_goals rfl

theorem atot13463 : totK PD2M8K2 D2M8K2.u13463 = [0, 0, 705065451965, 1863268467723, 935235648371, 58752935563, 0, 0] := by
  rw [show D2M8K2.u13463 = KTree.node D2M8K2.u13461 (nat_lit 29279448) (nat_lit 3601261849) (nat_lit 0) D2M8K2.u13462 from rfl, totK_node, atot13461, atot13462]
  decide +kernel

theorem arows13469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13469 = true := by
  rw [show D2M8K2.u13469 = KTree.node D2M8K2.u13467 (nat_lit 29283334) (nat_lit 3714763836) (nat_lit 0) D2M8K2.u13468 from rfl, allE_node, arows13467, irow13469, arows13468]
  all_goals rfl

theorem atot13469 : totK PD2M8K2 D2M8K2.u13469 = [0, 0, 420723439655, 1520858959746, 1394492402768, 233643629704, 11694822109, 0] := by
  rw [show D2M8K2.u13469 = KTree.node D2M8K2.u13467 (nat_lit 29283334) (nat_lit 3714763836) (nat_lit 0) D2M8K2.u13468 from rfl, totK_node, atot13467, atot13468]
  decide +kernel

theorem arows13472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13472 = true := by
  rw [show D2M8K2.u13472 = KTree.node D2M8K2.u13470 (nat_lit 29286386) (nat_lit 3170136446) (nat_lit 0) D2M8K2.u13471 from rfl, allE_node, arows13470, irow13472, arows13471]
  all_goals rfl

theorem atot13472 : totK PD2M8K2 D2M8K2.u13472 = [0, 0, 416587547331, 1407956736301, 1368751644028, 362632635516, 13342948984, 0] := by
  rw [show D2M8K2.u13472 = KTree.node D2M8K2.u13470 (nat_lit 29286386) (nat_lit 3170136446) (nat_lit 0) D2M8K2.u13471 from rfl, totK_node, atot13470, atot13471]
  decide +kernel

theorem arows13476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13476 = true := by
  rw [show D2M8K2.u13476 = KTree.node D2M8K2.u13474 (nat_lit 29289816) (nat_lit 3596966893) (nat_lit 0) D2M8K2.u13475 from rfl, allE_node, arows13474, irow13476, arows13475]
  all_goals rfl

theorem atot13476 : totK PD2M8K2 D2M8K2.u13476 = [0, 0, 416781929295, 1446796946423, 1367065907379, 288837533333, 12909266092, 0] := by
  rw [show D2M8K2.u13476 = KTree.node D2M8K2.u13474 (nat_lit 29289816) (nat_lit 3596966893) (nat_lit 0) D2M8K2.u13475 from rfl, totK_node, atot13474, atot13475]
  decide +kernel

theorem arows13479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13479 = true := by
  rw [show D2M8K2.u13479 = KTree.node D2M8K2.u13477 (nat_lit 29293210) (nat_lit 3534709036) (nat_lit 0) D2M8K2.u13478 from rfl, allE_node, arows13477, irow13479, arows13478]
  all_goals rfl

theorem atot13479 : totK PD2M8K2 D2M8K2.u13479 = [0, 0, 442835194728, 1455775019138, 1358234466802, 304360205108, 13110073960, 0] := by
  rw [show D2M8K2.u13479 = KTree.node D2M8K2.u13477 (nat_lit 29293210) (nat_lit 3534709036) (nat_lit 0) D2M8K2.u13478 from rfl, totK_node, atot13477, atot13478]
  decide +kernel

theorem arows13484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13484 = true := by
  rw [show D2M8K2.u13484 = KTree.node D2M8K2.u13482 (nat_lit 29300099) (nat_lit 2883344797) (nat_lit 0) D2M8K2.u13483 from rfl, allE_node, arows13482, irow13484, arows13483]
  all_goals rfl

theorem atot13484 : totK PD2M8K2 D2M8K2.u13484 = [0, 0, 0, 898554207267, 1921111950210, 655233348148, 34004956985, 0] := by
  rw [show D2M8K2.u13484 = KTree.node D2M8K2.u13482 (nat_lit 29300099) (nat_lit 2883344797) (nat_lit 0) D2M8K2.u13483 from rfl, totK_node, atot13482, atot13483]
  decide +kernel

theorem arows13487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13487 = true := by
  rw [show D2M8K2.u13487 = KTree.node D2M8K2.u13485 (nat_lit 29304244) (nat_lit 3816165285) (nat_lit 0) D2M8K2.u13486 from rfl, allE_node, arows13485, irow13487, arows13486]
  all_goals rfl

theorem atot13487 : totK PD2M8K2 D2M8K2.u13487 = [0, 0, 0, 588161568861, 1731238796041, 1057242566289, 117191995178, 1138244013] := by
  rw [show D2M8K2.u13487 = KTree.node D2M8K2.u13485 (nat_lit 29304244) (nat_lit 3816165285) (nat_lit 0) D2M8K2.u13486 from rfl, totK_node, atot13485, atot13486]
  decide +kernel

theorem arows13491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13491 = true := by
  rw [show D2M8K2.u13491 = KTree.node D2M8K2.u13489 (nat_lit 29310898) (nat_lit 2463975601) (nat_lit 2048) D2M8K2.u13490 from rfl, allE_node, arows13489, irow13491, arows13490]
  all_goals rfl

theorem atot13491 : totK PD2M8K2 D2M8K2.u13491 = [0, 0, 0, 820741913792, 1890810473320, 780958473503, 49884878935, 0] := by
  rw [show D2M8K2.u13491 = KTree.node D2M8K2.u13489 (nat_lit 29310898) (nat_lit 2463975601) (nat_lit 2048) D2M8K2.u13490 from rfl, totK_node, atot13489, atot13490]
  decide +kernel

theorem arows13494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13494 = true := by
  rw [show D2M8K2.u13494 = KTree.node D2M8K2.u13492 (nat_lit 29315880) (nat_lit 2138000273) (nat_lit 0) D2M8K2.u13493 from rfl, allE_node, arows13492, irow13494, arows13493]
  all_goals rfl

theorem atot13494 : totK PD2M8K2 D2M8K2.u13494 = [186677387228, 459373490871, 202050743940, 274126505567, 1114362222466, 1080849414683, 209907621525, 4977114383] := by
  rw [show D2M8K2.u13494 = KTree.node D2M8K2.u13492 (nat_lit 29315880) (nat_lit 2138000273) (nat_lit 0) D2M8K2.u13493 from rfl, totK_node, atot13492, atot13493]
  decide +kernel

theorem arows13501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13501 = true := by
  rw [show D2M8K2.u13501 = KTree.node D2M8K2.u13499 (nat_lit 29862205) (nat_lit 1220250907) (nat_lit 0) D2M8K2.u13500 from rfl, allE_node, arows13499, irow13501, arows13500]
  all_goals rfl

theorem atot13501 : totK PD2M8K2 D2M8K2.u13501 = [491099653415, 1619330699165, 1342925878366, 187667605829, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13501 = KTree.node D2M8K2.u13499 (nat_lit 29862205) (nat_lit 1220250907) (nat_lit 0) D2M8K2.u13500 from rfl, totK_node, atot13499, atot13500]
  decide +kernel

theorem arows13504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13504 = true := by
  rw [show D2M8K2.u13504 = KTree.node D2M8K2.u13502 (nat_lit 29869118) (nat_lit 3796942699) (nat_lit 0) D2M8K2.u13503 from rfl, allE_node, arows13502, irow13504, arows13503]
  all_goals rfl

theorem atot13504 : totK PD2M8K2 D2M8K2.u13504 = [367813922564, 1404111272164, 1434392040149, 332076977076, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13504 = KTree.node D2M8K2.u13502 (nat_lit 29869118) (nat_lit 3796942699) (nat_lit 0) D2M8K2.u13503 from rfl, totK_node, atot13502, atot13503]
  decide +kernel

theorem arows13508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13508 = true := by
  rw [show D2M8K2.u13508 = KTree.node D2M8K2.u13506 (nat_lit 29872800) (nat_lit 3697930913) (nat_lit 0) D2M8K2.u13507 from rfl, allE_node, arows13506, irow13508, arows13507]
  all_goals rfl

theorem atot13508 : totK PD2M8K2 D2M8K2.u13508 = [382740559004, 1405306966902, 1413029659151, 334116263607, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13508 = KTree.node D2M8K2.u13506 (nat_lit 29872800) (nat_lit 3697930913) (nat_lit 0) D2M8K2.u13507 from rfl, totK_node, atot13506, atot13507]
  decide +kernel

theorem arows13511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13511 = true := by
  rw [show D2M8K2.u13511 = KTree.node D2M8K2.u13509 (nat_lit 29875990) (nat_lit 2902889508) (nat_lit 0) D2M8K2.u13510 from rfl, allE_node, arows13509, irow13511, arows13510]
  all_goals rfl

theorem atot13511 : totK PD2M8K2 D2M8K2.u13511 = [466691814325, 1537105530115, 1329539192241, 230287024503, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13511 = KTree.node D2M8K2.u13509 (nat_lit 29875990) (nat_lit 2902889508) (nat_lit 0) D2M8K2.u13510 from rfl, totK_node, atot13509, atot13510]
  decide +kernel

theorem arows13516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13516 = true := by
  rw [show D2M8K2.u13516 = KTree.node D2M8K2.u13514 (nat_lit 29879455) (nat_lit 1243699196) (nat_lit 0) D2M8K2.u13515 from rfl, allE_node, arows13514, irow13516, arows13515]
  all_goals rfl

theorem atot13516 : totK PD2M8K2 D2M8K2.u13516 = [198165556517, 1161157526706, 1678711629789, 531966138449, 23418599596, 0, 0, 0] := by
  rw [show D2M8K2.u13516 = KTree.node D2M8K2.u13514 (nat_lit 29879455) (nat_lit 1243699196) (nat_lit 0) D2M8K2.u13515 from rfl, totK_node, atot13514, atot13515]
  decide +kernel

theorem arows13519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13519 = true := by
  rw [show D2M8K2.u13519 = KTree.node D2M8K2.u13517 (nat_lit 29882442) (nat_lit 3370762220) (nat_lit 0) D2M8K2.u13518 from rfl, allE_node, arows13517, irow13519, arows13518]
  all_goals rfl

theorem atot13519 : totK PD2M8K2 D2M8K2.u13519 = [0, 455257737372, 1640424419830, 1243147979169, 168579702786, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13519 = KTree.node D2M8K2.u13517 (nat_lit 29882442) (nat_lit 3370762220) (nat_lit 0) D2M8K2.u13518 from rfl, totK_node, atot13517, atot13518]
  decide +kernel

theorem arows13523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13523 = true := by
  rw [show D2M8K2.u13523 = KTree.node D2M8K2.u13521 (nat_lit 29891359) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u13522 from rfl, allE_node, arows13521, irow13523, arows13522]
  all_goals rfl

theorem atot13523 : totK PD2M8K2 D2M8K2.u13523 = [0, 738844972585, 1872496574460, 890073928572, 49065588925, 0, 0, 0] := by
  rw [show D2M8K2.u13523 = KTree.node D2M8K2.u13521 (nat_lit 29891359) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u13522 from rfl, totK_node, atot13521, atot13522]
  decide +kernel

theorem arows13526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13526 = true := by
  rw [show D2M8K2.u13526 = KTree.node D2M8K2.u13524 (nat_lit 29897978) (nat_lit 3459057828) (nat_lit 0) D2M8K2.u13525 from rfl, allE_node, arows13524, irow13526, arows13525]
  all_goals rfl

theorem atot13526 : totK PD2M8K2 D2M8K2.u13526 = [0, 731739643848, 1885067375708, 889286687019, 43273045437, 0, 0, 0] := by
  rw [show D2M8K2.u13526 = KTree.node D2M8K2.u13524 (nat_lit 29897978) (nat_lit 3459057828) (nat_lit 0) D2M8K2.u13525 from rfl, totK_node, atot13524, atot13525]
  decide +kernel

theorem arows13532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13532 = true := by
  rw [show D2M8K2.u13532 = KTree.node D2M8K2.u13530 (nat_lit 29944285) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u13531 from rfl, allE_node, arows13530, irow13532, arows13531]
  all_goals rfl

theorem atot13532 : totK PD2M8K2 D2M8K2.u13532 = [489670972117, 1582139076993, 1298659724919, 213095166899, 9990256793, 0, 0, 0] := by
  rw [show D2M8K2.u13532 = KTree.node D2M8K2.u13530 (nat_lit 29944285) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u13531 from rfl, totK_node, atot13530, atot13531]
  decide +kernel

theorem arows13535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13535 = true := by
  rw [show D2M8K2.u13535 = KTree.node D2M8K2.u13533 (nat_lit 29948443) (nat_lit 1692414287) (nat_lit 0) D2M8K2.u13534 from rfl, allE_node, arows13533, irow13535, arows13534]
  all_goals rfl

theorem atot13535 : totK PD2M8K2 D2M8K2.u13535 = [382161114357, 1346399827824, 1413491733309, 487290958782, 33448472445, 0, 0, 0] := by
  rw [show D2M8K2.u13535 = KTree.node D2M8K2.u13533 (nat_lit 29948443) (nat_lit 1692414287) (nat_lit 0) D2M8K2.u13534 from rfl, totK_node, atot13533, atot13534]
  decide +kernel

theorem arows13539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13539 = true := by
  rw [show D2M8K2.u13539 = KTree.node D2M8K2.u13537 (nat_lit 29951497) (nat_lit 1502375551) (nat_lit 0) D2M8K2.u13538 from rfl, allE_node, arows13537, irow13539, arows13538]
  all_goals rfl

theorem atot13539 : totK PD2M8K2 D2M8K2.u13539 = [396140694999, 1413369656767, 1434763126759, 336908229175, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13539 = KTree.node D2M8K2.u13537 (nat_lit 29951497) (nat_lit 1502375551) (nat_lit 0) D2M8K2.u13538 from rfl, totK_node, atot13537, atot13538]
  decide +kernel

theorem arows13542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13542 = true := by
  rw [show D2M8K2.u13542 = KTree.node D2M8K2.u13540 (nat_lit 29958421) (nat_lit 1248073642) (nat_lit 0) D2M8K2.u13541 from rfl, allE_node, arows13540, irow13542, arows13541]
  all_goals rfl

theorem atot13542 : totK PD2M8K2 D2M8K2.u13542 = [461523208585, 1551677308184, 1328229679693, 232590696197, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13542 = KTree.node D2M8K2.u13540 (nat_lit 29958421) (nat_lit 1248073642) (nat_lit 0) D2M8K2.u13541 from rfl, totK_node, atot13540, atot13541]
  decide +kernel

theorem arows13547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13547 = true := by
  rw [show D2M8K2.u13547 = KTree.node D2M8K2.u13545 (nat_lit 29962011) (nat_lit 982723940) (nat_lit 0) D2M8K2.u13546 from rfl, allE_node, arows13545, irow13547, arows13546]
  all_goals rfl

theorem atot13547 : totK PD2M8K2 D2M8K2.u13547 = [250158719299, 1244229221751, 1612631172475, 489713966893, 23412759273, 0, 0, 0] := by
  rw [show D2M8K2.u13547 = KTree.node D2M8K2.u13545 (nat_lit 29962011) (nat_lit 982723940) (nat_lit 0) D2M8K2.u13546 from rfl, totK_node, atot13545, atot13546]
  decide +kernel

theorem arows13550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13550 = true := by
  rw [show D2M8K2.u13550 = KTree.node D2M8K2.u13548 (nat_lit 29965316) (nat_lit 3126407821) (nat_lit 0) D2M8K2.u13549 from rfl, allE_node, arows13548, irow13550, arows13549]
  all_goals rfl

theorem atot13550 : totK PD2M8K2 D2M8K2.u13550 = [0, 504394650799, 1669039639319, 1221843672581, 140622270157, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13550 = KTree.node D2M8K2.u13548 (nat_lit 29965316) (nat_lit 3126407821) (nat_lit 0) D2M8K2.u13549 from rfl, totK_node, atot13548, atot13549]
  decide +kernel

theorem arows13554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13554 = true := by
  rw [show D2M8K2.u13554 = KTree.node D2M8K2.u13552 (nat_lit 29971021) (nat_lit 1376906499) (nat_lit 0) D2M8K2.u13553 from rfl, allE_node, arows13552, irow13554, arows13553]
  all_goals rfl

theorem atot13554 : totK PD2M8K2 D2M8K2.u13554 = [0, 588544338497, 1742554069834, 1125330565090, 130938460096, 1162935789, 0, 0] := by
  rw [show D2M8K2.u13554 = KTree.node D2M8K2.u13552 (nat_lit 29971021) (nat_lit 1376906499) (nat_lit 0) D2M8K2.u13553 from rfl, totK_node, atot13552, atot13553]
  decide +kernel

theorem arows13557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13557 = true := by
  rw [show D2M8K2.u13557 = KTree.node D2M8K2.u13555 (nat_lit 29977890) (nat_lit 2763669286) (nat_lit 0) D2M8K2.u13556 from rfl, allE_node, arows13555, irow13557, arows13556]
  all_goals rfl

theorem atot13557 : totK PD2M8K2 D2M8K2.u13557 = [0, 376974790039, 1429294132997, 1369358656046, 291652326333, 12874862223, 0, 0] := by
  rw [show D2M8K2.u13557 = KTree.node D2M8K2.u13555 (nat_lit 29977890) (nat_lit 2763669286) (nat_lit 0) D2M8K2.u13556 from rfl, totK_node, atot13555, atot13556]
  decide +kernel

theorem arows13566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13566 = true := by
  rw [show D2M8K2.u13566 = KTree.node D2M8K2.u13564 (nat_lit 29981584) (nat_lit 3680994124) (nat_lit 0) D2M8K2.u13565 from rfl, allE_node, arows13564, irow13566, arows13565]
  all_goals rfl

theorem atot13566 : totK PD2M8K2 D2M8K2.u13566 = [220861315748, 910741067577, 1429316136654, 883294300920, 127176309044, 3552795014, 0, 0] := by
  rw [show D2M8K2.u13566 = KTree.node D2M8K2.u13564 (nat_lit 29981584) (nat_lit 3680994124) (nat_lit 0) D2M8K2.u13565 from rfl, totK_node, atot13564, atot13565]
  decide +kernel

theorem arows13569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13569 = true := by
  rw [show D2M8K2.u13569 = KTree.node D2M8K2.u13567 (nat_lit 29986883) (nat_lit 2677167457) (nat_lit 0) D2M8K2.u13568 from rfl, allE_node, arows13567, irow13569, arows13568]
  all_goals rfl

theorem atot13569 : totK PD2M8K2 D2M8K2.u13569 = [441529716421, 1581958511610, 1395280106127, 197624131573, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13569 = KTree.node D2M8K2.u13567 (nat_lit 29986883) (nat_lit 2677167457) (nat_lit 0) D2M8K2.u13568 from rfl, totK_node, atot13567, atot13568]
  decide +kernel

theorem arows13573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13573 = true := by
  rw [show D2M8K2.u13573 = KTree.node D2M8K2.u13571 (nat_lit 29990920) (nat_lit 3623312919) (nat_lit 0) D2M8K2.u13572 from rfl, allE_node, arows13571, irow13573, arows13572]
  all_goals rfl

theorem atot13573 : totK PD2M8K2 D2M8K2.u13573 = [408739343578, 1348840676398, 1388512894298, 483801815316, 33488328804, 0, 0, 0] := by
  rw [show D2M8K2.u13573 = KTree.node D2M8K2.u13571 (nat_lit 29990920) (nat_lit 3623312919) (nat_lit 0) D2M8K2.u13572 from rfl, totK_node, atot13571, atot13572]
  decide +kernel

theorem arows13576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13576 = true := by
  rw [show D2M8K2.u13576 = KTree.node D2M8K2.u13574 (nat_lit 29997524) (nat_lit 3258713885) (nat_lit 0) D2M8K2.u13575 from rfl, allE_node, arows13574, irow13576, arows13575]
  all_goals rfl

theorem atot13576 : totK PD2M8K2 D2M8K2.u13576 = [378947756547, 1399820002658, 1444950833075, 347514670538, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13576 = KTree.node D2M8K2.u13574 (nat_lit 29997524) (nat_lit 3258713885) (nat_lit 0) D2M8K2.u13575 from rfl, totK_node, atot13574, atot13575]
  decide +kernel

theorem arows13581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13581 = true := by
  rw [show D2M8K2.u13581 = KTree.node D2M8K2.u13579 (nat_lit 30001050) (nat_lit 3677914707) (nat_lit 0) D2M8K2.u13580 from rfl, allE_node, arows13579, irow13581, arows13580]
  all_goals rfl

theorem atot13581 : totK PD2M8K2 D2M8K2.u13581 = [438968625802, 1551362432150, 1367242070357, 238325545619, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13581 = KTree.node D2M8K2.u13579 (nat_lit 30001050) (nat_lit 3677914707) (nat_lit 0) D2M8K2.u13580 from rfl, totK_node, atot13579, atot13580]
  decide +kernel

theorem arows13584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13584 = true := by
  rw [show D2M8K2.u13584 = KTree.node D2M8K2.u13582 (nat_lit 30004358) (nat_lit 2392905832) (nat_lit 0) D2M8K2.u13583 from rfl, allE_node, arows13582, irow13584, arows13583]
  all_goals rfl

theorem atot13584 : totK PD2M8K2 D2M8K2.u13584 = [92274514042, 958506971206, 1812736528791, 683008534215, 33125647945, 0, 0, 0] := by
  rw [show D2M8K2.u13584 = KTree.node D2M8K2.u13582 (nat_lit 30004358) (nat_lit 2392905832) (nat_lit 0) D2M8K2.u13583 from rfl, totK_node, atot13582, atot13583]
  decide +kernel

theorem arows13588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13588 = true := by
  rw [show D2M8K2.u13588 = KTree.node D2M8K2.u13586 (nat_lit 30008209) (nat_lit 1402184746) (nat_lit 0) D2M8K2.u13587 from rfl, allE_node, arows13586, irow13588, arows13587]
  all_goals rfl

theorem atot13588 : totK PD2M8K2 D2M8K2.u13588 = [0, 459925099327, 1634848577562, 1326282134004, 156916570938, 1239866073, 0, 0] := by
  rw [show D2M8K2.u13588 = KTree.node D2M8K2.u13586 (nat_lit 30008209) (nat_lit 1402184746) (nat_lit 0) D2M8K2.u13587 from rfl, totK_node, atot13586, atot13587]
  decide +kernel

theorem arows13591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13591 = true := by
  rw [show D2M8K2.u13591 = KTree.node D2M8K2.u13589 (nat_lit 30016847) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u13590 from rfl, allE_node, arows13589, irow13591, arows13590]
  all_goals rfl

theorem atot13591 : totK PD2M8K2 D2M8K2.u13591 = [0, 428503417529, 1466836633973, 1328433302340, 301786236307, 13105450397, 0, 0] := by
  rw [show D2M8K2.u13591 = KTree.node D2M8K2.u13589 (nat_lit 30016847) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u13590 from rfl, totK_node, atot13589, atot13590]
  decide +kernel

theorem arows13597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13597 = true := by
  rw [show D2M8K2.u13597 = KTree.node D2M8K2.u13595 (nat_lit 30020059) (nat_lit 2238416565) (nat_lit 0) D2M8K2.u13596 from rfl, allE_node, arows13595, irow13597, arows13596]
  all_goals rfl

theorem atot13597 : totK PD2M8K2 D2M8K2.u13597 = [0, 462319910073, 1545203026807, 1289746289307, 198387548519, 4720618446, 0, 0] := by
  rw [show D2M8K2.u13597 = KTree.node D2M8K2.u13595 (nat_lit 30020059) (nat_lit 2238416565) (nat_lit 0) D2M8K2.u13596 from rfl, totK_node, atot13595, atot13596]
  decide +kernel

theorem arows13600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13600 = true := by
  rw [show D2M8K2.u13600 = KTree.node D2M8K2.u13598 (nat_lit 30023999) (nat_lit 2760641158) (nat_lit 0) D2M8K2.u13599 from rfl, allE_node, arows13598, irow13600, arows13599]
  all_goals rfl

theorem atot13600 : totK PD2M8K2 D2M8K2.u13600 = [397873363933, 1279705035762, 1337282794338, 561238803007, 45305129206, 0, 0, 0] := by
  rw [show D2M8K2.u13600 = KTree.node D2M8K2.u13598 (nat_lit 30023999) (nat_lit 2760641158) (nat_lit 0) D2M8K2.u13599 from rfl, totK_node, atot13598, atot13599]
  decide +kernel

theorem arows13604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13604 = true := by
  rw [show D2M8K2.u13604 = KTree.node D2M8K2.u13602 (nat_lit 30032788) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u13603 from rfl, allE_node, arows13602, irow13604, arows13603]
  all_goals rfl

theorem atot13604 : totK PD2M8K2 D2M8K2.u13604 = [422898550529, 1577718847113, 1404410235595, 195984114466, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13604 = KTree.node D2M8K2.u13602 (nat_lit 30032788) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u13603 from rfl, totK_node, atot13602, atot13603]
  decide +kernel

theorem arows13607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13607 = true := by
  rw [show D2M8K2.u13607 = KTree.node D2M8K2.u13605 (nat_lit 30036251) (nat_lit 2697785286) (nat_lit 0) D2M8K2.u13606 from rfl, allE_node, arows13605, irow13607, arows13606]
  all_goals rfl

theorem atot13607 : totK PD2M8K2 D2M8K2.u13607 = [400370480135, 1431302639841, 1405897616990, 327325895881, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13607 = KTree.node D2M8K2.u13605 (nat_lit 30036251) (nat_lit 2697785286) (nat_lit 0) D2M8K2.u13606 from rfl, totK_node, atot13605, atot13606]
  decide +kernel

theorem arows13612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13612 = true := by
  rw [show D2M8K2.u13612 = KTree.node D2M8K2.u13610 (nat_lit 30039708) (nat_lit 3509432056) (nat_lit 0) D2M8K2.u13611 from rfl, allE_node, arows13610, irow13612, arows13611]
  all_goals rfl

theorem atot13612 : totK PD2M8K2 D2M8K2.u13612 = [423568743631, 1444865670694, 1365365088418, 332006150130, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13612 = KTree.node D2M8K2.u13610 (nat_lit 30039708) (nat_lit 3509432056) (nat_lit 0) D2M8K2.u13611 from rfl, totK_node, atot13610, atot13611]
  decide +kernel

theorem arows13615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13615 = true := by
  rw [show D2M8K2.u13615 = KTree.node D2M8K2.u13613 (nat_lit 30046691) (nat_lit 2226756917) (nat_lit 0) D2M8K2.u13614 from rfl, allE_node, arows13613, irow13615, arows13614]
  all_goals rfl

theorem atot13615 : totK PD2M8K2 D2M8K2.u13615 = [0, 837299378747, 1934590554300, 737198505561, 39140274892, 0, 0, 0] := by
  rw [show D2M8K2.u13615 = KTree.node D2M8K2.u13613 (nat_lit 30046691) (nat_lit 2226756917) (nat_lit 0) D2M8K2.u13614 from rfl, totK_node, atot13613, atot13614]
  decide +kernel

theorem arows13619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13619 = true := by
  rw [show D2M8K2.u13619 = KTree.node D2M8K2.u13617 (nat_lit 30053998) (nat_lit 3675649599) (nat_lit 0) D2M8K2.u13618 from rfl, allE_node, arows13617, irow13619, arows13618]
  all_goals rfl

theorem atot13619 : totK PD2M8K2 D2M8K2.u13619 = [0, 552142089101, 1731894469570, 1137719217863, 113790395095, 1138244013, 0, 0] := by
  rw [show D2M8K2.u13619 = KTree.node D2M8K2.u13617 (nat_lit 30053998) (nat_lit 3675649599) (nat_lit 0) D2M8K2.u13618 from rfl, totK_node, atot13617, atot13618]
  decide +kernel

theorem arows13622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13622 = true := by
  rw [show D2M8K2.u13622 = KTree.node D2M8K2.u13620 (nat_lit 30060674) (nat_lit 4123374192) (nat_lit 0) D2M8K2.u13621 from rfl, allE_node, arows13620, irow13622, arows13621]
  all_goals rfl

theorem atot13622 : totK PD2M8K2 D2M8K2.u13622 = [0, 666511639421, 1798666151760, 991560928515, 84487235099, 1095107716, 0, 0] := by
  rw [show D2M8K2.u13622 = KTree.node D2M8K2.u13620 (nat_lit 30060674) (nat_lit 4123374192) (nat_lit 0) D2M8K2.u13621 from rfl, totK_node, atot13620, atot13621]
  decide +kernel

theorem arows13629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13629 = true := by
  rw [show D2M8K2.u13629 = KTree.node D2M8K2.u13627 (nat_lit 30067931) (nat_lit 2356742145) (nat_lit 0) D2M8K2.u13628 from rfl, allE_node, arows13627, irow13629, arows13628]
  all_goals rfl

theorem atot13629 : totK PD2M8K2 D2M8K2.u13629 = [421765020787, 1170124591897, 1087495844212, 715481828406, 156586214729, 3882006667, 0, 0] := by
  rw [show D2M8K2.u13629 = KTree.node D2M8K2.u13627 (nat_lit 30067931) (nat_lit 2356742145) (nat_lit 0) D2M8K2.u13628 from rfl, totK_node, atot13627, atot13628]
  decide +kernel

theorem arows13632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13632 = true := by
  rw [show D2M8K2.u13632 = KTree.node D2M8K2.u13630 (nat_lit 30071527) (nat_lit 2376183818) (nat_lit 0) D2M8K2.u13631 from rfl, allE_node, arows13630, irow13632, arows13631]
  all_goals rfl

theorem atot13632 : totK PD2M8K2 D2M8K2.u13632 = [348618394764, 1423260251084, 1512997756756, 373705500806, 25092327913, 0, 0, 0] := by
  rw [show D2M8K2.u13632 = KTree.node D2M8K2.u13630 (nat_lit 30071527) (nat_lit 2376183818) (nat_lit 0) D2M8K2.u13631 from rfl, totK_node, atot13630, atot13631]
  decide +kernel

theorem arows13636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13636 = true := by
  rw [show D2M8K2.u13636 = KTree.node D2M8K2.u13634 (nat_lit 30074805) (nat_lit 1725144023) (nat_lit 0) D2M8K2.u13635 from rfl, allE_node, arows13634, irow13636, arows13635]
  all_goals rfl

theorem atot13636 : totK PD2M8K2 D2M8K2.u13636 = [412785445587, 1440202690261, 1417242366679, 354888893952, 11868314391, 0, 0, 0] := by
  rw [show D2M8K2.u13636 = KTree.node D2M8K2.u13634 (nat_lit 30074805) (nat_lit 1725144023) (nat_lit 0) D2M8K2.u13635 from rfl, totK_node, atot13634, atot13635]
  decide +kernel

theorem arows13639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13639 = true := by
  rw [show D2M8K2.u13639 = KTree.node D2M8K2.u13637 (nat_lit 30078515) (nat_lit 2864044449) (nat_lit 0) D2M8K2.u13638 from rfl, allE_node, arows13637, irow13639, arows13638]
  all_goals rfl

theorem atot13639 : totK PD2M8K2 D2M8K2.u13639 = [413029494510, 1439726424734, 1404151697310, 328470341875, 13077537112, 0, 0, 0] := by
  rw [show D2M8K2.u13639 = KTree.node D2M8K2.u13637 (nat_lit 30078515) (nat_lit 2864044449) (nat_lit 0) D2M8K2.u13638 from rfl, totK_node, atot13637, atot13638]
  decide +kernel

theorem arows13644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13644 = true := by
  rw [show D2M8K2.u13644 = KTree.node D2M8K2.u13642 (nat_lit 30085067) (nat_lit 2902669009) (nat_lit 0) D2M8K2.u13643 from rfl, allE_node, arows13642, irow13644, arows13643]
  all_goals rfl

theorem atot13644 : totK PD2M8K2 D2M8K2.u13644 = [442799796658, 1469976687881, 1372985003852, 333423484064, 13314450774, 0, 0, 0] := by
  rw [show D2M8K2.u13644 = KTree.node D2M8K2.u13642 (nat_lit 30085067) (nat_lit 2902669009) (nat_lit 0) D2M8K2.u13643 from rfl, totK_node, atot13642, atot13643]
  decide +kernel

theorem arows13647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13647 = true := by
  rw [show D2M8K2.u13647 = KTree.node D2M8K2.u13645 (nat_lit 30088202) (nat_lit 3281869230) (nat_lit 0) D2M8K2.u13646 from rfl, allE_node, arows13645, irow13647, arows13646]
  all_goals rfl

theorem atot13647 : totK PD2M8K2 D2M8K2.u13647 = [0, 735632678952, 1886910345387, 899314163032, 51755464200, 0, 0, 0] := by
  rw [show D2M8K2.u13647 = KTree.node D2M8K2.u13645 (nat_lit 30088202) (nat_lit 3281869230) (nat_lit 0) D2M8K2.u13646 from rfl, totK_node, atot13645, atot13646]
  decide +kernel

theorem arows13651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13651 = true := by
  rw [show D2M8K2.u13651 = KTree.node D2M8K2.u13649 (nat_lit 30092117) (nat_lit 2294122155) (nat_lit 0) D2M8K2.u13650 from rfl, allE_node, arows13649, irow13651, arows13650]
  all_goals rfl

theorem atot13651 : totK PD2M8K2 D2M8K2.u13651 = [0, 512985074010, 1641273048449, 1324866180989, 164010112984, 1310285577, 0, 0] := by
  rw [show D2M8K2.u13651 = KTree.node D2M8K2.u13649 (nat_lit 30092117) (nat_lit 2294122155) (nat_lit 0) D2M8K2.u13650 from rfl, totK_node, atot13649, atot13650]
  decide +kernel

theorem arows13654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13654 = true := by
  rw [show D2M8K2.u13654 = KTree.node D2M8K2.u13652 (nat_lit 30096986) (nat_lit 4113597546) (nat_lit 0) D2M8K2.u13653 from rfl, allE_node, arows13652, irow13654, arows13653]
  all_goals rfl

theorem atot13654 : totK PD2M8K2 D2M8K2.u13654 = [0, 466844589533, 1540949876876, 1337816651523, 218440556936, 4879840392, 0, 0] := by
  rw [show D2M8K2.u13654 = KTree.node D2M8K2.u13652 (nat_lit 30096986) (nat_lit 4113597546) (nat_lit 0) D2M8K2.u13653 from rfl, totK_node, atot13652, atot13653]
  decide +kernel

theorem arows13660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13660 = true := by
  rw [show D2M8K2.u13660 = KTree.node D2M8K2.u13658 (nat_lit 30100995) (nat_lit 2974846019) (nat_lit 0) D2M8K2.u13659 from rfl, allE_node, arows13658, irow13660, arows13659]
  all_goals rfl

theorem atot13660 : totK PD2M8K2 D2M8K2.u13660 = [0, 450066004870, 1577244307355, 1324958892231, 215336459515, 4931404646, 0, 0] := by
  rw [show D2M8K2.u13660 = KTree.node D2M8K2.u13658 (nat_lit 30100995) (nat_lit 2974846019) (nat_lit 0) D2M8K2.u13659 from rfl, totK_node, atot13658, atot13659]
  decide +kernel

theorem arows13663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13663 = true := by
  rw [show D2M8K2.u13663 = KTree.node D2M8K2.u13661 (nat_lit 30107647) (nat_lit 1764320284) (nat_lit 0) D2M8K2.u13662 from rfl, allE_node, arows13661, irow13663, arows13662]
  all_goals rfl

theorem atot13663 : totK PD2M8K2 D2M8K2.u13663 = [0, 360672467931, 1361157417988, 1429561822176, 397668547187, 21751168066, 0, 0] := by
  rw [show D2M8K2.u13663 = KTree.node D2M8K2.u13661 (nat_lit 30107647) (nat_lit 1764320284) (nat_lit 0) D2M8K2.u13662 from rfl, totK_node, atot13661, atot13662]
  decide +kernel

theorem arows13667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13667 = true := by
  rw [show D2M8K2.u13667 = KTree.node D2M8K2.u13665 (nat_lit 30110983) (nat_lit 2050303629) (nat_lit 0) D2M8K2.u13666 from rfl, allE_node, arows13665, irow13667, arows13666]
  all_goals rfl

theorem atot13667 : totK PD2M8K2 D2M8K2.u13667 = [0, 470990318115, 1599731709928, 1357001754921, 186262597638, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13667 = KTree.node D2M8K2.u13665 (nat_lit 30110983) (nat_lit 2050303629) (nat_lit 0) D2M8K2.u13666 from rfl, totK_node, atot13665, atot13666]
  decide +kernel

theorem arows13670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13670 = true := by
  rw [show D2M8K2.u13670 = KTree.node D2M8K2.u13668 (nat_lit 30117919) (nat_lit 998729329) (nat_lit 0) D2M8K2.u13669 from rfl, allE_node, arows13668, irow13670, arows13669]
  all_goals rfl

theorem atot13670 : totK PD2M8K2 D2M8K2.u13670 = [0, 382010816392, 1429852602644, 1412018783673, 292032172873, 12891658009, 0, 0] := by
  rw [show D2M8K2.u13670 = KTree.node D2M8K2.u13668 (nat_lit 30117919) (nat_lit 998729329) (nat_lit 0) D2M8K2.u13669 from rfl, totK_node, atot13668, atot13669]
  decide +kernel

theorem arows13675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13675 = true := by
  rw [show D2M8K2.u13675 = KTree.node D2M8K2.u13673 (nat_lit 30121187) (nat_lit 2938109483) (nat_lit 0) D2M8K2.u13674 from rfl, allE_node, arows13673, irow13675, arows13674]
  all_goals rfl

theorem atot13675 : totK PD2M8K2 D2M8K2.u13675 = [0, 394621489466, 1414321882387, 1398880230358, 298273318160, 13092379805, 0, 0] := by
  rw [show D2M8K2.u13675 = KTree.node D2M8K2.u13673 (nat_lit 30121187) (nat_lit 2938109483) (nat_lit 0) D2M8K2.u13674 from rfl, totK_node, atot13673, atot13674]
  decide +kernel

theorem arows13678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13678 = true := by
  rw [show D2M8K2.u13678 = KTree.node D2M8K2.u13676 (nat_lit 30124822) (nat_lit 2902889508) (nat_lit 0) D2M8K2.u13677 from rfl, allE_node, arows13676, irow13678, arows13677]
  all_goals rfl

theorem atot13678 : totK PD2M8K2 D2M8K2.u13678 = [0, 478618223945, 1542713269329, 1309463724501, 208448522664, 4934531535, 0, 0] := by
  rw [show D2M8K2.u13678 = KTree.node D2M8K2.u13676 (nat_lit 30124822) (nat_lit 2902889508) (nat_lit 0) D2M8K2.u13677 from rfl, totK_node, atot13676, atot13677]
  decide +kernel

theorem arows13682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13682 = true := by
  rw [show D2M8K2.u13682 = KTree.node D2M8K2.u13680 (nat_lit 30128308) (nat_lit 4069712062) (nat_lit 0) D2M8K2.u13681 from rfl, allE_node, arows13680, irow13682, arows13681]
  all_goals rfl

theorem atot13682 : totK PD2M8K2 D2M8K2.u13682 = [0, 182307975947, 1156447698861, 1696535787763, 496438838213, 23141784327, 0, 0] := by
  rw [show D2M8K2.u13682 = KTree.node D2M8K2.u13680 (nat_lit 30128308) (nat_lit 4069712062) (nat_lit 0) D2M8K2.u13681 from rfl, totK_node, atot13680, atot13681]
  decide +kernel

theorem arows13685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13685 = true := by
  rw [show D2M8K2.u13685 = KTree.node D2M8K2.u13683 (nat_lit 30131376) (nat_lit 3555022825) (nat_lit 0) D2M8K2.u13684 from rfl, allE_node, arows13683, irow13685, arows13684]
  all_goals rfl

theorem atot13685 : totK PD2M8K2 D2M8K2.u13685 = [0, 0, 499255464371, 1641502468140, 1170887783104, 165635478076, 1369150432, 0] := by
  rw [show D2M8K2.u13685 = KTree.node D2M8K2.u13683 (nat_lit 30131376) (nat_lit 3555022825) (nat_lit 0) D2M8K2.u13684 from rfl, totK_node, atot13683, atot13684]
  decide +kernel

theorem arows13693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13693 = true := by
  rw [show D2M8K2.u13693 = KTree.node D2M8K2.u13691 (nat_lit 30140806) (nat_lit 2465688847) (nat_lit 0) D2M8K2.u13692 from rfl, allE_node, arows13691, irow13693, arows13692]
  all_goals rfl

theorem atot13693 : totK PD2M8K2 D2M8K2.u13693 = [0, 0, 796652084988, 1891805024043, 747184980168, 44358804441, 0, 0] := by
  rw [show D2M8K2.u13693 = KTree.node D2M8K2.u13691 (nat_lit 30140806) (nat_lit 2465688847) (nat_lit 0) D2M8K2.u13692 from rfl, totK_node, atot13691, atot13692]
  decide +kernel

theorem arows13696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13696 = true := by
  rw [show D2M8K2.u13696 = KTree.node D2M8K2.u13694 (nat_lit 30147430) (nat_lit 2470277421) (nat_lit 0) D2M8K2.u13695 from rfl, allE_node, arows13694, irow13696, arows13695]
  all_goals rfl

theorem atot13696 : totK PD2M8K2 D2M8K2.u13696 = [0, 179595312347, 1030240235410, 1654872640048, 628958827468, 41758926042, 0, 0] := by
  rw [show D2M8K2.u13696 = KTree.node D2M8K2.u13694 (nat_lit 30147430) (nat_lit 2470277421) (nat_lit 0) D2M8K2.u13695 from rfl, totK_node, atot13694, atot13695]
  decide +kernel

theorem arows13700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13700 = true := by
  rw [show D2M8K2.u13700 = KTree.node D2M8K2.u13698 (nat_lit 30194022) (nat_lit 2460864383) (nat_lit 0) D2M8K2.u13699 from rfl, allE_node, arows13698, irow13700, arows13699]
  all_goals rfl

theorem atot13700 : totK PD2M8K2 D2M8K2.u13700 = [0, 466054209438, 1566276798245, 1357497088975, 194301407050, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13700 = KTree.node D2M8K2.u13698 (nat_lit 30194022) (nat_lit 2460864383) (nat_lit 0) D2M8K2.u13699 from rfl, totK_node, atot13698, atot13699]
  decide +kernel

theorem arows13703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13703 = true := by
  rw [show D2M8K2.u13703 = KTree.node D2M8K2.u13701 (nat_lit 30198528) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u13702 from rfl, allE_node, arows13701, irow13703, arows13702]
  all_goals rfl

theorem atot13703 : totK PD2M8K2 D2M8K2.u13703 = [0, 485140981043, 1582238413209, 1327617001561, 244010683745, 5284349065, 0, 0] := by
  rw [show D2M8K2.u13703 = KTree.node D2M8K2.u13701 (nat_lit 30198528) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u13702 from rfl, totK_node, atot13701, atot13702]
  decide +kernel

theorem arows13708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13708 = true := by
  rw [show D2M8K2.u13708 = KTree.node D2M8K2.u13706 (nat_lit 30201700) (nat_lit 3776536428) (nat_lit 0) D2M8K2.u13707 from rfl, allE_node, arows13706, irow13708, arows13707]
  all_goals rfl

theorem atot13708 : totK PD2M8K2 D2M8K2.u13708 = [0, 377088379950, 1401158145016, 1456099492752, 328994404020, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13708 = KTree.node D2M8K2.u13706 (nat_lit 30201700) (nat_lit 3776536428) (nat_lit 0) D2M8K2.u13707 from rfl, totK_node, atot13706, atot13707]
  decide +kernel

theorem arows13711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13711 = true := by
  rw [show D2M8K2.u13711 = KTree.node D2M8K2.u13709 (nat_lit 30208998) (nat_lit 2721519369) (nat_lit 0) D2M8K2.u13710 from rfl, allE_node, arows13709, irow13711, arows13710]
  all_goals rfl

theorem atot13711 : totK PD2M8K2 D2M8K2.u13711 = [0, 469375358738, 1577598427010, 1334854386234, 214340429694, 4917269347, 0, 0] := by
  rw [show D2M8K2.u13711 = KTree.node D2M8K2.u13709 (nat_lit 30208998) (nat_lit 2721519369) (nat_lit 0) D2M8K2.u13710 from rfl, totK_node, atot13709, atot13710]
  decide +kernel

theorem arows13715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13715 = true := by
  rw [show D2M8K2.u13715 = KTree.node D2M8K2.u13713 (nat_lit 30233140) (nat_lit 3917601996) (nat_lit 0) D2M8K2.u13714 from rfl, allE_node, arows13713, irow13715, arows13714]
  all_goals rfl

theorem atot13715 : totK PD2M8K2 D2M8K2.u13715 = [0, 418147218595, 1428239649192, 1377449618605, 329548593744, 13684302317, 0, 0] := by
  rw [show D2M8K2.u13715 = KTree.node D2M8K2.u13713 (nat_lit 30233140) (nat_lit 3917601996) (nat_lit 0) D2M8K2.u13714 from rfl, totK_node, atot13713, atot13714]
  decide +kernel

theorem arows13718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13718 = true := by
  rw [show D2M8K2.u13718 = KTree.node D2M8K2.u13716 (nat_lit 30237026) (nat_lit 4114323956) (nat_lit 0) D2M8K2.u13717 from rfl, allE_node, arows13716, irow13718, arows13717]
  all_goals rfl

theorem atot13718 : totK PD2M8K2 D2M8K2.u13718 = [0, 331012969055, 1508733449105, 1567726635550, 239621112874, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13718 = KTree.node D2M8K2.u13716 (nat_lit 30237026) (nat_lit 4114323956) (nat_lit 0) D2M8K2.u13717 from rfl, totK_node, atot13716, atot13717]
  decide +kernel

theorem arows13724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13724 = true := by
  rw [show D2M8K2.u13724 = KTree.node D2M8K2.u13722 (nat_lit 30244428) (nat_lit 3133996878) (nat_lit 0) D2M8K2.u13723 from rfl, allE_node, arows13722, irow13724, arows13723]
  all_goals rfl

theorem atot13724 : totK PD2M8K2 D2M8K2.u13724 = [0, 437333739896, 1489711350348, 1400701135985, 289339436770, 6527558394, 0, 0] := by
  rw [show D2M8K2.u13724 = KTree.node D2M8K2.u13722 (nat_lit 30244428) (nat_lit 3133996878) (nat_lit 0) D2M8K2.u13723 from rfl, totK_node, atot13722, atot13723]
  decide +kernel

theorem arows13727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13727 = true := by
  rw [show D2M8K2.u13727 = KTree.node D2M8K2.u13725 (nat_lit 30247500) (nat_lit 3529847835) (nat_lit 0) D2M8K2.u13726 from rfl, allE_node, arows13725, irow13727, arows13726]
  all_goals rfl

theorem atot13727 : totK PD2M8K2 D2M8K2.u13727 = [0, 378503758704, 1403775685390, 1430780768187, 323296797920, 13088430220, 0, 0] := by
  rw [show D2M8K2.u13727 = KTree.node D2M8K2.u13725 (nat_lit 30247500) (nat_lit 3529847835) (nat_lit 0) D2M8K2.u13726 from rfl, totK_node, atot13725, atot13726]
  decide +kernel

theorem arows13731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13731 = true := by
  rw [show D2M8K2.u13731 = KTree.node D2M8K2.u13729 (nat_lit 30251233) (nat_lit 1552380795) (nat_lit 0) D2M8K2.u13730 from rfl, allE_node, arows13729, irow13731, arows13730]
  all_goals rfl

theorem atot13731 : totK PD2M8K2 D2M8K2.u13731 = [0, 416049544855, 1512002434707, 1435195566216, 259271512208, 5053789144, 0, 0] := by
  rw [show D2M8K2.u13731 = KTree.node D2M8K2.u13729 (nat_lit 30251233) (nat_lit 1552380795) (nat_lit 0) D2M8K2.u13730 from rfl, totK_node, atot13729, atot13730]
  decide +kernel

theorem arows13734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13734 = true := by
  rw [show D2M8K2.u13734 = KTree.node D2M8K2.u13732 (nat_lit 30275561) (nat_lit 1278470880) (nat_lit 0) D2M8K2.u13733 from rfl, allE_node, arows13732, irow13734, arows13733]
  all_goals rfl

theorem atot13734 : totK PD2M8K2 D2M8K2.u13734 = [0, 418368644866, 1440026983280, 1357689625942, 319981329176, 13851206879, 0, 0] := by
  rw [show D2M8K2.u13734 = KTree.node D2M8K2.u13732 (nat_lit 30275561) (nat_lit 1278470880) (nat_lit 0) D2M8K2.u13733 from rfl, totK_node, atot13732, atot13733]
  decide +kernel

theorem arows13739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13739 = true := by
  rw [show D2M8K2.u13739 = KTree.node D2M8K2.u13737 (nat_lit 30282667) (nat_lit 1521807080) (nat_lit 0) D2M8K2.u13738 from rfl, allE_node, arows13737, irow13739, arows13738]
  all_goals rfl

theorem atot13739 : totK PD2M8K2 D2M8K2.u13739 = [0, 399128654420, 1485887797651, 1417422424451, 258648289963, 9521435666, 0, 0] := by
  rw [show D2M8K2.u13739 = KTree.node D2M8K2.u13737 (nat_lit 30282667) (nat_lit 1521807080) (nat_lit 0) D2M8K2.u13738 from rfl, totK_node, atot13737, atot13738]
  decide +kernel

theorem arows13742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13742 = true := by
  rw [show D2M8K2.u13742 = KTree.node D2M8K2.u13740 (nat_lit 30286152) (nat_lit 3524105691) (nat_lit 0) D2M8K2.u13741 from rfl, allE_node, arows13740, irow13742, arows13741]
  all_goals rfl

theorem atot13742 : totK PD2M8K2 D2M8K2.u13742 = [0, 399367273510, 1437968234545, 1407529975415, 305356137606, 13064381701, 0, 0] := by
  rw [show D2M8K2.u13742 = KTree.node D2M8K2.u13740 (nat_lit 30286152) (nat_lit 3524105691) (nat_lit 0) D2M8K2.u13741 from rfl, totK_node, atot13740, atot13741]
  decide +kernel

theorem arows13746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13746 = true := by
  rw [show D2M8K2.u13746 = KTree.node D2M8K2.u13744 (nat_lit 30289364) (nat_lit 3673606522) (nat_lit 0) D2M8K2.u13745 from rfl, allE_node, arows13744, irow13746, arows13745]
  all_goals rfl

theorem atot13746 : totK PD2M8K2 D2M8K2.u13746 = [0, 422902294394, 1530306073657, 1398379385432, 230945357815, 4678454933, 0, 0] := by
  rw [show D2M8K2.u13746 = KTree.node D2M8K2.u13744 (nat_lit 30289364) (nat_lit 3673606522) (nat_lit 0) D2M8K2.u13745 from rfl, totK_node, atot13744, atot13745]
  decide +kernel

theorem arows13749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13749 = true := by
  rw [show D2M8K2.u13749 = KTree.node D2M8K2.u13747 (nat_lit 30317341) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u13748 from rfl, allE_node, arows13747, irow13749, arows13748]
  all_goals rfl

theorem atot13749 : totK PD2M8K2 D2M8K2.u13749 = [0, 420136633399, 1510290546226, 1387388193015, 247779720285, 5253160287, 0, 0] := by
  rw [show D2M8K2.u13749 = KTree.node D2M8K2.u13747 (nat_lit 30317341) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u13748 from rfl, totK_node, atot13747, atot13748]
  decide +kernel

theorem arows13756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13756 = true := by
  rw [show D2M8K2.u13756 = KTree.node D2M8K2.u13754 (nat_lit 30321204) (nat_lit 3070713454) (nat_lit 0) D2M8K2.u13755 from rfl, allE_node, arows13754, irow13756, arows13755]
  all_goals rfl

theorem atot13756 : totK PD2M8K2 D2M8K2.u13756 = [0, 432782112006, 1466114613132, 1422696996870, 333482944872, 9575627623, 0, 0] := by
  rw [show D2M8K2.u13756 = KTree.node D2M8K2.u13754 (nat_lit 30321204) (nat_lit 3070713454) (nat_lit 0) D2M8K2.u13755 from rfl, totK_node, atot13754, atot13755]
  decide +kernel

theorem arows13759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13759 = true := by
  rw [show D2M8K2.u13759 = KTree.node D2M8K2.u13757 (nat_lit 30324753) (nat_lit 1506279371) (nat_lit 0) D2M8K2.u13758 from rfl, allE_node, arows13757, irow13759, arows13758]
  all_goals rfl

theorem atot13759 : totK PD2M8K2 D2M8K2.u13759 = [0, 457660261819, 1533574157716, 1389681062004, 246477154145, 5138457373, 0, 0] := by
  rw [show D2M8K2.u13759 = KTree.node D2M8K2.u13757 (nat_lit 30324753) (nat_lit 1506279371) (nat_lit 0) D2M8K2.u13758 from rfl, totK_node, atot13757, atot13758]
  decide +kernel

theorem arows13763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13763 = true := by
  rw [show D2M8K2.u13763 = KTree.node D2M8K2.u13761 (nat_lit 30328272) (nat_lit 3718232426) (nat_lit 0) D2M8K2.u13762 from rfl, allE_node, arows13761, irow13763, arows13762]
  all_goals rfl

theorem atot13763 : totK PD2M8K2 D2M8K2.u13763 = [0, 454961420763, 1535180811849, 1383598590547, 254481936309, 5193381917, 0, 0] := by
  rw [show D2M8K2.u13763 = KTree.node D2M8K2.u13761 (nat_lit 30328272) (nat_lit 3718232426) (nat_lit 0) D2M8K2.u13762 from rfl, totK_node, atot13761, atot13762]
  decide +kernel

theorem arows13766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13766 = true := by
  rw [show D2M8K2.u13766 = KTree.node D2M8K2.u13764 (nat_lit 30335174) (nat_lit 3405455167) (nat_lit 0) D2M8K2.u13765 from rfl, allE_node, arows13764, irow13766, arows13765]
  all_goals rfl

theorem atot13766 : totK PD2M8K2 D2M8K2.u13766 = [49567372496, 338282009044, 1245070064800, 1532790463048, 434706034421, 21897291087, 0, 0] := by
  rw [show D2M8K2.u13766 = KTree.node D2M8K2.u13764 (nat_lit 30335174) (nat_lit 3405455167) (nat_lit 0) D2M8K2.u13765 from rfl, totK_node, atot13764, atot13765]
  decide +kernel

theorem arows13771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13771 = true := by
  rw [show D2M8K2.u13771 = KTree.node D2M8K2.u13769 (nat_lit 30403944) (nat_lit 3218281652) (nat_lit 0) D2M8K2.u13770 from rfl, allE_node, arows13769, irow13771, arows13770]
  all_goals rfl

theorem atot13771 : totK PD2M8K2 D2M8K2.u13771 = [396143491144, 1417450944678, 1400377572643, 433794750308, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u13771 = KTree.node D2M8K2.u13769 (nat_lit 30403944) (nat_lit 3218281652) (nat_lit 0) D2M8K2.u13770 from rfl, totK_node, atot13769, atot13770]
  decide +kernel

theorem arows13774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13774 = true := by
  rw [show D2M8K2.u13774 = KTree.node D2M8K2.u13772 (nat_lit 30406665) (nat_lit 1757933004) (nat_lit 0) D2M8K2.u13773 from rfl, allE_node, arows13772, irow13774, arows13773]
  all_goals rfl

theorem atot13774 : totK PD2M8K2 D2M8K2.u13774 = [420106413946, 1440088433597, 1408447375341, 345683309230, 10502159150, 0, 0, 0] := by
  rw [show D2M8K2.u13774 = KTree.node D2M8K2.u13772 (nat_lit 30406665) (nat_lit 1757933004) (nat_lit 0) D2M8K2.u13773 from rfl, totK_node, atot13772, atot13773]
  decide +kernel

theorem arows13778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13778 = true := by
  rw [show D2M8K2.u13778 = KTree.node D2M8K2.u13776 (nat_lit 30410335) (nat_lit 2367312987) (nat_lit 0) D2M8K2.u13777 from rfl, allE_node, arows13776, irow13778, arows13777]
  all_goals rfl

theorem atot13778 : totK PD2M8K2 D2M8K2.u13778 = [420335746920, 1464801343335, 1394828063716, 309505226483, 11799187958, 0, 0, 0] := by
  rw [show D2M8K2.u13778 = KTree.node D2M8K2.u13776 (nat_lit 30410335) (nat_lit 2367312987) (nat_lit 0) D2M8K2.u13777 from rfl, totK_node, atot13776, atot13777]
  decide +kernel

theorem arows13781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13781 = true := by
  rw [show D2M8K2.u13781 = KTree.node D2M8K2.u13779 (nat_lit 30413473) (nat_lit 1442886075) (nat_lit 0) D2M8K2.u13780 from rfl, allE_node, arows13779, irow13781, arows13780]
  all_goals rfl

theorem atot13781 : totK PD2M8K2 D2M8K2.u13781 = [401950222738, 1449446147724, 1405785467837, 306915076987, 11884213561, 0, 0, 0] := by
  rw [show D2M8K2.u13781 = KTree.node D2M8K2.u13779 (nat_lit 30413473) (nat_lit 1442886075) (nat_lit 0) D2M8K2.u13780 from rfl, totK_node, atot13779, atot13780]
  decide +kernel

theorem arows13787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13787 = true := by
  rw [show D2M8K2.u13787 = KTree.node D2M8K2.u13785 (nat_lit 30417027) (nat_lit 3053786314) (nat_lit 0) D2M8K2.u13786 from rfl, allE_node, arows13785, irow13787, arows13786]
  all_goals rfl

theorem atot13787 : totK PD2M8K2 D2M8K2.u13787 = [425933657684, 1523256714017, 1429553654532, 266780504994, 5055171047, 0, 0, 0] := by
  rw [show D2M8K2.u13787 = KTree.node D2M8K2.u13785 (nat_lit 30417027) (nat_lit 3053786314) (nat_lit 0) D2M8K2.u13786 from rfl, totK_node, atot13785, atot13786]
  decide +kernel

theorem arows13790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13790 = true := by
  rw [show D2M8K2.u13790 = KTree.node D2M8K2.u13788 (nat_lit 30423888) (nat_lit 2714475972) (nat_lit 0) D2M8K2.u13789 from rfl, allE_node, arows13788, irow13790, arows13789]
  all_goals rfl

theorem atot13790 : totK PD2M8K2 D2M8K2.u13790 = [0, 626699871314, 1777178937587, 1100177366188, 132998970409, 10444649207, 0, 0] := by
  rw [show D2M8K2.u13790 = KTree.node D2M8K2.u13788 (nat_lit 30423888) (nat_lit 2714475972) (nat_lit 0) D2M8K2.u13789 from rfl, totK_node, atot13788, atot13789]
  decide +kernel

theorem arows13794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13794 = true := by
  rw [show D2M8K2.u13794 = KTree.node D2M8K2.u13792 (nat_lit 30426633) (nat_lit 1576427997) (nat_lit 0) D2M8K2.u13793 from rfl, allE_node, arows13792, irow13794, arows13793]
  all_goals rfl

theorem atot13794 : totK PD2M8K2 D2M8K2.u13794 = [0, 390961258195, 1283941894890, 1379983730206, 501275925185, 26477224647, 0, 0] := by
  rw [show D2M8K2.u13794 = KTree.node D2M8K2.u13792 (nat_lit 30426633) (nat_lit 1576427997) (nat_lit 0) D2M8K2.u13793 from rfl, totK_node, atot13792, atot13793]
  decide +kernel

theorem arows13797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13797 = true := by
  rw [show D2M8K2.u13797 = KTree.node D2M8K2.u13795 (nat_lit 30430185) (nat_lit 1884935950) (nat_lit 0) D2M8K2.u13796 from rfl, allE_node, arows13795, irow13797, arows13796]
  all_goals rfl

theorem atot13797 : totK PD2M8K2 D2M8K2.u13797 = [0, 441782284863, 1541117551483, 1366030812453, 244178840465, 5159868635, 0, 0] := by
  rw [show D2M8K2.u13797 = KTree.node D2M8K2.u13795 (nat_lit 30430185) (nat_lit 1884935950) (nat_lit 0) D2M8K2.u13796 from rfl, totK_node, atot13795, atot13796]
  decide +kernel

theorem arows13802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13802 = true := by
  rw [show D2M8K2.u13802 = KTree.node D2M8K2.u13800 (nat_lit 30433780) (nat_lit 3641286270) (nat_lit 0) D2M8K2.u13801 from rfl, allE_node, arows13800, irow13802, arows13801]
  all_goals rfl

theorem atot13802 : totK PD2M8K2 D2M8K2.u13802 = [0, 400050249191, 1509417722196, 1396162168866, 257157506300, 5218872685, 0, 0] := by
  rw [show D2M8K2.u13802 = KTree.node D2M8K2.u13800 (nat_lit 30433780) (nat_lit 3641286270) (nat_lit 0) D2M8K2.u13801 from rfl, totK_node, atot13800, atot13801]
  decide +kernel

theorem arows13805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13805 = true := by
  rw [show D2M8K2.u13805 = KTree.node D2M8K2.u13803 (nat_lit 30437462) (nat_lit 4148742603) (nat_lit 0) D2M8K2.u13804 from rfl, allE_node, arows13803, irow13805, arows13804]
  all_goals rfl

theorem atot13805 : totK PD2M8K2 D2M8K2.u13805 = [0, 423963005749, 1600904421189, 1417105378743, 201013110402, 1415142070, 0, 0] := by
  rw [show D2M8K2.u13805 = KTree.node D2M8K2.u13803 (nat_lit 30437462) (nat_lit 4148742603) (nat_lit 0) D2M8K2.u13804 from rfl, totK_node, atot13803, atot13804]
  decide +kernel

theorem arows13809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13809 = true := by
  rw [show D2M8K2.u13809 = KTree.node D2M8K2.u13807 (nat_lit 30441092) (nat_lit 3353609998) (nat_lit 0) D2M8K2.u13808 from rfl, allE_node, arows13807, irow13809, arows13808]
  all_goals rfl

theorem atot13809 : totK PD2M8K2 D2M8K2.u13809 = [325398345861, 1051258218792, 1113672159801, 819763105681, 256958915966, 9302370699, 0, 0] := by
  rw [show D2M8K2.u13809 = KTree.node D2M8K2.u13807 (nat_lit 30441092) (nat_lit 3353609998) (nat_lit 0) D2M8K2.u13808 from rfl, totK_node, atot13807, atot13808]
  decide +kernel

theorem arows13812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13812 = true := by
  rw [show D2M8K2.u13812 = KTree.node D2M8K2.u13810 (nat_lit 30445156) (nat_lit 3793462340) (nat_lit 0) D2M8K2.u13811 from rfl, allE_node, arows13810, irow13812, arows13811]
  all_goals rfl

theorem atot13812 : totK PD2M8K2 D2M8K2.u13812 = [428948337720, 1461094690579, 1380040720644, 372076345567, 25368447013, 0, 0, 0] := by
  rw [show D2M8K2.u13812 = KTree.node D2M8K2.u13810 (nat_lit 30445156) (nat_lit 3793462340) (nat_lit 0) D2M8K2.u13811 from rfl, totK_node, atot13810, atot13811]
  decide +kernel

theorem arows13822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13822 = true := by
  rw [show D2M8K2.u13822 = KTree.node D2M8K2.u13820 (nat_lit 30447929) (nat_lit 1190163074) (nat_lit 0) D2M8K2.u13821 from rfl, allE_node, arows13820, irow13822, arows13821]
  all_goals rfl

theorem atot13822 : totK PD2M8K2 D2M8K2.u13822 = [438381136503, 1417268769043, 1354612165764, 384139668975, 13392989424, 0, 0, 0] := by
  rw [show D2M8K2.u13822 = KTree.node D2M8K2.u13820 (nat_lit 30447929) (nat_lit 1190163074) (nat_lit 0) D2M8K2.u13821 from rfl, totK_node, atot13820, atot13821]
  decide +kernel

theorem arows13825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13825 = true := by
  rw [show D2M8K2.u13825 = KTree.node D2M8K2.u13823 (nat_lit 30454751) (nat_lit 2016398739) (nat_lit 0) D2M8K2.u13824 from rfl, allE_node, arows13823, irow13825, arows13824]
  all_goals rfl

theorem atot13825 : totK PD2M8K2 D2M8K2.u13825 = [382184329876, 1425719444364, 1446465958480, 324549566696, 12981912718, 0, 0, 0] := by
  rw [show D2M8K2.u13825 = KTree.node D2M8K2.u13823 (nat_lit 30454751) (nat_lit 2016398739) (nat_lit 0) D2M8K2.u13824 from rfl, totK_node, atot13823, atot13824]
  decide +kernel

theorem arows13829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13829 = true := by
  rw [show D2M8K2.u13829 = KTree.node D2M8K2.u13827 (nat_lit 30458361) (nat_lit 1785102710) (nat_lit 0) D2M8K2.u13828 from rfl, allE_node, arows13827, irow13829, arows13828]
  all_goals rfl

theorem atot13829 : totK PD2M8K2 D2M8K2.u13829 = [418584527484, 1518190032207, 1429697828783, 269643586276, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u13829 = KTree.node D2M8K2.u13827 (nat_lit 30458361) (nat_lit 1785102710) (nat_lit 0) D2M8K2.u13828 from rfl, totK_node, atot13827, atot13828]
  decide +kernel

theorem arows13832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13832 = true := by
  rw [show D2M8K2.u13832 = KTree.node D2M8K2.u13830 (nat_lit 30461917) (nat_lit 1152564544) (nat_lit 0) D2M8K2.u13831 from rfl, allE_node, arows13830, irow13832, arows13831]
  all_goals rfl

theorem atot13832 : totK PD2M8K2 D2M8K2.u13832 = [0, 537854544082, 1698203775707, 1166679947755, 131095853479, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13832 = KTree.node D2M8K2.u13830 (nat_lit 30461917) (nat_lit 1152564544) (nat_lit 0) D2M8K2.u13831 from rfl, totK_node, atot13830, atot13831]
  decide +kernel

theorem arows13837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13837 = true := by
  rw [show D2M8K2.u13837 = KTree.node D2M8K2.u13835 (nat_lit 30466112) (nat_lit 3238308586) (nat_lit 0) D2M8K2.u13836 from rfl, allE_node, arows13835, irow13837, arows13836]
  all_goals rfl

theorem atot13837 : totK PD2M8K2 D2M8K2.u13837 = [0, 734079893610, 1859788865148, 982144550046, 77273302693, 0, 0, 0] := by
  rw [show D2M8K2.u13837 = KTree.node D2M8K2.u13835 (nat_lit 30466112) (nat_lit 3238308586) (nat_lit 0) D2M8K2.u13836 from rfl, totK_node, atot13835, atot13836]
  decide +kernel

theorem arows13840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13840 = true := by
  rw [show D2M8K2.u13840 = KTree.node D2M8K2.u13838 (nat_lit 30471005) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u13839 from rfl, allE_node, arows13838, irow13840, arows13839]
  all_goals rfl

theorem atot13840 : totK PD2M8K2 D2M8K2.u13840 = [0, 405887930473, 1460246558552, 1349825574586, 302201133001, 13016197374, 0, 0] := by
  rw [show D2M8K2.u13840 = KTree.node D2M8K2.u13838 (nat_lit 30471005) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u13839 from rfl, totK_node, atot13838, atot13839]
  decide +kernel

theorem arows13844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13844 = true := by
  rw [show D2M8K2.u13844 = KTree.node D2M8K2.u13842 (nat_lit 30478470) (nat_lit 3470944662) (nat_lit 0) D2M8K2.u13843 from rfl, allE_node, arows13842, irow13844, arows13843]
  all_goals rfl

theorem atot13844 : totK PD2M8K2 D2M8K2.u13844 = [0, 515679201945, 1638063339628, 1213294193086, 179988993072, 4574395652, 0, 0] := by
  rw [show D2M8K2.u13844 = KTree.node D2M8K2.u13842 (nat_lit 30478470) (nat_lit 3470944662) (nat_lit 0) D2M8K2.u13843 from rfl, totK_node, atot13842, atot13843]
  decide +kernel

theorem arows13847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13847 = true := by
  rw [show D2M8K2.u13847 = KTree.node D2M8K2.u13845 (nat_lit 30483624) (nat_lit 3445181887) (nat_lit 0) D2M8K2.u13846 from rfl, allE_node, arows13845, irow13847, arows13846]
  all_goals rfl

theorem atot13847 : totK PD2M8K2 D2M8K2.u13847 = [491803923217, 1532992335278, 1316602194143, 291672001843, 14921770147, 0, 0, 0] := by
  rw [show D2M8K2.u13847 = KTree.node D2M8K2.u13845 (nat_lit 30483624) (nat_lit 3445181887) (nat_lit 0) D2M8K2.u13846 from rfl, totK_node, atot13845, atot13846]
  decide +kernel

theorem arows13853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13853 = true := by
  rw [show D2M8K2.u13853 = KTree.node D2M8K2.u13851 (nat_lit 30487606) (nat_lit 3390205630) (nat_lit 0) D2M8K2.u13852 from rfl, allE_node, arows13851, irow13853, arows13852]
  all_goals rfl

theorem atot13853 : totK PD2M8K2 D2M8K2.u13853 = [290839802986, 1198459441462, 1504404061322, 583704866756, 37595089999, 0, 0, 0] := by
  rw [show D2M8K2.u13853 = KTree.node D2M8K2.u13851 (nat_lit 30487606) (nat_lit 3390205630) (nat_lit 0) D2M8K2.u13852 from rfl, totK_node, atot13851, atot13852]
  decide +kernel

theorem arows13856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13856 = true := by
  rw [show D2M8K2.u13856 = KTree.node D2M8K2.u13854 (nat_lit 30493803) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13855 from rfl, allE_node, arows13854, irow13856, arows13855]
  all_goals rfl

theorem atot13856 : totK PD2M8K2 D2M8K2.u13856 = [410466835454, 1452964038695, 1405430942766, 325829485508, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13856 = KTree.node D2M8K2.u13854 (nat_lit 30493803) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13855 from rfl, totK_node, atot13854, atot13855]
  decide +kernel

theorem arows13860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13860 = true := by
  rw [show D2M8K2.u13860 = KTree.node D2M8K2.u13858 (nat_lit 30496948) (nat_lit 3930079892) (nat_lit 0) D2M8K2.u13859 from rfl, allE_node, arows13858, irow13860, arows13859]
  all_goals rfl

theorem atot13860 : totK PD2M8K2 D2M8K2.u13860 = [449430450335, 1519802108645, 1381869310147, 256450217301, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13860 = KTree.node D2M8K2.u13858 (nat_lit 30496948) (nat_lit 3930079892) (nat_lit 0) D2M8K2.u13859 from rfl, totK_node, atot13858, atot13859]
  decide +kernel

theorem arows13863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13863 = true := by
  rw [show D2M8K2.u13863 = KTree.node D2M8K2.u13861 (nat_lit 30500845) (nat_lit 1014122181) (nat_lit 0) D2M8K2.u13862 from rfl, allE_node, arows13861, irow13863, arows13862]
  all_goals rfl

theorem atot13863 : totK PD2M8K2 D2M8K2.u13863 = [351502754951, 1395924038829, 1506909550225, 375738691839, 9912687053, 0, 0, 0] := by
  rw [show D2M8K2.u13863 = KTree.node D2M8K2.u13861 (nat_lit 30500845) (nat_lit 1014122181) (nat_lit 0) D2M8K2.u13862 from rfl, totK_node, atot13861, atot13862]
  decide +kernel

theorem arows13868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13868 = true := by
  rw [show D2M8K2.u13868 = KTree.node D2M8K2.u13866 (nat_lit 30504465) (nat_lit 1805487424) (nat_lit 0) D2M8K2.u13867 from rfl, allE_node, arows13866, irow13868, arows13867]
  all_goals rfl

theorem atot13868 : totK PD2M8K2 D2M8K2.u13868 = [0, 524010276688, 1653671146785, 1253965606002, 155543775098, 1239866073, 0, 0] := by
  rw [show D2M8K2.u13868 = KTree.node D2M8K2.u13866 (nat_lit 30504465) (nat_lit 1805487424) (nat_lit 0) D2M8K2.u13867 from rfl, totK_node, atot13866, atot13867]
  decide +kernel

theorem arows13871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13871 = true := by
  rw [show D2M8K2.u13871 = KTree.node D2M8K2.u13869 (nat_lit 30513445) (nat_lit 1140417154) (nat_lit 0) D2M8K2.u13870 from rfl, allE_node, arows13869, irow13871, arows13870]
  all_goals rfl

theorem atot13871 : totK PD2M8K2 D2M8K2.u13871 = [0, 665141928177, 1818958578954, 1036985481810, 82878239399, 0, 0, 0] := by
  rw [show D2M8K2.u13871 = KTree.node D2M8K2.u13869 (nat_lit 30513445) (nat_lit 1140417154) (nat_lit 0) D2M8K2.u13870 from rfl, totK_node, atot13869, atot13870]
  decide +kernel

theorem arows13875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13875 = true := by
  rw [show D2M8K2.u13875 = KTree.node D2M8K2.u13873 (nat_lit 30516847) (nat_lit 2420155925) (nat_lit 0) D2M8K2.u13874 from rfl, allE_node, arows13873, irow13875, arows13874]
  all_goals rfl

theorem atot13875 : totK PD2M8K2 D2M8K2.u13875 = [0, 381429296974, 1429829123090, 1379798556736, 329730870482, 14158861562, 0, 0] := by
  rw [show D2M8K2.u13875 = KTree.node D2M8K2.u13873 (nat_lit 30516847) (nat_lit 2420155925) (nat_lit 0) D2M8K2.u13874 from rfl, totK_node, atot13873, atot13874]
  decide +kernel

theorem arows13878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13878 = true := by
  rw [show D2M8K2.u13878 = KTree.node D2M8K2.u13876 (nat_lit 30520569) (nat_lit 1532017181) (nat_lit 0) D2M8K2.u13877 from rfl, allE_node, arows13876, irow13878, arows13877]
  all_goals rfl

theorem atot13878 : totK PD2M8K2 D2M8K2.u13878 = [159085141884, 747517678010, 1513432527033, 1047807189783, 147869593782, 3667207281, 0, 0] := by
  rw [show D2M8K2.u13878 = KTree.node D2M8K2.u13876 (nat_lit 30520569) (nat_lit 1532017181) (nat_lit 0) D2M8K2.u13877 from rfl, totK_node, atot13876, atot13877]
  decide +kernel

theorem arows13885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13885 = true := by
  rw [show D2M8K2.u13885 = KTree.node D2M8K2.u13883 (nat_lit 30529051) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u13884 from rfl, allE_node, arows13883, irow13885, arows13884]
  all_goals rfl

theorem atot13885 : totK PD2M8K2 D2M8K2.u13885 = [273799819322, 1200267614437, 1521920751792, 589530078993, 37601708222, 0, 0, 0] := by
  rw [show D2M8K2.u13885 = KTree.node D2M8K2.u13883 (nat_lit 30529051) (nat_lit 1698073983) (nat_lit 0) D2M8K2.u13884 from rfl, totK_node, atot13883, atot13884]
  decide +kernel

theorem arows13888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13888 = true := by
  rw [show D2M8K2.u13888 = KTree.node D2M8K2.u13886 (nat_lit 30531866) (nat_lit 4014928098) (nat_lit 0) D2M8K2.u13887 from rfl, allE_node, arows13886, irow13888, arows13887]
  all_goals rfl

theorem atot13888 : totK PD2M8K2 D2M8K2.u13888 = [408804104127, 1431929586241, 1410026699954, 331269572987, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13888 = KTree.node D2M8K2.u13886 (nat_lit 30531866) (nat_lit 4014928098) (nat_lit 0) D2M8K2.u13887 from rfl, totK_node, atot13886, atot13887]
  decide +kernel

theorem arows13892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13892 = true := by
  rw [show D2M8K2.u13892 = KTree.node D2M8K2.u13890 (nat_lit 30535326) (nat_lit 3937483510) (nat_lit 0) D2M8K2.u13891 from rfl, allE_node, arows13890, irow13892, arows13891]
  all_goals rfl

theorem atot13892 : totK PD2M8K2 D2M8K2.u13892 = [399543574017, 1431020304169, 1416820909196, 341697495317, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13892 = KTree.node D2M8K2.u13890 (nat_lit 30535326) (nat_lit 3937483510) (nat_lit 0) D2M8K2.u13891 from rfl, totK_node, atot13890, atot13891]
  decide +kernel

theorem arows13895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13895 = true := by
  rw [show D2M8K2.u13895 = KTree.node D2M8K2.u13893 (nat_lit 30538432) (nat_lit 3734491491) (nat_lit 0) D2M8K2.u13894 from rfl, allE_node, arows13893, irow13895, arows13894]
  all_goals rfl

theorem atot13895 : totK PD2M8K2 D2M8K2.u13895 = [413278240240, 1541151531119, 1418646561503, 256795087695, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13895 = KTree.node D2M8K2.u13893 (nat_lit 30538432) (nat_lit 3734491491) (nat_lit 0) D2M8K2.u13894 from rfl, totK_node, atot13893, atot13894]
  decide +kernel

theorem arows13900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13900 = true := by
  rw [show D2M8K2.u13900 = KTree.node D2M8K2.u13898 (nat_lit 30549114) (nat_lit 3884806920) (nat_lit 0) D2M8K2.u13899 from rfl, allE_node, arows13898, irow13900, arows13899]
  all_goals rfl

theorem atot13900 : totK PD2M8K2 D2M8K2.u13900 = [0, 723010157486, 1884303380886, 948745264358, 66959409757, 0, 0, 0] := by
  rw [show D2M8K2.u13900 = KTree.node D2M8K2.u13898 (nat_lit 30549114) (nat_lit 3884806920) (nat_lit 0) D2M8K2.u13899 from rfl, totK_node, atot13898, atot13899]
  decide +kernel

theorem arows13903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13903 = true := by
  rw [show D2M8K2.u13903 = KTree.node D2M8K2.u13901 (nat_lit 30555753) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u13902 from rfl, allE_node, arows13901, irow13903, arows13902]
  all_goals rfl

theorem atot13903 : totK PD2M8K2 D2M8K2.u13903 = [0, 736470675921, 1876038080370, 931787887789, 57954360165, 0, 0, 0] := by
  rw [show D2M8K2.u13903 = KTree.node D2M8K2.u13901 (nat_lit 30555753) (nat_lit 1918754987) (nat_lit 0) D2M8K2.u13902 from rfl, totK_node, atot13901, atot13902]
  decide +kernel

theorem arows13907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13907 = true := by
  rw [show D2M8K2.u13907 = KTree.node D2M8K2.u13905 (nat_lit 30560850) (nat_lit 3144859954) (nat_lit 0) D2M8K2.u13906 from rfl, allE_node, arows13905, irow13907, arows13906]
  all_goals rfl

theorem atot13907 : totK PD2M8K2 D2M8K2.u13907 = [326941405754, 915547138135, 1165085109923, 944785761945, 197977337840, 4977114383, 0, 0] := by
  rw [show D2M8K2.u13907 = KTree.node D2M8K2.u13905 (nat_lit 30560850) (nat_lit 3144859954) (nat_lit 0) D2M8K2.u13906 from rfl, totK_node, atot13905, atot13906]
  decide +kernel

theorem arows13910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13910 = true := by
  rw [show D2M8K2.u13910 = KTree.node D2M8K2.u13908 (nat_lit 30568879) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u13909 from rfl, allE_node, arows13908, irow13910, arows13909]
  all_goals rfl

theorem atot13910 : totK PD2M8K2 D2M8K2.u13910 = [442843276203, 1605487740500, 1412832792828, 209584815957, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13910 = KTree.node D2M8K2.u13908 (nat_lit 30568879) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u13909 from rfl, totK_node, atot13908, atot13909]
  decide +kernel

theorem arows13916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13916 = true := by
  rw [show D2M8K2.u13916 = KTree.node D2M8K2.u13914 (nat_lit 30571632) (nat_lit 3271751738) (nat_lit 0) D2M8K2.u13915 from rfl, allE_node, arows13914, irow13916, arows13915]
  all_goals rfl

theorem atot13916 : totK PD2M8K2 D2M8K2.u13916 = [325509124295, 1225356553254, 1462204841241, 569502360788, 37589446790, 0, 0, 0] := by
  rw [show D2M8K2.u13916 = KTree.node D2M8K2.u13914 (nat_lit 30571632) (nat_lit 3271751738) (nat_lit 0) D2M8K2.u13915 from rfl, totK_node, atot13914, atot13915]
  decide +kernel

theorem arows13919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13919 = true := by
  rw [show D2M8K2.u13919 = KTree.node D2M8K2.u13917 (nat_lit 30574916) (nat_lit 3303650451) (nat_lit 0) D2M8K2.u13918 from rfl, allE_node, arows13917, irow13919, arows13918]
  all_goals rfl

theorem atot13919 : totK PD2M8K2 D2M8K2.u13919 = [415094949008, 1446353604255, 1420057144101, 326862260234, 12908646270, 0, 0, 0] := by
  rw [show D2M8K2.u13919 = KTree.node D2M8K2.u13917 (nat_lit 30574916) (nat_lit 3303650451) (nat_lit 0) D2M8K2.u13918 from rfl, totK_node, atot13917, atot13918]
  decide +kernel

theorem arows13923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13923 = true := by
  rw [show D2M8K2.u13923 = KTree.node D2M8K2.u13921 (nat_lit 30578289) (nat_lit 1495641409) (nat_lit 0) D2M8K2.u13922 from rfl, allE_node, arows13921, irow13923, arows13922]
  all_goals rfl

theorem atot13923 : totK PD2M8K2 D2M8K2.u13923 = [420039419397, 1448543721281, 1421015331267, 335803681703, 13084597552, 0, 0, 0] := by
  rw [show D2M8K2.u13923 = KTree.node D2M8K2.u13921 (nat_lit 30578289) (nat_lit 1495641409) (nat_lit 0) D2M8K2.u13922 from rfl, totK_node, atot13921, atot13922]
  decide +kernel

theorem arows13926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13926 = true := by
  rw [show D2M8K2.u13926 = KTree.node D2M8K2.u13924 (nat_lit 30584765) (nat_lit 1668102493) (nat_lit 0) D2M8K2.u13925 from rfl, allE_node, arows13924, irow13926, arows13925]
  all_goals rfl

theorem atot13926 : totK PD2M8K2 D2M8K2.u13926 = [112776311510, 1042397481045, 1800129145621, 624524635091, 27384849158, 0, 0, 0] := by
  rw [show D2M8K2.u13926 = KTree.node D2M8K2.u13924 (nat_lit 30584765) (nat_lit 1668102493) (nat_lit 0) D2M8K2.u13925 from rfl, totK_node, atot13924, atot13925]
  decide +kernel

theorem arows13931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13931 = true := by
  rw [show D2M8K2.u13931 = KTree.node D2M8K2.u13929 (nat_lit 30589408) (nat_lit 3751831776) (nat_lit 0) D2M8K2.u13930 from rfl, allE_node, arows13929, irow13931, arows13930]
  all_goals rfl

theorem atot13931 : totK PD2M8K2 D2M8K2.u13931 = [0, 517388909838, 1659547012820, 1305009074913, 157929928871, 1310285577, 0, 0] := by
  rw [show D2M8K2.u13931 = KTree.node D2M8K2.u13929 (nat_lit 30589408) (nat_lit 3751831776) (nat_lit 0) D2M8K2.u13930 from rfl, totK_node, atot13929, atot13930]
  decide +kernel

theorem arows13934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13934 = true := by
  rw [show D2M8K2.u13934 = KTree.node D2M8K2.u13932 (nat_lit 30593859) (nat_lit 2536446441) (nat_lit 0) D2M8K2.u13933 from rfl, allE_node, arows13932, irow13934, arows13933]
  all_goals rfl

theorem atot13934 : totK PD2M8K2 D2M8K2.u13934 = [0, 421635982222, 1563110876295, 1365725488693, 218536760228, 4879840392, 0, 0] := by
  rw [show D2M8K2.u13934 = KTree.node D2M8K2.u13932 (nat_lit 30593859) (nat_lit 2536446441) (nat_lit 0) D2M8K2.u13933 from rfl, totK_node, atot13932, atot13933]
  decide +kernel

theorem arows13938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13938 = true := by
  rw [show D2M8K2.u13938 = KTree.node D2M8K2.u13936 (nat_lit 30597483) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13937 from rfl, allE_node, arows13936, irow13938, arows13937]
  all_goals rfl

theorem atot13938 : totK PD2M8K2 D2M8K2.u13938 = [0, 489158394592, 1570156904115, 1294078869225, 221543842276, 4931404646, 0, 0] := by
  rw [show D2M8K2.u13938 = KTree.node D2M8K2.u13936 (nat_lit 30597483) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u13937 from rfl, totK_node, atot13936, atot13937]
  decide +kernel

theorem arows13941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13941 = true := by
  rw [show D2M8K2.u13941 = KTree.node D2M8K2.u13939 (nat_lit 30604474) (nat_lit 3946002751) (nat_lit 0) D2M8K2.u13940 from rfl, allE_node, arows13939, irow13941, arows13940]
  all_goals rfl

theorem atot13941 : totK PD2M8K2 D2M8K2.u13941 = [0, 362666900683, 1459089257660, 1457346736082, 303450871107, 8424427256, 0, 0] := by
  rw [show D2M8K2.u13941 = KTree.node D2M8K2.u13939 (nat_lit 30604474) (nat_lit 3946002751) (nat_lit 0) D2M8K2.u13940 from rfl, totK_node, atot13939, atot13940]
  decide +kernel

theorem arows13949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13949 = true := by
  rw [show D2M8K2.u13949 = KTree.node D2M8K2.u13947 (nat_lit 30652513) (nat_lit 1389520589) (nat_lit 0) D2M8K2.u13948 from rfl, allE_node, arows13947, irow13949, arows13948]
  all_goals rfl

theorem atot13949 : totK PD2M8K2 D2M8K2.u13949 = [0, 449442817316, 1420641630939, 1318046554306, 445264623986, 38700529177, 0, 0] := by
  rw [show D2M8K2.u13949 = KTree.node D2M8K2.u13947 (nat_lit 30652513) (nat_lit 1389520589) (nat_lit 0) D2M8K2.u13948 from rfl, totK_node, atot13947, atot13948]
  decide +kernel

theorem arows13952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13952 = true := by
  rw [show D2M8K2.u13952 = KTree.node D2M8K2.u13950 (nat_lit 30655297) (nat_lit 1488229367) (nat_lit 0) D2M8K2.u13951 from rfl, allE_node, arows13950, irow13952, arows13951]
  all_goals rfl

theorem atot13952 : totK PD2M8K2 D2M8K2.u13952 = [0, 420106413946, 1401613533123, 1395870135125, 383345249792, 12235609738, 0, 0] := by
  rw [show D2M8K2.u13952 = KTree.node D2M8K2.u13950 (nat_lit 30655297) (nat_lit 1488229367) (nat_lit 0) D2M8K2.u13951 from rfl, totK_node, atot13950, atot13951]
  decide +kernel

theorem arows13956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13956 = true := by
  rw [show D2M8K2.u13956 = KTree.node D2M8K2.u13954 (nat_lit 30658706) (nat_lit 4088199701) (nat_lit 0) D2M8K2.u13955 from rfl, allE_node, arows13954, irow13956, arows13955]
  all_goals rfl

theorem atot13956 : totK PD2M8K2 D2M8K2.u13956 = [0, 420335746920, 1460219725652, 1388248623081, 308564917864, 8706415949, 0, 0] := by
  rw [show D2M8K2.u13956 = KTree.node D2M8K2.u13954 (nat_lit 30658706) (nat_lit 4088199701) (nat_lit 0) D2M8K2.u13955 from rfl, totK_node, atot13954, atot13955]
  decide +kernel

theorem arows13959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13959 = true := by
  rw [show D2M8K2.u13959 = KTree.node D2M8K2.u13957 (nat_lit 30662136) (nat_lit 2625422553) (nat_lit 0) D2M8K2.u13958 from rfl, allE_node, arows13957, irow13959, arows13958]
  all_goals rfl

theorem atot13959 : totK PD2M8K2 D2M8K2.u13959 = [0, 401950222738, 1448231882797, 1400546707408, 312638401479, 8824320960, 0, 0] := by
  rw [show D2M8K2.u13959 = KTree.node D2M8K2.u13957 (nat_lit 30662136) (nat_lit 2625422553) (nat_lit 0) D2M8K2.u13958 from rfl, totK_node, atot13957, atot13958]
  decide +kernel

theorem arows13964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13964 = true := by
  rw [show D2M8K2.u13964 = KTree.node D2M8K2.u13962 (nat_lit 30665693) (nat_lit 2320840716) (nat_lit 0) D2M8K2.u13963 from rfl, allE_node, arows13962, irow13964, arows13963]
  all_goals rfl

theorem atot13964 : totK PD2M8K2 D2M8K2.u13964 = [0, 425933657684, 1541231885671, 1430649979195, 245070036937, 2498823382, 0, 0] := by
  rw [show D2M8K2.u13964 = KTree.node D2M8K2.u13962 (nat_lit 30665693) (nat_lit 2320840716) (nat_lit 0) D2M8K2.u13963 from rfl, totK_node, atot13962, atot13963]
  decide +kernel

theorem arows13967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13967 = true := by
  rw [show D2M8K2.u13967 = KTree.node D2M8K2.u13965 (nat_lit 30672571) (nat_lit 1165473726) (nat_lit 0) D2M8K2.u13966 from rfl, allE_node, arows13965, irow13967, arows13966]
  all_goals rfl

theorem atot13967 : totK PD2M8K2 D2M8K2.u13967 = [0, 0, 711055137719, 1857485613979, 980605932171, 74623789704, 0, 0] := by
  rw [show D2M8K2.u13967 = KTree.node D2M8K2.u13965 (nat_lit 30672571) (nat_lit 1165473726) (nat_lit 0) D2M8K2.u13966 from rfl, totK_node, atot13965, atot13966]
  decide +kernel

theorem arows13971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13971 = true := by
  rw [show D2M8K2.u13971 = KTree.node D2M8K2.u13969 (nat_lit 30675262) (nat_lit 3876981805) (nat_lit 0) D2M8K2.u13970 from rfl, allE_node, arows13969, irow13971, arows13970]
  all_goals rfl

theorem atot13971 : totK PD2M8K2 D2M8K2.u13971 = [0, 0, 329511745295, 1213270044301, 1446312320550, 546679313393, 36921873854, 0] := by
  rw [show D2M8K2.u13971 = KTree.node D2M8K2.u13969 (nat_lit 30675262) (nat_lit 3876981805) (nat_lit 0) D2M8K2.u13970 from rfl, totK_node, atot13969, atot13970]
  decide +kernel

theorem arows13974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13974 = true := by
  rw [show D2M8K2.u13974 = KTree.node D2M8K2.u13972 (nat_lit 30678744) (nat_lit 3173515499) (nat_lit 0) D2M8K2.u13973 from rfl, allE_node, arows13972, irow13974, arows13973]
  all_goals rfl

theorem atot13974 : totK PD2M8K2 D2M8K2.u13974 = [0, 0, 466880627890, 1534776406979, 1333205121852, 221594722775, 5067863418, 0] := by
  rw [show D2M8K2.u13974 = KTree.node D2M8K2.u13972 (nat_lit 30678744) (nat_lit 3173515499) (nat_lit 0) D2M8K2.u13973 from rfl, totK_node, atot13972, atot13973]
  decide +kernel

theorem arows13980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13980 = true := by
  rw [show D2M8K2.u13980 = KTree.node D2M8K2.u13978 (nat_lit 30682480) (nat_lit 3355468190) (nat_lit 0) D2M8K2.u13979 from rfl, allE_node, arows13978, irow13980, arows13979]
  all_goals rfl

theorem atot13980 : totK PD2M8K2 D2M8K2.u13980 = [0, 0, 432314584195, 1530116641926, 1341092728117, 230183599806, 5126512042, 0] := by
  rw [show D2M8K2.u13980 = KTree.node D2M8K2.u13978 (nat_lit 30682480) (nat_lit 3355468190) (nat_lit 0) D2M8K2.u13979 from rfl, totK_node, atot13978, atot13979]
  decide +kernel

theorem arows13983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13983 = true := by
  rw [show D2M8K2.u13983 = KTree.node D2M8K2.u13981 (nat_lit 30686291) (nat_lit 2744439150) (nat_lit 0) D2M8K2.u13982 from rfl, allE_node, arows13981, irow13983, arows13982]
  all_goals rfl

theorem atot13983 : totK PD2M8K2 D2M8K2.u13983 = [0, 0, 420062970017, 1595436838725, 1406906845391, 185003245142, 1392055030, 0] := by
  rw [show D2M8K2.u13983 = KTree.node D2M8K2.u13981 (nat_lit 30686291) (nat_lit 2744439150) (nat_lit 0) D2M8K2.u13982 from rfl, totK_node, atot13981, atot13982]
  decide +kernel

theorem arows13987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13987 = true := by
  rw [show D2M8K2.u13987 = KTree.node D2M8K2.u13985 (nat_lit 30689972) (nat_lit 3651056711) (nat_lit 0) D2M8K2.u13986 from rfl, allE_node, arows13985, irow13987, arows13986]
  all_goals rfl

theorem atot13987 : totK PD2M8K2 D2M8K2.u13987 = [0, 325398345861, 1080424331376, 1107568482248, 773214354747, 233794417657, 9139067247, 0] := by
  rw [show D2M8K2.u13987 = KTree.node D2M8K2.u13985 (nat_lit 30689972) (nat_lit 3651056711) (nat_lit 0) D2M8K2.u13986 from rfl, totK_node, atot13985, atot13986]
  decide +kernel

theorem arows13990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13990 = true := by
  rw [show D2M8K2.u13990 = KTree.node D2M8K2.u13988 (nat_lit 30694064) (nat_lit 3810331381) (nat_lit 0) D2M8K2.u13989 from rfl, allE_node, arows13988, irow13990, arows13989]
  all_goals rfl

theorem atot13990 : totK PD2M8K2 D2M8K2.u13990 = [0, 428948337720, 1428587769956, 1372889011158, 402641340221, 28198438779, 0, 0] := by
  rw [show D2M8K2.u13990 = KTree.node D2M8K2.u13988 (nat_lit 30694064) (nat_lit 3810331381) (nat_lit 0) D2M8K2.u13989 from rfl, totK_node, atot13988, atot13989]
  decide +kernel

theorem arows13995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13995 = true := by
  rw [show D2M8K2.u13995 = KTree.node D2M8K2.u13993 (nat_lit 30696807) (nat_lit 3625303506) (nat_lit 0) D2M8K2.u13994 from rfl, allE_node, arows13993, irow13995, arows13994]
  all_goals rfl

theorem atot13995 : totK PD2M8K2 D2M8K2.u13995 = [0, 438381136503, 1452211526385, 1357783666056, 344423429051, 10453207023, 0, 0] := by
  rw [show D2M8K2.u13995 = KTree.node D2M8K2.u13993 (nat_lit 30696807) (nat_lit 3625303506) (nat_lit 0) D2M8K2.u13994 from rfl, totK_node, atot13993, atot13994]
  decide +kernel

theorem arows13998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13998 = true := by
  rw [show D2M8K2.u13998 = KTree.node D2M8K2.u13996 (nat_lit 30703628) (nat_lit 3232090087) (nat_lit 0) D2M8K2.u13997 from rfl, allE_node, arows13996, irow13998, arows13997]
  all_goals rfl

theorem atot13998 : totK PD2M8K2 D2M8K2.u13998 = [0, 382184329876, 1425229090425, 1437159101948, 324081821757, 12981912718, 0, 0] := by
  rw [show D2M8K2.u13998 = KTree.node D2M8K2.u13996 (nat_lit 30703628) (nat_lit 3232090087) (nat_lit 0) D2M8K2.u13997 from rfl, totK_node, atot13996, atot13997]
  decide +kernel

theorem arows14002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14002 = true := by
  rw [show D2M8K2.u14002 = KTree.node D2M8K2.u14000 (nat_lit 30707263) (nat_lit 1764346693) (nat_lit 0) D2M8K2.u14001 from rfl, allE_node, arows14000, irow14002, arows14001]
  all_goals rfl

theorem atot14002 : totK PD2M8K2 D2M8K2.u14002 = [0, 418584527484, 1510534816484, 1421650536830, 276201544676, 5116408176, 0, 0] := by
  rw [show D2M8K2.u14002 = KTree.node D2M8K2.u14000 (nat_lit 30707263) (nat_lit 1764346693) (nat_lit 0) D2M8K2.u14001 from rfl, totK_node, atot14000, atot14001]
  decide +kernel

theorem arows14005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14005 = true := by
  rw [show D2M8K2.u14005 = KTree.node D2M8K2.u14003 (nat_lit 30711172) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u14004 from rfl, allE_node, arows14003, irow14005, arows14004]
  all_goals rfl

theorem atot14005 : totK PD2M8K2 D2M8K2.u14005 = [0, 0, 770355877832, 1896739478603, 846811861557, 52726152718, 0, 0] := by
  rw [show D2M8K2.u14005 = KTree.node D2M8K2.u14003 (nat_lit 30711172) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u14004 from rfl, totK_node, atot14003, atot14004]
  decide +kernel

theorem arows14012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14012 = true := by
  rw [show D2M8K2.u14012 = KTree.node D2M8K2.u14010 (nat_lit 30717568) (nat_lit 3781001236) (nat_lit 0) D2M8K2.u14011 from rfl, allE_node, arows14010, irow14012, arows14011]
  all_goals rfl

theorem atot14012 : totK PD2M8K2 D2M8K2.u14012 = [0, 0, 598115587017, 1780779130764, 1105079466790, 90093464286, 0, 0] := by
  rw [show D2M8K2.u14012 = KTree.node D2M8K2.u14010 (nat_lit 30717568) (nat_lit 3781001236) (nat_lit 0) D2M8K2.u14011 from rfl, totK_node, atot14010, atot14011]
  decide +kernel

theorem arows14015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14015 = true := by
  rw [show D2M8K2.u14015 = KTree.node D2M8K2.u14013 (nat_lit 30724608) (nat_lit 3395961390) (nat_lit 0) D2M8K2.u14014 from rfl, allE_node, arows14013, irow14015, arows14014]
  all_goals rfl

theorem atot14015 : totK PD2M8K2 D2M8K2.u14015 = [0, 0, 380365974925, 1492203994478, 1385689328507, 243847428768, 5320761635, 0] := by
  rw [show D2M8K2.u14015 = KTree.node D2M8K2.u14013 (nat_lit 30724608) (nat_lit 3395961390) (nat_lit 0) D2M8K2.u14014 from rfl, totK_node, atot14013, atot14014]
  decide +kernel

theorem arows14019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14019 = true := by
  rw [show D2M8K2.u14019 = KTree.node D2M8K2.u14017 (nat_lit 30728879) (nat_lit 2779027026) (nat_lit 0) D2M8K2.u14018 from rfl, allE_node, arows14017, irow14019, arows14018]
  all_goals rfl

theorem atot14019 : totK PD2M8K2 D2M8K2.u14019 = [0, 325540319114, 1249760736187, 1409035063078, 564613446451, 56638210013, 1225787871, 0] := by
  rw [show D2M8K2.u14019 = KTree.node D2M8K2.u14017 (nat_lit 30728879) (nat_lit 2779027026) (nat_lit 0) D2M8K2.u14018 from rfl, totK_node, atot14017, atot14018]
  decide +kernel

theorem arows14022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14022 = true := by
  rw [show D2M8K2.u14022 = KTree.node D2M8K2.u14020 (nat_lit 30735027) (nat_lit 2573122509) (nat_lit 0) D2M8K2.u14021 from rfl, allE_node, arows14020, irow14022, arows14021]
  all_goals rfl

theorem atot14022 : totK PD2M8K2 D2M8K2.u14022 = [0, 428995031423, 1513839266343, 1404321844968, 277748901540, 17170804139, 0, 0] := by
  rw [show D2M8K2.u14022 = KTree.node D2M8K2.u14020 (nat_lit 30735027) (nat_lit 2573122509) (nat_lit 0) D2M8K2.u14021 from rfl, totK_node, atot14020, atot14021]
  decide +kernel

theorem arows14027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14027 = true := by
  rw [show D2M8K2.u14027 = KTree.node D2M8K2.u14025 (nat_lit 30741221) (nat_lit 1377925776) (nat_lit 0) D2M8K2.u14026 from rfl, allE_node, arows14025, irow14027, arows14026]
  all_goals rfl

theorem atot14027 : totK PD2M8K2 D2M8K2.u14027 = [0, 438575211120, 1351685511867, 1347830480164, 462917747957, 21625412572, 0, 0] := by
  rw [show D2M8K2.u14027 = KTree.node D2M8K2.u14025 (nat_lit 30741221) (nat_lit 1377925776) (nat_lit 0) D2M8K2.u14026 from rfl, totK_node, atot14025, atot14026]
  decide +kernel

theorem arows14030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14030 = true := by
  rw [show D2M8K2.u14030 = KTree.node D2M8K2.u14028 (nat_lit 30744347) (nat_lit 2880308392) (nat_lit 0) D2M8K2.u14029 from rfl, allE_node, arows14028, irow14030, arows14029]
  all_goals rfl

theorem atot14030 : totK PD2M8K2 D2M8K2.u14030 = [0, 363107838268, 1386266528677, 1473522523086, 352494776412, 13196099988, 0, 0] := by
  rw [show D2M8K2.u14030 = KTree.node D2M8K2.u14028 (nat_lit 30744347) (nat_lit 2880308392) (nat_lit 0) D2M8K2.u14029 from rfl, totK_node, atot14028, atot14029]
  decide +kernel

theorem arows14034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14034 = true := by
  rw [show D2M8K2.u14034 = KTree.node D2M8K2.u14032 (nat_lit 30748188) (nat_lit 3445884564) (nat_lit 0) D2M8K2.u14033 from rfl, allE_node, arows14032, irow14034, arows14033]
  all_goals rfl

theorem atot14034 : totK PD2M8K2 D2M8K2.u14034 = [0, 437825367018, 1567952179328, 1376123995038, 235664379640, 4980514959, 0, 0] := by
  rw [show D2M8K2.u14034 = KTree.node D2M8K2.u14032 (nat_lit 30748188) (nat_lit 3445884564) (nat_lit 0) D2M8K2.u14033 from rfl, totK_node, atot14032, atot14033]
  decide +kernel

theorem arows14037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14037 = true := by
  rw [show D2M8K2.u14037 = KTree.node D2M8K2.u14035 (nat_lit 30751474) (nat_lit 4171954186) (nat_lit 0) D2M8K2.u14036 from rfl, allE_node, arows14035, irow14037, arows14036]
  all_goals rfl

theorem atot14037 : totK PD2M8K2 D2M8K2.u14037 = [0, 0, 898449014319, 1923627342880, 728502054624, 42216162315, 0, 0] := by
  rw [show D2M8K2.u14037 = KTree.node D2M8K2.u14035 (nat_lit 30751474) (nat_lit 4171954186) (nat_lit 0) D2M8K2.u14036 from rfl, totK_node, atot14035, atot14036]
  decide +kernel

theorem arows14043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14043 = true := by
  rw [show D2M8K2.u14043 = KTree.node D2M8K2.u14041 (nat_lit 30762099) (nat_lit 1259599614) (nat_lit 0) D2M8K2.u14042 from rfl, allE_node, arows14041, irow14043, arows14042]
  all_goals rfl

theorem atot14043 : totK PD2M8K2 D2M8K2.u14043 = [0, 0, 709569724265, 1850678961401, 961444413126, 58691143547, 0, 0] := by
  rw [show D2M8K2.u14043 = KTree.node D2M8K2.u14041 (nat_lit 30762099) (nat_lit 1259599614) (nat_lit 0) D2M8K2.u14042 from rfl, totK_node, atot14041, atot14042]
  decide +kernel

theorem arows14046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14046 = true := by
  rw [show D2M8K2.u14046 = KTree.node D2M8K2.u14044 (nat_lit 30765659) (nat_lit 2131384352) (nat_lit 0) D2M8K2.u14045 from rfl, allE_node, arows14044, irow14046, arows14045]
  all_goals rfl

theorem atot14046 : totK PD2M8K2 D2M8K2.u14046 = [0, 0, 379478203647, 1528604857599, 1398320140445, 235847294662, 5352782441, 0] := by
  rw [show D2M8K2.u14046 = KTree.node D2M8K2.u14044 (nat_lit 30765659) (nat_lit 2131384352) (nat_lit 0) D2M8K2.u14045 from rfl, totK_node, atot14044, atot14045]
  decide +kernel

theorem arows14050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14050 = true := by
  rw [show D2M8K2.u14050 = KTree.node D2M8K2.u14048 (nat_lit 30769615) (nat_lit 1640978934) (nat_lit 0) D2M8K2.u14049 from rfl, allE_node, arows14048, irow14050, arows14049]
  all_goals rfl

theorem atot14050 : totK PD2M8K2 D2M8K2.u14050 = [0, 180280610855, 856416069591, 1485967971005, 960054464941, 116443500635, 1271866555, 0] := by
  rw [show D2M8K2.u14050 = KTree.node D2M8K2.u14048 (nat_lit 30769615) (nat_lit 1640978934) (nat_lit 0) D2M8K2.u14049 from rfl, totK_node, atot14048, atot14049]
  decide +kernel

theorem arows14053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14053 = true := by
  rw [show D2M8K2.u14053 = KTree.node D2M8K2.u14051 (nat_lit 30777993) (nat_lit 1724246189) (nat_lit 0) D2M8K2.u14052 from rfl, allE_node, arows14051, irow14053, arows14052]
  all_goals rfl

theorem atot14053 : totK PD2M8K2 D2M8K2.u14053 = [0, 315951938370, 1204214720603, 1471630032890, 578871901496, 37491288561, 0, 0] := by
  rw [show D2M8K2.u14053 = KTree.node D2M8K2.u14051 (nat_lit 30777993) (nat_lit 1724246189) (nat_lit 0) D2M8K2.u14052 from rfl, totK_node, atot14051, atot14052]
  decide +kernel

theorem arows14058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14058 = true := by
  rw [show D2M8K2.u14058 = KTree.node D2M8K2.u14056 (nat_lit 30780868) (nat_lit 3793800199) (nat_lit 0) D2M8K2.u14057 from rfl, allE_node, arows14056, irow14058, arows14057]
  all_goals rfl

theorem atot14058 : totK PD2M8K2 D2M8K2.u14058 = [0, 402229888703, 1431263789144, 1404876133943, 326105576788, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14058 = KTree.node D2M8K2.u14056 (nat_lit 30780868) (nat_lit 3793800199) (nat_lit 0) D2M8K2.u14057 from rfl, totK_node, atot14056, atot14057]
  decide +kernel

theorem arows14061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14061 = true := by
  rw [show D2M8K2.u14061 = KTree.node D2M8K2.u14059 (nat_lit 30784329) (nat_lit 1809744348) (nat_lit 0) D2M8K2.u14060 from rfl, allE_node, arows14059, irow14061, arows14060]
  all_goals rfl

theorem atot14061 : totK PD2M8K2 D2M8K2.u14061 = [0, 406166122150, 1429302697061, 1401547439367, 336463809302, 13250685261, 0, 0] := by
  rw [show D2M8K2.u14061 = KTree.node D2M8K2.u14059 (nat_lit 30784329) (nat_lit 1809744348) (nat_lit 0) D2M8K2.u14060 from rfl, totK_node, atot14059, atot14060]
  decide +kernel

theorem arows14065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14065 = true := by
  rw [show D2M8K2.u14065 = KTree.node D2M8K2.u14063 (nat_lit 30787422) (nat_lit 3987577423) (nat_lit 0) D2M8K2.u14064 from rfl, allE_node, arows14063, irow14065, arows14064]
  all_goals rfl

theorem atot14065 : totK PD2M8K2 D2M8K2.u14065 = [0, 353655970187, 1473910495632, 1498318257341, 300710107496, 12011707486, 0, 0] := by
  rw [show D2M8K2.u14065 = KTree.node D2M8K2.u14063 (nat_lit 30787422) (nat_lit 3987577423) (nat_lit 0) D2M8K2.u14064 from rfl, totK_node, atot14063, atot14064]
  decide +kernel

theorem arows14068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14068 = true := by
  rw [show D2M8K2.u14068 = KTree.node D2M8K2.u14066 (nat_lit 30798137) (nat_lit 1117660658) (nat_lit 0) D2M8K2.u14067 from rfl, allE_node, arows14066, irow14068, arows14067]
  all_goals rfl

theorem atot14068 : totK PD2M8K2 D2M8K2.u14068 = [0, 0, 736731857298, 1858753914751, 934165970812, 59361175243, 0, 0] := by
  rw [show D2M8K2.u14068 = KTree.node D2M8K2.u14066 (nat_lit 30798137) (nat_lit 1117660658) (nat_lit 0) D2M8K2.u14067 from rfl, totK_node, atot14066, atot14067]
  decide +kernel

theorem arows14077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14077 = true := by
  rw [show D2M8K2.u14077 = KTree.node D2M8K2.u14075 (nat_lit 30804798) (nat_lit 3910760504) (nat_lit 0) D2M8K2.u14076 from rfl, allE_node, arows14075, irow14077, arows14076]
  all_goals rfl

theorem atot14077 : totK PD2M8K2 D2M8K2.u14077 = [0, 0, 733446370860, 1892266840409, 905717763519, 51351565314, 0, 0] := by
  rw [show D2M8K2.u14077 = KTree.node D2M8K2.u14075 (nat_lit 30804798) (nat_lit 3910760504) (nat_lit 0) D2M8K2.u14076 from rfl, totK_node, atot14075, atot14076]
  decide +kernel

theorem arows14080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14080 = true := by
  rw [show D2M8K2.u14080 = KTree.node D2M8K2.u14078 (nat_lit 30813707) (nat_lit 2925092234) (nat_lit 0) D2M8K2.u14079 from rfl, allE_node, arows14078, irow14080, arows14079]
  all_goals rfl

theorem atot14080 : totK PD2M8K2 D2M8K2.u14080 = [0, 342835346343, 1038515150032, 1211603750038, 837330557223, 143148215989, 1429815836, 0] := by
  rw [show D2M8K2.u14080 = KTree.node D2M8K2.u14078 (nat_lit 30813707) (nat_lit 2925092234) (nat_lit 0) D2M8K2.u14079 from rfl, totK_node, atot14078, atot14079]
  decide +kernel

theorem arows14084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14084 = true := by
  rw [show D2M8K2.u14084 = KTree.node D2M8K2.u14082 (nat_lit 30817997) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u14083 from rfl, allE_node, arows14082, irow14084, arows14083]
  all_goals rfl

theorem atot14084 : totK PD2M8K2 D2M8K2.u14084 = [0, 430864336105, 1493523297264, 1384043702114, 326331904723, 22761014182, 0, 0] := by
  rw [show D2M8K2.u14084 = KTree.node D2M8K2.u14082 (nat_lit 30817997) (nat_lit 1998270282) (nat_lit 0) D2M8K2.u14083 from rfl, totK_node, atot14082, atot14083]
  decide +kernel

theorem arows14087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14087 = true := by
  rw [show D2M8K2.u14087 = KTree.node D2M8K2.u14085 (nat_lit 30820802) (nat_lit 3353708193) (nat_lit 0) D2M8K2.u14086 from rfl, allE_node, arows14085, irow14087, arows14086]
  all_goals rfl

theorem atot14087 : totK PD2M8K2 D2M8K2.u14087 = [0, 414868691538, 1373785750556, 1390345869139, 429223218867, 16088841882, 0, 0] := by
  rw [show D2M8K2.u14087 = KTree.node D2M8K2.u14085 (nat_lit 30820802) (nat_lit 3353708193) (nat_lit 0) D2M8K2.u14086 from rfl, totK_node, atot14085, atot14086]
  decide +kernel

theorem arows14092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14092 = true := by
  rw [show D2M8K2.u14092 = KTree.node D2M8K2.u14090 (nat_lit 30824217) (nat_lit 1636836609) (nat_lit 0) D2M8K2.u14091 from rfl, allE_node, arows14090, irow14092, arows14091]
  all_goals rfl

theorem atot14092 : totK PD2M8K2 D2M8K2.u14092 = [0, 415117285625, 1468203928358, 1413228465777, 307508710873, 9068544132, 0, 0] := by
  rw [show D2M8K2.u14092 = KTree.node D2M8K2.u14090 (nat_lit 30824217) (nat_lit 1636836609) (nat_lit 0) D2M8K2.u14091 from rfl, totK_node, atot14090, atot14091]
  decide +kernel

theorem arows14095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14095 = true := by
  rw [show D2M8K2.u14095 = KTree.node D2M8K2.u14093 (nat_lit 30831103) (nat_lit 2324300023) (nat_lit 0) D2M8K2.u14094 from rfl, allE_node, arows14093, irow14095, arows14094]
  all_goals rfl

theorem atot14095 : totK PD2M8K2 D2M8K2.u14095 = [0, 443433827047, 1464822662280, 1392038443072, 322234039495, 9179787334, 0, 0] := by
  rw [show D2M8K2.u14095 = KTree.node D2M8K2.u14093 (nat_lit 30831103) (nat_lit 2324300023) (nat_lit 0) D2M8K2.u14094 from rfl, totK_node, atot14093, atot14094]
  decide +kernel

theorem arows14099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14099 = true := by
  rw [show D2M8K2.u14099 = KTree.node D2M8K2.u14097 (nat_lit 30834224) (nat_lit 2891916324) (nat_lit 0) D2M8K2.u14098 from rfl, allE_node, arows14097, irow14099, arows14098]
  all_goals rfl

theorem atot14099 : totK PD2M8K2 D2M8K2.u14099 = [0, 0, 951477441387, 1930378190505, 684918185118, 40775288762, 0, 0] := by
  rw [show D2M8K2.u14099 = KTree.node D2M8K2.u14097 (nat_lit 30834224) (nat_lit 2891916324) (nat_lit 0) D2M8K2.u14098 from rfl, totK_node, atot14097, atot14098]
  decide +kernel

theorem arows14102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14102 = true := by
  rw [show D2M8K2.u14102 = KTree.node D2M8K2.u14100 (nat_lit 30841465) (nat_lit 1519018273) (nat_lit 0) D2M8K2.u14101 from rfl, allE_node, arows14100, irow14102, arows14101]
  all_goals rfl

theorem atot14102 : totK PD2M8K2 D2M8K2.u14102 = [0, 0, 740228678743, 1839650776402, 965910828432, 60975939203, 0, 0] := by
  rw [show D2M8K2.u14102 = KTree.node D2M8K2.u14100 (nat_lit 30841465) (nat_lit 1519018273) (nat_lit 0) D2M8K2.u14101 from rfl, totK_node, atot14100, atot14101]
  decide +kernel

theorem arows14108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14108 = true := by
  rw [show D2M8K2.u14108 = KTree.node D2M8K2.u14106 (nat_lit 30845312) (nat_lit 3464593350) (nat_lit 0) D2M8K2.u14107 from rfl, allE_node, arows14106, irow14108, arows14107]
  all_goals rfl

theorem atot14108 : totK PD2M8K2 D2M8K2.u14108 = [0, 0, 408889572822, 1610437179737, 1400274860895, 169549723970, 1323630408, 0] := by
  rw [show D2M8K2.u14108 = KTree.node D2M8K2.u14106 (nat_lit 30845312) (nat_lit 3464593350) (nat_lit 0) D2M8K2.u14107 from rfl, totK_node, atot14106, atot14107]
  decide +kernel

theorem arows14111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14111 = true := by
  rw [show D2M8K2.u14111 = KTree.node D2M8K2.u14109 (nat_lit 30852542) (nat_lit 1884109182) (nat_lit 0) D2M8K2.u14110 from rfl, allE_node, arows14109, irow14111, arows14110]
  all_goals rfl

theorem atot14111 : totK PD2M8K2 D2M8K2.u14111 = [0, 0, 433612221016, 1552883813809, 1371051821980, 204896344007, 2562018515, 0] := by
  rw [show D2M8K2.u14111 = KTree.node D2M8K2.u14109 (nat_lit 30852542) (nat_lit 1884109182) (nat_lit 0) D2M8K2.u14110 from rfl, totK_node, atot14109, atot14110]
  decide +kernel

theorem arows14115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14115 = true := by
  rw [show D2M8K2.u14115 = KTree.node D2M8K2.u14113 (nat_lit 30856188) (nat_lit 3181821635) (nat_lit 0) D2M8K2.u14114 from rfl, allE_node, arows14113, irow14115, arows14114]
  all_goals rfl

theorem atot14115 : totK PD2M8K2 D2M8K2.u14115 = [433265610414, 1340202652183, 981625583340, 273456724025, 376655673132, 163540927763, 8304201444, 0] := by
  rw [show D2M8K2.u14115 = KTree.node D2M8K2.u14113 (nat_lit 30856188) (nat_lit 3181821635) (nat_lit 0) D2M8K2.u14114 from rfl, totK_node, atot14113, atot14114]
  decide +kernel

theorem arows14118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14118 = true := by
  rw [show D2M8K2.u14118 = KTree.node D2M8K2.u14116 (nat_lit 30863238) (nat_lit 3391013467) (nat_lit 0) D2M8K2.u14117 from rfl, allE_node, arows14116, irow14118, arows14117]
  all_goals rfl

theorem atot14118 : totK PD2M8K2 D2M8K2.u14118 = [423268943131, 1523450670125, 1406526003336, 249433207949, 7166294683, 0, 0, 0] := by
  rw [show D2M8K2.u14118 = KTree.node D2M8K2.u14116 (nat_lit 30863238) (nat_lit 3391013467) (nat_lit 0) D2M8K2.u14117 from rfl, totK_node, atot14116, atot14117]
  decide +kernel

theorem arows14123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14123 = true := by
  rw [show D2M8K2.u14123 = KTree.node D2M8K2.u14121 (nat_lit 30866914) (nat_lit 3133931486) (nat_lit 0) D2M8K2.u14122 from rfl, allE_node, arows14121, irow14123, arows14122]
  all_goals rfl

theorem atot14123 : totK PD2M8K2 D2M8K2.u14123 = [325217800642, 1301456788111, 1480882369968, 410986971371, 19134117812, 0, 0, 0] := by
  rw [show D2M8K2.u14123 = KTree.node D2M8K2.u14121 (nat_lit 30866914) (nat_lit 3133931486) (nat_lit 0) D2M8K2.u14122 from rfl, totK_node, atot14121, atot14122]
  decide +kernel

theorem arows14126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14126 = true := by
  rw [show D2M8K2.u14126 = KTree.node D2M8K2.u14124 (nat_lit 30870306) (nat_lit 2357662742) (nat_lit 0) D2M8K2.u14125 from rfl, allE_node, arows14124, irow14126, arows14125]
  all_goals rfl

theorem atot14126 : totK PD2M8K2 D2M8K2.u14126 = [465939027220, 1534187356670, 1320277674608, 236181719038, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14126 = KTree.node D2M8K2.u14124 (nat_lit 30870306) (nat_lit 2357662742) (nat_lit 0) D2M8K2.u14125 from rfl, totK_node, atot14124, atot14125]
  decide +kernel

theorem arows14130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14130 = true := by
  rw [show D2M8K2.u14130 = KTree.node D2M8K2.u14128 (nat_lit 30874196) (nat_lit 2993515436) (nat_lit 0) D2M8K2.u14129 from rfl, allE_node, arows14128, irow14130, arows14129]
  all_goals rfl

theorem atot14130 : totK PD2M8K2 D2M8K2.u14130 = [328860779294, 1297415766775, 1501238323497, 452039865085, 22048779143, 0, 0, 0] := by
  rw [show D2M8K2.u14130 = KTree.node D2M8K2.u14128 (nat_lit 30874196) (nat_lit 2993515436) (nat_lit 0) D2M8K2.u14129 from rfl, totK_node, atot14128, atot14129]
  decide +kernel

theorem arows14133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14133 = true := by
  rw [show D2M8K2.u14133 = KTree.node D2M8K2.u14131 (nat_lit 30877414) (nat_lit 3815781934) (nat_lit 0) D2M8K2.u14132 from rfl, allE_node, arows14131, irow14133, arows14132]
  all_goals rfl

theorem atot14133 : totK PD2M8K2 D2M8K2.u14133 = [0, 515223727465, 1637595070916, 1175383965819, 164485533808, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14133 = KTree.node D2M8K2.u14131 (nat_lit 30877414) (nat_lit 3815781934) (nat_lit 0) D2M8K2.u14132 from rfl, totK_node, atot14131, atot14132]
  decide +kernel

theorem arows14140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14140 = true := by
  rw [show D2M8K2.u14140 = KTree.node D2M8K2.u14138 (nat_lit 30884534) (nat_lit 2537300470) (nat_lit 0) D2M8K2.u14139 from rfl, allE_node, arows14138, irow14140, arows14139]
  all_goals rfl

theorem atot14140 : totK PD2M8K2 D2M8K2.u14140 = [0, 741226428993, 1882894615799, 893121932409, 49013558375, 0, 0, 0] := by
  rw [show D2M8K2.u14140 = KTree.node D2M8K2.u14138 (nat_lit 30884534) (nat_lit 2537300470) (nat_lit 0) D2M8K2.u14139 from rfl, totK_node, atot14138, atot14139]
  decide +kernel

theorem arows14143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14143 = true := by
  rw [show D2M8K2.u14143 = KTree.node D2M8K2.u14141 (nat_lit 30893293) (nat_lit 1133093022) (nat_lit 0) D2M8K2.u14142 from rfl, allE_node, arows14141, irow14143, arows14142]
  all_goals rfl

theorem atot14143 : totK PD2M8K2 D2M8K2.u14143 = [0, 707542101794, 1886641128946, 927478815340, 46154265434, 0, 0, 0] := by
  rw [show D2M8K2.u14143 = KTree.node D2M8K2.u14141 (nat_lit 30893293) (nat_lit 1133093022) (nat_lit 0) D2M8K2.u14142 from rfl, totK_node, atot14141, atot14142]
  decide +kernel

theorem arows14147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14147 = true := by
  rw [show D2M8K2.u14147 = KTree.node D2M8K2.u14145 (nat_lit 30901504) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u14146 from rfl, allE_node, arows14145, irow14147, arows14146]
  all_goals rfl

theorem atot14147 : totK PD2M8K2 D2M8K2.u14147 = [442594526442, 1415659554714, 1331898356025, 441084871755, 36487900741, 0, 0, 0] := by
  rw [show D2M8K2.u14147 = KTree.node D2M8K2.u14145 (nat_lit 30901504) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u14146 from rfl, totK_node, atot14145, atot14146]
  decide +kernel

theorem arows14150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14150 = true := by
  rw [show D2M8K2.u14150 = KTree.node D2M8K2.u14148 (nat_lit 30904242) (nat_lit 2631635771) (nat_lit 0) D2M8K2.u14149 from rfl, allE_node, arows14148, irow14150, arows14149]
  all_goals rfl

theorem atot14150 : totK PD2M8K2 D2M8K2.u14150 = [424901975805, 1459406005322, 1402781868306, 337584625758, 9378345584, 0, 0, 0] := by
  rw [show D2M8K2.u14150 = KTree.node D2M8K2.u14148 (nat_lit 30904242) (nat_lit 2631635771) (nat_lit 0) D2M8K2.u14149 from rfl, totK_node, atot14148, atot14149]
  decide +kernel

theorem arows14155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14155 = true := by
  rw [show D2M8K2.u14155 = KTree.node D2M8K2.u14153 (nat_lit 30908110) (nat_lit 3029894573) (nat_lit 0) D2M8K2.u14154 from rfl, allE_node, arows14153, irow14155, arows14154]
  all_goals rfl

theorem atot14155 : totK PD2M8K2 D2M8K2.u14155 = [331817292989, 1317100215328, 1537594962892, 419612763515, 20217845850, 0, 0, 0] := by
  rw [show D2M8K2.u14155 = KTree.node D2M8K2.u14153 (nat_lit 30908110) (nat_lit 3029894573) (nat_lit 0) D2M8K2.u14154 from rfl, totK_node, atot14153, atot14154]
  decide +kernel

theorem arows14158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14158 = true := by
  rw [show D2M8K2.u14158 = KTree.node D2M8K2.u14156 (nat_lit 30911646) (nat_lit 3855791684) (nat_lit 0) D2M8K2.u14157 from rfl, allE_node, arows14156, irow14158, arows14157]
  all_goals rfl

theorem atot14158 : totK PD2M8K2 D2M8K2.u14158 = [432228130150, 1522408935382, 1397771274660, 266647925629, 7475751835, 0, 0, 0] := by
  rw [show D2M8K2.u14158 = KTree.node D2M8K2.u14156 (nat_lit 30911646) (nat_lit 3855791684) (nat_lit 0) D2M8K2.u14157 from rfl, totK_node, atot14156, atot14157]
  decide +kernel

theorem arows14162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14162 = true := by
  rw [show D2M8K2.u14162 = KTree.node D2M8K2.u14160 (nat_lit 30915532) (nat_lit 3825752782) (nat_lit 0) D2M8K2.u14161 from rfl, allE_node, arows14160, irow14162, arows14161]
  all_goals rfl

theorem atot14162 : totK PD2M8K2 D2M8K2.u14162 = [369552348654, 1423551940836, 1489661783913, 356117647183, 9902458238, 0, 0, 0] := by
  rw [show D2M8K2.u14162 = KTree.node D2M8K2.u14160 (nat_lit 30915532) (nat_lit 3825752782) (nat_lit 0) D2M8K2.u14161 from rfl, totK_node, atot14160, atot14161]
  decide +kernel

theorem arows14165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14165 = true := by
  rw [show D2M8K2.u14165 = KTree.node D2M8K2.u14163 (nat_lit 30922157) (nat_lit 2025995828) (nat_lit 0) D2M8K2.u14164 from rfl, allE_node, arows14163, irow14165, arows14164]
  all_goals rfl

theorem atot14165 : totK PD2M8K2 D2M8K2.u14165 = [0, 441511943311, 1467094149908, 1342982606956, 372804921246, 26904681413, 0, 0] := by
  rw [show D2M8K2.u14165 = KTree.node D2M8K2.u14163 (nat_lit 30922157) (nat_lit 2025995828) (nat_lit 0) D2M8K2.u14164 from rfl, totK_node, atot14163, atot14164]
  decide +kernel

theorem arows14171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14171 = true := by
  rw [show D2M8K2.u14171 = KTree.node D2M8K2.u14169 (nat_lit 30924916) (nat_lit 4076853445) (nat_lit 0) D2M8K2.u14170 from rfl, allE_node, arows14169, irow14171, arows14170]
  all_goals rfl

theorem atot14171 : totK PD2M8K2 D2M8K2.u14171 = [0, 423270541845, 1482693159742, 1375422270056, 307727448423, 8969136212, 0, 0] := by
  rw [show D2M8K2.u14171 = KTree.node D2M8K2.u14169 (nat_lit 30924916) (nat_lit 4076853445) (nat_lit 0) D2M8K2.u14170 from rfl, totK_node, atot14169, atot14170]
  decide +kernel

theorem arows14174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14174 = true := by
  rw [show D2M8K2.u14174 = KTree.node D2M8K2.u14172 (nat_lit 30928952) (nat_lit 3779082584) (nat_lit 0) D2M8K2.u14173 from rfl, allE_node, arows14172, irow14174, arows14173]
  all_goals rfl

theorem atot14174 : totK PD2M8K2 D2M8K2.u14174 = [0, 330964272121, 1343068206219, 1557908022991, 383562715585, 10378741320, 0, 0] := by
  rw [show D2M8K2.u14174 = KTree.node D2M8K2.u14172 (nat_lit 30928952) (nat_lit 3779082584) (nat_lit 0) D2M8K2.u14173 from rfl, totK_node, atot14172, atot14173]
  decide +kernel

theorem arows14178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14178 = true := by
  rw [show D2M8K2.u14178 = KTree.node D2M8K2.u14176 (nat_lit 30932496) (nat_lit 3507141481) (nat_lit 0) D2M8K2.u14177 from rfl, allE_node, arows14176, irow14178, arows14177]
  all_goals rfl

theorem atot14178 : totK PD2M8K2 D2M8K2.u14178 = [0, 505829636957, 1626835872726, 1303570818006, 185500227899, 1415142070, 0, 0] := by
  rw [show D2M8K2.u14178 = KTree.node D2M8K2.u14176 (nat_lit 30932496) (nat_lit 3507141481) (nat_lit 0) D2M8K2.u14177 from rfl, totK_node, atot14176, atot14177]
  decide +kernel

theorem arows14181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14181 = true := by
  rw [show D2M8K2.u14181 = KTree.node D2M8K2.u14179 (nat_lit 30936714) (nat_lit 3826453001) (nat_lit 0) D2M8K2.u14180 from rfl, allE_node, arows14179, irow14181, arows14180]
  all_goals rfl

theorem atot14181 : totK PD2M8K2 D2M8K2.u14181 = [108461727635, 537297462970, 1310987628258, 1336926197987, 320210357818, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14181 = KTree.node D2M8K2.u14179 (nat_lit 30936714) (nat_lit 3826453001) (nat_lit 0) D2M8K2.u14180 from rfl, totK_node, atot14179, atot14180]
  decide +kernel

theorem arows14186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14186 = true := by
  rw [show D2M8K2.u14186 = KTree.node D2M8K2.u14184 (nat_lit 30939950) (nat_lit 2398694645) (nat_lit 0) D2M8K2.u14185 from rfl, allE_node, arows14184, irow14186, arows14185]
  all_goals rfl

theorem atot14186 : totK PD2M8K2 D2M8K2.u14186 = [476512913411, 1573240790907, 1347572964879, 195859858562, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14186 = KTree.node D2M8K2.u14184 (nat_lit 30939950) (nat_lit 2398694645) (nat_lit 0) D2M8K2.u14185 from rfl, totK_node, atot14184, atot14185]
  decide +kernel

theorem arows14189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14189 = true := by
  rw [show D2M8K2.u14189 = KTree.node D2M8K2.u14187 (nat_lit 30943798) (nat_lit 3399640141) (nat_lit 0) D2M8K2.u14188 from rfl, allE_node, arows14187, irow14189, arows14188]
  all_goals rfl

theorem atot14189 : totK PD2M8K2 D2M8K2.u14189 = [288922408015, 1204928936502, 1495777884027, 576652559166, 37391844562, 0, 0, 0] := by
  rw [show D2M8K2.u14189 = KTree.node D2M8K2.u14187 (nat_lit 30943798) (nat_lit 3399640141) (nat_lit 0) D2M8K2.u14188 from rfl, totK_node, atot14187, atot14188]
  decide +kernel

theorem arows14193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14193 = true := by
  rw [show D2M8K2.u14193 = KTree.node D2M8K2.u14191 (nat_lit 30946534) (nat_lit 3841895814) (nat_lit 0) D2M8K2.u14192 from rfl, allE_node, arows14191, irow14193, arows14192]
  all_goals rfl

theorem atot14193 : totK PD2M8K2 D2M8K2.u14193 = [408703373446, 1465809054110, 1420993612937, 318993560862, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14193 = KTree.node D2M8K2.u14191 (nat_lit 30946534) (nat_lit 3841895814) (nat_lit 0) D2M8K2.u14192 from rfl, totK_node, atot14191, atot14192]
  decide +kernel

theorem arows14196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14196 = true := by
  rw [show D2M8K2.u14196 = KTree.node D2M8K2.u14194 (nat_lit 30953100) (nat_lit 3559130200) (nat_lit 0) D2M8K2.u14195 from rfl, allE_node, arows14194, irow14196, arows14195]
  all_goals rfl

theorem atot14196 : totK PD2M8K2 D2M8K2.u14196 = [407435581739, 1488606848349, 1414428590192, 257733997374, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14196 = KTree.node D2M8K2.u14194 (nat_lit 30953100) (nat_lit 3559130200) (nat_lit 0) D2M8K2.u14195 from rfl, totK_node, atot14194, atot14195]
  decide +kernel

theorem arows14204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14204 = true := by
  rw [show D2M8K2.u14204 = KTree.node D2M8K2.u14202 (nat_lit 30956913) (nat_lit 918736965) (nat_lit 0) D2M8K2.u14203 from rfl, allE_node, arows14202, irow14204, arows14203]
  all_goals rfl

theorem atot14204 : totK PD2M8K2 D2M8K2.u14204 = [413128340692, 1471931397624, 1414201532261, 322887868193, 8692638541, 0, 0, 0] := by
  rw [show D2M8K2.u14204 = KTree.node D2M8K2.u14202 (nat_lit 30956913) (nat_lit 918736965) (nat_lit 0) D2M8K2.u14203 from rfl, totK_node, atot14202, atot14203]
  decide +kernel

theorem arows14207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14207 = true := by
  rw [show D2M8K2.u14207 = KTree.node D2M8K2.u14205 (nat_lit 30960195) (nat_lit 2389629524) (nat_lit 0) D2M8K2.u14206 from rfl, allE_node, arows14205, irow14207, arows14206]
  all_goals rfl

theorem atot14207 : totK PD2M8K2 D2M8K2.u14207 = [0, 488726962445, 1661891952900, 1209699807325, 133517403609, 1206465782, 0, 0] := by
  rw [show D2M8K2.u14207 = KTree.node D2M8K2.u14205 (nat_lit 30960195) (nat_lit 2389629524) (nat_lit 0) D2M8K2.u14206 from rfl, totK_node, atot14205, atot14206]
  decide +kernel

theorem arows14211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14211 = true := by
  rw [show D2M8K2.u14211 = KTree.node D2M8K2.u14209 (nat_lit 30963895) (nat_lit 1545470888) (nat_lit 0) D2M8K2.u14210 from rfl, allE_node, arows14209, irow14211, arows14210]
  all_goals rfl

theorem atot14211 : totK PD2M8K2 D2M8K2.u14211 = [0, 736364496668, 1871574270007, 958756370818, 73063522304, 0, 0, 0] := by
  rw [show D2M8K2.u14211 = KTree.node D2M8K2.u14209 (nat_lit 30963895) (nat_lit 1545470888) (nat_lit 0) D2M8K2.u14210 from rfl, totK_node, atot14209, atot14210]
  decide +kernel

theorem arows14214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14214 = true := by
  rw [show D2M8K2.u14214 = KTree.node D2M8K2.u14212 (nat_lit 30968785) (nat_lit 1437945999) (nat_lit 0) D2M8K2.u14213 from rfl, allE_node, arows14212, irow14214, arows14213]
  all_goals rfl

theorem atot14214 : totK PD2M8K2 D2M8K2.u14214 = [0, 396411570674, 1462605439898, 1350037295343, 302284220526, 13016197374, 0, 0] := by
  rw [show D2M8K2.u14214 = KTree.node D2M8K2.u14212 (nat_lit 30968785) (nat_lit 1437945999) (nat_lit 0) D2M8K2.u14213 from rfl, totK_node, atot14212, atot14213]
  decide +kernel

theorem arows14219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14219 = true := by
  rw [show D2M8K2.u14219 = KTree.node D2M8K2.u14217 (nat_lit 30975813) (nat_lit 1556026906) (nat_lit 0) D2M8K2.u14218 from rfl, allE_node, arows14217, irow14219, arows14218]
  all_goals rfl

theorem atot14219 : totK PD2M8K2 D2M8K2.u14219 = [0, 492633972742, 1582428137849, 1249986480189, 186855614601, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14219 = KTree.node D2M8K2.u14217 (nat_lit 30975813) (nat_lit 1556026906) (nat_lit 0) D2M8K2.u14218 from rfl, totK_node, atot14217, atot14218]
  decide +kernel

theorem arows14222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14222 = true := by
  rw [show D2M8K2.u14222 = KTree.node D2M8K2.u14220 (nat_lit 31022402) (nat_lit 3685380539) (nat_lit 0) D2M8K2.u14221 from rfl, allE_node, arows14220, irow14222, arows14221]
  all_goals rfl

theorem atot14222 : totK PD2M8K2 D2M8K2.u14222 = [433803088254, 1474113051343, 1346372022092, 297375073351, 14923282974, 0, 0, 0] := by
  rw [show D2M8K2.u14222 = KTree.node D2M8K2.u14220 (nat_lit 31022402) (nat_lit 3685380539) (nat_lit 0) D2M8K2.u14221 from rfl, totK_node, atot14220, atot14221]
  decide +kernel

theorem arows14226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14226 = true := by
  rw [show D2M8K2.u14226 = KTree.node D2M8K2.u14224 (nat_lit 31026126) (nat_lit 3694592462) (nat_lit 0) D2M8K2.u14225 from rfl, allE_node, arows14224, irow14226, arows14225]
  all_goals rfl

theorem atot14226 : totK PD2M8K2 D2M8K2.u14226 = [368589503553, 1327909960804, 1431978282475, 490901075924, 29380165115, 0, 0, 0] := by
  rw [show D2M8K2.u14226 = KTree.node D2M8K2.u14224 (nat_lit 31026126) (nat_lit 3694592462) (nat_lit 0) D2M8K2.u14225 from rfl, totK_node, atot14224, atot14225]
  decide +kernel

theorem arows14229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14229 = true := by
  rw [show D2M8K2.u14229 = KTree.node D2M8K2.u14227 (nat_lit 31029173) (nat_lit 2385402881) (nat_lit 0) D2M8K2.u14228 from rfl, allE_node, arows14227, irow14229, arows14228]
  all_goals rfl

theorem atot14229 : totK PD2M8K2 D2M8K2.u14229 = [424820203696, 1454427281438, 1367345591487, 347763867686, 16366254151, 0, 0, 0] := by
  rw [show D2M8K2.u14229 = KTree.node D2M8K2.u14227 (nat_lit 31029173) (nat_lit 2385402881) (nat_lit 0) D2M8K2.u14228 from rfl, totK_node, atot14227, atot14228]
  decide +kernel

theorem arows14235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14235 = true := by
  rw [show D2M8K2.u14235 = KTree.node D2M8K2.u14233 (nat_lit 31035716) (nat_lit 3280754383) (nat_lit 0) D2M8K2.u14234 from rfl, allE_node, arows14233, irow14235, arows14234]
  all_goals rfl

theorem atot14235 : totK PD2M8K2 D2M8K2.u14235 = [424157580399, 1516569765174, 1409027640397, 248212844761, 4558519234, 0, 0, 0] := by
  rw [show D2M8K2.u14235 = KTree.node D2M8K2.u14233 (nat_lit 31035716) (nat_lit 3280754383) (nat_lit 0) D2M8K2.u14234 from rfl, totK_node, atot14233, atot14234]
  decide +kernel

theorem arows14238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14238 = true := by
  rw [show D2M8K2.u14238 = KTree.node D2M8K2.u14236 (nat_lit 31043022) (nat_lit 3985348335) (nat_lit 0) D2M8K2.u14237 from rfl, allE_node, arows14236, irow14238, arows14237]
  all_goals rfl

theorem atot14238 : totK PD2M8K2 D2M8K2.u14238 = [0, 561857056507, 1717390066930, 1097743540394, 114991860159, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14238 = KTree.node D2M8K2.u14236 (nat_lit 31043022) (nat_lit 3985348335) (nat_lit 0) D2M8K2.u14237 from rfl, totK_node, atot14236, atot14237]
  decide +kernel

theorem arows14242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14242 = true := by
  rw [show D2M8K2.u14242 = KTree.node D2M8K2.u14240 (nat_lit 31046923) (nat_lit 1252676088) (nat_lit 0) D2M8K2.u14241 from rfl, allE_node, arows14240, irow14242, arows14241]
  all_goals rfl

theorem atot14242 : totK PD2M8K2 D2M8K2.u14242 = [0, 714981724649, 1876493268155, 963985176631, 69579611085, 0, 0, 0] := by
  rw [show D2M8K2.u14242 = KTree.node D2M8K2.u14240 (nat_lit 31046923) (nat_lit 1252676088) (nat_lit 0) D2M8K2.u14241 from rfl, totK_node, atot14240, atot14241]
  decide +kernel

theorem arows14245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14245 = true := by
  rw [show D2M8K2.u14245 = KTree.node D2M8K2.u14243 (nat_lit 31056632) (nat_lit 3506633385) (nat_lit 0) D2M8K2.u14244 from rfl, allE_node, arows14243, irow14245, arows14244]
  all_goals rfl

theorem atot14245 : totK PD2M8K2 D2M8K2.u14245 = [0, 469842659131, 1639366874794, 1255111949956, 158187442157, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14245 = KTree.node D2M8K2.u14243 (nat_lit 31056632) (nat_lit 3506633385) (nat_lit 0) D2M8K2.u14244 from rfl, totK_node, atot14243, atot14244]
  decide +kernel

theorem arows14250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14250 = true := by
  rw [show D2M8K2.u14250 = KTree.node D2M8K2.u14248 (nat_lit 31063998) (nat_lit 3636362000) (nat_lit 0) D2M8K2.u14249 from rfl, allE_node, arows14248, irow14250, arows14249]
  all_goals rfl

theorem atot14250 : totK PD2M8K2 D2M8K2.u14250 = [464880696672, 1523165130536, 1254975224728, 265836876923, 71699733546, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14250 = KTree.node D2M8K2.u14248 (nat_lit 31063998) (nat_lit 3636362000) (nat_lit 0) D2M8K2.u14249 from rfl, totK_node, atot14248, atot14249]
  decide +kernel

theorem arows14253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14253 = true := by
  rw [show D2M8K2.u14253 = KTree.node D2M8K2.u14251 (nat_lit 31067595) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u14252 from rfl, allE_node, arows14251, irow14253, arows14252]
  all_goals rfl

theorem atot14253 : totK PD2M8K2 D2M8K2.u14253 = [362948396135, 1346029486523, 1435530110073, 478785720461, 30599093470, 0, 0, 0] := by
  rw [show D2M8K2.u14253 = KTree.node D2M8K2.u14251 (nat_lit 31067595) (nat_lit 3740217982) (nat_lit 0) D2M8K2.u14252 from rfl, totK_node, atot14251, atot14252]
  decide +kernel

theorem arows14257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14257 = true := by
  rw [show D2M8K2.u14257 = KTree.node D2M8K2.u14255 (nat_lit 31070625) (nat_lit 1832606434) (nat_lit 0) D2M8K2.u14256 from rfl, allE_node, arows14255, irow14257, arows14256]
  all_goals rfl

theorem atot14257 : totK PD2M8K2 D2M8K2.u14257 = [426292166354, 1438445936447, 1389551434307, 356718825757, 16388616678, 0, 0, 0] := by
  rw [show D2M8K2.u14257 = KTree.node D2M8K2.u14255 (nat_lit 31070625) (nat_lit 1832606434) (nat_lit 0) D2M8K2.u14256 from rfl, totK_node, atot14255, atot14256]
  decide +kernel

theorem arows14260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14260 = true := by
  rw [show D2M8K2.u14260 = KTree.node D2M8K2.u14258 (nat_lit 31074012) (nat_lit 2738256711) (nat_lit 0) D2M8K2.u14259 from rfl, allE_node, arows14258, irow14260, arows14259]
  all_goals rfl

theorem atot14260 : totK PD2M8K2 D2M8K2.u14260 = [364107090402, 1399249211643, 1510414356849, 358999850783, 13009279077, 0, 0, 0] := by
  rw [show D2M8K2.u14260 = KTree.node D2M8K2.u14258 (nat_lit 31074012) (nat_lit 2738256711) (nat_lit 0) D2M8K2.u14259 from rfl, totK_node, atot14258, atot14259]
  decide +kernel

theorem arows14267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14267 = true := by
  rw [show D2M8K2.u14267 = KTree.node D2M8K2.u14265 (nat_lit 31081300) (nat_lit 4028089053) (nat_lit 0) D2M8K2.u14266 from rfl, allE_node, arows14265, irow14267, arows14266]
  all_goals rfl

theorem atot14267 : totK PD2M8K2 D2M8K2.u14267 = [424455604040, 1480953480459, 1409137555667, 322062867488, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u14267 = KTree.node D2M8K2.u14265 (nat_lit 31081300) (nat_lit 4028089053) (nat_lit 0) D2M8K2.u14266 from rfl, totK_node, atot14265, atot14266]
  decide +kernel

theorem arows14270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14270 = true := by
  rw [show D2M8K2.u14270 = KTree.node D2M8K2.u14268 (nat_lit 31084515) (nat_lit 2207056835) (nat_lit 0) D2M8K2.u14269 from rfl, allE_node, arows14268, irow14270, arows14269]
  all_goals rfl

theorem atot14270 : totK PD2M8K2 D2M8K2.u14270 = [0, 488824546015, 1650744615740, 1264631049646, 138658763560, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14270 = KTree.node D2M8K2.u14268 (nat_lit 31084515) (nat_lit 2207056835) (nat_lit 0) D2M8K2.u14269 from rfl, totK_node, atot14268, atot14269]
  decide +kernel

theorem arows14274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14274 = true := by
  rw [show D2M8K2.u14274 = KTree.node D2M8K2.u14272 (nat_lit 31088219) (nat_lit 2901615284) (nat_lit 0) D2M8K2.u14273 from rfl, allE_node, arows14272, irow14274, arows14273]
  all_goals rfl

theorem atot14274 : totK PD2M8K2 D2M8K2.u14274 = [0, 735917572705, 1844682555571, 997367209059, 86405465866, 0, 0, 0] := by
  rw [show D2M8K2.u14274 = KTree.node D2M8K2.u14272 (nat_lit 31088219) (nat_lit 2901615284) (nat_lit 0) D2M8K2.u14273 from rfl, totK_node, atot14272, atot14273]
  decide +kernel

theorem arows14277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14277 = true := by
  rw [show D2M8K2.u14277 = KTree.node D2M8K2.u14275 (nat_lit 31093360) (nat_lit 3200507106) (nat_lit 0) D2M8K2.u14276 from rfl, allE_node, arows14275, irow14277, arows14276]
  all_goals rfl

theorem atot14277 : totK PD2M8K2 D2M8K2.u14277 = [0, 451223248443, 1575088395207, 1346030187741, 214173412947, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14277 = KTree.node D2M8K2.u14275 (nat_lit 31093360) (nat_lit 3200507106) (nat_lit 0) D2M8K2.u14276 from rfl, totK_node, atot14275, atot14276]
  decide +kernel

theorem arows14282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14282 = true := by
  rw [show D2M8K2.u14282 = KTree.node D2M8K2.u14280 (nat_lit 31100911) (nat_lit 2414209680) (nat_lit 0) D2M8K2.u14281 from rfl, allE_node, arows14280, irow14282, arows14281]
  all_goals rfl

theorem atot14282 : totK PD2M8K2 D2M8K2.u14282 = [0, 441453999509, 1560200571409, 1379112156672, 226795348163, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14282 = KTree.node D2M8K2.u14280 (nat_lit 31100911) (nat_lit 2414209680) (nat_lit 0) D2M8K2.u14281 from rfl, totK_node, atot14280, atot14281]
  decide +kernel

theorem arows14285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14285 = true := by
  rw [show D2M8K2.u14285 = KTree.node D2M8K2.u14283 (nat_lit 31104068) (nat_lit 3308106591) (nat_lit 0) D2M8K2.u14284 from rfl, allE_node, arows14283, irow14285, arows14284]
  all_goals rfl

theorem atot14285 : totK PD2M8K2 D2M8K2.u14285 = [0, 432885870283, 1379238920530, 1315249191445, 386819588307, 21751168066, 0, 0] := by
  rw [show D2M8K2.u14285 = KTree.node D2M8K2.u14283 (nat_lit 31104068) (nat_lit 3308106591) (nat_lit 0) D2M8K2.u14284 from rfl, totK_node, atot14283, atot14284]
  decide +kernel

theorem arows14289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14289 = true := by
  rw [show D2M8K2.u14289 = KTree.node D2M8K2.u14287 (nat_lit 31111065) (nat_lit 1733176255) (nat_lit 0) D2M8K2.u14288 from rfl, allE_node, arows14287, irow14289, arows14288]
  all_goals rfl

theorem atot14289 : totK PD2M8K2 D2M8K2.u14289 = [0, 422291027537, 1595717205561, 1394148068363, 185334918471, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14289 = KTree.node D2M8K2.u14287 (nat_lit 31111065) (nat_lit 1733176255) (nat_lit 0) D2M8K2.u14288 from rfl, totK_node, atot14287, atot14288]
  decide +kernel

theorem arows14292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14292 = true := by
  rw [show D2M8K2.u14292 = KTree.node D2M8K2.u14290 (nat_lit 31114458) (nat_lit 3901361371) (nat_lit 0) D2M8K2.u14291 from rfl, allE_node, arows14290, irow14292, arows14291]
  all_goals rfl

theorem atot14292 : totK PD2M8K2 D2M8K2.u14292 = [0, 324921271312, 1342309118537, 1501491623892, 366249964710, 14247800626, 0, 0] := by
  rw [show D2M8K2.u14292 = KTree.node D2M8K2.u14290 (nat_lit 31114458) (nat_lit 3901361371) (nat_lit 0) D2M8K2.u14291 from rfl, totK_node, atot14290, atot14291]
  decide +kernel

theorem arows14298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14298 = true := by
  rw [show D2M8K2.u14298 = KTree.node D2M8K2.u14296 (nat_lit 31118700) (nat_lit 3550354764) (nat_lit 0) D2M8K2.u14297 from rfl, allE_node, arows14296, irow14298, arows14297]
  all_goals rfl

theorem atot14298 : totK PD2M8K2 D2M8K2.u14298 = [0, 377701375531, 1539182751560, 1454394185216, 189458615805, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14298 = KTree.node D2M8K2.u14296 (nat_lit 31118700) (nat_lit 3550354764) (nat_lit 0) D2M8K2.u14297 from rfl, totK_node, atot14296, atot14297]
  decide +kernel

theorem arows14301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14301 = true := by
  rw [show D2M8K2.u14301 = KTree.node D2M8K2.u14299 (nat_lit 31122390) (nat_lit 3695365109) (nat_lit 0) D2M8K2.u14300 from rfl, allE_node, arows14299, irow14301, arows14300]
  all_goals rfl

theorem atot14301 : totK PD2M8K2 D2M8K2.u14301 = [0, 415783439461, 1448280311931, 1418243748274, 312038008893, 8788760260, 0, 0] := by
  rw [show D2M8K2.u14301 = KTree.node D2M8K2.u14299 (nat_lit 31122390) (nat_lit 3695365109) (nat_lit 0) D2M8K2.u14300 from rfl, totK_node, atot14299, atot14300]
  decide +kernel

theorem arows14305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14305 = true := by
  rw [show D2M8K2.u14305 = KTree.node D2M8K2.u14303 (nat_lit 31126044) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u14304 from rfl, allE_node, arows14303, irow14305, arows14304]
  all_goals rfl

theorem atot14305 : totK PD2M8K2 D2M8K2.u14305 = [0, 0, 522835711926, 1703093094887, 1098216694355, 124924896289, 1275377855, 0] := by
  rw [show D2M8K2.u14305 = KTree.node D2M8K2.u14303 (nat_lit 31126044) (nat_lit 3082743799) (nat_lit 0) D2M8K2.u14304 from rfl, totK_node, atot14303, atot14304]
  decide +kernel

theorem arows14308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14308 = true := by
  rw [show D2M8K2.u14308 = KTree.node D2M8K2.u14306 (nat_lit 31133267) (nat_lit 2162158991) (nat_lit 0) D2M8K2.u14307 from rfl, allE_node, arows14306, irow14308, arows14307]
  all_goals rfl

theorem atot14308 : totK PD2M8K2 D2M8K2.u14308 = [0, 0, 838860713113, 1924869208229, 722310031834, 30175000210, 0, 0] := by
  rw [show D2M8K2.u14308 = KTree.node D2M8K2.u14306 (nat_lit 31133267) (nat_lit 2162158991) (nat_lit 0) D2M8K2.u14307 from rfl, totK_node, atot14306, atot14307]
  decide +kernel

theorem arows14313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14313 = true := by
  rw [show D2M8K2.u14313 = KTree.node D2M8K2.u14311 (nat_lit 31142446) (nat_lit 4034701571) (nat_lit 0) D2M8K2.u14312 from rfl, allE_node, arows14311, irow14313, arows14312]
  all_goals rfl

theorem atot14313 : totK PD2M8K2 D2M8K2.u14313 = [0, 183175457280, 1022572664711, 1723069600218, 628355196558, 28715729375, 0, 0] := by
  rw [show D2M8K2.u14313 = KTree.node D2M8K2.u14311 (nat_lit 31142446) (nat_lit 4034701571) (nat_lit 0) D2M8K2.u14312 from rfl, totK_node, atot14311, atot14312]
  decide +kernel

theorem arows14316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14316 = true := by
  rw [show D2M8K2.u14316 = KTree.node D2M8K2.u14314 (nat_lit 31151138) (nat_lit 4100234929) (nat_lit 0) D2M8K2.u14315 from rfl, allE_node, arows14314, irow14316, arows14315]
  all_goals rfl

theorem atot14316 : totK PD2M8K2 D2M8K2.u14316 = [0, 259144647737, 1199711784502, 1551830339382, 574811347749, 35325005162, 0, 0] := by
  rw [show D2M8K2.u14316 = KTree.node D2M8K2.u14314 (nat_lit 31151138) (nat_lit 4100234929) (nat_lit 0) D2M8K2.u14315 from rfl, totK_node, atot14314, atot14315]
  decide +kernel

theorem arows14320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14320 = true := by
  rw [show D2M8K2.u14320 = KTree.node D2M8K2.u14318 (nat_lit 31153883) (nat_lit 2906256691) (nat_lit 0) D2M8K2.u14319 from rfl, allE_node, arows14318, irow14320, arows14319]
  all_goals rfl

theorem atot14320 : totK PD2M8K2 D2M8K2.u14320 = [0, 424298996391, 1508427122096, 1386973422640, 280520639380, 14047627982, 0, 0] := by
  rw [show D2M8K2.u14320 = KTree.node D2M8K2.u14318 (nat_lit 31153883) (nat_lit 2906256691) (nat_lit 0) D2M8K2.u14319 from rfl, totK_node, atot14318, atot14319]
  decide +kernel

theorem arows14323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14323 = true := by
  rw [show D2M8K2.u14323 = KTree.node D2M8K2.u14321 (nat_lit 31157929) (nat_lit 936045605) (nat_lit 0) D2M8K2.u14322 from rfl, allE_node, arows14321, irow14323, arows14322]
  all_goals rfl

theorem atot14323 : totK PD2M8K2 D2M8K2.u14323 = [0, 472386807201, 1546456505385, 1382154381109, 267444596603, 5439011083, 0, 0] := by
  rw [show D2M8K2.u14323 = KTree.node D2M8K2.u14321 (nat_lit 31157929) (nat_lit 936045605) (nat_lit 0) D2M8K2.u14322 from rfl, totK_node, atot14321, atot14322]
  decide +kernel

theorem arows14335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14335 = true := by
  rw [show D2M8K2.u14335 = KTree.node D2M8K2.u14333 (nat_lit 31161734) (nat_lit 3775584940) (nat_lit 0) D2M8K2.u14334 from rfl, allE_node, arows14333, irow14335, arows14334]
  all_goals rfl

theorem atot14335 : totK PD2M8K2 D2M8K2.u14335 = [0, 487003745737, 1616069768937, 1328776518790, 205422163743, 3880716147, 0, 0] := by
  rw [show D2M8K2.u14335 = KTree.node D2M8K2.u14333 (nat_lit 31161734) (nat_lit 3775584940) (nat_lit 0) D2M8K2.u14334 from rfl, totK_node, atot14333, atot14334]
  decide +kernel

theorem arows14338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14338 = true := by
  rw [show D2M8K2.u14338 = KTree.node D2M8K2.u14336 (nat_lit 31165268) (nat_lit 2047720338) (nat_lit 0) D2M8K2.u14337 from rfl, allE_node, arows14336, irow14338, arows14337]
  all_goals rfl

theorem atot14338 : totK PD2M8K2 D2M8K2.u14338 = [0, 389238692753, 1382028052317, 1423646823437, 399127952439, 17791270226, 0, 0] := by
  rw [show D2M8K2.u14338 = KTree.node D2M8K2.u14336 (nat_lit 31165268) (nat_lit 2047720338) (nat_lit 0) D2M8K2.u14337 from rfl, totK_node, atot14336, atot14337]
  decide +kernel

theorem arows14342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14342 = true := by
  rw [show D2M8K2.u14342 = KTree.node D2M8K2.u14340 (nat_lit 31189633) (nat_lit 1480340801) (nat_lit 0) D2M8K2.u14341 from rfl, allE_node, arows14340, irow14342, arows14341]
  all_goals rfl

theorem atot14342 : totK PD2M8K2 D2M8K2.u14342 = [0, 446443419530, 1580719774942, 1372705541777, 174004204764, 1334361349, 0, 0] := by
  rw [show D2M8K2.u14342 = KTree.node D2M8K2.u14340 (nat_lit 31189633) (nat_lit 1480340801) (nat_lit 0) D2M8K2.u14341 from rfl, totK_node, atot14340, atot14341]
  decide +kernel

theorem arows14345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14345 = true := by
  rw [show D2M8K2.u14345 = KTree.node D2M8K2.u14343 (nat_lit 31193027) (nat_lit 2800952549) (nat_lit 0) D2M8K2.u14344 from rfl, allE_node, arows14343, irow14345, arows14344]
  all_goals rfl

theorem atot14345 : totK PD2M8K2 D2M8K2.u14345 = [0, 348598717717, 1322343732763, 1468200861864, 467292536375, 24088924277, 0, 0] := by
  rw [show D2M8K2.u14345 = KTree.node D2M8K2.u14343 (nat_lit 31193027) (nat_lit 2800952549) (nat_lit 0) D2M8K2.u14344 from rfl, totK_node, atot14343, atot14344]
  decide +kernel

theorem arows14350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14350 = true := by
  rw [show D2M8K2.u14350 = KTree.node D2M8K2.u14348 (nat_lit 31195931) (nat_lit 2820249337) (nat_lit 0) D2M8K2.u14349 from rfl, allE_node, arows14348, irow14350, arows14349]
  all_goals rfl

theorem atot14350 : totK PD2M8K2 D2M8K2.u14350 = [0, 423022570912, 1435644514258, 1401865937741, 320730835933, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14350 = KTree.node D2M8K2.u14348 (nat_lit 31195931) (nat_lit 2820249337) (nat_lit 0) D2M8K2.u14349 from rfl, totK_node, atot14348, atot14349]
  decide +kernel

theorem arows14353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14353 = true := by
  rw [show D2M8K2.u14353 = KTree.node D2M8K2.u14351 (nat_lit 31202817) (nat_lit 1787250882) (nat_lit 0) D2M8K2.u14352 from rfl, allE_node, arows14351, irow14353, arows14352]
  all_goals rfl

theorem atot14353 : totK PD2M8K2 D2M8K2.u14353 = [0, 417855203101, 1528255717991, 1391122496279, 230075022975, 4846308403, 0, 0] := by
  rw [show D2M8K2.u14353 = KTree.node D2M8K2.u14351 (nat_lit 31202817) (nat_lit 1787250882) (nat_lit 0) D2M8K2.u14352 from rfl, totK_node, atot14351, atot14352]
  decide +kernel

theorem arows14357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14357 = true := by
  rw [show D2M8K2.u14357 = KTree.node D2M8K2.u14355 (nat_lit 31206315) (nat_lit 3678804165) (nat_lit 0) D2M8K2.u14356 from rfl, allE_node, arows14355, irow14357, arows14356]
  all_goals rfl

theorem atot14357 : totK PD2M8K2 D2M8K2.u14357 = [0, 250501968678, 1260847251636, 1648447395334, 435370126511, 15099408334, 0, 0] := by
  rw [show D2M8K2.u14357 = KTree.node D2M8K2.u14355 (nat_lit 31206315) (nat_lit 3678804165) (nat_lit 0) D2M8K2.u14356 from rfl, totK_node, atot14355, atot14356]
  decide +kernel

theorem arows14360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14360 = true := by
  rw [show D2M8K2.u14360 = KTree.node D2M8K2.u14358 (nat_lit 31210037) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u14359 from rfl, allE_node, arows14358, irow14360, arows14359]
  all_goals rfl

theorem atot14360 : totK PD2M8K2 D2M8K2.u14360 = [0, 0, 505038558002, 1643660025829, 1167704597762, 138359776491, 1206465782, 0] := by
  rw [show D2M8K2.u14360 = KTree.node D2M8K2.u14358 (nat_lit 31210037) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u14359 from rfl, totK_node, atot14358, atot14359]
  decide +kernel

theorem arows14366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14366 = true := by
  rw [show D2M8K2.u14366 = KTree.node D2M8K2.u14364 (nat_lit 31215302) (nat_lit 3968173516) (nat_lit 0) D2M8K2.u14365 from rfl, allE_node, arows14364, irow14366, arows14365]
  all_goals rfl

theorem atot14366 : totK PD2M8K2 D2M8K2.u14366 = [0, 0, 580250314501, 1740314022987, 1108729400569, 135539151417, 1162935789, 0] := by
  rw [show D2M8K2.u14366 = KTree.node D2M8K2.u14364 (nat_lit 31215302) (nat_lit 3968173516) (nat_lit 0) D2M8K2.u14365 from rfl, totK_node, atot14364, atot14365]
  decide +kernel

theorem arows14369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14369 = true := by
  rw [show D2M8K2.u14369 = KTree.node D2M8K2.u14367 (nat_lit 31222132) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u14368 from rfl, allE_node, arows14367, irow14369, arows14368]
  all_goals rfl

theorem atot14369 : totK PD2M8K2 D2M8K2.u14369 = [0, 0, 392844216459, 1442204012223, 1285940728689, 279763222737, 12874862223, 0] := by
  rw [show D2M8K2.u14369 = KTree.node D2M8K2.u14367 (nat_lit 31222132) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u14368 from rfl, totK_node, atot14367, atot14368]
  decide +kernel

theorem arows14373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14373 = true := by
  rw [show D2M8K2.u14373 = KTree.node D2M8K2.u14371 (nat_lit 31225897) (nat_lit 1412782516) (nat_lit 0) D2M8K2.u14372 from rfl, allE_node, arows14371, irow14373, arows14372]
  all_goals rfl

theorem atot14373 : totK PD2M8K2 D2M8K2.u14373 = [0, 273758852699, 1079620957821, 1389158093429, 667919582637, 100116981626, 3552795014, 0] := by
  rw [show D2M8K2.u14373 = KTree.node D2M8K2.u14371 (nat_lit 31225897) (nat_lit 1412782516) (nat_lit 0) D2M8K2.u14372 from rfl, totK_node, atot14371, atot14372]
  decide +kernel

theorem arows14376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14376 = true := by
  rw [show D2M8K2.u14376 = KTree.node D2M8K2.u14374 (nat_lit 31273138) (nat_lit 3824044510) (nat_lit 0) D2M8K2.u14375 from rfl, allE_node, arows14374, irow14376, arows14375]
  all_goals rfl

theorem atot14376 : totK PD2M8K2 D2M8K2.u14376 = [0, 472644330730, 1612152231856, 1339930907840, 174323669035, 1310166938, 0, 0] := by
  rw [show D2M8K2.u14376 = KTree.node D2M8K2.u14374 (nat_lit 31273138) (nat_lit 3824044510) (nat_lit 0) D2M8K2.u14375 from rfl, totK_node, atot14374, atot14375]
  decide +kernel

theorem arows14381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14381 = true := by
  rw [show D2M8K2.u14381 = KTree.node D2M8K2.u14379 (nat_lit 31276555) (nat_lit 1727830438) (nat_lit 0) D2M8K2.u14380 from rfl, allE_node, arows14379, irow14381, arows14380]
  all_goals rfl

theorem atot14381 : totK PD2M8K2 D2M8K2.u14381 = [0, 402189884389, 1422159321571, 1422696881219, 386116857152, 15013989272, 0, 0] := by
  rw [show D2M8K2.u14381 = KTree.node D2M8K2.u14379 (nat_lit 31276555) (nat_lit 1727830438) (nat_lit 0) D2M8K2.u14380 from rfl, totK_node, atot14379, atot14380]
  decide +kernel

theorem arows14384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14384 = true := by
  rw [show D2M8K2.u14384 = KTree.node D2M8K2.u14382 (nat_lit 31279858) (nat_lit 2627911787) (nat_lit 0) D2M8K2.u14383 from rfl, allE_node, arows14382, irow14384, arows14383]
  all_goals rfl

theorem atot14384 : totK PD2M8K2 D2M8K2.u14384 = [0, 403554790543, 1424243563233, 1418521831779, 325876455179, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14384 = KTree.node D2M8K2.u14382 (nat_lit 31279858) (nat_lit 2627911787) (nat_lit 0) D2M8K2.u14383 from rfl, totK_node, atot14382, atot14383]
  decide +kernel

theorem arows14388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14388 = true := by
  rw [show D2M8K2.u14388 = KTree.node D2M8K2.u14386 (nat_lit 31286682) (nat_lit 3677914707) (nat_lit 0) D2M8K2.u14387 from rfl, allE_node, arows14386, irow14388, arows14387]
  all_goals rfl

theorem atot14388 : totK PD2M8K2 D2M8K2.u14388 = [0, 92237621127, 1061580764809, 1818593353231, 532410598930, 19651928425, 0, 0] := by
  rw [show D2M8K2.u14388 = KTree.node D2M8K2.u14386 (nat_lit 31286682) (nat_lit 3677914707) (nat_lit 0) D2M8K2.u14387 from rfl, totK_node, atot14386, atot14387]
  decide +kernel

theorem arows14391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14391 = true := by
  rw [show D2M8K2.u14391 = KTree.node D2M8K2.u14389 (nat_lit 31294695) (nat_lit 3631119225) (nat_lit 0) D2M8K2.u14390 from rfl, allE_node, arows14389, irow14391, arows14390]
  all_goals rfl

theorem atot14391 : totK PD2M8K2 D2M8K2.u14391 = [0, 0, 620508466451, 1757223212014, 1031385998336, 95809492293, 1103454931, 0] := by
  rw [show D2M8K2.u14391 = KTree.node D2M8K2.u14389 (nat_lit 31294695) (nat_lit 3631119225) (nat_lit 0) D2M8K2.u14390 from rfl, totK_node, atot14389, atot14390]
  decide +kernel

theorem arows14398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14398 = true := by
  rw [show D2M8K2.u14398 = KTree.node D2M8K2.u14396 (nat_lit 31304820) (nat_lit 1981520021) (nat_lit 0) D2M8K2.u14397 from rfl, allE_node, arows14396, irow14398, arows14397]
  all_goals rfl

theorem atot14398 : totK PD2M8K2 D2M8K2.u14398 = [0, 0, 665368000441, 1791097603410, 944423828227, 80529285470, 1061529118, 0] := by
  rw [show D2M8K2.u14398 = KTree.node D2M8K2.u14396 (nat_lit 31304820) (nat_lit 1981520021) (nat_lit 0) D2M8K2.u14397 from rfl, totK_node, atot14396, atot14397]
  decide +kernel

theorem arows14401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14401 = true := by
  rw [show D2M8K2.u14401 = KTree.node D2M8K2.u14399 (nat_lit 31312204) (nat_lit 3902263508) (nat_lit 0) D2M8K2.u14400 from rfl, allE_node, arows14399, irow14401, arows14400]
  all_goals rfl

theorem atot14401 : totK PD2M8K2 D2M8K2.u14401 = [0, 407385632425, 1212418789944, 1176186293039, 605157252419, 110436574361, 3718133097, 0] := by
  rw [show D2M8K2.u14401 = KTree.node D2M8K2.u14399 (nat_lit 31312204) (nat_lit 3902263508) (nat_lit 0) D2M8K2.u14400 from rfl, totK_node, atot14399, atot14400]
  decide +kernel

theorem arows14405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14405 = true := by
  rw [show D2M8K2.u14405 = KTree.node D2M8K2.u14403 (nat_lit 31315837) (nat_lit 1125221625) (nat_lit 0) D2M8K2.u14404 from rfl, allE_node, arows14403, irow14405, arows14404]
  all_goals rfl

theorem atot14405 : totK PD2M8K2 D2M8K2.u14405 = [0, 419151524677, 1485715517475, 1398128413380, 334452539804, 22212564151, 0, 0] := by
  rw [show D2M8K2.u14405 = KTree.node D2M8K2.u14403 (nat_lit 31315837) (nat_lit 1125221625) (nat_lit 0) D2M8K2.u14404 from rfl, totK_node, atot14403, atot14404]
  decide +kernel

theorem arows14408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14408 = true := by
  rw [show D2M8K2.u14408 = KTree.node D2M8K2.u14406 (nat_lit 31318746) (nat_lit 3593812099) (nat_lit 0) D2M8K2.u14407 from rfl, allE_node, arows14406, irow14408, arows14407]
  all_goals rfl

theorem atot14408 : totK PD2M8K2 D2M8K2.u14408 = [0, 425118687194, 1409813689984, 1394593274323, 367452044434, 11714154366, 0, 0] := by
  rw [show D2M8K2.u14408 = KTree.node D2M8K2.u14406 (nat_lit 31318746) (nat_lit 3593812099) (nat_lit 0) D2M8K2.u14407 from rfl, totK_node, atot14406, atot14407]
  decide +kernel

theorem arows14413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14413 = true := by
  rw [show D2M8K2.u14413 = KTree.node D2M8K2.u14411 (nat_lit 31322216) (nat_lit 2687699744) (nat_lit 0) D2M8K2.u14412 from rfl, allE_node, arows14411, irow14413, arows14412]
  all_goals rfl

theorem atot14413 : totK PD2M8K2 D2M8K2.u14413 = [0, 344739196673, 1450301804522, 1537034798747, 311946718535, 9617425803, 0, 0] := by
  rw [show D2M8K2.u14413 = KTree.node D2M8K2.u14411 (nat_lit 31322216) (nat_lit 2687699744) (nat_lit 0) D2M8K2.u14412 from rfl, totK_node, atot14411, atot14412]
  decide +kernel

theorem arows14416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14416 = true := by
  rw [show D2M8K2.u14416 = KTree.node D2M8K2.u14414 (nat_lit 31329510) (nat_lit 3859207955) (nat_lit 0) D2M8K2.u14415 from rfl, allE_node, arows14414, irow14416, arows14415]
  all_goals rfl

theorem atot14416 : totK PD2M8K2 D2M8K2.u14416 = [0, 442492819732, 1512378490504, 1400405674456, 286013551678, 6335033942, 0, 0] := by
  rw [show D2M8K2.u14416 = KTree.node D2M8K2.u14414 (nat_lit 31329510) (nat_lit 3859207955) (nat_lit 0) D2M8K2.u14415 from rfl, totK_node, atot14414, atot14415]
  decide +kernel

theorem arows14420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14420 = true := by
  rw [show D2M8K2.u14420 = KTree.node D2M8K2.u14418 (nat_lit 31353702) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u14419 from rfl, allE_node, arows14418, irow14420, arows14419]
  all_goals rfl

theorem atot14420 : totK PD2M8K2 D2M8K2.u14420 = [433286471789, 1240963189776, 1010627162238, 613076965847, 257233605328, 19678284834, 0, 0] := by
  rw [show D2M8K2.u14420 = KTree.node D2M8K2.u14418 (nat_lit 31353702) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u14419 from rfl, totK_node, atot14418, atot14419]
  decide +kernel

theorem arows14423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14423 = true := by
  rw [show D2M8K2.u14423 = KTree.node D2M8K2.u14421 (nat_lit 31361006) (nat_lit 3140268745) (nat_lit 0) D2M8K2.u14422 from rfl, allE_node, arows14421, irow14423, arows14422]
  all_goals rfl

theorem atot14423 : totK PD2M8K2 D2M8K2.u14423 = [325096442640, 1389229757225, 1508230112783, 326083407732, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14423 = KTree.node D2M8K2.u14421 (nat_lit 31361006) (nat_lit 3140268745) (nat_lit 0) D2M8K2.u14422 from rfl, totK_node, atot14421, atot14422]
  decide +kernel

theorem arows14429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14429 = true := by
  rw [show D2M8K2.u14429 = KTree.node D2M8K2.u14427 (nat_lit 31364613) (nat_lit 1725962492) (nat_lit 0) D2M8K2.u14428 from rfl, allE_node, arows14427, irow14429, arows14428]
  all_goals rfl

theorem atot14429 : totK PD2M8K2 D2M8K2.u14429 = [423460293700, 1468678384752, 1385911010228, 304480446674, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u14429 = KTree.node D2M8K2.u14427 (nat_lit 31364613) (nat_lit 1725962492) (nat_lit 0) D2M8K2.u14428 from rfl, totK_node, atot14427, atot14428]
  decide +kernel

theorem arows14432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14432 = true := by
  rw [show D2M8K2.u14432 = KTree.node D2M8K2.u14430 (nat_lit 31367816) (nat_lit 3713827311) (nat_lit 0) D2M8K2.u14431 from rfl, allE_node, arows14430, irow14432, arows14431]
  all_goals rfl

theorem atot14432 : totK PD2M8K2 D2M8K2.u14432 = [407781028146, 1455941058900, 1403006320590, 285128716638, 7550206458, 0, 0, 0] := by
  rw [show D2M8K2.u14432 = KTree.node D2M8K2.u14430 (nat_lit 31367816) (nat_lit 3713827311) (nat_lit 0) D2M8K2.u14431 from rfl, totK_node, atot14430, atot14431]
  decide +kernel

theorem arows14436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14436 = true := by
  rw [show D2M8K2.u14436 = KTree.node D2M8K2.u14434 (nat_lit 31371691) (nat_lit 1613191705) (nat_lit 0) D2M8K2.u14435 from rfl, allE_node, arows14434, irow14436, arows14435]
  all_goals rfl

theorem atot14436 : totK PD2M8K2 D2M8K2.u14436 = [387121083410, 1432206758619, 1442688431782, 340115757425, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u14436 = KTree.node D2M8K2.u14434 (nat_lit 31371691) (nat_lit 1613191705) (nat_lit 0) D2M8K2.u14435 from rfl, totK_node, atot14434, atot14435]
  decide +kernel

theorem arows14439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14439 = true := by
  rw [show D2M8K2.u14439 = KTree.node D2M8K2.u14437 (nat_lit 31374884) (nat_lit 3092981971) (nat_lit 0) D2M8K2.u14438 from rfl, allE_node, arows14437, irow14439, arows14438]
  all_goals rfl

theorem atot14439 : totK PD2M8K2 D2M8K2.u14439 = [0, 447762443282, 1615962338839, 1248193686585, 170869553202, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14439 = KTree.node D2M8K2.u14437 (nat_lit 31374884) (nat_lit 3092981971) (nat_lit 0) D2M8K2.u14438 from rfl, totK_node, atot14437, atot14438]
  decide +kernel

theorem arows14444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14444 = true := by
  rw [show D2M8K2.u14444 = KTree.node D2M8K2.u14442 (nat_lit 31384057) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u14443 from rfl, allE_node, arows14442, irow14444, arows14443]
  all_goals rfl

theorem atot14444 : totK PD2M8K2 D2M8K2.u14444 = [0, 746724532914, 1888607790088, 889056230091, 49479257802, 0, 0, 0] := by
  rw [show D2M8K2.u14444 = KTree.node D2M8K2.u14442 (nat_lit 31384057) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u14443 from rfl, totK_node, atot14442, atot14443]
  decide +kernel

theorem arows14447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14447 = true := by
  rw [show D2M8K2.u14447 = KTree.node D2M8K2.u14445 (nat_lit 31388738) (nat_lit 3130595635) (nat_lit 0) D2M8K2.u14446 from rfl, allE_node, arows14445, irow14447, arows14446]
  all_goals rfl

theorem atot14447 : totK PD2M8K2 D2M8K2.u14447 = [0, 758872964177, 1889421772861, 878010703883, 44731176856, 0, 0, 0] := by
  rw [show D2M8K2.u14447 = KTree.node D2M8K2.u14445 (nat_lit 31388738) (nat_lit 3130595635) (nat_lit 0) D2M8K2.u14446 from rfl, totK_node, atot14445, atot14446]
  decide +kernel

theorem arows14451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14451 = true := by
  rw [show D2M8K2.u14451 = KTree.node D2M8K2.u14449 (nat_lit 31398976) (nat_lit 3730865734) (nat_lit 0) D2M8K2.u14450 from rfl, allE_node, arows14449, irow14451, arows14450]
  all_goals rfl

theorem atot14451 : totK PD2M8K2 D2M8K2.u14451 = [442620365002, 1412022578654, 1326167526919, 453898426343, 38841936429, 0, 0, 0] := by
  rw [show D2M8K2.u14451 = KTree.node D2M8K2.u14449 (nat_lit 31398976) (nat_lit 3730865734) (nat_lit 0) D2M8K2.u14450 from rfl, totK_node, atot14449, atot14450]
  decide +kernel

theorem arows14454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14454 = true := by
  rw [show D2M8K2.u14454 = KTree.node D2M8K2.u14452 (nat_lit 31401936) (nat_lit 3586323523) (nat_lit 0) D2M8K2.u14453 from rfl, allE_node, arows14452, irow14454, arows14453]
  all_goals rfl

theorem atot14454 : totK PD2M8K2 D2M8K2.u14454 = [331688504469, 1297843606568, 1533487121052, 468412366089, 20534143082, 0, 0, 0] := by
  rw [show D2M8K2.u14454 = KTree.node D2M8K2.u14452 (nat_lit 31401936) (nat_lit 3586323523) (nat_lit 0) D2M8K2.u14453 from rfl, totK_node, atot14452, atot14453]
  decide +kernel

theorem arows14462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14462 = true := by
  rw [show D2M8K2.u14462 = KTree.node D2M8K2.u14460 (nat_lit 31405917) (nat_lit 1569734978) (nat_lit 0) D2M8K2.u14461 from rfl, allE_node, arows14460, irow14462, arows14461]
  all_goals rfl

theorem atot14462 : totK PD2M8K2 D2M8K2.u14462 = [425109459846, 1470998504165, 1397670307903, 316199495661, 12072568435, 0, 0, 0] := by
  rw [show D2M8K2.u14462 = KTree.node D2M8K2.u14460 (nat_lit 31405917) (nat_lit 1569734978) (nat_lit 0) D2M8K2.u14461 from rfl, totK_node, atot14460, atot14461]
  decide +kernel

theorem arows14465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14465 = true := by
  rw [show D2M8K2.u14465 = KTree.node D2M8K2.u14463 (nat_lit 31409123) (nat_lit 2864101918) (nat_lit 0) D2M8K2.u14464 from rfl, allE_node, arows14463, irow14465, arows14464]
  all_goals rfl

theorem atot14465 : totK PD2M8K2 D2M8K2.u14465 = [382612135951, 1488128891254, 1474254569304, 264469785267, 4672061215, 0, 0, 0] := by
  rw [show D2M8K2.u14465 = KTree.node D2M8K2.u14463 (nat_lit 31409123) (nat_lit 2864101918) (nat_lit 0) D2M8K2.u14464 from rfl, totK_node, atot14463, atot14464]
  decide +kernel

theorem arows14469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14469 = true := by
  rw [show D2M8K2.u14469 = KTree.node D2M8K2.u14467 (nat_lit 31413040) (nat_lit 3157933811) (nat_lit 0) D2M8K2.u14468 from rfl, allE_node, arows14467, irow14469, arows14468]
  all_goals rfl

theorem atot14469 : totK PD2M8K2 D2M8K2.u14469 = [419286654820, 1422767519272, 1413798582347, 370264434451, 12557053265, 0, 0, 0] := by
  rw [show D2M8K2.u14469 = KTree.node D2M8K2.u14467 (nat_lit 31413040) (nat_lit 3157933811) (nat_lit 0) D2M8K2.u14468 from rfl, totK_node, atot14467, atot14468]
  decide +kernel

theorem arows14472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14472 = true := by
  rw [show D2M8K2.u14472 = KTree.node D2M8K2.u14470 (nat_lit 31419653) (nat_lit 1731753652) (nat_lit 0) D2M8K2.u14471 from rfl, allE_node, arows14470, irow14472, arows14471]
  all_goals rfl

theorem atot14472 : totK PD2M8K2 D2M8K2.u14472 = [0, 516716619100, 1559361761862, 1233331905418, 315276095886, 25191558099, 0, 0] := by
  rw [show D2M8K2.u14472 = KTree.node D2M8K2.u14470 (nat_lit 31419653) (nat_lit 1731753652) (nat_lit 0) D2M8K2.u14471 from rfl, totK_node, atot14470, atot14471]
  decide +kernel

theorem arows14477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14477 = true := by
  rw [show D2M8K2.u14477 = KTree.node D2M8K2.u14475 (nat_lit 31422631) (nat_lit 1438874120) (nat_lit 0) D2M8K2.u14476 from rfl, allE_node, arows14475, irow14477, arows14476]
  all_goals rfl

theorem atot14477 : totK PD2M8K2 D2M8K2.u14477 = [0, 330829699317, 1309046544425, 1532828837871, 443644053391, 15740225044, 0, 0] := by
  rw [show D2M8K2.u14477 = KTree.node D2M8K2.u14475 (nat_lit 31422631) (nat_lit 1438874120) (nat_lit 0) D2M8K2.u14476 from rfl, totK_node, atot14475, atot14476]
  decide +kernel

theorem arows14480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14480 = true := by
  rw [show D2M8K2.u14480 = KTree.node D2M8K2.u14478 (nat_lit 31426638) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u14479 from rfl, allE_node, arows14478, irow14480, arows14479]
  all_goals rfl

theorem atot14480 : totK PD2M8K2 D2M8K2.u14480 = [0, 423480840933, 1513589014841, 1404144608013, 257359533252, 5181891108, 0, 0] := by
  rw [show D2M8K2.u14480 = KTree.node D2M8K2.u14478 (nat_lit 31426638) (nat_lit 4023064257) (nat_lit 0) D2M8K2.u14479 from rfl, totK_node, atot14478, atot14479]
  decide +kernel

theorem arows14484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14484 = true := by
  rw [show D2M8K2.u14484 = KTree.node D2M8K2.u14482 (nat_lit 31430003) (nat_lit 2782493915) (nat_lit 0) D2M8K2.u14483 from rfl, allE_node, arows14482, irow14484, arows14483]
  all_goals rfl

theorem atot14484 : totK PD2M8K2 D2M8K2.u14484 = [0, 449860434562, 1557356075342, 1375686293600, 231009064921, 2602082993, 0, 0] := by
  rw [show D2M8K2.u14484 = KTree.node D2M8K2.u14482 (nat_lit 31430003) (nat_lit 2782493915) (nat_lit 0) D2M8K2.u14483 from rfl, totK_node, atot14482, atot14483]
  decide +kernel

theorem arows14487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14487 = true := by
  rw [show D2M8K2.u14487 = KTree.node D2M8K2.u14485 (nat_lit 31433979) (nat_lit 3482876502) (nat_lit 0) D2M8K2.u14486 from rfl, allE_node, arows14485, irow14487, arows14486]
  all_goals rfl

theorem atot14487 : totK PD2M8K2 D2M8K2.u14487 = [71933061318, 449594834475, 1378212852454, 1395182018739, 321483960908, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14487 = KTree.node D2M8K2.u14485 (nat_lit 31433979) (nat_lit 3482876502) (nat_lit 0) D2M8K2.u14486 from rfl, totK_node, atot14485, atot14486]
  decide +kernel

theorem arows14493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14493 = true := by
  rw [show D2M8K2.u14493 = KTree.node D2M8K2.u14491 (nat_lit 31478916) (nat_lit 2899345851) (nat_lit 0) D2M8K2.u14492 from rfl, allE_node, arows14491, irow14493, arows14492]
  all_goals rfl

theorem atot14493 : totK PD2M8K2 D2M8K2.u14493 = [434616664587, 1583157205196, 1374702440560, 191357469223, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14493 = KTree.node D2M8K2.u14491 (nat_lit 31478916) (nat_lit 2899345851) (nat_lit 0) D2M8K2.u14492 from rfl, totK_node, atot14491, atot14492]
  decide +kernel

theorem arows14496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14496 = true := by
  rw [show D2M8K2.u14496 = KTree.node D2M8K2.u14494 (nat_lit 31482792) (nat_lit 2762650902) (nat_lit 0) D2M8K2.u14495 from rfl, allE_node, arows14494, irow14496, arows14495]
  all_goals rfl

theorem atot14496 : totK PD2M8K2 D2M8K2.u14496 = [330324744147, 1290706376696, 1476060791669, 494468504895, 30613093193, 0, 0, 0] := by
  rw [show D2M8K2.u14496 = KTree.node D2M8K2.u14494 (nat_lit 31482792) (nat_lit 2762650902) (nat_lit 0) D2M8K2.u14495 from rfl, totK_node, atot14494, atot14495]
  decide +kernel

theorem arows14500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14500 = true := by
  rw [show D2M8K2.u14500 = KTree.node D2M8K2.u14498 (nat_lit 31488947) (nat_lit 1985317167) (nat_lit 0) D2M8K2.u14499 from rfl, allE_node, arows14498, irow14500, arows14499]
  all_goals rfl

theorem atot14500 : totK PD2M8K2 D2M8K2.u14500 = [446011093392, 1477554401950, 1360902116621, 344399212100, 16444495623, 0, 0, 0] := by
  rw [show D2M8K2.u14500 = KTree.node D2M8K2.u14498 (nat_lit 31488947) (nat_lit 1985317167) (nat_lit 0) D2M8K2.u14499 from rfl, totK_node, atot14498, atot14499]
  decide +kernel

theorem arows14503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14503 = true := by
  rw [show D2M8K2.u14503 = KTree.node D2M8K2.u14501 (nat_lit 31492056) (nat_lit 3420842040) (nat_lit 0) D2M8K2.u14502 from rfl, allE_node, arows14501, irow14503, arows14502]
  all_goals rfl

theorem atot14503 : totK PD2M8K2 D2M8K2.u14503 = [399996709829, 1500713938694, 1422681070466, 247300714928, 4678454933, 0, 0, 0] := by
  rw [show D2M8K2.u14503 = KTree.node D2M8K2.u14501 (nat_lit 31492056) (nat_lit 3420842040) (nat_lit 0) D2M8K2.u14502 from rfl, totK_node, atot14501, atot14502]
  decide +kernel

theorem arows14508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14508 = true := by
  rw [show D2M8K2.u14508 = KTree.node D2M8K2.u14506 (nat_lit 31495619) (nat_lit 2696209974) (nat_lit 0) D2M8K2.u14507 from rfl, allE_node, arows14506, irow14508, arows14507]
  all_goals rfl

theorem atot14508 : totK PD2M8K2 D2M8K2.u14508 = [424393285092, 1446961113025, 1410002812103, 334297852480, 8833232361, 0, 0, 0] := by
  rw [show D2M8K2.u14508 = KTree.node D2M8K2.u14506 (nat_lit 31495619) (nat_lit 2696209974) (nat_lit 0) D2M8K2.u14507 from rfl, totK_node, atot14506, atot14507]
  decide +kernel

theorem arows14511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14511 = true := by
  rw [show D2M8K2.u14511 = KTree.node D2M8K2.u14509 (nat_lit 31499165) (nat_lit 1221863170) (nat_lit 0) D2M8K2.u14510 from rfl, allE_node, arows14509, irow14511, arows14510]
  all_goals rfl

theorem atot14511 : totK PD2M8K2 D2M8K2.u14511 = [0, 503385052365, 1669679721127, 1188118361614, 130066320831, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14511 = KTree.node D2M8K2.u14509 (nat_lit 31499165) (nat_lit 1221863170) (nat_lit 0) D2M8K2.u14510 from rfl, totK_node, atot14509, atot14510]
  decide +kernel

theorem arows14515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14515 = true := by
  rw [show D2M8K2.u14515 = KTree.node D2M8K2.u14513 (nat_lit 31502838) (nat_lit 3739328852) (nat_lit 0) D2M8K2.u14514 from rfl, allE_node, arows14513, irow14515, arows14514]
  all_goals rfl

theorem atot14515 : totK PD2M8K2 D2M8K2.u14515 = [0, 691141973487, 1834667974858, 1044723958220, 86493653081, 0, 0, 0] := by
  rw [show D2M8K2.u14515 = KTree.node D2M8K2.u14513 (nat_lit 31502838) (nat_lit 3739328852) (nat_lit 0) D2M8K2.u14514 from rfl, totK_node, atot14513, atot14514]
  decide +kernel

theorem arows14518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14518 = true := by
  rw [show D2M8K2.u14518 = KTree.node D2M8K2.u14516 (nat_lit 31511172) (nat_lit 3046544567) (nat_lit 0) D2M8K2.u14517 from rfl, allE_node, arows14516, irow14518, arows14517]
  all_goals rfl

theorem atot14518 : totK PD2M8K2 D2M8K2.u14518 = [0, 400559531884, 1445896317432, 1350248156841, 303345979633, 13105450397, 0, 0] := by
  rw [show D2M8K2.u14518 = KTree.node D2M8K2.u14516 (nat_lit 31511172) (nat_lit 3046544567) (nat_lit 0) D2M8K2.u14517 from rfl, totK_node, atot14516, atot14517]
  decide +kernel

theorem arows14525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14525 = true := by
  rw [show D2M8K2.u14525 = KTree.node D2M8K2.u14523 (nat_lit 31514721) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u14524 from rfl, allE_node, arows14523, irow14525, arows14524]
  all_goals rfl

theorem atot14525 : totK PD2M8K2 D2M8K2.u14525 = [0, 498775040038, 1601326875660, 1242975056331, 190368670729, 4720618446, 0, 0] := by
  rw [show D2M8K2.u14525 = KTree.node D2M8K2.u14523 (nat_lit 31514721) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u14524 from rfl, totK_node, atot14523, atot14524]
  decide +kernel

theorem arows14528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14528 = true := by
  rw [show D2M8K2.u14528 = KTree.node D2M8K2.u14526 (nat_lit 31519838) (nat_lit 2467698034) (nat_lit 0) D2M8K2.u14527 from rfl, allE_node, arows14526, irow14528, arows14527]
  all_goals rfl

theorem atot14528 : totK PD2M8K2 D2M8K2.u14528 = [395397800573, 1403544525267, 1363857880993, 380501533194, 23449123827, 0, 0, 0] := by
  rw [show D2M8K2.u14528 = KTree.node D2M8K2.u14526 (nat_lit 31519838) (nat_lit 2467698034) (nat_lit 0) D2M8K2.u14527 from rfl, totK_node, atot14526, atot14527]
  decide +kernel

theorem arows14532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14532 = true := by
  rw [show D2M8K2.u14532 = KTree.node D2M8K2.u14530 (nat_lit 31523485) (nat_lit 1074024239) (nat_lit 0) D2M8K2.u14531 from rfl, allE_node, arows14530, irow14532, arows14531]
  all_goals rfl

theorem atot14532 : totK PD2M8K2 D2M8K2.u14532 = [407088331048, 1402912644543, 1392798150671, 426857247507, 29380002449, 0, 0, 0] := by
  rw [show D2M8K2.u14532 = KTree.node D2M8K2.u14530 (nat_lit 31523485) (nat_lit 1074024239) (nat_lit 0) D2M8K2.u14531 from rfl, totK_node, atot14530, atot14531]
  decide +kernel

theorem arows14535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14535 = true := by
  rw [show D2M8K2.u14535 = KTree.node D2M8K2.u14533 (nat_lit 31530078) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u14534 from rfl, allE_node, arows14533, irow14535, arows14534]
  all_goals rfl

theorem atot14535 : totK PD2M8K2 D2M8K2.u14535 = [424986254693, 1457945563989, 1391294841976, 341635498931, 9385673438, 0, 0, 0] := by
  rw [show D2M8K2.u14535 = KTree.node D2M8K2.u14533 (nat_lit 31530078) (nat_lit 3970774059) (nat_lit 0) D2M8K2.u14534 from rfl, totK_node, atot14533, atot14534]
  decide +kernel

theorem arows14540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14540 = true := by
  rw [show D2M8K2.u14540 = KTree.node D2M8K2.u14538 (nat_lit 31533140) (nat_lit 3232123941) (nat_lit 0) D2M8K2.u14539 from rfl, allE_node, arows14538, irow14540, arows14539]
  all_goals rfl

theorem atot14540 : totK PD2M8K2 D2M8K2.u14540 = [424188206739, 1448383660412, 1379572691729, 320060740068, 13149116973, 0, 0, 0] := by
  rw [show D2M8K2.u14540 = KTree.node D2M8K2.u14538 (nat_lit 31533140) (nat_lit 3232123941) (nat_lit 0) D2M8K2.u14539 from rfl, totK_node, atot14538, atot14539]
  decide +kernel

theorem arows14543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14543 = true := by
  rw [show D2M8K2.u14543 = KTree.node D2M8K2.u14541 (nat_lit 31540452) (nat_lit 3217262408) (nat_lit 0) D2M8K2.u14542 from rfl, allE_node, arows14541, irow14543, arows14542]
  all_goals rfl

theorem atot14543 : totK PD2M8K2 D2M8K2.u14543 = [0, 635771708671, 1748634241770, 1009830914876, 106036581113, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14543 = KTree.node D2M8K2.u14541 (nat_lit 31540452) (nat_lit 3217262408) (nat_lit 0) D2M8K2.u14542 from rfl, totK_node, atot14541, atot14542]
  decide +kernel

theorem arows14547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14547 = true := by
  rw [show D2M8K2.u14547 = KTree.node D2M8K2.u14545 (nat_lit 31544283) (nat_lit 2572135765) (nat_lit 0) D2M8K2.u14546 from rfl, allE_node, arows14545, irow14547, arows14546]
  all_goals rfl

theorem atot14547 : totK PD2M8K2 D2M8K2.u14547 = [0, 705783523743, 1861339152954, 994212836239, 74722967582, 0, 0, 0] := by
  rw [show D2M8K2.u14547 = KTree.node D2M8K2.u14545 (nat_lit 31544283) (nat_lit 2572135765) (nat_lit 0) D2M8K2.u14546 from rfl, totK_node, atot14545, atot14546]
  decide +kernel

theorem arows14550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14550 = true := by
  rw [show D2M8K2.u14550 = KTree.node D2M8K2.u14548 (nat_lit 31554052) (nat_lit 4036229409) (nat_lit 0) D2M8K2.u14549 from rfl, allE_node, arows14548, irow14550, arows14549]
  all_goals rfl

theorem atot14550 : totK PD2M8K2 D2M8K2.u14550 = [0, 546175158356, 1694922986198, 1154483515661, 131684868383, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14550 = KTree.node D2M8K2.u14548 (nat_lit 31554052) (nat_lit 4036229409) (nat_lit 0) D2M8K2.u14549 from rfl, totK_node, atot14548, atot14549]
  decide +kernel

theorem arows14556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14556 = true := by
  rw [show D2M8K2.u14556 = KTree.node D2M8K2.u14554 (nat_lit 31561352) (nat_lit 3657766102) (nat_lit 0) D2M8K2.u14555 from rfl, allE_node, arows14554, irow14556, arows14555]
  all_goals rfl

theorem atot14556 : totK PD2M8K2 D2M8K2.u14556 = [408255430500, 1363068312201, 1240824670962, 443132870615, 100470472470, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14556 = KTree.node D2M8K2.u14554 (nat_lit 31561352) (nat_lit 3657766102) (nat_lit 0) D2M8K2.u14555 from rfl, totK_node, atot14554, atot14555]
  decide +kernel

theorem arows14559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14559 = true := by
  rw [show D2M8K2.u14559 = KTree.node D2M8K2.u14557 (nat_lit 31565002) (nat_lit 3111746170) (nat_lit 0) D2M8K2.u14558 from rfl, allE_node, arows14557, irow14559, arows14558]
  all_goals rfl

theorem atot14559 : totK PD2M8K2 D2M8K2.u14559 = [419662791441, 1424198000133, 1392624700105, 410744775464, 28048680602, 0, 0, 0] := by
  rw [show D2M8K2.u14559 = KTree.node D2M8K2.u14557 (nat_lit 31565002) (nat_lit 3111746170) (nat_lit 0) D2M8K2.u14558 from rfl, totK_node, atot14557, atot14558]
  decide +kernel

theorem arows14563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14563 = true := by
  rw [show D2M8K2.u14563 = KTree.node D2M8K2.u14561 (nat_lit 31567792) (nat_lit 3460882871) (nat_lit 0) D2M8K2.u14562 from rfl, allE_node, arows14561, irow14563, arows14562]
  all_goals rfl

theorem atot14563 : totK PD2M8K2 D2M8K2.u14563 = [345417083561, 1335803975783, 1513085065802, 435567910005, 18824724435, 0, 0, 0] := by
  rw [show D2M8K2.u14563 = KTree.node D2M8K2.u14561 (nat_lit 31567792) (nat_lit 3460882871) (nat_lit 0) D2M8K2.u14562 from rfl, totK_node, atot14561, atot14562]
  decide +kernel

theorem arows14566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14566 = true := by
  rw [show D2M8K2.u14566 = KTree.node D2M8K2.u14564 (nat_lit 31571957) (nat_lit 1293384282) (nat_lit 0) D2M8K2.u14565 from rfl, allE_node, arows14564, irow14566, arows14565]
  all_goals rfl

theorem atot14566 : totK PD2M8K2 D2M8K2.u14566 = [426476962799, 1481736214214, 1399670021980, 304359208828, 10676274061, 0, 0, 0] := by
  rw [show D2M8K2.u14566 = KTree.node D2M8K2.u14564 (nat_lit 31571957) (nat_lit 1293384282) (nat_lit 0) D2M8K2.u14565 from rfl, totK_node, atot14564, atot14565]
  decide +kernel

theorem arows14571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14571 = true := by
  rw [show D2M8K2.u14571 = KTree.node D2M8K2.u14569 (nat_lit 31578450) (nat_lit 3448682590) (nat_lit 0) D2M8K2.u14570 from rfl, allE_node, arows14569, irow14571, arows14570]
  all_goals rfl

theorem atot14571 : totK PD2M8K2 D2M8K2.u14571 = [443036656631, 1509978809270, 1398650383645, 295080413730, 7535506819, 0, 0, 0] := by
  rw [show D2M8K2.u14571 = KTree.node D2M8K2.u14569 (nat_lit 31578450) (nat_lit 3448682590) (nat_lit 0) D2M8K2.u14570 from rfl, totK_node, atot14569, atot14570]
  decide +kernel

theorem arows14574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14574 = true := by
  rw [show D2M8K2.u14574 = KTree.node D2M8K2.u14572 (nat_lit 31581914) (nat_lit 3713958547) (nat_lit 0) D2M8K2.u14573 from rfl, allE_node, arows14572, irow14574, arows14573]
  all_goals rfl

theorem atot14574 : totK PD2M8K2 D2M8K2.u14574 = [0, 563482021674, 1707328991918, 1154079714659, 124281242367, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14574 = KTree.node D2M8K2.u14572 (nat_lit 31581914) (nat_lit 3713958547) (nat_lit 0) D2M8K2.u14573 from rfl, totK_node, atot14572, atot14573]
  decide +kernel

theorem arows14578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14578 = true := by
  rw [show D2M8K2.u14578 = KTree.node D2M8K2.u14576 (nat_lit 31585589) (nat_lit 2324904255) (nat_lit 0) D2M8K2.u14577 from rfl, allE_node, arows14576, irow14578, arows14577]
  all_goals rfl

theorem atot14578 : totK PD2M8K2 D2M8K2.u14578 = [0, 673513636794, 1802538295104, 1091898421908, 93733935075, 0, 0, 0] := by
  rw [show D2M8K2.u14578 = KTree.node D2M8K2.u14576 (nat_lit 31585589) (nat_lit 2324904255) (nat_lit 0) D2M8K2.u14577 from rfl, totK_node, atot14576, atot14577]
  decide +kernel

theorem arows14581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14581 = true := by
  rw [show D2M8K2.u14581 = KTree.node D2M8K2.u14579 (nat_lit 31591301) (nat_lit 2195758453) (nat_lit 0) D2M8K2.u14580 from rfl, allE_node, arows14579, irow14581, arows14580]
  all_goals rfl

theorem atot14581 : totK PD2M8K2 D2M8K2.u14581 = [0, 483113289383, 1579727971058, 1313648983446, 214881108160, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14581 = KTree.node D2M8K2.u14579 (nat_lit 31591301) (nat_lit 2195758453) (nat_lit 0) D2M8K2.u14580 from rfl, totK_node, atot14579, atot14580]
  decide +kernel

theorem arows14590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14590 = true := by
  rw [show D2M8K2.u14590 = KTree.node D2M8K2.u14588 (nat_lit 31598312) (nat_lit 2660396263) (nat_lit 0) D2M8K2.u14589 from rfl, allE_node, arows14588, irow14590, arows14589]
  all_goals rfl

theorem atot14590 : totK PD2M8K2 D2M8K2.u14590 = [0, 472091240440, 1590555118603, 1319191397291, 214479272979, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14590 = KTree.node D2M8K2.u14588 (nat_lit 31598312) (nat_lit 2660396263) (nat_lit 0) D2M8K2.u14589 from rfl, totK_node, atot14588, atot14589]
  decide +kernel

theorem arows14593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14593 = true := by
  rw [show D2M8K2.u14593 = KTree.node D2M8K2.u14591 (nat_lit 31601501) (nat_lit 2264020349) (nat_lit 0) D2M8K2.u14592 from rfl, allE_node, arows14591, irow14593, arows14592]
  all_goals rfl

theorem atot14593 : totK PD2M8K2 D2M8K2.u14593 = [0, 345344010572, 1337868849316, 1426382964730, 401758715719, 21751168066, 0, 0] := by
  rw [show D2M8K2.u14593 = KTree.node D2M8K2.u14591 (nat_lit 31601501) (nat_lit 2264020349) (nat_lit 0) D2M8K2.u14592 from rfl, totK_node, atot14591, atot14592]
  decide +kernel

theorem arows14597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14597 = true := by
  rw [show D2M8K2.u14597 = KTree.node D2M8K2.u14595 (nat_lit 31604911) (nat_lit 2414986276) (nat_lit 0) D2M8K2.u14596 from rfl, allE_node, arows14595, irow14597, arows14596]
  all_goals rfl

theorem atot14597 : totK PD2M8K2 D2M8K2.u14597 = [0, 412688306785, 1598226201709, 1394509852755, 184530168676, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14597 = KTree.node D2M8K2.u14595 (nat_lit 31604911) (nat_lit 2414986276) (nat_lit 0) D2M8K2.u14596 from rfl, totK_node, atot14595, atot14596]
  decide +kernel

theorem arows14600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14600 = true := by
  rw [show D2M8K2.u14600 = KTree.node D2M8K2.u14598 (nat_lit 31612987) (nat_lit 2243241104) (nat_lit 0) D2M8K2.u14599 from rfl, allE_node, arows14598, irow14600, arows14599]
  all_goals rfl

theorem atot14600 : totK PD2M8K2 D2M8K2.u14600 = [0, 422890813044, 1521883055887, 1413377168726, 227526406211, 2362393012, 0, 0] := by
  rw [show D2M8K2.u14600 = KTree.node D2M8K2.u14598 (nat_lit 31612987) (nat_lit 2243241104) (nat_lit 0) D2M8K2.u14599 from rfl, totK_node, atot14598, atot14599]
  decide +kernel

theorem arows14605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14605 = true := by
  rw [show D2M8K2.u14605 = KTree.node D2M8K2.u14603 (nat_lit 31616132) (nat_lit 3378615208) (nat_lit 0) D2M8K2.u14604 from rfl, allE_node, arows14603, irow14605, arows14604]
  all_goals rfl

theorem atot14605 : totK PD2M8K2 D2M8K2.u14605 = [0, 378240016858, 1411923650521, 1414059797934, 316192729910, 13088430220, 0, 0] := by
  rw [show D2M8K2.u14605 = KTree.node D2M8K2.u14603 (nat_lit 31616132) (nat_lit 3378615208) (nat_lit 0) D2M8K2.u14604 from rfl, totK_node, atot14603, atot14604]
  decide +kernel

theorem arows14608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14608 = true := by
  rw [show D2M8K2.u14608 = KTree.node D2M8K2.u14606 (nat_lit 31619815) (nat_lit 2386616747) (nat_lit 0) D2M8K2.u14607 from rfl, allE_node, arows14606, irow14608, arows14607]
  all_goals rfl

theorem atot14608 : totK PD2M8K2 D2M8K2.u14608 = [0, 416264362644, 1506572052167, 1422138587494, 260667451490, 5089919014, 0, 0] := by
  rw [show D2M8K2.u14608 = KTree.node D2M8K2.u14606 (nat_lit 31619815) (nat_lit 2386616747) (nat_lit 0) D2M8K2.u14607 from rfl, totK_node, atot14606, atot14607]
  decide +kernel

theorem arows14612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14612 = true := by
  rw [show D2M8K2.u14612 = KTree.node D2M8K2.u14610 (nat_lit 31623442) (nat_lit 3592588208) (nat_lit 0) D2M8K2.u14611 from rfl, allE_node, arows14610, irow14612, arows14611]
  all_goals rfl

theorem atot14612 : totK PD2M8K2 D2M8K2.u14612 = [0, 0, 559280334239, 1733964449452, 1047366555375, 114266682255, 1310517177, 0] := by
  rw [show D2M8K2.u14612 = KTree.node D2M8K2.u14610 (nat_lit 31623442) (nat_lit 3592588208) (nat_lit 0) D2M8K2.u14611 from rfl, totK_node, atot14610, atot14611]
  decide +kernel

theorem arows14615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14615 = true := by
  rw [show D2M8K2.u14615 = KTree.node D2M8K2.u14613 (nat_lit 31632890) (nat_lit 3105181907) (nat_lit 0) D2M8K2.u14614 from rfl, allE_node, arows14613, irow14615, arows14614]
  all_goals rfl

theorem atot14615 : totK PD2M8K2 D2M8K2.u14615 = [0, 0, 742009259584, 1888275078837, 828551361601, 42759530925, 0, 0] := by
  rw [show D2M8K2.u14615 = KTree.node D2M8K2.u14613 (nat_lit 31632890) (nat_lit 3105181907) (nat_lit 0) D2M8K2.u14614 from rfl, totK_node, atot14613, atot14614]
  decide +kernel

theorem arows14621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14621 = true := by
  rw [show D2M8K2.u14621 = KTree.node D2M8K2.u14619 (nat_lit 31637632) (nat_lit 2358028210) (nat_lit 0) D2M8K2.u14620 from rfl, allE_node, arows14619, irow14621, arows14620]
  all_goals rfl

theorem atot14621 : totK PD2M8K2 D2M8K2.u14621 = [0, 57100535768, 866913396516, 1859858168450, 731964107902, 35139664464, 0, 0] := by
  rw [show D2M8K2.u14621 = KTree.node D2M8K2.u14619 (nat_lit 31637632) (nat_lit 2358028210) (nat_lit 0) D2M8K2.u14620 from rfl, totK_node, atot14619, atot14620]
  decide +kernel

theorem arows14624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14624 = true := by
  rw [show D2M8K2.u14624 = KTree.node D2M8K2.u14622 (nat_lit 31648123) (nat_lit 2220499248) (nat_lit 0) D2M8K2.u14623 from rfl, allE_node, arows14622, irow14624, arows14623]
  all_goals rfl

theorem atot14624 : totK PD2M8K2 D2M8K2.u14624 = [0, 385371427111, 1407845904112, 1404575046755, 427903485537, 29329034908, 0, 0] := by
  rw [show D2M8K2.u14624 = KTree.node D2M8K2.u14622 (nat_lit 31648123) (nat_lit 2220499248) (nat_lit 0) D2M8K2.u14623 from rfl, totK_node, atot14622, atot14623]
  decide +kernel

theorem arows14628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14628 = true := by
  rw [show D2M8K2.u14628 = KTree.node D2M8K2.u14626 (nat_lit 31651447) (nat_lit 2185559569) (nat_lit 0) D2M8K2.u14627 from rfl, allE_node, arows14626, irow14628, arows14627]
  all_goals rfl

theorem atot14628 : totK PD2M8K2 D2M8K2.u14628 = [0, 397578849835, 1356489107497, 1474734990189, 408269821539, 13541384893, 0, 0] := by
  rw [show D2M8K2.u14628 = KTree.node D2M8K2.u14626 (nat_lit 31651447) (nat_lit 2185559569) (nat_lit 0) D2M8K2.u14627 from rfl, totK_node, atot14626, atot14627]
  decide +kernel

theorem arows14631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14631 = true := by
  rw [show D2M8K2.u14631 = KTree.node D2M8K2.u14629 (nat_lit 31655115) (nat_lit 3727089298) (nat_lit 0) D2M8K2.u14630 from rfl, allE_node, arows14629, irow14631, arows14630]
  all_goals rfl

theorem atot14631 : totK PD2M8K2 D2M8K2.u14631 = [0, 358557365833, 1423346540832, 1465875499993, 339280735749, 13183084702, 0, 0] := by
  rw [show D2M8K2.u14631 = KTree.node D2M8K2.u14629 (nat_lit 31655115) (nat_lit 3727089298) (nat_lit 0) D2M8K2.u14630 from rfl, totK_node, atot14629, atot14630]
  decide +kernel

theorem arows14636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14636 = true := by
  rw [show D2M8K2.u14636 = KTree.node D2M8K2.u14634 (nat_lit 31658285) (nat_lit 2023480268) (nat_lit 0) D2M8K2.u14635 from rfl, allE_node, arows14634, irow14636, arows14635]
  all_goals rfl

theorem atot14636 : totK PD2M8K2 D2M8K2.u14636 = [0, 510859459706, 1630642900513, 1293114614050, 200230963965, 3880716147, 0, 0] := by
  rw [show D2M8K2.u14636 = KTree.node D2M8K2.u14634 (nat_lit 31658285) (nat_lit 2023480268) (nat_lit 0) D2M8K2.u14635 from rfl, totK_node, atot14634, atot14635]
  decide +kernel

theorem arows14639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14639 = true := by
  rw [show D2M8K2.u14639 = KTree.node D2M8K2.u14637 (nat_lit 31662282) (nat_lit 3610511611) (nat_lit 0) D2M8K2.u14638 from rfl, allE_node, arows14637, irow14639, arows14638]
  all_goals rfl

theorem atot14639 : totK PD2M8K2 D2M8K2.u14639 = [0, 358516663166, 1336199917672, 1485114908771, 422631970629, 17826494640, 0, 0] := by
  rw [show D2M8K2.u14639 = KTree.node D2M8K2.u14637 (nat_lit 31662282) (nat_lit 3610511611) (nat_lit 0) D2M8K2.u14638 from rfl, totK_node, atot14637, atot14638]
  decide +kernel

theorem arows14643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14643 = true := by
  rw [show D2M8K2.u14643 = KTree.node D2M8K2.u14641 (nat_lit 31727791) (nat_lit 2177577682) (nat_lit 0) D2M8K2.u14642 from rfl, allE_node, arows14641, irow14643, arows14642]
  all_goals rfl

theorem atot14643 : totK PD2M8K2 D2M8K2.u14643 = [0, 437848587025, 1587408622645, 1371055816120, 174036573640, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14643 = KTree.node D2M8K2.u14641 (nat_lit 31727791) (nat_lit 2177577682) (nat_lit 0) D2M8K2.u14642 from rfl, totK_node, atot14641, atot14642]
  decide +kernel

theorem arows14646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14646 = true := by
  rw [show D2M8K2.u14646 = KTree.node D2M8K2.u14644 (nat_lit 31731652) (nat_lit 3707512996) (nat_lit 0) D2M8K2.u14645 from rfl, allE_node, arows14644, irow14646, arows14645]
  all_goals rfl

theorem atot14646 : totK PD2M8K2 D2M8K2.u14646 = [0, 325836699752, 1267029586610, 1482440647606, 493319206504, 25003318349, 0, 0] := by
  rw [show D2M8K2.u14646 = KTree.node D2M8K2.u14644 (nat_lit 31731652) (nat_lit 3707512996) (nat_lit 0) D2M8K2.u14645 from rfl, totK_node, atot14644, atot14645]
  decide +kernel

theorem arows14653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14653 = true := by
  rw [show D2M8K2.u14653 = KTree.node D2M8K2.u14651 (nat_lit 31737860) (nat_lit 3609900589) (nat_lit 0) D2M8K2.u14652 from rfl, allE_node, arows14651, irow14653, arows14652]
  all_goals rfl

theorem atot14653 : totK PD2M8K2 D2M8K2.u14653 = [0, 445546028575, 1494476430036, 1355680431014, 322860390811, 15828848387, 0, 0] := by
  rw [show D2M8K2.u14653 = KTree.node D2M8K2.u14651 (nat_lit 31737860) (nat_lit 3609900589) (nat_lit 0) D2M8K2.u14652 from rfl, totK_node, atot14651, atot14652]
  decide +kernel

theorem arows14656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14656 = true := by
  rw [show D2M8K2.u14656 = KTree.node D2M8K2.u14654 (nat_lit 31740943) (nat_lit 2353684945) (nat_lit 0) D2M8K2.u14655 from rfl, allE_node, arows14654, irow14656, arows14655]
  all_goals rfl

theorem atot14656 : totK PD2M8K2 D2M8K2.u14656 = [0, 398782189923, 1501979905760, 1428230521730, 229446348553, 3666196603, 0, 0] := by
  rw [show D2M8K2.u14656 = KTree.node D2M8K2.u14654 (nat_lit 31740943) (nat_lit 2353684945) (nat_lit 0) D2M8K2.u14655 from rfl, totK_node, atot14654, atot14655]
  decide +kernel

theorem arows14660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14660 = true := by
  rw [show D2M8K2.u14660 = KTree.node D2M8K2.u14658 (nat_lit 31744809) (nat_lit 1440189803) (nat_lit 0) D2M8K2.u14659 from rfl, allE_node, arows14658, irow14660, arows14659]
  all_goals rfl

theorem atot14660 : totK PD2M8K2 D2M8K2.u14660 = [0, 423605550748, 1424253927739, 1400574987822, 335154981127, 9836738884, 0, 0] := by
  rw [show D2M8K2.u14660 = KTree.node D2M8K2.u14658 (nat_lit 31744809) (nat_lit 1440189803) (nat_lit 0) D2M8K2.u14659 from rfl, totK_node, atot14658, atot14659]
  decide +kernel

theorem arows14663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14663 = true := by
  rw [show D2M8K2.u14663 = KTree.node D2M8K2.u14661 (nat_lit 31748073) (nat_lit 1916366651) (nat_lit 0) D2M8K2.u14662 from rfl, allE_node, arows14661, irow14663, arows14662]
  all_goals rfl

theorem atot14663 : totK PD2M8K2 D2M8K2.u14663 = [0, 0, 507681940829, 1661357111468, 1143220095729, 131316457211, 1217496766, 0] := by
  rw [show D2M8K2.u14663 = KTree.node D2M8K2.u14661 (nat_lit 31748073) (nat_lit 1916366651) (nat_lit 0) D2M8K2.u14662 from rfl, totK_node, atot14661, atot14662]
  decide +kernel

theorem arows14668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14668 = true := by
  rw [show D2M8K2.u14668 = KTree.node D2M8K2.u14666 (nat_lit 31751992) (nat_lit 2304609080) (nat_lit 0) D2M8K2.u14667 from rfl, allE_node, arows14666, irow14668, arows14667]
  all_goals rfl

theorem atot14668 : totK PD2M8K2 D2M8K2.u14668 = [0, 0, 785144864253, 1899385550663, 868180460616, 59375851230, 0, 0] := by
  rw [show D2M8K2.u14668 = KTree.node D2M8K2.u14666 (nat_lit 31751992) (nat_lit 2304609080) (nat_lit 0) D2M8K2.u14667 from rfl, totK_node, atot14666, atot14667]
  decide +kernel

theorem arows14671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14671 = true := by
  rw [show D2M8K2.u14671 = KTree.node D2M8K2.u14669 (nat_lit 31760374) (nat_lit 3336756504) (nat_lit 0) D2M8K2.u14670 from rfl, allE_node, arows14669, irow14671, arows14670]
  all_goals rfl

theorem atot14671 : totK PD2M8K2 D2M8K2.u14671 = [0, 0, 407320997748, 1437252873783, 1317089192737, 303981060019, 13105450397, 0] := by
  rw [show D2M8K2.u14671 = KTree.node D2M8K2.u14669 (nat_lit 31760374) (nat_lit 3336756504) (nat_lit 0) D2M8K2.u14670 from rfl, totK_node, atot14669, atot14670]
  decide +kernel

theorem arows14675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14675 = true := by
  rw [show D2M8K2.u14675 = KTree.node D2M8K2.u14673 (nat_lit 31764239) (nat_lit 2708652181) (nat_lit 0) D2M8K2.u14674 from rfl, allE_node, arows14673, irow14675, arows14674]
  all_goals rfl

theorem atot14675 : totK PD2M8K2 D2M8K2.u14675 = [0, 71990150170, 561529330474, 1514884768936, 1152009265277, 178422919326, 4630915822, 0] := by
  rw [show D2M8K2.u14675 = KTree.node D2M8K2.u14673 (nat_lit 31764239) (nat_lit 2708652181) (nat_lit 0) D2M8K2.u14674 from rfl, totK_node, atot14673, atot14674]
  decide +kernel

theorem arows14678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14678 = true := by
  rw [show D2M8K2.u14678 = KTree.node D2M8K2.u14676 (nat_lit 31769328) (nat_lit 3628317869) (nat_lit 0) D2M8K2.u14677 from rfl, allE_node, arows14676, irow14678, arows14677]
  all_goals rfl

theorem atot14678 : totK PD2M8K2 D2M8K2.u14678 = [0, 470129200671, 1591020153140, 1333962619674, 173295972849, 1310517177, 0, 0] := by
  rw [show D2M8K2.u14678 = KTree.node D2M8K2.u14676 (nat_lit 31769328) (nat_lit 3628317869) (nat_lit 0) D2M8K2.u14677 from rfl, totK_node, atot14676, atot14677]
  decide +kernel

theorem arows14684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14684 = true := by
  rw [show D2M8K2.u14684 = KTree.node D2M8K2.u14682 (nat_lit 31773266) (nat_lit 4092167636) (nat_lit 0) D2M8K2.u14683 from rfl, allE_node, arows14682, irow14684, arows14683]
  all_goals rfl

theorem atot14684 : totK PD2M8K2 D2M8K2.u14684 = [0, 402565004951, 1444379394006, 1400187852256, 378911113221, 15066332673, 0, 0] := by
  rw [show D2M8K2.u14684 = KTree.node D2M8K2.u14682 (nat_lit 31773266) (nat_lit 4092167636) (nat_lit 0) D2M8K2.u14683 from rfl, totK_node, atot14682, atot14683]
  decide +kernel

theorem arows14687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14687 = true := by
  rw [show D2M8K2.u14687 = KTree.node D2M8K2.u14685 (nat_lit 31779793) (nat_lit 1540901483) (nat_lit 0) D2M8K2.u14686 from rfl, allE_node, arows14685, irow14687, arows14686]
  all_goals rfl

theorem atot14687 : totK PD2M8K2 D2M8K2.u14687 = [0, 361386309935, 1407165837478, 1450706246637, 343274104633, 13250685261, 0, 0] := by
  rw [show D2M8K2.u14687 = KTree.node D2M8K2.u14685 (nat_lit 31779793) (nat_lit 1540901483) (nat_lit 0) D2M8K2.u14686 from rfl, totK_node, atot14685, atot14686]
  decide +kernel

theorem arows14691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14691 = true := by
  rw [show D2M8K2.u14691 = KTree.node D2M8K2.u14689 (nat_lit 31783163) (nat_lit 1500536427) (nat_lit 0) D2M8K2.u14690 from rfl, allE_node, arows14689, irow14691, arows14690]
  all_goals rfl

theorem atot14691 : totK PD2M8K2 D2M8K2.u14691 = [0, 340115668443, 1400849757481, 1534170303074, 319246123555, 6350335412, 0, 0] := by
  rw [show D2M8K2.u14691 = KTree.node D2M8K2.u14689 (nat_lit 31783163) (nat_lit 1500536427) (nat_lit 0) D2M8K2.u14690 from rfl, totK_node, atot14689, atot14690]
  decide +kernel

theorem arows14694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14694 = true := by
  rw [show D2M8K2.u14694 = KTree.node D2M8K2.u14692 (nat_lit 31790608) (nat_lit 3056005996) (nat_lit 0) D2M8K2.u14693 from rfl, allE_node, arows14692, irow14694, arows14693]
  all_goals rfl

theorem atot14694 : totK PD2M8K2 D2M8K2.u14694 = [0, 0, 582978067033, 1726601315366, 1063209384532, 100923651860, 1138244013, 0] := by
  rw [show D2M8K2.u14694 = KTree.node D2M8K2.u14692 (nat_lit 31790608) (nat_lit 3056005996) (nat_lit 0) D2M8K2.u14693 from rfl, totK_node, atot14692, atot14693]
  decide +kernel

theorem arows14699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14699 = true := by
  rw [show D2M8K2.u14699 = KTree.node D2M8K2.u14697 (nat_lit 31799857) (nat_lit 1378394017) (nat_lit 0) D2M8K2.u14698 from rfl, allE_node, arows14697, irow14699, arows14698]
  all_goals rfl

theorem atot14699 : totK PD2M8K2 D2M8K2.u14699 = [0, 0, 762949214448, 1899340314237, 830744233274, 41711372375, 0, 0] := by
  rw [show D2M8K2.u14699 = KTree.node D2M8K2.u14697 (nat_lit 31799857) (nat_lit 1378394017) (nat_lit 0) D2M8K2.u14698 from rfl, totK_node, atot14697, atot14698]
  decide +kernel

theorem arows14702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14702 = true := by
  rw [show D2M8K2.u14702 = KTree.node D2M8K2.u14700 (nat_lit 31805002) (nat_lit 2194506350) (nat_lit 0) D2M8K2.u14701 from rfl, allE_node, arows14700, irow14702, arows14701]
  all_goals rfl

theorem atot14702 : totK PD2M8K2 D2M8K2.u14702 = [0, 318670901333, 939908193841, 1164103837293, 886774630820, 166615320882, 4914284239, 0] := by
  rw [show D2M8K2.u14702 = KTree.node D2M8K2.u14700 (nat_lit 31805002) (nat_lit 2194506350) (nat_lit 0) D2M8K2.u14701 from rfl, totK_node, atot14700, atot14701]
  decide +kernel

theorem arows14706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14706 = true := by
  rw [show D2M8K2.u14706 = KTree.node D2M8K2.u14704 (nat_lit 31812324) (nat_lit 3284341931) (nat_lit 0) D2M8K2.u14705 from rfl, allE_node, arows14704, irow14706, arows14705]
  all_goals rfl

theorem atot14706 : totK PD2M8K2 D2M8K2.u14706 = [0, 470533470550, 1598166229529, 1376333334618, 184047483090, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14706 = KTree.node D2M8K2.u14704 (nat_lit 31812324) (nat_lit 3284341931) (nat_lit 0) D2M8K2.u14705 from rfl, totK_node, atot14704, atot14705]
  decide +kernel

theorem arows14709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14709 = true := by
  rw [show D2M8K2.u14709 = KTree.node D2M8K2.u14707 (nat_lit 31815532) (nat_lit 3513860523) (nat_lit 0) D2M8K2.u14708 from rfl, allE_node, arows14707, irow14709, arows14708]
  all_goals rfl

theorem atot14709 : totK PD2M8K2 D2M8K2.u14709 = [0, 296644314414, 1230049889789, 1519718551722, 553582218517, 32804607976, 0, 0] := by
  rw [show D2M8K2.u14709 = KTree.node D2M8K2.u14707 (nat_lit 31815532) (nat_lit 3513860523) (nat_lit 0) D2M8K2.u14708 from rfl, totK_node, atot14707, atot14708]
  decide +kernel

theorem arows14717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14717 = true := by
  rw [show D2M8K2.u14717 = KTree.node D2M8K2.u14715 (nat_lit 31819483) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u14716 from rfl, allE_node, arows14715, irow14717, arows14716]
  all_goals rfl

theorem atot14717 : totK PD2M8K2 D2M8K2.u14717 = [0, 511389393047, 1579872242856, 1306940745438, 232854474084, 5172807878, 0, 0] := by
  rw [show D2M8K2.u14717 = KTree.node D2M8K2.u14715 (nat_lit 31819483) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u14716 from rfl, totK_node, atot14715, atot14716]
  decide +kernel

theorem arows14720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14720 = true := by
  rw [show D2M8K2.u14720 = KTree.node D2M8K2.u14718 (nat_lit 31822683) (nat_lit 3626850800) (nat_lit 0) D2M8K2.u14719 from rfl, allE_node, arows14718, irow14720, arows14719]
  all_goals rfl

theorem atot14720 : totK PD2M8K2 D2M8K2.u14720 = [0, 366744729367, 1412834558924, 1473183894563, 346003074522, 13183098110, 0, 0] := by
  rw [show D2M8K2.u14720 = KTree.node D2M8K2.u14718 (nat_lit 31822683) (nat_lit 3626850800) (nat_lit 0) D2M8K2.u14719 from rfl, totK_node, atot14718, atot14719]
  decide +kernel

theorem arows14724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14724 = true := by
  rw [show D2M8K2.u14724 = KTree.node D2M8K2.u14722 (nat_lit 31829125) (nat_lit 1047935701) (nat_lit 0) D2M8K2.u14723 from rfl, allE_node, arows14722, irow14724, arows14723]
  all_goals rfl

theorem atot14724 : totK PD2M8K2 D2M8K2.u14724 = [266170613056, 750080895795, 977880311037, 1175588491612, 413610653159, 21982715828, 0, 0] := by
  rw [show D2M8K2.u14724 = KTree.node D2M8K2.u14722 (nat_lit 31829125) (nat_lit 1047935701) (nat_lit 0) D2M8K2.u14723 from rfl, totK_node, atot14722, atot14723]
  decide +kernel

theorem arows14727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14727 = true := by
  rw [show D2M8K2.u14727 = KTree.node D2M8K2.u14725 (nat_lit 32351092) (nat_lit 3963259066) (nat_lit 0) D2M8K2.u14726 from rfl, allE_node, arows14725, irow14727, arows14726]
  all_goals rfl

theorem atot14727 : totK PD2M8K2 D2M8K2.u14727 = [489208780876, 1601211187619, 1335743849692, 188842090495, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14727 = KTree.node D2M8K2.u14725 (nat_lit 32351092) (nat_lit 3963259066) (nat_lit 0) D2M8K2.u14726 from rfl, totK_node, atot14725, atot14726]
  decide +kernel

theorem arows14732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14732 = true := by
  rw [show D2M8K2.u14732 = KTree.node D2M8K2.u14730 (nat_lit 32358037) (nat_lit 1050533111) (nat_lit 0) D2M8K2.u14731 from rfl, allE_node, arows14730, irow14732, arows14731]
  all_goals rfl

theorem atot14732 : totK PD2M8K2 D2M8K2.u14732 = [376402997013, 1421663013157, 1428712324340, 334217553932, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14732 = KTree.node D2M8K2.u14730 (nat_lit 32358037) (nat_lit 1050533111) (nat_lit 0) D2M8K2.u14731 from rfl, totK_node, atot14730, atot14731]
  decide +kernel

theorem arows14735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14735 = true := by
  rw [show D2M8K2.u14735 = KTree.node D2M8K2.u14733 (nat_lit 32361443) (nat_lit 1732011239) (nat_lit 0) D2M8K2.u14734 from rfl, allE_node, arows14733, irow14735, arows14734]
  all_goals rfl

theorem atot14735 : totK PD2M8K2 D2M8K2.u14735 = [387317509543, 1410770325828, 1401766982241, 335796940546, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u14735 = KTree.node D2M8K2.u14733 (nat_lit 32361443) (nat_lit 1732011239) (nat_lit 0) D2M8K2.u14734 from rfl, totK_node, atot14733, atot14734]
  decide +kernel

theorem arows14739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14739 = true := by
  rw [show D2M8K2.u14739 = KTree.node D2M8K2.u14737 (nat_lit 32365667) (nat_lit 2364030877) (nat_lit 0) D2M8K2.u14738 from rfl, allE_node, arows14737, irow14739, arows14738]
  all_goals rfl

theorem atot14739 : totK PD2M8K2 D2M8K2.u14739 = [481759246045, 1586486801291, 1304165070211, 215698292746, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14739 = KTree.node D2M8K2.u14737 (nat_lit 32365667) (nat_lit 2364030877) (nat_lit 0) D2M8K2.u14738 from rfl, totK_node, atot14737, atot14738]
  decide +kernel

theorem arows14742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14742 = true := by
  rw [show D2M8K2.u14742 = KTree.node D2M8K2.u14740 (nat_lit 32368832) (nat_lit 2252310745) (nat_lit 0) D2M8K2.u14741 from rfl, allE_node, arows14740, irow14742, arows14741]
  all_goals rfl

theorem atot14742 : totK PD2M8K2 D2M8K2.u14742 = [0, 793206424192, 1907295163937, 797587748399, 43865840370, 0, 0, 0] := by
  rw [show D2M8K2.u14742 = KTree.node D2M8K2.u14740 (nat_lit 32368832) (nat_lit 2252310745) (nat_lit 0) D2M8K2.u14741 from rfl, totK_node, atot14740, atot14741]
  decide +kernel

theorem arows14748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14748 = true := by
  rw [show D2M8K2.u14748 = KTree.node D2M8K2.u14746 (nat_lit 32375906) (nat_lit 2807585784) (nat_lit 0) D2M8K2.u14747 from rfl, allE_node, arows14746, irow14748, arows14747]
  all_goals rfl

theorem atot14748 : totK PD2M8K2 D2M8K2.u14748 = [0, 473748285735, 1641959086238, 1240575078915, 164078613321, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14748 = KTree.node D2M8K2.u14746 (nat_lit 32375906) (nat_lit 2807585784) (nat_lit 0) D2M8K2.u14747 from rfl, totK_node, atot14746, atot14747]
  decide +kernel

theorem arows14751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14751 = true := by
  rw [show D2M8K2.u14751 = KTree.node D2M8K2.u14749 (nat_lit 32380797) (nat_lit 1402179801) (nat_lit 0) D2M8K2.u14750 from rfl, allE_node, arows14749, irow14751, arows14750]
  all_goals rfl

theorem atot14751 : totK PD2M8K2 D2M8K2.u14751 = [0, 730595286554, 1877296186779, 888928022247, 50748302942, 0, 0, 0] := by
  rw [show D2M8K2.u14751 = KTree.node D2M8K2.u14749 (nat_lit 32380797) (nat_lit 1402179801) (nat_lit 0) D2M8K2.u14750 from rfl, totK_node, atot14749, atot14750]
  decide +kernel

theorem arows14755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14755 = true := by
  rw [show D2M8K2.u14755 = KTree.node D2M8K2.u14753 (nat_lit 32387702) (nat_lit 3831439198) (nat_lit 0) D2M8K2.u14754 from rfl, allE_node, arows14753, irow14755, arows14754]
  all_goals rfl

theorem atot14755 : totK PD2M8K2 D2M8K2.u14755 = [321352686989, 1198791255953, 1515324335298, 589429988056, 32550054213, 0, 0, 0] := by
  rw [show D2M8K2.u14755 = KTree.node D2M8K2.u14753 (nat_lit 32387702) (nat_lit 3831439198) (nat_lit 0) D2M8K2.u14754 from rfl, totK_node, atot14753, atot14754]
  decide +kernel

theorem arows14758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14758 = true := by
  rw [show D2M8K2.u14758 = KTree.node D2M8K2.u14756 (nat_lit 32395789) (nat_lit 948974913) (nat_lit 0) D2M8K2.u14757 from rfl, allE_node, arows14756, irow14758, arows14757]
  all_goals rfl

theorem atot14758 : totK PD2M8K2 D2M8K2.u14758 = [280366904576, 1209175325953, 1544032281468, 590932312915, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u14758 = KTree.node D2M8K2.u14756 (nat_lit 32395789) (nat_lit 948974913) (nat_lit 0) D2M8K2.u14757 from rfl, totK_node, atot14756, atot14757]
  decide +kernel

theorem arows14763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14763 = true := by
  rw [show D2M8K2.u14763 = KTree.node D2M8K2.u14761 (nat_lit 32398672) (nat_lit 3344895372) (nat_lit 0) D2M8K2.u14762 from rfl, allE_node, arows14761, irow14763, arows14762]
  all_goals rfl

theorem atot14763 : totK PD2M8K2 D2M8K2.u14763 = [414753389085, 1449416162964, 1410824341074, 324608789146, 12903319451, 0, 0, 0] := by
  rw [show D2M8K2.u14763 = KTree.node D2M8K2.u14761 (nat_lit 32398672) (nat_lit 3344895372) (nat_lit 0) D2M8K2.u14762 from rfl, totK_node, atot14761, atot14762]
  decide +kernel

theorem arows14766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14766 = true := by
  rw [show D2M8K2.u14766 = KTree.node D2M8K2.u14764 (nat_lit 32402096) (nat_lit 3710054563) (nat_lit 0) D2M8K2.u14765 from rfl, allE_node, arows14764, irow14766, arows14765]
  all_goals rfl

theorem atot14766 : totK PD2M8K2 D2M8K2.u14766 = [398219357499, 1415956733245, 1458462352674, 341682041009, 13079279802, 0, 0, 0] := by
  rw [show D2M8K2.u14766 = KTree.node D2M8K2.u14764 (nat_lit 32402096) (nat_lit 3710054563) (nat_lit 0) D2M8K2.u14765 from rfl, totK_node, atot14764, atot14765]
  decide +kernel

theorem arows14770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14770 = true := by
  rw [show D2M8K2.u14770 = KTree.node D2M8K2.u14768 (nat_lit 32406394) (nat_lit 2630262499) (nat_lit 0) D2M8K2.u14769 from rfl, allE_node, arows14768, irow14770, arows14769]
  all_goals rfl

theorem atot14770 : totK PD2M8K2 D2M8K2.u14770 = [523498754449, 1672328636358, 1278535904076, 178450185199, 2739859532, 0, 0, 0] := by
  rw [show D2M8K2.u14770 = KTree.node D2M8K2.u14768 (nat_lit 32406394) (nat_lit 2630262499) (nat_lit 0) D2M8K2.u14769 from rfl, totK_node, atot14768, atot14769]
  decide +kernel

theorem arows14773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14773 = true := by
  rw [show D2M8K2.u14773 = KTree.node D2M8K2.u14771 (nat_lit 32409635) (nat_lit 2964126074) (nat_lit 0) D2M8K2.u14772 from rfl, allE_node, arows14771, irow14773, arows14772]
  all_goals rfl

theorem atot14773 : totK PD2M8K2 D2M8K2.u14773 = [92999530293, 987380542171, 1781008078152, 722820850899, 50500853437, 0, 0, 0] := by
  rw [show D2M8K2.u14773 = KTree.node D2M8K2.u14771 (nat_lit 32409635) (nat_lit 2964126074) (nat_lit 0) D2M8K2.u14772 from rfl, totK_node, atot14771, atot14772]
  decide +kernel

theorem arows14780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14780 = true := by
  rw [show D2M8K2.u14780 = KTree.node D2M8K2.u14778 (nat_lit 32416270) (nat_lit 3963947503) (nat_lit 0) D2M8K2.u14779 from rfl, allE_node, arows14778, irow14780, arows14779]
  all_goals rfl

theorem atot14780 : totK PD2M8K2 D2M8K2.u14780 = [0, 293939590949, 1227955100783, 1495408330635, 549499136113, 36921873854, 0, 0] := by
  rw [show D2M8K2.u14780 = KTree.node D2M8K2.u14778 (nat_lit 32416270) (nat_lit 3963947503) (nat_lit 0) D2M8K2.u14779 from rfl, totK_node, atot14778, atot14779]
  decide +kernel

theorem arows14783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14783 = true := by
  rw [show D2M8K2.u14783 = KTree.node D2M8K2.u14781 (nat_lit 32419324) (nat_lit 3923274989) (nat_lit 0) D2M8K2.u14782 from rfl, allE_node, arows14781, irow14783, arows14782]
  all_goals rfl

theorem atot14783 : totK PD2M8K2 D2M8K2.u14783 = [0, 449849924291, 1558421137388, 1355846523339, 243021236772, 5159868635, 0, 0] := by
  rw [show D2M8K2.u14783 = KTree.node D2M8K2.u14781 (nat_lit 32419324) (nat_lit 3923274989) (nat_lit 0) D2M8K2.u14782 from rfl, totK_node, atot14781, atot14782]
  decide +kernel

theorem arows14787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14787 = true := by
  rw [show D2M8K2.u14787 = KTree.node D2M8K2.u14785 (nat_lit 32422857) (nat_lit 1879381460) (nat_lit 0) D2M8K2.u14786 from rfl, allE_node, arows14785, irow14787, arows14786]
  all_goals rfl

theorem atot14787 : totK PD2M8K2 D2M8K2.u14787 = [0, 428253951565, 1503499862946, 1413438701055, 269687764026, 5218872685, 0, 0] := by
  rw [show D2M8K2.u14787 = KTree.node D2M8K2.u14785 (nat_lit 32422857) (nat_lit 1879381460) (nat_lit 0) D2M8K2.u14786 from rfl, totK_node, atot14785, atot14786]
  decide +kernel

theorem arows14790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14790 = true := by
  rw [show D2M8K2.u14790 = KTree.node D2M8K2.u14788 (nat_lit 32427189) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u14789 from rfl, allE_node, arows14788, irow14790, arows14789]
  all_goals rfl

theorem atot14790 : totK PD2M8K2 D2M8K2.u14790 = [0, 497406845948, 1653956684177, 1310076640572, 178718892359, 1415142070, 0, 0] := by
  rw [show D2M8K2.u14790 = KTree.node D2M8K2.u14788 (nat_lit 32427189) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u14789 from rfl, totK_node, atot14788, atot14789]
  decide +kernel

theorem arows14795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14795 = true := by
  rw [show D2M8K2.u14795 = KTree.node D2M8K2.u14793 (nat_lit 32430952) (nat_lit 3774196079) (nat_lit 0) D2M8K2.u14794 from rfl, allE_node, arows14793, irow14795, arows14794]
  all_goals rfl

theorem atot14795 : totK PD2M8K2 D2M8K2.u14795 = [337985661236, 903452080149, 1033937946212, 994701298145, 285767696862, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14795 = KTree.node D2M8K2.u14793 (nat_lit 32430952) (nat_lit 3774196079) (nat_lit 0) D2M8K2.u14794 from rfl, totK_node, atot14793, atot14794]
  decide +kernel

theorem arows14798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14798 = true := by
  rw [show D2M8K2.u14798 = KTree.node D2M8K2.u14796 (nat_lit 32434921) (nat_lit 684388306) (nat_lit 0) D2M8K2.u14797 from rfl, allE_node, arows14796, irow14798, arows14797]
  all_goals rfl

theorem atot14798 : totK PD2M8K2 D2M8K2.u14798 = [487799923811, 1616144054364, 1345882608330, 192810665421, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14798 = KTree.node D2M8K2.u14796 (nat_lit 32434921) (nat_lit 684388306) (nat_lit 0) D2M8K2.u14797 from rfl, totK_node, atot14796, atot14797]
  decide +kernel

theorem arows14802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14802 = true := by
  rw [show D2M8K2.u14802 = KTree.node D2M8K2.u14800 (nat_lit 32437692) (nat_lit 1888260519) (nat_lit 0) D2M8K2.u14801 from rfl, allE_node, arows14800, irow14802, arows14801]
  all_goals rfl

theorem atot14802 : totK PD2M8K2 D2M8K2.u14802 = [285516911903, 1194657695963, 1537120303936, 588239538540, 37409560203, 0, 0, 0] := by
  rw [show D2M8K2.u14802 = KTree.node D2M8K2.u14800 (nat_lit 32437692) (nat_lit 1888260519) (nat_lit 0) D2M8K2.u14801 from rfl, totK_node, atot14800, atot14801]
  decide +kernel

theorem arows14805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14805 = true := by
  rw [show D2M8K2.u14805 = KTree.node D2M8K2.u14803 (nat_lit 32440560) (nat_lit 3222377419) (nat_lit 0) D2M8K2.u14804 from rfl, allE_node, arows14803, irow14805, arows14804]
  all_goals rfl

theorem atot14805 : totK PD2M8K2 D2M8K2.u14805 = [406306053643, 1433157894157, 1421238926960, 332381866200, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14805 = KTree.node D2M8K2.u14803 (nat_lit 32440560) (nat_lit 3222377419) (nat_lit 0) D2M8K2.u14804 from rfl, totK_node, atot14803, atot14804]
  decide +kernel

theorem arows14811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14811 = true := by
  rw [show D2M8K2.u14811 = KTree.node D2M8K2.u14809 (nat_lit 32448474) (nat_lit 3795893381) (nat_lit 0) D2M8K2.u14810 from rfl, allE_node, arows14809, irow14811, arows14810]
  all_goals rfl

theorem atot14811 : totK PD2M8K2 D2M8K2.u14811 = [500634718716, 1591149904265, 1300367805235, 222299789889, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14811 = KTree.node D2M8K2.u14809 (nat_lit 32448474) (nat_lit 3795893381) (nat_lit 0) D2M8K2.u14810 from rfl, totK_node, atot14809, atot14810]
  decide +kernel

theorem arows14814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14814 = true := by
  rw [show D2M8K2.u14814 = KTree.node D2M8K2.u14812 (nat_lit 32451675) (nat_lit 3640750391) (nat_lit 0) D2M8K2.u14813 from rfl, allE_node, arows14812, irow14814, arows14813]
  all_goals rfl

theorem atot14814 : totK PD2M8K2 D2M8K2.u14814 = [0, 833162174492, 1912649717769, 757790118138, 36862924779, 0, 0, 0] := by
  rw [show D2M8K2.u14814 = KTree.node D2M8K2.u14812 (nat_lit 32451675) (nat_lit 3640750391) (nat_lit 0) D2M8K2.u14813 from rfl, totK_node, atot14812, atot14813]
  decide +kernel

theorem arows14818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14818 = true := by
  rw [show D2M8K2.u14818 = KTree.node D2M8K2.u14816 (nat_lit 32455718) (nat_lit 4060571057) (nat_lit 0) D2M8K2.u14817 from rfl, allE_node, arows14816, irow14818, arows14817]
  all_goals rfl

theorem atot14818 : totK PD2M8K2 D2M8K2.u14818 = [0, 493724391687, 1674362097536, 1269691849414, 145884998280, 1206465782, 0, 0] := by
  rw [show D2M8K2.u14818 = KTree.node D2M8K2.u14816 (nat_lit 32455718) (nat_lit 4060571057) (nat_lit 0) D2M8K2.u14817 from rfl, totK_node, atot14816, atot14817]
  decide +kernel

theorem arows14821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14821 = true := by
  rw [show D2M8K2.u14821 = KTree.node D2M8K2.u14819 (nat_lit 32460224) (nat_lit 3110775897) (nat_lit 0) D2M8K2.u14820 from rfl, allE_node, arows14819, irow14821, arows14820]
  all_goals rfl

theorem atot14821 : totK PD2M8K2 D2M8K2.u14821 = [0, 438388770348, 1482232157934, 1307509110630, 299217319576, 13016197374, 0, 0] := by
  rw [show D2M8K2.u14821 = KTree.node D2M8K2.u14819 (nat_lit 32460224) (nat_lit 3110775897) (nat_lit 0) D2M8K2.u14820 from rfl, totK_node, atot14819, atot14820]
  decide +kernel

theorem arows14826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14826 = true := by
  rw [show D2M8K2.u14826 = KTree.node D2M8K2.u14824 (nat_lit 32467405) (nat_lit 1361732872) (nat_lit 0) D2M8K2.u14825 from rfl, allE_node, arows14824, irow14826, arows14825]
  all_goals rfl

theorem atot14826 : totK PD2M8K2 D2M8K2.u14826 = [0, 495905860830, 1603523831543, 1243630443814, 191089054947, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14826 = KTree.node D2M8K2.u14824 (nat_lit 32467405) (nat_lit 1361732872) (nat_lit 0) D2M8K2.u14825 from rfl, totK_node, atot14824, atot14825]
  decide +kernel

theorem arows14829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14829 = true := by
  rw [show D2M8K2.u14829 = KTree.node D2M8K2.u14827 (nat_lit 32473162) (nat_lit 3862752225) (nat_lit 0) D2M8K2.u14828 from rfl, allE_node, arows14827, irow14829, arows14828]
  all_goals rfl

theorem atot14829 : totK PD2M8K2 D2M8K2.u14829 = [407248351753, 1367666670364, 1329774879572, 460939196423, 30312490523, 0, 0, 0] := by
  rw [show D2M8K2.u14829 = KTree.node D2M8K2.u14827 (nat_lit 32473162) (nat_lit 3862752225) (nat_lit 0) D2M8K2.u14828 from rfl, totK_node, atot14827, atot14828]
  decide +kernel

theorem arows14833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14833 = true := by
  rw [show D2M8K2.u14833 = KTree.node D2M8K2.u14831 (nat_lit 32476805) (nat_lit 2375965505) (nat_lit 0) D2M8K2.u14832 from rfl, allE_node, arows14831, irow14833, arows14832]
  all_goals rfl

theorem atot14833 : totK PD2M8K2 D2M8K2.u14833 = [418686965063, 1497870082079, 1423412557229, 296490001664, 17217278631, 0, 0, 0] := by
  rw [show D2M8K2.u14833 = KTree.node D2M8K2.u14831 (nat_lit 32476805) (nat_lit 2375965505) (nat_lit 0) D2M8K2.u14832 from rfl, totK_node, atot14831, atot14832]
  decide +kernel

theorem arows14836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14836 = true := by
  rw [show D2M8K2.u14836 = KTree.node D2M8K2.u14834 (nat_lit 32483065) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u14835 from rfl, allE_node, arows14834, irow14836, arows14835]
  all_goals rfl

theorem atot14836 : totK PD2M8K2 D2M8K2.u14836 = [440017792159, 1377715381292, 1343515984775, 457502582891, 21560118809, 0, 0, 0] := by
  rw [show D2M8K2.u14836 = KTree.node D2M8K2.u14834 (nat_lit 32483065) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u14835 from rfl, totK_node, atot14834, atot14835]
  decide +kernel

theorem arows14846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14846 = true := by
  rw [show D2M8K2.u14846 = KTree.node D2M8K2.u14844 (nat_lit 32486196) (nat_lit 3173569772) (nat_lit 0) D2M8K2.u14845 from rfl, allE_node, arows14844, irow14846, arows14845]
  all_goals rfl

theorem atot14846 : totK PD2M8K2 D2M8K2.u14846 = [324118546996, 1379027016548, 1523971328844, 356542974330, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u14846 = KTree.node D2M8K2.u14844 (nat_lit 32486196) (nat_lit 3173569772) (nat_lit 0) D2M8K2.u14845 from rfl, totK_node, atot14844, atot14845]
  decide +kernel

theorem arows14849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14849 = true := by
  rw [show D2M8K2.u14849 = KTree.node D2M8K2.u14847 (nat_lit 32490366) (nat_lit 4014156936) (nat_lit 0) D2M8K2.u14848 from rfl, allE_node, arows14847, irow14849, arows14848]
  all_goals rfl

theorem atot14849 : totK PD2M8K2 D2M8K2.u14849 = [428678734595, 1485750499227, 1414914134408, 285991159806, 6249254262, 0, 0, 0] := by
  rw [show D2M8K2.u14849 = KTree.node D2M8K2.u14847 (nat_lit 32490366) (nat_lit 4014156936) (nat_lit 0) D2M8K2.u14848 from rfl, totK_node, atot14847, atot14848]
  decide +kernel

theorem arows14853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14853 = true := by
  rw [show D2M8K2.u14853 = KTree.node D2M8K2.u14851 (nat_lit 32493556) (nat_lit 3292707627) (nat_lit 0) D2M8K2.u14852 from rfl, allE_node, arows14851, irow14853, arows14852]
  all_goals rfl

theorem atot14853 : totK PD2M8K2 D2M8K2.u14853 = [0, 728155047704, 1866223895828, 901107778886, 54550816021, 0, 0, 0] := by
  rw [show D2M8K2.u14853 = KTree.node D2M8K2.u14851 (nat_lit 32493556) (nat_lit 3292707627) (nat_lit 0) D2M8K2.u14852 from rfl, totK_node, atot14851, atot14852]
  decide +kernel

theorem arows14856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14856 = true := by
  rw [show D2M8K2.u14856 = KTree.node D2M8K2.u14854 (nat_lit 32497633) (nat_lit 1471230399) (nat_lit 0) D2M8K2.u14855 from rfl, allE_node, arows14854, irow14856, arows14855]
  all_goals rfl

theorem atot14856 : totK PD2M8K2 D2M8K2.u14856 = [0, 566183370807, 1696117390921, 1202956427461, 139184756910, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14856 = KTree.node D2M8K2.u14854 (nat_lit 32497633) (nat_lit 1471230399) (nat_lit 0) D2M8K2.u14855 from rfl, totK_node, atot14854, atot14855]
  decide +kernel

theorem arows14861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14861 = true := by
  rw [show D2M8K2.u14861 = KTree.node D2M8K2.u14859 (nat_lit 32505528) (nat_lit 3602479749) (nat_lit 0) D2M8K2.u14860 from rfl, allE_node, arows14859, irow14861, arows14860]
  all_goals rfl

theorem atot14861 : totK PD2M8K2 D2M8K2.u14861 = [0, 368990127438, 1428411547212, 1404857327481, 316441547278, 13105450397, 0, 0] := by
  rw [show D2M8K2.u14861 = KTree.node D2M8K2.u14859 (nat_lit 32505528) (nat_lit 3602479749) (nat_lit 0) D2M8K2.u14860 from rfl, totK_node, atot14859, atot14860]
  decide +kernel

theorem arows14864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14864 = true := by
  rw [show D2M8K2.u14864 = KTree.node D2M8K2.u14862 (nat_lit 32509759) (nat_lit 2360457015) (nat_lit 0) D2M8K2.u14863 from rfl, allE_node, arows14862, irow14864, arows14863]
  all_goals rfl

theorem atot14864 : totK PD2M8K2 D2M8K2.u14864 = [0, 525430562662, 1609304532993, 1240572866466, 188710861430, 4720618446, 0, 0] := by
  rw [show D2M8K2.u14864 = KTree.node D2M8K2.u14862 (nat_lit 32509759) (nat_lit 2360457015) (nat_lit 0) D2M8K2.u14863 from rfl, totK_node, atot14862, atot14863]
  decide +kernel

theorem arows14868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14868 = true := by
  rw [show D2M8K2.u14868 = KTree.node D2M8K2.u14866 (nat_lit 32556474) (nat_lit 3935039902) (nat_lit 0) D2M8K2.u14867 from rfl, allE_node, arows14866, irow14868, arows14867]
  all_goals rfl

theorem atot14868 : totK PD2M8K2 D2M8K2.u14868 = [417370246931, 1419129084957, 1356228979836, 392973981361, 23449102626, 0, 0, 0] := by
  rw [show D2M8K2.u14868 = KTree.node D2M8K2.u14866 (nat_lit 32556474) (nat_lit 3935039902) (nat_lit 0) D2M8K2.u14867 from rfl, totK_node, atot14866, atot14867]
  decide +kernel

theorem arows14871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14871 = true := by
  rw [show D2M8K2.u14871 = KTree.node D2M8K2.u14869 (nat_lit 32560014) (nat_lit 3950856744) (nat_lit 0) D2M8K2.u14870 from rfl, allE_node, arows14869, irow14871, arows14870]
  all_goals rfl

theorem atot14871 : totK PD2M8K2 D2M8K2.u14871 = [427093384176, 1486634400356, 1378592459367, 345681465821, 24234642673, 0, 0, 0] := by
  rw [show D2M8K2.u14871 = KTree.node D2M8K2.u14869 (nat_lit 32560014) (nat_lit 3950856744) (nat_lit 0) D2M8K2.u14870 from rfl, totK_node, atot14869, atot14870]
  decide +kernel

theorem arows14877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14877 = true := by
  rw [show D2M8K2.u14877 = KTree.node D2M8K2.u14875 (nat_lit 32562854) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u14876 from rfl, allE_node, arows14875, irow14877, arows14876]
  all_goals rfl

theorem atot14877 : totK PD2M8K2 D2M8K2.u14877 = [422023626085, 1412342493250, 1388278185461, 388789915241, 14254720854, 0, 0, 0] := by
  rw [show D2M8K2.u14877 = KTree.node D2M8K2.u14875 (nat_lit 32562854) (nat_lit 4041768059) (nat_lit 0) D2M8K2.u14876 from rfl, totK_node, atot14875, atot14876]
  decide +kernel

theorem arows14880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14880 = true := by
  rw [show D2M8K2.u14880 = KTree.node D2M8K2.u14878 (nat_lit 32566251) (nat_lit 3704293716) (nat_lit 0) D2M8K2.u14879 from rfl, allE_node, arows14878, irow14880, arows14879]
  all_goals rfl

theorem atot14880 : totK PD2M8K2 D2M8K2.u14880 = [422231182245, 1484528328575, 1404624968108, 295290967640, 11738734009, 0, 0, 0] := by
  rw [show D2M8K2.u14880 = KTree.node D2M8K2.u14878 (nat_lit 32566251) (nat_lit 3704293716) (nat_lit 0) D2M8K2.u14879 from rfl, totK_node, atot14878, atot14879]
  decide +kernel

theorem arows14884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14884 = true := by
  rw [show D2M8K2.u14884 = KTree.node D2M8K2.u14882 (nat_lit 32573048) (nat_lit 2651465953) (nat_lit 0) D2M8K2.u14883 from rfl, allE_node, arows14882, irow14884, arows14883]
  all_goals rfl

theorem atot14884 : totK PD2M8K2 D2M8K2.u14884 = [448209323343, 1480636924942, 1378657602187, 325568694493, 13071894232, 0, 0, 0] := by
  rw [show D2M8K2.u14884 = KTree.node D2M8K2.u14882 (nat_lit 32573048) (nat_lit 2651465953) (nat_lit 0) D2M8K2.u14883 from rfl, totK_node, atot14882, atot14883]
  decide +kernel

theorem arows14887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14887 = true := by
  rw [show D2M8K2.u14887 = KTree.node D2M8K2.u14885 (nat_lit 32576138) (nat_lit 4134472591) (nat_lit 0) D2M8K2.u14886 from rfl, allE_node, arows14885, irow14887, arows14886]
  all_goals rfl

theorem atot14887 : totK PD2M8K2 D2M8K2.u14887 = [0, 824008246611, 1944838309511, 769450823696, 32483106296, 0, 0, 0] := by
  rw [show D2M8K2.u14887 = KTree.node D2M8K2.u14885 (nat_lit 32576138) (nat_lit 4134472591) (nat_lit 0) D2M8K2.u14886 from rfl, totK_node, atot14885, atot14886]
  decide +kernel

theorem arows14892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14892 = true := by
  rw [show D2M8K2.u14892 = KTree.node D2M8K2.u14890 (nat_lit 32580112) (nat_lit 3303686054) (nat_lit 0) D2M8K2.u14891 from rfl, allE_node, arows14890, irow14892, arows14891]
  all_goals rfl

theorem atot14892 : totK PD2M8K2 D2M8K2.u14892 = [0, 477403808178, 1629415528077, 1357840260145, 159764397079, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14892 = KTree.node D2M8K2.u14890 (nat_lit 32580112) (nat_lit 3303686054) (nat_lit 0) D2M8K2.u14891 from rfl, totK_node, atot14890, atot14891]
  decide +kernel

theorem arows14895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14895 = true := by
  rw [show D2M8K2.u14895 = KTree.node D2M8K2.u14893 (nat_lit 32584618) (nat_lit 3991841279) (nat_lit 0) D2M8K2.u14894 from rfl, allE_node, arows14893, irow14895, arows14894]
  all_goals rfl

theorem atot14895 : totK PD2M8K2 D2M8K2.u14895 = [0, 438406758745, 1532977475946, 1362958279783, 224947927829, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14895 = KTree.node D2M8K2.u14893 (nat_lit 32584618) (nat_lit 3991841279) (nat_lit 0) D2M8K2.u14894 from rfl, totK_node, atot14893, atot14894]
  decide +kernel

theorem arows14899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14899 = true := by
  rw [show D2M8K2.u14899 = KTree.node D2M8K2.u14897 (nat_lit 32588158) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u14898 from rfl, allE_node, arows14897, irow14899, arows14898]
  all_goals rfl

theorem atot14899 : totK PD2M8K2 D2M8K2.u14899 = [0, 488562808336, 1576959599152, 1286824288531, 214589224040, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14899 = KTree.node D2M8K2.u14897 (nat_lit 32588158) (nat_lit 3916153066) (nat_lit 0) D2M8K2.u14898 from rfl, totK_node, atot14897, atot14898]
  decide +kernel

theorem arows14902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14902 = true := by
  rw [show D2M8K2.u14902 = KTree.node D2M8K2.u14900 (nat_lit 32595132) (nat_lit 3252458510) (nat_lit 0) D2M8K2.u14901 from rfl, allE_node, arows14900, irow14902, arows14901]
  all_goals rfl

theorem atot14902 : totK PD2M8K2 D2M8K2.u14902 = [0, 359303690966, 1463287294580, 1460817831001, 303898127269, 8424427256, 0, 0] := by
  rw [show D2M8K2.u14902 = KTree.node D2M8K2.u14900 (nat_lit 32595132) (nat_lit 3252458510) (nat_lit 0) D2M8K2.u14901 from rfl, totK_node, atot14900, atot14901]
  decide +kernel

theorem arows14909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14909 = true := by
  rw [show D2M8K2.u14909 = KTree.node D2M8K2.u14907 (nat_lit 32598337) (nat_lit 1411258368) (nat_lit 0) D2M8K2.u14908 from rfl, allE_node, arows14907, irow14909, arows14908]
  all_goals rfl

theorem atot14909 : totK PD2M8K2 D2M8K2.u14909 = [0, 435713681569, 1520804474499, 1344509052042, 276315994401, 14695891242, 0, 0] := by
  rw [show D2M8K2.u14909 = KTree.node D2M8K2.u14907 (nat_lit 32598337) (nat_lit 1411258368) (nat_lit 0) D2M8K2.u14908 from rfl, totK_node, atot14907, atot14908]
  decide +kernel

theorem arows14912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14912 = true := by
  rw [show D2M8K2.u14912 = KTree.node D2M8K2.u14910 (nat_lit 32605402) (nat_lit 4009346706) (nat_lit 0) D2M8K2.u14911 from rfl, allE_node, arows14910, irow14912, arows14911]
  all_goals rfl

theorem atot14912 : totK PD2M8K2 D2M8K2.u14912 = [0, 429999876807, 1503237087201, 1392152485917, 256588357172, 5172807878, 0, 0] := by
  rw [show D2M8K2.u14912 = KTree.node D2M8K2.u14910 (nat_lit 32605402) (nat_lit 4009346706) (nat_lit 0) D2M8K2.u14911 from rfl, totK_node, atot14910, atot14911]
  decide +kernel

theorem arows14916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14916 = true := by
  rw [show D2M8K2.u14916 = KTree.node D2M8K2.u14914 (nat_lit 32608939) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u14915 from rfl, allE_node, arows14914, irow14916, arows14915]
  all_goals rfl

theorem atot14916 : totK PD2M8K2 D2M8K2.u14916 = [0, 443711550150, 1510968863729, 1366560851557, 255353184277, 5228939780, 0, 0] := by
  rw [show D2M8K2.u14916 = KTree.node D2M8K2.u14914 (nat_lit 32608939) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u14915 from rfl, totK_node, atot14914, atot14915]
  decide +kernel

theorem arows14919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14919 = true := by
  rw [show D2M8K2.u14919 = KTree.node D2M8K2.u14917 (nat_lit 32613129) (nat_lit 1826488374) (nat_lit 0) D2M8K2.u14918 from rfl, allE_node, arows14917, irow14919, arows14918]
  all_goals rfl

theorem atot14919 : totK PD2M8K2 D2M8K2.u14919 = [0, 514776020636, 1658622576620, 1224876613760, 144958649822, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14919 = KTree.node D2M8K2.u14917 (nat_lit 32613129) (nat_lit 1826488374) (nat_lit 0) D2M8K2.u14918 from rfl, totK_node, atot14917, atot14918]
  decide +kernel

theorem arows14924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14924 = true := by
  rw [show D2M8K2.u14924 = KTree.node D2M8K2.u14922 (nat_lit 32616726) (nat_lit 2478264732) (nat_lit 0) D2M8K2.u14923 from rfl, allE_node, arows14922, irow14924, arows14923]
  all_goals rfl

theorem atot14924 : totK PD2M8K2 D2M8K2.u14924 = [0, 179867083042, 1087124272061, 1703900060565, 572347705918, 27259379182, 0, 0] := by
  rw [show D2M8K2.u14924 = KTree.node D2M8K2.u14922 (nat_lit 32616726) (nat_lit 2478264732) (nat_lit 0) D2M8K2.u14923 from rfl, totK_node, atot14922, atot14923]
  decide +kernel

theorem arows14927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14927 = true := by
  rw [show D2M8K2.u14927 = KTree.node D2M8K2.u14925 (nat_lit 32620136) (nat_lit 3855031423) (nat_lit 0) D2M8K2.u14926 from rfl, allE_node, arows14925, irow14927, arows14926]
  all_goals rfl

theorem atot14927 : totK PD2M8K2 D2M8K2.u14927 = [0, 0, 503014257564, 1691858119305, 1150577592093, 127603067827, 1369150432, 0] := by
  rw [show D2M8K2.u14927 = KTree.node D2M8K2.u14925 (nat_lit 32620136) (nat_lit 3855031423) (nat_lit 0) D2M8K2.u14926 from rfl, totK_node, atot14925, atot14926]
  decide +kernel

theorem arows14931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14931 = true := by
  rw [show D2M8K2.u14931 = KTree.node D2M8K2.u14929 (nat_lit 32629115) (nat_lit 2354828485) (nat_lit 0) D2M8K2.u14930 from rfl, allE_node, arows14929, irow14931, arows14930]
  all_goals rfl

theorem atot14931 : totK PD2M8K2 D2M8K2.u14931 = [0, 0, 773050039741, 1930458421594, 766924453293, 29033494429, 0, 0] := by
  rw [show D2M8K2.u14931 = KTree.node D2M8K2.u14929 (nat_lit 32629115) (nat_lit 2354828485) (nat_lit 0) D2M8K2.u14930 from rfl, totK_node, atot14929, atot14930]
  decide +kernel

theorem arows14934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14934 = true := by
  rw [show D2M8K2.u14934 = KTree.node D2M8K2.u14932 (nat_lit 32635880) (nat_lit 3200377769) (nat_lit 0) D2M8K2.u14933 from rfl, allE_node, arows14932, irow14934, arows14933]
  all_goals rfl

theorem atot14934 : totK PD2M8K2 D2M8K2.u14934 = [0, 182603865993, 1007227167809, 1694822082920, 666739893184, 31823675696, 0, 0] := by
  rw [show D2M8K2.u14934 = KTree.node D2M8K2.u14932 (nat_lit 32635880) (nat_lit 3200377769) (nat_lit 0) D2M8K2.u14933 from rfl, totK_node, atot14932, atot14933]
  decide +kernel

theorem arows14940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14940 = true := by
  rw [show D2M8K2.u14940 = KTree.node D2M8K2.u14938 (nat_lit 32644225) (nat_lit 1241836278) (nat_lit 0) D2M8K2.u14939 from rfl, allE_node, arows14938, irow14940, arows14939]
  all_goals rfl

theorem atot14940 : totK PD2M8K2 D2M8K2.u14940 = [0, 328735633225, 1216959785405, 1479827221188, 574857881381, 37500656948, 0, 0] := by
  rw [show D2M8K2.u14940 = KTree.node D2M8K2.u14938 (nat_lit 32644225) (nat_lit 1241836278) (nat_lit 0) D2M8K2.u14939 from rfl, totK_node, atot14938, atot14939]
  decide +kernel

theorem arows14943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14943 = true := by
  rw [show D2M8K2.u14943 = KTree.node D2M8K2.u14941 (nat_lit 32647033) (nat_lit 1217079773) (nat_lit 0) D2M8K2.u14942 from rfl, allE_node, arows14941, irow14943, arows14942]
  all_goals rfl

theorem atot14943 : totK PD2M8K2 D2M8K2.u14943 = [0, 403389144557, 1453614419889, 1428002254565, 313970726427, 9067749566, 0, 0] := by
  rw [show D2M8K2.u14943 = KTree.node D2M8K2.u14941 (nat_lit 32647033) (nat_lit 1217079773) (nat_lit 0) D2M8K2.u14942 from rfl, totK_node, atot14941, atot14942]
  decide +kernel

theorem arows14947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14947 = true := by
  rw [show D2M8K2.u14947 = KTree.node D2M8K2.u14945 (nat_lit 32650475) (nat_lit 2880337099) (nat_lit 0) D2M8K2.u14946 from rfl, allE_node, arows14945, irow14947, arows14946]
  all_goals rfl

theorem atot14947 : totK PD2M8K2 D2M8K2.u14947 = [0, 393443164512, 1454545135287, 1442323238349, 323545772410, 9178989717, 0, 0] := by
  rw [show D2M8K2.u14947 = KTree.node D2M8K2.u14945 (nat_lit 32650475) (nat_lit 2880337099) (nat_lit 0) D2M8K2.u14946 from rfl, totK_node, atot14945, atot14946]
  decide +kernel

theorem arows14950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14950 = true := by
  rw [show D2M8K2.u14950 = KTree.node D2M8K2.u14948 (nat_lit 32654618) (nat_lit 4203815236) (nat_lit 0) D2M8K2.u14949 from rfl, allE_node, arows14948, irow14950, arows14949]
  all_goals rfl

theorem atot14950 : totK PD2M8K2 D2M8K2.u14950 = [0, 538852405723, 1669735983779, 1273461795220, 188500849115, 1429815836, 0, 0] := by
  rw [show D2M8K2.u14950 = KTree.node D2M8K2.u14948 (nat_lit 32654618) (nat_lit 4203815236) (nat_lit 0) D2M8K2.u14949 from rfl, totK_node, atot14948, atot14949]
  decide +kernel

theorem arows14955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14955 = true := by
  rw [show D2M8K2.u14955 = KTree.node D2M8K2.u14953 (nat_lit 32658113) (nat_lit 2222962290) (nat_lit 0) D2M8K2.u14954 from rfl, allE_node, arows14953, irow14955, arows14954]
  all_goals rfl

theorem atot14955 : totK PD2M8K2 D2M8K2.u14955 = [0, 358228590485, 1342033468441, 1445576760089, 425938897867, 21930582058, 0, 0] := by
  rw [show D2M8K2.u14955 = KTree.node D2M8K2.u14953 (nat_lit 32658113) (nat_lit 2222962290) (nat_lit 0) D2M8K2.u14954 from rfl, totK_node, atot14953, atot14954]
  decide +kernel

theorem arows14958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14958 = true := by
  rw [show D2M8K2.u14958 = KTree.node D2M8K2.u14956 (nat_lit 32682278) (nat_lit 3887857554) (nat_lit 0) D2M8K2.u14957 from rfl, allE_node, arows14956, irow14958, arows14957]
  all_goals rfl

theorem atot14958 : totK PD2M8K2 D2M8K2.u14958 = [0, 440891551873, 1567394672908, 1391374056178, 188123893460, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14958 = KTree.node D2M8K2.u14956 (nat_lit 32682278) (nat_lit 3887857554) (nat_lit 0) D2M8K2.u14957 from rfl, totK_node, atot14956, atot14957]
  decide +kernel

theorem arows14962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14962 = true := by
  rw [show D2M8K2.u14962 = KTree.node D2M8K2.u14960 (nat_lit 32685823) (nat_lit 1644478199) (nat_lit 0) D2M8K2.u14961 from rfl, allE_node, arows14960, irow14962, arows14961]
  all_goals rfl

theorem atot14962 : totK PD2M8K2 D2M8K2.u14962 = [0, 327074118951, 1266849663095, 1447063615272, 536771699083, 32764831815, 0, 0] := by
  rw [show D2M8K2.u14962 = KTree.node D2M8K2.u14960 (nat_lit 32685823) (nat_lit 1644478199) (nat_lit 0) D2M8K2.u14961 from rfl, totK_node, atot14960, atot14961]
  decide +kernel

theorem arows14965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14965 = true := by
  rw [show D2M8K2.u14965 = KTree.node D2M8K2.u14963 (nat_lit 32688660) (nat_lit 3110413492) (nat_lit 0) D2M8K2.u14964 from rfl, allE_node, arows14963, irow14965, arows14964]
  all_goals rfl

theorem atot14965 : totK PD2M8K2 D2M8K2.u14965 = [0, 390181737437, 1410659722411, 1439005713031, 338018043865, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14965 = KTree.node D2M8K2.u14963 (nat_lit 32688660) (nat_lit 3110413492) (nat_lit 0) D2M8K2.u14964 from rfl, totK_node, atot14963, atot14964]
  decide +kernel

theorem arows14973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14973 = true := by
  rw [show D2M8K2.u14973 = KTree.node D2M8K2.u14971 (nat_lit 32695862) (nat_lit 3939627442) (nat_lit 0) D2M8K2.u14972 from rfl, allE_node, arows14971, irow14973, arows14972]
  all_goals rfl

theorem atot14973 : totK PD2M8K2 D2M8K2.u14973 = [0, 506995764618, 1603063854423, 1283384501399, 200792322191, 4783062791, 0, 0] := by
  rw [show D2M8K2.u14973 = KTree.node D2M8K2.u14971 (nat_lit 32695862) (nat_lit 3939627442) (nat_lit 0) D2M8K2.u14972 from rfl, totK_node, atot14971, atot14972]
  decide +kernel

theorem arows14976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14976 = true := by
  rw [show D2M8K2.u14976 = KTree.node D2M8K2.u14974 (nat_lit 32699620) (nat_lit 3859750214) (nat_lit 0) D2M8K2.u14975 from rfl, allE_node, arows14974, irow14976, arows14975]
  all_goals rfl

theorem atot14976 : totK PD2M8K2 D2M8K2.u14976 = [0, 165290289616, 1104691643676, 1716509903713, 566428749803, 24498997062, 0, 0] := by
  rw [show D2M8K2.u14976 = KTree.node D2M8K2.u14974 (nat_lit 32699620) (nat_lit 3859750214) (nat_lit 0) D2M8K2.u14975 from rfl, totK_node, atot14974, atot14975]
  decide +kernel

theorem arows14980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14980 = true := by
  rw [show D2M8K2.u14980 = KTree.node D2M8K2.u14978 (nat_lit 32703338) (nat_lit 3300136621) (nat_lit 0) D2M8K2.u14979 from rfl, allE_node, arows14978, irow14980, arows14979]
  all_goals rfl

theorem atot14980 : totK PD2M8K2 D2M8K2.u14980 = [0, 0, 621349620275, 1724128705596, 1068754278527, 100259213506, 1166720416, 0] := by
  rw [show D2M8K2.u14980 = KTree.node D2M8K2.u14978 (nat_lit 32703338) (nat_lit 3300136621) (nat_lit 0) D2M8K2.u14979 from rfl, totK_node, atot14978, atot14979]
  decide +kernel

theorem arows14983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14983 = true := by
  rw [show D2M8K2.u14983 = KTree.node D2M8K2.u14981 (nat_lit 32708929) (nat_lit 1399887781) (nat_lit 0) D2M8K2.u14982 from rfl, allE_node, arows14981, irow14983, arows14982]
  all_goals rfl

theorem atot14983 : totK PD2M8K2 D2M8K2.u14983 = [0, 0, 449697370052, 1598164274510, 1250764941473, 199010811077, 5134755853, 0] := by
  rw [show D2M8K2.u14983 = KTree.node D2M8K2.u14981 (nat_lit 32708929) (nat_lit 1399887781) (nat_lit 0) D2M8K2.u14982 from rfl, totK_node, atot14981, atot14982]
  decide +kernel

theorem arows14988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14988 = true := by
  rw [show D2M8K2.u14988 = KTree.node D2M8K2.u14986 (nat_lit 32718292) (nat_lit 4018806574) (nat_lit 0) D2M8K2.u14987 from rfl, allE_node, arows14986, irow14988, arows14987]
  all_goals rfl

theorem atot14988 : totK PD2M8K2 D2M8K2.u14988 = [0, 78205854702, 850124636626, 1790069808941, 778725015027, 47982809640, 0, 0] := by
  rw [show D2M8K2.u14988 = KTree.node D2M8K2.u14986 (nat_lit 32718292) (nat_lit 4018806574) (nat_lit 0) D2M8K2.u14987 from rfl, totK_node, atot14986, atot14987]
  decide +kernel

theorem arows14991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14991 = true := by
  rw [show D2M8K2.u14991 = KTree.node D2M8K2.u14989 (nat_lit 32723137) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u14990 from rfl, allE_node, arows14989, irow14991, arows14990]
  all_goals rfl

theorem atot14991 : totK PD2M8K2 D2M8K2.u14991 = [0, 440741429639, 1595770523259, 1372149059674, 181284509818, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14991 = KTree.node D2M8K2.u14989 (nat_lit 32723137) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u14990 from rfl, totK_node, atot14989, atot14990]
  decide +kernel

theorem arows14995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14995 = true := by
  rw [show D2M8K2.u14995 = KTree.node D2M8K2.u14993 (nat_lit 32727050) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u14994 from rfl, allE_node, arows14993, irow14995, arows14994]
  all_goals rfl

theorem atot14995 : totK PD2M8K2 D2M8K2.u14995 = [0, 324991844466, 1248043442812, 1471711249201, 545205143951, 32805585335, 0, 0] := by
  rw [show D2M8K2.u14995 = KTree.node D2M8K2.u14993 (nat_lit 32727050) (nat_lit 4274136801) (nat_lit 0) D2M8K2.u14994 from rfl, totK_node, atot14993, atot14994]
  decide +kernel

theorem arows14998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14998 = true := by
  rw [show D2M8K2.u14998 = KTree.node D2M8K2.u14996 (nat_lit 32733276) (nat_lit 3042969168) (nat_lit 0) D2M8K2.u14997 from rfl, allE_node, arows14996, irow14998, arows14997]
  all_goals rfl

theorem atot14998 : totK PD2M8K2 D2M8K2.u14998 = [0, 421123081787, 1458054735934, 1382775250780, 323317177936, 13189998508, 0, 0] := by
  rw [show D2M8K2.u14998 = KTree.node D2M8K2.u14996 (nat_lit 32733276) (nat_lit 3042969168) (nat_lit 0) D2M8K2.u14997 from rfl, totK_node, atot14996, atot14997]
  decide +kernel

theorem arows15004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15004 = true := by
  rw [show D2M8K2.u15004 = KTree.node D2M8K2.u15002 (nat_lit 32736961) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u15003 from rfl, allE_node, arows15002, irow15004, arows15003]
  all_goals rfl

theorem atot15004 : totK PD2M8K2 D2M8K2.u15004 = [0, 497017640919, 1594569275755, 1291275416196, 208647154620, 4917684815, 0, 0] := by
  rw [show D2M8K2.u15004 = KTree.node D2M8K2.u15002 (nat_lit 32736961) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u15003 from rfl, totK_node, atot15002, atot15003]
  decide +kernel

theorem arows15007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15007 = true := by
  rw [show D2M8K2.u15007 = KTree.node D2M8K2.u15005 (nat_lit 32740641) (nat_lit 1178198151) (nat_lit 0) D2M8K2.u15006 from rfl, allE_node, arows15005, irow15007, arows15006]
  all_goals rfl

theorem atot15007 : totK PD2M8K2 D2M8K2.u15007 = [0, 254577982652, 1236537368165, 1614251565590, 472632835976, 21976073925, 0, 0] := by
  rw [show D2M8K2.u15007 = KTree.node D2M8K2.u15005 (nat_lit 32740641) (nat_lit 1178198151) (nat_lit 0) D2M8K2.u15006 from rfl, totK_node, atot15005, atot15006]
  decide +kernel

theorem arows15011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15011 = true := by
  rw [show D2M8K2.u15011 = KTree.node D2M8K2.u15009 (nat_lit 32743992) (nat_lit 3640629068) (nat_lit 0) D2M8K2.u15010 from rfl, allE_node, arows15009, irow15011, arows15010]
  all_goals rfl

theorem atot15011 : totK PD2M8K2 D2M8K2.u15011 = [0, 0, 561085646307, 1729426623577, 1114368495257, 102643072527, 1200365979, 0] := by
  rw [show D2M8K2.u15011 = KTree.node D2M8K2.u15009 (nat_lit 32743992) (nat_lit 3640629068) (nat_lit 0) D2M8K2.u15010 from rfl, totK_node, atot15009, atot15010]
  decide +kernel

theorem arows15014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15014 = true := by
  rw [show D2M8K2.u15014 = KTree.node D2M8K2.u15012 (nat_lit 32753533) (nat_lit 1184706117) (nat_lit 0) D2M8K2.u15013 from rfl, allE_node, arows15012, irow15014, arows15013]
  all_goals rfl

theorem atot15014 : totK PD2M8K2 D2M8K2.u15014 = [0, 0, 594270380115, 1699107664470, 1123687182821, 130034893821, 1135526696, 0] := by
  rw [show D2M8K2.u15014 = KTree.node D2M8K2.u15012 (nat_lit 32753533) (nat_lit 1184706117) (nat_lit 0) D2M8K2.u15013 from rfl, totK_node, atot15012, atot15013]
  decide +kernel

theorem arows15019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15019 = true := by
  rw [show D2M8K2.u15019 = KTree.node D2M8K2.u15017 (nat_lit 32759526) (nat_lit 3625528704) (nat_lit 0) D2M8K2.u15018 from rfl, allE_node, arows15017, irow15019, arows15018]
  all_goals rfl

theorem atot15019 : totK PD2M8K2 D2M8K2.u15019 = [0, 0, 739410399757, 1789865134408, 892388696244, 109685646430, 4028038878, 0] := by
  rw [show D2M8K2.u15019 = KTree.node D2M8K2.u15017 (nat_lit 32759526) (nat_lit 3625528704) (nat_lit 0) D2M8K2.u15018 from rfl, totK_node, atot15017, atot15018]
  decide +kernel

theorem arows15022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15022 = true := by
  rw [show D2M8K2.u15022 = KTree.node D2M8K2.u15020 (nat_lit 32805857) (nat_lit 2209927316) (nat_lit 0) D2M8K2.u15021 from rfl, allE_node, arows15020, irow15022, arows15021]
  all_goals rfl

theorem atot15022 : totK PD2M8K2 D2M8K2.u15022 = [0, 494137245386, 1593107171068, 1288463359047, 212049616379, 11127908908, 0, 0] := by
  rw [show D2M8K2.u15022 = KTree.node D2M8K2.u15020 (nat_lit 32805857) (nat_lit 2209927316) (nat_lit 0) D2M8K2.u15021 from rfl, totK_node, atot15020, atot15021]
  decide +kernel

theorem arows15026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15026 = true := by
  rw [show D2M8K2.u15026 = KTree.node D2M8K2.u15024 (nat_lit 32809444) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u15025 from rfl, allE_node, arows15024, irow15026, arows15025]
  all_goals rfl

theorem atot15026 : totK PD2M8K2 D2M8K2.u15026 = [0, 349808447617, 1337732126081, 1467586193159, 455679858656, 23602487642, 0, 0] := by
  rw [show D2M8K2.u15026 = KTree.node D2M8K2.u15024 (nat_lit 32809444) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u15025 from rfl, totK_node, atot15024, atot15025]
  decide +kernel

theorem arows15029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15029 = true := by
  rw [show D2M8K2.u15029 = KTree.node D2M8K2.u15027 (nat_lit 32812461) (nat_lit 1384193135) (nat_lit 0) D2M8K2.u15028 from rfl, allE_node, arows15027, irow15029, arows15028]
  all_goals rfl

theorem atot15029 : totK PD2M8K2 D2M8K2.u15029 = [0, 421439210138, 1438130378289, 1377934011279, 343668244063, 14416418966, 0, 0] := by
  rw [show D2M8K2.u15029 = KTree.node D2M8K2.u15027 (nat_lit 32812461) (nat_lit 1384193135) (nat_lit 0) D2M8K2.u15028 from rfl, totK_node, atot15027, atot15028]
  decide +kernel

theorem arows15036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15036 = true := by
  rw [show D2M8K2.u15036 = KTree.node D2M8K2.u15034 (nat_lit 32815879) (nat_lit 2358974295) (nat_lit 0) D2M8K2.u15035 from rfl, allE_node, arows15034, irow15036, arows15035]
  all_goals rfl

theorem atot15036 : totK PD2M8K2 D2M8K2.u15036 = [0, 421650918186, 1464669306410, 1398594086018, 299612409033, 8626649553, 0, 0] := by
  rw [show D2M8K2.u15036 = KTree.node D2M8K2.u15034 (nat_lit 32815879) (nat_lit 2358974295) (nat_lit 0) D2M8K2.u15035 from rfl, totK_node, atot15034, atot15035]
  decide +kernel

theorem arows15039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15039 = true := by
  rw [show D2M8K2.u15039 = KTree.node D2M8K2.u15037 (nat_lit 32822450) (nat_lit 3823609116) (nat_lit 0) D2M8K2.u15038 from rfl, allE_node, arows15037, irow15039, arows15038]
  all_goals rfl

theorem atot15039 : totK PD2M8K2 D2M8K2.u15039 = [0, 447988386812, 1556543085410, 1402715882588, 243244224203, 2244900742, 0, 0] := by
  rw [show D2M8K2.u15039 = KTree.node D2M8K2.u15037 (nat_lit 32822450) (nat_lit 3823609116) (nat_lit 0) D2M8K2.u15038 from rfl, totK_node, atot15037, atot15038]
  decide +kernel

theorem arows15043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15043 = true := by
  rw [show D2M8K2.u15043 = KTree.node D2M8K2.u15041 (nat_lit 32825859) (nat_lit 2812507176) (nat_lit 0) D2M8K2.u15042 from rfl, allE_node, arows15041, irow15043, arows15042]
  all_goals rfl

theorem atot15043 : totK PD2M8K2 D2M8K2.u15043 = [0, 0, 603604889838, 1749319362802, 1028861154651, 110641134736, 1288491354, 0] := by
  rw [show D2M8K2.u15043 = KTree.node D2M8K2.u15041 (nat_lit 32825859) (nat_lit 2812507176) (nat_lit 0) D2M8K2.u15042 from rfl, totK_node, atot15041, atot15042]
  decide +kernel

theorem arows15046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15046 = true := by
  rw [show D2M8K2.u15046 = KTree.node D2M8K2.u15044 (nat_lit 32829562) (nat_lit 3734278442) (nat_lit 0) D2M8K2.u15045 from rfl, allE_node, arows15044, irow15046, arows15045]
  all_goals rfl

theorem atot15046 : totK PD2M8K2 D2M8K2.u15046 = [0, 0, 681884513505, 1806922576981, 1028453361708, 84158711067, 0, 0] := by
  rw [show D2M8K2.u15046 = KTree.node D2M8K2.u15044 (nat_lit 32829562) (nat_lit 3734278442) (nat_lit 0) D2M8K2.u15045 from rfl, totK_node, atot15044, atot15045]
  decide +kernel

theorem arows15051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15051 = true := by
  rw [show D2M8K2.u15051 = KTree.node D2M8K2.u15049 (nat_lit 32834505) (nat_lit 1170134171) (nat_lit 0) D2M8K2.u15050 from rfl, allE_node, arows15049, irow15051, arows15050]
  all_goals rfl

theorem atot15051 : totK PD2M8K2 D2M8K2.u15051 = [0, 0, 459616310347, 1572644704222, 1255490551446, 192265761254, 4787054165, 0] := by
  rw [show D2M8K2.u15051 = KTree.node D2M8K2.u15049 (nat_lit 32834505) (nat_lit 1170134171) (nat_lit 0) D2M8K2.u15050 from rfl, totK_node, atot15049, atot15050]
  decide +kernel

theorem arows15054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15054 = true := by
  rw [show D2M8K2.u15054 = KTree.node D2M8K2.u15052 (nat_lit 32838688) (nat_lit 3380013468) (nat_lit 0) D2M8K2.u15053 from rfl, allE_node, arows15052, irow15054, arows15053]
  all_goals rfl

theorem atot15054 : totK PD2M8K2 D2M8K2.u15054 = [0, 0, 459086732875, 1592182453520, 1264606591131, 199953582142, 4838243418, 0] := by
  rw [show D2M8K2.u15054 = KTree.node D2M8K2.u15052 (nat_lit 32838688) (nat_lit 3380013468) (nat_lit 0) D2M8K2.u15053 from rfl, totK_node, atot15052, atot15053]
  decide +kernel

theorem arows15058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15058 = true := by
  rw [show D2M8K2.u15058 = KTree.node D2M8K2.u15056 (nat_lit 32845189) (nat_lit 1012365084) (nat_lit 0) D2M8K2.u15057 from rfl, allE_node, arows15056, irow15058, arows15057]
  all_goals rfl

theorem atot15058 : totK PD2M8K2 D2M8K2.u15058 = [0, 267847118239, 776032742791, 995299236747, 1122487303118, 380630927501, 21751168066, 0] := by
  rw [show D2M8K2.u15058 = KTree.node D2M8K2.u15056 (nat_lit 32845189) (nat_lit 1012365084) (nat_lit 0) D2M8K2.u15057 from rfl, totK_node, atot15056, atot15057]
  decide +kernel

theorem arows15061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15061 = true := by
  rw [show D2M8K2.u15061 = KTree.node D2M8K2.u15059 (nat_lit 32848746) (nat_lit 3276330268) (nat_lit 0) D2M8K2.u15060 from rfl, allE_node, arows15059, irow15061, arows15060]
  all_goals rfl

theorem atot15061 : totK PD2M8K2 D2M8K2.u15061 = [0, 485319323654, 1606396438873, 1341366824806, 187512121918, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15061 = KTree.node D2M8K2.u15059 (nat_lit 32848746) (nat_lit 3276330268) (nat_lit 0) D2M8K2.u15060 from rfl, totK_node, atot15059, atot15060]
  decide +kernel

theorem arows15067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15067 = true := by
  rw [show D2M8K2.u15067 = KTree.node D2M8K2.u15065 (nat_lit 32855674) (nat_lit 3067775120) (nat_lit 0) D2M8K2.u15066 from rfl, allE_node, arows15065, irow15067, arows15066]
  all_goals rfl

theorem atot15067 : totK PD2M8K2 D2M8K2.u15067 = [0, 378863248668, 1415839397636, 1435129231813, 324826615291, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15067 = KTree.node D2M8K2.u15065 (nat_lit 32855674) (nat_lit 3067775120) (nat_lit 0) D2M8K2.u15066 from rfl, totK_node, atot15065, atot15066]
  decide +kernel

theorem arows15070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15070 = true := by
  rw [show D2M8K2.u15070 = KTree.node D2M8K2.u15068 (nat_lit 32859051) (nat_lit 2358911518) (nat_lit 0) D2M8K2.u15069 from rfl, allE_node, arows15068, irow15070, arows15069]
  all_goals rfl

theorem atot15070 : totK PD2M8K2 D2M8K2.u15070 = [0, 380957323349, 1400756362195, 1408718057705, 326318171976, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15070 = KTree.node D2M8K2.u15068 (nat_lit 32859051) (nat_lit 2358911518) (nat_lit 0) D2M8K2.u15069 from rfl, totK_node, atot15068, atot15069]
  decide +kernel

theorem arows15074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15074 = true := by
  rw [show D2M8K2.u15074 = KTree.node D2M8K2.u15072 (nat_lit 32862536) (nat_lit 3713827311) (nat_lit 0) D2M8K2.u15073 from rfl, allE_node, arows15072, irow15074, arows15073]
  all_goals rfl

theorem atot15074 : totK PD2M8K2 D2M8K2.u15074 = [0, 472401235453, 1550417954151, 1332350319550, 217735573153, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15074 = KTree.node D2M8K2.u15072 (nat_lit 32862536) (nat_lit 3713827311) (nat_lit 0) D2M8K2.u15073 from rfl, totK_node, atot15072, atot15073]
  decide +kernel

theorem arows15077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15077 = true := by
  rw [show D2M8K2.u15077 = KTree.node D2M8K2.u15075 (nat_lit 32865743) (nat_lit 2123388063) (nat_lit 0) D2M8K2.u15076 from rfl, allE_node, arows15075, irow15077, arows15076]
  all_goals rfl

theorem atot15077 : totK PD2M8K2 D2M8K2.u15077 = [0, 107971457226, 1021338253567, 1791292182451, 630408802039, 31659692706, 0, 0] := by
  rw [show D2M8K2.u15077 = KTree.node D2M8K2.u15075 (nat_lit 32865743) (nat_lit 2123388063) (nat_lit 0) D2M8K2.u15076 from rfl, totK_node, atot15075, atot15076]
  decide +kernel

theorem arows15082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15082 = true := by
  rw [show D2M8K2.u15082 = KTree.node D2M8K2.u15080 (nat_lit 32869226) (nat_lit 3740499905) (nat_lit 0) D2M8K2.u15081 from rfl, allE_node, arows15080, irow15082, arows15081]
  all_goals rfl

theorem atot15082 : totK PD2M8K2 D2M8K2.u15082 = [0, 0, 467878385540, 1641843811371, 1235523670220, 166206114982, 1369150432, 0] := by
  rw [show D2M8K2.u15082 = KTree.node D2M8K2.u15080 (nat_lit 32869226) (nat_lit 3740499905) (nat_lit 0) D2M8K2.u15081 from rfl, totK_node, atot15080, atot15081]
  decide +kernel

theorem arows15085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15085 = true := by
  rw [show D2M8K2.u15085 = KTree.node D2M8K2.u15083 (nat_lit 32877966) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u15084 from rfl, allE_node, arows15083, irow15085, arows15084]
  all_goals rfl

theorem atot15085 : totK PD2M8K2 D2M8K2.u15085 = [0, 0, 763716724907, 1902802964910, 825025099735, 37970113474, 0, 0] := by
  rw [show D2M8K2.u15085 = KTree.node D2M8K2.u15083 (nat_lit 32877966) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u15084 from rfl, totK_node, atot15083, atot15084]
  decide +kernel

theorem arows15089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15089 = true := by
  rw [show D2M8K2.u15089 = KTree.node D2M8K2.u15087 (nat_lit 32884363) (nat_lit 1313751783) (nat_lit 0) D2M8K2.u15088 from rfl, allE_node, arows15087, irow15089, arows15088]
  all_goals rfl

theorem atot15089 : totK PD2M8K2 D2M8K2.u15089 = [0, 108844600523, 855204828039, 1718736945585, 819685478867, 50491034843, 0, 0] := by
  rw [show D2M8K2.u15089 = KTree.node D2M8K2.u15087 (nat_lit 32884363) (nat_lit 1313751783) (nat_lit 0) D2M8K2.u15088 from rfl, totK_node, atot15087, atot15088]
  decide +kernel

theorem arows15092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15092 = true := by
  rw [show D2M8K2.u15092 = KTree.node D2M8K2.u15090 (nat_lit 32930597) (nat_lit 2285314593) (nat_lit 0) D2M8K2.u15091 from rfl, allE_node, arows15090, irow15092, arows15091]
  all_goals rfl

theorem atot15092 : totK PD2M8K2 D2M8K2.u15092 = [0, 473030392450, 1581179159364, 1356925480417, 195006003465, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15092 = KTree.node D2M8K2.u15090 (nat_lit 32930597) (nat_lit 2285314593) (nat_lit 0) D2M8K2.u15091 from rfl, totK_node, atot15090, atot15091]
  decide +kernel

theorem arows15101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15101 = true := by
  rw [show D2M8K2.u15101 = KTree.node D2M8K2.u15099 (nat_lit 32934732) (nat_lit 2441652066) (nat_lit 0) D2M8K2.u15100 from rfl, allE_node, arows15099, irow15101, arows15100]
  all_goals rfl

theorem atot15101 : totK PD2M8K2 D2M8K2.u15101 = [0, 391950459975, 1357738619531, 1397355595038, 476584667334, 32018534269, 0, 0] := by
  rw [show D2M8K2.u15101 = KTree.node D2M8K2.u15099 (nat_lit 32934732) (nat_lit 2441652066) (nat_lit 0) D2M8K2.u15100 from rfl, totK_node, atot15099, atot15100]
  decide +kernel

theorem arows15104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15104 = true := by
  rw [show D2M8K2.u15104 = KTree.node D2M8K2.u15102 (nat_lit 32937993) (nat_lit 1794421657) (nat_lit 0) D2M8K2.u15103 from rfl, allE_node, arows15102, irow15104, arows15103]
  all_goals rfl

theorem atot15104 : totK PD2M8K2 D2M8K2.u15104 = [0, 367997957358, 1419432904114, 1461946010585, 329745760409, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15104 = KTree.node D2M8K2.u15102 (nat_lit 32937993) (nat_lit 1794421657) (nat_lit 0) D2M8K2.u15103 from rfl, totK_node, atot15102, atot15103]
  decide +kernel

theorem arows15108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15108 = true := by
  rw [show D2M8K2.u15108 = KTree.node D2M8K2.u15106 (nat_lit 32944960) (nat_lit 3764622440) (nat_lit 0) D2M8K2.u15107 from rfl, allE_node, arows15106, irow15108, arows15107]
  all_goals rfl

theorem atot15108 : totK PD2M8K2 D2M8K2.u15108 = [0, 476417403175, 1559305953710, 1327059098750, 220220544670, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15108 = KTree.node D2M8K2.u15106 (nat_lit 32944960) (nat_lit 3764622440) (nat_lit 0) D2M8K2.u15107 from rfl, totK_node, atot15106, atot15107]
  decide +kernel

theorem arows15111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15111 = true := by
  rw [show D2M8K2.u15111 = KTree.node D2M8K2.u15109 (nat_lit 32948506) (nat_lit 3709670711) (nat_lit 0) D2M8K2.u15110 from rfl, allE_node, arows15109, irow15111, arows15110]
  all_goals rfl

theorem atot15111 : totK PD2M8K2 D2M8K2.u15111 = [0, 161288847707, 1068379941311, 1718591377492, 618300159119, 31883931686, 0, 0] := by
  rw [show D2M8K2.u15111 = KTree.node D2M8K2.u15109 (nat_lit 32948506) (nat_lit 3709670711) (nat_lit 0) D2M8K2.u15110 from rfl, totK_node, atot15109, atot15110]
  decide +kernel

theorem arows15116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15116 = true := by
  rw [show D2M8K2.u15116 = KTree.node D2M8K2.u15114 (nat_lit 32952168) (nat_lit 3486472135) (nat_lit 0) D2M8K2.u15115 from rfl, allE_node, arows15114, irow15116, arows15115]
  all_goals rfl

theorem atot15116 : totK PD2M8K2 D2M8K2.u15116 = [0, 0, 506584575830, 1681170747404, 1203229062869, 138096815571, 1206465782, 0] := by
  rw [show D2M8K2.u15116 = KTree.node D2M8K2.u15114 (nat_lit 32952168) (nat_lit 3486472135) (nat_lit 0) D2M8K2.u15115 from rfl, totK_node, atot15114, atot15115]
  decide +kernel

theorem arows15119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15119 = true := by
  rw [show D2M8K2.u15119 = KTree.node D2M8K2.u15117 (nat_lit 32957652) (nat_lit 2913512365) (nat_lit 0) D2M8K2.u15118 from rfl, allE_node, arows15117, irow15119, arows15118]
  all_goals rfl

theorem atot15119 : totK PD2M8K2 D2M8K2.u15119 = [0, 0, 487649782836, 1612298415955, 1262635063502, 206761233966, 5395128787, 0] := by
  rw [show D2M8K2.u15119 = KTree.node D2M8K2.u15117 (nat_lit 32957652) (nat_lit 2913512365) (nat_lit 0) D2M8K2.u15118 from rfl, totK_node, atot15117, atot15118]
  decide +kernel

theorem arows15123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15123 = true := by
  rw [show D2M8K2.u15123 = KTree.node D2M8K2.u15121 (nat_lit 32964576) (nat_lit 3567677278) (nat_lit 0) D2M8K2.u15122 from rfl, allE_node, arows15121, irow15123, arows15122]
  all_goals rfl

theorem atot15123 : totK PD2M8K2 D2M8K2.u15123 = [0, 0, 700267617366, 1872218166168, 949697980032, 60983794163, 0, 0] := by
  rw [show D2M8K2.u15123 = KTree.node D2M8K2.u15121 (nat_lit 32964576) (nat_lit 3567677278) (nat_lit 0) D2M8K2.u15122 from rfl, totK_node, atot15121, atot15122]
  decide +kernel

theorem arows15126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15126 = true := by
  rw [show D2M8K2.u15126 = KTree.node D2M8K2.u15124 (nat_lit 32971453) (nat_lit 1210781706) (nat_lit 0) D2M8K2.u15125 from rfl, allE_node, arows15124, irow15126, arows15125]
  all_goals rfl

theorem atot15126 : totK PD2M8K2 D2M8K2.u15126 = [0, 419158787481, 1489325431116, 1360570197373, 299230439355, 14936070864, 0, 0] := by
  rw [show D2M8K2.u15126 = KTree.node D2M8K2.u15124 (nat_lit 32971453) (nat_lit 1210781706) (nat_lit 0) D2M8K2.u15125 from rfl, totK_node, atot15124, atot15125]
  decide +kernel

theorem arows15132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15132 = true := by
  rw [show D2M8K2.u15132 = KTree.node D2M8K2.u15130 (nat_lit 32975344) (nat_lit 3422900050) (nat_lit 0) D2M8K2.u15131 from rfl, allE_node, arows15130, irow15132, arows15131]
  all_goals rfl

theorem atot15132 : totK PD2M8K2 D2M8K2.u15132 = [0, 363749830908, 1313081283558, 1474009085976, 494916706057, 32096557826, 0, 0] := by
  rw [show D2M8K2.u15132 = KTree.node D2M8K2.u15130 (nat_lit 32975344) (nat_lit 3422900050) (nat_lit 0) D2M8K2.u15131 from rfl, totK_node, atot15130, atot15131]
  decide +kernel

theorem arows15135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15135 = true := by
  rw [show D2M8K2.u15135 = KTree.node D2M8K2.u15133 (nat_lit 32982133) (nat_lit 1244190151) (nat_lit 0) D2M8K2.u15134 from rfl, allE_node, arows15133, irow15135, arows15134]
  all_goals rfl

theorem atot15135 : totK PD2M8K2 D2M8K2.u15135 = [0, 405369694407, 1454380709023, 1409706543650, 323560977054, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15135 = KTree.node D2M8K2.u15133 (nat_lit 32982133) (nat_lit 1244190151) (nat_lit 0) D2M8K2.u15134 from rfl, totK_node, atot15133, atot15134]
  decide +kernel

theorem arows15139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15139 = true := by
  rw [show D2M8K2.u15139 = KTree.node D2M8K2.u15137 (nat_lit 32985297) (nat_lit 1864980272) (nat_lit 0) D2M8K2.u15138 from rfl, allE_node, arows15137, irow15139, arows15138]
  all_goals rfl

theorem atot15139 : totK PD2M8K2 D2M8K2.u15139 = [0, 464386049645, 1522221880050, 1354863783984, 235670864925, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15139 = KTree.node D2M8K2.u15137 (nat_lit 32985297) (nat_lit 1864980272) (nat_lit 0) D2M8K2.u15138 from rfl, totK_node, atot15137, atot15138]
  decide +kernel

theorem arows15142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15142 = true := by
  rw [show D2M8K2.u15142 = KTree.node D2M8K2.u15140 (nat_lit 32989226) (nat_lit 4070459218) (nat_lit 0) D2M8K2.u15141 from rfl, allE_node, arows15140, irow15142, arows15141]
  all_goals rfl

theorem atot15142 : totK PD2M8K2 D2M8K2.u15142 = [0, 331445521867, 1359339504385, 1519078461617, 405472333454, 13467081304, 0, 0] := by
  rw [show D2M8K2.u15142 = KTree.node D2M8K2.u15140 (nat_lit 32989226) (nat_lit 4070459218) (nat_lit 0) D2M8K2.u15141 from rfl, totK_node, atot15140, atot15141]
  decide +kernel

theorem arows15147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15147 = true := by
  rw [show D2M8K2.u15147 = KTree.node D2M8K2.u15145 (nat_lit 32992501) (nat_lit 1248354771) (nat_lit 0) D2M8K2.u15146 from rfl, allE_node, arows15145, irow15147, arows15146]
  all_goals rfl

theorem atot15147 : totK PD2M8K2 D2M8K2.u15147 = [0, 0, 506740296834, 1677374621307, 1209789836110, 140881895931, 1239866073, 0] := by
  rw [show D2M8K2.u15147 = KTree.node D2M8K2.u15145 (nat_lit 32992501) (nat_lit 1248354771) (nat_lit 0) D2M8K2.u15146 from rfl, totK_node, atot15145, atot15146]
  decide +kernel

theorem arows15150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15150 = true := by
  rw [show D2M8K2.u15150 = KTree.node D2M8K2.u15148 (nat_lit 33001718) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u15149 from rfl, allE_node, arows15148, irow15150, arows15149]
  all_goals rfl

theorem atot15150 : totK PD2M8K2 D2M8K2.u15150 = [0, 0, 677196745494, 1824121437254, 1035503157401, 78115907312, 0, 0] := by
  rw [show D2M8K2.u15150 = KTree.node D2M8K2.u15148 (nat_lit 33001718) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u15149 from rfl, totK_node, atot15148, atot15149]
  decide +kernel

theorem arows15154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15154 = true := by
  rw [show D2M8K2.u15154 = KTree.node D2M8K2.u15152 (nat_lit 33005310) (nat_lit 4004509611) (nat_lit 0) D2M8K2.u15153 from rfl, allE_node, arows15152, irow15154, arows15153]
  all_goals rfl

theorem atot15154 : totK PD2M8K2 D2M8K2.u15154 = [0, 0, 543465398672, 1657334565175, 1159789776686, 191675092474, 5425831197, 0] := by
  rw [show D2M8K2.u15154 = KTree.node D2M8K2.u15152 (nat_lit 33005310) (nat_lit 4004509611) (nat_lit 0) D2M8K2.u15153 from rfl, totK_node, atot15152, atot15153]
  decide +kernel

theorem arows15157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15157 = true := by
  rw [show D2M8K2.u15157 = KTree.node D2M8K2.u15155 (nat_lit 33011936) (nat_lit 3632077801) (nat_lit 0) D2M8K2.u15156 from rfl, allE_node, arows15155, irow15157, arows15156]
  all_goals rfl

theorem atot15157 : totK PD2M8K2 D2M8K2.u15157 = [0, 420637493945, 1349459748622, 1294550107509, 510168951015, 38630842457, 0, 0] := by
  rw [show D2M8K2.u15157 = KTree.node D2M8K2.u15155 (nat_lit 33011936) (nat_lit 3632077801) (nat_lit 0) D2M8K2.u15156 from rfl, totK_node, atot15155, atot15156]
  decide +kernel

theorem arows15164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15164 = true := by
  rw [show D2M8K2.u15164 = KTree.node D2M8K2.u15162 (nat_lit 33019084) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u15163 from rfl, allE_node, arows15162, irow15164, arows15163]
  all_goals rfl

theorem atot15164 : totK PD2M8K2 D2M8K2.u15164 = [0, 400134420517, 1509460638435, 1443630503636, 235103150594, 2533470052, 0, 0] := by
  rw [show D2M8K2.u15164 = KTree.node D2M8K2.u15162 (nat_lit 33019084) (nat_lit 3862111635) (nat_lit 0) D2M8K2.u15163 from rfl, totK_node, atot15162, atot15163]
  decide +kernel

theorem arows15167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15167 = true := by
  rw [show D2M8K2.u15167 = KTree.node D2M8K2.u15165 (nat_lit 33022593) (nat_lit 1812249422) (nat_lit 0) D2M8K2.u15166 from rfl, allE_node, arows15165, irow15167, arows15166]
  all_goals rfl

theorem atot15167 : totK PD2M8K2 D2M8K2.u15167 = [0, 400370480135, 1440028107878, 1428104362424, 305700946042, 13083481006, 0, 0] := by
  rw [show D2M8K2.u15167 = KTree.node D2M8K2.u15165 (nat_lit 33022593) (nat_lit 1812249422) (nat_lit 0) D2M8K2.u15166 from rfl, totK_node, atot15165, atot15166]
  decide +kernel

theorem arows15171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15171 = true := by
  rw [show D2M8K2.u15171 = KTree.node D2M8K2.u15169 (nat_lit 33026047) (nat_lit 2412280812) (nat_lit 0) D2M8K2.u15170 from rfl, allE_node, arows15169, irow15171, arows15170]
  all_goals rfl

theorem atot15171 : totK PD2M8K2 D2M8K2.u15171 = [0, 423568743631, 1466325668568, 1384848307811, 297520942055, 13149116973, 0, 0] := by
  rw [show D2M8K2.u15171 = KTree.node D2M8K2.u15169 (nat_lit 33026047) (nat_lit 2412280812) (nat_lit 0) D2M8K2.u15170 from rfl, totK_node, atot15169, atot15170]
  decide +kernel

theorem arows15174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15174 = true := by
  rw [show D2M8K2.u15174 = KTree.node D2M8K2.u15172 (nat_lit 33033278) (nat_lit 1848586682) (nat_lit 8) D2M8K2.u15173 from rfl, allE_node, arows15172, irow15174, arows15173]
  all_goals rfl

theorem atot15174 : totK PD2M8K2 D2M8K2.u15174 = [0, 0, 722010076055, 1808562609372, 881199795229, 91067027500, 1138244013, 0] := by
  rw [show D2M8K2.u15174 = KTree.node D2M8K2.u15172 (nat_lit 33033278) (nat_lit 1848586682) (nat_lit 8) D2M8K2.u15173 from rfl, totK_node, atot15172, atot15173]
  decide +kernel

theorem arows15179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15179 = true := by
  rw [show D2M8K2.u15179 = KTree.node D2M8K2.u15177 (nat_lit 33040576) (nat_lit 3746028621) (nat_lit 0) D2M8K2.u15178 from rfl, allE_node, arows15177, irow15179, arows15178]
  all_goals rfl

theorem atot15179 : totK PD2M8K2 D2M8K2.u15179 = [0, 0, 660194249641, 1864840321721, 969688658528, 58318132645, 0, 0] := by
  rw [show D2M8K2.u15179 = KTree.node D2M8K2.u15177 (nat_lit 33040576) (nat_lit 3746028621) (nat_lit 0) D2M8K2.u15178 from rfl, totK_node, atot15177, atot15178]
  decide +kernel

theorem arows15182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15182 = true := by
  rw [show D2M8K2.u15182 = KTree.node D2M8K2.u15180 (nat_lit 33047091) (nat_lit 2548329097) (nat_lit 0) D2M8K2.u15181 from rfl, allE_node, arows15180, irow15182, arows15181]
  all_goals rfl

theorem atot15182 : totK PD2M8K2 D2M8K2.u15182 = [0, 194625098643, 1029439441710, 1648910083969, 651752063326, 30989853071, 0, 0] := by
  rw [show D2M8K2.u15182 = KTree.node D2M8K2.u15180 (nat_lit 33047091) (nat_lit 2548329097) (nat_lit 0) D2M8K2.u15181 from rfl, totK_node, atot15180, atot15181]
  decide +kernel

theorem arows15186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15186 = true := by
  rw [show D2M8K2.u15186 = KTree.node D2M8K2.u15184 (nat_lit 33055621) (nat_lit 1273806737) (nat_lit 0) D2M8K2.u15185 from rfl, allE_node, arows15184, irow15186, arows15185]
  all_goals rfl

theorem atot15186 : totK PD2M8K2 D2M8K2.u15186 = [0, 485552303365, 1600497495715, 1365138773321, 193281402150, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15186 = KTree.node D2M8K2.u15184 (nat_lit 33055621) (nat_lit 1273806737) (nat_lit 0) D2M8K2.u15185 from rfl, totK_node, atot15184, atot15185]
  decide +kernel

theorem arows15189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15189 = true := by
  rw [show D2M8K2.u15189 = KTree.node D2M8K2.u15187 (nat_lit 33059450) (nat_lit 4046771069) (nat_lit 0) D2M8K2.u15188 from rfl, allE_node, arows15187, irow15189, arows15188]
  all_goals rfl

theorem atot15189 : totK PD2M8K2 D2M8K2.u15189 = [0, 347851527001, 1321752719601, 1457998572109, 508051934970, 31347031438, 0, 0] := by
  rw [show D2M8K2.u15189 = KTree.node D2M8K2.u15187 (nat_lit 33059450) (nat_lit 4046771069) (nat_lit 0) D2M8K2.u15188 from rfl, totK_node, atot15187, atot15188]
  decide +kernel

theorem arows15195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15195 = true := by
  rw [show D2M8K2.u15195 = KTree.node D2M8K2.u15193 (nat_lit 33062664) (nat_lit 3255026254) (nat_lit 0) D2M8K2.u15194 from rfl, allE_node, arows15193, irow15195, arows15194]
  all_goals rfl

theorem atot15195 : totK PD2M8K2 D2M8K2.u15195 = [0, 412939941895, 1459568242275, 1427675115541, 304913816232, 8812418916, 0, 0] := by
  rw [show D2M8K2.u15195 = KTree.node D2M8K2.u15193 (nat_lit 33062664) (nat_lit 3255026254) (nat_lit 0) D2M8K2.u15194 from rfl, totK_node, atot15193, atot15194]
  decide +kernel

theorem arows15198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15198 = true := by
  rw [show D2M8K2.u15198 = KTree.node D2M8K2.u15196 (nat_lit 33066386) (nat_lit 3507470642) (nat_lit 0) D2M8K2.u15197 from rfl, allE_node, arows15196, irow15198, arows15197]
  all_goals rfl

theorem atot15198 : totK PD2M8K2 D2M8K2.u15198 = [0, 416354623010, 1466418572472, 1424379704092, 311673694482, 8913432303, 0, 0] := by
  rw [show D2M8K2.u15198 = KTree.node D2M8K2.u15196 (nat_lit 33066386) (nat_lit 3507470642) (nat_lit 0) D2M8K2.u15197 from rfl, totK_node, atot15196, atot15197]
  decide +kernel

theorem arows15202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15202 = true := by
  rw [show D2M8K2.u15202 = KTree.node D2M8K2.u15200 (nat_lit 33072884) (nat_lit 2674274761) (nat_lit 0) D2M8K2.u15201 from rfl, allE_node, arows15200, irow15202, arows15201]
  all_goals rfl

theorem atot15202 : totK PD2M8K2 D2M8K2.u15202 = [0, 181674658392, 1114759558656, 1717756820188, 567176190603, 24569785200, 0, 0] := by
  rw [show D2M8K2.u15202 = KTree.node D2M8K2.u15200 (nat_lit 33072884) (nat_lit 2674274761) (nat_lit 0) D2M8K2.u15201 from rfl, totK_node, atot15200, atot15201]
  decide +kernel

theorem arows15205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15205 = true := by
  rw [show D2M8K2.u15205 = KTree.node D2M8K2.u15203 (nat_lit 33076284) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u15204 from rfl, allE_node, arows15203, irow15205, arows15204]
  all_goals rfl

theorem atot15205 : totK PD2M8K2 D2M8K2.u15205 = [0, 0, 479679678128, 1621875527630, 1331320865956, 155089426182, 1310285577, 0] := by
  rw [show D2M8K2.u15205 = KTree.node D2M8K2.u15203 (nat_lit 33076284) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u15204 from rfl, totK_node, atot15203, atot15204]
  decide +kernel

theorem arows15210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15210 = true := by
  rw [show D2M8K2.u15210 = KTree.node D2M8K2.u15208 (nat_lit 33081562) (nat_lit 3787012671) (nat_lit 0) D2M8K2.u15209 from rfl, allE_node, arows15208, irow15210, arows15209]
  all_goals rfl

theorem atot15210 : totK PD2M8K2 D2M8K2.u15210 = [0, 0, 522558686229, 1660197691943, 1249152281182, 163250501033, 2125526286, 0] := by
  rw [show D2M8K2.u15210 = KTree.node D2M8K2.u15208 (nat_lit 33081562) (nat_lit 3787012671) (nat_lit 0) D2M8K2.u15209 from rfl, totK_node, atot15208, atot15209]
  decide +kernel

theorem arows15213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15213 = true := by
  rw [show D2M8K2.u15213 = KTree.node D2M8K2.u15211 (nat_lit 33085519) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15212 from rfl, allE_node, arows15211, irow15213, arows15212]
  all_goals rfl

theorem atot15213 : totK PD2M8K2 D2M8K2.u15213 = [0, 0, 411389922482, 1550034154898, 1357148784373, 225652779299, 7685718752, 0] := by
  rw [show D2M8K2.u15213 = KTree.node D2M8K2.u15211 (nat_lit 33085519) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15212 from rfl, totK_node, atot15211, atot15212]
  decide +kernel

theorem arows15217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15217 = true := by
  rw [show D2M8K2.u15217 = KTree.node D2M8K2.u15215 (nat_lit 33092307) (nat_lit 2390885288) (nat_lit 0) D2M8K2.u15216 from rfl, allE_node, arows15215, irow15217, arows15216]
  all_goals rfl

theorem atot15217 : totK PD2M8K2 D2M8K2.u15217 = [0, 0, 440901618055, 1521991202875, 1367941773915, 262200936710, 5842784248, 0] := by
  rw [show D2M8K2.u15217 = KTree.node D2M8K2.u15215 (nat_lit 33092307) (nat_lit 2390885288) (nat_lit 0) D2M8K2.u15216 from rfl, totK_node, atot15215, atot15216]
  decide +kernel

theorem arows15220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15220 = true := by
  rw [show D2M8K2.u15220 = KTree.node D2M8K2.u15218 (nat_lit 33095772) (nat_lit 2814470669) (nat_lit 0) D2M8K2.u15219 from rfl, allE_node, arows15218, irow15220, arows15219]
  all_goals rfl

theorem atot15220 : totK PD2M8K2 D2M8K2.u15220 = [0, 0, 441506629438, 1498436380085, 1332318278853, 309399603184, 17277534250, 0] := by
  rw [show D2M8K2.u15220 = KTree.node D2M8K2.u15218 (nat_lit 33095772) (nat_lit 2814470669) (nat_lit 0) D2M8K2.u15219 from rfl, totK_node, atot15218, atot15219]
  decide +kernel

end QECKChecks.D2M8K2
