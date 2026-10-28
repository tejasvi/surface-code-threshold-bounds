import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A26

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows9340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9340 = true := by
  rw [show D2M8K2.u9340 = KTree.node D2M8K2.u9276 (nat_lit 20063167) (nat_lit 2440169442) (nat_lit 0) D2M8K2.u9339 from rfl, allE_node, arows9276, irow9340, arows9339]
  all_goals rfl

theorem atot9340 : totK PD2M8K2 D2M8K2.u9340 = [5790880190801, 29056011016736, 48016079984554, 27597682561610, 4130925172376, 117493365220, 0, 0] := by
  rw [show D2M8K2.u9340 = KTree.node D2M8K2.u9276 (nat_lit 20063167) (nat_lit 2440169442) (nat_lit 0) D2M8K2.u9339 from rfl, totK_node, atot9276, atot9339]
  decide +kernel

theorem arows9467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9467 = true := by
  rw [show D2M8K2.u9467 = KTree.node D2M8K2.u9403 (nat_lit 20322511) (nat_lit 2421511515) (nat_lit 0) D2M8K2.u9466 from rfl, allE_node, arows9403, irow9467, arows9466]
  all_goals rfl

theorem atot9467 : totK PD2M8K2 D2M8K2.u9467 = [2124144177298, 17066314251656, 43503020511144, 40290831694513, 10965781344213, 744948058248, 7324389265, 0] := by
  rw [show D2M8K2.u9467 = KTree.node D2M8K2.u9403 (nat_lit 20322511) (nat_lit 2421511515) (nat_lit 0) D2M8K2.u9466 from rfl, totK_node, atot9403, atot9466]
  decide +kernel

theorem arows9595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9595 = true := by
  rw [show D2M8K2.u9595 = KTree.node D2M8K2.u9531 (nat_lit 20517129) (nat_lit 1786811280) (nat_lit 0) D2M8K2.u9594 from rfl, allE_node, arows9531, irow9595, arows9594]
  all_goals rfl

theorem atot9595 : totK PD2M8K2 D2M8K2.u9595 = [7667864117489, 33680331234168, 47605368988026, 23352265517609, 3235901438474, 92617011592, 0, 0] := by
  rw [show D2M8K2.u9595 = KTree.node D2M8K2.u9531 (nat_lit 20517129) (nat_lit 1786811280) (nat_lit 0) D2M8K2.u9594 from rfl, totK_node, atot9531, atot9594]
  decide +kernel

theorem arows9722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9722 = true := by
  rw [show D2M8K2.u9722 = KTree.node D2M8K2.u9658 (nat_lit 20714977) (nat_lit 1538890929) (nat_lit 0) D2M8K2.u9721 from rfl, allE_node, arows9658, irow9722, arows9721]
  all_goals rfl

theorem atot9722 : totK PD2M8K2 D2M8K2.u9722 = [0, 9704954429801, 39690796540853, 47834860935226, 16226392664856, 1177402445588, 14034558254, 0] := by
  rw [show D2M8K2.u9722 = KTree.node D2M8K2.u9658 (nat_lit 20714977) (nat_lit 1538890929) (nat_lit 0) D2M8K2.u9721 from rfl, totK_node, atot9658, atot9721]
  decide +kernel

theorem arows9851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9851 = true := by
  rw [show D2M8K2.u9851 = KTree.node D2M8K2.u9787 (nat_lit 20936838) (nat_lit 3762746587) (nat_lit 0) D2M8K2.u9850 from rfl, allE_node, arows9787, irow9851, arows9850]
  all_goals rfl

theorem atot9851 : totK PD2M8K2 D2M8K2.u9851 = [0, 7476609797394, 34328639159058, 48980207707080, 21257302840814, 2300495481360, 54306508133, 0] := by
  rw [show D2M8K2.u9851 = KTree.node D2M8K2.u9787 (nat_lit 20936838) (nat_lit 3762746587) (nat_lit 0) D2M8K2.u9850 from rfl, totK_node, atot9787, atot9850]
  decide +kernel

theorem arows9978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9978 = true := by
  rw [show D2M8K2.u9978 = KTree.node D2M8K2.u9914 (nat_lit 21143554) (nat_lit 4060457115) (nat_lit 0) D2M8K2.u9977 from rfl, allE_node, arows9914, irow9978, arows9977]
  all_goals rfl

theorem atot9978 : totK PD2M8K2 D2M8K2.u9978 = [0, 3966979634810, 23949563072745, 47610437600287, 32951416793443, 5867176922617, 266062417517, 1369150432] := by
  rw [show D2M8K2.u9978 = KTree.node D2M8K2.u9914 (nat_lit 21143554) (nat_lit 4060457115) (nat_lit 0) D2M8K2.u9977 from rfl, totK_node, atot9914, atot9977]
  decide +kernel

theorem arows10106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10106 = true := by
  rw [show D2M8K2.u10106 = KTree.node D2M8K2.u10042 (nat_lit 21471245) (nat_lit 1906733758) (nat_lit 0) D2M8K2.u10105 from rfl, allE_node, arows10042, irow10106, arows10105]
  all_goals rfl

theorem atot10106 : totK PD2M8K2 D2M8K2.u10106 = [0, 5822524121155, 28876996936147, 48086800882713, 28524446377976, 4297842433105, 122621561903, 0] := by
  rw [show D2M8K2.u10106 = KTree.node D2M8K2.u10042 (nat_lit 21471245) (nat_lit 1906733758) (nat_lit 0) D2M8K2.u10105 from rfl, totK_node, atot10042, atot10105]
  decide +kernel

theorem arows10233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10233 = true := by
  rw [show D2M8K2.u10233 = KTree.node D2M8K2.u10169 (nat_lit 21627769) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u10232 from rfl, allE_node, arows10169, irow10233, arows10232]
  all_goals rfl

theorem atot10233 : totK PD2M8K2 D2M8K2.u10233 = [0, 7703030402801, 34814147473683, 48950000067440, 21484367370997, 2321330170863, 49933511991, 0] := by
  rw [show D2M8K2.u10233 = KTree.node D2M8K2.u10169 (nat_lit 21627769) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u10232 from rfl, totK_node, atot10169, atot10232]
  decide +kernel

theorem arows10364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10364 = true := by
  rw [show D2M8K2.u10364 = KTree.node D2M8K2.u10300 (nat_lit 22564686) (nat_lit 3869943219) (nat_lit 0) D2M8K2.u10363 from rfl, allE_node, arows10300, irow10364, arows10363]
  all_goals rfl

theorem atot10364 : totK PD2M8K2 D2M8K2.u10364 = [0, 6486059206525, 31357980497685, 48898853438034, 25320328676786, 3219665304257, 77525284008, 0] := by
  rw [show D2M8K2.u10364 = KTree.node D2M8K2.u10300 (nat_lit 22564686) (nat_lit 3869943219) (nat_lit 0) D2M8K2.u10363 from rfl, totK_node, atot10300, atot10363]
  decide +kernel

theorem arows10491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10491 = true := by
  rw [show D2M8K2.u10491 = KTree.node D2M8K2.u10427 (nat_lit 22784862) (nat_lit 3841478617) (nat_lit 0) D2M8K2.u10490 from rfl, allE_node, arows10427, irow10491, arows10490]
  all_goals rfl

theorem atot10491 : totK PD2M8K2 D2M8K2.u10491 = [0, 0, 9895759370605, 40266772949628, 47190868660662, 15532366585819, 1367534472837, 26316908414] := by
  rw [show D2M8K2.u10491 = KTree.node D2M8K2.u10427 (nat_lit 22784862) (nat_lit 3841478617) (nat_lit 0) D2M8K2.u10490 from rfl, totK_node, atot10427, atot10490]
  decide +kernel

theorem arows10619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10619 = true := by
  rw [show D2M8K2.u10619 = KTree.node D2M8K2.u10555 (nat_lit 22968223) (nat_lit 2376490998) (nat_lit 0) D2M8K2.u10618 from rfl, allE_node, arows10555, irow10619, arows10618]
  all_goals rfl

theorem atot10619 : totK PD2M8K2 D2M8K2.u10619 = [0, 7660580561124, 34584902256335, 48745637135946, 21728880432326, 2505006697803, 57645725651, 0] := by
  rw [show D2M8K2.u10619 = KTree.node D2M8K2.u10555 (nat_lit 22968223) (nat_lit 2376490998) (nat_lit 0) D2M8K2.u10618 from rfl, totK_node, atot10555, atot10618]
  decide +kernel

theorem arows10746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10746 = true := by
  rw [show D2M8K2.u10746 = KTree.node D2M8K2.u10682 (nat_lit 23176334) (nat_lit 3775170987) (nat_lit 0) D2M8K2.u10745 from rfl, allE_node, arows10682, irow10746, arows10745]
  all_goals rfl

theorem atot10746 : totK PD2M8K2 D2M8K2.u10746 = [0, 2102355608136, 19334346144493, 48148304155699, 37776395489975, 6971467838010, 265739985991, 1209030869] := by
  rw [show D2M8K2.u10746 = KTree.node D2M8K2.u10682 (nat_lit 23176334) (nat_lit 3775170987) (nat_lit 0) D2M8K2.u10745 from rfl, totK_node, atot10682, atot10745]
  decide +kernel

theorem arows10875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10875 = true := by
  rw [show D2M8K2.u10875 = KTree.node D2M8K2.u10811 (nat_lit 23449502) (nat_lit 3825812487) (nat_lit 0) D2M8K2.u10874 from rfl, allE_node, arows10811, irow10875, arows10874]
  all_goals rfl

theorem atot10875 : totK PD2M8K2 D2M8K2.u10875 = [0, 7089033540328, 31063433060646, 45462188875564, 25717634290488, 5513538078959, 388105001843, 6115358396] := by
  rw [show D2M8K2.u10875 = KTree.node D2M8K2.u10811 (nat_lit 23449502) (nat_lit 3825812487) (nat_lit 0) D2M8K2.u10874 from rfl, totK_node, atot10811, atot10874]
  decide +kernel

theorem arows11002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11002 = true := by
  rw [show D2M8K2.u11002 = KTree.node D2M8K2.u10938 (nat_lit 23890237) (nat_lit 1220250907) (nat_lit 0) D2M8K2.u11001 from rfl, allE_node, arows10938, irow11002, arows11001]
  all_goals rfl

theorem atot11002 : totK PD2M8K2 D2M8K2.u11002 = [4079684246657, 21096759366901, 39490468459898, 33997532778424, 14090026506023, 1840533459535, 51938633597, 0] := by
  rw [show D2M8K2.u11002 = KTree.node D2M8K2.u10938 (nat_lit 23890237) (nat_lit 1220250907) (nat_lit 0) D2M8K2.u11001 from rfl, totK_node, atot10938, atot11001]
  decide +kernel

theorem arows11130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11130 = true := by
  rw [show D2M8K2.u11130 = KTree.node D2M8K2.u11066 (nat_lit 24085406) (nat_lit 3638093454) (nat_lit 0) D2M8K2.u11129 from rfl, allE_node, arows11066, irow11130, arows11129]
  all_goals rfl

theorem atot11130 : totK PD2M8K2 D2M8K2.u11130 = [5665805863142, 27993861115466, 46482954521443, 28560336382749, 5415932353270, 308523599799, 1369150432, 0] := by
  rw [show D2M8K2.u11130 = KTree.node D2M8K2.u11066 (nat_lit 24085406) (nat_lit 3638093454) (nat_lit 0) D2M8K2.u11129 from rfl, totK_node, atot11066, atot11129]
  decide +kernel

theorem arows11257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11257 = true := by
  rw [show D2M8K2.u11257 = KTree.node D2M8K2.u11193 (nat_lit 24345942) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u11256 from rfl, allE_node, arows11193, irow11257, arows11256]
  all_goals rfl

theorem atot11257 : totK PD2M8K2 D2M8K2.u11257 = [3204512227035, 20748731151413, 46124022073262, 37449566520387, 7544276789049, 259082290045, 0, 0] := by
  rw [show D2M8K2.u11257 = KTree.node D2M8K2.u11193 (nat_lit 24345942) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u11256 from rfl, totK_node, atot11193, atot11256]
  decide +kernel

theorem arows11387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11387 = true := by
  rw [show D2M8K2.u11387 = KTree.node D2M8K2.u11323 (nat_lit 24555352) (nat_lit 3674325927) (nat_lit 0) D2M8K2.u11386 from rfl, allE_node, arows11323, irow11387, arows11386]
  all_goals rfl

theorem atot11387 : totK PD2M8K2 D2M8K2.u11387 = [6599946206114, 32002224207518, 49098881535243, 24470542469216, 3051005222221, 75540765224, 0, 0] := by
  rw [show D2M8K2.u11387 = KTree.node D2M8K2.u11323 (nat_lit 24555352) (nat_lit 3674325927) (nat_lit 0) D2M8K2.u11386 from rfl, totK_node, atot11323, atot11386]
  decide +kernel

theorem arows11514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11514 = true := by
  rw [show D2M8K2.u11514 = KTree.node D2M8K2.u11450 (nat_lit 24746357) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u11513 from rfl, allE_node, arows11450, irow11514, arows11513]
  all_goals rfl

theorem atot11514 : totK PD2M8K2 D2M8K2.u11514 = [0, 7692379089869, 34500369224888, 48186333782965, 21878792481071, 2670345052159, 70818570093, 0] := by
  rw [show D2M8K2.u11514 = KTree.node D2M8K2.u11450 (nat_lit 24746357) (nat_lit 2221120622) (nat_lit 0) D2M8K2.u11513 from rfl, totK_node, atot11450, atot11513]
  decide +kernel

theorem arows11642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11642 = true := by
  rw [show D2M8K2.u11642 = KTree.node D2M8K2.u11578 (nat_lit 24912552) (nat_lit 3424920724) (nat_lit 0) D2M8K2.u11641 from rfl, allE_node, arows11578, irow11642, arows11641]
  all_goals rfl

theorem atot11642 : totK PD2M8K2 D2M8K2.u11642 = [6028330417152, 26655125064811, 41582340070169, 29830393214228, 10229506378752, 978277970273, 13619666203, 0] := by
  rw [show D2M8K2.u11642 = KTree.node D2M8K2.u11578 (nat_lit 24912552) (nat_lit 3424920724) (nat_lit 0) D2M8K2.u11641 from rfl, totK_node, atot11578, atot11641]
  decide +kernel

theorem arows11769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11769 = true := by
  rw [show D2M8K2.u11769 = KTree.node D2M8K2.u11705 (nat_lit 25100658) (nat_lit 2895136433) (nat_lit 0) D2M8K2.u11768 from rfl, allE_node, arows11705, irow11769, arows11768]
  all_goals rfl

theorem atot11769 : totK PD2M8K2 D2M8K2.u11769 = [3746527156219, 23161422703080, 46815539345829, 33683296073874, 6929682560647, 320863913909, 1275377855, 0] := by
  rw [show D2M8K2.u11769 = KTree.node D2M8K2.u11705 (nat_lit 25100658) (nat_lit 2895136433) (nat_lit 0) D2M8K2.u11768 from rfl, totK_node, atot11705, atot11768]
  decide +kernel

theorem arows11898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11898 = true := by
  rw [show D2M8K2.u11898 = KTree.node D2M8K2.u11834 (nat_lit 25325968) (nat_lit 3408622960) (nat_lit 0) D2M8K2.u11897 from rfl, allE_node, arows11834, irow11898, arows11897]
  all_goals rfl

theorem atot11898 : totK PD2M8K2 D2M8K2.u11898 = [3073895952514, 18571130103144, 41206879264068, 38055540808951, 12345817244259, 1142615123630, 24680175954, 0] := by
  rw [show D2M8K2.u11898 = KTree.node D2M8K2.u11834 (nat_lit 25325968) (nat_lit 3408622960) (nat_lit 0) D2M8K2.u11897 from rfl, totK_node, atot11834, atot11897]
  decide +kernel

theorem arows12025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12025 = true := by
  rw [show D2M8K2.u12025 = KTree.node D2M8K2.u11961 (nat_lit 25542726) (nat_lit 3663581055) (nat_lit 0) D2M8K2.u12024 from rfl, allE_node, arows11961, irow12025, arows12024]
  all_goals rfl

theorem atot12025 : totK PD2M8K2 D2M8K2.u12025 = [6702266648599, 31854689616697, 48421881725222, 24814081501653, 3386655854261, 89441111478, 0, 0] := by
  rw [show D2M8K2.u12025 = KTree.node D2M8K2.u11961 (nat_lit 25542726) (nat_lit 3663581055) (nat_lit 0) D2M8K2.u12024 from rfl, totK_node, atot11961, atot12024]
  decide +kernel

theorem arows12153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12153 = true := by
  rw [show D2M8K2.u12153 = KTree.node D2M8K2.u12089 (nat_lit 25767169) (nat_lit 1449219382) (nat_lit 0) D2M8K2.u12152 from rfl, allE_node, arows12089, irow12153, arows12152]
  all_goals rfl

theorem atot12153 : totK PD2M8K2 D2M8K2.u12153 = [0, 9057676534882, 38493666705481, 48268129159457, 16941561222651, 1430711240771, 26316908414, 0] := by
  rw [show D2M8K2.u12153 = KTree.node D2M8K2.u12089 (nat_lit 25767169) (nat_lit 1449219382) (nat_lit 0) D2M8K2.u12152 from rfl, totK_node, atot12089, atot12152]
  decide +kernel

theorem arows12280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12280 = true := by
  rw [show D2M8K2.u12280 = KTree.node D2M8K2.u12216 (nat_lit 25946633) (nat_lit 1542151248) (nat_lit 0) D2M8K2.u12279 from rfl, allE_node, arows12216, irow12280, arows12279]
  all_goals rfl

theorem atot12280 : totK PD2M8K2 D2M8K2.u12280 = [7310598303305, 32813857407279, 47425986052606, 23850551128068, 3619898365044, 118969117359, 0, 0] := by
  rw [show D2M8K2.u12280 = KTree.node D2M8K2.u12216 (nat_lit 25946633) (nat_lit 1542151248) (nat_lit 0) D2M8K2.u12279 from rfl, totK_node, atot12216, atot12279]
  decide +kernel

theorem arows12412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12412 = true := by
  rw [show D2M8K2.u12412 = KTree.node D2M8K2.u12348 (nat_lit 26135928) (nat_lit 3337081392) (nat_lit 0) D2M8K2.u12411 from rfl, allE_node, arows12348, irow12412, arows12411]
  all_goals rfl

theorem atot12412 : totK PD2M8K2 D2M8K2.u12412 = [2880687651292, 20839912152128, 46927394700898, 36355440647543, 7540781874420, 334607999800, 1209030869, 0] := by
  rw [show D2M8K2.u12412 = KTree.node D2M8K2.u12348 (nat_lit 26135928) (nat_lit 3337081392) (nat_lit 0) D2M8K2.u12411 from rfl, totK_node, atot12348, atot12411]
  decide +kernel

theorem arows12539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12539 = true := by
  rw [show D2M8K2.u12539 = KTree.node D2M8K2.u12475 (nat_lit 26888406) (nat_lit 2648274116) (nat_lit 0) D2M8K2.u12538 from rfl, allE_node, arows12475, irow12539, arows12538]
  all_goals rfl

theorem atot12539 : totK PD2M8K2 D2M8K2.u12539 = [0, 8993844252530, 38183421117075, 48427154529529, 17330707477757, 1514713072600, 26281567636, 0] := by
  rw [show D2M8K2.u12539 = KTree.node D2M8K2.u12475 (nat_lit 26888406) (nat_lit 2648274116) (nat_lit 0) D2M8K2.u12538 from rfl, totK_node, atot12475, atot12538]
  decide +kernel

theorem arows12667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12667 = true := by
  rw [show D2M8K2.u12667 = KTree.node D2M8K2.u12603 (nat_lit 27090283) (nat_lit 1065189961) (nat_lit 0) D2M8K2.u12666 from rfl, allE_node, arows12603, irow12667, arows12666]
  all_goals rfl

theorem atot12667 : totK PD2M8K2 D2M8K2.u12667 = [0, 4477984716750, 26021614253864, 48273375413282, 29967831779835, 5108459427878, 240779108065, 1369150432] := by
  rw [show D2M8K2.u12667 = KTree.node D2M8K2.u12603 (nat_lit 27090283) (nat_lit 1065189961) (nat_lit 0) D2M8K2.u12666 from rfl, totK_node, atot12603, atot12666]
  decide +kernel

theorem arows12794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12794 = true := by
  rw [show D2M8K2.u12794 = KTree.node D2M8K2.u12730 (nat_lit 27433708) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u12793 from rfl, allE_node, arows12730, irow12794, arows12793]
  all_goals rfl

theorem atot12794 : totK PD2M8K2 D2M8K2.u12794 = [0, 5303085958430, 28057629819518, 48520208016048, 28902734012015, 4369423188749, 130362375966, 0] := by
  rw [show D2M8K2.u12794 = KTree.node D2M8K2.u12730 (nat_lit 27433708) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u12793 from rfl, totK_node, atot12730, atot12793]
  decide +kernel

theorem arows12923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12923 = true := by
  rw [show D2M8K2.u12923 = KTree.node D2M8K2.u12859 (nat_lit 27588676) (nat_lit 3715339663) (nat_lit 0) D2M8K2.u12922 from rfl, allE_node, arows12859, irow12923, arows12922]
  all_goals rfl

theorem atot12923 : totK PD2M8K2 D2M8K2.u12923 = [0, 7679677351800, 35035992484450, 49398379960248, 20966708633257, 2093806004490, 37349168698, 0] := by
  rw [show D2M8K2.u12923 = KTree.node D2M8K2.u12859 (nat_lit 27588676) (nat_lit 3715339663) (nat_lit 0) D2M8K2.u12922 from rfl, totK_node, atot12859, atot12922]
  decide +kernel

theorem arows13050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13050 = true := by
  rw [show D2M8K2.u13050 = KTree.node D2M8K2.u12986 (nat_lit 28037024) (nat_lit 3298492019) (nat_lit 0) D2M8K2.u13049 from rfl, allE_node, arows12986, irow13050, arows13049]
  all_goals rfl

theorem atot13050 : totK PD2M8K2 D2M8K2.u13050 = [0, 7253817315811, 33498809594327, 48907025596993, 22784943889811, 2600028878572, 52766663144, 0] := by
  rw [show D2M8K2.u13050 = KTree.node D2M8K2.u12986 (nat_lit 28037024) (nat_lit 3298492019) (nat_lit 0) D2M8K2.u13049 from rfl, totK_node, atot12986, atot13049]
  decide +kernel

theorem arows13178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13178 = true := by
  rw [show D2M8K2.u13178 = KTree.node D2M8K2.u13114 (nat_lit 28493048) (nat_lit 3564687317) (nat_lit 0) D2M8K2.u13177 from rfl, allE_node, arows13114, irow13178, arows13177]
  all_goals rfl

theorem atot13178 : totK PD2M8K2 D2M8K2.u13178 = [0, 7460967312844, 34452066384682, 49304474096401, 21591655804714, 2265423739560, 43385059181, 0] := by
  rw [show D2M8K2.u13178 = KTree.node D2M8K2.u13114 (nat_lit 28493048) (nat_lit 3564687317) (nat_lit 0) D2M8K2.u13177 from rfl, totK_node, atot13114, atot13177]
  decide +kernel

theorem arows13305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13305 = true := by
  rw [show D2M8K2.u13305 = KTree.node D2M8K2.u13241 (nat_lit 28910060) (nat_lit 3712679515) (nat_lit 0) D2M8K2.u13304 from rfl, allE_node, arows13241, irow13305, arows13304]
  all_goals rfl

theorem atot13305 : totK PD2M8K2 D2M8K2.u13305 = [0, 7704369475572, 34590806530554, 48707030576099, 21611916403999, 2347653423157, 49315384803, 0] := by
  rw [show D2M8K2.u13305 = KTree.node D2M8K2.u13241 (nat_lit 28910060) (nat_lit 3712679515) (nat_lit 0) D2M8K2.u13304 from rfl, totK_node, atot13241, atot13304]
  decide +kernel

theorem arows13435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13435 = true := by
  rw [show D2M8K2.u13435 = KTree.node D2M8K2.u13371 (nat_lit 29051273) (nat_lit 1556148319) (nat_lit 0) D2M8K2.u13434 from rfl, allE_node, arows13371, irow13435, arows13434]
  all_goals rfl

theorem atot13435 : totK PD2M8K2 D2M8K2.u13435 = [0, 4145233399486, 24385457937024, 47576042350620, 32073434929599, 5896774063905, 285826085983, 1209030869] := by
  rw [show D2M8K2.u13435 = KTree.node D2M8K2.u13371 (nat_lit 29051273) (nat_lit 1556148319) (nat_lit 0) D2M8K2.u13434 from rfl, totK_node, atot13371, atot13434]
  decide +kernel

theorem arows13562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13562 = true := by
  rw [show D2M8K2.u13562 = KTree.node D2M8K2.u13498 (nat_lit 29860709) (nat_lit 2065902022) (nat_lit 0) D2M8K2.u13561 from rfl, allE_node, arows13498, irow13562, arows13561]
  all_goals rfl

theorem atot13562 : totK PD2M8K2 D2M8K2.u13562 = [4080737729171, 18135969369773, 30201011973003, 31058600818244, 23559904108279, 6710160738949, 529618835960, 6115358396] := by
  rw [show D2M8K2.u13562 = KTree.node D2M8K2.u13498 (nat_lit 29860709) (nat_lit 2065902022) (nat_lit 0) D2M8K2.u13561 from rfl, totK_node, atot13498, atot13561]
  decide +kernel

theorem arows13690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13690 = true := by
  rw [show D2M8K2.u13690 = KTree.node D2M8K2.u13626 (nat_lit 30062180) (nat_lit 2697562718) (nat_lit 0) D2M8K2.u13689 from rfl, allE_node, arows13626, irow13690, arows13689]
  all_goals rfl

theorem atot13690 : totK PD2M8K2 D2M8K2.u13690 = [5667819174842, 28289837838791, 46948401845615, 28311669358687, 5105462755270, 282671769191, 1369150432, 0] := by
  rw [show D2M8K2.u13690 = KTree.node D2M8K2.u13626 (nat_lit 30062180) (nat_lit 2697562718) (nat_lit 0) D2M8K2.u13689 from rfl, totK_node, atot13626, atot13689]
  decide +kernel

theorem arows13817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13817 = true := by
  rw [show D2M8K2.u13817 = KTree.node D2M8K2.u13753 (nat_lit 30319292) (nat_lit 2469767352) (nat_lit 0) D2M8K2.u13816 from rfl, allE_node, arows13753, irow13817, arows13816]
  all_goals rfl

theorem atot13817 : totK PD2M8K2 D2M8K2.u13817 = [2872115542185, 19803787006691, 45760136988922, 38476527679365, 8122358167327, 296652982477, 0, 0] := by
  rw [show D2M8K2.u13817 = KTree.node D2M8K2.u13753 (nat_lit 30319292) (nat_lit 2469767352) (nat_lit 0) D2M8K2.u13816 from rfl, totK_node, atot13753, atot13816]
  decide +kernel

theorem arows13946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13946 = true := by
  rw [show D2M8K2.u13946 = KTree.node D2M8K2.u13882 (nat_lit 30527527) (nat_lit 2020490091) (nat_lit 0) D2M8K2.u13945 from rfl, allE_node, arows13882, irow13946, arows13945]
  all_goals rfl

theorem atot13946 : totK PD2M8K2 D2M8K2.u13946 = [6938597777729, 32541270803460, 48921494716034, 24085748922375, 2904341995847, 62386065978, 0, 0] := by
  rw [show D2M8K2.u13946 = KTree.node D2M8K2.u13882 (nat_lit 30527527) (nat_lit 2020490091) (nat_lit 0) D2M8K2.u13945 from rfl, totK_node, atot13882, atot13945]
  decide +kernel

theorem arows14073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14073 = true := by
  rw [show D2M8K2.u14073 = KTree.node D2M8K2.u14009 (nat_lit 30714629) (nat_lit 2265354362) (nat_lit 0) D2M8K2.u14072 from rfl, allE_node, arows14009, irow14073, arows14072]
  all_goals rfl

theorem atot14073 : totK PD2M8K2 D2M8K2.u14073 = [0, 7763593833256, 34485147083418, 48014472501959, 22095368328887, 2709641951959, 70818570093, 0] := by
  rw [show D2M8K2.u14073 = KTree.node D2M8K2.u14009 (nat_lit 30714629) (nat_lit 2265354362) (nat_lit 0) D2M8K2.u14072 from rfl, totK_node, atot14009, atot14072]
  decide +kernel

theorem arows14201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14201 = true := by
  rw [show D2M8K2.u14201 = KTree.node D2M8K2.u14137 (nat_lit 30882954) (nat_lit 3427018085) (nat_lit 0) D2M8K2.u14200 from rfl, allE_node, arows14137, irow14201, arows14200]
  all_goals rfl

theorem atot14201 : totK PD2M8K2 D2M8K2.u14201 = [5667682438987, 26135353886000, 42315191706774, 30346122701563, 9954888212027, 950723470913, 13619666203, 0] := by
  rw [show D2M8K2.u14201 = KTree.node D2M8K2.u14137 (nat_lit 30882954) (nat_lit 3427018085) (nat_lit 0) D2M8K2.u14200 from rfl, totK_node, atot14137, atot14200]
  decide +kernel

theorem arows14328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14328 = true := by
  rw [show D2M8K2.u14328 = KTree.node D2M8K2.u14264 (nat_lit 31079821) (nat_lit 1391339689) (nat_lit 0) D2M8K2.u14327 from rfl, allE_node, arows14264, irow14328, arows14327]
  all_goals rfl

theorem atot14328 : totK PD2M8K2 D2M8K2.u14328 = [4107182670197, 23735627651154, 46385366772884, 33350978527357, 6938311608253, 321914602408, 1275377855, 0] := by
  rw [show D2M8K2.u14328 = KTree.node D2M8K2.u14264 (nat_lit 31079821) (nat_lit 1391339689) (nat_lit 0) D2M8K2.u14327 from rfl, totK_node, atot14264, atot14327]
  decide +kernel

theorem arows14459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14459 = true := by
  rw [show D2M8K2.u14459 = KTree.node D2M8K2.u14395 (nat_lit 31298048) (nat_lit 3598993038) (nat_lit 0) D2M8K2.u14458 from rfl, allE_node, arows14395, irow14459, arows14458]
  all_goals rfl

theorem atot14459 : totK PD2M8K2 D2M8K2.u14459 = [2751054189156, 18105969734565, 41594306803922, 38541559597148, 12391827664028, 1142021291951, 24680175954, 0] := by
  rw [show D2M8K2.u14459 = KTree.node D2M8K2.u14395 (nat_lit 31298048) (nat_lit 3598993038) (nat_lit 0) D2M8K2.u14458 from rfl, totK_node, atot14395, atot14458]
  decide +kernel

theorem arows14586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14586 = true := by
  rw [show D2M8K2.u14586 = KTree.node D2M8K2.u14522 (nat_lit 31512678) (nat_lit 3848496419) (nat_lit 0) D2M8K2.u14585 from rfl, allE_node, arows14522, irow14586, arows14585]
  all_goals rfl

theorem atot14586 : totK PD2M8K2 D2M8K2.u14586 = [7028793326967, 32399385196871, 48097981656271, 24430873038299, 3362475875733, 89389547224, 0, 0] := by
  rw [show D2M8K2.u14586 = KTree.node D2M8K2.u14522 (nat_lit 31512678) (nat_lit 3848496419) (nat_lit 0) D2M8K2.u14585 from rfl, totK_node, atot14522, atot14585]
  decide +kernel

theorem arows14714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14714 = true := by
  rw [show D2M8K2.u14714 = KTree.node D2M8K2.u14650 (nat_lit 31732931) (nat_lit 2761992659) (nat_lit 0) D2M8K2.u14713 from rfl, allE_node, arows14650, irow14714, arows14713]
  all_goals rfl

theorem atot14714 : totK PD2M8K2 D2M8K2.u14714 = [0, 9286247491574, 38818810268973, 47980747682381, 16793177875875, 1428192943447, 26316908414, 0] := by
  rw [show D2M8K2.u14714 = KTree.node D2M8K2.u14650 (nat_lit 31732931) (nat_lit 2761992659) (nat_lit 0) D2M8K2.u14713 from rfl, totK_node, atot14650, atot14713]
  decide +kernel

theorem arows14841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14841 = true := by
  rw [show D2M8K2.u14841 = KTree.node D2M8K2.u14777 (nat_lit 32414814) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u14840 from rfl, allE_node, arows14777, irow14841, arows14840]
  all_goals rfl

theorem atot14841 : totK PD2M8K2 D2M8K2.u14841 = [7323068860337, 32528028168267, 47233854651610, 24420703308145, 3758841665329, 118522958999, 0, 0] := by
  rw [show D2M8K2.u14841 = KTree.node D2M8K2.u14777 (nat_lit 32414814) (nat_lit 3951079944) (nat_lit 0) D2M8K2.u14840 from rfl, totK_node, atot14777, atot14840]
  decide +kernel

theorem arows14970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14970 = true := by
  rw [show D2M8K2.u14970 = KTree.node D2M8K2.u14906 (nat_lit 32596838) (nat_lit 3925278030) (nat_lit 0) D2M8K2.u14969 from rfl, allE_node, arows14906, irow14970, arows14969]
  all_goals rfl

theorem atot14970 : totK PD2M8K2 D2M8K2.u14970 = [2889725044371, 20313474234475, 45592740325355, 37095853314447, 8721412155408, 406817157531, 1369150432, 0] := by
  rw [show D2M8K2.u14970 = KTree.node D2M8K2.u14906 (nat_lit 32596838) (nat_lit 3925278030) (nat_lit 0) D2M8K2.u14969 from rfl, totK_node, atot14906, atot14969]
  decide +kernel

theorem arows15097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15097 = true := by
  rw [show D2M8K2.u15097 = KTree.node D2M8K2.u15033 (nat_lit 32814183) (nat_lit 2435255461) (nat_lit 0) D2M8K2.u15096 from rfl, allE_node, arows15033, irow15097, arows15096]
  all_goals rfl

theorem atot15097 : totK PD2M8K2 D2M8K2.u15097 = [0, 7502993972980, 34716459403577, 49088219657590, 20757051893772, 2141171666703, 46699515257, 0] := by
  rw [show D2M8K2.u15097 = KTree.node D2M8K2.u15033 (nat_lit 32814183) (nat_lit 2435255461) (nat_lit 0) D2M8K2.u15096 from rfl, totK_node, atot15033, atot15096]
  decide +kernel

theorem arows15225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15225 = true := by
  rw [show D2M8K2.u15225 = KTree.node D2M8K2.u15161 (nat_lit 33013496) (nat_lit 3640468847) (nat_lit 0) D2M8K2.u15224 from rfl, allE_node, arows15161, irow15225, arows15224]
  all_goals rfl

theorem atot15225 : totK PD2M8K2 D2M8K2.u15225 = [0, 7065473843057, 33425247997499, 49505343738632, 22614943872928, 2419268269247, 48647384965, 0] := by
  rw [show D2M8K2.u15225 = KTree.node D2M8K2.u15161 (nat_lit 33013496) (nat_lit 3640468847) (nat_lit 0) D2M8K2.u15224 from rfl, totK_node, atot15161, atot15224]
  decide +kernel

theorem arows15352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15352 = true := by
  rw [show D2M8K2.u15352 = KTree.node D2M8K2.u15288 (nat_lit 33261265) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u15351 from rfl, allE_node, arows15288, irow15352, arows15351]
  all_goals rfl

theorem atot15352 : totK PD2M8K2 D2M8K2.u15352 = [0, 2117768858604, 17943321789426, 46376707871721, 40471454833793, 8083005285228, 357461072340, 1369150432] := by
  rw [show D2M8K2.u15352 = KTree.node D2M8K2.u15288 (nat_lit 33261265) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u15351 from rfl, totK_node, atot15288, atot15351]
  decide +kernel

theorem arows15482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15482 = true := by
  rw [show D2M8K2.u15482 = KTree.node D2M8K2.u15418 (nat_lit 33488484) (nat_lit 3265186967) (nat_lit 0) D2M8K2.u15481 from rfl, allE_node, arows15418, irow15482, arows15481]
  all_goals rfl

theorem atot15482 : totK PD2M8K2 D2M8K2.u15482 = [0, 7692944461310, 34345358945717, 48647339782581, 22546712302806, 2527020741824, 41577055297, 0] := by
  rw [show D2M8K2.u15482 = KTree.node D2M8K2.u15418 (nat_lit 33488484) (nat_lit 3265186967) (nat_lit 0) D2M8K2.u15481 from rfl, totK_node, atot15418, atot15481]
  decide +kernel

theorem arows15609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15609 = true := by
  rw [show D2M8K2.u15609 = KTree.node D2M8K2.u15545 (nat_lit 33901550) (nat_lit 2609194944) (nat_lit 0) D2M8K2.u15608 from rfl, allE_node, arows15545, irow15609, arows15608]
  all_goals rfl

theorem atot15609 : totK PD2M8K2 D2M8K2.u15609 = [0, 6886883735494, 31924936986389, 47978985704604, 24816662465836, 3552467470877, 103489207152, 0] := by
  rw [show D2M8K2.u15609 = KTree.node D2M8K2.u15545 (nat_lit 33901550) (nat_lit 2609194944) (nat_lit 0) D2M8K2.u15608 from rfl, totK_node, atot15545, atot15608]
  decide +kernel

theorem arows15737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15737 = true := by
  rw [show D2M8K2.u15737 = KTree.node D2M8K2.u15673 (nat_lit 34098308) (nat_lit 3609898978) (nat_lit 0) D2M8K2.u15736 from rfl, allE_node, arows15673, irow15737, arows15736]
  all_goals rfl

theorem atot15737 : totK PD2M8K2 D2M8K2.u15737 = [0, 2891661737698, 20325205905480, 46102404114642, 37089329482855, 8270977522914, 403268735789, 2481843637] := by
  rw [show D2M8K2.u15737 = KTree.node D2M8K2.u15673 (nat_lit 34098308) (nat_lit 3609898978) (nat_lit 0) D2M8K2.u15736 from rfl, totK_node, atot15673, atot15736]
  decide +kernel

theorem arows15864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15864 = true := by
  rw [show D2M8K2.u15864 = KTree.node D2M8K2.u15800 (nat_lit 34373476) (nat_lit 3745620599) (nat_lit 0) D2M8K2.u15863 from rfl, allE_node, arows15800, irow15864, arows15863]
  all_goals rfl

theorem atot15864 : totK PD2M8K2 D2M8K2.u15864 = [0, 6085337998138, 29364989984053, 46935863728047, 27514773862700, 5264582367928, 330112300278, 5395128787] := by
  rw [show D2M8K2.u15864 = KTree.node D2M8K2.u15800 (nat_lit 34373476) (nat_lit 3745620599) (nat_lit 0) D2M8K2.u15863 from rfl, totK_node, atot15800, atot15863]
  decide +kernel

theorem arows15993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15993 = true := by
  rw [show D2M8K2.u15993 = KTree.node D2M8K2.u15929 (nat_lit 34567763) (nat_lit 2933783805) (nat_lit 0) D2M8K2.u15992 from rfl, allE_node, arows15929, irow15993, arows15992]
  all_goals rfl

theorem atot15993 : totK PD2M8K2 D2M8K2.u15993 = [0, 3694509517985, 23386937789381, 47789899365777, 33731997580489, 6264474695811, 246364475153, 1310517177] := by
  rw [show D2M8K2.u15993 = KTree.node D2M8K2.u15929 (nat_lit 34567763) (nat_lit 2933783805) (nat_lit 0) D2M8K2.u15992 from rfl, totK_node, atot15929, atot15992]
  decide +kernel

theorem arows16120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16120 = true := by
  rw [show D2M8K2.u16120 = KTree.node D2M8K2.u16056 (nat_lit 35342767) (nat_lit 2070755573) (nat_lit 0) D2M8K2.u16119 from rfl, allE_node, arows16056, irow16120, arows16119]
  all_goals rfl

theorem atot16120 : totK PD2M8K2 D2M8K2.u16120 = [0, 4038872482053, 23550179749975, 46033961993656, 33476060349762, 7791069244232, 498487279767, 6643327963] := by
  rw [show D2M8K2.u16120 = KTree.node D2M8K2.u16056 (nat_lit 35342767) (nat_lit 2070755573) (nat_lit 0) D2M8K2.u16119 from rfl, totK_node, atot16056, atot16119]
  decide +kernel

theorem arows16248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16248 = true := by
  rw [show D2M8K2.u16248 = KTree.node D2M8K2.u16184 (nat_lit 35492336) (nat_lit 3747592774) (nat_lit 0) D2M8K2.u16247 from rfl, allE_node, arows16184, irow16248, arows16247]
  all_goals rfl

theorem atot16248 : totK PD2M8K2 D2M8K2.u16248 = [0, 6173921422655, 30115355904820, 48424858516828, 26778413483549, 3633997651811, 97897266262, 0] := by
  rw [show D2M8K2.u16248 = KTree.node D2M8K2.u16184 (nat_lit 35492336) (nat_lit 3747592774) (nat_lit 0) D2M8K2.u16247 from rfl, totK_node, atot16184, atot16247]
  decide +kernel

theorem arows16375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16375 = true := by
  rw [show D2M8K2.u16375 = KTree.node D2M8K2.u16311 (nat_lit 35711759) (nat_lit 2143130451) (nat_lit 0) D2M8K2.u16374 from rfl, allE_node, arows16311, irow16375, arows16374]
  all_goals rfl

theorem atot16375 : totK PD2M8K2 D2M8K2.u16375 = [0, 0, 8184697330568, 36366960209461, 48613044825537, 19414874086321, 2000227626721, 46699515257] := by
  rw [show D2M8K2.u16375 = KTree.node D2M8K2.u16311 (nat_lit 35711759) (nat_lit 2143130451) (nat_lit 0) D2M8K2.u16374 from rfl, totK_node, atot16311, atot16374]
  decide +kernel

theorem arows254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u254 = true := by
  rw [show D2M8K2.u254 = KTree.node D2M8K2.u126 (nat_lit 191060) (nat_lit 3657281242) (nat_lit 0) D2M8K2.u253 from rfl, allE_node, arows126, irow254, arows253]
  all_goals rfl

theorem atot254 : totK PD2M8K2 D2M8K2.u254 = [10180875791748, 53670718132189, 94375487784409, 59958610571042, 10762379638120, 477990857973, 1369150432, 0] := by
  rw [show D2M8K2.u254 = KTree.node D2M8K2.u126 (nat_lit 191060) (nat_lit 3657281242) (nat_lit 0) D2M8K2.u253 from rfl, totK_node, atot126, atot253]
  decide +kernel

theorem arows509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u509 = true := by
  rw [show D2M8K2.u509 = KTree.node D2M8K2.u381 (nat_lit 1117170) (nat_lit 3148330649) (nat_lit 0) D2M8K2.u508 from rfl, allE_node, arows381, irow509, arows508]
  all_goals rfl

theorem atot509 : totK PD2M8K2 D2M8K2.u509 = [9774186910825, 52192686935970, 93821303366142, 61902977321832, 11826718360738, 480242329425, 1275377855, 0] := by
  rw [show D2M8K2.u509 = KTree.node D2M8K2.u381 (nat_lit 1117170) (nat_lit 3148330649) (nat_lit 0) D2M8K2.u508 from rfl, totK_node, atot381, atot508]
  decide +kernel

theorem arows765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u765 = true := by
  rw [show D2M8K2.u765 = KTree.node D2M8K2.u637 (nat_lit 1561562) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u764 from rfl, allE_node, arows637, irow765, arows764]
  all_goals rfl

theorem atot765 : totK PD2M8K2 D2M8K2.u765 = [9775486533803, 50473879806105, 89763079966920, 62731110150804, 15496199805033, 1216910909291, 24680175954, 0] := by
  rw [show D2M8K2.u765 = KTree.node D2M8K2.u637 (nat_lit 1561562) (nat_lit 4241602830) (nat_lit 0) D2M8K2.u764 from rfl, totK_node, atot637, atot764]
  decide +kernel

theorem arows1020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1020 = true := by
  rw [show D2M8K2.u1020 = KTree.node D2M8K2.u892 (nat_lit 1993064) (nat_lit 3860982447) (nat_lit 0) D2M8K2.u1019 from rfl, allE_node, arows892, irow1020, arows1019]
  all_goals rfl

theorem atot1020 : totK PD2M8K2 D2M8K2.u1020 = [7657849809243, 43064168678448, 86217318586102, 70658422731462, 20056220247306, 1530241061500, 26316908414, 0] := by
  rw [show D2M8K2.u1020 = KTree.node D2M8K2.u892 (nat_lit 1993064) (nat_lit 3860982447) (nat_lit 0) D2M8K2.u1019 from rfl, totK_node, atot892, atot1019]
  decide +kernel

theorem arows1277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1277 = true := by
  rw [show D2M8K2.u1277 = KTree.node D2M8K2.u1149 (nat_lit 2411456) (nat_lit 3731499917) (nat_lit 0) D2M8K2.u1276 from rfl, allE_node, arows1149, irow1277, arows1276]
  all_goals rfl

theorem atot1277 : totK PD2M8K2 D2M8K2.u1277 = [8035599402638, 46056288765121, 91027955333999, 68127201761994, 15435245722916, 890394704345, 7324389265, 0] := by
  rw [show D2M8K2.u1277 = KTree.node D2M8K2.u1149 (nat_lit 2411456) (nat_lit 3731499917) (nat_lit 0) D2M8K2.u1276 from rfl, totK_node, atot1149, atot1276]
  decide +kernel

theorem arows1532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1532 = true := by
  rw [show D2M8K2.u1532 = KTree.node D2M8K2.u1404 (nat_lit 2826410) (nat_lit 3988603594) (nat_lit 0) D2M8K2.u1531 from rfl, allE_node, arows1404, irow1532, arows1531]
  all_goals rfl

theorem atot1532 : totK PD2M8K2 D2M8K2.u1532 = [3856492171129, 30030718159581, 79762341221915, 83944560041317, 29005353981356, 2534387411518, 48068665689, 0] := by
  rw [show D2M8K2.u1532 = KTree.node D2M8K2.u1404 (nat_lit 2826410) (nat_lit 3988603594) (nat_lit 0) D2M8K2.u1531 from rfl, totK_node, atot1404, atot1531]
  decide +kernel

theorem arows1788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1788 = true := by
  rw [show D2M8K2.u1788 = KTree.node D2M8K2.u1660 (nat_lit 3218552) (nat_lit 2437563933) (nat_lit 0) D2M8K2.u1787 from rfl, allE_node, arows1660, irow1788, arows1787]
  all_goals rfl

theorem atot1788 : totK PD2M8K2 D2M8K2.u1788 = [0, 9691994989002, 52552423346697, 94774781162621, 59829515195774, 10557014316184, 516342103239, 1369150432] := by
  rw [show D2M8K2.u1788 = KTree.node D2M8K2.u1660 (nat_lit 3218552) (nat_lit 2437563933) (nat_lit 0) D2M8K2.u1787 from rfl, totK_node, atot1660, atot1787]
  decide +kernel

theorem arows2043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2043 = true := by
  rw [show D2M8K2.u2043 = KTree.node D2M8K2.u1915 (nat_lit 4200560) (nat_lit 2998696123) (nat_lit 0) D2M8K2.u2042 from rfl, allE_node, arows1915, irow2043, arows2042]
  all_goals rfl

theorem atot2043 : totK PD2M8K2 D2M8K2.u2043 = [0, 14971921044815, 68474605334622, 98214813402883, 43545956572353, 4397824668797, 79902298461, 0] := by
  rw [show D2M8K2.u2043 = KTree.node D2M8K2.u1915 (nat_lit 4200560) (nat_lit 2998696123) (nat_lit 0) D2M8K2.u2042 from rfl, totK_node, atot1915, atot2042]
  decide +kernel

theorem arows2301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2301 = true := by
  rw [show D2M8K2.u2301 = KTree.node D2M8K2.u2173 (nat_lit 5068338) (nat_lit 2747045833) (nat_lit 0) D2M8K2.u2300 from rfl, allE_node, arows2173, irow2301, arows2300]
  all_goals rfl

theorem atot2301 : totK PD2M8K2 D2M8K2.u2301 = [0, 15163457082368, 69476700364065, 98528137798171, 41918123360996, 4064401308850, 74341147577, 0] := by
  rw [show D2M8K2.u2301 = KTree.node D2M8K2.u2173 (nat_lit 5068338) (nat_lit 2747045833) (nat_lit 0) D2M8K2.u2300 from rfl, totK_node, atot2173, atot2300]
  decide +kernel

theorem arows2556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2556 = true := by
  rw [show D2M8K2.u2556 = KTree.node D2M8K2.u2428 (nat_lit 5716030) (nat_lit 3892354265) (nat_lit 0) D2M8K2.u2555 from rfl, allE_node, arows2428, irow2556, arows2555]
  all_goals rfl

theorem atot2556 : totK PD2M8K2 D2M8K2.u2556 = [7348351400121, 39484499321305, 79825952815476, 73601202571818, 27659298422356, 2863849774360, 58547776104, 0] := by
  rw [show D2M8K2.u2556 = KTree.node D2M8K2.u2428 (nat_lit 5716030) (nat_lit 3892354265) (nat_lit 0) D2M8K2.u2555 from rfl, totK_node, atot2428, atot2555]
  decide +kernel

theorem arows2812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2812 = true := by
  rw [show D2M8K2.u2812 = KTree.node D2M8K2.u2684 (nat_lit 6831388) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u2811 from rfl, allE_node, arows2684, irow2812, arows2811]
  all_goals rfl

theorem atot2812 : totK PD2M8K2 D2M8K2.u2812 = [4525618389806, 31343089613261, 77604720855661, 80726778363516, 32218052952236, 3634007417719, 84438236296, 0] := by
  rw [show D2M8K2.u2812 = KTree.node D2M8K2.u2684 (nat_lit 6831388) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u2811 from rfl, totK_node, atot2684, atot2811]
  decide +kernel

theorem arows3067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3067 = true := by
  rw [show D2M8K2.u3067 = KTree.node D2M8K2.u2939 (nat_lit 7186140) (nat_lit 2360979910) (nat_lit 0) D2M8K2.u3066 from rfl, allE_node, arows2939, irow3067, arows3066]
  all_goals rfl

theorem atot3067 : totK PD2M8K2 D2M8K2.u3067 = [8133655785380, 45620643239615, 89159114722615, 68445639330492, 17409328647172, 1250143617707, 21175891594, 0] := by
  rw [show D2M8K2.u3067 = KTree.node D2M8K2.u2939 (nat_lit 7186140) (nat_lit 2360979910) (nat_lit 0) D2M8K2.u3066 from rfl, totK_node, atot2939, atot3066]
  decide +kernel

theorem arows3324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3324 = true := by
  rw [show D2M8K2.u3324 = KTree.node D2M8K2.u3196 (nat_lit 7627501) (nat_lit 1129020837) (nat_lit 0) D2M8K2.u3323 from rfl, allE_node, arows3196, irow3324, arows3323]
  all_goals rfl

theorem atot3324 : totK PD2M8K2 D2M8K2.u3324 = [9782518764193, 51503951484357, 92099299059816, 62735355441903, 13586804596608, 712535752277, 6090179392, 0] := by
  rw [show D2M8K2.u3324 = KTree.node D2M8K2.u3196 (nat_lit 7627501) (nat_lit 1129020837) (nat_lit 0) D2M8K2.u3323 from rfl, totK_node, atot3196, atot3323]
  decide +kernel

theorem arows3579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3579 = true := by
  rw [show D2M8K2.u3579 = KTree.node D2M8K2.u3451 (nat_lit 8031901) (nat_lit 1205972667) (nat_lit 0) D2M8K2.u3578 from rfl, allE_node, arows3451, irow3579, arows3578]
  all_goals rfl

theorem atot3579 : totK PD2M8K2 D2M8K2.u3579 = [9766688187780, 50281001763039, 89378040134278, 62977307399004, 15903492944527, 1249279082464, 25006391237, 0] := by
  rw [show D2M8K2.u3579 = KTree.node D2M8K2.u3451 (nat_lit 8031901) (nat_lit 1205972667) (nat_lit 0) D2M8K2.u3578 from rfl, totK_node, atot3451, atot3578]
  decide +kernel

theorem arows3835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3835 = true := by
  rw [show D2M8K2.u3835 = KTree.node D2M8K2.u3707 (nat_lit 8488513) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u3834 from rfl, allE_node, arows3707, irow3835, arows3834]
  all_goals rfl

theorem atot3835 : totK PD2M8K2 D2M8K2.u3835 = [8930255257929, 48113733033101, 90552721279173, 66655911141329, 15312578657687, 892779419576, 7324389265, 0] := by
  rw [show D2M8K2.u3835 = KTree.node D2M8K2.u3707 (nat_lit 8488513) (nat_lit 1556661526) (nat_lit 0) D2M8K2.u3834 from rfl, totK_node, atot3707, atot3834]
  decide +kernel

theorem arows4090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4090 = true := by
  rw [show D2M8K2.u4090 = KTree.node D2M8K2.u3962 (nat_lit 8857523) (nat_lit 2808667942) (nat_lit 0) D2M8K2.u4089 from rfl, allE_node, arows3962, irow4090, arows4089]
  all_goals rfl

theorem atot4090 : totK PD2M8K2 D2M8K2.u4090 = [867070346516, 19765974151032, 73357954527380, 92621393503281, 38855666824302, 4518723705072, 116130170494, 0] := by
  rw [show D2M8K2.u4090 = KTree.node D2M8K2.u3962 (nat_lit 8857523) (nat_lit 2808667942) (nat_lit 0) D2M8K2.u4089 from rfl, totK_node, atot3962, atot4089]
  decide +kernel

theorem arows4349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4349 = true := by
  rw [show D2M8K2.u4349 = KTree.node D2M8K2.u4221 (nat_lit 9774202) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u4348 from rfl, allE_node, arows4221, irow4349, arows4348]
  all_goals rfl

theorem atot4349 : totK PD2M8K2 D2M8K2.u4349 = [0, 5499994119439, 36142041102752, 82685387597988, 76948291805668, 26719976907285, 2826173158500, 72248385929] := by
  rw [show D2M8K2.u4349 = KTree.node D2M8K2.u4221 (nat_lit 9774202) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u4348 from rfl, totK_node, atot4221, atot4348]
  decide +kernel

theorem arows4604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4604 = true := by
  rw [show D2M8K2.u4604 = KTree.node D2M8K2.u4476 (nat_lit 10128425) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u4603 from rfl, allE_node, arows4476, irow4604, arows4603]
  all_goals rfl

theorem atot4604 : totK PD2M8K2 D2M8K2.u4604 = [0, 9781205774498, 50792138828390, 90549207305825, 62566660230961, 15627472265043, 1223299041053, 19237966639] := by
  rw [show D2M8K2.u4604 = KTree.node D2M8K2.u4476 (nat_lit 10128425) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u4603 from rfl, totK_node, atot4476, atot4603]
  decide +kernel

theorem arows4860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4860 = true := by
  rw [show D2M8K2.u4860 = KTree.node D2M8K2.u4732 (nat_lit 10594429) (nat_lit 1193218578) (nat_lit 0) D2M8K2.u4859 from rfl, allE_node, arows4732, irow4860, arows4859]
  all_goals rfl

theorem atot4860 : totK PD2M8K2 D2M8K2.u4860 = [0, 9782518764193, 52809085802628, 94819601850534, 61525656511317, 11695769928369, 474581403645, 1394496256] := by
  rw [show D2M8K2.u4860 = KTree.node D2M8K2.u4732 (nat_lit 10594429) (nat_lit 1193218578) (nat_lit 0) D2M8K2.u4859 from rfl, totK_node, atot4732, atot4859]
  decide +kernel

theorem arows5115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5115 = true := by
  rw [show D2M8K2.u5115 = KTree.node D2M8K2.u4987 (nat_lit 11022667) (nat_lit 1790597141) (nat_lit 0) D2M8K2.u5114 from rfl, allE_node, arows4987, irow5115, arows5114]
  all_goals rfl

theorem atot5115 : totK PD2M8K2 D2M8K2.u5115 = [0, 9766688187780, 51150374657839, 91909673438085, 62728885142487, 13793706469795, 823055894133, 8535762846] := by
  rw [show D2M8K2.u5115 = KTree.node D2M8K2.u4987 (nat_lit 11022667) (nat_lit 1790597141) (nat_lit 0) D2M8K2.u5114 from rfl, totK_node, atot4987, atot5114]
  decide +kernel

theorem arows5372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5372 = true := by
  rw [show D2M8K2.u5372 = KTree.node D2M8K2.u5244 (nat_lit 11502164) (nat_lit 3162555651) (nat_lit 0) D2M8K2.u5371 from rfl, allE_node, arows5244, irow5372, arows5371]
  all_goals rfl

theorem atot5372 : totK PD2M8K2 D2M8K2.u5372 = [0, 9797325604445, 52123644322676, 94001556378989, 62718956537790, 12132568170568, 539464490362, 1493059870] := by
  rw [show D2M8K2.u5372 = KTree.node D2M8K2.u5244 (nat_lit 11502164) (nat_lit 3162555651) (nat_lit 0) D2M8K2.u5371 from rfl, totK_node, atot5244, atot5371]
  decide +kernel

theorem arows5627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5627 = true := by
  rw [show D2M8K2.u5627 = KTree.node D2M8K2.u5499 (nat_lit 11942792) (nat_lit 2883087598) (nat_lit 0) D2M8K2.u5626 from rfl, allE_node, arows5499, irow5627, arows5626]
  all_goals rfl

theorem atot5627 : totK PD2M8K2 D2M8K2.u5627 = [7757745427395, 34824274573060, 58529199750641, 61252614548660, 50061643091789, 16230875758469, 1254008283127, 16131274116] := by
  rw [show D2M8K2.u5627 = KTree.node D2M8K2.u5499 (nat_lit 11942792) (nat_lit 2883087598) (nat_lit 0) D2M8K2.u5626 from rfl, totK_node, atot5499, atot5626]
  decide +kernel

theorem arows5883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5883 = true := by
  rw [show D2M8K2.u5883 = KTree.node D2M8K2.u5755 (nat_lit 12401300) (nat_lit 3273101852) (nat_lit 0) D2M8K2.u5882 from rfl, allE_node, arows5755, irow5883, arows5882]
  all_goals rfl

theorem atot5883 : totK PD2M8K2 D2M8K2.u5883 = [8322207016486, 47359000195689, 92737567856162, 67654647891303, 13444410891255, 588251658597, 1369150432, 0] := by
  rw [show D2M8K2.u5883 = KTree.node D2M8K2.u5755 (nat_lit 12401300) (nat_lit 3273101852) (nat_lit 0) D2M8K2.u5882 from rfl, totK_node, atot5755, atot5882]
  decide +kernel

theorem arows6138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6138 = true := by
  rw [show D2M8K2.u6138 = KTree.node D2M8K2.u6010 (nat_lit 12794833) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u6137 from rfl, allE_node, arows6010, irow6138, arows6137]
  all_goals rfl

theorem atot6138 : totK PD2M8K2 D2M8K2.u6138 = [5477993298553, 33740544533643, 77253604587467, 78379524796300, 31739621395461, 3628876646345, 84438236296, 0] := by
  rw [show D2M8K2.u6138 = KTree.node D2M8K2.u6010 (nat_lit 12794833) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u6137 from rfl, totK_node, atot6010, atot6137]
  decide +kernel

theorem arows6396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6396 = true := by
  rw [show D2M8K2.u6396 = KTree.node D2M8K2.u6268 (nat_lit 13152520) (nat_lit 3833857520) (nat_lit 0) D2M8K2.u6395 from rfl, allE_node, arows6268, irow6396, arows6395]
  all_goals rfl

theorem atot6396 : totK PD2M8K2 D2M8K2.u6396 = [8195615458647, 46470482966124, 90494163438860, 67371367256868, 16279804613561, 1144545612468, 20072436663, 0] := by
  rw [show D2M8K2.u6396 = KTree.node D2M8K2.u6268 (nat_lit 13152520) (nat_lit 3833857520) (nat_lit 0) D2M8K2.u6395 from rfl, totK_node, atot6268, atot6395]
  decide +kernel

theorem arows6651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6651 = true := by
  rw [show D2M8K2.u6651 = KTree.node D2M8K2.u6523 (nat_lit 14036433) (nat_lit 1199115551) (nat_lit 0) D2M8K2.u6650 from rfl, allE_node, arows6523, irow6651, arows6650]
  all_goals rfl

theorem atot6651 : totK PD2M8K2 D2M8K2.u6651 = [9762656065877, 51035461434561, 91552202506209, 62757770367851, 13666938892145, 750938398298, 7092148015, 0] := by
  rw [show D2M8K2.u6651 = KTree.node D2M8K2.u6523 (nat_lit 14036433) (nat_lit 1199115551) (nat_lit 0) D2M8K2.u6650 from rfl, totK_node, atot6523, atot6650]
  decide +kernel

theorem arows6907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6907 = true := by
  rw [show D2M8K2.u6907 = KTree.node D2M8K2.u6779 (nat_lit 14502148) (nat_lit 4054154634) (nat_lit 0) D2M8K2.u6906 from rfl, allE_node, arows6779, irow6907, arows6906]
  all_goals rfl

theorem atot6907 : totK PD2M8K2 D2M8K2.u6907 = [9791754696174, 51693732902139, 92839952480957, 62485316178883, 12733553688410, 684297900691, 6115358396, 0] := by
  rw [show D2M8K2.u6907 = KTree.node D2M8K2.u6779 (nat_lit 14502148) (nat_lit 4054154634) (nat_lit 0) D2M8K2.u6906 from rfl, totK_node, atot6779, atot6906]
  decide +kernel

theorem arows7162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7162 = true := by
  rw [show D2M8K2.u7162 = KTree.node D2M8K2.u7034 (nat_lit 14917692) (nat_lit 3242775292) (nat_lit 0) D2M8K2.u7161 from rfl, allE_node, arows7034, irow7162, arows7161]
  all_goals rfl

theorem atot7162 : totK PD2M8K2 D2M8K2.u7162 = [0, 16299049385759, 72199270625595, 97793091558999, 38962267544478, 3618433524231, 69243834583, 0] := by
  rw [show D2M8K2.u7162 = KTree.node D2M8K2.u7034 (nat_lit 14917692) (nat_lit 3242775292) (nat_lit 0) D2M8K2.u7161 from rfl, totK_node, atot7034, atot7161]
  decide +kernel

theorem arows7419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7419 = true := by
  rw [show D2M8K2.u7419 = KTree.node D2M8K2.u7291 (nat_lit 15394855) (nat_lit 1951953504) (nat_lit 0) D2M8K2.u7418 from rfl, allE_node, arows7291, irow7419, arows7418]
  all_goals rfl

theorem atot7419 : totK PD2M8K2 D2M8K2.u7419 = [0, 9533131593803, 52358732543330, 95923254907305, 61719607898271, 10267313756948, 397028948209, 1369150432] := by
  rw [show D2M8K2.u7419 = KTree.node D2M8K2.u7291 (nat_lit 15394855) (nat_lit 1951953504) (nat_lit 0) D2M8K2.u7418 from rfl, totK_node, atot7291, atot7418]
  decide +kernel

theorem arows7674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7674 = true := by
  rw [show D2M8K2.u7674 = KTree.node D2M8K2.u7546 (nat_lit 16014217) (nat_lit 1284303548) (nat_lit 0) D2M8K2.u7673 from rfl, allE_node, arows7546, irow7674, arows7673]
  all_goals rfl

theorem atot7674 : totK PD2M8K2 D2M8K2.u7674 = [0, 12466220192153, 60703463255181, 96143764843509, 52218728611024, 8137097041756, 322569388171, 1275377855] := by
  rw [show D2M8K2.u7674 = KTree.node D2M8K2.u7546 (nat_lit 16014217) (nat_lit 1284303548) (nat_lit 0) D2M8K2.u7673 from rfl, totK_node, atot7546, atot7673]
  decide +kernel

theorem arows7930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7930 = true := by
  rw [show D2M8K2.u7930 = KTree.node D2M8K2.u7802 (nat_lit 16956086) (nat_lit 3858369850) (nat_lit 0) D2M8K2.u7929 from rfl, allE_node, arows7802, irow7930, arows7929]
  all_goals rfl

theorem atot7930 : totK PD2M8K2 D2M8K2.u7930 = [0, 9762656065877, 51398711500751, 91313457874028, 61315386515222, 14585042145319, 1190995016293, 24680175954] := by
  rw [show D2M8K2.u7930 = KTree.node D2M8K2.u7802 (nat_lit 16956086) (nat_lit 3858369850) (nat_lit 0) D2M8K2.u7929 from rfl, totK_node, atot7802, atot7929]
  decide +kernel

theorem arows8185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8185 = true := by
  rw [show D2M8K2.u8185 = KTree.node D2M8K2.u8057 (nat_lit 17437858) (nat_lit 3965402304) (nat_lit 0) D2M8K2.u8184 from rfl, allE_node, arows8057, irow8185, arows8184]
  all_goals rfl

theorem atot8185 : totK PD2M8K2 D2M8K2.u8185 = [0, 9111867490900, 50620054470392, 94199329276271, 63050991021296, 12242708844725, 637176726696, 7324389265] := by
  rw [show D2M8K2.u8185 = KTree.node D2M8K2.u8057 (nat_lit 17437858) (nat_lit 3965402304) (nat_lit 0) D2M8K2.u8184 from rfl, totK_node, atot8057, atot8184]
  decide +kernel

theorem arows8445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8445 = true := by
  rw [show D2M8K2.u8445 = KTree.node D2M8K2.u8317 (nat_lit 18085995) (nat_lit 3731856320) (nat_lit 0) D2M8K2.u8444 from rfl, allE_node, arows8317, irow8445, arows8444]
  all_goals rfl

theorem atot8445 : totK PD2M8K2 D2M8K2.u8445 = [9747010765452, 50348032555266, 89255390327337, 62213707301444, 15985522000629, 1477991409238, 34241849113, 0] := by
  rw [show D2M8K2.u8445 = KTree.node D2M8K2.u8317 (nat_lit 18085995) (nat_lit 3731856320) (nat_lit 0) D2M8K2.u8444 from rfl, totK_node, atot8317, atot8444]
  decide +kernel

theorem arows8700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8700 = true := by
  rw [show D2M8K2.u8700 = KTree.node D2M8K2.u8572 (nat_lit 18554539) (nat_lit 1562109062) (nat_lit 0) D2M8K2.u8699 from rfl, allE_node, arows8572, irow8700, arows8699]
  all_goals rfl

theorem atot8700 : totK PD2M8K2 D2M8K2.u8700 = [9809346359322, 51183212487518, 91034671482689, 62152931877190, 15173135554392, 1481299076607, 48508304344, 0] := by
  rw [show D2M8K2.u8700 = KTree.node D2M8K2.u8572 (nat_lit 18554539) (nat_lit 1562109062) (nat_lit 0) D2M8K2.u8699 from rfl, totK_node, atot8572, atot8699]
  decide +kernel

theorem arows8956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8956 = true := by
  rw [show D2M8K2.u8956 = KTree.node D2M8K2.u8828 (nat_lit 18908399) (nat_lit 2147319959) (nat_lit 0) D2M8K2.u8955 from rfl, allE_node, arows8828, irow8956, arows8955]
  all_goals rfl

theorem atot8956 : totK PD2M8K2 D2M8K2.u8956 = [7827715727631, 41529546491774, 81689634072056, 71585841325551, 25344399018275, 2413155348267, 35929931952, 0] := by
  rw [show D2M8K2.u8956 = KTree.node D2M8K2.u8828 (nat_lit 18908399) (nat_lit 2147319959) (nat_lit 0) D2M8K2.u8955 from rfl, totK_node, atot8828, atot8955]
  decide +kernel

theorem arows9211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9211 = true := by
  rw [show D2M8K2.u9211 = KTree.node D2M8K2.u9083 (nat_lit 19804739) (nat_lit 2880583681) (nat_lit 0) D2M8K2.u9210 from rfl, allE_node, arows9083, irow9211, arows9210]
  all_goals rfl

theorem atot9211 : totK PD2M8K2 D2M8K2.u9211 = [6346607621987, 40115488826224, 87046195490742, 73769806653959, 20642356891676, 1542575483442, 26316908414, 0] := by
  rw [show D2M8K2.u9211 = KTree.node D2M8K2.u9083 (nat_lit 19804739) (nat_lit 2880583681) (nat_lit 0) D2M8K2.u9210 from rfl, totK_node, atot9083, atot9210]
  decide +kernel

theorem arows9468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9468 = true := by
  rw [show D2M8K2.u9468 = KTree.node D2M8K2.u9340 (nat_lit 20177941) (nat_lit 1262771631) (nat_lit 0) D2M8K2.u9467 from rfl, allE_node, arows9340, irow9468, arows9467]
  all_goals rfl

theorem atot9468 : totK PD2M8K2 D2M8K2.u9468 = [7915024368099, 46122325268392, 91519100495698, 67888514256123, 15096706516589, 863704195099, 7324389265, 0] := by
  rw [show D2M8K2.u9468 = KTree.node D2M8K2.u9340 (nat_lit 20177941) (nat_lit 1262771631) (nat_lit 0) D2M8K2.u9467 from rfl, totK_node, atot9340, atot9467]
  decide +kernel

theorem arows9723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9723 = true := by
  rw [show D2M8K2.u9723 = KTree.node D2M8K2.u9595 (nat_lit 20636173) (nat_lit 520628060) (nat_lit 0) D2M8K2.u9722 from rfl, allE_node, arows9595, irow9723, arows9722]
  all_goals rfl

theorem atot9723 : totK PD2M8K2 D2M8K2.u9723 = [7667864117489, 43385285663969, 87296165528879, 71187647080895, 19462294103330, 1270019457180, 14034558254, 0] := by
  rw [show D2M8K2.u9723 = KTree.node D2M8K2.u9595 (nat_lit 20636173) (nat_lit 520628060) (nat_lit 0) D2M8K2.u9722 from rfl, totK_node, atot9595, atot9722]
  decide +kernel

theorem arows9979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9979 = true := by
  rw [show D2M8K2.u9979 = KTree.node D2M8K2.u9851 (nat_lit 21065190) (nat_lit 3859207955) (nat_lit 0) D2M8K2.u9978 from rfl, allE_node, arows9851, irow9979, arows9978]
  all_goals rfl

theorem atot9979 : totK PD2M8K2 D2M8K2.u9979 = [0, 11443589432204, 58282061439758, 96590645307367, 54208719634257, 8167672403977, 320368925650, 1369150432] := by
  rw [show D2M8K2.u9979 = KTree.node D2M8K2.u9851 (nat_lit 21065190) (nat_lit 3859207955) (nat_lit 0) D2M8K2.u9978 from rfl, totK_node, atot9851, atot9978]
  decide +kernel

theorem arows10234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10234 = true := by
  rw [show D2M8K2.u10234 = KTree.node D2M8K2.u10106 (nat_lit 21548636) (nat_lit 3581999532) (nat_lit 0) D2M8K2.u10233 from rfl, allE_node, arows10106, irow10234, arows10233]
  all_goals rfl

theorem atot10234 : totK PD2M8K2 D2M8K2.u10234 = [0, 13525554523956, 63691144409830, 97036800950153, 50012395748505, 6619172603968, 172555073894, 0] := by
  rw [show D2M8K2.u10234 = KTree.node D2M8K2.u10106 (nat_lit 21548636) (nat_lit 3581999532) (nat_lit 0) D2M8K2.u10233 from rfl, totK_node, atot10106, atot10233]
  decide +kernel

theorem arows10492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10492 = true := by
  rw [show D2M8K2.u10492 = KTree.node D2M8K2.u10364 (nat_lit 22642065) (nat_lit 1162450049) (nat_lit 0) D2M8K2.u10491 from rfl, allE_node, arows10364, irow10492, arows10491]
  all_goals rfl

theorem atot10492 : totK PD2M8K2 D2M8K2.u10492 = [0, 6486059206525, 41253739868290, 89165626387662, 72512359787497, 18752031890076, 1445059756845, 26316908414] := by
  rw [show D2M8K2.u10492 = KTree.node D2M8K2.u10364 (nat_lit 22642065) (nat_lit 1162450049) (nat_lit 0) D2M8K2.u10491 from rfl, totK_node, atot10364, atot10491]
  decide +kernel

theorem arows10747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10747 = true := by
  rw [show D2M8K2.u10747 = KTree.node D2M8K2.u10619 (nat_lit 23052206) (nat_lit 3650733318) (nat_lit 0) D2M8K2.u10746 from rfl, allE_node, arows10619, irow10747, arows10746]
  all_goals rfl

theorem atot10747 : totK PD2M8K2 D2M8K2.u10747 = [0, 9762936169260, 53919248400828, 96897592024963, 59505275922301, 9476474535813, 323385711642, 1209030869] := by
  rw [show D2M8K2.u10747 = KTree.node D2M8K2.u10619 (nat_lit 23052206) (nat_lit 3650733318) (nat_lit 0) D2M8K2.u10746 from rfl, totK_node, atot10619, atot10746]
  decide +kernel

theorem arows11003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11003 = true := by
  rw [show D2M8K2.u11003 = KTree.node D2M8K2.u10875 (nat_lit 23529322) (nat_lit 3591191713) (nat_lit 0) D2M8K2.u11002 from rfl, allE_node, arows10875, irow11003, arows11002]
  all_goals rfl

theorem atot11003 : totK PD2M8K2 D2M8K2.u11003 = [4079684246657, 28189384098942, 70553901520544, 79459721653988, 39807660796511, 7354071538494, 440043635440, 6115358396] := by
  rw [show D2M8K2.u11003 = KTree.node D2M8K2.u10875 (nat_lit 23529322) (nat_lit 3591191713) (nat_lit 0) D2M8K2.u11002 from rfl, totK_node, atot10875, atot11002]
  decide +kernel

theorem arows11258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11258 = true := by
  rw [show D2M8K2.u11258 = KTree.node D2M8K2.u11130 (nat_lit 24169022) (nat_lit 2012835306) (nat_lit 0) D2M8K2.u11257 from rfl, allE_node, arows11130, irow11258, arows11257]
  all_goals rfl

theorem atot11258 : totK PD2M8K2 D2M8K2.u11258 = [8870318090177, 48742592266879, 92606976594705, 66011915738442, 12960209142319, 567605889844, 1369150432, 0] := by
  rw [show D2M8K2.u11258 = KTree.node D2M8K2.u11130 (nat_lit 24169022) (nat_lit 2012835306) (nat_lit 0) D2M8K2.u11257 from rfl, totK_node, atot11130, atot11257]
  decide +kernel

theorem arows11515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11515 = true := by
  rw [show D2M8K2.u11515 = KTree.node D2M8K2.u11387 (nat_lit 24681358) (nat_lit 3962638447) (nat_lit 0) D2M8K2.u11514 from rfl, allE_node, arows11387, irow11515, arows11514]
  all_goals rfl

theorem atot11515 : totK PD2M8K2 D2M8K2.u11515 = [6599946206114, 39694603297387, 83599250760131, 72660838890628, 24929797703292, 2745885817383, 70818570093, 0] := by
  rw [show D2M8K2.u11515 = KTree.node D2M8K2.u11387 (nat_lit 24681358) (nat_lit 3962638447) (nat_lit 0) D2M8K2.u11514 from rfl, totK_node, atot11387, atot11514]
  decide +kernel

theorem arows11770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11770 = true := by
  rw [show D2M8K2.u11770 = KTree.node D2M8K2.u11642 (nat_lit 24984903) (nat_lit 3621839421) (nat_lit 0) D2M8K2.u11769 from rfl, allE_node, arows11642, irow11770, arows11769]
  all_goals rfl

theorem atot11770 : totK PD2M8K2 D2M8K2.u11770 = [9774857573371, 49816547767891, 88401501255419, 63513689288102, 17159188939399, 1299141884182, 14895044058, 0] := by
  rw [show D2M8K2.u11770 = KTree.node D2M8K2.u11642 (nat_lit 24984903) (nat_lit 3621839421) (nat_lit 0) D2M8K2.u11769 from rfl, totK_node, atot11642, atot11769]
  decide +kernel

theorem arows12026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12026 = true := by
  rw [show D2M8K2.u12026 = KTree.node D2M8K2.u11898 (nat_lit 25433953) (nat_lit 1455147382) (nat_lit 0) D2M8K2.u12025 from rfl, allE_node, arows11898, irow12026, arows12025]
  all_goals rfl

theorem atot12026 : totK PD2M8K2 D2M8K2.u12026 = [9776162601113, 50427274867223, 89628760989290, 62869622310604, 15732473098520, 1232056235108, 24680175954, 0] := by
  rw [show D2M8K2.u12026 = KTree.node D2M8K2.u11898 (nat_lit 25433953) (nat_lit 1455147382) (nat_lit 0) D2M8K2.u12025 from rfl, totK_node, atot11898, atot12025]
  decide +kernel

theorem arows12281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12281 = true := by
  rw [show D2M8K2.u12281 = KTree.node D2M8K2.u12153 (nat_lit 25843894) (nat_lit 3390271686) (nat_lit 0) D2M8K2.u12280 from rfl, allE_node, arows12153, irow12281, arows12280]
  all_goals rfl

theorem atot12281 : totK PD2M8K2 D2M8K2.u12281 = [7310598303305, 41871533942161, 85919652758087, 72118680287525, 20564849859381, 1549680358130, 26316908414, 0] := by
  rw [show D2M8K2.u12281 = KTree.node D2M8K2.u12153 (nat_lit 25843894) (nat_lit 3390271686) (nat_lit 0) D2M8K2.u12280 from rfl, totK_node, atot12153, atot12280]
  decide +kernel

theorem arows12540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12540 = true := by
  rw [show D2M8K2.u12540 = KTree.node D2M8K2.u12412 (nat_lit 26253434) (nat_lit 3545882995) (nat_lit 0) D2M8K2.u12539 from rfl, allE_node, arows12412, irow12540, arows12539]
  all_goals rfl

theorem atot12540 : totK PD2M8K2 D2M8K2.u12540 = [2880687651292, 29833756404658, 85114361700968, 84782595177072, 24871489352177, 1849321072400, 27490598505, 0] := by
  rw [show D2M8K2.u12540 = KTree.node D2M8K2.u12412 (nat_lit 26253434) (nat_lit 3545882995) (nat_lit 0) D2M8K2.u12539 from rfl, totK_node, atot12412, atot12539]
  decide +kernel

theorem arows12795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12795 = true := by
  rw [show D2M8K2.u12795 = KTree.node D2M8K2.u12667 (nat_lit 27247874) (nat_lit 1981206302) (nat_lit 2056) D2M8K2.u12794 from rfl, allE_node, arows12667, irow12795, arows12794]
  all_goals rfl

theorem atot12795 : totK PD2M8K2 D2M8K2.u12795 = [0, 9781070675180, 54079244073382, 96795564635632, 58870565791850, 9477882616627, 371141484031, 1369150432] := by
  rw [show D2M8K2.u12795 = KTree.node D2M8K2.u12667 (nat_lit 27247874) (nat_lit 1981206302) (nat_lit 2056) D2M8K2.u12794 from rfl, totK_node, atot12667, atot12794]
  decide +kernel

theorem arows13051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13051 = true := by
  rw [show D2M8K2.u13051 = KTree.node D2M8K2.u12923 (nat_lit 27923163) (nat_lit 3685727677) (nat_lit 0) D2M8K2.u13050 from rfl, allE_node, arows12923, irow13051, arows13050]
  all_goals rfl

theorem atot13051 : totK PD2M8K2 D2M8K2.u13051 = [0, 14933494667611, 68534802078777, 98309091284918, 43751652523068, 4693834883062, 90115831842, 0] := by
  rw [show D2M8K2.u13051 = KTree.node D2M8K2.u12923 (nat_lit 27923163) (nat_lit 3685727677) (nat_lit 0) D2M8K2.u13050 from rfl, totK_node, atot12923, atot13050]
  decide +kernel

theorem arows13306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13306 = true := by
  rw [show D2M8K2.u13306 = KTree.node D2M8K2.u13178 (nat_lit 28565508) (nat_lit 2811836272) (nat_lit 0) D2M8K2.u13305 from rfl, allE_node, arows13178, irow13306, arows13305]
  all_goals rfl

theorem atot13306 : totK PD2M8K2 D2M8K2.u13306 = [0, 15165336788416, 69042872915236, 98011504672500, 43206384044985, 4613077162717, 92700443984, 0] := by
  rw [show D2M8K2.u13306 = KTree.node D2M8K2.u13178 (nat_lit 28565508) (nat_lit 2811836272) (nat_lit 0) D2M8K2.u13305 from rfl, totK_node, atot13178, atot13305]
  decide +kernel

theorem arows13563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13563 = true := by
  rw [show D2M8K2.u13563 = KTree.node D2M8K2.u13435 (nat_lit 29200868) (nat_lit 3288119639) (nat_lit 0) D2M8K2.u13562 from rfl, allE_node, arows13435, irow13563, arows13562]
  all_goals rfl

theorem atot13563 : totK PD2M8K2 D2M8K2.u13563 = [4080737729171, 22281202769259, 54586469910027, 78634643168864, 55636627157517, 12606934802854, 815444921943, 7324389265] := by
  rw [show D2M8K2.u13563 = KTree.node D2M8K2.u13435 (nat_lit 29200868) (nat_lit 3288119639) (nat_lit 0) D2M8K2.u13562 from rfl, totK_node, atot13435, atot13562]
  decide +kernel

theorem arows13818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13818 = true := by
  rw [show D2M8K2.u13818 = KTree.node D2M8K2.u13690 (nat_lit 30137089) (nat_lit 1425605381) (nat_lit 0) D2M8K2.u13817 from rfl, allE_node, arows13690, irow13818, arows13817]
  all_goals rfl

theorem atot13818 : totK PD2M8K2 D2M8K2.u13818 = [8539934717027, 48093624845482, 92708538834537, 66788197038052, 13229246527978, 579324751668, 1369150432, 0] := by
  rw [show D2M8K2.u13818 = KTree.node D2M8K2.u13690 (nat_lit 30137089) (nat_lit 1425605381) (nat_lit 0) D2M8K2.u13817 from rfl, totK_node, atot13690, atot13817]
  decide +kernel

theorem arows14074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14074 = true := by
  rw [show D2M8K2.u14074 = KTree.node D2M8K2.u13946 (nat_lit 30606185) (nat_lit 1614263446) (nat_lit 0) D2M8K2.u14073 from rfl, allE_node, arows13946, irow14074, arows14073]
  all_goals rfl

theorem atot14074 : totK PD2M8K2 D2M8K2.u14074 = [6938597777729, 40304864636716, 83406641799452, 72100221424334, 25001324588180, 2772028017937, 70818570093, 0] := by
  rw [show D2M8K2.u14074 = KTree.node D2M8K2.u13946 (nat_lit 30606185) (nat_lit 1614263446) (nat_lit 0) D2M8K2.u14073 from rfl, totK_node, atot13946, atot14073]
  decide +kernel

theorem arows14329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14329 = true := by
  rw [show D2M8K2.u14329 = KTree.node D2M8K2.u14201 (nat_lit 30955398) (nat_lit 3680364008) (nat_lit 0) D2M8K2.u14328 from rfl, allE_node, arows14201, irow14329, arows14328]
  all_goals rfl

theorem atot14329 : totK PD2M8K2 D2M8K2.u14329 = [9778545473192, 49870981537154, 88700558479658, 63697101228920, 16893199820280, 1272638073321, 14895044058, 0] := by
  rw [show D2M8K2.u14329 = KTree.node D2M8K2.u14201 (nat_lit 30955398) (nat_lit 3680364008) (nat_lit 0) D2M8K2.u14328 from rfl, totK_node, atot14201, atot14328]
  decide +kernel

theorem arows14587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14587 = true := by
  rw [show D2M8K2.u14587 = KTree.node D2M8K2.u14459 (nat_lit 31404212) (nat_lit 3694315474) (nat_lit 0) D2M8K2.u14586 from rfl, allE_node, arows14459, irow14587, arows14586]
  all_goals rfl

theorem atot14587 : totK PD2M8K2 D2M8K2.u14587 = [9779847516123, 50505354931436, 89695982775667, 62972432635447, 15754303539761, 1231410839175, 24680175954, 0] := by
  rw [show D2M8K2.u14587 = KTree.node D2M8K2.u14459 (nat_lit 31404212) (nat_lit 3694315474) (nat_lit 0) D2M8K2.u14586 from rfl, totK_node, atot14459, atot14586]
  decide +kernel

theorem arows14842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14842 = true := by
  rw [show D2M8K2.u14842 = KTree.node D2M8K2.u14714 (nat_lit 31817377) (nat_lit 1553212496) (nat_lit 0) D2M8K2.u14841 from rfl, allE_node, arows14714, irow14842, arows14841]
  all_goals rfl

theorem atot14842 : totK PD2M8K2 D2M8K2.u14842 = [7323068860337, 41814275659841, 86054218133079, 72401450990526, 20552019541204, 1546715902446, 26316908414, 0] := by
  rw [show D2M8K2.u14842 = KTree.node D2M8K2.u14714 (nat_lit 31817377) (nat_lit 1553212496) (nat_lit 0) D2M8K2.u14841 from rfl, totK_node, atot14714, atot14841]
  decide +kernel

theorem arows15098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15098 = true := by
  rw [show D2M8K2.u15098 = KTree.node D2M8K2.u14970 (nat_lit 32693912) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u15097 from rfl, allE_node, arows14970, irow15098, arows15097]
  all_goals rfl

theorem atot15098 : totK PD2M8K2 D2M8K2.u15098 = [2889725044371, 27816468207455, 80312722258871, 86184072972037, 29478464049180, 2547988824234, 48068665689, 0] := by
  rw [show D2M8K2.u15098 = KTree.node D2M8K2.u14970 (nat_lit 32693912) (nat_lit 3522529939) (nat_lit 0) D2M8K2.u15097 from rfl, totK_node, atot14970, atot15097]
  decide +kernel

theorem arows15353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15353 = true := by
  rw [show D2M8K2.u15353 = KTree.node D2M8K2.u15225 (nat_lit 33097549) (nat_lit 1384954955) (nat_lit 0) D2M8K2.u15352 from rfl, allE_node, arows15225, irow15353, arows15352]
  all_goals rfl

theorem atot15353 : totK PD2M8K2 D2M8K2.u15353 = [0, 9183242701661, 51368569786925, 95882051610353, 63086398706721, 10503658509430, 406108457305, 1369150432] := by
  rw [show D2M8K2.u15353 = KTree.node D2M8K2.u15225 (nat_lit 33097549) (nat_lit 1384954955) (nat_lit 0) D2M8K2.u15352 from rfl, totK_node, atot15225, atot15352]
  decide +kernel

theorem arows15610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15610 = true := by
  rw [show D2M8K2.u15610 = KTree.node D2M8K2.u15482 (nat_lit 33573391) (nat_lit 2415735841) (nat_lit 0) D2M8K2.u15609 from rfl, allE_node, arows15482, irow15610, arows15609]
  all_goals rfl

theorem atot15610 : totK PD2M8K2 D2M8K2.u15610 = [0, 14579828196804, 66270295932106, 96626325487185, 47365790504483, 6079488212701, 145066262449, 0] := by
  rw [show D2M8K2.u15610 = KTree.node D2M8K2.u15482 (nat_lit 33573391) (nat_lit 2415735841) (nat_lit 0) D2M8K2.u15609 from rfl, totK_node, atot15482, atot15609]
  decide +kernel

theorem arows15865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15865 = true := by
  rw [show D2M8K2.u15865 = KTree.node D2M8K2.u15737 (nat_lit 34202136) (nat_lit 3571591327) (nat_lit 0) D2M8K2.u15864 from rfl, allE_node, arows15737, irow15865, arows15864]
  all_goals rfl

theorem atot15865 : totK PD2M8K2 D2M8K2.u15865 = [0, 8976999735836, 49690195889533, 93041839434016, 64604103345555, 13535559890842, 733381036067, 7876972424] := by
  rw [show D2M8K2.u15865 = KTree.node D2M8K2.u15737 (nat_lit 34202136) (nat_lit 3571591327) (nat_lit 0) D2M8K2.u15864 from rfl, totK_node, atot15737, atot15864]
  decide +kernel

theorem arows16121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16121 = true := by
  rw [show D2M8K2.u16121 = KTree.node D2M8K2.u15993 (nat_lit 34716429) (nat_lit 1479814141) (nat_lit 0) D2M8K2.u16120 from rfl, allE_node, arows15993, irow16121, arows16120]
  all_goals rfl

theorem atot16121 : totK PD2M8K2 D2M8K2.u16121 = [0, 7733382000038, 46937117539356, 93823861359433, 67209537744392, 14055543940043, 744851754920, 7953845140] := by
  rw [show D2M8K2.u16121 = KTree.node D2M8K2.u15993 (nat_lit 34716429) (nat_lit 1479814141) (nat_lit 0) D2M8K2.u16120 from rfl, totK_node, atot15993, atot16120]
  decide +kernel

theorem arows16376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16376 = true := by
  rw [show D2M8K2.u16376 = KTree.node D2M8K2.u16248 (nat_lit 35603822) (nat_lit 2567457834) (nat_lit 0) D2M8K2.u16375 from rfl, allE_node, arows16248, irow16376, arows16375]
  all_goals rfl

theorem atot16376 : totK PD2M8K2 D2M8K2.u16376 = [0, 6173921422655, 38300053235388, 84791818726289, 75394025766920, 23048871738132, 2098124892983, 46699515257] := by
  rw [show D2M8K2.u16376 = KTree.node D2M8K2.u16248 (nat_lit 35603822) (nat_lit 2567457834) (nat_lit 0) D2M8K2.u16375 from rfl, totK_node, atot16248, atot16375]
  decide +kernel

theorem arows510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u510 = true := by
  rw [show D2M8K2.u510 = KTree.node D2M8K2.u254 (nat_lit 425237) (nat_lit 2115311576) (nat_lit 0) D2M8K2.u509 from rfl, allE_node, arows254, irow510, arows509]
  all_goals rfl

theorem atot510 : totK PD2M8K2 D2M8K2.u510 = [19955062702573, 105863405068159, 188196791150551, 121863703204450, 22589097998858, 958233187398, 2644528287, 0] := by
  rw [show D2M8K2.u510 = KTree.node D2M8K2.u254 (nat_lit 425237) (nat_lit 2115311576) (nat_lit 0) D2M8K2.u509 from rfl, totK_node, atot254, atot509]
  decide +kernel

theorem arows1021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1021 = true := by
  rw [show D2M8K2.u1021 = KTree.node D2M8K2.u765 (nat_lit 1753756) (nat_lit 3674163886) (nat_lit 0) D2M8K2.u1020 from rfl, allE_node, arows765, irow1021, arows1020]
  all_goals rfl

theorem atot1021 : totK PD2M8K2 D2M8K2.u1021 = [17433336343046, 93541722648439, 175980398553022, 133389532882266, 35552420052339, 2747151970791, 50997084368, 0] := by
  rw [show D2M8K2.u1021 = KTree.node D2M8K2.u765 (nat_lit 1753756) (nat_lit 3674163886) (nat_lit 0) D2M8K2.u1020 from rfl, totK_node, atot765, atot1020]
  decide +kernel

theorem arows1533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1533 = true := by
  rw [show D2M8K2.u1533 = KTree.node D2M8K2.u1277 (nat_lit 2613757) (nat_lit 1186107345) (nat_lit 0) D2M8K2.u1532 from rfl, allE_node, arows1277, irow1533, arows1532]
  all_goals rfl

theorem atot1533 : totK PD2M8K2 D2M8K2.u1533 = [11892091573767, 76087006924702, 170790296555914, 152072947910656, 44440599704272, 3424782115863, 55393054954, 0] := by
  rw [show D2M8K2.u1533 = KTree.node D2M8K2.u1277 (nat_lit 2613757) (nat_lit 1186107345) (nat_lit 0) D2M8K2.u1532 from rfl, totK_node, atot1277, atot1532]
  decide +kernel

theorem arows2044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2044 = true := by
  rw [show D2M8K2.u2044 = KTree.node D2M8K2.u1788 (nat_lit 3998641) (nat_lit 1511572004) (nat_lit 0) D2M8K2.u2043 from rfl, allE_node, arows1788, irow2044, arows2043]
  all_goals rfl

theorem atot2044 : totK PD2M8K2 D2M8K2.u2044 = [0, 24663916033817, 121028540253323, 192989594565504, 103375471768127, 14954838984981, 596244401700, 1369150432] := by
  rw [show D2M8K2.u2044 = KTree.node D2M8K2.u1788 (nat_lit 3998641) (nat_lit 1511572004) (nat_lit 0) D2M8K2.u2043 from rfl, totK_node, atot1788, atot2043]
  decide +kernel

theorem arows2557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2557 = true := by
  rw [show D2M8K2.u2557 = KTree.node D2M8K2.u2301 (nat_lit 5521567) (nat_lit 1843399602) (nat_lit 0) D2M8K2.u2556 from rfl, allE_node, arows2301, irow2557, arows2556]
  all_goals rfl

theorem atot2557 : totK PD2M8K2 D2M8K2.u2557 = [7348351400121, 54647956403673, 149302653179541, 172131183769591, 69577421783352, 6928251083210, 132888923681, 0] := by
  rw [show D2M8K2.u2557 = KTree.node D2M8K2.u2301 (nat_lit 5521567) (nat_lit 1843399602) (nat_lit 0) D2M8K2.u2556 from rfl, totK_node, atot2301, atot2556]
  decide +kernel

theorem arows3068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3068 = true := by
  rw [show D2M8K2.u3068 = KTree.node D2M8K2.u2812 (nat_lit 6996561) (nat_lit 1024151386) (nat_lit 0) D2M8K2.u3067 from rfl, allE_node, arows2812, irow3068, arows3067]
  all_goals rfl

theorem atot3068 : totK PD2M8K2 D2M8K2.u3068 = [12659274175186, 76963732852876, 166763835578276, 149173441845394, 49627381599408, 4884151035426, 105614127890, 0] := by
  rw [show D2M8K2.u3068 = KTree.node D2M8K2.u2812 (nat_lit 6996561) (nat_lit 1024151386) (nat_lit 0) D2M8K2.u3067 from rfl, totK_node, atot2812, atot3067]
  decide +kernel

theorem arows3580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3580 = true := by
  rw [show D2M8K2.u3580 = KTree.node D2M8K2.u3324 (nat_lit 7850154) (nat_lit 3844795051) (nat_lit 0) D2M8K2.u3579 from rfl, allE_node, arows3324, irow3580, arows3579]
  all_goals rfl

theorem atot3580 : totK PD2M8K2 D2M8K2.u3580 = [19549206951973, 101784953247396, 181481183989145, 125712662840907, 29490297541135, 1961814834741, 31096570629, 0] := by
  rw [show D2M8K2.u3580 = KTree.node D2M8K2.u3324 (nat_lit 7850154) (nat_lit 3844795051) (nat_lit 0) D2M8K2.u3579 from rfl, totK_node, atot3324, atot3579]
  decide +kernel

theorem arows4091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4091 = true := by
  rw [show D2M8K2.u4091 = KTree.node D2M8K2.u3835 (nat_lit 8677761) (nat_lit 1275301552) (nat_lit 0) D2M8K2.u4090 from rfl, allE_node, arows3835, irow4091, arows4090]
  all_goals rfl

theorem atot4091 : totK PD2M8K2 D2M8K2.u4091 = [9797325604445, 67879707184133, 163911951108105, 159277304644610, 54168245481989, 5411503124648, 123454559759, 0] := by
  rw [show D2M8K2.u4091 = KTree.node D2M8K2.u3835 (nat_lit 8677761) (nat_lit 1275301552) (nat_lit 0) D2M8K2.u4090 from rfl, totK_node, atot3835, atot4090]
  decide +kernel

theorem arows4605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4605 = true := by
  rw [show D2M8K2.u4605 = KTree.node D2M8K2.u4349 (nat_lit 9931905) (nat_lit 1519425954) (nat_lit 0) D2M8K2.u4604 from rfl, allE_node, arows4349, irow4605, arows4604]
  all_goals rfl

theorem atot4605 : totK PD2M8K2 D2M8K2.u4605 = [0, 15281199893937, 86934179931142, 173234594903813, 139514952036629, 42348968598282, 4049472199553, 91486352568] := by
  rw [show D2M8K2.u4605 = KTree.node D2M8K2.u4349 (nat_lit 9931905) (nat_lit 1519425954) (nat_lit 0) D2M8K2.u4604 from rfl, totK_node, atot4349, atot4604]
  decide +kernel

theorem arows5116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5116 = true := by
  rw [show D2M8K2.u5116 = KTree.node D2M8K2.u4860 (nat_lit 10835666) (nat_lit 3965365235) (nat_lit 0) D2M8K2.u5115 from rfl, allE_node, arows4860, irow5116, arows5115]
  all_goals rfl

theorem atot5116 : totK PD2M8K2 D2M8K2.u5116 = [0, 19549206951973, 103959460460467, 186733240653854, 124254541653804, 25489476398164, 1297637297778, 9930259102] := by
  rw [show D2M8K2.u5116 = KTree.node D2M8K2.u4860 (nat_lit 10835666) (nat_lit 3965365235) (nat_lit 0) D2M8K2.u5115 from rfl, totK_node, atot4860, atot5115]
  decide +kernel

theorem arows5628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5628 = true := by
  rw [show D2M8K2.u5628 = KTree.node D2M8K2.u5372 (nat_lit 11686181) (nat_lit 2047249975) (nat_lit 0) D2M8K2.u5627 from rfl, allE_node, arows5372, irow5628, arows5627]
  all_goals rfl

theorem atot5628 : totK PD2M8K2 D2M8K2.u5628 = [7757745427395, 44621600177505, 110652844073317, 155256218177624, 112780599629579, 28363443929037, 1793472773489, 17624333986] := by
  rw [show D2M8K2.u5628 = KTree.node D2M8K2.u5372 (nat_lit 11686181) (nat_lit 2047249975) (nat_lit 0) D2M8K2.u5627 from rfl, totK_node, atot5372, atot5627]
  decide +kernel

theorem arows6139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6139 = true := by
  rw [show D2M8K2.u6139 = KTree.node D2M8K2.u5883 (nat_lit 12611816) (nat_lit 3536012270) (nat_lit 0) D2M8K2.u6138 from rfl, allE_node, arows5883, irow6139, arows6138]
  all_goals rfl

theorem atot6139 : totK PD2M8K2 D2M8K2.u6139 = [13803736327309, 81099544729332, 169991172443629, 146034172687603, 45184032286716, 4217128304942, 85807386728, 0] := by
  rw [show D2M8K2.u6139 = KTree.node D2M8K2.u5883 (nat_lit 12611816) (nat_lit 3536012270) (nat_lit 0) D2M8K2.u6138 from rfl, totK_node, atot5883, atot6138]
  decide +kernel

theorem arows6652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6652 = true := by
  rw [show D2M8K2.u6652 = KTree.node D2M8K2.u6396 (nat_lit 13364405) (nat_lit 2316452482) (nat_lit 0) D2M8K2.u6651 from rfl, allE_node, arows6396, irow6652, arows6651]
  all_goals rfl

theorem atot6652 : totK PD2M8K2 D2M8K2.u6652 = [17958271524524, 97505944400685, 182048682397551, 130129137624719, 29946743505706, 1895484010766, 27164584678, 0] := by
  rw [show D2M8K2.u6652 = KTree.node D2M8K2.u6396 (nat_lit 13364405) (nat_lit 2316452482) (nat_lit 0) D2M8K2.u6651 from rfl, totK_node, atot6396, atot6651]
  decide +kernel

theorem arows7163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7163 = true := by
  rw [show D2M8K2.u7163 = KTree.node D2M8K2.u6907 (nat_lit 14694920) (nat_lit 3643078003) (nat_lit 0) D2M8K2.u7162 from rfl, allE_node, arows6907, irow7163, arows7162]
  all_goals rfl

theorem atot7163 : totK PD2M8K2 D2M8K2.u7163 = [9791754696174, 67996425365901, 165039223106552, 160278407737882, 51695821232888, 4302731424922, 75359192979, 0] := by
  rw [show D2M8K2.u7163 = KTree.node D2M8K2.u6907 (nat_lit 14694920) (nat_lit 3643078003) (nat_lit 0) D2M8K2.u7162 from rfl, totK_node, atot6907, atot7162]
  decide +kernel

theorem arows7675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7675 = true := by
  rw [show D2M8K2.u7675 = KTree.node D2M8K2.u7419 (nat_lit 15607866) (nat_lit 3474702526) (nat_lit 0) D2M8K2.u7674 from rfl, allE_node, arows7419, irow7675, arows7674]
  all_goals rfl

theorem atot7675 : totK PD2M8K2 D2M8K2.u7675 = [0, 21999351785956, 113062195798511, 192070494453340, 113938336509295, 18404410798704, 719598336380, 2644528287] := by
  rw [show D2M8K2.u7675 = KTree.node D2M8K2.u7419 (nat_lit 15607866) (nat_lit 3474702526) (nat_lit 0) D2M8K2.u7674 from rfl, totK_node, atot7419, atot7674]
  decide +kernel

theorem arows8186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8186 = true := by
  rw [show D2M8K2.u8186 = KTree.node D2M8K2.u7930 (nat_lit 17114735) (nat_lit 2032219023) (nat_lit 0) D2M8K2.u8185 from rfl, allE_node, arows7930, irow8186, arows8185]
  all_goals rfl

theorem atot8186 : totK PD2M8K2 D2M8K2.u8186 = [0, 18874523556777, 102018765971143, 185512787150299, 124368409755541, 26827750990044, 1828171742989, 32004565219] := by
  rw [show D2M8K2.u8186 = KTree.node D2M8K2.u7930 (nat_lit 17114735) (nat_lit 2032219023) (nat_lit 0) D2M8K2.u8185 from rfl, totK_node, atot7930, atot8185]
  decide +kernel

theorem arows8701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8701 = true := by
  rw [show D2M8K2.u8701 = KTree.node D2M8K2.u8445 (nat_lit 18306057) (nat_lit 1813301637) (nat_lit 0) D2M8K2.u8700 from rfl, allE_node, arows8445, irow8701, arows8700]
  all_goals rfl

theorem atot8701 : totK PD2M8K2 D2M8K2.u8701 = [19556357124774, 101531245042784, 180290061810026, 124366639178634, 31160470856658, 2959290485845, 82750153457, 0] := by
  rw [show D2M8K2.u8701 = KTree.node D2M8K2.u8445 (nat_lit 18306057) (nat_lit 1813301637) (nat_lit 0) D2M8K2.u8700 from rfl, totK_node, atot8445, atot8700]
  decide +kernel

theorem arows9212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9212 = true := by
  rw [show D2M8K2.u9212 = KTree.node D2M8K2.u8956 (nat_lit 19588811) (nat_lit 2055446333) (nat_lit 0) D2M8K2.u9211 from rfl, allE_node, arows8956, irow9212, arows9211]
  all_goals rfl

theorem atot9212 : totK PD2M8K2 D2M8K2.u9212 = [14174323349618, 81645035317998, 168737885009131, 145355647979510, 45986755909951, 3955730831709, 62246840366, 0] := by
  rw [show D2M8K2.u9212 = KTree.node D2M8K2.u8956 (nat_lit 19588811) (nat_lit 2055446333) (nat_lit 0) D2M8K2.u9211 from rfl, totK_node, atot8956, atot9211]
  decide +kernel

theorem arows9724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9724 = true := by
  rw [show D2M8K2.u9724 = KTree.node D2M8K2.u9468 (nat_lit 20449790) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u9723 from rfl, allE_node, arows9468, irow9724, arows9723]
  all_goals rfl

theorem atot9724 : totK PD2M8K2 D2M8K2.u9724 = [15582888485588, 89511526064076, 178815266024577, 139076161337018, 34559000619919, 2133723652279, 21358947519, 0] := by
  rw [show D2M8K2.u9724 = KTree.node D2M8K2.u9468 (nat_lit 20449790) (nat_lit 3915131715) (nat_lit 0) D2M8K2.u9723 from rfl, totK_node, atot9468, atot9723]
  decide +kernel

theorem arows10235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10235 = true := by
  rw [show D2M8K2.u10235 = KTree.node D2M8K2.u9979 (nat_lit 21294148) (nat_lit 3668739202) (nat_lit 0) D2M8K2.u10234 from rfl, allE_node, arows9979, irow10235, arows10234]
  all_goals rfl

theorem atot10235 : totK PD2M8K2 D2M8K2.u10235 = [0, 24969143956160, 121973205849588, 193631114996722, 104221115382762, 14786845007945, 492923999544, 1369150432] := by
  rw [show D2M8K2.u10235 = KTree.node D2M8K2.u9979 (nat_lit 21294148) (nat_lit 3668739202) (nat_lit 0) D2M8K2.u10234 from rfl, totK_node, atot9979, atot10234]
  decide +kernel

theorem arows10748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10748 = true := by
  rw [show D2M8K2.u10748 = KTree.node D2M8K2.u10492 (nat_lit 22868816) (nat_lit 3571016490) (nat_lit 0) D2M8K2.u10747 from rfl, allE_node, arows10492, irow10748, arows10747]
  all_goals rfl

theorem atot10748 : totK PD2M8K2 D2M8K2.u10748 = [0, 16248995375785, 95172988269118, 186066789429115, 132017635709798, 28228506425889, 1768445468487, 27525939283] := by
  rw [show D2M8K2.u10748 = KTree.node D2M8K2.u10492 (nat_lit 22868816) (nat_lit 3571016490) (nat_lit 0) D2M8K2.u10747 from rfl, totK_node, atot10492, atot10747]
  decide +kernel

theorem arows11259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11259 = true := by
  rw [show D2M8K2.u11259 = KTree.node D2M8K2.u11003 (nat_lit 24009601) (nat_lit 1419478073) (nat_lit 0) D2M8K2.u11258 from rfl, allE_node, arows11003, irow11259, arows11258]
  all_goals rfl

theorem atot11259 : totK PD2M8K2 D2M8K2.u11259 = [12950002336834, 76931976365821, 163160878115249, 145473056870503, 52767869938830, 7921677428338, 441412785872, 6115358396] := by
  rw [show D2M8K2.u11259 = KTree.node D2M8K2.u11003 (nat_lit 24009601) (nat_lit 1419478073) (nat_lit 0) D2M8K2.u11258 from rfl, totK_node, atot11003, atot11258]
  decide +kernel

theorem arows11771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11771 = true := by
  rw [show D2M8K2.u11771 = KTree.node D2M8K2.u11515 (nat_lit 24825861) (nat_lit 1675495268) (nat_lit 0) D2M8K2.u11770 from rfl, allE_node, arows11515, irow11771, arows11770]
  all_goals rfl

theorem atot11771 : totK PD2M8K2 D2M8K2.u11771 = [16374803779485, 89511151065278, 172000752015550, 136174528178730, 42088986642691, 4046703196833, 85713614151, 0] := by
  rw [show D2M8K2.u11771 = KTree.node D2M8K2.u11515 (nat_lit 24825861) (nat_lit 1675495268) (nat_lit 0) D2M8K2.u11770 from rfl, totK_node, atot11515, atot11770]
  decide +kernel

theorem arows12282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12282 = true := by
  rw [show D2M8K2.u12282 = KTree.node D2M8K2.u12026 (nat_lit 25627137) (nat_lit 1592153276) (nat_lit 0) D2M8K2.u12281 from rfl, allE_node, arows12026, irow12282, arows12281]
  all_goals rfl

theorem atot12282 : totK PD2M8K2 D2M8K2.u12282 = [17086760904418, 92298808809384, 175550005900653, 134988302598129, 36297322957901, 2781736593238, 50997084368, 0] := by
  rw [show D2M8K2.u12282 = KTree.node D2M8K2.u12026 (nat_lit 25627137) (nat_lit 1592153276) (nat_lit 0) D2M8K2.u12281 from rfl, totK_node, atot12026, atot12281]
  decide +kernel

theorem arows12796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12796 = true := by
  rw [show D2M8K2.u12796 = KTree.node D2M8K2.u12540 (nat_lit 27010731) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u12795 from rfl, allE_node, arows12540, irow12796, arows12795]
  all_goals rfl

theorem atot12796 : totK PD2M8K2 D2M8K2.u12796 = [2880687651292, 39614827079838, 139193605774350, 181581863410704, 83742055144027, 11327203689027, 398632082536, 1369150432] := by
  rw [show D2M8K2.u12796 = KTree.node D2M8K2.u12540 (nat_lit 27010731) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u12795 from rfl, totK_node, atot12540, atot12795]
  decide +kernel

theorem arows13307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13307 = true := by
  rw [show D2M8K2.u13307 = KTree.node D2M8K2.u13051 (nat_lit 28374970) (nat_lit 3154198928) (nat_lit 0) D2M8K2.u13306 from rfl, allE_node, arows13051, irow13307, arows13306]
  all_goals rfl

theorem atot13307 : totK PD2M8K2 D2M8K2.u13307 = [0, 30101985654955, 137577674994013, 196320595957418, 86958036568053, 9306912045779, 182816275826, 0] := by
  rw [show D2M8K2.u13307 = KTree.node D2M8K2.u13051 (nat_lit 28374970) (nat_lit 3154198928) (nat_lit 0) D2M8K2.u13306 from rfl, totK_node, atot13051, atot13306]
  decide +kernel

theorem arows13819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13819 = true := by
  rw [show D2M8K2.u13819 = KTree.node D2M8K2.u13563 (nat_lit 29979716) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u13818 from rfl, allE_node, arows13563, irow13819, arows13818]
  all_goals rfl

theorem atot13819 : totK PD2M8K2 D2M8K2.u13819 = [12620672446198, 70374827614741, 147295008744564, 145426209231480, 68865873685495, 13186259554522, 816814072375, 7324389265] := by
  rw [show D2M8K2.u13819 = KTree.node D2M8K2.u13563 (nat_lit 29979716) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u13818 from rfl, totK_node, atot13563, atot13818]
  decide +kernel

theorem arows14330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14330 = true := by
  rw [show D2M8K2.u14330 = KTree.node D2M8K2.u14074 (nat_lit 30801445) (nat_lit 1287732095) (nat_lit 0) D2M8K2.u14329 from rfl, allE_node, arows14074, irow14330, arows14329]
  all_goals rfl

theorem atot14330 : totK PD2M8K2 D2M8K2.u14330 = [16717143250921, 90175846173870, 172107200279110, 135797322653254, 41895812140555, 4044666091258, 85713614151, 0] := by
  rw [show D2M8K2.u14330 = KTree.node D2M8K2.u14074 (nat_lit 30801445) (nat_lit 1287732095) (nat_lit 0) D2M8K2.u14329 from rfl, totK_node, atot14074, atot14329]
  decide +kernel

theorem arows14843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14843 = true := by
  rw [show D2M8K2.u14843 = KTree.node D2M8K2.u14587 (nat_lit 31592811) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u14842 from rfl, allE_node, arows14587, irow14843, arows14842]
  all_goals rfl

theorem atot14843 : totK PD2M8K2 D2M8K2.u14843 = [17102916376460, 92319630591277, 175753830242638, 135373883625973, 36306323080965, 2778126741621, 50997084368, 0] := by
  rw [show D2M8K2.u14843 = KTree.node D2M8K2.u14587 (nat_lit 31592811) (nat_lit 3629333892) (nat_lit 0) D2M8K2.u14842 from rfl, totK_node, atot14587, atot14842]
  decide +kernel

theorem arows15354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15354 = true := by
  rw [show D2M8K2.u15354 = KTree.node D2M8K2.u15098 (nat_lit 32932922) (nat_lit 4057184514) (nat_lit 0) D2M8K2.u15353 from rfl, allE_node, arows15098, irow15354, arows15353]
  all_goals rfl

theorem atot15354 : totK PD2M8K2 D2M8K2.u15354 = [2889725044371, 37003768093630, 131681292045796, 182066124582390, 92564862755901, 13051647333664, 454177122994, 1369150432] := by
  rw [show D2M8K2.u15354 = KTree.node D2M8K2.u15098 (nat_lit 32932922) (nat_lit 4057184514) (nat_lit 0) D2M8K2.u15353 from rfl, totK_node, atot15098, atot15353]
  decide +kernel

theorem arows15866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15866 = true := by
  rw [show D2M8K2.u15866 = KTree.node D2M8K2.u15610 (nat_lit 34012778) (nat_lit 4109747187) (nat_lit 0) D2M8K2.u15865 from rfl, allE_node, arows15610, irow15866, arows15865]
  all_goals rfl

theorem atot15866 : totK PD2M8K2 D2M8K2.u15866 = [0, 23556827932640, 115960491821639, 189672274668388, 111969893850038, 19615048103543, 878447298516, 7876972424] := by
  rw [show D2M8K2.u15866 = KTree.node D2M8K2.u15610 (nat_lit 34012778) (nat_lit 4109747187) (nat_lit 0) D2M8K2.u15865 from rfl, totK_node, atot15610, atot15865]
  decide +kernel

theorem arows16377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16377 = true := by
  rw [show D2M8K2.u16377 = KTree.node D2M8K2.u16121 (nat_lit 35416451) (nat_lit 2576854062) (nat_lit 0) D2M8K2.u16376 from rfl, allE_node, arows16121, irow16377, arows16376]
  all_goals rfl

theorem atot16377 : totK PD2M8K2 D2M8K2.u16377 = [0, 13907303422693, 85237170774744, 178615680085722, 142603563511312, 37106992532237, 2842976647903, 54653360397] := by
  rw [show D2M8K2.u16377 = KTree.node D2M8K2.u16121 (nat_lit 35416451) (nat_lit 2576854062) (nat_lit 0) D2M8K2.u16376 from rfl, totK_node, atot16121, atot16376]
  decide +kernel

theorem arows1022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1022 = true := by
  rw [show D2M8K2.u1022 = KTree.node D2M8K2.u510 (nat_lit 1336010) (nat_lit 3128128024) (nat_lit 0) D2M8K2.u1021 from rfl, allE_node, arows510, irow1022, arows1021]
  all_goals rfl

theorem atot1022 : totK PD2M8K2 D2M8K2.u1022 = [37388399045619, 199405127716598, 364177189703573, 255256364214740, 58141518051197, 3705385158189, 53641612655, 0] := by
  rw [show D2M8K2.u1022 = KTree.node D2M8K2.u510 (nat_lit 1336010) (nat_lit 3128128024) (nat_lit 0) D2M8K2.u1021 from rfl, totK_node, atot510, atot1021]
  decide +kernel

theorem arows2045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2045 = true := by
  rw [show D2M8K2.u2045 = KTree.node D2M8K2.u1533 (nat_lit 3024960) (nat_lit 3430850179) (nat_lit 0) D2M8K2.u2044 from rfl, allE_node, arows1533, irow2045, arows2044]
  all_goals rfl

theorem atot2045 : totK PD2M8K2 D2M8K2.u2045 = [11892091573767, 100750922958519, 291822267659416, 345062542476160, 147816071472399, 18379621100844, 651637456654, 1369150432] := by
  rw [show D2M8K2.u2045 = KTree.node D2M8K2.u1533 (nat_lit 3024960) (nat_lit 3430850179) (nat_lit 0) D2M8K2.u2044 from rfl, totK_node, atot1533, atot2044]
  decide +kernel

theorem arows3069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3069 = true := by
  rw [show D2M8K2.u3069 = KTree.node D2M8K2.u2557 (nat_lit 6644888) (nat_lit 3329091244) (nat_lit 0) D2M8K2.u3068 from rfl, allE_node, arows2557, irow3069, arows3068]
  all_goals rfl

theorem atot3069 : totK PD2M8K2 D2M8K2.u3069 = [20007625575307, 131611689256549, 316069817849061, 321304625614985, 119204803382760, 11812402118636, 238503051571, 0] := by
  rw [show D2M8K2.u3069 = KTree.node D2M8K2.u2557 (nat_lit 6644888) (nat_lit 3329091244) (nat_lit 0) D2M8K2.u3068 from rfl, totK_node, atot2557, atot3068]
  decide +kernel

theorem arows4092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4092 = true := by
  rw [show D2M8K2.u4092 = KTree.node D2M8K2.u3580 (nat_lit 8222768) (nat_lit 3779522820) (nat_lit 0) D2M8K2.u4091 from rfl, allE_node, arows3580, irow4092, arows4091]
  all_goals rfl

theorem atot4092 : totK PD2M8K2 D2M8K2.u4092 = [29346532556418, 169668439954349, 345393135097250, 284989967485517, 83658543023124, 7373317959389, 154551130388, 0] := by
  rw [show D2M8K2.u4092 = KTree.node D2M8K2.u3580 (nat_lit 8222768) (nat_lit 3779522820) (nat_lit 0) D2M8K2.u4091 from rfl, totK_node, atot3580, atot4091]
  decide +kernel

theorem arows5117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5117 = true := by
  rw [show D2M8K2.u5117 = KTree.node D2M8K2.u4605 (nat_lit 10372041) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u5116 from rfl, allE_node, arows4605, irow5117, arows5116]
  all_goals rfl

theorem atot5117 : totK PD2M8K2 D2M8K2.u5117 = [0, 34830406845910, 190893640391609, 359969623873863, 263769493690433, 67838444996446, 5347109497331, 101416611670] := by
  rw [show D2M8K2.u5117 = KTree.node D2M8K2.u4605 (nat_lit 10372041) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u5116 from rfl, totK_node, atot4605, atot5116]
  decide +kernel

theorem arows6140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6140 = true := by
  rw [show D2M8K2.u6140 = KTree.node D2M8K2.u5628 (nat_lit 12142528) (nat_lit 1768552435) (nat_lit 0) D2M8K2.u6139 from rfl, allE_node, arows5628, irow6140, arows6139]
  all_goals rfl

theorem atot6140 : totK PD2M8K2 D2M8K2.u6140 = [21561481754704, 125721144906837, 280644016516946, 301292159417662, 157964631916295, 32580572233979, 1879280160217, 17624333986] := by
  rw [show D2M8K2.u6140 = KTree.node D2M8K2.u5628 (nat_lit 12142528) (nat_lit 1768552435) (nat_lit 0) D2M8K2.u6139 from rfl, totK_node, atot5628, atot6139]
  decide +kernel

theorem arows7164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7164 = true := by
  rw [show D2M8K2.u7164 = KTree.node D2M8K2.u6652 (nat_lit 14243616) (nat_lit 3549517115) (nat_lit 0) D2M8K2.u7163 from rfl, allE_node, arows6652, irow7164, arows7163]
  all_goals rfl

theorem atot7164 : totK PD2M8K2 D2M8K2.u7164 = [27750026220698, 165505919283701, 347087905504103, 290407545362601, 81642564738594, 6198215435688, 102523777657, 0] := by
  rw [show D2M8K2.u7164 = KTree.node D2M8K2.u6652 (nat_lit 14243616) (nat_lit 3549517115) (nat_lit 0) D2M8K2.u7163 from rfl, totK_node, atot6652, atot7163]
  decide +kernel

theorem arows8187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8187 = true := by
  rw [show D2M8K2.u8187 = KTree.node D2M8K2.u7675 (nat_lit 16219565) (nat_lit 2174839631) (nat_lit 0) D2M8K2.u8186 from rfl, allE_node, arows7675, irow8187, arows8186]
  all_goals rfl

theorem atot8187 : totK PD2M8K2 D2M8K2.u8187 = [0, 40873875342733, 215080961769654, 377583281603639, 238308921104467, 45232161788748, 2547770079369, 34649093506] := by
  rw [show D2M8K2.u8187 = KTree.node D2M8K2.u7675 (nat_lit 16219565) (nat_lit 2174839631) (nat_lit 0) D2M8K2.u8186 from rfl, totK_node, atot7675, atot8186]
  decide +kernel

theorem arows9213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9213 = true := by
  rw [show D2M8K2.u9213 = KTree.node D2M8K2.u8701 (nat_lit 18742350) (nat_lit 3854965123) (nat_lit 0) D2M8K2.u9212 from rfl, allE_node, arows8701, irow9213, arows9212]
  all_goals rfl

theorem atot9213 : totK PD2M8K2 D2M8K2.u9213 = [33730680474392, 183176280360782, 349027946819157, 269726142123267, 77147226766609, 6915021317554, 144996993823, 0] := by
  rw [show D2M8K2.u9213 = KTree.node D2M8K2.u8701 (nat_lit 18742350) (nat_lit 3854965123) (nat_lit 0) D2M8K2.u9212 from rfl, totK_node, atot8701, atot9212]
  decide +kernel

theorem arows10236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10236 = true := by
  rw [show D2M8K2.u10236 = KTree.node D2M8K2.u9724 (nat_lit 20863371) (nat_lit 2753598739) (nat_lit 0) D2M8K2.u10235 from rfl, allE_node, arows9724, irow10236, arows10235]
  all_goals rfl

theorem atot10236 : totK PD2M8K2 D2M8K2.u10236 = [15582888485588, 114480670020236, 300788471874165, 332710029932479, 138780116002681, 16920568660224, 514282947063, 1369150432] := by
  rw [show D2M8K2.u10236 = KTree.node D2M8K2.u9724 (nat_lit 20863371) (nat_lit 2753598739) (nat_lit 0) D2M8K2.u10235 from rfl, totK_node, atot9724, atot10235]
  decide +kernel

theorem arows11260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11260 = true := by
  rw [show D2M8K2.u11260 = KTree.node D2M8K2.u10748 (nat_lit 23320731) (nat_lit 2334463293) (nat_lit 0) D2M8K2.u11259 from rfl, allE_node, arows10748, irow11260, arows11259]
  all_goals rfl

theorem atot11260 : totK PD2M8K2 D2M8K2.u11260 = [12950002336834, 93180971741606, 258333866384367, 331539846299618, 184785505648628, 36152518317520, 2209858254359, 33641297679] := by
  rw [show D2M8K2.u11260 = KTree.node D2M8K2.u10748 (nat_lit 23320731) (nat_lit 2334463293) (nat_lit 0) D2M8K2.u11259 from rfl, totK_node, atot10748, atot11259]
  decide +kernel

theorem arows12283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12283 = true := by
  rw [show D2M8K2.u12283 = KTree.node D2M8K2.u11771 (nat_lit 25191140) (nat_lit 3103980657) (nat_lit 0) D2M8K2.u12282 from rfl, allE_node, arows11771, irow12283, arows12282]
  all_goals rfl

theorem atot12283 : totK PD2M8K2 D2M8K2.u12283 = [33461564683903, 181809959874662, 347553861896860, 271162830776859, 78386309600592, 6828439790071, 136710698519, 0] := by
  rw [show D2M8K2.u12283 = KTree.node D2M8K2.u11771 (nat_lit 25191140) (nat_lit 3103980657) (nat_lit 0) D2M8K2.u12282 from rfl, totK_node, atot11771, atot12282]
  decide +kernel

theorem arows13308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13308 = true := by
  rw [show D2M8K2.u13308 = KTree.node D2M8K2.u12796 (nat_lit 27508159) (nat_lit 2332151599) (nat_lit 0) D2M8K2.u13307 from rfl, allE_node, arows12796, irow13308, arows13307]
  all_goals rfl

theorem atot13308 : totK PD2M8K2 D2M8K2.u13308 = [2880687651292, 69716812734793, 276771280768363, 377904791519721, 170700091712080, 20634115734806, 581448358362, 1369150432] := by
  rw [show D2M8K2.u13308 = KTree.node D2M8K2.u12796 (nat_lit 27508159) (nat_lit 2332151599) (nat_lit 0) D2M8K2.u13307 from rfl, totK_node, atot12796, atot13307]
  decide +kernel

theorem arows14331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14331 = true := by
  rw [show D2M8K2.u14331 = KTree.node D2M8K2.u13819 (nat_lit 30446670) (nat_lit 3924127462) (nat_lit 0) D2M8K2.u14330 from rfl, allE_node, arows13819, irow14331, arows14330]
  all_goals rfl

theorem atot14331 : totK PD2M8K2 D2M8K2.u14331 = [29337815697119, 160550673788611, 319406133151136, 281223531884734, 110761685826050, 17230925645780, 902527686526, 7324389265] := by
  rw [show D2M8K2.u14331 = KTree.node D2M8K2.u13819 (nat_lit 30446670) (nat_lit 3924127462) (nat_lit 0) D2M8K2.u14330 from rfl, totK_node, atot13819, atot14330]
  decide +kernel

theorem arows15355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15355 = true := by
  rw [show D2M8K2.u15355 = KTree.node D2M8K2.u14843 (nat_lit 32484538) (nat_lit 3928083805) (nat_lit 0) D2M8K2.u15354 from rfl, allE_node, arows14843, irow15355, arows15354]
  all_goals rfl

theorem atot15355 : totK PD2M8K2 D2M8K2.u15355 = [19992641420831, 129327326768712, 307435122288434, 317440008208363, 128871185836866, 15829774075285, 505174207362, 1369150432] := by
  rw [show D2M8K2.u15355 = KTree.node D2M8K2.u14843 (nat_lit 32484538) (nat_lit 3928083805) (nat_lit 0) D2M8K2.u15354 from rfl, totK_node, atot14843, atot15354]
  decide +kernel

theorem arows16378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16378 = true := by
  rw [show D2M8K2.u16378 = KTree.node D2M8K2.u15866 (nat_lit 34484106) (nat_lit 3757748445) (nat_lit 0) D2M8K2.u16377 from rfl, allE_node, arows15866, irow16378, arows16377]
  all_goals rfl

theorem atot16378 : totK PD2M8K2 D2M8K2.u16378 = [0, 37464131355333, 201197662596383, 368291712502555, 254573457361350, 56722040635780, 3721423946419, 62530332821] := by
  rw [show D2M8K2.u16378 = KTree.node D2M8K2.u15866 (nat_lit 34484106) (nat_lit 3757748445) (nat_lit 0) D2M8K2.u16377 from rfl, totK_node, atot15866, atot16377]
  decide +kernel

theorem arows2046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2046 = true := by
  rw [show D2M8K2.u2046 = KTree.node D2M8K2.u1022 (nat_lit 2151032) (nat_lit 3930769992) (nat_lit 0) D2M8K2.u2045 from rfl, allE_node, arows1022, irow2046, arows2045]
  all_goals rfl

theorem atot2046 : totK PD2M8K2 D2M8K2.u2046 = [49280490619386, 300156050675117, 656003388132981, 600318906690900, 205957589523596, 22085006259033, 705279069309, 1369150432] := by
  rw [show D2M8K2.u2046 = KTree.node D2M8K2.u1022 (nat_lit 2151032) (nat_lit 3930769992) (nat_lit 0) D2M8K2.u2045 from rfl, totK_node, atot1022, atot2045]
  decide +kernel

theorem arows4093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4093 = true := by
  rw [show D2M8K2.u4093 = KTree.node D2M8K2.u3069 (nat_lit 7409675) (nat_lit 2785025561) (nat_lit 0) D2M8K2.u4092 from rfl, allE_node, arows3069, irow4093, arows4092]
  all_goals rfl

theorem atot4093 : totK PD2M8K2 D2M8K2.u4093 = [49354158131725, 301280129210898, 661462952946311, 606297378126063, 202863346405884, 19185720078025, 393054181959, 0] := by
  rw [show D2M8K2.u4093 = KTree.node D2M8K2.u3069 (nat_lit 7409675) (nat_lit 2785025561) (nat_lit 0) D2M8K2.u4092 from rfl, totK_node, atot3069, atot4092]
  decide +kernel

theorem arows6141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6141 = true := by
  rw [show D2M8K2.u6141 = KTree.node D2M8K2.u5117 (nat_lit 11242839) (nat_lit 3626128243) (nat_lit 0) D2M8K2.u6140 from rfl, allE_node, arows5117, irow6141, arows6140]
  all_goals rfl

theorem atot6141 : totK PD2M8K2 D2M8K2.u6141 = [21561481754704, 160551551752747, 471537656908555, 661261783291525, 421734125606728, 100422643358668, 7226389657548, 119040945656] := by
  rw [show D2M8K2.u6141 = KTree.node D2M8K2.u5117 (nat_lit 11242839) (nat_lit 3626128243) (nat_lit 0) D2M8K2.u6140 from rfl, totK_node, atot5117, atot6140]
  decide +kernel

theorem arows8188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8188 = true := by
  rw [show D2M8K2.u8188 = KTree.node D2M8K2.u7164 (nat_lit 15123566) (nat_lit 2994984798) (nat_lit 0) D2M8K2.u8187 from rfl, allE_node, arows7164, irow8188, arows8187]
  all_goals rfl

theorem atot8188 : totK PD2M8K2 D2M8K2.u8188 = [27750026220698, 206379794626434, 562168867273757, 667993821951038, 319951485843061, 51430377224436, 2650293857026, 34649093506] := by
  rw [show D2M8K2.u8188 = KTree.node D2M8K2.u7164 (nat_lit 15123566) (nat_lit 2994984798) (nat_lit 0) D2M8K2.u8187 from rfl, totK_node, atot7164, atot8187]
  decide +kernel

theorem arows10237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10237 = true := by
  rw [show D2M8K2.u10237 = KTree.node D2M8K2.u9213 (nat_lit 19982383) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u10236 from rfl, allE_node, arows9213, irow10237, arows10236]
  all_goals rfl

theorem atot10237 : totK PD2M8K2 D2M8K2.u10237 = [49313568959980, 297656950381018, 649816418693322, 602438598775593, 215927342769290, 23835589977778, 659279940886, 1369150432] := by
  rw [show D2M8K2.u10237 = KTree.node D2M8K2.u9213 (nat_lit 19982383) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u10236 from rfl, totK_node, atot9213, atot10236]
  decide +kernel

theorem arows12284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12284 = true := by
  rw [show D2M8K2.u12284 = KTree.node D2M8K2.u11260 (nat_lit 24476640) (nat_lit 3540450641) (nat_lit 0) D2M8K2.u12283 from rfl, allE_node, arows11260, irow12284, arows12283]
  all_goals rfl

theorem atot12284 : totK PD2M8K2 D2M8K2.u12284 = [46415107471378, 274990931616268, 605887728281227, 602702677076477, 263171815249220, 42980958107591, 2346568952878, 33641297679] := by
  rw [show D2M8K2.u12284 = KTree.node D2M8K2.u11260 (nat_lit 24476640) (nat_lit 3540450641) (nat_lit 0) D2M8K2.u12283 from rfl, totK_node, atot11260, atot12283]
  decide +kernel

theorem arows14332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14332 = true := by
  rw [show D2M8K2.u14332 = KTree.node D2M8K2.u13308 (nat_lit 28976290) (nat_lit 3343085411) (nat_lit 0) D2M8K2.u14331 from rfl, allE_node, arows13308, irow14332, arows14331]
  all_goals rfl

theorem atot14332 : totK PD2M8K2 D2M8K2.u14332 = [32218503348411, 230267486523404, 596180757004910, 659128323404455, 281461777538130, 37865041380586, 1483976044888, 8693539697] := by
  rw [show D2M8K2.u14332 = KTree.node D2M8K2.u13308 (nat_lit 28976290) (nat_lit 3343085411) (nat_lit 0) D2M8K2.u14331 from rfl, totK_node, atot13308, atot14331]
  decide +kernel

theorem arows16379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16379 = true := by
  rw [show D2M8K2.u16379 = KTree.node D2M8K2.u15355 (nat_lit 33417168) (nat_lit 3222312734) (nat_lit 0) D2M8K2.u16378 from rfl, allE_node, arows15355, irow16379, arows16378]
  all_goals rfl

theorem atot16379 : totK PD2M8K2 D2M8K2.u16379 = [19992641420831, 166791458124045, 508632784884817, 685734943023652, 383444643198216, 72551814711065, 4226598153781, 63899483253] := by
  rw [show D2M8K2.u16379 = KTree.node D2M8K2.u15355 (nat_lit 33417168) (nat_lit 3222312734) (nat_lit 0) D2M8K2.u16378 from rfl, totK_node, atot15355, atot16378]
  decide +kernel

theorem arows4094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4094 = true := by
  rw [show D2M8K2.u4094 = KTree.node D2M8K2.u2046 (nat_lit 4652561) (nat_lit 2211249437) (nat_lit 0) D2M8K2.u4093 from rfl, allE_node, arows2046, irow4094, arows4093]
  all_goals rfl

theorem atot4094 : totK PD2M8K2 D2M8K2.u4094 = [98634648751111, 601436179886015, 1317466341079292, 1206616284816963, 408823147178917, 41270726337058, 1098333251268, 1369150432] := by
  rw [show D2M8K2.u4094 = KTree.node D2M8K2.u2046 (nat_lit 4652561) (nat_lit 2211249437) (nat_lit 0) D2M8K2.u4093 from rfl, totK_node, atot2046, atot4093]
  decide +kernel

theorem arows8189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8189 = true := by
  rw [show D2M8K2.u8189 = KTree.node D2M8K2.u6141 (nat_lit 12961164) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u8188 from rfl, allE_node, arows6141, irow8189, arows8188]
  all_goals rfl

theorem atot8189 : totK PD2M8K2 D2M8K2.u8189 = [49311507975402, 366931346379181, 1033710093411094, 1329255605242563, 741685611449789, 151853020583104, 9876683514574, 153690039162] := by
  rw [show D2M8K2.u8189 = KTree.node D2M8K2.u6141 (nat_lit 12961164) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u8188 from rfl, totK_node, atot6141, atot8188]
  decide +kernel

theorem arows12285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12285 = true := by
  rw [show D2M8K2.u12285 = KTree.node D2M8K2.u10237 (nat_lit 22453973) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u12284 from rfl, allE_node, arows10237, irow12285, arows12284]
  all_goals rfl

theorem atot12285 : totK PD2M8K2 D2M8K2.u12285 = [95728676431358, 572647881997286, 1255706520865479, 1205141275852070, 479099158018510, 66816548085369, 3005848893764, 35010448111] := by
  rw [show D2M8K2.u12285 = KTree.node D2M8K2.u10237 (nat_lit 22453973) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u12284 from rfl, totK_node, atot10237, atot12284]
  decide +kernel

theorem arows16380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16380 = true := by
  rw [show D2M8K2.u16380 = KTree.node D2M8K2.u14332 (nat_lit 31159865) (nat_lit 1177676325) (nat_lit 0) D2M8K2.u16379 from rfl, allE_node, arows14332, irow16380, arows16379]
  all_goals rfl

theorem atot16380 : totK PD2M8K2 D2M8K2.u16380 = [52211144769242, 397058944647449, 1104813541889727, 1344863266428107, 664907598412671, 110416856091651, 5710574198669, 72593022950] := by
  rw [show D2M8K2.u16380 = KTree.node D2M8K2.u14332 (nat_lit 31159865) (nat_lit 1177676325) (nat_lit 0) D2M8K2.u16379 from rfl, totK_node, atot14332, atot16379]
  decide +kernel

theorem arows8190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8190 = true := by
  rw [show D2M8K2.u8190 = KTree.node D2M8K2.u4094 (nat_lit 9584473) (nat_lit 1389147864) (nat_lit 0) D2M8K2.u8189 from rfl, allE_node, arows4094, irow8190, arows8189]
  all_goals rfl

theorem atot8190 : totK PD2M8K2 D2M8K2.u8190 = [147946156726513, 968367526265196, 2351177823638250, 2535871890059526, 1150508758628706, 193123746920162, 10975016765842, 155059189594] := by
  rw [show D2M8K2.u8190 = KTree.node D2M8K2.u4094 (nat_lit 9584473) (nat_lit 1389147864) (nat_lit 0) D2M8K2.u8189 from rfl, totK_node, atot4094, atot8189]
  decide +kernel

theorem arows16381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16381 = true := by
  rw [show D2M8K2.u16381 = KTree.node D2M8K2.u12285 (nat_lit 26016515) (nat_lit 2890378161) (nat_lit 0) D2M8K2.u16380 from rfl, allE_node, arows12285, irow16381, arows16380]
  all_goals rfl

theorem atot16381 : totK PD2M8K2 D2M8K2.u16381 = [147939821200600, 969706826644735, 2360522953133367, 2550004542280177, 1144006756431181, 177233404177020, 8716423092433, 107603471061] := by
  rw [show D2M8K2.u16381 = KTree.node D2M8K2.u12285 (nat_lit 26016515) (nat_lit 2890378161) (nat_lit 0) D2M8K2.u16380 from rfl, totK_node, atot12285, atot16380]
  decide +kernel

theorem arows16382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16382 = true := by
  rw [show D2M8K2.u16382 = KTree.node D2M8K2.u8190 (nat_lit 17636543) (nat_lit 2114062433) (nat_lit 0) D2M8K2.u16381 from rfl, allE_node, arows8190, irow16382, arows16381]
  all_goals rfl

theorem atot16382 : totK PD2M8K2 D2M8K2.u16382 = [295885977927113, 1938074352909931, 4711700776771617, 5085876432339703, 2294517629122320, 370357151097182, 19691439858275, 262662660655] := by
  rw [show D2M8K2.u16382 = KTree.node D2M8K2.u8190 (nat_lit 17636543) (nat_lit 2114062433) (nat_lit 0) D2M8K2.u16381 from rfl, totK_node, atot8190, atot16381]
  decide +kernel

end QECKChecks.D2M8K2
