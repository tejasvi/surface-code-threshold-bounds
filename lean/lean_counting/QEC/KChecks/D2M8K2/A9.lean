import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A8

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows10795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10795 = true := by
  rw [show D2M8K2.u10795 = KTree.node D2M8K2.t10800 (nat_lit 23436238) (nat_lit 3023972472) (nat_lit 0) D2M8K2.t10801 from rfl, allE_node, rows10800, irow10795, rows10801]
  all_goals rfl

theorem atot10795 : totK PD2M8K2 D2M8K2.u10795 = [0, 348582227776, 930419232757, 513144410372, 33488006337, 0, 0, 0] := by
  rw [show D2M8K2.u10795 = KTree.node D2M8K2.t10800 (nat_lit 23436238) (nat_lit 3023972472) (nat_lit 0) D2M8K2.t10801 from rfl, totK_node, tot10800, tot10801]
  decide +kernel

theorem arows10796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10796 = true := by
  rw [show D2M8K2.u10796 = KTree.node D2M8K2.t10802 (nat_lit 23437694) (nat_lit 2472646182) (nat_lit 0) D2M8K2.t10803 from rfl, allE_node, rows10802, irow10796, rows10803]
  all_goals rfl

theorem atot10796 : totK PD2M8K2 D2M8K2.u10796 = [0, 0, 385334577388, 944338028952, 451494052556, 30804453458, 0, 0] := by
  rw [show D2M8K2.u10796 = KTree.node D2M8K2.t10802 (nat_lit 23437694) (nat_lit 2472646182) (nat_lit 0) D2M8K2.t10803 from rfl, totK_node, tot10802, tot10803]
  decide +kernel

theorem arows10798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10798 = true := by
  rw [show D2M8K2.u10798 = KTree.node D2M8K2.t10804 (nat_lit 23439071) (nat_lit 2033526733) (nat_lit 0) D2M8K2.t10805 from rfl, allE_node, rows10804, irow10798, rows10805]
  all_goals rfl

theorem atot10798 : totK PD2M8K2 D2M8K2.u10798 = [0, 298308119120, 816044984886, 572963348201, 139219396623, 6804944647, 0, 0] := by
  rw [show D2M8K2.u10798 = KTree.node D2M8K2.t10804 (nat_lit 23439071) (nat_lit 2033526733) (nat_lit 0) D2M8K2.t10805 from rfl, totK_node, tot10804, tot10805]
  decide +kernel

theorem arows10799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10799 = true := by
  rw [show D2M8K2.u10799 = KTree.node D2M8K2.t10806 (nat_lit 23440718) (nat_lit 3856126188) (nat_lit 0) D2M8K2.t10807 from rfl, allE_node, rows10806, irow10799, rows10807]
  all_goals rfl

theorem atot10799 : totK PD2M8K2 D2M8K2.u10799 = [0, 87333051614, 577676671439, 876092850758, 248333732346, 9479825071, 0, 0] := by
  rw [show D2M8K2.u10799 = KTree.node D2M8K2.t10806 (nat_lit 23440718) (nat_lit 3856126188) (nat_lit 0) D2M8K2.t10807 from rfl, totK_node, tot10806, tot10807]
  decide +kernel

theorem arows10802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10802 = true := by
  rw [show D2M8K2.u10802 = KTree.node D2M8K2.t10808 (nat_lit 23442617) (nat_lit 1161529178) (nat_lit 0) D2M8K2.t10809 from rfl, allE_node, rows10808, irow10802, rows10809]
  all_goals rfl

theorem atot10802 : totK PD2M8K2 D2M8K2.u10802 = [0, 353549074048, 914136013016, 524774602068, 48982046169, 0, 0, 0] := by
  rw [show D2M8K2.u10802 = KTree.node D2M8K2.t10808 (nat_lit 23442617) (nat_lit 1161529178) (nat_lit 0) D2M8K2.t10809 from rfl, totK_node, tot10808, tot10809]
  decide +kernel

theorem arows10803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10803 = true := by
  rw [show D2M8K2.u10803 = KTree.node D2M8K2.t10810 (nat_lit 23444186) (nat_lit 4116261873) (nat_lit 0) D2M8K2.t10811 from rfl, allE_node, rows10810, irow10803, rows10811]
  all_goals rfl

theorem atot10803 : totK PD2M8K2 D2M8K2.u10803 = [0, 59913483018, 540243963819, 897425021113, 278794717037, 13204088881, 0, 0] := by
  rw [show D2M8K2.u10803 = KTree.node D2M8K2.t10810 (nat_lit 23444186) (nat_lit 4116261873) (nat_lit 0) D2M8K2.t10811 from rfl, totK_node, tot10810, tot10811]
  decide +kernel

theorem arows10805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10805 = true := by
  rw [show D2M8K2.u10805 = KTree.node D2M8K2.t10812 (nat_lit 23446272) (nat_lit 2875189748) (nat_lit 0) D2M8K2.t10813 from rfl, allE_node, rows10812, irow10805, rows10813]
  all_goals rfl

theorem atot10805 : totK PD2M8K2 D2M8K2.u10805 = [0, 330086036772, 913503632388, 557792891088, 59653854356, 0, 0, 0] := by
  rw [show D2M8K2.u10805 = KTree.node D2M8K2.t10812 (nat_lit 23446272) (nat_lit 2875189748) (nat_lit 0) D2M8K2.t10813 from rfl, totK_node, tot10812, tot10813]
  decide +kernel

theorem arows10806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10806 = true := by
  rw [show D2M8K2.u10806 = KTree.node D2M8K2.t10814 (nat_lit 23448500) (nat_lit 3702992746) (nat_lit 0) D2M8K2.t10815 from rfl, allE_node, rows10814, irow10806, rows10815]
  all_goals rfl

theorem atot10806 : totK PD2M8K2 D2M8K2.u10806 = [0, 161977806534, 726729702893, 809238474245, 150833240032, 2804045914, 0, 0] := by
  rw [show D2M8K2.u10806 = KTree.node D2M8K2.t10814 (nat_lit 23448500) (nat_lit 3702992746) (nat_lit 0) D2M8K2.t10815 from rfl, totK_node, tot10814, tot10815]
  decide +kernel

theorem arows10812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10812 = true := by
  rw [show D2M8K2.u10812 = KTree.node D2M8K2.t10816 (nat_lit 23450085) (nat_lit 1412378762) (nat_lit 0) D2M8K2.t10817 from rfl, allE_node, rows10816, irow10812, rows10817]
  all_goals rfl

theorem atot10812 : totK PD2M8K2 D2M8K2.u10812 = [0, 265593258125, 802251898267, 630035507293, 107543203308, 1267860612, 0, 0] := by
  rw [show D2M8K2.u10812 = KTree.node D2M8K2.t10816 (nat_lit 23450085) (nat_lit 1412378762) (nat_lit 0) D2M8K2.t10817 from rfl, totK_node, tot10816, tot10817]
  decide +kernel

theorem arows10813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10813 = true := by
  rw [show D2M8K2.u10813 = KTree.node D2M8K2.t10818 (nat_lit 23451770) (nat_lit 3725889655) (nat_lit 0) D2M8K2.t10819 from rfl, allE_node, rows10818, irow10813, rows10819]
  all_goals rfl

theorem atot10813 : totK PD2M8K2 D2M8K2.u10813 = [0, 0, 418034366813, 952898757604, 393261901710, 31232626135, 0, 0] := by
  rw [show D2M8K2.u10813 = KTree.node D2M8K2.t10818 (nat_lit 23451770) (nat_lit 3725889655) (nat_lit 0) D2M8K2.t10819 from rfl, totK_node, tot10818, tot10819]
  decide +kernel

theorem arows10815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10815 = true := by
  rw [show D2M8K2.u10815 = KTree.node D2M8K2.t10820 (nat_lit 23456958) (nat_lit 4061456727) (nat_lit 0) D2M8K2.t10821 from rfl, allE_node, rows10820, irow10815, rows10821]
  all_goals rfl

theorem atot10815 : totK PD2M8K2 D2M8K2.u10815 = [0, 0, 347675481477, 925011343315, 526477553544, 30410694320, 0, 0] := by
  rw [show D2M8K2.u10815 = KTree.node D2M8K2.t10820 (nat_lit 23456958) (nat_lit 4061456727) (nat_lit 0) D2M8K2.t10821 from rfl, totK_node, tot10820, tot10821]
  decide +kernel

theorem arows10816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10816 = true := by
  rw [show D2M8K2.u10816 = KTree.node D2M8K2.t10822 (nat_lit 23458442) (nat_lit 3982115117) (nat_lit 0) D2M8K2.t10823 from rfl, allE_node, rows10822, irow10816, rows10823]
  all_goals rfl

theorem atot10816 : totK PD2M8K2 D2M8K2.u10816 = [0, 0, 0, 412011090381, 947686246800, 412012231364, 26567849899, 0] := by
  rw [show D2M8K2.u10816 = KTree.node D2M8K2.t10822 (nat_lit 23458442) (nat_lit 3982115117) (nat_lit 0) D2M8K2.t10823 from rfl, totK_node, tot10822, tot10823]
  decide +kernel

theorem arows10819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10819 = true := by
  rw [show D2M8K2.u10819 = KTree.node D2M8K2.t10824 (nat_lit 23459839) (nat_lit 2277701783) (nat_lit 0) D2M8K2.t10825 from rfl, allE_node, rows10824, irow10819, rows10825]
  all_goals rfl

theorem atot10819 : totK PD2M8K2 D2M8K2.u10819 = [0, 0, 313218107063, 819505380417, 550418180233, 125955531182, 6524090962, 0] := by
  rw [show D2M8K2.u10819 = KTree.node D2M8K2.t10824 (nat_lit 23459839) (nat_lit 2277701783) (nat_lit 0) D2M8K2.t10825 from rfl, totK_node, tot10824, tot10825]
  decide +kernel

theorem arows10820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10820 = true := by
  rw [show D2M8K2.u10820 = KTree.node D2M8K2.t10826 (nat_lit 23461694) (nat_lit 3821288067) (nat_lit 0) D2M8K2.t10827 from rfl, allE_node, rows10826, irow10820, rows10827]
  all_goals rfl

theorem atot10820 : totK PD2M8K2 D2M8K2.u10820 = [0, 0, 139147128951, 733900472179, 807680588308, 132089755279, 1547833102, 0] := by
  rw [show D2M8K2.u10820 = KTree.node D2M8K2.t10826 (nat_lit 23461694) (nat_lit 3821288067) (nat_lit 0) D2M8K2.t10827 from rfl, totK_node, tot10826, tot10827]
  decide +kernel

theorem arows10822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10822 = true := by
  rw [show D2M8K2.u10822 = KTree.node D2M8K2.t10828 (nat_lit 23463892) (nat_lit 2433501766) (nat_lit 0) D2M8K2.t10829 from rfl, allE_node, rows10828, irow10822, rows10829]
  all_goals rfl

theorem atot10822 : totK PD2M8K2 D2M8K2.u10822 = [0, 0, 348589735848, 917345191256, 525919419152, 45629479002, 0, 0] := by
  rw [show D2M8K2.u10822 = KTree.node D2M8K2.t10828 (nat_lit 23463892) (nat_lit 2433501766) (nat_lit 0) D2M8K2.t10829 from rfl, totK_node, tot10828, tot10829]
  decide +kernel

theorem arows10823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10823 = true := by
  rw [show D2M8K2.u10823 = KTree.node D2M8K2.t10830 (nat_lit 23465732) (nat_lit 3279896291) (nat_lit 0) D2M8K2.t10831 from rfl, allE_node, rows10830, irow10823, rows10831]
  all_goals rfl

theorem atot10823 : totK PD2M8K2 D2M8K2.u10823 = [0, 0, 89442567638, 616274476585, 885140748960, 217985653977, 5218872685, 0] := by
  rw [show D2M8K2.u10823 = KTree.node D2M8K2.t10830 (nat_lit 23465732) (nat_lit 3279896291) (nat_lit 0) D2M8K2.t10831 from rfl, totK_node, tot10830, tot10831]
  decide +kernel

theorem arows10827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10827 = true := by
  rw [show D2M8K2.u10827 = KTree.node D2M8K2.t10832 (nat_lit 23467450) (nat_lit 2545889234) (nat_lit 0) D2M8K2.t10833 from rfl, allE_node, rows10832, irow10827, rows10833]
  all_goals rfl

theorem atot10827 : totK PD2M8K2 D2M8K2.u10827 = [0, 0, 239764877979, 876240447759, 667324360557, 65361969826, 0, 0] := by
  rw [show D2M8K2.u10827 = KTree.node D2M8K2.t10832 (nat_lit 23467450) (nat_lit 2545889234) (nat_lit 0) D2M8K2.t10833 from rfl, totK_node, tot10832, tot10833]
  decide +kernel

theorem arows10828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10828 = true := by
  rw [show D2M8K2.u10828 = KTree.node D2M8K2.t10834 (nat_lit 23470115) (nat_lit 2970155676) (nat_lit 0) D2M8K2.t10835 from rfl, allE_node, rows10834, irow10828, rows10835]
  all_goals rfl

theorem atot10828 : totK PD2M8K2 D2M8K2.u10828 = [0, 0, 328853834180, 827866284930, 565133238864, 91953122894, 1415142070, 0] := by
  rw [show D2M8K2.u10828 = KTree.node D2M8K2.t10834 (nat_lit 23470115) (nat_lit 2970155676) (nat_lit 0) D2M8K2.t10835 from rfl, totK_node, tot10834, tot10835]
  decide +kernel

theorem arows10830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10830 = true := by
  rw [show D2M8K2.u10830 = KTree.node D2M8K2.t10836 (nat_lit 23471772) (nat_lit 2381903620) (nat_lit 0) D2M8K2.t10837 from rfl, allE_node, rows10836, irow10830, rows10837]
  all_goals rfl

theorem atot10830 : totK PD2M8K2 D2M8K2.u10830 = [0, 0, 92755880245, 677438429816, 840975971385, 178739424417, 2484078857, 0] := by
  rw [show D2M8K2.u10830 = KTree.node D2M8K2.t10836 (nat_lit 23471772) (nat_lit 2381903620) (nat_lit 0) D2M8K2.t10837 from rfl, totK_node, tot10836, tot10837]
  decide +kernel

theorem arows10831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10831 = true := by
  rw [show D2M8K2.u10831 = KTree.node D2M8K2.t10838 (nat_lit 23473766) (nat_lit 4004283025) (nat_lit 0) D2M8K2.t10839 from rfl, allE_node, rows10838, irow10831, rows10839]
  all_goals rfl

theorem atot10831 : totK PD2M8K2 D2M8K2.u10831 = [0, 309149030834, 732272659673, 381453412101, 235277569649, 109855808566, 6818291842, 0] := by
  rw [show D2M8K2.u10831 = KTree.node D2M8K2.t10838 (nat_lit 23473766) (nat_lit 4004283025) (nat_lit 0) D2M8K2.t10839 from rfl, totK_node, tot10838, tot10839]
  decide +kernel

theorem arows10834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10834 = true := by
  rw [show D2M8K2.u10834 = KTree.node D2M8K2.t10840 (nat_lit 23475102) (nat_lit 3795066915) (nat_lit 0) D2M8K2.t10841 from rfl, allE_node, rows10840, irow10834, rows10841]
  all_goals rfl

theorem atot10834 : totK PD2M8K2 D2M8K2.u10834 = [0, 95314668664, 669817927047, 880802483140, 144299189771, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10834 = KTree.node D2M8K2.t10840 (nat_lit 23475102) (nat_lit 3795066915) (nat_lit 0) D2M8K2.t10841 from rfl, totK_node, tot10840, tot10841]
  decide +kernel

theorem arows10835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10835 = true := by
  rw [show D2M8K2.u10835 = KTree.node D2M8K2.t10842 (nat_lit 23477448) (nat_lit 3248309775) (nat_lit 0) D2M8K2.t10843 from rfl, allE_node, rows10842, irow10835, rows10843]
  all_goals rfl

theorem atot10835 : totK PD2M8K2 D2M8K2.u10835 = [0, 399885794023, 940883041488, 471402131431, 36995264978, 0, 0, 0] := by
  rw [show D2M8K2.u10835 = KTree.node D2M8K2.t10842 (nat_lit 23477448) (nat_lit 3248309775) (nat_lit 0) D2M8K2.t10843 from rfl, totK_node, tot10842, tot10843]
  decide +kernel

theorem arows10837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10837 = true := by
  rw [show D2M8K2.u10837 = KTree.node D2M8K2.t10844 (nat_lit 23479015) (nat_lit 1092048241) (nat_lit 128) D2M8K2.t10845 from rfl, allE_node, rows10844, irow10837, rows10845]
  all_goals rfl

theorem atot10837 : totK PD2M8K2 D2M8K2.u10837 = [0, 0, 435859165914, 937047477505, 413798528194, 26780188391, 0, 0] := by
  rw [show D2M8K2.u10837 = KTree.node D2M8K2.t10844 (nat_lit 23479015) (nat_lit 1092048241) (nat_lit 128) D2M8K2.t10845 from rfl, totK_node, tot10844, tot10845]
  decide +kernel

theorem arows10838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10838 = true := by
  rw [show D2M8K2.u10838 = KTree.node D2M8K2.t10846 (nat_lit 23480427) (nat_lit 3687369073) (nat_lit 0) D2M8K2.t10847 from rfl, allE_node, rows10846, irow10838, rows10847]
  all_goals rfl

theorem atot10838 : totK PD2M8K2 D2M8K2.u10838 = [0, 300095866282, 789166429338, 574200986836, 143523857352, 6800370819, 0, 0] := by
  rw [show D2M8K2.u10838 = KTree.node D2M8K2.t10846 (nat_lit 23480427) (nat_lit 3687369073) (nat_lit 0) D2M8K2.t10847 from rfl, totK_node, tot10846, tot10847]
  decide +kernel

theorem arows10843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10843 = true := by
  rw [show D2M8K2.u10843 = KTree.node D2M8K2.t10848 (nat_lit 23481908) (nat_lit 3519671186) (nat_lit 0) D2M8K2.t10849 from rfl, allE_node, rows10848, irow10843, rows10849]
  all_goals rfl

theorem atot10843 : totK PD2M8K2 D2M8K2.u10843 = [0, 126136851789, 650089245239, 805351884298, 207525977889, 9587713104, 0, 0] := by
  rw [show D2M8K2.u10843 = KTree.node D2M8K2.t10848 (nat_lit 23481908) (nat_lit 3519671186) (nat_lit 0) D2M8K2.t10849 from rfl, totK_node, tot10848, tot10849]
  decide +kernel

theorem arows10844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10844 = true := by
  rw [show D2M8K2.u10844 = KTree.node D2M8K2.t10850 (nat_lit 23490793) (nat_lit 1041930700) (nat_lit 0) D2M8K2.t10851 from rfl, allE_node, rows10850, irow10844, rows10851]
  all_goals rfl

theorem atot10844 : totK PD2M8K2 D2M8K2.u10844 = [0, 296703418010, 866608377488, 601845640097, 67526500033, 0, 0, 0] := by
  rw [show D2M8K2.u10844 = KTree.node D2M8K2.t10850 (nat_lit 23490793) (nat_lit 1041930700) (nat_lit 0) D2M8K2.t10851 from rfl, totK_node, tot10850, tot10851]
  decide +kernel

theorem arows10846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10846 = true := by
  rw [show D2M8K2.u10846 = KTree.node D2M8K2.t10852 (nat_lit 23492268) (nat_lit 3139076412) (nat_lit 0) D2M8K2.t10853 from rfl, allE_node, rows10852, irow10846, rows10853]
  all_goals rfl

theorem atot10846 : totK PD2M8K2 D2M8K2.u10846 = [0, 130424248025, 650946744411, 812474929056, 202290806882, 4967996017, 0, 0] := by
  rw [show D2M8K2.u10846 = KTree.node D2M8K2.t10852 (nat_lit 23492268) (nat_lit 3139076412) (nat_lit 0) D2M8K2.t10853 from rfl, totK_node, tot10852, tot10853]
  decide +kernel

theorem arows10847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10847 = true := by
  rw [show D2M8K2.u10847 = KTree.node D2M8K2.t10854 (nat_lit 23493967) (nat_lit 2409231177) (nat_lit 0) D2M8K2.t10855 from rfl, allE_node, rows10854, irow10847, rows10855]
  all_goals rfl

theorem atot10847 : totK PD2M8K2 D2M8K2.u10847 = [0, 0, 390472880524, 958668783821, 406690498028, 22690954046, 0, 0] := by
  rw [show D2M8K2.u10847 = KTree.node D2M8K2.t10854 (nat_lit 23493967) (nat_lit 2409231177) (nat_lit 0) D2M8K2.t10855 from rfl, totK_node, tot10854, tot10855]
  decide +kernel

theorem arows10850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10850 = true := by
  rw [show D2M8K2.u10850 = KTree.node D2M8K2.t10856 (nat_lit 23495668) (nat_lit 3977858031) (nat_lit 0) D2M8K2.t10857 from rfl, allE_node, rows10856, irow10850, rows10857]
  all_goals rfl

theorem atot10850 : totK PD2M8K2 D2M8K2.u10850 = [0, 0, 153087167813, 765963332914, 726814779161, 82960039176, 1206465782, 0] := by
  rw [show D2M8K2.u10850 = KTree.node D2M8K2.t10856 (nat_lit 23495668) (nat_lit 3977858031) (nat_lit 0) D2M8K2.t10857 from rfl, totK_node, tot10856, tot10857]
  decide +kernel

theorem arows10851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10851 = true := by
  rw [show D2M8K2.u10851 = KTree.node D2M8K2.t10858 (nat_lit 23498075) (nat_lit 2300054644) (nat_lit 0) D2M8K2.t10859 from rfl, allE_node, rows10858, irow10851, rows10859]
  all_goals rfl

theorem atot10851 : totK PD2M8K2 D2M8K2.u10851 = [0, 0, 356086488672, 932138638378, 512824726360, 41248096935, 0, 0] := by
  rw [show D2M8K2.u10851 = KTree.node D2M8K2.t10858 (nat_lit 23498075) (nat_lit 2300054644) (nat_lit 0) D2M8K2.t10859 from rfl, totK_node, tot10858, tot10859]
  decide +kernel

theorem arows10853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10853 = true := by
  rw [show D2M8K2.u10853 = KTree.node D2M8K2.t10860 (nat_lit 23501189) (nat_lit 2316387304) (nat_lit 0) D2M8K2.t10861 from rfl, allE_node, rows10860, irow10853, rows10861]
  all_goals rfl

theorem atot10853 : totK PD2M8K2 D2M8K2.u10853 = [0, 0, 368942846988, 930176818824, 473928245374, 36117821407, 0, 0] := by
  rw [show D2M8K2.u10853 = KTree.node D2M8K2.t10860 (nat_lit 23501189) (nat_lit 2316387304) (nat_lit 0) D2M8K2.t10861 from rfl, totK_node, tot10860, tot10861]
  decide +kernel

theorem arows10854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10854 = true := by
  rw [show D2M8K2.u10854 = KTree.node D2M8K2.t10862 (nat_lit 23502720) (nat_lit 3480946997) (nat_lit 0) D2M8K2.t10863 from rfl, allE_node, rows10862, irow10854, rows10863]
  all_goals rfl

theorem atot10854 : totK PD2M8K2 D2M8K2.u10854 = [0, 0, 103563397318, 677989806982, 804549247719, 166867579290, 5395128787, 0] := by
  rw [show D2M8K2.u10854 = KTree.node D2M8K2.t10862 (nat_lit 23502720) (nat_lit 3480946997) (nat_lit 0) D2M8K2.t10863 from rfl, totK_node, tot10862, tot10863]
  decide +kernel

theorem arows10858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10858 = true := by
  rw [show D2M8K2.u10858 = KTree.node D2M8K2.t10864 (nat_lit 23511680) (nat_lit 2547652087) (nat_lit 0) D2M8K2.t10865 from rfl, allE_node, rows10864, irow10858, rows10865]
  all_goals rfl

theorem atot10858 : totK PD2M8K2 D2M8K2.u10858 = [0, 0, 346589521515, 911373313319, 509152957120, 42369163799, 0, 0] := by
  rw [show D2M8K2.u10858 = KTree.node D2M8K2.t10864 (nat_lit 23511680) (nat_lit 2547652087) (nat_lit 0) D2M8K2.t10865 from rfl, totK_node, tot10864, tot10865]
  decide +kernel

theorem arows10859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10859 = true := by
  rw [show D2M8K2.u10859 = KTree.node D2M8K2.t10866 (nat_lit 23515220) (nat_lit 3086047140) (nat_lit 0) D2M8K2.t10867 from rfl, allE_node, rows10866, irow10859, rows10867]
  all_goals rfl

theorem atot10859 : totK PD2M8K2 D2M8K2.u10859 = [0, 302668140502, 783087804877, 537208216127, 159179929015, 13566920432, 0, 0] := by
  rw [show D2M8K2.u10859 = KTree.node D2M8K2.t10866 (nat_lit 23515220) (nat_lit 3086047140) (nat_lit 0) D2M8K2.t10867 from rfl, totK_node, tot10866, tot10867]
  decide +kernel

theorem arows10861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10861 = true := by
  rw [show D2M8K2.u10861 = KTree.node D2M8K2.t10868 (nat_lit 23516486) (nat_lit 2716690233) (nat_lit 0) D2M8K2.t10869 from rfl, allE_node, rows10868, irow10861, rows10869]
  all_goals rfl

theorem atot10861 : totK PD2M8K2 D2M8K2.u10861 = [0, 105378643387, 694927312722, 843288147680, 139570065062, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10861 = KTree.node D2M8K2.t10868 (nat_lit 23516486) (nat_lit 2716690233) (nat_lit 0) D2M8K2.t10869 from rfl, totK_node, tot10868, tot10869]
  decide +kernel

theorem arows10862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10862 = true := by
  rw [show D2M8K2.u10862 = KTree.node D2M8K2.t10870 (nat_lit 23518869) (nat_lit 1021638022) (nat_lit 0) D2M8K2.t10871 from rfl, allE_node, rows10870, irow10862, rows10871]
  all_goals rfl

theorem atot10862 : totK PD2M8K2 D2M8K2.u10862 = [0, 345381350797, 895152698170, 546373972261, 52621824319, 0, 0, 0] := by
  rw [show D2M8K2.u10862 = KTree.node D2M8K2.t10870 (nat_lit 23518869) (nat_lit 1021638022) (nat_lit 0) D2M8K2.t10871 from rfl, totK_node, tot10870, tot10871]
  decide +kernel

theorem arows10865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10865 = true := by
  rw [show D2M8K2.u10865 = KTree.node D2M8K2.t10872 (nat_lit 23520363) (nat_lit 3674679839) (nat_lit 0) D2M8K2.t10873 from rfl, allE_node, rows10872, irow10865, rows10873]
  all_goals rfl

theorem atot10865 : totK PD2M8K2 D2M8K2.u10865 = [0, 74089972484, 513135773220, 836965865182, 374667775447, 27811546229, 0, 0] := by
  rw [show D2M8K2.u10865 = KTree.node D2M8K2.t10872 (nat_lit 23520363) (nat_lit 3674679839) (nat_lit 0) D2M8K2.t10873 from rfl, totK_node, tot10872, tot10873]
  decide +kernel

theorem arows10866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10866 = true := by
  rw [show D2M8K2.u10866 = KTree.node D2M8K2.t10874 (nat_lit 23525129) (nat_lit 1564729346) (nat_lit 0) D2M8K2.t10875 from rfl, allE_node, rows10874, irow10866, rows10875]
  all_goals rfl

theorem atot10866 : totK PD2M8K2 D2M8K2.u10866 = [0, 268541825635, 721339088430, 631344907200, 202870941085, 8209296672, 0, 0] := by
  rw [show D2M8K2.u10866 = KTree.node D2M8K2.t10874 (nat_lit 23525129) (nat_lit 1564729346) (nat_lit 0) D2M8K2.t10875 from rfl, totK_node, tot10874, tot10875]
  decide +kernel

theorem arows10868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10868 = true := by
  rw [show D2M8K2.u10868 = KTree.node D2M8K2.t10876 (nat_lit 23526607) (nat_lit 2225959971) (nat_lit 0) D2M8K2.t10877 from rfl, allE_node, rows10876, irow10868, rows10877]
  all_goals rfl

theorem atot10868 : totK PD2M8K2 D2M8K2.u10868 = [0, 172848159982, 764317336598, 752429306767, 126082292229, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10868 = KTree.node D2M8K2.t10876 (nat_lit 23526607) (nat_lit 2225959971) (nat_lit 0) D2M8K2.t10877 from rfl, totK_node, tot10876, tot10877]
  decide +kernel

theorem arows10869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10869 = true := by
  rw [show D2M8K2.u10869 = KTree.node D2M8K2.t10878 (nat_lit 23528284) (nat_lit 3661903846) (nat_lit 0) D2M8K2.t10879 from rfl, allE_node, rows10878, irow10869, rows10879]
  all_goals rfl

theorem atot10869 : totK PD2M8K2 D2M8K2.u10869 = [0, 180188373297, 641656078066, 735671060275, 222895812690, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10869 = KTree.node D2M8K2.t10878 (nat_lit 23528284) (nat_lit 3661903846) (nat_lit 0) D2M8K2.t10879 from rfl, totK_node, tot10878, tot10879]
  decide +kernel

theorem arows10876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10876 = true := by
  rw [show D2M8K2.u10876 = KTree.node D2M8K2.t10880 (nat_lit 23530246) (nat_lit 2400429954) (nat_lit 0) D2M8K2.t10881 from rfl, allE_node, rows10880, irow10876, rows10881]
  all_goals rfl

theorem atot10876 : totK PD2M8K2 D2M8K2.u10876 = [0, 159361347106, 762813871643, 780486505500, 114467711071, 1096505104, 0, 0] := by
  rw [show D2M8K2.u10876 = KTree.node D2M8K2.t10880 (nat_lit 23530246) (nat_lit 2400429954) (nat_lit 0) D2M8K2.t10881 from rfl, totK_node, tot10880, tot10881]
  decide +kernel

theorem arows10877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10877 = true := by
  rw [show D2M8K2.u10877 = KTree.node D2M8K2.t10882 (nat_lit 23532379) (nat_lit 1701508204) (nat_lit 0) D2M8K2.t10883 from rfl, allE_node, rows10882, irow10877, rows10883]
  all_goals rfl

theorem atot10877 : totK PD2M8K2 D2M8K2.u10877 = [0, 335155343445, 847290762861, 530234792021, 97803372327, 3884009855, 0, 0] := by
  rw [show D2M8K2.u10877 = KTree.node D2M8K2.t10882 (nat_lit 23532379) (nat_lit 1701508204) (nat_lit 0) D2M8K2.t10883 from rfl, totK_node, tot10882, tot10883]
  decide +kernel

theorem arows10879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10879 = true := by
  rw [show D2M8K2.u10879 = KTree.node D2M8K2.t10884 (nat_lit 23533877) (nat_lit 1081193286) (nat_lit 0) D2M8K2.t10885 from rfl, allE_node, rows10884, irow10879, rows10885]
  all_goals rfl

theorem atot10879 : totK PD2M8K2 D2M8K2.u10879 = [0, 92934196222, 605129828326, 873564129842, 225810653494, 4965269624, 0, 0] := by
  rw [show D2M8K2.u10879 = KTree.node D2M8K2.t10884 (nat_lit 23533877) (nat_lit 1081193286) (nat_lit 0) D2M8K2.t10885 from rfl, totK_node, tot10884, tot10885]
  decide +kernel

theorem arows10880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10880 = true := by
  rw [show D2M8K2.u10880 = KTree.node D2M8K2.t10886 (nat_lit 23535524) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t10887 from rfl, allE_node, rows10886, irow10880, rows10887]
  all_goals rfl

theorem atot10880 : totK PD2M8K2 D2M8K2.u10880 = [0, 0, 352656089948, 940460868741, 448172931999, 28160378321, 0, 0] := by
  rw [show D2M8K2.u10880 = KTree.node D2M8K2.t10886 (nat_lit 23535524) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t10887 from rfl, totK_node, tot10886, tot10887]
  decide +kernel

theorem arows10883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10883 = true := by
  rw [show D2M8K2.u10883 = KTree.node D2M8K2.t10888 (nat_lit 23537181) (nat_lit 1420372386) (nat_lit 0) D2M8K2.t10889 from rfl, allE_node, rows10888, irow10883, rows10889]
  all_goals rfl

theorem atot10883 : totK PD2M8K2 D2M8K2.u10883 = [0, 0, 146753975262, 732933125452, 751631812234, 104309358406, 1239866073, 0] := by
  rw [show D2M8K2.u10883 = KTree.node D2M8K2.t10888 (nat_lit 23537181) (nat_lit 1420372386) (nat_lit 0) D2M8K2.t10889 from rfl, totK_node, tot10888, tot10889]
  decide +kernel

theorem arows10884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10884 = true := by
  rw [show D2M8K2.u10884 = KTree.node D2M8K2.t10890 (nat_lit 23539636) (nat_lit 3239332608) (nat_lit 0) D2M8K2.t10891 from rfl, allE_node, rows10890, irow10884, rows10891]
  all_goals rfl

theorem atot10884 : totK PD2M8K2 D2M8K2.u10884 = [0, 0, 352679571477, 927262388983, 517263654125, 43573323795, 0, 0] := by
  rw [show D2M8K2.u10884 = KTree.node D2M8K2.t10890 (nat_lit 23539636) (nat_lit 3239332608) (nat_lit 0) D2M8K2.t10891 from rfl, totK_node, tot10890, tot10891]
  decide +kernel

theorem arows10886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10886 = true := by
  rw [show D2M8K2.u10886 = KTree.node D2M8K2.t10892 (nat_lit 23546091) (nat_lit 3704293716) (nat_lit 0) D2M8K2.t10893 from rfl, allE_node, rows10892, irow10886, rows10893]
  all_goals rfl

theorem atot10886 : totK PD2M8K2 D2M8K2.u10886 = [0, 0, 369043687806, 918095160173, 497287388397, 40091399552, 0, 0] := by
  rw [show D2M8K2.u10886 = KTree.node D2M8K2.t10892 (nat_lit 23546091) (nat_lit 3704293716) (nat_lit 0) D2M8K2.t10893 from rfl, totK_node, tot10892, tot10893]
  decide +kernel

theorem arows10887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10887 = true := by
  rw [show D2M8K2.u10887 = KTree.node D2M8K2.t10894 (nat_lit 23547547) (nat_lit 2239021588) (nat_lit 0) D2M8K2.t10895 from rfl, allE_node, rows10894, irow10887, rows10895]
  all_goals rfl

theorem atot10887 : totK PD2M8K2 D2M8K2.u10887 = [0, 0, 136668606607, 661681667949, 763950198335, 197406759321, 9633262574, 0] := by
  rw [show D2M8K2.u10887 = KTree.node D2M8K2.t10894 (nat_lit 23547547) (nat_lit 2239021588) (nat_lit 0) D2M8K2.t10895 from rfl, totK_node, tot10894, tot10895]
  decide +kernel

theorem arows10891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10891 = true := by
  rw [show D2M8K2.u10891 = KTree.node D2M8K2.t10896 (nat_lit 23549407) (nat_lit 2383192834) (nat_lit 0) D2M8K2.t10897 from rfl, allE_node, rows10896, irow10891, rows10897]
  all_goals rfl

theorem atot10891 : totK PD2M8K2 D2M8K2.u10891 = [0, 0, 254267556450, 804749727836, 614077063344, 108561351859, 3472187823, 0] := by
  rw [show D2M8K2.u10891 = KTree.node D2M8K2.t10896 (nat_lit 23549407) (nat_lit 2383192834) (nat_lit 0) D2M8K2.t10897 from rfl, totK_node, tot10896, tot10897]
  decide +kernel

theorem arows10892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10892 = true := by
  rw [show D2M8K2.u10892 = KTree.node D2M8K2.t10898 (nat_lit 23551301) (nat_lit 1449622005) (nat_lit 34) D2M8K2.t10899 from rfl, allE_node, rows10898, irow10892, rows10899]
  all_goals rfl

theorem atot10892 : totK PD2M8K2 D2M8K2.u10892 = [0, 0, 172423528885, 689659162730, 723997303893, 149940344048, 4720618446, 0] := by
  rw [show D2M8K2.u10892 = KTree.node D2M8K2.t10898 (nat_lit 23551301) (nat_lit 1449622005) (nat_lit 34) D2M8K2.t10899 from rfl, totK_node, tot10898, tot10899]
  decide +kernel

theorem arows10894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10894 = true := by
  rw [show D2M8K2.u10894 = KTree.node D2M8K2.t10900 (nat_lit 23553391) (nat_lit 1615594989) (nat_lit 0) D2M8K2.t10901 from rfl, allE_node, rows10900, irow10894, rows10901]
  all_goals rfl

theorem atot10894 : totK PD2M8K2 D2M8K2.u10894 = [0, 0, 341638308135, 926419487591, 516845091845, 37038241221, 0, 0] := by
  rw [show D2M8K2.u10894 = KTree.node D2M8K2.t10900 (nat_lit 23553391) (nat_lit 1615594989) (nat_lit 0) D2M8K2.t10901 from rfl, totK_node, tot10900, tot10901]
  decide +kernel

theorem arows10895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10895 = true := by
  rw [show D2M8K2.u10895 = KTree.node D2M8K2.t10902 (nat_lit 23598400) (nat_lit 3279458550) (nat_lit 0) D2M8K2.t10903 from rfl, allE_node, rows10902, irow10895, rows10903]
  all_goals rfl

theorem atot10895 : totK PD2M8K2 D2M8K2.u10895 = [0, 369552279963, 887322541226, 429885511868, 75524488354, 9758758476, 0, 0] := by
  rw [show D2M8K2.u10895 = KTree.node D2M8K2.t10902 (nat_lit 23598400) (nat_lit 3279458550) (nat_lit 0) D2M8K2.t10903 from rfl, totK_node, tot10902, tot10903]
  decide +kernel

theorem arows10898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10898 = true := by
  rw [show D2M8K2.u10898 = KTree.node D2M8K2.t10904 (nat_lit 23599976) (nat_lit 2659760070) (nat_lit 0) D2M8K2.t10905 from rfl, allE_node, rows10904, irow10898, rows10905]
  all_goals rfl

theorem atot10898 : totK PD2M8K2 D2M8K2.u10898 = [0, 112289258290, 677851404686, 871095186860, 149585976500, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10898 = KTree.node D2M8K2.t10904 (nat_lit 23599976) (nat_lit 2659760070) (nat_lit 0) D2M8K2.t10905 from rfl, totK_node, tot10904, tot10905]
  decide +kernel

theorem arows10899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10899 = true := by
  rw [show D2M8K2.u10899 = KTree.node D2M8K2.t10906 (nat_lit 23601981) (nat_lit 1527236342) (nat_lit 0) D2M8K2.t10907 from rfl, allE_node, rows10906, irow10899, rows10907]
  all_goals rfl

theorem atot10899 : totK PD2M8K2 D2M8K2.u10899 = [0, 353897445293, 923167920663, 504252513663, 40676250713, 0, 0, 0] := by
  rw [show D2M8K2.u10899 = KTree.node D2M8K2.t10906 (nat_lit 23601981) (nat_lit 1527236342) (nat_lit 0) D2M8K2.t10907 from rfl, totK_node, tot10906, tot10907]
  decide +kernel

theorem arows10901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10901 = true := by
  rw [show D2M8K2.u10901 = KTree.node D2M8K2.t10908 (nat_lit 23603464) (nat_lit 3833857520) (nat_lit 0) D2M8K2.t10909 from rfl, allE_node, rows10908, irow10901, rows10909]
  all_goals rfl

theorem atot10901 : totK PD2M8K2 D2M8K2.u10901 = [0, 0, 399135295058, 934827997565, 435048500164, 27764542694, 0, 0] := by
  rw [show D2M8K2.u10901 = KTree.node D2M8K2.t10908 (nat_lit 23603464) (nat_lit 3833857520) (nat_lit 0) D2M8K2.t10909 from rfl, totK_node, tot10908, tot10909]
  decide +kernel

theorem arows10902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10902 = true := by
  rw [show D2M8K2.u10902 = KTree.node D2M8K2.t10910 (nat_lit 23604825) (nat_lit 1789918709) (nat_lit 0) D2M8K2.t10911 from rfl, allE_node, rows10910, irow10902, rows10911]
  all_goals rfl

theorem atot10902 : totK PD2M8K2 D2M8K2.u10902 = [0, 277239998783, 782120150881, 588240479791, 145014965388, 8204069046, 0, 0] := by
  rw [show D2M8K2.u10902 = KTree.node D2M8K2.t10910 (nat_lit 23604825) (nat_lit 1789918709) (nat_lit 0) D2M8K2.t10911 from rfl, totK_node, tot10910, tot10911]
  decide +kernel

theorem arows10907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10907 = true := by
  rw [show D2M8K2.u10907 = KTree.node D2M8K2.t10912 (nat_lit 23606358) (nat_lit 3057158767) (nat_lit 0) D2M8K2.t10913 from rfl, allE_node, rows10912, irow10907, rows10913]
  all_goals rfl

theorem atot10907 : totK PD2M8K2 D2M8K2.u10907 = [0, 125598274321, 631847584060, 812332490976, 205328321546, 7832068735, 0, 0] := by
  rw [show D2M8K2.u10907 = KTree.node D2M8K2.t10912 (nat_lit 23606358) (nat_lit 3057158767) (nat_lit 0) D2M8K2.t10913 from rfl, totK_node, tot10912, tot10913]
  decide +kernel

theorem arows10908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10908 = true := by
  rw [show D2M8K2.u10908 = KTree.node D2M8K2.t10914 (nat_lit 23608309) (nat_lit 1111919870) (nat_lit 0) D2M8K2.t10915 from rfl, allE_node, rows10914, irow10908, rows10915]
  all_goals rfl

theorem atot10908 : totK PD2M8K2 D2M8K2.u10908 = [0, 299563686931, 831590386157, 592815381982, 90524071356, 980350181, 0, 0] := by
  rw [show D2M8K2.u10908 = KTree.node D2M8K2.t10914 (nat_lit 23608309) (nat_lit 1111919870) (nat_lit 0) D2M8K2.t10915 from rfl, totK_node, tot10914, tot10915]
  decide +kernel

theorem arows10910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10910 = true := by
  rw [show D2M8K2.u10910 = KTree.node D2M8K2.t10916 (nat_lit 23609795) (nat_lit 2948508575) (nat_lit 0) D2M8K2.t10917 from rfl, allE_node, rows10916, irow10910, rows10917]
  all_goals rfl

theorem atot10910 : totK PD2M8K2 D2M8K2.u10910 = [0, 123351558152, 633478876416, 812195463234, 218422038159, 9652233629, 0, 0] := by
  rw [show D2M8K2.u10910 = KTree.node D2M8K2.t10916 (nat_lit 23609795) (nat_lit 2948508575) (nat_lit 0) D2M8K2.t10917 from rfl, totK_node, tot10916, tot10917]
  decide +kernel

theorem arows10911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10911 = true := by
  rw [show D2M8K2.u10911 = KTree.node D2M8K2.t10918 (nat_lit 23615118) (nat_lit 3819441806) (nat_lit 0) D2M8K2.t10919 from rfl, allE_node, rows10918, irow10911, rows10919]
  all_goals rfl

theorem atot10911 : totK PD2M8K2 D2M8K2.u10911 = [0, 265120815309, 801703952142, 637649839649, 121240730540, 3564119920, 0, 0] := by
  rw [show D2M8K2.u10911 = KTree.node D2M8K2.t10918 (nat_lit 23615118) (nat_lit 3819441806) (nat_lit 0) D2M8K2.t10919 from rfl, totK_node, tot10918, tot10919]
  decide +kernel

theorem arows10914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10914 = true := by
  rw [show D2M8K2.u10914 = KTree.node D2M8K2.t10920 (nat_lit 23616557) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t10921 from rfl, allE_node, rows10920, irow10914, rows10921]
  all_goals rfl

theorem atot10914 : totK PD2M8K2 D2M8K2.u10914 = [0, 182497872290, 750846484175, 764164032231, 139130732949, 1268739303, 0, 0] := by
  rw [show D2M8K2.u10914 = KTree.node D2M8K2.t10920 (nat_lit 23616557) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t10921 from rfl, totK_node, tot10920, tot10921]
  decide +kernel

theorem arows10915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10915 = true := by
  rw [show D2M8K2.u10915 = KTree.node D2M8K2.t10922 (nat_lit 23618195) (nat_lit 2572641369) (nat_lit 0) D2M8K2.t10923 from rfl, allE_node, rows10922, irow10915, rows10923]
  all_goals rfl

theorem atot10915 : totK PD2M8K2 D2M8K2.u10915 = [0, 0, 354909255864, 947375655171, 442867929410, 24426732703, 0, 0] := by
  rw [show D2M8K2.u10915 = KTree.node D2M8K2.t10922 (nat_lit 23618195) (nat_lit 2572641369) (nat_lit 0) D2M8K2.t10923 from rfl, totK_node, tot10922, tot10923]
  decide +kernel

theorem arows10917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10917 = true := by
  rw [show D2M8K2.u10917 = KTree.node D2M8K2.t10924 (nat_lit 23619805) (nat_lit 1207863925) (nat_lit 0) D2M8K2.t10925 from rfl, allE_node, rows10924, irow10917, rows10925]
  all_goals rfl

theorem atot10917 : totK PD2M8K2 D2M8K2.u10917 = [0, 0, 238016796079, 793309330823, 625681062615, 87429968825, 1310285577, 0] := by
  rw [show D2M8K2.u10917 = KTree.node D2M8K2.t10924 (nat_lit 23619805) (nat_lit 1207863925) (nat_lit 0) D2M8K2.t10925 from rfl, totK_node, tot10924, tot10925]
  decide +kernel

theorem arows10918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10918 = true := by
  rw [show D2M8K2.u10918 = KTree.node D2M8K2.t10926 (nat_lit 23622174) (nat_lit 3885041401) (nat_lit 0) D2M8K2.t10927 from rfl, allE_node, rows10926, irow10918, rows10927]
  all_goals rfl

theorem atot10918 : totK PD2M8K2 D2M8K2.u10918 = [0, 0, 249872527311, 815082906137, 676624601466, 66729049529, 0, 0] := by
  rw [show D2M8K2.u10918 = KTree.node D2M8K2.t10926 (nat_lit 23622174) (nat_lit 3885041401) (nat_lit 0) D2M8K2.t10927 from rfl, totK_node, tot10926, tot10927]
  decide +kernel

theorem arows10922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10922 = true := by
  rw [show D2M8K2.u10922 = KTree.node D2M8K2.t10928 (nat_lit 23623417) (nat_lit 1352727943) (nat_lit 0) D2M8K2.t10929 from rfl, allE_node, rows10928, irow10922, rows10929]
  all_goals rfl

theorem atot10922 : totK PD2M8K2 D2M8K2.u10922 = [0, 0, 338721517675, 936132259982, 503495083148, 36289523740, 0, 0] := by
  rw [show D2M8K2.u10922 = KTree.node D2M8K2.t10928 (nat_lit 23623417) (nat_lit 1352727943) (nat_lit 0) D2M8K2.t10929 from rfl, totK_node, tot10928, tot10929]
  decide +kernel

theorem arows10923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10923 = true := by
  rw [show D2M8K2.u10923 = KTree.node D2M8K2.t10930 (nat_lit 23626729) (nat_lit 1415783702) (nat_lit 0) D2M8K2.t10931 from rfl, allE_node, rows10930, irow10923, rows10931]
  all_goals rfl

theorem atot10923 : totK PD2M8K2 D2M8K2.u10923 = [0, 0, 230912756337, 801347266029, 655885271491, 85358027678, 1075657031, 0] := by
  rw [show D2M8K2.u10923 = KTree.node D2M8K2.t10930 (nat_lit 23626729) (nat_lit 1415783702) (nat_lit 0) D2M8K2.t10931 from rfl, totK_node, tot10930, tot10931]
  decide +kernel

theorem arows10925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10925 = true := by
  rw [show D2M8K2.u10925 = KTree.node D2M8K2.t10932 (nat_lit 23628808) (nat_lit 3402759368) (nat_lit 0) D2M8K2.t10933 from rfl, allE_node, rows10932, irow10925, rows10933]
  all_goals rfl

theorem atot10925 : totK PD2M8K2 D2M8K2.u10925 = [0, 0, 264020450567, 775912392919, 624018563510, 117441139891, 3804183361, 0] := by
  rw [show D2M8K2.u10925 = KTree.node D2M8K2.t10932 (nat_lit 23628808) (nat_lit 3402759368) (nat_lit 0) D2M8K2.t10933 from rfl, totK_node, tot10932, tot10933]
  decide +kernel

theorem arows10926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10926 = true := by
  rw [show D2M8K2.u10926 = KTree.node D2M8K2.t10934 (nat_lit 23630337) (nat_lit 1525361624) (nat_lit 0) D2M8K2.t10935 from rfl, allE_node, rows10934, irow10926, rows10935]
  all_goals rfl

theorem atot10926 : totK PD2M8K2 D2M8K2.u10926 = [0, 0, 156878551535, 742498709821, 756414430328, 118569177344, 1107157161, 0] := by
  rw [show D2M8K2.u10926 = KTree.node D2M8K2.t10934 (nat_lit 23630337) (nat_lit 1525361624) (nat_lit 0) D2M8K2.t10935 from rfl, totK_node, tot10934, tot10935]
  decide +kernel

theorem arows10929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10929 = true := by
  rw [show D2M8K2.u10929 = KTree.node D2M8K2.t10936 (nat_lit 23635902) (nat_lit 3920342692) (nat_lit 0) D2M8K2.t10937 from rfl, allE_node, rows10936, irow10929, rows10937]
  all_goals rfl

theorem atot10929 : totK PD2M8K2 D2M8K2.u10929 = [0, 0, 263782340324, 824666881443, 607547272908, 101826046885, 2770420231, 0] := by
  rw [show D2M8K2.u10929 = KTree.node D2M8K2.t10936 (nat_lit 23635902) (nat_lit 3920342692) (nat_lit 0) D2M8K2.t10937 from rfl, totK_node, tot10936, tot10937]
  decide +kernel

theorem arows10930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10930 = true := by
  rw [show D2M8K2.u10930 = KTree.node D2M8K2.t10938 (nat_lit 23637310) (nat_lit 3907958896) (nat_lit 0) D2M8K2.t10939 from rfl, allE_node, rows10938, irow10930, rows10939]
  all_goals rfl

theorem atot10930 : totK PD2M8K2 D2M8K2.u10930 = [0, 0, 177996210166, 724095669676, 747222014514, 146539985979, 2243379097, 0] := by
  rw [show D2M8K2.u10930 = KTree.node D2M8K2.t10938 (nat_lit 23637310) (nat_lit 3907958896) (nat_lit 0) D2M8K2.t10939 from rfl, totK_node, tot10938, tot10939]
  decide +kernel

theorem arows10932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10932 = true := by
  rw [show D2M8K2.u10932 = KTree.node D2M8K2.t10940 (nat_lit 23639017) (nat_lit 1448736475) (nat_lit 0) D2M8K2.t10941 from rfl, allE_node, rows10940, irow10932, rows10941]
  all_goals rfl

theorem atot10932 : totK PD2M8K2 D2M8K2.u10932 = [186677387228, 461439392893, 202050743940, 187244844477, 474091814588, 240942723549, 19507788969, 0] := by
  rw [show D2M8K2.u10932 = KTree.node D2M8K2.t10940 (nat_lit 23639017) (nat_lit 1448736475) (nat_lit 0) D2M8K2.t10941 from rfl, totK_node, tot10940, tot10941]
  decide +kernel

theorem arows10933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10933 = true := by
  rw [show D2M8K2.u10933 = KTree.node D2M8K2.t10942 (nat_lit 23889350) (nat_lit 2349351058) (nat_lit 0) D2M8K2.t10943 from rfl, allE_node, rows10942, irow10933, rows10943]
  all_goals rfl

theorem atot10933 : totK PD2M8K2 D2M8K2.u10933 = [251856805486, 808697726510, 642168273518, 105322300753, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u10933 = KTree.node D2M8K2.t10942 (nat_lit 23889350) (nat_lit 2349351058) (nat_lit 0) D2M8K2.t10943 from rfl, totK_node, tot10942, tot10943]
  decide +kernel

theorem arows10939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10939 = true := by
  rw [show D2M8K2.u10939 = KTree.node D2M8K2.t10944 (nat_lit 23894852) (nat_lit 3320357973) (nat_lit 0) D2M8K2.t10945 from rfl, allE_node, rows10944, irow10939, rows10945]
  all_goals rfl

theorem atot10939 : totK PD2M8K2 D2M8K2.u10939 = [239322649124, 810031113385, 699718451522, 80704768101, 0, 0, 0, 0] := by
  rw [show D2M8K2.u10939 = KTree.node D2M8K2.t10944 (nat_lit 23894852) (nat_lit 3320357973) (nat_lit 0) D2M8K2.t10945 from rfl, totK_node, tot10944, tot10945]
  decide +kernel

theorem arows10940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10940 = true := by
  rw [show D2M8K2.u10940 = KTree.node D2M8K2.t10946 (nat_lit 23896372) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t10947 from rfl, allE_node, rows10946, irow10940, rows10947]
  all_goals rfl

theorem atot10940 : totK PD2M8K2 D2M8K2.u10940 = [177286973961, 755330115405, 723041645037, 117407283321, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u10940 = KTree.node D2M8K2.t10946 (nat_lit 23896372) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t10947 from rfl, totK_node, tot10946, tot10947]
  decide +kernel

theorem arows10942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10942 = true := by
  rw [show D2M8K2.u10942 = KTree.node D2M8K2.t10948 (nat_lit 23898077) (nat_lit 2232995411) (nat_lit 0) D2M8K2.t10949 from rfl, allE_node, rows10948, irow10942, rows10949]
  all_goals rfl

theorem atot10942 : totK PD2M8K2 D2M8K2.u10942 = [190499018848, 649742773759, 707509861897, 213484440969, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u10942 = KTree.node D2M8K2.t10948 (nat_lit 23898077) (nat_lit 2232995411) (nat_lit 0) D2M8K2.t10949 from rfl, totK_node, tot10948, tot10949]
  decide +kernel

theorem arows10943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10943 = true := by
  rw [show D2M8K2.u10943 = KTree.node D2M8K2.t10950 (nat_lit 23899740) (nat_lit 3108171929) (nat_lit 0) D2M8K2.t10951 from rfl, allE_node, rows10950, irow10943, rows10951]
  all_goals rfl

theorem atot10943 : totK PD2M8K2 D2M8K2.u10943 = [226316553554, 775204565620, 669163772393, 110557569580, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u10943 = KTree.node D2M8K2.t10950 (nat_lit 23899740) (nat_lit 3108171929) (nat_lit 0) D2M8K2.t10951 from rfl, totK_node, tot10950, tot10951]
  decide +kernel

theorem arows10946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10946 = true := by
  rw [show D2M8K2.u10946 = KTree.node D2M8K2.t10952 (nat_lit 23901440) (nat_lit 2275647427) (nat_lit 0) D2M8K2.t10953 from rfl, allE_node, rows10952, irow10946, rows10953]
  all_goals rfl

theorem atot10946 : totK PD2M8K2 D2M8K2.u10946 = [155852417729, 635734402802, 747318949901, 228559398043, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u10946 = KTree.node D2M8K2.t10952 (nat_lit 23901440) (nat_lit 2275647427) (nat_lit 0) D2M8K2.t10953 from rfl, totK_node, tot10952, tot10953]
  decide +kernel

theorem arows10947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10947 = true := by
  rw [show D2M8K2.u10947 = KTree.node D2M8K2.t10954 (nat_lit 23902825) (nat_lit 1408418971) (nat_lit 0) D2M8K2.t10955 from rfl, allE_node, rows10954, irow10947, rows10955]
  all_goals rfl

theorem atot10947 : totK PD2M8K2 D2M8K2.u10947 = [263173227214, 807852053290, 625436990353, 90398721628, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u10947 = KTree.node D2M8K2.t10954 (nat_lit 23902825) (nat_lit 1408418971) (nat_lit 0) D2M8K2.t10955 from rfl, totK_node, tot10954, tot10955]
  decide +kernel

theorem arows10949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10949 = true := by
  rw [show D2M8K2.u10949 = KTree.node D2M8K2.t10956 (nat_lit 23904793) (nat_lit 1302733211) (nat_lit 0) D2M8K2.t10957 from rfl, allE_node, rows10956, irow10949, rows10957]
  all_goals rfl

theorem atot10949 : totK PD2M8K2 D2M8K2.u10949 = [192703141660, 727209661920, 732781073354, 141730101158, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u10949 = KTree.node D2M8K2.t10956 (nat_lit 23904793) (nat_lit 1302733211) (nat_lit 0) D2M8K2.t10957 from rfl, totK_node, tot10956, tot10957]
  decide +kernel

theorem arows10950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10950 = true := by
  rw [show D2M8K2.u10950 = KTree.node D2M8K2.t10958 (nat_lit 23906673) (nat_lit 1481370009) (nat_lit 0) D2M8K2.t10959 from rfl, allE_node, rows10958, irow10950, rows10959]
  all_goals rfl

theorem atot10950 : totK PD2M8K2 D2M8K2.u10950 = [209384673087, 761541592761, 693403471890, 116592801573, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u10950 = KTree.node D2M8K2.t10958 (nat_lit 23906673) (nat_lit 1481370009) (nat_lit 0) D2M8K2.t10959 from rfl, totK_node, tot10958, tot10959]
  decide +kernel

theorem arows10954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10954 = true := by
  rw [show D2M8K2.u10954 = KTree.node D2M8K2.t10960 (nat_lit 23908392) (nat_lit 3493111030) (nat_lit 0) D2M8K2.t10961 from rfl, allE_node, rows10960, irow10954, rows10961]
  all_goals rfl

theorem atot10954 : totK PD2M8K2 D2M8K2.u10954 = [0, 394564107203, 943814623650, 404734506359, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u10954 = KTree.node D2M8K2.t10960 (nat_lit 23908392) (nat_lit 3493111030) (nat_lit 0) D2M8K2.t10961 from rfl, totK_node, tot10960, tot10961]
  decide +kernel

theorem arows10955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10955 = true := by
  rw [show D2M8K2.u10955 = KTree.node D2M8K2.t10962 (nat_lit 23909861) (nat_lit 2316145649) (nat_lit 0) D2M8K2.t10963 from rfl, allE_node, rows10962, irow10955, rows10963]
  all_goals rfl

theorem atot10955 : totK PD2M8K2 D2M8K2.u10955 = [0, 279407875829, 873712926260, 545579327448, 50271802712, 0, 0, 0] := by
  rw [show D2M8K2.u10955 = KTree.node D2M8K2.t10962 (nat_lit 23909861) (nat_lit 2316145649) (nat_lit 0) D2M8K2.t10963 from rfl, totK_node, tot10962, tot10963]
  decide +kernel

theorem arows10957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10957 = true := by
  rw [show D2M8K2.u10957 = KTree.node D2M8K2.t10964 (nat_lit 23911837) (nat_lit 1135335793) (nat_lit 0) D2M8K2.t10965 from rfl, allE_node, rows10964, irow10957, rows10965]
  all_goals rfl

theorem atot10957 : totK PD2M8K2 D2M8K2.u10957 = [0, 179803319846, 762629024084, 693516503102, 118307900074, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10957 = KTree.node D2M8K2.t10964 (nat_lit 23911837) (nat_lit 1135335793) (nat_lit 0) D2M8K2.t10965 from rfl, totK_node, tot10964, tot10965]
  decide +kernel

theorem arows10958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10958 = true := by
  rw [show D2M8K2.u10958 = KTree.node D2M8K2.t10966 (nat_lit 23917004) (nat_lit 2301073810) (nat_lit 0) D2M8K2.t10967 from rfl, allE_node, rows10966, irow10958, rows10967]
  all_goals rfl

theorem atot10958 : totK PD2M8K2 D2M8K2.u10958 = [0, 385733427949, 939842671050, 424487842051, 22421051990, 0, 0, 0] := by
  rw [show D2M8K2.u10958 = KTree.node D2M8K2.t10966 (nat_lit 23917004) (nat_lit 2301073810) (nat_lit 0) D2M8K2.t10967 from rfl, totK_node, tot10966, tot10967]
  decide +kernel

theorem arows10961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10961 = true := by
  rw [show D2M8K2.u10961 = KTree.node D2M8K2.t10968 (nat_lit 23920288) (nat_lit 2168028237) (nat_lit 0) D2M8K2.t10969 from rfl, allE_node, rows10968, irow10961, rows10969]
  all_goals rfl

theorem atot10961 : totK PD2M8K2 D2M8K2.u10961 = [0, 353020543503, 931115609215, 464372854955, 26644536935, 0, 0, 0] := by
  rw [show D2M8K2.u10961 = KTree.node D2M8K2.t10968 (nat_lit 23920288) (nat_lit 2168028237) (nat_lit 0) D2M8K2.t10969 from rfl, totK_node, tot10968, tot10969]
  decide +kernel

theorem arows10962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10962 = true := by
  rw [show D2M8K2.u10962 = KTree.node D2M8K2.t10970 (nat_lit 23923338) (nat_lit 3850770401) (nat_lit 0) D2M8K2.t10971 from rfl, allE_node, rows10970, irow10962, rows10971]
  all_goals rfl

theorem atot10962 : totK PD2M8K2 D2M8K2.u10962 = [0, 385245976713, 947387471508, 419856995579, 22161131776, 0, 0, 0] := by
  rw [show D2M8K2.u10962 = KTree.node D2M8K2.t10970 (nat_lit 23923338) (nat_lit 3850770401) (nat_lit 0) D2M8K2.t10971 from rfl, totK_node, tot10970, tot10971]
  decide +kernel

theorem arows10964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10964 = true := by
  rw [show D2M8K2.u10964 = KTree.node D2M8K2.t10972 (nat_lit 23926667) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t10973 from rfl, allE_node, rows10972, irow10964, rows10973]
  all_goals rfl

theorem atot10964 : totK PD2M8K2 D2M8K2.u10964 = [0, 346391894202, 933489013133, 465937683147, 21111913661, 0, 0, 0] := by
  rw [show D2M8K2.u10964 = KTree.node D2M8K2.t10972 (nat_lit 23926667) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t10973 from rfl, totK_node, tot10972, tot10973]
  decide +kernel

theorem arows10965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10965 = true := by
  rw [show D2M8K2.u10965 = KTree.node D2M8K2.t10974 (nat_lit 23971667) (nat_lit 2933783805) (nat_lit 0) D2M8K2.t10975 from rfl, allE_node, rows10974, irow10965, rows10975]
  all_goals rfl

theorem atot10965 : totK PD2M8K2 D2M8K2.u10965 = [384126823169, 915175898258, 427325775592, 56112130749, 8621106361, 0, 0, 0] := by
  rw [show D2M8K2.u10965 = KTree.node D2M8K2.t10974 (nat_lit 23971667) (nat_lit 2933783805) (nat_lit 0) D2M8K2.t10975 from rfl, totK_node, tot10974, tot10975]
  decide +kernel

theorem arows10970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10970 = true := by
  rw [show D2M8K2.u10970 = KTree.node D2M8K2.t10976 (nat_lit 23973232) (nat_lit 3413510559) (nat_lit 0) D2M8K2.t10977 from rfl, allE_node, rows10976, irow10970, rows10977]
  all_goals rfl

theorem atot10970 : totK PD2M8K2 D2M8K2.u10970 = [106446963495, 667631700179, 870520555827, 153358181050, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u10970 = KTree.node D2M8K2.t10976 (nat_lit 23973232) (nat_lit 3413510559) (nat_lit 0) D2M8K2.t10977 from rfl, totK_node, tot10976, tot10977]
  decide +kernel

theorem arows10971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10971 = true := by
  rw [show D2M8K2.u10971 = KTree.node D2M8K2.t10978 (nat_lit 23975504) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t10979 from rfl, allE_node, rows10978, irow10971, rows10979]
  all_goals rfl

theorem atot10971 : totK PD2M8K2 D2M8K2.u10971 = [259389689780, 835997725655, 630194643841, 103225847417, 10438989511, 0, 0, 0] := by
  rw [show D2M8K2.u10971 = KTree.node D2M8K2.t10978 (nat_lit 23975504) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t10979 from rfl, totK_node, tot10978, tot10979]
  decide +kernel

theorem arows10973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10973 = true := by
  rw [show D2M8K2.u10973 = KTree.node D2M8K2.t10980 (nat_lit 23977355) (nat_lit 1219430583) (nat_lit 0) D2M8K2.t10981 from rfl, allE_node, rows10980, irow10973, rows10981]
  all_goals rfl

theorem atot10973 : totK PD2M8K2 D2M8K2.u10973 = [125231109916, 522981426775, 770000683411, 369799220395, 21804665281, 0, 0, 0] := by
  rw [show D2M8K2.u10973 = KTree.node D2M8K2.t10980 (nat_lit 23977355) (nat_lit 1219430583) (nat_lit 0) D2M8K2.t10981 from rfl, totK_node, tot10980, tot10981]
  decide +kernel

theorem arows10974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10974 = true := by
  rw [show D2M8K2.u10974 = KTree.node D2M8K2.t10982 (nat_lit 23978925) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t10983 from rfl, allE_node, rows10982, irow10974, rows10983]
  all_goals rfl

theorem atot10974 : totK PD2M8K2 D2M8K2.u10974 = [308272391800, 887911278333, 561827140186, 52857550967, 0, 0, 0, 0] := by
  rw [show D2M8K2.u10974 = KTree.node D2M8K2.t10982 (nat_lit 23978925) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t10983 from rfl, totK_node, tot10982, tot10983]
  decide +kernel

theorem arows10977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10977 = true := by
  rw [show D2M8K2.u10977 = KTree.node D2M8K2.t10984 (nat_lit 23980300) (nat_lit 3877811141) (nat_lit 0) D2M8K2.t10985 from rfl, allE_node, rows10984, irow10977, rows10985]
  all_goals rfl

theorem atot10977 : totK PD2M8K2 D2M8K2.u10977 = [84862533686, 524436065073, 875074513537, 282762015339, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u10977 = KTree.node D2M8K2.t10984 (nat_lit 23980300) (nat_lit 3877811141) (nat_lit 0) D2M8K2.t10985 from rfl, totK_node, tot10984, tot10985]
  decide +kernel

theorem arows10978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10978 = true := by
  rw [show D2M8K2.u10978 = KTree.node D2M8K2.t10986 (nat_lit 23985409) (nat_lit 1417801816) (nat_lit 0) D2M8K2.t10987 from rfl, allE_node, rows10986, irow10978, rows10987]
  all_goals rfl

theorem atot10978 : totK PD2M8K2 D2M8K2.u10978 = [327302098136, 914692289443, 524339488745, 42682837105, 0, 0, 0, 0] := by
  rw [show D2M8K2.u10978 = KTree.node D2M8K2.t10986 (nat_lit 23985409) (nat_lit 1417801816) (nat_lit 0) D2M8K2.t10987 from rfl, totK_node, tot10986, tot10987]
  decide +kernel

theorem arows10980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10980 = true := by
  rw [show D2M8K2.u10980 = KTree.node D2M8K2.t10988 (nat_lit 23987306) (nat_lit 3762967388) (nat_lit 0) D2M8K2.t10989 from rfl, allE_node, rows10988, irow10980, rows10989]
  all_goals rfl

theorem atot10980 : totK PD2M8K2 D2M8K2.u10980 = [88915620767, 618611242049, 874220425825, 201719681946, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u10980 = KTree.node D2M8K2.t10988 (nat_lit 23987306) (nat_lit 3762967388) (nat_lit 0) D2M8K2.t10989 from rfl, totK_node, tot10988, tot10989]
  decide +kernel

theorem arows10981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10981 = true := by
  rw [show D2M8K2.u10981 = KTree.node D2M8K2.t10990 (nat_lit 23989081) (nat_lit 1484051182) (nat_lit 0) D2M8K2.t10991 from rfl, allE_node, rows10990, irow10981, rows10991]
  all_goals rfl

theorem atot10981 : totK PD2M8K2 D2M8K2.u10981 = [294197057641, 848825929538, 600963465603, 67406339684, 0, 0, 0, 0] := by
  rw [show D2M8K2.u10981 = KTree.node D2M8K2.t10990 (nat_lit 23989081) (nat_lit 1484051182) (nat_lit 0) D2M8K2.t10991 from rfl, totK_node, tot10990, tot10991]
  decide +kernel

theorem arows10985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10985 = true := by
  rw [show D2M8K2.u10985 = KTree.node D2M8K2.t10992 (nat_lit 23990844) (nat_lit 2917211623) (nat_lit 0) D2M8K2.t10993 from rfl, allE_node, rows10992, irow10985, rows10993]
  all_goals rfl

theorem atot10985 : totK PD2M8K2 D2M8K2.u10985 = [0, 387285391070, 937580312470, 414235072714, 23412759273, 0, 0, 0] := by
  rw [show D2M8K2.u10985 = KTree.node D2M8K2.t10992 (nat_lit 23990844) (nat_lit 2917211623) (nat_lit 0) D2M8K2.t10993 from rfl, totK_node, tot10992, tot10993]
  decide +kernel

theorem arows10986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10986 = true := by
  rw [show D2M8K2.u10986 = KTree.node D2M8K2.t10994 (nat_lit 23992744) (nat_lit 3667198012) (nat_lit 0) D2M8K2.t10995 from rfl, allE_node, rows10994, irow10986, rows10995]
  all_goals rfl

theorem atot10986 : totK PD2M8K2 D2M8K2.u10986 = [0, 326431309034, 923305063707, 473699032887, 29635838686, 0, 0, 0] := by
  rw [show D2M8K2.u10986 = KTree.node D2M8K2.t10994 (nat_lit 23992744) (nat_lit 3667198012) (nat_lit 0) D2M8K2.t10995 from rfl, totK_node, tot10994, tot10995]
  decide +kernel

theorem arows10988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10988 = true := by
  rw [show D2M8K2.u10988 = KTree.node D2M8K2.t10996 (nat_lit 23994750) (nat_lit 2104929824) (nat_lit 0) D2M8K2.t10997 from rfl, allE_node, rows10996, irow10988, rows10997]
  all_goals rfl

theorem atot10988 : totK PD2M8K2 D2M8K2.u10988 = [0, 177425867739, 745081648147, 749394076834, 111000423882, 1206465782, 0, 0] := by
  rw [show D2M8K2.u10988 = KTree.node D2M8K2.t10996 (nat_lit 23994750) (nat_lit 2104929824) (nat_lit 0) D2M8K2.t10997 from rfl, totK_node, tot10996, tot10997]
  decide +kernel

theorem arows10989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10989 = true := by
  rw [show D2M8K2.u10989 = KTree.node D2M8K2.t10998 (nat_lit 23998473) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t10999 from rfl, allE_node, rows10998, irow10989, rows10999]
  all_goals rfl

theorem atot10989 : totK PD2M8K2 D2M8K2.u10989 = [0, 359335912323, 935902525523, 479318242086, 36469894054, 0, 0, 0] := by
  rw [show D2M8K2.u10989 = KTree.node D2M8K2.t10998 (nat_lit 23998473) (nat_lit 1826613998) (nat_lit 0) D2M8K2.t10999 from rfl, totK_node, tot10998, tot10999]
  decide +kernel

theorem arows10992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10992 = true := by
  rw [show D2M8K2.u10992 = KTree.node D2M8K2.t11000 (nat_lit 23999964) (nat_lit 3188351728) (nat_lit 0) D2M8K2.t11001 from rfl, allE_node, rows11000, irow10992, rows11001]
  all_goals rfl

theorem atot10992 : totK PD2M8K2 D2M8K2.u10992 = [0, 228436729931, 799269991511, 642224242447, 96997791300, 1162935789, 0, 0] := by
  rw [show D2M8K2.u10992 = KTree.node D2M8K2.t11000 (nat_lit 23999964) (nat_lit 3188351728) (nat_lit 0) D2M8K2.t11001 from rfl, totK_node, tot11000, tot11001]
  decide +kernel

theorem arows10993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10993 = true := by
  rw [show D2M8K2.u10993 = KTree.node D2M8K2.t11002 (nat_lit 24001672) (nat_lit 3781635903) (nat_lit 0) D2M8K2.t11003 from rfl, allE_node, rows11002, irow10993, rows11003]
  all_goals rfl

theorem atot10993 : totK PD2M8K2 D2M8K2.u10993 = [0, 164100838655, 656713708855, 712246140085, 204906555536, 11853261585, 0, 0] := by
  rw [show D2M8K2.u10993 = KTree.node D2M8K2.t11002 (nat_lit 24001672) (nat_lit 3781635903) (nat_lit 0) D2M8K2.t11003 from rfl, totK_node, tot11002, tot11003]
  decide +kernel

theorem arows10995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10995 = true := by
  rw [show D2M8K2.u10995 = KTree.node D2M8K2.t11004 (nat_lit 24006579) (nat_lit 3636694463) (nat_lit 0) D2M8K2.t11005 from rfl, allE_node, rows11004, irow10995, rows11005]
  all_goals rfl

theorem atot10995 : totK PD2M8K2 D2M8K2.u10995 = [0, 245970580446, 815027530344, 617423844841, 74126708953, 1021600638, 0, 0] := by
  rw [show D2M8K2.u10995 = KTree.node D2M8K2.t11004 (nat_lit 24006579) (nat_lit 3636694463) (nat_lit 0) D2M8K2.t11005 from rfl, totK_node, tot11004, tot11005]
  decide +kernel

theorem arows10996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10996 = true := by
  rw [show D2M8K2.u10996 = KTree.node D2M8K2.t11006 (nat_lit 24008948) (nat_lit 3398742819) (nat_lit 0) D2M8K2.t11007 from rfl, allE_node, rows11006, irow10996, rows11007]
  all_goals rfl

theorem atot10996 : totK PD2M8K2 D2M8K2.u10996 = [0, 238912398576, 773095917487, 629432283752, 112522943552, 3552795014, 0, 0] := by
  rw [show D2M8K2.u10996 = KTree.node D2M8K2.t11006 (nat_lit 24008948) (nat_lit 3398742819) (nat_lit 0) D2M8K2.t11007 from rfl, totK_node, tot11006, tot11007]
  decide +kernel

theorem arows11004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11004 = true := by
  rw [show D2M8K2.u11004 = KTree.node D2M8K2.t11008 (nat_lit 24012341) (nat_lit 2361569578) (nat_lit 0) D2M8K2.t11009 from rfl, allE_node, rows11008, irow11004, rows11009]
  all_goals rfl

theorem atot11004 : totK PD2M8K2 D2M8K2.u11004 = [231330679436, 660504594574, 613620964893, 263476752032, 22321705707, 0, 0, 0] := by
  rw [show D2M8K2.u11004 = KTree.node D2M8K2.t11008 (nat_lit 24012341) (nat_lit 2361569578) (nat_lit 0) D2M8K2.t11009 from rfl, totK_node, tot11008, tot11009]
  decide +kernel

theorem arows11005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11005 = true := by
  rw [show D2M8K2.u11005 = KTree.node D2M8K2.t11010 (nat_lit 24013872) (nat_lit 3701496321) (nat_lit 0) D2M8K2.t11011 from rfl, allE_node, rows11010, irow11005, rows11011]
  all_goals rfl

theorem atot11005 : totK PD2M8K2 D2M8K2.u11005 = [184159978963, 753858118035, 718161347493, 119400649859, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11005 = KTree.node D2M8K2.t11010 (nat_lit 24013872) (nat_lit 3701496321) (nat_lit 0) D2M8K2.t11011 from rfl, totK_node, tot11010, tot11011]
  decide +kernel

theorem arows11007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11007 = true := by
  rw [show D2M8K2.u11007 = KTree.node D2M8K2.t11012 (nat_lit 24016226) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t11013 from rfl, allE_node, rows11012, irow11007, rows11013]
  all_goals rfl

theorem atot11007 : totK PD2M8K2 D2M8K2.u11007 = [261593313394, 826298227006, 673415963935, 78052748502, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11007 = KTree.node D2M8K2.t11012 (nat_lit 24016226) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t11013 from rfl, totK_node, tot11012, tot11013]
  decide +kernel

theorem arows11008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11008 = true := by
  rw [show D2M8K2.u11008 = KTree.node D2M8K2.t11014 (nat_lit 24018018) (nat_lit 3140774908) (nat_lit 0) D2M8K2.t11015 from rfl, allE_node, rows11014, irow11008, rows11015]
  all_goals rfl

theorem atot11008 : totK PD2M8K2 D2M8K2.u11008 = [69491567446, 523305462511, 844545613110, 354859967413, 26712625787, 0, 0, 0] := by
  rw [show D2M8K2.u11008 = KTree.node D2M8K2.t11014 (nat_lit 24018018) (nat_lit 3140774908) (nat_lit 0) D2M8K2.t11015 from rfl, totK_node, tot11014, tot11015]
  decide +kernel

theorem arows11011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11011 = true := by
  rw [show D2M8K2.u11011 = KTree.node D2M8K2.t11016 (nat_lit 24023087) (nat_lit 2755379926) (nat_lit 0) D2M8K2.t11017 from rfl, allE_node, rows11016, irow11011, rows11017]
  all_goals rfl

theorem atot11011 : totK PD2M8K2 D2M8K2.u11011 = [351465405159, 835772090725, 530860725404, 114667703813, 5558641093, 0, 0, 0] := by
  rw [show D2M8K2.u11011 = KTree.node D2M8K2.t11016 (nat_lit 24023087) (nat_lit 2755379926) (nat_lit 0) D2M8K2.t11017 from rfl, totK_node, tot11016, tot11017]
  decide +kernel

theorem arows11012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11012 = true := by
  rw [show D2M8K2.u11012 = KTree.node D2M8K2.t11018 (nat_lit 24024537) (nat_lit 1671820488) (nat_lit 0) D2M8K2.t11019 from rfl, allE_node, rows11018, irow11012, rows11019]
  all_goals rfl

theorem atot11012 : totK PD2M8K2 D2M8K2.u11012 = [86218514020, 625555923688, 844075787583, 223206562898, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u11012 = KTree.node D2M8K2.t11018 (nat_lit 24024537) (nat_lit 1671820488) (nat_lit 0) D2M8K2.t11019 from rfl, totK_node, tot11018, tot11019]
  decide +kernel

theorem arows11014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11014 = true := by
  rw [show D2M8K2.u11014 = KTree.node D2M8K2.t11020 (nat_lit 24026360) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11021 from rfl, allE_node, rows11020, irow11014, rows11021]
  all_goals rfl

theorem atot11014 : totK PD2M8K2 D2M8K2.u11014 = [268681290812, 767994399964, 622819911446, 125928438573, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u11014 = KTree.node D2M8K2.t11020 (nat_lit 24026360) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11021 from rfl, totK_node, tot11020, tot11021]
  decide +kernel

theorem arows11015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11015 = true := by
  rw [show D2M8K2.u11015 = KTree.node D2M8K2.t11022 (nat_lit 24027920) (nat_lit 3685405955) (nat_lit 0) D2M8K2.t11023 from rfl, allE_node, rows11022, irow11015, rows11023]
  all_goals rfl

theorem atot11015 : totK PD2M8K2 D2M8K2.u11015 = [143538345355, 743645890810, 797507964862, 122755414951, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11015 = KTree.node D2M8K2.t11022 (nat_lit 24027920) (nat_lit 3685405955) (nat_lit 0) D2M8K2.t11023 from rfl, totK_node, tot11022, tot11023]
  decide +kernel

theorem arows11019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11019 = true := by
  rw [show D2M8K2.u11019 = KTree.node D2M8K2.t11024 (nat_lit 24029958) (nat_lit 3739316520) (nat_lit 0) D2M8K2.t11025 from rfl, allE_node, rows11024, irow11019, rows11025]
  all_goals rfl

theorem atot11019 : totK PD2M8K2 D2M8K2.u11019 = [293190256390, 800946034107, 583828995418, 122219220493, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u11019 = KTree.node D2M8K2.t11024 (nat_lit 24029958) (nat_lit 3739316520) (nat_lit 0) D2M8K2.t11025 from rfl, totK_node, tot11024, tot11025]
  decide +kernel

theorem arows11020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11020 = true := by
  rw [show D2M8K2.u11020 = KTree.node D2M8K2.t11026 (nat_lit 24031562) (nat_lit 3392334402) (nat_lit 0) D2M8K2.t11027 from rfl, allE_node, rows11026, irow11020, rows11027]
  all_goals rfl

theorem atot11020 : totK PD2M8K2 D2M8K2.u11020 = [90019449239, 564387304801, 846332630962, 261393409385, 8708013637, 0, 0, 0] := by
  rw [show D2M8K2.u11020 = KTree.node D2M8K2.t11026 (nat_lit 24031562) (nat_lit 3392334402) (nat_lit 0) D2M8K2.t11027 from rfl, totK_node, tot11026, tot11027]
  decide +kernel

theorem arows11022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11022 = true := by
  rw [show D2M8K2.u11022 = KTree.node D2M8K2.t11028 (nat_lit 24033622) (nat_lit 3421468054) (nat_lit 0) D2M8K2.t11029 from rfl, allE_node, rows11028, irow11022, rows11029]
  all_goals rfl

theorem atot11022 : totK PD2M8K2 D2M8K2.u11022 = [0, 390324351240, 947401471598, 411536633628, 24417634308, 0, 0, 0] := by
  rw [show D2M8K2.u11022 = KTree.node D2M8K2.t11028 (nat_lit 24033622) (nat_lit 3421468054) (nat_lit 0) D2M8K2.t11029 from rfl, totK_node, tot11028, tot11029]
  decide +kernel

theorem arows11023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11023 = true := by
  rw [show D2M8K2.u11023 = KTree.node D2M8K2.t11030 (nat_lit 24034897) (nat_lit 1544864874) (nat_lit 0) D2M8K2.t11031 from rfl, allE_node, rows11030, irow11023, rows11031]
  all_goals rfl

theorem atot11023 : totK PD2M8K2 D2M8K2.u11023 = [0, 102813076522, 719343755683, 798888338722, 107178269969, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11023 = KTree.node D2M8K2.t11030 (nat_lit 24034897) (nat_lit 1544864874) (nat_lit 0) D2M8K2.t11031 from rfl, totK_node, tot11030, tot11031]
  decide +kernel

theorem arows11026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11026 = true := by
  rw [show D2M8K2.u11026 = KTree.node D2M8K2.t11032 (nat_lit 24037589) (nat_lit 1195462002) (nat_lit 0) D2M8K2.t11033 from rfl, allE_node, rows11032, irow11026, rows11033]
  all_goals rfl

theorem atot11026 : totK PD2M8K2 D2M8K2.u11026 = [0, 373051825635, 911677853541, 506516264249, 48505295151, 0, 0, 0] := by
  rw [show D2M8K2.u11026 = KTree.node D2M8K2.t11032 (nat_lit 24037589) (nat_lit 1195462002) (nat_lit 0) D2M8K2.t11033 from rfl, totK_node, tot11032, tot11033]
  decide +kernel

theorem arows11027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11027 = true := by
  rw [show D2M8K2.u11027 = KTree.node D2M8K2.t11034 (nat_lit 24044350) (nat_lit 3883642573) (nat_lit 0) D2M8K2.t11035 from rfl, allE_node, rows11034, irow11027, rows11035]
  all_goals rfl

theorem atot11027 : totK PD2M8K2 D2M8K2.u11027 = [0, 373071657530, 938361658105, 460453827719, 32230650292, 0, 0, 0] := by
  rw [show D2M8K2.u11027 = KTree.node D2M8K2.t11034 (nat_lit 24044350) (nat_lit 3883642573) (nat_lit 0) D2M8K2.t11035 from rfl, totK_node, tot11034, tot11035]
  decide +kernel

theorem arows11029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11029 = true := by
  rw [show D2M8K2.u11029 = KTree.node D2M8K2.t11036 (nat_lit 24046014) (nat_lit 3978513910) (nat_lit 0) D2M8K2.t11037 from rfl, allE_node, rows11036, irow11029, rows11037]
  all_goals rfl

theorem atot11029 : totK PD2M8K2 D2M8K2.u11029 = [0, 19434652667, 510422844252, 909416077241, 276430382034, 13105450397, 0, 0] := by
  rw [show D2M8K2.u11029 = KTree.node D2M8K2.t11036 (nat_lit 24046014) (nat_lit 3978513910) (nat_lit 0) D2M8K2.t11037 from rfl, totK_node, tot11036, tot11037]
  decide +kernel

theorem arows11030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11030 = true := by
  rw [show D2M8K2.u11030 = KTree.node D2M8K2.t11038 (nat_lit 24047432) (nat_lit 3625956652) (nat_lit 0) D2M8K2.t11039 from rfl, allE_node, rows11038, irow11030, rows11039]
  all_goals rfl

theorem atot11030 : totK PD2M8K2 D2M8K2.u11030 = [0, 376173940144, 928481422128, 464313337571, 31731663107, 0, 0, 0] := by
  rw [show D2M8K2.u11030 = KTree.node D2M8K2.t11038 (nat_lit 24047432) (nat_lit 3625956652) (nat_lit 0) D2M8K2.t11039 from rfl, totK_node, tot11038, tot11039]
  decide +kernel

theorem arows11035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11035 = true := by
  rw [show D2M8K2.u11035 = KTree.node D2M8K2.t11040 (nat_lit 24049213) (nat_lit 1039564208) (nat_lit 0) D2M8K2.t11041 from rfl, allE_node, rows11040, irow11035, rows11041]
  all_goals rfl

theorem atot11035 : totK PD2M8K2 D2M8K2.u11035 = [0, 110320052351, 648686286747, 800202324375, 159747015753, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11035 = KTree.node D2M8K2.t11040 (nat_lit 24049213) (nat_lit 1039564208) (nat_lit 0) D2M8K2.t11041 from rfl, totK_node, tot11040, tot11041]
  decide +kernel

theorem arows11036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11036 = true := by
  rw [show D2M8K2.u11036 = KTree.node D2M8K2.t11042 (nat_lit 24051207) (nat_lit 3608696269) (nat_lit 0) D2M8K2.t11043 from rfl, allE_node, rows11042, irow11036, rows11043]
  all_goals rfl

theorem atot11036 : totK PD2M8K2 D2M8K2.u11036 = [33270956665, 336515158937, 872235249668, 517800912704, 45421536417, 0, 0, 0] := by
  rw [show D2M8K2.u11036 = KTree.node D2M8K2.t11042 (nat_lit 24051207) (nat_lit 3608696269) (nat_lit 0) D2M8K2.t11043 from rfl, totK_node, tot11042, tot11043]
  decide +kernel

theorem arows11038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11038 = true := by
  rw [show D2M8K2.u11038 = KTree.node D2M8K2.t11044 (nat_lit 24054715) (nat_lit 2242977437) (nat_lit 0) D2M8K2.t11045 from rfl, allE_node, rows11044, irow11038, rows11045]
  all_goals rfl

theorem atot11038 : totK PD2M8K2 D2M8K2.u11038 = [387991013745, 958945804815, 428213064671, 22386190152, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11038 = KTree.node D2M8K2.t11044 (nat_lit 24054715) (nat_lit 2242977437) (nat_lit 0) D2M8K2.t11045 from rfl, totK_node, tot11044, tot11045]
  decide +kernel

theorem arows11039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11039 = true := by
  rw [show D2M8K2.u11039 = KTree.node D2M8K2.t11046 (nat_lit 24056390) (nat_lit 3643871698) (nat_lit 0) D2M8K2.t11047 from rfl, allE_node, rows11046, irow11039, rows11047]
  all_goals rfl

theorem atot11039 : totK PD2M8K2 D2M8K2.u11039 = [89920432300, 664368437134, 891352498325, 162592495962, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11039 = KTree.node D2M8K2.t11046 (nat_lit 24056390) (nat_lit 3643871698) (nat_lit 0) D2M8K2.t11047 from rfl, totK_node, tot11046, tot11047]
  decide +kernel

theorem arows11042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11042 = true := by
  rw [show D2M8K2.u11042 = KTree.node D2M8K2.t11048 (nat_lit 24058303) (nat_lit 2437959466) (nat_lit 0) D2M8K2.t11049 from rfl, allE_node, rows11048, irow11042, rows11049]
  all_goals rfl

theorem atot11042 : totK PD2M8K2 D2M8K2.u11042 = [256314843456, 808724907772, 629035878202, 132349352654, 13132336007, 0, 0, 0] := by
  rw [show D2M8K2.u11042 = KTree.node D2M8K2.t11048 (nat_lit 24058303) (nat_lit 2437959466) (nat_lit 0) D2M8K2.t11049 from rfl, totK_node, tot11048, tot11049]
  decide +kernel

theorem arows11043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11043 = true := by
  rw [show D2M8K2.u11043 = KTree.node D2M8K2.t11050 (nat_lit 24060102) (nat_lit 3552281165) (nat_lit 0) D2M8K2.t11051 from rfl, allE_node, rows11050, irow11043, rows11051]
  all_goals rfl

theorem atot11043 : totK PD2M8K2 D2M8K2.u11043 = [134351269633, 547674921920, 776029368138, 334154775208, 17536640259, 0, 0, 0] := by
  rw [show D2M8K2.u11043 = KTree.node D2M8K2.t11050 (nat_lit 24060102) (nat_lit 3552281165) (nat_lit 0) D2M8K2.t11051 from rfl, totK_node, tot11050, tot11051]
  decide +kernel

theorem arows11045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11045 = true := by
  rw [show D2M8K2.u11045 = KTree.node D2M8K2.t11052 (nat_lit 24061886) (nat_lit 3853134236) (nat_lit 0) D2M8K2.t11053 from rfl, allE_node, rows11052, irow11045, rows11053]
  all_goals rfl

theorem atot11045 : totK PD2M8K2 D2M8K2.u11045 = [277509460112, 845976222237, 603308074566, 70657251596, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11045 = KTree.node D2M8K2.t11052 (nat_lit 24061886) (nat_lit 3853134236) (nat_lit 0) D2M8K2.t11053 from rfl, totK_node, tot11052, tot11053]
  decide +kernel

theorem arows11046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11046 = true := by
  rw [show D2M8K2.u11046 = KTree.node D2M8K2.t11054 (nat_lit 24063614) (nat_lit 3708250261) (nat_lit 0) D2M8K2.t11055 from rfl, allE_node, rows11054, irow11046, rows11055]
  all_goals rfl

theorem atot11046 : totK PD2M8K2 D2M8K2.u11046 = [104502498990, 571007569518, 826760296823, 260789233506, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u11046 = KTree.node D2M8K2.t11054 (nat_lit 24063614) (nat_lit 3708250261) (nat_lit 0) D2M8K2.t11055 from rfl, totK_node, tot11054, tot11055]
  decide +kernel

theorem arows11050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11050 = true := by
  rw [show D2M8K2.u11050 = KTree.node D2M8K2.t11056 (nat_lit 24065312) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t11057 from rfl, allE_node, rows11056, irow11050, rows11057]
  all_goals rfl

theorem atot11050 : totK PD2M8K2 D2M8K2.u11050 = [303578319377, 881977107573, 571583279407, 53830948167, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11050 = KTree.node D2M8K2.t11056 (nat_lit 24065312) (nat_lit 3817447700) (nat_lit 0) D2M8K2.t11057 from rfl, totK_node, tot11056, tot11057]
  decide +kernel

theorem arows11051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11051 = true := by
  rw [show D2M8K2.u11051 = KTree.node D2M8K2.t11058 (nat_lit 24067034) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t11059 from rfl, allE_node, rows11058, irow11051, rows11059]
  all_goals rfl

theorem atot11051 : totK PD2M8K2 D2M8K2.u11051 = [86654048599, 532579410573, 848226194149, 289453871196, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11051 = KTree.node D2M8K2.t11058 (nat_lit 24067034) (nat_lit 4201800693) (nat_lit 0) D2M8K2.t11059 from rfl, totK_node, tot11058, tot11059]
  decide +kernel

theorem arows11053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11053 = true := by
  rw [show D2M8K2.u11053 = KTree.node D2M8K2.t11060 (nat_lit 24068420) (nat_lit 3280754383) (nat_lit 0) D2M8K2.t11061 from rfl, allE_node, rows11060, irow11053, rows11061]
  all_goals rfl

theorem atot11053 : totK PD2M8K2 D2M8K2.u11053 = [352446817612, 927362423061, 510545980462, 40817807037, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11053 = KTree.node D2M8K2.t11060 (nat_lit 24068420) (nat_lit 3280754383) (nat_lit 0) D2M8K2.t11061 from rfl, totK_node, tot11060, tot11061]
  decide +kernel

theorem arows11054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11054 = true := by
  rw [show D2M8K2.u11054 = KTree.node D2M8K2.t11062 (nat_lit 24070221) (nat_lit 1449081816) (nat_lit 0) D2M8K2.t11063 from rfl, allE_node, rows11062, irow11054, rows11063]
  all_goals rfl

theorem atot11054 : totK PD2M8K2 D2M8K2.u11054 = [0, 512828891928, 1021311310871, 265971976439, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u11054 = KTree.node D2M8K2.t11062 (nat_lit 24070221) (nat_lit 1449081816) (nat_lit 0) D2M8K2.t11063 from rfl, totK_node, tot11062, tot11063]
  decide +kernel

theorem arows11057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11057 = true := by
  rw [show D2M8K2.u11057 = KTree.node D2M8K2.t11064 (nat_lit 24075626) (nat_lit 2974309393) (nat_lit 0) D2M8K2.t11065 from rfl, allE_node, rows11064, irow11057, rows11065]
  all_goals rfl

theorem atot11057 : totK PD2M8K2 D2M8K2.u11057 = [0, 329084385323, 919741354929, 471586100705, 32789939480, 0, 0, 0] := by
  rw [show D2M8K2.u11057 = KTree.node D2M8K2.t11064 (nat_lit 24075626) (nat_lit 2974309393) (nat_lit 0) D2M8K2.t11065 from rfl, totK_node, tot11064, tot11065]
  decide +kernel

theorem arows11058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11058 = true := by
  rw [show D2M8K2.u11058 = KTree.node D2M8K2.t11066 (nat_lit 24077722) (nat_lit 3889443527) (nat_lit 0) D2M8K2.t11067 from rfl, allE_node, rows11066, irow11058, rows11067]
  all_goals rfl

theorem atot11058 : totK PD2M8K2 D2M8K2.u11058 = [0, 173438096905, 773794375065, 726634308274, 103569178992, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11058 = KTree.node D2M8K2.t11066 (nat_lit 24077722) (nat_lit 3889443527) (nat_lit 0) D2M8K2.t11067 from rfl, totK_node, tot11066, tot11067]
  decide +kernel

theorem arows11060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11060 = true := by
  rw [show D2M8K2.u11060 = KTree.node D2M8K2.t11068 (nat_lit 24081460) (nat_lit 4009520606) (nat_lit 0) D2M8K2.t11069 from rfl, allE_node, rows11068, irow11060, rows11069]
  all_goals rfl

theorem atot11060 : totK PD2M8K2 D2M8K2.u11060 = [0, 399903741772, 960781957745, 430395277907, 23658624696, 0, 0, 0] := by
  rw [show D2M8K2.u11060 = KTree.node D2M8K2.t11068 (nat_lit 24081460) (nat_lit 4009520606) (nat_lit 0) D2M8K2.t11069 from rfl, totK_node, tot11068, tot11069]
  decide +kernel

theorem arows11061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11061 = true := by
  rw [show D2M8K2.u11061 = KTree.node D2M8K2.t11070 (nat_lit 24082993) (nat_lit 1514554575) (nat_lit 0) D2M8K2.t11071 from rfl, allE_node, rows11070, irow11061, rows11071]
  all_goals rfl

theorem atot11061 : totK PD2M8K2 D2M8K2.u11061 = [0, 347135103758, 940352856097, 464208132291, 25790587952, 0, 0, 0] := by
  rw [show D2M8K2.u11061 = KTree.node D2M8K2.t11070 (nat_lit 24082993) (nat_lit 1514554575) (nat_lit 0) D2M8K2.t11071 from rfl, totK_node, tot11070, tot11071]
  decide +kernel

theorem arows11067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11067 = true := by
  rw [show D2M8K2.u11067 = KTree.node D2M8K2.t11072 (nat_lit 24086305) (nat_lit 1542665037) (nat_lit 0) D2M8K2.t11073 from rfl, allE_node, rows11072, irow11067, rows11073]
  all_goals rfl

theorem atot11067 : totK PD2M8K2 D2M8K2.u11067 = [0, 400836306974, 952518052449, 420270811253, 18931416259, 0, 0, 0] := by
  rw [show D2M8K2.u11067 = KTree.node D2M8K2.t11072 (nat_lit 24086305) (nat_lit 1542665037) (nat_lit 0) D2M8K2.t11073 from rfl, totK_node, tot11072, tot11073]
  decide +kernel

theorem arows11068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11068 = true := by
  rw [show D2M8K2.u11068 = KTree.node D2M8K2.t11074 (nat_lit 24089304) (nat_lit 3274590043) (nat_lit 0) D2M8K2.t11075 from rfl, allE_node, rows11074, irow11068, rows11075]
  all_goals rfl

theorem atot11068 : totK PD2M8K2 D2M8K2.u11068 = [0, 277352291330, 878512273689, 564342080422, 51331368037, 0, 0, 0] := by
  rw [show D2M8K2.u11068 = KTree.node D2M8K2.t11074 (nat_lit 24089304) (nat_lit 3274590043) (nat_lit 0) D2M8K2.t11075 from rfl, totK_node, tot11074, tot11075]
  decide +kernel

theorem arows11070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11070 = true := by
  rw [show D2M8K2.u11070 = KTree.node D2M8K2.t11076 (nat_lit 24091265) (nat_lit 2098391034) (nat_lit 0) D2M8K2.t11077 from rfl, allE_node, rows11076, irow11070, rows11077]
  all_goals rfl

theorem atot11070 : totK PD2M8K2 D2M8K2.u11070 = [176301523965, 350521227424, 443038860350, 624537135335, 170150085366, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11070 = KTree.node D2M8K2.t11076 (nat_lit 24091265) (nat_lit 2098391034) (nat_lit 0) D2M8K2.t11077 from rfl, totK_node, tot11076, tot11077]
  decide +kernel

theorem arows11071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11071 = true := by
  rw [show D2M8K2.u11071 = KTree.node D2M8K2.t11078 (nat_lit 24096580) (nat_lit 3917132378) (nat_lit 0) D2M8K2.t11079 from rfl, allE_node, rows11078, irow11071, rows11079]
  all_goals rfl

theorem atot11071 : totK PD2M8K2 D2M8K2.u11071 = [245026313010, 814619260431, 626333885140, 96269117878, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11071 = KTree.node D2M8K2.t11078 (nat_lit 24096580) (nat_lit 3917132378) (nat_lit 0) D2M8K2.t11079 from rfl, totK_node, tot11078, tot11079]
  decide +kernel

theorem arows11074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11074 = true := by
  rw [show D2M8K2.u11074 = KTree.node D2M8K2.t11080 (nat_lit 24098526) (nat_lit 3894591339) (nat_lit 0) D2M8K2.t11081 from rfl, allE_node, rows11080, irow11074, rows11081]
  all_goals rfl

theorem atot11074 : totK PD2M8K2 D2M8K2.u11074 = [190366795483, 770708890946, 758290248930, 99896824931, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11074 = KTree.node D2M8K2.t11080 (nat_lit 24098526) (nat_lit 3894591339) (nat_lit 0) D2M8K2.t11081 from rfl, totK_node, tot11080, tot11081]
  decide +kernel

theorem arows11075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11075 = true := by
  rw [show D2M8K2.u11075 = KTree.node D2M8K2.t11082 (nat_lit 24103708) (nat_lit 3928746637) (nat_lit 0) D2M8K2.t11083 from rfl, allE_node, rows11082, irow11075, rows11083]
  all_goals rfl

theorem atot11075 : totK PD2M8K2 D2M8K2.u11075 = [210934628431, 771413524286, 697733653312, 113047163907, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u11075 = KTree.node D2M8K2.t11082 (nat_lit 24103708) (nat_lit 3928746637) (nat_lit 0) D2M8K2.t11083 from rfl, totK_node, tot11082, tot11083]
  decide +kernel

theorem arows11077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11077 = true := by
  rw [show D2M8K2.u11077 = KTree.node D2M8K2.t11084 (nat_lit 24105445) (nat_lit 1357964992) (nat_lit 0) D2M8K2.t11085 from rfl, allE_node, rows11084, irow11077, rows11085]
  all_goals rfl

theorem atot11077 : totK PD2M8K2 D2M8K2.u11077 = [190484942520, 662775640820, 708677046446, 214673131189, 11879463720, 0, 0, 0] := by
  rw [show D2M8K2.u11077 = KTree.node D2M8K2.t11084 (nat_lit 24105445) (nat_lit 1357964992) (nat_lit 0) D2M8K2.t11085 from rfl, totK_node, tot11084, tot11085]
  decide +kernel

theorem arows11078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11078 = true := by
  rw [show D2M8K2.u11078 = KTree.node D2M8K2.t11086 (nat_lit 24107171) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t11087 from rfl, allE_node, rows11086, irow11078, rows11087]
  all_goals rfl

theorem atot11078 : totK PD2M8K2 D2M8K2.u11078 = [211067643887, 765898200943, 700035862730, 119555911835, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u11078 = KTree.node D2M8K2.t11086 (nat_lit 24107171) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t11087 from rfl, totK_node, tot11086, tot11087]
  decide +kernel

theorem arows11082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11082 = true := by
  rw [show D2M8K2.u11082 = KTree.node D2M8K2.t11088 (nat_lit 24108901) (nat_lit 1358151366) (nat_lit 0) D2M8K2.t11089 from rfl, allE_node, rows11088, irow11082, rows11089]
  all_goals rfl

theorem atot11082 : totK PD2M8K2 D2M8K2.u11082 = [196322580659, 665684730759, 706314591153, 221337229414, 12045711471, 0, 0, 0] := by
  rw [show D2M8K2.u11082 = KTree.node D2M8K2.t11088 (nat_lit 24108901) (nat_lit 1358151366) (nat_lit 0) D2M8K2.t11089 from rfl, totK_node, tot11088, tot11089]
  decide +kernel

theorem arows11083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11083 = true := by
  rw [show D2M8K2.u11083 = KTree.node D2M8K2.t11090 (nat_lit 24114002) (nat_lit 4025594030) (nat_lit 0) D2M8K2.t11091 from rfl, allE_node, rows11090, irow11083, rows11091]
  all_goals rfl

theorem atot11083 : totK PD2M8K2 D2M8K2.u11083 = [231510415361, 782986454220, 670669224579, 116985032967, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u11083 = KTree.node D2M8K2.t11090 (nat_lit 24114002) (nat_lit 4025594030) (nat_lit 0) D2M8K2.t11091 from rfl, totK_node, tot11090, tot11091]
  decide +kernel

theorem arows11085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11085 = true := by
  rw [show D2M8K2.u11085 = KTree.node D2M8K2.t11092 (nat_lit 24115693) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t11093 from rfl, allE_node, rows11092, irow11085, rows11093]
  all_goals rfl

theorem atot11085 : totK PD2M8K2 D2M8K2.u11085 = [0, 399729449849, 956759154805, 402405307880, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u11085 = KTree.node D2M8K2.t11092 (nat_lit 24115693) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t11093 from rfl, totK_node, tot11092, tot11093]
  decide +kernel

theorem arows11086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11086 = true := by
  rw [show D2M8K2.u11086 = KTree.node D2M8K2.t11094 (nat_lit 24117206) (nat_lit 2686994097) (nat_lit 0) D2M8K2.t11095 from rfl, allE_node, rows11094, irow11086, rows11095]
  all_goals rfl

theorem atot11086 : totK PD2M8K2 D2M8K2.u11086 = [0, 303510602080, 893521900575, 535826844514, 39186623309, 0, 0, 0] := by
  rw [show D2M8K2.u11086 = KTree.node D2M8K2.t11094 (nat_lit 24117206) (nat_lit 2686994097) (nat_lit 0) D2M8K2.t11095 from rfl, totK_node, tot11094, tot11095]
  decide +kernel

theorem arows11089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11089 = true := by
  rw [show D2M8K2.u11089 = KTree.node D2M8K2.t11096 (nat_lit 24119209) (nat_lit 1491446707) (nat_lit 0) D2M8K2.t11097 from rfl, allE_node, rows11096, irow11089, rows11097]
  all_goals rfl

theorem atot11089 : totK PD2M8K2 D2M8K2.u11089 = [0, 171648112585, 726938715780, 768802700087, 109808140476, 1310285577, 0, 0] := by
  rw [show D2M8K2.u11089 = KTree.node D2M8K2.t11096 (nat_lit 24119209) (nat_lit 1491446707) (nat_lit 0) D2M8K2.t11097 from rfl, totK_node, tot11096, tot11097]
  decide +kernel

theorem arows11090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11090 = true := by
  rw [show D2M8K2.u11090 = KTree.node D2M8K2.t11098 (nat_lit 24124390) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t11099 from rfl, allE_node, rows11098, irow11090, rows11099]
  all_goals rfl

theorem atot11090 : totK PD2M8K2 D2M8K2.u11090 = [0, 228030834965, 797901329116, 658099146334, 86751512363, 1075657031, 0, 0] := by
  rw [show D2M8K2.u11090 = KTree.node D2M8K2.t11098 (nat_lit 24124390) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t11099 from rfl, totK_node, tot11098, tot11099]
  decide +kernel

theorem arows11092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11092 = true := by
  rw [show D2M8K2.u11092 = KTree.node D2M8K2.t11100 (nat_lit 24126450) (nat_lit 3385779123) (nat_lit 0) D2M8K2.t11101 from rfl, allE_node, rows11100, irow11092, rows11101]
  all_goals rfl

theorem atot11092 : totK PD2M8K2 D2M8K2.u11092 = [0, 245011211565, 762487890904, 640947198405, 126183169194, 3804183361, 0, 0] := by
  rw [show D2M8K2.u11092 = KTree.node D2M8K2.t11100 (nat_lit 24126450) (nat_lit 3385779123) (nat_lit 0) D2M8K2.t11101 from rfl, totK_node, tot11100, tot11101]
  decide +kernel

theorem arows11093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11093 = true := by
  rw [show D2M8K2.u11093 = KTree.node D2M8K2.t11102 (nat_lit 24128046) (nat_lit 3844506042) (nat_lit 0) D2M8K2.t11103 from rfl, allE_node, rows11102, irow11093, rows11103]
  all_goals rfl

theorem atot11093 : totK PD2M8K2 D2M8K2.u11093 = [0, 154925078361, 702419909988, 756004900080, 144489683633, 2160984415, 0, 0] := by
  rw [show D2M8K2.u11093 = KTree.node D2M8K2.t11102 (nat_lit 24128046) (nat_lit 3844506042) (nat_lit 0) D2M8K2.t11103 from rfl, totK_node, tot11102, tot11103]
  decide +kernel

theorem arows11098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11098 = true := by
  rw [show D2M8K2.u11098 = KTree.node D2M8K2.t11104 (nat_lit 24133592) (nat_lit 2803403647) (nat_lit 0) D2M8K2.t11105 from rfl, allE_node, rows11104, irow11098, rows11105]
  all_goals rfl

theorem atot11098 : totK PD2M8K2 D2M8K2.u11098 = [0, 300796169211, 852184274773, 563560280876, 74620398068, 1689881148, 0, 0] := by
  rw [show D2M8K2.u11098 = KTree.node D2M8K2.t11104 (nat_lit 24133592) (nat_lit 2803403647) (nat_lit 0) D2M8K2.t11105 from rfl, totK_node, tot11104, tot11105]
  decide +kernel

theorem arows11099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11099 = true := by
  rw [show D2M8K2.u11099 = KTree.node D2M8K2.t11106 (nat_lit 24135062) (nat_lit 2833896980) (nat_lit 0) D2M8K2.t11107 from rfl, allE_node, rows11106, irow11099, rows11107]
  all_goals rfl

theorem atot11099 : totK PD2M8K2 D2M8K2.u11099 = [0, 125224413203, 659464155461, 798043766591, 182342542488, 4811815119, 0, 0] := by
  rw [show D2M8K2.u11099 = KTree.node D2M8K2.t11106 (nat_lit 24135062) (nat_lit 2833896980) (nat_lit 0) D2M8K2.t11107 from rfl, totK_node, tot11106, tot11107]
  decide +kernel

theorem arows11101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11101 = true := by
  rw [show D2M8K2.u11101 = KTree.node D2M8K2.t11108 (nat_lit 24136779) (nat_lit 2783640611) (nat_lit 0) D2M8K2.t11109 from rfl, allE_node, rows11108, irow11101, rows11109]
  all_goals rfl

theorem atot11101 : totK PD2M8K2 D2M8K2.u11101 = [0, 248762059863, 692544641195, 614154903334, 216359181147, 16939352947, 0, 0] := by
  rw [show D2M8K2.u11101 = KTree.node D2M8K2.t11108 (nat_lit 24136779) (nat_lit 2783640611) (nat_lit 0) D2M8K2.t11109 from rfl, totK_node, tot11108, tot11109]
  decide +kernel

theorem arows11102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11102 = true := by
  rw [show D2M8K2.u11102 = KTree.node D2M8K2.t11110 (nat_lit 24138277) (nat_lit 1367397861) (nat_lit 0) D2M8K2.t11111 from rfl, allE_node, rows11110, irow11102, rows11111]
  all_goals rfl

theorem atot11102 : totK PD2M8K2 D2M8K2.u11102 = [0, 192527614797, 771178878260, 707910062590, 119340074925, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11102 = KTree.node D2M8K2.t11110 (nat_lit 24138277) (nat_lit 1367397861) (nat_lit 0) D2M8K2.t11111 from rfl, totK_node, tot11110, tot11111]
  decide +kernel

theorem arows11105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11105 = true := by
  rw [show D2M8K2.u11105 = KTree.node D2M8K2.t11112 (nat_lit 24143761) (nat_lit 1561206651) (nat_lit 0) D2M8K2.t11113 from rfl, allE_node, rows11112, irow11105, rows11113]
  all_goals rfl

theorem atot11105 : totK PD2M8K2 D2M8K2.u11105 = [0, 245714175996, 839161354392, 663252366680, 66920044116, 0, 0, 0] := by
  rw [show D2M8K2.u11105 = KTree.node D2M8K2.t11112 (nat_lit 24143761) (nat_lit 1561206651) (nat_lit 0) D2M8K2.t11113 from rfl, totK_node, tot11112, tot11113]
  decide +kernel

theorem arows11106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11106 = true := by
  rw [show D2M8K2.u11106 = KTree.node D2M8K2.t11114 (nat_lit 24145326) (nat_lit 3665884571) (nat_lit 0) D2M8K2.t11115 from rfl, allE_node, rows11114, irow11106, rows11115]
  all_goals rfl

theorem atot11106 : totK PD2M8K2 D2M8K2.u11106 = [0, 168631518356, 702328016148, 750548918439, 137312442066, 2309606161, 0, 0] := by
  rw [show D2M8K2.u11106 = KTree.node D2M8K2.t11114 (nat_lit 24145326) (nat_lit 3665884571) (nat_lit 0) D2M8K2.t11115 from rfl, totK_node, tot11114, tot11115]
  decide +kernel

theorem arows11108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11108 = true := by
  rw [show D2M8K2.u11108 = KTree.node D2M8K2.t11116 (nat_lit 24147177) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t11117 from rfl, allE_node, rows11116, irow11108, rows11117]
  all_goals rfl

theorem atot11108 : totK PD2M8K2 D2M8K2.u11108 = [0, 245858540806, 728903414508, 631293141486, 148740955090, 10582051848, 0, 0] := by
  rw [show D2M8K2.u11108 = KTree.node D2M8K2.t11116 (nat_lit 24147177) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t11117 from rfl, totK_node, tot11116, tot11117]
  decide +kernel

theorem arows11109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11109 = true := by
  rw [show D2M8K2.u11109 = KTree.node D2M8K2.t11118 (nat_lit 24148717) (nat_lit 1047102671) (nat_lit 0) D2M8K2.t11119 from rfl, allE_node, rows11118, irow11109, rows11119]
  all_goals rfl

theorem atot11109 : totK PD2M8K2 D2M8K2.u11109 = [0, 168696510211, 741071858661, 749969417216, 114884890762, 1198073392, 0, 0] := by
  rw [show D2M8K2.u11109 = KTree.node D2M8K2.t11118 (nat_lit 24148717) (nat_lit 1047102671) (nat_lit 0) D2M8K2.t11119 from rfl, totK_node, tot11118, tot11119]
  decide +kernel

theorem arows11113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11113 = true := by
  rw [show D2M8K2.u11113 = KTree.node D2M8K2.t11120 (nat_lit 24150588) (nat_lit 3236655436) (nat_lit 0) D2M8K2.t11121 from rfl, allE_node, rows11120, irow11113, rows11121]
  all_goals rfl

theorem atot11113 : totK PD2M8K2 D2M8K2.u11113 = [0, 240131806118, 681404558510, 640229744301, 182836946140, 11894306413, 0, 0] := by
  rw [show D2M8K2.u11113 = KTree.node D2M8K2.t11120 (nat_lit 24150588) (nat_lit 3236655436) (nat_lit 0) D2M8K2.t11121 from rfl, totK_node, tot11120, tot11121]
  decide +kernel

theorem arows11114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11114 = true := by
  rw [show D2M8K2.u11114 = KTree.node D2M8K2.t11122 (nat_lit 24151825) (nat_lit 1526015612) (nat_lit 0) D2M8K2.t11123 from rfl, allE_node, rows11122, irow11114, rows11123]
  all_goals rfl

theorem atot11114 : totK PD2M8K2 D2M8K2.u11114 = [0, 175892744135, 764778413509, 733857386182, 96483545615, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11114 = KTree.node D2M8K2.t11122 (nat_lit 24151825) (nat_lit 1526015612) (nat_lit 0) D2M8K2.t11123 from rfl, totK_node, tot11122, tot11123]
  decide +kernel

theorem arows11116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11116 = true := by
  rw [show D2M8K2.u11116 = KTree.node D2M8K2.t11124 (nat_lit 24154120) (nat_lit 3769889359) (nat_lit 0) D2M8K2.t11125 from rfl, allE_node, rows11124, irow11116, rows11125]
  all_goals rfl

theorem atot11116 : totK PD2M8K2 D2M8K2.u11116 = [0, 230840086652, 763248381997, 656444452014, 115461319131, 3838026431, 0, 0] := by
  rw [show D2M8K2.u11116 = KTree.node D2M8K2.t11124 (nat_lit 24154120) (nat_lit 3769889359) (nat_lit 0) D2M8K2.t11125 from rfl, totK_node, tot11124, tot11125]
  decide +kernel

theorem arows11117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11117 = true := by
  rw [show D2M8K2.u11117 = KTree.node D2M8K2.t11126 (nat_lit 24155711) (nat_lit 2760641158) (nat_lit 0) D2M8K2.t11127 from rfl, allE_node, rows11126, irow11117, rows11127]
  all_goals rfl

theorem atot11117 : totK PD2M8K2 D2M8K2.u11117 = [0, 169213615022, 669533988295, 750899831753, 169462265070, 4928554699, 0, 0] := by
  rw [show D2M8K2.u11117 = KTree.node D2M8K2.t11126 (nat_lit 24155711) (nat_lit 2760641158) (nat_lit 0) D2M8K2.t11127 from rfl, totK_node, tot11126, tot11127]
  decide +kernel

theorem arows11120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11120 = true := by
  rw [show D2M8K2.u11120 = KTree.node D2M8K2.t11128 (nat_lit 24157451) (nat_lit 2925092234) (nat_lit 0) D2M8K2.t11129 from rfl, allE_node, rows11128, irow11120, rows11129]
  all_goals rfl

theorem atot11120 : totK PD2M8K2 D2M8K2.u11120 = [0, 0, 389537838103, 939096300019, 396082458153, 26454322738, 0, 0] := by
  rw [show D2M8K2.u11120 = KTree.node D2M8K2.t11128 (nat_lit 24157451) (nat_lit 2925092234) (nat_lit 0) D2M8K2.t11129 from rfl, totK_node, tot11128, tot11129]
  decide +kernel

theorem arows11121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11121 = true := by
  rw [show D2M8K2.u11121 = KTree.node D2M8K2.t11130 (nat_lit 24158966) (nat_lit 3255310897) (nat_lit 0) D2M8K2.t11131 from rfl, allE_node, rows11130, irow11121, rows11131]
  all_goals rfl

theorem atot11121 : totK PD2M8K2 D2M8K2.u11121 = [0, 0, 213213442716, 770513922475, 629218510802, 113827446485, 1369150432, 0] := by
  rw [show D2M8K2.u11121 = KTree.node D2M8K2.t11130 (nat_lit 24158966) (nat_lit 3255310897) (nat_lit 0) D2M8K2.t11131 from rfl, totK_node, tot11130, tot11131]
  decide +kernel

theorem arows11123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11123 = true := by
  rw [show D2M8K2.u11123 = KTree.node D2M8K2.t11132 (nat_lit 24164512) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t11133 from rfl, allE_node, rows11132, irow11123, rows11133]
  all_goals rfl

theorem atot11123 : totK PD2M8K2 D2M8K2.u11123 = [0, 0, 297714335343, 874106026609, 522805123689, 50754145376, 0, 0] := by
  rw [show D2M8K2.u11123 = KTree.node D2M8K2.t11132 (nat_lit 24164512) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t11133 from rfl, totK_node, tot11132, tot11133]
  decide +kernel

theorem arows11124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11124 = true := by
  rw [show D2M8K2.u11124 = KTree.node D2M8K2.t11134 (nat_lit 24167953) (nat_lit 1561210761) (nat_lit 0) D2M8K2.t11135 from rfl, allE_node, rows11134, irow11124, rows11135]
  all_goals rfl

theorem atot11124 : totK PD2M8K2 D2M8K2.u11124 = [0, 0, 398473441146, 948619188981, 376634829234, 22217418727, 0, 0] := by
  rw [show D2M8K2.u11124 = KTree.node D2M8K2.t11134 (nat_lit 24167953) (nat_lit 1561210761) (nat_lit 0) D2M8K2.t11135 from rfl, totK_node, tot11134, tot11135]
  decide +kernel

theorem arows11131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11131 = true := by
  rw [show D2M8K2.u11131 = KTree.node D2M8K2.t11136 (nat_lit 24171395) (nat_lit 2780300125) (nat_lit 0) D2M8K2.t11137 from rfl, allE_node, rows11136, irow11131, rows11137]
  all_goals rfl

theorem atot11131 : totK PD2M8K2 D2M8K2.u11131 = [0, 0, 409713398283, 949546469212, 363276282329, 22045623307, 0, 0] := by
  rw [show D2M8K2.u11131 = KTree.node D2M8K2.t11136 (nat_lit 24171395) (nat_lit 2780300125) (nat_lit 0) D2M8K2.t11137 from rfl, totK_node, tot11136, tot11137]
  decide +kernel

theorem arows11132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11132 = true := by
  rw [show D2M8K2.u11132 = KTree.node D2M8K2.t11138 (nat_lit 24174841) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t11139 from rfl, allE_node, rows11138, irow11132, rows11139]
  all_goals rfl

theorem atot11132 : totK PD2M8K2 D2M8K2.u11132 = [0, 0, 404787268043, 964053517069, 362581436179, 17474881745, 0, 0] := by
  rw [show D2M8K2.u11132 = KTree.node D2M8K2.t11138 (nat_lit 24174841) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t11139 from rfl, totK_node, tot11138, tot11139]
  decide +kernel

theorem arows11134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11134 = true := by
  rw [show D2M8K2.u11134 = KTree.node D2M8K2.t11140 (nat_lit 24219769) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t11141 from rfl, allE_node, rows11140, irow11134, rows11141]
  all_goals rfl

theorem atot11134 : totK PD2M8K2 D2M8K2.u11134 = [0, 249048924493, 699617998587, 602655565983, 209723342689, 17192599809, 0, 0] := by
  rw [show D2M8K2.u11134 = KTree.node D2M8K2.t11140 (nat_lit 24219769) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t11141 from rfl, totK_node, tot11140, tot11141]
  decide +kernel

theorem arows11135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11135 = true := by
  rw [show D2M8K2.u11135 = KTree.node D2M8K2.t11142 (nat_lit 24221314) (nat_lit 3935865609) (nat_lit 0) D2M8K2.t11143 from rfl, allE_node, rows11142, irow11135, rows11143]
  all_goals rfl

theorem atot11135 : totK PD2M8K2 D2M8K2.u11135 = [0, 168436381521, 717171551575, 741423569334, 130538788541, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11135 = KTree.node D2M8K2.t11142 (nat_lit 24221314) (nat_lit 3935865609) (nat_lit 0) D2M8K2.t11143 from rfl, totK_node, tot11142, tot11143]
  decide +kernel

theorem arows11138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11138 = true := by
  rw [show D2M8K2.u11138 = KTree.node D2M8K2.t11144 (nat_lit 24223659) (nat_lit 3681345420) (nat_lit 0) D2M8K2.t11145 from rfl, allE_node, rows11144, irow11138, rows11145]
  all_goals rfl

theorem atot11138 : totK PD2M8K2 D2M8K2.u11138 = [0, 274390061548, 847728039758, 636960584782, 66457729285, 0, 0, 0] := by
  rw [show D2M8K2.u11138 = KTree.node D2M8K2.t11144 (nat_lit 24223659) (nat_lit 3681345420) (nat_lit 0) D2M8K2.t11145 from rfl, totK_node, tot11144, tot11145]
  decide +kernel

theorem arows11139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11139 = true := by
  rw [show D2M8K2.u11139 = KTree.node D2M8K2.t11146 (nat_lit 24225622) (nat_lit 2951961772) (nat_lit 0) D2M8K2.t11147 from rfl, allE_node, rows11146, irow11139, rows11147]
  all_goals rfl

theorem atot11139 : totK PD2M8K2 D2M8K2.u11139 = [0, 142874825808, 642372545171, 821153882083, 209271383486, 5284349065, 0, 0] := by
  rw [show D2M8K2.u11139 = KTree.node D2M8K2.t11146 (nat_lit 24225622) (nat_lit 2951961772) (nat_lit 0) D2M8K2.t11147 from rfl, totK_node, tot11146, tot11147]
  decide +kernel

theorem arows11141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11141 = true := by
  rw [show D2M8K2.u11141 = KTree.node D2M8K2.t11148 (nat_lit 24227329) (nat_lit 1425605381) (nat_lit 0) D2M8K2.t11149 from rfl, allE_node, rows11148, irow11141, rows11149]
  all_goals rfl

theorem atot11141 : totK PD2M8K2 D2M8K2.u11141 = [0, 349999861274, 933809766385, 501495191796, 35323669199, 0, 0, 0] := by
  rw [show D2M8K2.u11141 = KTree.node D2M8K2.t11148 (nat_lit 24227329) (nat_lit 1425605381) (nat_lit 0) D2M8K2.t11149 from rfl, totK_node, tot11148, tot11149]
  decide +kernel

theorem arows11142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11142 = true := by
  rw [show D2M8K2.u11142 = KTree.node D2M8K2.t11150 (nat_lit 24228991) (nat_lit 1506151173) (nat_lit 0) D2M8K2.t11151 from rfl, allE_node, rows11150, irow11142, rows11151]
  all_goals rfl

theorem atot11142 : totK PD2M8K2 D2M8K2.u11142 = [0, 22021801666, 487344071980, 959931188466, 289764680774, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11142 = KTree.node D2M8K2.t11150 (nat_lit 24228991) (nat_lit 1506151173) (nat_lit 0) D2M8K2.t11151 from rfl, totK_node, tot11150, tot11151]
  decide +kernel

theorem arows11146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11146 = true := by
  rw [show D2M8K2.u11146 = KTree.node D2M8K2.t11152 (nat_lit 24234104) (nat_lit 3784687220) (nat_lit 0) D2M8K2.t11153 from rfl, allE_node, rows11152, irow11146, rows11153]
  all_goals rfl

theorem atot11146 : totK PD2M8K2 D2M8K2.u11146 = [0, 389044801386, 919682595240, 461976822564, 38113243126, 0, 0, 0] := by
  rw [show D2M8K2.u11146 = KTree.node D2M8K2.t11152 (nat_lit 24234104) (nat_lit 3784687220) (nat_lit 0) D2M8K2.t11153 from rfl, totK_node, tot11152, tot11153]
  decide +kernel

theorem arows11147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11147 = true := by
  rw [show D2M8K2.u11147 = KTree.node D2M8K2.t11154 (nat_lit 24235846) (nat_lit 3404296931) (nat_lit 0) D2M8K2.t11155 from rfl, allE_node, rows11154, irow11147, rows11155]
  all_goals rfl

theorem atot11147 : totK PD2M8K2 D2M8K2.u11147 = [0, 84566615325, 624604461048, 876969389612, 182296183279, 4917269347, 0, 0] := by
  rw [show D2M8K2.u11147 = KTree.node D2M8K2.t11154 (nat_lit 24235846) (nat_lit 3404296931) (nat_lit 0) D2M8K2.t11155 from rfl, totK_node, tot11154, tot11155]
  decide +kernel

theorem arows11149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11149 = true := by
  rw [show D2M8K2.u11149 = KTree.node D2M8K2.t11156 (nat_lit 24237744) (nat_lit 3260456199) (nat_lit 0) D2M8K2.t11157 from rfl, allE_node, rows11156, irow11149, rows11157]
  all_goals rfl

theorem atot11149 : totK PD2M8K2 D2M8K2.u11149 = [0, 298072348121, 895238212332, 572352219622, 50146708781, 0, 0, 0] := by
  rw [show D2M8K2.u11149 = KTree.node D2M8K2.t11156 (nat_lit 24237744) (nat_lit 3260456199) (nat_lit 0) D2M8K2.t11157 from rfl, totK_node, tot11156, tot11157]
  decide +kernel

theorem arows11150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11150 = true := by
  rw [show D2M8K2.u11150 = KTree.node D2M8K2.t11158 (nat_lit 24239532) (nat_lit 3430610864) (nat_lit 0) D2M8K2.t11159 from rfl, allE_node, rows11158, irow11150, rows11159]
  all_goals rfl

theorem atot11150 : totK PD2M8K2 D2M8K2.u11150 = [0, 90907693037, 537693549052, 845321312181, 284669196486, 13684302317, 0, 0] := by
  rw [show D2M8K2.u11150 = KTree.node D2M8K2.t11158 (nat_lit 24239532) (nat_lit 3430610864) (nat_lit 0) D2M8K2.t11159 from rfl, totK_node, tot11158, tot11159]
  decide +kernel

theorem arows11153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11153 = true := by
  rw [show D2M8K2.u11153 = KTree.node D2M8K2.t11160 (nat_lit 24262294) (nat_lit 2772899451) (nat_lit 0) D2M8K2.t11161 from rfl, allE_node, rows11160, irow11153, rows11161]
  all_goals rfl

theorem atot11153 : totK PD2M8K2 D2M8K2.u11153 = [0, 326611931626, 903955732042, 504470217572, 35868602280, 0, 0, 0] := by
  rw [show D2M8K2.u11153 = KTree.node D2M8K2.t11160 (nat_lit 24262294) (nat_lit 2772899451) (nat_lit 0) D2M8K2.t11161 from rfl, totK_node, tot11160, tot11161]
  decide +kernel

theorem arows11154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11154 = true := by
  rw [show D2M8K2.u11154 = KTree.node D2M8K2.t11162 (nat_lit 24264082) (nat_lit 2772415005) (nat_lit 0) D2M8K2.t11163 from rfl, allE_node, rows11162, irow11154, rows11163]
  all_goals rfl

theorem atot11154 : totK PD2M8K2 D2M8K2.u11154 = [0, 134457132423, 665980275365, 853931567030, 158456804035, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11154 = KTree.node D2M8K2.t11162 (nat_lit 24264082) (nat_lit 2772415005) (nat_lit 0) D2M8K2.t11163 from rfl, totK_node, tot11162, tot11163]
  decide +kernel

theorem arows11156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11156 = true := by
  rw [show D2M8K2.u11156 = KTree.node D2M8K2.t11164 (nat_lit 24266153) (nat_lit 1476243435) (nat_lit 0) D2M8K2.t11165 from rfl, allE_node, rows11164, irow11156, rows11165]
  all_goals rfl

theorem atot11156 : totK PD2M8K2 D2M8K2.u11156 = [0, 196018273815, 766699953006, 710595257999, 143853885187, 4002076922, 0, 0] := by
  rw [show D2M8K2.u11156 = KTree.node D2M8K2.t11164 (nat_lit 24266153) (nat_lit 1476243435) (nat_lit 0) D2M8K2.t11165 from rfl, totK_node, tot11164, tot11165]
  decide +kernel

theorem arows11157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11157 = true := by
  rw [show D2M8K2.u11157 = KTree.node D2M8K2.t11166 (nat_lit 24271814) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t11167 from rfl, allE_node, rows11166, irow11157, rows11167]
  all_goals rfl

theorem atot11157 : totK PD2M8K2 D2M8K2.u11157 = [0, 275229502788, 800968927426, 634390751734, 112183261309, 1346730670, 0, 0] := by
  rw [show D2M8K2.u11157 = KTree.node D2M8K2.t11166 (nat_lit 24271814) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t11167 from rfl, totK_node, tot11166, tot11167]
  decide +kernel

theorem arows11162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11162 = true := by
  rw [show D2M8K2.u11162 = KTree.node D2M8K2.t11168 (nat_lit 24273268) (nat_lit 2882252414) (nat_lit 0) D2M8K2.t11169 from rfl, allE_node, rows11168, irow11162, rows11169]
  all_goals rfl

theorem atot11162 : totK PD2M8K2 D2M8K2.u11162 = [0, 161889094836, 698391290588, 772995222406, 163359195771, 2329117419, 0, 0] := by
  rw [show D2M8K2.u11162 = KTree.node D2M8K2.t11168 (nat_lit 24273268) (nat_lit 2882252414) (nat_lit 0) D2M8K2.t11169 from rfl, totK_node, tot11168, tot11169]
  decide +kernel

theorem arows11163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11163 = true := by
  rw [show D2M8K2.u11163 = KTree.node D2M8K2.t11170 (nat_lit 24275048) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t11171 from rfl, allE_node, rows11170, irow11163, rows11171]
  all_goals rfl

theorem atot11163 : totK PD2M8K2 D2M8K2.u11163 = [0, 232110450907, 722360054948, 647409380973, 165267917265, 10841558499, 0, 0] := by
  rw [show D2M8K2.u11163 = KTree.node D2M8K2.t11170 (nat_lit 24275048) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t11171 from rfl, totK_node, tot11170, tot11171]
  decide +kernel

theorem arows11165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11165 = true := by
  rw [show D2M8K2.u11165 = KTree.node D2M8K2.t11172 (nat_lit 24276315) (nat_lit 2569358548) (nat_lit 0) D2M8K2.t11173 from rfl, allE_node, rows11172, irow11165, rows11173]
  all_goals rfl

theorem atot11165 : totK PD2M8K2 D2M8K2.u11165 = [0, 179009229301, 759217165300, 751751753404, 103013419646, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11165 = KTree.node D2M8K2.t11172 (nat_lit 24276315) (nat_lit 2569358548) (nat_lit 0) D2M8K2.t11173 from rfl, totK_node, tot11172, tot11173]
  decide +kernel

theorem arows11166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11166 = true := by
  rw [show D2M8K2.u11166 = KTree.node D2M8K2.t11174 (nat_lit 24278644) (nat_lit 2657628201) (nat_lit 0) D2M8K2.t11175 from rfl, allE_node, rows11174, irow11166, rows11175]
  all_goals rfl

theorem atot11166 : totK PD2M8K2 D2M8K2.u11166 = [0, 292784908091, 787204933789, 603649080945, 117327900714, 3821179711, 0, 0] := by
  rw [show D2M8K2.u11166 = KTree.node D2M8K2.t11174 (nat_lit 24278644) (nat_lit 2657628201) (nat_lit 0) D2M8K2.t11175 from rfl, totK_node, tot11174, tot11175]
  decide +kernel

theorem arows11169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11169 = true := by
  rw [show D2M8K2.u11169 = KTree.node D2M8K2.t11176 (nat_lit 24280262) (nat_lit 3357025746) (nat_lit 0) D2M8K2.t11177 from rfl, allE_node, rows11176, irow11169, rows11177]
  all_goals rfl

theorem atot11169 : totK PD2M8K2 D2M8K2.u11169 = [0, 89955272290, 628436290519, 855339525479, 204020365704, 4957057700, 0, 0] := by
  rw [show D2M8K2.u11169 = KTree.node D2M8K2.t11176 (nat_lit 24280262) (nat_lit 3357025746) (nat_lit 0) D2M8K2.t11177 from rfl, totK_node, tot11176, tot11177]
  decide +kernel

theorem arows11170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11170 = true := by
  rw [show D2M8K2.u11170 = KTree.node D2M8K2.t11178 (nat_lit 24303201) (nat_lit 1787134696) (nat_lit 0) D2M8K2.t11179 from rfl, allE_node, rows11178, irow11170, rows11179]
  all_goals rfl

theorem atot11170 : totK PD2M8K2 D2M8K2.u11170 = [0, 294166280893, 803147965679, 549712594243, 125241865255, 8757608180, 0, 0] := by
  rw [show D2M8K2.u11170 = KTree.node D2M8K2.t11178 (nat_lit 24303201) (nat_lit 1787134696) (nat_lit 0) D2M8K2.t11179 from rfl, totK_node, tot11178, tot11179]
  decide +kernel

theorem arows11172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11172 = true := by
  rw [show D2M8K2.u11172 = KTree.node D2M8K2.t11180 (nat_lit 24304437) (nat_lit 1626971826) (nat_lit 0) D2M8K2.t11181 from rfl, allE_node, rows11180, irow11172, rows11181]
  all_goals rfl

theorem atot11172 : totK PD2M8K2 D2M8K2.u11172 = [0, 121453431582, 696399818457, 815671990809, 141279070135, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11172 = KTree.node D2M8K2.t11180 (nat_lit 24304437) (nat_lit 1626971826) (nat_lit 0) D2M8K2.t11181 from rfl, totK_node, tot11180, tot11181]
  decide +kernel

theorem arows11173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11173 = true := by
  rw [show D2M8K2.u11173 = KTree.node D2M8K2.t11182 (nat_lit 24306761) (nat_lit 1619371859) (nat_lit 0) D2M8K2.t11183 from rfl, allE_node, rows11182, irow11173, rows11183]
  all_goals rfl

theorem atot11173 : totK PD2M8K2 D2M8K2.u11173 = [0, 345134840290, 885277067786, 547701108358, 53959665673, 0, 0, 0] := by
  rw [show D2M8K2.u11173 = KTree.node D2M8K2.t11182 (nat_lit 24306761) (nat_lit 1619371859) (nat_lit 0) D2M8K2.t11183 from rfl, totK_node, tot11182, tot11183]
  decide +kernel

theorem arows11177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11177 = true := by
  rw [show D2M8K2.u11177 = KTree.node D2M8K2.t11184 (nat_lit 24308978) (nat_lit 4032614726) (nat_lit 0) D2M8K2.t11185 from rfl, allE_node, rows11184, irow11177, rows11185]
  all_goals rfl

theorem atot11177 : totK PD2M8K2 D2M8K2.u11177 = [0, 165143338399, 748704073044, 776071441380, 139204940706, 1409560813, 0, 0] := by
  rw [show D2M8K2.u11177 = KTree.node D2M8K2.t11184 (nat_lit 24308978) (nat_lit 4032614726) (nat_lit 0) D2M8K2.t11185 from rfl, totK_node, tot11184, tot11185]
  decide +kernel

theorem arows11178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11178 = true := by
  rw [show D2M8K2.u11178 = KTree.node D2M8K2.t11186 (nat_lit 24310766) (nat_lit 3826854700) (nat_lit 0) D2M8K2.t11187 from rfl, allE_node, rows11186, irow11178, rows11187]
  all_goals rfl

theorem atot11178 : totK PD2M8K2 D2M8K2.u11178 = [0, 245877175324, 789653244140, 642749019979, 99444539878, 1164319620, 0, 0] := by
  rw [show D2M8K2.u11178 = KTree.node D2M8K2.t11186 (nat_lit 24310766) (nat_lit 3826854700) (nat_lit 0) D2M8K2.t11187 from rfl, totK_node, tot11186, tot11187]
  decide +kernel

theorem arows11180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11180 = true := by
  rw [show D2M8K2.u11180 = KTree.node D2M8K2.t11188 (nat_lit 24312538) (nat_lit 2420943333) (nat_lit 0) D2M8K2.t11189 from rfl, allE_node, rows11188, irow11180, rows11189]
  all_goals rfl

theorem atot11180 : totK PD2M8K2 D2M8K2.u11180 = [0, 153980021500, 644820481399, 764336289463, 203675324350, 11819130176, 0, 0] := by
  rw [show D2M8K2.u11180 = KTree.node D2M8K2.t11188 (nat_lit 24312538) (nat_lit 2420943333) (nat_lit 0) D2M8K2.t11189 from rfl, totK_node, tot11188, tot11189]
  decide +kernel

theorem arows11181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11181 = true := by
  rw [show D2M8K2.u11181 = KTree.node D2M8K2.t11190 (nat_lit 24314208) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t11191 from rfl, allE_node, rows11190, irow11181, rows11191]
  all_goals rfl

theorem atot11181 : totK PD2M8K2 D2M8K2.u11181 = [0, 253257260999, 813136155777, 628982112284, 92214903817, 1198073392, 0, 0] := by
  rw [show D2M8K2.u11181 = KTree.node D2M8K2.t11190 (nat_lit 24314208) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t11191 from rfl, totK_node, tot11190, tot11191]
  decide +kernel

theorem arows11184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11184 = true := by
  rw [show D2M8K2.u11184 = KTree.node D2M8K2.t11192 (nat_lit 24315950) (nat_lit 3675338402) (nat_lit 0) D2M8K2.t11193 from rfl, allE_node, rows11192, irow11184, rows11193]
  all_goals rfl

theorem atot11184 : totK PD2M8K2 D2M8K2.u11184 = [0, 142048566188, 626513642423, 791022104012, 216233336488, 11986244008, 0, 0] := by
  rw [show D2M8K2.u11184 = KTree.node D2M8K2.t11192 (nat_lit 24315950) (nat_lit 3675338402) (nat_lit 0) D2M8K2.t11193 from rfl, totK_node, tot11192, tot11193]
  decide +kernel

theorem arows11185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11185 = true := by
  rw [show D2M8K2.u11185 = KTree.node D2M8K2.t11194 (nat_lit 24317377) (nat_lit 1476393655) (nat_lit 0) D2M8K2.t11195 from rfl, allE_node, rows11194, irow11185, rows11195]
  all_goals rfl

theorem atot11185 : totK PD2M8K2 D2M8K2.u11185 = [0, 296385850786, 886637849878, 581033800375, 54103006896, 0, 0, 0] := by
  rw [show D2M8K2.u11185 = KTree.node D2M8K2.t11194 (nat_lit 24317377) (nat_lit 1476393655) (nat_lit 0) D2M8K2.t11195 from rfl, totK_node, tot11194, tot11195]
  decide +kernel

theorem arows11187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11187 = true := by
  rw [show D2M8K2.u11187 = KTree.node D2M8K2.t11196 (nat_lit 24319323) (nat_lit 3755858908) (nat_lit 0) D2M8K2.t11197 from rfl, allE_node, rows11196, irow11187, rows11197]
  all_goals rfl

theorem atot11187 : totK PD2M8K2 D2M8K2.u11187 = [0, 141484286328, 660111814598, 816054201621, 184838210681, 4980514959, 0, 0] := by
  rw [show D2M8K2.u11187 = KTree.node D2M8K2.t11196 (nat_lit 24319323) (nat_lit 3755858908) (nat_lit 0) D2M8K2.t11197 from rfl, totK_node, tot11196, tot11197]
  decide +kernel

theorem arows11188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11188 = true := by
  rw [show D2M8K2.u11188 = KTree.node D2M8K2.t11198 (nat_lit 24345317) (nat_lit 2294487725) (nat_lit 0) D2M8K2.t11199 from rfl, allE_node, rows11198, irow11188, rows11199]
  all_goals rfl

theorem atot11188 : totK PD2M8K2 D2M8K2.u11188 = [0, 277883783896, 854681047605, 578361045717, 58871933799, 0, 0, 0] := by
  rw [show D2M8K2.u11188 = KTree.node D2M8K2.t11198 (nat_lit 24345317) (nat_lit 2294487725) (nat_lit 0) D2M8K2.t11199 from rfl, totK_node, tot11198, tot11199]
  decide +kernel

theorem arows11194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11194 = true := by
  rw [show D2M8K2.u11194 = KTree.node D2M8K2.t11200 (nat_lit 24347292) (nat_lit 3185288832) (nat_lit 0) D2M8K2.t11201 from rfl, allE_node, rows11200, irow11194, rows11201]
  all_goals rfl

theorem atot11194 : totK PD2M8K2 D2M8K2.u11194 = [0, 157922964993, 721136750602, 791566201522, 133360597559, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11194 = KTree.node D2M8K2.t11200 (nat_lit 24347292) (nat_lit 3185288832) (nat_lit 0) D2M8K2.t11201 from rfl, totK_node, tot11200, tot11201]
  decide +kernel

theorem arows11195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11195 = true := by
  rw [show D2M8K2.u11195 = KTree.node D2M8K2.t11202 (nat_lit 24352475) (nat_lit 2906256691) (nat_lit 0) D2M8K2.t11203 from rfl, allE_node, rows11202, irow11195, rows11203]
  all_goals rfl

theorem atot11195 : totK PD2M8K2 D2M8K2.u11195 = [0, 242283200860, 790710553045, 654881116435, 103872905115, 1129969115, 0, 0] := by
  rw [show D2M8K2.u11195 = KTree.node D2M8K2.t11202 (nat_lit 24352475) (nat_lit 2906256691) (nat_lit 0) D2M8K2.t11203 from rfl, totK_node, tot11202, tot11203]
  decide +kernel

theorem arows11197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11197 = true := by
  rw [show D2M8K2.u11197 = KTree.node D2M8K2.t11204 (nat_lit 24354502) (nat_lit 3641128292) (nat_lit 0) D2M8K2.t11205 from rfl, allE_node, rows11204, irow11197, rows11205]
  all_goals rfl

theorem atot11197 : totK PD2M8K2 D2M8K2.u11197 = [0, 233898286044, 744708192236, 689352193803, 140094482792, 4008488258, 0, 0] := by
  rw [show D2M8K2.u11197 = KTree.node D2M8K2.t11204 (nat_lit 24354502) (nat_lit 3641128292) (nat_lit 0) D2M8K2.t11205 from rfl, totK_node, tot11204, tot11205]
  decide +kernel

theorem arows11198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11198 = true := by
  rw [show D2M8K2.u11198 = KTree.node D2M8K2.t11206 (nat_lit 24356069) (nat_lit 2233629742) (nat_lit 0) D2M8K2.t11207 from rfl, allE_node, rows11206, irow11198, rows11207]
  all_goals rfl

theorem atot11198 : totK PD2M8K2 D2M8K2.u11198 = [0, 166561591980, 748947971148, 751678779775, 124415452774, 1162515529, 0, 0] := by
  rw [show D2M8K2.u11198 = KTree.node D2M8K2.t11206 (nat_lit 24356069) (nat_lit 2233629742) (nat_lit 0) D2M8K2.t11207 from rfl, totK_node, tot11206, tot11207]
  decide +kernel

theorem arows11201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11201 = true := by
  rw [show D2M8K2.u11201 = KTree.node D2M8K2.t11208 (nat_lit 24361506) (nat_lit 2819827655) (nat_lit 0) D2M8K2.t11209 from rfl, allE_node, rows11208, irow11201, rows11209]
  all_goals rfl

theorem atot11201 : totK PD2M8K2 D2M8K2.u11201 = [0, 247338984673, 768689353672, 656900335407, 133518157073, 4030866388, 0, 0] := by
  rw [show D2M8K2.u11201 = KTree.node D2M8K2.t11208 (nat_lit 24361506) (nat_lit 2819827655) (nat_lit 0) D2M8K2.t11209 from rfl, totK_node, tot11208, tot11209]
  decide +kernel

theorem arows11202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11202 = true := by
  rw [show D2M8K2.u11202 = KTree.node D2M8K2.t11210 (nat_lit 24363014) (nat_lit 2608622746) (nat_lit 0) D2M8K2.t11211 from rfl, allE_node, rows11210, irow11202, rows11211]
  all_goals rfl

theorem atot11202 : totK PD2M8K2 D2M8K2.u11202 = [0, 179743082377, 732285529452, 760458984745, 135180858790, 1249641317, 0, 0] := by
  rw [show D2M8K2.u11202 = KTree.node D2M8K2.t11210 (nat_lit 24363014) (nat_lit 2608622746) (nat_lit 0) D2M8K2.t11211 from rfl, totK_node, tot11210, tot11211]
  decide +kernel

theorem arows11204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11204 = true := by
  rw [show D2M8K2.u11204 = KTree.node D2M8K2.t11212 (nat_lit 24364714) (nat_lit 3968985432) (nat_lit 0) D2M8K2.t11213 from rfl, allE_node, rows11212, irow11204, rows11213]
  all_goals rfl

theorem atot11204 : totK PD2M8K2 D2M8K2.u11204 = [183285179032, 397829498317, 387805480619, 543285302159, 272508601339, 20647649770, 0, 0] := by
  rw [show D2M8K2.u11204 = KTree.node D2M8K2.t11212 (nat_lit 24364714) (nat_lit 3968985432) (nat_lit 0) D2M8K2.t11213 from rfl, totK_node, tot11212, tot11213]
  decide +kernel

theorem arows11205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11205 = true := by
  rw [show D2M8K2.u11205 = KTree.node D2M8K2.t11214 (nat_lit 24431794) (nat_lit 3482505753) (nat_lit 0) D2M8K2.t11215 from rfl, allE_node, rows11214, irow11205, rows11215]
  all_goals rfl

theorem atot11205 : totK PD2M8K2 D2M8K2.u11205 = [266133872380, 850608527588, 617339400890, 98634765941, 10444649207, 0, 0, 0] := by
  rw [show D2M8K2.u11205 = KTree.node D2M8K2.t11214 (nat_lit 24431794) (nat_lit 3482505753) (nat_lit 0) D2M8K2.t11215 from rfl, totK_node, tot11214, tot11215]
  decide +kernel

theorem arows11209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11209 = true := by
  rw [show D2M8K2.u11209 = KTree.node D2M8K2.t11216 (nat_lit 24433284) (nat_lit 2342214189) (nat_lit 0) D2M8K2.t11217 from rfl, allE_node, rows11216, irow11209, rows11217]
  all_goals rfl

theorem atot11209 : totK PD2M8K2 D2M8K2.u11209 = [0, 353508003902, 947160546191, 487239636513, 22733219847, 0, 0, 0] := by
  rw [show D2M8K2.u11209 = KTree.node D2M8K2.t11216 (nat_lit 24433284) (nat_lit 2342214189) (nat_lit 0) D2M8K2.t11217 from rfl, totK_node, tot11216, tot11217]
  decide +kernel

theorem arows11210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11210 = true := by
  rw [show D2M8K2.u11210 = KTree.node D2M8K2.t11218 (nat_lit 24434541) (nat_lit 1478205480) (nat_lit 0) D2M8K2.t11219 from rfl, allE_node, rows11218, irow11210, rows11219]
  all_goals rfl

theorem atot11210 : totK PD2M8K2 D2M8K2.u11210 = [386648953929, 922244795951, 461726783844, 42803240453, 3299353041, 0, 0, 0] := by
  rw [show D2M8K2.u11210 = KTree.node D2M8K2.t11218 (nat_lit 24434541) (nat_lit 1478205480) (nat_lit 0) D2M8K2.t11219 from rfl, totK_node, tot11218, tot11219]
  decide +kernel

theorem arows11212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11212 = true := by
  rw [show D2M8K2.u11212 = KTree.node D2M8K2.t11220 (nat_lit 24436240) (nat_lit 3414903850) (nat_lit 0) D2M8K2.t11221 from rfl, allE_node, rows11220, irow11212, rows11221]
  all_goals rfl

theorem atot11212 : totK PD2M8K2 D2M8K2.u11212 = [33497804063, 518084723106, 918507159842, 282704821168, 12995965463, 0, 0, 0] := by
  rw [show D2M8K2.u11212 = KTree.node D2M8K2.t11220 (nat_lit 24436240) (nat_lit 3414903850) (nat_lit 0) D2M8K2.t11221 from rfl, totK_node, tot11220, tot11221]
  decide +kernel

theorem arows11213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11213 = true := by
  rw [show D2M8K2.u11213 = KTree.node D2M8K2.t11222 (nat_lit 24437934) (nat_lit 3845978438) (nat_lit 0) D2M8K2.t11223 from rfl, allE_node, rows11222, irow11213, rows11223]
  all_goals rfl

theorem atot11213 : totK PD2M8K2 D2M8K2.u11213 = [337241554360, 906671255550, 535006153484, 48543629597, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11213 = KTree.node D2M8K2.t11222 (nat_lit 24437934) (nat_lit 3845978438) (nat_lit 0) D2M8K2.t11223 from rfl, totK_node, tot11222, tot11223]
  decide +kernel

theorem arows11216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11216 = true := by
  rw [show D2M8K2.u11216 = KTree.node D2M8K2.t11224 (nat_lit 24439489) (nat_lit 1170380981) (nat_lit 0) D2M8K2.t11225 from rfl, allE_node, rows11224, irow11216, rows11225]
  all_goals rfl

theorem atot11216 : totK PD2M8K2 D2M8K2.u11216 = [83129192267, 552740062160, 870308278342, 261596026506, 10628034384, 0, 0, 0] := by
  rw [show D2M8K2.u11216 = KTree.node D2M8K2.t11224 (nat_lit 24439489) (nat_lit 1170380981) (nat_lit 0) D2M8K2.t11225 from rfl, totK_node, tot11224, tot11225]
  decide +kernel

theorem arows11217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11217 = true := by
  rw [show D2M8K2.u11217 = KTree.node D2M8K2.t11226 (nat_lit 24441316) (nat_lit 3994297237) (nat_lit 0) D2M8K2.t11227 from rfl, allE_node, rows11226, irow11217, rows11227]
  all_goals rfl

theorem atot11217 : totK PD2M8K2 D2M8K2.u11217 = [329820035759, 870578740295, 539139261702, 76959712132, 2566665356, 0, 0, 0] := by
  rw [show D2M8K2.u11217 = KTree.node D2M8K2.t11226 (nat_lit 24441316) (nat_lit 3994297237) (nat_lit 0) D2M8K2.t11227 from rfl, totK_node, tot11226, tot11227]
  decide +kernel

theorem arows11219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11219 = true := by
  rw [show D2M8K2.u11219 = KTree.node D2M8K2.t11228 (nat_lit 24442891) (nat_lit 1791681818) (nat_lit 0) D2M8K2.t11229 from rfl, allE_node, rows11228, irow11219, rows11229]
  all_goals rfl

theorem atot11219 : totK PD2M8K2 D2M8K2.u11219 = [91352441409, 711974428773, 876172262098, 139856043993, 1092001298, 0, 0, 0] := by
  rw [show D2M8K2.u11219 = KTree.node D2M8K2.t11228 (nat_lit 24442891) (nat_lit 1791681818) (nat_lit 0) D2M8K2.t11229 from rfl, totK_node, tot11228, tot11229]
  decide +kernel

theorem arows11220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11220 = true := by
  rw [show D2M8K2.u11220 = KTree.node D2M8K2.t11230 (nat_lit 24444864) (nat_lit 2830013604) (nat_lit 0) D2M8K2.t11231 from rfl, allE_node, rows11230, irow11220, rows11231]
  all_goals rfl

theorem atot11220 : totK PD2M8K2 D2M8K2.u11220 = [330828488568, 825230967724, 530623271580, 108186967293, 3867150671, 0, 0, 0] := by
  rw [show D2M8K2.u11220 = KTree.node D2M8K2.t11230 (nat_lit 24444864) (nat_lit 2830013604) (nat_lit 0) D2M8K2.t11231 from rfl, totK_node, tot11230, tot11231]
  decide +kernel

theorem arows11225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11225 = true := by
  rw [show D2M8K2.u11225 = KTree.node D2M8K2.t11232 (nat_lit 24446437) (nat_lit 1179863068) (nat_lit 0) D2M8K2.t11233 from rfl, allE_node, rows11232, irow11225, rows11233]
  all_goals rfl

theorem atot11225 : totK PD2M8K2 D2M8K2.u11225 = [75805549015, 567401972480, 877836914282, 251574790990, 7205897528, 0, 0, 0] := by
  rw [show D2M8K2.u11225 = KTree.node D2M8K2.t11232 (nat_lit 24446437) (nat_lit 1179863068) (nat_lit 0) D2M8K2.t11233 from rfl, totK_node, tot11232, tot11233]
  decide +kernel

theorem arows11226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11226 = true := by
  rw [show D2M8K2.u11226 = KTree.node D2M8K2.t11234 (nat_lit 24451770) (nat_lit 3540926838) (nat_lit 0) D2M8K2.t11235 from rfl, allE_node, rows11234, irow11226, rows11235]
  all_goals rfl

theorem atot11226 : totK PD2M8K2 D2M8K2.u11226 = [0, 341134235870, 909790182419, 534257276045, 48213163711, 0, 0, 0] := by
  rw [show D2M8K2.u11226 = KTree.node D2M8K2.t11234 (nat_lit 24451770) (nat_lit 3540926838) (nat_lit 0) D2M8K2.t11235 from rfl, totK_node, tot11234, tot11235]
  decide +kernel

theorem arows11228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11228 = true := by
  rw [show D2M8K2.u11228 = KTree.node D2M8K2.t11236 (nat_lit 24453273) (nat_lit 1774750196) (nat_lit 0) D2M8K2.t11237 from rfl, allE_node, rows11236, irow11228, rows11237]
  all_goals rfl

theorem atot11228 : totK PD2M8K2 D2M8K2.u11228 = [0, 163133196925, 645253173953, 724812531383, 271662675960, 25191558099, 0, 0] := by
  rw [show D2M8K2.u11228 = KTree.node D2M8K2.t11236 (nat_lit 24453273) (nat_lit 1774750196) (nat_lit 0) D2M8K2.t11237 from rfl, totK_node, tot11236, tot11237]
  decide +kernel

theorem arows11229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11229 = true := by
  rw [show D2M8K2.u11229 = KTree.node D2M8K2.t11238 (nat_lit 24454461) (nat_lit 1011517804) (nat_lit 0) D2M8K2.t11239 from rfl, allE_node, rows11238, irow11229, rows11239]
  all_goals rfl

theorem atot11229 : totK PD2M8K2 D2M8K2.u11229 = [0, 155525263493, 580152417140, 759841933323, 284556090966, 11730315755, 0, 0] := by
  rw [show D2M8K2.u11229 = KTree.node D2M8K2.t11238 (nat_lit 24454461) (nat_lit 1011517804) (nat_lit 0) D2M8K2.t11239 from rfl, totK_node, tot11238, tot11239]
  decide +kernel

theorem arows11232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11232 = true := by
  rw [show D2M8K2.u11232 = KTree.node D2M8K2.t11240 (nat_lit 24456004) (nat_lit 3991981685) (nat_lit 0) D2M8K2.t11241 from rfl, allE_node, rows11240, irow11232, rows11241]
  all_goals rfl

theorem atot11232 : totK PD2M8K2 D2M8K2.u11232 = [0, 262698497468, 863711661383, 620780098082, 54437449544, 0, 0, 0] := by
  rw [show D2M8K2.u11232 = KTree.node D2M8K2.t11240 (nat_lit 24456004) (nat_lit 3991981685) (nat_lit 0) D2M8K2.t11241 from rfl, totK_node, tot11240, tot11241]
  decide +kernel

theorem arows11233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11233 = true := by
  rw [show D2M8K2.u11233 = KTree.node D2M8K2.t11242 (nat_lit 24457870) (nat_lit 3956579102) (nat_lit 0) D2M8K2.t11243 from rfl, allE_node, rows11242, irow11233, rows11243]
  all_goals rfl

theorem atot11233 : totK PD2M8K2 D2M8K2.u11233 = [0, 155622024732, 655737569236, 783019523367, 194129201429, 5159868635, 0, 0] := by
  rw [show D2M8K2.u11233 = KTree.node D2M8K2.t11242 (nat_lit 24457870) (nat_lit 3956579102) (nat_lit 0) D2M8K2.t11243 from rfl, totK_node, tot11242, tot11243]
  decide +kernel

theorem arows11235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11235 = true := by
  rw [show D2M8K2.u11235 = KTree.node D2M8K2.t11244 (nat_lit 24459558) (nat_lit 3779129378) (nat_lit 0) D2M8K2.t11245 from rfl, allE_node, rows11244, irow11235, rows11245]
  all_goals rfl

theorem atot11235 : totK PD2M8K2 D2M8K2.u11235 = [0, 262832266500, 864544772213, 616242769025, 60799549793, 0, 0, 0] := by
  rw [show D2M8K2.u11235 = KTree.node D2M8K2.t11244 (nat_lit 24459558) (nat_lit 3779129378) (nat_lit 0) D2M8K2.t11245 from rfl, totK_node, tot11244, tot11245]
  decide +kernel

theorem arows11236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11236 = true := by
  rw [show D2M8K2.u11236 = KTree.node D2M8K2.t11246 (nat_lit 24461406) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t11247 from rfl, allE_node, rows11246, irow11236, rows11247]
  all_goals rfl

theorem atot11236 : totK PD2M8K2 D2M8K2.u11236 = [0, 190283383896, 655667898634, 742238468488, 192889356855, 5218872685, 0, 0] := by
  rw [show D2M8K2.u11236 = KTree.node D2M8K2.t11246 (nat_lit 24461406) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t11247 from rfl, totK_node, tot11246, tot11247]
  decide +kernel

theorem arows11240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11240 = true := by
  rw [show D2M8K2.u11240 = KTree.node D2M8K2.t11248 (nat_lit 24462770) (nat_lit 4020524323) (nat_lit 0) D2M8K2.t11249 from rfl, allE_node, rows11248, irow11240, rows11249]
  all_goals rfl

theorem atot11240 : totK PD2M8K2 D2M8K2.u11240 = [0, 228989119725, 855972520932, 659685206927, 60848895645, 0, 0, 0] := by
  rw [show D2M8K2.u11240 = KTree.node D2M8K2.t11248 (nat_lit 24462770) (nat_lit 4020524323) (nat_lit 0) D2M8K2.t11249 from rfl, totK_node, tot11248, tot11249]
  decide +kernel

theorem arows11241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11241 = true := by
  rw [show D2M8K2.u11241 = KTree.node D2M8K2.t11250 (nat_lit 24465293) (nat_lit 1819777668) (nat_lit 0) D2M8K2.t11251 from rfl, allE_node, rows11250, irow11241, rows11251]
  all_goals rfl

theorem atot11241 : totK PD2M8K2 D2M8K2.u11241 = [0, 227486098258, 757138850189, 701891430556, 124901727909, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11241 = KTree.node D2M8K2.t11250 (nat_lit 24465293) (nat_lit 1819777668) (nat_lit 0) D2M8K2.t11251 from rfl, totK_node, tot11250, tot11251]
  decide +kernel

theorem arows11243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11243 = true := by
  rw [show D2M8K2.u11243 = KTree.node D2M8K2.t11252 (nat_lit 24466738) (nat_lit 4176030581) (nat_lit 0) D2M8K2.t11253 from rfl, allE_node, rows11252, irow11243, rows11253]
  all_goals rfl

theorem atot11243 : totK PD2M8K2 D2M8K2.u11243 = [0, 177177287391, 755341002821, 736159303904, 129145244026, 1238673482, 0, 0] := by
  rw [show D2M8K2.u11243 = KTree.node D2M8K2.t11252 (nat_lit 24466738) (nat_lit 4176030581) (nat_lit 0) D2M8K2.t11253 from rfl, totK_node, tot11252, tot11253]
  decide +kernel

theorem arows11244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11244 = true := by
  rw [show D2M8K2.u11244 = KTree.node D2M8K2.t11254 (nat_lit 24468637) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t11255 from rfl, allE_node, rows11254, irow11244, rows11255]
  all_goals rfl

theorem atot11244 : totK PD2M8K2 D2M8K2.u11244 = [256161886194, 632678687429, 374959936838, 340266134887, 159704578765, 8063697217, 0, 0] := by
  rw [show D2M8K2.u11244 = KTree.node D2M8K2.t11254 (nat_lit 24468637) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t11255 from rfl, totK_node, tot11254, tot11255]
  decide +kernel

theorem arows11247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11247 = true := by
  rw [show D2M8K2.u11247 = KTree.node D2M8K2.t11256 (nat_lit 24470843) (nat_lit 2766824521) (nat_lit 0) D2M8K2.t11257 from rfl, allE_node, rows11256, irow11247, rows11257]
  all_goals rfl

theorem atot11247 : totK PD2M8K2 D2M8K2.u11247 = [162285611601, 707032353643, 800930441447, 149343377511, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11247 = KTree.node D2M8K2.t11256 (nat_lit 24470843) (nat_lit 2766824521) (nat_lit 0) D2M8K2.t11257 from rfl, totK_node, tot11256, tot11257]
  decide +kernel

theorem arows11248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11248 = true := by
  rw [show D2M8K2.u11248 = KTree.node D2M8K2.t11258 (nat_lit 24473060) (nat_lit 3288119639) (nat_lit 0) D2M8K2.t11259 from rfl, allE_node, rows11258, irow11248, rows11259]
  all_goals rfl

theorem atot11248 : totK PD2M8K2 D2M8K2.u11248 = [335343125088, 909932488540, 530592905655, 38073248566, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11248 = KTree.node D2M8K2.t11258 (nat_lit 24473060) (nat_lit 3288119639) (nat_lit 0) D2M8K2.t11259 from rfl, totK_node, tot11258, tot11259]
  decide +kernel

theorem arows11250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11250 = true := by
  rw [show D2M8K2.u11250 = KTree.node D2M8K2.t11260 (nat_lit 24474507) (nat_lit 3439577478) (nat_lit 0) D2M8K2.t11261 from rfl, allE_node, rows11260, irow11250, rows11261]
  all_goals rfl

theorem atot11250 : totK PD2M8K2 D2M8K2.u11250 = [0, 391707691255, 939170794962, 453891295445, 30796745998, 0, 0, 0] := by
  rw [show D2M8K2.u11250 = KTree.node D2M8K2.t11260 (nat_lit 24474507) (nat_lit 3439577478) (nat_lit 0) D2M8K2.t11261 from rfl, totK_node, tot11260, tot11261]
  decide +kernel

theorem arows11251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11251 = true := by
  rw [show D2M8K2.u11251 = KTree.node D2M8K2.t11262 (nat_lit 24475816) (nat_lit 3805066039) (nat_lit 0) D2M8K2.t11263 from rfl, allE_node, rows11262, irow11251, rows11263]
  all_goals rfl

theorem atot11251 : totK PD2M8K2 D2M8K2.u11251 = [332978533370, 820059519976, 531805194825, 129253649564, 6800370819, 0, 0, 0] := by
  rw [show D2M8K2.u11251 = KTree.node D2M8K2.t11262 (nat_lit 24475816) (nat_lit 3805066039) (nat_lit 0) D2M8K2.t11263 from rfl, totK_node, tot11262, tot11263]
  decide +kernel

theorem arows11261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11261 = true := by
  rw [show D2M8K2.u11261 = KTree.node D2M8K2.t11264 (nat_lit 24477268) (nat_lit 3636862074) (nat_lit 0) D2M8K2.t11265 from rfl, allE_node, rows11264, irow11261, rows11265]
  all_goals rfl

theorem atot11261 : totK PD2M8K2 D2M8K2.u11261 = [101997513634, 634874964692, 830322485199, 215883913717, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u11261 = KTree.node D2M8K2.t11264 (nat_lit 24477268) (nat_lit 3636862074) (nat_lit 0) D2M8K2.t11265 from rfl, totK_node, tot11264, tot11265]
  decide +kernel

theorem arows11262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11262 = true := by
  rw [show D2M8K2.u11262 = KTree.node D2M8K2.t11266 (nat_lit 24482578) (nat_lit 3169329769) (nat_lit 0) D2M8K2.t11267 from rfl, allE_node, rows11266, irow11262, rows11267]
  all_goals rfl

theorem atot11262 : totK PD2M8K2 D2M8K2.u11262 = [254411431982, 773415210091, 644175981171, 123237109435, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u11262 = KTree.node D2M8K2.t11266 (nat_lit 24482578) (nat_lit 3169329769) (nat_lit 0) D2M8K2.t11267 from rfl, totK_node, tot11266, tot11267]
  decide +kernel

theorem arows11264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11264 = true := by
  rw [show D2M8K2.u11264 = KTree.node D2M8K2.t11268 (nat_lit 24484105) (nat_lit 1465126543) (nat_lit 0) D2M8K2.t11269 from rfl, allE_node, rows11268, irow11264, rows11269]
  all_goals rfl

theorem atot11264 : totK PD2M8K2 D2M8K2.u11264 = [159319719328, 743758072028, 781080557421, 124166177371, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11264 = KTree.node D2M8K2.t11268 (nat_lit 24484105) (nat_lit 1465126543) (nat_lit 0) D2M8K2.t11269 from rfl, totK_node, tot11268, tot11269]
  decide +kernel

theorem arows11265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11265 = true := by
  rw [show D2M8K2.u11265 = KTree.node D2M8K2.t11270 (nat_lit 24486165) (nat_lit 1675071546) (nat_lit 0) D2M8K2.t11271 from rfl, allE_node, rows11270, irow11265, rows11271]
  all_goals rfl

theorem atot11265 : totK PD2M8K2 D2M8K2.u11265 = [296138298740, 801462570084, 594166383837, 121566857517, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u11265 = KTree.node D2M8K2.t11270 (nat_lit 24486165) (nat_lit 1675071546) (nat_lit 0) D2M8K2.t11271 from rfl, totK_node, tot11270, tot11271]
  decide +kernel

theorem arows11268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11268 = true := by
  rw [show D2M8K2.u11268 = KTree.node D2M8K2.t11272 (nat_lit 24487818) (nat_lit 3788763235) (nat_lit 0) D2M8K2.t11273 from rfl, allE_node, rows11272, irow11268, rows11273]
  all_goals rfl

theorem atot11268 : totK PD2M8K2 D2M8K2.u11268 = [90490504222, 586361478732, 853498104517, 251031660020, 7564582307, 0, 0, 0] := by
  rw [show D2M8K2.u11268 = KTree.node D2M8K2.t11272 (nat_lit 24487818) (nat_lit 3788763235) (nat_lit 0) D2M8K2.t11273 from rfl, totK_node, tot11272, tot11273]
  decide +kernel

theorem arows11269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11269 = true := by
  rw [show D2M8K2.u11269 = KTree.node D2M8K2.t11274 (nat_lit 24489827) (nat_lit 2375001887) (nat_lit 0) D2M8K2.t11275 from rfl, allE_node, rows11274, irow11269, rows11275]
  all_goals rfl

theorem atot11269 : totK PD2M8K2 D2M8K2.u11269 = [0, 378400576507, 933476080484, 427061941996, 26872229658, 0, 0, 0] := by
  rw [show D2M8K2.u11269 = KTree.node D2M8K2.t11274 (nat_lit 24489827) (nat_lit 2375001887) (nat_lit 0) D2M8K2.t11275 from rfl, totK_node, tot11274, tot11275]
  decide +kernel

theorem arows11271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11271 = true := by
  rw [show D2M8K2.u11271 = KTree.node D2M8K2.t11276 (nat_lit 24492144) (nat_lit 3512421255) (nat_lit 0) D2M8K2.t11277 from rfl, allE_node, rows11276, irow11271, rows11277]
  all_goals rfl

theorem atot11271 : totK PD2M8K2 D2M8K2.u11271 = [0, 149326064459, 711575491786, 802574750815, 124872156171, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11271 = KTree.node D2M8K2.t11276 (nat_lit 24492144) (nat_lit 3512421255) (nat_lit 0) D2M8K2.t11277 from rfl, totK_node, tot11276, tot11277]
  decide +kernel

theorem arows11272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11272 = true := by
  rw [show D2M8K2.u11272 = KTree.node D2M8K2.t11278 (nat_lit 24493933) (nat_lit 1100838146) (nat_lit 0) D2M8K2.t11279 from rfl, allE_node, rows11278, irow11272, rows11279]
  all_goals rfl

theorem atot11272 : totK PD2M8K2 D2M8K2.u11272 = [0, 378664197608, 944266918469, 447291570724, 26876109049, 0, 0, 0] := by
  rw [show D2M8K2.u11272 = KTree.node D2M8K2.t11278 (nat_lit 24493933) (nat_lit 1100838146) (nat_lit 0) D2M8K2.t11279 from rfl, totK_node, tot11278, tot11279]
  decide +kernel

theorem arows11276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11276 = true := by
  rw [show D2M8K2.u11276 = KTree.node D2M8K2.t11280 (nat_lit 24496901) (nat_lit 2384514699) (nat_lit 0) D2M8K2.t11281 from rfl, allE_node, rows11280, irow11276, rows11281]
  all_goals rfl

theorem atot11276 : totK PD2M8K2 D2M8K2.u11276 = [0, 355758147572, 945751277899, 481790889861, 30830301070, 0, 0, 0] := by
  rw [show D2M8K2.u11276 = KTree.node D2M8K2.t11280 (nat_lit 24496901) (nat_lit 2384514699) (nat_lit 0) D2M8K2.t11281 from rfl, totK_node, tot11280, tot11281]
  decide +kernel

theorem arows11277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11277 = true := by
  rw [show D2M8K2.u11277 = KTree.node D2M8K2.t11282 (nat_lit 24498586) (nat_lit 3433883998) (nat_lit 0) D2M8K2.t11283 from rfl, allE_node, rows11282, irow11277, rows11283]
  all_goals rfl

theorem atot11277 : totK PD2M8K2 D2M8K2.u11277 = [0, 48964430500, 513167626310, 876457527188, 275944749368, 13016197374, 0, 0] := by
  rw [show D2M8K2.u11277 = KTree.node D2M8K2.t11282 (nat_lit 24498586) (nat_lit 3433883998) (nat_lit 0) D2M8K2.t11283 from rfl, totK_node, tot11282, tot11283]
  decide +kernel

theorem arows11279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11279 = true := by
  rw [show D2M8K2.u11279 = KTree.node D2M8K2.t11284 (nat_lit 24503752) (nat_lit 3841835345) (nat_lit 0) D2M8K2.t11285 from rfl, allE_node, rows11284, irow11279, rows11285]
  all_goals rfl

theorem atot11279 : totK PD2M8K2 D2M8K2.u11279 = [0, 363708666320, 962592099496, 457700383657, 24182529053, 0, 0, 0] := by
  rw [show D2M8K2.u11279 = KTree.node D2M8K2.t11284 (nat_lit 24503752) (nat_lit 3841835345) (nat_lit 0) D2M8K2.t11285 from rfl, totK_node, tot11284, tot11285]
  decide +kernel

theorem arows11280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11280 = true := by
  rw [show D2M8K2.u11280 = KTree.node D2M8K2.t11286 (nat_lit 24505731) (nat_lit 2805971763) (nat_lit 0) D2M8K2.t11287 from rfl, allE_node, rows11286, irow11280, rows11287]
  all_goals rfl

theorem atot11280 : totK PD2M8K2 D2M8K2.u11280 = [0, 123016409097, 669278416773, 776327133036, 152566252214, 4574395652, 0, 0] := by
  rw [show D2M8K2.u11280 = KTree.node D2M8K2.t11286 (nat_lit 24505731) (nat_lit 2805971763) (nat_lit 0) D2M8K2.t11287 from rfl, totK_node, tot11286, tot11287]
  decide +kernel

theorem arows11283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11283 = true := by
  rw [show D2M8K2.u11283 = KTree.node D2M8K2.t11288 (nat_lit 24507532) (nat_lit 3159417426) (nat_lit 0) D2M8K2.t11289 from rfl, allE_node, rows11288, irow11283, rows11289]
  all_goals rfl

theorem atot11283 : totK PD2M8K2 D2M8K2.u11283 = [85430600343, 437519291237, 794501814123, 453852567853, 41617348889, 0, 0, 0] := by
  rw [show D2M8K2.u11283 = KTree.node D2M8K2.t11288 (nat_lit 24507532) (nat_lit 3159417426) (nat_lit 0) D2M8K2.t11289 from rfl, totK_node, tot11288, tot11289]
  decide +kernel

theorem arows11284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11284 = true := by
  rw [show D2M8K2.u11284 = KTree.node D2M8K2.t11290 (nat_lit 24511396) (nat_lit 2812729693) (nat_lit 0) D2M8K2.t11291 from rfl, allE_node, rows11290, irow11284, rows11291]
  all_goals rfl

theorem atot11284 : totK PD2M8K2 D2M8K2.u11284 = [239580803521, 805403842459, 645433810145, 107074671936, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11284 = KTree.node D2M8K2.t11290 (nat_lit 24511396) (nat_lit 2812729693) (nat_lit 0) D2M8K2.t11291 from rfl, totK_node, tot11290, tot11291]
  decide +kernel

theorem arows11286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11286 = true := by
  rw [show D2M8K2.u11286 = KTree.node D2M8K2.t11292 (nat_lit 24513941) (nat_lit 2233589688) (nat_lit 0) D2M8K2.t11293 from rfl, allE_node, rows11292, irow11286, rows11293]
  all_goals rfl

theorem atot11286 : totK PD2M8K2 D2M8K2.u11286 = [269168489951, 835309333322, 661538970600, 76293522941, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11286 = KTree.node D2M8K2.t11292 (nat_lit 24513941) (nat_lit 2233589688) (nat_lit 0) D2M8K2.t11293 from rfl, totK_node, tot11292, tot11293]
  decide +kernel

theorem arows11287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11287 = true := by
  rw [show D2M8K2.u11287 = KTree.node D2M8K2.t11294 (nat_lit 24515471) (nat_lit 2142955787) (nat_lit 0) D2M8K2.t11295 from rfl, allE_node, rows11294, irow11287, rows11295]
  all_goals rfl

theorem atot11287 : totK PD2M8K2 D2M8K2.u11287 = [159791897586, 632918851208, 709278814356, 284375404089, 25364689049, 0, 0, 0] := by
  rw [show D2M8K2.u11287 = KTree.node D2M8K2.t11294 (nat_lit 24515471) (nat_lit 2142955787) (nat_lit 0) D2M8K2.t11295 from rfl, totK_node, tot11294, tot11295]
  decide +kernel

theorem arows11292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11292 = true := by
  rw [show D2M8K2.u11292 = KTree.node D2M8K2.t11296 (nat_lit 24516696) (nat_lit 3326736989) (nat_lit 0) D2M8K2.t11297 from rfl, allE_node, rows11296, irow11292, rows11297]
  all_goals rfl

theorem atot11292 : totK PD2M8K2 D2M8K2.u11292 = [171723400371, 595657407605, 737270698258, 292503091947, 12230400950, 0, 0, 0] := by
  rw [show D2M8K2.u11292 = KTree.node D2M8K2.t11296 (nat_lit 24516696) (nat_lit 3326736989) (nat_lit 0) D2M8K2.t11297 from rfl, totK_node, tot11296, tot11297]
  decide +kernel

theorem arows11293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11293 = true := by
  rw [show D2M8K2.u11293 = KTree.node D2M8K2.t11298 (nat_lit 24521623) (nat_lit 2230937039) (nat_lit 0) D2M8K2.t11299 from rfl, allE_node, rows11298, irow11293, rows11299]
  all_goals rfl

theorem atot11293 : totK PD2M8K2 D2M8K2.u11293 = [266980621076, 833694193161, 620231246498, 80678273757, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u11293 = KTree.node D2M8K2.t11298 (nat_lit 24521623) (nat_lit 2230937039) (nat_lit 0) D2M8K2.t11299 from rfl, totK_node, tot11298, tot11299]
  decide +kernel

theorem arows11295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11295 = true := by
  rw [show D2M8K2.u11295 = KTree.node D2M8K2.t11300 (nat_lit 24523274) (nat_lit 4016923976) (nat_lit 0) D2M8K2.t11301 from rfl, allE_node, rows11300, irow11295, rows11301]
  all_goals rfl

theorem atot11295 : totK PD2M8K2 D2M8K2.u11295 = [97326488611, 574774288046, 846898395840, 263137597460, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u11295 = KTree.node D2M8K2.t11300 (nat_lit 24523274) (nat_lit 4016923976) (nat_lit 0) D2M8K2.t11301 from rfl, totK_node, tot11300, tot11301]
  decide +kernel

theorem arows11296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11296 = true := by
  rw [show D2M8K2.u11296 = KTree.node D2M8K2.t11302 (nat_lit 24524713) (nat_lit 1496149245) (nat_lit 0) D2M8K2.t11303 from rfl, allE_node, rows11302, irow11296, rows11303]
  all_goals rfl

theorem atot11296 : totK PD2M8K2 D2M8K2.u11296 = [316461552066, 888976320931, 552379853337, 53938790009, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11296 = KTree.node D2M8K2.t11302 (nat_lit 24524713) (nat_lit 1496149245) (nat_lit 0) D2M8K2.t11303 from rfl, totK_node, tot11302, tot11303]
  decide +kernel

theorem arows11299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11299 = true := by
  rw [show D2M8K2.u11299 = KTree.node D2M8K2.t11304 (nat_lit 24526684) (nat_lit 3748511897) (nat_lit 0) D2M8K2.t11305 from rfl, allE_node, rows11304, irow11299, rows11305]
  all_goals rfl

theorem atot11299 : totK PD2M8K2 D2M8K2.u11299 = [153057018287, 656300383490, 808045454610, 191888693508, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11299 = KTree.node D2M8K2.t11304 (nat_lit 24526684) (nat_lit 3748511897) (nat_lit 0) D2M8K2.t11305 from rfl, totK_node, tot11304, tot11305]
  decide +kernel

theorem arows11300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11300 = true := by
  rw [show D2M8K2.u11300 = KTree.node D2M8K2.t11306 (nat_lit 24528345) (nat_lit 1837559071) (nat_lit 0) D2M8K2.t11307 from rfl, allE_node, rows11306, irow11300, rows11307]
  all_goals rfl

theorem atot11300 : totK PD2M8K2 D2M8K2.u11300 = [233675638286, 794073484060, 671771686372, 115104342987, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u11300 = KTree.node D2M8K2.t11306 (nat_lit 24528345) (nat_lit 1837559071) (nat_lit 0) D2M8K2.t11307 from rfl, totK_node, tot11306, tot11307]
  decide +kernel

theorem arows11302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11302 = true := by
  rw [show D2M8K2.u11302 = KTree.node D2M8K2.t11308 (nat_lit 24530440) (nat_lit 3732401723) (nat_lit 0) D2M8K2.t11309 from rfl, allE_node, rows11308, irow11302, rows11309]
  all_goals rfl

theorem atot11302 : totK PD2M8K2 D2M8K2.u11302 = [0, 422316471501, 958900872258, 385314677795, 20929661710, 0, 0, 0] := by
  rw [show D2M8K2.u11302 = KTree.node D2M8K2.t11308 (nat_lit 24530440) (nat_lit 3732401723) (nat_lit 0) D2M8K2.t11309 from rfl, totK_node, tot11308, tot11309]
  decide +kernel

theorem arows11303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11303 = true := by
  rw [show D2M8K2.u11303 = KTree.node D2M8K2.t11310 (nat_lit 24532267) (nat_lit 1612429280) (nat_lit 0) D2M8K2.t11311 from rfl, allE_node, rows11310, irow11303, rows11311]
  all_goals rfl

theorem atot11303 : totK PD2M8K2 D2M8K2.u11303 = [0, 185950553881, 763936543464, 697498350965, 100316603174, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11303 = KTree.node D2M8K2.t11310 (nat_lit 24532267) (nat_lit 1612429280) (nat_lit 0) D2M8K2.t11311 from rfl, totK_node, tot11310, tot11311]
  decide +kernel

theorem arows11307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11307 = true := by
  rw [show D2M8K2.u11307 = KTree.node D2M8K2.t11312 (nat_lit 24534836) (nat_lit 3642093816) (nat_lit 0) D2M8K2.t11313 from rfl, allE_node, rows11312, irow11307, rows11313]
  all_goals rfl

theorem atot11307 : totK PD2M8K2 D2M8K2.u11307 = [0, 341126602647, 900123736691, 548712774717, 51408944837, 0, 0, 0] := by
  rw [show D2M8K2.u11307 = KTree.node D2M8K2.t11312 (nat_lit 24534836) (nat_lit 3642093816) (nat_lit 0) D2M8K2.t11313 from rfl, totK_node, tot11312, tot11313]
  decide +kernel

theorem arows11308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11308 = true := by
  rw [show D2M8K2.u11308 = KTree.node D2M8K2.t11314 (nat_lit 24541281) (nat_lit 1733426590) (nat_lit 0) D2M8K2.t11315 from rfl, allE_node, rows11314, irow11308, rows11315]
  all_goals rfl

theorem atot11308 : totK PD2M8K2 D2M8K2.u11308 = [0, 350544056679, 932276737972, 497416009751, 35301946487, 0, 0, 0] := by
  rw [show D2M8K2.u11308 = KTree.node D2M8K2.t11314 (nat_lit 24541281) (nat_lit 1733426590) (nat_lit 0) D2M8K2.t11315 from rfl, totK_node, tot11314, tot11315]
  decide +kernel

theorem arows11310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11310 = true := by
  rw [show D2M8K2.u11310 = KTree.node D2M8K2.t11316 (nat_lit 24542732) (nat_lit 1532382989) (nat_lit 0) D2M8K2.t11317 from rfl, allE_node, rows11316, irow11310, rows11317]
  all_goals rfl

theorem atot11310 : totK PD2M8K2 D2M8K2.u11310 = [0, 173124426782, 733913097721, 732189867430, 127351341945, 1171084559, 0, 0] := by
  rw [show D2M8K2.u11310 = KTree.node D2M8K2.t11316 (nat_lit 24542732) (nat_lit 1532382989) (nat_lit 0) D2M8K2.t11317 from rfl, totK_node, tot11316, tot11317]
  decide +kernel

theorem arows11311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11311 = true := by
  rw [show D2M8K2.u11311 = KTree.node D2M8K2.t11318 (nat_lit 24544602) (nat_lit 3873051234) (nat_lit 0) D2M8K2.t11319 from rfl, allE_node, rows11318, irow11311, rows11319]
  all_goals rfl

theorem atot11311 : totK PD2M8K2 D2M8K2.u11311 = [0, 233612656303, 715272481830, 620436390867, 180557242963, 11934365838, 0, 0] := by
  rw [show D2M8K2.u11311 = KTree.node D2M8K2.t11318 (nat_lit 24544602) (nat_lit 3873051234) (nat_lit 0) D2M8K2.t11319 from rfl, totK_node, tot11318, tot11319]
  decide +kernel

theorem arows11314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11314 = true := by
  rw [show D2M8K2.u11314 = KTree.node D2M8K2.t11320 (nat_lit 24545889) (nat_lit 1845086237) (nat_lit 0) D2M8K2.t11321 from rfl, allE_node, rows11320, irow11314, rows11321]
  all_goals rfl

theorem atot11314 : totK PD2M8K2 D2M8K2.u11314 = [0, 179118419696, 796793933372, 700051420046, 90078881630, 1053411165, 0, 0] := by
  rw [show D2M8K2.u11314 = KTree.node D2M8K2.t11320 (nat_lit 24545889) (nat_lit 1845086237) (nat_lit 0) D2M8K2.t11321 from rfl, totK_node, tot11320, tot11321]
  decide +kernel

theorem arows11315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11315 = true := by
  rw [show D2M8K2.u11315 = KTree.node D2M8K2.t11322 (nat_lit 24548341) (nat_lit 1076362185) (nat_lit 0) D2M8K2.t11323 from rfl, allE_node, rows11322, irow11315, rows11323]
  all_goals rfl

theorem atot11315 : totK PD2M8K2 D2M8K2.u11315 = [0, 295343814987, 793301805559, 588548019563, 105157231516, 3667207281, 0, 0] := by
  rw [show D2M8K2.u11315 = KTree.node D2M8K2.t11322 (nat_lit 24548341) (nat_lit 1076362185) (nat_lit 0) D2M8K2.t11323 from rfl, totK_node, tot11322, tot11323]
  decide +kernel

theorem arows11317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11317 = true := by
  rw [show D2M8K2.u11317 = KTree.node D2M8K2.t11324 (nat_lit 24551617) (nat_lit 1503277576) (nat_lit 0) D2M8K2.t11325 from rfl, allE_node, rows11324, irow11317, rows11325]
  all_goals rfl

theorem atot11317 : totK PD2M8K2 D2M8K2.u11317 = [252531195499, 719676718039, 584685388945, 222854995385, 20786437047, 0, 0, 0] := by
  rw [show D2M8K2.u11317 = KTree.node D2M8K2.t11324 (nat_lit 24551617) (nat_lit 1503277576) (nat_lit 0) D2M8K2.t11325 from rfl, totK_node, tot11324, tot11325]
  decide +kernel

theorem arows11318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11318 = true := by
  rw [show D2M8K2.u11318 = KTree.node D2M8K2.t11326 (nat_lit 24553768) (nat_lit 3657270356) (nat_lit 0) D2M8K2.t11327 from rfl, allE_node, rows11326, irow11318, rows11327]
  all_goals rfl

theorem atot11318 : totK PD2M8K2 D2M8K2.u11318 = [181436308940, 742922009663, 763383380899, 132482172669, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11318 = KTree.node D2M8K2.t11326 (nat_lit 24553768) (nat_lit 3657270356) (nat_lit 0) D2M8K2.t11327 from rfl, totK_node, tot11326, tot11327]
  decide +kernel

theorem arows11324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11324 = true := by
  rw [show D2M8K2.u11324 = KTree.node D2M8K2.t11328 (nat_lit 24555896) (nat_lit 3419756427) (nat_lit 0) D2M8K2.t11329 from rfl, allE_node, rows11328, irow11324, rows11329]
  all_goals rfl

theorem atot11324 : totK PD2M8K2 D2M8K2.u11324 = [336687528240, 919102605923, 528344341488, 41719448686, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11324 = KTree.node D2M8K2.t11328 (nat_lit 24555896) (nat_lit 3419756427) (nat_lit 0) D2M8K2.t11329 from rfl, totK_node, tot11328, tot11329]
  decide +kernel

theorem arows11325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11325 = true := by
  rw [show D2M8K2.u11325 = KTree.node D2M8K2.t11330 (nat_lit 24557388) (nat_lit 2433872619) (nat_lit 0) D2M8K2.t11331 from rfl, allE_node, rows11330, irow11325, rows11331]
  all_goals rfl

theorem atot11325 : totK PD2M8K2 D2M8K2.u11325 = [0, 378571748972, 947230452207, 455498140260, 30800671508, 0, 0, 0] := by
  rw [show D2M8K2.u11325 = KTree.node D2M8K2.t11330 (nat_lit 24557388) (nat_lit 2433872619) (nat_lit 0) D2M8K2.t11331 from rfl, totK_node, tot11330, tot11331]
  decide +kernel

theorem arows11327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11327 = true := by
  rw [show D2M8K2.u11327 = KTree.node D2M8K2.t11332 (nat_lit 24558729) (nat_lit 1895653084) (nat_lit 0) D2M8K2.t11333 from rfl, allE_node, rows11332, irow11327, rows11333]
  all_goals rfl

theorem atot11327 : totK PD2M8K2 D2M8K2.u11327 = [312489422666, 796250380112, 556999304334, 141668876412, 6801036714, 0, 0, 0] := by
  rw [show D2M8K2.u11327 = KTree.node D2M8K2.t11332 (nat_lit 24558729) (nat_lit 1895653084) (nat_lit 0) D2M8K2.t11333 from rfl, totK_node, tot11332, tot11333]
  decide +kernel

theorem arows11328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11328 = true := by
  rw [show D2M8K2.u11328 = KTree.node D2M8K2.t11334 (nat_lit 24560257) (nat_lit 1441321856) (nat_lit 0) D2M8K2.t11335 from rfl, allE_node, rows11334, irow11328, rows11335]
  all_goals rfl

theorem atot11328 : totK PD2M8K2 D2M8K2.u11328 = [101331513776, 632444204482, 822740575733, 215127558939, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u11328 = KTree.node D2M8K2.t11334 (nat_lit 24560257) (nat_lit 1441321856) (nat_lit 0) D2M8K2.t11335 from rfl, totK_node, tot11334, tot11335]
  decide +kernel

theorem arows11331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11331 = true := by
  rw [show D2M8K2.u11331 = KTree.node D2M8K2.t11336 (nat_lit 24562149) (nat_lit 1449482134) (nat_lit 0) D2M8K2.t11337 from rfl, allE_node, rows11336, irow11331, rows11337]
  all_goals rfl

theorem atot11331 : totK PD2M8K2 D2M8K2.u11331 = [282975434275, 791330757260, 607068104677, 119451284580, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u11331 = KTree.node D2M8K2.t11336 (nat_lit 24562149) (nat_lit 1449482134) (nat_lit 0) D2M8K2.t11337 from rfl, totK_node, tot11336, tot11337]
  decide +kernel

theorem arows11332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11332 = true := by
  rw [show D2M8K2.u11332 = KTree.node D2M8K2.t11338 (nat_lit 24563643) (nat_lit 2408450923) (nat_lit 0) D2M8K2.t11339 from rfl, allE_node, rows11338, irow11332, rows11339]
  all_goals rfl

theorem atot11332 : totK PD2M8K2 D2M8K2.u11332 = [131071623720, 640210441720, 783007192377, 215627763189, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u11332 = KTree.node D2M8K2.t11338 (nat_lit 24563643) (nat_lit 2408450923) (nat_lit 0) D2M8K2.t11339 from rfl, totK_node, tot11338, tot11339]
  decide +kernel

theorem arows11334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11334 = true := by
  rw [show D2M8K2.u11334 = KTree.node D2M8K2.t11340 (nat_lit 24565496) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11341 from rfl, allE_node, rows11340, irow11334, rows11341]
  all_goals rfl

theorem atot11334 : totK PD2M8K2 D2M8K2.u11334 = [259485140390, 788009325297, 637151058505, 128082556476, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u11334 = KTree.node D2M8K2.t11340 (nat_lit 24565496) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11341 from rfl, totK_node, tot11340, tot11341]
  decide +kernel

theorem arows11335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11335 = true := by
  rw [show D2M8K2.u11335 = KTree.node D2M8K2.t11342 (nat_lit 24566661) (nat_lit 1726220677) (nat_lit 0) D2M8K2.t11343 from rfl, allE_node, rows11342, irow11335, rows11343]
  all_goals rfl

theorem atot11335 : totK PD2M8K2 D2M8K2.u11335 = [180183318095, 765001366926, 755946544399, 113417923546, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11335 = KTree.node D2M8K2.t11342 (nat_lit 24566661) (nat_lit 1726220677) (nat_lit 0) D2M8K2.t11343 from rfl, totK_node, tot11342, tot11343]
  decide +kernel

theorem arows11339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11339 = true := by
  rw [show D2M8K2.u11339 = KTree.node D2M8K2.t11344 (nat_lit 24572385) (nat_lit 1737235550) (nat_lit 0) D2M8K2.t11345 from rfl, allE_node, rows11344, irow11339, rows11345]
  all_goals rfl

theorem atot11339 : totK PD2M8K2 D2M8K2.u11339 = [0, 398245509137, 958904264831, 396996841176, 22145572651, 0, 0, 0] := by
  rw [show D2M8K2.u11339 = KTree.node D2M8K2.t11344 (nat_lit 24572385) (nat_lit 1737235550) (nat_lit 0) D2M8K2.t11345 from rfl, totK_node, tot11344, tot11345]
  decide +kernel

theorem arows11340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11340 = true := by
  rw [show D2M8K2.u11340 = KTree.node D2M8K2.t11346 (nat_lit 24574567) (nat_lit 1990081131) (nat_lit 0) D2M8K2.t11347 from rfl, allE_node, rows11346, irow11340, rows11347]
  all_goals rfl

theorem atot11340 : totK PD2M8K2 D2M8K2.u11340 = [0, 173485014645, 767929534084, 726036312532, 106467316773, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11340 = KTree.node D2M8K2.t11346 (nat_lit 24574567) (nat_lit 1990081131) (nat_lit 0) D2M8K2.t11347 from rfl, totK_node, tot11346, tot11347]
  decide +kernel

theorem arows11342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11342 = true := by
  rw [show D2M8K2.u11342 = KTree.node D2M8K2.t11348 (nat_lit 24576750) (nat_lit 3912898739) (nat_lit 0) D2M8K2.t11349 from rfl, allE_node, rows11348, irow11342, rows11349]
  all_goals rfl

theorem atot11342 : totK PD2M8K2 D2M8K2.u11342 = [0, 382946769316, 940119556130, 457960256445, 30137274223, 0, 0, 0] := by
  rw [show D2M8K2.u11342 = KTree.node D2M8K2.t11348 (nat_lit 24576750) (nat_lit 3912898739) (nat_lit 0) D2M8K2.t11349 from rfl, totK_node, tot11348, tot11349]
  decide +kernel

theorem arows11343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11343 = true := by
  rw [show D2M8K2.u11343 = KTree.node D2M8K2.t11350 (nat_lit 24579774) (nat_lit 2362933359) (nat_lit 0) D2M8K2.t11351 from rfl, allE_node, rows11350, irow11343, rows11351]
  all_goals rfl

theorem atot11343 : totK PD2M8K2 D2M8K2.u11343 = [0, 366414286024, 950829977862, 459738972634, 24540873380, 0, 0, 0] := by
  rw [show D2M8K2.u11343 = KTree.node D2M8K2.t11350 (nat_lit 24579774) (nat_lit 2362933359) (nat_lit 0) D2M8K2.t11351 from rfl, totK_node, tot11350, tot11351]
  decide +kernel

theorem arows11346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11346 = true := by
  rw [show D2M8K2.u11346 = KTree.node D2M8K2.t11352 (nat_lit 24583401) (nat_lit 1821171256) (nat_lit 0) D2M8K2.t11353 from rfl, allE_node, rows11352, irow11346, rows11353]
  all_goals rfl

theorem atot11346 : totK PD2M8K2 D2M8K2.u11346 = [0, 373442603486, 948663567682, 463446773357, 26127028216, 0, 0, 0] := by
  rw [show D2M8K2.u11346 = KTree.node D2M8K2.t11352 (nat_lit 24583401) (nat_lit 1821171256) (nat_lit 0) D2M8K2.t11353 from rfl, totK_node, tot11352, tot11353]
  decide +kernel

theorem arows11347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11347 = true := by
  rw [show D2M8K2.u11347 = KTree.node D2M8K2.t11354 (nat_lit 24586442) (nat_lit 4267280952) (nat_lit 0) D2M8K2.t11355 from rfl, allE_node, rows11354, irow11347, rows11355]
  all_goals rfl

theorem atot11347 : totK PD2M8K2 D2M8K2.u11347 = [0, 385896412335, 945634533557, 437623061695, 27892550339, 0, 0, 0] := by
  rw [show D2M8K2.u11347 = KTree.node D2M8K2.t11354 (nat_lit 24586442) (nat_lit 4267280952) (nat_lit 0) D2M8K2.t11355 from rfl, totK_node, tot11354, tot11355]
  decide +kernel

theorem arows11349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11349 = true := by
  rw [show D2M8K2.u11349 = KTree.node D2M8K2.t11356 (nat_lit 24587929) (nat_lit 1383366300) (nat_lit 0) D2M8K2.t11357 from rfl, allE_node, rows11356, irow11349, rows11357]
  all_goals rfl

theorem atot11349 : totK PD2M8K2 D2M8K2.u11349 = [0, 92584149739, 718467562662, 811666201313, 129117174233, 1095107716, 0, 0] := by
  rw [show D2M8K2.u11349 = KTree.node D2M8K2.t11356 (nat_lit 24587929) (nat_lit 1383366300) (nat_lit 0) D2M8K2.t11357 from rfl, totK_node, tot11356, tot11357]
  decide +kernel

theorem arows11350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11350 = true := by
  rw [show D2M8K2.u11350 = KTree.node D2M8K2.t11358 (nat_lit 24597038) (nat_lit 3803052382) (nat_lit 0) D2M8K2.t11359 from rfl, allE_node, rows11358, irow11350, rows11359]
  all_goals rfl

theorem atot11350 : totK PD2M8K2 D2M8K2.u11350 = [340079057287, 808458492837, 445601717375, 150654384497, 71419506712, 3882006667, 0, 0] := by
  rw [show D2M8K2.u11350 = KTree.node D2M8K2.t11358 (nat_lit 24597038) (nat_lit 3803052382) (nat_lit 0) D2M8K2.t11359 from rfl, totK_node, tot11358, tot11359]
  decide +kernel

theorem arows11355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11355 = true := by
  rw [show D2M8K2.u11355 = KTree.node D2M8K2.t11360 (nat_lit 24598560) (nat_lit 2242088954) (nat_lit 0) D2M8K2.t11361 from rfl, allE_node, rows11360, irow11355, rows11361]
  all_goals rfl

theorem atot11355 : totK PD2M8K2 D2M8K2.u11355 = [89923614195, 566254148523, 824038897382, 318399941520, 25359931193, 0, 0, 0] := by
  rw [show D2M8K2.u11355 = KTree.node D2M8K2.t11360 (nat_lit 24598560) (nat_lit 2242088954) (nat_lit 0) D2M8K2.t11361 from rfl, totK_node, tot11360, tot11361]
  decide +kernel

theorem arows11356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11356 = true := by
  rw [show D2M8K2.u11356 = KTree.node D2M8K2.t11362 (nat_lit 24599819) (nat_lit 2911071882) (nat_lit 0) D2M8K2.t11363 from rfl, allE_node, rows11362, irow11356, rows11363]
  all_goals rfl

theorem atot11356 : totK PD2M8K2 D2M8K2.u11356 = [211286606546, 632226602102, 699097568714, 269039342345, 12229515597, 0, 0, 0] := by
  rw [show D2M8K2.u11356 = KTree.node D2M8K2.t11362 (nat_lit 24599819) (nat_lit 2911071882) (nat_lit 0) D2M8K2.t11363 from rfl, totK_node, tot11362, tot11363]
  decide +kernel

theorem arows11358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11358 = true := by
  rw [show D2M8K2.u11358 = KTree.node D2M8K2.t11364 (nat_lit 24601396) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t11365 from rfl, allE_node, rows11364, irow11358, rows11365]
  all_goals rfl

theorem atot11358 : totK PD2M8K2 D2M8K2.u11358 = [192172715236, 771708860993, 722328607084, 120773048578, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u11358 = KTree.node D2M8K2.t11364 (nat_lit 24601396) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t11365 from rfl, totK_node, tot11364, tot11365]
  decide +kernel

theorem arows11359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11359 = true := by
  rw [show D2M8K2.u11359 = KTree.node D2M8K2.t11366 (nat_lit 24603337) (nat_lit 1517277401) (nat_lit 0) D2M8K2.t11367 from rfl, allE_node, rows11366, irow11359, rows11367]
  all_goals rfl

theorem atot11359 : totK PD2M8K2 D2M8K2.u11359 = [211429557122, 676794033853, 696999650749, 206232427515, 11846586184, 0, 0, 0] := by
  rw [show D2M8K2.u11359 = KTree.node D2M8K2.t11366 (nat_lit 24603337) (nat_lit 1517277401) (nat_lit 0) D2M8K2.t11367 from rfl, totK_node, tot11366, tot11367]
  decide +kernel

theorem arows11362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11362 = true := by
  rw [show D2M8K2.u11362 = KTree.node D2M8K2.t11368 (nat_lit 24604860) (nat_lit 3242536103) (nat_lit 0) D2M8K2.t11369 from rfl, allE_node, rows11368, irow11362, rows11369]
  all_goals rfl

theorem atot11362 : totK PD2M8K2 D2M8K2.u11362 = [189007297548, 767460724584, 727329076965, 124674699647, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u11362 = KTree.node D2M8K2.t11368 (nat_lit 24604860) (nat_lit 3242536103) (nat_lit 0) D2M8K2.t11369 from rfl, totK_node, tot11368, tot11369]
  decide +kernel

theorem arows11363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11363 = true := by
  rw [show D2M8K2.u11363 = KTree.node D2M8K2.t11370 (nat_lit 24610229) (nat_lit 2374301204) (nat_lit 0) D2M8K2.t11371 from rfl, allE_node, rows11370, irow11363, rows11371]
  all_goals rfl

theorem atot11363 : totK PD2M8K2 D2M8K2.u11363 = [216523885254, 678200043015, 696980343790, 210700934610, 12010829577, 0, 0, 0] := by
  rw [show D2M8K2.u11363 = KTree.node D2M8K2.t11370 (nat_lit 24610229) (nat_lit 2374301204) (nat_lit 0) D2M8K2.t11371 from rfl, totK_node, tot11370, tot11371]
  decide +kernel

theorem arows11365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11365 = true := by
  rw [show D2M8K2.u11365 = KTree.node D2M8K2.t11372 (nat_lit 24611700) (nat_lit 3200128714) (nat_lit 0) D2M8K2.t11373 from rfl, allE_node, rows11372, irow11365, rows11373]
  all_goals rfl

theorem atot11365 : totK PD2M8K2 D2M8K2.u11365 = [212497088019, 780785700009, 698043585856, 120939581916, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u11365 = KTree.node D2M8K2.t11372 (nat_lit 24611700) (nat_lit 3200128714) (nat_lit 0) D2M8K2.t11373 from rfl, totK_node, tot11372, tot11373]
  decide +kernel

theorem arows11366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11366 = true := by
  rw [show D2M8K2.u11366 = KTree.node D2M8K2.t11374 (nat_lit 24613402) (nat_lit 4021842791) (nat_lit 0) D2M8K2.t11375 from rfl, allE_node, rows11374, irow11366, rows11375]
  all_goals rfl

theorem atot11366 : totK PD2M8K2 D2M8K2.u11366 = [0, 363678190320, 910591813070, 477613201594, 42706721542, 0, 0, 0] := by
  rw [show D2M8K2.u11366 = KTree.node D2M8K2.t11374 (nat_lit 24613402) (nat_lit 4021842791) (nat_lit 0) D2M8K2.t11375 from rfl, totK_node, tot11374, tot11375]
  decide +kernel

theorem arows11370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11370 = true := by
  rw [show D2M8K2.u11370 = KTree.node D2M8K2.t11376 (nat_lit 24618304) (nat_lit 3717757236) (nat_lit 0) D2M8K2.t11377 from rfl, allE_node, rows11376, irow11370, rows11377]
  all_goals rfl

theorem atot11370 : totK PD2M8K2 D2M8K2.u11370 = [0, 380823828979, 949429647287, 465066719963, 27866845372, 0, 0, 0] := by
  rw [show D2M8K2.u11370 = KTree.node D2M8K2.t11376 (nat_lit 24618304) (nat_lit 3717757236) (nat_lit 0) D2M8K2.t11377 from rfl, totK_node, tot11376, tot11377]
  decide +kernel

theorem arows11371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11371 = true := by
  rw [show D2M8K2.u11371 = KTree.node D2M8K2.t11378 (nat_lit 24621296) (nat_lit 3529627069) (nat_lit 0) D2M8K2.t11379 from rfl, allE_node, rows11378, irow11371, rows11379]
  all_goals rfl

theorem atot11371 : totK PD2M8K2 D2M8K2.u11371 = [0, 335064857676, 911556146757, 522232336746, 40509460136, 0, 0, 0] := by
  rw [show D2M8K2.u11371 = KTree.node D2M8K2.t11378 (nat_lit 24621296) (nat_lit 3529627069) (nat_lit 0) D2M8K2.t11379 from rfl, totK_node, tot11378, tot11379]
  decide +kernel

theorem arows11373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11373 = true := by
  rw [show D2M8K2.u11373 = KTree.node D2M8K2.t11380 (nat_lit 24623123) (nat_lit 2330070553) (nat_lit 0) D2M8K2.t11381 from rfl, allE_node, rows11380, irow11373, rows11381]
  all_goals rfl

theorem atot11373 : totK PD2M8K2 D2M8K2.u11373 = [0, 139860632777, 671770209506, 777226683506, 170652235352, 4879840392, 0, 0] := by
  rw [show D2M8K2.u11373 = KTree.node D2M8K2.t11380 (nat_lit 24623123) (nat_lit 2330070553) (nat_lit 0) D2M8K2.t11381 from rfl, totK_node, tot11380, tot11381]
  decide +kernel

theorem arows11374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11374 = true := by
  rw [show D2M8K2.u11374 = KTree.node D2M8K2.t11382 (nat_lit 24625260) (nat_lit 2962010638) (nat_lit 0) D2M8K2.t11383 from rfl, allE_node, rows11382, irow11374, rows11383]
  all_goals rfl

theorem atot11374 : totK PD2M8K2 D2M8K2.u11374 = [0, 258522372213, 812637062034, 626089187376, 87547781406, 1107157161, 0, 0] := by
  rw [show D2M8K2.u11374 = KTree.node D2M8K2.t11382 (nat_lit 24625260) (nat_lit 2962010638) (nat_lit 0) D2M8K2.t11383 from rfl, totK_node, tot11382, tot11383]
  decide +kernel

theorem arows11377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11377 = true := by
  rw [show D2M8K2.u11377 = KTree.node D2M8K2.t11384 (nat_lit 24627253) (nat_lit 1215904753) (nat_lit 0) D2M8K2.t11385 from rfl, allE_node, rows11384, irow11377, rows11385]
  all_goals rfl

theorem atot11377 : totK PD2M8K2 D2M8K2.u11377 = [0, 171428166111, 743637622454, 741842421174, 141801584808, 3824247485, 0, 0] := by
  rw [show D2M8K2.u11377 = KTree.node D2M8K2.t11384 (nat_lit 24627253) (nat_lit 1215904753) (nat_lit 0) D2M8K2.t11385 from rfl, totK_node, tot11384, tot11385]
  decide +kernel

theorem arows11378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11378 = true := by
  rw [show D2M8K2.u11378 = KTree.node D2M8K2.t11386 (nat_lit 24632383) (nat_lit 2299740379) (nat_lit 0) D2M8K2.t11387 from rfl, allE_node, rows11386, irow11378, rows11387]
  all_goals rfl

theorem atot11378 : totK PD2M8K2 D2M8K2.u11378 = [0, 253685383600, 813409429133, 632996293513, 98283070070, 1242138600, 0, 0] := by
  rw [show D2M8K2.u11378 = KTree.node D2M8K2.t11386 (nat_lit 24632383) (nat_lit 2299740379) (nat_lit 0) D2M8K2.t11387 from rfl, totK_node, tot11386, tot11387]
  decide +kernel

theorem arows11380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11380 = true := by
  rw [show D2M8K2.u11380 = KTree.node D2M8K2.t11388 (nat_lit 24634113) (nat_lit 929194411) (nat_lit 0) D2M8K2.t11389 from rfl, allE_node, rows11388, irow11380, rows11389]
  all_goals rfl

theorem atot11380 : totK PD2M8K2 D2M8K2.u11380 = [0, 94445126902, 522769805378, 824454260572, 308625542768, 20509029466, 0, 0] := by
  rw [show D2M8K2.u11380 = KTree.node D2M8K2.t11388 (nat_lit 24634113) (nat_lit 929194411) (nat_lit 0) D2M8K2.t11389 from rfl, totK_node, tot11388, tot11389]
  decide +kernel

theorem arows11381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11381 = true := by
  rw [show D2M8K2.u11381 = KTree.node D2M8K2.t11390 (nat_lit 24680457) (nat_lit 1842761263) (nat_lit 0) D2M8K2.t11391 from rfl, allE_node, rows11390, irow11381, rows11391]
  all_goals rfl

theorem atot11381 : totK PD2M8K2 D2M8K2.u11381 = [0, 354973924510, 929383313729, 505877632963, 44009941886, 0, 0, 0] := by
  rw [show D2M8K2.u11381 = KTree.node D2M8K2.t11390 (nat_lit 24680457) (nat_lit 1842761263) (nat_lit 0) D2M8K2.t11391 from rfl, totK_node, tot11390, tot11391]
  decide +kernel

theorem arows11388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11388 = true := by
  rw [show D2M8K2.u11388 = KTree.node D2M8K2.t11392 (nat_lit 24681914) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t11393 from rfl, allE_node, rows11392, irow11388, rows11393]
  all_goals rfl

theorem atot11388 : totK PD2M8K2 D2M8K2.u11388 = [0, 0, 390064020046, 946292933296, 449657200776, 30804453458, 0, 0] := by
  rw [show D2M8K2.u11388 = KTree.node D2M8K2.t11392 (nat_lit 24681914) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t11393 from rfl, totK_node, tot11392, tot11393]
  decide +kernel

theorem arows11389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11389 = true := by
  rw [show D2M8K2.u11389 = KTree.node D2M8K2.t11394 (nat_lit 24683235) (nat_lit 3690477071) (nat_lit 0) D2M8K2.t11395 from rfl, allE_node, rows11394, irow11389, rows11395]
  all_goals rfl

theorem atot11389 : totK PD2M8K2 D2M8K2.u11389 = [0, 334249120324, 823646764406, 519577861488, 130459634534, 6804944647, 0, 0] := by
  rw [show D2M8K2.u11389 = KTree.node D2M8K2.t11394 (nat_lit 24683235) (nat_lit 3690477071) (nat_lit 0) D2M8K2.t11395 from rfl, totK_node, tot11394, tot11395]
  decide +kernel

theorem arows11391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11391 = true := by
  rw [show D2M8K2.u11391 = KTree.node D2M8K2.t11396 (nat_lit 24684802) (nat_lit 4031730029) (nat_lit 0) D2M8K2.t11397 from rfl, allE_node, rows11396, irow11391, rows11397]
  all_goals rfl

theorem atot11391 : totK PD2M8K2 D2M8K2.u11391 = [0, 85897637668, 622399547329, 863483476858, 208635446269, 6564653432, 0, 0] := by
  rw [show D2M8K2.u11391 = KTree.node D2M8K2.t11396 (nat_lit 24684802) (nat_lit 4031730029) (nat_lit 0) D2M8K2.t11397 from rfl, totK_node, tot11396, tot11397]
  decide +kernel

theorem arows11392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11392 = true := by
  rw [show D2M8K2.u11392 = KTree.node D2M8K2.t11398 (nat_lit 24686627) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t11399 from rfl, allE_node, rows11398, irow11392, rows11399]
  all_goals rfl

theorem atot11392 : totK PD2M8K2 D2M8K2.u11392 = [0, 315633426598, 822326919243, 563553418857, 104984224577, 2141762517, 0, 0] := by
  rw [show D2M8K2.u11392 = KTree.node D2M8K2.t11398 (nat_lit 24686627) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t11399 from rfl, totK_node, tot11398, tot11399]
  decide +kernel

theorem arows11395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11395 = true := by
  rw [show D2M8K2.u11395 = KTree.node D2M8K2.t11400 (nat_lit 24688155) (nat_lit 1589181965) (nat_lit 0) D2M8K2.t11401 from rfl, allE_node, rows11400, irow11395, rows11401]
  all_goals rfl

theorem atot11395 : totK PD2M8K2 D2M8K2.u11395 = [0, 104737320029, 644147611255, 820319260469, 203705294558, 6603055607, 0, 0] := by
  rw [show D2M8K2.u11395 = KTree.node D2M8K2.t11400 (nat_lit 24688155) (nat_lit 1589181965) (nat_lit 0) D2M8K2.t11401 from rfl, totK_node, tot11400, tot11401]
  decide +kernel

theorem arows11396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11396 = true := by
  rw [show D2M8K2.u11396 = KTree.node D2M8K2.t11402 (nat_lit 24690027) (nat_lit 3695183521) (nat_lit 0) D2M8K2.t11403 from rfl, allE_node, rows11402, irow11396, rows11403]
  all_goals rfl

theorem atot11396 : totK PD2M8K2 D2M8K2.u11396 = [0, 277929188432, 790337588343, 608011873225, 120462674682, 2221265353, 0, 0] := by
  rw [show D2M8K2.u11396 = KTree.node D2M8K2.t11402 (nat_lit 24690027) (nat_lit 3695183521) (nat_lit 0) D2M8K2.t11403 from rfl, totK_node, tot11402, tot11403]
  decide +kernel

theorem arows11398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11398 = true := by
  rw [show D2M8K2.u11398 = KTree.node D2M8K2.t11404 (nat_lit 24691488) (nat_lit 3363651533) (nat_lit 0) D2M8K2.t11405 from rfl, allE_node, rows11404, irow11398, rows11405]
  all_goals rfl

theorem atot11398 : totK PD2M8K2 D2M8K2.u11398 = [0, 143243288736, 750862793878, 806983738114, 111028265872, 0, 0, 0] := by
  rw [show D2M8K2.u11398 = KTree.node D2M8K2.t11404 (nat_lit 24691488) (nat_lit 3363651533) (nat_lit 0) D2M8K2.t11405 from rfl, totK_node, tot11404, tot11405]
  decide +kernel

theorem arows11399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11399 = true := by
  rw [show D2M8K2.u11399 = KTree.node D2M8K2.t11406 (nat_lit 24693600) (nat_lit 2616819561) (nat_lit 0) D2M8K2.t11407 from rfl, allE_node, rows11406, irow11399, rows11407]
  all_goals rfl

theorem atot11399 : totK PD2M8K2 D2M8K2.u11399 = [0, 314778734707, 807139737965, 558003194043, 118437845679, 2498823382, 0, 0] := by
  rw [show D2M8K2.u11399 = KTree.node D2M8K2.t11406 (nat_lit 24693600) (nat_lit 2616819561) (nat_lit 0) D2M8K2.t11407 from rfl, totK_node, tot11406, tot11407]
  decide +kernel

theorem arows11403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11403 = true := by
  rw [show D2M8K2.u11403 = KTree.node D2M8K2.t11408 (nat_lit 24695179) (nat_lit 1778438129) (nat_lit 0) D2M8K2.t11409 from rfl, allE_node, rows11408, irow11403, rows11409]
  all_goals rfl

theorem atot11403 : totK PD2M8K2 D2M8K2.u11403 = [0, 91855302876, 619170489809, 855992825623, 213116145215, 2307515475, 0, 0] := by
  rw [show D2M8K2.u11403 = KTree.node D2M8K2.t11408 (nat_lit 24695179) (nat_lit 1778438129) (nat_lit 0) D2M8K2.t11409 from rfl, totK_node, tot11408, tot11409]
  decide +kernel

theorem arows11404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11404 = true := by
  rw [show D2M8K2.u11404 = KTree.node D2M8K2.t11410 (nat_lit 24700514) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t11411 from rfl, allE_node, rows11410, irow11404, rows11411]
  all_goals rfl

theorem atot11404 : totK PD2M8K2 D2M8K2.u11404 = [0, 0, 361490406257, 914430332589, 503354742161, 41740452966, 0, 0] := by
  rw [show D2M8K2.u11404 = KTree.node D2M8K2.t11410 (nat_lit 24700514) (nat_lit 4114323956) (nat_lit 0) D2M8K2.t11411 from rfl, totK_node, tot11410, tot11411]
  decide +kernel

theorem arows11406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11406 = true := by
  rw [show D2M8K2.u11406 = KTree.node D2M8K2.t11412 (nat_lit 24701689) (nat_lit 1271732196) (nat_lit 0) D2M8K2.t11413 from rfl, allE_node, rows11412, irow11406, rows11413]
  all_goals rfl

theorem atot11406 : totK PD2M8K2 D2M8K2.u11406 = [0, 0, 175680115246, 689894928483, 711102531680, 224212955201, 21385604922, 0] := by
  rw [show D2M8K2.u11406 = KTree.node D2M8K2.t11412 (nat_lit 24701689) (nat_lit 1271732196) (nat_lit 0) D2M8K2.t11413 from rfl, totK_node, tot11412, tot11413]
  decide +kernel

theorem arows11407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11407 = true := by
  rw [show D2M8K2.u11407 = KTree.node D2M8K2.t11414 (nat_lit 24703206) (nat_lit 3464537022) (nat_lit 0) D2M8K2.t11415 from rfl, allE_node, rows11414, irow11407, rows11415]
  all_goals rfl

theorem atot11407 : totK PD2M8K2 D2M8K2.u11407 = [0, 0, 150546653249, 530686331363, 745832629834, 322246464651, 15536268932, 0] := by
  rw [show D2M8K2.u11407 = KTree.node D2M8K2.t11414 (nat_lit 24703206) (nat_lit 3464537022) (nat_lit 0) D2M8K2.t11415 from rfl, totK_node, tot11414, tot11415]
  decide +kernel

theorem arows11410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11410 = true := by
  rw [show D2M8K2.u11410 = KTree.node D2M8K2.t11416 (nat_lit 24704733) (nat_lit 1499306159) (nat_lit 0) D2M8K2.t11417 from rfl, allE_node, rows11416, irow11410, rows11417]
  all_goals rfl

theorem atot11410 : totK PD2M8K2 D2M8K2.u11410 = [0, 0, 260722520627, 871259186843, 606566811322, 54738610643, 0, 0] := by
  rw [show D2M8K2.u11410 = KTree.node D2M8K2.t11416 (nat_lit 24704733) (nat_lit 1499306159) (nat_lit 0) D2M8K2.t11417 from rfl, totK_node, tot11416, tot11417]
  decide +kernel

theorem arows11411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11411 = true := by
  rw [show D2M8K2.u11411 = KTree.node D2M8K2.t11418 (nat_lit 24706629) (nat_lit 1126872306) (nat_lit 0) D2M8K2.t11419 from rfl, allE_node, rows11418, irow11411, rows11419]
  all_goals rfl

theorem atot11411 : totK PD2M8K2 D2M8K2.u11411 = [0, 0, 154782206337, 652047843596, 783711553212, 180444708286, 5067863418, 0] := by
  rw [show D2M8K2.u11411 = KTree.node D2M8K2.t11418 (nat_lit 24706629) (nat_lit 1126872306) (nat_lit 0) D2M8K2.t11419 from rfl, totK_node, tot11418, tot11419]
  decide +kernel

theorem arows11413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11413 = true := by
  rw [show D2M8K2.u11413 = KTree.node D2M8K2.t11420 (nat_lit 24708341) (nat_lit 2091783588) (nat_lit 0) D2M8K2.t11421 from rfl, allE_node, rows11420, irow11413, rows11421]
  all_goals rfl

theorem atot11413 : totK PD2M8K2 D2M8K2.u11413 = [0, 0, 260857234067, 867909968311, 609220915500, 49963531878, 0, 0] := by
  rw [show D2M8K2.u11413 = KTree.node D2M8K2.t11420 (nat_lit 24708341) (nat_lit 2091783588) (nat_lit 0) D2M8K2.t11421 from rfl, totK_node, tot11420, tot11421]
  decide +kernel

theorem arows11414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11414 = true := by
  rw [show D2M8K2.u11414 = KTree.node D2M8K2.t11422 (nat_lit 24710237) (nat_lit 1892105378) (nat_lit 0) D2M8K2.t11423 from rfl, allE_node, rows11422, irow11414, rows11423]
  all_goals rfl

theorem atot11414 : totK PD2M8K2 D2M8K2.u11414 = [0, 0, 188462997637, 650370009890, 736135736330, 181949751753, 5126512042, 0] := by
  rw [show D2M8K2.u11414 = KTree.node D2M8K2.t11422 (nat_lit 24710237) (nat_lit 1892105378) (nat_lit 0) D2M8K2.t11423 from rfl, totK_node, tot11422, tot11423]
  decide +kernel

theorem arows11419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11419 = true := by
  rw [show D2M8K2.u11419 = KTree.node D2M8K2.t11424 (nat_lit 24711620) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t11425 from rfl, allE_node, rows11424, irow11419, rows11425]
  all_goals rfl

theorem atot11419 : totK PD2M8K2 D2M8K2.u11419 = [0, 0, 223729905005, 847825852254, 660402911830, 53191587803, 0, 0] := by
  rw [show D2M8K2.u11419 = KTree.node D2M8K2.t11424 (nat_lit 24711620) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t11425 from rfl, totK_node, tot11424, tot11425]
  decide +kernel

theorem arows11420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11420 = true := by
  rw [show D2M8K2.u11420 = KTree.node D2M8K2.t11426 (nat_lit 24714195) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t11427 from rfl, allE_node, rows11426, irow11420, rows11427]
  all_goals rfl

theorem atot11420 : totK PD2M8K2 D2M8K2.u11420 = [0, 0, 251469085656, 772300134871, 659205820064, 110302376851, 1392055030, 0] := by
  rw [show D2M8K2.u11420 = KTree.node D2M8K2.t11426 (nat_lit 24714195) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t11427 from rfl, totK_node, tot11426, tot11427]
  decide +kernel

theorem arows11422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11422 = true := by
  rw [show D2M8K2.u11422 = KTree.node D2M8K2.t11428 (nat_lit 24715708) (nat_lit 3625502302) (nat_lit 0) D2M8K2.t11429 from rfl, allE_node, rows11428, irow11422, rows11429]
  all_goals rfl

theorem atot11422 : totK PD2M8K2 D2M8K2.u11422 = [0, 0, 150518623154, 717858389024, 774086673898, 134079272854, 1215345381, 0] := by
  rw [show D2M8K2.u11422 = KTree.node D2M8K2.t11428 (nat_lit 24715708) (nat_lit 3625502302) (nat_lit 0) D2M8K2.t11429 from rfl, totK_node, tot11428, tot11429]
  decide +kernel

theorem arows11423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11423 = true := by
  rw [show D2M8K2.u11423 = KTree.node D2M8K2.t11430 (nat_lit 24717582) (nat_lit 2743738979) (nat_lit 0) D2M8K2.t11431 from rfl, allE_node, rows11430, irow11423, rows11431]
  all_goals rfl

theorem atot11423 : totK PD2M8K2 D2M8K2.u11423 = [0, 283783099808, 680982434915, 379337433698, 278631233700, 132183714156, 7923721866, 0] := by
  rw [show D2M8K2.u11423 = KTree.node D2M8K2.t11430 (nat_lit 24717582) (nat_lit 2743738979) (nat_lit 0) D2M8K2.t11431 from rfl, totK_node, tot11430, tot11431]
  decide +kernel

theorem arows11426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11426 = true := by
  rw [show D2M8K2.u11426 = KTree.node D2M8K2.t11432 (nat_lit 24720196) (nat_lit 3708996614) (nat_lit 0) D2M8K2.t11433 from rfl, allE_node, rows11432, irow11426, rows11433]
  all_goals rfl

theorem atot11426 : totK PD2M8K2 D2M8K2.u11426 = [0, 134664397987, 705849334007, 837002492283, 132515133577, 1275377855, 0, 0] := by
  rw [show D2M8K2.u11426 = KTree.node D2M8K2.t11432 (nat_lit 24720196) (nat_lit 3708996614) (nat_lit 0) D2M8K2.t11433 from rfl, totK_node, tot11432, tot11433]
  decide +kernel

theorem arows11427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11427 = true := by
  rw [show D2M8K2.u11427 = KTree.node D2M8K2.t11434 (nat_lit 24721970) (nat_lit 4046883989) (nat_lit 0) D2M8K2.t11435 from rfl, allE_node, rows11434, irow11427, rows11435]
  all_goals rfl

theorem atot11427 : totK PD2M8K2 D2M8K2.u11427 = [0, 335343125088, 913440924406, 516209612432, 48689320768, 0, 0, 0] := by
  rw [show D2M8K2.u11427 = KTree.node D2M8K2.t11434 (nat_lit 24721970) (nat_lit 4046883989) (nat_lit 0) D2M8K2.t11435 from rfl, totK_node, tot11434, tot11435]
  decide +kernel

theorem arows11429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11429 = true := by
  rw [show D2M8K2.u11429 = KTree.node D2M8K2.t11436 (nat_lit 24723459) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t11437 from rfl, allE_node, rows11436, irow11429, rows11437]
  all_goals rfl

theorem atot11429 : totK PD2M8K2 D2M8K2.u11429 = [0, 0, 371227698132, 947665976009, 453828524344, 30730646440, 0, 0] := by
  rw [show D2M8K2.u11429 = KTree.node D2M8K2.t11436 (nat_lit 24723459) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t11437 from rfl, totK_node, tot11436, tot11437]
  decide +kernel

theorem arows11430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11430 = true := by
  rw [show D2M8K2.u11430 = KTree.node D2M8K2.t11438 (nat_lit 24724737) (nat_lit 1743436877) (nat_lit 0) D2M8K2.t11439 from rfl, allE_node, rows11438, irow11430, rows11439]
  all_goals rfl

theorem atot11430 : totK PD2M8K2 D2M8K2.u11430 = [0, 351869631213, 859164492690, 483483060634, 113080806589, 6756679742, 0, 0] := by
  rw [show D2M8K2.u11430 = KTree.node D2M8K2.t11438 (nat_lit 24724737) (nat_lit 1743436877) (nat_lit 0) D2M8K2.t11439 from rfl, totK_node, tot11438, tot11439]
  decide +kernel

theorem arows11434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11434 = true := by
  rw [show D2M8K2.u11434 = KTree.node D2M8K2.t11440 (nat_lit 24726267) (nat_lit 3785722185) (nat_lit 0) D2M8K2.t11441 from rfl, allE_node, rows11440, irow11434, rows11441]
  all_goals rfl

theorem atot11434 : totK PD2M8K2 D2M8K2.u11434 = [0, 86646866432, 610325230624, 858838444499, 224476933707, 9587713104, 0, 0] := by
  rw [show D2M8K2.u11434 = KTree.node D2M8K2.t11440 (nat_lit 24726267) (nat_lit 3785722185) (nat_lit 0) D2M8K2.t11441 from rfl, totK_node, tot11440, tot11441]
  decide +kernel

theorem arows11435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11435 = true := by
  rw [show D2M8K2.u11435 = KTree.node D2M8K2.t11442 (nat_lit 24731506) (nat_lit 3234735674) (nat_lit 0) D2M8K2.t11443 from rfl, allE_node, rows11442, irow11435, rows11443]
  all_goals rfl

theorem atot11435 : totK PD2M8K2 D2M8K2.u11435 = [0, 297661919600, 793372858923, 589179150334, 114461787247, 3462014130, 0, 0] := by
  rw [show D2M8K2.u11435 = KTree.node D2M8K2.t11442 (nat_lit 24731506) (nat_lit 3234735674) (nat_lit 0) D2M8K2.t11443 from rfl, totK_node, tot11442, tot11443]
  decide +kernel

theorem arows11437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11437 = true := by
  rw [show D2M8K2.u11437 = KTree.node D2M8K2.t11444 (nat_lit 24733026) (nat_lit 1964766957) (nat_lit 0) D2M8K2.t11445 from rfl, allE_node, rows11444, irow11437, rows11445]
  all_goals rfl

theorem atot11437 : totK PD2M8K2 D2M8K2.u11437 = [0, 112281440014, 723730873088, 825468020645, 133215894404, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11437 = KTree.node D2M8K2.t11444 (nat_lit 24733026) (nat_lit 1964766957) (nat_lit 0) D2M8K2.t11445 from rfl, totK_node, tot11444, tot11445]
  decide +kernel

theorem arows11438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11438 = true := by
  rw [show D2M8K2.u11438 = KTree.node D2M8K2.t11446 (nat_lit 24735092) (nat_lit 3057697910) (nat_lit 0) D2M8K2.t11447 from rfl, allE_node, rows11446, irow11438, rows11447]
  all_goals rfl

theorem atot11438 : totK PD2M8K2 D2M8K2.u11438 = [0, 320652799013, 821918143177, 555088506094, 112112193885, 3884009855, 0, 0] := by
  rw [show D2M8K2.u11438 = KTree.node D2M8K2.t11446 (nat_lit 24735092) (nat_lit 3057697910) (nat_lit 0) D2M8K2.t11447 from rfl, totK_node, tot11446, tot11447]
  decide +kernel

theorem arows11441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11441 = true := by
  rw [show D2M8K2.u11441 = KTree.node D2M8K2.t11448 (nat_lit 24736725) (nat_lit 1363845599) (nat_lit 0) D2M8K2.t11449 from rfl, allE_node, rows11448, irow11441, rows11449]
  all_goals rfl

theorem atot11441 : totK PD2M8K2 D2M8K2.u11441 = [0, 62160131298, 566712974665, 892850167129, 258061042392, 6222784045, 0, 0] := by
  rw [show D2M8K2.u11441 = KTree.node D2M8K2.t11448 (nat_lit 24736725) (nat_lit 1363845599) (nat_lit 0) D2M8K2.t11449 from rfl, totK_node, tot11448, tot11449]
  decide +kernel

theorem arows11442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11442 = true := by
  rw [show D2M8K2.u11442 = KTree.node D2M8K2.t11450 (nat_lit 24738760) (nat_lit 3834472075) (nat_lit 0) D2M8K2.t11451 from rfl, allE_node, rows11450, irow11442, rows11451]
  all_goals rfl

theorem atot11442 : totK PD2M8K2 D2M8K2.u11442 = [0, 0, 413436922964, 972601749965, 358950269955, 15181765150, 0, 0] := by
  rw [show D2M8K2.u11442 = KTree.node D2M8K2.t11450 (nat_lit 24738760) (nat_lit 3834472075) (nat_lit 0) D2M8K2.t11451 from rfl, totK_node, tot11450, tot11451]
  decide +kernel

theorem arows11444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11444 = true := by
  rw [show D2M8K2.u11444 = KTree.node D2M8K2.t11452 (nat_lit 24742489) (nat_lit 696078483) (nat_lit 0) D2M8K2.t11453 from rfl, allE_node, rows11452, irow11444, rows11453]
  all_goals rfl

theorem atot11444 : totK PD2M8K2 D2M8K2.u11444 = [0, 0, 352472097778, 937995734267, 485260514628, 34980311049, 0, 0] := by
  rw [show D2M8K2.u11444 = KTree.node D2M8K2.t11452 (nat_lit 24742489) (nat_lit 696078483) (nat_lit 0) D2M8K2.t11453 from rfl, totK_node, tot11452, tot11453]
  decide +kernel

theorem arows11445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11445 = true := by
  rw [show D2M8K2.u11445 = KTree.node D2M8K2.t11454 (nat_lit 24745495) (nat_lit 1627625856) (nat_lit 0) D2M8K2.t11455 from rfl, allE_node, rows11454, irow11445, rows11455]
  all_goals rfl

theorem atot11445 : totK PD2M8K2 D2M8K2.u11445 = [0, 0, 349191983452, 923395855551, 483622717021, 35145091269, 0, 0] := by
  rw [show D2M8K2.u11445 = KTree.node D2M8K2.t11454 (nat_lit 24745495) (nat_lit 1627625856) (nat_lit 0) D2M8K2.t11455 from rfl, totK_node, tot11454, tot11455]
  decide +kernel

theorem arows11451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11451 = true := by
  rw [show D2M8K2.u11451 = KTree.node D2M8K2.t11456 (nat_lit 24747272) (nat_lit 3522523285) (nat_lit 0) D2M8K2.t11457 from rfl, allE_node, rows11456, irow11451, rows11457]
  all_goals rfl

theorem atot11451 : totK PD2M8K2 D2M8K2.u11451 = [0, 0, 86023540623, 614547024172, 843675109157, 193549150518, 5320761635, 0] := by
  rw [show D2M8K2.u11451 = KTree.node D2M8K2.t11456 (nat_lit 24747272) (nat_lit 3522523285) (nat_lit 0) D2M8K2.t11457 from rfl, totK_node, tot11456, tot11457]
  decide +kernel

theorem arows11452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11452 = true := by
  rw [show D2M8K2.u11452 = KTree.node D2M8K2.t11458 (nat_lit 24752468) (nat_lit 3136047754) (nat_lit 0) D2M8K2.t11459 from rfl, allE_node, rows11458, irow11452, rows11459]
  all_goals rfl

theorem atot11452 : totK PD2M8K2 D2M8K2.u11452 = [0, 0, 392801516952, 950323795630, 428949909630, 25853049624, 0, 0] := by
  rw [show D2M8K2.u11452 = KTree.node D2M8K2.t11458 (nat_lit 24752468) (nat_lit 3136047754) (nat_lit 0) D2M8K2.t11459 from rfl, totK_node, tot11458, tot11459]
  decide +kernel

theorem arows11454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11454 = true := by
  rw [show D2M8K2.u11454 = KTree.node D2M8K2.t11460 (nat_lit 24754564) (nat_lit 2780663339) (nat_lit 0) D2M8K2.t11461 from rfl, allE_node, rows11460, irow11454, rows11461]
  all_goals rfl

theorem atot11454 : totK PD2M8K2 D2M8K2.u11454 = [0, 0, 167412957984, 775683119963, 709013733625, 95543296928, 1225787871, 0] := by
  rw [show D2M8K2.u11454 = KTree.node D2M8K2.t11460 (nat_lit 24754564) (nat_lit 2780663339) (nat_lit 0) D2M8K2.t11461 from rfl, totK_node, tot11460, tot11461]
  decide +kernel

theorem arows11455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11455 = true := by
  rw [show D2M8K2.u11455 = KTree.node D2M8K2.t11462 (nat_lit 24756419) (nat_lit 2656748349) (nat_lit 0) D2M8K2.t11463 from rfl, allE_node, rows11462, irow11455, rows11463]
  all_goals rfl

theorem atot11455 : totK PD2M8K2 D2M8K2.u11455 = [0, 85430600343, 445003494198, 777074802730, 449012558007, 38062205523, 0, 0] := by
  rw [show D2M8K2.u11455 = KTree.node D2M8K2.t11462 (nat_lit 24756419) (nat_lit 2656748349) (nat_lit 0) D2M8K2.t11463 from rfl, totK_node, tot11462, tot11463]
  decide +kernel

theorem arows11458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11458 = true := by
  rw [show D2M8K2.u11458 = KTree.node D2M8K2.t11464 (nat_lit 24760258) (nat_lit 4040465123) (nat_lit 0) D2M8K2.t11465 from rfl, allE_node, rows11464, irow11458, rows11465]
  all_goals rfl

theorem atot11458 : totK PD2M8K2 D2M8K2.u11458 = [0, 239580803521, 790200947794, 660268006439, 98610704827, 1310517177, 0, 0] := by
  rw [show D2M8K2.u11458 = KTree.node D2M8K2.t11464 (nat_lit 24760258) (nat_lit 4040465123) (nat_lit 0) D2M8K2.t11465 from rfl, totK_node, tot11464, tot11465]
  decide +kernel

theorem arows11459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11459 = true := by
  rw [show D2M8K2.u11459 = KTree.node D2M8K2.t11466 (nat_lit 24762811) (nat_lit 1169983801) (nat_lit 0) D2M8K2.t11467 from rfl, allE_node, rows11466, irow11459, rows11467]
  all_goals rfl

theorem atot11459 : totK PD2M8K2 D2M8K2.u11459 = [0, 290818680508, 855885647685, 625553349410, 65685357952, 0, 0, 0] := by
  rw [show D2M8K2.u11459 = KTree.node D2M8K2.t11466 (nat_lit 24762811) (nat_lit 1169983801) (nat_lit 0) D2M8K2.t11467 from rfl, totK_node, tot11466, tot11467]
  decide +kernel

theorem arows11461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11461 = true := by
  rw [show D2M8K2.u11461 = KTree.node D2M8K2.t11468 (nat_lit 24764338) (nat_lit 3921309467) (nat_lit 0) D2M8K2.t11469 from rfl, allE_node, rows11468, irow11461, rows11469]
  all_goals rfl

theorem atot11461 : totK PD2M8K2 D2M8K2.u11461 = [0, 138141707029, 628409082647, 734552284833, 286699927477, 25298831311, 0, 0] := by
  rw [show D2M8K2.u11461 = KTree.node D2M8K2.t11468 (nat_lit 24764338) (nat_lit 3921309467) (nat_lit 0) D2M8K2.t11469 from rfl, totK_node, tot11468, tot11469]
  decide +kernel

theorem arows11462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11462 = true := by
  rw [show D2M8K2.u11462 = KTree.node D2M8K2.t11470 (nat_lit 24765580) (nat_lit 3692259456) (nat_lit 0) D2M8K2.t11471 from rfl, allE_node, rows11470, irow11462, rows11471]
  all_goals rfl

theorem atot11462 : totK PD2M8K2 D2M8K2.u11462 = [0, 171723400371, 591254150389, 733301754609, 291965283647, 12186868223, 0, 0] := by
  rw [show D2M8K2.u11462 = KTree.node D2M8K2.t11470 (nat_lit 24765580) (nat_lit 3692259456) (nat_lit 0) D2M8K2.t11471 from rfl, totK_node, tot11470, tot11471]
  decide +kernel

theorem arows11466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11466 = true := by
  rw [show D2M8K2.u11466 = KTree.node D2M8K2.t11472 (nat_lit 24770504) (nat_lit 3744693544) (nat_lit 0) D2M8K2.t11473 from rfl, allE_node, rows11472, irow11466, rows11473]
  all_goals rfl

theorem atot11466 : totK PD2M8K2 D2M8K2.u11466 = [0, 266980621076, 804439847200, 627383704826, 95098616824, 1178750802, 0, 0] := by
  rw [show D2M8K2.u11466 = KTree.node D2M8K2.t11472 (nat_lit 24770504) (nat_lit 3744693544) (nat_lit 0) D2M8K2.t11473 from rfl, totK_node, tot11472, tot11473]
  decide +kernel

theorem arows11467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11467 = true := by
  rw [show D2M8K2.u11467 = KTree.node D2M8K2.t11474 (nat_lit 24772140) (nat_lit 3032076892) (nat_lit 0) D2M8K2.t11475 from rfl, allE_node, rows11474, irow11467, rows11475]
  all_goals rfl

theorem atot11467 : totK PD2M8K2 D2M8K2.u11467 = [0, 121014833368, 604612371852, 805401365762, 241561246755, 12017349186, 0, 0] := by
  rw [show D2M8K2.u11467 = KTree.node D2M8K2.t11474 (nat_lit 24772140) (nat_lit 3032076892) (nat_lit 0) D2M8K2.t11475 from rfl, totK_node, tot11474, tot11475]
  decide +kernel

theorem arows11469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11469 = true := by
  rw [show D2M8K2.u11469 = KTree.node D2M8K2.t11476 (nat_lit 24773588) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t11477 from rfl, allE_node, rows11476, irow11469, rows11477]
  all_goals rfl

theorem atot11469 : totK PD2M8K2 D2M8K2.u11469 = [0, 292773207309, 873537511503, 582996569924, 61391599003, 0, 0, 0] := by
  rw [show D2M8K2.u11469 = KTree.node D2M8K2.t11476 (nat_lit 24773588) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t11477 from rfl, totK_node, tot11476, tot11477]
  decide +kernel

theorem arows11470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11470 = true := by
  rw [show D2M8K2.u11470 = KTree.node D2M8K2.t11478 (nat_lit 24775556) (nat_lit 3384184800) (nat_lit 0) D2M8K2.t11479 from rfl, allE_node, rows11478, irow11470, rows11479]
  all_goals rfl

theorem atot11470 : totK PD2M8K2 D2M8K2.u11470 = [0, 153057018287, 674643255097, 790067580552, 190297007389, 4980514959, 0, 0] := by
  rw [show D2M8K2.u11470 = KTree.node D2M8K2.t11478 (nat_lit 24775556) (nat_lit 3384184800) (nat_lit 0) D2M8K2.t11479 from rfl, totK_node, tot11478, tot11479]
  decide +kernel

theorem arows11473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11473 = true := by
  rw [show D2M8K2.u11473 = KTree.node D2M8K2.t11480 (nat_lit 24777530) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t11481 from rfl, allE_node, rows11480, irow11473, rows11481]
  all_goals rfl

theorem atot11473 : totK PD2M8K2 D2M8K2.u11473 = [0, 233675638286, 786945125063, 677841142337, 111087678497, 1232609433, 0, 0] := by
  rw [show D2M8K2.u11473 = KTree.node D2M8K2.t11480 (nat_lit 24777530) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t11481 from rfl, totK_node, tot11480, tot11481]
  decide +kernel

theorem arows11474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11474 = true := by
  rw [show D2M8K2.u11474 = KTree.node D2M8K2.t11482 (nat_lit 24779313) (nat_lit 1162376633) (nat_lit 0) D2M8K2.t11483 from rfl, allE_node, rows11482, irow11474, rows11483]
  all_goals rfl

theorem atot11474 : totK PD2M8K2 D2M8K2.u11474 = [0, 0, 424206627559, 960904466617, 372026036484, 17973113626, 0, 0] := by
  rw [show D2M8K2.u11474 = KTree.node D2M8K2.t11482 (nat_lit 24779313) (nat_lit 1162376633) (nat_lit 0) D2M8K2.t11483 from rfl, totK_node, tot11482, tot11483]
  decide +kernel

theorem arows11476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11476 = true := by
  rw [show D2M8K2.u11476 = KTree.node D2M8K2.t11484 (nat_lit 24783459) (nat_lit 3693876886) (nat_lit 0) D2M8K2.t11485 from rfl, allE_node, rows11484, irow11476, rows11485]
  all_goals rfl

theorem atot11476 : totK PD2M8K2 D2M8K2.u11476 = [0, 0, 405232194211, 946791044950, 434014656788, 31518471056, 0, 0] := by
  rw [show D2M8K2.u11476 = KTree.node D2M8K2.t11484 (nat_lit 24783459) (nat_lit 3693876886) (nat_lit 0) D2M8K2.t11485 from rfl, totK_node, tot11484, tot11485]
  decide +kernel

theorem arows11477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11477 = true := by
  rw [show D2M8K2.u11477 = KTree.node D2M8K2.t11486 (nat_lit 24784699) (nat_lit 1454714567) (nat_lit 0) D2M8K2.t11487 from rfl, allE_node, rows11486, irow11477, rows11487]
  all_goals rfl

theorem atot11477 : totK PD2M8K2 D2M8K2.u11477 = [0, 0, 366770683519, 912106126754, 476427691988, 33989709050, 0, 0] := by
  rw [show D2M8K2.u11477 = KTree.node D2M8K2.t11486 (nat_lit 24784699) (nat_lit 1454714567) (nat_lit 0) D2M8K2.t11487 from rfl, totK_node, tot11486, tot11487]
  decide +kernel

theorem arows11482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11482 = true := by
  rw [show D2M8K2.u11482 = KTree.node D2M8K2.t11488 (nat_lit 24791375) (nat_lit 2155777725) (nat_lit 0) D2M8K2.t11489 from rfl, allE_node, rows11488, irow11482, rows11489]
  all_goals rfl

theorem atot11482 : totK PD2M8K2 D2M8K2.u11482 = [0, 0, 235351928068, 856054453924, 636224559226, 55883525344, 0, 0] := by
  rw [show D2M8K2.u11482 = KTree.node D2M8K2.t11488 (nat_lit 24791375) (nat_lit 2155777725) (nat_lit 0) D2M8K2.t11489 from rfl, totK_node, tot11488, tot11489]
  decide +kernel

theorem arows11483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11483 = true := by
  rw [show D2M8K2.u11483 = KTree.node D2M8K2.t11490 (nat_lit 24793392) (nat_lit 3496955729) (nat_lit 0) D2M8K2.t11491 from rfl, allE_node, rows11490, irow11483, rows11491]
  all_goals rfl

theorem atot11483 : totK PD2M8K2 D2M8K2.u11483 = [0, 0, 232910778978, 702313266877, 657901584754, 164879444323, 5352782441, 0] := by
  rw [show D2M8K2.u11483 = KTree.node D2M8K2.t11490 (nat_lit 24793392) (nat_lit 3496955729) (nat_lit 0) D2M8K2.t11491 from rfl, totK_node, tot11490, tot11491]
  decide +kernel

theorem arows11485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11485 = true := by
  rw [show D2M8K2.u11485 = KTree.node D2M8K2.t11492 (nat_lit 24794689) (nat_lit 1313752886) (nat_lit 0) D2M8K2.t11493 from rfl, allE_node, rows11492, irow11485, rows11493]
  all_goals rfl

theorem atot11485 : totK PD2M8K2 D2M8K2.u11485 = [0, 0, 178017608236, 868454062766, 672963537402, 52953394355, 0, 0] := by
  rw [show D2M8K2.u11485 = KTree.node D2M8K2.t11492 (nat_lit 24794689) (nat_lit 1313752886) (nat_lit 0) D2M8K2.t11493 from rfl, totK_node, tot11492, tot11493]
  decide +kernel

theorem arows11486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11486 = true := by
  rw [show D2M8K2.u11486 = KTree.node D2M8K2.t11494 (nat_lit 24797291) (nat_lit 2675393706) (nat_lit 0) D2M8K2.t11495 from rfl, allE_node, rows11494, irow11486, rows11495]
  all_goals rfl

theorem atot11486 : totK PD2M8K2 D2M8K2.u11486 = [0, 0, 318041175738, 819186175118, 562497200805, 83008900797, 1271866555, 0] := by
  rw [show D2M8K2.u11486 = KTree.node D2M8K2.t11494 (nat_lit 24797291) (nat_lit 2675393706) (nat_lit 0) D2M8K2.t11495 from rfl, totK_node, tot11494, tot11495]
  decide +kernel

theorem arows11489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11489 = true := by
  rw [show D2M8K2.u11489 = KTree.node D2M8K2.t11496 (nat_lit 24800882) (nat_lit 3807173899) (nat_lit 0) D2M8K2.t11497 from rfl, allE_node, rows11496, irow11489, rows11497]
  all_goals rfl

theorem atot11489 : totK PD2M8K2 D2M8K2.u11489 = [0, 318589914238, 789528734414, 513587114519, 155744001178, 11758933175, 0, 0] := by
  rw [show D2M8K2.u11489 = KTree.node D2M8K2.t11496 (nat_lit 24800882) (nat_lit 3807173899) (nat_lit 0) D2M8K2.t11497 from rfl, totK_node, tot11496, tot11497]
  decide +kernel

theorem arows11490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11490 = true := by
  rw [show D2M8K2.u11490 = KTree.node D2M8K2.t11498 (nat_lit 24802890) (nat_lit 3805544656) (nat_lit 0) D2M8K2.t11499 from rfl, allE_node, rows11498, irow11490, rows11499]
  all_goals rfl

theorem atot11490 : totK PD2M8K2 D2M8K2.u11490 = [0, 126010812522, 715245314140, 836972340001, 124893034783, 1209030869, 0, 0] := by
  rw [show D2M8K2.u11490 = KTree.node D2M8K2.t11498 (nat_lit 24802890) (nat_lit 3805544656) (nat_lit 0) D2M8K2.t11499 from rfl, totK_node, tot11498, tot11499]
  decide +kernel

theorem arows11492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11492 = true := by
  rw [show D2M8K2.u11492 = KTree.node D2M8K2.t11500 (nat_lit 24804894) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t11501 from rfl, allE_node, rows11500, irow11492, rows11501]
  all_goals rfl

theorem atot11492 : totK PD2M8K2 D2M8K2.u11492 = [0, 326054305919, 914942325388, 532881963517, 49565121694, 0, 0, 0] := by
  rw [show D2M8K2.u11492 = KTree.node D2M8K2.t11500 (nat_lit 24804894) (nat_lit 3869046296) (nat_lit 0) D2M8K2.t11501 from rfl, totK_node, tot11500, tot11501]
  decide +kernel

theorem arows11493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11493 = true := by
  rw [show D2M8K2.u11493 = KTree.node D2M8K2.t11502 (nat_lit 24806396) (nat_lit 3357507821) (nat_lit 0) D2M8K2.t11503 from rfl, allE_node, rows11502, irow11493, rows11503]
  all_goals rfl

theorem atot11493 : totK PD2M8K2 D2M8K2.u11493 = [0, 0, 372290935367, 945153459195, 459518289473, 30800671508, 0, 0] := by
  rw [show D2M8K2.u11493 = KTree.node D2M8K2.t11502 (nat_lit 24806396) (nat_lit 3357507821) (nat_lit 0) D2M8K2.t11503 from rfl, totK_node, tot11502, tot11503]
  decide +kernel

theorem arows11497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11497 = true := by
  rw [show D2M8K2.u11497 = KTree.node D2M8K2.t11504 (nat_lit 24807699) (nat_lit 3690519580) (nat_lit 0) D2M8K2.t11505 from rfl, allE_node, rows11504, irow11497, rows11505]
  all_goals rfl

theorem atot11497 : totK PD2M8K2 D2M8K2.u11497 = [0, 346154659613, 863928488146, 480816002224, 105794125797, 6690617053, 0, 0] := by
  rw [show D2M8K2.u11497 = KTree.node D2M8K2.t11504 (nat_lit 24807699) (nat_lit 3690519580) (nat_lit 0) D2M8K2.t11505 from rfl, totK_node, tot11504, tot11505]
  decide +kernel

theorem arows11498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11498 = true := by
  rw [show D2M8K2.u11498 = KTree.node D2M8K2.t11506 (nat_lit 24809280) (nat_lit 2510043472) (nat_lit 0) D2M8K2.t11507 from rfl, allE_node, rows11506, irow11498, rows11507]
  all_goals rfl

theorem atot11498 : totK PD2M8K2 D2M8K2.u11498 = [0, 67666276829, 534990385083, 887633245985, 260305090616, 10568566766, 0, 0] := by
  rw [show D2M8K2.u11498 = KTree.node D2M8K2.t11506 (nat_lit 24809280) (nat_lit 2510043472) (nat_lit 0) D2M8K2.t11507 from rfl, totK_node, tot11506, tot11507]
  decide +kernel

theorem arows11500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11500 = true := by
  rw [show D2M8K2.u11500 = KTree.node D2M8K2.t11508 (nat_lit 24811114) (nat_lit 3345831298) (nat_lit 0) D2M8K2.t11509 from rfl, allE_node, rows11508, irow11500, rows11509]
  all_goals rfl

theorem atot11500 : totK PD2M8K2 D2M8K2.u11500 = [0, 346306473296, 880810616615, 513679168057, 69697093013, 2481160468, 0, 0] := by
  rw [show D2M8K2.u11500 = KTree.node D2M8K2.t11508 (nat_lit 24811114) (nat_lit 3345831298) (nat_lit 0) D2M8K2.t11509 from rfl, totK_node, tot11508, tot11509]
  decide +kernel

theorem arows11501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11501 = true := by
  rw [show D2M8K2.u11501 = KTree.node D2M8K2.t11510 (nat_lit 24812692) (nat_lit 3866928256) (nat_lit 0) D2M8K2.t11511 from rfl, allE_node, rows11510, irow11501, rows11511]
  all_goals rfl

theorem atot11501 : totK PD2M8K2 D2M8K2.u11501 = [0, 67740584699, 587884571169, 863055248875, 240536840336, 10680993762, 0, 0] := by
  rw [show D2M8K2.u11501 = KTree.node D2M8K2.t11510 (nat_lit 24812692) (nat_lit 3866928256) (nat_lit 0) D2M8K2.t11511 from rfl, totK_node, tot11510, tot11511]
  decide +kernel

theorem arows11504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11504 = true := by
  rw [show D2M8K2.u11504 = KTree.node D2M8K2.t11512 (nat_lit 24814492) (nat_lit 3730996958) (nat_lit 0) D2M8K2.t11513 from rfl, allE_node, rows11512, irow11504, rows11513]
  all_goals rfl

theorem atot11504 : totK PD2M8K2 D2M8K2.u11504 = [0, 332816055673, 838927100295, 545855731006, 97003169289, 2569691499, 0, 0] := by
  rw [show D2M8K2.u11504 = KTree.node D2M8K2.t11512 (nat_lit 24814492) (nat_lit 3730996958) (nat_lit 0) D2M8K2.t11513 from rfl, totK_node, tot11512, tot11513]
  decide +kernel

theorem arows11505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11505 = true := by
  rw [show D2M8K2.u11505 = KTree.node D2M8K2.t11514 (nat_lit 24815957) (nat_lit 2027660470) (nat_lit 0) D2M8K2.t11515 from rfl, allE_node, rows11514, irow11505, rows11515]
  all_goals rfl

theorem atot11505 : totK PD2M8K2 D2M8K2.u11505 = [0, 106852402812, 727177468494, 847600469627, 127941333980, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11505 = KTree.node D2M8K2.t11514 (nat_lit 24815957) (nat_lit 2027660470) (nat_lit 0) D2M8K2.t11515 from rfl, totK_node, tot11514, tot11515]
  decide +kernel

theorem arows11507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11507 = true := by
  rw [show D2M8K2.u11507 = KTree.node D2M8K2.t11516 (nat_lit 24821677) (nat_lit 1121151367) (nat_lit 0) D2M8K2.t11517 from rfl, allE_node, rows11516, irow11507, rows11517]
  all_goals rfl

theorem atot11507 : totK PD2M8K2 D2M8K2.u11507 = [0, 0, 394614336768, 991330736027, 351130262454, 8673785509, 0, 0] := by
  rw [show D2M8K2.u11507 = KTree.node D2M8K2.t11516 (nat_lit 24821677) (nat_lit 1121151367) (nat_lit 0) D2M8K2.t11517 from rfl, totK_node, tot11516, tot11517]
  decide +kernel

theorem arows11508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11508 = true := by
  rw [show D2M8K2.u11508 = KTree.node D2M8K2.t11518 (nat_lit 24825233) (nat_lit 2157008697) (nat_lit 0) D2M8K2.t11519 from rfl, allE_node, rows11518, irow11508, rows11519]
  all_goals rfl

theorem atot11508 : totK PD2M8K2 D2M8K2.u11508 = [0, 0, 356548500562, 940161694999, 480762532880, 35829827450, 0, 0] := by
  rw [show D2M8K2.u11508 = KTree.node D2M8K2.t11518 (nat_lit 24825233) (nat_lit 2157008697) (nat_lit 0) D2M8K2.t11519 from rfl, totK_node, tot11518, tot11519]
  decide +kernel

theorem arows11516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11516 = true := by
  rw [show D2M8K2.u11516 = KTree.node D2M8K2.t11520 (nat_lit 24828294) (nat_lit 3519212062) (nat_lit 0) D2M8K2.t11521 from rfl, allE_node, rows11520, irow11516, rows11521]
  all_goals rfl

theorem atot11516 : totK PD2M8K2 D2M8K2.u11516 = [0, 0, 399754090417, 929425125953, 439491640948, 26397804287, 0, 0] := by
  rw [show D2M8K2.u11516 = KTree.node D2M8K2.t11520 (nat_lit 24828294) (nat_lit 3519212062) (nat_lit 0) D2M8K2.t11521 from rfl, totK_node, tot11520, tot11521]
  decide +kernel

theorem arows11517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11517 = true := by
  rw [show D2M8K2.u11517 = KTree.node D2M8K2.t11522 (nat_lit 24831626) (nat_lit 2698750787) (nat_lit 0) D2M8K2.t11523 from rfl, allE_node, rows11522, irow11517, rows11523]
  all_goals rfl

theorem atot11517 : totK PD2M8K2 D2M8K2.u11517 = [0, 0, 344463322798, 949279154926, 467827592156, 24807239199, 0, 0] := by
  rw [show D2M8K2.u11517 = KTree.node D2M8K2.t11522 (nat_lit 24831626) (nat_lit 2698750787) (nat_lit 0) D2M8K2.t11523 from rfl, totK_node, tot11522, tot11523]
  decide +kernel

theorem arows11519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11519 = true := by
  rw [show D2M8K2.u11519 = KTree.node D2M8K2.t11524 (nat_lit 24834920) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t11525 from rfl, allE_node, rows11524, irow11519, rows11525]
  all_goals rfl

theorem atot11519 : totK PD2M8K2 D2M8K2.u11519 = [0, 0, 414123202128, 962719146663, 408514387394, 21038541225, 0, 0] := by
  rw [show D2M8K2.u11519 = KTree.node D2M8K2.t11524 (nat_lit 24834920) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t11525 from rfl, totK_node, tot11524, tot11525]
  decide +kernel

theorem arows11520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11520 = true := by
  rw [show D2M8K2.u11520 = KTree.node D2M8K2.t11526 (nat_lit 24836119) (nat_lit 2216481971) (nat_lit 0) D2M8K2.t11527 from rfl, allE_node, rows11526, irow11520, rows11527]
  all_goals rfl

theorem atot11520 : totK PD2M8K2 D2M8K2.u11520 = [0, 0, 179858698636, 828933872130, 674246387687, 67652456505, 0, 0] := by
  rw [show D2M8K2.u11520 = KTree.node D2M8K2.t11526 (nat_lit 24836119) (nat_lit 2216481971) (nat_lit 0) D2M8K2.t11527 from rfl, totK_node, tot11526, tot11527]
  decide +kernel

theorem arows11523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11523 = true := by
  rw [show D2M8K2.u11523 = KTree.node D2M8K2.t11528 (nat_lit 24845702) (nat_lit 3911505399) (nat_lit 0) D2M8K2.t11529 from rfl, allE_node, rows11528, irow11523, rows11529]
  all_goals rfl

theorem atot11523 : totK PD2M8K2 D2M8K2.u11523 = [0, 267389991301, 652708496477, 501755052287, 312962040580, 84897210332, 1429815836, 0] := by
  rw [show D2M8K2.u11523 = KTree.node D2M8K2.t11528 (nat_lit 24845702) (nat_lit 3911505399) (nat_lit 0) D2M8K2.t11529 from rfl, totK_node, tot11528, tot11529]
  decide +kernel

theorem arows11524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11524 = true := by
  rw [show D2M8K2.u11524 = KTree.node D2M8K2.t11530 (nat_lit 24847234) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t11531 from rfl, allE_node, rows11530, irow11524, rows11531]
  all_goals rfl

theorem atot11524 : totK PD2M8K2 D2M8K2.u11524 = [0, 162612680181, 636492823908, 711499914583, 277885911618, 25316940874, 0, 0] := by
  rw [show D2M8K2.u11524 = KTree.node D2M8K2.t11530 (nat_lit 24847234) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t11531 from rfl, totK_node, tot11530, tot11531]
  decide +kernel

theorem arows11526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11526 = true := by
  rw [show D2M8K2.u11526 = KTree.node D2M8K2.t11532 (nat_lit 24848434) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t11533 from rfl, allE_node, rows11532, irow11526, rows11533]
  all_goals rfl

theorem atot11526 : totK PD2M8K2 D2M8K2.u11526 = [0, 156085019224, 588947218706, 761239563473, 297941434607, 12163764758, 0, 0] := by
  rw [show D2M8K2.u11526 = KTree.node D2M8K2.t11532 (nat_lit 24848434) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t11533 from rfl, totK_node, tot11532, tot11533]
  decide +kernel

theorem arows11527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11527 = true := by
  rw [show D2M8K2.u11527 = KTree.node D2M8K2.t11534 (nat_lit 24850039) (nat_lit 1754071807) (nat_lit 0) D2M8K2.t11535 from rfl, allE_node, rows11534, irow11527, rows11535]
  all_goals rfl

theorem atot11527 : totK PD2M8K2 D2M8K2.u11527 = [0, 247374302558, 795536433563, 655087799647, 105317335774, 1129969115, 0, 0] := by
  rw [show D2M8K2.u11527 = KTree.node D2M8K2.t11534 (nat_lit 24850039) (nat_lit 1754071807) (nat_lit 0) D2M8K2.t11535 from rfl, totK_node, tot11534, tot11535]
  decide +kernel

theorem arows11531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11531 = true := by
  rw [show D2M8K2.u11531 = KTree.node D2M8K2.t11536 (nat_lit 24851824) (nat_lit 3292011200) (nat_lit 0) D2M8K2.t11537 from rfl, allE_node, rows11536, irow11531, rows11537]
  all_goals rfl

theorem atot11531 : totK PD2M8K2 D2M8K2.u11531 = [0, 156180567191, 654119508252, 775026493319, 211955629141, 7938575017, 0, 0] := by
  rw [show D2M8K2.u11531 = KTree.node D2M8K2.t11536 (nat_lit 24851824) (nat_lit 3292011200) (nat_lit 0) D2M8K2.t11537 from rfl, totK_node, tot11536, tot11537]
  decide +kernel

theorem arows11532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11532 = true := by
  rw [show D2M8K2.u11532 = KTree.node D2M8K2.t11538 (nat_lit 24853548) (nat_lit 3556071319) (nat_lit 0) D2M8K2.t11539 from rfl, allE_node, rows11538, irow11532, rows11539]
  all_goals rfl

theorem atot11532 : totK PD2M8K2 D2M8K2.u11532 = [0, 247537208781, 802250846906, 648937577075, 105575155849, 1162515529, 0, 0] := by
  rw [show D2M8K2.u11532 = KTree.node D2M8K2.t11538 (nat_lit 24853548) (nat_lit 3556071319) (nat_lit 0) D2M8K2.t11539 from rfl, totK_node, tot11538, tot11539]
  decide +kernel

theorem arows11534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11534 = true := by
  rw [show D2M8K2.u11534 = KTree.node D2M8K2.t11540 (nat_lit 24855305) (nat_lit 1302412910) (nat_lit 0) D2M8K2.t11541 from rfl, allE_node, rows11540, irow11534, rows11541]
  all_goals rfl

theorem atot11534 : totK PD2M8K2 D2M8K2.u11534 = [0, 162235715068, 657304609798, 770671308310, 216893910257, 8017271805, 0, 0] := by
  rw [show D2M8K2.u11534 = KTree.node D2M8K2.t11540 (nat_lit 24855305) (nat_lit 1302412910) (nat_lit 0) D2M8K2.t11541 from rfl, totK_node, tot11540, tot11541]
  decide +kernel

theorem arows11535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11535 = true := by
  rw [show D2M8K2.u11535 = KTree.node D2M8K2.t11542 (nat_lit 24860124) (nat_lit 2240188791) (nat_lit 0) D2M8K2.t11543 from rfl, allE_node, rows11542, irow11535, rows11543]
  all_goals rfl

theorem atot11535 : totK PD2M8K2 D2M8K2.u11535 = [0, 266785258205, 797933570815, 632798550545, 107576054164, 1249641317, 0, 0] := by
  rw [show D2M8K2.u11535 = KTree.node D2M8K2.t11542 (nat_lit 24860124) (nat_lit 2240188791) (nat_lit 0) D2M8K2.t11543 from rfl, totK_node, tot11542, tot11543]
  decide +kernel

theorem arows11538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11538 = true := by
  rw [show D2M8K2.u11538 = KTree.node D2M8K2.t11544 (nat_lit 24861778) (nat_lit 3876954289) (nat_lit 0) D2M8K2.t11545 from rfl, allE_node, rows11544, irow11538, rows11545]
  all_goals rfl

theorem atot11538 : totK PD2M8K2 D2M8K2.u11538 = [0, 0, 425728039297, 951251007635, 388605587419, 31171451738, 0, 0] := by
  rw [show D2M8K2.u11538 = KTree.node D2M8K2.t11544 (nat_lit 24861778) (nat_lit 3876954289) (nat_lit 0) D2M8K2.t11545 from rfl, totK_node, tot11544, tot11545]
  decide +kernel

theorem arows11539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11539 = true := by
  rw [show D2M8K2.u11539 = KTree.node D2M8K2.t11546 (nat_lit 24867000) (nat_lit 3116453103) (nat_lit 0) D2M8K2.t11547 from rfl, allE_node, rows11546, irow11539, rows11547]
  all_goals rfl

theorem atot11539 : totK PD2M8K2 D2M8K2.u11539 = [0, 0, 331849690950, 907723083410, 532117424931, 31512871554, 0, 0] := by
  rw [show D2M8K2.u11539 = KTree.node D2M8K2.t11546 (nat_lit 24867000) (nat_lit 3116453103) (nat_lit 0) D2M8K2.t11547 from rfl, totK_node, tot11546, tot11547]
  decide +kernel

theorem arows11541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11541 = true := by
  rw [show D2M8K2.u11541 = KTree.node D2M8K2.t11548 (nat_lit 24870013) (nat_lit 1223849724) (nat_lit 0) D2M8K2.t11549 from rfl, allE_node, rows11548, irow11541, rows11549]
  all_goals rfl

theorem atot11541 : totK PD2M8K2 D2M8K2.u11541 = [0, 0, 400052871575, 921850941515, 447562861671, 32628958346, 0, 0] := by
  rw [show D2M8K2.u11541 = KTree.node D2M8K2.t11548 (nat_lit 24870013) (nat_lit 1223849724) (nat_lit 0) D2M8K2.t11549 from rfl, totK_node, tot11548, tot11549]
  decide +kernel

theorem arows11542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11542 = true := by
  rw [show D2M8K2.u11542 = KTree.node D2M8K2.t11550 (nat_lit 24872284) (nat_lit 3682890661) (nat_lit 0) D2M8K2.t11551 from rfl, allE_node, rows11550, irow11542, rows11551]
  all_goals rfl

theorem atot11542 : totK PD2M8K2 D2M8K2.u11542 = [0, 0, 155062923995, 756440614438, 767514568249, 108954946646, 1323630408, 0] := by
  rw [show D2M8K2.u11542 = KTree.node D2M8K2.t11550 (nat_lit 24872284) (nat_lit 3682890661) (nat_lit 0) D2M8K2.t11551 from rfl, totK_node, tot11550, tot11551]
  decide +kernel

theorem arows11547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11547 = true := by
  rw [show D2M8K2.u11547 = KTree.node D2M8K2.t11552 (nat_lit 24874227) (nat_lit 2510919269) (nat_lit 0) D2M8K2.t11553 from rfl, allE_node, rows11552, irow11547, rows11553]
  all_goals rfl

theorem atot11547 : totK PD2M8K2 D2M8K2.u11547 = [0, 0, 245252665714, 854251279209, 646646780152, 51921350803, 0, 0] := by
  rw [show D2M8K2.u11547 = KTree.node D2M8K2.t11552 (nat_lit 24874227) (nat_lit 2510919269) (nat_lit 0) D2M8K2.t11553 from rfl, totK_node, tot11552, tot11553]
  decide +kernel

theorem arows11548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11548 = true := by
  rw [show D2M8K2.u11548 = KTree.node D2M8K2.t11554 (nat_lit 24879940) (nat_lit 3948762570) (nat_lit 0) D2M8K2.t11555 from rfl, allE_node, rows11554, irow11548, rows11555]
  all_goals rfl

theorem atot11548 : totK PD2M8K2 D2M8K2.u11548 = [0, 0, 245252845207, 794890752374, 643625966692, 102887369256, 1332468113, 0] := by
  rw [show D2M8K2.u11548 = KTree.node D2M8K2.t11554 (nat_lit 24879940) (nat_lit 3948762570) (nat_lit 0) D2M8K2.t11555 from rfl, totK_node, tot11554, tot11555]
  decide +kernel

theorem arows11550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11550 = true := by
  rw [show D2M8K2.u11550 = KTree.node D2M8K2.t11556 (nat_lit 24881409) (nat_lit 1304199793) (nat_lit 0) D2M8K2.t11557 from rfl, allE_node, rows11556, irow11550, rows11557]
  all_goals rfl

theorem atot11550 : totK PD2M8K2 D2M8K2.u11550 = [0, 0, 178176977009, 753122968735, 741052025804, 104270180707, 1229550402, 0] := by
  rw [show D2M8K2.u11550 = KTree.node D2M8K2.t11556 (nat_lit 24881409) (nat_lit 1304199793) (nat_lit 0) D2M8K2.t11557 from rfl, totK_node, tot11556, tot11557]
  decide +kernel

theorem arows11551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11551 = true := by
  rw [show D2M8K2.u11551 = KTree.node D2M8K2.t11558 (nat_lit 24883302) (nat_lit 3747886277) (nat_lit 0) D2M8K2.t11559 from rfl, allE_node, rows11558, irow11551, rows11559]
  all_goals rfl

theorem atot11551 : totK PD2M8K2 D2M8K2.u11551 = [261533257835, 580991266440, 221015946110, 153445768585, 393497652979, 169144195257, 8304201444, 0] := by
  rw [show D2M8K2.u11551 = KTree.node D2M8K2.t11558 (nat_lit 24883302) (nat_lit 3747886277) (nat_lit 0) D2M8K2.t11559 from rfl, totK_node, tot11558, tot11559]
  decide +kernel

theorem arows11554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11554 = true := by
  rw [show D2M8K2.u11554 = KTree.node D2M8K2.t11560 (nat_lit 24884814) (nat_lit 2541617095) (nat_lit 0) D2M8K2.t11561 from rfl, allE_node, rows11560, irow11554, rows11561]
  all_goals rfl

theorem atot11554 : totK PD2M8K2 D2M8K2.u11554 = [171611975712, 742523790524, 747436662428, 123577020815, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11554 = KTree.node D2M8K2.t11560 (nat_lit 24884814) (nat_lit 2541617095) (nat_lit 0) D2M8K2.t11561 from rfl, totK_node, tot11560, tot11561]
  decide +kernel

theorem arows11555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11555 = true := by
  rw [show D2M8K2.u11555 = KTree.node D2M8K2.t11562 (nat_lit 24890337) (nat_lit 1699295928) (nat_lit 0) D2M8K2.t11563 from rfl, allE_node, rows11562, irow11555, rows11563]
  all_goals rfl

theorem atot11555 : totK PD2M8K2 D2M8K2.u11555 = [252442151127, 833958389857, 652740891999, 71469276087, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11555 = KTree.node D2M8K2.t11562 (nat_lit 24890337) (nat_lit 1699295928) (nat_lit 0) D2M8K2.t11563 from rfl, totK_node, tot11562, tot11563]
  decide +kernel

theorem arows11557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11557 = true := by
  rw [show D2M8K2.u11557 = KTree.node D2M8K2.t11564 (nat_lit 24891846) (nat_lit 3499009848) (nat_lit 0) D2M8K2.t11565 from rfl, allE_node, rows11564, irow11557, rows11565]
  all_goals rfl

theorem atot11557 : totK PD2M8K2 D2M8K2.u11557 = [170926481118, 698163725390, 759825074943, 160110034229, 2309606161, 0, 0, 0] := by
  rw [show D2M8K2.u11557 = KTree.node D2M8K2.t11564 (nat_lit 24891846) (nat_lit 3499009848) (nat_lit 0) D2M8K2.t11565 from rfl, totK_node, tot11564, tot11565]
  decide +kernel

theorem arows11558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11558 = true := by
  rw [show D2M8K2.u11558 = KTree.node D2M8K2.t11566 (nat_lit 24893676) (nat_lit 3199526130) (nat_lit 0) D2M8K2.t11567 from rfl, allE_node, rows11566, irow11558, rows11567]
  all_goals rfl

theorem atot11558 : totK PD2M8K2 D2M8K2.u11558 = [256468330477, 746666742249, 604827576440, 156229668997, 10740121073, 0, 0, 0] := by
  rw [show D2M8K2.u11558 = KTree.node D2M8K2.t11566 (nat_lit 24893676) (nat_lit 3199526130) (nat_lit 0) D2M8K2.t11567 from rfl, totK_node, tot11566, tot11567]
  decide +kernel

theorem arows11562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11562 = true := by
  rw [show D2M8K2.u11562 = KTree.node D2M8K2.t11568 (nat_lit 24896161) (nat_lit 1549666246) (nat_lit 0) D2M8K2.t11569 from rfl, allE_node, rows11568, irow11562, rows11569]
  all_goals rfl

theorem atot11562 : totK PD2M8K2 D2M8K2.u11562 = [68430962919, 534811732308, 862450277076, 272341252375, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u11562 = KTree.node D2M8K2.t11568 (nat_lit 24896161) (nat_lit 1549666246) (nat_lit 0) D2M8K2.t11569 from rfl, totK_node, tot11568, tot11569]
  decide +kernel

theorem arows11563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11563 = true := by
  rw [show D2M8K2.u11563 = KTree.node D2M8K2.t11570 (nat_lit 24897611) (nat_lit 2722176732) (nat_lit 0) D2M8K2.t11571 from rfl, allE_node, rows11570, irow11563, rows11571]
  all_goals rfl

theorem atot11563 : totK PD2M8K2 D2M8K2.u11563 = [356378868046, 901738224913, 501983394365, 48089253488, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11563 = KTree.node D2M8K2.t11570 (nat_lit 24897611) (nat_lit 2722176732) (nat_lit 0) D2M8K2.t11571 from rfl, totK_node, tot11570, tot11571]
  decide +kernel

theorem arows11565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11565 = true := by
  rw [show D2M8K2.u11565 = KTree.node D2M8K2.t11572 (nat_lit 24899335) (nat_lit 1998664270) (nat_lit 0) D2M8K2.t11573 from rfl, allE_node, rows11572, irow11565, rows11573]
  all_goals rfl

theorem atot11565 : totK PD2M8K2 D2M8K2.u11565 = [77505186634, 616838139030, 885832757929, 204304122614, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u11565 = KTree.node D2M8K2.t11572 (nat_lit 24899335) (nat_lit 1998664270) (nat_lit 0) D2M8K2.t11573 from rfl, totK_node, tot11572, tot11573]
  decide +kernel

theorem arows11566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11566 = true := by
  rw [show D2M8K2.u11566 = KTree.node D2M8K2.t11574 (nat_lit 24901201) (nat_lit 1526200743) (nat_lit 0) D2M8K2.t11575 from rfl, allE_node, rows11574, irow11566, rows11575]
  all_goals rfl

theorem atot11566 : totK PD2M8K2 D2M8K2.u11566 = [357252159725, 917435247932, 482988597497, 39592826251, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11566 = KTree.node D2M8K2.t11574 (nat_lit 24901201) (nat_lit 1526200743) (nat_lit 0) D2M8K2.t11575 from rfl, totK_node, tot11574, tot11575]
  decide +kernel

theorem arows11569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11569 = true := by
  rw [show D2M8K2.u11569 = KTree.node D2M8K2.t11576 (nat_lit 24902937) (nat_lit 1166317325) (nat_lit 0) D2M8K2.t11577 from rfl, allE_node, rows11576, irow11569, rows11577]
  all_goals rfl

theorem atot11569 : totK PD2M8K2 D2M8K2.u11569 = [0, 412898834581, 951030327464, 372633675310, 14971720341, 0, 0, 0] := by
  rw [show D2M8K2.u11569 = KTree.node D2M8K2.t11576 (nat_lit 24902937) (nat_lit 1166317325) (nat_lit 0) D2M8K2.t11577 from rfl, totK_node, tot11576, tot11577]
  decide +kernel

theorem arows11570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11570 = true := by
  rw [show D2M8K2.u11570 = KTree.node D2M8K2.t11578 (nat_lit 24904813) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t11579 from rfl, allE_node, rows11578, irow11570, rows11579]
  all_goals rfl

theorem atot11570 : totK PD2M8K2 D2M8K2.u11570 = [0, 388772197013, 926950881778, 413716564115, 28894120029, 0, 0, 0] := by
  rw [show D2M8K2.u11570 = KTree.node D2M8K2.t11578 (nat_lit 24904813) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t11579 from rfl, totK_node, tot11578, tot11579]
  decide +kernel

theorem arows11572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11572 = true := by
  rw [show D2M8K2.u11572 = KTree.node D2M8K2.t11580 (nat_lit 24906352) (nat_lit 3231563751) (nat_lit 0) D2M8K2.t11581 from rfl, allE_node, rows11580, irow11572, rows11581]
  all_goals rfl

theorem atot11572 : totK PD2M8K2 D2M8K2.u11572 = [0, 118648469823, 689713394993, 777228477007, 142668472581, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11572 = KTree.node D2M8K2.t11580 (nat_lit 24906352) (nat_lit 3231563751) (nat_lit 0) D2M8K2.t11581 from rfl, totK_node, tot11580, tot11581]
  decide +kernel

theorem arows11573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11573 = true := by
  rw [show D2M8K2.u11573 = KTree.node D2M8K2.t11582 (nat_lit 24911627) (nat_lit 2406172620) (nat_lit 0) D2M8K2.t11583 from rfl, allE_node, rows11582, irow11573, rows11583]
  all_goals rfl

theorem atot11573 : totK PD2M8K2 D2M8K2.u11573 = [0, 342671193301, 946368509469, 463129168613, 21551083610, 0, 0, 0] := by
  rw [show D2M8K2.u11573 = KTree.node D2M8K2.t11582 (nat_lit 24911627) (nat_lit 2406172620) (nat_lit 0) D2M8K2.t11583 from rfl, totK_node, tot11582, tot11583]
  decide +kernel

theorem arows11579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11579 = true := by
  rw [show D2M8K2.u11579 = KTree.node D2M8K2.t11584 (nat_lit 24915468) (nat_lit 3547735429) (nat_lit 0) D2M8K2.t11585 from rfl, allE_node, rows11584, irow11579, rows11585]
  all_goals rfl

theorem atot11579 : totK PD2M8K2 D2M8K2.u11579 = [0, 396127242630, 933917170429, 425699453652, 27462474765, 0, 0, 0] := by
  rw [show D2M8K2.u11579 = KTree.node D2M8K2.t11584 (nat_lit 24915468) (nat_lit 3547735429) (nat_lit 0) D2M8K2.t11585 from rfl, totK_node, tot11584, tot11585]
  decide +kernel

theorem arows11580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11580 = true := by
  rw [show D2M8K2.u11580 = KTree.node D2M8K2.t11586 (nat_lit 24918578) (nat_lit 3785708774) (nat_lit 0) D2M8K2.t11587 from rfl, allE_node, rows11586, irow11580, rows11587]
  all_goals rfl

theorem atot11580 : totK PD2M8K2 D2M8K2.u11580 = [0, 342461502153, 944706740809, 459883863004, 23530630971, 0, 0, 0] := by
  rw [show D2M8K2.u11580 = KTree.node D2M8K2.t11586 (nat_lit 24918578) (nat_lit 3785708774) (nat_lit 0) D2M8K2.t11587 from rfl, totK_node, tot11586, tot11587]
  decide +kernel

theorem arows11582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11582 = true := by
  rw [show D2M8K2.u11582 = KTree.node D2M8K2.t11588 (nat_lit 24921931) (nat_lit 1478189921) (nat_lit 0) D2M8K2.t11589 from rfl, allE_node, rows11588, irow11582, rows11589]
  all_goals rfl

theorem atot11582 : totK PD2M8K2 D2M8K2.u11582 = [0, 374516506599, 953972935472, 440576987018, 18692006533, 0, 0, 0] := by
  rw [show D2M8K2.u11582 = KTree.node D2M8K2.t11588 (nat_lit 24921931) (nat_lit 1478189921) (nat_lit 0) D2M8K2.t11589 from rfl, totK_node, tot11588, tot11589]
  decide +kernel

theorem arows11583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11583 = true := by
  rw [show D2M8K2.u11583 = KTree.node D2M8K2.t11590 (nat_lit 24928901) (nat_lit 2382857609) (nat_lit 0) D2M8K2.t11591 from rfl, allE_node, rows11590, irow11583, rows11591]
  all_goals rfl

theorem atot11583 : totK PD2M8K2 D2M8K2.u11583 = [355056847956, 903867846508, 498057168658, 77886831646, 9677292770, 0, 0, 0] := by
  rw [show D2M8K2.u11583 = KTree.node D2M8K2.t11590 (nat_lit 24928901) (nat_lit 2382857609) (nat_lit 0) D2M8K2.t11591 from rfl, totK_node, tot11590, tot11591]
  decide +kernel

theorem arows11586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11586 = true := by
  rw [show D2M8K2.u11586 = KTree.node D2M8K2.t11592 (nat_lit 24930384) (nat_lit 2256440345) (nat_lit 0) D2M8K2.t11593 from rfl, allE_node, rows11592, irow11586, rows11593]
  all_goals rfl

theorem atot11586 : totK PD2M8K2 D2M8K2.u11586 = [87489192441, 499530184244, 829912435792, 374239200638, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u11586 = KTree.node D2M8K2.t11592 (nat_lit 24930384) (nat_lit 2256440345) (nat_lit 0) D2M8K2.t11593 from rfl, totK_node, tot11592, tot11593]
  decide +kernel

theorem arows11587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11587 = true := by
  rw [show D2M8K2.u11587 = KTree.node D2M8K2.t11594 (nat_lit 24931646) (nat_lit 3262056161) (nat_lit 0) D2M8K2.t11595 from rfl, allE_node, rows11594, irow11587, rows11595]
  all_goals rfl

theorem atot11587 : totK PD2M8K2 D2M8K2.u11587 = [227911934454, 680274311216, 692421680369, 220519497712, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u11587 = KTree.node D2M8K2.t11594 (nat_lit 24931646) (nat_lit 3262056161) (nat_lit 0) D2M8K2.t11595 from rfl, totK_node, tot11594, tot11595]
  decide +kernel

theorem arows11589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11589 = true := by
  rw [show D2M8K2.u11589 = KTree.node D2M8K2.t11596 (nat_lit 24933150) (nat_lit 3700650081) (nat_lit 0) D2M8K2.t11597 from rfl, allE_node, rows11596, irow11589, rows11597]
  all_goals rfl

theorem atot11589 : totK PD2M8K2 D2M8K2.u11589 = [194208477335, 777177913071, 706881596550, 114879386822, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u11589 = KTree.node D2M8K2.t11596 (nat_lit 24933150) (nat_lit 3700650081) (nat_lit 0) D2M8K2.t11597 from rfl, totK_node, tot11596, tot11597]
  decide +kernel

theorem arows11590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11590 = true := by
  rw [show D2M8K2.u11590 = KTree.node D2M8K2.t11598 (nat_lit 24934830) (nat_lit 3232171685) (nat_lit 0) D2M8K2.t11599 from rfl, allE_node, rows11598, irow11590, rows11599]
  all_goals rfl

theorem atot11590 : totK PD2M8K2 D2M8K2.u11590 = [177968616047, 650374626800, 750526220944, 220590812649, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u11590 = KTree.node D2M8K2.t11598 (nat_lit 24934830) (nat_lit 3232171685) (nat_lit 0) D2M8K2.t11599 from rfl, totK_node, tot11598, tot11599]
  decide +kernel

theorem arows11594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11594 = true := by
  rw [show D2M8K2.u11594 = KTree.node D2M8K2.t11600 (nat_lit 24937098) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t11601 from rfl, allE_node, rows11600, irow11594, rows11601]
  all_goals rfl

theorem atot11594 : totK PD2M8K2 D2M8K2.u11594 = [153457411749, 691415333047, 766627905726, 192864193764, 9443594156, 0, 0, 0] := by
  rw [show D2M8K2.u11594 = KTree.node D2M8K2.t11600 (nat_lit 24937098) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t11601 from rfl, totK_node, tot11600, tot11601]
  decide +kernel

theorem arows11595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11595 = true := by
  rw [show D2M8K2.u11595 = KTree.node D2M8K2.t11602 (nat_lit 24938968) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t11603 from rfl, allE_node, rows11602, irow11595, rows11603]
  all_goals rfl

theorem atot11595 : totK PD2M8K2 D2M8K2.u11595 = [323315828539, 839205711405, 559979139409, 96347248552, 2556887798, 0, 0, 0] := by
  rw [show D2M8K2.u11595 = KTree.node D2M8K2.t11602 (nat_lit 24938968) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t11603 from rfl, totK_node, tot11602, tot11603]
  decide +kernel

theorem arows11597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11597 = true := by
  rw [show D2M8K2.u11597 = KTree.node D2M8K2.t11604 (nat_lit 24940553) (nat_lit 1788976002) (nat_lit 0) D2M8K2.t11605 from rfl, allE_node, rows11604, irow11597, rows11605]
  all_goals rfl

theorem atot11597 : totK PD2M8K2 D2M8K2.u11597 = [90950819051, 703254481886, 877080568836, 144630664382, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u11597 = KTree.node D2M8K2.t11604 (nat_lit 24940553) (nat_lit 1788976002) (nat_lit 0) D2M8K2.t11605 from rfl, totK_node, tot11604, tot11605]
  decide +kernel

theorem arows11598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11598 = true := by
  rw [show D2M8K2.u11598 = KTree.node D2M8K2.t11606 (nat_lit 24942529) (nat_lit 1524998021) (nat_lit 0) D2M8K2.t11607 from rfl, allE_node, rows11606, irow11598, rows11607]
  all_goals rfl

theorem atot11598 : totK PD2M8K2 D2M8K2.u11598 = [350112410335, 846490637788, 521175770102, 104594608962, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u11598 = KTree.node D2M8K2.t11606 (nat_lit 24942529) (nat_lit 1524998021) (nat_lit 0) D2M8K2.t11607 from rfl, totK_node, tot11606, tot11607]
  decide +kernel

theorem arows11601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11601 = true := by
  rw [show D2M8K2.u11601 = KTree.node D2M8K2.t11608 (nat_lit 24944296) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t11609 from rfl, allE_node, rows11608, irow11601, rows11609]
  all_goals rfl

theorem atot11601 : totK PD2M8K2 D2M8K2.u11601 = [36951561255, 537463403825, 937323856535, 274789965160, 7559198010, 0, 0, 0] := by
  rw [show D2M8K2.u11601 = KTree.node D2M8K2.t11608 (nat_lit 24944296) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t11609 from rfl, totK_node, tot11608, tot11609]
  decide +kernel

theorem arows11602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11602 = true := by
  rw [show D2M8K2.u11602 = KTree.node D2M8K2.t11610 (nat_lit 24949563) (nat_lit 3642318905) (nat_lit 0) D2M8K2.t11611 from rfl, allE_node, rows11610, irow11602, rows11611]
  all_goals rfl

theorem atot11602 : totK PD2M8K2 D2M8K2.u11602 = [0, 354207273945, 904947205002, 524548957491, 48199927199, 0, 0, 0] := by
  rw [show D2M8K2.u11602 = KTree.node D2M8K2.t11610 (nat_lit 24949563) (nat_lit 3642318905) (nat_lit 0) D2M8K2.t11611 from rfl, totK_node, tot11610, tot11611]
  decide +kernel

theorem arows11604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11604 = true := by
  rw [show D2M8K2.u11604 = KTree.node D2M8K2.t11612 (nat_lit 24951067) (nat_lit 1698073983) (nat_lit 0) D2M8K2.t11613 from rfl, allE_node, rows11612, irow11604, rows11613]
  all_goals rfl

theorem atot11604 : totK PD2M8K2 D2M8K2.u11604 = [0, 87270580140, 561434682981, 828942950650, 310406645010, 25191558099, 0, 0] := by
  rw [show D2M8K2.u11604 = KTree.node D2M8K2.t11612 (nat_lit 24951067) (nat_lit 1698073983) (nat_lit 0) D2M8K2.t11613 from rfl, totK_node, tot11612, tot11613]
  decide +kernel

theorem arows11605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11605 = true := by
  rw [show D2M8K2.u11605 = KTree.node D2M8K2.t11614 (nat_lit 24952318) (nat_lit 3749681712) (nat_lit 0) D2M8K2.t11615 from rfl, allE_node, rows11614, irow11605, rows11615]
  all_goals rfl

theorem atot11605 : totK PD2M8K2 D2M8K2.u11605 = [0, 196318172781, 630957288820, 701417650754, 252961618295, 11730315755, 0, 0] := by
  rw [show D2M8K2.u11605 = KTree.node D2M8K2.t11614 (nat_lit 24952318) (nat_lit 3749681712) (nat_lit 0) D2M8K2.t11615 from rfl, totK_node, tot11614, tot11615]
  decide +kernel

theorem arows11610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11610 = true := by
  rw [show D2M8K2.u11610 = KTree.node D2M8K2.t11616 (nat_lit 24953820) (nat_lit 3129697929) (nat_lit 0) D2M8K2.t11617 from rfl, allE_node, rows11616, irow11610, rows11617]
  all_goals rfl

theorem atot11610 : totK PD2M8K2 D2M8K2.u11610 = [0, 227109119648, 852218502175, 658986439757, 65955378408, 0, 0, 0] := by
  rw [show D2M8K2.u11610 = KTree.node D2M8K2.t11616 (nat_lit 24953820) (nat_lit 3129697929) (nat_lit 0) D2M8K2.t11617 from rfl, totK_node, tot11616, tot11617]
  decide +kernel

theorem arows11611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11611 = true := by
  rw [show D2M8K2.u11611 = KTree.node D2M8K2.t11618 (nat_lit 24956120) (nat_lit 3579320266) (nat_lit 0) D2M8K2.t11619 from rfl, allE_node, rows11618, irow11611, rows11619]
  all_goals rfl

theorem atot11611 : totK PD2M8K2 D2M8K2.u11611 = [0, 198653097769, 667695460727, 749003719761, 185910679388, 5159868635, 0, 0] := by
  rw [show D2M8K2.u11611 = KTree.node D2M8K2.t11618 (nat_lit 24956120) (nat_lit 3579320266) (nat_lit 0) D2M8K2.t11619 from rfl, totK_node, tot11618, tot11619]
  decide +kernel

theorem arows11613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11613 = true := by
  rw [show D2M8K2.u11613 = KTree.node D2M8K2.t11620 (nat_lit 24957913) (nat_lit 664001016) (nat_lit 0) D2M8K2.t11621 from rfl, allE_node, rows11620, irow11613, rows11621]
  all_goals rfl

theorem atot11613 : totK PD2M8K2 D2M8K2.u11613 = [0, 128060521418, 659562726990, 812755515223, 202176013625, 5218872685, 0, 0] := by
  rw [show D2M8K2.u11613 = KTree.node D2M8K2.t11620 (nat_lit 24957913) (nat_lit 664001016) (nat_lit 0) D2M8K2.t11621 from rfl, totK_node, tot11620, tot11621]
  decide +kernel

theorem arows11614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11614 = true := by
  rw [show D2M8K2.u11614 = KTree.node D2M8K2.t11622 (nat_lit 24959808) (nat_lit 3605952180) (nat_lit 0) D2M8K2.t11623 from rfl, allE_node, rows11622, irow11614, rows11623]
  all_goals rfl

theorem atot11614 : totK PD2M8K2 D2M8K2.u11614 = [0, 354525726372, 894394562506, 512840418632, 50939060859, 0, 0, 0] := by
  rw [show D2M8K2.u11614 = KTree.node D2M8K2.t11622 (nat_lit 24959808) (nat_lit 3605952180) (nat_lit 0) D2M8K2.t11623 from rfl, totK_node, tot11622, tot11623]
  decide +kernel

theorem arows11617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11617 = true := by
  rw [show D2M8K2.u11617 = KTree.node D2M8K2.t11624 (nat_lit 24961600) (nat_lit 3764622440) (nat_lit 0) D2M8K2.t11625 from rfl, allE_node, rows11624, irow11617, rows11625]
  all_goals rfl

theorem atot11617 : totK PD2M8K2 D2M8K2.u11617 = [0, 111416696167, 704903897219, 848626503969, 141812813261, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11617 = KTree.node D2M8K2.t11624 (nat_lit 24961600) (nat_lit 3764622440) (nat_lit 0) D2M8K2.t11625 from rfl, totK_node, tot11624, tot11625]
  decide +kernel

theorem arows11618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11618 = true := by
  rw [show D2M8K2.u11618 = KTree.node D2M8K2.t11626 (nat_lit 24963504) (nat_lit 2457522036) (nat_lit 0) D2M8K2.t11627 from rfl, allE_node, rows11626, irow11618, rows11627]
  all_goals rfl

theorem atot11618 : totK PD2M8K2 D2M8K2.u11618 = [0, 333427766290, 905040503325, 543175648796, 48714551882, 0, 0, 0] := by
  rw [show D2M8K2.u11618 = KTree.node D2M8K2.t11626 (nat_lit 24963504) (nat_lit 2457522036) (nat_lit 0) D2M8K2.t11627 from rfl, totK_node, tot11626, tot11627]
  decide +kernel

theorem arows11620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11620 = true := by
  rw [show D2M8K2.u11620 = KTree.node D2M8K2.t11628 (nat_lit 24965504) (nat_lit 2890452882) (nat_lit 0) D2M8K2.t11629 from rfl, allE_node, rows11628, irow11620, rows11629]
  all_goals rfl

theorem atot11620 : totK PD2M8K2 D2M8K2.u11620 = [90523122812, 221364108128, 440261259376, 761631955527, 263927749761, 9302370699, 0, 0] := by
  rw [show D2M8K2.u11620 = KTree.node D2M8K2.t11628 (nat_lit 24965504) (nat_lit 2890452882) (nat_lit 0) D2M8K2.t11629 from rfl, totK_node, tot11628, tot11629]
  decide +kernel

theorem arows11621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11621 = true := by
  rw [show D2M8K2.u11621 = KTree.node D2M8K2.t11630 (nat_lit 24967348) (nat_lit 3974221304) (nat_lit 0) D2M8K2.t11631 from rfl, allE_node, rows11630, irow11621, rows11631]
  all_goals rfl

theorem atot11621 : totK PD2M8K2 D2M8K2.u11621 = [322678352438, 885997231659, 518090756965, 41834181383, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11621 = KTree.node D2M8K2.t11630 (nat_lit 24967348) (nat_lit 3974221304) (nat_lit 0) D2M8K2.t11631 from rfl, totK_node, tot11630, tot11631]
  decide +kernel

theorem arows11625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11625 = true := by
  rw [show D2M8K2.u11625 = KTree.node D2M8K2.t11632 (nat_lit 24969140) (nat_lit 3691010282) (nat_lit 0) D2M8K2.t11633 from rfl, allE_node, rows11632, irow11625, rows11633]
  all_goals rfl

theorem atot11625 : totK PD2M8K2 D2M8K2.u11625 = [153805469543, 685024589468, 829136299873, 153535307847, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11625 = KTree.node D2M8K2.t11632 (nat_lit 24969140) (nat_lit 3691010282) (nat_lit 0) D2M8K2.t11633 from rfl, totK_node, tot11632, tot11633]
  decide +kernel

theorem arows11626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11626 = true := by
  rw [show D2M8K2.u11626 = KTree.node D2M8K2.t11634 (nat_lit 24970923) (nat_lit 3727771151) (nat_lit 0) D2M8K2.t11635 from rfl, allE_node, rows11634, irow11626, rows11635]
  all_goals rfl

theorem atot11626 : totK PD2M8K2 D2M8K2.u11626 = [265950053628, 853825775382, 591980504494, 90392355407, 8415650999, 0, 0, 0] := by
  rw [show D2M8K2.u11626 = KTree.node D2M8K2.t11634 (nat_lit 24970923) (nat_lit 3727771151) (nat_lit 0) D2M8K2.t11635 from rfl, totK_node, tot11634, tot11635]
  decide +kernel

theorem arows11628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11628 = true := by
  rw [show D2M8K2.u11628 = KTree.node D2M8K2.t11636 (nat_lit 24972448) (nat_lit 1392937969) (nat_lit 0) D2M8K2.t11637 from rfl, allE_node, rows11636, irow11628, rows11637]
  all_goals rfl

theorem atot11628 : totK PD2M8K2 D2M8K2.u11628 = [18547827660, 350407592769, 905543500886, 486420766260, 26950892994, 0, 0, 0] := by
  rw [show D2M8K2.u11628 = KTree.node D2M8K2.t11636 (nat_lit 24972448) (nat_lit 1392937969) (nat_lit 0) D2M8K2.t11637 from rfl, totK_node, tot11636, tot11637]
  decide +kernel

theorem arows11629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11629 = true := by
  rw [show D2M8K2.u11629 = KTree.node D2M8K2.t11638 (nat_lit 24973665) (nat_lit 1817379955) (nat_lit 0) D2M8K2.t11639 from rfl, allE_node, rows11638, irow11629, rows11639]
  all_goals rfl

theorem atot11629 : totK PD2M8K2 D2M8K2.u11629 = [375512669416, 947200541999, 481131265142, 35498527673, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11629 = KTree.node D2M8K2.t11638 (nat_lit 24973665) (nat_lit 1817379955) (nat_lit 0) D2M8K2.t11639 from rfl, totK_node, tot11638, tot11639]
  decide +kernel

theorem arows11632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11632 = true := by
  rw [show D2M8K2.u11632 = KTree.node D2M8K2.t11640 (nat_lit 24975184) (nat_lit 3344895372) (nat_lit 0) D2M8K2.t11641 from rfl, allE_node, rows11640, irow11632, rows11641]
  all_goals rfl

theorem atot11632 : totK PD2M8K2 D2M8K2.u11632 = [48334856787, 527106480030, 919325949796, 281624643793, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11632 = KTree.node D2M8K2.t11640 (nat_lit 24975184) (nat_lit 3344895372) (nat_lit 0) D2M8K2.t11641 from rfl, totK_node, tot11640, tot11641]
  decide +kernel

theorem arows11633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11633 = true := by
  rw [show D2M8K2.u11633 = KTree.node D2M8K2.t11642 (nat_lit 24980435) (nat_lit 2605451683) (nat_lit 0) D2M8K2.t11643 from rfl, allE_node, rows11642, irow11633, rows11643]
  all_goals rfl

theorem atot11633 : totK PD2M8K2 D2M8K2.u11633 = [328839265906, 886688712267, 549299860112, 56564877728, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11633 = KTree.node D2M8K2.t11642 (nat_lit 24980435) (nat_lit 2605451683) (nat_lit 0) D2M8K2.t11643 from rfl, totK_node, tot11642, tot11643]
  decide +kernel

theorem arows11635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11635 = true := by
  rw [show D2M8K2.u11635 = KTree.node D2M8K2.t11644 (nat_lit 24982014) (nat_lit 3832990939) (nat_lit 0) D2M8K2.t11645 from rfl, allE_node, rows11644, irow11635, rows11645]
  all_goals rfl

theorem atot11635 : totK PD2M8K2 D2M8K2.u11635 = [91398613323, 682803794401, 879074013595, 145796594365, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11635 = KTree.node D2M8K2.t11644 (nat_lit 24982014) (nat_lit 3832990939) (nat_lit 0) D2M8K2.t11645 from rfl, totK_node, tot11644, tot11645]
  decide +kernel

theorem arows11636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11636 = true := by
  rw [show D2M8K2.u11636 = KTree.node D2M8K2.t11646 (nat_lit 24983928) (nat_lit 1352557670) (nat_lit 0) D2M8K2.t11647 from rfl, allE_node, rows11646, irow11636, rows11647]
  all_goals rfl

theorem atot11636 : totK PD2M8K2 D2M8K2.u11636 = [349252350151, 846653078853, 501996657625, 97723837701, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u11636 = KTree.node D2M8K2.t11646 (nat_lit 24983928) (nat_lit 1352557670) (nat_lit 0) D2M8K2.t11647 from rfl, totK_node, tot11646, tot11647]
  decide +kernel

theorem arows11643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11643 = true := by
  rw [show D2M8K2.u11643 = KTree.node D2M8K2.t11648 (nat_lit 24985519) (nat_lit 1788182620) (nat_lit 0) D2M8K2.t11649 from rfl, allE_node, rows11648, irow11643, rows11649]
  all_goals rfl

theorem atot11643 : totK PD2M8K2 D2M8K2.u11643 = [54703274150, 550291944007, 899241218761, 260488953252, 6032590049, 0, 0, 0] := by
  rw [show D2M8K2.u11643 = KTree.node D2M8K2.t11648 (nat_lit 24985519) (nat_lit 1788182620) (nat_lit 0) D2M8K2.t11649 from rfl, totK_node, tot11648, tot11649]
  decide +kernel

theorem arows11644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11644 = true := by
  rw [show D2M8K2.u11644 = KTree.node D2M8K2.t11650 (nat_lit 24987552) (nat_lit 3528681453) (nat_lit 0) D2M8K2.t11651 from rfl, allE_node, rows11650, irow11644, rows11651]
  all_goals rfl

theorem atot11644 : totK PD2M8K2 D2M8K2.u11644 = [0, 366742988758, 935037861290, 423864656786, 25341011067, 0, 0, 0] := by
  rw [show D2M8K2.u11644 = KTree.node D2M8K2.t11650 (nat_lit 24987552) (nat_lit 3528681453) (nat_lit 0) D2M8K2.t11651 from rfl, totK_node, tot11650, tot11651]
  decide +kernel

theorem arows11646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11646 = true := by
  rw [show D2M8K2.u11646 = KTree.node D2M8K2.t11652 (nat_lit 24988873) (nat_lit 1448625263) (nat_lit 0) D2M8K2.t11653 from rfl, allE_node, rows11652, irow11646, rows11653]
  all_goals rfl

theorem atot11646 : totK PD2M8K2 D2M8K2.u11646 = [0, 122847376193, 723523081901, 779773542128, 108089697200, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11646 = KTree.node D2M8K2.t11652 (nat_lit 24988873) (nat_lit 1448625263) (nat_lit 0) D2M8K2.t11653 from rfl, totK_node, tot11652, tot11653]
  decide +kernel

theorem arows11647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11647 = true := by
  rw [show D2M8K2.u11647 = KTree.node D2M8K2.t11654 (nat_lit 24991281) (nat_lit 1763753338) (nat_lit 0) D2M8K2.t11655 from rfl, allE_node, rows11654, irow11647, rows11655]
  all_goals rfl

theorem atot11647 : totK PD2M8K2 D2M8K2.u11647 = [0, 383489784944, 944588042256, 457902884586, 36099705989, 0, 0, 0] := by
  rw [show D2M8K2.u11647 = KTree.node D2M8K2.t11654 (nat_lit 24991281) (nat_lit 1763753338) (nat_lit 0) D2M8K2.t11655 from rfl, totK_node, tot11654, tot11655]
  decide +kernel

theorem arows11650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11650 = true := by
  rw [show D2M8K2.u11650 = KTree.node D2M8K2.t11656 (nat_lit 24994273) (nat_lit 1202906033) (nat_lit 0) D2M8K2.t11657 from rfl, allE_node, rows11656, irow11650, rows11657]
  all_goals rfl

theorem atot11650 : totK PD2M8K2 D2M8K2.u11650 = [0, 355691930362, 924316935804, 494866423092, 36982119859, 0, 0, 0] := by
  rw [show D2M8K2.u11650 = KTree.node D2M8K2.t11656 (nat_lit 24994273) (nat_lit 1202906033) (nat_lit 0) D2M8K2.t11657 from rfl, totK_node, tot11656, tot11657]
  decide +kernel

theorem arows11651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11651 = true := by
  rw [show D2M8K2.u11651 = KTree.node D2M8K2.t11658 (nat_lit 24995768) (nat_lit 3687505457) (nat_lit 0) D2M8K2.t11659 from rfl, allE_node, rows11658, irow11651, rows11659]
  all_goals rfl

theorem atot11651 : totK PD2M8K2 D2M8K2.u11651 = [0, 87927492280, 632262781270, 814942540115, 209721410556, 9579374723, 0, 0] := by
  rw [show D2M8K2.u11651 = KTree.node D2M8K2.t11658 (nat_lit 24995768) (nat_lit 3687505457) (nat_lit 0) D2M8K2.t11659 from rfl, totK_node, tot11658, tot11659]
  decide +kernel

theorem arows11653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11653 = true := by
  rw [show D2M8K2.u11653 = KTree.node D2M8K2.t11660 (nat_lit 25001074) (nat_lit 3080872609) (nat_lit 0) D2M8K2.t11661 from rfl, allE_node, rows11660, irow11653, rows11661]
  all_goals rfl

theorem atot11653 : totK PD2M8K2 D2M8K2.u11653 = [0, 322999040144, 832520333587, 533050997783, 92562809970, 3436822651, 0, 0] := by
  rw [show D2M8K2.u11653 = KTree.node D2M8K2.t11660 (nat_lit 25001074) (nat_lit 3080872609) (nat_lit 0) D2M8K2.t11661 from rfl, totK_node, tot11660, tot11661]
  decide +kernel

theorem arows11654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11654 = true := by
  rw [show D2M8K2.u11654 = KTree.node D2M8K2.t11662 (nat_lit 25002656) (nat_lit 3340895426) (nat_lit 0) D2M8K2.t11663 from rfl, allE_node, rows11662, irow11654, rows11663]
  all_goals rfl

theorem atot11654 : totK PD2M8K2 D2M8K2.u11654 = [0, 94888957409, 712918581280, 786469958061, 120445217759, 2012620868, 0, 0] := by
  rw [show D2M8K2.u11654 = KTree.node D2M8K2.t11662 (nat_lit 25002656) (nat_lit 3340895426) (nat_lit 0) D2M8K2.t11663 from rfl, totK_node, tot11662, tot11663]
  decide +kernel

theorem arows11658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11658 = true := by
  rw [show D2M8K2.u11658 = KTree.node D2M8K2.t11664 (nat_lit 25004695) (nat_lit 1631197809) (nat_lit 0) D2M8K2.t11665 from rfl, allE_node, rows11664, irow11658, rows11665]
  all_goals rfl

theorem atot11658 : totK PD2M8K2 D2M8K2.u11658 = [0, 369574368791, 882185501692, 470052026795, 61858283027, 2561774784, 0, 0] := by
  rw [show D2M8K2.u11658 = KTree.node D2M8K2.t11664 (nat_lit 25004695) (nat_lit 1631197809) (nat_lit 0) D2M8K2.t11665 from rfl, totK_node, tot11664, tot11665]
  decide +kernel

theorem arows11659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11659 = true := by
  rw [show D2M8K2.u11659 = KTree.node D2M8K2.t11666 (nat_lit 25049774) (nat_lit 3498029023) (nat_lit 0) D2M8K2.t11667 from rfl, allE_node, rows11666, irow11659, rows11667]
  all_goals rfl

theorem atot11659 : totK PD2M8K2 D2M8K2.u11659 = [341618104599, 815817889523, 478433623756, 142710302802, 13462490481, 0, 0, 0] := by
  rw [show D2M8K2.u11659 = KTree.node D2M8K2.t11666 (nat_lit 25049774) (nat_lit 3498029023) (nat_lit 0) D2M8K2.t11667 from rfl, totK_node, tot11666, tot11667]
  decide +kernel

theorem arows11661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11661 = true := by
  rw [show D2M8K2.u11661 = KTree.node D2M8K2.t11668 (nat_lit 25051061) (nat_lit 2004577482) (nat_lit 0) D2M8K2.t11669 from rfl, allE_node, rows11668, irow11661, rows11669]
  all_goals rfl

theorem atot11661 : totK PD2M8K2 D2M8K2.u11661 = [65428233788, 655707513577, 891105246478, 152593519207, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11661 = KTree.node D2M8K2.t11668 (nat_lit 25051061) (nat_lit 2004577482) (nat_lit 0) D2M8K2.t11669 from rfl, totK_node, tot11668, tot11669]
  decide +kernel

theorem arows11662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11662 = true := by
  rw [show D2M8K2.u11662 = KTree.node D2M8K2.t11670 (nat_lit 25053374) (nat_lit 2483933108) (nat_lit 0) D2M8K2.t11671 from rfl, allE_node, rows11670, irow11662, rows11671]
  all_goals rfl

theorem atot11662 : totK PD2M8K2 D2M8K2.u11662 = [368610090665, 924315768606, 504687881593, 42856476539, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11662 = KTree.node D2M8K2.t11670 (nat_lit 25053374) (nat_lit 2483933108) (nat_lit 0) D2M8K2.t11671 from rfl, totK_node, tot11670, tot11671]
  decide +kernel

theorem arows11665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11665 = true := by
  rw [show D2M8K2.u11665 = KTree.node D2M8K2.t11672 (nat_lit 25054892) (nat_lit 3687896008) (nat_lit 0) D2M8K2.t11673 from rfl, allE_node, rows11672, irow11665, rows11673]
  all_goals rfl

theorem atot11665 : totK PD2M8K2 D2M8K2.u11665 = [49717183811, 482167670088, 866967359481, 387865973579, 29380165115, 0, 0, 0] := by
  rw [show D2M8K2.u11665 = KTree.node D2M8K2.t11672 (nat_lit 25054892) (nat_lit 3687896008) (nat_lit 0) D2M8K2.t11673 from rfl, totK_node, tot11672, tot11673]
  decide +kernel

theorem arows11666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11666 = true := by
  rw [show D2M8K2.u11666 = KTree.node D2M8K2.t11674 (nat_lit 25056241) (nat_lit 1492717941) (nat_lit 0) D2M8K2.t11675 from rfl, allE_node, rows11674, irow11666, rows11675]
  all_goals rfl

theorem atot11666 : totK PD2M8K2 D2M8K2.u11666 = [265364800320, 731738107620, 618624838237, 192988970564, 8036788501, 0, 0, 0] := by
  rw [show D2M8K2.u11666 = KTree.node D2M8K2.t11674 (nat_lit 25056241) (nat_lit 1492717941) (nat_lit 0) D2M8K2.t11675 from rfl, totK_node, tot11674, tot11675]
  decide +kernel

theorem arows11668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11668 = true := by
  rw [show D2M8K2.u11668 = KTree.node D2M8K2.t11676 (nat_lit 25057738) (nat_lit 3797500052) (nat_lit 0) D2M8K2.t11677 from rfl, allE_node, rows11676, irow11668, rows11677]
  all_goals rfl

theorem atot11668 : totK PD2M8K2 D2M8K2.u11668 = [160348302782, 707746258130, 768409532837, 155763093769, 2309606161, 0, 0, 0] := by
  rw [show D2M8K2.u11668 = KTree.node D2M8K2.t11676 (nat_lit 25057738) (nat_lit 3797500052) (nat_lit 0) D2M8K2.t11677 from rfl, totK_node, tot11676, tot11677]
  decide +kernel

theorem arows11669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11669 = true := by
  rw [show D2M8K2.u11669 = KTree.node D2M8K2.t11678 (nat_lit 25059570) (nat_lit 3407810300) (nat_lit 0) D2M8K2.t11679 from rfl, allE_node, rows11678, irow11669, rows11679]
  all_goals rfl

theorem atot11669 : totK PD2M8K2 D2M8K2.u11669 = [254940120903, 722332860253, 641139766990, 177180305766, 10740121073, 0, 0, 0] := by
  rw [show D2M8K2.u11669 = KTree.node D2M8K2.t11678 (nat_lit 25059570) (nat_lit 3407810300) (nat_lit 0) D2M8K2.t11679 from rfl, totK_node, tot11678, tot11679]
  decide +kernel

theorem arows11674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11674 = true := by
  rw [show D2M8K2.u11674 = KTree.node D2M8K2.t11680 (nat_lit 25061402) (nat_lit 3200152305) (nat_lit 0) D2M8K2.t11681 from rfl, allE_node, rows11680, irow11674, rows11681]
  all_goals rfl

theorem atot11674 : totK PD2M8K2 D2M8K2.u11674 = [88410714321, 632732321165, 841788832482, 219456613823, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u11674 = KTree.node D2M8K2.t11680 (nat_lit 25061402) (nat_lit 3200152305) (nat_lit 0) D2M8K2.t11681 from rfl, totK_node, tot11680, tot11681]
  decide +kernel

theorem arows11675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11675 = true := by
  rw [show D2M8K2.u11675 = KTree.node D2M8K2.t11682 (nat_lit 25063384) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t11683 from rfl, allE_node, rows11682, irow11675, rows11683]
  all_goals rfl

theorem atot11675 : totK PD2M8K2 D2M8K2.u11675 = [346671972883, 840573933320, 522389467482, 98710473578, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u11675 = KTree.node D2M8K2.t11682 (nat_lit 25063384) (nat_lit 3667199931) (nat_lit 0) D2M8K2.t11683 from rfl, totK_node, tot11682, tot11683]
  decide +kernel

theorem arows11677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11677 = true := by
  rw [show D2M8K2.u11677 = KTree.node D2M8K2.t11684 (nat_lit 25064880) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t11685 from rfl, allE_node, rows11684, irow11677, rows11685]
  all_goals rfl

theorem atot11677 : totK PD2M8K2 D2M8K2.u11677 = [92722701599, 709420784768, 881606553063, 139678051803, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11677 = KTree.node D2M8K2.t11684 (nat_lit 25064880) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t11685 from rfl, totK_node, tot11684, tot11685]
  decide +kernel

theorem arows11678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11678 = true := by
  rw [show D2M8K2.u11678 = KTree.node D2M8K2.t11686 (nat_lit 25070548) (nat_lit 3742961715) (nat_lit 0) D2M8K2.t11687 from rfl, allE_node, rows11686, irow11678, rows11687]
  all_goals rfl

theorem atot11678 : totK PD2M8K2 D2M8K2.u11678 = [0, 365907318340, 945291531454, 421788743912, 23226855963, 0, 0, 0] := by
  rw [show D2M8K2.u11678 = KTree.node D2M8K2.t11686 (nat_lit 25070548) (nat_lit 3742961715) (nat_lit 0) D2M8K2.t11687 from rfl, totK_node, tot11686, tot11687]
  decide +kernel

theorem arows11681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11681 = true := by
  rw [show D2M8K2.u11681 = KTree.node D2M8K2.t11688 (nat_lit 25072227) (nat_lit 2978592485) (nat_lit 0) D2M8K2.t11689 from rfl, allE_node, rows11688, irow11681, rows11689]
  all_goals rfl

theorem atot11681 : totK PD2M8K2 D2M8K2.u11681 = [0, 158075385073, 767582548903, 715330635115, 100202621916, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11681 = KTree.node D2M8K2.t11688 (nat_lit 25072227) (nat_lit 2978592485) (nat_lit 0) D2M8K2.t11689 from rfl, totK_node, tot11688, tot11689]
  decide +kernel

theorem arows11682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11682 = true := by
  rw [show D2M8K2.u11682 = KTree.node D2M8K2.t11690 (nat_lit 25074367) (nat_lit 2435060492) (nat_lit 0) D2M8K2.t11691 from rfl, allE_node, rows11690, irow11682, rows11691]
  all_goals rfl

theorem atot11682 : totK PD2M8K2 D2M8K2.u11682 = [0, 343026173496, 924827263502, 505748846846, 37708537832, 0, 0, 0] := by
  rw [show D2M8K2.u11682 = KTree.node D2M8K2.t11690 (nat_lit 25074367) (nat_lit 2435060492) (nat_lit 0) D2M8K2.t11691 from rfl, totK_node, tot11690, tot11691]
  decide +kernel

theorem arows11684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11684 = true := by
  rw [show D2M8K2.u11684 = KTree.node D2M8K2.t11692 (nat_lit 25077365) (nat_lit 2404007425) (nat_lit 0) D2M8K2.t11693 from rfl, allE_node, rows11692, irow11684, rows11693]
  all_goals rfl

theorem atot11684 : totK PD2M8K2 D2M8K2.u11684 = [0, 387475433779, 957009359419, 438693257299, 23422307148, 0, 0, 0] := by
  rw [show D2M8K2.u11684 = KTree.node D2M8K2.t11692 (nat_lit 25077365) (nat_lit 2404007425) (nat_lit 0) D2M8K2.t11693 from rfl, totK_node, tot11692, tot11693]
  decide +kernel

theorem arows11685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11685 = true := by
  rw [show D2M8K2.u11685 = KTree.node D2M8K2.t11694 (nat_lit 25080704) (nat_lit 3674175421) (nat_lit 0) D2M8K2.t11695 from rfl, allE_node, rows11694, irow11685, rows11695]
  all_goals rfl

theorem atot11685 : totK PD2M8K2 D2M8K2.u11685 = [0, 356483888741, 955068497478, 466797228699, 24449061815, 0, 0, 0] := by
  rw [show D2M8K2.u11685 = KTree.node D2M8K2.t11694 (nat_lit 25080704) (nat_lit 3674175421) (nat_lit 0) D2M8K2.t11695 from rfl, totK_node, tot11694, tot11695]
  decide +kernel

theorem arows11689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11689 = true := by
  rw [show D2M8K2.u11689 = KTree.node D2M8K2.t11696 (nat_lit 25084229) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t11697 from rfl, allE_node, rows11696, irow11689, rows11697]
  all_goals rfl

theorem atot11689 : totK PD2M8K2 D2M8K2.u11689 = [0, 370312277228, 924235818662, 462564764317, 35363470864, 0, 0, 0] := by
  rw [show D2M8K2.u11689 = KTree.node D2M8K2.t11696 (nat_lit 25084229) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t11697 from rfl, totK_node, tot11696, tot11697]
  decide +kernel

theorem arows11690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11690 = true := by
  rw [show D2M8K2.u11690 = KTree.node D2M8K2.t11698 (nat_lit 25085767) (nat_lit 2317696545) (nat_lit 0) D2M8K2.t11699 from rfl, allE_node, rows11698, irow11690, rows11699]
  all_goals rfl

theorem atot11690 : totK PD2M8K2 D2M8K2.u11690 = [11364832707, 66884483406, 625074267352, 842934180291, 192215148162, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11690 = KTree.node D2M8K2.t11698 (nat_lit 25085767) (nat_lit 2317696545) (nat_lit 0) D2M8K2.t11699 from rfl, totK_node, tot11698, tot11699]
  decide +kernel

theorem arows11692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11692 = true := by
  rw [show D2M8K2.u11692 = KTree.node D2M8K2.t11700 (nat_lit 25091510) (nat_lit 3277805245) (nat_lit 0) D2M8K2.t11701 from rfl, allE_node, rows11700, irow11692, rows11701]
  all_goals rfl

theorem atot11692 : totK PD2M8K2 D2M8K2.u11692 = [384944921602, 942987097767, 430022066381, 23607203109, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11692 = KTree.node D2M8K2.t11700 (nat_lit 25091510) (nat_lit 3277805245) (nat_lit 0) D2M8K2.t11701 from rfl, totK_node, tot11700, tot11701]
  decide +kernel

theorem arows11693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11693 = true := by
  rw [show D2M8K2.u11693 = KTree.node D2M8K2.t11702 (nat_lit 25093257) (nat_lit 1833001472) (nat_lit 0) D2M8K2.t11703 from rfl, allE_node, rows11702, irow11693, rows11703]
  all_goals rfl

theorem atot11693 : totK PD2M8K2 D2M8K2.u11693 = [92632204243, 653705712199, 888207931707, 166862252378, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11693 = KTree.node D2M8K2.t11702 (nat_lit 25093257) (nat_lit 1833001472) (nat_lit 0) D2M8K2.t11703 from rfl, totK_node, tot11702, tot11703]
  decide +kernel

theorem arows11696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11696 = true := by
  rw [show D2M8K2.u11696 = KTree.node D2M8K2.t11704 (nat_lit 25095208) (nat_lit 3801179835) (nat_lit 0) D2M8K2.t11705 from rfl, allE_node, rows11704, irow11696, rows11705]
  all_goals rfl

theorem atot11696 : totK PD2M8K2 D2M8K2.u11696 = [315597201980, 904822456299, 564062426680, 55616844837, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11696 = KTree.node D2M8K2.t11704 (nat_lit 25095208) (nat_lit 3801179835) (nat_lit 0) D2M8K2.t11705 from rfl, totK_node, tot11704, tot11705]
  decide +kernel

theorem arows11697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11697 = true := by
  rw [show D2M8K2.u11697 = KTree.node D2M8K2.t11706 (nat_lit 25096724) (nat_lit 3535616441) (nat_lit 0) D2M8K2.t11707 from rfl, allE_node, rows11706, irow11697, rows11707]
  all_goals rfl

theorem atot11697 : totK PD2M8K2 D2M8K2.u11697 = [0, 350926241157, 932066775486, 494851949814, 33123195192, 0, 0, 0] := by
  rw [show D2M8K2.u11697 = KTree.node D2M8K2.t11706 (nat_lit 25096724) (nat_lit 3535616441) (nat_lit 0) D2M8K2.t11707 from rfl, totK_node, tot11706, tot11707]
  decide +kernel

theorem arows11699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11699 = true := by
  rw [show D2M8K2.u11699 = KTree.node D2M8K2.t11708 (nat_lit 25098038) (nat_lit 3939280358) (nat_lit 0) D2M8K2.t11709 from rfl, allE_node, rows11708, irow11699, rows11709]
  all_goals rfl

theorem atot11699 : totK PD2M8K2 D2M8K2.u11699 = [372592538776, 907490370734, 468834304684, 61586798344, 4431529051, 0, 0, 0] := by
  rw [show D2M8K2.u11699 = KTree.node D2M8K2.t11708 (nat_lit 25098038) (nat_lit 3939280358) (nat_lit 0) D2M8K2.t11709 from rfl, totK_node, tot11708, tot11709]
  decide +kernel

theorem arows11700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11700 = true := by
  rw [show D2M8K2.u11700 = KTree.node D2M8K2.t11710 (nat_lit 25099588) (nat_lit 3783410094) (nat_lit 0) D2M8K2.t11711 from rfl, allE_node, rows11710, irow11700, rows11711]
  all_goals rfl

theorem atot11700 : totK PD2M8K2 D2M8K2.u11700 = [52876224345, 533918503376, 899951552883, 276773046918, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u11700 = KTree.node D2M8K2.t11710 (nat_lit 25099588) (nat_lit 3783410094) (nat_lit 0) D2M8K2.t11711 from rfl, totK_node, tot11710, tot11711]
  decide +kernel

theorem arows11706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11706 = true := by
  rw [show D2M8K2.u11706 = KTree.node D2M8K2.t11712 (nat_lit 25108322) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t11713 from rfl, allE_node, rows11712, irow11706, rows11713]
  all_goals rfl

theorem atot11706 : totK PD2M8K2 D2M8K2.u11706 = [334611860343, 901659916139, 543566906740, 55452891327, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11706 = KTree.node D2M8K2.t11712 (nat_lit 25108322) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t11713 from rfl, totK_node, tot11712, tot11713]
  decide +kernel

theorem arows11707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11707 = true := by
  rw [show D2M8K2.u11707 = KTree.node D2M8K2.t11714 (nat_lit 25109833) (nat_lit 1467577154) (nat_lit 0) D2M8K2.t11715 from rfl, allE_node, rows11714, irow11707, rows11715]
  all_goals rfl

theorem atot11707 : totK PD2M8K2 D2M8K2.u11707 = [93371872402, 597963583826, 873924554227, 230505884283, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u11707 = KTree.node D2M8K2.t11714 (nat_lit 25109833) (nat_lit 1467577154) (nat_lit 0) D2M8K2.t11715 from rfl, totK_node, tot11714, tot11715]
  decide +kernel

theorem arows11709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11709 = true := by
  rw [show D2M8K2.u11709 = KTree.node D2M8K2.t11716 (nat_lit 25111492) (nat_lit 3957779519) (nat_lit 0) D2M8K2.t11717 from rfl, allE_node, rows11716, irow11709, rows11717]
  all_goals rfl

theorem atot11709 : totK PD2M8K2 D2M8K2.u11709 = [0, 358588632104, 935392300089, 453265807896, 26435335346, 0, 0, 0] := by
  rw [show D2M8K2.u11709 = KTree.node D2M8K2.t11716 (nat_lit 25111492) (nat_lit 3957779519) (nat_lit 0) D2M8K2.t11717 from rfl, totK_node, tot11716, tot11717]
  decide +kernel

theorem arows11710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11710 = true := by
  rw [show D2M8K2.u11710 = KTree.node D2M8K2.t11718 (nat_lit 25113145) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t11719 from rfl, allE_node, rows11718, irow11710, rows11719]
  all_goals rfl

theorem atot11710 : totK PD2M8K2 D2M8K2.u11710 = [0, 125222935637, 709581345261, 795979456390, 111880546449, 1310285577, 0, 0] := by
  rw [show D2M8K2.u11710 = KTree.node D2M8K2.t11718 (nat_lit 25113145) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t11719 from rfl, totK_node, tot11718, tot11719]
  decide +kernel

theorem arows11713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11713 = true := by
  rw [show D2M8K2.u11713 = KTree.node D2M8K2.t11720 (nat_lit 25115503) (nat_lit 1690238040) (nat_lit 0) D2M8K2.t11721 from rfl, allE_node, rows11720, irow11713, rows11721]
  all_goals rfl

theorem atot11713 : totK PD2M8K2 D2M8K2.u11713 = [0, 366363062589, 917621761952, 520444878177, 45416876609, 0, 0, 0] := by
  rw [show D2M8K2.u11713 = KTree.node D2M8K2.t11720 (nat_lit 25115503) (nat_lit 1690238040) (nat_lit 0) D2M8K2.t11721 from rfl, totK_node, tot11720, tot11721]
  decide +kernel

theorem arows11714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11714 = true := by
  rw [show D2M8K2.u11714 = KTree.node D2M8K2.t11722 (nat_lit 25118599) (nat_lit 1635715178) (nat_lit 0) D2M8K2.t11723 from rfl, allE_node, rows11722, irow11714, rows11723]
  all_goals rfl

theorem atot11714 : totK PD2M8K2 D2M8K2.u11714 = [0, 357126846211, 915056625328, 491624405267, 42533042960, 0, 0, 0] := by
  rw [show D2M8K2.u11714 = KTree.node D2M8K2.t11722 (nat_lit 25118599) (nat_lit 1635715178) (nat_lit 0) D2M8K2.t11723 from rfl, totK_node, tot11722, tot11723]
  decide +kernel

theorem arows11716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11716 = true := by
  rw [show D2M8K2.u11716 = KTree.node D2M8K2.t11724 (nat_lit 25120087) (nat_lit 1140319164) (nat_lit 0) D2M8K2.t11725 from rfl, allE_node, rows11724, irow11716, rows11725]
  all_goals rfl

theorem atot11716 : totK PD2M8K2 D2M8K2.u11716 = [0, 107081524770, 670985640922, 802707582234, 163615286280, 4879840392, 0, 0] := by
  rw [show D2M8K2.u11716 = KTree.node D2M8K2.t11724 (nat_lit 25120087) (nat_lit 1140319164) (nat_lit 0) D2M8K2.t11725 from rfl, totK_node, tot11724, tot11725]
  decide +kernel

theorem arows11717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11717 = true := by
  rw [show D2M8K2.u11717 = KTree.node D2M8K2.t11726 (nat_lit 25129057) (nat_lit 1153823719) (nat_lit 0) D2M8K2.t11727 from rfl, allE_node, rows11726, irow11717, rows11727]
  all_goals rfl

theorem atot11717 : totK PD2M8K2 D2M8K2.u11717 = [0, 333314550976, 898012738228, 532591342981, 47408868191, 0, 0, 0] := by
  rw [show D2M8K2.u11717 = KTree.node D2M8K2.t11726 (nat_lit 25129057) (nat_lit 1153823719) (nat_lit 0) D2M8K2.t11727 from rfl, totK_node, tot11726, tot11727]
  decide +kernel

theorem arows11721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11721 = true := by
  rw [show D2M8K2.u11721 = KTree.node D2M8K2.t11728 (nat_lit 25130573) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t11729 from rfl, allE_node, rows11728, irow11721, rows11729]
  all_goals rfl

theorem atot11721 : totK PD2M8K2 D2M8K2.u11721 = [0, 93186765550, 588326431388, 852153859578, 225044804279, 5842784248, 0, 0] := by
  rw [show D2M8K2.u11721 = KTree.node D2M8K2.t11728 (nat_lit 25130573) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t11729 from rfl, totK_node, tot11728, tot11729]
  decide +kernel

theorem arows11722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11722 = true := by
  rw [show D2M8K2.u11722 = KTree.node D2M8K2.t11730 (nat_lit 25132279) (nat_lit 2224132896) (nat_lit 0) D2M8K2.t11731 from rfl, allE_node, rows11730, irow11722, rows11731]
  all_goals rfl

theorem atot11722 : totK PD2M8K2 D2M8K2.u11722 = [0, 268839193492, 758895951902, 563594865495, 174978410368, 15908383818, 0, 0] := by
  rw [show D2M8K2.u11722 = KTree.node D2M8K2.t11730 (nat_lit 25132279) (nat_lit 2224132896) (nat_lit 0) D2M8K2.t11731 from rfl, totK_node, tot11730, tot11731]
  decide +kernel

theorem arows11724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11724 = true := by
  rw [show D2M8K2.u11724 = KTree.node D2M8K2.t11732 (nat_lit 25133808) (nat_lit 3628317869) (nat_lit 0) D2M8K2.t11733 from rfl, allE_node, rows11732, irow11724, rows11733]
  all_goals rfl

theorem atot11724 : totK PD2M8K2 D2M8K2.u11724 = [0, 160081200723, 737120267958, 762479592047, 125978237844, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11724 = KTree.node D2M8K2.t11732 (nat_lit 25133808) (nat_lit 3628317869) (nat_lit 0) D2M8K2.t11733 from rfl, totK_node, tot11732, tot11733]
  decide +kernel

theorem arows11725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11725 = true := by
  rw [show D2M8K2.u11725 = KTree.node D2M8K2.t11734 (nat_lit 25139349) (nat_lit 1689335052) (nat_lit 0) D2M8K2.t11735 from rfl, allE_node, rows11734, irow11725, rows11735]
  all_goals rfl

theorem atot11725 : totK PD2M8K2 D2M8K2.u11725 = [0, 325746947286, 870627692072, 557622126364, 54446699142, 0, 0, 0] := by
  rw [show D2M8K2.u11725 = KTree.node D2M8K2.t11734 (nat_lit 25139349) (nat_lit 1689335052) (nat_lit 0) D2M8K2.t11735 from rfl, totK_node, tot11734, tot11735]
  decide +kernel

theorem arows11728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11728 = true := by
  rw [show D2M8K2.u11728 = KTree.node D2M8K2.t11736 (nat_lit 25140821) (nat_lit 2175232008) (nat_lit 0) D2M8K2.t11737 from rfl, allE_node, rows11736, irow11728, rows11737]
  all_goals rfl

theorem atot11728 : totK PD2M8K2 D2M8K2.u11728 = [0, 96336557448, 627180092206, 831119403002, 210446329660, 9587713104, 0, 0] := by
  rw [show D2M8K2.u11728 = KTree.node D2M8K2.t11736 (nat_lit 25140821) (nat_lit 2175232008) (nat_lit 0) D2M8K2.t11737 from rfl, totK_node, tot11736, tot11737]
  decide +kernel

theorem arows11729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11729 = true := by
  rw [show D2M8K2.u11729 = KTree.node D2M8K2.t11738 (nat_lit 25143271) (nat_lit 2396299761) (nat_lit 0) D2M8K2.t11739 from rfl, allE_node, rows11738, irow11729, rows11739]
  all_goals rfl

theorem atot11729 : totK PD2M8K2 D2M8K2.u11729 = [0, 287319053733, 813417162828, 558015505630, 100012888907, 3462014130, 0, 0] := by
  rw [show D2M8K2.u11729 = KTree.node D2M8K2.t11738 (nat_lit 25143271) (nat_lit 2396299761) (nat_lit 0) D2M8K2.t11739 from rfl, totK_node, tot11738, tot11739]
  decide +kernel

theorem arows11731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11731 = true := by
  rw [show D2M8K2.u11731 = KTree.node D2M8K2.t11740 (nat_lit 25145296) (nat_lit 2789454278) (nat_lit 0) D2M8K2.t11741 from rfl, allE_node, rows11740, irow11731, rows11741]
  all_goals rfl

theorem atot11731 : totK PD2M8K2 D2M8K2.u11731 = [0, 170920902350, 745209220754, 755666749828, 114495186556, 1198073392, 0, 0] := by
  rw [show D2M8K2.u11731 = KTree.node D2M8K2.t11740 (nat_lit 25145296) (nat_lit 2789454278) (nat_lit 0) D2M8K2.t11741 from rfl, totK_node, tot11740, tot11741]
  decide +kernel

theorem arows11732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11732 = true := by
  rw [show D2M8K2.u11732 = KTree.node D2M8K2.t11742 (nat_lit 25146872) (nat_lit 3506633385) (nat_lit 0) D2M8K2.t11743 from rfl, allE_node, rows11742, irow11732, rows11743]
  all_goals rfl

theorem atot11732 : totK PD2M8K2 D2M8K2.u11732 = [0, 269924349554, 827800039661, 597300264968, 73800497959, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11732 = KTree.node D2M8K2.t11742 (nat_lit 25146872) (nat_lit 3506633385) (nat_lit 0) D2M8K2.t11743 from rfl, totK_node, tot11742, tot11743]
  decide +kernel

theorem arows11737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11737 = true := by
  rw [show D2M8K2.u11737 = KTree.node D2M8K2.t11744 (nat_lit 25148846) (nat_lit 3652554697) (nat_lit 0) D2M8K2.t11745 from rfl, allE_node, rows11744, irow11737, rows11745]
  all_goals rfl

theorem atot11737 : totK PD2M8K2 D2M8K2.u11737 = [0, 158898794424, 688544495211, 794843523515, 151846230042, 3820764243, 0, 0] := by
  rw [show D2M8K2.u11737 = KTree.node D2M8K2.t11744 (nat_lit 25148846) (nat_lit 3652554697) (nat_lit 0) D2M8K2.t11745 from rfl, totK_node, tot11744, tot11745]
  decide +kernel

theorem arows11738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11738 = true := by
  rw [show D2M8K2.u11738 = KTree.node D2M8K2.t11746 (nat_lit 25150834) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t11747 from rfl, allE_node, rows11746, irow11738, rows11747]
  all_goals rfl

theorem atot11738 : totK PD2M8K2 D2M8K2.u11738 = [0, 223387765407, 776181363507, 669571868743, 113442510155, 1268739303, 0, 0] := by
  rw [show D2M8K2.u11738 = KTree.node D2M8K2.t11746 (nat_lit 25150834) (nat_lit 4023268641) (nat_lit 0) D2M8K2.t11747 from rfl, totK_node, tot11746, tot11747]
  decide +kernel

theorem arows11740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11740 = true := by
  rw [show D2M8K2.u11740 = KTree.node D2M8K2.t11748 (nat_lit 25152745) (nat_lit 1448736475) (nat_lit 0) D2M8K2.t11749 from rfl, allE_node, rows11748, irow11740, rows11749]
  all_goals rfl

theorem atot11740 : totK PD2M8K2 D2M8K2.u11740 = [0, 0, 397487880231, 953728942366, 391440513998, 22062817559, 0, 0] := by
  rw [show D2M8K2.u11740 = KTree.node D2M8K2.t11748 (nat_lit 25152745) (nat_lit 1448736475) (nat_lit 0) D2M8K2.t11749 from rfl, totK_node, tot11748, tot11749]
  decide +kernel

theorem arows11741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11741 = true := by
  rw [show D2M8K2.u11741 = KTree.node D2M8K2.t11750 (nat_lit 25154290) (nat_lit 3994572769) (nat_lit 0) D2M8K2.t11751 from rfl, allE_node, rows11750, irow11741, rows11751]
  all_goals rfl

theorem atot11741 : totK PD2M8K2 D2M8K2.u11741 = [0, 0, 237015874363, 795235408672, 579757102856, 86558769187, 1275377855, 0] := by
  rw [show D2M8K2.u11741 = KTree.node D2M8K2.t11750 (nat_lit 25154290) (nat_lit 3994572769) (nat_lit 0) D2M8K2.t11751 from rfl, totK_node, tot11750, tot11751]
  decide +kernel

theorem arows11744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11744 = true := by
  rw [show D2M8K2.u11744 = KTree.node D2M8K2.t11752 (nat_lit 25159996) (nat_lit 3937950544) (nat_lit 0) D2M8K2.t11753 from rfl, allE_node, rows11752, irow11744, rows11753]
  all_goals rfl

theorem atot11744 : totK PD2M8K2 D2M8K2.u11744 = [0, 0, 291471052203, 909177906364, 509768631598, 33924260570, 0, 0] := by
  rw [show D2M8K2.u11744 = KTree.node D2M8K2.t11752 (nat_lit 25159996) (nat_lit 3937950544) (nat_lit 0) D2M8K2.t11753 from rfl, totK_node, tot11752, tot11753]
  decide +kernel

theorem arows11745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11745 = true := by
  rw [show D2M8K2.u11745 = KTree.node D2M8K2.t11754 (nat_lit 25163250) (nat_lit 3296305079) (nat_lit 0) D2M8K2.t11755 from rfl, allE_node, rows11754, irow11745, rows11755]
  all_goals rfl

theorem atot11745 : totK PD2M8K2 D2M8K2.u11745 = [0, 0, 429549777084, 952316288865, 339648274883, 14883806702, 0, 0] := by
  rw [show D2M8K2.u11745 = KTree.node D2M8K2.t11754 (nat_lit 25163250) (nat_lit 3296305079) (nat_lit 0) D2M8K2.t11755 from rfl, totK_node, tot11754, tot11755]
  decide +kernel

theorem arows11747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11747 = true := by
  rw [show D2M8K2.u11747 = KTree.node D2M8K2.t11756 (nat_lit 25167230) (nat_lit 3794842270) (nat_lit 0) D2M8K2.t11757 from rfl, allE_node, rows11756, irow11747, rows11757]
  all_goals rfl

theorem atot11747 : totK PD2M8K2 D2M8K2.u11747 = [0, 0, 425527962478, 990095153808, 331319406483, 12118062284, 0, 0] := by
  rw [show D2M8K2.u11747 = KTree.node D2M8K2.t11756 (nat_lit 25167230) (nat_lit 3794842270) (nat_lit 0) D2M8K2.t11757 from rfl, totK_node, tot11756, tot11757]
  decide +kernel

theorem arows11748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11748 = true := by
  rw [show D2M8K2.u11748 = KTree.node D2M8K2.t11758 (nat_lit 25170747) (nat_lit 3539802514) (nat_lit 0) D2M8K2.t11759 from rfl, allE_node, rows11758, irow11748, rows11759]
  all_goals rfl

theorem atot11748 : totK PD2M8K2 D2M8K2.u11748 = [0, 38616506213, 421953056796, 919174018377, 379966847642, 17967166286, 0, 0] := by
  rw [show D2M8K2.u11748 = KTree.node D2M8K2.t11758 (nat_lit 25170747) (nat_lit 3539802514) (nat_lit 0) D2M8K2.t11759 from rfl, totK_node, tot11758, tot11759]
  decide +kernel

theorem arows11752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11752 = true := by
  rw [show D2M8K2.u11752 = KTree.node D2M8K2.t11760 (nat_lit 25177858) (nat_lit 3995497417) (nat_lit 0) D2M8K2.t11761 from rfl, allE_node, rows11760, irow11752, rows11761]
  all_goals rfl

theorem atot11752 : totK PD2M8K2 D2M8K2.u11752 = [0, 366621563026, 935175316876, 499988622625, 38774867355, 0, 0, 0] := by
  rw [show D2M8K2.u11752 = KTree.node D2M8K2.t11760 (nat_lit 25177858) (nat_lit 3995497417) (nat_lit 0) D2M8K2.t11761 from rfl, totK_node, tot11760, tot11761]
  decide +kernel

theorem arows11753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11753 = true := by
  rw [show D2M8K2.u11753 = KTree.node D2M8K2.t11762 (nat_lit 25179303) (nat_lit 3631119225) (nat_lit 0) D2M8K2.t11763 from rfl, allE_node, rows11762, irow11753, rows11763]
  all_goals rfl

theorem atot11753 : totK PD2M8K2 D2M8K2.u11753 = [0, 36931127369, 482949543441, 882093783739, 383074677604, 29328793087, 0, 0] := by
  rw [show D2M8K2.u11753 = KTree.node D2M8K2.t11762 (nat_lit 25179303) (nat_lit 3631119225) (nat_lit 0) D2M8K2.t11763 from rfl, totK_node, tot11762, tot11763]
  decide +kernel

theorem arows11755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11755 = true := by
  rw [show D2M8K2.u11755 = KTree.node D2M8K2.t11764 (nat_lit 25180611) (nat_lit 1696620042) (nat_lit 0) D2M8K2.t11765 from rfl, allE_node, rows11764, irow11755, rows11765]
  all_goals rfl

theorem atot11755 : totK PD2M8K2 D2M8K2.u11755 = [0, 252861190695, 709114787443, 648844731306, 203453682896, 8170814383, 0, 0] := by
  rw [show D2M8K2.u11755 = KTree.node D2M8K2.t11764 (nat_lit 25180611) (nat_lit 1696620042) (nat_lit 0) D2M8K2.t11765 from rfl, totK_node, tot11764, tot11765]
  decide +kernel

theorem arows11756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11756 = true := by
  rw [show D2M8K2.u11756 = KTree.node D2M8K2.t11766 (nat_lit 25182078) (nat_lit 3232038899) (nat_lit 0) D2M8K2.t11767 from rfl, allE_node, rows11766, irow11756, rows11767]
  all_goals rfl

theorem atot11756 : totK PD2M8K2 D2M8K2.u11756 = [0, 171243662000, 733421756727, 740762278253, 145880795537, 5998727602, 0, 0] := by
  rw [show D2M8K2.u11756 = KTree.node D2M8K2.t11766 (nat_lit 25182078) (nat_lit 3232038899) (nat_lit 0) D2M8K2.t11767 from rfl, totK_node, tot11766, tot11767]
  decide +kernel

theorem arows11759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11759 = true := by
  rw [show D2M8K2.u11759 = KTree.node D2M8K2.t11768 (nat_lit 25184294) (nat_lit 4041823053) (nat_lit 0) D2M8K2.t11769 from rfl, allE_node, rows11768, irow11759, rows11769]
  all_goals rfl

theorem atot11759 : totK PD2M8K2 D2M8K2.u11759 = [0, 260845155826, 738842498242, 668833790399, 146347185180, 5874298072, 0, 0] := by
  rw [show D2M8K2.u11759 = KTree.node D2M8K2.t11768 (nat_lit 25184294) (nat_lit 4041823053) (nat_lit 0) D2M8K2.t11769 from rfl, totK_node, tot11768, tot11769]
  decide +kernel

theorem arows11760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11760 = true := by
  rw [show D2M8K2.u11760 = KTree.node D2M8K2.t11770 (nat_lit 25186548) (nat_lit 3142586240) (nat_lit 0) D2M8K2.t11771 from rfl, allE_node, rows11770, irow11760, rows11771]
  all_goals rfl

theorem atot11760 : totK PD2M8K2 D2M8K2.u11760 = [0, 97731668663, 640354745523, 852974688605, 215194332265, 5439011083, 0, 0] := by
  rw [show D2M8K2.u11760 = KTree.node D2M8K2.t11770 (nat_lit 25186548) (nat_lit 3142586240) (nat_lit 0) D2M8K2.t11771 from rfl, totK_node, tot11770, tot11771]
  decide +kernel

theorem arows11762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11762 = true := by
  rw [show D2M8K2.u11762 = KTree.node D2M8K2.t11772 (nat_lit 25188006) (nat_lit 3058419716) (nat_lit 0) D2M8K2.t11773 from rfl, allE_node, rows11772, irow11762, rows11773]
  all_goals rfl

theorem atot11762 : totK PD2M8K2 D2M8K2.u11762 = [0, 385513896612, 936084514249, 465909803649, 39203232067, 0, 0, 0] := by
  rw [show D2M8K2.u11762 = KTree.node D2M8K2.t11772 (nat_lit 25188006) (nat_lit 3058419716) (nat_lit 0) D2M8K2.t11773 from rfl, totK_node, tot11772, tot11773]
  decide +kernel

theorem arows11763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11763 = true := by
  rw [show D2M8K2.u11763 = KTree.node D2M8K2.t11774 (nat_lit 25189960) (nat_lit 3085972138) (nat_lit 0) D2M8K2.t11775 from rfl, allE_node, rows11774, irow11763, rows11775]
  all_goals rfl

theorem atot11763 : totK PD2M8K2 D2M8K2.u11763 = [0, 90893841501, 688154939726, 865693062771, 161732232076, 3880716147, 0, 0] := by
  rw [show D2M8K2.u11763 = KTree.node D2M8K2.t11774 (nat_lit 25189960) (nat_lit 3085972138) (nat_lit 0) D2M8K2.t11775 from rfl, totK_node, tot11774, tot11775]
  decide +kernel

theorem arows11772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11772 = true := by
  rw [show D2M8K2.u11772 = KTree.node D2M8K2.t11776 (nat_lit 25191732) (nat_lit 2709752370) (nat_lit 0) D2M8K2.t11777 from rfl, allE_node, rows11776, irow11772, rows11777]
  all_goals rfl

theorem atot11772 : totK PD2M8K2 D2M8K2.u11772 = [0, 295825200940, 856965195517, 595203309414, 75159966481, 1231519631, 0, 0] := by
  rw [show D2M8K2.u11772 = KTree.node D2M8K2.t11776 (nat_lit 25191732) (nat_lit 2709752370) (nat_lit 0) D2M8K2.t11777 from rfl, totK_node, tot11776, tot11777]
  decide +kernel

theorem arows11773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11773 = true := by
  rw [show D2M8K2.u11773 = KTree.node D2M8K2.t11778 (nat_lit 25193546) (nat_lit 4100340752) (nat_lit 0) D2M8K2.t11779 from rfl, allE_node, rows11778, irow11773, rows11779]
  all_goals rfl

theorem atot11773 : totK PD2M8K2 D2M8K2.u11773 = [0, 90277532827, 512151436903, 841806113959, 326636761217, 16559750595, 0, 0] := by
  rw [show D2M8K2.u11773 = KTree.node D2M8K2.t11778 (nat_lit 25193546) (nat_lit 4100340752) (nat_lit 0) D2M8K2.t11779 from rfl, totK_node, tot11778, tot11779]
  decide +kernel

theorem arows11775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11775 = true := by
  rw [show D2M8K2.u11775 = KTree.node D2M8K2.t11780 (nat_lit 25216161) (nat_lit 1847415472) (nat_lit 0) D2M8K2.t11781 from rfl, allE_node, rows11780, irow11775, rows11781]
  all_goals rfl

theorem atot11775 : totK PD2M8K2 D2M8K2.u11775 = [0, 321403526368, 907612274882, 500572592403, 33719423733, 0, 0, 0] := by
  rw [show D2M8K2.u11775 = KTree.node D2M8K2.t11780 (nat_lit 25216161) (nat_lit 1847415472) (nat_lit 0) D2M8K2.t11781 from rfl, totK_node, tot11780, tot11781]
  decide +kernel

theorem arows11776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11776 = true := by
  rw [show D2M8K2.u11776 = KTree.node D2M8K2.t11782 (nat_lit 25217960) (nat_lit 3933518588) (nat_lit 0) D2M8K2.t11783 from rfl, allE_node, rows11782, irow11776, rows11783]
  all_goals rfl

theorem atot11776 : totK PD2M8K2 D2M8K2.u11776 = [0, 146499304292, 686491036267, 836067473940, 136061364502, 1334361349, 0, 0] := by
  rw [show D2M8K2.u11776 = KTree.node D2M8K2.t11782 (nat_lit 25217960) (nat_lit 3933518588) (nat_lit 0) D2M8K2.t11783 from rfl, totK_node, tot11782, tot11783]
  decide +kernel

theorem arows11779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11779 = true := by
  rw [show D2M8K2.u11779 = KTree.node D2M8K2.t11784 (nat_lit 25219748) (nat_lit 3014307990) (nat_lit 0) D2M8K2.t11785 from rfl, allE_node, rows11784, irow11779, rows11785]
  all_goals rfl

theorem atot11779 : totK PD2M8K2 D2M8K2.u11779 = [0, 276519636857, 856443213554, 587542338667, 83691902179, 6124536247, 0, 0] := by
  rw [show D2M8K2.u11779 = KTree.node D2M8K2.t11784 (nat_lit 25219748) (nat_lit 3014307990) (nat_lit 0) D2M8K2.t11785 from rfl, totK_node, tot11784, tot11785]
  decide +kernel

theorem arows11780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11780 = true := by
  rw [show D2M8K2.u11780 = KTree.node D2M8K2.t11786 (nat_lit 25221374) (nat_lit 3850045680) (nat_lit 0) D2M8K2.t11787 from rfl, allE_node, rows11786, irow11780, rows11787]
  all_goals rfl

theorem atot11780 : totK PD2M8K2 D2M8K2.u11780 = [0, 86563879224, 461996379472, 852969304897, 374086273513, 17964388030, 0, 0] := by
  rw [show D2M8K2.u11780 = KTree.node D2M8K2.t11786 (nat_lit 25221374) (nat_lit 3850045680) (nat_lit 0) D2M8K2.t11787 from rfl, totK_node, tot11786, tot11787]
  decide +kernel

theorem arows11782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11782 = true := by
  rw [show D2M8K2.u11782 = KTree.node D2M8K2.t11788 (nat_lit 25222615) (nat_lit 1153339818) (nat_lit 0) D2M8K2.t11789 from rfl, allE_node, rows11788, irow11782, rows11789]
  all_goals rfl

theorem atot11782 : totK PD2M8K2 D2M8K2.u11782 = [0, 358792387986, 944083151274, 502672538582, 36238467182, 0, 0, 0] := by
  rw [show D2M8K2.u11782 = KTree.node D2M8K2.t11788 (nat_lit 25222615) (nat_lit 1153339818) (nat_lit 0) D2M8K2.t11789 from rfl, totK_node, tot11788, tot11789]
  decide +kernel

theorem arows11783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11783 = true := by
  rw [show D2M8K2.u11783 = KTree.node D2M8K2.t11790 (nat_lit 25224257) (nat_lit 2224460729) (nat_lit 0) D2M8K2.t11791 from rfl, allE_node, rows11790, irow11783, rows11791]
  all_goals rfl

theorem atot11783 : totK PD2M8K2 D2M8K2.u11783 = [0, 0, 493868020829, 981261519505, 293997192866, 13049727234, 0, 0] := by
  rw [show D2M8K2.u11783 = KTree.node D2M8K2.t11790 (nat_lit 25224257) (nat_lit 2224460729) (nat_lit 0) D2M8K2.t11791 from rfl, totK_node, tot11790, tot11791]
  decide +kernel

theorem arows11787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11787 = true := by
  rw [show D2M8K2.u11787 = KTree.node D2M8K2.t11792 (nat_lit 25229374) (nat_lit 3840457228) (nat_lit 0) D2M8K2.t11793 from rfl, allE_node, rows11792, irow11787, rows11793]
  all_goals rfl

theorem atot11787 : totK PD2M8K2 D2M8K2.u11787 = [0, 382545719068, 912079129441, 471536459679, 42103734476, 0, 0, 0] := by
  rw [show D2M8K2.u11787 = KTree.node D2M8K2.t11792 (nat_lit 25229374) (nat_lit 3840457228) (nat_lit 0) D2M8K2.t11793 from rfl, totK_node, tot11792, tot11793]
  decide +kernel

theorem arows11788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11788 = true := by
  rw [show D2M8K2.u11788 = KTree.node D2M8K2.t11794 (nat_lit 25231113) (nat_lit 1826488374) (nat_lit 0) D2M8K2.t11795 from rfl, allE_node, rows11794, irow11788, rows11795]
  all_goals rfl

theorem atot11788 : totK PD2M8K2 D2M8K2.u11788 = [0, 76339986798, 624374931258, 890032944141, 182391681857, 4846308403, 0, 0] := by
  rw [show D2M8K2.u11788 = KTree.node D2M8K2.t11794 (nat_lit 25231113) (nat_lit 1826488374) (nat_lit 0) D2M8K2.t11795 from rfl, totK_node, tot11794, tot11795]
  decide +kernel

theorem arows11790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11790 = true := by
  rw [show D2M8K2.u11790 = KTree.node D2M8K2.t11796 (nat_lit 25232891) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t11797 from rfl, allE_node, rows11796, irow11790, rows11797]
  all_goals rfl

theorem atot11790 : totK PD2M8K2 D2M8K2.u11790 = [0, 362987134942, 931553859777, 478761560262, 33471988599, 0, 0, 0] := by
  rw [show D2M8K2.u11790 = KTree.node D2M8K2.t11796 (nat_lit 25232891) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t11797 from rfl, totK_node, tot11796, tot11797]
  decide +kernel

theorem arows11791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11791 = true := by
  rw [show D2M8K2.u11791 = KTree.node D2M8K2.t11798 (nat_lit 25234625) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t11799 from rfl, allE_node, rows11798, irow11791, rows11799]
  all_goals rfl

theorem atot11791 : totK PD2M8K2 D2M8K2.u11791 = [0, 0, 465656403019, 960898300368, 318408202412, 13729587881, 0, 0] := by
  rw [show D2M8K2.u11791 = KTree.node D2M8K2.t11798 (nat_lit 25234625) (nat_lit 2222962290) (nat_lit 0) D2M8K2.t11799 from rfl, totK_node, tot11798, tot11799]
  decide +kernel

theorem arows11794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11794 = true := by
  rw [show D2M8K2.u11794 = KTree.node D2M8K2.t11800 (nat_lit 25236678) (nat_lit 3483204883) (nat_lit 0) D2M8K2.t11801 from rfl, allE_node, rows11800, irow11794, rows11801]
  all_goals rfl

theorem atot11794 : totK PD2M8K2 D2M8K2.u11794 = [0, 0, 388623783951, 958219714684, 367037968386, 15891741372, 0, 0] := by
  rw [show D2M8K2.u11794 = KTree.node D2M8K2.t11800 (nat_lit 25236678) (nat_lit 3483204883) (nat_lit 0) D2M8K2.t11801 from rfl, totK_node, tot11800, tot11801]
  decide +kernel

theorem arows11795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11795 = true := by
  rw [show D2M8K2.u11795 = KTree.node D2M8K2.t11802 (nat_lit 25238612) (nat_lit 3189106635) (nat_lit 0) D2M8K2.t11803 from rfl, allE_node, rows11802, irow11795, rows11803]
  all_goals rfl

theorem atot11795 : totK PD2M8K2 D2M8K2.u11795 = [0, 0, 118261042653, 703404980910, 779120262259, 118814710053, 1206465782, 0] := by
  rw [show D2M8K2.u11795 = KTree.node D2M8K2.t11802 (nat_lit 25238612) (nat_lit 3189106635) (nat_lit 0) D2M8K2.t11803 from rfl, totK_node, tot11802, tot11803]
  decide +kernel

theorem arows11797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11797 = true := by
  rw [show D2M8K2.u11797 = KTree.node D2M8K2.t11804 (nat_lit 25240576) (nat_lit 2878608012) (nat_lit 0) D2M8K2.t11805 from rfl, allE_node, rows11804, irow11797, rows11805]
  all_goals rfl

theorem atot11797 : totK PD2M8K2 D2M8K2.u11797 = [0, 0, 419902058465, 979933991178, 376701396983, 15622891705, 0, 0] := by
  rw [show D2M8K2.u11797 = KTree.node D2M8K2.t11804 (nat_lit 25240576) (nat_lit 2878608012) (nat_lit 0) D2M8K2.t11805 from rfl, totK_node, tot11804, tot11805]
  decide +kernel

theorem arows11798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11798 = true := by
  rw [show D2M8K2.u11798 = KTree.node D2M8K2.t11806 (nat_lit 25243821) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t11807 from rfl, allE_node, rows11806, irow11798, rows11807]
  all_goals rfl

theorem atot11798 : totK PD2M8K2 D2M8K2.u11798 = [0, 0, 315774630370, 903449901451, 528712362742, 43086678394, 0, 0] := by
  rw [show D2M8K2.u11798 = KTree.node D2M8K2.t11806 (nat_lit 25243821) (nat_lit 1500645314) (nat_lit 0) D2M8K2.t11807 from rfl, totK_node, tot11806, tot11807]
  decide +kernel

theorem arows11803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11803 = true := by
  rw [show D2M8K2.u11803 = KTree.node D2M8K2.t11808 (nat_lit 25245520) (nat_lit 3328303018) (nat_lit 0) D2M8K2.t11809 from rfl, allE_node, rows11808, irow11803, rows11809]
  all_goals rfl

theorem atot11803 : totK PD2M8K2 D2M8K2.u11803 = [0, 0, 82638451573, 535348088715, 818026419316, 264146471447, 13016197374, 0] := by
  rw [show D2M8K2.u11803 = KTree.node D2M8K2.t11808 (nat_lit 25245520) (nat_lit 3328303018) (nat_lit 0) D2M8K2.t11809 from rfl, totK_node, tot11808, tot11809]
  decide +kernel

theorem arows11804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11804 = true := by
  rw [show D2M8K2.u11804 = KTree.node D2M8K2.t11810 (nat_lit 25250380) (nat_lit 3912255824) (nat_lit 0) D2M8K2.t11811 from rfl, allE_node, rows11810, irow11804, rows11811]
  all_goals rfl

theorem atot11804 : totK PD2M8K2 D2M8K2.u11804 = [0, 0, 329926752524, 914922541265, 464924086743, 32646588033, 0, 0] := by
  rw [show D2M8K2.u11804 = KTree.node D2M8K2.t11810 (nat_lit 25250380) (nat_lit 3912255824) (nat_lit 0) D2M8K2.t11811 from rfl, totK_node, tot11810, tot11811]
  decide +kernel

theorem arows11806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11806 = true := by
  rw [show D2M8K2.u11806 = KTree.node D2M8K2.t11812 (nat_lit 25252491) (nat_lit 2224525396) (nat_lit 0) D2M8K2.t11813 from rfl, allE_node, rows11812, irow11806, rows11813]
  all_goals rfl

theorem atot11806 : totK PD2M8K2 D2M8K2.u11806 = [0, 0, 168319464383, 690733017906, 681715395908, 144082506298, 4574395652, 0] := by
  rw [show D2M8K2.u11806 = KTree.node D2M8K2.t11812 (nat_lit 25252491) (nat_lit 2224525396) (nat_lit 0) D2M8K2.t11813 from rfl, totK_node, tot11812, tot11813]
  decide +kernel

theorem arows11807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11807 = true := by
  rw [show D2M8K2.u11807 = KTree.node D2M8K2.t11814 (nat_lit 25254518) (nat_lit 3879615552) (nat_lit 0) D2M8K2.t11815 from rfl, allE_node, rows11814, irow11807, rows11815]
  all_goals rfl

theorem atot11807 : totK PD2M8K2 D2M8K2.u11807 = [0, 175422674038, 587807729897, 703718978088, 310144481522, 19449748168, 0, 0] := by
  rw [show D2M8K2.u11807 = KTree.node D2M8K2.t11814 (nat_lit 25254518) (nat_lit 3879615552) (nat_lit 0) D2M8K2.t11815 from rfl, totK_node, tot11814, tot11815]
  decide +kernel

theorem arows11810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11810 = true := by
  rw [show D2M8K2.u11810 = KTree.node D2M8K2.t11816 (nat_lit 25299248) (nat_lit 3798690481) (nat_lit 0) D2M8K2.t11817 from rfl, allE_node, rows11816, irow11810, rows11817]
  all_goals rfl

theorem atot11810 : totK PD2M8K2 D2M8K2.u11810 = [0, 230390774409, 788442730208, 636932002593, 98206690630, 1310166938, 0, 0] := by
  rw [show D2M8K2.u11810 = KTree.node D2M8K2.t11816 (nat_lit 25299248) (nat_lit 3798690481) (nat_lit 0) D2M8K2.t11817 from rfl, totK_node, tot11816, tot11817]
  decide +kernel

theorem arows11811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11811 = true := by
  rw [show D2M8K2.u11811 = KTree.node D2M8K2.t11818 (nat_lit 25301737) (nat_lit 1033470632) (nat_lit 0) D2M8K2.t11819 from rfl, allE_node, rows11818, irow11811, rows11819]
  all_goals rfl

theorem atot11811 : totK PD2M8K2 D2M8K2.u11811 = [0, 210056841937, 786297723249, 737654687381, 83297523498, 0, 0, 0] := by
  rw [show D2M8K2.u11811 = KTree.node D2M8K2.t11818 (nat_lit 25301737) (nat_lit 1033470632) (nat_lit 0) D2M8K2.t11819 from rfl, totK_node, tot11818, tot11819]
  decide +kernel

theorem arows11813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11813 = true := by
  rw [show D2M8K2.u11813 = KTree.node D2M8K2.t11820 (nat_lit 25302949) (nat_lit 980475327) (nat_lit 0) D2M8K2.t11821 from rfl, allE_node, rows11820, irow11813, rows11821]
  all_goals rfl

theorem atot11813 : totK PD2M8K2 D2M8K2.u11813 = [0, 207786537624, 752242582474, 689716065677, 175523022127, 9631076594, 0, 0] := by
  rw [show D2M8K2.u11813 = KTree.node D2M8K2.t11820 (nat_lit 25302949) (nat_lit 980475327) (nat_lit 0) D2M8K2.t11821 from rfl, totK_node, tot11820, tot11821]
  decide +kernel

theorem arows11814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11814 = true := by
  rw [show D2M8K2.u11814 = KTree.node D2M8K2.t11822 (nat_lit 25304667) (nat_lit 3668430525) (nat_lit 0) D2M8K2.t11823 from rfl, allE_node, rows11822, irow11814, rows11823]
  all_goals rfl

theorem atot11814 : totK PD2M8K2 D2M8K2.u11814 = [0, 172251388467, 678324119724, 751126067149, 207553083245, 5382912678, 0, 0] := by
  rw [show D2M8K2.u11814 = KTree.node D2M8K2.t11822 (nat_lit 25304667) (nat_lit 3668430525) (nat_lit 0) D2M8K2.t11823 from rfl, totK_node, tot11822, tot11823]
  decide +kernel

theorem arows11818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11818 = true := by
  rw [show D2M8K2.u11818 = KTree.node D2M8K2.t11824 (nat_lit 25306281) (nat_lit 1530262024) (nat_lit 0) D2M8K2.t11825 from rfl, allE_node, rows11824, irow11818, rows11825]
  all_goals rfl

theorem atot11818 : totK PD2M8K2 D2M8K2.u11818 = [0, 252280108147, 796355270973, 648083251806, 101544557505, 1164319620, 0, 0] := by
  rw [show D2M8K2.u11818 = KTree.node D2M8K2.t11824 (nat_lit 25306281) (nat_lit 1530262024) (nat_lit 0) D2M8K2.t11825 from rfl, totK_node, tot11824, tot11825]
  decide +kernel

theorem arows11819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11819 = true := by
  rw [show D2M8K2.u11819 = KTree.node D2M8K2.t11826 (nat_lit 25308006) (nat_lit 2396088587) (nat_lit 0) D2M8K2.t11827 from rfl, allE_node, rows11826, irow11819, rows11827]
  all_goals rfl

theorem atot11819 : totK PD2M8K2 D2M8K2.u11819 = [0, 165990908636, 658762835231, 737216560965, 213656604986, 11885407614, 0, 0] := by
  rw [show D2M8K2.u11819 = KTree.node D2M8K2.t11826 (nat_lit 25308006) (nat_lit 2396088587) (nat_lit 0) D2M8K2.t11827 from rfl, totK_node, tot11826, tot11827]
  decide +kernel

theorem arows11821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11821 = true := by
  rw [show D2M8K2.u11821 = KTree.node D2M8K2.t11828 (nat_lit 25309688) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t11829 from rfl, allE_node, rows11828, irow11821, rows11829]
  all_goals rfl

theorem atot11821 : totK PD2M8K2 D2M8K2.u11821 = [0, 176587901273, 765101856706, 758280909486, 107350119927, 1104198603, 0, 0] := by
  rw [show D2M8K2.u11821 = KTree.node D2M8K2.t11828 (nat_lit 25309688) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t11829 from rfl, totK_node, tot11828, tot11829]
  decide +kernel

theorem arows11822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11822 = true := by
  rw [show D2M8K2.u11822 = KTree.node D2M8K2.t11830 (nat_lit 25312140) (nat_lit 2690613492) (nat_lit 0) D2M8K2.t11831 from rfl, allE_node, rows11830, irow11822, rows11831]
  all_goals rfl

theorem atot11822 : totK PD2M8K2 D2M8K2.u11822 = [0, 327438645702, 813887657180, 556116212265, 105481698415, 3581949829, 0, 0] := by
  rw [show D2M8K2.u11822 = KTree.node D2M8K2.t11830 (nat_lit 25312140) (nat_lit 2690613492) (nat_lit 0) D2M8K2.t11831 from rfl, totK_node, tot11830, tot11831]
  decide +kernel

theorem arows11825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11825 = true := by
  rw [show D2M8K2.u11825 = KTree.node D2M8K2.t11832 (nat_lit 25313610) (nat_lit 2737934010) (nat_lit 0) D2M8K2.t11833 from rfl, allE_node, rows11832, irow11825, rows11833]
  all_goals rfl

theorem atot11825 : totK PD2M8K2 D2M8K2.u11825 = [0, 111279211669, 732870215319, 841825501844, 123161505298, 1096505104, 0, 0] := by
  rw [show D2M8K2.u11825 = KTree.node D2M8K2.t11832 (nat_lit 25313610) (nat_lit 2737934010) (nat_lit 0) D2M8K2.t11833 from rfl, totK_node, tot11832, tot11833]
  decide +kernel

theorem arows11826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11826 = true := by
  rw [show D2M8K2.u11826 = KTree.node D2M8K2.t11834 (nat_lit 25319334) (nat_lit 2849277559) (nat_lit 0) D2M8K2.t11835 from rfl, allE_node, rows11834, irow11826, rows11835]
  all_goals rfl

theorem atot11826 : totK PD2M8K2 D2M8K2.u11826 = [0, 0, 391133603832, 965371149470, 365953963558, 15799471283, 0, 0] := by
  rw [show D2M8K2.u11826 = KTree.node D2M8K2.t11834 (nat_lit 25319334) (nat_lit 2849277559) (nat_lit 0) D2M8K2.t11835 from rfl, totK_node, tot11834, tot11835]
  decide +kernel

theorem arows11828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11828 = true := by
  rw [show D2M8K2.u11828 = KTree.node D2M8K2.t11836 (nat_lit 25321064) (nat_lit 3860982447) (nat_lit 0) D2M8K2.t11837 from rfl, allE_node, rows11836, irow11828, rows11837]
  all_goals rfl

theorem atot11828 : totK PD2M8K2 D2M8K2.u11828 = [0, 0, 156061637942, 780205625425, 673937599119, 80899932839, 1103454931, 0] := by
  rw [show D2M8K2.u11828 = KTree.node D2M8K2.t11836 (nat_lit 25321064) (nat_lit 3860982447) (nat_lit 0) D2M8K2.t11837 from rfl, totK_node, tot11836, tot11837]
  decide +kernel

theorem arows11829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11829 = true := by
  rw [show D2M8K2.u11829 = KTree.node D2M8K2.t11838 (nat_lit 25323369) (nat_lit 1917677306) (nat_lit 0) D2M8K2.t11839 from rfl, allE_node, rows11838, irow11829, rows11839]
  all_goals rfl

theorem atot11829 : totK PD2M8K2 D2M8K2.u11829 = [0, 0, 473502854527, 969734746083, 341928576616, 9410981244, 0, 0] := by
  rw [show D2M8K2.u11829 = KTree.node D2M8K2.t11838 (nat_lit 25323369) (nat_lit 1917677306) (nat_lit 0) D2M8K2.t11839 from rfl, totK_node, tot11838, tot11839]
  decide +kernel

theorem arows11835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11835 = true := by
  rw [show D2M8K2.u11835 = KTree.node D2M8K2.t11840 (nat_lit 25326820) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t11841 from rfl, allE_node, rows11840, irow11835, rows11841]
  all_goals rfl

theorem atot11835 : totK PD2M8K2 D2M8K2.u11835 = [0, 0, 345180024716, 943442908385, 439300617778, 26931641441, 0, 0] := by
  rw [show D2M8K2.u11835 = KTree.node D2M8K2.t11840 (nat_lit 25326820) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t11841 from rfl, totK_node, tot11840, tot11841]
  decide +kernel

theorem arows11836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11836 = true := by
  rw [show D2M8K2.u11836 = KTree.node D2M8K2.t11842 (nat_lit 25332539) (nat_lit 2436657498) (nat_lit 0) D2M8K2.t11843 from rfl, allE_node, rows11842, irow11836, rows11843]
  all_goals rfl

theorem atot11836 : totK PD2M8K2 D2M8K2.u11836 = [0, 0, 487085702270, 956500782334, 319672873840, 14651266580, 0, 0] := by
  rw [show D2M8K2.u11836 = KTree.node D2M8K2.t11842 (nat_lit 25332539) (nat_lit 2436657498) (nat_lit 0) D2M8K2.t11843 from rfl, totK_node, tot11842, tot11843]
  decide +kernel

theorem arows11838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11838 = true := by
  rw [show D2M8K2.u11838 = KTree.node D2M8K2.t11844 (nat_lit 25333782) (nat_lit 3459918960) (nat_lit 0) D2M8K2.t11845 from rfl, allE_node, rows11844, irow11838, rows11845]
  all_goals rfl

theorem atot11838 : totK PD2M8K2 D2M8K2.u11838 = [0, 0, 192817630493, 787600902871, 637521546495, 85021995124, 1061529118, 0] := by
  rw [show D2M8K2.u11838 = KTree.node D2M8K2.t11844 (nat_lit 25333782) (nat_lit 3459918960) (nat_lit 0) D2M8K2.t11845 from rfl, totK_node, tot11844, tot11845]
  decide +kernel

theorem arows11839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11839 = true := by
  rw [show D2M8K2.u11839 = KTree.node D2M8K2.t11846 (nat_lit 25339611) (nat_lit 1034790109) (nat_lit 0) D2M8K2.t11847 from rfl, allE_node, rows11846, irow11839, rows11847]
  all_goals rfl

theorem atot11839 : totK PD2M8K2 D2M8K2.u11839 = [0, 270182989682, 646071885140, 452775375256, 290271449311, 77687341865, 3718133097, 0] := by
  rw [show D2M8K2.u11839 = KTree.node D2M8K2.t11846 (nat_lit 25339611) (nat_lit 1034790109) (nat_lit 0) D2M8K2.t11847 from rfl, totK_node, tot11846, tot11847]
  decide +kernel

theorem arows11842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11842 = true := by
  rw [show D2M8K2.u11842 = KTree.node D2M8K2.t11848 (nat_lit 25341232) (nat_lit 3150670641) (nat_lit 0) D2M8K2.t11849 from rfl, allE_node, rows11848, irow11842, rows11849]
  all_goals rfl

theorem atot11842 : totK PD2M8K2 D2M8K2.u11842 = [0, 125195970774, 705166026136, 811601353386, 129894417726, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11842 = KTree.node D2M8K2.t11848 (nat_lit 25341232) (nat_lit 3150670641) (nat_lit 0) D2M8K2.t11849 from rfl, totK_node, tot11848, tot11849]
  decide +kernel

theorem arows11843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11843 = true := by
  rw [show D2M8K2.u11843 = KTree.node D2M8K2.t11850 (nat_lit 25343578) (nat_lit 3732917961) (nat_lit 0) D2M8K2.t11851 from rfl, allE_node, rows11850, irow11843, rows11851]
  all_goals rfl

theorem atot11843 : totK PD2M8K2 D2M8K2.u11843 = [0, 352707079676, 911436061365, 533911295290, 49553840046, 0, 0, 0] := by
  rw [show D2M8K2.u11843 = KTree.node D2M8K2.t11850 (nat_lit 25343578) (nat_lit 3732917961) (nat_lit 0) D2M8K2.t11851 from rfl, totK_node, tot11850, tot11851]
  decide +kernel

theorem arows11845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11845 = true := by
  rw [show D2M8K2.u11845 = KTree.node D2M8K2.t11852 (nat_lit 25345163) (nat_lit 2352653459) (nat_lit 0) D2M8K2.t11853 from rfl, allE_node, rows11852, irow11845, rows11853]
  all_goals rfl

theorem atot11845 : totK PD2M8K2 D2M8K2.u11845 = [0, 55017796214, 500835939192, 871647336021, 364605300717, 24685107821, 0, 0] := by
  rw [show D2M8K2.u11845 = KTree.node D2M8K2.t11852 (nat_lit 25345163) (nat_lit 2352653459) (nat_lit 0) D2M8K2.t11853 from rfl, totK_node, tot11852, tot11853]
  decide +kernel

theorem arows11846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11846 = true := by
  rw [show D2M8K2.u11846 = KTree.node D2M8K2.t11854 (nat_lit 25346552) (nat_lit 3731640598) (nat_lit 0) D2M8K2.t11855 from rfl, allE_node, rows11854, irow11846, rows11855]
  all_goals rfl

theorem atot11846 : totK PD2M8K2 D2M8K2.u11846 = [0, 263692549022, 731979365398, 613825580401, 184231745342, 8077291076, 0, 0] := by
  rw [show D2M8K2.u11846 = KTree.node D2M8K2.t11854 (nat_lit 25346552) (nat_lit 3731640598) (nat_lit 0) D2M8K2.t11855 from rfl, totK_node, tot11854, tot11855]
  decide +kernel

theorem arows11850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11850 = true := by
  rw [show D2M8K2.u11850 = KTree.node D2M8K2.t11856 (nat_lit 25348045) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t11857 from rfl, allE_node, rows11856, irow11850, rows11857]
  all_goals rfl

theorem atot11850 : totK PD2M8K2 D2M8K2.u11850 = [0, 160500127258, 700235410654, 778041492244, 157151617818, 2309606161, 0, 0] := by
  rw [show D2M8K2.u11850 = KTree.node D2M8K2.t11856 (nat_lit 25348045) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t11857 from rfl, totK_node, tot11856, tot11857]
  decide +kernel

theorem arows11851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11851 = true := by
  rw [show D2M8K2.u11851 = KTree.node D2M8K2.t11858 (nat_lit 25356920) (nat_lit 2481360301) (nat_lit 0) D2M8K2.t11859 from rfl, allE_node, rows11858, irow11851, rows11859]
  all_goals rfl

theorem atot11851 : totK PD2M8K2 D2M8K2.u11851 = [0, 261392635110, 808015558048, 621815369667, 117840285233, 7274065870, 0, 0] := by
  rw [show D2M8K2.u11851 = KTree.node D2M8K2.t11858 (nat_lit 25356920) (nat_lit 2481360301) (nat_lit 0) D2M8K2.t11859 from rfl, totK_node, tot11858, tot11859]
  decide +kernel

theorem arows11853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11853 = true := by
  rw [show D2M8K2.u11853 = KTree.node D2M8K2.t11860 (nat_lit 25358409) (nat_lit 1693974173) (nat_lit 0) D2M8K2.t11861 from rfl, allE_node, rows11860, irow11853, rows11861]
  all_goals rfl

theorem atot11853 : totK PD2M8K2 D2M8K2.u11853 = [0, 166122192533, 708754110085, 770190693302, 161016149505, 2304167554, 0, 0] := by
  rw [show D2M8K2.u11853 = KTree.node D2M8K2.t11860 (nat_lit 25358409) (nat_lit 1693974173) (nat_lit 0) D2M8K2.t11861 from rfl, totK_node, tot11860, tot11861]
  decide +kernel

theorem arows11854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11854 = true := by
  rw [show D2M8K2.u11854 = KTree.node D2M8K2.t11862 (nat_lit 25360111) (nat_lit 2134540417) (nat_lit 0) D2M8K2.t11863 from rfl, allE_node, rows11862, irow11854, rows11863]
  all_goals rfl

theorem atot11854 : totK PD2M8K2 D2M8K2.u11854 = [191552386262, 467060425676, 360321084954, 481348609914, 254856796336, 19678284834, 0, 0] := by
  rw [show D2M8K2.u11854 = KTree.node D2M8K2.t11862 (nat_lit 25360111) (nat_lit 2134540417) (nat_lit 0) D2M8K2.t11863 from rfl, totK_node, tot11862, tot11863]
  decide +kernel

theorem arows11857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11857 = true := by
  rw [show D2M8K2.u11857 = KTree.node D2M8K2.t11864 (nat_lit 25382357) (nat_lit 2375860474) (nat_lit 0) D2M8K2.t11865 from rfl, allE_node, rows11864, irow11857, rows11865]
  all_goals rfl

theorem atot11857 : totK PD2M8K2 D2M8K2.u11857 = [238181002485, 790512520880, 653489431056, 110228006387, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11857 = KTree.node D2M8K2.t11864 (nat_lit 25382357) (nat_lit 2375860474) (nat_lit 0) D2M8K2.t11865 from rfl, totK_node, tot11864, tot11865]
  decide +kernel

theorem arows11858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11858 = true := by
  rw [show D2M8K2.u11858 = KTree.node D2M8K2.t11866 (nat_lit 25387868) (nat_lit 3207783292) (nat_lit 0) D2M8K2.t11867 from rfl, allE_node, rows11866, irow11858, rows11867]
  all_goals rfl

theorem atot11858 : totK PD2M8K2 D2M8K2.u11858 = [252426960626, 824466505312, 660974419893, 68609890752, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11858 = KTree.node D2M8K2.t11866 (nat_lit 25387868) (nat_lit 3207783292) (nat_lit 0) D2M8K2.t11867 from rfl, totK_node, tot11866, tot11867]
  decide +kernel

theorem arows11860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11860 = true := by
  rw [show D2M8K2.u11860 = KTree.node D2M8K2.t11868 (nat_lit 25389751) (nat_lit 1034006354) (nat_lit 0) D2M8K2.t11869 from rfl, allE_node, rows11868, irow11860, rows11869]
  all_goals rfl

theorem atot11860 : totK PD2M8K2 D2M8K2.u11860 = [68412647006, 557295911656, 848635088605, 261747489510, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u11860 = KTree.node D2M8K2.t11868 (nat_lit 25389751) (nat_lit 1034006354) (nat_lit 0) D2M8K2.t11869 from rfl, totK_node, tot11868, tot11869]
  decide +kernel

theorem arows11861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11861 = true := by
  rw [show D2M8K2.u11861 = KTree.node D2M8K2.t11870 (nat_lit 25391796) (nat_lit 1237986660) (nat_lit 0) D2M8K2.t11871 from rfl, allE_node, rows11870, irow11861, rows11871]
  all_goals rfl

theorem atot11861 : totK PD2M8K2 D2M8K2.u11861 = [349289747127, 907733131702, 513246364404, 45717464266, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11861 = KTree.node D2M8K2.t11870 (nat_lit 25391796) (nat_lit 1237986660) (nat_lit 0) D2M8K2.t11871 from rfl, totK_node, tot11870, tot11871]
  decide +kernel

theorem arows11866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11866 = true := by
  rw [show D2M8K2.u11866 = KTree.node D2M8K2.t11872 (nat_lit 25393333) (nat_lit 1106558576) (nat_lit 0) D2M8K2.t11873 from rfl, allE_node, rows11872, irow11866, rows11873]
  all_goals rfl

theorem atot11866 : totK PD2M8K2 D2M8K2.u11866 = [74265839187, 548993682657, 878320145799, 263444794215, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u11866 = KTree.node D2M8K2.t11872 (nat_lit 25393333) (nat_lit 1106558576) (nat_lit 0) D2M8K2.t11873 from rfl, totK_node, tot11872, tot11873]
  decide +kernel

theorem arows11867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11867 = true := by
  rw [show D2M8K2.u11867 = KTree.node D2M8K2.t11874 (nat_lit 25395150) (nat_lit 3792792122) (nat_lit 0) D2M8K2.t11875 from rfl, allE_node, rows11874, irow11867, rows11875]
  all_goals rfl

theorem atot11867 : totK PD2M8K2 D2M8K2.u11867 = [320833236977, 856272414793, 533653611950, 79334089897, 2569691499, 0, 0, 0] := by
  rw [show D2M8K2.u11867 = KTree.node D2M8K2.t11874 (nat_lit 25395150) (nat_lit 3792792122) (nat_lit 0) D2M8K2.t11875 from rfl, totK_node, tot11874, tot11875]
  decide +kernel

theorem arows11869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11869 = true := by
  rw [show D2M8K2.u11869 = KTree.node D2M8K2.t11876 (nat_lit 25396730) (nat_lit 4252386283) (nat_lit 0) D2M8K2.t11877 from rfl, allE_node, rows11876, irow11869, rows11877]
  all_goals rfl

theorem atot11869 : totK PD2M8K2 D2M8K2.u11869 = [90840904916, 680563915067, 877837410852, 148583969385, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11869 = KTree.node D2M8K2.t11876 (nat_lit 25396730) (nat_lit 4252386283) (nat_lit 0) D2M8K2.t11877 from rfl, totK_node, tot11876, tot11877]
  decide +kernel

theorem arows11870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11870 = true := by
  rw [show D2M8K2.u11870 = KTree.node D2M8K2.t11878 (nat_lit 25398768) (nat_lit 3554358504) (nat_lit 0) D2M8K2.t11879 from rfl, allE_node, rows11878, irow11870, rows11879]
  all_goals rfl

theorem atot11870 : totK PD2M8K2 D2M8K2.u11870 = [363101264539, 839207328113, 483001020075, 98835872001, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u11870 = KTree.node D2M8K2.t11878 (nat_lit 25398768) (nat_lit 3554358504) (nat_lit 0) D2M8K2.t11879 from rfl, totK_node, tot11878, tot11879]
  decide +kernel

theorem arows11873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11873 = true := by
  rw [show D2M8K2.u11873 = KTree.node D2M8K2.t11880 (nat_lit 25400504) (nat_lit 3241630095) (nat_lit 0) D2M8K2.t11881 from rfl, allE_node, rows11880, irow11873, rows11881]
  all_goals rfl

theorem atot11873 : totK PD2M8K2 D2M8K2.u11873 = [19692840307, 518377006058, 936821847438, 285064394356, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u11873 = KTree.node D2M8K2.t11880 (nat_lit 25400504) (nat_lit 3241630095) (nat_lit 0) D2M8K2.t11881 from rfl, totK_node, tot11880, tot11881]
  decide +kernel

theorem arows11874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11874 = true := by
  rw [show D2M8K2.u11874 = KTree.node D2M8K2.t11882 (nat_lit 25402336) (nat_lit 3255720474) (nat_lit 0) D2M8K2.t11883 from rfl, allE_node, rows11882, irow11874, rows11883]
  all_goals rfl

theorem atot11874 : totK PD2M8K2 D2M8K2.u11874 = [0, 346480627927, 917876399495, 456057771063, 32422137020, 0, 0, 0] := by
  rw [show D2M8K2.u11874 = KTree.node D2M8K2.t11882 (nat_lit 25402336) (nat_lit 3255720474) (nat_lit 0) D2M8K2.t11883 from rfl, totK_node, tot11882, tot11883]
  decide +kernel

theorem arows11876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11876 = true := by
  rw [show D2M8K2.u11876 = KTree.node D2M8K2.t11884 (nat_lit 25403569) (nat_lit 1485859938) (nat_lit 0) D2M8K2.t11885 from rfl, allE_node, rows11884, irow11876, rows11885]
  all_goals rfl

theorem atot11876 : totK PD2M8K2 D2M8K2.u11876 = [0, 85094963948, 681869915599, 806918077906, 142731758143, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11876 = KTree.node D2M8K2.t11884 (nat_lit 25403569) (nat_lit 1485859938) (nat_lit 0) D2M8K2.t11885 from rfl, totK_node, tot11884, tot11885]
  decide +kernel

theorem arows11877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11877 = true := by
  rw [show D2M8K2.u11877 = KTree.node D2M8K2.t11886 (nat_lit 25409703) (nat_lit 3465791083) (nat_lit 0) D2M8K2.t11887 from rfl, allE_node, rows11886, irow11877, rows11887]
  all_goals rfl

theorem atot11877 : totK PD2M8K2 D2M8K2.u11877 = [0, 411207234233, 943471118209, 399427559443, 25090729337, 0, 0, 0] := by
  rw [show D2M8K2.u11877 = KTree.node D2M8K2.t11886 (nat_lit 25409703) (nat_lit 3465791083) (nat_lit 0) D2M8K2.t11887 from rfl, totK_node, tot11886, tot11887]
  decide +kernel

theorem arows11881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11881 = true := by
  rw [show D2M8K2.u11881 = KTree.node D2M8K2.t11888 (nat_lit 25413073) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t11889 from rfl, allE_node, rows11888, irow11881, rows11889]
  all_goals rfl

theorem atot11881 : totK PD2M8K2 D2M8K2.u11881 = [0, 335259814088, 950024232451, 478210544962, 21689720530, 0, 0, 0] := by
  rw [show D2M8K2.u11881 = KTree.node D2M8K2.t11888 (nat_lit 25413073) (nat_lit 1405126266) (nat_lit 0) D2M8K2.t11889 from rfl, totK_node, tot11888, tot11889]
  decide +kernel

theorem arows11882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11882 = true := by
  rw [show D2M8K2.u11882 = KTree.node D2M8K2.t11890 (nat_lit 25416108) (nat_lit 3137875246) (nat_lit 0) D2M8K2.t11891 from rfl, allE_node, rows11890, irow11882, rows11891]
  all_goals rfl

theorem atot11882 : totK PD2M8K2 D2M8K2.u11882 = [0, 410856992768, 937132682989, 406285315657, 24589251068, 0, 0, 0] := by
  rw [show D2M8K2.u11882 = KTree.node D2M8K2.t11890 (nat_lit 25416108) (nat_lit 3137875246) (nat_lit 0) D2M8K2.t11891 from rfl, totK_node, tot11890, tot11891]
  decide +kernel

theorem arows11884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11884 = true := by
  rw [show D2M8K2.u11884 = KTree.node D2M8K2.t11892 (nat_lit 25419472) (nat_lit 3414140836) (nat_lit 0) D2M8K2.t11893 from rfl, allE_node, rows11892, irow11884, rows11893]
  all_goals rfl

theorem atot11884 : totK PD2M8K2 D2M8K2.u11884 = [0, 362430963248, 958791399731, 442285140349, 18773482866, 0, 0, 0] := by
  rw [show D2M8K2.u11884 = KTree.node D2M8K2.t11892 (nat_lit 25419472) (nat_lit 3414140836) (nat_lit 0) D2M8K2.t11893 from rfl, totK_node, tot11892, tot11893]
  decide +kernel

theorem arows11885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11885 = true := by
  rw [show D2M8K2.u11885 = KTree.node D2M8K2.t11894 (nat_lit 25426433) (nat_lit 2223004315) (nat_lit 0) D2M8K2.t11895 from rfl, allE_node, rows11894, irow11885, rows11895]
  all_goals rfl

theorem atot11885 : totK PD2M8K2 D2M8K2.u11885 = [336184739765, 797703707867, 538714797714, 156290641561, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u11885 = KTree.node D2M8K2.t11894 (nat_lit 25426433) (nat_lit 2223004315) (nat_lit 0) D2M8K2.t11895 from rfl, totK_node, tot11894, tot11895]
  decide +kernel

theorem arows11888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11888 = true := by
  rw [show D2M8K2.u11888 = KTree.node D2M8K2.t11896 (nat_lit 25427929) (nat_lit 934040467) (nat_lit 0) D2M8K2.t11897 from rfl, allE_node, rows11896, irow11888, rows11897]
  all_goals rfl

theorem atot11888 : totK PD2M8K2 D2M8K2.u11888 = [106385935448, 613798683147, 783480877758, 295487426706, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u11888 = KTree.node D2M8K2.t11896 (nat_lit 25427929) (nat_lit 934040467) (nat_lit 0) D2M8K2.t11897 from rfl, totK_node, tot11896, tot11897]
  decide +kernel

theorem arows11889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11889 = true := by
  rw [show D2M8K2.u11889 = KTree.node D2M8K2.t11898 (nat_lit 25429160) (nat_lit 2373320058) (nat_lit 0) D2M8K2.t11899 from rfl, allE_node, rows11898, irow11889, rows11899]
  all_goals rfl

theorem atot11889 : totK PD2M8K2 D2M8K2.u11889 = [177873774604, 572040148045, 764681864360, 300013883639, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u11889 = KTree.node D2M8K2.t11898 (nat_lit 25429160) (nat_lit 2373320058) (nat_lit 0) D2M8K2.t11899 from rfl, totK_node, tot11898, tot11899]
  decide +kernel

theorem arows11891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11891 = true := by
  rw [show D2M8K2.u11891 = KTree.node D2M8K2.t11900 (nat_lit 25430974) (nat_lit 3906092754) (nat_lit 0) D2M8K2.t11901 from rfl, allE_node, rows11900, irow11891, rows11901]
  all_goals rfl

theorem atot11891 : totK PD2M8K2 D2M8K2.u11891 = [153428177587, 717294519219, 767631180110, 170803049855, 8390071763, 0, 0, 0] := by
  rw [show D2M8K2.u11891 = KTree.node D2M8K2.t11900 (nat_lit 25430974) (nat_lit 3906092754) (nat_lit 0) D2M8K2.t11901 from rfl, totK_node, tot11900, tot11901]
  decide +kernel

theorem arows11892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11892 = true := by
  rw [show D2M8K2.u11892 = KTree.node D2M8K2.t11902 (nat_lit 25433129) (nat_lit 1495184172) (nat_lit 0) D2M8K2.t11903 from rfl, allE_node, rows11902, irow11892, rows11903]
  all_goals rfl

theorem atot11892 : totK PD2M8K2 D2M8K2.u11892 = [324051653101, 826493160515, 563370838654, 108036778998, 3443453901, 0, 0, 0] := by
  rw [show D2M8K2.u11892 = KTree.node D2M8K2.t11902 (nat_lit 25433129) (nat_lit 1495184172) (nat_lit 0) D2M8K2.t11903 from rfl, totK_node, tot11902, tot11903]
  decide +kernel

theorem arows11899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11899 = true := by
  rw [show D2M8K2.u11899 = KTree.node D2M8K2.t11904 (nat_lit 25434594) (nat_lit 2778954591) (nat_lit 0) D2M8K2.t11905 from rfl, allE_node, rows11904, irow11899, rows11905]
  all_goals rfl

theorem atot11899 : totK PD2M8K2 D2M8K2.u11899 = [101166807539, 633499978376, 823660671444, 220057314264, 9661765460, 0, 0, 0] := by
  rw [show D2M8K2.u11899 = KTree.node D2M8K2.t11904 (nat_lit 25434594) (nat_lit 2778954591) (nat_lit 0) D2M8K2.t11905 from rfl, totK_node, tot11904, tot11905]
  decide +kernel

theorem arows11900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11900 = true := by
  rw [show D2M8K2.u11900 = KTree.node D2M8K2.t11906 (nat_lit 25436505) (nat_lit 1834796014) (nat_lit 0) D2M8K2.t11907 from rfl, allE_node, rows11906, irow11900, rows11907]
  all_goals rfl

theorem atot11900 : totK PD2M8K2 D2M8K2.u11900 = [271363896511, 778500279272, 627937119753, 125834837415, 3575904516, 0, 0, 0] := by
  rw [show D2M8K2.u11900 = KTree.node D2M8K2.t11906 (nat_lit 25436505) (nat_lit 1834796014) (nat_lit 0) D2M8K2.t11907 from rfl, totK_node, tot11906, tot11907]
  decide +kernel

theorem arows11902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11902 = true := by
  rw [show D2M8K2.u11902 = KTree.node D2M8K2.t11908 (nat_lit 25437981) (nat_lit 1555880650) (nat_lit 0) D2M8K2.t11909 from rfl, allE_node, rows11908, irow11902, rows11909]
  all_goals rfl

theorem atot11902 : totK PD2M8K2 D2M8K2.u11902 = [142936575108, 744172878982, 804231425122, 124272676145, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u11902 = KTree.node D2M8K2.t11908 (nat_lit 25437981) (nat_lit 1555880650) (nat_lit 0) D2M8K2.t11909 from rfl, totK_node, tot11908, tot11909]
  decide +kernel

theorem arows11903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11903 = true := by
  rw [show D2M8K2.u11903 = KTree.node D2M8K2.t11910 (nat_lit 25440089) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t11911 from rfl, allE_node, rows11910, irow11903, rows11911]
  all_goals rfl

theorem atot11903 : totK PD2M8K2 D2M8K2.u11903 = [296623182143, 809830319758, 593288090131, 123835427389, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u11903 = KTree.node D2M8K2.t11910 (nat_lit 25440089) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t11911 from rfl, totK_node, tot11910, tot11911]
  decide +kernel

theorem arows11906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11906 = true := by
  rw [show D2M8K2.u11906 = KTree.node D2M8K2.t11912 (nat_lit 25441711) (nat_lit 2410620835) (nat_lit 0) D2M8K2.t11913 from rfl, allE_node, rows11912, irow11906, rows11913]
  all_goals rfl

theorem atot11906 : totK PD2M8K2 D2M8K2.u11906 = [90526578066, 588966486344, 861402595485, 247543241702, 7589564108, 0, 0, 0] := by
  rw [show D2M8K2.u11906 = KTree.node D2M8K2.t11912 (nat_lit 25441711) (nat_lit 2410620835) (nat_lit 0) D2M8K2.t11913 from rfl, totK_node, tot11912, tot11913]
  decide +kernel

theorem arows11907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11907 = true := by
  rw [show D2M8K2.u11907 = KTree.node D2M8K2.t11914 (nat_lit 25447099) (nat_lit 1165473726) (nat_lit 0) D2M8K2.t11915 from rfl, allE_node, rows11914, irow11907, rows11915]
  all_goals rfl

theorem atot11907 : totK PD2M8K2 D2M8K2.u11907 = [0, 347247262751, 904513182308, 526236139530, 48198963659, 0, 0, 0] := by
  rw [show D2M8K2.u11907 = KTree.node D2M8K2.t11914 (nat_lit 25447099) (nat_lit 1165473726) (nat_lit 0) D2M8K2.t11915 from rfl, totK_node, tot11914, tot11915]
  decide +kernel

theorem arows11909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11909 = true := by
  rw [show D2M8K2.u11909 = KTree.node D2M8K2.t11916 (nat_lit 25448609) (nat_lit 2097071108) (nat_lit 0) D2M8K2.t11917 from rfl, allE_node, rows11916, irow11909, rows11917]
  all_goals rfl

theorem atot11909 : totK PD2M8K2 D2M8K2.u11909 = [0, 145614629867, 635493451350, 727589154829, 277933634264, 25191558099, 0, 0] := by
  rw [show D2M8K2.u11909 = KTree.node D2M8K2.t11916 (nat_lit 25448609) (nat_lit 2097071108) (nat_lit 0) D2M8K2.t11917 from rfl, totK_node, tot11916, tot11917]
  decide +kernel

theorem arows11910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11910 = true := by
  rw [show D2M8K2.u11910 = KTree.node D2M8K2.t11918 (nat_lit 25449826) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t11919 from rfl, allE_node, rows11918, irow11910, rows11919]
  all_goals rfl

theorem atot11910 : totK PD2M8K2 D2M8K2.u11910 = [0, 170815217169, 566665762754, 775696924833, 285870657080, 11730315755, 0, 0] := by
  rw [show D2M8K2.u11910 = KTree.node D2M8K2.t11918 (nat_lit 25449826) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t11919 from rfl, totK_node, tot11918, tot11919]
  decide +kernel

theorem arows11914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11914 = true := by
  rw [show D2M8K2.u11914 = KTree.node D2M8K2.t11920 (nat_lit 25451642) (nat_lit 3921280757) (nat_lit 0) D2M8K2.t11921 from rfl, allE_node, rows11920, irow11914, rows11921]
  all_goals rfl

theorem atot11914 : totK PD2M8K2 D2M8K2.u11914 = [0, 159649504657, 740941337600, 758964439054, 148533260616, 4009909289, 0, 0] := by
  rw [show D2M8K2.u11914 = KTree.node D2M8K2.t11920 (nat_lit 25451642) (nat_lit 3921280757) (nat_lit 0) D2M8K2.t11921 from rfl, totK_node, tot11920, tot11921]
  decide +kernel

theorem arows11915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11915 = true := by
  rw [show D2M8K2.u11915 = KTree.node D2M8K2.t11922 (nat_lit 25453853) (nat_lit 2002073016) (nat_lit 0) D2M8K2.t11923 from rfl, allE_node, rows11922, irow11915, rows11923]
  all_goals rfl

theorem atot11915 : totK PD2M8K2 D2M8K2.u11915 = [0, 319318248081, 824352835184, 581218934243, 96572057549, 1149959346, 0, 0] := by
  rw [show D2M8K2.u11915 = KTree.node D2M8K2.t11922 (nat_lit 25453853) (nat_lit 2002073016) (nat_lit 0) D2M8K2.t11923 from rfl, totK_node, tot11922, tot11923]
  decide +kernel

theorem arows11917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11917 = true := by
  rw [show D2M8K2.u11917 = KTree.node D2M8K2.t11924 (nat_lit 25455512) (nat_lit 3490419788) (nat_lit 0) D2M8K2.t11925 from rfl, allE_node, rows11924, irow11917, rows11925]
  all_goals rfl

theorem atot11917 : totK PD2M8K2 D2M8K2.u11917 = [0, 104314460792, 677785111661, 826568620531, 169357374707, 4031931762, 0, 0] := by
  rw [show D2M8K2.u11917 = KTree.node D2M8K2.t11924 (nat_lit 25455512) (nat_lit 3490419788) (nat_lit 0) D2M8K2.t11925 from rfl, totK_node, tot11924, tot11925]
  decide +kernel

theorem arows11918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11918 = true := by
  rw [show D2M8K2.u11918 = KTree.node D2M8K2.t11926 (nat_lit 25457375) (nat_lit 2026167334) (nat_lit 0) D2M8K2.t11927 from rfl, allE_node, rows11926, irow11918, rows11927]
  all_goals rfl

theorem atot11918 : totK PD2M8K2 D2M8K2.u11918 = [0, 322371748181, 857316458829, 545010572357, 79670275241, 1186940923, 0, 0] := by
  rw [show D2M8K2.u11918 = KTree.node D2M8K2.t11926 (nat_lit 25457375) (nat_lit 2026167334) (nat_lit 0) D2M8K2.t11927 from rfl, totK_node, tot11926, tot11927]
  decide +kernel

theorem arows11921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11921 = true := by
  rw [show D2M8K2.u11921 = KTree.node D2M8K2.t11928 (nat_lit 25459024) (nat_lit 3329647725) (nat_lit 0) D2M8K2.t11929 from rfl, allE_node, rows11928, irow11921, rows11929]
  all_goals rfl

theorem atot11921 : totK PD2M8K2 D2M8K2.u11921 = [0, 97508695222, 687563575465, 875337949596, 147928286402, 1415142070, 0, 0] := by
  rw [show D2M8K2.u11921 = KTree.node D2M8K2.t11928 (nat_lit 25459024) (nat_lit 3329647725) (nat_lit 0) D2M8K2.t11929 from rfl, totK_node, tot11928, tot11929]
  decide +kernel

theorem arows11922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11922 = true := by
  rw [show D2M8K2.u11922 = KTree.node D2M8K2.t11930 (nat_lit 25461067) (nat_lit 1481904274) (nat_lit 0) D2M8K2.t11931 from rfl, allE_node, rows11930, irow11922, rows11931]
  all_goals rfl

theorem atot11922 : totK PD2M8K2 D2M8K2.u11922 = [0, 375874771608, 937497137452, 483686103998, 36510742237, 0, 0, 0] := by
  rw [show D2M8K2.u11922 = KTree.node D2M8K2.t11930 (nat_lit 25461067) (nat_lit 1481904274) (nat_lit 0) D2M8K2.t11931 from rfl, totK_node, tot11930, tot11931]
  decide +kernel

theorem arows11924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11924 = true := by
  rw [show D2M8K2.u11924 = KTree.node D2M8K2.t11932 (nat_lit 25463024) (nat_lit 3407881143) (nat_lit 0) D2M8K2.t11933 from rfl, allE_node, rows11932, irow11924, rows11933]
  all_goals rfl

theorem atot11924 : totK PD2M8K2 D2M8K2.u11924 = [78840680958, 114310399466, 444334019979, 856630991417, 277447180775, 9302370699, 0, 0] := by
  rw [show D2M8K2.u11924 = KTree.node D2M8K2.t11932 (nat_lit 25463024) (nat_lit 3407881143) (nat_lit 0) D2M8K2.t11933 from rfl, totK_node, tot11932, tot11933]
  decide +kernel

theorem arows11925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11925 = true := by
  rw [show D2M8K2.u11925 = KTree.node D2M8K2.t11934 (nat_lit 25506380) (nat_lit 3186690631) (nat_lit 0) D2M8K2.t11935 from rfl, allE_node, rows11934, irow11925, rows11935]
  all_goals rfl

theorem atot11925 : totK PD2M8K2 D2M8K2.u11925 = [330701195045, 921291527816, 485537463898, 28736742233, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11925 = KTree.node D2M8K2.t11934 (nat_lit 25506380) (nat_lit 3186690631) (nat_lit 0) D2M8K2.t11935 from rfl, totK_node, tot11934, tot11935]
  decide +kernel

theorem arows11930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11930 = true := by
  rw [show D2M8K2.u11930 = KTree.node D2M8K2.t11936 (nat_lit 25508180) (nat_lit 3285357013) (nat_lit 0) D2M8K2.t11937 from rfl, allE_node, rows11936, irow11930, rows11937]
  all_goals rfl

theorem atot11930 : totK PD2M8K2 D2M8K2.u11930 = [93305483181, 661242953294, 894425910470, 163540287496, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11930 = KTree.node D2M8K2.t11936 (nat_lit 25508180) (nat_lit 3285357013) (nat_lit 0) D2M8K2.t11937 from rfl, totK_node, tot11936, tot11937]
  decide +kernel

theorem arows11931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11931 = true := by
  rw [show D2M8K2.u11931 = KTree.node D2M8K2.t11938 (nat_lit 25509937) (nat_lit 1121681490) (nat_lit 0) D2M8K2.t11939 from rfl, allE_node, rows11938, irow11931, rows11939]
  all_goals rfl

theorem atot11931 : totK PD2M8K2 D2M8K2.u11931 = [330393042040, 906287833040, 528543489030, 50336326117, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11931 = KTree.node D2M8K2.t11938 (nat_lit 25509937) (nat_lit 1121681490) (nat_lit 0) D2M8K2.t11939 from rfl, totK_node, tot11938, tot11939]
  decide +kernel

theorem arows11933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11933 = true := by
  rw [show D2M8K2.u11933 = KTree.node D2M8K2.t11940 (nat_lit 25511445) (nat_lit 1730766126) (nat_lit 0) D2M8K2.t11941 from rfl, allE_node, rows11940, irow11933, rows11941]
  all_goals rfl

theorem atot11933 : totK PD2M8K2 D2M8K2.u11933 = [0, 370218571643, 952332245516, 454937944058, 30761172332, 0, 0, 0] := by
  rw [show D2M8K2.u11933 = KTree.node D2M8K2.t11940 (nat_lit 25511445) (nat_lit 1730766126) (nat_lit 0) D2M8K2.t11941 from rfl, totK_node, tot11940, tot11941]
  decide +kernel

theorem arows11934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11934 = true := by
  rw [show D2M8K2.u11934 = KTree.node D2M8K2.t11942 (nat_lit 25516163) (nat_lit 2736703174) (nat_lit 0) D2M8K2.t11943 from rfl, allE_node, rows11942, irow11934, rows11943]
  all_goals rfl

theorem atot11934 : totK PD2M8K2 D2M8K2.u11934 = [357754573816, 874610241904, 485225240348, 104433158510, 6630726990, 0, 0, 0] := by
  rw [show D2M8K2.u11934 = KTree.node D2M8K2.t11942 (nat_lit 25516163) (nat_lit 2736703174) (nat_lit 0) D2M8K2.t11943 from rfl, totK_node, tot11942, tot11943]
  decide +kernel

theorem arows11937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11937 = true := by
  rw [show D2M8K2.u11937 = KTree.node D2M8K2.t11944 (nat_lit 25517647) (nat_lit 1807601626) (nat_lit 0) D2M8K2.t11945 from rfl, allE_node, rows11944, irow11937, rows11945]
  all_goals rfl

theorem atot11937 : totK PD2M8K2 D2M8K2.u11937 = [88301595136, 611085936392, 871414811854, 231334286425, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u11937 = KTree.node D2M8K2.t11944 (nat_lit 25517647) (nat_lit 1807601626) (nat_lit 0) D2M8K2.t11945 from rfl, totK_node, tot11944, tot11945]
  decide +kernel

theorem arows11938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11938 = true := by
  rw [show D2M8K2.u11938 = KTree.node D2M8K2.t11946 (nat_lit 25519448) (nat_lit 3721919425) (nat_lit 0) D2M8K2.t11947 from rfl, allE_node, rows11946, irow11938, rows11947]
  all_goals rfl

theorem atot11938 : totK PD2M8K2 D2M8K2.u11938 = [295256932139, 778495881875, 594277638932, 119988931677, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u11938 = KTree.node D2M8K2.t11946 (nat_lit 25519448) (nat_lit 3721919425) (nat_lit 0) D2M8K2.t11947 from rfl, totK_node, tot11946, tot11947]
  decide +kernel

theorem arows11940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11940 = true := by
  rw [show D2M8K2.u11940 = KTree.node D2M8K2.t11948 (nat_lit 25520941) (nat_lit 1130304457) (nat_lit 0) D2M8K2.t11949 from rfl, allE_node, rows11948, irow11940, rows11949]
  all_goals rfl

theorem atot11940 : totK PD2M8K2 D2M8K2.u11940 = [125022379307, 738066340538, 825297241808, 125401806181, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11940 = KTree.node D2M8K2.t11948 (nat_lit 25520941) (nat_lit 1130304457) (nat_lit 0) D2M8K2.t11949 from rfl, totK_node, tot11948, tot11949]
  decide +kernel

theorem arows11941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11941 = true := by
  rw [show D2M8K2.u11941 = KTree.node D2M8K2.t11950 (nat_lit 25522942) (nat_lit 3868341862) (nat_lit 0) D2M8K2.t11951 from rfl, allE_node, rows11950, irow11941, rows11951]
  all_goals rfl

theorem atot11941 : totK PD2M8K2 D2M8K2.u11941 = [312485795603, 812840438386, 551232346935, 114047052536, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u11941 = KTree.node D2M8K2.t11950 (nat_lit 25522942) (nat_lit 3868341862) (nat_lit 0) D2M8K2.t11951 from rfl, totK_node, tot11950, tot11951]
  decide +kernel

theorem arows11945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11945 = true := by
  rw [show D2M8K2.u11945 = KTree.node D2M8K2.t11952 (nat_lit 25524505) (nat_lit 1459118305) (nat_lit 0) D2M8K2.t11953 from rfl, allE_node, rows11952, irow11945, rows11953]
  all_goals rfl

theorem atot11945 : totK PD2M8K2 D2M8K2.u11945 = [91570829045, 598206083340, 861992801272, 224640679677, 3368571557, 0, 0, 0] := by
  rw [show D2M8K2.u11945 = KTree.node D2M8K2.t11952 (nat_lit 25524505) (nat_lit 1459118305) (nat_lit 0) D2M8K2.t11953 from rfl, totK_node, tot11952, tot11953]
  decide +kernel

theorem arows11946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11946 = true := by
  rw [show D2M8K2.u11946 = KTree.node D2M8K2.t11954 (nat_lit 25526257) (nat_lit 1499128955) (nat_lit 0) D2M8K2.t11955 from rfl, allE_node, rows11954, irow11946, rows11955]
  all_goals rfl

theorem atot11946 : totK PD2M8K2 D2M8K2.u11946 = [0, 375372291919, 931363740793, 430689592517, 26990637955, 0, 0, 0] := by
  rw [show D2M8K2.u11946 = KTree.node D2M8K2.t11954 (nat_lit 25526257) (nat_lit 1499128955) (nat_lit 0) D2M8K2.t11955 from rfl, totK_node, tot11954, tot11955]
  decide +kernel

theorem arows11948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11948 = true := by
  rw [show D2M8K2.u11948 = KTree.node D2M8K2.t11956 (nat_lit 25527848) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t11957 from rfl, allE_node, rows11956, irow11948, rows11957]
  all_goals rfl

theorem atot11948 : totK PD2M8K2 D2M8K2.u11948 = [0, 126923202586, 727907323264, 766179629808, 104344589333, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11948 = KTree.node D2M8K2.t11956 (nat_lit 25527848) (nat_lit 3841917883) (nat_lit 0) D2M8K2.t11957 from rfl, totK_node, tot11956, tot11957]
  decide +kernel

theorem arows11949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11949 = true := by
  rw [show D2M8K2.u11949 = KTree.node D2M8K2.t11958 (nat_lit 25530295) (nat_lit 1269709843) (nat_lit 0) D2M8K2.t11959 from rfl, allE_node, rows11958, irow11949, rows11959]
  all_goals rfl

theorem atot11949 : totK PD2M8K2 D2M8K2.u11949 = [0, 349774477503, 913968089495, 521694923653, 45193288160, 0, 0, 0] := by
  rw [show D2M8K2.u11949 = KTree.node D2M8K2.t11958 (nat_lit 25530295) (nat_lit 1269709843) (nat_lit 0) D2M8K2.t11959 from rfl, totK_node, tot11958, tot11959]
  decide +kernel

theorem arows11952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11952 = true := by
  rw [show D2M8K2.u11952 = KTree.node D2M8K2.t11960 (nat_lit 25536734) (nat_lit 3918564793) (nat_lit 0) D2M8K2.t11961 from rfl, allE_node, rows11960, irow11952, rows11961]
  all_goals rfl

theorem atot11952 : totK PD2M8K2 D2M8K2.u11952 = [0, 358462671783, 925256438360, 495680485681, 39951563590, 0, 0, 0] := by
  rw [show D2M8K2.u11952 = KTree.node D2M8K2.t11960 (nat_lit 25536734) (nat_lit 3918564793) (nat_lit 0) D2M8K2.t11961 from rfl, totK_node, tot11960, tot11961]
  decide +kernel

theorem arows11953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11953 = true := by
  rw [show D2M8K2.u11953 = KTree.node D2M8K2.t11962 (nat_lit 25538184) (nat_lit 3599962255) (nat_lit 0) D2M8K2.t11963 from rfl, allE_node, rows11962, irow11953, rows11963]
  all_goals rfl

theorem atot11953 : totK PD2M8K2 D2M8K2.u11953 = [0, 153667419549, 681282853511, 749242532725, 181838144846, 7203532459, 0, 0] := by
  rw [show D2M8K2.u11953 = KTree.node D2M8K2.t11962 (nat_lit 25538184) (nat_lit 3599962255) (nat_lit 0) D2M8K2.t11963 from rfl, totK_node, tot11962, tot11963]
  decide +kernel

theorem arows11955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11955 = true := by
  rw [show D2M8K2.u11955 = KTree.node D2M8K2.t11964 (nat_lit 25539992) (nat_lit 3522529939) (nat_lit 0) D2M8K2.t11965 from rfl, allE_node, rows11964, irow11955, rows11965]
  all_goals rfl

theorem atot11955 : totK PD2M8K2 D2M8K2.u11955 = [0, 238437018067, 778142168530, 611869650685, 121507834787, 4923312241, 0, 0] := by
  rw [show D2M8K2.u11955 = KTree.node D2M8K2.t11964 (nat_lit 25539992) (nat_lit 3522529939) (nat_lit 0) D2M8K2.t11965 from rfl, totK_node, tot11964, tot11965]
  decide +kernel

theorem arows11956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11956 = true := by
  rw [show D2M8K2.u11956 = KTree.node D2M8K2.t11966 (nat_lit 25541588) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t11967 from rfl, allE_node, rows11966, irow11956, rows11967]
  all_goals rfl

theorem atot11956 : totK PD2M8K2 D2M8K2.u11956 = [0, 176102677452, 779173381063, 715559922736, 93278212678, 1053411165, 0, 0] := by
  rw [show D2M8K2.u11956 = KTree.node D2M8K2.t11966 (nat_lit 25541588) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t11967 from rfl, totK_node, tot11966, tot11967]
  decide +kernel

theorem arows11962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11962 = true := by
  rw [show D2M8K2.u11962 = KTree.node D2M8K2.t11968 (nat_lit 25543664) (nat_lit 3471514717) (nat_lit 0) D2M8K2.t11969 from rfl, allE_node, rows11968, irow11962, rows11969]
  all_goals rfl

theorem atot11962 : totK PD2M8K2 D2M8K2.u11962 = [0, 311069621982, 802055257445, 544492875210, 98070960797, 3667207281, 0, 0] := by
  rw [show D2M8K2.u11962 = KTree.node D2M8K2.t11968 (nat_lit 25543664) (nat_lit 3471514717) (nat_lit 0) D2M8K2.t11969 from rfl, totK_node, tot11968, tot11969]
  decide +kernel

theorem arows11963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11963 = true := by
  rw [show D2M8K2.u11963 = KTree.node D2M8K2.t11970 (nat_lit 25546908) (nat_lit 3511600203) (nat_lit 0) D2M8K2.t11971 from rfl, allE_node, rows11970, irow11963, rows11971]
  all_goals rfl

theorem atot11963 : totK PD2M8K2 D2M8K2.u11963 = [254098032854, 711453270804, 584054879621, 227730973471, 20798538164, 0, 0, 0] := by
  rw [show D2M8K2.u11963 = KTree.node D2M8K2.t11970 (nat_lit 25546908) (nat_lit 3511600203) (nat_lit 0) D2M8K2.t11971 from rfl, totK_node, tot11970, tot11971]
  decide +kernel

theorem arows11965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11965 = true := by
  rw [show D2M8K2.u11965 = KTree.node D2M8K2.t11972 (nat_lit 25548530) (nat_lit 2534478782) (nat_lit 0) D2M8K2.t11973 from rfl, allE_node, rows11972, irow11965, rows11973]
  all_goals rfl

theorem atot11965 : totK PD2M8K2 D2M8K2.u11965 = [152982732611, 717730514115, 771934766332, 131322557466, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u11965 = KTree.node D2M8K2.t11972 (nat_lit 25548530) (nat_lit 2534478782) (nat_lit 0) D2M8K2.t11973 from rfl, totK_node, tot11972, tot11973]
  decide +kernel

theorem arows11966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11966 = true := by
  rw [show D2M8K2.u11966 = KTree.node D2M8K2.t11974 (nat_lit 25550834) (nat_lit 4093144090) (nat_lit 0) D2M8K2.t11975 from rfl, allE_node, rows11974, irow11966, rows11975]
  all_goals rfl

theorem atot11966 : totK PD2M8K2 D2M8K2.u11966 = [319508034115, 857994998002, 584185100802, 65578102081, 0, 0, 0, 0] := by
  rw [show D2M8K2.u11966 = KTree.node D2M8K2.t11974 (nat_lit 25550834) (nat_lit 4093144090) (nat_lit 0) D2M8K2.t11975 from rfl, totK_node, tot11974, tot11975]
  decide +kernel

theorem arows11969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11969 = true := by
  rw [show D2M8K2.u11969 = KTree.node D2M8K2.t11976 (nat_lit 25552403) (nat_lit 2702778676) (nat_lit 0) D2M8K2.t11977 from rfl, allE_node, rows11976, irow11969, rows11977]
  all_goals rfl

theorem atot11969 : totK PD2M8K2 D2M8K2.u11969 = [94864624234, 580779554493, 804428049997, 314226452188, 25358898171, 0, 0, 0] := by
  rw [show D2M8K2.u11969 = KTree.node D2M8K2.t11976 (nat_lit 25552403) (nat_lit 2702778676) (nat_lit 0) D2M8K2.t11977 from rfl, totK_node, tot11976, tot11977]
  decide +kernel

theorem arows11970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11970 = true := by
  rw [show D2M8K2.u11970 = KTree.node D2M8K2.t11978 (nat_lit 25553680) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t11979 from rfl, allE_node, rows11978, irow11970, rows11979]
  all_goals rfl

theorem atot11970 : totK PD2M8K2 D2M8K2.u11970 = [202588200404, 637548095288, 694076765816, 269710816749, 12058116921, 0, 0, 0] := by
  rw [show D2M8K2.u11970 = KTree.node D2M8K2.t11978 (nat_lit 25553680) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t11979 from rfl, totK_node, tot11978, tot11979]
  decide +kernel

theorem arows11972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11972 = true := by
  rw [show D2M8K2.u11972 = KTree.node D2M8K2.t11980 (nat_lit 25555494) (nat_lit 3315025756) (nat_lit 0) D2M8K2.t11981 from rfl, allE_node, rows11980, irow11972, rows11981]
  all_goals rfl

theorem atot11972 : totK PD2M8K2 D2M8K2.u11972 = [140648108908, 665874357799, 771943509052, 203532051853, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u11972 = KTree.node D2M8K2.t11980 (nat_lit 25555494) (nat_lit 3315025756) (nat_lit 0) D2M8K2.t11981 from rfl, totK_node, tot11980, tot11981]
  decide +kernel

theorem arows11973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11973 = true := by
  rw [show D2M8K2.u11973 = KTree.node D2M8K2.t11982 (nat_lit 25557505) (nat_lit 1220878859) (nat_lit 0) D2M8K2.t11983 from rfl, allE_node, rows11982, irow11973, rows11983]
  all_goals rfl

theorem atot11973 : totK PD2M8K2 D2M8K2.u11973 = [308947465393, 813214412908, 580997072304, 105377272632, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u11973 = KTree.node D2M8K2.t11982 (nat_lit 25557505) (nat_lit 1220878859) (nat_lit 0) D2M8K2.t11983 from rfl, totK_node, tot11982, tot11983]
  decide +kernel

theorem arows11977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11977 = true := by
  rw [show D2M8K2.u11977 = KTree.node D2M8K2.t11984 (nat_lit 25558990) (nat_lit 3802166889) (nat_lit 0) D2M8K2.t11985 from rfl, allE_node, rows11984, irow11977, rows11985]
  all_goals rfl

theorem atot11977 : totK PD2M8K2 D2M8K2.u11977 = [113317089915, 639930743078, 808445724183, 216484145439, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u11977 = KTree.node D2M8K2.t11984 (nat_lit 25558990) (nat_lit 3802166889) (nat_lit 0) D2M8K2.t11985 from rfl, totK_node, tot11984, tot11985]
  decide +kernel

theorem arows11978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11978 = true := by
  rw [show D2M8K2.u11978 = KTree.node D2M8K2.t11986 (nat_lit 25560824) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11987 from rfl, allE_node, rows11986, irow11978, rows11987]
  all_goals rfl

theorem atot11978 : totK PD2M8K2 D2M8K2.u11978 = [258390828352, 777411259253, 636680469963, 129179070884, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u11978 = KTree.node D2M8K2.t11986 (nat_lit 25560824) (nat_lit 3862132601) (nat_lit 0) D2M8K2.t11987 from rfl, totK_node, tot11986, tot11987]
  decide +kernel

theorem arows11980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11980 = true := by
  rw [show D2M8K2.u11980 = KTree.node D2M8K2.t11988 (nat_lit 25562310) (nat_lit 3735160554) (nat_lit 0) D2M8K2.t11989 from rfl, allE_node, rows11988, irow11980, rows11989]
  all_goals rfl

theorem atot11980 : totK PD2M8K2 D2M8K2.u11980 = [181015165609, 763099873312, 760161396889, 116607635186, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u11980 = KTree.node D2M8K2.t11988 (nat_lit 25562310) (nat_lit 3735160554) (nat_lit 0) D2M8K2.t11989 from rfl, totK_node, tot11988, tot11989]
  decide +kernel

theorem arows11981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11981 = true := by
  rw [show D2M8K2.u11981 = KTree.node D2M8K2.t11990 (nat_lit 25567713) (nat_lit 1737235550) (nat_lit 0) D2M8K2.t11991 from rfl, allE_node, rows11990, irow11981, rows11991]
  all_goals rfl

theorem atot11981 : totK PD2M8K2 D2M8K2.u11981 = [0, 399853083224, 950302149428, 394438367587, 22145572651, 0, 0, 0] := by
  rw [show D2M8K2.u11981 = KTree.node D2M8K2.t11990 (nat_lit 25567713) (nat_lit 1737235550) (nat_lit 0) D2M8K2.t11991 from rfl, totK_node, tot11990, tot11991]
  decide +kernel

theorem arows11984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11984 = true := by
  rw [show D2M8K2.u11984 = KTree.node D2M8K2.t11992 (nat_lit 25569332) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t11993 from rfl, allE_node, rows11992, irow11984, rows11993]
  all_goals rfl

theorem atot11984 : totK PD2M8K2 D2M8K2.u11984 = [0, 148608975348, 772360520327, 712126878372, 92846287508, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11984 = KTree.node D2M8K2.t11992 (nat_lit 25569332) (nat_lit 3476848073) (nat_lit 0) D2M8K2.t11993 from rfl, totK_node, tot11992, tot11993]
  decide +kernel

theorem arows11985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11985 = true := by
  rw [show D2M8K2.u11985 = KTree.node D2M8K2.t11994 (nat_lit 25571814) (nat_lit 3822693604) (nat_lit 0) D2M8K2.t11995 from rfl, allE_node, rows11994, irow11985, rows11995]
  all_goals rfl

theorem atot11985 : totK PD2M8K2 D2M8K2.u11985 = [0, 377906543060, 943931893148, 471889956823, 39317757797, 0, 0, 0] := by
  rw [show D2M8K2.u11985 = KTree.node D2M8K2.t11994 (nat_lit 25571814) (nat_lit 3822693604) (nat_lit 0) D2M8K2.t11995 from rfl, totK_node, tot11994, tot11995]
  decide +kernel

theorem arows11987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11987 = true := by
  rw [show D2M8K2.u11987 = KTree.node D2M8K2.t11996 (nat_lit 25574867) (nat_lit 2563302657) (nat_lit 0) D2M8K2.t11997 from rfl, allE_node, rows11996, irow11987, rows11997]
  all_goals rfl

theorem atot11987 : totK PD2M8K2 D2M8K2.u11987 = [0, 377107717087, 939894753275, 461391089549, 27430601314, 0, 0, 0] := by
  rw [show D2M8K2.u11987 = KTree.node D2M8K2.t11996 (nat_lit 25574867) (nat_lit 2563302657) (nat_lit 0) D2M8K2.t11997 from rfl, totK_node, tot11996, tot11997]
  decide +kernel

theorem arows11988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11988 = true := by
  rw [show D2M8K2.u11988 = KTree.node D2M8K2.t11998 (nat_lit 25578402) (nat_lit 3304450853) (nat_lit 0) D2M8K2.t11999 from rfl, allE_node, rows11998, irow11988, rows11999]
  all_goals rfl

theorem atot11988 : totK PD2M8K2 D2M8K2.u11988 = [0, 352553144384, 953236594337, 474087686878, 26325870948, 0, 0, 0] := by
  rw [show D2M8K2.u11988 = KTree.node D2M8K2.t11998 (nat_lit 25578402) (nat_lit 3304450853) (nat_lit 0) D2M8K2.t11999 from rfl, totK_node, tot11998, tot11999]
  decide +kernel

end QECKChecks.D2M8K2
