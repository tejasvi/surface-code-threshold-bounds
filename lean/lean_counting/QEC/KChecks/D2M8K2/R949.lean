import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3796 = true := by
  decide +kernel

theorem tot3796 : totK PD2M8K2 D2M8K2.t3796 = [155861873861, 417093655701, 323517825818, 40652125242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3797 = true := by
  decide +kernel

theorem tot3797 : totK PD2M8K2 D2M8K2.t3797 = [173242471757, 483073579527, 244922315439, 15519916989, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3798 = true := by
  decide +kernel

theorem tot3798 : totK PD2M8K2 D2M8K2.t3798 = [88459214294, 363269826977, 360719753548, 94686057021, 10443687594, 0, 0, 0] := by
  decide +kernel

theorem rows3799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3799 = true := by
  decide +kernel

theorem tot3799 : totK PD2M8K2 D2M8K2.t3799 = [0, 158871470601, 456734217903, 272584416211, 17265136778, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
