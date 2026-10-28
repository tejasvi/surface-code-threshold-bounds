import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7564 = true := by
  decide +kernel

theorem tot7564 : totK PD2M8K2 D2M8K2.t7564 = [0, 0, 209100906239, 499203882561, 173533757505, 4967996017, 0, 0] := by
  decide +kernel

theorem rows7565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7565 = true := by
  decide +kernel

theorem tot7565 : totK PD2M8K2 D2M8K2.t7565 = [0, 0, 196917351909, 460463891908, 214899474737, 15090175782, 0, 0] := by
  decide +kernel

theorem rows7566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7566 = true := by
  decide +kernel

theorem tot7566 : totK PD2M8K2 D2M8K2.t7566 = [0, 0, 199114529529, 479083689928, 198779017053, 9840992866, 0, 0] := by
  decide +kernel

theorem rows7567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7567 = true := by
  decide +kernel

theorem tot7567 : totK PD2M8K2 D2M8K2.t7567 = [0, 0, 178208316056, 480680195219, 203182940359, 6239403452, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
