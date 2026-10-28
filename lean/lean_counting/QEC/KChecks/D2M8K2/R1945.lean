import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7780 = true := by
  decide +kernel

theorem tot7780 : totK PD2M8K2 D2M8K2.t7780 = [0, 190871841998, 489437351981, 211303522223, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows7781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7781 = true := by
  decide +kernel

theorem tot7781 : totK PD2M8K2 D2M8K2.t7781 = [0, 182858717031, 467326724191, 222782987863, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows7782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7782 = true := by
  decide +kernel

theorem tot7782 : totK PD2M8K2 D2M8K2.t7782 = [0, 0, 276630476703, 500367460727, 108593276245, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7783 = true := by
  decide +kernel

theorem tot7783 : totK PD2M8K2 D2M8K2.t7783 = [0, 87164153352, 377160248457, 391799405708, 47987853721, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
