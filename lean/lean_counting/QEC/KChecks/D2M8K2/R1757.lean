import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7028 = true := by
  decide +kernel

theorem tot7028 : totK PD2M8K2 D2M8K2.t7028 = [0, 182730307053, 475116597401, 254068514450, 22631808637, 0, 0, 0] := by
  decide +kernel

theorem rows7029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7029 = true := by
  decide +kernel

theorem tot7029 : totK PD2M8K2 D2M8K2.t7029 = [0, 181906100151, 472964357917, 241665097409, 15553135208, 0, 0, 0] := by
  decide +kernel

theorem rows7030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7030 = true := by
  decide +kernel

theorem tot7030 : totK PD2M8K2 D2M8K2.t7030 = [0, 0, 286025141132, 504461075262, 110771058260, 1268739303, 0, 0] := by
  decide +kernel

theorem rows7031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7031 = true := by
  decide +kernel

theorem tot7031 : totK PD2M8K2 D2M8K2.t7031 = [0, 0, 201734503178, 483408789459, 187906495850, 7442000727, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
