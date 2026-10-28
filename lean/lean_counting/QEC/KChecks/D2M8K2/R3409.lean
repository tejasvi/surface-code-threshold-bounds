import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13636 = true := by
  decide +kernel

theorem tot13636 : totK PD2M8K2 D2M8K2.t13636 = [8225356785, 330325989860, 509782273790, 66469517412, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13637 = true := by
  decide +kernel

theorem tot13637 : totK PD2M8K2 D2M8K2.t13637 = [169576319405, 445921673833, 279123984492, 30017483267, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13638 = true := by
  decide +kernel

theorem tot13638 : totK PD2M8K2 D2M8K2.t13638 = [166877321919, 465347381724, 273373368522, 21799273814, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13639 = true := by
  decide +kernel

theorem tot13639 : totK PD2M8K2 D2M8K2.t13639 = [0, 179289021849, 450718129952, 251779831767, 25092327913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
