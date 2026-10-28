import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7364 = true := by
  decide +kernel

theorem tot7364 : totK PD2M8K2 D2M8K2.t7364 = [0, 0, 163217471195, 450876629394, 246535926539, 18225953085, 0, 0] := by
  decide +kernel

theorem rows7365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7365 = true := by
  decide +kernel

theorem tot7365 : totK PD2M8K2 D2M8K2.t7365 = [0, 0, 198969354211, 484974209357, 197925074999, 9840992866, 0, 0] := by
  decide +kernel

theorem rows7366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7366 = true := by
  decide +kernel

theorem tot7366 : totK PD2M8K2 D2M8K2.t7366 = [0, 0, 200491610329, 468654378671, 210943629031, 12659244494, 0, 0] := by
  decide +kernel

theorem rows7367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7367 = true := by
  decide +kernel

theorem tot7367 : totK PD2M8K2 D2M8K2.t7367 = [0, 0, 166381972750, 457747589258, 270131512246, 29200286642, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
