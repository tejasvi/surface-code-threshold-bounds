import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14852 = true := by
  decide +kernel

theorem tot14852 : totK PD2M8K2 D2M8K2.t14852 = [0, 279542199875, 515307926106, 104751152210, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14853 = true := by
  decide +kernel

theorem tot14853 : totK PD2M8K2 D2M8K2.t14853 = [173880593436, 402325288890, 238765771930, 76338004430, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows14854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14854 = true := by
  decide +kernel

theorem tot14854 : totK PD2M8K2 D2M8K2.t14854 = [161863944937, 448902994164, 280798750184, 23027905747, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14855 = true := by
  decide +kernel

theorem tot14855 : totK PD2M8K2 D2M8K2.t14855 = [92934196222, 350965859362, 374732364838, 81874097419, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
