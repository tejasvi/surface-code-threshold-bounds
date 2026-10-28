import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14420 = true := by
  decide +kernel

theorem tot14420 : totK PD2M8K2 D2M8K2.t14420 = [0, 105988959550, 345998229367, 347361417169, 96157026286, 4030866388, 0, 0] := by
  decide +kernel

theorem rows14421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14421 = true := by
  decide +kernel

theorem tot14421 : totK PD2M8K2 D2M8K2.t14421 = [0, 164637852085, 445239607182, 281500832501, 28232646136, 0, 0, 0] := by
  decide +kernel

theorem rows14422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14422 = true := by
  decide +kernel

theorem tot14422 : totK PD2M8K2 D2M8K2.t14422 = [0, 168006800142, 469167110881, 264455288754, 20178829921, 0, 0, 0] := by
  decide +kernel

theorem rows14423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14423 = true := by
  decide +kernel

theorem tot14423 : totK PD2M8K2 D2M8K2.t14423 = [0, 0, 243830959644, 507088136032, 141445049335, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
