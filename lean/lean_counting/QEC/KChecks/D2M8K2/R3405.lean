import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13620 = true := by
  decide +kernel

theorem tot13620 : totK PD2M8K2 D2M8K2.t13620 = [0, 276951255903, 516022602113, 102574887884, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13621 = true := by
  decide +kernel

theorem tot13621 : totK PD2M8K2 D2M8K2.t13621 = [0, 231813519097, 496630636759, 163841925227, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows13622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13622 = true := by
  decide +kernel

theorem tot13622 : totK PD2M8K2 D2M8K2.t13622 = [0, 170186349872, 453336292790, 224192451747, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows13623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13623 = true := by
  decide +kernel

theorem tot13623 : totK PD2M8K2 D2M8K2.t13623 = [0, 158348253875, 462728919184, 244362483786, 15898197137, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
