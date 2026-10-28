import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13948 = true := by
  decide +kernel

theorem tot13948 : totK PD2M8K2 D2M8K2.t13948 = [0, 181446867724, 472344732330, 249518438451, 20128547347, 0, 0, 0] := by
  decide +kernel

theorem rows13949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13949 = true := by
  decide +kernel

theorem tot13949 : totK PD2M8K2 D2M8K2.t13949 = [0, 181220032959, 472462790808, 238090276588, 12503027455, 0, 0, 0] := by
  decide +kernel

theorem rows13950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13950 = true := by
  decide +kernel

theorem tot13950 : totK PD2M8K2 D2M8K2.t13950 = [0, 0, 297547525494, 490589440068, 103517174304, 1242138600, 0, 0] := by
  decide +kernel

theorem rows13951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13951 = true := by
  decide +kernel

theorem tot13951 : totK PD2M8K2 D2M8K2.t13951 = [0, 0, 208765716000, 476269248969, 167302122001, 7182288656, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
