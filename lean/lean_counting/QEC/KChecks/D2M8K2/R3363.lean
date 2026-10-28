import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13452 = true := by
  decide +kernel

theorem tot13452 : totK PD2M8K2 D2M8K2.t13452 = [0, 0, 214482388135, 493669011887, 182375620232, 5265093891, 0, 0] := by
  decide +kernel

theorem rows13453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13453 = true := by
  decide +kernel

theorem tot13453 : totK PD2M8K2 D2M8K2.t13453 = [0, 0, 183172194667, 454063987115, 224369968140, 17045720036, 0, 0] := by
  decide +kernel

theorem rows13454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13454 = true := by
  decide +kernel

theorem tot13454 : totK PD2M8K2 D2M8K2.t13454 = [0, 0, 76406302441, 347614275031, 361388187774, 68858997482, 1310517177, 0] := by
  decide +kernel

theorem rows13455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13455 = true := by
  decide +kernel

theorem tot13455 : totK PD2M8K2 D2M8K2.t13455 = [0, 0, 37098105492, 353854188803, 449271404323, 45674889126, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
