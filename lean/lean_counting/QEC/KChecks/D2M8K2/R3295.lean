import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13180 = true := by
  decide +kernel

theorem tot13180 : totK PD2M8K2 D2M8K2.t13180 = [0, 0, 202781237447, 479286913475, 208488240064, 11051716772, 0, 0] := by
  decide +kernel

theorem rows13181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13181 = true := by
  decide +kernel

theorem tot13181 : totK PD2M8K2 D2M8K2.t13181 = [0, 0, 194732942111, 469350094641, 209903743210, 12370590376, 0, 0] := by
  decide +kernel

theorem rows13182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13182 = true := by
  decide +kernel

theorem tot13182 : totK PD2M8K2 D2M8K2.t13182 = [0, 0, 188167127382, 487835324031, 222737574233, 11066126582, 0, 0] := by
  decide +kernel

theorem rows13183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13183 = true := by
  decide +kernel

theorem tot13183 : totK PD2M8K2 D2M8K2.t13183 = [0, 0, 159636122652, 465835655119, 254998160416, 13597322258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
