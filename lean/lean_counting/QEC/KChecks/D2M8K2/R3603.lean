import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14412 = true := by
  decide +kernel

theorem tot14412 : totK PD2M8K2 D2M8K2.t14412 = [0, 0, 225927262985, 504924119484, 171924042712, 3765316428, 0, 0] := by
  decide +kernel

theorem rows14413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14413 = true := by
  decide +kernel

theorem tot14413 : totK PD2M8K2 D2M8K2.t14413 = [0, 172608296538, 383254746513, 238369157173, 100376510120, 6784518318, 0, 0] := by
  decide +kernel

theorem rows14414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14414 = true := by
  decide +kernel

theorem tot14414 : totK PD2M8K2 D2M8K2.t14414 = [0, 162776293173, 436098342001, 273386623061, 25567252863, 0, 0, 0] := by
  decide +kernel

theorem rows14415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14415 = true := by
  decide +kernel

theorem tot14415 : totK PD2M8K2 D2M8K2.t14415 = [0, 89734097483, 360645642393, 372290459272, 69584238739, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
