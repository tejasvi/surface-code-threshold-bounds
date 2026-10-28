import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15328 = true := by
  decide +kernel

theorem tot15328 : totK PD2M8K2 D2M8K2.t15328 = [0, 75480366365, 116487580931, 133203876416, 356661984211, 200034575611, 17014456371, 0] := by
  decide +kernel

theorem rows15329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15329 = true := by
  decide +kernel

theorem tot15329 : totK PD2M8K2 D2M8K2.t15329 = [0, 170388833371, 441457730133, 285799838677, 30321150294, 0, 0, 0] := by
  decide +kernel

theorem rows15330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15330 = true := by
  decide +kernel

theorem tot15330 : totK PD2M8K2 D2M8K2.t15330 = [0, 195506104499, 482765607678, 221344881913, 11637544544, 0, 0, 0] := by
  decide +kernel

theorem rows15331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15331 = true := by
  decide +kernel

theorem tot15331 : totK PD2M8K2 D2M8K2.t15331 = [0, 0, 263416797005, 441317649846, 194459894922, 21400436502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
