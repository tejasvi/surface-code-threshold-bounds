import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5700 = true := by
  decide +kernel

theorem tot5700 : totK PA10K2 A10K2.t5700 = [0, 0, 226056126454, 1214755312369, 2127231351522, 1302175952387, 220894068608, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5701 = true := by
  decide +kernel

theorem tot5701 : totK PA10K2 A10K2.t5701 = [0, 310366196018, 1073954339101, 1407940507113, 1316892644077, 773244418564, 91885338759, 0, 0, 0] := by
  decide +kernel

theorem rows5702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5702 = true := by
  decide +kernel

theorem tot5702 : totK PA10K2 A10K2.t5702 = [0, 490160962616, 1836217900974, 1907404614811, 473672692688, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5703 = true := by
  decide +kernel

theorem tot5703 : totK PA10K2 A10K2.t5703 = [0, 0, 578245653560, 1968194460618, 1711876650510, 404922093072, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
