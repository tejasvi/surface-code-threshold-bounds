import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1172 = true := by
  decide +kernel

theorem tot1172 : totK PD2M8K2 D2M8K2.t1172 = [0, 0, 218598641153, 488664913169, 166571462736, 5139136978, 0, 0] := by
  decide +kernel

theorem rows1173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1173 = true := by
  decide +kernel

theorem tot1173 : totK PD2M8K2 D2M8K2.t1173 = [0, 0, 176090528067, 460641112060, 228281920873, 18069584445, 0, 0] := by
  decide +kernel

theorem rows1174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1174 = true := by
  decide +kernel

theorem tot1174 : totK PD2M8K2 D2M8K2.t1174 = [0, 0, 237089110061, 482120986535, 160201471406, 5187627908, 0, 0] := by
  decide +kernel

theorem rows1175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1175 = true := by
  decide +kernel

theorem tot1175 : totK PD2M8K2 D2M8K2.t1175 = [0, 0, 173412945679, 467096983722, 234117924330, 16750095950, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
