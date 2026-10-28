import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4516 = true := by
  decide +kernel

theorem tot4516 : totK PD2M8K2 D2M8K2.t4516 = [0, 22171057249, 270040333092, 469865843197, 149753570898, 7057208448, 0, 0] := by
  decide +kernel

theorem rows4517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4517 = true := by
  decide +kernel

theorem tot4517 : totK PD2M8K2 D2M8K2.t4517 = [0, 188426569546, 456391258033, 245179576182, 23003581512, 0, 0, 0] := by
  decide +kernel

theorem rows4518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4518 = true := by
  decide +kernel

theorem tot4518 : totK PD2M8K2 D2M8K2.t4518 = [0, 191527222623, 466745975703, 238097213250, 15060770392, 0, 0, 0] := by
  decide +kernel

theorem rows4519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4519 = true := by
  decide +kernel

theorem tot4519 : totK PD2M8K2 D2M8K2.t4519 = [0, 38138102475, 318056467819, 438870563425, 100798856484, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
