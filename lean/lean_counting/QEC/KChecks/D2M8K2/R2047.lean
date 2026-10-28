import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8188 = true := by
  decide +kernel

theorem tot8188 : totK PD2M8K2 D2M8K2.t8188 = [0, 205342374630, 475914698448, 210988939985, 12317784814, 0, 0, 0] := by
  decide +kernel

theorem rows8189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8189 = true := by
  decide +kernel

theorem tot8189 : totK PD2M8K2 D2M8K2.t8189 = [0, 0, 297434502487, 498505597221, 100047175265, 1164319620, 0, 0] := by
  decide +kernel

theorem rows8190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8190 = true := by
  decide +kernel

theorem tot8190 : totK PD2M8K2 D2M8K2.t8190 = [0, 0, 218566802108, 482185637184, 176602910655, 9387791372, 0, 0] := by
  decide +kernel

theorem rows8191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8191 = true := by
  decide +kernel

theorem tot8191 : totK PD2M8K2 D2M8K2.t8191 = [0, 170754457897, 438920385748, 260409387696, 27904399126, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
