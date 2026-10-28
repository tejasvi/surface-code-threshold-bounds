import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8516 = true := by
  decide +kernel

theorem tot8516 : totK PD2M8K2 D2M8K2.t8516 = [0, 198688719040, 450178488439, 223419701338, 39543322229, 4256931014, 0, 0] := by
  decide +kernel

theorem rows8517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8517 = true := by
  decide +kernel

theorem tot8517 : totK PD2M8K2 D2M8K2.t8517 = [0, 183665725418, 468157323890, 217213831156, 12106535584, 0, 0, 0] := by
  decide +kernel

theorem rows8518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8518 = true := by
  decide +kernel

theorem tot8518 : totK PD2M8K2 D2M8K2.t8518 = [0, 11817147487, 340767193738, 474479077142, 70620425112, 0, 0, 0] := by
  decide +kernel

theorem rows8519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8519 = true := by
  decide +kernel

theorem tot8519 : totK PD2M8K2 D2M8K2.t8519 = [0, 66965202460, 266179982743, 399048727525, 136333027083, 5159868635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
