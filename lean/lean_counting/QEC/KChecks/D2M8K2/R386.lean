import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1544 = true := by
  decide +kernel

theorem tot1544 : totK PD2M8K2 D2M8K2.t1544 = [0, 178667450671, 440917796293, 247083188991, 42300893900, 3060566153, 0, 0] := by
  decide +kernel

theorem rows1545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1545 = true := by
  decide +kernel

theorem tot1545 : totK PD2M8K2 D2M8K2.t1545 = [0, 191534658027, 481228076447, 222577033176, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows1546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1546 = true := by
  decide +kernel

theorem tot1546 : totK PD2M8K2 D2M8K2.t1546 = [0, 66582615597, 330843714642, 412587475415, 88128689987, 1164319620, 0, 0] := by
  decide +kernel

theorem rows1547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1547 = true := by
  decide +kernel

theorem tot1547 : totK PD2M8K2 D2M8K2.t1547 = [0, 0, 213604026643, 489020050268, 171059471784, 9404247146, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
