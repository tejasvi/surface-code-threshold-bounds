import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12760 = true := by
  decide +kernel

theorem tot12760 : totK PD2M8K2 D2M8K2.t12760 = [0, 194739848767, 480079883728, 217900471726, 11995599190, 0, 0, 0] := by
  decide +kernel

theorem rows12761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12761 = true := by
  decide +kernel

theorem tot12761 : totK PD2M8K2 D2M8K2.t12761 = [0, 47019603360, 278593752607, 378623698952, 177862255484, 21395095148, 0, 0] := by
  decide +kernel

theorem rows12762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12762 = true := by
  decide +kernel

theorem tot12762 : totK PD2M8K2 D2M8K2.t12762 = [0, 0, 212038893111, 477437700455, 208140479002, 7992090037, 0, 0] := by
  decide +kernel

theorem rows12763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12763 = true := by
  decide +kernel

theorem tot12763 : totK PD2M8K2 D2M8K2.t12763 = [0, 81767663791, 240628992510, 373108724411, 179871926091, 8209931632, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
