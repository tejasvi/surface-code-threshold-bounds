import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1116 = true := by
  decide +kernel

theorem tot1116 : totK PD2M8K2 D2M8K2.t1116 = [0, 189668183713, 482833509663, 224103161638, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows1117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1117 = true := by
  decide +kernel

theorem tot1117 : totK PD2M8K2 D2M8K2.t1117 = [0, 0, 293107949314, 496065081168, 98648392704, 1164319620, 0, 0] := by
  decide +kernel

theorem rows1118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1118 = true := by
  decide +kernel

theorem tot1118 : totK PD2M8K2 D2M8K2.t1118 = [0, 0, 198354855527, 477005348897, 188839462597, 11885407614, 0, 0] := by
  decide +kernel

theorem rows1119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1119 = true := by
  decide +kernel

theorem tot1119 : totK PD2M8K2 D2M8K2.t1119 = [0, 169505873603, 447323867609, 256714451996, 23809070646, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
