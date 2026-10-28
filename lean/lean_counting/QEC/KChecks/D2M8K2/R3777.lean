import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15108 = true := by
  decide +kernel

theorem tot15108 : totK PD2M8K2 D2M8K2.t15108 = [0, 190594145816, 470687795897, 222446077778, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows15109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15109 = true := by
  decide +kernel

theorem tot15109 : totK PD2M8K2 D2M8K2.t15109 = [0, 19433589518, 311644300426, 470104867243, 97816428913, 1164319620, 0, 0] := by
  decide +kernel

theorem rows15110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15110 = true := by
  decide +kernel

theorem tot15110 : totK PD2M8K2 D2M8K2.t15110 = [0, 0, 197777855300, 476037404947, 189136027392, 11885407614, 0, 0] := by
  decide +kernel

theorem rows15111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15111 = true := by
  decide +kernel

theorem tot15111 : totK PD2M8K2 D2M8K2.t15111 = [0, 157970222024, 439322952491, 290373353687, 29239470316, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
