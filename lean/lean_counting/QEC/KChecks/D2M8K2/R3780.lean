import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15120 = true := by
  decide +kernel

theorem tot15120 : totK PD2M8K2 D2M8K2.t15120 = [0, 0, 208857297232, 478542199218, 166049406423, 4978993093, 0, 0] := by
  decide +kernel

theorem rows15121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15121 = true := by
  decide +kernel

theorem tot15121 : totK PD2M8K2 D2M8K2.t15121 = [0, 0, 19330912284, 304259835419, 455038500491, 82454667506, 1206465782, 0] := by
  decide +kernel

theorem rows15122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15122 = true := by
  decide +kernel

theorem tot15122 : totK PD2M8K2 D2M8K2.t15122 = [0, 0, 89112857528, 416020448428, 356210620923, 34800753210, 0, 0] := by
  decide +kernel

theorem rows15123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15123 = true := by
  decide +kernel

theorem tot15123 : totK PD2M8K2 D2M8K2.t15123 = [0, 0, 189283508786, 471862611349, 225930535032, 15862401762, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
