import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15956 = true := by
  decide +kernel

theorem tot15956 : totK PD2M8K2 D2M8K2.t15956 = [0, 0, 173477795397, 451494168164, 263454248456, 19570179518, 0, 0] := by
  decide +kernel

theorem rows15957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15957 = true := by
  decide +kernel

theorem tot15957 : totK PD2M8K2 D2M8K2.t15957 = [0, 0, 150331015777, 466366726398, 255232988434, 14527409711, 0, 0] := by
  decide +kernel

theorem rows15958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15958 = true := by
  decide +kernel

theorem tot15958 : totK PD2M8K2 D2M8K2.t15958 = [0, 0, 0, 290621875090, 511787537602, 78656837428, 1164319620, 0] := by
  decide +kernel

theorem rows15959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15959 = true := by
  decide +kernel

theorem tot15959 : totK PD2M8K2 D2M8K2.t15959 = [0, 0, 194800701799, 457090533974, 232897864982, 23060754447, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
