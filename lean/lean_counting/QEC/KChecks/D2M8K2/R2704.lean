import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10816 = true := by
  decide +kernel

theorem tot10816 : totK PD2M8K2 D2M8K2.t10816 = [0, 172593727832, 443476508006, 256808277685, 20365899507, 0, 0, 0] := by
  decide +kernel

theorem rows10817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10817 = true := by
  decide +kernel

theorem tot10817 : totK PD2M8K2 D2M8K2.t10817 = [0, 92999530293, 358775390261, 373227229608, 85764925039, 1267860612, 0, 0] := by
  decide +kernel

theorem rows10818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10818 = true := by
  decide +kernel

theorem tot10818 : totK PD2M8K2 D2M8K2.t10818 = [0, 0, 231392709054, 487347422730, 155357864488, 4755924271, 0, 0] := by
  decide +kernel

theorem rows10819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10819 = true := by
  decide +kernel

theorem tot10819 : totK PD2M8K2 D2M8K2.t10819 = [0, 0, 186641657759, 461825445219, 237904037222, 26476701864, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
