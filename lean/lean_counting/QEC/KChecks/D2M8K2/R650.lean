import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2600 = true := by
  decide +kernel

theorem tot2600 : totK PD2M8K2 D2M8K2.t2600 = [93768764846, 392508243423, 368107917759, 57622718326, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows2601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2601 = true := by
  decide +kernel

theorem tot2601 : totK PD2M8K2 D2M8K2.t2601 = [0, 231960940354, 501379070487, 160303780597, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows2602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2602 = true := by
  decide +kernel

theorem tot2602 : totK PD2M8K2 D2M8K2.t2602 = [0, 193385845635, 460658082298, 215545063104, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows2603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2603 = true := by
  decide +kernel

theorem tot2603 : totK PD2M8K2 D2M8K2.t2603 = [0, 162893828111, 478927483625, 233948603999, 9354552220, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
