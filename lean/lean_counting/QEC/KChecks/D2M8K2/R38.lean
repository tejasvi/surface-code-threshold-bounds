import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t152 = true := by
  decide +kernel

theorem tot152 : totK PD2M8K2 D2M8K2.t152 = [87240234242, 326868036896, 375653691034, 105405249712, 3579068459, 0, 0, 0] := by
  decide +kernel

theorem rows153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t153 = true := by
  decide +kernel

theorem tot153 : totK PD2M8K2 D2M8K2.t153 = [172770268313, 463580940225, 263393360633, 22180653340, 0, 0, 0, 0] := by
  decide +kernel

theorem rows154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t154 = true := by
  decide +kernel

theorem tot154 : totK PD2M8K2 D2M8K2.t154 = [181674658392, 468617122647, 250054237963, 16029620758, 0, 0, 0, 0] := by
  decide +kernel

theorem rows155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t155 = true := by
  decide +kernel

theorem tot155 : totK PD2M8K2 D2M8K2.t155 = [0, 269020524842, 507318952530, 122521547452, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
