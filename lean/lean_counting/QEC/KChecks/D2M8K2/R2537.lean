import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10148 = true := by
  decide +kernel

theorem tot10148 : totK PD2M8K2 D2M8K2.t10148 = [0, 0, 178053555707, 462062673433, 242253989006, 18246066036, 0, 0] := by
  decide +kernel

theorem rows10149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10149 = true := by
  decide +kernel

theorem tot10149 : totK PD2M8K2 D2M8K2.t10149 = [0, 0, 184653437315, 486474021186, 213391759236, 6536386765, 0, 0] := by
  decide +kernel

theorem rows10150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10150 = true := by
  decide +kernel

theorem tot10150 : totK PD2M8K2 D2M8K2.t10150 = [0, 0, 180163922697, 466865954323, 254122919779, 16844766783, 0, 0] := by
  decide +kernel

theorem rows10151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10151 = true := by
  decide +kernel

theorem tot10151 : totK PD2M8K2 D2M8K2.t10151 = [0, 0, 209968629687, 480508512649, 204199998188, 7667967876, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
