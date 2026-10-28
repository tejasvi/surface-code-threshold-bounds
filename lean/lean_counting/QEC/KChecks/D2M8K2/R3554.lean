import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14216 = true := by
  decide +kernel

theorem tot14216 : totK PD2M8K2 D2M8K2.t14216 = [0, 176020930727, 454605931738, 271815758955, 29184232052, 0, 0, 0] := by
  decide +kernel

theorem rows14217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14217 = true := by
  decide +kernel

theorem tot14217 : totK PD2M8K2 D2M8K2.t14217 = [0, 205350274880, 487708396289, 189435807116, 6762184908, 0, 0, 0] := by
  decide +kernel

theorem rows14218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14218 = true := by
  decide +kernel

theorem tot14218 : totK PD2M8K2 D2M8K2.t14218 = [0, 175591062921, 466275237949, 244141486677, 20489171410, 0, 0, 0] := by
  decide +kernel

theorem rows14219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14219 = true := by
  decide +kernel

theorem tot14219 : totK PD2M8K2 D2M8K2.t14219 = [0, 179402228140, 456568601669, 251817847182, 16627933934, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
