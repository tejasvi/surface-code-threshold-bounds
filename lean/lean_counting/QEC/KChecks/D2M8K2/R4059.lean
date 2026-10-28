import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16236 = true := by
  decide +kernel

theorem tot16236 : totK PD2M8K2 D2M8K2.t16236 = [0, 0, 0, 212656486543, 474746351942, 168902032075, 7182288656, 0] := by
  decide +kernel

theorem rows16237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16237 = true := by
  decide +kernel

theorem tot16237 : totK PD2M8K2 D2M8K2.t16237 = [0, 0, 174989750872, 368504295503, 226951746062, 116946933432, 13326740810, 0] := by
  decide +kernel

theorem rows16238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16238 = true := by
  decide +kernel

theorem tot16238 : totK PD2M8K2 D2M8K2.t16238 = [0, 0, 167936292315, 466410691631, 236676420047, 13427660039, 0, 0] := by
  decide +kernel

theorem rows16239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16239 = true := by
  decide +kernel

theorem tot16239 : totK PD2M8K2 D2M8K2.t16239 = [0, 0, 88680480173, 383563112185, 354676222344, 61834499192, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
