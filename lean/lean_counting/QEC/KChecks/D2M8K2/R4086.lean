import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16344 = true := by
  decide +kernel

theorem tot16344 : totK PD2M8K2 D2M8K2.t16344 = [0, 0, 0, 174067170111, 470233300328, 231101886383, 13882020092, 0] := by
  decide +kernel

theorem rows16345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16345 = true := by
  decide +kernel

theorem tot16345 : totK PD2M8K2 D2M8K2.t16345 = [0, 0, 18874737507, 174218700406, 440514386130, 253021066444, 20086427390, 0] := by
  decide +kernel

theorem rows16346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16346 = true := by
  decide +kernel

theorem tot16346 : totK PD2M8K2 D2M8K2.t16346 = [0, 0, 193363106587, 484659970822, 205264348353, 7846568611, 0, 0] := by
  decide +kernel

theorem rows16347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16347 = true := by
  decide +kernel

theorem tot16347 : totK PD2M8K2 D2M8K2.t16347 = [0, 0, 204614464733, 485623064327, 188678533259, 7650820675, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
