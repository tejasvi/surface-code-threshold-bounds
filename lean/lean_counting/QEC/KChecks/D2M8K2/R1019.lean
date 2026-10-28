import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4076 = true := by
  decide +kernel

theorem tot4076 : totK PD2M8K2 D2M8K2.t4076 = [0, 0, 160467667633, 478689672109, 235056651454, 9861922787, 0, 0] := by
  decide +kernel

theorem rows4077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4077 = true := by
  decide +kernel

theorem tot4077 : totK PD2M8K2 D2M8K2.t4077 = [0, 0, 185199694924, 454987790266, 224642675988, 19213705731, 0, 0] := by
  decide +kernel

theorem rows4078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4078 = true := by
  decide +kernel

theorem tot4078 : totK PD2M8K2 D2M8K2.t4078 = [0, 0, 136151143189, 440006714493, 278347313472, 20048707049, 0, 0] := by
  decide +kernel

theorem rows4079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4079 = true := by
  decide +kernel

theorem tot4079 : totK PD2M8K2 D2M8K2.t4079 = [0, 0, 93421458046, 383766531206, 381676340202, 37454104101, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
