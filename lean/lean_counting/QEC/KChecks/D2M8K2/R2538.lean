import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10152 = true := by
  decide +kernel

theorem tot10152 : totK PD2M8K2 D2M8K2.t10152 = [0, 0, 189641843039, 475625747404, 224949698601, 15844255384, 0, 0] := by
  decide +kernel

theorem rows10153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10153 = true := by
  decide +kernel

theorem tot10153 : totK PD2M8K2 D2M8K2.t10153 = [0, 0, 188819380167, 449833588506, 223893475307, 16702988424, 0, 0] := by
  decide +kernel

theorem rows10154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10154 = true := by
  decide +kernel

theorem tot10154 : totK PD2M8K2 D2M8K2.t10154 = [0, 0, 3950786586, 326682854501, 440233577654, 84004588546, 1095107716, 0] := by
  decide +kernel

theorem rows10155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10155 = true := by
  decide +kernel

theorem tot10155 : totK PD2M8K2 D2M8K2.t10155 = [0, 77804430160, 106549316852, 215839687046, 364007142049, 107080344441, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
