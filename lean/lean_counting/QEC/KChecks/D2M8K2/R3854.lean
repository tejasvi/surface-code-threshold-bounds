import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15416 = true := by
  decide +kernel

theorem tot15416 : totK PD2M8K2 D2M8K2.t15416 = [0, 118223217492, 352334712908, 325266778428, 88827320189, 3581949829, 0, 0] := by
  decide +kernel

theorem rows15417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15417 = true := by
  decide +kernel

theorem tot15417 : totK PD2M8K2 D2M8K2.t15417 = [0, 172532326786, 445815844827, 274519192605, 28234979583, 0, 0, 0] := by
  decide +kernel

theorem rows15418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15418 = true := by
  decide +kernel

theorem tot15418 : totK PD2M8K2 D2M8K2.t15418 = [0, 88783717721, 412797031551, 354429777997, 39829925242, 0, 0, 0] := by
  decide +kernel

theorem rows15419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15419 = true := by
  decide +kernel

theorem tot15419 : totK PD2M8K2 D2M8K2.t15419 = [0, 24251088202, 275814866679, 482762300315, 119039950927, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
