import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10392 = true := by
  decide +kernel

theorem tot10392 : totK PD2M8K2 D2M8K2.t10392 = [0, 0, 0, 297191238934, 496560270679, 83398694048, 1077676460, 0] := by
  decide +kernel

theorem rows10393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10393 = true := by
  decide +kernel

theorem tot10393 : totK PD2M8K2 D2M8K2.t10393 = [0, 0, 0, 181446283914, 497487801626, 211162227678, 6649401931, 0] := by
  decide +kernel

theorem rows10394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10394 = true := by
  decide +kernel

theorem tot10394 : totK PD2M8K2 D2M8K2.t10394 = [0, 0, 0, 170317179708, 455212971696, 224516367597, 14917588509, 0] := by
  decide +kernel

theorem rows10395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10395 = true := by
  decide +kernel

theorem tot10395 : totK PD2M8K2 D2M8K2.t10395 = [0, 0, 0, 218352305340, 475570154669, 164523500445, 7603700886, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
