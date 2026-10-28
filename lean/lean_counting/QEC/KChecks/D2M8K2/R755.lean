import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3020 = true := by
  decide +kernel

theorem tot3020 : totK PD2M8K2 D2M8K2.t3020 = [0, 86054094960, 248031361860, 393713806014, 159988479717, 5521894595, 0, 0] := by
  decide +kernel

theorem rows3021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3021 = true := by
  decide +kernel

theorem tot3021 : totK PD2M8K2 D2M8K2.t3021 = [0, 183111027323, 471733492188, 254782580889, 22605955834, 0, 0, 0] := by
  decide +kernel

theorem rows3022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3022 = true := by
  decide +kernel

theorem tot3022 : totK PD2M8K2 D2M8K2.t3022 = [0, 176333444930, 476403512892, 238646269494, 13632511348, 0, 0, 0] := by
  decide +kernel

theorem rows3023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3023 = true := by
  decide +kernel

theorem tot3023 : totK PD2M8K2 D2M8K2.t3023 = [0, 0, 292141299314, 505524321253, 105312595206, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
