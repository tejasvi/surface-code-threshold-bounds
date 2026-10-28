import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14148 = true := by
  decide +kernel

theorem tot14148 : totK PD2M8K2 D2M8K2.t14148 = [0, 156887562578, 471259191086, 240979461002, 11127237002, 0, 0, 0] := by
  decide +kernel

theorem rows14149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14149 = true := by
  decide +kernel

theorem tot14149 : totK PD2M8K2 D2M8K2.t14149 = [0, 203253827134, 462706124717, 197482694700, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows14150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14150 = true := by
  decide +kernel

theorem tot14150 : totK PD2M8K2 D2M8K2.t14150 = [0, 176134838188, 482344721320, 237697443843, 9478852111, 0, 0, 0] := by
  decide +kernel

theorem rows14151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14151 = true := by
  decide +kernel

theorem tot14151 : totK PD2M8K2 D2M8K2.t14151 = [0, 171265873894, 463762785084, 250186122773, 13144782352, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
