import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3732 = true := by
  decide +kernel

theorem tot3732 : totK PD2M8K2 D2M8K2.t3732 = [102537100388, 441073239058, 343019119634, 36496398561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3733 = true := by
  decide +kernel

theorem tot3733 : totK PD2M8K2 D2M8K2.t3733 = [28075548323, 279510577070, 474697560507, 121361929577, 3785881357, 0, 0, 0] := by
  decide +kernel

theorem rows3734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3734 = true := by
  decide +kernel

theorem tot3734 : totK PD2M8K2 D2M8K2.t3734 = [185342268821, 466699820095, 253238784503, 23349548986, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3735 = true := by
  decide +kernel

theorem tot3735 : totK PD2M8K2 D2M8K2.t3735 = [193299541545, 460190812585, 233156389427, 16468539872, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
