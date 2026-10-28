import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6064 = true := by
  decide +kernel

theorem tot6064 : totK PD2M8K2 D2M8K2.t6064 = [0, 46230025988, 225627751624, 424065959816, 198277322098, 8100177866, 0, 0] := by
  decide +kernel

theorem rows6065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6065 = true := by
  decide +kernel

theorem tot6065 : totK PD2M8K2 D2M8K2.t6065 = [0, 190226224533, 455800051330, 247039161425, 23200982689, 0, 0, 0] := by
  decide +kernel

theorem rows6066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6066 = true := by
  decide +kernel

theorem tot6066 : totK PD2M8K2 D2M8K2.t6066 = [0, 178977901183, 477792863057, 230368743533, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows6067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6067 = true := by
  decide +kernel

theorem tot6067 : totK PD2M8K2 D2M8K2.t6067 = [0, 0, 285834381624, 497459448325, 106065740716, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
