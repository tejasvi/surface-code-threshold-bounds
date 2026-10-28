import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15736 = true := by
  decide +kernel

theorem tot15736 : totK PD2M8K2 D2M8K2.t15736 = [0, 0, 0, 192756534370, 476526217372, 205306826903, 12488965933, 0] := by
  decide +kernel

theorem rows15737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15737 = true := by
  decide +kernel

theorem tot15737 : totK PD2M8K2 D2M8K2.t15737 = [0, 0, 0, 208624676660, 494765762430, 177615300588, 5616011243, 0] := by
  decide +kernel

theorem rows15738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15738 = true := by
  decide +kernel

theorem tot15738 : totK PD2M8K2 D2M8K2.t15738 = [0, 0, 0, 191309187276, 474221266090, 163078138819, 6040864367, 0] := by
  decide +kernel

theorem rows15739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15739 = true := by
  decide +kernel

theorem tot15739 : totK PD2M8K2 D2M8K2.t15739 = [0, 0, 0, 0, 319868150697, 438280846597, 69508129484, 1206465782] := by
  decide +kernel

end QECKChecks.D2M8K2
