import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5176 = true := by
  decide +kernel

theorem tot5176 : totK PD2M8K2 D2M8K2.t5176 = [0, 0, 89005186762, 329218112296, 391634983595, 95669073606, 1398595139, 0] := by
  decide +kernel

theorem rows5177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5177 = true := by
  decide +kernel

theorem tot5177 : totK PD2M8K2 D2M8K2.t5177 = [0, 0, 167529964076, 466521247281, 226575407314, 14566626306, 0, 0] := by
  decide +kernel

theorem rows5178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5178 = true := by
  decide +kernel

theorem tot5178 : totK PD2M8K2 D2M8K2.t5178 = [0, 0, 138081896298, 431155122325, 281454394768, 20788685507, 0, 0] := by
  decide +kernel

theorem rows5179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5179 = true := by
  decide +kernel

theorem tot5179 : totK PD2M8K2 D2M8K2.t5179 = [0, 0, 0, 275842707427, 501669405262, 93523371037, 1326647619, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
