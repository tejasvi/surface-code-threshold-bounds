import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3256 = true := by
  decide +kernel

theorem tot3256 : totK PD2M8K2 D2M8K2.t3256 = [0, 173321245871, 473750607661, 226670819830, 8917007962, 0, 0, 0] := by
  decide +kernel

theorem rows3257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3257 = true := by
  decide +kernel

theorem tot3257 : totK PD2M8K2 D2M8K2.t3257 = [0, 0, 276763878632, 496193581661, 93962216230, 1310285577, 0, 0] := by
  decide +kernel

theorem rows3258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3258 = true := by
  decide +kernel

theorem tot3258 : totK PD2M8K2 D2M8K2.t3258 = [0, 122430309746, 388070730155, 364589301491, 42639892933, 0, 0, 0] := by
  decide +kernel

theorem rows3259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3259 = true := by
  decide +kernel

theorem tot3259 : totK PD2M8K2 D2M8K2.t3259 = [0, 189921604272, 476247946147, 235900025988, 13118995350, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
