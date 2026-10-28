import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12156 = true := by
  decide +kernel

theorem tot12156 : totK PD2M8K2 D2M8K2.t12156 = [0, 157402941617, 449165235019, 283265122532, 23119592771, 0, 0, 0] := by
  decide +kernel

theorem rows12157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12157 = true := by
  decide +kernel

theorem tot12157 : totK PD2M8K2 D2M8K2.t12157 = [0, 157955920744, 459579256566, 275656057774, 28355204665, 0, 0, 0] := by
  decide +kernel

theorem rows12158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12158 = true := by
  decide +kernel

theorem tot12158 : totK PD2M8K2 D2M8K2.t12158 = [0, 0, 190570527331, 454663170103, 236927221125, 20729648156, 0, 0] := by
  decide +kernel

theorem rows12159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12159 = true := by
  decide +kernel

theorem tot12159 : totK PD2M8K2 D2M8K2.t12159 = [0, 0, 185990152900, 495610265697, 207376005989, 6455993582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
