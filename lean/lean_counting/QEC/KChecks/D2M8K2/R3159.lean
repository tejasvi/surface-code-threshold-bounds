import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12636 = true := by
  decide +kernel

theorem tot12636 : totK PD2M8K2 D2M8K2.t12636 = [0, 0, 187540238935, 461346645564, 218004107715, 12523541424, 0, 0] := by
  decide +kernel

theorem rows12637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12637 = true := by
  decide +kernel

theorem tot12637 : totK PD2M8K2 D2M8K2.t12637 = [0, 0, 0, 313593586326, 475636176791, 87355618985, 1198073392, 0] := by
  decide +kernel

theorem rows12638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12638 = true := by
  decide +kernel

theorem tot12638 : totK PD2M8K2 D2M8K2.t12638 = [0, 0, 22203310812, 208870945664, 433083478789, 164155722417, 11894306413, 0] := by
  decide +kernel

theorem rows12639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12639 = true := by
  decide +kernel

theorem tot12639 : totK PD2M8K2 D2M8K2.t12639 = [0, 0, 201090246357, 467649638534, 207531566166, 9745156230, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
