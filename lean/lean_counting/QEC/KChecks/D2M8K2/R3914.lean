import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15656 = true := by
  decide +kernel

theorem tot15656 : totK PD2M8K2 D2M8K2.t15656 = [0, 0, 177093894189, 472818094436, 225092205611, 12667552787, 0, 0] := by
  decide +kernel

theorem rows15657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15657 = true := by
  decide +kernel

theorem tot15657 : totK PD2M8K2 D2M8K2.t15657 = [0, 0, 193309763324, 479107121177, 207836784292, 12413128817, 0, 0] := by
  decide +kernel

theorem rows15658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15658 = true := by
  decide +kernel

theorem tot15658 : totK PD2M8K2 D2M8K2.t15658 = [0, 0, 213634486140, 484174587866, 176538291888, 5098257138, 0, 0] := by
  decide +kernel

theorem rows15659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15659 = true := by
  decide +kernel

theorem tot15659 : totK PD2M8K2 D2M8K2.t15659 = [0, 0, 0, 288665168703, 496779151896, 89961306557, 1310285577, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
