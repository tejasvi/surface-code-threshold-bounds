import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10612 = true := by
  decide +kernel

theorem tot10612 : totK PD2M8K2 D2M8K2.t10612 = [0, 0, 195786216300, 472092798261, 216196351977, 15252404492, 0, 0] := by
  decide +kernel

theorem rows10613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10613 = true := by
  decide +kernel

theorem tot10613 : totK PD2M8K2 D2M8K2.t10613 = [0, 0, 206290967986, 496478067982, 167005974212, 2519015093, 0, 0] := by
  decide +kernel

theorem rows10614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10614 = true := by
  decide +kernel

theorem tot10614 : totK PD2M8K2 D2M8K2.t10614 = [0, 0, 163374322970, 459020019884, 243289323453, 13621712409, 0, 0] := by
  decide +kernel

theorem rows10615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10615 = true := by
  decide +kernel

theorem tot10615 : totK PD2M8K2 D2M8K2.t10615 = [0, 0, 0, 279518812216, 479863604293, 88008631996, 1239866073, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
