import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2464 = true := by
  decide +kernel

theorem tot2464 : totK PD2M8K2 D2M8K2.t2464 = [0, 172383748415, 466974632737, 241689225218, 13419830806, 0, 0, 0] := by
  decide +kernel

theorem rows2465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2465 = true := by
  decide +kernel

theorem tot2465 : totK PD2M8K2 D2M8K2.t2465 = [0, 0, 304841610159, 492755013592, 101941586665, 2909416399, 0, 0] := by
  decide +kernel

theorem rows2466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2466 = true := by
  decide +kernel

theorem tot2466 : totK PD2M8K2 D2M8K2.t2466 = [0, 66295400433, 299160293195, 401053336181, 107100755075, 2250452236, 0, 0] := by
  decide +kernel

theorem rows2467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2467 = true := by
  decide +kernel

theorem tot2467 : totK PD2M8K2 D2M8K2.t2467 = [0, 182309491354, 466155520047, 259197395724, 23031666925, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
