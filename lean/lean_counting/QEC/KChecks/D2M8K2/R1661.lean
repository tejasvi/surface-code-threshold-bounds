import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6644 = true := by
  decide +kernel

theorem tot6644 : totK PD2M8K2 D2M8K2.t6644 = [0, 177515619407, 463921452342, 243492903995, 15359369050, 0, 0, 0] := by
  decide +kernel

theorem rows6645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6645 = true := by
  decide +kernel

theorem tot6645 : totK PD2M8K2 D2M8K2.t6645 = [0, 80504024103, 389230808913, 395431060636, 51065325974, 0, 0, 0] := by
  decide +kernel

theorem rows6646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6646 = true := by
  decide +kernel

theorem tot6646 : totK PD2M8K2 D2M8K2.t6646 = [0, 0, 202499423312, 477641089756, 186737456048, 11873025674, 0, 0] := by
  decide +kernel

theorem rows6647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6647 = true := by
  decide +kernel

theorem tot6647 : totK PD2M8K2 D2M8K2.t6647 = [0, 161095609644, 431698712302, 290774732785, 34513186551, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
