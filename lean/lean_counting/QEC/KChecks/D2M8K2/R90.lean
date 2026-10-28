import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t360 = true := by
  decide +kernel

theorem tot360 : totK PD2M8K2 D2M8K2.t360 = [84415941621, 335309005449, 367917240396, 93668022289, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t361 = true := by
  decide +kernel

theorem tot361 : totK PD2M8K2 D2M8K2.t361 = [174894712533, 445864640155, 265057488716, 27172656264, 0, 0, 0, 0] := by
  decide +kernel

theorem rows362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t362 = true := by
  decide +kernel

theorem tot362 : totK PD2M8K2 D2M8K2.t362 = [156825944409, 449665671399, 261112452672, 16568053419, 0, 0, 0, 0] := by
  decide +kernel

theorem rows363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t363 = true := by
  decide +kernel

theorem tot363 : totK PD2M8K2 D2M8K2.t363 = [0, 274822647873, 506440335462, 105327913837, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
