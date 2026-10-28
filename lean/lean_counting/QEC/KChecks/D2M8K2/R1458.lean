import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5832 = true := by
  decide +kernel

theorem tot5832 : totK PD2M8K2 D2M8K2.t5832 = [154953960986, 436114155339, 283941544100, 27934971959, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5833 = true := by
  decide +kernel

theorem tot5833 : totK PD2M8K2 D2M8K2.t5833 = [90936333741, 355035350506, 357364995314, 73508326752, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5834 = true := by
  decide +kernel

theorem tot5834 : totK PD2M8K2 D2M8K2.t5834 = [0, 311305466140, 505897398324, 88971445384, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows5835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5835 = true := by
  decide +kernel

theorem tot5835 : totK PD2M8K2 D2M8K2.t5835 = [167868472426, 408958577889, 265371682393, 66190072274, 2814597007, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
