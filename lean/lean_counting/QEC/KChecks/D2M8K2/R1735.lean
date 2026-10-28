import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6940 = true := by
  decide +kernel

theorem tot6940 : totK PD2M8K2 D2M8K2.t6940 = [0, 179542182719, 453171005907, 263653987305, 24484864565, 0, 0, 0] := by
  decide +kernel

theorem rows6941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6941 = true := by
  decide +kernel

theorem tot6941 : totK PD2M8K2 D2M8K2.t6941 = [0, 153421184897, 457897276441, 275937854109, 20670601551, 0, 0, 0] := by
  decide +kernel

theorem rows6942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6942 = true := by
  decide +kernel

theorem tot6942 : totK PD2M8K2 D2M8K2.t6942 = [0, 0, 230852123381, 480166646969, 169687929067, 6797886035, 0, 0] := by
  decide +kernel

theorem rows6943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6943 = true := by
  decide +kernel

theorem tot6943 : totK PD2M8K2 D2M8K2.t6943 = [0, 89709506736, 334423126188, 398328741007, 97307885643, 2381103682, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
