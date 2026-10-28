import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12444 = true := by
  decide +kernel

theorem tot12444 : totK PD2M8K2 D2M8K2.t12444 = [0, 0, 203961381036, 475586840180, 177321375291, 11780292382, 0, 0] := by
  decide +kernel

theorem rows12445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12445 = true := by
  decide +kernel

theorem tot12445 : totK PD2M8K2 D2M8K2.t12445 = [0, 171610040655, 444194228147, 261282668982, 27109661347, 0, 0, 0] := by
  decide +kernel

theorem rows12446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12446 = true := by
  decide +kernel

theorem tot12446 : totK PD2M8K2 D2M8K2.t12446 = [0, 180462386115, 455266733657, 257734846021, 17842981053, 0, 0, 0] := by
  decide +kernel

theorem rows12447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12447 = true := by
  decide +kernel

theorem tot12447 : totK PD2M8K2 D2M8K2.t12447 = [0, 67329814524, 342056603097, 390687841831, 76391072570, 1162740214, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
