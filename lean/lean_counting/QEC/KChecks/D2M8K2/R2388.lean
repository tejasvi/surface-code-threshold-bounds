import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9552 = true := by
  decide +kernel

theorem tot9552 : totK PD2M8K2 D2M8K2.t9552 = [187909200779, 463995575809, 244997226692, 23077241460, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9553 = true := by
  decide +kernel

theorem tot9553 : totK PD2M8K2 D2M8K2.t9553 = [140604754396, 453849095417, 285687559403, 21885830156, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9554 = true := by
  decide +kernel

theorem tot9554 : totK PD2M8K2 D2M8K2.t9554 = [0, 291258707549, 514715506780, 103729749297, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows9555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9555 = true := by
  decide +kernel

theorem tot9555 : totK PD2M8K2 D2M8K2.t9555 = [173880593436, 391621150706, 245314561298, 83016700829, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
