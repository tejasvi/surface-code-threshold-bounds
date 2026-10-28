import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11208 = true := by
  decide +kernel

theorem tot11208 : totK PD2M8K2 D2M8K2.t11208 = [0, 87240234242, 315700502306, 386171016501, 108780768938, 4030866388, 0, 0] := by
  decide +kernel

theorem rows11209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11209 = true := by
  decide +kernel

theorem tot11209 : totK PD2M8K2 D2M8K2.t11209 = [0, 160098750431, 452988851366, 267909491251, 24737388135, 0, 0, 0] := by
  decide +kernel

theorem rows11210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11210 = true := by
  decide +kernel

theorem tot11210 : totK PD2M8K2 D2M8K2.t11210 = [0, 179743082377, 467379067333, 249485377065, 12425053908, 0, 0, 0] := by
  decide +kernel

theorem rows11211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11211 = true := by
  decide +kernel

theorem tot11211 : totK PD2M8K2 D2M8K2.t11211 = [0, 0, 264906462119, 508364984934, 122755804882, 1249641317, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
