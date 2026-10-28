import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4832 = true := by
  decide +kernel

theorem tot4832 : totK PD2M8K2 D2M8K2.t4832 = [0, 0, 85286195146, 415123124816, 359686337199, 34782965602, 0, 0] := by
  decide +kernel

theorem rows4833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4833 = true := by
  decide +kernel

theorem tot4833 : totK PD2M8K2 D2M8K2.t4833 = [0, 0, 225646975932, 472665196087, 214869517939, 13304245942, 0, 0] := by
  decide +kernel

theorem rows4834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4834 = true := by
  decide +kernel

theorem tot4834 : totK PD2M8K2 D2M8K2.t4834 = [0, 0, 185488770186, 455746718907, 261223910463, 26995087098, 0, 0] := by
  decide +kernel

theorem rows4835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4835 = true := by
  decide +kernel

theorem tot4835 : totK PD2M8K2 D2M8K2.t4835 = [0, 0, 174122390709, 461776241871, 266168858815, 18955433537, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
